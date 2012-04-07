%
% (c) The University of Glasgow 2011
%

The deriving code for the Generic class
(equivalent to the code in TcGenDeriv, for other classes)

\begin{code}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://hackage.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details


module TcGenGenerics (canDoGenerics, GenericKind(..), DeriveGeneric(..),
                      gen_Generic_binds) where


import DynFlags
import HsSyn
import Type
import TcType
import {-# SOURCE #-} TcDeriv (cond_functorOK_tc)
import TcGenDeriv
import DataCon
import TyCon
import FamInstEnv       ( FamInst, mkSynFamInst )
import Module           ( Module, moduleName, moduleNameString )
import IfaceEnv         ( newGlobalBinder )
import Name      hiding ( varName )
import RdrName
import BasicTypes
import TysWiredIn
import PrelNames
import InstEnv
import TcEnv
import MkId
import TcRnMonad
import HscTypes
import BuildTyCl
import SrcLoc
import Bag
import VarSet (isEmptyVarSet)
import Outputable 
import FastString
import UniqSupply

#include "HsVersions.h"
\end{code}

%************************************************************************
%*                                                                      *
\subsection{Bindings for the new generic deriving mechanism}
%*                                                                      *
%************************************************************************

For the generic representation we need to generate:
\begin{itemize}
\item A Generic instance
\item A Rep type instance 
\item Many auxiliary datatypes and instances for them (for the meta-information)
\end{itemize}

\begin{code}
gen_Generic_binds :: DeriveGeneric -> TyCon -> Module
                 -> TcM (LHsBinds RdrName, BagDerivStuff)
gen_Generic_binds dg tc mod = do
        { (metaTyCons, repTyInsts) <- genGenericRepExtras dg tc mod
        ; metaInsts                <- genDtMeta (tc, metaTyCons)
        ; return ( let each gk = mkBindsRep gk tc
                   in case dg of
                        One gk -> each gk
                        Both   -> each Gen0 `unionBags` each Gen1
                 ,             (mapBag DerivFamInst repTyInsts)
                   `unionBags` ((mapBag DerivTyCon (metaTyCons2TyCons metaTyCons))
                   `unionBags` metaInsts)) }

genGenericRepExtras :: DeriveGeneric -> TyCon -> Module -> TcM (MetaTyCons, Bag FamInst)
genGenericRepExtras dg tc mod =
  do  uniqS <- newUniqueSupply
      let
        -- Uniques for everyone
        (uniqD:uniqs) = uniqsFromSupply uniqS
        (uniqsC,us) = splitAt (length tc_cons) uniqs
        uniqsS :: [[Unique]] -- Unique supply for the S datatypes
        uniqsS = mkUniqsS tc_arits us
        mkUniqsS []    _  = []
        mkUniqsS (n:t) us = case splitAt n us of
                              (us1,us2) -> us1 : mkUniqsS t us2

        tc_name   = tyConName tc
        tc_cons   = tyConDataCons tc
        tc_arits  = map dataConSourceArity tc_cons
        
        tc_occ    = nameOccName tc_name
        d_occ     = mkGenD tc_occ
        c_occ m   = mkGenC tc_occ m
        s_occ m n = mkGenS tc_occ m n
        d_name    = mkExternalName uniqD mod d_occ wiredInSrcSpan
        c_names   = [ mkExternalName u mod (c_occ m) wiredInSrcSpan
                      | (u,m) <- zip uniqsC [0..] ]
        s_names   = [ [ mkExternalName u mod (s_occ m n) wiredInSrcSpan 
                        | (u,n) <- zip us [0..] ] | (us,m) <- zip uniqsS [0..] ]
        
        mkTyCon name = ASSERT( isExternalName name )
                       buildAlgTyCon name [] Nothing [] distinctAbstractTyConRhs
                                          NonRecursive False NoParentTyCon

      let metaDTyCon  = mkTyCon d_name
          metaCTyCons = map mkTyCon c_names
          metaSTyCons =  [ [ mkTyCon s_name | s_name <- s_namesC ] 
                         | s_namesC <- s_names ]

          metaDts = MetaTyCons metaDTyCon metaCTyCons metaSTyCons

      rep_insts <- let each gk = tc_mkRepFamInsts gk tc metaDts mod
                   in mapBagM each $ listToBag $ case dg of
                                    One gk -> [gk]
                                    Both -> [Gen0, Gen1]
      
      -- pprTrace "rep0" (ppr rep0_tycon) $
      return (metaDts, rep_insts)

genDtMeta :: (TyCon, MetaTyCons) -> TcM BagDerivStuff
genDtMeta (tc,metaDts) =
  do  loc <- getSrcSpanM
      dflags <- getDynFlags
      dClas <- tcLookupClass datatypeClassName
      let new_dfun_name clas tycon = newDFunName clas [mkTyConApp tycon []] loc
      d_dfun_name <- new_dfun_name dClas tc
      cClas <- tcLookupClass constructorClassName
      c_dfun_names <- sequence [ new_dfun_name cClas tc | _ <- metaC metaDts ]
      sClas <- tcLookupClass selectorClassName
      s_dfun_names <- sequence (map sequence [ [ new_dfun_name sClas tc 
                                               | _ <- x ] 
                                             | x <- metaS metaDts ])
      fix_env <- getFixityEnv

      let
        safeOverlap = safeLanguageOn dflags
        (dBinds,cBinds,sBinds) = mkBindsMetaD fix_env tc
        
        -- Datatype
        d_metaTycon = metaD metaDts
        d_inst = mkLocalInstance d_dfun $ NoOverlap safeOverlap
        d_binds = VanillaInst dBinds [] False
        d_dfun  = mkDictFunId d_dfun_name (tyConTyVars tc) [] dClas 
                    [ mkTyConTy d_metaTycon ]
        d_mkInst = DerivInst (InstInfo { iSpec = d_inst, iBinds = d_binds })
        
        -- Constructor
        c_metaTycons = metaC metaDts
        c_insts = [ mkLocalInstance (c_dfun c ds) $ NoOverlap safeOverlap
                  | (c, ds) <- myZip1 c_metaTycons c_dfun_names ]
        c_binds = [ VanillaInst c [] False | c <- cBinds ]
        c_dfun c dfun_name = mkDictFunId dfun_name (tyConTyVars tc) [] cClas 
                               [ mkTyConTy c ]
        c_mkInst = [ DerivInst (InstInfo { iSpec = is, iBinds = bs })
                   | (is,bs) <- myZip1 c_insts c_binds ]
        
        -- Selector
        s_metaTycons = metaS metaDts
        s_insts = map (map (\(s,ds) -> mkLocalInstance (s_dfun s ds) $
                                                  NoOverlap safeOverlap))
                    (myZip2 s_metaTycons s_dfun_names)
        s_binds = [ [ VanillaInst s [] False | s <- ss ] | ss <- sBinds ]
        s_dfun s dfun_name = mkDictFunId dfun_name (tyConTyVars tc) [] sClas
                               [ mkTyConTy s ]
        s_mkInst = map (map (\(is,bs) -> DerivInst (InstInfo { iSpec  = is
                                                             , iBinds = bs})))
                       (myZip2 s_insts s_binds)
       
        myZip1 :: [a] -> [b] -> [(a,b)]
        myZip1 l1 l2 = ASSERT (length l1 == length l2) zip l1 l2
        
        myZip2 :: [[a]] -> [[b]] -> [[(a,b)]]
        myZip2 l1 l2 =
          ASSERT (and (zipWith (>=) (map length l1) (map length l2)))
            [ zip x1 x2 | (x1,x2) <- zip l1 l2 ]
        
      return (listToBag (d_mkInst : c_mkInst ++ concat s_mkInst))
\end{code}

%************************************************************************
%*                                                                      *
\subsection{Generating representation types}
%*                                                                      *
%************************************************************************

\begin{code}
canDoGenerics :: TyCon -> Maybe SDoc
-- Called on source-code data types, to see if we should generate
-- generic functions for them.
-- Nothing == yes
-- Just s  == no, because of `s`

canDoGenerics tycon
  =  mergeErrors (
          -- We do not support datatypes with context
              (if (not (null (tyConStupidTheta tycon)))
                then (Just (ppr tycon <+> text "must not have a datatype context"))
                else Nothing)
          -- We don't like type families
            : (if (isFamilyTyCon tycon)
                then (Just (ppr tycon <+> text "must not be a family instance"))
                else Nothing)
          -- See comment below
            : (map bad_con (tyConDataCons tycon)))
  where
        -- If any of the constructor has an unboxed type as argument,
        -- then we can't build the embedding-projection pair, because
        -- it relies on instantiating *polymorphic* sum and product types
        -- at the argument types of the constructors
    bad_con dc = if (any bad_arg_type (dataConOrigArgTys dc))
                  then (Just (ppr dc <+> text "must not have unlifted or polymorphic arguments"))
                  else (if (not (isVanillaDataCon dc))
                          then (Just (ppr dc <+> text "must be a vanilla data constructor"))
                          else Nothing)

	-- Nor can we do the job if it's an existential data constructor,
	-- Nor if the args are polymorphic types (I don't think)
    bad_arg_type ty = isUnLiftedType ty || not (isTauTy ty)
    
    mergeErrors :: [Maybe SDoc] -> Maybe SDoc
    mergeErrors []           = Nothing
    mergeErrors ((Just s):t) = case mergeErrors t of
                                 Nothing -> Just s
                                 Just s' -> Just (s <> text ", and" $$ s')
    mergeErrors (Nothing :t) = mergeErrors t
\end{code}

%************************************************************************
%*									*
\subsection{Generating the RHS of a generic default method}
%*									*
%************************************************************************

\begin{code}
type US = Int	-- Local unique supply, just a plain Int
type Alt = (LPat RdrName, LHsExpr RdrName)

-- GenericKind serves to mark if a datatype derives Generic (Gen0) or
-- Generic1 (Gen1).
data GenericKind = Gen0 | Gen1

-- as above, but with a payload of "the" parameter's TyVar
data GenericKind_ = Gen0_ | Gen1_ TyVar

-- A flag to denote if a type derives only one of Generic/Generic1, or both.
-- We need this because in a type derives both the representation types should
-- use the same meta-information datatypes, instead of duplicating them.
data DeriveGeneric = One GenericKind | Both

forgetArgVar :: GenericKind_ -> GenericKind
forgetArgVar Gen0_ = Gen0
forgetArgVar (Gen1_ _) = Gen1



-- Bindings for the Generic instance
mkBindsRep :: GenericKind -> TyCon -> LHsBinds RdrName
mkBindsRep gk tycon = 
    unitBag (L loc (mkFunBind (L loc from01_RDR) from_matches))
  `unionBags`
    unitBag (L loc (mkFunBind (L loc to01_RDR) to_matches))
      where
        from_matches  = [mkSimpleHsAlt pat rhs | (pat,rhs) <- from_alts]
        to_matches    = [mkSimpleHsAlt pat rhs | (pat,rhs) <- to_alts  ]
        loc           = srcLocSpan (getSrcLoc tycon)
        datacons      = tyConDataCons tycon

        (from01_RDR, to01_RDR) = case gk of
                                   Gen0 -> (from_RDR,  to_RDR)
                                   Gen1 -> (from1_RDR, to1_RDR)

        -- Recurse over the sum first
        from_alts, to_alts :: [Alt]
        (from_alts, to_alts) = mkSum gk_ (1 :: US) tycon datacons
          where gk_ = case gk of
                  Gen0 -> Gen0_
                  Gen1 -> ASSERT (length tyvars >= 1)
                          Gen1_ (last tyvars)
                    where tyvars = tyConTyVars tycon
        
--------------------------------------------------------------------------------
-- The type instance synonym and synonym
--       type instance Rep (D a b) = Rep_D a b
--       type Rep_D a b = ...representation type for D ...
--------------------------------------------------------------------------------

tc_mkRepFamInsts ::  GenericKind     -- Gen0 or Gen1
               -> TyCon           -- The type to generate representation for
               -> MetaTyCons      -- Metadata datatypes to refer to
               -> Module          -- Used as the location of the new RepTy
               -> TcM FamInst     -- Generated representation0 coercion
tc_mkRepFamInsts gk tycon metaDts mod = 
-- Consider the example input tycon `D`, where data D a b = D_ a
  do { -- `rep` = GHC.Generics.Rep or GHC.Generics.Rep1 (type family)
       rep <- case gk of
         Gen0 -> tcLookupTyCon repTyConName
         Gen1 -> tcLookupTyCon rep1TyConName

       -- `repTy` = D1 ... (C1 ... (S1 ... (Rec0 a))) :: * -> *
     ; repTy <- tc_mkRepTy gk tycon metaDts
    
       -- `rep_name` is a name we generate for the synonym
     ; rep_name <- let mkGen = case gk of Gen0 -> mkGenR; Gen1 -> mkGen1R
                   in newGlobalBinder mod (mkGen (nameOccName (tyConName tycon)))
                        (nameSrcSpan (tyConName tycon))

     ; let -- `tyvars` = [a,b]
           tyvars  = (case gk of Gen0 -> id; Gen1 -> init) (tyConTyVars tycon)

           -- `appT` = D a b
           appT = [mkTyConApp tycon (mkTyVarTys tyvars)]
     ; return $ mkSynFamInst rep_name tyvars rep appT repTy
     }



--------------------------------------------------------------------------------
-- Type representation
--------------------------------------------------------------------------------

data ArgTyAlg a = ArgTyAlg
 { ata_par0 :: (Type -> a)
 , ata_rec0 :: (Type -> a)
 , ata_par1 :: a
 , ata_rec1 :: (Type -> a)
 , ata_comp :: (Type -> a -> a)
 }

-- | Interpret a type (as an argument to a data constructor) based on that
-- type's Generic structure. (Figure 3 from <http://dreixel.net/research/pdf/gdmh.pdf>)
argTyFold :: ArgTyAlg a -> Var -> Type -> a
argTyFold (ArgTyAlg {ata_par1 = mkPar1, ata_par0 = mkPar0,
                     ata_rec1 = mkRec1, ata_comp = mkComp, ata_rec0 = mkRec0})
  argVar = go1 where
  -- First check if the argument is a parameter.
  go1 t = case getTyVar_maybe t of
    Just t' -> if (t' == argVar)
               -- The argument is "the" parameter
               then mkPar1  -- gdmh.pdf, Figure 3, arg case 2
               -- The argument is some other type variable
               else mkPar0 t  -- gdmh.pdf, Figure 3, arg case 1
    -- The argument is not a type variable
    Nothing -> go2 t

  -- Check if the argument is an application.
  go2 t = case splitTyConApp_maybe t of
    Just (t1,t2)
      -- Is it a tycon applied to "the" parameter?
      | getTyVar_maybe lastArg == Just argVar -> 
        -- Yes, use Rec1
        mkRec1 t1App  -- gdmh.pdf, Figure 3, arg case 3

        -- Is t1 functorial?
      | isNothing (cond_functorOK_tc True t1)
                 -- And does lastArg contain variables?
                 && not (isEmptyVarSet (exactTyVarsOfType lastArg)) ->
        -- It's a composition
        mkComp t1App (go2 lastArg)  -- gdmh.pdf, Figure 3, arg case 4

      where lastArg = ASSERT (length t2 > 0)
                      last t2
            t1App   = mkTyConApp t1 (init t2)
            isNothing = maybe True (const False)

        -- Ok, I don't recognize it as anything special, so I use Rec0.
    _ -> mkRec0 t  -- gdmh.pdf, Figure 3, arg case 5




tc_mkRepTy ::  -- Gen0 or Gen1, for Rep or Rep1
               GenericKind
              -- The type to generate representation for
            -> TyCon 
               -- Metadata datatypes to refer to
            -> MetaTyCons 
               -- Generated representation0 type
            -> TcM Type
tc_mkRepTy gk tycon metaDts = 
  do
    d1    <- tcLookupTyCon d1TyConName
    c1    <- tcLookupTyCon c1TyConName
    s1    <- tcLookupTyCon s1TyConName
    nS1   <- tcLookupTyCon noSelTyConName
    rec0  <- tcLookupTyCon rec0TyConName
    rec1  <- tcLookupTyCon rec1TyConName
    par0  <- tcLookupTyCon par0TyConName
    par1  <- tcLookupTyCon par1TyConName
    u1    <- tcLookupTyCon u1TyConName
    v1    <- tcLookupTyCon v1TyConName
    plus  <- tcLookupTyCon sumTyConName
    times <- tcLookupTyCon prodTyConName
    comp  <- tcLookupTyCon compTyConName
    
    let mkSum' a b = mkTyConApp plus  [a,b]
        mkProd a b = mkTyConApp times [a,b]
        mkComp a b = mkTyConApp comp  [a,b]
        mkRec0 a   = mkTyConApp rec0  [a]
        mkRec1 a   = mkTyConApp rec1  [a]
        mkPar0 a   = mkTyConApp par0  [a]
        mkPar1     = mkTyConTy  par1
        mkD    a   = mkTyConApp d1    [metaDTyCon, sumP (tyConDataCons a)]
        mkC  i d a = mkTyConApp c1    [d, prod i (dataConOrigArgTys a) 
                                                 (null (dataConFieldLabels a))]
        -- This field has no label
        mkS True  _ a = mkTyConApp s1 [mkTyConTy nS1, a]
        -- This field has a  label
        mkS False d a = mkTyConApp s1 [d, a]
        
        -- Sums and products are done in the same way for both Rep and Rep1
        sumP [] = mkTyConTy v1
        sumP l  = ASSERT (length metaCTyCons == length l)
                    foldBal mkSum' [ mkC i d a
                                   | (d,(a,i)) <- zip metaCTyCons (zip l [0..])]
        -- The Bool is True if this constructor has labelled fields
        prod :: Int -> [Type] -> Bool -> Type
        prod i [] _ = ASSERT (length metaSTyCons > i)
                        ASSERT (length (metaSTyCons !! i) == 0)
                          mkTyConTy u1
        prod i l b  = ASSERT (length metaSTyCons > i)
                        ASSERT (length l == length (metaSTyCons !! i))
                          foldBal mkProd [ arg d t b
                                         | (d,t) <- zip (metaSTyCons !! i) l ]
        
        arg :: Type -> Type -> Bool -> Type
        arg d t b = mkS b d $ case gk of 
                      Gen0 -> recOrPar t (getTyVar_maybe t)
                      Gen1 -> argPar t
          where
            -- Argument is not a type variable, use Rec0
            recOrPar t Nothing  = mkRec0 t
            -- Argument is a type variable, use Par0
            recOrPar t (Just _) = mkPar0 t

            -- Builds argument represention for Rep1 (more complicated due to
            -- the presence of composition).
            argPar =
              let argVar = ASSERT (length (tyConTyVars tycon) >= 1)
                           last (tyConTyVars tycon)
              in argTyFold (ArgTyAlg {ata_par0 = mkPar0, ata_rec0 = mkRec0,
                                      ata_par1 = mkPar1, ata_rec1 = mkRec1,
                                      ata_comp = mkComp}) argVar
        
       
        metaDTyCon  = mkTyConTy (metaD metaDts)
        metaCTyCons = map mkTyConTy (metaC metaDts)
        metaSTyCons = map (map mkTyConTy) (metaS metaDts)
        
    return (mkD tycon)

--------------------------------------------------------------------------------
-- Meta-information
--------------------------------------------------------------------------------

data MetaTyCons = MetaTyCons { -- One meta datatype per dataype
                               metaD :: TyCon
                               -- One meta datatype per constructor
                             , metaC :: [TyCon]
                               -- One meta datatype per selector per constructor
                             , metaS :: [[TyCon]] }
                             
instance Outputable MetaTyCons where
  ppr (MetaTyCons d c s) = ppr d $$ vcat (map ppr c) $$ vcat (map ppr (concat s))
                                   
metaTyCons2TyCons :: MetaTyCons -> Bag TyCon
metaTyCons2TyCons (MetaTyCons d c s) = listToBag (d : c ++ concat s)


-- Bindings for Datatype, Constructor, and Selector instances
mkBindsMetaD :: FixityEnv -> TyCon 
             -> ( LHsBinds RdrName      -- Datatype instance
                , [LHsBinds RdrName]    -- Constructor instances
                , [[LHsBinds RdrName]]) -- Selector instances
mkBindsMetaD fix_env tycon = (dtBinds, allConBinds, allSelBinds)
      where
        mkBag l = foldr1 unionBags 
                    [ unitBag (L loc (mkFunBind (L loc name) matches)) 
                        | (name, matches) <- l ]
        dtBinds       = mkBag [ (datatypeName_RDR, dtName_matches)
                              , (moduleName_RDR, moduleName_matches)]

        allConBinds   = map conBinds datacons
        conBinds c    = mkBag ( [ (conName_RDR, conName_matches c)]
                              ++ ifElseEmpty (dataConIsInfix c)
                                   [ (conFixity_RDR, conFixity_matches c) ]
                              ++ ifElseEmpty (length (dataConFieldLabels c) > 0)
                                   [ (conIsRecord_RDR, conIsRecord_matches c) ]
                              )

        ifElseEmpty p x = if p then x else []
        fixity c      = case lookupFixity fix_env (dataConName c) of
                          Fixity n InfixL -> buildFix n leftAssocDataCon_RDR
                          Fixity n InfixR -> buildFix n rightAssocDataCon_RDR
                          Fixity n InfixN -> buildFix n notAssocDataCon_RDR
        buildFix n assoc = nlHsApps infixDataCon_RDR [nlHsVar assoc
                                                     , nlHsIntLit (toInteger n)]

        allSelBinds   = map (map selBinds) datasels
        selBinds s    = mkBag [(selName_RDR, selName_matches s)]

        loc           = srcLocSpan (getSrcLoc tycon)
        mkStringLHS s = [mkSimpleHsAlt nlWildPat (nlHsLit (mkHsString s))]
        datacons      = tyConDataCons tycon
        datasels      = map dataConFieldLabels datacons

        dtName_matches     = mkStringLHS . showPpr . nameOccName . tyConName 
                           $ tycon
        moduleName_matches = mkStringLHS . moduleNameString . moduleName 
                           . nameModule . tyConName $ tycon

        conName_matches     c = mkStringLHS . showPpr . nameOccName
                              . dataConName $ c
        conFixity_matches   c = [mkSimpleHsAlt nlWildPat (fixity c)]
        conIsRecord_matches _ = [mkSimpleHsAlt nlWildPat (nlHsVar true_RDR)]

        selName_matches     s = mkStringLHS (showPpr (nameOccName s))


--------------------------------------------------------------------------------
-- Dealing with sums
--------------------------------------------------------------------------------

mkSum :: GenericKind_ -- Gen0_ or Gen1_ argVar
      -> US          -- Base for generating unique names
      -> TyCon       -- The type constructor
      -> [DataCon]   -- The data constructors
      -> ([Alt],     -- Alternatives for the T->Trep "from" function
          [Alt])     -- Alternatives for the Trep->T "to" function

-- Datatype without any constructors
mkSum _ _ tycon [] = ([from_alt], [to_alt])
  where
    from_alt = (nlWildPat, mkM1_E (makeError errMsgFrom))
    to_alt   = (mkM1_P nlWildPat, makeError errMsgTo)
               -- These M1s are meta-information for the datatype
    makeError s = nlHsApp (nlHsVar error_RDR) (nlHsLit (mkHsString s))
    errMsgFrom = "No generic representation for empty datatype " ++ showPpr tycon
    errMsgTo = "No values for empty datatype " ++ showPpr tycon

-- Datatype with at least one constructor
mkSum gk_ us _ datacons =
 unzip [ mk1Sum gk_ us i (length datacons) d | (d,i) <- zip datacons [1..] ]

-- Build the sum for a particular constructor
mk1Sum :: GenericKind_ -- Gen0_ or Gen1_ argVar
       -> US        -- Base for generating unique names
       -> Int       -- The index of this constructor
       -> Int       -- Total number of constructors
       -> DataCon   -- The data constructor
       -> (Alt,     -- Alternative for the T->Trep "from" function
           Alt)     -- Alternative for the Trep->T "to" function
mk1Sum gk_ us i n datacon = (from_alt, to_alt)
  where
    gk = forgetArgVar gk_

    -- Existentials already excluded
    argTys = dataConOrigArgTys datacon
    n_args = dataConSourceArity datacon

    datacon_varTys = zip (map mkGenericLocal [us .. us+n_args-1]) argTys
    datacon_vars = map fst datacon_varTys
    us'          = us + n_args

    datacon_rdr  = getRdrName datacon
    
    from_alt     = (nlConVarPat datacon_rdr datacon_vars, from_alt_rhs)
    from_alt_rhs = mkM1_E (genLR_E i n (mkProd_E gk_ us' datacon_varTys))
    
    to_alt     = (mkM1_P (genLR_P i n (mkProd_P gk us' datacon_vars)), to_alt_rhs)
                 -- These M1s are meta-information for the datatype
    to_alt_rhs = case gk_ of
      Gen0_        -> nlHsVarApps datacon_rdr datacon_vars
      Gen1_ argVar -> nlHsApps datacon_rdr $ map argTo datacon_varTys
        where
          argTo (var, ty) = (\f -> f argVar ty `nlHsApp` nlHsVar var) $ argTyFold $ ArgTyAlg
            {ata_par0 = const $ nlHsVar unK1_RDR,
             ata_rec0 = const $ nlHsVar unK1_RDR,
             ata_par1 = nlHsVar unPar1_RDR,
             ata_rec1 = const $ nlHsVar unRec1_RDR,
             ata_comp = \_ cnv -> (nlHsVar fmap_RDR `nlHsApp` cnv) `nlHsCompose` nlHsVar unComp1_RDR }



-- Generates the L1/R1 sum pattern
genLR_P :: Int -> Int -> LPat RdrName -> LPat RdrName
genLR_P i n p
  | n == 0       = error "impossible"
  | n == 1       = p
  | i <= div n 2 = nlConPat l1DataCon_RDR [genLR_P i     (div n 2) p]
  | otherwise    = nlConPat r1DataCon_RDR [genLR_P (i-m) (n-m)     p]
                     where m = div n 2

-- Generates the L1/R1 sum expression
genLR_E :: Int -> Int -> LHsExpr RdrName -> LHsExpr RdrName
genLR_E i n e
  | n == 0       = error "impossible"
  | n == 1       = e
  | i <= div n 2 = nlHsVar l1DataCon_RDR `nlHsApp` genLR_E i     (div n 2) e
  | otherwise    = nlHsVar r1DataCon_RDR `nlHsApp` genLR_E (i-m) (n-m)     e
                     where m = div n 2

--------------------------------------------------------------------------------
-- Dealing with products
--------------------------------------------------------------------------------

-- Build a product expression
mkProd_E :: GenericKind_      -- Gen0_ or Gen1_ argVar
         -> US	            -- Base for unique names
         -> [(RdrName, Type)] -- List of variables matched on the lhs and their types
	 -> LHsExpr RdrName -- Resulting product expression
mkProd_E _   _ []     = mkM1_E (nlHsVar u1DataCon_RDR)
mkProd_E gk_ _ varTys = mkM1_E (foldBal prod appVars)
                     -- These M1s are meta-information for the constructor
  where
    appVars = map (wrapArg_E gk_) varTys
    prod a b = prodDataCon_RDR `nlHsApps` [a,b]

wrapArg_E :: GenericKind_ -> (RdrName, Type) -> LHsExpr RdrName
wrapArg_E Gen0_          (var, _)  = mkM1_E (k1DataCon_RDR `nlHsVarApps` [var])
                         -- This M1 is meta-information for the selector
wrapArg_E (Gen1_ argVar) (var, ty) = mkM1_E $
                         -- This M1 is meta-information for the selector
  (\f -> f argVar ty `nlHsApp` nlHsVar var) $ argTyFold $ ArgTyAlg
  {ata_par0 = const $ nlHsVar k1DataCon_RDR,
   ata_rec0 = const $ nlHsVar k1DataCon_RDR,
   ata_par1 = nlHsVar par1DataCon_RDR,
   ata_rec1 = const $ nlHsVar rec1DataCon_RDR,
   ata_comp = \_ cnv -> nlHsVar comp1DataCon_RDR `nlHsCompose` (nlHsVar fmap_RDR `nlHsApp` cnv) }



-- Build a product pattern
mkProd_P :: GenericKind   -- Gen0 or Gen1
         -> US		        -- Base for unique names
	       -> [RdrName]     -- List of variables to match
	       -> LPat RdrName  -- Resulting product pattern
mkProd_P _  _ []   = mkM1_P (nlNullaryConPat u1DataCon_RDR)
mkProd_P gk _ vars = mkM1_P (foldBal prod appVars)
                     -- These M1s are meta-information for the constructor
  where
    appVars = map (wrapArg_P gk) vars
    prod a b = prodDataCon_RDR `nlConPat` [a,b]

wrapArg_P :: GenericKind -> RdrName -> LPat RdrName
wrapArg_P Gen0 v = mkM1_P (k1DataCon_RDR `nlConVarPat` [v])
                   -- This M1 is meta-information for the selector
wrapArg_P Gen1 v = m1DataCon_RDR `nlConVarPat` [v]

mkGenericLocal :: US -> RdrName
mkGenericLocal u = mkVarUnqual (mkFastString ("g" ++ show u))

mkM1_E :: LHsExpr RdrName -> LHsExpr RdrName
mkM1_E e = nlHsVar m1DataCon_RDR `nlHsApp` e

mkM1_P :: LPat RdrName -> LPat RdrName
mkM1_P p = m1DataCon_RDR `nlConPat` [p]

nlHsCompose :: LHsExpr RdrName -> LHsExpr RdrName -> LHsExpr RdrName
nlHsCompose x y = compose_RDR `nlHsApps` [x, y]

-- | Variant of foldr1 for producing balanced lists
foldBal :: (a -> a -> a) -> [a] -> a
foldBal op = foldBal' op (error "foldBal: empty list")

foldBal' :: (a -> a -> a) -> a -> [a] -> a
foldBal' _  x []  = x
foldBal' _  _ [y] = y
foldBal' op x l   = let (a,b) = splitAt (length l `div` 2) l
                    in foldBal' op x a `op` foldBal' op x b

\end{code}
