{
module ParserCore ( parseCore ) where

import IfaceSyn
import ForeignCall
import RdrHsSyn
import TcIface ( tcIfaceKind )
import HsSyn
import RdrName
import OccName
import Name( nameOccName, nameModuleName )
import Module
import ParserCoreUtils
import LexCore
import Literal
import BasicTypes
import SrcLoc
import TysPrim( wordPrimTyCon, intPrimTyCon, charPrimTyCon, 
		floatPrimTyCon, doublePrimTyCon, addrPrimTyCon )
import TyCon ( TyCon, tyConName )
import FastString
import Outputable

#include "../HsVersions.h"

}

%name parseCore
%tokentype { Token }

%token
 '%module'	{ TKmodule }
 '%data'	{ TKdata }
 '%newtype'	{ TKnewtype }
 '%forall'	{ TKforall }
 '%rec'		{ TKrec }
 '%let'		{ TKlet }
 '%in'		{ TKin }
 '%case'	{ TKcase }
 '%of'		{ TKof }
 '%coerce'	{ TKcoerce }
 '%note'	{ TKnote }
 '%external'	{ TKexternal }
 '%_'		{ TKwild }
 '('		{ TKoparen }
 ')'		{ TKcparen }
 '{'		{ TKobrace }
 '}'		{ TKcbrace }
 '#' 		{ TKhash}
 '='		{ TKeq }
 '::'		{ TKcoloncolon }
 '*'		{ TKstar }
 '->'		{ TKrarrow }
 '\\'		{ TKlambda}
 '@'		{ TKat }
 '.'		{ TKdot }
 '?'		{ TKquestion}
 ';'            { TKsemicolon }
 NAME		{ TKname $$ }
 CNAME 		{ TKcname $$ }
 INTEGER	{ TKinteger $$ }
 RATIONAL	{ TKrational $$ }
 STRING		{ TKstring $$ }
 CHAR		{ TKchar $$ }

%monad { P } { thenP } { returnP }
%lexer { lexer } { TKEOF }

%%

module	:: { HsExtCore RdrName }
         : '%module' modid tdefs vdefgs
		{ HsExtCore (mkHomeModule $2) $3 $4 }

modid	:: { ModuleName }
	: CNAME	                 { mkSysModuleNameFS (mkFastString $1) }

-------------------------------------------------------------
--     Type and newtype declarations are in HsSyn syntax

tdefs	:: { [TyClDecl RdrName] }
	: {- empty -}	{[]}
	| tdef ';' tdefs	{$1:$3}

tdef	:: { TyClDecl RdrName }
	: '%data' q_tc_name tv_bndrs '=' '{' cons1 '}'
                { mkTyData DataType ([], ifaceExtRdrName $2, map toHsTvBndr $3) $6 Nothing noSrcLoc }
	| '%newtype' q_tc_name tv_bndrs trep 
		{ let tc_rdr = ifaceExtRdrName $2 in
                  mkTyData NewType ([], tc_rdr, map toHsTvBndr $3) ($4 (rdrNameOcc tc_rdr)) Nothing noSrcLoc }

-- For a newtype we have to invent a fake data constructor name
-- It doesn't matter what it is, because it won't be used
trep    :: { OccName -> [ConDecl RdrName] }
        : {- empty -}   { (\ tc_occ -> []) }
        | '=' ty        { (\ tc_occ -> let { dc_name  = mkRdrUnqual (setOccNameSpace dataName tc_occ) ;
			                      con_info = PrefixCon [unbangedType (toHsType $2)] }
			                in [ConDecl dc_name [] [] con_info noSrcLoc]) }

cons1	:: { [ConDecl RdrName] }
	: con		{ [$1] }
	| con ';' cons1	{ $1:$3 }

con	:: { ConDecl RdrName }
	: d_pat_occ attv_bndrs hs_atys 
		{ ConDecl (mkRdrUnqual $1) $2 [] (PrefixCon (map unbangedType $3)) noSrcLoc}

attv_bndrs :: { [HsTyVarBndr RdrName] }
	: {- empty -} 	         { [] }
	| '@' tv_bndr attv_bndrs {  toHsTvBndr $2 : $3 }

hs_atys :: { [HsType RdrName] }
         : atys               { map toHsType $1 }


---------------------------------------
--                 Types
---------------------------------------

atys	:: { [IfaceType] }
	: {- empty -}   { [] }
	| aty atys      { $1:$2 }

aty	:: { IfaceType }
	: tv_occ    { IfaceTyVar $1 }
	| q_tc_name  { IfaceTyConApp (IfaceTc $1) [] }
	| '(' ty ')' { $2 }

bty	:: { IfaceType }
	: tv_occ atys    { foldl IfaceAppTy (IfaceTyVar $1) $2 }
        | q_tc_name atys  { IfaceTyConApp (IfaceTc $1) $2 }

ty	:: { IfaceType }
	: bty	                     { $1 }
	| bty '->' ty                { IfaceFunTy $1 $3 }
	| '%forall' tv_bndrs '.' ty  { foldr IfaceForAllTy $4 $2 }

----------------------------------------------
--        Bindings are in Iface syntax

vdefgs	:: { [IfaceBinding] }
	: {- empty -}	        { [] }
	| let_bind ';' vdefgs	{ $1 : $3 }

let_bind :: { IfaceBinding }
	: '%rec' '{' vdefs1 '}' { IfaceRec $3 }
	|  vdef                 { let (b,r) = $1
				  in IfaceNonRec b r }

vdefs1	:: { [(IfaceIdBndr, IfaceExpr)] }
	: vdef		        { [$1] }
	| vdef ';' vdefs1       { $1:$3 }

vdef	:: { (IfaceIdBndr, IfaceExpr) }
	: qd_occ '::' ty '=' exp { (($1, $3), $5) }
  -- NB: qd_occ includes data constructors, because
  --     we allow data-constructor wrappers at top level
  -- But we discard the module name, because it must be the
  -- same as the module being compiled, and Iface syntax only
  -- has OccNames in binding positions

qd_occ :: { OccName }
        : var_occ { $1 }
        | d_occ   { $1 }

---------------------------------------
--  Binders
bndr	:: { IfaceBndr }
        : '@' tv_bndr 	{ IfaceTvBndr $2 }
	| id_bndr	{ IfaceIdBndr $1 }

bndrs 	:: { [IfaceBndr] }
	: bndr		{ [$1] }
	| bndr bndrs	{ $1:$2 }

id_bndr	:: { IfaceIdBndr }
	: '(' var_occ '::' ty ')'	{ ($2,$4) }

id_bndrs :: { [IfaceIdBndr] }
	: {-empty -}    	{ [] }
	| id_bndr id_bndrs	{ $1:$2 }

tv_bndr	:: { IfaceTvBndr }
	:  tv_occ                    { ($1, IfaceLiftedTypeKind) }
	|  '(' tv_occ '::' akind ')' { ($2, $4) }

tv_bndrs 	:: { [IfaceTvBndr] }
	: {- empty -}	{ [] }
	| tv_bndr tv_bndrs	{ $1:$2 }

akind	:: { IfaceKind }
	: '*' 		   { IfaceLiftedTypeKind   }	
	| '#'		   { IfaceUnliftedTypeKind }
	| '?'		   { IfaceOpenTypeKind     }
        | '(' kind ')'	   { $2 }

kind 	:: { IfaceKind }
	: akind 	   { $1 }
	| akind '->' kind  { IfaceFunKind $1 $3 }

-----------------------------------------
--             Expressions

aexp    :: { IfaceExpr }
	: var_occ	         { IfaceLcl $1 }
	| modid '.' qd_occ	 { IfaceExt (ExtPkg $1 $3) }
	| lit		{ IfaceLit $1 }
	| '(' exp ')' 	{ $2 }

fexp	:: { IfaceExpr }
	: fexp aexp	{ IfaceApp $1 $2 }
	| fexp '@' aty	{ IfaceApp $1 (IfaceType $3) }
	| aexp		{ $1 }

exp	:: { IfaceExpr }
	: fexp		              { $1 }
	| '\\' bndrs '->' exp 	      { foldr IfaceLam $4 $2 }
	| '%let' let_bind '%in' exp   { IfaceLet $2 $4 }
	| '%case' aexp '%of' id_bndr
	  '{' alts1 '}'		      { IfaceCase $2 (fst $4) $6 }
	| '%coerce' aty exp   	      { IfaceNote (IfaceCoerce $2) $3 }
	| '%note' STRING exp 	   
	    { case $2 of
	       --"SCC"      -> IfaceNote (IfaceSCC "scc") $3
	       "InlineCall" -> IfaceNote IfaceInlineCall $3
	       "InlineMe"   -> IfaceNote IfaceInlineMe $3
            }
        | '%external' STRING aty   { IfaceFCall (ForeignCall.CCall 
                                                    (CCallSpec (StaticTarget (mkFastString $2)) 
                                                               CCallConv (PlaySafe False))) 
                                                 $3 }

alts1	:: { [IfaceAlt] }
	: alt		{ [$1] }
	| alt ';' alts1	{ $1:$3 }

alt	:: { IfaceAlt }
	: modid '.' d_pat_occ bndrs '->' exp 
		{ (IfaceDataAlt $3, map ifaceBndrName $4, $6) } 
                       -- The external syntax currently includes the types of the
		       -- the args, but they aren't needed internally
                       -- Nor is the module qualifier
	| lit '->' exp
		{ (IfaceLitAlt $1, [], $3) }
	| '%_' '->' exp
		{ (IfaceDefault, [], $3) }

lit	:: { Literal }
	: '(' INTEGER '::' aty ')'	{ convIntLit $2 $4 }
	| '(' RATIONAL '::' aty ')'	{ convRatLit $2 $4 }
	| '(' CHAR '::' aty ')'		{ MachChar (fromEnum $2) }
	| '(' STRING '::' aty ')'	{ MachStr (mkFastString $2) }

tv_occ	:: { OccName }
	: NAME	{ mkSysOcc tvName $1 }

var_occ	:: { OccName }
	: NAME	{ mkSysOcc varName $1 }


-- Type constructor
q_tc_name	:: { IfaceExtName }
        : modid '.' CNAME	{ ExtPkg $1 (mkSysOcc tcName $3) }

-- Data constructor in a pattern or data type declaration; use the dataName, 
-- because that's what we expect in Core case patterns
d_pat_occ :: { OccName }
        : CNAME      { mkSysOcc dataName $1 }

-- Data constructor occurrence in an expression;
-- use the varName because that's the worker Id
d_occ :: { OccName }
       : CNAME { mkSysOcc varName $1 }

{

ifaceBndrName (IfaceIdBndr (n,_)) = n
ifaceBndrName (IfaceTvBndr (n,_)) = n

convIntLit :: Integer -> IfaceType -> Literal
convIntLit i (IfaceTyConApp tc [])
  | tc `eqTc` intPrimTyCon  = MachInt  i  
  | tc `eqTc` wordPrimTyCon = MachWord i
  | tc `eqTc` charPrimTyCon = MachChar (fromInteger i)
  | tc `eqTc` addrPrimTyCon && i == 0 = MachNullAddr
convIntLit i aty
  = pprPanic "Unknown integer literal type" (ppr aty)

convRatLit :: Rational -> IfaceType -> Literal
convRatLit r (IfaceTyConApp tc [])
  | tc `eqTc` floatPrimTyCon  = MachFloat  r
  | tc `eqTc` doublePrimTyCon = MachDouble r
convRatLit i aty
  = pprPanic "Unknown rational literal type" (ppr aty)

eqTc :: IfaceTyCon -> TyCon -> Bool   -- Ugh!
eqTc (IfaceTc (ExtPkg mod occ)) tycon
  = mod == nameModuleName nm && occ == nameOccName nm
  where
    nm = tyConName tycon

-- Tiresomely, we have to generate both HsTypes (in type/class decls) 
-- and IfaceTypes (in Core expressions).  So we parse them as IfaceTypes,
-- and convert to HsTypes here.  But the IfaceTypes we can see here
-- are very limited (see the productions for 'ty', so the translation
-- isn't hard
toHsType :: IfaceType -> HsType RdrName
toHsType (IfaceTyVar v)        		 = HsTyVar (mkRdrUnqual v)
toHsType (IfaceAppTy t1 t2)    		 = HsAppTy (toHsType t1) (toHsType t2)
toHsType (IfaceFunTy t1 t2)    		 = HsFunTy (toHsType t1) (toHsType t2)
toHsType (IfaceTyConApp (IfaceTc tc) ts) = foldl HsAppTy (HsTyVar (ifaceExtRdrName tc)) (map toHsType ts) 
toHsType (IfaceForAllTy tv t)            = add_forall (toHsTvBndr tv) (toHsType t)

toHsTvBndr :: IfaceTvBndr -> HsTyVarBndr RdrName
toHsTvBndr (tv,k) = KindedTyVar (mkRdrUnqual tv) (tcIfaceKind k)

ifaceExtRdrName :: IfaceExtName -> RdrName
ifaceExtRdrName (ExtPkg mod occ) = mkOrig mod occ
ifaceExtRdrName other = pprPanic "ParserCore.ifaceExtRdrName" (ppr other)

add_forall tv (HsForAllTy exp tvs cxt t) = HsForAllTy exp (tv:tvs) cxt t
add_forall tv t                          = HsForAllTy Explicit [tv] [] t
  
happyError :: P a 
happyError s l = failP (show l ++ ": Parse error\n") (take 100 s) l
}

