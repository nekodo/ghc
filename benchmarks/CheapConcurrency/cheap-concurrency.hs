{-# OPTIONS -fglasgow-exts -O2 -optc-O3 #-}
-- $Id: message-ghc-2.code,v 1.27 2006/01/08 22:44:56 igouy-guest Exp $
-- The Great Computer Language Shootout
-- http://shootout.alioth.debian.org/
-- Contributed by Einar Karttunen
-- Modified by Simon Marlow and Don Stewart

import Control.Concurrent
import Control.Monad
import System

thread im om = do (x::Int) <- takeMVar im; putMVar om $! x+1; thread im om

spawn  c  _  = do n <- newEmptyMVar; forkIO (thread c n); return n

main = do n <- getArgs >>= readIO . head
          s <- newEmptyMVar
          f <- newEmptyMVar
          e <- foldM spawn s [1..500]
          forkIO $ replicateM n (takeMVar e) >>= putMVar f . sum
          replicateM n (putMVar s 0)
          takeMVar f >>= print
