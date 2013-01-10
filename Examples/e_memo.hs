module Main where
import Prelude
import Data.Int
import System.IO

aux n = 1:n:1:(aux (n+2))

eContFrac =  2:(aux 2)

ratTrans av bv cv dv xs =
             if ((signum cv == signum dv) || (abs cv < abs dv)) &&
                      (((cv+dv)*(bv `div` dv) < av+bv+1) &&
                           (av+bv < (cv+dv)*(bv `div` dv) + (cv+dv))) 
             then
                (bv `div` dv) : (ratTrans cv dv (av-(bv `div` dv)*cv) (bv-(bv `div` dv)*dv) xs)
             else 
                let xv:tl = xs in
                 ratTrans bv (av+xv*bv) dv (cv+xv*dv) tl

toDigits (h:t) = h:(toDigits (ratTrans 10 0 0 1 t))

e :: [Int64]
e = take 500 (toDigits eContFrac)

main =
   mapM (\i -> do {putStr (show i); hFlush stdout}) e

