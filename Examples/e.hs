module Main where
import Prelude hiding (tail, and, or, abs, signum)
import Data.Int

fix f = f (fix f)

cons x xs =
  \i -> if i == 0 then x else xs (i-1)

head xs = xs 0

tail xs = \i -> xs (i+1)

aux = fix (\a -> \n -> cons 1 (cons n (cons 1 (a (n+2)))))

eContFrac = cons 2 (aux 2)

signum x = if x < 0 then 0-1 else if x == 0 then 0 else 1
abs x =if x < 0 then 0-x else x
not x = if x then False else True
and x y =
    if x then (if y then True else False) else False
or x y = 
  if x then True else y

ratTrans =
  fix (\ratTrans -> \av bv cv dv xs iv ->
             let qv = if dv == 0 then 1 else bv `div` dv in
             if and (or (signum cv == signum dv) (abs cv < abs dv)) 
                      (and ((cv+dv)*qv < av+bv+1) 
                           (av+bv < (cv+dv)*qv + (cv+dv))) 
             then
                  (if iv == 0 then qv else 
                      ratTrans cv dv (av-qv*cv) (bv-qv*dv) xs (iv-1))
             else 
                 let xv = xs 0 in 
                 ratTrans bv (av+xv*bv) dv (cv+xv*dv) (tail xs) iv)

toDigits = 
  fix (\toDigits -> \l ->
   \i -> if i == 0 then l i else toDigits (ratTrans 10 0 0 1 (tail l)) (i-1))

e :: Int64 -> Int64
e = toDigits eContFrac

main =
   mapM print [e i | i<-[0..9]]

