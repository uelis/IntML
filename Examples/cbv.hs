module Main where
import Data.Int

{-
data Path = L Path | R Path | T deriving Show
branch (p:ps) = p : p : branch ps

paths () = let r = 0 : branch r in r

large () = take 4000000 (paths ())

val !n = \k -> k n
add k = k (\n -> \k1-> k1 (\m -> \k2 -> k2 (n:m)))
app e1 e2 = \k -> e1 (\x1 -> e2 (\x2 -> x1 x2 k))
add2 n1 n2 = app (app add n1) n2
test = 
  app (val (\y -> val 3)) (val (large ()))
  \k -> (\y -> val 3) (large ()) k
-}

strict 0 = 0
strict n = n 

fix = \f -> f (fix f)

val = \n -> \k -> k n
add = \k -> k (\n -> \k1 -> 
                          k1 (\m -> \k2 -> 
                              let s = strict (n + m) in
                                k2 s))
app = \e1 -> \e2 -> \k -> e1 (\x1 -> e2 (\x2 -> x1 x2 k))
mem = \f -> \k -> let n = f (\r -> r) in k n

step1 =
   \f ->
     val (\x0 -> mem (\k ->
          let x = strict x0 in
          if x < 2 then val (1 ::Int64) k else
              app (app add (f (x - 1))) (f (x - 2)) k 
         ))

fixv = \step -> fix (\a -> step (\x -> \k -> a (\b -> b x k))) 

tt = app (fixv step1) (val (38 :: Int64))
testfib = tt (\r -> r) 
main =
  print (testfib)


