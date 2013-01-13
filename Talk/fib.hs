module Main where
import Data.Int

add x y = if y == 0 then x else 1 + (add x (y-1))

fib :: Int64 -> Int64 
fib x = if x == 0 || x==1 then 1 else (fib (x-1)) + (fib (x-2))

main =
  print (fib 38)