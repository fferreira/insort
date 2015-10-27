module NatSort where

open import Nat hiding (compare)
open import MSort

module M = Ord Nat.ℕ Nat._≤_

compare : (x y : Nat.ℕ) -> M.cmp x y
compare z _ = M.leq Nat.z≤n
compare (s x) z = M.geq z≤n
compare (s x) (s y) with compare x y
compare (s x) (s y) | M.leq x≤y = M.leq (s≤s x≤y)
compare (s x) (s y) | M.geq y≤x = M.geq (s≤s y≤x)

open module MC = M.Compare compare Nat.x≤x

v = 2 :: 3 :: 1 :: 6 :: 4 :: 5 :: []

ov = sort-ordered-vec v
