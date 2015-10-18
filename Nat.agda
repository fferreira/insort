module Nat where

data ℕ : Set where
  z : ℕ
  s : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}

data _≤_ : ℕ -> ℕ -> Set where
  z≤n : ∀{n} -> z ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → s m ≤ s n

x≤x : ∀{x} -> x ≤ x
x≤x {z} = z≤n
x≤x {s x} = s≤s x≤x

-- data cmp (x y : ℕ) : Set where
--   leq : (x≤y : x ≤ y) -> cmp x y
--   geq : (y≤x : y ≤ x) -> cmp x y

-- compare : (x y : ℕ) -> cmp x y
-- compare z _ = leq z≤n
-- compare (s x) z = geq z≤n
-- compare (s x) (s y) with compare x y
-- compare (s x) (s y) | leq x≤y = leq (s≤s x≤y)
-- compare (s x) (s y) | geq y≤x = geq (s≤s y≤x)

-- min : ℕ -> ℕ -> ℕ
-- min x y with compare x y
-- min x y | leq x≤y = x
-- min x y | geq y≤x = y
