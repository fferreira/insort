module NatPrime where

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

trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
trans z≤n n = z≤n
trans (s≤s m₂) (s≤s n₁) = s≤s (trans m₂ n₁)

data cmpℕ (x y : ℕ) : Set where
  leq : (x≤y : x ≤ y) -> cmpℕ x y
  geq : (y≤x : y ≤ x) -> cmpℕ x y

compare : (x y : ℕ) -> cmpℕ x y
compare z y = leq z≤n
compare (s x) z = geq z≤n
compare (s x) (s y) with compare x y
compare (s x) (s y) | leq x≤y = leq (s≤s x≤y)
compare (s x) (s y) | geq y≤x = geq (s≤s y≤x)

min : ℕ -> ℕ -> ℕ
min x y with compare x y
min x y | leq x≤y = x
min x y | geq y≤x = y

-- min : ℕ -> ℕ -> ℕ
-- min z y = z
-- min (s x) z = z
-- min (s x) (s y) = s (min x y)

{-
≤min : ∀ {x y b} → x ≤ y → x ≤ b → x ≤ min y b
≤min z≤n z≤n = z≤n
≤min (s≤s x) (s≤s y) = s≤s (≤min x y)

smin≤mins : ∀ n₁ n₂ → s (min n₁ n₂) ≤ min (s n₁) (s n₂)
smin≤mins m n = s≤s x≤x
-}
