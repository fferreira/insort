module Eq where


data _≡_ {l} {A : Set l} (x : A) : A → Set l where
 refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

cong : {A : Set} {a b : A} (f : A -> A) → a ≡ b → (f a) ≡ (f b)
cong f refl = refl

sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl
