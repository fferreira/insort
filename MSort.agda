module MSort where

open import Nat

data vec (A : Set) : ℕ -> Set where
  [] : vec A z
  _::_ : ∀{n} -> A -> vec A n -> vec A (s n)

infixr 9 _::_

module Ord (A : Set) (_≤_ : A -> A -> Set) where
  data ord-list : (bound : A) -> Set where
    [] : ∀{b} -> ord-list b
    cons : ∀{b} -> (x : A) -> x ≤ b -> ord-list b -> ord-list x

  data ord-vec : (n : ℕ) -> (b : A) -> Set where
    [] : ∀{b} -> ord-vec z b
    cons : ∀{n b} -> (x : A) -> x ≤ b -> ord-vec n b -> ord-vec (s n) x

  data cmp (x y : A) : Set where
    leq : (x≤y : x ≤ y) -> cmp x y
    geq : (y≤x : y ≤ x) -> cmp x y

  module Compare (compare : ∀ a b -> cmp a b) (x≤x : ∀ {x} → x ≤ x) where

    ins-geq : ∀ {b n} x → b ≤ x → ord-vec n b → ord-vec (s n) b
    ins-geq x b≤x [] = cons _ b≤x []
    ins-geq x b≤x (cons {b = b} y y≤b v) with compare x b
    ins-geq x b≤x (cons y y≤b v) | leq x≤y = cons y b≤x (cons x x≤y v)
    ins-geq x b≤x (cons y y≤b v) | geq y≤x = cons y y≤b (ins-geq x y≤x v)

    min : A -> A -> A
    min x y with compare x y
    min x y | leq x≤y = x
    min x y | geq y≤x = y

    ins : ∀{n b} -> (x : A) -> ord-vec n b -> ord-vec (s n) (min x b)
    ins {b = b} x v with compare x b
    ins x v | leq x≤b = cons x x≤b v
    ins x v | geq b≤x = ins-geq x b≤x v

    min-vec : ∀{n} -> vec A (s n) -> A
    min-vec (x :: []) = x
    min-vec (x :: x₁ :: v) = min x (min-vec (x₁ :: v))

    unary : ∀ x → ord-vec (s z) x
    unary x = cons x x≤x []

    sort-ordered-vec : ∀{n} -> (v : vec A (s n)) -> ord-vec (s n) (min-vec v)
    sort-ordered-vec (x :: []) = unary x
    sort-ordered-vec (x :: x₁ :: v) = ins x (sort-ordered-vec (x₁ :: v))

    copies : ∀ n b → ord-vec n b
    copies z b = []
    copies (s n) b = cons b x≤x (copies n b)

    non-sort : ∀{n} -> (v : vec A (s n)) -> ord-vec (s n) (min-vec v)
    non-sort {n} v with min-vec v
    ... | bound = copies (s n) bound
