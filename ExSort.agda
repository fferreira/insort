module ExSort where

open import Eq

data cmp {A : Set} (x y : A) {_≤_ : A -> A -> Set} : Set where
    leq : (x≤y : x ≤ y) -> cmp x y
    geq : (y≤x : y ≤ x) -> cmp x y

module Ord (A : Set) (_≤_ : A -> A -> Set) (compare : ∀ a b -> cmp a b {_≤_}) where

  data list (A : Set) : Set where
    [] : list A
    _::_ : A -> list A -> list A

  infixr 9 _::_

  insert : A -> list A -> list A
  insert x [] = x :: []
  insert x (y :: l) with compare x y
  insert x (y :: l) | leq x≤y = x :: y :: l
  insert x (y :: l) | geq y≤x = y :: insert x l

  sort : list A -> list A
  sort [] = []
  sort (x :: l) = insert x l

  data sorted : list A -> Set where
    [] : sorted []
    _::[] : ∀ x -> sorted (x :: [])
    _::_ : ∀{x y ys} -> x ≤ y -> sorted (y :: ys) -> sorted (x :: y :: ys)

  mutual
    p : ∀ l -> sorted (sort l)
    p [] = []
    p (x :: l) = p' x l (p l)

    p' : ∀ x l → sorted (sort l) -> sorted (insert x l)
    p' x [] ps = x ::[]
    p' x (y :: l) ps with compare x y
    p' x (y :: l) ps | leq x≤y = x≤y :: {!!}
    p' x (y :: l) ps | geq y≤x = {!!}
