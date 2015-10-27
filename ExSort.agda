module ExSort2 where

open import Eq

data cmp {A : Set} (x y : A) {_≤_ : A -> A -> Set} : Set where
    leq : (x≤y : x ≤ y) -> cmp x y
    geq : (y≤x : y ≤ x) -> cmp x y

module Ord (A : Set) (_≤_ : A -> A -> Set) (trans : ∀{x y z} -> x ≤ y -> y ≤ z -> x ≤ z) (compare : ∀ a b -> cmp a b {_≤_}) where

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
  sort (x :: l) = insert x (sort l)

  data sorted' : list A -> Set where
    [] : sorted' []
    _::[] : ∀ x -> sorted' (x :: [])
    _::_ : ∀{x y ys} -> x ≤ y -> sorted' (y :: ys) -> sorted' (x :: y :: ys)

  data _≤*_ : A -> list A -> Set where
    [] : ∀{x} -> x ≤* []
    _::_ : ∀{x y ys} -> x ≤ y -> x ≤* ys -> x ≤* (y :: ys)

  data sorted : list A -> Set where
    [] : sorted []
    _::_ : ∀{x xs} -> x ≤* xs -> sorted xs -> sorted (x :: xs)

  lemma : ∀{x y l} -> y ≤ x -> y ≤* l -> y ≤* insert x l
  lemma y<x [] = y<x :: []
  lemma {x = x} y<x (_::_ {y = y₁} x₁ ps) with compare x y₁
  lemma y<x (x₁ :: ps) | leq x≤y = y<x :: x₁ :: ps
  lemma y<x (x₁ :: ps ) | geq y≤x = x₁ :: lemma y<x ps

  lemma-1 : ∀{x y l} -> x ≤ y -> y ≤* l -> x ≤* l
  lemma-1 x<y [] = []
  lemma-1 x<y (x₁ :: y<l) = trans x<y x₁ :: (lemma-1 x<y y<l)

  mutual
    p : ∀ l -> sorted (sort l)
    p [] = []
    p (x :: l) = p' x (sort l) (p l)

    p' : ∀ x l → sorted l -> sorted (insert x l)
    p' x [] ps = [] :: ps
    p' x (y :: l) ps with compare x y
    p' x (y :: l) (x₁ :: ps) | leq x≤y = (x≤y :: lemma-1 x≤y x₁) :: (x₁ :: ps)
    p' x (y :: l) (x₁ :: ps) | geq y≤x = lemma y≤x x₁ :: (p' x l ps)
