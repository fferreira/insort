module ExSortSimple where

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
  sort (x :: l) = insert x (sort l)

  data ordered' : list A -> Set where
    [] : ordered' []
    _::[] : ∀ x -> ordered' (x :: [])
    _::_ : ∀{x y ys} -> x ≤ y -> ordered' (y :: ys) -> ordered' (x :: y :: ys)

  data _≤ordered_ : A -> list A -> Set where
    ≤nil : ∀{x} -> x ≤ordered []
    ≤head : ∀{x y ys} -> x ≤ y {--> x ≤* ys -} -> x ≤ordered (y :: ys)

  data ordered : list A -> Set where
    [] : ordered []
    _::_ : ∀{x xs} -> x ≤ordered xs -> ordered xs -> ordered (x :: xs)

  lemma : ∀{x y l} -> y ≤ x -> y ≤ordered l -> y ≤ordered insert x l
  lemma y<x ≤nil = ≤head y<x
  lemma {x = x} y<x (≤head {y = y₁} x₁ ) with compare x y₁
  lemma y<x (≤head x₁) | leq x≤y = ≤head y<x
  lemma y<x (≤head x₁ ) | geq y≤x = ≤head x₁ -- x₁ :: (lemma y<x ?)

  mutual
    p : ∀ l -> ordered (sort l)
    p [] = []
    p (x :: l) = p' x (sort l) (p l)

    p' : ∀ x l → ordered l -> ordered (insert x l)
    p' x [] ps = ≤nil :: ps
    p' x (y :: l) ps with compare x y
    p' x (y :: l) (x₁ :: ps) | leq x≤y = (≤head x≤y ) :: (x₁ :: ps)
    p' x (y :: l) (x₁ :: ps) | geq y≤x = lemma y≤x x₁ :: (p' x l ps)
