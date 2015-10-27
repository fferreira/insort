module ExSort where

open import Nat renaming (compare to compareℕ)
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

  -- data ordered' : list A -> Set where
  --   [] : ordered' []
  --   _::[] : ∀ x -> ordered' (x :: [])
  --   _::_ : ∀{x y ys} -> x ≤ y -> ordered' (y :: ys) -> ordered' (x :: y :: ys)

  data _≤*_ : A -> list A -> Set where
    [] : ∀{x} -> x ≤* []
    _::_ : ∀{x y ys} -> x ≤ y -> x ≤* ys -> x ≤* (y :: ys)

  data ordered : list A -> Set where
    [] : ordered []
    _::_ : ∀{x xs} -> x ≤* xs -> ordered xs -> ordered (x :: xs)

  lemma : ∀{x y l} -> y ≤ x -> y ≤* l -> y ≤* insert x l
  lemma y<x [] = y<x :: []
  lemma {x = x} y<x (_::_ {y = y₁} x₁ ps) with compare x y₁
  lemma y<x (x₁ :: ps) | leq x≤y = y<x :: x₁ :: ps
  lemma y<x (x₁ :: ps ) | geq y≤x = x₁ :: lemma y<x ps

  lemma-1 : ∀{x y l} -> x ≤ y -> y ≤* l -> x ≤* l
  lemma-1 x<y [] = []
  lemma-1 x<y (x₁ :: y<l) = trans x<y x₁ :: (lemma-1 x<y y<l)

  mutual
    p : ∀ l -> ordered (sort l)
    p [] = []
    p (x :: l) = p' x (sort l) (p l)

    p' : ∀ x l → ordered l -> ordered (insert x l)
    p' x [] ps = [] :: ps
    p' x (y :: l) ps with compare x y
    p' x (y :: l) (x₁ :: ps) | leq x≤y = (x≤y :: lemma-1 x≤y x₁) :: (x₁ :: ps)
    p' x (y :: l) (x₁ :: ps) | geq y≤x = lemma y≤x x₁ :: (p' x l ps)

  len : (l : list A) -> ℕ
  len [] = z
  len (_ :: l) = s (len l)

  lemma-2 : ∀{x} l -> s (len l) ≡ len (insert x l)
  lemma-2 [] = refl
  lemma-2 {x} (y :: l) with compare x y
  lemma-2 (y :: l) | leq x≤y = refl
  lemma-2 (y :: l) | geq y≤x = cong s (lemma-2 l)

  len-p : ∀ l -> len l ≡ len (sort l)
  len-p [] = refl
  len-p (x :: l) rewrite len-p l = lemma-2 (sort l)
