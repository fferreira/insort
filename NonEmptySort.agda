module NonEmptySort where

open import Nat
open import Eq

infixr 9 _::_

--- length preserving

data vec (A : Set) : ℕ -> Set where
  [] : vec A z
  _::_ : ∀{n} -> A -> vec A n -> vec A (s n)

--- order preserving

data ord-vec : (n : ℕ) -> (h : ℕ) -> Set where
  [_] : (h : ℕ) -> ord-vec z h
  cons : ∀{n h} -> (x : ℕ) -> x ≤ h -> ord-vec n h -> ord-vec (s n) x

to-vec : ∀{n b} -> ord-vec n b -> vec ℕ (s n)
to-vec [ h ] = h :: []
to-vec (cons x _ v) = x :: (to-vec v)

lemma : ∀ {x h} → x ≤ h → min x h ≤ h
lemma z≤n = z≤n
lemma (s≤s w) = s≤s (lemma w)

lemma-1 : ∀{x h} -> x ≤ h -> min x h ≡ x
lemma-1 z≤n = refl
lemma-1 (s≤s w) = cong s (lemma-1 w)

lemma-1-5 : ∀ x y -> min x y ≡ min y x
lemma-1-5 z z = refl
lemma-1-5 z (s y) = refl
lemma-1-5 (s x) z = refl
lemma-1-5 (s x) (s y) = cong s (lemma-1-5 x y)

lemma-2 : ∀{x h} -> h ≤ x -> min x h ≡ h
lemma-2 {x} {h} w rewrite lemma-1-5 x h = lemma-1 w

lemma-3 : ∀ {x y z} →  x ≤ z -> x ≤ y → x ≤ (min y z)
lemma-3 z≤n r' = z≤n
lemma-3 (s≤s r) (s≤s r') = s≤s (lemma-3 r r')

mutual
  ins-geq : ∀ {n h} x -> h ≤ x -> ord-vec n h -> ord-vec (s n) h
  ins-geq x h≤x [ h ] = cons h h≤x [ x ]
  ins-geq x h≤x (cons h h≤hv v) = cons h (lemma-3 h≤hv h≤x) (ins x v)

  ins : ∀{n h} -> (x : ℕ) -> ord-vec n h -> ord-vec (s n) (min x h)
  ins x [ h ] with compare x h
  ins x [ h ] | leq x≤h rewrite lemma-1 x≤h = cons x x≤h [ h ]
  ins x [ h ] | geq h≤x rewrite lemma-2 h≤x = cons h h≤x [ x ]
  ins x (cons h h≤hv v) with compare x h
  ins x (cons h h≤hv v) | leq x≤y rewrite lemma-1 x≤y = cons x x≤y (cons h h≤hv v)
  ins x (cons h h≤hv v) | geq y≤x rewrite lemma-2 y≤x = ins-geq x y≤x (cons h h≤hv v)

min-vec : ∀{n} -> vec ℕ (s n) -> ℕ
min-vec (x :: []) = x
min-vec (x :: x₁ :: v) = min x (min-vec (x₁ :: v))

sort-ordered-vec : ∀{n} -> (v : vec ℕ (s n)) -> ord-vec n (min-vec v)
sort-ordered-vec (x :: []) = [ x ]
sort-ordered-vec (x :: x₁ :: v) = ins x (sort-ordered-vec (x₁ :: v))

copies : ∀ n b → ord-vec n b
copies z b = [ b ]
copies (s n) b = cons b x≤x (copies n b)

non-sort : ∀{n} -> (v : vec ℕ (s n)) -> ord-vec (s n) (min-vec v)
non-sort {n} v with min-vec v
... | bound = copies (s n) bound

v : vec ℕ 7
v = 2 :: 3 :: 1 :: 6 :: 4 :: 5 :: 1 :: []

ov = to-vec (sort-ordered-vec v)

nov = to-vec (non-sort v)
