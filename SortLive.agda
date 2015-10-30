module SortLive where

open import NatPrime renaming (min to minℕ ; compare to compareℕ) hiding (cmpℕ)
open import Eq

data list (A : Set) : Set where
  [] : list A
  _::_ : A -> list A -> list A

infixr 9 _::_

insert : ℕ -> list ℕ -> list ℕ
insert x [] = x :: []
insert x (y :: l) with compareℕ x y
insert x (y :: l) | leq x≤y = x :: y :: l
insert x (y :: l) | geq y≤x = y :: insert x l

sort : list ℕ -> list ℕ
sort [] = []
sort (x :: l) = insert x (sort l)

--- length preserving

data vec (A : Set) : ℕ -> Set where
  [] : vec A z
  _::_ : ∀{n} -> A -> vec A n -> vec A (s n)

insvec : ∀{n} -> ℕ -> vec ℕ n -> vec ℕ (s n)
insvec x [] = x :: []
insvec x (y :: l) with compareℕ x y
insvec x (y :: l) | leq x≤y = x :: y :: l
insvec x (y :: l) | geq y≤x = y :: insvec x l

sortvec : ∀{n} -> vec ℕ n -> vec ℕ n
sortvec [] = []
sortvec (x :: l) = insvec x (sortvec l)

--- oredered

data _+Inf (A : Set) : Set where
  val : A -> A +Inf
  ∞ : A +Inf

data _≤+_ : ℕ -> ℕ +Inf -> Set where
  comp : ∀{x y} -> x ≤ y -> x ≤+ (val y)
  ≤∞ : ∀{x} -> x ≤+ ∞

data ord-vec : (n : ℕ) -> (b : ℕ +Inf) -> Set where
  [] : ord-vec z ∞
  cons : ∀{n b} x ->  x ≤+ b -> ord-vec n b -> ord-vec (s n) (val x)

to-vec : ∀{n b} -> ord-vec n b -> vec ℕ n
to-vec [] = []
to-vec (cons x _ v) = x :: to-vec v

min : ℕ -> ℕ +Inf -> ℕ
min n (val m) = minℕ n m
min n ∞ = n

min-vec : ∀{n} -> vec ℕ n -> ℕ +Inf
min-vec [] = ∞
min-vec (x :: v) = val (min x (min-vec v))

lemma : ∀ {x y b} → y ≤ x → y ≤+ b → y ≤+ val (min x b)
lemma {x} y<x (comp {y = y₁} p) with compareℕ x y₁
lemma y<x (comp p) | leq x≤y = comp y<x
lemma y<x (comp p) | geq y≤x = comp p
lemma y<x ≤∞ = comp y<x

iov : ∀{n b} -> (x : ℕ) -> ord-vec n b -> ord-vec (s n) (val (min x b))
iov x [] = cons x ≤∞ []
iov x (cons y y<b v) with compareℕ x y
iov x (cons y y<b v) | leq x≤y = cons x (comp x≤y) (cons y y<b v)
iov x (cons y y<b v) | geq y≤x = cons y (lemma y≤x y<b) (iov x v)

sov : ∀{n} -> (v : vec ℕ n) -> ord-vec n (min-vec v)
sov [] = []
sov (x :: v) = iov x (sov v)
