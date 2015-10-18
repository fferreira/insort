module Sort where

open import Nat

data list (A : Set) : Set where
  [] : list A
  _::_ : A -> list A -> list A

infixr 9 _::_

insert : ℕ -> list ℕ -> list ℕ
insert x [] = x :: []
insert x (y :: l) with compare x y
insert x (y :: l) | leq x≤y = y :: (insert x l)
insert x (y :: l) | geq y≤x = x :: y :: l

sort : list ℕ -> list ℕ
sort [] = []
sort (x :: l) = insert x l

--- length preserving

data vec (A : Set) : ℕ -> Set where
  [] : vec A z
  _::_ : ∀{n} -> A -> vec A n -> vec A (s n)

insvec : ∀{n} -> ℕ -> vec ℕ n -> vec ℕ (s n)
insvec x [] = x :: []
insvec x (y :: v) with compare x y
insvec x (y :: v) | leq x≤y = y :: (insvec x v)
insvec x (y :: v) | geq y≤x = x :: y :: v

sortvec : ∀{n} -> vec ℕ n -> vec ℕ n
sortvec [] = []
sortvec (x :: v) = insvec x v

data ord-list : (bound : ℕ) -> Set where
  [] : ∀{b} -> ord-list b
  cons : ∀{b} -> (x : ℕ) -> x ≤ b -> ord-list b -> ord-list x

data ord-vec : (n : ℕ) -> (b : ℕ) -> Set where
  [] : ∀{b} -> ord-vec z b
  cons : ∀{n b} -> (x : ℕ) -> x ≤ b -> ord-vec n b -> ord-vec (s n) x

ins-geq : ∀ {b n} x → b ≤ x → ord-vec n b → ord-vec (s n) b
ins-geq x b≤x [] = cons _ b≤x []
ins-geq x b≤x (cons {b = b} y y≤b v) with compare x b
ins-geq x b≤x (cons y y≤b v) | leq x≤y = cons y b≤x (cons x x≤y v)
ins-geq x b≤x (cons y y≤b v) | geq y≤x = cons y y≤b (ins-geq x y≤x v)

ins : ∀{n b} -> (x : ℕ) -> ord-vec n b -> ord-vec (s n) (min x b)
ins {b = b} x v with compare x b
ins x v | leq x≤b = cons x x≤b v
ins x v | geq b≤x = ins-geq x b≤x v

min-vec : ∀{n} -> vec ℕ (s n) -> ℕ
min-vec (x :: []) = x
min-vec (x :: x₁ :: v) = min x (min-vec (x₁ :: v))

unary : ∀ x → ord-vec (s z) x
unary x = cons x x≤x []

sort-ordered-vec : ∀{n} -> (v : vec ℕ (s n)) -> ord-vec (s n) (min-vec v)
sort-ordered-vec (x :: []) = unary x
sort-ordered-vec (x :: x₁ :: v) = ins x (sort-ordered-vec (x₁ :: v))

copies : ∀ n b → ord-vec n b
copies z b = []
copies (s n) b = cons b x≤x (copies n b)

non-sort : ∀{n} -> (v : vec ℕ (s n)) -> ord-vec (s n) (min-vec v)
non-sort {n} v with min-vec v
... | bound = copies (s n) bound

v : vec ℕ 6
v = 2 :: 3 :: 1 :: 6 :: 4 :: 5 :: []

ov = sort-ordered-vec v
