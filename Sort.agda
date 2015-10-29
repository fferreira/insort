module Sort where

open import Nat renaming (min to minℕ ; compare to compareℕ) hiding (cmpℕ)
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
insvec x (y :: v) with compareℕ x y
insvec x (y :: v) | leq x≤y = x :: y :: v
insvec x (y :: v) | geq y≤x = y :: insvec x v

sortvec : ∀{n} -> vec ℕ n -> vec ℕ n
sortvec [] = []
sortvec (x :: v) = insvec x (sortvec v)

data _+Inf (A : Set) : Set where
  val : A -> A +Inf
  ∞ : A +Inf

-- data ord-list : (bound : ℕ) -> Set where
--   [] : ∀{b} -> ord-list b
--   cons : ∀{b} -> (x : ℕ) -> x ≤ b -> ord-list b -> ord-list x

data _≤+_ : ℕ -> ℕ +Inf -> Set where
  comp : ∀{x y} -> x ≤ y -> x ≤+ (val y)
  ≤∞ : ∀{x} -> x ≤+ ∞

data ord-vec : (n : ℕ) -> (b : ℕ +Inf) -> Set where
  [] : ord-vec z ∞
  cons : ∀{n b} -> (x : ℕ) -> x ≤+ b -> ord-vec n b -> ord-vec (s n) (val x)

to-vec : ∀{n b} -> ord-vec n b -> vec ℕ n
to-vec [] = []
to-vec (cons x _ v) = x :: to-vec v

min : ℕ -> (ℕ +Inf) -> ℕ
min x (val y) = minℕ x y
min x ∞ = x

data cmp∞ (x : ℕ) : (y : ℕ +Inf) -> Set where
  leq : ∀ {y} (x≤y : x ≤+ y) -> cmp∞ x y
  geq : ∀ {y} (y≤x : y ≤+ (val x)) -> cmp∞ x (val y)

compare : (x : ℕ) -> (y : ℕ +Inf) -> cmp∞ x y
compare x (val y) with compareℕ x y
compare x (val y) | leq x≤y = leq (comp x≤y)
compare x (val y) | geq y≤x = geq (comp y≤x)
compare x ∞ = leq ≤∞

lemma-1 : ∀ {x b} → x ≤ b -> minℕ x b ≡ x
lemma-1 z≤n = refl
lemma-1 (s≤s w) = cong s (lemma-1 w)

lemma-2 : ∀ x b → minℕ b x ≡ minℕ x b
lemma-2 z z = refl
lemma-2 z (s b) = refl
lemma-2 (s x) z = refl
lemma-2 (s x) (s b) = cong s (lemma-2 x b)

lemma-3 : ∀ {x b} → x ≤ b -> minℕ b x ≡ x
lemma-3 {x = z} {b = b} z≤n rewrite lemma-2 z b = refl
lemma-3 (s≤s w) = cong s (lemma-3 w)

lemma-4 : ∀ {b x} y → b ≤ x → b ≤+ y → b ≤ min x y
lemma-4 y z≤n b<y = z≤n
lemma-4 (val ._) (s≤s b<x) (comp (s≤s x₁)) = s≤s (lemma-4 (val _) b<x (comp x₁))
lemma-4 ∞ (s≤s b<x) b<y = s≤s b<x

ins : ∀{n b} -> (x : ℕ) -> ord-vec n b -> ord-vec (s n) (val (min x b))
ins x [] = cons x ≤∞ []
ins x (cons b x₂ v) with compareℕ x b
ins x (cons b x₂ v) | leq x≤y rewrite lemma-1 x≤y = cons x (comp x≤y) (cons b x₂ v)
ins x (cons {b = b'} b x₂ v) | geq y≤x rewrite lemma-3 y≤x = cons b (comp (lemma-4 b' y≤x x₂)) (ins x v)

min-vec : ∀{n} -> vec ℕ (s n) -> ℕ
min-vec (x :: []) = x
min-vec (x :: x₁ :: v) = minℕ x (min-vec (x₁ :: v))

sort-ordered-vec : ∀{n} -> (v : vec ℕ (s n)) -> ord-vec (s n) (val (min-vec v))
sort-ordered-vec (x :: []) = cons x ≤∞ []
sort-ordered-vec (x :: x₁ :: v) = ins x (sort-ordered-vec (x₁ :: v))

copies : ∀ n b → ord-vec (s n) (val b)
copies z b = cons b ≤∞ []
copies (s n) b = cons b (comp x≤x) (copies n b)

non-sort : ∀{n} -> (v : vec ℕ (s n)) -> ord-vec (s n) (val (min-vec v))
non-sort {n} v with min-vec v
... | bound = copies n bound

v : vec ℕ 6
v = 2 :: 3 :: 1 :: 6 :: 4 :: 5 :: []

ov = to-vec (sort-ordered-vec v)
nov = to-vec (non-sort v)
