module Sort where

open import Nat renaming (min to minℕ ; compare to compareℕ) hiding (cmp)
open import Eq

data list (A : Set) : Set where
  [] : list A
  _::_ : A -> list A -> list A

infixr 9 _::_

insert : ℕ -> list ℕ -> list ℕ
insert x [] = x :: []
insert x (y :: l) with compareℕ x y
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
insvec x (y :: v) with compareℕ x y
insvec x (y :: v) | leq x≤y = y :: (insvec x v)
insvec x (y :: v) | geq y≤x = x :: y :: v

sortvec : ∀{n} -> vec ℕ n -> vec ℕ n
sortvec [] = []
sortvec (x :: v) = insvec x v

data _⊎_  (A B : Set) : Set where
  inl : A -> A ⊎ B
  inr : B -> A ⊎ B

data ⊤ : Set where
  ⋆ : ⊤

-- data ord-list : (bound : ℕ) -> Set where
--   [] : ∀{b} -> ord-list b
--   cons : ∀{b} -> (x : ℕ) -> x ≤ b -> ord-list b -> ord-list x

_⊎⊤ : {A : Set} -> (A -> A -> Set) -> A -> (A ⊎ ⊤) -> Set
_⊎⊤ f x (inl y) = f x y
_⊎⊤ f x (inr ⋆) = ⊤

_≤+_ = _≤_ ⊎⊤

data ord-vec : (n : ℕ) -> (b : ℕ ⊎ ⊤) -> Set where
  [] : ord-vec z (inr ⋆)
  cons : ∀{n b} -> (x : ℕ) -> x ≤+ b -> ord-vec n b -> ord-vec (s n) (inl x)

to-vec : ∀{n b} -> ord-vec n b -> vec ℕ n
to-vec [] = []
to-vec (cons x _ v) = x :: to-vec v

min : ℕ -> (ℕ ⊎ ⊤) -> ℕ
min x (inl y) = minℕ x y
min x (inr ⋆) = x

data cmp⊎⊤ (x : ℕ) : (y : ℕ ⊎ ⊤) -> Set where
  leq : ∀ {y} (x≤y : x ≤+ y) -> cmp⊎⊤ x y
  geq : ∀ {y} (y≤x : y ≤+ (inl x)) -> cmp⊎⊤ x (inl y)

compare : (x : ℕ) -> (y : ℕ ⊎ ⊤) -> cmp⊎⊤ x y
compare x (inl y) with compareℕ x y
compare x (inl y) | leq x≤y = leq x≤y
compare x (inl y) | geq y≤x = geq y≤x
compare x (inr ⋆) = leq ⋆

lemma : ∀ {x b} -> b ≤ x → b ≤+ (inl (minℕ x b))
lemma z≤n = z≤n
lemma (s≤s w) = s≤s (lemma w)

lemma3 : ∀ {x b} → x ≤ b -> minℕ x b ≡ x
lemma3 z≤n = refl
lemma3 (s≤s w) = cong s (lemma3 w)

lemma35 : ∀ x b → minℕ b x ≡ minℕ x b
lemma35 z z = refl
lemma35 z (s b) = refl
lemma35 (s x) z = refl
lemma35 (s x) (s b) = cong s (lemma35 x b)

lemma4 : ∀ {x b} → x ≤ b -> minℕ b x ≡ x
lemma4 {x = z} {b = b} z≤n rewrite lemma35 z b = refl
lemma4 (s≤s w) = cong s (lemma4 w)

trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
trans z≤n n = z≤n
trans (s≤s m₂) (s≤s n₁) = s≤s (trans m₂ n₁)

lemmaplsstop : ∀ {m n} → (s m) ≤ (s n) → m ≤ n
lemmaplsstop (s≤s r) = r

lemma5 : ∀ {b x} y → b ≤ x → b ≤+ y → b ≤ min x y
lemma5 y z≤n r' = z≤n
lemma5 (inl z) (s≤s r) r' = r'
lemma5 (inl (s x)) (s≤s r) r' = s≤s (lemma5 (inl x) r (lemmaplsstop r'))
lemma5 (inr ⋆) (s≤s r) r' = s≤s r

ins : ∀{n b} -> (x : ℕ) -> ord-vec n b -> ord-vec (s n) (inl (min x b))
ins x [] = cons x ⋆ []
ins x (cons b x₂ v) with compareℕ x b
ins x (cons b x₂ v) | leq x≤y rewrite lemma3 x≤y = cons x x≤y (cons b x₂ v)
ins x (cons {b = b'} b x₂ v) | geq y≤x rewrite lemma4 y≤x = cons b (lemma5 b' y≤x x₂) (ins x v)

min-vec : ∀{n} -> vec ℕ (s n) -> ℕ
min-vec (x :: []) = x
min-vec (x :: x₁ :: v) = minℕ x (min-vec (x₁ :: v))

unary : (x  : ℕ) → ord-vec (s z) (inl x)
unary x = cons x ⋆ []

sort-ordered-vec : ∀{n} -> (v : vec ℕ (s n)) -> ord-vec (s n) (inl (min-vec v))
sort-ordered-vec (x :: []) = unary x
sort-ordered-vec (x :: x₁ :: v) = ins x (sort-ordered-vec (x₁ :: v))

copies : ∀ n b → ord-vec (s n) (inl b)
copies z b = cons b ⋆ []
copies (s n) b = cons b x≤x (copies n b)

non-sort : ∀{n} -> (v : vec ℕ (s n)) -> ord-vec (s n) (inl (min-vec v))
non-sort {n} v with min-vec v
... | bound = copies n bound

v : vec ℕ 6
v = 2 :: 3 :: 1 :: 6 :: 4 :: 5 :: []

ov = to-vec (sort-ordered-vec v)
nov = to-vec (non-sort v)
