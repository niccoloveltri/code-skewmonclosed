{-# OPTIONS --rewriting #-}

module VarCondition where

open import Function
open import Data.Empty
open import Data.Bool 
open import Data.Bool.Properties
open import Data.Maybe renaming (map to mmap)
open import Data.Sum renaming ([_,_] to elim⊎; map to map⊎; assocˡ to assocL ; assocʳ to assocR) hiding (reduce)
open import Data.Sum.Properties
open import Data.List as List renaming (map to mapL)
open import Data.List.Relation.Unary.All
--open import Relation.Unary hiding (_∈_;_∖_)
open import Data.Product hiding (assocˡ; assocʳ; swap)
open import Relation.Binary.PropositionalEquality as PE hiding (_≗_) hiding ([_])
open ≡-Reasoning
open import Utilities
open import Formulae
open import SeqCalc 
open import Equations
open import Interpolation

-- List of atoms in formulae, contexts and stoups
-- We also keep track of polarities of atoms via Booleans.

at : Bool → Fma → List (Bool × At)
at b (` X) = [ b , X ]
at b I = []
at b (A ⊗ B) = at b A ++ at b B
at b (A ⊸ B) = at (not b) A ++ at b B

at-c : Bool → Cxt → List (Bool × At)
at-c b Γ = concat (mapL (at b) Γ)

at-s : Bool → Stp → List (Bool × At)
at-s b (just A) = at b A
at-s b ─ = []

isInj : {A B : Set} → (A → B) → Set
isInj f = ∀ {x y} → f x ≡ f y → x ≡ y

areDisj : {A B C : Set} → (A → C) → (B → C) → Set
areDisj f g = ∀ {x y} → f x ≡ g y → ⊥

compIsInj : {A B C : Set} (f : A → B) (g : B → C)
  → isInj f → isInj g → isInj (λ x → g (f x))
compIsInj f g if ig eq = if (ig eq)

_→ⁱ_ : Set → Set → Set
A →ⁱ B = Σ (A → B) isInj

substIsInj : {A : Set} (P : A → Set) {x y : A} (eq : x ≡ y) {p q : P x}
  → subst P eq p ≡ subst P eq q → p ≡ q
substIsInj P refl eq = eq

∈at++ : ∀ {b X} Γ Δ → X ∈ at-c b (Γ ++ Δ) → X ∈ at-c b Γ ++ at-c b Δ
∈at++ Γ Δ m = subst (λ x → _ ∈ x) (concat++ (mapL (at _) Γ) (mapL (at _) Δ)) m

∈at++ⁱ : ∀ {b X} Γ Δ → (X ∈ at-c b (Γ ++ Δ)) →ⁱ (X ∈ at-c b Γ ++ at-c b Δ)
∈at++ⁱ Γ Δ = (∈at++ Γ Δ) , substIsInj (_ ∈_) (concat++ (mapL (at _) Γ) (mapL (at _) Δ))

at++∈ : ∀ {b X} Γ Δ → X ∈ at-c b Γ ++ at-c b Δ → X ∈ at-c b (Γ ++ Δ)
at++∈ Γ Δ m = subst (λ x → _ ∈ x) (sym (concat++ (mapL (at _) Γ) (mapL (at _) Δ))) m

at++∈ⁱ : ∀ {b X} Γ Δ → (X ∈ at-c b Γ ++ at-c b Δ) →ⁱ (X ∈ at-c b (Γ ++ Δ))
at++∈ⁱ Γ Δ = (at++∈ Γ Δ) , substIsInj (_ ∈_) (sym (concat++ (mapL (at _) Γ) (mapL (at _) Δ)))

idⁱ : ∀ {A} → A →ⁱ A
idⁱ = id , λ x → x

compⁱ : {A B C : Set} (f : A →ⁱ B) (g : B →ⁱ C) → A →ⁱ C
compⁱ (f , i) (g , j) = g ∘ f , compIsInj f g i j

elim⊎IsInj : {A B C : Set} {f : A → C} {g : B → C}
  → isInj f → isInj g → areDisj f g → isInj (elim⊎ f g)
elim⊎IsInj if ig d {inj₁ x} {inj₁ x₁} eq = cong inj₁ (if eq)
elim⊎IsInj if ig d {inj₁ x} {inj₂ y} eq = ⊥-elim (d eq)
elim⊎IsInj if ig d {inj₂ y} {inj₁ x} eq = ⊥-elim (d (sym eq))
elim⊎IsInj if ig d {inj₂ y} {inj₂ y₁} eq = cong inj₂ (ig eq)

elim⊎ⁱ : {A B C : Set} (f : A →ⁱ C) (g : B →ⁱ C)
  → areDisj (f .proj₁) (g .proj₁)
  → (A ⊎ B) →ⁱ C
elim⊎ⁱ (f , i) (g , j) d = elim⊎ f g , elim⊎IsInj i j d

map⊎IsInj : {A B C D : Set} {f : A → C} {g : B → D}
  → isInj f → isInj g → isInj (map⊎ f g)
map⊎IsInj i j {inj₁ x} {inj₁ x₁} eq = cong inj₁ (i (inj₁-injective eq))
map⊎IsInj i j {inj₂ y} {inj₂ y₁} eq = cong inj₂ (j (inj₂-injective eq))

map⊎ⁱ : {A B C D : Set} (f : A →ⁱ C) (g : B →ⁱ D)
  → (A ⊎ B) →ⁱ (C ⊎ D)
map⊎ⁱ (f , i) (g , j) = map⊎ f g , map⊎IsInj i j

∈++IsInj : ∀{A a} (xs ys : List A) → isInj (∈++ {a = a} xs ys)
∈++IsInj [] ys refl = refl
∈++IsInj (x ∷ xs) ys {here} {here} eq = refl
∈++IsInj (x ∷ xs) ys {here} {there m'} eq with ∈++ xs ys m'
∈++IsInj (x ∷ xs) ys {here} {there m'} () | inj₁ n
∈++IsInj (x ∷ xs) ys {here} {there m'} () | inj₂ n
∈++IsInj (x ∷ xs) ys {there m} {here} eq with ∈++ xs ys m
∈++IsInj (x ∷ xs) ys {there m} {here} () | inj₁ n
∈++IsInj (x ∷ xs) ys {there m} {here} () | inj₂ n
∈++IsInj {a = a} (x ∷ xs) ys {there m} {there m'} eq =
  cong there (∈++IsInj xs ys (elim⊎IsInj (λ { refl → refl }) (λ { refl → refl }) (λ ()) eq))

∈++ⁱ : ∀{A a} (xs ys : List A) → (a ∈ xs ++ ys) →ⁱ (a ∈ xs ⊎ a ∈ ys)
∈++ⁱ xs ys = (∈++ xs ys) , ∈++IsInj xs ys

thereⁱ : ∀{A a} {x : A} {xs} → (a ∈ xs) →ⁱ (a ∈ x ∷ xs)
thereⁱ = there , λ { refl → refl}

++∈ : ∀{A a} (xs ys : List A) → a ∈ xs ⊎ a ∈ ys → a ∈ xs ++ ys
++∈ xs ys (inj₁ m) = ∈₁ xs ys m
++∈ xs ys (inj₂ m) = ∈₂ xs ys m

∈₁IsInj : ∀{A a} (xs ys : List A) → isInj (∈₁ {a = a} xs ys)
∈₁IsInj .(_ ∷ _) ys {here} {here} eq = refl
∈₁IsInj .(_ ∷ _) ys {there m} {there m'} eq = cong there (∈₁IsInj _ ys (thereⁱ .proj₂ eq))

∈₂IsInj : ∀{A a} (xs ys : List A) → isInj (∈₂ {a = a} xs ys)
∈₂IsInj [] ys eq = eq
∈₂IsInj (x ∷ xs) ys eq = ∈₂IsInj xs ys (thereⁱ .proj₂ eq)

∈₁ⁱ : ∀{A a} (xs ys : List A) → (a ∈ xs) →ⁱ (a ∈ xs ++ ys)
∈₁ⁱ xs ys = (∈₁ xs ys) , ∈₁IsInj xs ys

∈₂ⁱ : ∀{A a} (xs ys : List A) → (a ∈ ys) →ⁱ (a ∈ xs ++ ys)
∈₂ⁱ xs ys = (∈₂ xs ys) , ∈₂IsInj xs ys

∈₁⊥∈₂ : ∀{A a} (xs ys : List A) {m : a ∈ xs} {n : a ∈ ys}
  → ∈₁ xs ys m ≡ ∈₂ xs ys n → ⊥
∈₁⊥∈₂ (x ∷ xs) ys {there m} eq = ∈₁⊥∈₂ xs ys (thereⁱ .proj₂ eq)

++∈IsInj : ∀{A a} (xs ys : List A) → isInj (++∈ {a = a} xs ys)
++∈IsInj xs ys {inj₁ x} {inj₁ x₁} eq = cong inj₁ (∈₁IsInj xs ys eq)
++∈IsInj xs ys {inj₁ x} {inj₂ y} eq = ⊥-elim (∈₁⊥∈₂ xs ys eq)
++∈IsInj xs ys {inj₂ y} {inj₁ x} eq = ⊥-elim (∈₁⊥∈₂ xs ys (sym eq))
++∈IsInj xs ys {inj₂ y} {inj₂ y₁} eq = cong inj₂ (∈₂IsInj xs ys eq)

++∈ⁱ : ∀{A a} (xs ys : List A) → (a ∈ xs ⊎ a ∈ ys) →ⁱ (a ∈ xs ++ ys)
++∈ⁱ xs ys = (++∈ xs ys) , ++∈IsInj xs ys

swapIsInj : {A B : Set} → isInj (swap {A = A}{B = B})
swapIsInj {x = inj₁ x} {inj₁ .x} refl = refl
swapIsInj {x = inj₂ y} {inj₂ .y} refl = refl

swapⁱ : {A B : Set} → (A ⊎ B) →ⁱ (B ⊎ A)
swapⁱ = swap , swapIsInj

assocLIsInj : {A B C : Set} → isInj (assocL {A = A}{B = B}{C = C})
assocLIsInj {x = inj₁ x} {inj₁ .x} refl = refl
assocLIsInj {x = inj₁ x} {inj₂ (inj₁ x₁)} ()
assocLIsInj {x = inj₁ x} {inj₂ (inj₂ y)} ()
assocLIsInj {x = inj₂ (inj₁ x)} {inj₁ x₁} ()
assocLIsInj {x = inj₂ (inj₂ y)} {inj₁ x₁} ()
assocLIsInj {x = inj₂ (inj₁ x)} {inj₂ (inj₁ .x)} refl = refl
assocLIsInj {x = inj₂ (inj₂ y)} {inj₂ (inj₂ .(id y))} refl = refl

assocRIsInj : {A B C : Set} → isInj (assocR {A = A}{B = B}{C = C})
assocRIsInj {x = inj₁ (inj₁ x)} {inj₁ (inj₁ .(id x))} refl = refl
assocRIsInj {x = inj₁ (inj₂ y)} {inj₁ (inj₂ .y)} refl = refl
assocRIsInj {x = inj₁ (inj₁ x)} {inj₂ y} ()
assocRIsInj {x = inj₁ (inj₂ y₁)} {inj₂ y} ()
assocRIsInj {x = inj₂ y} {inj₁ (inj₁ x)} ()
assocRIsInj {x = inj₂ y} {inj₁ (inj₂ y₁)} ()
assocRIsInj {x = inj₂ y} {inj₂ .y} refl = refl

assocLⁱ : {A B C : Set} → (A ⊎ B ⊎ C) →ⁱ ((A ⊎ B) ⊎ C)
assocLⁱ = assocL , assocLIsInj

assocRⁱ : {A B C : Set} → ((A ⊎ B) ⊎ C) →ⁱ (A ⊎ B ⊎ C)
assocRⁱ = assocR , assocRIsInj


∈at⊸⋆ⁱ : ∀{b X} (Γ : Cxt) {C} → (X ∈ at b (Γ ⊸⋆ C)) →ⁱ (X ∈ at-c (not b) Γ ⊎ X ∈ at b C)
∈at⊸⋆ⁱ [] = inj₂ , inj₂-injective
∈at⊸⋆ⁱ (A ∷ Γ) {C} =
  compⁱ (∈++ⁱ (at _ A) (at _ (Γ ⊸⋆ C)))
  (compⁱ (map⊎ⁱ idⁱ (∈at⊸⋆ⁱ Γ))
  (compⁱ assocLⁱ
        (map⊎ⁱ (++∈ⁱ (at _ A) (at-c _ Γ)) idⁱ)))

∈at-c-notnot : ∀ {b X} Γ → (X ∈ at-c (not (not b)) Γ) →ⁱ (X ∈ at-c b Γ)
∈at-c-notnot {false} Γ = idⁱ
∈at-c-notnot {true} Γ = idⁱ

∈at-notnot2 : ∀ {b X} A → (X ∈ at b A) →ⁱ (X ∈ at (not (not b)) A)
∈at-notnot2 {false} A = idⁱ
∈at-notnot2 {true} A = idⁱ

++∈++ : ∀{A a} (xs ys : List A) (m : a ∈ xs ++ ys)
  → ++∈ xs ys (∈++ xs ys m) ≡ m
++∈++ [] ys m = refl
++∈++ (x ∷ xs) ys here = refl
++∈++ (x ∷ xs) ys (there m) with ∈++ xs ys m | inspect (∈++ xs ys) m
... | inj₁ p | PE.[ eq ] = cong there (trans (sym (cong (++∈ xs ys) eq)) (++∈++ xs ys m))
... | inj₂ p | PE.[ eq ] = cong there (trans (sym (cong (++∈ xs ys) eq)) (++∈++ xs ys m))

∈++₁ : ∀{A a} (xs ys : List A) (m : a ∈ xs) → ∈++ xs ys (∈₁ xs ys m) ≡ inj₁ m
∈++₁ ._ ys here = refl
∈++₁ ._ ys (there m) rewrite ∈++₁ _ ys m = refl

∈++₂ : ∀{A a} (xs ys : List A) (m : a ∈ ys) → ∈++ xs ys (∈₂ xs ys m) ≡ inj₂ m
∈++₂ [] ys m = refl
∈++₂ (x ∷ xs) ys m rewrite ∈++₂ xs ys m = refl

∈not : ∀ {b p X} A → p , X ∈ at b A → not p , X ∈ at (not b) A
∈not (` Y) here = here
∈not (A ⊗ B) m = ++∈ (at _ A) (at _ B) (map⊎ (∈not A) (∈not B) (∈++ (at _ A) (at _ B) m))
∈not (A ⊸ B) m = ++∈ (at _ A) (at _ B) (map⊎ (∈not A) (∈not B) (∈++ (at _ A) (at _ B) m))

∈not-iso-tt : ∀ {X} A (m : true , X ∈ at true A) → ∈not A (∈not A m) ≡ m
∈not-iso-tf : ∀ {X} A (m : true , X ∈ at false A) → ∈not A (∈not A m) ≡ m

∈not-iso-tt (` A) here = refl
∈not-iso-tt (A ⊗ B) m with ∈++ (at _ A) (at _ B) m | inspect (∈++ (at _ A) (at _ B)) m
... | inj₁ p | PE.[ eq ] rewrite ∈++₁ (at false A) (at false B) (∈not A p) =
  trans (cong (∈₁ (at _ A) (at _ B)) (∈not-iso-tt A p))
  (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
         (++∈++ (at _ A) (at _ B) m))
... | inj₂ p | PE.[ eq ] rewrite ∈++₂ (at false A) (at false B) (∈not B p) = 
  trans (cong (∈₂ (at _ A) (at _ B)) (∈not-iso-tt B p))
  (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
         (++∈++ (at _ A) (at _ B) m))
∈not-iso-tt (A ⊸ B) m with ∈++ (at _ A) (at _ B) m | inspect (∈++ (at _ A) (at _ B)) m
... | inj₁ p | PE.[ eq ] rewrite ∈++₁ (at true A) (at false B) (∈not A p) = 
  trans (cong (∈₁ (at _ A) (at _ B)) (∈not-iso-tf A p))
  (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
         (++∈++ (at _ A) (at _ B) m))
... | inj₂ p | PE.[ eq ] rewrite ∈++₂ (at true A) (at false B) (∈not B p) = 
  trans (cong (∈₂ (at _ A) (at _ B)) (∈not-iso-tt B p))
  (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
         (++∈++ (at _ A) (at _ B) m))

∈not-iso-tf (` X) (there ())
∈not-iso-tf (A ⊗ B) m with ∈++ (at _ A) (at _ B) m | inspect (∈++ (at _ A) (at _ B)) m
... | inj₁ p | PE.[ eq ] rewrite ∈++₁ (at true A) (at true B) (∈not A p) = 
  trans (cong (∈₁ (at _ A) (at _ B)) (∈not-iso-tf A p))
  (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
         (++∈++ (at _ A) (at _ B) m))
... | inj₂ p | PE.[ eq ] rewrite ∈++₂ (at true A) (at true B) (∈not B p) = 
  trans (cong (∈₂ (at _ A) (at _ B)) (∈not-iso-tf B p))
  (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
         (++∈++ (at _ A) (at _ B) m))
∈not-iso-tf (A ⊸ B) m with ∈++ (at _ A) (at _ B) m | inspect (∈++ (at _ A) (at _ B)) m
... | inj₁ p | PE.[ eq ] rewrite ∈++₁ (at false A) (at true B) (∈not A p) = 
  trans (cong (∈₁ (at _ A) (at _ B)) (∈not-iso-tt A p))
  (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
         (++∈++ (at _ A) (at _ B) m))
... | inj₂ p | PE.[ eq ] rewrite ∈++₂ (at false A) (at true B) (∈not B p) = 
 trans (cong (∈₂ (at _ A) (at _ B)) (∈not-iso-tf B p))
 (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
        (++∈++ (at _ A) (at _ B) m))

∈not-iso-ff : ∀ {X} A (m : false , X ∈ at false A) → ∈not A (∈not A m) ≡ m
∈not-iso-ft : ∀ {X} A (m : false , X ∈ at true A) → ∈not A (∈not A m) ≡ m

∈not-iso-ff (` A) here = refl
∈not-iso-ff (A ⊗ B) m with ∈++ (at _ A) (at _ B) m | inspect (∈++ (at _ A) (at _ B)) m
... | inj₁ p | PE.[ eq ] rewrite ∈++₁ (at true A) (at true B) (∈not A p) =
  trans (cong (∈₁ (at _ A) (at _ B)) (∈not-iso-ff A p))
  (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
         (++∈++ (at _ A) (at _ B) m))
... | inj₂ p | PE.[ eq ] rewrite ∈++₂ (at true A) (at true B) (∈not B p) = 
  trans (cong (∈₂ (at _ A) (at _ B)) (∈not-iso-ff B p))
  (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
         (++∈++ (at _ A) (at _ B) m))
∈not-iso-ff (A ⊸ B) m with ∈++ (at _ A) (at _ B) m | inspect (∈++ (at _ A) (at _ B)) m
... | inj₁ p | PE.[ eq ] rewrite ∈++₁ (at false A) (at true B) (∈not A p) = 
  trans (cong (∈₁ (at _ A) (at _ B)) (∈not-iso-ft A p))
  (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
         (++∈++ (at _ A) (at _ B) m))
... | inj₂ p | PE.[ eq ] rewrite ∈++₂ (at false A) (at true B) (∈not B p) = 
  trans (cong (∈₂ (at _ A) (at _ B)) (∈not-iso-ff B p))
  (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
         (++∈++ (at _ A) (at _ B) m))

∈not-iso-ft (` X) (there ())
∈not-iso-ft (A ⊗ B) m with ∈++ (at _ A) (at _ B) m | inspect (∈++ (at _ A) (at _ B)) m
... | inj₁ p | PE.[ eq ] rewrite ∈++₁ (at false A) (at false B) (∈not A p) = 
  trans (cong (∈₁ (at _ A) (at _ B)) (∈not-iso-ft A p))
  (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
         (++∈++ (at _ A) (at _ B) m))
... | inj₂ p | PE.[ eq ] rewrite ∈++₂ (at false A) (at false B) (∈not B p) = 
  trans (cong (∈₂ (at _ A) (at _ B)) (∈not-iso-ft B p))
  (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
         (++∈++ (at _ A) (at _ B) m))
∈not-iso-ft (A ⊸ B) m with ∈++ (at _ A) (at _ B) m | inspect (∈++ (at _ A) (at _ B)) m
... | inj₁ p | PE.[ eq ] rewrite ∈++₁ (at true A) (at false B) (∈not A p) = 
  trans (cong (∈₁ (at _ A) (at _ B)) (∈not-iso-ff A p))
  (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
         (++∈++ (at _ A) (at _ B) m))
... | inj₂ p | PE.[ eq ] rewrite ∈++₂ (at true A) (at false B) (∈not B p) = 
 trans (cong (∈₂ (at _ A) (at _ B)) (∈not-iso-ft B p))
 (trans (sym (cong (++∈ (at _ A) (at _ B)) eq))
        (++∈++ (at _ A) (at _ B) m))

∈not-iso : ∀ {p b X} A (m : p , X ∈ at b A)
  → ∈not A (∈not A m) ≡ subst₂ (λ x y → x , X ∈ at y A) (sym (not-involutive p)) (sym (not-involutive b)) m
∈not-iso {false} {false} = ∈not-iso-ff
∈not-iso {false} {true} = ∈not-iso-ft
∈not-iso {true} {false} = ∈not-iso-tf
∈not-iso {true} {true} = ∈not-iso-tt


{-
The variable conditions:

sVar collects variable conditions:
- an injective map from occurrences of atoms in D to occurrences of atoms in S,Γ
- an injective map from occurrences of atoms in D to occurrences of atoms in Δ,C

cVar collects variable conditions:
- an injective map from occurrences of atoms in D₁,...,Dₙ to occurrences of atoms in S,Δ₀,Δ₁,C
- an injective map from occurrences of atoms in D₁,...,Dₙ to occurrences of atoms in Γ₁,...,Γₙ

Notice that we also keep track of atom polarities.
In `at-g` below, if atom X has polarity p in formula D, then its associated occurrence in S,Γ₁ has same polarity.
In `at-h` below, if atom X has polarity p in formula D, then its associated occurrence in Γ₂,C has either opposite polarity if it is is Γ₂ or the same polarity if it is in C.
-}

record sVar S Γ₁ Γ₂ C D : Set where
  constructor v-s
  field
    at-g : ∀{b p X} → (p , X ∈ at b D) →ⁱ (p , X ∈ at-s b S ++ at-c b Γ₁)
    at-h : ∀{b p X} → (p , X ∈ at b D) →ⁱ (p , X ∈ at-c (not b) Γ₂ ++ at b C)

record cVar S Γ₀ Γ₁ Γ₂ C Ds : Set where
  constructor v-c
  field
    at-Ξ : ∀{b p X} → (p , X ∈ at-c b Ds) →ⁱ (p , X ∈ at-c b Γ₁)
    at-g : ∀{b p X} → (p , X ∈ at-c b Ds) →ⁱ (p , X ∈ at-s (not b) S ++ at-c (not b) Γ₀ ++ at-c (not b) Γ₂ ++ at b C)

svar : ∀ {S} Γ₁ Γ₂ {Γ C}
  → (f : S ∣ Γ ⊢ C) 
  → (eq : Γ ≡ Γ₁ ++ Γ₂)
  → sVar S Γ₁ Γ₂ C (sIntrp.D (sintrp Γ₁ Γ₂ f eq))

cvar : ∀{S} Γ₀ Γ₁ Γ₂ {Γ C}
  → (f : S ∣ Γ ⊢ C)
  → (eq : Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂)
  → cVar S Γ₀ Γ₁ Γ₂ C (cIntrp.Ds (cintrp Γ₀ Γ₁ Γ₂ f eq))

svar Γ₁ Γ₂ (Il f) refl with svar Γ₁ Γ₂ f refl
... | v-s ag ah = v-s ag ah
svar Γ₁ Γ₂ (⊗l f) refl with svar (_ ∷ Γ₁) Γ₂ f refl
... | v-s ag ah = v-s ag ah
svar Γ₁ Γ₂ (⊸r {A = A} {B} f) refl with svar Γ₁ (Γ₂ ∷ʳ A) f refl
... | v-s ag ah =
  v-s ag
    (compⁱ ah
     (compⁱ (∈++ⁱ (at-c _ (Γ₂ ∷ʳ A)) (at _ B))
     (compⁱ (map⊎ⁱ (∈at++ⁱ Γ₂ [ A ]) idⁱ)
            (++∈ⁱ (at-c _ Γ₂ ++ at _ A) (at _ B)))))

svar Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
svar {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ ([] , refl , refl) with svar Γ [] f refl 
... | v-s ag ah =
  v-s
    ag
    (compⁱ ah (compⁱ (∈₁ⁱ (at _ A) (at _ B)) (∈₂ⁱ (at-c _ Γ₂) (at _ A ++ at _ B))))
svar {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (A' ∷ Γ' , refl , refl) with svar Γ [] f refl | svar (A' ∷ Γ') Γ₂ g refl
... | v-s ag ah | v-s ak al =
  v-s  
    (compⁱ (∈++ⁱ (at _ (sIntrp.D (sintrp Γ [] f refl))) (at _ (sIntrp.D (sintrp (A' ∷ Γ') Γ₂ g refl))))
     (compⁱ (map⊎ⁱ (compⁱ ag (∈++ⁱ (at-s _ S) (at-c _ Γ))) ak)
     (compⁱ assocRⁱ
     (compⁱ (map⊎ⁱ idⁱ (compⁱ (++∈ⁱ (at-c _ Γ) (at-c _ (A' ∷ Γ'))) (at++∈ⁱ Γ (A' ∷ Γ'))))
           (++∈ⁱ (at-s _ S) (at-c _ (Γ ++ A' ∷ Γ')))))))
           
    (compⁱ (∈++ⁱ (at _ (sIntrp.D (sintrp Γ [] f refl))) (at _ (sIntrp.D (sintrp (A' ∷ Γ') Γ₂ g refl))))
     (compⁱ (map⊎ⁱ ah (compⁱ al (∈++ⁱ (at-c _ Γ₂) (at _ B))))
     (compⁱ (compⁱ assocLⁱ (compⁱ (map⊎ⁱ swapⁱ idⁱ) assocRⁱ))
     (compⁱ (map⊎ⁱ idⁱ (++∈ⁱ (at _ A) (at _ B)))
            (++∈ⁱ (at-c _ Γ₂) (at _ A ++ at _ B))))))            
svar Γ₁ _ (⊗r {Γ = _} {Δ = Δ} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) with svar Γ₁ (_ ∷ Γ') f refl
... | v-s ag ak =
  v-s
    ag    
    (compⁱ ak
     (compⁱ (∈++ⁱ (at-c _ (A' ∷ Γ')) (at _ A))
     (compⁱ (map⊎ⁱ (compⁱ (∈₁ⁱ (at-c _ (A' ∷ Γ')) (at-c _ Δ)) (at++∈ⁱ (A' ∷ Γ') Δ))
                   (∈₁ⁱ (at _ A) (at _ B)))
            (++∈ⁱ (at-c _ (A' ∷ Γ' ++ Δ)) (at _ A ++ at _ B) ))))

svar Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ Γ₁ Δ Γ₂ (sym eq)
svar Γ₁ .(Γ' ++ Δ) (⊸l {_} {Δ = Δ} {A}{B}{C} f g) refl | inj₁ (Γ' , refl , refl) with svar [] Δ g refl | cvar Γ₁ Γ' [] f refl
... | v-s ah ak | v-c ahs al =
  v-s
   (compⁱ (∈at⊸⋆ⁱ (cIntrp.Ds (cintrp Γ₁ Γ' [] f refl)))
   (compⁱ (map⊎ⁱ (compⁱ al (compⁱ (∈++ⁱ (at-c _ Γ₁) (at _ A)) (map⊎ⁱ (∈at-c-notnot Γ₁) idⁱ))) ah)
   (compⁱ (compⁱ assocRⁱ (compⁱ swapⁱ assocRⁱ))
   (compⁱ (map⊎ⁱ idⁱ (++∈ⁱ (at _ B) (at-c _ Γ₁)))
          (++∈ⁱ (at _ A) (at _ B ++ at-c _ Γ₁))))))

   (compⁱ (∈at⊸⋆ⁱ (cIntrp.Ds (cintrp Γ₁ Γ' [] f refl)))
    (compⁱ (map⊎ⁱ ahs (compⁱ ak (∈++ⁱ (at-c _ Δ) (at _ C))))
    (compⁱ assocLⁱ
    (compⁱ (map⊎ⁱ (compⁱ (++∈ⁱ (at-c _ Γ') (at-c _ Δ)) (at++∈ⁱ Γ' Δ)) idⁱ)
          (++∈ⁱ (at-c _ (Γ' ++ Δ)) (at _ C))))))
    
svar _ Γ₂ (⊸l {Γ} {_} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) with svar (A' ∷ Γ') Γ₂ g refl
... | v-s ah ak =
  v-s
   (compⁱ ah
    (compⁱ (∈++ⁱ (at _ B) (at-c _ (A' ∷ Γ')))
    (compⁱ (map⊎ⁱ (∈₂ⁱ (at _ A) (at _ B)) (compⁱ (∈₂ⁱ (at-c _ Γ) (at-c _ (A' ∷ Γ'))) (at++∈ⁱ Γ (A' ∷ Γ'))))
           (++∈ⁱ (at _ A ++ at _ B) (at-c _ (Γ ++ A' ∷ Γ'))))))
   ak 
svar [] [] ax refl = v-s idⁱ idⁱ
svar [] (A ∷ Γ₂) (pass f) refl = v-s idⁱ ((λ ()) , λ { {()}} )
svar (A ∷ Γ₁) Γ₂ (pass f) refl with svar Γ₁ Γ₂ f refl
... | v-s ah ak = v-s ah ak
svar [] [] Ir refl = v-s idⁱ idⁱ

cvar Γ₀ Γ₁ Γ₂ (Il f) refl with cvar Γ₀ Γ₁ Γ₂ f refl
... | v-c ahs ag = v-c ahs ag
cvar Γ₀ Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
cvar {S} .(Γ ++ Γ₀) Γ₁ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (Γ₀ , refl , refl) with cvar Γ₀ Γ₁ Γ₂ g refl
... | v-c ags ah =
  v-c
    ags

    (compⁱ ah
     (compⁱ (∈++ⁱ (at-c _ Γ₀ ++ at-c _ Γ₂) (at _ B))
     (compⁱ (map⊎ⁱ (compⁱ (∈++ⁱ (at-c _ Γ₀) (at-c _ Γ₂))
                    (compⁱ (map⊎ⁱ (compⁱ (∈₂ⁱ (at-c _ Γ) (at-c _ Γ₀))
                                   (compⁱ (at++∈ⁱ Γ Γ₀) (∈₂ⁱ (at-s _ S) (at-c _ (Γ ++ Γ₀)))))
                                 idⁱ)
                          (++∈ⁱ (at-s _ S ++ at-c _ (Γ ++ Γ₀)) (at-c _ Γ₂))))
                  (∈₂ⁱ (at _ A) (at _ B)))
             (++∈ⁱ (at-s _ S ++ at-c _ (Γ ++ Γ₀) ++ at-c _ Γ₂) (at _ A ++ at _ B)))))
cvar Γ₀ [] _ (⊗r f g) refl | inj₂ (A , Γ₁ , refl , refl) = v-c idⁱ ((λ ()) , (λ { { () } }))
cvar Γ₀ (A ∷ Γ₁) Γ₂ (⊗r {Δ = Δ} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
cvar {S} Γ₀ (A ∷ Γ₁) _ (⊗r {Δ = Δ}{A₁}{B₁} f g) refl | inj₂ (A , ._ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) with cvar Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
... | v-c ags ah =
  v-c
    ags

    (compⁱ ah
      (compⁱ (∈++ⁱ (at-s _ S ++ at-c _ Γ₀ ++ at _ A' ++ at-c _ Γ₂) (at _ A₁))
      (compⁱ (map⊎ⁱ (compⁱ (∈++ⁱ (at-s _ S ++ at-c _ Γ₀ ++ at _ A') (at-c _ Γ₂) )
                     (compⁱ (map⊎ⁱ idⁱ (compⁱ (∈₁ⁱ (at-c _ Γ₂) (at-c _ Δ)) (at++∈ⁱ Γ₂ Δ)))
                           (++∈ⁱ (at-s _ S ++ at-c _ Γ₀ ++ at _ A') (at-c _ (Γ₂ ++ Δ)))))
                    (∈₁ⁱ (at _ A₁) (at _ B₁)))
             (++∈ⁱ (at-s _ S ++ at-c _ Γ₀ ++ at _ A' ++ at-c _ (Γ₂ ++ Δ)) (at _ A₁ ++ at _ B₁)))))
cvar Γ₀ (A ∷ _) Γ₂ (⊗r f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁ , refl , refl) with cvar Γ₀ (_ ∷ Γ') [] f refl | cvar [] Γ₁ Γ₂ g refl
cvar {S} Γ₀ (A ∷ _) Γ₂ (⊗r {A = A₁}{B} f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁@_ , refl , refl) | v-c a-Ξf a-h | v-c a-Ξg a-k = 
  v-c
    (compⁱ (∈at++ⁱ (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl)) (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))
     (compⁱ (∈++ⁱ (at-c _ (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl))) (at-c _ (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl))))
     (compⁱ (map⊎ⁱ a-Ξf a-Ξg)
     (compⁱ (++∈ⁱ (at-c _ (A ∷ Γ')) (at-c _ Γ₁)) (at++∈ⁱ (A ∷ Γ') Γ₁))) ))

    (compⁱ (∈at++ⁱ (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl)) (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))
      (compⁱ (∈++ⁱ (at-c _ (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl))) (at-c _ (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl))))
      (compⁱ (map⊎ⁱ (compⁱ a-h (∈++ⁱ (at-s _ S ++ at-c _ Γ₀) (at _ A₁)))
                   (compⁱ a-k (∈++ⁱ (at-c _ Γ₂) (at _ B))))
      (compⁱ (compⁱ assocLⁱ (compⁱ (map⊎ⁱ (compⁱ assocRⁱ (compⁱ (map⊎ⁱ idⁱ swapⁱ) assocLⁱ)) idⁱ) assocRⁱ))
      (compⁱ (map⊎ⁱ (++∈ⁱ (at-s _ S ++ at-c _ Γ₀) (at-c _ Γ₂)) (++∈ⁱ (at _ A₁) (at _ B)))
             (++∈ⁱ (at-s _ S ++ at-c _ Γ₀ ++ at-c _ Γ₂) (at _ A₁ ++ at _ B)))))))
cvar Γ₀ Γ₁ Γ₂ (⊗l f) refl with cvar (_ ∷ Γ₀) Γ₁ Γ₂ f refl
... | v-c ahs ag = v-c ahs ag
cvar {S} Γ₀ Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with cvar Γ₀ Γ₁ (Γ₂ ∷ʳ A) f refl
... | v-c ahs ag =
  v-c
    ahs
    (compⁱ ag
     (compⁱ (∈++ⁱ (at-s _ S ++ at-c _ Γ₀) (at-c _ (Γ₂ ++ A ∷ []) ++ at _ B))
     (compⁱ (map⊎ⁱ idⁱ
                   (compⁱ (∈++ⁱ (at-c _ (Γ₂ ++ A ∷ [])) (at _ B))
                    (compⁱ (map⊎ⁱ (∈at++ⁱ Γ₂ [ A ]) idⁱ)
                          (++∈ⁱ (at-c _ Γ₂ ++ at _ A) (at _ B))) ))
            (++∈ⁱ (at-s _ S ++ at-c _ Γ₀) (at-c _ Γ₂ ++ at _ A ++ at _ B)))))
cvar Γ₀ Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
cvar _ Γ₁ Γ₂ (⊸l {Γ} f g) refl | inj₁ (Γ₀ , refl , refl) with cvar Γ₀ Γ₁ Γ₂ g refl
cvar _ _ Γ₂ (⊸l {Γ} {A = A}{B}{C} f g) refl | inj₁ (Γ₀ , refl , refl) | v-c a-Ξ a-h = 
  v-c
    a-Ξ
    (compⁱ a-h
     (compⁱ (∈++ⁱ (at _ B ++ at-c _ Γ₀) (at-c _ Γ₂ ++ at _ C))
     (compⁱ (map⊎ⁱ (compⁱ (∈++ⁱ (at _ B) (at-c _ Γ₀))
                     (compⁱ (map⊎ⁱ (∈₂ⁱ (at _ A) (at _ B))
                                   (compⁱ (∈₂ⁱ (at-c _ Γ) (at-c _ Γ₀))
                                          (at++∈ⁱ Γ Γ₀)))
                            (++∈ⁱ (at _ A ++ at _ B) (at-c _ (Γ ++ Γ₀)))))
                   idⁱ)
            (++∈ⁱ (at _ A ++ at _ B ++ at-c _ (Γ ++ Γ₀)) (at-c _ Γ₂ ++ at _ C)))))
cvar Γ₀ [] _ (⊸l f g) refl | inj₂ (B , Γ' , refl , refl) =
  v-c (((λ ()) , (λ { { () } }))) (((λ ()) , (λ { { () } })))
cvar Γ₀ (A ∷ Γ₁) Γ₂ (⊸l {Δ = Δ} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
cvar Γ₀ (A ∷ Γ₁) _ (⊸l {Δ = Δ} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) with cvar Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
cvar Γ₀ (A ∷ Γ₁) _ (⊸l {Δ = Δ} {A₁}{B₁}{C} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) | v-c a-Ξ a-h = 
  v-c
    a-Ξ
    (compⁱ a-h
     (compⁱ (compⁱ (∈++ⁱ (at-c _ Γ₀ ++ at _ A' ++ at-c _ Γ₂) (at _ A₁)) (map⊎ⁱ idⁱ (∈at-notnot2 A₁)))
     (compⁱ swapⁱ
     (compⁱ (map⊎ⁱ (∈₁ⁱ (at _ A₁) (at _ B₁))
                   (compⁱ (∈++ⁱ (at-c _ Γ₀ ++ at _ A') (at-c _ Γ₂))
                    (compⁱ (map⊎ⁱ idⁱ (compⁱ (∈₁ⁱ (at-c _ Γ₂) (at-c _ Δ))
                                      (compⁱ (at++∈ⁱ Γ₂ Δ) (∈₁ⁱ (at-c _ (Γ₂ ++ Δ)) (at _ C)))))
                           (++∈ⁱ (at-c _ Γ₀ ++ at _ A') (at-c _ (Γ₂ ++ Δ) ++ at _ C)))))
            (++∈ⁱ (at _ A₁ ++ at _ B₁) (at-c _ Γ₀ ++ at _ A' ++ at-c _ (Γ₂ ++ Δ) ++ at _ C))))))

cvar Γ₀ (A ∷ _) Γ₂ (⊸l f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁ , refl , refl) with cvar Γ₀ (_ ∷ Γ') [] f refl | cvar [] Γ₁ Γ₂ g refl
cvar Γ₀ (A ∷ _) Γ₂ (⊸l {A = A₁}{B₁}{C} f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁@_ , refl , refl) | v-c a-Ξf a-h | v-c a-Ξg a-k = 
  v-c
    (compⁱ (∈at++ⁱ (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl)) (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))
     (compⁱ (∈++ⁱ (at-c _ (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl))) (at-c _ (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl))))
     (compⁱ (map⊎ⁱ a-Ξf a-Ξg)
     (compⁱ (++∈ⁱ (at-c _ (A ∷ Γ')) (at-c _ Γ₁))
            (at++∈ⁱ (A ∷ Γ') Γ₁)))))

    (compⁱ (∈at++ⁱ (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl)) (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))
     (compⁱ (∈++ⁱ (at-c _ (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl))) (at-c _ (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl))))
     (compⁱ (map⊎ⁱ (compⁱ a-h (∈++ⁱ (at-c _ Γ₀) (at _ A₁)))
                   (compⁱ a-k (∈++ⁱ (at _ B₁) (at-c _ Γ₂ ++ at _ C))))
     (compⁱ (compⁱ assocLⁱ (compⁱ (map⊎ⁱ (compⁱ assocRⁱ swapⁱ) idⁱ) assocRⁱ))
     (compⁱ (map⊎ⁱ (compⁱ (map⊎ⁱ (∈at-notnot2 A₁) idⁱ) (++∈ⁱ (at _ A₁) (at _ B₁))) (++∈ⁱ (at-c _ Γ₀) (at-c _ Γ₂ ++ at _ C))) 
            (++∈ⁱ (at _ A₁ ++ at _ B₁) (at-c _ Γ₀ ++ at-c _ Γ₂ ++ at _ C)))))))
cvar [] [] [] ax refl = v-c idⁱ (((λ ()) , (λ { { () } })))
cvar [] [] Γ₂ (pass f) refl = v-c idⁱ (((λ ()) , (λ { { () } })))
cvar [] (A ∷ Γ₁) Γ₂ (pass f) refl with svar Γ₁ Γ₂ f refl
... | v-s a-g a-k = v-c a-g a-k
cvar (A ∷ Γ₀) Γ₁ Γ₂ (pass f) refl with cvar Γ₀ Γ₁ Γ₂ f refl
... | v-c a-Ξ a-h = v-c a-Ξ a-h
cvar [] [] [] Ir refl = v-c (((λ ()) , (λ { { () } }))) (((λ ()) , (λ { { () } })))
