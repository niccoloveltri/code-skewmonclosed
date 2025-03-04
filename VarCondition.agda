{-# OPTIONS --rewriting #-}

module VarCondition where

open import Function
open import Data.Empty
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

at : Fma → List At
at (` X) = [ X ]
at I = []
at (A ⊗ B) = at A ++ at B
at (A ⊸ B) = at A ++ at B

at-c : Cxt → List At
at-c Γ = concat (mapL at Γ)

at-s : Stp → List At
at-s (just A) = at A
at-s ─ = []

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

∈at++ : ∀ {X} Γ Δ → X ∈ at-c (Γ ++ Δ) → X ∈ at-c Γ ++ at-c Δ
∈at++ Γ Δ m = subst (λ x → _ ∈ x) (concat++ (mapL at Γ) (mapL at Δ)) m

∈at++ⁱ : ∀ {X} Γ Δ → (X ∈ at-c (Γ ++ Δ)) →ⁱ (X ∈ at-c Γ ++ at-c Δ)
∈at++ⁱ Γ Δ = (∈at++ Γ Δ) , substIsInj (_ ∈_) (concat++ (mapL at Γ) (mapL at Δ))

at++∈ : ∀ {X} Γ Δ → X ∈ at-c Γ ++ at-c Δ → X ∈ at-c (Γ ++ Δ)
at++∈ Γ Δ m = subst (λ x → _ ∈ x) (sym (concat++ (mapL at Γ) (mapL at Δ))) m

at++∈ⁱ : ∀ {X} Γ Δ → (X ∈ at-c Γ ++ at-c Δ) →ⁱ (X ∈ at-c (Γ ++ Δ))
at++∈ⁱ Γ Δ = (at++∈ Γ Δ) , substIsInj (_ ∈_) (sym (concat++ (mapL at Γ) (mapL at Δ)))


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


∈at⊸⋆ⁱ : ∀{X} (Γ : Cxt) {C} → (X ∈ at (Γ ⊸⋆ C)) →ⁱ (X ∈ at-c Γ ⊎ X ∈ at C)
∈at⊸⋆ⁱ [] = inj₂ , inj₂-injective
∈at⊸⋆ⁱ (A ∷ Γ) {C} =
  compⁱ (∈++ⁱ (at A) (at (Γ ⊸⋆ C)))
  (compⁱ (map⊎ⁱ idⁱ (∈at⊸⋆ⁱ Γ))
  (compⁱ assocLⁱ
        (map⊎ⁱ (++∈ⁱ (at A) (at-c Γ)) idⁱ)))



{-
The variable conditions:

sVar collects variable conditions:
- an injective map from occurrences of ats in D to occurrences of ats in S,Γ
- an injective map from occurrences of ats in D to occurrences of ats in Δ,C

cVar collects variable conditions:
- an injective map from occurrences of ats in D₁,...,Dₙ to occurrences of ats in S,Δ₀,Δ₁,C
- an injective map from occurrences of ats in D₁,...,Dₙ to occurrences of ats in Γ₁,...,Γₙ
-}

record sVar S Γ₁ Γ₂ C D : Set where
  constructor v-s
  field
    at-g : ∀{X} → (X ∈ at D) →ⁱ (X ∈ at-s S ++ at-c Γ₁)
    at-h : ∀{X} → (X ∈ at D) →ⁱ (X ∈ at-c Γ₂ ++ at C)

record cVar S Γ₀ Γ₁ Γ₂ C Ds : Set where
  constructor v-c
  field
    at-Ξ : ∀{X} → (X ∈ at-c Ds) →ⁱ (X ∈ at-c Γ₁)
    at-g : ∀{X} → (X ∈ at-c Ds) →ⁱ (X ∈ at-s S ++ at-c Γ₀ ++ at-c Γ₂ ++ at C)


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
svar Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with svar Γ₁ (Γ₂ ∷ʳ A) f refl
... | v-s ag ah =
  v-s
    ag 
    (compⁱ ah
     (compⁱ (∈++ⁱ (at-c (Γ₂ ∷ʳ A)) (at B))
     (compⁱ (map⊎ⁱ (∈at++ⁱ Γ₂ [ A ]) idⁱ)
            (++∈ⁱ (at-c Γ₂ ++ at A) (at B)))))
            
svar Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
svar {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ ([] , refl , refl) with svar Γ [] f refl 
... | v-s ag ah =
  v-s
    ag
    (compⁱ ah (compⁱ (∈₁ⁱ (at A) (at B)) (∈₂ⁱ (at-c Γ₂) (at A ++ at B))))
svar {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (A' ∷ Γ' , refl , refl) with svar Γ [] f refl | svar (A' ∷ Γ') Γ₂ g refl
... | v-s ag ah | v-s ak al =
  v-s  
    (compⁱ (∈++ⁱ (at (sIntrp.D (sintrp Γ [] f refl))) (at (sIntrp.D (sintrp (A' ∷ Γ') Γ₂ g refl))))
     (compⁱ (map⊎ⁱ (compⁱ ag (∈++ⁱ (at-s S) (at-c Γ))) ak)
     (compⁱ assocRⁱ
     (compⁱ (map⊎ⁱ idⁱ (compⁱ (++∈ⁱ (at-c Γ) (at-c (A' ∷ Γ'))) (at++∈ⁱ Γ (A' ∷ Γ'))))
           (++∈ⁱ (at-s S) (at-c (Γ ++ A' ∷ Γ')))))))
                 
    (compⁱ (∈++ⁱ (at (sIntrp.D (sintrp Γ [] f refl))) (at (sIntrp.D (sintrp (A' ∷ Γ') Γ₂ g refl))))
     (compⁱ (map⊎ⁱ ah (compⁱ al (∈++ⁱ (at-c Γ₂) (at B))))
     (compⁱ (compⁱ assocLⁱ (compⁱ (map⊎ⁱ swapⁱ idⁱ) assocRⁱ))
     (compⁱ (map⊎ⁱ idⁱ (++∈ⁱ (at A) (at B)))
            (++∈ⁱ (at-c Γ₂) (at A ++ at B))))))            
svar Γ₁ _ (⊗r {Γ = _} {Δ = Δ} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) with svar Γ₁ (_ ∷ Γ') f refl
... | v-s ag ak =
  v-s
    ag    
    (compⁱ ak
     (compⁱ (∈++ⁱ (at-c (A' ∷ Γ')) (at A))
     (compⁱ (map⊎ⁱ (compⁱ (∈₁ⁱ (at-c (A' ∷ Γ')) (at-c Δ)) (at++∈ⁱ (A' ∷ Γ') Δ))
                   (∈₁ⁱ (at A) (at B)))
            (++∈ⁱ (at-c (A' ∷ Γ' ++ Δ)) (at A ++ at B) ))))
svar Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ Γ₁ Δ Γ₂ (sym eq)
svar Γ₁ .(Γ' ++ Δ) (⊸l {_} {Δ = Δ} {A}{B}{C} f g) refl | inj₁ (Γ' , refl , refl) with svar [] Δ g refl | cvar Γ₁ Γ' [] f refl
... | v-s ah ak | v-c ahs al =
  v-s  
   (compⁱ (∈at⊸⋆ⁱ (cIntrp.Ds (cintrp Γ₁ Γ' [] f refl)))
    (compⁱ (map⊎ⁱ (compⁱ al (∈++ⁱ (at-c Γ₁) (at A))) ah)
    (compⁱ (compⁱ assocRⁱ (compⁱ swapⁱ assocRⁱ))
    (compⁱ (map⊎ⁱ idⁱ (++∈ⁱ (at B) (at-c Γ₁)))
          (++∈ⁱ (at A) (at B ++ at-c Γ₁))))))
   
   (compⁱ (∈at⊸⋆ⁱ (cIntrp.Ds (cintrp Γ₁ Γ' [] f refl)))
    (compⁱ (map⊎ⁱ ahs (compⁱ ak (∈++ⁱ (at-c Δ) (at C))))
    (compⁱ assocLⁱ
    (compⁱ (map⊎ⁱ (compⁱ (++∈ⁱ (at-c Γ') (at-c Δ)) (at++∈ⁱ Γ' Δ)) idⁱ)
          (++∈ⁱ (at-c (Γ' ++ Δ)) (at C))))))
          
svar _ Γ₂ (⊸l {Γ} {_} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) with svar (A' ∷ Γ') Γ₂ g refl
... | v-s ah ak =
  v-s
   (compⁱ ah
    (compⁱ (∈++ⁱ (at B) (at-c (A' ∷ Γ')))
    (compⁱ (map⊎ⁱ (∈₂ⁱ (at A) (at B)) (compⁱ (∈₂ⁱ (at-c Γ) (at-c (A' ∷ Γ'))) (at++∈ⁱ Γ (A' ∷ Γ'))))
           (++∈ⁱ (at A ++ at B) (at-c (Γ ++ A' ∷ Γ'))))))
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
     (compⁱ (∈++ⁱ (at-c Γ₀ ++ at-c Γ₂) (at B))
     (compⁱ (map⊎ⁱ (compⁱ (∈++ⁱ (at-c Γ₀) (at-c Γ₂))
                    (compⁱ (map⊎ⁱ (compⁱ (∈₂ⁱ (at-c Γ) (at-c Γ₀))
                                   (compⁱ (at++∈ⁱ Γ Γ₀) (∈₂ⁱ (at-s S) (at-c (Γ ++ Γ₀)))))
                                 idⁱ)
                          (++∈ⁱ (at-s S ++ at-c (Γ ++ Γ₀)) (at-c Γ₂))))
                  (∈₂ⁱ (at A) (at B)))
             (++∈ⁱ (at-s S ++ at-c (Γ ++ Γ₀) ++ at-c Γ₂) (at A ++ at B)))))
cvar Γ₀ [] _ (⊗r f g) refl | inj₂ (A , Γ₁ , refl , refl) = v-c idⁱ ((λ ()) , (λ { { () } }))
cvar Γ₀ (A ∷ Γ₁) Γ₂ (⊗r {Δ = Δ} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
cvar {S} Γ₀ (A ∷ Γ₁) _ (⊗r {Δ = Δ}{A₁}{B₁} f g) refl | inj₂ (A , ._ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) with cvar Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
... | v-c ags ah =
  v-c
    ags
    
    (compⁱ ah
      (compⁱ (∈++ⁱ (at-s S ++ at-c Γ₀ ++ at A' ++ at-c Γ₂) (at A₁))
      (compⁱ (map⊎ⁱ (compⁱ (∈++ⁱ (at-s S ++ at-c Γ₀ ++ at A') (at-c Γ₂) )
                     (compⁱ (map⊎ⁱ idⁱ (compⁱ (∈₁ⁱ (at-c Γ₂) (at-c Δ)) (at++∈ⁱ Γ₂ Δ)))
                           (++∈ⁱ (at-s S ++ at-c Γ₀ ++ at A') (at-c (Γ₂ ++ Δ)))))
                    (∈₁ⁱ (at A₁) (at B₁)))
             (++∈ⁱ (at-s S ++ at-c Γ₀ ++ at A' ++ at-c (Γ₂ ++ Δ)) (at A₁ ++ at B₁)))))
cvar Γ₀ (A ∷ _) Γ₂ (⊗r f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁ , refl , refl) with cvar Γ₀ (_ ∷ Γ') [] f refl | cvar [] Γ₁ Γ₂ g refl
cvar {S} Γ₀ (A ∷ _) Γ₂ (⊗r {A = A₁}{B} f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁@_ , refl , refl) | v-c a-Ξf a-h | v-c a-Ξg a-k = 
  v-c
    (compⁱ (∈at++ⁱ (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl)) (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))
     (compⁱ (∈++ⁱ (at-c (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl))) (at-c (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl))))
     (compⁱ (map⊎ⁱ a-Ξf a-Ξg)
     (compⁱ (++∈ⁱ (at-c (A ∷ Γ')) (at-c Γ₁)) (at++∈ⁱ (A ∷ Γ') Γ₁))) ))

    (compⁱ (∈at++ⁱ (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl)) (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))
      (compⁱ (∈++ⁱ (at-c (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl))) (at-c (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl))))
      (compⁱ (map⊎ⁱ (compⁱ a-h (∈++ⁱ (at-s S ++ at-c Γ₀) (at A₁)))
                   (compⁱ a-k (∈++ⁱ (at-c Γ₂) (at B))))
      (compⁱ (compⁱ assocLⁱ (compⁱ (map⊎ⁱ (compⁱ assocRⁱ (compⁱ (map⊎ⁱ idⁱ swapⁱ) assocLⁱ)) idⁱ) assocRⁱ))
      (compⁱ (map⊎ⁱ (++∈ⁱ (at-s S ++ at-c Γ₀) (at-c Γ₂)) (++∈ⁱ (at A₁) (at B)))
             (++∈ⁱ (at-s S ++ at-c Γ₀ ++ at-c Γ₂) (at A₁ ++ at B)))))))
cvar Γ₀ Γ₁ Γ₂ (⊗l f) refl with cvar (_ ∷ Γ₀) Γ₁ Γ₂ f refl
... | v-c ahs ag = v-c ahs ag
cvar {S} Γ₀ Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with cvar Γ₀ Γ₁ (Γ₂ ∷ʳ A) f refl
... | v-c ahs ag =
  v-c
    ahs
    (compⁱ ag
     (compⁱ (∈++ⁱ (at-s S ++ at-c Γ₀) (at-c (Γ₂ ++ A ∷ []) ++ at B))
     (compⁱ (map⊎ⁱ idⁱ
                   (compⁱ (∈++ⁱ (at-c (Γ₂ ++ A ∷ [])) (at B))
                    (compⁱ (map⊎ⁱ (∈at++ⁱ Γ₂ [ A ]) idⁱ)
                          (++∈ⁱ (at-c Γ₂ ++ at A) (at B))) ))
            (++∈ⁱ (at-s S ++ at-c Γ₀) (at-c Γ₂ ++ at A ++ at B)))))
cvar Γ₀ Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
cvar _ Γ₁ Γ₂ (⊸l {Γ} f g) refl | inj₁ (Γ₀ , refl , refl) with cvar Γ₀ Γ₁ Γ₂ g refl
cvar _ _ Γ₂ (⊸l {Γ} {A = A}{B}{C} f g) refl | inj₁ (Γ₀ , refl , refl) | v-c a-Ξ a-h = 
  v-c
    a-Ξ
    (compⁱ a-h
     (compⁱ (∈++ⁱ (at B ++ at-c Γ₀) (at-c Γ₂ ++ at C))
     (compⁱ (map⊎ⁱ (compⁱ (∈++ⁱ (at B) (at-c Γ₀))
                     (compⁱ (map⊎ⁱ (∈₂ⁱ (at A) (at B))
                                   (compⁱ (∈₂ⁱ (at-c Γ) (at-c Γ₀))
                                          (at++∈ⁱ Γ Γ₀)))
                            (++∈ⁱ (at A ++ at B) (at-c (Γ ++ Γ₀)))))
                   idⁱ)
            (++∈ⁱ (at A ++ at B ++ at-c (Γ ++ Γ₀)) (at-c Γ₂ ++ at C)))))
cvar Γ₀ [] _ (⊸l f g) refl | inj₂ (B , Γ' , refl , refl) =
  v-c (((λ ()) , (λ { { () } }))) (((λ ()) , (λ { { () } })))
cvar Γ₀ (A ∷ Γ₁) Γ₂ (⊸l {Δ = Δ} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
cvar Γ₀ (A ∷ Γ₁) _ (⊸l {Δ = Δ} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) with cvar Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
cvar Γ₀ (A ∷ Γ₁) _ (⊸l {Δ = Δ} {A₁}{B₁}{C} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) | v-c a-Ξ a-h = 
  v-c
    a-Ξ
    (compⁱ a-h
     (compⁱ (∈++ⁱ (at-c Γ₀ ++ at A' ++ at-c Γ₂) (at A₁))
     (compⁱ swapⁱ
     (compⁱ (map⊎ⁱ (∈₁ⁱ (at A₁) (at B₁))
                   (compⁱ (∈++ⁱ (at-c Γ₀ ++ at A') (at-c Γ₂))
                    (compⁱ (map⊎ⁱ idⁱ (compⁱ (∈₁ⁱ (at-c Γ₂) (at-c Δ))
                                      (compⁱ (at++∈ⁱ Γ₂ Δ) (∈₁ⁱ (at-c (Γ₂ ++ Δ)) (at C)))))
                           (++∈ⁱ (at-c Γ₀ ++ at A') (at-c (Γ₂ ++ Δ) ++ at C)))))
            (++∈ⁱ (at A₁ ++ at B₁) (at-c Γ₀ ++ at A' ++ at-c (Γ₂ ++ Δ) ++ at C))))))
cvar Γ₀ (A ∷ _) Γ₂ (⊸l f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁ , refl , refl) with cvar Γ₀ (_ ∷ Γ') [] f refl | cvar [] Γ₁ Γ₂ g refl
cvar Γ₀ (A ∷ _) Γ₂ (⊸l {A = A₁}{B₁}{C} f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁@_ , refl , refl) | v-c a-Ξf a-h | v-c a-Ξg a-k = 
  v-c
    (compⁱ (∈at++ⁱ (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl)) (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))
     (compⁱ (∈++ⁱ (at-c (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl))) (at-c (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl))))
     (compⁱ (map⊎ⁱ a-Ξf a-Ξg)
     (compⁱ (++∈ⁱ (at-c (A ∷ Γ')) (at-c Γ₁))
            (at++∈ⁱ (A ∷ Γ') Γ₁)))))
    
    (compⁱ (∈at++ⁱ (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl)) (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))
     (compⁱ (∈++ⁱ (at-c (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl))) (at-c (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl))))
     (compⁱ (map⊎ⁱ (compⁱ a-h (∈++ⁱ (at-c Γ₀) (at A₁)))
                   (compⁱ a-k (∈++ⁱ (at B₁) (at-c Γ₂ ++ at C))))
     (compⁱ (compⁱ assocLⁱ (compⁱ (map⊎ⁱ (compⁱ assocRⁱ swapⁱ) idⁱ) assocRⁱ))
     (compⁱ (map⊎ⁱ (++∈ⁱ (at A₁) (at B₁)) (++∈ⁱ (at-c Γ₀) (at-c Γ₂ ++ at C)))
            (++∈ⁱ (at A₁ ++ at B₁) (at-c Γ₀ ++ at-c Γ₂ ++ at C)))))))
cvar [] [] [] ax refl = v-c idⁱ (((λ ()) , (λ { { () } })))
cvar [] [] Γ₂ (pass f) refl = v-c idⁱ (((λ ()) , (λ { { () } })))
cvar [] (A ∷ Γ₁) Γ₂ (pass f) refl with svar Γ₁ Γ₂ f refl
... | v-s a-g a-k = v-c a-g a-k
cvar (A ∷ Γ₀) Γ₁ Γ₂ (pass f) refl with cvar Γ₀ Γ₁ Γ₂ f refl
... | v-c a-Ξ a-h = v-c a-Ξ a-h
cvar [] [] [] Ir refl = v-c (((λ ()) , (λ { { () } }))) (((λ ()) , (λ { { () } })))


