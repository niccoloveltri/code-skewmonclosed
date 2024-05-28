{-# OPTIONS --rewriting #-}

module SeqCalc where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List as List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Formulae

-- =======================================================================

-- Sequent calculus

infix 15 _∣_⊢_

data _∣_⊢_ : Stp → Cxt → Fma → Set where
  ax : {A : Fma} → just A ∣ [] ⊢ A
  pass : {Γ : Cxt} → {A C : Fma} → 
              just A ∣ Γ ⊢ C → ─ ∣ A ∷ Γ ⊢ C
  Ir : ─ ∣ [] ⊢ I
  Il : {Γ : Cxt} → {C : Fma} → 
              ─ ∣ Γ ⊢ C → just I ∣ Γ ⊢ C 
  ⊗r : {S : Stp} → {Γ Δ : Cxt} → {A B : Fma} → 
              S ∣ Γ ⊢ A → ─ ∣ Δ ⊢ B → S ∣ Γ ++ Δ ⊢ A ⊗ B 
  ⊗l : {Γ : Cxt} → {A B C : Fma} → 
              just A ∣ B ∷ Γ ⊢ C → just (A ⊗ B) ∣ Γ ⊢ C
  ⊸r : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              S ∣ Γ ++ A ∷ [] ⊢ B → S ∣ Γ ⊢ A ⊸ B
  ⊸l : {Γ Δ : Cxt} → {A B C : Fma} →
              ─ ∣ Γ ⊢ A → just B ∣ Δ ⊢ C →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢ C
                
subst-cxt : {S : Stp} → {Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → S ∣ Γ ⊢ A → S ∣ Γ' ⊢ A 
subst-cxt refl f = f

-- Admissible invertible rules

Il-1 : {Γ : Cxt} → {C : Fma}
  → just I ∣ Γ ⊢ C
  →  ─ ∣ Γ ⊢ C
Il-1 ax = Ir
Il-1 (Il f) = f
Il-1 (⊗r f g) = ⊗r (Il-1 f) g
Il-1 (⊸r f) = ⊸r (Il-1 f)

⊗l-1 : {Γ : Cxt} → {A B C : Fma}
  → just (A ⊗ B) ∣ Γ ⊢ C
  → just A ∣ B ∷ Γ ⊢ C
⊗l-1 ax = ⊗r ax (pass ax)
⊗l-1 (⊗r f g) = ⊗r (⊗l-1 f) g
⊗l-1 (⊗l f) = f
⊗l-1 (⊸r f) = ⊸r (⊗l-1 f)

⊸r-1 : {S : Stp} → {Γ : Cxt} → {A B : Fma}
  → S ∣ Γ ⊢ A ⊸ B
  → S ∣ Γ ∷ʳ A ⊢ B
⊸r-1 ax = ⊸l (pass ax) ax
⊸r-1 (pass f) = pass (⊸r-1 f)
⊸r-1 (Il f) = Il (⊸r-1 f)
⊸r-1 (⊗l f) = ⊗l (⊸r-1 f)
⊸r-1 (⊸r f) = f
⊸r-1 (⊸l f g) = ⊸l f (⊸r-1 g)


-- Cut admissibility

scut : {S : Stp} {Γ Δ : Cxt} {A C : Fma} 
        (f : S ∣ Γ ⊢ A) (g : just A ∣ Δ ⊢ C)  →
     ------------------------------------------
        S ∣ Γ ++ Δ ⊢ C

ccut : {T : Stp} {Γ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A C : Fma}
       (f : ─ ∣ Γ ⊢ A)  (g : T ∣ Δ ⊢ C) (eq : Δ ≡ Δ₀ ++ A ∷ Δ') →
       -----------------------------------------------------------------
                     T ∣ Δ₀ ++ Γ ++ Δ' ⊢ C

scut ax g = g
scut (pass f) g = pass (scut f g)
scut Ir ax = Ir
scut Ir (Il g) = g
scut Ir (⊗r g h) = ⊗r (scut Ir g) h
scut Ir (⊸r g) = ⊸r (scut Ir g)
scut (Il f) g = Il (scut f g)
scut (⊗r f f') ax = ⊗r f f'
scut (⊗r f f') (⊗r g g') = ⊗r (scut (⊗r f f') g) g'
scut (⊗r {Γ = Γ} f f') (⊗l g) = scut f (ccut [] f' g refl)
scut (⊗r f f') (⊸r g) = ⊸r (scut (⊗r f f') g)
scut (⊗l f) g = ⊗l (scut f g)
scut (⊸r f) ax = ⊸r f
scut (⊸r {Γ = Γ} f) (⊸l g g') = scut (ccut Γ g f refl) g'
scut (⊸r f) (⊸r g) = ⊸r (scut (⊸r f) g)
scut (⊸r f) (⊗r g g') = ⊗r (scut (⊸r f) g) g'
scut (⊸l f f') g = ⊸l f (scut f' g)

ccut Δ₀ f ax r = ⊥-elim ([]disj∷ Δ₀ r)
ccut Δ₀ f (pass g) r with cases∷ Δ₀ r
ccut .[] f (pass g) r | inj₁ (refl , refl , refl) = scut f g
ccut .(_ ∷ Γ₀) f (pass g) r | inj₂ (Γ₀ , p , refl) = pass (ccut Γ₀ f g p)
ccut Δ₀ f Ir r = ⊥-elim ([]disj∷ Δ₀ r)
ccut Δ₀ f (⊸r g) refl = ⊸r (ccut Δ₀ f g refl)
ccut Δ₀ f (Il g) r = Il (ccut Δ₀ f g r) 
ccut Δ₀ {Δ'} f (⊸l {Γ = Γ}{Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
ccut Δ₀ f (⊸l g g') p | inj₁ (Γ₀ , r , refl) = ⊸l (ccut Δ₀ f g r) g'
ccut ._ f (⊸l g g') p | inj₂ (Γ₀ , refl , refl) = ⊸l g (ccut Γ₀ f g' refl)
ccut Δ₀ {Δ'} f (⊗r {Γ = Γ}{Δ} g g') p with cases++ Δ₀ Γ Δ' Δ p
ccut Δ₀ f (⊗r g g') p | inj₁ (Γ₀ , refl , refl) = ⊗r (ccut Δ₀ f g refl) g'
ccut ._ f (⊗r g g') p | inj₂ (Γ₀ , refl , refl) = ⊗r g (ccut Γ₀  f g' refl)
ccut Δ₀ f (⊗l {B = B} g) r = ⊗l (ccut (B ∷ Δ₀) f g (cong (_∷_ B) r))


-- ====================================================================

-- Equality of proofs 

infixl 15 _∙_

data _≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where

-- -- equivalence relation
  refl : ∀{S Γ A} {f : S ∣ Γ ⊢ A} → f ≗ f
  ~_ : ∀{S Γ A} {f g : S ∣ Γ ⊢ A} → f ≗ g → g ≗ f
  _∙_ : ∀{S Γ A} {f g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗ h → f ≗ h

-- -- congruence
  pass : ∀{Γ A C} {f g : just A ∣ Γ ⊢ C} → f ≗ g → pass f ≗ pass g
  Il : ∀{Γ C} {f g : ─ ∣ Γ ⊢ C} → f ≗ g → Il f ≗ Il g
  ⊗l : ∀{Γ A B C} {f g : just A ∣ B ∷ Γ ⊢ C} → f ≗ g → ⊗l f ≗ ⊗l g
  ⊗r : ∀{S Γ Δ A B} {f g : S ∣ Γ ⊢ A} {f' g' : ─ ∣ Δ ⊢ B}
    → f ≗ g → f' ≗ g' → ⊗r f f' ≗ ⊗r g g'
  ⊸r : ∀{S Γ A C} {f g : S ∣ Γ ++ A ∷ [] ⊢ C} → f ≗ g → ⊸r f ≗ ⊸r g
  ⊸l : ∀{Γ Δ A B C} {f g : ─ ∣ Γ ⊢ A} {f' g' : just B ∣ Δ ⊢ C}
    → f ≗ g → f' ≗ g' → ⊸l f f' ≗ ⊸l g g'

-- -- η-conversions
  axI : ax ≗ Il Ir
  ax⊗ : {A B : Fma} → ax {A ⊗ B} ≗ ⊗l (⊗r ax (pass ax))
  ax⊸ : {A B : Fma} → ax {A ⊸ B} ≗ ⊸r (⊸l (pass ax) ax)

-- -- permutative conversions
  ⊗rpass : {Γ Δ : Cxt} {A A' B : Fma}
    → {f : just A' ∣ Γ ⊢ A} {g : ─ ∣ Δ ⊢ B}
    → ⊗r (pass f) g ≗ pass (⊗r f g)
  ⊗rIl : {Γ Δ : Cxt} {A B : Fma}
    → {f : ─ ∣ Γ ⊢ A} {g : ─ ∣ Δ ⊢ B}
    → ⊗r (Il f) g ≗ Il (⊗r f g)
  ⊗r⊗l : {Γ Δ : Cxt} {A A' B B' : Fma}
    → {f : just A' ∣ B' ∷ Γ ⊢ A} {g : ─ ∣ Δ ⊢ B}
    → ⊗r (⊗l f) g ≗ ⊗l (⊗r f g)
  ⊗r⊸l : {Γ Δ Λ : Cxt} {A A' B B' : Fma}
    → {f : ─ ∣ Γ ⊢ A'} {f' : just B' ∣ Δ ⊢ A} {g : ─ ∣ Λ ⊢ B}
    → ⊗r (⊸l f f') g ≗ ⊸l f (⊗r f' g)
  ⊸rpass : {Γ : Cxt} {A B C : Fma} {f : just A ∣ Γ ++ B ∷ [] ⊢ C}
    → ⊸r (pass f) ≗ pass (⊸r f)
  ⊸rIl : {Γ : Cxt} {B C : Fma} {f : ─ ∣ Γ ++ B ∷ [] ⊢ C}
    → ⊸r (Il f) ≗ Il (⊸r f)
  ⊸r⊗l : {Γ : Cxt} {A B D C : Fma} {f : just A ∣ B ∷ Γ ++ D ∷ [] ⊢ C}
    → ⊸r (⊗l f) ≗ ⊗l (⊸r f)
  ⊸r⊸l : {Γ Δ : Cxt} {A B C D : Fma}
    → {f : ─ ∣ Γ ⊢ A} {g : just B ∣ Δ ++ C ∷ [] ⊢ D}
    → ⊸r {Γ = Γ ++ Δ} (⊸l f g) ≗ ⊸l f (⊸r g)

≡-to-≗ : ∀{S Γ C} {f g : S ∣ Γ ⊢ C} → f ≡ g → f ≗ g
≡-to-≗ refl = refl

-- -- equational reasoning sugar for ≗

infix 4 _≗'_
infix 1 proof≗_
infixr 2 _≗〈_〉_
infix 3 _qed≗

data _≗'_ {S  : Stp}{Γ : Cxt}{A : Fma} (f g : S ∣ Γ ⊢ A) : Set where
  relto :  f ≗ g → f ≗' g

proof≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} {f g : S ∣ Γ ⊢ A} → f ≗' g → f ≗ g
proof≗ relto p = p

_≗〈_〉_ :  {S  : Stp}{Γ : Cxt}{A : Fma} (f : S ∣ Γ ⊢ A) {g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗' h → f ≗' h 

_ ≗〈 p 〉 relto q = relto (p ∙ q)

_qed≗  :  {S  : Stp}{Γ : Cxt}{A : Fma} (f : S ∣ Γ ⊢ A) → f ≗' f
_qed≗ _ = relto refl

-- Iterated ⊸r
⊸r⋆ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {A : Fma}
      (f : S ∣ Γ ++ Δ ⊢ A) →
  --------------------------------------------
           S ∣ Γ ⊢ Δ ⊸⋆ A

⊸r⋆ [] f = f
⊸r⋆ (A' ∷ Δ) f = ⊸r (⊸r⋆ Δ f)


-- Admissible equivalences
cong⊸r⋆ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma}
         {f g : S ∣ Γ ++ Δ ⊢ C} (eq : f ≗ g) →
          --------------------------------------------
           ⊸r⋆ Δ f ≗ ⊸r⋆ Δ g
cong⊸r⋆ [] eq = eq
cong⊸r⋆ (A ∷ Δ) eq = ⊸r (cong⊸r⋆ Δ eq)


⊸r⋆⊸r : {S : Stp} {Γ : Cxt} (Δ : Cxt) {A C : Fma}
         (f : S ∣ Γ ++ Δ ∷ʳ A ⊢ C) →
          --------------------------------------------
           ⊸r⋆ (Δ ∷ʳ A) f ≗ ⊸r⋆ Δ (⊸r {Γ = Γ ++ Δ} f)
⊸r⋆⊸r [] f = refl
⊸r⋆⊸r (A' ∷ Δ) f = ⊸r (⊸r⋆⊸r Δ f)

⊸r⋆pass : {Γ : Cxt} (Γ' : Cxt) {A C : Fma}
          {f : just A ∣ Γ ++ Γ' ⊢ C} → 
          ⊸r⋆ Γ' (pass f) ≗ pass (⊸r⋆ Γ' f)
⊸r⋆pass [] = refl
⊸r⋆pass (B ∷ Γ') = ⊸r (⊸r⋆pass Γ') ∙ ⊸rpass

⊸r⋆Il : {Γ : Cxt} (Γ' : Cxt) {C : Fma}
        {f : ─ ∣ Γ ++ Γ' ⊢ C} → 
        ⊸r⋆ Γ' (Il f) ≗ Il (⊸r⋆ Γ' f)
⊸r⋆Il [] = refl
⊸r⋆Il (B ∷ Γ') = ⊸r (⊸r⋆Il Γ') ∙ ⊸rIl

⊸r⋆⊗l : {Γ : Cxt} (Γ' : Cxt) {A B C : Fma}
        {f : just A ∣ B ∷ Γ ++ Γ' ⊢ C} → 
        ⊸r⋆ Γ' (⊗l f) ≗ ⊗l (⊸r⋆ Γ' f)
⊸r⋆⊗l [] = refl
⊸r⋆⊗l (B ∷ Γ') = ⊸r (⊸r⋆⊗l Γ') ∙ ⊸r⊗l

⊸r⋆⊸l : {Γ : Cxt} (Γ' : Cxt) {Δ : Cxt} {A B C : Fma}
         {f : ─ ∣ Γ ⊢ A} {g : just B ∣ Δ ++ Γ' ⊢ C} → 
         ⊸r⋆ {Γ = Γ ++ Δ} Γ' (⊸l f g) ≗ ⊸l f (⊸r⋆ Γ' g)
⊸r⋆⊸l [] = refl
⊸r⋆⊸l (A' ∷ Γ') {Δ}  = ⊸r (⊸r⋆⊸l Γ' {Δ ∷ʳ A'}) ∙ ⊸r⊸l


-- Iterated ⊸l
⊸l⋆ : {Δ : Cxt} {B C : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → just B ∣ Δ ⊢ C
  → just (List.map (λ x → proj₁ (proj₂ x)) Ξ ⊸⋆ B) ∣ concat (List.map proj₁ Ξ) ++ Δ ⊢ C
⊸l⋆ [] g = g
⊸l⋆ ((Γ , A , f) ∷ Ξ) g = ⊸l {Γ = Γ} f (⊸l⋆ Ξ g)

-- Iterated ccut
ccut⋆ : ∀{S : Stp} Γ₀ Γ₁ {Γ : Cxt} {C : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : S ∣ Γ ⊢ C)
  → (eq : Γ ≡ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ Γ₁)
  → S ∣ Γ₀ ++ concat (List.map proj₁ Ξ) ++ Γ₁ ⊢ C
ccut⋆ Γ₀ _ [] f eq = subst-cxt eq f
ccut⋆ Γ₀ Γ₁ ((Δ , A , g) ∷ Ξ) f refl = ccut Γ₀ g (ccut⋆ (Γ₀ ∷ʳ _) Γ₁ Ξ f refl) refl

