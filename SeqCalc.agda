{-# OPTIONS --rewriting #-}

module SeqCalc (At : Set) where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Formulae At

-- =======================================================================

-- Sequent calculus

infix 15 _∣_⊢_

data _∣_⊢_ : Stp → Cxt → Fma → Set where
  ax : {A : Fma} → just A ∣ [] ⊢ A
  pass : {Γ : Cxt} → {A C : Fma} → 
              just A ∣ Γ ⊢ C → nothing ∣ A ∷ Γ ⊢ C
  Ir : nothing ∣ [] ⊢ I
  Il : {Γ : Cxt} → {C : Fma} → 
              nothing ∣ Γ ⊢ C → just I ∣ Γ ⊢ C 
  ⊗r : {S : Stp} → {Γ Δ : Cxt} → {A B : Fma} → 
              S ∣ Γ ⊢ A → nothing ∣ Δ ⊢ B → S ∣ Γ ++ Δ ⊢ A ⊗ B 
  ⊗l : {Γ : Cxt} → {A B C : Fma} → 
              just A ∣ B ∷ Γ ⊢ C → just (A ⊗ B) ∣ Γ ⊢ C
  ⊸r : {S : Stp} → {Γ : Cxt} → {A B : Fma} →
              S ∣ Γ ++ A ∷ [] ⊢ B → S ∣ Γ ⊢ A ⊸ B
  ⊸l : {Γ Δ : Cxt} → {A B C : Fma} →
              nothing ∣ Γ ⊢ A → just B ∣ Δ ⊢ C →
              just (A ⊸ B) ∣ Γ ++ Δ ⊢ C
                
subst-cxt : {S : Stp} → {Γ Γ' : Cxt} → {A : Fma} → 
      Γ ≡ Γ' → S ∣ Γ ⊢ A → S ∣ Γ' ⊢ A 
subst-cxt refl f = f


-- ====================================================================

-- Equality of proofs 

infixl 15 _∙_

data _≗_ : {S  : Stp}{Γ : Cxt}{A : Fma} → S ∣ Γ ⊢ A → S ∣ Γ ⊢ A → Set where
  refl : ∀{S}{Γ}{A}{f : S ∣ Γ ⊢ A} → f ≗ f
  ~_ : ∀{S}{Γ}{A}{f g : S ∣ Γ ⊢ A} → f ≗ g → g ≗ f
  _∙_ : ∀{S}{Γ}{A}{f g h : S ∣ Γ ⊢ A} → f ≗ g → g ≗ h → f ≗ h
  pass : ∀{Γ}{A}{C}{f g : just A ∣ Γ ⊢ C} → f ≗ g → pass f ≗ pass g
  Il : ∀{Γ}{C}{f g : nothing ∣ Γ ⊢ C} → f ≗ g → Il f ≗ Il g
  ⊗l : ∀{Γ}{A}{B}{C}{f g : just A ∣ B ∷ Γ ⊢ C} → f ≗ g → ⊗l f ≗ ⊗l g
  ⊗r : ∀{S}{Γ}{Δ}{A}{B}{f g : S ∣ Γ ⊢ A}{f' g' : nothing ∣ Δ ⊢ B}
    → f ≗ g → f' ≗ g' → ⊗r f f' ≗ ⊗r g g'
  ⊸r : ∀{S}{Γ}{A}{C}{f g : S ∣ Γ ++ A ∷ [] ⊢ C} → f ≗ g → ⊸r f ≗ ⊸r g
  ⊸l : ∀{Γ}{Δ}{A}{B}{C}{f g : nothing ∣ Γ ⊢ A}{f' g' : just B ∣ Δ ⊢ C}
    → f ≗ g → f' ≗ g' → ⊸l f f' ≗ ⊸l g g'
  axI : ax ≗ Il Ir
  ax⊗ : {A B : Fma} → ax {A ⊗ B} ≗ ⊗l (⊗r ax (pass ax))
  ⊗rpass : {Γ Δ : Cxt}{A A' B : Fma}
    → {f : just A' ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (pass f) g ≗ pass (⊗r f g)
  ⊗rIl : {Γ Δ : Cxt}{A B : Fma}
    → {f : nothing ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (Il f) g ≗ Il (⊗r f g)
  ⊗r⊗l : {Γ Δ : Cxt}{A A' B B' : Fma}
    → {f : just A' ∣ B' ∷ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
    → ⊗r (⊗l f) g ≗ ⊗l (⊗r f g)
  ⊗r⊸l : {Γ Δ Λ : Cxt}{A A' B B' : Fma}
    → {f : nothing ∣ Γ ⊢ A'}{f' : just B' ∣ Δ ⊢ A}{g : nothing ∣ Λ ⊢ B}
    → ⊗r (⊸l f f') g ≗ ⊸l f (⊗r f' g)
  ax⊸ : {A B : Fma} → ax {A ⊸ B} ≗ ⊸r (⊸l (pass ax) ax)
  ⊸rpass : {Γ : Cxt}{A B C : Fma} {f : just A ∣ Γ ++ B ∷ [] ⊢ C}
    → ⊸r (pass f) ≗ pass (⊸r f)
  ⊸rIl : {Γ : Cxt}{B C : Fma} {f : nothing ∣ Γ ++ B ∷ [] ⊢ C}
    → ⊸r (Il f) ≗ Il (⊸r f)
  ⊸r⊗l : {Γ : Cxt}{A B D C : Fma} {f : just A ∣ B ∷ Γ ++ D ∷ [] ⊢ C}
    → ⊸r (⊗l f) ≗ ⊗l (⊸r f)
  ⊸r⊸l : {Γ Δ : Cxt}{A B C D : Fma}
    → {f : nothing ∣ Γ ⊢ A}{g : just B ∣ Δ ++ C ∷ [] ⊢ D}
    → ⊸r {Γ = Γ ++ Δ} (⊸l f g) ≗ ⊸l f (⊸r g)
    

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
        {f : nothing ∣ Γ ++ Γ' ⊢ C} → 
        ⊸r⋆ Γ' (Il f) ≗ Il (⊸r⋆ Γ' f)
⊸r⋆Il [] = refl
⊸r⋆Il (B ∷ Γ') = ⊸r (⊸r⋆Il Γ') ∙ ⊸rIl

⊸r⋆⊗l : {Γ : Cxt} (Γ' : Cxt) {A B C : Fma}
        {f : just A ∣ B ∷ Γ ++ Γ' ⊢ C} → 
        ⊸r⋆ Γ' (⊗l f) ≗ ⊗l (⊸r⋆ Γ' f)
⊸r⋆⊗l [] = refl
⊸r⋆⊗l (B ∷ Γ') = ⊸r (⊸r⋆⊗l Γ') ∙ ⊸r⊗l

⊸r⋆⊸l : {Γ : Cxt} (Γ' : Cxt) {Δ : Cxt} {A B C : Fma}
         {f : nothing ∣ Γ ⊢ A} {g : just B ∣ Δ ++ Γ' ⊢ C} → 
         ⊸r⋆ {Γ = Γ ++ Δ} Γ' (⊸l f g) ≗ ⊸l f (⊸r⋆ Γ' g)
⊸r⋆⊸l [] = refl
⊸r⋆⊸l (A' ∷ Γ') {Δ}  = ⊸r (⊸r⋆⊸l Γ' {Δ ∷ʳ A'}) ∙ ⊸r⊸l


