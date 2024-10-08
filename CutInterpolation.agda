{-# OPTIONS --rewriting #-}

module CutInterpolation where

open import Function
open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum hiding (reduce)
open import Data.List as List
open import Data.List.Relation.Unary.All
open import Relation.Unary hiding (_∈_)
open import Data.Product
open import Relation.Binary.PropositionalEquality as PE hiding (_≗_) hiding ([_])
open ≡-Reasoning
open import Utilities
open import Formulae
open import SeqCalc 
open import Equations
open import Interpolation


{-
The result of applying scut to the two derivations produced by sintrp is equal (modulo ≗) to the identity.
A similar result also holds for ccut⋆ and cintrp
-}

scut-sintrp : ∀ {S} Γ₁ Γ₂ {Γ C}
  → (f : S ∣ Γ ⊢ C)
  → (eq : Γ ≡ Γ₁ ++ Γ₂)
  →  scut (sIntrp.g (sintrp Γ₁ Γ₂ f eq)) (sIntrp.h (sintrp Γ₁ Γ₂ f eq)) ≗ subst-cxt eq f
ccut-cintrp : ∀{S} Γ₀ Γ₁ Γ₂ {Γ C}
  → (f : S ∣ Γ ⊢ C)
  → (eq : Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂)
  → ccut⋆ Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ Γ₁ Γ₂ f eq)) (cIntrp.g (cintrp Γ₀ Γ₁ Γ₂ f eq))
          ≗ subst-cxt eq f

scut-sintrp Γ₁ Γ₂ (Il f) refl = Il (scut-sintrp Γ₁ Γ₂ f refl)
scut-sintrp Γ₁ Γ₂ (⊗l f) refl = ⊗l (scut-sintrp (_ ∷ Γ₁) Γ₂ f refl)
scut-sintrp Γ₁ Γ₂ (⊸r {A = A}{B} f) refl =
  scut⊸r (sIntrp.g (sintrp Γ₁ (Γ₂ ∷ʳ _) f refl)) _
  ∙ ⊸r (scut-sintrp Γ₁ (Γ₂ ∷ʳ _) f refl)
scut-sintrp Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
scut-sintrp {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ ([] , refl , refl) =
  scut⊗r (sIntrp.g (sintrp Γ [] f refl)) (sIntrp.h (sintrp Γ [] f refl)) _
  ∙ ⊗r (scut-sintrp Γ [] f refl) refl
scut-sintrp {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (A' ∷ Γ' , refl , refl) = 
  scut⊗r (sIntrp.g (sintrp Γ [] f refl)) (sIntrp.h (sintrp Γ [] f refl)) _
  ∙ ⊗r (scut-sintrp Γ [] f refl) (scut-sintrp (A' ∷ Γ') Γ₂ g refl)
scut-sintrp Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) =
  scut⊗r (sIntrp.g (sintrp Γ₁ (_ ∷ Γ') f refl)) (sIntrp.h (sintrp Γ₁ (_ ∷ Γ') f refl)) g
  ∙ ⊗r (scut-sintrp Γ₁ (A' ∷ Γ') f refl) refl
scut-sintrp Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ Γ₁ Δ Γ₂ (sym eq)
scut-sintrp Γ₁ .(Γ' ++ Δ) (⊸l {Δ = Δ} {A}{B}{C} f g) refl | inj₁ (Γ' , refl , refl) = 
  ≡-to-≗ (scut⊸r⋆⊸ls (cIntrp.hs (cintrp Γ₁ Γ' [] f refl)) (⊸l (cIntrp.g (cintrp Γ₁ Γ' [] f refl)) (sIntrp.g (sintrp [] Δ g refl))) _)
  ∙ cong-scut1 (≡-to-≗ (ccut⋆⊸l1 Γ₁ [] (cIntrp.hs (cintrp Γ₁ Γ' [] f refl)) _ _)) _
  ∙ ⊸l (ccut-cintrp Γ₁ Γ' [] f refl) (scut-sintrp [] Δ g refl)
scut-sintrp _ Γ₂ (⊸l {Γ} {_} f g) refl | inj₂ (A' , Γ' , refl , refl) =
  ⊸l refl (scut-sintrp (A' ∷ Γ') Γ₂ g refl)
scut-sintrp [] [] ax refl = refl
scut-sintrp [] (A ∷ Γ₂) (pass f) refl = refl
scut-sintrp (A ∷ Γ₁) Γ₂ (pass f) refl = pass (scut-sintrp Γ₁ Γ₂ f refl)
scut-sintrp [] [] Ir refl = refl

ccut-cintrp Γ₀ Γ₁ Γ₂ (Il f) refl =
  ≡-to-≗ (ccut⋆Il Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ Γ₁ Γ₂ f refl)) (cIntrp.g (cintrp Γ₀ Γ₁ Γ₂ f refl)))
  ∙ Il (ccut-cintrp Γ₀ Γ₁ Γ₂ f refl)
ccut-cintrp Γ₀ Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
ccut-cintrp .(Γ ++ Γ₀) Γ₁ Γ₂ (⊗r {Γ = Γ} f g) refl | inj₁ (Γ₀ , refl , refl) =
  ≡-to-≗ (ccut⋆⊗r2 Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ Γ₁ Γ₂ g refl)) f (cIntrp.g (cintrp Γ₀ Γ₁ Γ₂ g refl)))
  ∙ ⊗r refl (ccut-cintrp Γ₀ Γ₁ Γ₂ g refl)
ccut-cintrp Γ₀ [] _ (⊗r f g) refl | inj₂ (A , Γ₁ , refl , refl) = refl
ccut-cintrp Γ₀ (A ∷ Γ₁) Γ₂ (⊗r {Δ = Δ} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
ccut-cintrp Γ₀ (A ∷ Γ₁) _ (⊗r f g) refl | inj₂ (A , ._ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) =
  ≡-to-≗ (ccut⋆⊗r1 Γ₀ (_ ∷ Γ₂) (cIntrp.hs (cintrp Γ₀ (A ∷ Γ₁) (A' ∷ Γ₂) f refl)) (cIntrp.g (cintrp Γ₀ (A ∷ Γ₁) (A' ∷ Γ₂) f refl)) g)
  ∙ ⊗r (ccut-cintrp Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl) refl
ccut-cintrp Γ₀ (A ∷ _) Γ₂ (⊗r f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁ , refl , refl) =
  ≡-to-≗ (ccut⋆⊗r Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ (A ∷ Γ') [] f refl)) (cIntrp.hs (cintrp [] Γ₁ Γ₂ g refl)) _ _)
   ∙ ⊗r (ccut-cintrp Γ₀ (_ ∷ Γ') [] f refl) (ccut-cintrp [] Γ₁ Γ₂ g refl)
ccut-cintrp Γ₀ Γ₁ Γ₂ (⊗l f) refl =
  ≡-to-≗ (ccut⋆⊗l Γ₀ Γ₂ (cIntrp.hs (cintrp (_ ∷ Γ₀) Γ₁ Γ₂ f refl)) (cIntrp.g (cintrp (_ ∷ Γ₀) Γ₁ Γ₂ f refl)))
  ∙ ⊗l (ccut-cintrp (_ ∷ Γ₀) Γ₁ Γ₂ f refl)
ccut-cintrp {S} Γ₀ Γ₁ Γ₂ (⊸r {A = A}{B} f) refl =
  ≡-to-≗ (ccut⋆⊸r Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ Γ₁ (Γ₂ ++ A ∷ []) f refl)) (cIntrp.g (cintrp Γ₀ Γ₁ (Γ₂ ++ A ∷ []) f refl)))
  ∙ ⊸r (ccut-cintrp Γ₀ Γ₁ (Γ₂ ∷ʳ _) f refl)
ccut-cintrp Γ₀ Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
ccut-cintrp _ Γ₁ Γ₂ (⊸l {Γ} f g) refl | inj₁ (Γ₀ , refl , refl) =
  ≡-to-≗ (ccut⋆⊸l2 Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ Γ₁ Γ₂ g refl)) f (cIntrp.g (cintrp Γ₀ Γ₁ Γ₂ g refl)))
  ∙ ⊸l refl (ccut-cintrp Γ₀ Γ₁ Γ₂ g refl)
ccut-cintrp Γ₀ [] _ (⊸l f g) refl | inj₂ (B , Γ' , refl , refl) = refl
ccut-cintrp Γ₀ (A ∷ Γ₁) Γ₂ (⊸l {Δ = Δ} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
ccut-cintrp Γ₀ (A ∷ Γ₁) _ (⊸l {Δ = Δ} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) =
  ≡-to-≗ (ccut⋆⊸l1 Γ₀ (_ ∷ Γ₂) (cIntrp.hs (cintrp Γ₀ (A ∷ Γ₁) (A' ∷ Γ₂) f refl)) (cIntrp.g (cintrp Γ₀ (A ∷ Γ₁) (A' ∷ Γ₂) f refl)) g)
  ∙ ⊸l (ccut-cintrp Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl) refl
ccut-cintrp Γ₀ (A ∷ _) Γ₂ (⊸l f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁ , refl , refl) =
  ≡-to-≗ (ccut⋆⊸l Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ (A ∷ Γ') [] f refl)) (cIntrp.hs (cintrp [] Γ₁ Γ₂ g refl)) _ _)
  ∙ ⊸l (ccut-cintrp Γ₀ (_ ∷ Γ') [] f refl) (ccut-cintrp [] Γ₁ Γ₂ g refl)
ccut-cintrp [] [] [] ax refl = refl
ccut-cintrp [] [] Γ₂ (pass f) refl = refl
ccut-cintrp [] (A ∷ Γ₁) Γ₂ (pass f) refl = pass (scut-sintrp Γ₁ Γ₂ f refl)
ccut-cintrp (A ∷ Γ₀) Γ₁ Γ₂ (pass f) refl =
  ≡-to-≗ (ccut⋆pass Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ Γ₁ Γ₂ f refl)) (cIntrp.g (cintrp Γ₀ Γ₁ Γ₂ f refl)))
  ∙ pass (ccut-cintrp Γ₀ Γ₁ Γ₂ f refl)
ccut-cintrp [] [] [] Ir refl = refl
