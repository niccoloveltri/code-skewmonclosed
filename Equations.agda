{-# OPTIONS --rewriting #-}

module Equations where

open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List as List
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Formulae 
open import SeqCalc 


-- =======================================================================

-- Unitality and assiciativity of cut rules

scut-unit : {S : Stp}{Γ : Cxt}{A : Fma}(f : S ∣ Γ ⊢ A) → scut f ax ≡ f
scut-unit ax = refl
scut-unit (pass f) = cong pass (scut-unit f)
scut-unit Ir = refl
scut-unit (⊗r f f') = refl
scut-unit (Il f) = cong Il (scut-unit f)
scut-unit (⊗l f) = cong ⊗l (scut-unit f)
scut-unit (⊸l f f') = cong (⊸l f) (scut-unit f')
scut-unit (⊸r f) = refl

ccut-unit : {S : Stp} (Δ₀ : Cxt) {Δ₁ Δ : Cxt}{A C : Fma}
  → (f : S ∣ Δ ⊢ C)
  → (eq : Δ ≡ Δ₀ ++ A ∷ Δ₁)
  → ccut Δ₀ (pass ax) f eq ≡ subst-cxt eq f
ccut-unit Δ₀ ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
ccut-unit [] (pass f) refl = refl
ccut-unit (A ∷ Δ₀) (pass f) refl = cong pass (ccut-unit Δ₀ f refl)
ccut-unit Δ₀ Ir eq = ⊥-elim ([]disj∷ Δ₀ eq)
ccut-unit Δ₀ (Il f) refl = cong Il (ccut-unit Δ₀ f refl)
ccut-unit Δ₀ (⊗l f) refl = cong ⊗l (ccut-unit (_ ∷ Δ₀) f refl)
ccut-unit Δ₀ (⊸r f) refl = cong ⊸r (ccut-unit Δ₀ f refl)
ccut-unit Δ₀ {Δ₁} (⊗r {Γ = Γ} {Δ} f f₁) eq with cases++ Δ₀ Γ Δ₁ Δ eq
ccut-unit Δ₀ {.(Γ₀ ++ Δ)} (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} f f₁) refl | inj₁ (Γ₀ , refl , refl) =
  cong (λ x → ⊗r {Γ = Δ₀ ++ _ ∷ Γ₀} x f₁) (ccut-unit Δ₀ f refl)
ccut-unit .(Γ ++ Γ₀) {Δ₁} (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ₁)} f f₁) refl | inj₂ (Γ₀ , refl , refl) =
  cong (⊗r f) (ccut-unit Γ₀ f₁ refl)
ccut-unit Δ₀ {Δ₁} (⊸l {Γ} {Δ} f f₁) eq with cases++ Δ₀ Γ Δ₁ Δ eq
ccut-unit Δ₀ {.(Γ₀ ++ Δ)} (⊸l {.(Δ₀ ++ _ ∷ Γ₀)} {Δ} f f₁) refl | inj₁ (Γ₀ , refl , refl) =
  cong (λ x → ⊸l {Δ₀ ++ _ ∷ Γ₀} x f₁) (ccut-unit Δ₀ f refl)
ccut-unit .(Γ ++ Γ₀) {Δ₁} (⊸l {Γ} {.(Γ₀ ++ _ ∷ Δ₁)} f f₁) refl | inj₂ (Γ₀ , refl , refl) =
  cong (⊸l f) (ccut-unit Γ₀ f₁ refl)

scutIr-hass : {Γ₂ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A₂ C : Fma}
  → (f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : just I ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A₂ ∷ Δ')
  → scut Ir (ccut Δ₀ f₂ g r) ≡ ccut Δ₀ f₂ (scut Ir g) r
scutIr-hass Δ₀ f ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
scutIr-hass Δ₀ f (Il g) eq = refl
scutIr-hass {Γ₂ = Γ₂} Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g₁) eq with cases++ Δ₀ Γ Δ' Δ eq
... | inj₁ (Γ₀ , refl , refl) = cong (λ x → ⊗r {Γ = Δ₀ ++ Γ₂ ++ Γ₀} x g₁) (scutIr-hass Δ₀ f g refl)
... | inj₂ (Γ₀ , refl , refl) = refl
scutIr-hass Δ₀ f (⊸r g) refl = cong ⊸r (scutIr-hass Δ₀ f g refl)

scutscutIr-vass : {Δ Δ' : Cxt} → {B C : Fma}
  → (g : just I ∣ Δ ⊢ B)(h : just B ∣ Δ' ⊢ C)
  → scut Ir (scut g h) ≡ scut (scut Ir g) h
scutscutIr-vass ax h = refl
scutscutIr-vass (Il g) h = refl
scutscutIr-vass (⊗r g g₁) ax = refl
scutscutIr-vass (⊗r {Γ = Γ}{Δ} g g₁) (⊗r {Γ = Γ₁} h h₁) =
  cong (λ x → ⊗r {Γ = Γ ++ Δ ++ Γ₁} x h₁) (scutscutIr-vass (⊗r g g₁) h)
scutscutIr-vass (⊗r g g₁) (⊗l h) = scutscutIr-vass g (ccut [] g₁ h refl)
scutscutIr-vass (⊗r g g₁) (⊸r h) = cong ⊸r (scutscutIr-vass (⊗r g g₁) h)
scutscutIr-vass (⊸r g) ax = refl
scutscutIr-vass (⊸r {Γ = Γ} g) (⊗r {Γ = Δ} h h₁) =
  cong (λ x → ⊗r {Γ = Γ ++ Δ} x h₁) (scutscutIr-vass (⊸r g) h)
scutscutIr-vass (⊸r g) (⊸r h) = cong ⊸r (scutscutIr-vass (⊸r g) h)
scutscutIr-vass (⊸r {Γ = Δ} g) (⊸l {Γ = Γ} h h₁) =
  trans (scutscutIr-vass (ccut Δ h g refl) h₁)
        (cong (λ x → scut {Γ = Δ ++ Γ} x h₁) (scutIr-hass Δ h g refl))

scut⊗r-hass : {T : Stp}{Γ₁ Γ₁' Γ₂ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A₁ A₁' A₂ C : Fma}
  → (f₁ : T ∣ Γ₁ ⊢ A₁)(f₁' : nothing ∣ Γ₁' ⊢ A₁')(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : just (A₁ ⊗ A₁') ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A₂ ∷ Δ')
  → scut (⊗r f₁ f₁') (ccut Δ₀ f₂ g r) ≡ ccut (Γ₁ ++ Γ₁' ++ Δ₀) f₂ (scut (⊗r f₁ f₁') g) (cong (_++_ (Γ₁ ++ Γ₁')) r)
scut⊸r-hass : {T : Stp}{Γ₁ Γ₂ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A₁ A₂ B C : Fma}
  → (f₁ : T ∣ Γ₁ ∷ʳ B ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : just (B ⊸ A₁) ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A₂ ∷ Δ')
  → scut (⊸r f₁) (ccut Δ₀ f₂ g r) ≡ ccut (Γ₁ ++ Δ₀) f₂ (scut (⊸r f₁) g) (cong (Γ₁ ++_) r)
scut-hass : {T : Stp}{Γ₁ Γ₂ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' : Cxt} → {A₁ A₂ C : Fma}
  → (f₁ : T ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : just A₁ ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A₂ ∷ Δ')
  → scut f₁ (ccut Δ₀ f₂ g r) ≡ ccut (Γ₁ ++ Δ₀) f₂ (scut f₁ g) (cong (_++_ Γ₁) r)
ccut-hass : {T : Stp} → {Γ₁ Γ₂ : Cxt} → (Δ₀ : Cxt) → {Δ Δ₁ Δ₂ : Cxt} → {A₁ A₂ C : Fma}
  → (f₁ : nothing ∣ Γ₁ ⊢ A₁)(f₂ : nothing ∣ Γ₂ ⊢ A₂)(g : T ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A₁ ∷ Δ₁ ++ A₂ ∷ Δ₂)
  → ccut Δ₀ f₁ (ccut (Δ₀ ++ A₁ ∷ Δ₁) f₂ g r) refl ≡ ccut (Δ₀ ++ Γ₁ ++ Δ₁) f₂ (ccut Δ₀ f₁ g r) refl
scutscut⊗r-vass : {S : Stp} → {Γ Γ' Δ Δ' : Cxt} → {A A' B C : Fma}
  → (f : S ∣ Γ ⊢ A)(f' : nothing ∣ Γ' ⊢ A')(g : just (A ⊗ A') ∣ Δ ⊢ B)(h : just B ∣ Δ' ⊢ C)
  → scut (⊗r f f') (scut g h) ≡ scut (scut (⊗r f f') g) h
scutscut⊸r-vass : {S : Stp} → {Γ Δ Δ' : Cxt} → {A A' B C : Fma}
  → (f : S ∣ Γ ∷ʳ A ⊢ A')(g : just (A ⊸ A') ∣ Δ ⊢ B)(h : just B ∣ Δ' ⊢ C)
  → scut (⊸r f) (scut g h) ≡ scut (scut (⊸r f) g) h
scutscut-vass : {S : Stp} → {Γ Δ Δ' : Cxt} → {A B C : Fma}
  → (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(h : just B ∣ Δ' ⊢ C)
  → scut f (scut g h) ≡ scut (scut f g) h
ccutscut⊸r-vass : {T : Stp} → {Γ : Cxt} → (Δ₀ : Cxt) → {Δ' Δ'' : Cxt} → {A A' B C : Fma}
  → (f : nothing ∣ Γ ⊢ A)(g : T ∣ Δ₀ ++ A ∷ Δ' ∷ʳ A' ⊢ B)(h : just (A' ⊸ B) ∣ Δ'' ⊢ C)
  → ccut Δ₀ f (scut (⊸r {Γ = Δ₀ ++ A ∷ Δ'} g) h) refl ≡ scut (ccut Δ₀ f (⊸r {Γ = Δ₀ ++ A ∷ Δ'} g) refl) h
ccutscut⊗r1-vass : {T : Stp} → {Γ : Cxt} → (Δ₀ : Cxt) → {Δ Δ' Δ'' : Cxt} → {A B B' C : Fma}
  → (f : nothing ∣ Γ ⊢ A)(g : T ∣ Δ₀ ++ A ∷ Δ' ⊢ B)(g' : nothing ∣ Δ ⊢ B')(h : just (B ⊗ B') ∣ Δ'' ⊢ C)
  → ccut Δ₀ f (scut (⊗r {Γ = Δ₀ ++ A ∷ Δ'} g g') h) refl ≡ scut (⊗r (ccut Δ₀ f g refl) g') h
ccutscut⊗r2-vass : {T : Stp} → {Γ : Cxt} → (Δ₀ : Cxt) → {Δ Δ' Δ'' : Cxt} → {A B B' C : Fma}
  → (f : nothing ∣ Γ ⊢ A)(g : T ∣ Δ ⊢ B)(g' : nothing ∣ Δ₀ ++ A ∷ Δ' ⊢ B')(h : just (B ⊗ B') ∣ Δ'' ⊢ C)
  → ccut (Δ ++ Δ₀) f (scut (⊗r g g') h) refl ≡ scut (⊗r g (ccut Δ₀ f g' refl)) h
ccutscut-vass : {T : Stp} → {Γ Δ : Cxt} → (Δ₀ : Cxt) → {Δ' Δ'' : Cxt} → {A B C : Fma}
  → (f : nothing ∣ Γ ⊢ A)(g : T ∣ Δ ⊢ B)(h : just B ∣ Δ'' ⊢ C)
  → (r : Δ ≡ Δ₀ ++ A ∷ Δ')
  → ccut Δ₀ f (scut g h) (cong₂ _++_ r (refl {x = Δ''})) ≡ scut (ccut Δ₀ f g r) h
ccutccut-vass : {T : Stp} → {Γ Δ : Cxt} → (Γ₀ Δ₀ : Cxt) → {Δ' Γ' : Cxt} → {A B C : Fma}
  → (f : nothing ∣ Γ ⊢ A)(g : nothing ∣ Γ₀ ++ A ∷ Γ' ⊢ B)(h : T ∣ Δ ⊢ C)
  → (r : Δ ≡ Δ₀ ++ B ∷ Δ')
  → ccut (Δ₀ ++ Γ₀) f (ccut Δ₀ g h r) refl ≡ ccut Δ₀ (ccut Γ₀ f g refl) h r

ccutccut-vass Γ₀ Δ₀ f g ax r = ⊥-elim ([]disj∷ Δ₀ r)
ccutccut-vass Γ₀ [] f g (pass h) refl = ccutscut-vass Γ₀ f g h refl
ccutccut-vass Γ₀ (A ∷ Δ₀) f g (pass h) refl = cong pass (ccutccut-vass Γ₀ Δ₀ f g h refl)
ccutccut-vass Γ₀ Δ₀ f g Ir r = ⊥-elim ([]disj∷ Δ₀ r)
ccutccut-vass Γ₀ Δ₀ f g (Il h) refl = cong Il (ccutccut-vass Γ₀ Δ₀ f g h refl) 
ccutccut-vass Γ₀ Δ₀ f g (⊗l h) refl = cong ⊗l (ccutccut-vass Γ₀ (_ ∷ Δ₀) f g h refl)
ccutccut-vass Γ₀ Δ₀ f g (⊸r h) refl = cong ⊸r (ccutccut-vass Γ₀ Δ₀ f g h refl)
ccutccut-vass {Γ = Γ₁} Γ₀ Δ₀ {Δ'} {Γ'} {A = A} f g (⊗r {Γ = Γ} {Δ} h h₁) r with cases++ Δ₀ Γ Δ' Δ r
... | inj₁ (Λ , refl , refl) rewrite cases++-inj₁ (Δ₀ ++ Γ₀) (Γ' ++ Λ) Δ A =
  cong (λ x → ⊗r {Γ = Δ₀ ++ Γ₀ ++ Γ₁ ++ Γ' ++ Λ} x h₁) (ccutccut-vass Γ₀ Δ₀ f g h refl)
... | inj₂ (Λ , refl , refl) rewrite cases++-inj₂ (Λ ++ Γ₀) Γ (Γ' ++ Δ') A =
  cong (⊗r h) (ccutccut-vass Γ₀ Λ f g h₁ refl)
ccutccut-vass {Γ = Γ₁} Γ₀ Δ₀ {Δ'} {Γ'} {A = A} f g (⊸l {Γ} {Δ} h h₁) r with cases++ Δ₀ Γ Δ' Δ r 
... | inj₁ (Λ , refl , refl) rewrite cases++-inj₁ (Δ₀ ++ Γ₀) (Γ' ++ Λ) Δ A =
  cong (λ x → ⊸l {Δ₀ ++ Γ₀ ++ Γ₁ ++ Γ' ++ Λ} x h₁) (ccutccut-vass Γ₀ Δ₀ f g h refl)
... | inj₂ (Λ , refl , refl) rewrite cases++-inj₂ (Λ ++ Γ₀) Γ (Γ' ++ Δ') A =
  cong (⊸l h) (ccutccut-vass Γ₀ Λ f g h₁ refl)

ccutscut⊸r-vass Δ₀ f g ax = refl
ccutscut⊸r-vass {Γ = Γ₁} Δ₀ {Δ'} {A = A} f g (⊗r {Γ = Γ}{Δ} h h₁)
  rewrite cases++-inj₁ Δ₀ (Δ' ++ Γ) Δ A =
  cong (λ x → ⊗r {Γ = Δ₀ ++ Γ₁ ++ Δ' ++ Γ} x h₁) (ccutscut⊸r-vass Δ₀ f g h)
ccutscut⊸r-vass Δ₀ f g (⊸r h) = cong ⊸r (ccutscut⊸r-vass Δ₀ f g h)
ccutscut⊸r-vass {Γ = Γ} Δ₀ {Δ'} f g (⊸l {Γ = Γ₁} h h₁) =
  trans (ccutscut-vass Δ₀ f (ccut (Δ₀ ++ _ ∷ Δ') h g refl) h₁ refl)
        (cong (λ x → scut {Γ = Δ₀ ++ Γ ++ Δ' ++ Γ₁} x h₁) (ccut-hass Δ₀ f h g refl))

ccutscut⊗r1-vass Δ₀ {Δ}{Δ'} {A = A} f g g' ax
  rewrite cases++-inj₁ Δ₀ Δ' Δ A = refl
ccutscut⊗r1-vass {Γ = Γ₁} Δ₀ {Δ₁} {Δ'} {A = A} f g g' (⊗r {Γ = Γ} {Δ} h h₁)
  rewrite cases++-inj₁ Δ₀ (Δ' ++ Δ₁ ++ Γ) Δ A =
  cong (λ x → ⊗r {Γ = Δ₀ ++ Γ₁ ++ Δ' ++ Δ₁ ++ Γ} x h₁) (ccutscut⊗r1-vass Δ₀ f g g' h)
ccutscut⊗r1-vass Δ₀ f g g' (⊗l h) = ccutscut-vass Δ₀ f g (ccut [] g' h refl) refl
ccutscut⊗r1-vass Δ₀ f g g' (⊸r h) = cong ⊸r (ccutscut⊗r1-vass Δ₀ f g g' h)

ccutscut⊗r2-vass Δ₀ {Δ} {Δ'} {A = A} f g g' ax
  rewrite cases++-inj₂ Δ₀ Δ Δ' A = refl
ccutscut⊗r2-vass {Γ = Γ₁} Δ₀ {Δ₁} {Δ'} {A = A} f g g' (⊗r {Γ = Γ} {Δ} h h₁)
  rewrite cases++-inj₁ (Δ₁ ++ Δ₀) (Δ' ++ Γ) Δ A =
  cong (λ x → ⊗r {Γ = Δ₁ ++ Δ₀ ++ Γ₁ ++ Δ' ++ Γ} x h₁) (ccutscut⊗r2-vass Δ₀ f g g' h)
ccutscut⊗r2-vass Δ₀ f g g' (⊗l h) =
  trans (sym (scut-hass Δ₀ g f (ccut [] g' h refl) refl))
        (cong (scut g) (ccutccut-vass Δ₀ [] f g' h refl))
ccutscut⊗r2-vass Δ₀ f g g' (⊸r h) = cong ⊸r (ccutscut⊗r2-vass Δ₀ f g g' h)

ccutscut-vass Δ₀ f ax h r = ⊥-elim ([]disj∷ Δ₀ r)
ccutscut-vass [] f (pass g) h refl = scutscut-vass f g h
ccutscut-vass (_ ∷ Δ₀) f (pass g) h refl = cong pass (ccutscut-vass Δ₀ f g h refl)
ccutscut-vass Δ₀ f Ir h r = ⊥-elim ([]disj∷ Δ₀ r)
ccutscut-vass Δ₀ f (Il g) h refl = cong Il (ccutscut-vass Δ₀ f g h refl)
ccutscut-vass Δ₀ f (⊗l g) h refl = cong ⊗l (ccutscut-vass (_ ∷ Δ₀) f g h refl)
ccutscut-vass Δ₀ {Δ'} f (⊸l {Γ} {Δ} g g₁) h r with cases++ Δ₀ Γ Δ' Δ r
ccutscut-vass Δ₀ {.(Λ ++ Δ)} {Δ''} {A = A} f (⊸l {.(Δ₀ ++ _ ∷ Λ)} {Δ} g g₁) h refl | inj₁ (Λ , refl , refl)
  rewrite cases++-inj₁ Δ₀ Λ (Δ ++ Δ'') A = refl
ccutscut-vass .(Γ ++ Λ) {Δ'} {Δ''} {A = A} f (⊸l {Γ} {.(Λ ++ _ ∷ Δ')} g g₁) h refl | inj₂ (Λ , refl , refl)
  rewrite cases++-inj₂ Λ Γ (Δ' ++ Δ'') A = cong (⊸l g) (ccutscut-vass Λ f g₁ h refl)
ccutscut-vass Δ₀ f (⊸r g) h refl = ccutscut⊸r-vass Δ₀ f g h
ccutscut-vass Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} g g₁) h r with cases++ Δ₀ Γ Δ' Δ r
ccutscut-vass Δ₀ {.(Γ₀ ++ Δ)} f (⊗r {Γ = .(Δ₀ ++ _ ∷ Γ₀)} {Δ} g g₁) h refl | inj₁ (Γ₀ , refl , refl) = ccutscut⊗r1-vass Δ₀ f g g₁ h
ccutscut-vass .(Γ ++ Γ₀) {Δ'} f (⊗r {Γ = Γ} {.(Γ₀ ++ _ ∷ Δ')} g g₁) h refl | inj₂ (Γ₀ , refl , refl) = ccutscut⊗r2-vass Γ₀ f g g₁ h

scutscut⊗r-vass f f' ax h = refl
scutscut⊗r-vass f f' (⊗r g g₁) ax = refl
scutscut⊗r-vass {Γ = Γ}{Γ'} f f' (⊗r {Γ = Δ}{Δ'} g g₁) (⊗r {Γ = Λ} h h₁) =
  cong (λ x → ⊗r {Γ = Γ ++ Γ' ++ Δ ++ Δ' ++ Λ} x h₁) (scutscut⊗r-vass f f' (⊗r g g₁) h)
scutscut⊗r-vass f f' (⊗r g g₁) (⊗l h) = scutscut⊗r-vass f f' g (ccut [] g₁ h refl)
scutscut⊗r-vass f f' (⊗r g g₁) (⊸r h) = cong ⊸r (scutscut⊗r-vass f f' (⊗r g g₁) h)
scutscut⊗r-vass {Γ = Γ}{Γ'} f f' (⊗l {Δ} g) h =
  trans (cong (scut f) (ccutscut-vass [] f' g h refl))
        (scutscut-vass f (ccut [] f' g refl) h)
scutscut⊗r-vass f f' (⊸r g) ax = refl
scutscut⊗r-vass {Γ = Γ}{Γ'} f f' (⊸r {Γ = Δ} g) (⊗r {Γ = Λ} h h₁) =
  cong (λ x → ⊗r {Γ = Γ ++ Γ' ++ Δ ++ Λ} x h₁) (scutscut⊗r-vass f f' (⊸r g) h)
scutscut⊗r-vass f f' (⊸r g) (⊸r h) = cong ⊸r (scutscut⊗r-vass f f' (⊸r g) h)
scutscut⊗r-vass {Γ = Γ}{Γ'} f f' (⊸r {Γ = Δ} g) (⊸l {Γ = Λ} h h₁) =
  trans (scutscut⊗r-vass f f' (ccut Δ h g refl) h₁)
        (cong (λ x → scut {Γ = Γ ++ Γ' ++ Δ ++ Λ} x h₁) (scut⊗r-hass Δ f f' h g refl))

scutscut⊸r-vass f ax h = refl
scutscut⊸r-vass f (⊗r g g₁) ax = refl
scutscut⊸r-vass {Γ = Γ} f (⊗r {Γ = Δ}{Δ'} g g₁) (⊗r {Γ = Λ} h h₁) =
  cong (λ x → ⊗r {Γ = Γ ++ Δ ++ Δ' ++ Λ} x h₁) (scutscut⊸r-vass f (⊗r g g₁) h)
scutscut⊸r-vass f (⊗r g g₁) (⊗l h) = scutscut⊸r-vass f g (ccut [] g₁ h refl)
scutscut⊸r-vass f (⊗r g g₁) (⊸r h) = cong ⊸r (scutscut⊸r-vass f (⊗r g g₁) h)
scutscut⊸r-vass f (⊸r g) ax = refl
scutscut⊸r-vass {Γ = Γ} f (⊸r {Γ = Δ} g) (⊗r {Γ = Λ} h h₁) = 
  cong (λ x → ⊗r {Γ = Γ ++ Δ ++ Λ} x h₁) (scutscut⊸r-vass f (⊸r g) h)
scutscut⊸r-vass f (⊸r g) (⊸r h) = cong ⊸r (scutscut⊸r-vass f (⊸r g) h)
scutscut⊸r-vass {Γ = Γ} f (⊸r {Γ = Δ} g) (⊸l {Γ = Λ}{Λ'} h h₁) =
  trans (scutscut⊸r-vass f (ccut Δ h g refl) h₁)
        (cong (λ x → scut {Γ = Γ ++ Δ ++ Λ} x h₁) (scut⊸r-hass Δ f h g refl))
scutscut⊸r-vass {Γ = Γ} f (⊸l g g₁) h = scutscut-vass (ccut Γ g f refl) g₁ h

scutscut-vass ax g h = refl
scutscut-vass (pass f) g h = cong pass (scutscut-vass f g h)
scutscut-vass (Il f) g h = cong Il (scutscut-vass f g h)
scutscut-vass (⊗l f) g h = cong ⊗l (scutscut-vass f g h)
scutscut-vass (⊸l f f') g h = cong (⊸l f) (scutscut-vass f' g h)
scutscut-vass Ir g h = scutscutIr-vass g h
scutscut-vass (⊗r f f') g h = scutscut⊗r-vass f f' g h
scutscut-vass (⊸r f) g h = scutscut⊸r-vass f g h

scut⊸r-hass Δ₀ f₁ f₂ ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
scut⊸r-hass Δ₀ {Δ'} {A₂ = A₂} f₁ f₂ (⊗r {Γ = Γ} {Δ} g g') eq with cases++ Δ₀ Γ Δ' Δ eq
scut⊸r-hass {Γ₁ = Γ₁}{Γ₂} Δ₀ {A₂ = A₂} f₁ f₂ (⊗r {Γ = .(Δ₀ ++ A₂ ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) 
  rewrite cases++-inj₁ (Γ₁ ++ Δ₀) Γ₀ Δ A₂ = cong (λ x → ⊗r {Γ = Γ₁ ++ Δ₀ ++ Γ₂ ++ Γ₀} x g') (scut⊸r-hass Δ₀ f₁ f₂ g refl)
scut⊸r-hass {Γ₁ = Γ₁} .(Γ ++ Γ₀) {Δ'} {A₂ = A₂} f₁ f₂ (⊗r {Γ = Γ} {.(Γ₀ ++ A₂ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ Γ₀ (Γ₁ ++ Γ) Δ' A₂ = refl
scut⊸r-hass Δ₀ f₁ f₂ (⊸r g) refl = cong ⊸r (scut⊸r-hass Δ₀ f₁ f₂ g refl)
scut⊸r-hass Δ₀ {Δ'} {A₂ = A₂} f₁ f₂ (⊸l {Γ} {Δ} g g') eq with cases++ Δ₀ Γ Δ' Δ eq
scut⊸r-hass {Γ₁ = Γ₁}{Γ₂} Δ₀ {.(Γ₀ ++ Δ)} {A₂ = A₂} f₁ f₂ (⊸l {.(Δ₀ ++ A₂ ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl) =
  trans (cong (λ x → scut {Γ = Γ₁ ++ Δ₀ ++ Γ₂ ++ Γ₀} x g') (sym (ccutccut-vass Δ₀ Γ₁ f₂ g f₁ refl)))
        (sym (ccutscut-vass (Γ₁ ++ Δ₀) f₂ (ccut Γ₁ g f₁ refl) g' refl))
scut⊸r-hass {Γ₁ = Γ₁} .(Γ ++ Γ₀) {Δ'} {A₂ = A₂} f₁ f₂ (⊸l {Γ} {.(Γ₀ ++ A₂ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) = 
  scut-hass Γ₀ (ccut Γ₁ g f₁ refl) f₂ g' refl

scut⊗r-hass Δ₀ f₁ f₃ f₂ ax eq = ⊥-elim ([]disj∷ Δ₀ eq)
scut⊗r-hass Δ₀ {Δ'} f₁ f₃ f₂ (⊗r {Γ = Γ} {Δ} g g') eq with cases++ Δ₀ Γ Δ' Δ eq
scut⊗r-hass {Γ₁ = Γ₁} {Γ₁'} {Γ₂} Δ₀ {.(Γ₀ ++ Δ)} {A₂ = A₂} f₁ f₃ f₂ (⊗r {Γ = .(Δ₀ ++ A₂ ∷ Γ₀)} {Δ} g g') refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Γ₁' ++ Δ₀) Γ₀ Δ A₂ = cong (λ x → ⊗r {Γ = Γ₁ ++ Γ₁' ++ Δ₀ ++ Γ₂ ++ Γ₀} x g') (scut⊗r-hass Δ₀ f₁ f₃ f₂ g refl)
scut⊗r-hass {Γ₁ = Γ₁} {Γ₁'} {Γ₂} .(Γ ++ Γ₀) {Δ'} {A₂ = A₂} f₁ f₃ f₂ (⊗r {Γ = Γ} {.(Γ₀ ++ A₂ ∷ Δ')} g g') refl | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ Γ₀ (Γ₁ ++ Γ₁' ++ Γ) Δ' A₂ = refl
scut⊗r-hass {Γ₁ = Γ₁}{Γ₁'}{Γ₂} Δ₀ f₁ f₃ f₂ (⊗l g) refl =
  trans (cong (scut f₁) (ccut-hass [] f₃ f₂ g refl))
        (scut-hass (Γ₁' ++ Δ₀) f₁ f₂ (ccut [] f₃ g refl) refl)
scut⊗r-hass Δ₀ f₁ f₃ f₂ (⊸r g) refl = cong ⊸r (scut⊗r-hass Δ₀ f₁ f₃ f₂ g refl)

scut-hass Δ₀ ax f₂ g refl = refl
scut-hass Δ₀ (pass f₁) f₂ g refl = cong pass (scut-hass Δ₀ f₁ f₂ g refl)
scut-hass Δ₀ Ir f₂ g refl = scutIr-hass Δ₀ f₂ g refl
scut-hass Δ₀ (⊗r f₁ f₃) f₂ g eq = scut⊗r-hass Δ₀ f₁ f₃ f₂ g eq
scut-hass Δ₀ (Il f₁) f₂ g refl = cong Il (scut-hass Δ₀ f₁ f₂ g refl)
scut-hass Δ₀ (⊗l f₁) f₂ g refl = cong ⊗l (scut-hass Δ₀ f₁ f₂ g refl)
scut-hass Δ₀ (⊸r f₁) f₂ g eq = scut⊸r-hass Δ₀ f₁ f₂ g eq
scut-hass Δ₀ {Δ'} {A₂ = A₂} (⊸l {Γ} {Δ} f₁ f₃) f₂ g refl
  rewrite cases++-inj₂ (Δ ++ Δ₀) Γ Δ' A₂ = cong (⊸l f₁) (scut-hass Δ₀ f₃ f₂ g refl)

ccut-hass Δ₀ f₁ f₂ ax r = ⊥-elim ([]disj∷ Δ₀ r)
ccut-hass [] {Δ₁ = Δ₁} f₁ f₂ (pass g) refl = scut-hass Δ₁ f₁ f₂ g refl
ccut-hass (_ ∷ Δ₀) f₁ f₂ (pass g) refl = cong pass (ccut-hass Δ₀ f₁ f₂ g refl)
ccut-hass Δ₀ f₁ f₂ Ir r = ⊥-elim ([]disj∷ Δ₀ r)
ccut-hass Δ₀ {Δ₁ = Δ₁}{Δ₂} f₁ f₂ (⊗r {Γ = Γ}{Δ} g g') r with cases++ (Δ₀ ++ _ ∷ Δ₁) Γ Δ₂ Δ r
ccut-hass {Γ₁ = Γ₁}{Γ₂} Δ₀ {Δ₁ = Δ₁} {A₁ = A₁} {A₂} f₁ f₂ (⊗r {Δ = Δ} g g') refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Δ₁ ++ Γ₂ ++ Γ₀) Δ A₁ | cases++-inj₁ Δ₀ (Δ₁ ++ A₂ ∷ Γ₀) Δ A₁ | cases++-inj₁ (Δ₀ ++ Γ₁ ++ Δ₁) Γ₀ Δ A₂ =
    cong (λ x → ⊗r {Γ = Δ₀ ++ Γ₁ ++ Δ₁ ++ Γ₂ ++ Γ₀} x g') (ccut-hass Δ₀ f₁ f₂ g refl)
... | inj₂ (Γ₀ , refl , q) with cases++ Δ₀ Γ Δ₁ Γ₀ (sym q)
ccut-hass {Γ₁ = Γ₁}{Γ₂} Δ₀ {Δ₂ = Δ₂} {A₁} {A₂} f₁ f₂ (⊗r g g') refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ Γ₂ ++ Δ₂) A₁ | cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ Γ₀ (Δ₀ ++ Γ₁ ++ Γ₀') Δ₂ A₂ = refl
ccut-hass {Γ₁ = Γ₁} {Γ₂} _ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊗r {Γ = Γ} g g') refl | inj₂ (_ , refl , refl) | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ Γ (Δ₁ ++ Γ₂ ++ Δ₂) A₁ | cases++-inj₂ Γ₀ Γ (Δ₁ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ (Γ₀ ++ Γ₁ ++ Δ₁) Γ Δ₂ A₂ =
    cong (⊗r g) (ccut-hass Γ₀ f₁ f₂ g' refl)
ccut-hass Δ₀ f₁ f₂ (Il g) refl = cong Il (ccut-hass Δ₀ f₁ f₂ g refl)
ccut-hass Δ₀ f₁ f₂ (⊗l {B = B} g) refl = cong ⊗l (ccut-hass (B ∷ Δ₀) f₁ f₂ g refl)
ccut-hass Δ₀ f₁ f₂ (⊸r g) refl = cong ⊸r (ccut-hass Δ₀ f₁ f₂ g refl)
ccut-hass Δ₀ {Δ₁ = Δ₁} {Δ₂} {A₁} f₁ f₂ (⊸l {Γ} {Δ} g g') eq with cases++ (Δ₀ ++ A₁ ∷ Δ₁) Γ Δ₂ Δ eq
ccut-hass {Γ₁ = Γ₁}{Γ₂} Δ₀ {Δ₁ = Δ₁} {A₁ = A₁} {A₂} f₁ f₂ (⊸l {Δ = Δ} g g') refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ (Δ₁ ++ Γ₂ ++ Γ₀) Δ A₁ | cases++-inj₁ Δ₀ (Δ₁ ++ A₂ ∷ Γ₀) Δ A₁ | cases++-inj₁ (Δ₀ ++ Γ₁ ++ Δ₁) Γ₀ Δ A₂ =
    cong (λ x → ⊸l {Δ₀ ++ Γ₁ ++ Δ₁ ++ Γ₂ ++ Γ₀} x g') (ccut-hass Δ₀ f₁ f₂ g refl)
... | inj₂ (Γ₀ , refl , q) with cases++ Δ₀ Γ Δ₁ Γ₀ (sym q)
ccut-hass {Γ₁ = Γ₁} {Γ₂} Δ₀ {Δ₂ = Δ₂} {A₁} {A₂} f₁ f₂ (⊸l g g') refl | inj₂ (Γ₀ , refl , refl) | inj₁ (Γ₀' , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ Γ₂ ++ Δ₂) A₁ | cases++-inj₁ Δ₀ Γ₀' (Γ₀ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ Γ₀ (Δ₀ ++ Γ₁ ++ Γ₀') Δ₂ A₂ = refl
ccut-hass {Γ₁ = Γ₁} {Γ₂} _ {Δ₁ = Δ₁} {Δ₂} {A₁} {A₂} f₁ f₂ (⊸l {Γ} g g') refl | inj₂ (_ , refl , refl) | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ Γ (Δ₁ ++ Γ₂ ++ Δ₂) A₁ | cases++-inj₂ Γ₀ Γ (Δ₁ ++ A₂ ∷ Δ₂) A₁ | cases++-inj₂ (Γ₀ ++ Γ₁ ++ Δ₁) Γ Δ₂ A₂ =
    cong (⊸l g) (ccut-hass Γ₀ f₁ f₂ g' refl)


----------------
----------------

-- cut rules and logical rules

scut⊗rpass : {Γ Δ Δ' : Cxt}{A A' B C : Fma}
  → {f : just A' ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
  → (f' : just (A ⊗ B) ∣ Δ' ⊢ C)
  → scut (⊗r (pass f) g) f' ≗ pass (scut (⊗r f g) f')
scut⊗rpass ax = ⊗rpass
scut⊗rpass {f = f}{g} (⊗r h h') =
  proof≗
  ⊗r (scut (⊗r (pass f) g) h) h'
  ≗〈 ⊗r (scut⊗rpass h) refl 〉
  ⊗r (pass (scut (⊗r f g) h)) h'
  ≗〈 ⊗rpass 〉
  pass (⊗r (scut (⊗r f g) h) h')
  qed≗
scut⊗rpass (⊗l h) = refl
scut⊗rpass {Γ}{Δ} {f = f} {g} (⊸r {Γ = Λ} h) =
  proof≗
  ⊸r (scut (⊗r (pass f) g) h)
  ≗〈 ⊸r (scut⊗rpass h) 〉
  ⊸r (pass (scut (⊗r f g) h))
  ≗〈 ⊸rpass 〉
  pass (⊸r {Γ = Γ ++ Δ ++ Λ} (scut (⊗r f g) h))
  qed≗

scut⊗rIl : {Γ Δ Δ' : Cxt}{A B C : Fma}
  → {f : nothing ∣ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
  → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
  → scut (⊗r (Il f) g) h ≗ Il (scut (⊗r f g) h)
scut⊗rIl ax = ⊗rIl
scut⊗rIl {f = f}{g}(⊗r h h') =
  proof≗
  ⊗r (scut (⊗r (Il f) g) h) h'
  ≗〈 ⊗r (scut⊗rIl h) refl 〉
  ⊗r (Il (scut (⊗r f g) h)) h'
  ≗〈 ⊗rIl 〉
  Il (⊗r (scut (⊗r f g) h) h')
  qed≗
scut⊗rIl (⊗l h) = refl
scut⊗rIl {Γ}{Δ}{f = f}{g} (⊸r {Γ = Λ} h) =
  proof≗
  ⊸r {Γ = Γ ++ Δ ++ Λ} (scut (⊗r (Il f) g) h)
  ≗〈 ⊸r (scut⊗rIl h) 〉
  ⊸r {Γ = Γ ++ Δ ++ Λ} (Il (scut (⊗r f g) h))
  ≗〈 ⊸rIl 〉
  Il (⊸r {Γ = Γ ++ Δ ++ Λ} (scut (⊗r f g) h))
  qed≗

scut⊗r⊗l : {Γ Δ Δ' : Cxt}{A A' B B' C : Fma}
  → {f : just A' ∣ B' ∷ Γ ⊢ A}{g : nothing ∣ Δ ⊢ B}
  → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
  → scut (⊗r (⊗l f) g) h ≗ ⊗l (scut (⊗r f g) h)
scut⊗r⊗l ax = ⊗r⊗l
scut⊗r⊗l {f = f}{g} (⊗r h h') =
  proof≗
  ⊗r (scut (⊗r (⊗l f) g) h) h'
  ≗〈 ⊗r (scut⊗r⊗l h) refl 〉
  ⊗r (⊗l (scut (⊗r f g) h)) h'
  ≗〈 ⊗r⊗l 〉
  ⊗l (⊗r (scut (⊗r f g) h) h')
  qed≗
scut⊗r⊗l (⊗l h) = refl
scut⊗r⊗l {Γ}{Δ}{f = f}{g} (⊸r {Γ = Λ} h) =
  proof≗
  ⊸r {Γ = Γ ++ Δ ++ Λ} (scut (⊗r (⊗l f) g) h)
  ≗〈 ⊸r (scut⊗r⊗l h) 〉
  ⊸r {Γ = Γ ++ Δ ++ Λ} (⊗l (scut (⊗r f g) h))
  ≗〈 ⊸r⊗l 〉
  ⊗l (⊸r {Γ = _ ∷ Γ ++ Δ ++ Λ} (scut (⊗r f g) h))
  qed≗

scut⊗r : ∀{S}{Γ}{Δ}{Δ'}{A}{B}{C}
  → (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ⊢ B)(g' : nothing ∣ Δ' ⊢ C)
  → scut f (⊗r g g') ≗ ⊗r (scut f g) g'
scut⊗r ax g g' = refl
scut⊗r (pass f) g g' =
  proof≗
  pass (scut f (⊗r g g'))
  ≗〈 pass (scut⊗r f g g') 〉 
  pass (⊗r (scut f g) g')
  ≗〈 ~ ⊗rpass 〉 
  ⊗r (pass (scut f g)) g'
  qed≗
scut⊗r Ir g g' = refl
scut⊗r (⊗r f f') g g' = refl
scut⊗r (Il f) g g' =
  proof≗
  Il (scut f (⊗r g g'))
  ≗〈 Il (scut⊗r f g g') 〉 
  Il (⊗r (scut f g) g')
  ≗〈 ~ ⊗rIl 〉 
  ⊗r (Il (scut f g)) g'
  qed≗
scut⊗r (⊗l f) g g' =
  proof≗
  ⊗l (scut f (⊗r g g'))
  ≗〈 ⊗l (scut⊗r f g g') 〉 
  ⊗l (⊗r (scut f g) g')
  ≗〈 ~ ⊗r⊗l 〉 
  ⊗r (⊗l (scut f g)) g'
  qed≗
scut⊗r (⊸r f) g g' = refl
scut⊗r (⊸l f f') g g' =
  proof≗
  ⊸l f (scut f' (⊗r g g'))
  ≗〈 ⊸l refl (scut⊗r f' g g') 〉
  ⊸l f (⊗r (scut f' g) g')
  ≗〈 ~ ⊗r⊸l 〉
  ⊗r (⊸l f (scut f' g)) g'
  qed≗

scut⊸r : ∀{S}{Γ}{Δ}{A}{B}{C}
  → (f : S ∣ Γ ⊢ A)(g : just A ∣ Δ ∷ʳ B ⊢ C)
  → scut f (⊸r g) ≗ ⊸r (scut f g)
scut⊸r ax g = refl
scut⊸r {Δ = Δ} (pass {Γ} f) g =
  proof≗
  pass (scut f (⊸r g))
  ≗〈 pass (scut⊸r f g) 〉
  pass (⊸r {Γ = Γ ++ Δ} (scut f g))
  ≗〈 ~ ⊸rpass 〉
  ⊸r (pass (scut f g))
  qed≗
scut⊸r Ir g = refl
scut⊸r {Γ = Γ}{Δ} (Il f) g = 
  proof≗
  Il (scut f (⊸r g))
  ≗〈 Il (scut⊸r f g) 〉
  Il (⊸r {Γ = Γ ++ Δ} (scut f g))
  ≗〈 ~ ⊸rIl 〉
  ⊸r {Γ = Γ ++ Δ} (Il (scut f g))
  qed≗
scut⊸r (⊗r f f₁) g = refl
scut⊸r {Γ = Γ}{Δ} (⊗l f) g = 
  proof≗
  ⊗l (scut f (⊸r g))
  ≗〈 ⊗l (scut⊸r f g) 〉
  ⊗l (⊸r {Γ = _ ∷ Γ ++ Δ} (scut f g))
  ≗〈 ~ ⊸r⊗l 〉
  ⊸r {Γ = Γ ++ Δ} (⊗l (scut f g))
  qed≗
scut⊸r (⊸r f) g = refl
scut⊸r {Δ = Δ} (⊸l {Γ = Γ}{Γ'} f f') g =
  proof≗ 
  ⊸l f (scut f' (⊸r g))
  ≗〈 ⊸l refl (scut⊸r f' g) 〉
  ⊸l f (⊸r {Γ = Γ' ++ Δ} (scut f' g))
  ≗〈 ~ ⊸r⊸l {Γ = Γ}{Γ' ++ Δ} 〉
  ⊸r {Γ = Γ ++ Γ' ++ Δ} (⊸l f (scut f' g))
  qed≗

scut⊸r⊗l : {Γ Δ : Cxt}{A A' B B' C : Fma}
  → {f : just A' ∣ B' ∷ Γ ∷ʳ A ⊢ B}
  → (h : just (A ⊸ B) ∣ Δ ⊢ C)
  → scut (⊸r (⊗l f)) h ≗ ⊗l (scut (⊸r f) h)
scut⊸r⊗l ax = ⊸r⊗l
scut⊸r⊗l (⊗r h h₁) = ⊗r (scut⊸r⊗l h) refl ∙ ⊗r⊗l
scut⊸r⊗l (⊸r h) = ⊸r (scut⊸r⊗l h) ∙ ⊸r⊗l
scut⊸r⊗l (⊸l h h₁) = refl

scut⊸rIl : {Γ Δ : Cxt}{A B C : Fma}
  → {f : nothing ∣ Γ ∷ʳ A ⊢ B}
  → (h : just (A ⊸ B) ∣ Δ ⊢ C)
  → scut (⊸r (Il f)) h ≗ Il (scut (⊸r f) h)
scut⊸rIl ax = ⊸rIl
scut⊸rIl (⊗r h h₁) = ⊗r (scut⊸rIl h) refl ∙ ⊗rIl
scut⊸rIl (⊸r h) = ⊸r (scut⊸rIl h) ∙ ⊸rIl
scut⊸rIl (⊸l h h₁) = refl

scut⊸rpass : {Γ Δ : Cxt}{A A' B C : Fma}
  → {f : just A' ∣ Γ ∷ʳ A ⊢ B}
  → (h : just (A ⊸ B) ∣ Δ ⊢ C)
  → scut (⊸r (pass f)) h ≗ pass (scut (⊸r f) h)
scut⊸rpass ax = ⊸rpass
scut⊸rpass (⊗r h h₁) = ⊗r (scut⊸rpass h) refl ∙ ⊗rpass
scut⊸rpass (⊸r h) = ⊸r (scut⊸rpass h) ∙ ⊸rpass
scut⊸rpass (⊸l h h₁) = refl

scut⊗r⊸l : {Γ Γ' Δ Δ' : Cxt}{A A' B B' C : Fma}
  → {f : nothing ∣ Γ ⊢ A'}{f' : just B' ∣ Γ' ⊢ A}{g : nothing ∣ Δ ⊢ B}
  → (h : just (A ⊗ B) ∣ Δ' ⊢ C)
  → scut (⊗r (⊸l f f') g) h ≗ ⊸l f (scut (⊗r f' g) h)
scut⊗r⊸l ax = ⊗r⊸l
scut⊗r⊸l (⊗r h h₁) = ⊗r (scut⊗r⊸l h) refl ∙ ⊗r⊸l
scut⊗r⊸l (⊗l h) = refl
scut⊗r⊸l {Γ}{Γ'}{Δ} (⊸r {Γ = Δ'} h) = ⊸r (scut⊗r⊸l h) ∙ ⊸r⊸l {Γ}{Γ' ++ Δ ++ Δ'}

scut⊸r⊸l : {Γ Γ' Δ : Cxt}{A A' B B' C : Fma}
  → {f : nothing ∣ Γ ⊢ A'}{g : just B' ∣ Γ' ∷ʳ A ⊢ B}
  → (h : just (A ⊸ B) ∣ Δ ⊢ C)
  → scut (⊸r {Γ = Γ ++ Γ'} (⊸l f g)) h ≗ ⊸l f (scut (⊸r g) h)
scut⊸r⊸l ax = ⊸r⊸l
scut⊸r⊸l (⊗r h h₁) = ⊗r (scut⊸r⊸l h) refl ∙ ⊗r⊸l
scut⊸r⊸l {Γ}{Γ'} (⊸r {Γ = Δ} h) = ⊸r (scut⊸r⊸l h) ∙ ⊸r⊸l {Γ}{Γ' ++ Δ}
scut⊸r⊸l {Γ}{Γ'} {A = A} (⊸l h h₁)
  rewrite cases++-inj₂ Γ' Γ [] A = refl

scut⊸r⋆⊸l⋆ : {S : Stp} {Γ Δ : Cxt} {B C : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : S ∣ Γ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ⊢ B)
  → (g : just B ∣ Δ ⊢ C)
  → scut (⊸r⋆ (List.map (λ x → proj₁ (proj₂ x)) Ξ) f) (⊸l⋆ Ξ g)
         ≡ scut (ccut⋆ Γ [] Ξ f refl) g
scut⊸r⋆⊸l⋆ [] f g = refl
scut⊸r⋆⊸l⋆ {Γ = Γ} ((Δ , A , h) ∷ Ξ) f g =
  trans (sym (ccutscut-vass Γ {[]} h (⊸r⋆ {Γ = Γ ∷ʳ _} (List.map (λ x → proj₁ (proj₂ x)) Ξ) f) (⊸l⋆ Ξ g) refl) )
  (trans (cong (λ x → ccut Γ h x refl) (scut⊸r⋆⊸l⋆ {Γ = Γ ∷ʳ _} Ξ f g))
         (ccutscut-vass Γ h (ccut⋆ (Γ ∷ʳ A) [] Ξ f refl) g refl))

subst-cxt-uip : ∀ {S Γ Γ' A}
  → (eq eq' : Γ ≡ Γ')
  → (f : S ∣ Γ ⊢ A) 
  → subst-cxt eq f ≡ subst-cxt eq' f
subst-cxt-uip refl refl f = refl

subst-cxt⊗l : ∀ {Γ Γ' A B C}
  → (eq : Γ ≡ Γ')
  → (f : just A ∣ B ∷ Γ ⊢ C) 
  → subst-cxt eq (⊗l f) ≡ ⊗l (subst-cxt (cong (B ∷_) eq) f)
subst-cxt⊗l refl f = refl

subst-cxt⊗r1 : ∀ {S Γ Γ' Δ A B}
  → (eq : Γ ≡ Γ')
  → (f : S ∣ Γ ⊢ A) 
  → (g : ─ ∣ Δ ⊢ B)
  → subst-cxt (cong (_++ Δ) eq) (⊗r f g) ≡ ⊗r (subst-cxt eq f) g
subst-cxt⊗r1 refl f g = refl

subst-cxt⊗r2 : ∀ {S Γ Δ Δ' A B}
  → (eq : Δ ≡ Δ')
  → (f : S ∣ Γ ⊢ A) 
  → (g : ─ ∣ Δ ⊢ B)
  → subst-cxt (cong (Γ ++_) eq) (⊗r f g) ≡ ⊗r f (subst-cxt eq g)
subst-cxt⊗r2 refl f g = refl

subst-cxt⊸l1 : ∀ {Γ Γ' Δ A B C}
  → (eq : Γ ≡ Γ')
  → (f : ─ ∣ Γ ⊢ A) 
  → (g : just B ∣ Δ ⊢ C)
  → subst-cxt (cong (_++ Δ) eq) (⊸l f g) ≡ ⊸l (subst-cxt eq f) g
subst-cxt⊸l1 refl f g = refl

subst-cxt⊸l2 : ∀ {Γ Δ Δ' A B C}
  → (eq : Δ ≡ Δ')
  → (f : ─ ∣ Γ ⊢ A) 
  → (g : just B ∣ Δ ⊢ C)
  → subst-cxt (cong (Γ ++_) eq) (⊸l f g) ≡ ⊸l f (subst-cxt eq g)
subst-cxt⊸l2 refl f g = refl

cong-subst-cxt : ∀ {S Γ Γ' A}
  → (eq : Γ ≡ Γ')
  → {f f' : S ∣ Γ ⊢ A} (eq' : f ≗ f')
  → subst-cxt eq f ≗ subst-cxt eq f'
cong-subst-cxt refl eq = eq

trans-subst-cxt : ∀ {S Γ Γ' Γ'' A}
  → (eq : Γ ≡ Γ') (eq' : Γ' ≡ Γ'')
  → (f : S ∣ Γ ⊢ A)
  → subst-cxt eq' (subst-cxt eq f) ≡ subst-cxt (trans eq eq') f
trans-subst-cxt refl refl f = refl  

subst-cxt-ccut2 : ∀ {S Γ} Δ₀ {Δ Δ' A C}
  → (f : ─ ∣ Γ ⊢ A)  (g : S ∣ Δ₀ ++ A ∷ Δ ⊢ C) (eq : Δ ≡ Δ')
  → ccut Δ₀ f (subst-cxt (cong (λ x → Δ₀ ++ A ∷ x) eq) g) refl
       ≡ subst-cxt (cong (λ x → Δ₀ ++ Γ ++ x) eq) (ccut Δ₀ f g refl)
subst-cxt-ccut2 Δ₀ f g refl = refl

ccut⋆pass : ∀ Γ₀ Γ₁ {A C : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : just A ∣ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ Γ₁ ⊢ C)
  → ccut⋆ (A ∷ Γ₀) Γ₁ Ξ (pass f) refl ≡ pass (ccut⋆ Γ₀ Γ₁ Ξ f refl)
ccut⋆pass Γ₀ Γ₁ [] f = refl
ccut⋆pass Γ₀ Γ₁ ((Δ , B , g) ∷ Ξ) f =
  cong (λ x → ccut (_ ∷ Γ₀) g x refl) (ccut⋆pass (Γ₀ ∷ʳ B) Γ₁ Ξ f)

ccut⋆Il : ∀ Γ₀ Γ₁ {C : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : ─ ∣ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ Γ₁ ⊢ C)
  → ccut⋆ Γ₀ Γ₁ Ξ (Il f) refl ≡ Il (ccut⋆ Γ₀ Γ₁ Ξ f refl)
ccut⋆Il Γ₀ Γ₁ [] f = refl
ccut⋆Il Γ₀ Γ₁ ((Δ , B , g) ∷ Ξ) f =
  cong (λ x → ccut Γ₀ g x refl) (ccut⋆Il (Γ₀ ∷ʳ B) Γ₁ Ξ f)

ccut⋆⊗l : ∀ Γ₀ Γ₁ {A B C : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : just A ∣ B ∷ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ Γ₁ ⊢ C)
  → ccut⋆ Γ₀ Γ₁ Ξ (⊗l f) refl ≡ ⊗l (ccut⋆ (B ∷ Γ₀) Γ₁ Ξ f refl)
ccut⋆⊗l Γ₀ Γ₁ [] f = refl
ccut⋆⊗l Γ₀ Γ₁ ((Δ , B , g) ∷ Ξ) f =
  cong (λ x → ccut Γ₀ g x refl) (ccut⋆⊗l (Γ₀ ∷ʳ B) Γ₁ Ξ f)

ccut⋆⊗r1 : ∀ {S} Γ₀ Γ₁ {Λ} {A B : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : S ∣ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ Γ₁ ⊢ A)
  → (g : ─ ∣ Λ ⊢ B)
  → ccut⋆ Γ₀ (Γ₁ ++ Λ) Ξ (⊗r f g) refl ≡ ⊗r (ccut⋆ Γ₀ Γ₁ Ξ f refl) g
ccut⋆⊗r1 Γ₀ Γ₁ [] f g = refl
ccut⋆⊗r1 Γ₀ Γ₁ {Λ} ((Δ , B , h) ∷ Ξ) f g with cong (λ x → ccut Γ₀ h x refl) (ccut⋆⊗r1 (Γ₀ ∷ʳ B) Γ₁ Ξ f g)
... | ih rewrite cases++-inj₁ Γ₀ (concat (List.map proj₁ Ξ) ++ Γ₁) Λ B = ih

ccut⋆⊗r2 : ∀ {S} Γ₀ Γ₁ {Λ} {A B : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : S ∣ Λ ⊢ A)
  → (g : ─ ∣ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ Γ₁ ⊢ B)
  → ccut⋆ (Λ ++ Γ₀) Γ₁ Ξ (⊗r f g) refl ≡ ⊗r f (ccut⋆ Γ₀ Γ₁ Ξ g refl)
ccut⋆⊗r2 Γ₀ Γ₁ [] f g = refl
ccut⋆⊗r2 Γ₀ Γ₁ {Λ} ((Δ , B , h) ∷ Ξ) f g with cong (λ x → ccut (Λ ++ Γ₀) h x refl) (ccut⋆⊗r2 (Γ₀ ∷ʳ B) Γ₁ Ξ f g)
... | ih rewrite cases++-inj₂ Γ₀ Λ (concat (List.map proj₁ Ξ) ++ Γ₁) B = ih


ccut⋆++ : ∀ {S} Γ₀ Γ₁ {C : Fma}
  → (Ξ Ψ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : S ∣ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ List.map (λ x → proj₁ (proj₂ x)) Ψ ++ Γ₁ ⊢ C)
  → ccut⋆ Γ₀ Γ₁ (Ξ ++ Ψ) f refl
          ≡ subst-cxt (cong (λ x → Γ₀ ++ x ++ Γ₁) (sym (concat++ (List.map proj₁ Ξ) (List.map proj₁ Ψ))))
                      (ccut⋆ Γ₀ (concat (List.map proj₁ Ψ) ++ Γ₁) Ξ (ccut⋆ (Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ) Γ₁ Ψ f refl) refl)
ccut⋆++ Γ₀ Γ₁ [] Ψ f = refl
ccut⋆++ Γ₀ Γ₁ ((Δ , B , h) ∷ Ξ) Ψ f =
  trans (cong (λ x → ccut Γ₀ h x refl) (ccut⋆++ (Γ₀ ∷ʳ B) Γ₁ Ξ Ψ f))
  (trans (cong (λ x → ccut Γ₀ h x refl) (subst-cxt-uip (cong (λ x → Γ₀ ++ B ∷ x ++ Γ₁) eq') (cong (λ x → Γ₀ ++ B ∷ x) eq) _))
  (trans (subst-cxt-ccut2 Γ₀ h k eq)
         (subst-cxt-uip (cong (λ x → Γ₀ ++ Δ ++ x) (cong (_++ Γ₁) eq')) _ _)))
  where
    k = ccut⋆ (Γ₀ ∷ʳ B) (concat (List.map proj₁ Ψ) ++ Γ₁) Ξ (ccut⋆ (Γ₀ ++ B ∷ List.map (λ x → proj₁ (proj₂ x)) Ξ) Γ₁ Ψ f refl) refl
    eq = cong (_++ Γ₁) {concat (List.map proj₁ Ξ) ++ concat (List.map proj₁ Ψ)} (sym (concat++ (List.map proj₁ Ξ) (List.map proj₁ Ψ)))
    eq' = sym (concat++ (List.map proj₁ Ξ) (List.map proj₁ Ψ))


ccut⋆⊗r : ∀ {S} Γ₀ Γ₁ {A B : Fma}
  → (Ξ Ψ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : S ∣ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ⊢ A)
  → (g : ─ ∣ List.map (λ x → proj₁ (proj₂ x)) Ψ ++ Γ₁ ⊢ B)
  → ccut⋆ Γ₀ Γ₁ (Ξ ++ Ψ) (⊗r f g) refl
          ≡ subst-cxt (cong (λ x → Γ₀ ++ x ++ Γ₁) (sym (concat++ (List.map proj₁ Ξ) (List.map proj₁ Ψ))))
                      (⊗r (ccut⋆ Γ₀ [] Ξ f refl) (ccut⋆ [] Γ₁ Ψ g refl))
ccut⋆⊗r Γ₀ Γ₁ Ξ Ψ f g =
  trans (ccut⋆++ Γ₀ Γ₁ Ξ Ψ (⊗r f g))
        (cong (subst-cxt (cong (λ x → Γ₀ ++ x ++ Γ₁) (sym (concat++ (List.map proj₁ Ξ) (List.map proj₁ Ψ)))))
              (trans (cong (λ x → ccut⋆ Γ₀ (concat (List.map proj₁ Ψ) ++ Γ₁) Ξ x refl) (ccut⋆⊗r2 [] Γ₁ Ψ f g))
                     (ccut⋆⊗r1 Γ₀ [] Ξ f (ccut⋆ [] Γ₁ Ψ g refl))))


ccut⋆⊸r : ∀ {S} Γ₀ Γ₁ {A B : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : S ∣ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ Γ₁ ∷ʳ A ⊢ B)
  → ccut⋆ Γ₀ Γ₁ Ξ (⊸r {Γ = Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ Γ₁} f) refl
       ≡ ⊸r (ccut⋆ Γ₀ (Γ₁ ∷ʳ A) Ξ f refl)
ccut⋆⊸r Γ₀ Γ₁ [] f = refl
ccut⋆⊸r Γ₀ Γ₁ ((Δ , B , g) ∷ Ξ) f = cong (λ x → ccut Γ₀ g x refl) (ccut⋆⊸r (Γ₀ ∷ʳ B) Γ₁ Ξ f)

ccut⋆⊸l1 : ∀ Γ₀ Γ₁ {Λ} {A B C : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : ─ ∣ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ Γ₁ ⊢ A)
  → (g : just B ∣ Λ ⊢ C)
  → ccut⋆ Γ₀ (Γ₁ ++ Λ) Ξ (⊸l f g) refl ≡ ⊸l (ccut⋆ Γ₀ Γ₁ Ξ f refl) g
ccut⋆⊸l1 Γ₀ Γ₁ [] f g = refl
ccut⋆⊸l1 Γ₀ Γ₁ {Λ} ((Δ , B , h) ∷ Ξ) f g with cong (λ x → ccut Γ₀ h x refl) (ccut⋆⊸l1 (Γ₀ ∷ʳ B) Γ₁ Ξ f g)
... | ih rewrite cases++-inj₁ Γ₀ (concat (List.map proj₁ Ξ) ++ Γ₁) Λ B = ih

ccut⋆⊸l2 : ∀ Γ₀ Γ₁ {Λ} {A B C : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : ─ ∣ Λ ⊢ A)
  → (g : just B ∣ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ Γ₁ ⊢ C)
  → ccut⋆ (Λ ++ Γ₀) Γ₁ Ξ (⊸l f g) refl ≡ ⊸l f (ccut⋆ Γ₀ Γ₁ Ξ g refl)
ccut⋆⊸l2 Γ₀ Γ₁ [] f g = refl
ccut⋆⊸l2 Γ₀ Γ₁ {Λ} ((Δ , B , h) ∷ Ξ) f g with cong (λ x → ccut (Λ ++ Γ₀) h x refl) (ccut⋆⊸l2 (Γ₀ ∷ʳ B) Γ₁ Ξ f g)
... | ih rewrite cases++-inj₂ Γ₀ Λ (concat (List.map proj₁ Ξ) ++ Γ₁) B = ih

ccut⋆⊸l : ∀ Γ₀ Γ₁ {A B C : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (Ψ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : ─ ∣ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ⊢ A)
  → (g : just B ∣ List.map (λ x → proj₁ (proj₂ x)) Ψ ++ Γ₁ ⊢ C)
  → ccut⋆ Γ₀ Γ₁ (Ξ ++ Ψ) (⊸l f g) refl
          ≡ subst-cxt (cong (λ x → Γ₀ ++ x ++ Γ₁) (sym (concat++ (List.map proj₁ Ξ) (List.map proj₁ Ψ))))
                      (⊸l (ccut⋆ Γ₀ [] Ξ f refl) (ccut⋆ [] Γ₁ Ψ g refl))
ccut⋆⊸l Γ₀ Γ₁ Ξ Ψ f g =
  trans (ccut⋆++ Γ₀ Γ₁ Ξ Ψ (⊸l f g))
        (cong (subst-cxt (cong (λ x → Γ₀ ++ x ++ Γ₁) (sym (concat++ (List.map proj₁ Ξ) (List.map proj₁ Ψ)))))
              (trans (cong (λ x → ccut⋆ Γ₀ (concat (List.map proj₁ Ψ) ++ Γ₁) Ξ x refl) (ccut⋆⊸l2 [] Γ₁ Ψ f g))
                     (ccut⋆⊸l1 Γ₀ [] Ξ f (ccut⋆ [] Γ₁ Ψ g refl))))

scut-axI : ∀{Γ C} (f : just I ∣ Γ ⊢ C)
  → f ≗ Il (scut Ir f)
scut-axI ax = axI
scut-axI (Il f) = refl
scut-axI (⊗r f f₁) = ⊗r (scut-axI f) refl ∙ ⊗rIl
scut-axI (⊸r f) = ⊸r (scut-axI f) ∙ ⊸rIl

scut-ax⊗ : ∀{Γ A B C} (f : just (A ⊗ B) ∣ Γ ⊢ C)
  → f ≗ ⊗l (scut (⊗r ax (pass ax)) f)
scut-ax⊗ ax = ax⊗
scut-ax⊗ (⊗r f f₁) = ⊗r (scut-ax⊗ f) refl ∙ ⊗r⊗l
scut-ax⊗ (⊗l f) = ⊗l (~ ≡-to-≗ (ccut-unit [] f refl))
scut-ax⊗ (⊸r f) = ⊸r (scut-ax⊗ f) ∙ ⊸r⊗l

scut-ax⊸ : ∀{Γ A B C} (f : just (A ⊸ B) ∣ Γ ⊢ C)
  → f ≗ scut (⊸r (⊸l (pass ax) ax)) f
scut-ax⊸ ax = ax⊸
scut-ax⊸ (⊗r f g) = ⊗r (scut-ax⊸ f) refl
scut-ax⊸ (⊸r f) = ⊸r (scut-ax⊸ f)
scut-ax⊸ (⊸l f g) = ⊸l (~ ≡-to-≗ (scut-unit f)) refl



-- cut rules respect equivalence of derivations ≗

cong-scut2Ir : ∀{Γ C} {f g : just I ∣ Γ ⊢ C}
  → f ≗ g → scut Ir f ≗ scut Ir g
cong-scut2Ir refl = refl
cong-scut2Ir (~ eq) = ~ cong-scut2Ir eq
cong-scut2Ir (eq ∙ eq₁) = cong-scut2Ir eq ∙ cong-scut2Ir eq₁
cong-scut2Ir (Il eq) = eq
cong-scut2Ir (⊗r eq eq₁) = ⊗r (cong-scut2Ir eq) eq₁
cong-scut2Ir (⊸r eq) = ⊸r (cong-scut2Ir eq)
cong-scut2Ir axI = refl
cong-scut2Ir ⊗rIl = refl
cong-scut2Ir ⊸rIl = refl

cong-scut1⊗r : {S : Stp} {Γ Γ' Δ : Cxt} {A A' C : Fma} 
  → {f f' : S ∣ Γ ⊢ A} (eq : f ≗ f')
  → {h h' : nothing ∣ Γ' ⊢ A'} (eq' : h ≗ h')
  → (g : just (A ⊗ A') ∣ Δ ⊢ C)
  → scut (⊗r f h) g ≗ scut (⊗r f' h') g
cong-scut1⊸r : {S : Stp} {Γ Δ : Cxt} {A B C : Fma} 
  → {f f' : S ∣ Γ ∷ʳ A ⊢ B} (eq : f ≗ f')
  → (g : just (A ⊸ B) ∣ Δ ⊢ C)
  → scut (⊸r f) g ≗ scut (⊸r f') g
cong-scut1 : {S : Stp} {Γ Δ : Cxt} {A C : Fma} 
  → {f f' : S ∣ Γ ⊢ A} (eq : f ≗ f') (g : just A ∣ Δ ⊢ C)
  → scut f g ≗ scut f' g
cong-scut2 : {S : Stp} {Γ Δ : Cxt} {A C : Fma} 
  → (f : S ∣ Γ ⊢ A) {g g' : just A ∣ Δ ⊢ C} (eq : g ≗ g')
  → scut f g ≗ scut f g'
cong-ccut1 : {T : Stp} {Γ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A C : Fma}
  → {f f' : ─ ∣ Γ ⊢ A} (eq : f ≗ f') (g : T ∣ Δ ⊢ C) (r : Δ ≡ Δ₀ ++ A ∷ Δ')
  → ccut Δ₀ f g r ≗ ccut Δ₀ f' g r
cong-ccut2 : {T : Stp} {Γ Δ : Cxt} (Δ₀ : Cxt) {Δ' : Cxt} {A C : Fma}
  → (f : ─ ∣ Γ ⊢ A) {g g' : T ∣ Δ ⊢ C}  (eq : g ≗ g') (r : Δ ≡ Δ₀ ++ A ∷ Δ')
  → ccut Δ₀ f g r ≗ ccut Δ₀ f g' r
cong-scut2⊗r : ∀{S Γ Δ Λ A B C}
  → (f : S ∣ Γ ⊢ A) (f' : ─ ∣ Δ ⊢ B)
  → {g g' : just (A ⊗ B) ∣ Λ ⊢ C}
  → g ≗ g' → scut (⊗r f f') g ≗ scut (⊗r f f') g'
cong-scut2⊸r : ∀{S Γ Δ A B C}
  → (f : S ∣ Γ ∷ʳ A ⊢ B) 
  → {g g' : just (A ⊸ B) ∣ Δ ⊢ C}
  → g ≗ g' → scut (⊸r f) g ≗ scut (⊸r f) g'

cong-scut1⊗r eq eq' ax = ⊗r eq eq'
cong-scut1⊗r eq eq' (⊗r g g₁) = ⊗r (cong-scut1⊗r eq eq' g) refl
cong-scut1⊗r {f' = f'} eq eq' (⊗l g) =
  cong-scut1 eq _ ∙ cong-scut2 f' (cong-ccut1 [] eq' g refl)
cong-scut1⊗r eq eq' (⊸r g) = ⊸r (cong-scut1⊗r eq eq' g)

cong-scut1⊸r eq ax = ⊸r eq
cong-scut1⊸r eq (⊗r g g₁) = ⊗r (cong-scut1⊸r eq g) refl
cong-scut1⊸r eq (⊸r g) = ⊸r (cong-scut1⊸r eq g)
cong-scut1⊸r {Γ = Γ} eq (⊸l {Δ} g g₁) =
  cong-scut1 {Γ = Γ ++ Δ} (cong-ccut2 Γ g eq refl) g₁

cong-scut1 refl g = refl
cong-scut1 (~ eq) g = ~ cong-scut1 eq g
cong-scut1 (eq ∙ eq₁) g = cong-scut1 eq g ∙ cong-scut1 eq₁ g
cong-scut1 (pass eq) g = pass (cong-scut1 eq g)
cong-scut1 (Il eq) g = Il (cong-scut1 eq g)
cong-scut1 (⊗l eq) g = ⊗l (cong-scut1 eq g)
cong-scut1 (⊸l eq eq₁) g = ⊸l eq (cong-scut1 eq₁ g)
cong-scut1 (⊗r eq eq₁) g = cong-scut1⊗r eq eq₁ g
cong-scut1 (⊸r eq) g = cong-scut1⊸r eq g
cong-scut1 axI g = scut-axI g
cong-scut1 ax⊗ g = scut-ax⊗ g
cong-scut1 ax⊸ g = scut-ax⊸ g
cong-scut1 ⊗rpass g = scut⊗rpass g
cong-scut1 ⊗rIl g = scut⊗rIl g
cong-scut1 ⊗r⊗l g = scut⊗r⊗l g
cong-scut1 ⊗r⊸l g = scut⊗r⊸l g
cong-scut1 ⊸rpass g = scut⊸rpass g
cong-scut1 ⊸rIl g = scut⊸rIl g
cong-scut1 ⊸r⊗l g = scut⊸r⊗l g
cong-scut1 ⊸r⊸l g = scut⊸r⊸l g

cong-scut2 ax eq = eq
cong-scut2 (pass f) eq = pass (cong-scut2 f eq)
cong-scut2 (Il f) eq = Il (cong-scut2 f eq)
cong-scut2 (⊗l f) eq = ⊗l (cong-scut2 f eq)
cong-scut2 (⊸l f f₁) eq = ⊸l refl (cong-scut2 f₁ eq)
cong-scut2 Ir eq = cong-scut2Ir eq
cong-scut2 (⊗r f f₁) eq = cong-scut2⊗r f f₁ eq
cong-scut2 (⊸r f) eq = cong-scut2⊸r f eq

cong-scut2⊗r f f' refl = refl
cong-scut2⊗r f f' (~ eq) = ~ (cong-scut2⊗r f f' eq)
cong-scut2⊗r f f' (eq ∙ eq₁) = cong-scut2⊗r f f' eq ∙ cong-scut2⊗r f f' eq₁
cong-scut2⊗r f f' (⊗l eq) = cong-scut2 f (cong-ccut2 [] f' eq refl)
cong-scut2⊗r f f' (⊗r eq eq₁) = ⊗r (cong-scut2⊗r f f' eq) eq₁
cong-scut2⊗r f f' (⊸r eq) = ⊸r (cong-scut2⊗r f f' eq)
cong-scut2⊗r f f' ax⊗ =
  ⊗r (~ (≡-to-≗ (scut-unit f))) (~ (≡-to-≗ (scut-unit f')))
  ∙ (~ scut⊗r f ax (scut f' ax))
cong-scut2⊗r f f' (⊗r⊗l {f = g} {h}) = ~ scut⊗r f (ccut [] f' g refl) h
cong-scut2⊗r {Γ = Γ} {Δ} {Λ} f f' (⊸r⊗l {f = g}) =
  ~ scut⊸r {Γ = Γ}{Δ ++ Λ} f (ccut [] f' g refl)

cong-scut2⊸r f refl = refl
cong-scut2⊸r f (~ eq) = ~ cong-scut2⊸r f eq
cong-scut2⊸r f (eq ∙ eq₁) = cong-scut2⊸r f eq ∙ cong-scut2⊸r f eq₁
cong-scut2⊸r f (⊗r eq eq₁) = ⊗r (cong-scut2⊸r f eq) eq₁
cong-scut2⊸r f (⊸r eq) = ⊸r (cong-scut2⊸r f eq)
cong-scut2⊸r {Γ = Γ} f (⊸l {Δ} {f = g}{g' = h'} eq eq₁) =
  cong-scut2 (ccut Γ g f refl) eq₁
  ∙ cong-scut1 {Γ = Γ ++ Δ} (cong-ccut1 Γ eq f refl) h'
cong-scut2⊸r {Γ = Γ} f ax⊸ =
  ⊸r (~ (≡-to-≗ (trans (scut-unit (ccut Γ (pass ax) f refl))
                       (ccut-unit Γ f refl))))
cong-scut2⊸r {Γ = Γ} f (⊗r⊸l {Δ} {f = g}{h}{k}) =
  ~ scut⊗r {Γ = Γ ++ Δ} (ccut Γ g f refl) h k
cong-scut2⊸r {Γ = Γ} f (⊸r⊸l {Δ} {f = g}{h}) =
  ~ (scut⊸r {Γ = Γ ++ Δ} (ccut Γ g f refl) h)

cong-ccut1 Δ₀ eq ax r = ⊥-elim ([]disj∷ Δ₀ r)
cong-ccut1 [] eq (pass g) refl = cong-scut1 eq g
cong-ccut1 (_ ∷ Δ₀) eq (pass g) refl = pass (cong-ccut1 Δ₀ eq g refl)
cong-ccut1 Δ₀ eq Ir r = ⊥-elim ([]disj∷ Δ₀ r)
cong-ccut1 Δ₀ eq (Il g) r = Il (cong-ccut1 Δ₀ eq g r)
cong-ccut1 Δ₀ eq (⊗l g) refl = ⊗l (cong-ccut1 (_ ∷ Δ₀) eq g refl)
cong-ccut1 Δ₀ eq (⊸r g) refl = ⊸r (cong-ccut1 Δ₀ eq g refl)
cong-ccut1 Δ₀ {Δ'} eq (⊗r {Γ = Γ} {Δ} g g₁) r with cases++ Δ₀ Γ Δ' Δ r
... | inj₁ (Γ₀ , refl , refl) = ⊗r (cong-ccut1 Δ₀ eq g refl) refl
... | inj₂ (Γ₀ , refl , refl) = ⊗r refl (cong-ccut1 Γ₀ eq g₁ refl)
cong-ccut1 Δ₀ {Δ'} eq (⊸l {Γ} {Δ} g g₁) r with cases++ Δ₀ Γ Δ' Δ r
... | inj₁ (Γ₀ , refl , refl) = ⊸l (cong-ccut1 Δ₀ eq g refl) refl
... | inj₂ (Γ₀ , refl , refl) = ⊸l refl (cong-ccut1 Γ₀ eq g₁ refl)

cong-ccut2 Δ₀ f refl r = refl
cong-ccut2 Δ₀ f (~ eq) r = ~ cong-ccut2 Δ₀ f eq r
cong-ccut2 Δ₀ f (eq ∙ eq₁) r = cong-ccut2 Δ₀ f eq r ∙ cong-ccut2 Δ₀ f eq₁ r
cong-ccut2 [] f (pass eq) refl = cong-scut2 f eq
cong-ccut2 (_ ∷ Δ₀) f (pass eq) refl = pass (cong-ccut2 Δ₀ f eq refl)
cong-ccut2 Δ₀ f (Il eq) r = Il (cong-ccut2 Δ₀ f eq r)
cong-ccut2 Δ₀ f (⊗l eq) refl = ⊗l (cong-ccut2 (_ ∷ Δ₀) f eq refl)
cong-ccut2 Δ₀ f (⊸r eq) refl = ⊸r (cong-ccut2 Δ₀ f eq refl)
cong-ccut2 Δ₀ {Δ'} f (⊗r {Γ = Γ} {Δ} eq eq₁) r with cases++ Δ₀ Γ Δ' Δ r
... | inj₁ (Γ₀ , refl , refl) = ⊗r (cong-ccut2 Δ₀ f eq refl) eq₁
... | inj₂ (Γ₀ , refl , refl) = ⊗r eq (cong-ccut2 Γ₀ f eq₁ refl)
cong-ccut2 Δ₀ {Δ'} f (⊸l {Γ} {Δ} eq eq₁) r with cases++ Δ₀ Γ Δ' Δ r
... | inj₁ (Γ₀ , refl , refl) = ⊸l (cong-ccut2 Δ₀ f eq refl) eq₁
... | inj₂ (Γ₀ , refl , refl) = ⊸l eq (cong-ccut2 Γ₀ f eq₁ refl)
cong-ccut2 Δ₀ f axI r = ⊥-elim ([]disj∷ Δ₀ r)
cong-ccut2 Δ₀ f ax⊗ r = ⊥-elim ([]disj∷ Δ₀ r)
cong-ccut2 Δ₀ f ax⊸ r = ⊥-elim ([]disj∷ Δ₀ r)
cong-ccut2 Δ₀ f ⊗rpass r with cases∷ Δ₀ r
cong-ccut2 .[] f ⊗rpass refl | inj₁ (refl , refl , refl) = ~ scut⊗r f _ _
cong-ccut2 .(_ ∷ Δ₀) {Δ'} f (⊗rpass {Γ}{Δ}) r | inj₂ (Δ₀ , p , refl) with cases++ Δ₀ Γ Δ' Δ p
cong-ccut2 .(_ ∷ Δ₀) {A = A} f (⊗rpass {Δ = Δ}) refl | inj₂ (Δ₀ , p , refl) | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀ Δ A = ⊗rpass
cong-ccut2 .(_ ∷ _ ++ Γ₀) {Δ'} {A = A} f (⊗rpass {Γ}) refl | inj₂ (.(_ ++ Γ₀) , p , refl) | inj₂ (Γ₀ , refl , refl) 
  rewrite cases++-inj₂ Γ₀ Γ Δ' A = ⊗rpass
cong-ccut2 [] f ⊸rpass refl = ~ scut⊸r f _
cong-ccut2 (_ ∷ Δ₀) f ⊸rpass refl = ⊸rpass
cong-ccut2 Δ₀ f ⊸rIl refl = ⊸rIl
cong-ccut2 Δ₀ f ⊸r⊗l refl = ⊸r⊗l
cong-ccut2 Δ₀ {Δ'}{A = A} f (⊗rIl {Γ}{Δ}) r with cases++ Δ₀ Γ Δ' Δ r
... | inj₁ (Γ₀ , refl , refl) = ⊗rIl
... | inj₂ (Γ₀ , refl , refl) = ⊗rIl
cong-ccut2 Δ₀ {Δ'}{A = A} f (⊗r⊗l {Γ}{Δ}) r with cases++ Δ₀ Γ Δ' Δ r
cong-ccut2 Δ₀ {A = A} f (⊗r⊗l {Δ = Δ}) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀ Δ A = ⊗r⊗l
cong-ccut2 .(_ ++ Γ₀) {Δ'} {A = A} f (⊗r⊗l {Γ}) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ Γ Δ' A = ⊗r⊗l
cong-ccut2 Δ₀ {Δ'}{A = A} f (⊸r⊸l {Γ}{Δ}) r with cases++ Δ₀ Γ Δ' Δ r
cong-ccut2 Δ₀ {A = A} f (⊸r⊸l {Δ = Δ} {C = C}) refl | inj₁ (Γ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ Γ₀ (Δ ∷ʳ C) A = ⊸r⊸l
cong-ccut2 {Γ = Γ₁} .(_ ++ Γ₀) {Δ'} {A = A} f (⊸r⊸l {Γ} {C = C}) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ Γ₀ Γ (Δ' ∷ʳ C) A = ⊸r⊸l {Γ}{Γ₀ ++ Γ₁ ++ Δ'}
cong-ccut2 Δ₀ {Δ'}{A = A} f (⊗r⊸l {Γ}{Δ}{Λ}) r with cases++ Δ₀ (Γ ++ Δ) Δ' Λ r
cong-ccut2 _ {Δ'} {A = A} f (⊗r⊸l {Γ}{Δ}) refl | inj₂ (Γ₀ , refl , refl)
  rewrite cases++-inj₂ (Δ ++ Γ₀) Γ Δ' A | cases++-inj₂ Γ₀ Δ Δ' A = ⊗r⊸l
... | inj₁ (Γ₀ , p , refl) with cases++ Δ₀ Γ Γ₀ Δ p
cong-ccut2 Δ₀ {A = A} f (⊗r⊸l {Δ = Δ}{Λ}) refl | inj₁ (_ , refl , refl) | inj₁ (Λ₀ , refl , refl)
  rewrite cases++-inj₁ Δ₀ Λ₀ Δ A | cases++-inj₁ Δ₀ Λ₀ (Δ ++ Λ) A = ⊗r⊸l
cong-ccut2 .(_ ++ Λ₀) {A = A} f (⊗r⊸l {Γ}{_}{Λ}) refl | inj₁ (Γ₀ , refl , refl) | inj₂ (Λ₀ , refl , refl)
  rewrite cases++-inj₂ Λ₀ Γ Γ₀ A | cases++-inj₂ Λ₀ Γ (Γ₀ ++ Λ) A | cases++-inj₁ Λ₀ Γ₀ Λ A = ⊗r⊸l
