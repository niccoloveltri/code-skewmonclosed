{-# OPTIONS --rewriting #-}

module InterpolationEq where

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

cintrp[] : ∀ {S} Γ₀ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C)
  → (eq : Γ ≡ Γ₀ ++ Γ₂)
  → cintrp Γ₀ [] Γ₂ f eq ≡ i-c [] [] (subst-cxt eq f)
cintrp[] Γ₀ Γ₂ (Il f) refl rewrite cintrp[] Γ₀ Γ₂ f refl = refl
cintrp[] Γ₀ Γ₂ (⊗r {Γ = Γ} {Δ} f f₁) eq with ++? Γ₀ Γ Γ₂ Δ eq
cintrp[] ._ Γ₂ (⊗r {Γ = Γ} f f₁) refl | inj₁ (Γ' , refl , refl)
  rewrite cintrp[] Γ' Γ₂ f₁ refl = refl
cintrp[] Γ₀ ._ (⊗r {Δ = Δ} f f₁) refl | inj₂ (A' , Γ' , refl , refl) = refl
cintrp[] Γ₀ Γ₂ (⊗l f) refl rewrite cintrp[] (_ ∷ Γ₀) Γ₂ f refl = refl
cintrp[] Γ₀ Γ₂ (⊸r f) refl rewrite cintrp[] Γ₀ (Γ₂ ∷ʳ _) f refl = refl
cintrp[] Γ₀ Γ₂ (⊸l {Γ} {Δ} f f₁) eq with ++? Γ₀ Γ Γ₂ Δ eq
cintrp[] ._ Γ₂ (⊸l {Γ} f f₁) refl | inj₁ (Γ' , refl , refl)
  rewrite cintrp[] Γ' Γ₂ f₁ refl = refl
cintrp[] Γ₀ ._ (⊸l {Δ = Δ} f f₁) refl | inj₂ (A' , Γ' , refl , refl) = refl
cintrp[] [] _ ax refl = refl
cintrp[] [] _ (pass f) refl = refl
cintrp[] (A ∷ Γ₀) Γ₂ (pass f) refl rewrite cintrp[] Γ₀ Γ₂ f refl = refl
cintrp[] [] .[] Ir refl = refl


⊗r⊸l⋆ : {Γ Δ Λ Ω : Cxt} {A B C : Fma}
  → (fs : Ders Γ Δ) (g : just A ∣ Λ ⊢ B) (h : ─ ∣ Ω ⊢ C)
  → ⊗r {Γ = Γ ++ Λ} (⊸ls fs g) h ≗ ⊸ls fs (⊗r g h)
⊗r⊸l⋆ [] g h = refl
⊗r⊸l⋆ (der Δ D h₁ fs) g h =
  ⊗r⊸l ∙ ⊸l refl (⊗r⊸l⋆ fs g h)

⊸r⊸l⋆ : {Γ Δ Λ : Cxt} {A B C : Fma}
  → (fs : Ders Γ Δ) (g : just A ∣ Λ ∷ʳ B ⊢ C)
  → ⊸r {Γ = Γ ++ Λ} (⊸ls fs g) ≗ ⊸ls fs (⊸r g)
⊸r⊸l⋆ [] g = refl
⊸r⊸l⋆ {Λ = Λ} (der Δ D {Γ} h fs) g =
  ⊸r⊸l {Δ}{Γ ++ Λ} ∙ ⊸l refl (⊸r⊸l⋆ fs g)

cong⊸l⋆1 : {Γ Δ Λ : Cxt} {A C : Fma}
  → {fs fs' : Ders Γ Δ} → fs ≗s fs'
  → (g : just A ∣ Λ ⊢ C)
  → ⊸ls fs g ≗ ⊸ls fs' g
cong⊸l⋆1 []≗ g = refl
cong⊸l⋆1 (der≗ q p) g = ⊸l q (cong⊸l⋆1 p g)

cong⊸l⋆2 : {Γ Δ Λ : Cxt} {A C : Fma}
  → (fs : Ders Γ Δ) 
  → {g g' : just A ∣ Λ ⊢ C} → g ≗ g'
  → ⊸ls fs g ≗ ⊸ls fs g'
cong⊸l⋆2 [] q = q
cong⊸l⋆2 (der Δ D h fs) q = ⊸l refl (cong⊸l⋆2 fs q)

cong⊸l⋆ : {Γ Δ Λ : Cxt} {A C : Fma}
  → {fs fs' : Ders Γ Δ} → fs ≗s fs'
  → {g g' : just A ∣ Λ ⊢ C} → g ≗ g'
  → ⊸ls fs g ≗ ⊸ls fs' g'
cong⊸l⋆ {fs' = fs'} p q =
  cong⊸l⋆1 p _ ∙ cong⊸l⋆2 fs' q

refl≗s : {Δs Ds : Cxt} {hs : Ders Δs Ds} → hs ≗s hs
refl≗s {hs = []} = []≗
refl≗s {hs = der Δ D h hs} = der≗ refl refl≗s

sym≗s : {Δs Ds : Cxt} {hs hs' : Ders Δs Ds}
  → hs ≗s hs' → hs' ≗s hs
sym≗s []≗ = []≗
sym≗s (der≗ eq p) = der≗ (~ eq) (sym≗s p)

trans≗s : {Δs Ds : Cxt} {hs hs' hs'' : Ders Δs Ds}
  → hs ≗s hs' → hs' ≗s hs'' → hs ≗s hs''
trans≗s []≗ q = q
trans≗s (der≗ eq p) (der≗ eq' q) = der≗ (eq ∙ eq') (trans≗s p q)

record sIntrp≗ {S Γ₁ Γ₂ C} (s s' : sIntrp S Γ₁ Γ₂ C) : Set where
  constructor i-s≗
  field
    D≡ : sIntrp.D s ≡ sIntrp.D s'
    g≗ : subst (λ x → S ∣ Γ₁ ⊢ x) D≡ (sIntrp.g s) ≗ sIntrp.g s'
    h≗ : subst (λ x → just x ∣ Γ₂ ⊢ C) D≡ (sIntrp.h s) ≗ sIntrp.h s'

record cIntrp≗ {S Γ₀ Γ₁ Γ₂ C} (c c' : cIntrp S Γ₀ Γ₁ Γ₂ C) : Set where
  constructor i-c≗
  field
    Ds≡ : cIntrp.Ds c ≡ cIntrp.Ds c'
    hs≗ : subst (Ders Γ₁) Ds≡ (cIntrp.hs c) ≗s cIntrp.hs c'
    g≗ : subst (λ x → S ∣ Γ₀ ++ x ++ Γ₂ ⊢ C) Ds≡ (cIntrp.g c) ≗ cIntrp.g c'

-- The interpolation algorithms
sintrp≗ : ∀ {S} Γ₁ Γ₂ {Γ C}
  → {f f' : S ∣ Γ ⊢ C} → f ≗ f'
  → (eq : Γ ≡ Γ₁ ++ Γ₂)
  → sIntrp≗ (sintrp Γ₁ Γ₂ f eq) (sintrp Γ₁ Γ₂ f' eq)
cintrp≗ : ∀{S} Γ₀ Γ₁ Γ₂ {Γ C}
  → {f f' : S ∣ Γ ⊢ C} → f ≗ f'
  → (eq : Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂)
  → cIntrp≗ (cintrp Γ₀ Γ₁ Γ₂ f eq) (cintrp Γ₀ Γ₁ Γ₂ f' eq)

{-
sintrp≗ Γ₁ Γ₂ refl eq = i-s≗ refl refl refl
sintrp≗ Γ₁ Γ₂ {f = f}{g} (~ p) eq with sintrp Γ₁ Γ₂ f eq | sintrp Γ₁ Γ₂ g eq | sintrp≗ Γ₁ Γ₂ p eq
... | i-s D g h | i-s .D g' h' | i-s≗ refl eqg eqh = i-s≗ refl (~ eqg) (~ eqh)
sintrp≗ Γ₁ Γ₂ (_∙_ {f = f}{g}{h} p p') eq with sintrp Γ₁ Γ₂ f eq | sintrp Γ₁ Γ₂ g eq | sintrp Γ₁ Γ₂ h eq | sintrp≗ Γ₁ Γ₂ p eq | sintrp≗ Γ₁ Γ₂ p' eq
... | i-s D g h | i-s .D g' h' | i-s .D g'' h'' | i-s≗ refl eqg eqh | i-s≗ refl eqg' eqh' = i-s≗ refl (eqg ∙ eqg') (eqh ∙ eqh')
sintrp≗ [] Γ₂ (pass p) refl = i-s≗ refl refl (Il (pass p))
sintrp≗ (A ∷ Γ₁) Γ₂ (pass {f = f}{g} p) refl with sintrp Γ₁ Γ₂ f refl | sintrp Γ₁ Γ₂ g refl | sintrp≗ Γ₁ Γ₂ p refl
... | i-s D g h | i-s .D g' h' | i-s≗ refl eqg eqh = i-s≗ refl (pass eqg) eqh
sintrp≗ Γ₁ Γ₂ (Il {f = f}{g} p) refl with sintrp Γ₁ Γ₂ f refl | sintrp Γ₁ Γ₂ g refl | sintrp≗ Γ₁ Γ₂ p refl
... | i-s D g h | i-s .D g' h' | i-s≗ refl eqg eqh = i-s≗ refl (Il eqg) eqh
sintrp≗ Γ₁ Γ₂ (⊗l {f = f}{g} p) refl with sintrp (_ ∷ Γ₁) Γ₂ f refl | sintrp (_ ∷ Γ₁) Γ₂ g refl | sintrp≗ (_ ∷ Γ₁) Γ₂ p refl
... | i-s D g h | i-s .D g' h' | i-s≗ refl eqg eqh = i-s≗ refl (⊗l eqg) eqh
sintrp≗ Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} p p') eq with ++? Γ₁ Γ Γ₂ Δ eq
sintrp≗ Γ₁ Γ₂ (⊗r {Γ = Γ} {_} {f = f}{k}{f'}{k'} p p') refl | inj₁ ([] , refl , refl) 
  with sintrp Γ₁ [] f refl | sintrp Γ₁ [] k refl | sintrp≗ Γ₁ [] p refl
... | i-s D g h | i-s .D j l | i-s≗ refl eqg eqh = i-s≗ refl eqg (⊗r eqh p')
sintrp≗ Γ₁ Γ₂ (⊗r {Γ = Γ} {_} {f = f}{k}{f'}{k'} p p') refl | inj₁ (A' ∷ Γ₀ , refl , refl)
  with sintrp Γ [] f refl | sintrp Γ [] k refl | sintrp (A' ∷ Γ₀) Γ₂ f' refl | sintrp (A' ∷ Γ₀) Γ₂ k' refl
     | sintrp≗ Γ [] p refl | sintrp≗ (A' ∷ Γ₀) Γ₂ p' refl
... | i-s D g h | i-s .D j l | i-s E g' h' | i-s .E j' l'
    | i-s≗ refl eqg eqh | i-s≗ refl eqg' eqh' = i-s≗ refl (⊗r eqg eqg') (⊗l (⊗r eqh (pass eqh')))
sintrp≗ Γ₁ Γ₂ (⊗r {Γ = _} {_} {f = f}{k}{f'}{k'} p p') refl | inj₂ (A' , Γ₀ , refl , refl)
  with sintrp Γ₁ (A' ∷ Γ₀) f refl | sintrp Γ₁ (A' ∷ Γ₀) k refl | sintrp≗ Γ₁ (A' ∷ Γ₀) p refl
... | i-s D g h | i-s .D j l | i-s≗ refl eqg eqh = i-s≗ refl eqg (⊗r eqh p')
sintrp≗ Γ₁ Γ₂ (⊸r {f = f}{g} p) refl with sintrp Γ₁ (Γ₂ ∷ʳ _) f refl | sintrp Γ₁ (Γ₂ ∷ʳ _) g refl | sintrp≗ Γ₁ (Γ₂ ∷ʳ _) p refl
... | i-s D g h | i-s .D g' h' | i-s≗ refl eqg eqh = i-s≗ refl eqg (⊸r eqh)
sintrp≗ Γ₁ Γ₂ (⊸l {Γ} {Δ} p p') eq with ++? Γ Γ₁ Δ Γ₂ (sym eq)
sintrp≗ Γ₁ ._ (⊸l {_} {Δ} {f = f}{k}{f'}{k'} p p') refl | inj₁ (Γ₀ , refl , refl)
  with cintrp Γ₁ Γ₀ [] f refl | cintrp Γ₁ Γ₀ [] k refl | sintrp [] Δ f' refl | sintrp [] Δ k' refl
     | cintrp≗ Γ₁ Γ₀ [] p refl | sintrp≗ [] Δ p' refl
... | i-c Ds hs g | i-c .Ds ls j | i-s E g' h' | i-s .E j' l'
    | i-c≗ refl eqhs eqg | i-s≗ refl eqk eqh = i-s≗ refl (cong⊸r⋆ Ds (⊸l eqg eqk)) (cong⊸l⋆ eqhs eqh)
sintrp≗ .(_ ++ A' ∷ Γ₀) Γ₂ (⊸l {_} {_} {f = f}{k}{f'}{k'} p p') refl | inj₂ (A' , Γ₀ , refl , refl) 
  with sintrp (A' ∷ Γ₀) Γ₂ f' refl | sintrp (A' ∷ Γ₀) Γ₂ k' refl
     | sintrp≗ (A' ∷ Γ₀) Γ₂ p' refl
... | i-s D g h | i-s .D g' h' | i-s≗ refl eqg eqh = i-s≗ refl (⊸l p eqg) eqh
sintrp≗ [] [] axI refl = i-s≗ refl axI refl
sintrp≗ [] [] ax⊗ refl = i-s≗ refl ax⊗ ax⊗
sintrp≗ [] [] ax⊸ refl = i-s≗ refl ax⊸ ax⊸
sintrp≗ [] ._ ⊗rpass refl = i-s≗ refl refl (⊗rIl ∙ Il ⊗rpass)
sintrp≗ (A' ∷ Γ₁) Γ₂ (⊗rpass {Γ} {Δ}) eq with ++? Γ₁ Γ Γ₂ Δ (inj∷ eq .proj₂)
sintrp≗ (A' ∷ _) Γ₂ (⊗rpass {Γ} {_}) refl | inj₁ ([] , refl , refl)
  rewrite ++?-inj₁ [] Γ Γ₂ = i-s≗ refl refl refl
sintrp≗ (A' ∷ _) Γ₂ (⊗rpass {Γ} {_}) refl | inj₁ (A'' ∷ Γ₀ , refl , refl)
  rewrite ++?-inj₁ (A'' ∷ Γ₀) Γ Γ₂ = i-s≗ refl ⊗rpass refl
sintrp≗ (A' ∷ Γ₁) ._ (⊗rpass {_} {Δ}) refl | inj₂ (A₀ , Γ₀ , refl , refl)
  rewrite ++?-inj₂ Γ₁ Γ₀ Δ A₀ = i-s≗ refl refl refl
sintrp≗ Γ₁ Γ₂ (⊗rIl {Γ} {Δ}) eq with ++? Γ₁ Γ Γ₂ Δ eq
sintrp≗ ._ Γ₂ (⊗rIl {Γ} {_}) refl | inj₁ ([] , refl , refl)
  rewrite ++?-inj₁ [] Γ Γ₂ = i-s≗ refl refl refl 
sintrp≗ ._ Γ₂ (⊗rIl {Γ} {_}) refl | inj₁ (A ∷ Γ₀ , refl , refl)
  rewrite ++?-inj₁ (A ∷ Γ₀) Γ Γ₂ = i-s≗ refl ⊗rIl refl 
sintrp≗ Γ₁ ._ (⊗rIl {_} {Δ}) refl | inj₂ (A' , Γ₀ , refl , refl) 
  rewrite ++?-inj₂ Γ₁ Γ₀ Δ A' = i-s≗ refl refl refl
sintrp≗ Γ₁ Γ₂ (⊗r⊗l {Γ} {Δ}) eq with ++? Γ₁ Γ Γ₂ Δ eq
sintrp≗ ._ Γ₂ (⊗r⊗l {Γ} {_}) refl | inj₁ ([] , refl , refl)
  rewrite ++?-inj₁ [] Γ Γ₂ = i-s≗ refl refl refl 
sintrp≗ ._ Γ₂ (⊗r⊗l {Γ} {_}) refl | inj₁ (A ∷ Γ₀ , refl , refl)
  rewrite ++?-inj₁ (A ∷ Γ₀) Γ Γ₂ = i-s≗ refl ⊗r⊗l refl 
sintrp≗ Γ₁ ._ (⊗r⊗l {_} {Δ}) refl | inj₂ (A' , Γ₀ , refl , refl) 
  rewrite ++?-inj₂ Γ₁ Γ₀ Δ A' = i-s≗ refl refl refl
sintrp≗ Γ₁ Γ₂ (⊗r⊸l {Γ} {Δ} {Λ}) eq with ++? Γ Γ₁ (Δ ++ Λ) Γ₂ (sym eq)
sintrp≗ Γ₁ ._ (⊗r⊸l {_} {Δ} {Λ}) refl | inj₁ (Γ₀ , refl , refl) with ++? Γ₁ (Γ₁ ++ Γ₀ ++ Δ) (Γ₀ ++ Δ ++ Λ) Λ refl
sintrp≗ Γ₁ ._ (⊗r⊸l {_} {Δ} {Λ}) refl | inj₁ (Γ₀ , refl , refl) | inj₁ (Λ₀ , p , q) with canc++ [] (Λ₀ ++ Γ₀ ++ Δ) {Λ} p
sintrp≗ Γ₁ ._ (⊗r⊸l {Γ} {[]} {Λ} {f = f}) refl | inj₁ ([] , refl , refl) | inj₁ ([] , refl , refl) | refl
  rewrite ++?-inj₁ [] Γ₁ [] | cintrp[] Γ [] f refl = i-s≗ refl refl refl
sintrp≗ Γ₁ ._ (⊗r⊸l {_} {Δ} {Λ}) refl | inj₁ (Γ₀ , refl , refl) | inj₂ (A , Λ₀ , p , q) with canc++ (Γ₀ ++ Δ) (A ∷ Λ₀) {Λ} q
sintrp≗ Γ₁ ._ (⊗r⊸l {_} {Δ} {Λ}) refl | inj₁ ([] , refl , refl) | inj₂ (A , Λ₀ , refl , refl) | refl
  rewrite ++?-inj₁ [] Γ₁ (A ∷ Λ₀) = i-s≗ refl refl (⊗r⊸l⋆ _ _ _)
sintrp≗ Γ₁ Γ₂@_ (⊗r⊸l {_} {[]} {Λ} {f = f}) refl | inj₁ (A' ∷ Γ₀ , refl , refl) | inj₂ (A , Λ₀ , refl , refl) | refl 
  rewrite ++?-inj₁ (A' ∷ Γ₀) Γ₁ [] = i-s≗ refl refl (⊗r⊸l⋆ _ _ _) 
sintrp≗ Γ₁ ._ (⊗r⊸l {_} {A₀ ∷ Δ} {Λ}) refl | inj₁ (A' ∷ Γ₀ , refl , refl) | inj₂ (A , Λ₀ , refl , refl) | refl 
  rewrite ++?-inj₁ (A' ∷ Γ₀) Γ₁ (A₀ ∷ Δ) = i-s≗ refl refl (⊗r⊸l⋆ _ _ _)
sintrp≗ .(_ ++ A' ∷ Γ₀) Γ₂ (⊗r⊸l {Γ} {[]} {_} {f = f} ) refl | inj₂ (A' , Γ₀ , refl , refl)
  rewrite ++?-inj₁ (A' ∷ Γ₀) Γ Γ₂ | ++?-inj₁ [] Γ [] | cintrp[] Γ [] f refl = i-s≗ refl ⊗r⊸l refl
sintrp≗ .(_ ++ A' ∷ Γ₀) Γ₂ (⊗r⊸l {_} {A₀ ∷ Δ} {Λ}) eq | inj₂ (A' , Γ₀ , refl , q) with ++? Γ₀ Δ Γ₂ Λ (inj∷ q .proj₂)
sintrp≗ ._ Γ₂ (⊗r⊸l {Γ} {A₀ ∷ Δ} {_}) refl | inj₂ (_ , _ , refl , refl) | inj₁ ([] , refl , refl)
  rewrite ++?-inj₁ [] (Γ ++ A₀ ∷ Δ) Γ₂ | ++?-inj₂ Γ Δ [] A₀ | ++?-inj₁ [] Δ Γ₂ = i-s≗ refl refl refl
sintrp≗ ._ Γ₂ (⊗r⊸l {Γ} {A₀ ∷ Δ} {_}) refl | inj₂ (_ , ._ , refl , refl) | inj₁ (A ∷ Δ₀ , refl , refl)
  rewrite ++?-inj₁ (A ∷ Δ₀) (Γ ++ A₀ ∷ Δ) Γ₂ | ++?-inj₂ Γ Δ [] A₀ | ++?-inj₁ (A ∷ Δ₀) Δ Γ₂ = i-s≗ refl ⊗r⊸l refl
sintrp≗ .(_ ++ _ ∷ Γ₀) ._ (⊗r⊸l {Γ} {.(_ ∷ _)} {Λ}) refl | inj₂ (A₀ , Γ₀ , refl , refl) | inj₂ (A₁ , Δ₀ , refl , refl)
  rewrite ++?-inj₂ (Γ ++ A₀ ∷ Γ₀) Δ₀ Λ A₁ | ++?-inj₂ Γ₀ Δ₀ Λ A₁ | ++?-inj₂ Γ Γ₀ (A₁ ∷ Δ₀) A₀ = i-s≗ refl refl refl
sintrp≗ [] Γ₂ ⊸rpass refl = i-s≗ refl refl (⊸rIl ∙ Il ⊸rpass)
sintrp≗ (A ∷ Γ₁) Γ₂ ⊸rpass refl = i-s≗ refl refl refl
sintrp≗ Γ₁ Γ₂ ⊸rIl refl = i-s≗ refl refl refl
sintrp≗ Γ₁ Γ₂ ⊸r⊗l refl = i-s≗ refl refl refl
sintrp≗ Γ₁ Γ₂ (⊸r⊸l {Γ} {Δ}) eq with ++? Γ Γ₁ Δ Γ₂ (sym eq)
sintrp≗ Γ₁ ._ (⊸r⊸l {_} {Δ} {C = C}) refl | inj₁ (Γ₀ , refl , refl)
  rewrite ++?-inj₁ Γ₀ Γ₁ (Δ ++ C ∷ []) = i-s≗ refl refl (⊸r⊸l⋆ _ _)
sintrp≗ .(_ ++ A ∷ Γ₀) Γ₂ (⊸r⊸l {Γ} {_} {C = C}) refl | inj₂ (A , Γ₀ , refl , refl)
  rewrite ++?-inj₂ Γ Γ₀ (Γ₂ ∷ʳ C) A = i-s≗ refl refl refl
-}

cintrp≗ Γ₀ Γ₁ Γ₂ refl eq = i-c≗ refl refl≗s refl
cintrp≗ Γ₀ Γ₁ Γ₂ {f = f}{f'} (~ p) eq with cintrp Γ₀ Γ₁ Γ₂ f eq | cintrp Γ₀ Γ₁ Γ₂ f' eq | cintrp≗ Γ₀ Γ₁ Γ₂ p eq
... | i-c Ds hs g | i-c .Ds hs' g' | i-c≗ refl eqhs eqg = i-c≗ refl (sym≗s eqhs) (~ eqg)
cintrp≗ Γ₀ Γ₁ Γ₂ (_∙_ {f = f}{f'}{f''} p p') eq
  with cintrp Γ₀ Γ₁ Γ₂ f eq | cintrp Γ₀ Γ₁ Γ₂ f' eq | cintrp Γ₀ Γ₁ Γ₂ f'' eq
     | cintrp≗ Γ₀ Γ₁ Γ₂ p eq | cintrp≗ Γ₀ Γ₁ Γ₂ p' eq
... | i-c Ds hs g | i-c .Ds hs' g' | i-c .Ds hs'' g''
    | i-c≗ refl eqhs eqg | i-c≗ refl eqhs' eqg' = i-c≗ refl (trans≗s eqhs eqhs') (eqg ∙ eqg')
cintrp≗ [] [] Γ₂ (pass p) refl = i-c≗ refl []≗ (pass p)
cintrp≗ [] (A ∷ Γ₁) Γ₂ (pass {f = f}{f'} p) refl with sintrp Γ₁ Γ₂ f refl | sintrp Γ₁ Γ₂ f' refl | sintrp≗ Γ₁ Γ₂ p refl
... | i-s D g h | i-s .D g' h' | i-s≗ refl eqg eqh = i-c≗ refl (der≗ (pass eqg) []≗) (pass eqh)
cintrp≗ (A ∷ Γ₀) Γ₁ Γ₂ (pass {f = f}{f'} p) refl with cintrp Γ₀ Γ₁ Γ₂ f refl | cintrp Γ₀ Γ₁ Γ₂ f' refl | cintrp≗ Γ₀ Γ₁ Γ₂ p refl
... | i-c Ds hs g | i-c .Ds hs' g' | i-c≗ refl eqhs eqg = i-c≗ refl eqhs (pass eqg)
cintrp≗ Γ₀ Γ₁ Γ₂ (Il {f = f}{f'} p) refl with cintrp Γ₀ Γ₁ Γ₂ f refl | cintrp Γ₀ Γ₁ Γ₂ f' refl | cintrp≗ Γ₀ Γ₁ Γ₂ p refl
... | i-c Ds hs g | i-c .Ds hs' g' | i-c≗ refl eqhs eqg = i-c≗ refl eqhs (Il eqg)
cintrp≗ Γ₀ Γ₁ Γ₂ (⊗l {f = f}{f'} p) refl with cintrp (_ ∷ Γ₀) Γ₁ Γ₂ f refl | cintrp (_ ∷ Γ₀) Γ₁ Γ₂ f' refl | cintrp≗ (_ ∷ Γ₀) Γ₁ Γ₂ p refl
... | i-c Ds hs g | i-c .Ds hs' g' | i-c≗ refl eqhs eqg = i-c≗ refl eqhs (⊗l eqg)
cintrp≗ Γ₀ Γ₁ Γ₂ (⊗r {Γ = Γ}{Δ} p p') eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
... | inj₂ (A₀ , Λ₀ , refl , q) with ++? (A₀ ∷ Λ₀) Γ₁ Δ Γ₂ q
cintrp≗ Γ₀ [] ._ (⊗r {_} {.(Γ₀ ++ A₀ ∷ Λ₀)} {_} p p') refl | inj₂ (A₀ , Λ₀ , refl , refl) | inj₁ (.(A₀ ∷ Λ₀) , refl , refl) = i-c≗ refl []≗ (⊗r p p')
cintrp≗ Γ₀ (x ∷ Γ₁) Γ₂ (⊗r {_} {.(Γ₀ ++ x ∷ Γ₁ ++ [])} {_} p p') refl | inj₂ (x , .(Γ₁ ++ []) , refl , refl) | inj₁ ([] , refl , refl)
  rewrite ++?-inj₁ [] Γ₁ Γ₂ = {!true!}
cintrp≗ Γ₀ (x ∷ Γ₁) ._ (⊗r {_} {.(Γ₀ ++ x ∷ Γ₁ ++ x₁ ∷ Λ₁)} {Δ} p p') refl | inj₂ (x , .(Γ₁ ++ x₁ ∷ Λ₁) , refl , refl) | inj₁ (x₁ ∷ Λ₁ , refl , refl)
  rewrite ++?-inj₂ Γ₁ Λ₁ Δ x₁ = {!true!}
cintrp≗ Γ₀ .(A₀ ∷ Λ₀ ++ A₁ ∷ Λ₁) Γ₂ (⊗r {_} {.(Γ₀ ++ A₀ ∷ Λ₀)} {_} {f = f}{g}{f'}{g'} p p') refl | inj₂ (A₀ , Λ₀ , refl , refl) | inj₂ (A₁ , Λ₁ , refl , refl)
--  with cintrp Γ₀ (A₀ ∷ Λ₀) [] f refl | cintrp Γ₀ (A₀ ∷ Λ₀) [] g refl | cintrp [] (A₁ ∷ Λ₁) Γ₂ f' refl | cintrp [] (A₁ ∷ Λ₁) Γ₂ g' refl
--... | i-c Ds hs g | i-c Es ks l | i-c Ds' hs' g' | i-c Es' ks' l'
  rewrite ++?-inj₁ (A₁ ∷ Λ₁) Λ₀ Γ₂ = {!true!}
cintrp≗ .(_ ++ Λ₀) Γ₁ Γ₂ (⊗r {Γ = _} {_} {f' = f'}{g' = g'} p p') refl | inj₁ (Λ₀ , refl , refl) 
  with cintrp Λ₀ Γ₁ Γ₂ f' refl | cintrp Λ₀ Γ₁ Γ₂ g' refl | cintrp≗ Λ₀ Γ₁ Γ₂ p' refl
... | i-c Ds hs g | i-c .Ds hs' g' | i-c≗ refl eqhs eqg = i-c≗ refl eqhs (⊗r p eqg)
cintrp≗ Γ₀ Γ₁ Γ₂ (⊸r {f = f}{f'} p) refl with cintrp Γ₀ Γ₁ (Γ₂ ∷ʳ _) f refl | cintrp Γ₀ Γ₁ (Γ₂ ∷ʳ _) f' refl | cintrp≗ Γ₀ Γ₁ (Γ₂ ∷ʳ _) p refl
... | i-c Ds hs g | i-c .Ds hs' g' | i-c≗ refl eqhs eqg = i-c≗ refl eqhs (⊸r eqg)
cintrp≗ Γ₀ Γ₁ Γ₂ (⊸l p p') eq = {!!}
cintrp≗ [] [] [] axI refl = i-c≗ refl []≗ axI
cintrp≗ [] [] [] ax⊗ refl = i-c≗ refl []≗ ax⊗
cintrp≗ [] [] [] ax⊸ refl = i-c≗ refl []≗ ax⊸
cintrp≗ Γ₀ Γ₁ Γ₂ (⊗rpass {Γ} {Δ} {A' = A'}) eq with ++? Γ₀ (A' ∷ Γ) (Γ₁ ++ Γ₂) Δ eq
cintrp≗ .(_ ∷ _ ++ Λ₀) Γ₁ Γ₂ (⊗rpass {Γ} {_} {A' = _}) refl | inj₁ (Λ₀ , refl , refl)
  rewrite ++?-inj₁ Λ₀ Γ (Γ₁ ++ Γ₂) = i-c≗ refl refl≗s ⊗rpass
... | inj₂ (A₀ , Λ₀ , p , q) with ++? (A₀ ∷ Λ₀) Γ₁ Δ Γ₂ q
cintrp≗ [] [] ._ (⊗rpass {_} {_} {A' = _}) refl | inj₂ (A₀ , Λ₀ , refl , refl) | inj₁ (.(A₀ ∷ Λ₀) , refl , refl) = i-c≗ refl []≗ ⊗rpass
cintrp≗ [] (A'' ∷ Γ₁) Γ₂ (⊗rpass {_} {_} {A' = _} {g = g}) refl | inj₂ (A'' , .(Γ₁ ++ []) , refl , refl) | inj₁ ([] , refl , refl)
  rewrite ++?-inj₁ [] Γ₁ Γ₂ | cintrp[] [] Γ₂ g refl = i-c≗ refl (der≗ refl []≗) ⊗rpass
cintrp≗ [] (x ∷ Γ₁) ._ (⊗rpass {_} {Δ} {A' = _}) refl | inj₂ (x , .(Γ₁ ++ x₁ ∷ Λ₁) , refl , refl) | inj₁ (x₁ ∷ Λ₁ , refl , refl)
  rewrite ++?-inj₂ Γ₁ Λ₁ Δ x₁ = i-c≗ refl (der≗ refl []≗) ⊗rpass
cintrp≗ (x ∷ Γ₀) [] ._ (⊗rpass {_} {Δ} {A' = _}) refl | inj₂ (A₀ , Λ₀ , refl , refl) | inj₁ (.(A₀ ∷ Λ₀) , refl , refl)
  rewrite ++?-inj₂ Γ₀ Λ₀ Δ A₀ = i-c≗ refl []≗ ⊗rpass
cintrp≗ (x ∷ Γ₀) (x₁ ∷ Γ₁) Γ₂ (⊗rpass {_} {_} {A' = _}) refl | inj₂ (x₁ , .(Γ₁ ++ []) , refl , refl) | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ Γ₀ Γ₁ Γ₂ x₁ | ++?-inj₁ [] Γ₁ Γ₂ = i-c≗ refl refl≗s ⊗rpass
cintrp≗ (x ∷ Γ₀) (x₁ ∷ Γ₁) _ (⊗rpass {_} {Δ} {A' = _}) refl | inj₂ (x₁ , .(Γ₁ ++ x₂ ∷ Λ₁) , refl , refl) | inj₁ (x₂ ∷ Λ₁ , refl , refl)
  rewrite ++?-inj₂ Γ₀ (Γ₁ ++ x₂ ∷ Λ₁) Δ x₁ | ++?-inj₂ Γ₁ Λ₁ Δ x₂ = i-c≗ refl refl≗s ⊗rpass
cintrp≗ [] .(A₀ ∷ Λ₀ ++ A₁ ∷ Λ₁) Γ₂ (⊗rpass {_} {_} {A' = _}) refl | inj₂ (A₀ , Λ₀ , refl , refl) | inj₂ (A₁ , Λ₁ , refl , refl)
  rewrite ++?-inj₁ (A₁ ∷ Λ₁) Λ₀ Γ₂ = i-c≗ {!!} {!!} {!!} --problem
cintrp≗ (x ∷ Γ₀) .(A₀ ∷ Λ₀ ++ A₁ ∷ Λ₁) Γ₂ (⊗rpass {_} {_} {A' = _}) refl | inj₂ (A₀ , Λ₀ , refl , refl) | inj₂ (A₁ , Λ₁ , refl , refl)
  rewrite  ++?-inj₂ Γ₀ Λ₀ (A₁ ∷ Λ₁ ++ Γ₂) A₀ | ++?-inj₁ (A₁ ∷ Λ₁) Λ₀ Γ₂ = i-c≗ refl refl≗s ⊗rpass
cintrp≗ Γ₀ Γ₁ Γ₂ (⊗rIl {Γ} {Δ}) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
cintrp≗ .(_ ++ Λ₀) Γ₁ Γ₂ (⊗rIl {Γ} {_}) refl | inj₁ (Λ₀ , refl , refl)
  rewrite ++?-inj₁ Λ₀ Γ (Γ₁ ++ Γ₂) = i-c≗ refl refl≗s ⊗rIl
cintrp≗ Γ₀ [] ._ (⊗rIl {_} {Δ}) refl | inj₂ (A' , Λ₀ , refl , refl)
  rewrite ++?-inj₂ Γ₀ Λ₀ Δ A' = i-c≗ refl []≗ ⊗rIl
cintrp≗ Γ₀ (x ∷ Γ₁) Γ₂ (⊗rIl {_} {Δ}) eq | inj₂ (A' , Λ₀ , refl , p) with ++? Γ₁ Λ₀ Γ₂ Δ (sym (inj∷ p .proj₂))
cintrp≗ Γ₀ (x ∷ .(Λ₀ ++ Λ₁)) Γ₂ (⊗rIl {.(Γ₀ ++ x ∷ Λ₀)} {_}) refl | inj₂ (.x , Λ₀ , refl , refl) | inj₁ (Λ₁ , refl , refl)
  rewrite ++?-inj₂ Γ₀ Λ₀ (Λ₁ ++ Γ₂) x | ++?-inj₁ Λ₁ Λ₀ Γ₂ = i-c≗ refl refl≗s ⊗rIl
cintrp≗ Γ₀ (x ∷ Γ₁) ._ (⊗rIl {.(Γ₀ ++ x ∷ Γ₁ ++ A'' ∷ Λ₁)} {Δ}) refl | inj₂ (.x , .(Γ₁ ++ A'' ∷ Λ₁) , refl , refl) | inj₂ (A'' , Λ₁ , refl , refl)
  rewrite ++?-inj₂ Γ₁ Λ₁ Δ A'' | ++?-inj₂ Γ₀ (Γ₁ ++ A'' ∷ Λ₁) Δ x | ++?-inj₂ Γ₁ Λ₁ Δ A'' = i-c≗ refl refl≗s ⊗rIl
cintrp≗ Γ₀ Γ₁ Γ₂ (⊗r⊗l {Γ} {Δ}) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
cintrp≗ .(_ ++ Λ₀) Γ₁ Γ₂ (⊗r⊗l {Γ} {_}) refl | inj₁ (Λ₀ , refl , refl)
  rewrite ++?-inj₁ Λ₀ Γ (Γ₁ ++ Γ₂) = i-c≗ refl refl≗s ⊗r⊗l
cintrp≗ Γ₀ [] ._ (⊗r⊗l {_} {Δ}) refl | inj₂ (A' , Λ₀ , refl , refl)
  rewrite ++?-inj₂ Γ₀ Λ₀ Δ A' = i-c≗ refl []≗ ⊗r⊗l
cintrp≗ Γ₀ (x ∷ Γ₁) Γ₂ (⊗r⊗l {_} {Δ}) eq | inj₂ (A' , Λ₀ , refl , p) with ++? Γ₁ Λ₀ Γ₂ Δ (sym (inj∷ p .proj₂))
cintrp≗ Γ₀ (x ∷ .(Λ₀ ++ Λ₁)) Γ₂ (⊗r⊗l {.(Γ₀ ++ x ∷ Λ₀)} {_}) refl | inj₂ (.x , Λ₀ , refl , refl) | inj₁ (Λ₁ , refl , refl)
  rewrite ++?-inj₂ Γ₀ Λ₀ (Λ₁ ++ Γ₂) x | ++?-inj₁ Λ₁ Λ₀ Γ₂ = i-c≗ refl refl≗s ⊗r⊗l
cintrp≗ Γ₀ (x ∷ Γ₁) ._ (⊗r⊗l {.(Γ₀ ++ x ∷ Γ₁ ++ A'' ∷ Λ₁)} {Δ}) refl | inj₂ (.x , .(Γ₁ ++ A'' ∷ Λ₁) , refl , refl) | inj₂ (A'' , Λ₁ , refl , refl)
  rewrite ++?-inj₂ Γ₁ Λ₁ Δ A'' | ++?-inj₂ Γ₀ (Γ₁ ++ A'' ∷ Λ₁) Δ x | ++?-inj₂ Γ₁ Λ₁ Δ A'' = i-c≗ refl refl≗s ⊗r⊗l
cintrp≗ Γ₀ Γ₁ Γ₂ (⊗r⊸l {Γ} {Δ} {Λ}) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) (Δ ++ Λ) eq
cintrp≗ .(_ ++ Λ₀) Γ₁ Γ₂ (⊗r⊸l {_} {Δ} {Λ}) eq | inj₁ (Λ₀ , p , refl) with ++? Λ₀ Δ (Γ₁ ++ Γ₂) Λ p
cintrp≗ ._ Γ₁ Γ₂ (⊗r⊸l {Γ} {Δ} {_}) refl | inj₁ (.(_ ++ Λ₁) , refl , refl) | inj₁ (Λ₁ , refl , refl)
  rewrite ++?-inj₁ Λ₁ (Γ ++ Δ) (Γ₁ ++ Γ₂) | ++?-inj₁ Λ₁ Δ (Γ₁ ++ Γ₂) = i-c≗ refl refl≗s ⊗r⊸l
... | inj₂ (A₁ , Λ₁ , refl , q') with ++? (A₁ ∷ Λ₁) Γ₁ Λ Γ₂ q'
cintrp≗ .(_ ++ Λ₀) [] ._ (⊗r⊸l {Γ} {.(Λ₀ ++ A₁ ∷ Λ₁)} {Λ}) refl | inj₁ (Λ₀ , refl , refl) | inj₂ (A₁ , Λ₁ , refl , refl) | inj₁ (.(A₁ ∷ Λ₁) , refl , refl)
  rewrite ++?-inj₂ (Γ ++ Λ₀) Λ₁ Λ A₁ | ++?-inj₂ Λ₀ Λ₁ Λ A₁ = i-c≗ refl []≗ ⊗r⊸l
cintrp≗ .(_ ++ Λ₀) (x ∷ Γ₁) ._ (⊗r⊸l {Γ} {._} {Λ}) refl | inj₁ (Λ₀ , refl , refl) | inj₂ (.x , ._ , refl , refl) | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ (Γ ++ Λ₀) Γ₁ Λ x | ++?-inj₂ Λ₀ Γ₁ Λ x | ++?-inj₁ [] Γ₁ Λ | ++?-inj₁ Λ₀ Γ (x ∷ Γ₁) = i-c≗ refl refl≗s ⊗r⊸l
cintrp≗ .(_ ++ Λ₀) (x ∷ Γ₁) ._ (⊗r⊸l {Γ} {._} {Λ}) refl | inj₁ (Λ₀ , refl , refl) | inj₂ (.x , ._ , refl , refl) | inj₁ (y ∷ Λ₂ , refl , refl)
  rewrite ++?-inj₂ (Γ ++ Λ₀) (Γ₁ ++ y ∷ Λ₂) Λ x | ++?-inj₂ Λ₀ (Γ₁ ++ y ∷ Λ₂) Λ x | ++?-inj₂ Γ₁ Λ₂ Λ y | ++?-inj₁ Λ₀ Γ (x ∷ Γ₁ ++ y ∷ Λ₂) = i-c≗ refl refl≗s ⊗r⊸l
cintrp≗ .(_ ++ Λ₀) .(A₁ ∷ Λ₁ ++ A₂ ∷ Λ₂) Γ₂ (⊗r⊸l {Γ} {.(Λ₀ ++ A₁ ∷ Λ₁)} {_}) refl | inj₁ (Λ₀ , refl , refl) | inj₂ (A₁ , Λ₁ , refl , refl) | inj₂ (A₂ , Λ₂ , refl , refl)
  rewrite ++?-inj₂ (Γ ++ Λ₀) Λ₁ (A₂ ∷ Λ₂ ++ Γ₂) A₁ | ++?-inj₂ Λ₀ Λ₁ (A₂ ∷ Λ₂ ++ Γ₂) A₁ | ++?-inj₁ (A₂ ∷ Λ₂) Λ₁ Γ₂ | ++?-inj₁ Λ₀ Γ (A₁ ∷ Λ₁) = i-c≗ refl refl≗s ⊗r⊸l
cintrp≗ Γ₀ Γ₁ Γ₂ (⊗r⊸l {_} {Δ} {Λ}) eq | inj₂ (A , Λ₀ , refl , q) with ++? (A ∷ Λ₀) Γ₁ (Δ ++ Λ) Γ₂ q
cintrp≗ Γ₀ [] ._ (⊗r⊸l {.(Γ₀ ++ A ∷ Λ₀)} {Δ} {Λ}) refl | inj₂ (A , Λ₀ , refl , refl) | inj₁ (.(A ∷ Λ₀) , refl , refl)
  rewrite ++?-inj₂ Γ₀ (Λ₀ ++ Δ) Λ A = i-c≗ refl []≗ ⊗r⊸l
cintrp≗ Γ₀ (x ∷ Γ₁) ._ (⊗r⊸l {._} {[]} {Λ} {f' = f'} {g = g}) refl | inj₂ (.x , ._ , refl , refl) | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ Γ₀ Γ₁ Λ x | ++?-inj₁ [] Γ₁ Λ | ++?-inj₂ Γ₀ Γ₁ [] x | ++?-inj₁ [] Γ₁ [] | cintrp[] [] Λ g refl | cintrp[] [] [] f' refl = i-c≗ refl {!true!} ⊗r⊸l
cintrp≗ Γ₀ (x ∷ Γ₁) ._ (⊗r⊸l {._} {z ∷ Δ} {Λ} {f' = f'}) refl | inj₂ (.x , ._ , refl , refl) | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ Γ₀ (Γ₁ ++ z ∷ Δ) Λ x | ++?-inj₁ [] Γ₁ (z ∷ Δ ++ Λ) | ++?-inj₂ Γ₁ Δ Λ z | ++?-inj₂ Γ₀ Γ₁ (z ∷ Δ) x | ++?-inj₁ [] Γ₁ (z ∷ Δ) | cintrp[] [] (z ∷ Δ) f' refl =
    i-c≗ refl refl≗s ⊗r⊸l
cintrp≗ Γ₀ (x ∷ Γ₁) ._ (⊗r⊸l {._} {Δ} {Λ}) refl | inj₂ (.x , ._ , refl , refl) | inj₁ (A₁ ∷ Λ₁ , refl , refl)
  rewrite ++?-inj₂ Γ₀ (Γ₁ ++ A₁ ∷ Λ₁ ++ Δ) Λ x | ++?-inj₂ Γ₁ (Λ₁ ++ Δ) Λ A₁ | ++?-inj₂ Γ₀ (Γ₁ ++ A₁ ∷ Λ₁) Δ x | ++?-inj₂ Γ₁ Λ₁ Δ A₁ | ++?-inj₂ Γ₁ Λ₁ (Δ ++ Λ) A₁ =
    i-c≗ refl refl≗s ⊗r⊸l
cintrp≗ Γ₀ .(A ∷ Λ₀ ++ A₁ ∷ Λ₁) Γ₂ (⊗r⊸l {.(Γ₀ ++ A ∷ Λ₀)} {Δ} {Λ}) eq | inj₂ (A , Λ₀ , refl , q) | inj₂ (A₁ , Λ₁ , refl , q') with ++? (A₁ ∷ Λ₁) Δ Γ₂ Λ q'
cintrp≗ Γ₀ .(A ∷ Λ₀ ++ A₁ ∷ Λ₁) Γ₂ (⊗r⊸l {.(Γ₀ ++ A ∷ Λ₀)} {[]} {_} {f' = f'}) refl | inj₂ (A , Λ₀ , refl , refl) | inj₂ (A₁ , Λ₁ , refl , refl) | inj₁ (.(A₁ ∷ Λ₁) , refl , refl)
  rewrite ++?-inj₂ Γ₀ Λ₀ (A₁ ∷ Λ₁ ++ Γ₂) A | ++?-inj₁ (A₁ ∷ Λ₁) Λ₀ Γ₂ | ++?-inj₂ Γ₀ Λ₀ [] A | ++?-inj₁ [] Λ₀ [] | cintrp[] [] [] f' refl = i-c≗ refl {!true!} ⊗r⊸l
cintrp≗ Γ₀ .(A ∷ Λ₀ ++ x ∷ Δ ++ Λ₂) Γ₂ (⊗r⊸l {.(Γ₀ ++ A ∷ Λ₀)} {x ∷ Δ} {Λ}) refl | inj₂ (A , Λ₀ , refl , refl) | inj₂ (.x , .(Δ ++ Λ₂) , refl , refl) | inj₁ (Λ₂ , refl , refl)
  rewrite ++?-inj₂ Γ₀ (Λ₀ ++ x ∷ Δ) (Λ₂ ++ Γ₂) A | ++?-inj₁ (x ∷ Δ ++ Λ₂) Λ₀ Γ₂ | ++?-inj₁ Λ₂ (Λ₀ ++ x ∷ Δ) Γ₂ | ++?-inj₂ Γ₀ Λ₀ (x ∷ Δ) A | ++?-inj₁ (x ∷ Δ) Λ₀ [] | ++?-inj₁ Λ₂ Δ Γ₂ =
    i-c≗ refl {!true!} ⊗r⊸l
cintrp≗ Γ₀ .(A ∷ Λ₀ ++ A₁ ∷ Λ₁) ._ (⊗r⊸l {.(Γ₀ ++ A ∷ Λ₀)} {Δ} {Λ}) refl | inj₂ (A , Λ₀ , refl , refl) | inj₂ (A₁ , Λ₁ , refl , refl) | inj₂ (A₂ , Λ₂ , refl , refl)
  rewrite ++?-inj₂ Γ₀ (Λ₀ ++ A₁ ∷ Λ₁ ++ A₂ ∷ Λ₂) Λ A | ++?-inj₁ (A₁ ∷ Λ₁) Λ₀ (A₂ ∷ Λ₂ ++ Λ) | ++?-inj₂ (Λ₀ ++ A₁ ∷ Λ₁) Λ₂ Λ A₂ | ++?-inj₂ Γ₀ Λ₀ (A₁ ∷ Λ₁ ++ A₂ ∷ Λ₂) A
        | ++?-inj₁ (A₁ ∷ Λ₁) Λ₀ (A₂ ∷ Λ₂) | ++?-inj₂ Λ₁ Λ₂ Λ A₂ = i-c≗ refl refl≗s ⊗r⊸l
cintrp≗ [] [] Γ₂ ⊸rpass refl = i-c≗ refl []≗ ⊸rpass
cintrp≗ [] (A ∷ Γ₁) Γ₂ ⊸rpass refl = i-c≗ refl (der≗ refl []≗) ⊸rpass
cintrp≗ (A ∷ Γ₀) Γ₁ Γ₂ ⊸rpass refl = i-c≗ refl refl≗s ⊸rpass
cintrp≗ Γ₀ Γ₁ Γ₂ ⊸rIl refl = i-c≗ refl refl≗s ⊸rIl
cintrp≗ Γ₀ Γ₁ Γ₂ ⊸r⊗l refl = i-c≗ refl refl≗s ⊸r⊗l
cintrp≗ Γ₀ Γ₁ Γ₂ (⊸r⊸l {Γ} {Δ}) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
cintrp≗ .(_ ++ Λ₀) Γ₁ Γ₂ (⊸r⊸l {Γ} {C = C} {g = g}) refl | inj₁ (Λ₀ , refl , refl)
  rewrite ++?-inj₁ Λ₀ Γ (Γ₁ ++ Γ₂ ∷ʳ C) = i-c≗ refl refl≗s (⊸r⊸l {Γ}{Λ₀ ++ cIntrp.Ds (cintrp Λ₀ Γ₁ (Γ₂ ++ C ∷ []) g refl) ++ Γ₂})
cintrp≗ Γ₀ [] ._ (⊸r⊸l {_} {Δ} {C = C} {g = g}) refl | inj₂ (A , Λ₀ , refl , refl)
  rewrite ++?-inj₂ Γ₀ Λ₀ (Δ ++ C ∷ []) A = i-c≗ refl []≗ ⊸r⊸l
cintrp≗ Γ₀ (x ∷ Γ₁) Γ₂ (⊸r⊸l {_} {_}) eq | inj₂ (A , Λ₀ , refl , q) with cases∷ [] q
cintrp≗ Γ₀ (x ∷ Γ₁) Γ₂ (⊸r⊸l {.(Γ₀ ++ x ∷ Λ₀)} {Δ}) eq | inj₂ (.x , Λ₀ , refl , q) | inj₁ (refl , refl , q') with ++? Γ₁ Λ₀ Γ₂ Δ q'
cintrp≗ Γ₀ (x ∷ .(Λ₀ ++ Λ₁)) Γ₂ (⊸r⊸l {.(Γ₀ ++ x ∷ Λ₀)} {_} {C = C}{f = f}{g}) refl | inj₂ (x , Λ₀ , refl , refl) | inj₁ (refl , refl , refl) | inj₁ (Λ₁ , refl , refl) 
  rewrite ++?-inj₂ Γ₀ Λ₀ (Λ₁ ++ Γ₂ ++ C ∷ []) x | ++?-inj₁ Λ₁ Λ₀ (Γ₂ ++ C ∷ []) =
    i-c≗ refl refl≗s (⊸r⊸l {Γ₀ ++ cIntrp.Ds (cintrp Γ₀ (x ∷ Λ₀) [] f refl)} {cIntrp.Ds (cintrp [] Λ₁ (Γ₂ ++ C ∷ []) g refl) ++ Γ₂})
cintrp≗ Γ₀ (x ∷ Γ₁) ._ (⊸r⊸l {.(Γ₀ ++ x ∷ Γ₁ ++ A₁ ∷ Λ₁)} {Δ} {C = C}) refl | inj₂ (x , .(Γ₁ ++ A₁ ∷ Λ₁) , refl , refl) | inj₁ (refl , refl , refl) | inj₂ (A₁ , Λ₁ , refl , refl)
  rewrite ++?-inj₁ Γ₀ (x ∷ Γ₁ ++ A₁ ∷ Λ₁) (Δ ++ C ∷ []) | ++?-inj₂ Γ₀ (Γ₁ ++ A₁ ∷ Λ₁) (Δ ++ C ∷ []) x | ++?-inj₂ Γ₁ Λ₁ (Δ ++ C ∷ []) A₁ =
    i-c≗ refl refl≗s ⊸r⊸l



-- sintrp Γ₁ Γ₂ (Il f) refl =
--   i-s (sIntrp.D (sintrp Γ₁ Γ₂ f refl))
--       (Il (sIntrp.g (sintrp Γ₁ Γ₂ f refl)))
--       (sIntrp.h (sintrp Γ₁ Γ₂ f refl))
-- sintrp Γ₁ Γ₂ (⊗l f) refl =
--   i-s (sIntrp.D (sintrp (_ ∷ Γ₁) Γ₂ f refl))
--       (⊗l (sIntrp.g (sintrp (_ ∷ Γ₁) Γ₂ f refl)))
--       (sIntrp.h (sintrp (_ ∷ Γ₁) Γ₂ f refl))
-- sintrp Γ₁ Γ₂ (⊸r {A = A}{B} f) refl =
--   i-s (sIntrp.D (sintrp Γ₁ (Γ₂ ∷ʳ _) f refl))
--       (sIntrp.g (sintrp Γ₁ (Γ₂ ∷ʳ _) f refl))
--       (⊸r (sIntrp.h (sintrp Γ₁ (Γ₂ ∷ʳ _) f refl)))
-- sintrp Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
-- sintrp {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (Γ' , refl , refl) =
--   i-s (sIntrp.D (sintrp Γ [] f refl) ⊗ sIntrp.D (sintrp Γ' Γ₂ g refl))
--       (⊗r (sIntrp.g (sintrp Γ [] f refl)) (sIntrp.g (sintrp Γ' Γ₂ g refl)))
--       (⊗l (⊗r (sIntrp.h (sintrp Γ [] f refl)) (pass (sIntrp.h (sintrp Γ' Γ₂ g refl)))))
-- sintrp Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) eq | inj₂ (A' , Γ' , refl , refl) with sintrp Γ₁ (_ ∷ Γ') f refl
-- sintrp Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) | i-s D h k = i-s D h (⊗r k g)
-- sintrp Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ Γ₁ Δ Γ₂ (sym eq)
-- sintrp Γ₁ .(Γ' ++ Δ) (⊸l {Δ = Δ} {A}{B}{C} f g) eq | inj₁ (Γ' , refl , refl) with sintrp [] Δ g refl | cintrp Γ₁ Γ' [] f refl
-- sintrp Γ₁ .(_ ++ Δ) (⊸l {Δ = Δ} f g) refl | inj₁ (_ , refl , refl) | i-s E h k | i-c Ds gs l =
--   i-s (Ds ⊸⋆ E) (⊸r⋆ Ds (⊸l l h)) (⊸ls gs k)
-- sintrp _ Γ₂ (⊸l {Γ} {A = A}{B} f g) eq | inj₂ (A' , Γ' , refl , refl) with sintrp (A' ∷ Γ') Γ₂ g refl
-- sintrp _ Γ₂ (⊸l {Γ} {A = A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) | i-s D h k = i-s _ (⊸l f h) k
-- sintrp [] [] ax refl = i-s _ ax ax
-- sintrp [] (A ∷ Γ₂) (pass f) refl = i-s _ Ir (Il (pass f)) 
-- sintrp (A ∷ Γ₁) Γ₂ (pass f) refl =
--   i-s (sIntrp.D (sintrp Γ₁ Γ₂ f refl))
--       (pass (sIntrp.g (sintrp Γ₁ Γ₂ f refl)))
--       (sIntrp.h (sintrp Γ₁ Γ₂ f refl))
-- sintrp [] [] Ir refl = i-s I Ir ax

-- cintrp Γ₀ Γ₁ Γ₂ (Il f) refl with cintrp Γ₀ Γ₁ Γ₂ f refl
-- ... | i-c Ds gs h = i-c Ds gs (Il h) 
-- cintrp {S} Γ₀ Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} {A}{B} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
-- ... | inj₁ (Γ₀ , refl , refl) with cintrp Γ₀ Γ₁ Γ₂ g refl
-- cintrp {S} _ _ Γ₂ (⊗r {Γ = Γ} {A = A} {B} f g) refl | inj₁ (Γ₀ , refl , refl) | i-c Ds gs h =  i-c Ds gs (⊗r f h)
-- cintrp Γ₀ [] _ (⊗r f g) refl | inj₂ (A , Γ₁ , refl , refl) = i-c [] [] (⊗r f g)
-- cintrp {S} Γ₀ (A ∷ Γ₁) Γ₂ (⊗r {Δ = Δ} {A₁}{B₁} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
-- ... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
-- ... | inj₂ (A' , Γ₂ , refl , refl) with cintrp Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
-- cintrp {S} Γ₀ (A ∷ Γ₁) _ (⊗r {Δ = Δ} {A₁} {B₁} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) | i-c Ds gs h = i-c Ds gs (⊗r h g)
-- cintrp {S} Γ₀ (A ∷ _) Γ₂ (⊗r {A = A₁}{B} f g) eq | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , eq') | inj₁ (Γ₁ , refl , refl) with cintrp Γ₀ (_ ∷ Γ') [] f refl | cintrp [] Γ₁ Γ₂ g refl
-- cintrp {S} Γ₀ (A ∷ _) Γ₂ (⊗r {A = A₁}{B} f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁@_ , refl , refl) | i-c Ds gs h | i-c Es ls k = 
--   i-c (Ds ++ Es) (gs ++s ls) (⊗r h k)
-- cintrp Γ₀ Γ₁ Γ₂ (⊗l f) refl with cintrp (_ ∷ Γ₀) Γ₁ Γ₂ f refl
-- ... | i-c Ds gs h = i-c Ds gs (⊗l h) 
-- cintrp {S} Γ₀ Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with cintrp Γ₀ Γ₁ (Γ₂ ∷ʳ _) f refl
-- ... | i-c Ds gs h = i-c Ds gs (⊸r h)
-- cintrp Γ₀ Γ₁ Γ₂ (⊸l {Γ} {Δ} {A}{B}{C} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
-- ... | inj₁ (Γ₀ , refl , refl) with cintrp Γ₀ Γ₁ Γ₂ g refl
-- cintrp _ _ Γ₂ (⊸l {Γ} {A = A}{B}{C} f g) refl | inj₁ (Γ₀ , refl , refl) | i-c Ds gs h = i-c Ds gs (⊸l {Γ = Γ} f h)
-- cintrp Γ₀ [] _ (⊸l f g) refl | inj₂ (B , Γ' , refl , refl) = i-c [] [] (⊸l f g)
-- cintrp Γ₀ (A ∷ Γ₁) Γ₂ (⊸l {Δ = Δ} {A₁}{B₁}{C} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
-- ... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
-- ... | inj₂ (A' , Γ₂ , refl , refl) with cintrp Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
-- cintrp Γ₀ (A ∷ Γ₁) _ (⊸l {Δ = Δ} {A₁}{B₁}{C} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) | i-c Ds gs h = i-c Ds gs (⊸l h g)
-- cintrp Γ₀ (A ∷ _) Γ₂ (⊸l {A = A₁}{B₁}{C} f g) eq | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , eq') | inj₁ (Γ₁ , refl , refl) with cintrp Γ₀ (_ ∷ Γ') [] f refl | cintrp [] Γ₁ Γ₂ g refl
-- cintrp Γ₀ (A ∷ _) Γ₂ (⊸l {A = A₁}{B₁}{C} f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁@_ , refl , refl) | i-c Ds gs h | i-c Es ls k =
--   i-c (Ds ++ Es) (gs ++s ls) (⊸l h k)
-- cintrp [] [] [] ax refl = i-c [] [] ax
-- cintrp [] [] Γ₂ (pass f) refl = i-c [] [] (pass f) 
-- cintrp [] (A ∷ Γ₁) Γ₂ (pass f) refl with sintrp Γ₁ Γ₂ f refl
-- ... | i-s D g k = i-c [ D ] (der (A ∷ Γ₁) D (pass g) []) (pass k)
-- cintrp (A ∷ Γ₀) Γ₁ Γ₂ (pass f) refl with cintrp Γ₀ Γ₁ Γ₂ f refl
-- ... | i-c Ds gs h = i-c Ds gs (pass h)
-- cintrp [] [] [] Ir refl = i-c [] [] Ir

