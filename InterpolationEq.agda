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
sintrp≗ Γ₁ Γ₂ (⊗r {Γ = Γ} {_} {f = f}{k}{f'}{k'} p p') refl | inj₁ (Γ₀ , refl , refl)
  with sintrp Γ [] f refl | sintrp Γ [] k refl | sintrp Γ₀ Γ₂ f' refl | sintrp Γ₀ Γ₂ k' refl
     | sintrp≗ Γ [] p refl | sintrp≗ Γ₀ Γ₂ p' refl
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
    | i-c≗ refl eqhs eqg | i-s≗ refl eqk eqh = i-s≗ refl (cong⊸r⋆ Ds (⊸l eqg eqk)) {!!}
sintrp≗ .(_ ++ A' ∷ Γ₀) Γ₂ (⊸l {_} {_} {f = f}{k}{f'}{k'} p p') refl | inj₂ (A' , Γ₀ , refl , refl) 
  with sintrp (A' ∷ Γ₀) Γ₂ f' refl | sintrp (A' ∷ Γ₀) Γ₂ k' refl
     | sintrp≗ (A' ∷ Γ₀) Γ₂ p' refl
... | i-s D g h | i-s .D g' h' | i-s≗ refl eqg eqh = i-s≗ refl (⊸l p eqg) eqh
sintrp≗ [] [] axI refl = i-s≗ refl axI refl
sintrp≗ [] [] ax⊗ refl = i-s≗ refl ax⊗ ax⊗
sintrp≗ [] [] ax⊸ refl = i-s≗ refl ax⊸ ax⊸
sintrp≗ [] ._ ⊗rpass refl = i-s≗ refl refl (⊗rIl ∙ Il ⊗rpass)
sintrp≗ (A' ∷ Γ₁) Γ₂ (⊗rpass {Γ} {Δ}) eq with ++? Γ₁ Γ Γ₂ Δ (inj∷ eq .proj₂)
sintrp≗ (A' ∷ .(_ ++ Γ₀)) Γ₂ (⊗rpass {Γ} {_}) refl | inj₁ (Γ₀ , refl , refl)
  rewrite ++?-inj₁ Γ₀ Γ Γ₂ = i-s≗ refl ⊗rpass refl
sintrp≗ (A' ∷ Γ₁) ._ (⊗rpass {_} {Δ}) refl | inj₂ (A₀ , Γ₀ , refl , refl)
  rewrite ++?-inj₂ Γ₁ Γ₀ Δ A₀ = i-s≗ refl refl refl
sintrp≗ Γ₁ Γ₂ (⊗rIl {Γ} {Δ}) eq with ++? Γ₁ Γ Γ₂ Δ eq
sintrp≗ .(_ ++ Γ₀) Γ₂ (⊗rIl {Γ} {_}) refl | inj₁ (Γ₀ , refl , refl)
  rewrite ++?-inj₁ Γ₀ Γ Γ₂ = i-s≗ refl ⊗rIl refl 
sintrp≗ Γ₁ ._ (⊗rIl {_} {Δ}) refl | inj₂ (A' , Γ₀ , refl , refl) 
  rewrite ++?-inj₂ Γ₁ Γ₀ Δ A' = i-s≗ refl refl refl
sintrp≗ Γ₁ Γ₂ (⊗r⊗l {Γ} {Δ}) eq with ++? Γ₁ Γ Γ₂ Δ eq
sintrp≗ .(_ ++ Γ₀) Γ₂ (⊗r⊗l {Γ} {_}) refl | inj₁ (Γ₀ , refl , refl)
  rewrite ++?-inj₁ Γ₀ Γ Γ₂ = i-s≗ refl ⊗r⊗l refl 
sintrp≗ Γ₁ ._ (⊗r⊗l {_} {Δ}) refl | inj₂ (A' , Γ₀ , refl , refl) 
  rewrite ++?-inj₂ Γ₁ Γ₀ Δ A' = i-s≗ refl refl refl
sintrp≗ Γ₁ Γ₂ (⊗r⊸l {Γ} {Δ} {Λ}) eq with ++? Γ Γ₁ (Δ ++ Λ) Γ₂ (sym eq)
sintrp≗ Γ₁ ._ (⊗r⊸l {_} {Δ} {Λ}) refl | inj₁ (Γ₀ , refl , refl) = {!!}
sintrp≗ .(_ ++ A' ∷ Γ₀) Γ₂ (⊗r⊸l {Γ} {[]} {_} {f = f} ) refl | inj₂ (A' , Γ₀ , refl , refl)
  rewrite ++?-inj₁ (A' ∷ Γ₀) Γ Γ₂ | ++?-inj₁ [] Γ [] | cintrp[] Γ [] f refl = i-s≗ refl ⊗r⊸l refl
sintrp≗ .(_ ++ A' ∷ Γ₀) Γ₂ (⊗r⊸l {_} {A₀ ∷ Δ} {Λ}) eq | inj₂ (A' , Γ₀ , refl , q) with ++? Γ₀ Δ Γ₂ Λ (inj∷ q .proj₂)
sintrp≗ .(_ ++ _ ∷ _ ++ Δ₀) Γ₂ (⊗r⊸l {Γ} {A₀ ∷ Δ} {_}) refl | inj₂ (_ , .(_ ++ Δ₀) , refl , refl) | inj₁ (Δ₀ , refl , refl)
  rewrite ++?-inj₁ Δ₀ (Γ ++ A₀ ∷ Δ) Γ₂ | ++?-inj₂ Γ Δ [] A₀ | ++?-inj₁ Δ₀ Δ Γ₂ = i-s≗ refl ⊗r⊸l refl
sintrp≗ .(_ ++ _ ∷ Γ₀) ._ (⊗r⊸l {Γ} {.(_ ∷ _)} {Λ}) refl | inj₂ (A₀ , Γ₀ , refl , refl) | inj₂ (A₁ , Δ₀ , refl , refl)
  rewrite ++?-inj₂ (Γ ++ A₀ ∷ Γ₀) Δ₀ Λ A₁ | ++?-inj₂ Γ₀ Δ₀ Λ A₁ | ++?-inj₂ Γ Γ₀ (A₁ ∷ Δ₀) A₀ = i-s≗ refl refl refl
sintrp≗ [] Γ₂ ⊸rpass refl = i-s≗ refl refl (⊸rIl ∙ Il ⊸rpass)
sintrp≗ (A ∷ Γ₁) Γ₂ ⊸rpass refl = i-s≗ refl refl refl
sintrp≗ Γ₁ Γ₂ ⊸rIl refl = i-s≗ refl refl refl
sintrp≗ Γ₁ Γ₂ ⊸r⊗l refl = i-s≗ refl refl refl
sintrp≗ Γ₁ Γ₂ ⊸r⊸l eq = {!!}

-- cintrp≗ Γ₀ Γ₁ Γ₂ refl eq = i-c≗ refl refl≗s refl
-- cintrp≗ Γ₀ Γ₁ Γ₂ {f = f}{f'} (~ p) eq with cintrp Γ₀ Γ₁ Γ₂ f eq | cintrp Γ₀ Γ₁ Γ₂ f' eq | cintrp≗ Γ₀ Γ₁ Γ₂ p eq
-- ... | i-c Ds hs g | i-c .Ds hs' g' | i-c≗ refl eqhs eqg = i-c≗ refl (sym≗s eqhs) (~ eqg)
-- cintrp≗ Γ₀ Γ₁ Γ₂ (p ∙ p') eq = {!!}
-- cintrp≗ [] [] Γ₂ (pass p) refl = i-c≗ refl []≗ (pass p)
-- cintrp≗ [] (A ∷ Γ₁) Γ₂ (pass {f = f}{f'} p) refl with sintrp Γ₁ Γ₂ f refl | sintrp Γ₁ Γ₂ f' refl | sintrp≗ Γ₁ Γ₂ p refl
-- ... | i-s D g h | i-s .D g' h' | i-s≗ refl eqg eqh = i-c≗ refl (der≗ (pass eqg) []≗) (pass eqh)
-- cintrp≗ (A ∷ Γ₀) Γ₁ Γ₂ (pass p) refl = {!!}
-- cintrp≗ Γ₀ Γ₁ Γ₂ (Il p) eq = {!!}
-- cintrp≗ Γ₀ Γ₁ Γ₂ (⊗l p) eq = {!!}
-- cintrp≗ Γ₀ Γ₁ Γ₂ (⊗r p p₁) eq = {!!}
-- cintrp≗ Γ₀ Γ₁ Γ₂ (⊸r p) eq = {!!}
-- cintrp≗ Γ₀ Γ₁ Γ₂ (⊸l p p₁) eq = {!!}
-- cintrp≗ [] [] [] axI refl = i-c≗ refl []≗ axI
-- cintrp≗ [] [] [] ax⊗ refl = i-c≗ refl []≗ ax⊗
-- cintrp≗ [] [] [] ax⊸ refl = i-c≗ refl []≗ ax⊸
-- cintrp≗ Γ₀ Γ₁ Γ₂ ⊗rpass eq = {!!}
-- cintrp≗ Γ₀ Γ₁ Γ₂ ⊗rIl eq = {!!}
-- cintrp≗ Γ₀ Γ₁ Γ₂ ⊗r⊗l eq = {!!}
-- cintrp≗ Γ₀ Γ₁ Γ₂ ⊗r⊸l eq = {!!}
-- cintrp≗ [] [] Γ₂ ⊸rpass refl = i-c≗ refl []≗ ⊸rpass
-- cintrp≗ [] (A ∷ Γ₁) Γ₂ ⊸rpass refl = i-c≗ refl (der≗ refl []≗) ⊸rpass
-- cintrp≗ (A ∷ Γ₀) Γ₁ Γ₂ ⊸rpass refl = i-c≗ refl refl≗s ⊸rpass
-- cintrp≗ Γ₀ Γ₁ Γ₂ ⊸rIl refl = i-c≗ refl refl≗s ⊸rIl
-- cintrp≗ Γ₀ Γ₁ Γ₂ ⊸r⊗l refl = i-c≗ refl refl≗s ⊸r⊗l
-- cintrp≗ Γ₀ Γ₁ Γ₂ ⊸r⊸l eq = {!!}

-- -- sintrp Γ₁ Γ₂ (Il f) refl =
-- --   i-s (sIntrp.D (sintrp Γ₁ Γ₂ f refl))
-- --       (Il (sIntrp.g (sintrp Γ₁ Γ₂ f refl)))
-- --       (sIntrp.h (sintrp Γ₁ Γ₂ f refl))
-- -- sintrp Γ₁ Γ₂ (⊗l f) refl =
-- --   i-s (sIntrp.D (sintrp (_ ∷ Γ₁) Γ₂ f refl))
-- --       (⊗l (sIntrp.g (sintrp (_ ∷ Γ₁) Γ₂ f refl)))
-- --       (sIntrp.h (sintrp (_ ∷ Γ₁) Γ₂ f refl))
-- -- sintrp Γ₁ Γ₂ (⊸r {A = A}{B} f) refl =
-- --   i-s (sIntrp.D (sintrp Γ₁ (Γ₂ ∷ʳ _) f refl))
-- --       (sIntrp.g (sintrp Γ₁ (Γ₂ ∷ʳ _) f refl))
-- --       (⊸r (sIntrp.h (sintrp Γ₁ (Γ₂ ∷ʳ _) f refl)))
-- -- sintrp Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
-- -- sintrp {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (Γ' , refl , refl) =
-- --   i-s (sIntrp.D (sintrp Γ [] f refl) ⊗ sIntrp.D (sintrp Γ' Γ₂ g refl))
-- --       (⊗r (sIntrp.g (sintrp Γ [] f refl)) (sIntrp.g (sintrp Γ' Γ₂ g refl)))
-- --       (⊗l (⊗r (sIntrp.h (sintrp Γ [] f refl)) (pass (sIntrp.h (sintrp Γ' Γ₂ g refl)))))
-- -- sintrp Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) eq | inj₂ (A' , Γ' , refl , refl) with sintrp Γ₁ (_ ∷ Γ') f refl
-- -- sintrp Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) | i-s D h k = i-s D h (⊗r k g)
-- -- sintrp Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ Γ₁ Δ Γ₂ (sym eq)
-- -- sintrp Γ₁ .(Γ' ++ Δ) (⊸l {Δ = Δ} {A}{B}{C} f g) eq | inj₁ (Γ' , refl , refl) with sintrp [] Δ g refl | cintrp Γ₁ Γ' [] f refl
-- -- sintrp Γ₁ .(_ ++ Δ) (⊸l {Δ = Δ} f g) refl | inj₁ (_ , refl , refl) | i-s E h k | i-c Ds gs l =
-- --   i-s (Ds ⊸⋆ E) (⊸r⋆ Ds (⊸l l h)) (⊸ls gs k)
-- -- sintrp _ Γ₂ (⊸l {Γ} {A = A}{B} f g) eq | inj₂ (A' , Γ' , refl , refl) with sintrp (A' ∷ Γ') Γ₂ g refl
-- -- sintrp _ Γ₂ (⊸l {Γ} {A = A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) | i-s D h k = i-s _ (⊸l f h) k
-- -- sintrp [] [] ax refl = i-s _ ax ax
-- -- sintrp [] (A ∷ Γ₂) (pass f) refl = i-s _ Ir (Il (pass f)) 
-- -- sintrp (A ∷ Γ₁) Γ₂ (pass f) refl =
-- --   i-s (sIntrp.D (sintrp Γ₁ Γ₂ f refl))
-- --       (pass (sIntrp.g (sintrp Γ₁ Γ₂ f refl)))
-- --       (sIntrp.h (sintrp Γ₁ Γ₂ f refl))
-- -- sintrp [] [] Ir refl = i-s I Ir ax

-- -- cintrp Γ₀ Γ₁ Γ₂ (Il f) refl with cintrp Γ₀ Γ₁ Γ₂ f refl
-- -- ... | i-c Ds gs h = i-c Ds gs (Il h) 
-- -- cintrp {S} Γ₀ Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} {A}{B} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
-- -- ... | inj₁ (Γ₀ , refl , refl) with cintrp Γ₀ Γ₁ Γ₂ g refl
-- -- cintrp {S} _ _ Γ₂ (⊗r {Γ = Γ} {A = A} {B} f g) refl | inj₁ (Γ₀ , refl , refl) | i-c Ds gs h =  i-c Ds gs (⊗r f h)
-- -- cintrp Γ₀ [] _ (⊗r f g) refl | inj₂ (A , Γ₁ , refl , refl) = i-c [] [] (⊗r f g)
-- -- cintrp {S} Γ₀ (A ∷ Γ₁) Γ₂ (⊗r {Δ = Δ} {A₁}{B₁} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
-- -- ... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
-- -- ... | inj₂ (A' , Γ₂ , refl , refl) with cintrp Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
-- -- cintrp {S} Γ₀ (A ∷ Γ₁) _ (⊗r {Δ = Δ} {A₁} {B₁} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) | i-c Ds gs h = i-c Ds gs (⊗r h g)
-- -- cintrp {S} Γ₀ (A ∷ _) Γ₂ (⊗r {A = A₁}{B} f g) eq | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , eq') | inj₁ (Γ₁ , refl , refl) with cintrp Γ₀ (_ ∷ Γ') [] f refl | cintrp [] Γ₁ Γ₂ g refl
-- -- cintrp {S} Γ₀ (A ∷ _) Γ₂ (⊗r {A = A₁}{B} f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁@_ , refl , refl) | i-c Ds gs h | i-c Es ls k = 
-- --   i-c (Ds ++ Es) (gs ++s ls) (⊗r h k)
-- -- cintrp Γ₀ Γ₁ Γ₂ (⊗l f) refl with cintrp (_ ∷ Γ₀) Γ₁ Γ₂ f refl
-- -- ... | i-c Ds gs h = i-c Ds gs (⊗l h) 
-- -- cintrp {S} Γ₀ Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with cintrp Γ₀ Γ₁ (Γ₂ ∷ʳ _) f refl
-- -- ... | i-c Ds gs h = i-c Ds gs (⊸r h)
-- -- cintrp Γ₀ Γ₁ Γ₂ (⊸l {Γ} {Δ} {A}{B}{C} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
-- -- ... | inj₁ (Γ₀ , refl , refl) with cintrp Γ₀ Γ₁ Γ₂ g refl
-- -- cintrp _ _ Γ₂ (⊸l {Γ} {A = A}{B}{C} f g) refl | inj₁ (Γ₀ , refl , refl) | i-c Ds gs h = i-c Ds gs (⊸l {Γ = Γ} f h)
-- -- cintrp Γ₀ [] _ (⊸l f g) refl | inj₂ (B , Γ' , refl , refl) = i-c [] [] (⊸l f g)
-- -- cintrp Γ₀ (A ∷ Γ₁) Γ₂ (⊸l {Δ = Δ} {A₁}{B₁}{C} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
-- -- ... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
-- -- ... | inj₂ (A' , Γ₂ , refl , refl) with cintrp Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
-- -- cintrp Γ₀ (A ∷ Γ₁) _ (⊸l {Δ = Δ} {A₁}{B₁}{C} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) | i-c Ds gs h = i-c Ds gs (⊸l h g)
-- -- cintrp Γ₀ (A ∷ _) Γ₂ (⊸l {A = A₁}{B₁}{C} f g) eq | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , eq') | inj₁ (Γ₁ , refl , refl) with cintrp Γ₀ (_ ∷ Γ') [] f refl | cintrp [] Γ₁ Γ₂ g refl
-- -- cintrp Γ₀ (A ∷ _) Γ₂ (⊸l {A = A₁}{B₁}{C} f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁@_ , refl , refl) | i-c Ds gs h | i-c Es ls k =
-- --   i-c (Ds ++ Es) (gs ++s ls) (⊸l h k)
-- -- cintrp [] [] [] ax refl = i-c [] [] ax
-- -- cintrp [] [] Γ₂ (pass f) refl = i-c [] [] (pass f) 
-- -- cintrp [] (A ∷ Γ₁) Γ₂ (pass f) refl with sintrp Γ₁ Γ₂ f refl
-- -- ... | i-s D g k = i-c [ D ] (der (A ∷ Γ₁) D (pass g) []) (pass k)
-- -- cintrp (A ∷ Γ₀) Γ₁ Γ₂ (pass f) refl with cintrp Γ₀ Γ₁ Γ₂ f refl
-- -- ... | i-c Ds gs h = i-c Ds gs (pass h)
-- -- cintrp [] [] [] Ir refl = i-c [] [] Ir

