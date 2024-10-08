{-# OPTIONS --rewriting #-}

module Interpolation where

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

-- =======================================================
-- A proof of Craig interpolation for the sequent calculus
-- =======================================================

{-
Records collecting the data of Craig interpolation.

sIntrp reads:

Given a sequent S ∣ Γ ++ Δ ⊢ C, there exist
  - a formula D
  - derivations g : S ∣ Γ ⊢ D and h : D ∣ Δ ⊢ C

cIntrp reads:

  Given sequent S ∣ Δ₀ ++ Γ ++ Δ₁ ⊢ C there exist
  - a partition Γ = Γ₁,...,Γₙ
  - formulae D₁,...,Dₙ
  - derivations g : S ∣ Δ₀ , D₁ , ... , Dₙ , Δ₁ ⊢ C and hᵢ : ─ ∣  Γᵢ ⊢ Dᵢ for all i≥1
-}

record sIntrp S Γ₁ Γ₂ C : Set where
  constructor i-s
  field
    D : Fma
    g : S ∣ Γ₁ ⊢ D
    h : just D ∣ Γ₂ ⊢ C

record cIntrp S Γ₀ Γ₁ Γ₂ C : Set where
  constructor i-c
  field
    Ds : List Fma
    hs : Ders Γ₁ Ds
    g : S ∣ Γ₀ ++ Ds ++ Γ₂ ⊢ C

-- The interpolation algorithms
sintrp : ∀ {S} Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₁ ++ Γ₂)
  → sIntrp S Γ₁ Γ₂ C
cintrp : ∀{S} Γ₀ Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂)
  → cIntrp S Γ₀ Γ₁ Γ₂ C

sintrp Γ₁ Γ₂ (Il f) refl =
  i-s (sIntrp.D (sintrp Γ₁ Γ₂ f refl))
      (Il (sIntrp.g (sintrp Γ₁ Γ₂ f refl)))
      (sIntrp.h (sintrp Γ₁ Γ₂ f refl))
sintrp Γ₁ Γ₂ (⊗l f) refl =
  i-s (sIntrp.D (sintrp (_ ∷ Γ₁) Γ₂ f refl))
      (⊗l (sIntrp.g (sintrp (_ ∷ Γ₁) Γ₂ f refl)))
      (sIntrp.h (sintrp (_ ∷ Γ₁) Γ₂ f refl))
sintrp Γ₁ Γ₂ (⊸r {A = A}{B} f) refl =
  i-s (sIntrp.D (sintrp Γ₁ (Γ₂ ∷ʳ _) f refl))
      (sIntrp.g (sintrp Γ₁ (Γ₂ ∷ʳ _) f refl))
      (⊸r (sIntrp.h (sintrp Γ₁ (Γ₂ ∷ʳ _) f refl)))
sintrp Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
sintrp {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ ([] , refl , refl) =
  i-s (sIntrp.D (sintrp Γ [] f refl)) (sIntrp.g (sintrp Γ [] f refl)) (⊗r (sIntrp.h (sintrp Γ [] f refl)) g)
sintrp {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (A' ∷ Γ' , refl , refl) = 
  i-s (sIntrp.D (sintrp Γ [] f refl) ⊗ sIntrp.D (sintrp (A' ∷ Γ') Γ₂ g refl))
      (⊗r (sIntrp.g (sintrp Γ [] f refl)) (sIntrp.g (sintrp (A' ∷ Γ') Γ₂ g refl)))
      (⊗l (⊗r (sIntrp.h (sintrp Γ [] f refl)) (pass (sIntrp.h (sintrp (A' ∷ Γ') Γ₂ g refl)))))
sintrp Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) eq | inj₂ (A' , Γ' , refl , refl) with sintrp Γ₁ (_ ∷ Γ') f refl
sintrp Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) | i-s D h k = i-s D h (⊗r k g)
sintrp Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ Γ₁ Δ Γ₂ (sym eq)
sintrp Γ₁ .(Γ' ++ Δ) (⊸l {Δ = Δ} {A}{B}{C} f g) eq | inj₁ (Γ' , refl , refl) with sintrp [] Δ g refl | cintrp Γ₁ Γ' [] f refl
sintrp Γ₁ .(_ ++ Δ) (⊸l {Δ = Δ} f g) refl | inj₁ (_ , refl , refl) | i-s E h k | i-c Ds gs l =
  i-s (Ds ⊸⋆ E) (⊸r⋆ Ds (⊸l l h)) (⊸ls gs k)
sintrp _ Γ₂ (⊸l {Γ} {A = A}{B} f g) eq | inj₂ (A' , Γ' , refl , refl) with sintrp (A' ∷ Γ') Γ₂ g refl
sintrp _ Γ₂ (⊸l {Γ} {A = A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) | i-s D h k = i-s _ (⊸l f h) k
sintrp [] [] ax refl = i-s _ ax ax
sintrp [] (A ∷ Γ₂) (pass f) refl = i-s _ Ir (Il (pass f)) 
sintrp (A ∷ Γ₁) Γ₂ (pass f) refl =
  i-s (sIntrp.D (sintrp Γ₁ Γ₂ f refl))
      (pass (sIntrp.g (sintrp Γ₁ Γ₂ f refl)))
      (sIntrp.h (sintrp Γ₁ Γ₂ f refl))
sintrp [] [] Ir refl = i-s I Ir ax

cintrp Γ₀ Γ₁ Γ₂ (Il f) refl with cintrp Γ₀ Γ₁ Γ₂ f refl
... | i-c Ds gs h = i-c Ds gs (Il h) 
cintrp {S} Γ₀ Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} {A}{B} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
... | inj₁ (Γ₀ , refl , refl) with cintrp Γ₀ Γ₁ Γ₂ g refl
cintrp {S} _ _ Γ₂ (⊗r {Γ = Γ} {A = A} {B} f g) refl | inj₁ (Γ₀ , refl , refl) | i-c Ds gs h =  i-c Ds gs (⊗r f h)
cintrp Γ₀ [] _ (⊗r f g) refl | inj₂ (A , Γ₁ , refl , refl) = i-c [] [] (⊗r f g)
cintrp {S} Γ₀ (A ∷ Γ₁) Γ₂ (⊗r {Δ = Δ} {A₁}{B₁} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
... | inj₂ (A' , Γ₂ , refl , refl) with cintrp Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
cintrp {S} Γ₀ (A ∷ Γ₁) _ (⊗r {Δ = Δ} {A₁} {B₁} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) | i-c Ds gs h = i-c Ds gs (⊗r h g)
cintrp {S} Γ₀ (A ∷ _) Γ₂ (⊗r {A = A₁}{B} f g) eq | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , eq') | inj₁ (Γ₁ , refl , refl) with cintrp Γ₀ (_ ∷ Γ') [] f refl | cintrp [] Γ₁ Γ₂ g refl
cintrp {S} Γ₀ (A ∷ _) Γ₂ (⊗r {A = A₁}{B} f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁@_ , refl , refl) | i-c Ds gs h | i-c Es ls k = 
  i-c (Ds ++ Es) (gs ++s ls) (⊗r h k)
cintrp Γ₀ Γ₁ Γ₂ (⊗l f) refl with cintrp (_ ∷ Γ₀) Γ₁ Γ₂ f refl
... | i-c Ds gs h = i-c Ds gs (⊗l h) 
cintrp {S} Γ₀ Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with cintrp Γ₀ Γ₁ (Γ₂ ∷ʳ _) f refl
... | i-c Ds gs h = i-c Ds gs (⊸r h)
cintrp Γ₀ Γ₁ Γ₂ (⊸l {Γ} {Δ} {A}{B}{C} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
... | inj₁ (Γ₀ , refl , refl) with cintrp Γ₀ Γ₁ Γ₂ g refl
cintrp _ _ Γ₂ (⊸l {Γ} {A = A}{B}{C} f g) refl | inj₁ (Γ₀ , refl , refl) | i-c Ds gs h = i-c Ds gs (⊸l {Γ = Γ} f h)
cintrp Γ₀ [] _ (⊸l f g) refl | inj₂ (B , Γ' , refl , refl) = i-c [] [] (⊸l f g)
cintrp Γ₀ (A ∷ Γ₁) Γ₂ (⊸l {Δ = Δ} {A₁}{B₁}{C} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
... | inj₂ (A' , Γ₂ , refl , refl) with cintrp Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
cintrp Γ₀ (A ∷ Γ₁) _ (⊸l {Δ = Δ} {A₁}{B₁}{C} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) | i-c Ds gs h = i-c Ds gs (⊸l h g)
cintrp Γ₀ (A ∷ _) Γ₂ (⊸l {A = A₁}{B₁}{C} f g) eq | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , eq') | inj₁ (Γ₁ , refl , refl) with cintrp Γ₀ (_ ∷ Γ') [] f refl | cintrp [] Γ₁ Γ₂ g refl
cintrp Γ₀ (A ∷ _) Γ₂ (⊸l {A = A₁}{B₁}{C} f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁@_ , refl , refl) | i-c Ds gs h | i-c Es ls k =
  i-c (Ds ++ Es) (gs ++s ls) (⊸l h k)
cintrp [] [] [] ax refl = i-c [] [] ax
cintrp [] [] Γ₂ (pass f) refl = i-c [] [] (pass f) 
cintrp [] (A ∷ Γ₁) Γ₂ (pass f) refl with sintrp Γ₁ Γ₂ f refl
... | i-s D g k = i-c [ D ] (der (A ∷ Γ₁) D (pass g) []) (pass k)
cintrp (A ∷ Γ₀) Γ₁ Γ₂ (pass f) refl with cintrp Γ₀ Γ₁ Γ₂ f refl
... | i-c Ds gs h = i-c Ds gs (pass h)
cintrp [] [] [] Ir refl = i-c [] [] Ir

module Test (X Y Z W : At) where

{-
  f : just ((` Y ⊗ ` W) ⊸ ` Z) ∣ ` X ⊸ ` Y ∷ ` X ∷ ` W ∷ [] ⊢ ` Z
  f = ⊸l {_ ∷ _ ∷ _ ∷ []} (pass (⊸l {[ _ ]} (pass ax) (⊗r ax (pass ax)))) ax

  sf : sIntrp (just ((` Y ⊗ ` W) ⊸ ` Z)) [ ` X ⊸ ` Y ] (` X ∷ ` W ∷ []) (` Z)
  sf = sintrp [ ` X ⊸ ` Y ] (` X ∷ ` W ∷ []) f refl

  D = ` X ⊸ (` W ⊸ ` Z)

  eq : D ≡ sIntrp.D sf
  eq = refl
-}

{-
f : - | Γ₀ , Γ₁ ⊢ A'
f' : B' | [] ⊢ A
g : - | Γ₂ ⊢ B
⊗r (⊸l f f') g ≗ ⊸l f (⊗r f' g) : A' ⊸ B' | Γ₀ , Γ₁ , Γ₂ ⊢ A ⊗ B
Γ₁ is non-empty
Partition ⟨ Γ₀ , (Γ₁ , Γ₂) ⟩
-}

  module Issue1 where --fixed

    f : ─ ∣ ` X ∷  ` Y ∷ [] ⊢ ` X ⊗ ` Y
    f = pass (⊗r ax (pass ax))
    
    f' : just (` Z) ∣ [] ⊢ ` Z
    f' = ax
  
    g : ─ ∣ ` W ∷ [] ⊢ ` W
    g = pass ax
  
    s : sIntrp _ [ ` X ] (` Y ∷ ` W ∷ []) _
    s = sintrp [ ` X ] (` Y ∷ ` W ∷ []) (⊗r (⊸l f f') g) refl
  
    s' : sIntrp _ [ ` X ] (` Y ∷ ` W ∷ []) _
    s' = sintrp [ ` X ] (` Y ∷ ` W ∷ []) (⊸l f (⊗r f' g)) refl
  
    eqD : sIntrp.D s ≡ ` Y ⊸ ` Z
    eqD = refl
  
    eqD' : sIntrp.D s' ≡ ` Y ⊸ ` Z --(` Z ⊗ I)
    eqD' = refl
  
    eqE : sIntrp.D (sintrp [] (` W ∷ []) (⊗r f' g) refl) ≡ ` Z --` Z ⊗ I
    eqE = refl

  module Issue2 where -- fixed

    f : just (` X) ∣ [] ⊢ ` X
    f = ax

    g : ─ ∣ [ ` Y ]  ⊢ ` Y
    g = pass ax
    
    c : cIntrp _ [] [ ` X ] [ ` Y ] _
    c = cintrp [] [ ` X ] [ ` Y ] (⊗r (pass f) g) refl

    c' : cIntrp _ [] [ ` X ] [ ` Y ] _
    c' = cintrp [] [ ` X ] [ ` Y ] (pass (⊗r f g)) refl

    eqDs : cIntrp.Ds c ≡ [ ` X ]
    eqDs = refl
  
    eqDs' : cIntrp.Ds c' ≡ [ ` X ] --[ ` X ⊗ I ]
    eqDs' = refl


  module Issue3 where

    f : just (` X) ∣ [] ⊢ ` X
    f = ax

    g : ─ ∣ [ ` Y ] ⊢ ` Y
    g = pass ax

    c : cIntrp _ [] (` X ∷ ` Y ∷ []) [] _
    c = cintrp [] (` X ∷ ` Y ∷ []) [] (⊗r (pass f) g) refl

    c' : cIntrp _ [] (` X ∷ ` Y ∷ []) [] _
    c' = cintrp [] (` X ∷ ` Y ∷ []) [] (pass (⊗r f g)) refl

    eqDs : cIntrp.Ds c ≡ ` X ∷  ` Y ∷ []
    eqDs = refl
  
    eqDs' : cIntrp.Ds c' ≡ ` X ⊗ ` Y ∷ []
    eqDs' = refl
