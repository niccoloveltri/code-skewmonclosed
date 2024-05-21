{-# OPTIONS --rewriting #-}

module Interpolation where

open import Function
open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum
open import Data.List as List
open import Data.List.Relation.Unary.All
open import Relation.Unary hiding (_∈_)
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open ≡-Reasoning
open import Utilities
open import Formulae
open import SeqCalc 
open import Equations

-- =======================================================
-- A proof of Craig interpolation for the sequent calculus
-- =======================================================

-- Iterated ⊸l
⊸l⋆ : {Δ Γ : Cxt} {B C : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → just B ∣ Δ ⊢ C
  → Γ ≡ concat (List.map proj₁ Ξ)
  → just (List.map (λ x → proj₁ (proj₂ x)) Ξ ⊸⋆ B) ∣ Γ ++ Δ ⊢ C
⊸l⋆ [] g refl = g
⊸l⋆ ((Γ , A , f) ∷ Ξ) g refl = ⊸l {Γ = Γ} f (⊸l⋆ Ξ g refl)

-- List of atoms in formulae, contexts and stoups
atom : Fma → List At
atom (` X) = List.[ X ]
atom I = []
atom (A ⊗ B) = atom A ++ atom B
atom (A ⊸ B) = atom A ++ atom B

atom-c : Cxt → List At
atom-c Γ = concat (List.map atom Γ)

atom-s : Stp → List At
atom-s (just A) = atom A
atom-s ─ = []

∈atom⊸⋆ : ∀{X} (Γ : Cxt) {C} → X ∈ atom (Γ ⊸⋆ C) → X ∈ atom-c Γ ⊎ X ∈ atom C
∈atom⊸⋆ [] m = inj₂ m
∈atom⊸⋆ (A ∷ Γ) {C} m with ∈++ (atom A) (atom (Γ ⊸⋆ C)) m
... | inj₁ m' = inj₁ (∈₁ (atom A) (atom-c Γ) m')
... | inj₂ m' with ∈atom⊸⋆ Γ m'
... | inj₁ m'' = inj₁ (∈₂ (atom A) (atom-c Γ) m'')
... | inj₂ m'' = inj₂ m''

{-
Records collecting the data of Craig interpolation.

hasIntrp-s reads:

Given f : S ∣ Γ ++ Δ ⊢ C, there exist
- a formula D
- derivations g : S ∣ Γ ⊢ D and h : D ∣ Δ ⊢ C
- a map from occurrences of atoms in D to occurrences of atoms in S,Γ
- a map from occurrences of atoms in D to occurrences of atoms in Δ,C

hasIntrp-c reads:

Given f : S ∣ Δ₀ ++ Γ ++ Δ₁ ⊢ C there exist
- a partition Γ = Γ₁,...,Γₙ
- formulae D₁,...,Dₙ
- derivations g : S ∣ Δ₀ , D₁ , ... , Dₙ , Δ₁ ⊢ C and hᵢ : ─ ∣  Γᵢ ⊢ Dᵢ for all i≥1
- a map from occurrences of atoms in D₁,...,Dₙ to occurrences of atoms in S,Δ₀,Δ₁,C
- a map from occurrences of atoms in D₁,...,Dₙ to occurrences of atoms in Γ₁,...,Γₙ
-}

record hasIntrp-s {S} Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₁ ++ Γ₂) : Set where
  constructor i-s
  field
    D : Fma
    g : S ∣ Γ₁ ⊢ D
    h : just D ∣ Γ₂ ⊢ C
    atom-g : ∀{X} → X ∈ atom D → X ∈ atom-s S ++ atom-c Γ₁
    atom-h : ∀{X} → X ∈ atom D → X ∈ atom-c Γ₂ ++ atom C

record hasIntrp-c {S} Γ₀ Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂) : Set where
  constructor i-c
  field
    Ξ : List (Σ Cxt λ Δ → Σ Fma λ D → ─ ∣ Δ ⊢ D)
    pt : Γ₁ ≡ concat (List.map proj₁ Ξ)
    g : S ∣ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ Γ₂ ⊢ C
    atom-Ξ : ∀{X} → X ∈ atom-c (List.map (λ x → proj₁ (proj₂ x)) Ξ) → X ∈ atom-c (concat (List.map proj₁ Ξ))
    atom-g : ∀{X} → X ∈ atom-c (List.map (λ x → proj₁ (proj₂ x)) Ξ) → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C


-- The proof of Craig interpolation

intrp-s : ∀ {S} Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₁ ++ Γ₂)
  → hasIntrp-s Γ₁ Γ₂ f eq

intrp-c : ∀{S} Γ₀ Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂)
  → hasIntrp-c Γ₀ Γ₁ Γ₂ f eq

intrp-s Γ₁ Γ₂ (Il f) refl with intrp-s Γ₁ Γ₂ f refl
... | i-s D g h a-g a-h = i-s D (Il g) h a-g a-h
intrp-s Γ₁ Γ₂ (⊗l f) refl with intrp-s (_ ∷ Γ₁) Γ₂ f refl
... | i-s D g h a-g a-h = i-s D (⊗l g) h a-g a-h
intrp-s Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with intrp-s Γ₁ (Γ₂ ∷ʳ _) f refl
... | i-s D g h a-g a-h = i-s D g (⊸r h) a-g a-h'
  where
    a-h' : ∀{X} → X ∈ atom D → X ∈ atom-c Γ₂ ++ atom A ++ atom B
    a-h' m with ∈++ (atom-c (Γ₂ ∷ʳ A)) (atom B) (a-h m)
    ... | inj₁ m' = ∈₁ (atom-c Γ₂ ++ atom A) (atom B) (subst (λ x → _ ∈ x) (concat++ (List.map atom Γ₂) List.[ atom A ]) m')
    ... | inj₂ m' = ∈₂ (atom-c Γ₂ ++ atom A) (atom B) m'
intrp-s Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
intrp-s {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (Γ' , refl , refl) with intrp-s Γ [] f refl | intrp-s Γ' Γ₂ g refl
... | i-s D g h a-g a-h | i-s E k l a-k a-l = i-s (D ⊗ E) (⊗r g k) (⊗l (⊗r h (pass l))) a-g' a-h'
  where
    a-g' : ∀{X} → X ∈ atom D ++ atom E → X ∈ atom-s S ++ atom-c (Γ ++ Γ')
    a-g' m with ∈++ (atom D) (atom E) m
    ... | inj₂ m' = ∈₂ (atom-s S) (atom-c (Γ ++ Γ')) (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ) (List.map atom Γ'))) (∈₂ (atom-c Γ) (atom-c Γ') (a-k m')))
    ... | inj₁ m' with ∈++ (atom-s S) (atom-c Γ) (a-g m')
    ... | inj₁ m'' = ∈₁ (atom-s S) (atom-c (Γ ++ Γ')) m''
    ... | inj₂ m'' = ∈₂ (atom-s S) (atom-c (Γ ++ Γ')) (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ) (List.map atom Γ'))) (∈₁ (atom-c Γ) (atom-c Γ') m''))

    a-h' : ∀{X} → X ∈ atom D ++ atom E → X ∈ atom-c Γ₂ ++ atom A ++ atom B
    a-h' m with ∈++ (atom D) (atom E) m
    ... | inj₁ m' = ∈₂ (atom-c Γ₂) (atom A ++ atom B) (∈₁ (atom A) (atom B) (a-h m'))
    ... | inj₂ m' with ∈++ (atom-c Γ₂) (atom B) (a-l m')
    ... | inj₁ m'' = ∈₁ (atom-c Γ₂) (atom A ++ atom B) m''
    ... | inj₂ m'' = ∈₂ (atom-c Γ₂ ++ atom A) (atom B) m''
intrp-s Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) eq | inj₂ (A' , Γ' , refl , refl) with intrp-s Γ₁ (_ ∷ Γ') f refl
... | i-s D h k a-h a-k = i-s D h (⊗r k g) a-h a-k'
  where
    a-k' : ∀{X} → X ∈ atom D → X ∈ atom A' ++ atom-c (Γ' ++ Δ) ++ atom A ++ atom B
    a-k' m with ∈++ (atom A') (atom-c Γ' ++ atom A) (a-k m)
    ... | inj₁ m' = ∈₁ (atom A') (atom-c (Γ' ++ Δ) ++ atom A ++ atom B) m'
    ... | inj₂ m' with ∈++ (atom-c Γ') (atom A) m'
    ... | inj₁ m'' =
      ∈₂ (atom A') (atom-c (Γ' ++ Δ) ++ atom A ++ atom B)
        (∈₁ (atom-c (Γ' ++ Δ)) (atom A ++ atom B)
          (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ') (List.map atom Δ))) (∈₁ (atom-c Γ') (atom-c Δ) m'')))
    ... | inj₂ m'' = ∈₂ (atom A' ++ atom-c (Γ' ++ Δ)) (atom A ++ atom B) (∈₁ (atom A) (atom B) m'')
intrp-s Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
intrp-s _ Γ₂ (⊸l {Γ} {A = A}{B} f g) eq | inj₁ (Γ' , refl , refl) with intrp-s Γ' Γ₂ g refl
... | i-s D h k a-h a-k = i-s _ (⊸l f h) k a-h' a-k
  where
    a-h' : ∀{X} → X ∈ atom D → X ∈ atom A ++ atom B ++ atom-c (Γ ++ Γ')
    a-h' m with ∈++ (atom B) (atom-c Γ') (a-h m)
    ... | inj₁ m' = ∈₁ (atom A ++ atom B) (atom-c (Γ ++ Γ')) (∈₂ (atom A) (atom B) m')
    ... | inj₂ m' = ∈₂ (atom A ++ atom B) (atom-c (Γ ++ Γ')) (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ) (List.map atom Γ'))) (∈₂ (atom-c Γ) (atom-c Γ') m'))
intrp-s Γ₁ _ (⊸l {Δ = Δ} {A = A}{B}{C} f g) eq | inj₂ (A' , Γ' , refl , refl) with intrp-s [] Δ g refl | intrp-c Γ₁ (A' ∷ Γ') [] f refl
... | i-s E h k a-h a-k | i-c Ξ eq' l a-Ξ a-l = 
  i-s (Ds ⊸⋆ E) (⊸r⋆ Ds (⊸l l h)) (⊸l⋆ Ξ k eq') a-h' a-k'
  where
    Ds = List.map (λ x → proj₁ (proj₂ x)) Ξ

    a-h' : ∀{X} → X ∈ atom (Ds ⊸⋆ E) → X ∈ atom A ++ atom B ++ atom-c Γ₁
    a-h' m with ∈atom⊸⋆ Ds m
    ... | inj₂ m' = ∈₁ (atom A ++ atom B) (atom-c Γ₁) (∈₂ (atom A) (atom B) (a-h m'))
    ... | inj₁ m' with ∈++ (atom-c Γ₁) (atom A) (a-l m')
    ... | inj₁ m'' = ∈₂ (atom A ++ atom B) (atom-c Γ₁) m''
    ... | inj₂ m'' = ∈₁ (atom A) (atom B ++ atom-c Γ₁) m''

    a-k' : ∀{X} → X ∈ atom (Ds ⊸⋆ E) → X ∈ atom A' ++ atom-c (Γ' ++ Δ) ++ atom C
    a-k' m with ∈atom⊸⋆ Ds m
    ... | inj₂ m' =
      ∈₂ (atom A') (atom-c (Γ' ++ Δ) ++ atom C)
        (subst (λ x → _ ∈ x ++ atom C) (sym (concat++ (List.map atom Γ') (List.map atom Δ)))
          (∈₂ (atom-c Γ') (atom-c Δ ++ atom C) (a-k m')))
    ... | inj₁ m' =
      ∈₁ (atom A' ++ atom-c (Γ' ++ Δ)) (atom C)
        (subst (λ x → _ ∈ atom A' ++ x) (sym (concat++ (List.map atom Γ') (List.map atom Δ)))
          (∈₁ (atom A' ++ atom-c Γ') (atom-c Δ) (subst (λ x → _ ∈ atom-c x) (sym eq') (a-Ξ m'))))
intrp-s [] [] ax refl = i-s _ ax ax id id
intrp-s [] (A ∷ Γ₂) (pass f) refl = i-s _ Ir (Il (pass f)) (λ ()) λ ()
intrp-s (A ∷ Γ₁) Γ₂ (pass f) refl with intrp-s Γ₁ Γ₂ f refl
... | i-s D g h a-g a-h = i-s D (pass g) h a-g a-h
intrp-s [] [] Ir refl = i-s I Ir ax (λ ()) id

intrp-c [] [] [] ax refl = i-c [] refl ax id (λ ())
intrp-c [] [] Γ₂ (pass f) refl = i-c [] refl (pass f) (λ ()) (λ ())
intrp-c [] (A ∷ Γ₁) Γ₂ (pass f) refl with intrp-s Γ₁ Γ₂ f refl
... | i-s D g k a-g a-k = i-c List.[ (A ∷ Γ₁ , _ , pass g) ] refl (pass k) a-g a-k
intrp-c (A ∷ Γ₀) Γ₁ Γ₂ (pass f) refl with intrp-c Γ₀ Γ₁ Γ₂ f refl
... | i-c Ξ eq h a-Ξ a-h = i-c Ξ eq (pass h) a-Ξ a-h
intrp-c [] [] [] Ir refl = i-c [] refl Ir (λ ()) id
intrp-c Γ₀ Γ₁ Γ₂ (Il f) refl with intrp-c Γ₀ Γ₁ Γ₂ f refl
... | i-c Ξ eq h a-Ξ a-h = i-c Ξ eq (Il h) a-Ξ a-h
intrp-c {S} Γ₀ Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} {A}{B} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
... | inj₁ (Γ₀ , refl , refl) with intrp-c Γ₀ Γ₁ Γ₂ g refl
... | i-c Ξ eq' h a-Ξ a-h = i-c Ξ eq' (⊗r f h) a-Ξ a-h'
  where
    Ds = List.map (λ x → proj₁ (proj₂ x)) Ξ
    
    a-h' : ∀{X} → X ∈ atom-c Ds → X ∈ atom-s S ++ atom-c (Γ ++ Γ₀) ++ atom-c Γ₂ ++ atom A ++ atom B
    a-h' m with ∈++ (atom-c Γ₀) (atom-c Γ₂ ++ atom B) (a-h m)
    ... | inj₁ m' =
      ∈₁ (atom-s S ++ atom-c (Γ ++ Γ₀)) (atom-c Γ₂ ++ atom A ++ atom B)
        (∈₂ (atom-s S) (atom-c (Γ ++ Γ₀)) (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ) (List.map atom Γ₀))) (∈₂ (atom-c Γ) (atom-c Γ₀) m')))
    ... | inj₂ m' with ∈++ (atom-c Γ₂) (atom B) m'
    ... | inj₁ m'' = ∈₂ (atom-s S ++ atom-c (Γ ++ Γ₀)) (atom-c Γ₂ ++ atom A ++ atom B) (∈₁  (atom-c Γ₂) (atom A ++ atom B) m'')
    ... | inj₂ m'' = ∈₂ (atom-s S ++ atom-c (Γ ++ Γ₀) ++ atom-c Γ₂ ++ atom A) (atom B) m''
    
intrp-c Γ₀ [] _ (⊗r f g) eq | inj₂ (A , Γ₁ , refl , refl) = i-c [] refl (⊗r f g) (λ ()) (λ ())
intrp-c {S} Γ₀ (A ∷ Γ₁) Γ₂ (⊗r {Δ = Δ} {A₁}{B₁} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
... | inj₂ (A' , Γ₂ , refl , refl) with intrp-c Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
... | i-c Ξ eq'' h a-Ξ a-h = i-c Ξ eq'' (⊗r h g) a-Ξ (a-h' ∘ a-h)
  where
    a-h' : ∀{X}
      → X ∈ atom-s S ++ atom-c Γ₀ ++ atom A' ++ atom-c Γ₂ ++ atom A₁
      → X ∈ atom-s S ++ atom-c Γ₀ ++ atom A' ++ atom-c (Γ₂ ++ Δ) ++ atom A₁ ++ atom B₁
    a-h' m with ∈++ (atom-s S ++ atom-c Γ₀ ++ atom A' ++ atom-c Γ₂) (atom A₁) m
    ... | inj₁ m' =
      ∈₁ (atom-s S ++ atom-c Γ₀ ++ atom A' ++ atom-c (Γ₂ ++ Δ)) (atom A₁ ++ atom B₁)
        (subst (λ x → _ ∈ atom-s S ++ atom-c Γ₀ ++ atom A' ++ x) (sym (concat++ (List.map atom Γ₂) (List.map atom Δ)))
          (∈₁ (atom-s S ++ atom-c Γ₀ ++ atom A' ++ atom-c Γ₂) (atom-c Δ) m'))
    ... | inj₂ m' = ∈₂ (atom-s S ++ atom-c Γ₀ ++ atom A' ++ atom-c (Γ₂ ++ Δ)) (atom A₁ ++ atom B₁) (∈₁ (atom A₁) (atom B₁) m')
         
intrp-c {S} Γ₀ (A ∷ _) Γ₂ (⊗r {A = A₁}{B} f g) eq | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , eq') | inj₁ (Γ₁ , refl , refl) with intrp-c Γ₀ (_ ∷ Γ') [] f refl | intrp-c [] Γ₁ Γ₂ g refl
... | i-c Ξf eqf h a-Ξf a-h | i-c Ξg eqg k a-Ξg a-k =
  i-c (Ξf ++ Ξg)
      (trans (cong₂ _++_ {x = _ ∷ Γ'} eqf eqg) (sym (concat++ (List.map proj₁ Ξf) (List.map proj₁ Ξg))))
      (⊗r h k)
      a-Ξ
      a-h'
  where
    Δs = List.map proj₁ Ξf
    Λs = List.map proj₁ Ξg
    Ds = List.map (λ x → proj₁ (proj₂ x)) Ξf
    Es = List.map (λ x → proj₁ (proj₂ x)) Ξg

    a-Ξ : ∀{X} → X ∈ atom-c (Ds ++ Es) → X ∈ atom-c (concat (Δs ++ Λs))
    a-Ξ m with ∈++ (atom-c Ds) (atom-c Es) (subst (λ x → _ ∈ x) (concat++ (List.map atom Ds) (List.map atom Es)) m)
    ... | inj₁ m' =
      subst (λ x → _ ∈ atom-c x) (sym (concat++ Δs Λs))
        (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom (concat Δs)) (List.map atom (concat Λs))))
          (∈₁ (atom-c (concat Δs)) (atom-c (concat Λs)) (a-Ξf m')))
    ... | inj₂ m' = 
      subst (λ x → _ ∈ atom-c x) (sym (concat++ Δs Λs))
        (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom (concat Δs)) (List.map atom (concat Λs))))
          (∈₂ (atom-c (concat Δs)) (atom-c (concat Λs)) (a-Ξg m')))

    a-h' : ∀{X} → X ∈ atom-c (Ds ++ Es) → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom A₁ ++ atom B
    a-h' m with ∈++ (atom-c Ds) (atom-c Es) (subst (λ x → _ ∈ x) (concat++ (List.map atom Ds) (List.map atom Es)) m)
    a-h' m | inj₂ m' with ∈++ (atom-c Γ₂) (atom B) (a-k m')
    ... | inj₁ m'' = ∈₁ (atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂) (atom A₁ ++ atom B) (∈₂ (atom-s S ++ atom-c Γ₀) (atom-c Γ₂) m'')
    ... | inj₂ m'' = ∈₂ (atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom A₁) (atom B) m''
    a-h' m | inj₁ m' with ∈++ (atom-s S ++ atom-c Γ₀) (atom A₁) (a-h m')
    ... | inj₁ m'' = ∈₁ (atom-s S ++ atom-c Γ₀) (atom-c Γ₂ ++ atom A₁ ++ atom B) m''
    ... | inj₂ m'' = ∈₂ (atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂) (atom A₁ ++ atom B) (∈₁ (atom A₁) (atom B) m'')

intrp-c Γ₀ Γ₁ Γ₂ (⊗l f) refl with intrp-c (_ ∷ Γ₀) Γ₁ Γ₂ f refl
... | i-c Ξ eq h a-Ξ a-h = i-c Ξ eq (⊗l h) a-Ξ a-h
intrp-c {S} Γ₀ Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with intrp-c Γ₀ Γ₁ (Γ₂ ∷ʳ _) f refl
... | i-c Ξ eq h a-Ξ a-h = i-c Ξ eq (⊸r h) a-Ξ (a-h' ∘ a-h)
  where
    a-h' : ∀{X}
      → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c (Γ₂ ∷ʳ A) ++ atom B
      → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom A ++ atom B
    a-h' m = subst (λ x → _ ∈ atom-s S ++ atom-c Γ₀ ++ x ++ atom B) (concat++ (List.map atom Γ₂) List.[ atom A ]) m
intrp-c Γ₀ Γ₁ Γ₂ (⊸l {Γ} {Δ} {A}{B}{C} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
... | inj₁ (Γ₀ , refl , refl) with intrp-c Γ₀ Γ₁ Γ₂ g refl
... | i-c Ξ eq' h a-Ξ a-h = i-c Ξ eq' (⊸l {Γ = Γ} f h) a-Ξ (a-h' ∘ a-h)
  where
    a-h' : ∀{X}
      → X ∈ atom B ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C
      → X ∈ atom A ++ atom B ++ atom-c (Γ ++ Γ₀) ++ atom-c Γ₂ ++ atom C
    a-h' m with ∈++ (atom B) (atom-c Γ₀ ++ atom-c Γ₂ ++ atom C) m
    ... | inj₁ m' = ∈₁ (atom A ++ atom B) (atom-c (Γ ++ Γ₀) ++ atom-c Γ₂ ++ atom C) (∈₂ (atom A) (atom B) m')
    ... | inj₂ m' =
      ∈₂ (atom A ++ atom B) (atom-c (Γ ++ Γ₀) ++ atom-c Γ₂ ++ atom C)
        (subst (λ x → _ ∈ x ++ atom-c Γ₂ ++ atom C) (sym (concat++ (List.map atom Γ) (List.map atom Γ₀)))
          (∈₂ (atom-c Γ) (atom-c Γ₀ ++ atom-c Γ₂ ++ atom C) m') )
intrp-c Γ₀ [] _ (⊸l f g) eq | inj₂ (B , Γ' , refl , refl) = i-c [] refl (⊸l f g) (λ ()) (λ ())
intrp-c Γ₀ (A ∷ Γ₁) Γ₂ (⊸l {Δ = Δ} {A₁}{B₁}{C} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
... | inj₂ (A' , Γ₂ , refl , refl) with intrp-c Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
... | i-c Ξ eq'' h a-Ξ a-h = i-c Ξ eq'' (⊸l h g) a-Ξ (a-h' ∘ a-h)
  where
    a-h' : ∀{X}
      → X ∈ atom-c Γ₀ ++ atom A' ++ atom-c Γ₂ ++ atom A₁
      → X ∈ atom A₁ ++ atom B₁ ++ atom-c Γ₀ ++ atom A' ++ atom-c (Γ₂ ++ Δ) ++ atom C
    a-h' m with ∈++ (atom-c Γ₀ ++ atom A' ++ atom-c Γ₂) (atom A₁) m
    ... | inj₁ m' =
      subst (λ x → _ ∈ atom A₁ ++ atom B₁ ++ atom-c Γ₀ ++ atom A' ++ x ++ atom C) (sym (concat++ (List.map atom Γ₂) (List.map atom Δ)))
        (∈₁ (atom A₁ ++ atom B₁ ++ atom-c Γ₀ ++ atom A' ++ atom-c Γ₂) (atom-c Δ ++ atom C)
          (∈₂ (atom A₁ ++ atom B₁) (atom-c Γ₀ ++ atom A' ++ atom-c Γ₂) m'))
    ... | inj₂ m' = ∈₁ (atom A₁) (atom B₁ ++ atom-c Γ₀ ++ atom A' ++ atom-c (Γ₂ ++ Δ) ++ atom C) m'
intrp-c Γ₀ (A ∷ _) Γ₂ (⊸l {A = A₁}{B₁}{C} f g) eq | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , eq') | inj₁ (Γ₁ , refl , refl) with intrp-c Γ₀ (_ ∷ Γ') [] f refl | intrp-c [] Γ₁ Γ₂ g refl
... | i-c Ξf eqf h a-Ξf a-h | i-c Ξg eqg k a-Ξg a-k =
  i-c (Ξf ++ Ξg)
      (trans (cong₂ _++_ {x = _ ∷ Γ'} eqf eqg) (sym (concat++ (List.map proj₁ Ξf) (List.map proj₁ Ξg))))
      (⊸l h k)
      a-Ξ
      a-h'
  where
    Δs = List.map proj₁ Ξf
    Λs = List.map proj₁ Ξg
    Ds = List.map (λ x → proj₁ (proj₂ x)) Ξf
    Es = List.map (λ x → proj₁ (proj₂ x)) Ξg

    a-Ξ : ∀{X} → X ∈ atom-c (Ds ++ Es) → X ∈ atom-c (concat (Δs ++ Λs))
    a-Ξ m with ∈++ (atom-c Ds) (atom-c Es) (subst (λ x → _ ∈ x) (concat++ (List.map atom Ds) (List.map atom Es)) m)
    ... | inj₁ m' =
      subst (λ x → _ ∈ atom-c x) (sym (concat++ Δs Λs))
        (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom (concat Δs)) (List.map atom (concat Λs))))
          (∈₁ (atom-c (concat Δs)) (atom-c (concat Λs)) (a-Ξf m')))
    ... | inj₂ m' = 
      subst (λ x → _ ∈ atom-c x) (sym (concat++ Δs Λs))
        (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom (concat Δs)) (List.map atom (concat Λs))))
          (∈₂ (atom-c (concat Δs)) (atom-c (concat Λs)) (a-Ξg m')))

    a-h' : ∀{X} → X ∈ atom-c (Ds ++ Es) → X ∈ atom A₁ ++ atom B₁ ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C
    a-h' m with ∈++ (atom-c Ds) (atom-c Es) (subst (λ x → _ ∈ x) (concat++ (List.map atom Ds) (List.map atom Es)) m)
    a-h' m | inj₂ m' with ∈++ (atom B₁) (atom-c Γ₂ ++ atom C) (a-k m')
    ... | inj₁ m'' = ∈₁ (atom A₁ ++ atom B₁) (atom-c Γ₀ ++ atom-c Γ₂ ++ atom C) (∈₂ (atom A₁) (atom B₁) m'') 
    ... | inj₂ m'' = ∈₂ (atom A₁ ++ atom B₁ ++ atom-c Γ₀) (atom-c Γ₂ ++ atom C) m''
    a-h' m | inj₁ m'  with ∈++ (atom-c Γ₀) (atom A₁) (a-h m')
    ... | inj₁ m'' = ∈₁ (atom A₁ ++ atom B₁ ++ atom-c Γ₀) (atom-c Γ₂ ++ atom C) (∈₂ (atom A₁ ++ atom B₁) (atom-c Γ₀) m'')
    ... | inj₂ m'' = ∈₁ (atom A₁) (atom B₁ ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C) m''

---

-- Examples

module Ex {X Y Z W V : At} where

  f : just ((` X ⊗ ` Y) ⊸ ` Z) ∣ ` W ⊸ ` X  ∷ ` W ∷ ` Y ∷ [] ⊢ ` Z
  f = ⊸l (pass (⊸l (pass ax) (⊗r ax (pass ax)))) ax

  intrp-f : hasIntrp-s List.[ ` W ⊸ ` X ] (` W ∷ ` Y ∷ []) f refl
  intrp-f = intrp-s List.[ ` W ⊸ ` X ] (` W ∷ ` Y ∷ []) f refl

  D = hasIntrp-s.D intrp-f
  D-eq : D ≡ ` W ⊸ (` Y ⊸ ` Z)
  D-eq = refl


  f' : just ((` X ⊗ ` Y) ⊸ ` Z) ∣ [] ⊢ ` X ⊸ (` Y ⊸ ` Z)
  f' = ⊸r (⊸r (⊸l (pass (⊗r ax (pass ax))) ax))

  intrp-f' : hasIntrp-s [] [] f' refl
  intrp-f' = intrp-s [] [] f' refl

  intrp-f'-alt : hasIntrp-s [] [] f' refl
  intrp-f'-alt =
    i-s (` X ⊸ (` Y ⊸ ` Z))
        f'
        ax
        id
        id

  non-uniq : intrp-f'-alt ≡ intrp-f' → ⊥
  non-uniq eq with cong hasIntrp-s.D eq
  ... | ()
  


---


ccut⋆ : ∀{S : Stp} Γ₀ Γ₁ {Γ : Cxt} {C : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : S ∣ Γ ⊢ C)
  → (eq : Γ ≡ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ Γ₁)
  → S ∣ Γ₀ ++ concat (List.map proj₁ Ξ) ++ Γ₁ ⊢ C
ccut⋆ Γ₀ _ [] f eq = subst-cxt eq f
ccut⋆ Γ₀ Γ₁ ((Δ , A , g) ∷ Ξ) f refl = ccut Γ₀ g (ccut⋆ (Γ₀ ∷ʳ _) Γ₁ Ξ f refl) refl

scut⊸r⋆⊸l⋆ : {S : Stp} {Γ Δ Λ : Cxt} {B C : Fma}
  → (Ξ : List (Σ Cxt λ Δ → Σ Fma λ A → ─ ∣ Δ ⊢ A))
  → (f : S ∣ Γ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ⊢ B)
  → (g : just B ∣ Δ ⊢ C)
  → (eq : Λ ≡ concat (List.map proj₁ Ξ))
  → scut (⊸r⋆ (List.map (λ x → proj₁ (proj₂ x)) Ξ) f) (⊸l⋆ Ξ g eq)
         ≗ subst-cxt (cong (λ x → Γ ++ x ++ Δ) (sym eq)) (scut (ccut⋆ Γ [] Ξ f refl) g)

scut-intrp-s : ∀ {S} Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₁ ++ Γ₂)
  → scut (hasIntrp-s.g (intrp-s Γ₁ Γ₂ f eq)) (hasIntrp-s.h (intrp-s Γ₁ Γ₂ f eq)) ≗ subst-cxt eq f

scut-intrp-s Γ₁ Γ₂ (Il f) refl = Il (scut-intrp-s Γ₁ Γ₂ f refl)
scut-intrp-s Γ₁ Γ₂ (⊗l f) refl = ⊗l (scut-intrp-s (_ ∷ Γ₁) Γ₂ f refl)
scut-intrp-s Γ₁ Γ₂ (⊸r {A = A}{B} f) refl =
  scut⊸r (hasIntrp-s.g (intrp-s Γ₁ (Γ₂ ++ A ∷ []) f refl)) _
  ∙ ⊸r (scut-intrp-s Γ₁ (Γ₂ ∷ʳ _) f refl)
scut-intrp-s Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
scut-intrp-s {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (Γ' , refl , refl) =
  scut⊗r (hasIntrp-s.g (intrp-s Γ [] f refl)) _ _
  ∙ ⊗r (scut-intrp-s Γ [] f refl) (scut-intrp-s Γ' Γ₂ g refl)
scut-intrp-s Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) =
  scut⊗r (hasIntrp-s.g (intrp-s Γ₁ (A' ∷ Γ') f refl)) _ _
  ∙ ⊗r {Γ = Γ₁ ++ A' ∷ Γ'} (scut-intrp-s Γ₁ (A' ∷ Γ') f refl) refl
scut-intrp-s Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
scut-intrp-s _ Γ₂ (⊸l {Γ} {A = A}{B} f g) refl | inj₁ (Γ' , refl , refl) =
  ⊸l refl (scut-intrp-s Γ' Γ₂ g refl)
scut-intrp-s Γ₁ _ (⊸l {Δ = Δ} {A = A}{B}{C} f g) refl | inj₂ (A' , Γ' , refl , refl) =
  lem
  where
    Ξ = hasIntrp-c.Ξ (intrp-c Γ₁ (A' ∷ Γ') [] f refl)
    Δs = List.map proj₁ Ξ
    As = List.map (λ x → proj₁ (proj₂ x)) Ξ

    eq : A' ∷ Γ' ≡ concat Δs
    eq = hasIntrp-c.pt (intrp-c Γ₁ (A' ∷ Γ') [] f refl)

    f' : ─ ∣ Γ₁ ++ As ⊢ A
    f' = hasIntrp-c.g (intrp-c Γ₁ (A' ∷ Γ') [] f refl)
    
    E = hasIntrp-s.D (intrp-s [] Δ g refl)

    g' : just B ∣ [] ⊢ E
    g' = hasIntrp-s.g (intrp-s [] Δ g refl)

    g'' : just E ∣ Δ ⊢ C
    g'' = hasIntrp-s.h (intrp-s [] Δ g refl)

    lem : scut (⊸r⋆ As (⊸l f' g')) (⊸l⋆ Ξ g'' eq) ≗ ⊸l f g
    lem =
      scut⊸r⋆⊸l⋆ Ξ (⊸l f' g') g'' eq
      ∙ {!!}

scut-intrp-s [] [] ax refl = refl
scut-intrp-s [] (A ∷ Γ₂) (pass f) refl = refl
scut-intrp-s (A ∷ Γ₁) Γ₂ (pass f) refl = pass (scut-intrp-s Γ₁ Γ₂ f refl)
scut-intrp-s [] [] Ir refl = refl

