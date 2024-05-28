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
open import Relation.Binary.PropositionalEquality as PE hiding (_≗_) hiding ([_])
open ≡-Reasoning
open import Utilities
open import Formulae
open import SeqCalc 
open import Equations

-- =======================================================
-- A proof of Craig interpolation for the sequent calculus
-- =======================================================

-- List of atoms in formulae, contexts and stoups
atom : Fma → List At
atom (` X) = [ X ]
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

sIntrp reads:

Given a sequent S ∣ Γ ++ Δ ⊢ C, there exist
- a formula D
- derivations g : S ∣ Γ ⊢ D and h : D ∣ Δ ⊢ C

sVar collects variable conditions:
- a map from occurrences of atoms in D to occurrences of atoms in S,Γ
- a map from occurrences of atoms in D to occurrences of atoms in Δ,C

cIntrp reads:

Given sequent S ∣ Δ₀ ++ Γ ++ Δ₁ ⊢ C there exist
- a partition Γ = Γ₁,...,Γₙ
- formulae D₁,...,Dₙ
- derivations g : S ∣ Δ₀ , D₁ , ... , Dₙ , Δ₁ ⊢ C and hᵢ : ─ ∣  Γᵢ ⊢ Dᵢ for all i≥1

cVar collects variable conditions"
- a map from occurrences of atoms in D₁,...,Dₙ to occurrences of atoms in S,Δ₀,Δ₁,C
- a map from occurrences of atoms in D₁,...,Dₙ to occurrences of atoms in Γ₁,...,Γₙ
-}

record sIntrp S Γ₁ Γ₂ C : Set where
  constructor i-s
  field
    D : Fma
    g : S ∣ Γ₁ ⊢ D
    h : just D ∣ Γ₂ ⊢ C

record sVar S Γ₁ Γ₂ C D : Set where
  constructor v-s
  field
    atom-g : ∀{X} → X ∈ atom D → X ∈ atom-s S ++ atom-c Γ₁
    atom-h : ∀{X} → X ∈ atom D → X ∈ atom-c Γ₂ ++ atom C

record cIntrp S Γ₀ Γ₁ Γ₂ C : Set where
  constructor i-c
  field
    Ξ : List (Σ Cxt λ Δ → Σ Fma λ D → ─ ∣ Δ ⊢ D)
    pt : Γ₁ ≡ concat (List.map proj₁ Ξ)
    g : S ∣ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ Γ₂ ⊢ C

  Δs = List.map proj₁ Ξ
  Ds = List.map (λ x → proj₁ (proj₂ x)) Ξ

record cVar S Γ₀ Γ₁ Γ₂ C Ds : Set where
  constructor v-c
  field
    atom-Ξ : ∀{X} → X ∈ atom-c Ds → X ∈ atom-c Γ₁
    atom-g : ∀{X} → X ∈ atom-c Ds → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C



-- The proof of Craig interpolation

sintrp-thm : ∀ {S} Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₁ ++ Γ₂)
  → Σ (sIntrp S Γ₁ Γ₂ C)
     λ p → sVar S Γ₁ Γ₂ C (sIntrp.D p)
         × scut (sIntrp.g p) (sIntrp.h p) ≗ subst-cxt eq f

cintrp-thm : ∀{S} Γ₀ Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂)
  → Σ (cIntrp S Γ₀ Γ₁ Γ₂ C)
     λ p → cVar S Γ₀ Γ₁ Γ₂ C (cIntrp.Ds p)
         × ccut⋆ Γ₀ Γ₂ (cIntrp.Ξ p) (cIntrp.g p) refl ≗ subst-cxt (trans eq (cong (λ x → Γ₀ ++ x ++ Γ₂) (cIntrp.pt p))) f


sintrp-thm Γ₁ Γ₂ (Il f) refl with sintrp-thm Γ₁ Γ₂ f refl
... | i-s D g h , v-s a-g a-h , eq =
  i-s D (Il g) h ,
  v-s a-g a-h ,
  Il eq
sintrp-thm Γ₁ Γ₂ (⊗l f) refl with sintrp-thm (_ ∷ Γ₁) Γ₂ f refl
... | i-s D g h , v-s a-g a-h , eq =
  i-s D (⊗l g) h ,
  v-s a-g a-h ,
  ⊗l eq
sintrp-thm Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with sintrp-thm Γ₁ (Γ₂ ∷ʳ _) f refl
... | i-s D g h , v-s a-g a-h , eq =
  i-s D g (⊸r h) ,
  v-s a-g a-h' ,
  scut⊸r g h ∙ ⊸r eq
  where
    a-h' : ∀{X} → X ∈ atom D → X ∈ atom-c Γ₂ ++ atom A ++ atom B
    a-h' m with ∈++ (atom-c (Γ₂ ∷ʳ A)) (atom B) (a-h m)
    ... | inj₁ m' = ∈₁ (atom-c Γ₂ ++ atom A) (atom B) (subst (λ x → _ ∈ x) (concat++ (List.map atom Γ₂) [ atom A ]) m')
    ... | inj₂ m' = ∈₂ (atom-c Γ₂ ++ atom A) (atom B) m'
sintrp-thm Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
sintrp-thm {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (Γ' , refl , refl) with sintrp-thm Γ [] f refl | sintrp-thm Γ' Γ₂ g refl
... | i-s D g h , v-s a-g a-h , eq | i-s E k l , v-s a-k a-l , eq' =
  i-s (D ⊗ E) (⊗r g k) (⊗l (⊗r h (pass l))) ,
  v-s a-g' a-h' ,
  scut⊗r g h (scut k l) ∙ ⊗r eq eq' 
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
sintrp-thm Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) eq | inj₂ (A' , Γ' , refl , refl) with sintrp-thm Γ₁ (_ ∷ Γ') f refl
sintrp-thm Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) | i-s D h k , v-s a-h a-k , eq = 
  i-s D h (⊗r k g) ,
  v-s a-h a-k' ,
  scut⊗r h k g ∙ ⊗r eq refl
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
sintrp-thm Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ Γ₁ Δ Γ₂ (sym eq)
sintrp-thm Γ₁ .(Γ' ++ Δ) (⊸l {Δ = Δ} {A}{B}{C} f g) eq | inj₁ (Γ' , refl , refl) with sintrp-thm [] Δ g refl | cintrp-thm Γ₁ Γ' [] f refl
sintrp-thm Γ₁ _ (⊸l {Δ = Δ} {A}{B}{C} f g) refl | inj₁ (Γ'@_ , refl , refl) | i-s E h k , v-s a-h a-k , eq | i-c Ξ refl l , v-c a-Ξ a-l , eq' = 
  i-s (Ds ⊸⋆ E) (⊸r⋆ Ds (⊸l l h)) (⊸l⋆ Ξ k) ,
  v-s a-h' a-k' ,
  ≡-to-≗ (scut⊸r⋆⊸l⋆ Ξ (⊸l l h) k)
  ∙ cong-scut1 {Γ = Γ₁ ++ concat Δs} (≡-to-≗ (ccut⋆⊸l1 Γ₁ [] Ξ l h) ∙ ⊸l eq' refl) k
  ∙ ⊸l refl eq
  where
    Δs = List.map proj₁ Ξ
    Ds = List.map (λ x → proj₁ (proj₂ x)) Ξ

    a-h' : ∀{X} → X ∈ atom (Ds ⊸⋆ E) → X ∈ atom A ++ atom B ++ atom-c Γ₁
    a-h' m with ∈atom⊸⋆ Ds m
    ... | inj₂ m' = ∈₁ (atom A ++ atom B) (atom-c Γ₁) (∈₂ (atom A) (atom B) (a-h m'))
    ... | inj₁ m' with ∈++ (atom-c Γ₁) (atom A) (a-l m')
    ... | inj₁ m'' = ∈₂ (atom A ++ atom B) (atom-c Γ₁) m''
    ... | inj₂ m'' = ∈₁ (atom A) (atom B ++ atom-c Γ₁) m''

    a-k' : ∀{X} → X ∈ atom (Ds ⊸⋆ E) → X ∈ atom-c (Γ' ++ Δ) ++ atom C
    a-k' m with ∈atom⊸⋆ Ds m
    ... | inj₂ m' =
        subst (λ x → _ ∈ x ++ atom C) (sym (concat++ (List.map atom Γ') (List.map atom Δ)))
           (∈₂ (atom-c Γ') (atom-c Δ ++ atom C) (a-k m'))
    ... | inj₁ m' = 
      ∈₁ (atom-c (Γ' ++ Δ)) (atom C)
        (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ') (List.map atom Δ)))
          (∈₁ (atom-c Γ') (atom-c Δ) (a-Ξ m')))
sintrp-thm _ Γ₂ (⊸l {Γ} {A = A}{B} f g) eq | inj₂ (A' , Γ' , refl , refl) with sintrp-thm (A' ∷ Γ') Γ₂ g refl
sintrp-thm _ Γ₂ (⊸l {Γ} {A = A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) | i-s D h k , v-s a-h a-k , eq =
  i-s _ (⊸l f h) k ,
  v-s a-h' a-k ,
  ⊸l refl eq
  where
    a-h' : ∀{X} → X ∈ atom D → X ∈ atom A ++ atom B ++ atom-c (Γ ++ A' ∷ Γ')
    a-h' m with ∈++ (atom B) (atom-c (A' ∷ Γ')) (a-h m)
    ... | inj₁ m' = ∈₁ (atom A ++ atom B) (atom-c (Γ ++ A' ∷ Γ')) (∈₂ (atom A) (atom B) m')
    ... | inj₂ m' =
      ∈₂ (atom A ++ atom B) (atom-c (Γ ++ A' ∷ Γ'))
        (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ) (List.map atom (A' ∷ Γ')))) (∈₂ (atom-c Γ) (atom-c (A' ∷ Γ')) m'))

sintrp-thm [] [] ax refl = i-s _ ax ax , v-s id id , refl
sintrp-thm [] (A ∷ Γ₂) (pass f) refl = i-s _ Ir (Il (pass f)) , v-s (λ ()) (λ ()) , refl
sintrp-thm (A ∷ Γ₁) Γ₂ (pass f) refl with sintrp-thm Γ₁ Γ₂ f refl
... | i-s D g h , v-s a-g a-h , eq = i-s D (pass g) h , v-s a-g a-h , pass eq
sintrp-thm [] [] Ir refl = i-s I Ir ax , v-s (λ ()) id , refl

cintrp-thm [] [] [] ax refl = i-c [] refl ax , v-c id (λ ()) , refl
cintrp-thm [] [] Γ₂ (pass f) refl = i-c [] refl (pass f) , v-c (λ ()) (λ ()) , refl
cintrp-thm [] (A ∷ Γ₁) Γ₂ (pass f) refl with sintrp-thm Γ₁ Γ₂ f refl
... | i-s D g k , v-s a-g a-k , eq =
  i-c [ (A ∷ Γ₁ , _ , pass g) ] refl (pass k) ,
  v-c a-g a-k ,
  pass eq
cintrp-thm (A ∷ Γ₀) Γ₁ Γ₂ (pass f) refl with cintrp-thm Γ₀ Γ₁ Γ₂ f refl
... | i-c Ξ refl h , v-c a-Ξ a-h , eq =
  i-c Ξ refl (pass h) ,
  v-c a-Ξ a-h ,
  ≡-to-≗ (ccut⋆pass Γ₀ Γ₂ Ξ h)
  ∙ pass eq
cintrp-thm [] [] [] Ir refl = i-c [] refl Ir , v-c (λ ()) id , refl
cintrp-thm Γ₀ Γ₁ Γ₂ (Il f) refl with cintrp-thm Γ₀ Γ₁ Γ₂ f refl
... | i-c Ξ refl h , v-c a-Ξ a-h , eq =
  i-c Ξ refl (Il h) ,
  v-c a-Ξ a-h ,
  ≡-to-≗ (ccut⋆Il Γ₀ Γ₂ Ξ h)
  ∙ Il eq
cintrp-thm {S} Γ₀ Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} {A}{B} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
... | inj₁ (Γ₀ , refl , refl) with cintrp-thm Γ₀ Γ₁ Γ₂ g refl
cintrp-thm {S} _ _ Γ₂ (⊗r {Γ = Γ} {A = A} {B} f g) refl | inj₁ (Γ₀ , refl , refl) | i-c Ξ refl h , v-c a-Ξ a-h , eq = 
  i-c Ξ refl (⊗r f h) ,
  v-c a-Ξ a-h' ,
  ≡-to-≗ (ccut⋆⊗r2 Γ₀ Γ₂ Ξ f h)
  ∙ ⊗r refl eq
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
 
cintrp-thm Γ₀ [] _ (⊗r f g) refl | inj₂ (A , Γ₁ , refl , refl) = i-c [] refl (⊗r f g) , v-c (λ ()) (λ ()) , refl
cintrp-thm {S} Γ₀ (A ∷ Γ₁) Γ₂ (⊗r {Δ = Δ} {A₁}{B₁} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
... | inj₂ (A' , Γ₂ , refl , refl) with cintrp-thm Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
cintrp-thm {S} Γ₀ (A ∷ Γ₁) _ (⊗r {Δ = Δ} {A₁} {B₁} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) | i-c Ξ eq h , v-c a-Ξ a-h , eq' = 
  i-c Ξ eq (⊗r h g) ,
  v-c a-Ξ (a-h' ∘ a-h) ,
  ≡-to-≗ (ccut⋆⊗r1 Γ₀ (_ ∷ Γ₂) Ξ h g)
  ∙ ⊗r eq' refl
  ∙ ≡-to-≗ (sym (trans (subst-cxt-uip _ _ (⊗r f g))
                       (subst-cxt⊗r1 (cong (λ x → Γ₀ ++ x ++ A' ∷ Γ₂) eq) f g) ))
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
      
cintrp-thm {S} Γ₀ (A ∷ _) Γ₂ (⊗r {A = A₁}{B} f g) eq | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , eq') | inj₁ (Γ₁ , refl , refl) with cintrp-thm Γ₀ (_ ∷ Γ') [] f refl | cintrp-thm [] Γ₁ Γ₂ g refl
cintrp-thm {S} Γ₀ (A ∷ _) Γ₂ (⊗r {A = A₁}{B} f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁@_ , refl , refl) | i-c Ξf eqf h , v-c a-Ξf a-h , eq | i-c Ξg refl k , v-c a-Ξg a-k , eq' = 
  i-c (Ξf ++ Ξg) eq'' (⊗r h k) ,
  v-c a-Ξ a-h' ,
  ≡-to-≗ (ccut⋆⊗r Γ₀ Γ₂ Ξf Ξg h k)
  ∙ cong-subst-cxt (cong (λ x → Γ₀ ++ x ++ Γ₂) (sym (concat++ Δs Λs)))
                   (⊗r eq eq' ∙ ≡-to-≗ (sym (subst-cxt⊗r1 (cong (Γ₀ ++_) eqf) f g)))
  ∙ ≡-to-≗ (trans-subst-cxt (cong (_++ concat (List.map proj₁ Ξg) ++ Γ₂) (cong (Γ₀ ++_) eqf)) (cong (λ x → Γ₀ ++ x ++ Γ₂) (sym (concat++ Δs Λs))) (⊗r f g))
  ∙ ≡-to-≗ (subst-cxt-uip _ (cong (λ x → Γ₀ ++ x ++ Γ₂) eq'') (⊗r f g))
  where
    Δs = List.map proj₁ Ξf
    Λs = List.map proj₁ Ξg
    Ds = List.map (λ x → proj₁ (proj₂ x)) Ξf
    Es = List.map (λ x → proj₁ (proj₂ x)) Ξg

    eq'' = trans (cong (_++ concat Λs) eqf) (sym (concat++ Δs Λs))

    a-Ξ : ∀{X} → X ∈ atom-c (Ds ++ Es) → X ∈ atom-c (A ∷ Γ' ++ Γ₁)
    a-Ξ m with ∈++ (atom-c Ds) (atom-c Es) (subst (λ x → _ ∈ x) (concat++ (List.map atom Ds) (List.map atom Es)) m)
    ... | inj₁ m' = 
       subst (λ x → _ ∈ x) (sym (concat++ (List.map atom (A ∷ Γ')) (List.map atom Γ₁)))
         (∈₁ (atom-c (A ∷ Γ')) (atom-c Γ₁) (a-Ξf m'))
    ... | inj₂ m' = 
       subst (λ x → _ ∈ x) (sym (concat++ (List.map atom (A ∷ Γ')) (List.map atom Γ₁)))
         (∈₂ (atom-c (A ∷ Γ')) (atom-c Γ₁) (a-Ξg m'))

    a-h' : ∀{X} → X ∈ atom-c (Ds ++ Es) → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom A₁ ++ atom B
    a-h' m with ∈++ (atom-c Ds) (atom-c Es) (subst (λ x → _ ∈ x) (concat++ (List.map atom Ds) (List.map atom Es)) m)
    a-h' m | inj₂ m' with ∈++ (atom-c Γ₂) (atom B) (a-k m')
    ... | inj₁ m'' = ∈₁ (atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂) (atom A₁ ++ atom B) (∈₂ (atom-s S ++ atom-c Γ₀) (atom-c Γ₂) m'')
    ... | inj₂ m'' = ∈₂ (atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom A₁) (atom B) m''
    a-h' m | inj₁ m' with ∈++ (atom-s S ++ atom-c Γ₀) (atom A₁) (a-h m')
    ... | inj₁ m'' = ∈₁ (atom-s S ++ atom-c Γ₀) (atom-c Γ₂ ++ atom A₁ ++ atom B) m''
    ... | inj₂ m'' = ∈₂ (atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂) (atom A₁ ++ atom B) (∈₁ (atom A₁) (atom B) m'')

cintrp-thm Γ₀ Γ₁ Γ₂ (⊗l f) refl with cintrp-thm (_ ∷ Γ₀) Γ₁ Γ₂ f refl
... | i-c Ξ eq h , v-c a-Ξ a-h , eq' =
  i-c Ξ eq (⊗l h) ,
  v-c a-Ξ a-h ,
  ≡-to-≗ (ccut⋆⊗l Γ₀ Γ₂ Ξ h)
  ∙ ⊗l eq'
  ∙ ≡-to-≗ (sym (trans (subst-cxt⊗l (cong (λ x → Γ₀ ++ x ++ Γ₂) eq) f)
                       (cong ⊗l (subst-cxt-uip _ _ f))))
cintrp-thm {S} Γ₀ Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with cintrp-thm Γ₀ Γ₁ (Γ₂ ∷ʳ _) f refl
... | i-c Ξ refl h , v-c a-Ξ a-h , eq =
  i-c Ξ refl (⊸r h) ,
  v-c a-Ξ (a-h' ∘ a-h) ,
  ≡-to-≗ (ccut⋆⊸r Γ₀ Γ₂ Ξ h)
  ∙ ⊸r eq
  where
    a-h' : ∀{X}
      → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c (Γ₂ ∷ʳ A) ++ atom B
      → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom A ++ atom B
    a-h' m = subst (λ x → _ ∈ atom-s S ++ atom-c Γ₀ ++ x ++ atom B) (concat++ (List.map atom Γ₂) [ atom A ]) m
cintrp-thm Γ₀ Γ₁ Γ₂ (⊸l {Γ} {Δ} {A}{B}{C} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
... | inj₁ (Γ₀ , refl , refl) with cintrp-thm Γ₀ Γ₁ Γ₂ g refl
cintrp-thm _ _ Γ₂ (⊸l {Γ} {A = A}{B}{C} f g) refl | inj₁ (Γ₀ , refl , refl) | i-c Ξ refl h , v-c a-Ξ a-h , eq = 
  i-c Ξ refl (⊸l {Γ = Γ} f h) ,
  v-c a-Ξ (a-h' ∘ a-h) ,
  ≡-to-≗ (ccut⋆⊸l2 Γ₀ Γ₂ Ξ f h)
  ∙ ⊸l refl eq
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
cintrp-thm Γ₀ [] _ (⊸l f g) refl | inj₂ (B , Γ' , refl , refl) = i-c [] refl (⊸l f g) , v-c (λ ()) (λ ()) , refl
cintrp-thm Γ₀ (A ∷ Γ₁) Γ₂ (⊸l {Δ = Δ} {A₁}{B₁}{C} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
... | inj₂ (A' , Γ₂ , refl , refl) with cintrp-thm Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
cintrp-thm Γ₀ (A ∷ Γ₁) _ (⊸l {Δ = Δ} {A₁}{B₁}{C} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) | i-c Ξ eq h , v-c a-Ξ a-h , eq' = 
  i-c Ξ eq (⊸l h g) ,
  v-c a-Ξ (a-h' ∘ a-h) ,
  ≡-to-≗ (ccut⋆⊸l1 Γ₀ (_ ∷ Γ₂) Ξ h g)
  ∙ ⊸l eq' refl
  ∙ ≡-to-≗ (sym (trans (subst-cxt-uip _ _ (⊸l f g))
                       (subst-cxt⊸l1 (cong (λ x → Γ₀ ++ x ++ _ ∷ Γ₂) eq) f g)))
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
cintrp-thm Γ₀ (A ∷ _) Γ₂ (⊸l {A = A₁}{B₁}{C} f g) eq | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , eq') | inj₁ (Γ₁ , refl , refl) with cintrp-thm Γ₀ (_ ∷ Γ') [] f refl | cintrp-thm [] Γ₁ Γ₂ g refl
cintrp-thm Γ₀ (A ∷ _) Γ₂ (⊸l {A = A₁}{B₁}{C} f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁@_ , refl , refl) | i-c Ξf eqf h , v-c a-Ξf a-h , eq | i-c Ξg refl k , v-c a-Ξg a-k , eq' = 
  i-c (Ξf ++ Ξg) eq'' (⊸l h k) ,
  v-c a-Ξ a-h' ,
  ≡-to-≗ (ccut⋆⊸l Γ₀ Γ₂ Ξf Ξg h k)
  ∙ cong-subst-cxt (cong (λ x → Γ₀ ++ x ++ Γ₂) (sym (concat++ Δs Λs)))
                   (⊸l eq eq' ∙ ≡-to-≗ (sym (subst-cxt⊸l1 (cong (Γ₀ ++_) eqf) f g)))
  ∙ ≡-to-≗ (trans-subst-cxt (cong (_++ concat (List.map proj₁ Ξg) ++ Γ₂) (cong (Γ₀ ++_) eqf)) (cong (λ x → Γ₀ ++ x ++ Γ₂) (sym (concat++ Δs Λs))) (⊸l f g))
  ∙ ≡-to-≗ (subst-cxt-uip _ (cong (λ x → Γ₀ ++ x ++ Γ₂) eq'') (⊸l f g))
  where
    Δs = List.map proj₁ Ξf
    Λs = List.map proj₁ Ξg
    Ds = List.map (λ x → proj₁ (proj₂ x)) Ξf
    Es = List.map (λ x → proj₁ (proj₂ x)) Ξg

    eq'' = trans (cong (_++ concat Λs) eqf) (sym (concat++ Δs Λs))

    a-Ξ : ∀{X} → X ∈ atom-c (Ds ++ Es) → X ∈ atom-c (A ∷ Γ' ++ Γ₁)
    a-Ξ m with ∈++ (atom-c Ds) (atom-c Es) (subst (λ x → _ ∈ x) (concat++ (List.map atom Ds) (List.map atom Es)) m)
    ... | inj₁ m' = 
       subst (λ x → _ ∈ x) (sym (concat++ (List.map atom (A ∷ Γ')) (List.map atom Γ₁)))
         (∈₁ (atom-c (A ∷ Γ')) (atom-c Γ₁) (a-Ξf m'))
    ... | inj₂ m' = 
       subst (λ x → _ ∈ x) (sym (concat++ (List.map atom (A ∷ Γ')) (List.map atom Γ₁)))
         (∈₂ (atom-c (A ∷ Γ')) (atom-c Γ₁) (a-Ξg m'))

    a-h' : ∀{X} → X ∈ atom-c (Ds ++ Es) → X ∈ atom A₁ ++ atom B₁ ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C
    a-h' m with ∈++ (atom-c Ds) (atom-c Es) (subst (λ x → _ ∈ x) (concat++ (List.map atom Ds) (List.map atom Es)) m)
    a-h' m | inj₂ m' with ∈++ (atom B₁) (atom-c Γ₂ ++ atom C) (a-k m')
    ... | inj₁ m'' = ∈₁ (atom A₁ ++ atom B₁) (atom-c Γ₀ ++ atom-c Γ₂ ++ atom C) (∈₂ (atom A₁) (atom B₁) m'') 
    ... | inj₂ m'' = ∈₂ (atom A₁ ++ atom B₁ ++ atom-c Γ₀) (atom-c Γ₂ ++ atom C) m''
    a-h' m | inj₁ m'  with ∈++ (atom-c Γ₀) (atom A₁) (a-h m')
    ... | inj₁ m'' = ∈₁ (atom A₁ ++ atom B₁ ++ atom-c Γ₀) (atom-c Γ₂ ++ atom C) (∈₂ (atom A₁ ++ atom B₁) (atom-c Γ₀) m'')
    ... | inj₂ m'' = ∈₁ (atom A₁) (atom B₁ ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C) m''



sintrp : ∀ {S} Γ₁ Γ₂ {C}
  → S ∣ Γ₁ ++ Γ₂ ⊢ C
  → sIntrp S Γ₁ Γ₂ C
sintrp Γ₁ Γ₂ f = sintrp-thm Γ₁ Γ₂ f refl .proj₁

cintrp : ∀{S} Γ₀ Γ₁ Γ₂ {C}
  → S ∣ Γ₀ ++ Γ₁ ++ Γ₂ ⊢ C
  → cIntrp S Γ₀ Γ₁ Γ₂ C
cintrp Γ₀ Γ₁ Γ₂ f = cintrp-thm Γ₀ Γ₁ Γ₂ f refl .proj₁

svar : ∀ {S} Γ₁ Γ₂ {C}
  → (f : S ∣ Γ₁ ++ Γ₂ ⊢ C) 
  → sVar S Γ₁ Γ₂ C (sIntrp.D (sintrp Γ₁ Γ₂ f))
svar Γ₁ Γ₂ f = sintrp-thm Γ₁ Γ₂ f refl .proj₂ .proj₁


cvar : ∀{S} Γ₀ Γ₁ Γ₂ {C}
  → (f : S ∣ Γ₀ ++ Γ₁ ++ Γ₂ ⊢ C)
  → cVar S Γ₀ Γ₁ Γ₂ C (cIntrp.Ds (cintrp Γ₀ Γ₁ Γ₂ f))
cvar Γ₀ Γ₁ Γ₂ f = cintrp-thm Γ₀ Γ₁ Γ₂ f refl .proj₂ .proj₁

scut-sintrp : ∀ {S} Γ₁ Γ₂ {C}
  → (f : S ∣ Γ₁ ++ Γ₂ ⊢ C)
  →  scut (sIntrp.g (sintrp Γ₁ Γ₂ f)) (sIntrp.h (sintrp Γ₁ Γ₂ f)) ≗ f
scut-sintrp Γ₁ Γ₂ f = sintrp-thm Γ₁ Γ₂ f refl .proj₂ .proj₂

cvar-cintrp : ∀{S} Γ₀ Γ₁ Γ₂ {C}
  → (f : S ∣ Γ₀ ++ Γ₁ ++ Γ₂ ⊢ C)
  → ccut⋆ Γ₀ Γ₂ (cIntrp.Ξ (cintrp Γ₀ Γ₁ Γ₂ f)) (cIntrp.g (cintrp Γ₀ Γ₁ Γ₂ f)) refl
          ≗ subst-cxt (cong (λ x → Γ₀ ++ x ++ Γ₂) (cIntrp.pt (cintrp Γ₀ Γ₁ Γ₂ f))) f
cvar-cintrp Γ₀ Γ₁ Γ₂ f = cintrp-thm Γ₀ Γ₁ Γ₂ f refl .proj₂ .proj₂








-- ---

-- -- Examples

-- module Ex {X Y Z W V : At} where

--   f : just ((` X ⊗ ` Y) ⊸ ` Z) ∣ ` W ⊸ ` X  ∷ ` W ∷ ` Y ∷ [] ⊢ ` Z
--   f = ⊸l (pass (⊸l (pass ax) (⊗r ax (pass ax)))) ax

--   intrp-f : hasIntrp-s (just ((` X ⊗ ` Y) ⊸ ` Z)) [ ` W ⊸ ` X ] (` W ∷ ` Y ∷ []) (` Z) refl
--   intrp-f = intrp-s [ ` W ⊸ ` X ] (` W ∷ ` Y ∷ []) f refl

--   D = hasIntrp-s.D intrp-f
--   D-eq : D ≡ ` W ⊸ (` Y ⊸ ` Z)
--   D-eq = refl


--   f' : just ((` X ⊗ ` Y) ⊸ ` Z) ∣ [] ⊢ ` X ⊸ (` Y ⊸ ` Z)
--   f' = ⊸r (⊸r (⊸l (pass (⊗r ax (pass ax))) ax))

--   intrp-f' : hasIntrp-s (just ((` X ⊗ ` Y) ⊸ ` Z)) [] [] (` X ⊸ (` Y ⊸ ` Z)) refl
--   intrp-f' = intrp-s [] [] f' refl

--   intrp-f'-alt : hasIntrp-s (just ((` X ⊗ ` Y) ⊸ ` Z)) [] [] (` X ⊸ (` Y ⊸ ` Z)) refl
--   intrp-f'-alt =
--     i-s (` X ⊸ (` Y ⊸ ` Z))
--         f'
--         ax
--         id
--         id

--   non-uniq : intrp-f'-alt ≡ intrp-f' → ⊥
--   non-uniq eq with cong hasIntrp-s.D eq
--   ... | ()
  

--   intrp-ax : hasIntrp-c (just (` X)) [] [] [] (` X) refl
--   intrp-ax = intrp-c [] [] [] (ax {` X}) refl

--   open hasIntrp-c

--   k : just (` X) ∣ I ∷ ` Y ∷ [] ⊢ ` X ⊗ ` Y
--   k = ⊗r ax (pass (Il (pass ax)))

--   test = {!!}



-- ---



-- scut-intrp-s : ∀ {S} Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₁ ++ Γ₂)
--   → scut (hasIntrp-s.g (intrp-s Γ₁ Γ₂ f eq)) (hasIntrp-s.h (intrp-s Γ₁ Γ₂ f eq)) ≗ subst-cxt eq f
  
-- ccut-intrp-c : ∀{S} Γ₀ Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂)
--   → ccut⋆ Γ₀ Γ₂ (hasIntrp-c.Ξ (intrp-c Γ₀ Γ₁ Γ₂ f eq)) (hasIntrp-c.g (intrp-c Γ₀ Γ₁ Γ₂ f eq)) refl
--           ≗ subst-cxt (trans eq (cong (λ x → Γ₀ ++ x ++ Γ₂) (hasIntrp-c.pt (intrp-c Γ₀ Γ₁ Γ₂ f eq)))) f

-- scut-intrp-s Γ₁ Γ₂ (Il f) refl = Il (scut-intrp-s Γ₁ Γ₂ f refl)
-- scut-intrp-s Γ₁ Γ₂ (⊗l f) refl = ⊗l (scut-intrp-s (_ ∷ Γ₁) Γ₂ f refl)
-- scut-intrp-s Γ₁ Γ₂ (⊸r {A = A}{B} f) refl =
--   scut⊸r (hasIntrp-s.g (intrp-s Γ₁ (Γ₂ ++ A ∷ []) f refl)) _
--   ∙ ⊸r (scut-intrp-s Γ₁ (Γ₂ ∷ʳ _) f refl)
-- scut-intrp-s Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
-- scut-intrp-s {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (Γ' , refl , refl) =
--   scut⊗r (hasIntrp-s.g (intrp-s Γ [] f refl)) _ _
--   ∙ ⊗r (scut-intrp-s Γ [] f refl) (scut-intrp-s Γ' Γ₂ g refl)
-- scut-intrp-s Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) =
--   scut⊗r (hasIntrp-s.g (intrp-s Γ₁ (A' ∷ Γ') f refl)) _ _
--   ∙ ⊗r {Γ = Γ₁ ++ A' ∷ Γ'} (scut-intrp-s Γ₁ (A' ∷ Γ') f refl) refl
-- scut-intrp-s Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ Γ₁  Δ Γ₂ (sym eq)
-- scut-intrp-s _ Γ₂ (⊸l {Γ} {A = A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) =
--   ⊸l refl (scut-intrp-s (A' ∷ Γ') Γ₂ g refl)
-- scut-intrp-s Γ₁ _ (⊸l {Δ = Δ} {A = A}{B}{C} f g) refl | inj₁ (Γ' , refl , refl) with intrp-c Γ₁ Γ' [] f refl | inspect (λ x → intrp-c Γ₁ Γ' [] x refl) f
-- ... | i-c Ξ refl f' _ _ | PE.[ eq ] = 
--       proof≗
--       scut (⊸r⋆ As (⊸l f' g')) (⊸l⋆ Ξ g'')
--       ≗〈 ≡-to-≗ (scut⊸r⋆⊸l⋆ Ξ (⊸l f' g') g'') 〉
--       scut (ccut⋆ Γ₁ [] Ξ (⊸l f' g') refl) g''
--       ≗〈 cong-scut1 {Γ = Γ₁ ++ concat Δs} lem g'' 〉
--       scut (⊸l f g') g''
--       ≗〈 refl 〉
--       ⊸l f (scut g' g'')
--       ≗〈 ⊸l refl (scut-intrp-s [] Δ g refl) 〉
--       ⊸l f g
--       qed≗
-- --with intrp-c Γ₁ Γ' [] f refl | intrp-s [] Δ g refl
-- --... | i-c Ξ refl f' _ _ | i-s E g' g'' _ _ = {!!}
--   where
--     Δs = List.map proj₁ Ξ
--     As = List.map (λ x → proj₁ (proj₂ x)) Ξ

--     E = hasIntrp-s.D (intrp-s [] Δ g refl)
--     g' = hasIntrp-s.g (intrp-s [] Δ g refl)
--     g'' = hasIntrp-s.h (intrp-s [] Δ g refl)

--     lem' : ccut⋆ Γ₁ [] (hasIntrp-c.Ξ (intrp-c Γ₁ (concat Δs) [] f refl)) (hasIntrp-c.g (intrp-c Γ₁ (concat Δs) [] f refl)) refl
--          ≗ subst-cxt (trans refl (cong (Γ₁ ++_) (hasIntrp-c.pt (intrp-c Γ₁ (concat Δs) [] f refl)))) f
--     lem' = ccut-intrp-c Γ₁ _ [] f refl

--     lem : ccut⋆ Γ₁ [] Ξ (⊸l f' g') refl ≗ ⊸l f g'
--     lem = 
--       proof≗
--       ccut⋆ Γ₁ [] Ξ (⊸l f' g') refl
--       ≗〈 {!!} 〉
--       ⊸l (ccut⋆ Γ₁ [] Ξ f' refl) g'
--       ≗〈 ⊸l {!ccut-intrp-c Γ₁ _ [] f refl!} refl 〉
--       ⊸l f g'
--       qed≗

-- -- 
-- --     lem2 : subst-cxt (cong (λ x → Γ₁ ++ x) (sym eq)) (ccut⋆ Γ₁ [] Ξ (⊸l f' g') refl) ≗ ⊸l f g'
-- --     lem2 = {!!}
-- -- 
-- --     lem : scut (⊸r⋆ As (⊸l f' g')) (⊸l⋆ Ξ g'' eq) ≗ ⊸l f g
-- --     lem =
-- --       proof≗
-- --       scut (⊸r⋆ As (⊸l f' g')) (⊸l⋆ Ξ g'' eq)
-- --       ≗〈 ≡-to-≗ (scut⊸r⋆⊸l⋆ Ξ (⊸l f' g') g'' eq) 〉
-- --       subst-cxt (cong (λ x → Γ₁ ++ x ++ Δ) (sym eq)) (scut (ccut⋆ Γ₁ [] Ξ (⊸l f' g') refl) g'')
-- --       ≗〈 {!!} 〉
-- --       scut (subst-cxt (cong (λ x → Γ₁ ++ x) (sym eq)) (ccut⋆ Γ₁ [] Ξ (⊸l f' g') refl)) g''
-- --       ≗〈 cong-scut1 {Γ = Γ₁ ++ _ ∷ Γ'} lem2 g'' 〉
-- --       scut (⊸l f g') g''
-- --       ≗〈 refl 〉
-- --       ⊸l f (scut g' g'')
-- --       ≗〈 ⊸l refl (scut-intrp-s [] Δ g refl) 〉
-- --       ⊸l f g
-- --       qed≗
-- scut-intrp-s [] [] ax refl = refl
-- scut-intrp-s [] (A ∷ Γ₂) (pass f) refl = refl
-- scut-intrp-s (A ∷ Γ₁) Γ₂ (pass f) refl = pass (scut-intrp-s Γ₁ Γ₂ f refl)
-- scut-intrp-s [] [] Ir refl = refl





















{-
-- The proof of Craig interpolation

sintrp : ∀ {S} Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₁ ++ Γ₂)
  → sIntrp S Γ₁ Γ₂ C

cintrp : ∀{S} Γ₀ Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂)
  → cIntrp S Γ₀ Γ₁ Γ₂ C

sintrp Γ₁ Γ₂ (Il f) refl with sintrp Γ₁ Γ₂ f refl
... | i-s D g h = i-s D (Il g) h
sintrp Γ₁ Γ₂ (⊗l f) refl with sintrp (_ ∷ Γ₁) Γ₂ f refl
... | i-s D g h = i-s D (⊗l g) h
sintrp Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with sintrp Γ₁ (Γ₂ ∷ʳ _) f refl
... | i-s D g h = i-s D g (⊸r h)
sintrp Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
sintrp {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (Γ' , refl , refl) with sintrp Γ [] f refl | sintrp Γ' Γ₂ g refl
... | i-s D g h | i-s E k l = i-s (D ⊗ E) (⊗r g k) (⊗l (⊗r h (pass l))) 
sintrp Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) eq | inj₂ (A' , Γ' , refl , refl) with sintrp Γ₁ (_ ∷ Γ') f refl
... | i-s D h k = i-s D h (⊗r k g)
sintrp Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ Γ₁ Δ Γ₂ (sym eq)
sintrp Γ₁ .(Γ' ++ Δ) (⊸l {Δ = Δ} {A}{B}{C} f g) eq | inj₁ (Γ' , refl , refl) with sintrp [] Δ g refl | cintrp Γ₁ Γ' [] f refl
... | i-s E h k | i-c Ξ refl l = 
  i-s (Ds ⊸⋆ E) (⊸r⋆ Ds (⊸l l h)) (⊸l⋆ Ξ k)
  where
    Ds = List.map (λ x → proj₁ (proj₂ x)) Ξ
sintrp _ Γ₂ (⊸l {Γ} {A = A}{B} f g) eq | inj₂ (A' , Γ' , refl , refl) with sintrp (A' ∷ Γ') Γ₂ g refl
... | i-s D h k = i-s _ (⊸l f h) k
sintrp [] [] ax refl = i-s _ ax ax
sintrp [] (A ∷ Γ₂) (pass f) refl = i-s _ Ir (Il (pass f))
sintrp (A ∷ Γ₁) Γ₂ (pass f) refl with sintrp Γ₁ Γ₂ f refl
... | i-s D g h = i-s D (pass g) h
sintrp [] [] Ir refl = i-s I Ir ax

cintrp [] [] [] ax refl = i-c [] refl ax
cintrp [] [] Γ₂ (pass f) refl = i-c [] refl (pass f)
cintrp [] (A ∷ Γ₁) Γ₂ (pass f) refl with sintrp Γ₁ Γ₂ f refl
... | i-s D g k = i-c [ (A ∷ Γ₁ , _ , pass g) ] refl (pass k)
cintrp (A ∷ Γ₀) Γ₁ Γ₂ (pass f) refl with cintrp Γ₀ Γ₁ Γ₂ f refl
... | i-c Ξ eq h = i-c Ξ eq (pass h)
cintrp [] [] [] Ir refl = i-c [] refl Ir
cintrp Γ₀ Γ₁ Γ₂ (Il f) refl with cintrp Γ₀ Γ₁ Γ₂ f refl
... | i-c Ξ eq h = i-c Ξ eq (Il h)
cintrp {S} Γ₀ Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} {A}{B} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
... | inj₁ (Γ₀ , refl , refl) with cintrp Γ₀ Γ₁ Γ₂ g refl
... | i-c Ξ eq' h = i-c Ξ eq' (⊗r f h)
  where
    Ds = List.map (λ x → proj₁ (proj₂ x)) Ξ 
cintrp Γ₀ [] _ (⊗r f g) eq | inj₂ (A , Γ₁ , refl , refl) = i-c [] refl (⊗r f g)
cintrp {S} Γ₀ (A ∷ Γ₁) Γ₂ (⊗r {Δ = Δ} {A₁}{B₁} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
... | inj₂ (A' , Γ₂ , refl , refl) with cintrp Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
... | i-c Ξ eq'' h = i-c Ξ eq'' (⊗r h g)
cintrp {S} Γ₀ (A ∷ _) Γ₂ (⊗r {A = A₁}{B} f g) eq | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , eq') | inj₁ (Γ₁ , refl , refl)
  with cintrp Γ₀ (_ ∷ Γ') [] f refl | cintrp [] Γ₁ Γ₂ g refl
... | i-c Ξf eqf h | i-c Ξg eqg k =
  i-c (Ξf ++ Ξg)
      (trans (cong₂ _++_ {x = _ ∷ Γ'} eqf eqg) (sym (concat++ (List.map proj₁ Ξf) (List.map proj₁ Ξg))))
      (⊗r h k)
  where
    Δs = List.map proj₁ Ξf
    Λs = List.map proj₁ Ξg
    Ds = List.map (λ x → proj₁ (proj₂ x)) Ξf
    Es = List.map (λ x → proj₁ (proj₂ x)) Ξg
cintrp Γ₀ Γ₁ Γ₂ (⊗l f) refl with cintrp (_ ∷ Γ₀) Γ₁ Γ₂ f refl
... | i-c Ξ eq h = i-c Ξ eq (⊗l h)
cintrp {S} Γ₀ Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with cintrp Γ₀ Γ₁ (Γ₂ ∷ʳ _) f refl
... | i-c Ξ eq h = i-c Ξ eq (⊸r h)
cintrp Γ₀ Γ₁ Γ₂ (⊸l {Γ} {Δ} {A}{B}{C} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
... | inj₁ (Γ₀ , refl , refl) with cintrp Γ₀ Γ₁ Γ₂ g refl
... | i-c Ξ eq' h = i-c Ξ eq' (⊸l {Γ = Γ} f h)
cintrp Γ₀ [] _ (⊸l f g) eq | inj₂ (B , Γ' , refl , refl) = i-c [] refl (⊸l f g)
cintrp Γ₀ (A ∷ Γ₁) Γ₂ (⊸l {Δ = Δ} {A₁}{B₁}{C} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
... | inj₂ (A' , Γ₂ , refl , refl) with cintrp Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
... | i-c Ξ eq'' h = i-c Ξ eq'' (⊸l h g) 
cintrp Γ₀ (A ∷ _) Γ₂ (⊸l {A = A₁}{B₁}{C} f g) eq | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , eq') | inj₁ (Γ₁ , refl , refl)
  with cintrp Γ₀ (_ ∷ Γ') [] f refl | cintrp [] Γ₁ Γ₂ g refl
... | i-c Ξf eqf h | i-c Ξg eqg k =
  i-c (Ξf ++ Ξg)
      (trans (cong₂ _++_ {x = _ ∷ Γ'} eqf eqg) (sym (concat++ (List.map proj₁ Ξf) (List.map proj₁ Ξg))))
      (⊸l h k)
  where
    Δs = List.map proj₁ Ξf
    Λs = List.map proj₁ Ξg
    Ds = List.map (λ x → proj₁ (proj₂ x)) Ξf
    Es = List.map (λ x → proj₁ (proj₂ x)) Ξg


svar : ∀ {S} Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₁ ++ Γ₂)
  → sVar S Γ₁ Γ₂ C (sIntrp.D (sintrp Γ₁ Γ₂ f eq))

cvar : ∀{S} Γ₀ Γ₁ Γ₂ {Γ C} (f : S ∣ Γ ⊢ C) (eq : Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂)
  → cVar S Γ₀ Γ₁ Γ₂ C (cIntrp.Ds (cintrp Γ₀ Γ₁ Γ₂ f eq))

svar Γ₁ Γ₂ (Il f) refl with sintrp Γ₁ Γ₂ f refl | svar Γ₁ Γ₂ f refl
... | i-s D g h | v-s a-g a-h = v-s a-g a-h
svar Γ₁ Γ₂ (⊗l f) refl with sintrp (_ ∷ Γ₁) Γ₂ f refl | svar (_ ∷ Γ₁) Γ₂ f refl
... | i-s D g h | v-s a-g a-h = v-s a-g a-h
svar Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with sintrp Γ₁ (Γ₂ ∷ʳ _) f refl | svar Γ₁ (Γ₂ ∷ʳ _) f refl
... | i-s D g h | v-s a-g a-h = v-s a-g a-h'
  where
    a-h' : ∀{X} → X ∈ atom D → X ∈ atom-c Γ₂ ++ atom A ++ atom B
    a-h' m with ∈++ (atom-c (Γ₂ ∷ʳ A)) (atom B) (a-h m)
    ... | inj₁ m' = ∈₁ (atom-c Γ₂ ++ atom A) (atom B) (subst (λ x → _ ∈ x) (concat++ (List.map atom Γ₂) [ atom A ]) m')
    ... | inj₂ m' = ∈₂ (atom-c Γ₂ ++ atom A) (atom B) m'
svar Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
svar {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (Γ' , refl , refl)
  with sintrp Γ [] f refl | sintrp Γ' Γ₂ g refl | svar Γ [] f refl | svar Γ' Γ₂ g refl
... | i-s D g h | i-s E k l | v-s a-g a-h | v-s a-k a-l = v-s a-g' a-h'
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
svar Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) eq | inj₂ (A' , Γ' , refl , refl)
  with sintrp Γ₁ (_ ∷ Γ') f refl | svar Γ₁ (_ ∷ Γ') f refl
... | i-s D h k | v-s a-h a-k = v-s a-h a-k'
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
svar Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ Γ₁ Δ Γ₂ (sym eq)
svar Γ₁ .(Γ' ++ Δ) (⊸l {Δ = Δ} {A}{B}{C} f g) eq | inj₁ (Γ' , refl , refl)
  with sintrp [] Δ g refl | cintrp Γ₁ Γ' [] f refl | svar [] Δ g refl | cvar Γ₁ Γ' [] f refl
... | i-s E h k | i-c Ξ refl l | v-s a-h a-k | v-c a-Ξ a-l = v-s a-h' a-k'
  where
    Ds = List.map (λ x → proj₁ (proj₂ x)) Ξ

    a-h' : ∀{X} → X ∈ atom (Ds ⊸⋆ E) → X ∈ atom A ++ atom B ++ atom-c Γ₁
    a-h' m with ∈atom⊸⋆ Ds m
    ... | inj₂ m' = ∈₁ (atom A ++ atom B) (atom-c Γ₁) (∈₂ (atom A) (atom B) (a-h m'))
    ... | inj₁ m' with ∈++ (atom-c Γ₁) (atom A) (a-l m')
    ... | inj₁ m'' = ∈₂ (atom A ++ atom B) (atom-c Γ₁) m''
    ... | inj₂ m'' = ∈₁ (atom A) (atom B ++ atom-c Γ₁) m''

    a-k' : ∀{X} → X ∈ atom (Ds ⊸⋆ E) → X ∈ atom-c (Γ' ++ Δ) ++ atom C
    a-k' m with ∈atom⊸⋆ Ds m
    ... | inj₂ m' =
        subst (λ x → _ ∈ x ++ atom C) (sym (concat++ (List.map atom Γ') (List.map atom Δ)))
           (∈₂ (atom-c Γ') (atom-c Δ ++ atom C) (a-k m'))
    ... | inj₁ m' = 
      ∈₁ (atom-c (Γ' ++ Δ)) (atom C)
        (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ') (List.map atom Δ)))
          (∈₁ (atom-c Γ') (atom-c Δ) (a-Ξ m')))
svar _ Γ₂ (⊸l {Γ} {A = A}{B} f g) eq | inj₂ (A' , Γ' , refl , refl)
  with sintrp (A' ∷ Γ') Γ₂ g refl | svar (A' ∷ Γ') Γ₂ g refl
... | i-s D h k | v-s a-h a-k = v-s a-h' a-k
  where
    a-h' : ∀{X} → X ∈ atom D → X ∈ atom A ++ atom B ++ atom-c (Γ ++ A' ∷ Γ')
    a-h' m with ∈++ (atom B) (atom-c (A' ∷ Γ')) (a-h m)
    ... | inj₁ m' = ∈₁ (atom A ++ atom B) (atom-c (Γ ++ A' ∷ Γ')) (∈₂ (atom A) (atom B) m')
    ... | inj₂ m' =
      ∈₂ (atom A ++ atom B) (atom-c (Γ ++ A' ∷ Γ'))
        (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ) (List.map atom (A' ∷ Γ')))) (∈₂ (atom-c Γ) (atom-c (A' ∷ Γ')) m'))
svar [] [] ax refl = v-s id id
svar [] (A ∷ Γ₂) (pass f) refl = v-s (λ ()) λ ()
svar (A ∷ Γ₁) Γ₂ (pass f) refl with sintrp Γ₁ Γ₂ f refl | svar Γ₁ Γ₂ f refl
... | i-s D g h | v-s a-g a-h = v-s a-g a-h
svar [] [] Ir refl = v-s (λ ()) id


cvar [] [] [] ax refl = v-c id (λ ())
cvar [] [] Γ₂ (pass f) refl = v-c (λ ()) (λ ())
cvar [] (A ∷ Γ₁) Γ₂ (pass f) refl with sintrp Γ₁ Γ₂ f refl | svar Γ₁ Γ₂ f refl
... | i-s D g k | v-s a-g a-k = v-c a-g a-k
cvar (A ∷ Γ₀) Γ₁ Γ₂ (pass f) refl with cintrp Γ₀ Γ₁ Γ₂ f refl | cvar Γ₀ Γ₁ Γ₂ f refl
... | i-c Ξ eq h | v-c a-Ξ a-h = v-c a-Ξ a-h
cvar [] [] [] Ir refl = v-c (λ ()) id
cvar Γ₀ Γ₁ Γ₂ (Il f) refl with cintrp Γ₀ Γ₁ Γ₂ f refl
... | i-c Ξ refl h with cvar Γ₀ (concat (List.map proj₁ Ξ)) Γ₂ f refl
... | v-c a-Ξ a-h = v-c {!a-Ξ!} {!a-h!}
cvar {S} Γ₀ Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} {A}{B} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
... | inj₁ (Γ₀ , refl , refl) with cintrp Γ₀ Γ₁ Γ₂ g refl | cvar Γ₀ Γ₁ Γ₂ g refl
... | i-c Ξ eq' h | v-c a-Ξ a-h = {!!} --v-c a-Ξ a-h'
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
 
cvar Γ₀ [] _ (⊗r f g) eq | inj₂ (A , Γ₁ , refl , refl) = v-c (λ ()) (λ ())
cvar {S} Γ₀ (A ∷ Γ₁) Γ₂ (⊗r {Δ = Δ} {A₁}{B₁} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
... | inj₂ (A' , Γ₂ , refl , refl) with cintrp Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl | cvar Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
... | i-c Ξ eq'' h | v-c a-Ξ a-h = {!!} --v-c a-Ξ (a-h' ∘ a-h)
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
      
cvar {S} Γ₀ (A ∷ _) Γ₂ (⊗r {A = A₁}{B} f g) eq | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , eq') | inj₁ (Γ₁ , refl , refl)
  with cintrp Γ₀ (_ ∷ Γ') [] f refl | cintrp [] Γ₁ Γ₂ g refl | cvar Γ₀ (_ ∷ Γ') [] f refl | cvar [] Γ₁ Γ₂ g refl
... | i-c Ξf eqf h | i-c Ξg eqg k | v-c a-Ξf a-h | v-c a-Ξg a-k = {!!} --v-c a-Ξ a-h'
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
          (∈₁ (atom-c (concat Δs)) (atom-c (concat Λs)) {!!})) --(a-Ξf m')
    ... | inj₂ m' = 
      subst (λ x → _ ∈ atom-c x) (sym (concat++ Δs Λs))
        (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom (concat Δs)) (List.map atom (concat Λs))))
          (∈₂ (atom-c (concat Δs)) (atom-c (concat Λs)) {!!})) --(a-Ξg m')

    a-h' : ∀{X} → X ∈ atom-c (Ds ++ Es) → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom A₁ ++ atom B
    a-h' m with ∈++ (atom-c Ds) (atom-c Es) (subst (λ x → _ ∈ x) (concat++ (List.map atom Ds) (List.map atom Es)) m)
    a-h' m | inj₂ m' with ∈++ (atom-c Γ₂) (atom B) (a-k m')
    ... | inj₁ m'' = ∈₁ (atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂) (atom A₁ ++ atom B) (∈₂ (atom-s S ++ atom-c Γ₀) (atom-c Γ₂) m'')
    ... | inj₂ m'' = ∈₂ (atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom A₁) (atom B) m''
    a-h' m | inj₁ m' with ∈++ (atom-s S ++ atom-c Γ₀) (atom A₁) (a-h m')
    ... | inj₁ m'' = ∈₁ (atom-s S ++ atom-c Γ₀) (atom-c Γ₂ ++ atom A₁ ++ atom B) m''
    ... | inj₂ m'' = ∈₂ (atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂) (atom A₁ ++ atom B) (∈₁ (atom A₁) (atom B) m'')

cvar Γ₀ Γ₁ Γ₂ (⊗l f) refl with cintrp (_ ∷ Γ₀) Γ₁ Γ₂ f refl | cvar (_ ∷ Γ₀) Γ₁ Γ₂ f refl
... | i-c Ξ eq h | v-c a-Ξ a-h = {!!} --v-c a-Ξ a-h
cvar {S} Γ₀ Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with cintrp Γ₀ Γ₁ (Γ₂ ∷ʳ _) f refl | cvar Γ₀ Γ₁ (Γ₂ ∷ʳ _) f refl
... | i-c Ξ eq h | v-c a-Ξ a-h = {!!} --v-c a-Ξ (a-h' ∘ a-h)
  where
    a-h' : ∀{X}
      → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c (Γ₂ ∷ʳ A) ++ atom B
      → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom A ++ atom B
    a-h' m = subst (λ x → _ ∈ atom-s S ++ atom-c Γ₀ ++ x ++ atom B) (concat++ (List.map atom Γ₂) [ atom A ]) m
cvar Γ₀ Γ₁ Γ₂ (⊸l {Γ} {Δ} {A}{B}{C} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
... | inj₁ (Γ₀ , refl , refl) with cintrp Γ₀ Γ₁ Γ₂ g refl | cvar Γ₀ Γ₁ Γ₂ g refl
... | i-c Ξ eq' h | v-c a-Ξ a-h = {!!} --v-c a-Ξ (a-h' ∘ a-h)
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
cvar Γ₀ [] _ (⊸l f g) eq | inj₂ (B , Γ' , refl , refl) = v-c (λ ()) (λ ())
cvar Γ₀ (A ∷ Γ₁) Γ₂ (⊸l {Δ = Δ} {A₁}{B₁}{C} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
... | inj₂ (A' , Γ₂ , refl , refl) with cintrp Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl | cvar Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
... | i-c Ξ eq'' h | v-c a-Ξ a-h = {!!} --v-c a-Ξ (a-h' ∘ a-h)
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
cvar Γ₀ (A ∷ _) Γ₂ (⊸l {A = A₁}{B₁}{C} f g) eq | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , eq') | inj₁ (Γ₁ , refl , refl)
  with cintrp Γ₀ (_ ∷ Γ') [] f refl | cintrp [] Γ₁ Γ₂ g refl | cvar Γ₀ (_ ∷ Γ') [] f refl | cvar [] Γ₁ Γ₂ g refl
... | i-c Ξf eqf h | i-c Ξg eqg k | v-c a-Ξf a-h | v-c a-Ξg a-k = {!!} --v-c a-Ξ a-h'
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
          (∈₁ (atom-c (concat Δs)) (atom-c (concat Λs)) {!!})) --(a-Ξf m')
    ... | inj₂ m' = 
      subst (λ x → _ ∈ atom-c x) (sym (concat++ Δs Λs))
        (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom (concat Δs)) (List.map atom (concat Λs))))
          (∈₂ (atom-c (concat Δs)) (atom-c (concat Λs)) {!!})) --(a-Ξg m')

    a-h' : ∀{X} → X ∈ atom-c (Ds ++ Es) → X ∈ atom A₁ ++ atom B₁ ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C
    a-h' m with ∈++ (atom-c Ds) (atom-c Es) (subst (λ x → _ ∈ x) (concat++ (List.map atom Ds) (List.map atom Es)) m)
    a-h' m | inj₂ m' with ∈++ (atom B₁) (atom-c Γ₂ ++ atom C) (a-k m')
    ... | inj₁ m'' = ∈₁ (atom A₁ ++ atom B₁) (atom-c Γ₀ ++ atom-c Γ₂ ++ atom C) (∈₂ (atom A₁) (atom B₁) m'') 
    ... | inj₂ m'' = ∈₂ (atom A₁ ++ atom B₁ ++ atom-c Γ₀) (atom-c Γ₂ ++ atom C) m''
    a-h' m | inj₁ m'  with ∈++ (atom-c Γ₀) (atom A₁) (a-h m')
    ... | inj₁ m'' = ∈₁ (atom A₁ ++ atom B₁ ++ atom-c Γ₀) (atom-c Γ₂ ++ atom C) (∈₂ (atom A₁ ++ atom B₁) (atom-c Γ₀) m'')
    ... | inj₂ m'' = ∈₁ (atom A₁) (atom B₁ ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C) m''
-}



-- record hasIntrp-s S Γ₁ Γ₂ {Γ} C (eq : Γ ≡ Γ₁ ++ Γ₂) : Set where
--   constructor i-s
--   field
--     D : Fma
--     g : S ∣ Γ₁ ⊢ D
--     h : just D ∣ Γ₂ ⊢ C
--     atom-g : ∀{X} → X ∈ atom D → X ∈ atom-s S ++ atom-c Γ₁
--     atom-h : ∀{X} → X ∈ atom D → X ∈ atom-c Γ₂ ++ atom C

-- record hasIntrp-c S Γ₀ Γ₁ Γ₂ {Γ} C (eq : Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂) : Set where
--   constructor i-c
--   field
--     Ξ : List (Σ Cxt λ Δ → Σ Fma λ D → ─ ∣ Δ ⊢ D)
--     pt : Γ₁ ≡ concat (List.map proj₁ Ξ)
--     g : S ∣ Γ₀ ++ List.map (λ x → proj₁ (proj₂ x)) Ξ ++ Γ₂ ⊢ C
--     atom-Ξ : ∀{X} → X ∈ atom-c (List.map (λ x → proj₁ (proj₂ x)) Ξ) → X ∈ atom-c (concat (List.map proj₁ Ξ))
--     atom-g : ∀{X} → X ∈ atom-c (List.map (λ x → proj₁ (proj₂ x)) Ξ) → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C
