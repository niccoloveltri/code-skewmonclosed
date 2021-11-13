{-# OPTIONS --rewriting #-}

module Formulae (At : Set) where

open import Data.Maybe
open import Data.List
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Utilities


-- Formulae
data Fma : Set where
  ` : At → Fma
  I : Fma
  _⊗_ : Fma → Fma → Fma
  _⊸_ : Fma → Fma → Fma

infix 22 _⊸_ _⊗_

-- Stoup
Stp : Set
Stp = Maybe Fma

pattern ─ = nothing

-- Context
Cxt : Set
Cxt = List Fma

-- Iterated ⊸
_⊸⋆_ : Cxt → Fma → Fma
[] ⊸⋆ C = C
(A ∷ Γ) ⊸⋆ C = A ⊸ (Γ ⊸⋆ C)

infix 21 _⊸⋆_

snoc⊸⋆ : (Γ : Cxt) (A B : Fma)
  → Γ ⊸⋆ A ⊸ B ≡ (Γ ∷ʳ A) ⊸⋆ B
snoc⊸⋆ [] A B = refl
snoc⊸⋆ (A' ∷ Γ) A B rewrite snoc⊸⋆ Γ A B = refl

{-# REWRITE snoc⊸⋆ #-}

-- Predicates on formulae checking whether:

-- -- the formula isn't atomic
isn'tAt : Fma → Set
isn'tAt (` X) = ⊥
isn'tAt _ = ⊤

-- -- the main connective isn't ⊗
isn't⊗ : Fma → Set
isn't⊗ (A ⊗ B) = ⊥
isn't⊗ _ = ⊤

-- -- the main connective isn't unit nor tensor, i.e. the formula is
-- -- negative (atoms are not polarized)
isNeg : Fma → Set
isNeg (` X) = ⊤
isNeg (A ⊸ B) = ⊤
isNeg _ = ⊥

is⊸ : Fma → Set
is⊸ (A ⊸ B) = ⊤
is⊸ _ = ⊥

isAt : Fma → Set
isAt (` X) = ⊤
isAt _ = ⊥

-- -- the main connective isn't ⊸, i.e. the formula is positive (atoms
-- -- are not polarized)
isPos : Fma → Set
isPos (A ⊸ B) = ⊥
isPos _ = ⊤



-- Predicate on stoups checking whether the stoup is irreducible,
-- i.e. if it is a single formula, then it is negative
isIrr : Stp → Set
isIrr ─ = ⊤
isIrr (just A) = isNeg A

isIrr⊸ : Stp → Set
isIrr⊸ ─ = ⊤
isIrr⊸ (just A) = is⊸ A

isIrrAt : Stp → Set
isIrrAt ─ = ⊤
isIrrAt (just A) = isAt A

-- The type of irreducible stoups
Irr : Set
Irr = Σ Stp λ S → isIrr S

Irr⊸ : Set
Irr⊸ = Σ Stp λ S → isIrr⊸ S

IrrAt : Set
IrrAt = Σ Stp λ S → isIrrAt S

irrisAt : ∀ S → isIrrAt S → isIrr S
irrisAt ─ p = tt
irrisAt (just (` X)) p = tt

irris⊸ : ∀ S → isIrr⊸ S → isIrr S
irris⊸ ─ p = tt
irris⊸ (just (A ⊸ B)) p = tt

irrAt : IrrAt → Irr
irrAt (S , p) = S , irrisAt S p

irr⊸ : Irr⊸ → Irr
irr⊸ (S , p) = S , irris⊸ S p

-- The type of positive formulae
Pos : Set
Pos = Σ Fma λ A → isPos A

-- The type of negative formulae
Neg : Set
Neg = Σ Fma λ A → isNeg A

-- Projections and embeddings
irr : Irr → Stp
irr (S , s) = S

pos : Pos → Fma
pos (A , a) = A

neg : Neg → Fma
neg (A , a) = A

neg2irr : Neg → Irr
neg2irr (A , a) = just A , a
