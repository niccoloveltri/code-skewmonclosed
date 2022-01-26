{-# OPTIONS --rewriting #-}

module Focusing (At : Set) where

open import Data.List renaming (map to mapList)
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open import Data.Bool renaming (Bool to Tag; true to •; false to ∘)

open import Utilities
open import Formulae At
open import SeqCalc At

{-
===============================================================
The focused sequent calculus of skew monoidal closed categories
=============================================================== 
-}

-- Tagged contexts
TCxt : Tag → Set
TCxt • = Cxt
TCxt ∘ = ⊤

tcxt : (x : Tag) → TCxt x → Cxt
tcxt ∘ Ω = []
tcxt • Ω = Ω

T[] : (x : Tag) → TCxt x
T[] ∘ = tt
T[] • = []

{- ====================================================== -}

-- Inference rules

-- Sequents have 4 phases:

-- -- ri = right invertible
data [_]_∣_؛_⊢ri_ : (x : Tag) → Stp → Cxt → TCxt x → Fma → Set

-- -- li = left invertible 
data [_]_∣_؛_⊢li_ : (x : Tag) → Stp → Cxt → TCxt x → Pos → Set

-- -- p = passivation
data [_]_∣_؛_⊢p_ : (x : Tag) → Irr → Cxt → TCxt x → Pos → Set

-- -- f = focusing
data [_]_∣_؛_⊢f_ : (x : Tag) → Irr → Cxt → TCxt x → Pos → Set

data [_]_∣_؛_⊢ri_ where
  ⊸r : {S : Stp} {Γ : Cxt} {A B : Fma} 
        (f : [ ∘ ] S ∣ Γ ∷ʳ A ؛ _ ⊢ri B) →
       ---------------------------------
             [ ∘ ] S ∣ Γ ؛ _ ⊢ri A ⊸ B

  ⊸r• : {S : Stp} {Γ Ω : Cxt} {A B : Fma} 
        (f : [ • ] S ∣ Γ ؛ Ω ∷ʳ A ⊢ri B) →
       ---------------------------------
             [ • ] S ∣ Γ ؛ Ω ⊢ri A ⊸ B

  li2ri : {x : Tag} {S : Stp} {Γ : Cxt} {Ω : TCxt x} {C : Pos}
          (f : [ x ] S ∣ Γ ؛ Ω ⊢li C) → 
       ---------------------------------
              [ x ] S ∣ Γ ؛ Ω ⊢ri pos C


data [_]_∣_؛_⊢li_ where
  Il : {Γ : Cxt} {C : Pos}
       (f : [ ∘ ] ─ ∣ Γ ؛ _ ⊢li C) →
    -------------------------
       [ ∘ ] just I ∣ Γ ؛ _ ⊢li C 

  ⊗l : {Γ : Cxt} {A B : Fma} {C : Pos}
       (f : [ ∘ ] just A ∣ B ∷ Γ ؛ _ ⊢li C) →
    -------------------------------------
         [ ∘ ] just (A ⊗ B) ∣ Γ ؛ _ ⊢li C 


  p2li : {x : Tag} {S : Irr} {Γ : Cxt} {Ω : TCxt x} {C : Pos} 
         (f : [ x ] S ∣ Γ ؛ Ω ⊢p C) → 
      ------------------------------------
         [ x ] irr S ∣ Γ ؛ Ω ⊢li C


data [_]_∣_؛_⊢p_ where
  pass : {Γ : Cxt} {A : Fma} {C : Pos}
         (f : [ ∘ ] just A ∣ Γ ؛ _ ⊢li C) →
     ----------------------------------
             [ ∘ ] (─ , _) ∣ A ∷ Γ ؛ _ ⊢p C 

  pass• : {Ω : Cxt} {A : Fma} {C : Pos}
         (f : [ ∘ ] just A ∣ Ω ؛ _ ⊢li C) →
     ----------------------------------
             [ • ] (─ , _) ∣ [] ؛ A ∷ Ω ⊢p C 

  f2p : {x : Tag} {S : Irr} {Γ : Cxt} {Ω : TCxt x} {C : Pos} 
        (f : [ x ] S ∣ Γ ؛ Ω  ⊢f C) → 
      ------------------------------------
                 [ x ] S ∣ Γ ؛ Ω ⊢p C

data [_]_∣_؛_⊢f_ where

  ax : {x : Tag} {X : At} →
       [ x ] (just (` X) , _) ∣ [] ؛ T[] x ⊢f (` X , _)

  Ir : {x : Tag} → [ x ] (─ , _) ∣ [] ؛ T[] x ⊢f (I , _)

  ⊸l : {Γ Δ : Cxt} {A B : Fma} {C : Pos}
        (f : [ ∘ ] ─ ∣ Γ ؛ _ ⊢ri A)
        (g : [ ∘ ] just B ∣ Δ ؛ _ ⊢li C) → 
      -------------------------------------------
         [ ∘ ] (just (A ⊸ B) , _) ∣ Γ ++ Δ ؛ _ ⊢f C

  ⊸l• : {Γ Δ Ω : Cxt} {A B D : Fma} {C : Pos}
        (f : [ ∘ ] ─ ∣ Γ ++ D ∷ Δ ؛ _ ⊢ri A)
        (g : [ ∘ ] just B ∣ Ω ؛ _ ⊢li C) → 
      -------------------------------------------
         [ • ] (just (A ⊸ B) , _) ∣ Γ ؛ D ∷ Δ ++ Ω ⊢f C

  ⊗r : {x : Tag} {S : Irr} {Γ Δ : Cxt} {Ω : TCxt x} {A B : Fma} 
         (f : [ • ] irr S ∣ Γ ؛ [] ⊢ri A)
         (g : [ ∘ ] ─ ∣ Δ ++ tcxt x Ω ؛ _ ⊢ri B) →
     ---------------------------------------------
            [ x ] S ∣ Γ ++ Δ ؛ Ω ⊢f (A ⊗ B , _)

  ⊗r2 : {S : Irr} {Γ Δ Ω : Cxt} {A B D : Fma} 
        (f : [ • ] irr S ∣ Γ ++ D ∷ Δ ؛ [] ⊢ri A)
        (g : [ ∘ ] ─ ∣ Ω ؛ _ ⊢ri B) →
     ---------------------------------------------
        [ • ] S ∣ Γ ؛ D ∷ Δ ++ Ω ⊢f (A ⊗ B , _)

-- We don't display the white phase
_∣_⊢ri_ : Stp → Cxt → Fma → Set
S ∣ Γ ⊢ri C = [ ∘ ] S ∣ Γ ؛ _ ⊢ri C

_∣_⊢li_ : Stp → Cxt → Pos → Set
S ∣ Γ ⊢li C = [ ∘ ] S ∣ Γ ؛ _ ⊢li C

_∣_⊢p_ : Irr → Cxt → Pos → Set
S ∣ Γ ⊢p C = [ ∘ ] S ∣ Γ ؛ _ ⊢p C

_∣_⊢f_ : Irr → Cxt → Pos → Set
S ∣ Γ ⊢f C = [ ∘ ] S ∣ Γ ؛ _ ⊢f C

{- ====================================================== -}

-- Admissible rules

-- Iterated ⊸r and ⊸r•
⊸r⋆-ri : {S : Stp} {Γ : Cxt} (Δ : Cxt) {A : Fma}
      (f : S ∣ Γ ++ Δ ⊢ri A) →
  --------------------------------------------
           S ∣ Γ ⊢ri Δ ⊸⋆ A

⊸r⋆-ri [] f = f
⊸r⋆-ri (A' ∷ Δ) f = ⊸r (⊸r⋆-ri {Γ = _ ∷ʳ A'} Δ f) 

⊸r⋆-ri• : {S : Stp} {Γ Ω : Cxt} (Φ : Cxt) {A : Fma}
      (f : [ • ] S ∣ Γ ؛ Ω ++ Φ ⊢ri A) →
  --------------------------------------------
           [ • ] S ∣ Γ ؛ Ω ⊢ri Φ ⊸⋆ A

⊸r⋆-ri• [] f = f
⊸r⋆-ri• (A' ∷ Δ) f = ⊸r• (⊸r⋆-ri• Δ f)

-- -- Il rule in phase ri
Il-ri : {Γ : Cxt} {C : Fma}
        (f : ─ ∣ Γ ⊢ri C) →
    ------------------------
        just I ∣ Γ ⊢ri C 

Il-ri (⊸r f) = ⊸r (Il-ri f)
Il-ri (li2ri f) = li2ri (Il f)

-- -- ⊗l rule in phase ri
⊗l-ri : {Γ : Cxt} {A B C : Fma}
        (f : just A ∣ B ∷ Γ ⊢ri C) →
      --------------------------------
           just (A ⊗ B) ∣ Γ ⊢ri C 

⊗l-ri (⊸r f) = ⊸r (⊗l-ri f)
⊗l-ri (li2ri f) = li2ri (⊗l f)


-- -- pass rule in phase ri
pass-ri : {Γ : Cxt} {A C : Fma}
          (f : just A ∣ Γ ⊢ri C) →
     --------------------------------
              ─ ∣ A ∷ Γ ⊢ri C 

pass-ri (⊸r f) = ⊸r (pass-ri f)
pass-ri (li2ri f) = li2ri (p2li (pass f))

-- -- Ir rule in phase ri
Ir-ri : ─ ∣ [] ⊢ri I
Ir-ri = li2ri (p2li (f2p Ir))

-- -- ⊸l rule in phase ri
⊸l-ri : {Γ Δ : Cxt} {A B C : Fma} 
        (f : ─ ∣ Γ ⊢ri A) (g : just B ∣ Δ ⊢ri C) →
      ---------------------------------------------
         just (A ⊸ B) ∣ Γ ++ Δ ⊢ri C

⊸l-ri f (⊸r g) = ⊸r (⊸l-ri f g)
⊸l-ri f (li2ri g) = li2ri (p2li (f2p (⊸l f g)))

-- -- Generalization of rule ⊗r in phase ri, proved simultaneusly with
-- -- variants where the 1st premise is in phase li and f
gen⊗r-ri : {S : Stp} {Γ₀ : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A B : Fma}
            (f : S ∣ Γ₀ ++ Γ₁ ⊢ri A) (g :  ─ ∣ Δ ⊢ri B) →
        -----------------------------------------------------------
                    S ∣ Γ₀ ++ Δ ⊢li ((Γ₁ ⊸⋆ A) ⊗ B , _)

gen⊗r-li : {S : Stp} {Γ Δ Γ₀ : Cxt} (Γ₁ : Cxt) {A : Pos} {B : Fma}
            (f : S ∣ Γ ⊢li A) (g :  ─ ∣ Δ ⊢ri B)
            (eq : Γ ≡ Γ₀ ++ Γ₁) →
        ------------------------------------------------------------
                  S ∣ Γ₀ ++ Δ ⊢li ((Γ₁ ⊸⋆ pos A) ⊗ B , _)

gen⊗r-p : {S : Irr} {Γ Δ Γ₀ : Cxt} (Γ₁ : Cxt) {A : Pos} {B : Fma}
            (f :  S ∣ Γ ⊢p A)
            (g :  ─ ∣ Δ ⊢ri B)
            (eq : Γ ≡ Γ₀ ++ Γ₁) →
        ------------------------------------------------------------
                  S ∣ Γ₀ ++ Δ ⊢p ((Γ₁ ⊸⋆ pos A) ⊗ B , _)

gen⊗r-f : {S : Irr} {Γ Δ Γ₀ : Cxt} (Γ₁ : Cxt) {A : Pos} {B : Fma} 
           (f :  S ∣ Γ ⊢f A)
           (g :  ─ ∣ Δ ⊢ri B) 
           (eq : Γ ≡ Γ₀ ++ Γ₁) →
        ------------------------------------------------------------
                  S ∣ Γ₀ ++ Δ ⊢f ((Γ₁ ⊸⋆ pos A) ⊗ B , _)

gen⊗r-ri Γ₁ (⊸r {A = A} f) g = gen⊗r-ri (Γ₁ ∷ʳ A) f g
gen⊗r-ri Γ₁ (li2ri f) g = gen⊗r-li Γ₁ f g refl 

gen⊗r-li Γ₁ (Il f) g eq = Il (gen⊗r-li Γ₁ f g eq)
gen⊗r-li Γ₁ (⊗l f) g eq = ⊗l (gen⊗r-li Γ₁ f g (cong (_ ∷_) eq))
gen⊗r-li Γ₁ (p2li f) g eq = p2li (gen⊗r-p Γ₁ f g eq)

gen⊗r-p Γ₁ (f2p f) g eq = f2p (gen⊗r-f Γ₁ f g eq)
gen⊗r-p {Δ = Δ} {Γ₀ = []} (A' ∷ Γ) (pass f) g refl =
  f2p (⊗r (⊸r⋆-ri• (A' ∷ Γ) (li2ri (p2li (pass• f)))) g)
gen⊗r-p {Γ₀ = A' ∷ Γ₀} Γ₁ (pass f) g refl = pass (gen⊗r-li Γ₁ f g refl)

gen⊗r-f {Γ₀ = Γ₀} Γ₁ (⊸l {Γ} {Δ} f g) h eq with ++? Γ₀ Γ Γ₁ Δ eq
... | inj₁ (Λ , refl , refl) = ⊸l f (gen⊗r-li Γ₁ g h refl)
... | inj₂ (D , Λ , refl , refl) =
  ⊗r (⊸r⋆-ri• (D ∷ Λ ++ Δ) (li2ri (p2li (f2p (⊸l• f g))))) h
gen⊗r-f {Γ₀ = Γ₀} Γ₁ (⊗r {Γ = Γ} {Δ} f g) h eq with ++? Γ₀ Γ Γ₁ Δ eq
gen⊗r-f Γ₁ (⊗r {S = S}{Γ = Γ} f g) h eq | inj₁ (Λ , refl , refl)
  = ⊗r {Γ = Γ ++ Λ} (⊸r⋆-ri• Γ₁ (li2ri (p2li {S = S} (f2p (⊗r f g))))) h
gen⊗r-f ._ (⊗r {S = S} {Δ = Δ} f g) h eq | inj₂ (D , Λ , refl , refl)
  = ⊗r (⊸r⋆-ri• (D ∷ Λ ++ Δ) (li2ri (p2li {S = S} (f2p (⊗r2 f g))))) h
gen⊗r-f {Γ₀ = []} .[] ax g refl = ⊗r (li2ri (p2li (f2p ax))) g
gen⊗r-f {Γ₀ = []} .[] Ir g refl = ⊗r (li2ri (p2li (f2p Ir))) g


-- -- Rule ⊗r in phase li and ri
⊗r-li : {S : Stp} {Γ Δ : Cxt} {A B : Fma}
        (f :  S ∣ Γ  ⊢ri A) (g :  ─ ∣ Δ ⊢ri B) →
      -----------------------------------------
               S ∣ Γ ++ Δ ⊢li (A ⊗ B , _)
⊗r-li f g = gen⊗r-ri [] f g

⊗r-ri : {S : Stp} {Γ Δ : Cxt} {A B : Fma}
        (f :  S ∣ Γ ⊢ri A) (g :  ─ ∣ Δ ⊢ri B) →
      -----------------------------------------
               S ∣ Γ ++ Δ ⊢ri A ⊗ B

⊗r-ri f g = li2ri (⊗r-li f g)

-- -- Rule ax in phase ri
ax-ri : {A : Fma} →  just A ∣ [] ⊢ri A
ax-ri {` X} = li2ri (p2li (f2p ax))
ax-ri {I} = li2ri (Il (p2li (f2p Ir)))
ax-ri {A ⊗ B} = li2ri (⊗l (⊗r-li (ax-ri {A}) (pass-ri (ax-ri {B}))))
ax-ri {A ⊸ B} = ⊸r (⊸l-ri (pass-ri (ax-ri {A})) (ax-ri {B}))


{- ====================================================== -}

-- Soundness and completeness (wrt. derivability)

-- -- The focusing function
focus : {S : Stp} {Γ : Cxt} {C : Fma}
  → S ∣ Γ ⊢ C →  S ∣ Γ ⊢ri C
focus ax = ax-ri
focus (pass f) = pass-ri (focus f)
focus Ir = Ir-ri
focus (Il f) = Il-ri (focus f)
focus (⊗r f g) = ⊗r-ri (focus f) (focus g)
focus (⊗l f) = ⊗l-ri (focus f)
focus (⊸r f) = ⊸r (focus f)
focus (⊸l f g) = ⊸l-ri (focus f) (focus g)

-- -- Embedding
emb-ri : {S : Stp} {Γ : Cxt} {C : Fma}
  →  S ∣ Γ ⊢ri C → S ∣ Γ ⊢ C
emb-ri• : {S : Stp} {Γ Ω : Cxt} {C : Fma}
  → [ • ] S ∣ Γ ؛ Ω ⊢ri C → S ∣ Γ ++ Ω ⊢ C
emb-li : {S : Stp} {Γ : Cxt} {C : Pos}
  →  S ∣ Γ  ⊢li C → S ∣ Γ ⊢ pos C
emb-p : {S : Irr} {Γ : Cxt} {C : Pos}
  →  S ∣ Γ ⊢p C → irr S ∣ Γ ⊢ pos C
emb-p• : {S : Irr} {Γ Ω : Cxt} {C : Pos}
  → [ • ] S ∣ Γ ؛ Ω ⊢p C → irr S ∣ Γ ++ Ω ⊢ pos C
emb-f : {S : Irr} {Γ : Cxt} {C : Pos}
  →  S ∣ Γ ⊢f C → irr S ∣ Γ ⊢ pos C
emb-f• : {S : Irr} {Γ Ω : Cxt} {C : Pos}
  → [ • ] S ∣ Γ ؛ Ω ⊢f C → irr S ∣ Γ ++ Ω ⊢ pos C

emb-ri (⊸r f) = ⊸r (emb-ri f)
emb-ri (li2ri f) = emb-li f

emb-ri• (⊸r• f) = ⊸r (emb-ri• f)
emb-ri• (li2ri (p2li f)) = emb-p• f

emb-li (Il f) = Il (emb-li f)
emb-li (⊗l f) = ⊗l (emb-li f)
emb-li (p2li f) = emb-p f

emb-p (pass f) = pass (emb-li f)
emb-p (f2p f) = emb-f f

emb-p• (pass• f) = pass (emb-li f)
emb-p• (f2p f) = emb-f• f

emb-f ax = ax
emb-f Ir = Ir
emb-f (⊸l f g) = ⊸l (emb-ri f) (emb-li g)
emb-f (⊗r f g) = ⊗r (emb-ri• f) (emb-ri g)

emb-f• (⊸l• f g) = ⊸l (emb-ri f) (emb-li g)
emb-f• ax = ax
emb-f• Ir = Ir
emb-f• (⊗r f g) = ⊗r (emb-ri• f) (emb-ri g)
emb-f• (⊗r2 f g) = ⊗r (emb-ri• f) (emb-ri g)

{- ====================================================== -}

-- Commutative conversions

-- ⊗r commutes with Il
gen⊗rIl-ri : {Γ₀ : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A B : Fma}
            (f :  ─ ∣ Γ₀ ++ Γ₁  ⊢ri A) (g :  ─ ∣ Δ ⊢ri B) →
        -----------------------------------------------------------
              gen⊗r-ri Γ₁ (Il-ri f) g ≡ Il (gen⊗r-ri Γ₁ f g)

gen⊗rIl-ri Γ₁ (⊸r {A = A} f) g = gen⊗rIl-ri (Γ₁ ∷ʳ A) f g
gen⊗rIl-ri Γ₁ (li2ri f) g = refl

⊗rIl-ri : {Γ Δ : Cxt} {A B : Fma}
          (f :  ─ ∣ Γ ⊢ri A) (g :  ─ ∣ Δ ⊢ri B) →
        ------------------------------------------
              ⊗r-ri (Il-ri f) g ≡ Il-ri (⊗r-ri f g)

⊗rIl-ri f g = cong li2ri (gen⊗rIl-ri [] f g)

-- ⊗r commutes with ⊗l
gen⊗r⊗l-ri : {Γ₀ : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A B A' B' : Fma}
            (f :  just A' ∣ B' ∷ Γ₀ ++ Γ₁ ⊢ri A)
            (g :  ─ ∣ Δ ⊢ri B) →
        -----------------------------------------------------------
              gen⊗r-ri Γ₁ (⊗l-ri f) g ≡ ⊗l (gen⊗r-ri Γ₁ f g)

gen⊗r⊗l-ri Γ₁ (⊸r {A = A} f) g = gen⊗r⊗l-ri (Γ₁ ∷ʳ A) f g
gen⊗r⊗l-ri Γ₁ (li2ri f) g = refl

⊗r⊗l-ri : {Γ Δ : Cxt} {A B A' B' : Fma}
          (f :  just A' ∣ B' ∷ Γ ⊢ri A)
          (g :  ─ ∣ Δ ⊢ri B) →
        ------------------------------------------
              ⊗r-ri (⊗l-ri f) g ≡ ⊗l-ri (⊗r-ri f g)

⊗r⊗l-ri f g = cong li2ri (gen⊗r⊗l-ri [] f g)


-- ⊗r commutes with pass
gen⊗rpass-ri : {Γ₀ : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A B A' : Fma}
            (f : just A' ∣ Γ₀ ++ Γ₁ ⊢ri A) (g : ─ ∣ Δ ⊢ri B) →
        -----------------------------------------------------------
            gen⊗r-ri Γ₁ (pass-ri f) g  ≡ p2li (pass (gen⊗r-ri Γ₁ f g))
gen⊗rpass-ri Γ₁ (⊸r {A = A} f) g = gen⊗rpass-ri (Γ₁ ∷ʳ A) f g
gen⊗rpass-ri Γ₁ (li2ri f) g = refl

⊗rpass-ri : {Γ₀ Δ : Cxt} {A B A' : Fma}
            (f : just A' ∣ Γ₀ ⊢ri A) (g : ─ ∣ Δ ⊢ri B) →
        -----------------------------------------------------------
             ⊗r-ri (pass-ri f) g  ≡ pass-ri (⊗r-ri f g)
⊗rpass-ri f g = cong li2ri (gen⊗rpass-ri [] f g)

-- ⊗r commutes with ⊸l
gen⊗r⊸l-ri : {Γ₀ : Cxt} (Γ₁ : Cxt) {Δ Λ : Cxt} {A B A' B' : Fma}
              (f : nothing ∣ Γ₀ ⊢ri A')
              (g : just B' ∣ Δ ++ Γ₁ ⊢ri A)
              (h : ─ ∣ Λ ⊢ri B) →
        -----------------------------------------------------------
              gen⊗r-ri {Γ₀ = Γ₀ ++ Δ} Γ₁ (⊸l-ri f g) h
                 ≡ p2li (f2p (⊸l f (gen⊗r-ri Γ₁ g h)))

gen⊗r⊸l-ri Γ₁ f (⊸r {A = A} g) h = gen⊗r⊸l-ri (Γ₁ ∷ʳ A) f g h
gen⊗r⊸l-ri {Γ₀} Γ₁ {Δ} f (li2ri g) h rewrite ++?-inj₁ Δ Γ₀ Γ₁ = refl

⊗r⊸l-ri : {Γ Δ Λ : Cxt} {A B A' B' : Fma}
           (f : nothing ∣ Γ ⊢ri A')
           (g : just B' ∣ Δ ⊢ri A)
           (h : ─ ∣ Λ ⊢ri B) →
        -----------------------------------------------------------
         ⊗r-ri {Γ = Γ ++ Δ} (⊸l-ri f g) h ≡ ⊸l-ri f (⊗r-ri g h) 

⊗r⊸l-ri f g h = cong li2ri (gen⊗r⊸l-ri [] f g h)

⊸r⋆⊸r-ri• : {S : Stp} {Γ Ω : Cxt} (Δ : Cxt) {A C : Fma}
             (f : [ • ] S ∣ Γ ؛ Ω ++ Δ ∷ʳ A ⊢ri C) →
           --------------------------------------------------
             ⊸r⋆-ri• {Ω = Ω} (Δ ∷ʳ A) f ≡ ⊸r⋆-ri• Δ (⊸r• f)
⊸r⋆⊸r-ri• [] f = refl
⊸r⋆⊸r-ri• (A' ∷ Δ) f = cong ⊸r• (⊸r⋆⊸r-ri• Δ f)

{- ====================================================== -}

-- Equational soundness

eqfocus : {S : Stp} {Γ : Cxt} {C : Fma} → {f f' : S ∣ Γ ⊢ C} →
          f ≗ f' → focus f ≡ focus f'
eqfocus refl = refl
eqfocus (~ p) = sym (eqfocus p)
eqfocus (p ∙ p₁) = trans (eqfocus p) (eqfocus p₁)
eqfocus (pass p) = cong pass-ri (eqfocus p)
eqfocus (Il p) = cong Il-ri (eqfocus p)
eqfocus (⊗l p) = cong ⊗l-ri (eqfocus p)
eqfocus (⊗r p p₁) = cong₂ ⊗r-ri (eqfocus p) (eqfocus p₁)
eqfocus (⊸r p) = cong ⊸r (eqfocus p)
eqfocus (⊸l p p₁) = cong₂ ⊸l-ri (eqfocus p) (eqfocus p₁)
eqfocus axI = refl
eqfocus ax⊗ = refl
eqfocus ax⊸ = refl
eqfocus (⊗rpass {f = f}) = ⊗rpass-ri (focus f) _
eqfocus (⊗rIl {f = f}) = ⊗rIl-ri (focus f) _
eqfocus (⊗r⊗l {f = f}) = ⊗r⊗l-ri (focus f) _
eqfocus (⊗r⊸l {f = f}{g}) = ⊗r⊸l-ri (focus f) (focus g) _
eqfocus ⊸rpass = refl
eqfocus ⊸rIl = refl
eqfocus ⊸r⊗l = refl
eqfocus ⊸r⊸l = refl

{- ====================================================== -}

-- Every seq. calc. derivation is ≗-to the its normal form, i.e.
-- emb-ri (focus f) ≗ f

embpass : {Γ : Cxt} {A C : Fma}
          (f : just A ∣ Γ ⊢ri C) → 
           emb-ri (pass-ri f) ≗ pass (emb-ri f)
embpass (⊸r f) = ⊸r (embpass f) ∙ ⊸rpass
embpass (li2ri f) = refl

embIl : {Γ : Cxt} {C : Fma}
        (f : ─ ∣ Γ ⊢ri C) → 
         emb-ri (Il-ri f) ≗ Il (emb-ri f)
embIl (⊸r f) = ⊸r (embIl f) ∙ ⊸rIl
embIl (li2ri f) = refl

emb⊗l : {Γ : Cxt} {A B C : Fma}
        (f : just A ∣ B ∷ Γ ⊢ri C) → 
         emb-ri (⊗l-ri f) ≗ ⊗l (emb-ri f)
emb⊗l (⊸r f) = ⊸r (emb⊗l f) ∙ ⊸r⊗l
emb⊗l (li2ri f) = refl

emb⊸l : {Γ Δ : Cxt} {A B C : Fma}
         (f : ─ ∣ Γ ⊢ri A) (g : just B ∣ Δ ⊢ri C) → 
         emb-ri (⊸l-ri f g) ≗ ⊸l (emb-ri f) (emb-ri g)
emb⊸l f (⊸r g) = ⊸r (emb⊸l f g) ∙ ⊸r⊸l
emb⊸l f (li2ri g) = refl

emb⊸r⋆ : {S : Stp} {Γ : Cxt} (Δ : Cxt) {C : Fma}
         (f : S ∣ Γ ++ Δ ⊢ri C) → 
         emb-ri (⊸r⋆-ri Δ f) ≗ ⊸r⋆ Δ (emb-ri f)
emb⊸r⋆ [] f = refl
emb⊸r⋆ {Γ = Γ} (A ∷ Δ) f =
  ⊸r (emb⊸r⋆ {Γ = Γ ∷ʳ A} Δ f)

emb⊸r⋆• : {S : Stp} {Γ Ω : Cxt} (Δ : Cxt) {C : Fma}
          (f : [ • ] S ∣ Γ ؛ Ω ++ Δ ⊢ri C) → 
          emb-ri• (⊸r⋆-ri• Δ f) ≗ ⊸r⋆ Δ (emb-ri• f)
emb⊸r⋆• [] f = refl
emb⊸r⋆• {Ω = Ω} (A ∷ Δ) f =
  ⊸r (emb⊸r⋆• {Ω = Ω ∷ʳ A} Δ f) 

embgen⊗r-ri : {S : Stp} {Γ : Cxt} (Γ' : Cxt) {Δ : Cxt} {A B : Fma}
              (f : S ∣ Γ ++ Γ' ⊢ri A) (g : ─ ∣ Δ ⊢ri B) → 
              emb-li (gen⊗r-ri Γ' f g) ≗ ⊗r (⊸r⋆ Γ' (emb-ri f)) (emb-ri g)
embgen⊗r-li : {S : Stp} {Γ₀ : Cxt} (Γ₁ : Cxt) {Γ Δ : Cxt} {A : Pos} {B : Fma}
              (f : S ∣ Γ ⊢li A) (g : ─ ∣ Δ ⊢ri B)
              (eq : Γ ≡ Γ₀ ++ Γ₁) → 
              emb-li (gen⊗r-li Γ₁ f g eq)
                  ≗ ⊗r (⊸r⋆ Γ₁ (emb-li (subst (λ x → S ∣ x ⊢li A) eq f)))
                       (emb-ri g)
embgen⊗r-p : {S : Irr} {Γ₀ : Cxt} (Γ₁ : Cxt) {Γ Δ : Cxt} {A : Pos} {B : Fma}
              (f : S ∣ Γ ⊢p A) (g : ─ ∣ Δ ⊢ri B)
              (eq : Γ ≡ Γ₀ ++ Γ₁) → 
              emb-p (gen⊗r-p Γ₁ f g eq)
                ≗ ⊗r (⊸r⋆ Γ₁ (emb-p (subst (λ x → S ∣ x ⊢p A) eq f)))
                     (emb-ri g) 
embgen⊗r-f : {S : Irr} {Γ₀ : Cxt} (Γ₁ : Cxt) {Γ Δ : Cxt} {A : Pos} {B : Fma}
              (f : S ∣ Γ ⊢f A) (g : ─ ∣ Δ ⊢ri B)
              (eq : Γ ≡ Γ₀ ++ Γ₁) → 
              emb-f (gen⊗r-f Γ₁ f g eq)
                ≗ ⊗r (⊸r⋆ Γ₁ (emb-f (subst (λ x → S ∣ x ⊢f A) eq f)))
                     (emb-ri g)

embgen⊗r-ri Γ' (⊸r {A = A} f) g =
  embgen⊗r-ri (Γ' ∷ʳ A) f g ∙ ⊗r (⊸r⋆⊸r Γ' _) refl
embgen⊗r-ri Γ' (li2ri f) g = embgen⊗r-li Γ' f g refl

embgen⊗r-li Γ₁ (Il f) g refl =
  Il (embgen⊗r-li Γ₁ f g refl)
  ∙ (~ ⊗rIl)
  ∙ ⊗r (~ (⊸r⋆Il Γ₁)) refl
embgen⊗r-li Γ₁ (⊗l f) g refl = 
  ⊗l (embgen⊗r-li Γ₁ f g refl)
  ∙ (~ ⊗r⊗l)
  ∙ ⊗r (~ (⊸r⋆⊗l Γ₁)) refl
embgen⊗r-li Γ₁ (p2li f) g refl = embgen⊗r-p Γ₁ f g refl

embgen⊗r-p {Γ₀ = []} .(_ ∷ _) (pass {Γ} f) g refl 
 = ⊗r (⊸r (emb⊸r⋆• Γ _)) refl
embgen⊗r-p {Γ₀ = A' ∷ Γ₀} Γ₁ (pass f) g refl 
 = pass (embgen⊗r-li Γ₁ f g refl)
   ∙ (~ ⊗rpass)
   ∙ ⊗r (~ (⊸r⋆pass Γ₁)) refl
embgen⊗r-p Γ₁ (f2p f) g refl = embgen⊗r-f Γ₁ f g refl
 
embgen⊗r-f {Γ₀ = Γ₀} Γ₁ (⊸l {Γ} {Δ} f g₁) g eq with ++? Γ₀ Γ Γ₁ Δ eq
embgen⊗r-f Γ₁ (⊸l {Γ} f g₁) g refl | inj₁ (Λ , refl , refl) 
  = ⊸l refl (embgen⊗r-li Γ₁ g₁ g refl)
    ∙ (~ ⊗r⊸l)
    ∙ ⊗r (~ (⊸r⋆⊸l Γ₁)) refl
embgen⊗r-f ._ (⊸l {Δ = Δ} f g₁) g refl | inj₂ (D , Λ , refl , refl)
  = ⊗r (⊸r (emb⊸r⋆• (Λ ++ Δ) _)) refl
embgen⊗r-f {Γ₀ = Γ₀} Γ₁ (⊗r {Γ = Γ} {Δ} f g) h eq with ++? Γ₀ Γ Γ₁ Δ eq
embgen⊗r-f Γ₁ (⊗r f g) h refl | inj₁ (Λ , refl , refl)
  = ⊗r (emb⊸r⋆• Γ₁ _) refl
embgen⊗r-f _ (⊗r {Δ = Δ} f g) h refl | inj₂ (D , Λ , refl , refl)
  = ⊗r (⊸r (emb⊸r⋆• (Λ ++ Δ) _)) refl
embgen⊗r-f {Γ₀ = []} .[] ax g refl = refl
embgen⊗r-f {Γ₀ = []} .[] Ir g refl = refl

emb⊗r : {S : Stp} {Γ Δ : Cxt} {A B : Fma}
        (f : S ∣ Γ ⊢ri A) (g : ─ ∣ Δ ⊢ri B) → 
        emb-ri (⊗r-ri f g) ≗ ⊗r (emb-ri f) (emb-ri g)
emb⊗r f g = embgen⊗r-ri [] f g

embax : {A : Fma} → emb-ri (ax-ri {A}) ≗ ax
embax {` X} = refl
embax {I} = ~ axI
embax {A ⊗ B}
  = ⊗l (emb⊗r ax-ri (pass-ri ax-ri) ∙ ⊗r embax (embpass (ax-ri) ∙ pass embax))
    ∙ ~ ax⊗
embax {A ⊸ B}
  = ⊸r (emb⊸l (pass-ri ax-ri) ax-ri ∙ ⊸l (embpass ax-ri ∙ pass embax) embax)
    ∙ ~ ax⊸

embfocus : {S : Stp} {Γ : Cxt} {C : Fma}
           (f : S ∣ Γ ⊢ C) → 
           emb-ri (focus f) ≗ f
embfocus ax = embax
embfocus (pass f) = embpass (focus f) ∙ pass (embfocus f)
embfocus Ir = refl
embfocus (Il f) = embIl (focus f) ∙ Il (embfocus f)
embfocus (⊗r f g) = emb⊗r (focus f) (focus g) ∙ ⊗r (embfocus f) (embfocus g)
embfocus (⊗l f) = emb⊗l (focus f) ∙ ⊗l (embfocus f)
embfocus (⊸r f) = ⊸r (embfocus f)
embfocus (⊸l f g) = emb⊸l (focus f) (focus g) ∙ ⊸l (embfocus f) (embfocus g)

-- Running the normalization algorithm on a normal form is
-- syntactically equal to the normal form itself, i.e.
-- focus (emb-ri f) ≡ f

ri•2ri : {S : Stp} {Γ Ω : Cxt} {C : Fma}
         (f : [ • ] S ∣ Γ ؛ Ω ⊢ri C) →
         S ∣ Γ ++ Ω ⊢ri C
p•2p : {S : Irr} {Γ Ω : Cxt} {C : Pos}
         (f : [ • ] S ∣ Γ ؛ Ω ⊢p C) →
         S ∣ Γ ++ Ω ⊢p C
f•2f : {S : Irr} {Γ Ω : Cxt} {C : Pos}
         (f : [ • ] S ∣ Γ ؛ Ω ⊢f C) →
         S ∣ Γ ++ Ω ⊢f C

ri•2ri (⊸r• f) = ⊸r (ri•2ri f)
ri•2ri (li2ri (p2li f)) = li2ri (p2li (p•2p f))

p•2p (pass• f) = pass f
p•2p (f2p f) = f2p (f•2f f) 

f•2f (⊸l• f g) = ⊸l f g
f•2f Ir = Ir
f•2f ax = ax
f•2f (⊗r f g) = ⊗r f g
f•2f (⊗r2 f g) = ⊗r f g

gen⊗r-f-eq : {S : Irr} {Γ₀ : Cxt} (Γ₁ : Cxt) {Δ : Cxt} {A : Pos} {B : Fma}
               (f : [ • ] S ∣ Γ₀ ؛ Γ₁ ⊢f A)
               (g : ─ ∣ Δ ⊢ri B) →
               gen⊗r-f Γ₁ (f•2f f) g refl
                    ≡ ⊗r (⊸r⋆-ri• Γ₁ (li2ri (p2li (f2p f)))) g
gen⊗r-f-eq .(T[] •) ax g = refl
gen⊗r-f-eq .(T[] •) Ir g = refl
gen⊗r-f-eq {Γ₀ = Γ₀} .(D ∷ Δ ++ Ω) (⊸l• {Δ = Δ} {Ω} {D = D} f g₁) g
  rewrite ++?-inj₂ Γ₀ Δ Ω D = refl
gen⊗r-f-eq Γ₁ (⊗r {Γ = Γ} {Δ} f g) h
  rewrite ++?-inj₁ Δ Γ Γ₁ = refl 
gen⊗r-f-eq {Γ₀ = Γ₀} .(D ∷ Δ ++ Ω) (⊗r2 {Δ = Δ} {Ω} {D = D} f g) h 
  rewrite ++?-inj₂ Γ₀ Δ Ω D = refl
  
f2p∘ : {S : Irr} {Γ : Cxt} {C : Pos} 
       (f :  S ∣ Γ ⊢f C) → 
    -------------------------
        S ∣ Γ ⊢p C
f2p∘ {─ , _} f = f2p f
f2p∘ {just (` _) , _} f = f2p f
f2p∘ {just (_ ⊸ _) , _} f = f2p f

gen⊗r-ri-eq : {S : Irr} {Γ : Cxt} (Γ' : Cxt) {Δ : Cxt} {A B : Fma}
              (f : [ • ] irr S ∣ Γ ؛ Γ' ⊢ri A) (g : ─ ∣ Δ ⊢ri B) →
              gen⊗r-ri Γ' (ri•2ri f) g
                ≡ p2li {S = S} (f2p (⊗r (⊸r⋆-ri• Γ' f) g))
gen⊗r-p-eq : {S : Irr} {Γ : Cxt} (Γ' : Cxt) {Δ : Cxt} {A : Pos} {B : Fma}
             (f : [ • ] S ∣ Γ ؛ Γ' ⊢p A) (g : ─ ∣ Δ ⊢ri B) →
             gen⊗r-p Γ' (p•2p f) g refl
                ≡ f2p (⊗r (⊸r⋆-ri• Γ' (li2ri (p2li f))) g)
       
gen⊗r-ri-eq Γ' (⊸r• f) g =
  trans (gen⊗r-ri-eq _ f g)
        (cong p2li (cong f2p (cong (λ x → ⊗r x g) (⊸r⋆⊸r-ri• Γ' f)))) 
gen⊗r-ri-eq {─ , _} Γ' (li2ri (p2li f)) g = cong p2li (gen⊗r-p-eq Γ' f g)
gen⊗r-ri-eq {just (` X) , _} Γ' (li2ri (p2li f)) g
  = cong p2li (gen⊗r-p-eq Γ' f g)
gen⊗r-ri-eq {just (A' ⊸ B') , _} Γ' (li2ri (p2li f)) g
  = cong p2li (gen⊗r-p-eq Γ' f g)

gen⊗r-p-eq .(_ ∷ _) (pass• f) g = refl
gen⊗r-p-eq Γ' (f2p f) g = cong f2p (gen⊗r-f-eq Γ' f g)

focusemb-ri : {S : Stp} {Γ : Cxt} {C : Fma}
           (f : S ∣ Γ ⊢ri C) → 
           focus (emb-ri f) ≡ f
focusemb-ri• : {S : Stp} {Γ Ω : Cxt} {C : Fma}
           (f : [ • ] S ∣ Γ ؛ Ω ⊢ri C) → 
           focus (emb-ri• f) ≡ ri•2ri f
focusemb-li : {S : Stp} {Γ : Cxt} {C : Pos}
           (f : S ∣ Γ ⊢li C) → 
           focus (emb-li f) ≡ li2ri f
focusemb-p : {S : Irr} {Γ : Cxt} {C : Pos}
           (f : S ∣ Γ ⊢p C) → 
           focus (emb-p f) ≡ li2ri (p2li f)
focusemb-p• : {S : Irr} {Γ Ω : Cxt} {C : Pos}
           (f : [ • ] S ∣ Γ ؛ Ω ⊢p C) → 
           focus (emb-p• f) ≡ li2ri (p2li (p•2p f))
focusemb-f : {S : Irr} {Γ : Cxt} {C : Pos}
           (f : S ∣ Γ ⊢f C) → 
           focus (emb-f f) ≡ li2ri (p2li (f2p f))
focusemb-f• : {S : Irr} {Γ Ω : Cxt} {C : Pos}
           (f : [ • ] S ∣ Γ ؛ Ω ⊢f C) → 
           focus (emb-f• f) ≡ li2ri (p2li (f2p (f•2f f)))

focusemb-ri (⊸r f) = cong ⊸r (focusemb-ri f)
focusemb-ri (li2ri f) = focusemb-li f

focusemb-ri• (⊸r• f) = cong ⊸r (focusemb-ri• f)
focusemb-ri• (li2ri (p2li f)) = focusemb-p• f

focusemb-li (Il f) = cong Il-ri (focusemb-li f)
focusemb-li (⊗l f) = cong ⊗l-ri (focusemb-li f)
focusemb-li (p2li f) = focusemb-p f

focusemb-p (pass f) = cong pass-ri (focusemb-li f)
focusemb-p (f2p f) = focusemb-f f

focusemb-p• (pass• f) = cong pass-ri (focusemb-li f)
focusemb-p• (f2p f) = focusemb-f• f 

focusemb-f ax = refl
focusemb-f Ir = refl
focusemb-f (⊸l f g) = cong₂ ⊸l-ri (focusemb-ri f) (focusemb-li g)
focusemb-f (⊗r f g) =
  cong li2ri (trans (cong₂ ⊗r-li (focusemb-ri• f) (focusemb-ri g))
                    (gen⊗r-ri-eq [] f g)) 

focusemb-f• ax = refl
focusemb-f• Ir = refl
focusemb-f• (⊸l• f g) = cong₂ ⊸l-ri (focusemb-ri f) (focusemb-li g)
focusemb-f• (⊗r f g) = 
  cong li2ri (trans (cong₂ ⊗r-li (focusemb-ri• f) (focusemb-ri g))
                    (gen⊗r-ri-eq [] f g))
focusemb-f• (⊗r2 f g) = 
  cong li2ri (trans (cong₂ ⊗r-li (focusemb-ri• f) (focusemb-ri g))
                    (gen⊗r-ri-eq [] f g))


{-
t : {X Y : At}
  → just ((` X ⊸ ` X) ⊸ (` X ⊸ ` Y)) ∣ ` X ⊸ ` X ∷ ` X ∷ [] ⊢ri ` Y
t {X} {Y} = li2ri (p2li (f2p⊸
  (⊸l {` X ⊸ ` X ∷ []}
      (⊸r (li2ri (p2li (pass (p2li (f2p⊸
        (⊸l {` X ∷ []}
            (li2ri (p2li (pass (p2li (f2p ax)))))
            (p2li (f2p ax)))))))))
     (p2li (f2p⊸
        (⊸l {` X ∷ []}
             (li2ri (p2li (pass (p2li (f2p ax)))))
             (p2li (f2p ax))))))))

t' : {X Y : At}
  → just ((` X ⊸ ` X) ⊸ (` X ⊸ ` Y)) ∣ ` X ⊸ ` X ∷ ` X ∷ [] ⊢ri ` Y
t' {X} {Y} = li2ri (p2li (f2p⊸
  (⊸l {[]}
       (⊸r (li2ri (p2li (pass (p2li (f2p ax))))))
       (p2li (f2p⊸
         (⊸l {_} {[]}
              (li2ri (p2li (pass (p2li (f2p⊸
                (⊸l (li2ri (p2li (pass (p2li (f2p ax))))) (p2li (f2p ax))))))))
              (p2li (f2p ax))))))))

-}
