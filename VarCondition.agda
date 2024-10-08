{-# OPTIONS --rewriting #-}

module VarCondition where

open import Function
open import Data.Empty
open import Data.Maybe renaming (map to mmap)
open import Data.Sum hiding (reduce)
open import Data.List as List
open import Data.List.Relation.Unary.All
open import Relation.Unary hiding (_∈_;_∖_)
open import Data.Product
open import Relation.Binary.PropositionalEquality as PE hiding (_≗_) hiding ([_])
open ≡-Reasoning
open import Utilities
open import Formulae
open import SeqCalc 
open import Equations
open import Interpolation

infixr 6 _∖_
infix 3 _≲_
infixl 3 _∙≲_

_∖_ : {A : Set} (xs : List A) {x : A} → x ∈ xs → List A
(x ∷ xs) ∖ here = xs
(x ∷ xs) ∖ there m = x ∷ xs ∖ m

data _≲_ {A : Set} : (xs ys : List A) → Set where
  []≲ : ∀ {ys} → [] ≲ ys
  ∷≲ : ∀ {xs ys x} (m : x ∈ ys)
    → xs ≲ ys ∖ m 
    → x ∷ xs ≲ ys

refl≲ : ∀ {A} (xs : List A) → xs ≲ xs
refl≲ [] = []≲
refl≲ (x ∷ xs) = ∷≲ here (refl≲ xs)

≡≲ : ∀ {A} {xs ys : List A} → xs ≡ ys → xs ≲ ys
≡≲ refl = refl≲ _

∈∖ : ∀ {A} {ys : List A} {x y} (m : y ∈ ys)
  → x ∈ ys ∖ m → x ∈ ys
∈∖ here m' = there m'
∈∖ (there m) here = here
∈∖ (there m) (there m') = there (∈∖ m m')

∈∖∖ : ∀ {A} {ys : List A} {x y}
  → (m : y ∈ ys) (m' : x ∈ ys ∖ m)
  → y ∈ ys ∖ (∈∖ m m')
∈∖∖ here m' = here
∈∖∖ (there m) here = m
∈∖∖ (there m) (there m') = there (∈∖∖ m m')

∖∖≡ : ∀ {A} {ys : List A} {x y}
  → (m : y ∈ ys) (m' : x ∈ ys ∖ m)
  → (ys ∖ m) ∖ m' ≡ (ys ∖ ∈∖ m m') ∖ ∈∖∖ m m'
∖∖≡ here m' = refl
∖∖≡ (there m) here = refl
∖∖≡ (there m) (there {x = x} m') = cong (x ∷_) (∖∖≡ m m')

mem≲ : ∀ {A} {xs ys : List A} {x}
  → (m : x ∈ xs) → xs ≲ ys
  → Σ (x ∈ ys) λ m' → xs ∖ m ≲ ys ∖ m'
mem≲ here (∷≲ m' p) = m' , p
mem≲ (there m) (∷≲ m' p) with mem≲ m p
... | m'' , p' = (∈∖ m' m'') , ∷≲ (∈∖∖ m' m'') (subst (λ z → _ ∖ m ≲ z) (∖∖≡ m' m'') p')

trans≲ : ∀ {A} {xs ys zs : List A} → xs ≲ ys → ys ≲ zs → xs ≲ zs
trans≲ []≲ q = []≲
trans≲ (∷≲ m p) q = ∷≲ (mem≲ m q .proj₁) (trans≲ p (mem≲ m q .proj₂))

_∙≲_ = trans≲

∖++₁ : ∀ {A} {ys : List A} zs {x} (m : x ∈ ys)
  → (ys ∖ m) ++ zs ≡ (ys ++ zs) ∖ ∈₁ ys zs m
∖++₁ zs here = refl
∖++₁ zs (there {x} m) = cong (x ∷_) (∖++₁ zs m)

∖++₂ : ∀ {A} ys {zs : List A} {x} (m : x ∈ zs)
  → ys ++ (zs ∖ m) ≡ (ys ++ zs) ∖ ∈₂ ys zs m
∖++₂ [] m = refl
∖++₂ (x ∷ ys) m = cong (x ∷_) (∖++₂ ys m)

≲++₁ : ∀ {A} {xs ys zs : List A} → xs ≲ ys → xs ≲ ys ++ zs
≲++₁ []≲ = []≲
≲++₁ {ys = ys} {zs} (∷≲ {xs} m p) = ∷≲ (∈₁ ys zs m) (subst (xs ≲_) (∖++₁ zs m) (≲++₁ {zs = zs} p) )

≲++₂ : ∀ {A} {xs ys zs : List A} → xs ≲ zs → xs ≲ ys ++ zs
≲++₂ []≲ = []≲
≲++₂ {ys = ys} (∷≲ {xs = xs} {zs} m p) = ∷≲ (∈₂ ys zs m) (subst (xs ≲_) (∖++₂ ys m) (≲++₂ p))

++≲ : ∀ {A} {xs ys zs ws : List A} → xs ≲ ys → ws ≲ zs → xs ++ ws ≲ ys ++ zs
++≲ []≲ q = ≲++₂ q
++≲ {zs = zs}{ws} (∷≲ {xs = xs}{ys} m p) q = ∷≲ (∈₁ _ zs m) (subst (xs ++ ws ≲_) (∖++₁ zs m) (++≲ p q))

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

atom⊸⋆≡ : ∀ (Γ : Cxt) {C} → atom (Γ ⊸⋆ C) ≡ atom-c Γ ++ atom C
atom⊸⋆≡ [] = refl
atom⊸⋆≡ (A ∷ Γ) = cong (atom A ++_) (atom⊸⋆≡ Γ)

-- ∈atom⊸⋆ : ∀{X} (Γ : Cxt) {C} → X ∈ atom (Γ ⊸⋆ C) → X ∈ atom-c Γ ⊎ X ∈ atom C
-- ∈atom⊸⋆ [] m = inj₂ m
-- ∈atom⊸⋆ (A ∷ Γ) {C} m with ∈++ (atom A) (atom (Γ ⊸⋆ C)) m
-- ... | inj₁ m' = inj₁ (∈₁ (atom A) (atom-c Γ) m')
-- ... | inj₂ m' with ∈atom⊸⋆ Γ m'
-- ... | inj₁ m'' = inj₁ (∈₂ (atom A) (atom-c Γ) m'')
-- ... | inj₂ m'' = inj₂ m''

{-
The variable conditions:

sVar collects variable conditions:
- a map from occurrences of atoms in D to occurrences of atoms in S,Γ
- a map from occurrences of atoms in D to occurrences of atoms in Δ,C

cVar collects variable conditions:
- a map from occurrences of atoms in D₁,...,Dₙ to occurrences of atoms in S,Δ₀,Δ₁,C
- a map from occurrences of atoms in D₁,...,Dₙ to occurrences of atoms in Γ₁,...,Γₙ
-}

record sVar S Γ₁ Γ₂ C D : Set where
  constructor v-s
  field
    atom-g : atom D ≲ atom-s S ++ atom-c Γ₁
    atom-h : atom D ≲ atom-c Γ₂ ++ atom C

record cVar S Γ₀ Γ₁ Γ₂ C Ds : Set where
  constructor v-c
  field
    atom-Ξ : atom-c Ds ≲ atom-c Γ₁
    atom-g : atom-c Ds ≲ atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C

-- record sVar S Γ₁ Γ₂ C D : Set where
--   constructor v-s
--   field
--     atom-g : ∀{X} → X ∈ atom D → X ∈ atom-s S ++ atom-c Γ₁
--     atom-h : ∀{X} → X ∈ atom D → X ∈ atom-c Γ₂ ++ atom C

-- record cVar S Γ₀ Γ₁ Γ₂ C Ds : Set where
--   constructor v-c
--   field
--     atom-Ξ : ∀{X} → X ∈ atom-c Ds → X ∈ atom-c Γ₁
--     atom-g : ∀{X} → X ∈ atom-c Ds → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C

-- Proof that the produced interpolants satisfy the variable conditions
svar : ∀ {S} Γ₁ Γ₂ {Γ C}
  → (f : S ∣ Γ ⊢ C) 
  → (eq : Γ ≡ Γ₁ ++ Γ₂)
  → sVar S Γ₁ Γ₂ C (sIntrp.D (sintrp Γ₁ Γ₂ f eq))
cvar : ∀{S} Γ₀ Γ₁ Γ₂ {Γ C}
  → (f : S ∣ Γ ⊢ C)
  → (eq : Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂)
  → cVar S Γ₀ Γ₁ Γ₂ C (cIntrp.Ds (cintrp Γ₀ Γ₁ Γ₂ f eq))

svar Γ₁ Γ₂ (Il f) refl with svar Γ₁ Γ₂ f refl
... | v-s ag ah = v-s ag ah
svar Γ₁ Γ₂ (⊗l f) refl with svar (_ ∷ Γ₁) Γ₂ f refl
... | v-s ag ah = v-s ag ah
svar Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with svar Γ₁ (Γ₂ ∷ʳ A) f refl
... | v-s ag ah = v-s ag (ah
                          ∙≲ ≡≲ (cong (λ x → x ++ atom B) {y = atom-c Γ₂ ++ atom A} (concat++ (List.map atom Γ₂) [ _ ])))
svar Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
svar {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (Γ' , refl , refl) with svar Γ [] f refl | svar Γ' Γ₂ g refl
... | v-s ag ah | v-s ak al =
  v-s (++≲ ag ak
       ∙≲ ≡≲ (sym (cong (atom-s S ++_) (concat++ (List.map atom Γ) (List.map atom Γ')))))
       (++≲ ah al
       ∙≲ ++≲ {xs = atom A ++ atom-c Γ₂} {atom-c Γ₂ ++ atom A} {!!} (refl≲ (atom B)))
svar Γ₁ _ (⊗r {Γ = _} {Δ = Δ} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) with svar Γ₁ (_ ∷ Γ') f refl
... | v-s ag ak =
  v-s ag
      (ak
       ∙≲ ++≲ {zs = atom-c (Γ' ++ Δ) ++ atom A ++ atom B} {atom-c Γ' ++ atom A} (refl≲ (atom A'))
              (≲++₁ {ys = atom-c (Γ' ++ Δ) ++ atom A} {atom B}
                    (++≲ {xs = atom-c Γ'}{atom-c (Γ' ++ Δ)} (subst (atom-c Γ' ≲_) (sym (concat++ (List.map atom Γ') (List.map atom Δ))) (≲++₁ {zs = atom-c Δ} (refl≲ (atom-c Γ'))))
                                                            (refl≲ (atom A)))))
svar Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ Γ₁ Δ Γ₂ (sym eq)
svar Γ₁ .(Γ' ++ Δ) (⊸l {_} {Δ = Δ} {A}{B}{C} f g) refl | inj₁ (Γ' , refl , refl) with svar [] Δ g refl | cvar Γ₁ Γ' [] f refl
... | v-s ah ak | v-c ahs al =
  v-s
    (≡≲ (atom⊸⋆≡ (cintrp Γ₁ Γ' [] f refl .cIntrp.Ds))
     ∙≲ ++≲ al ah
     ∙≲ {!!})
    (≡≲ (atom⊸⋆≡ (cintrp Γ₁ Γ' [] f refl .cIntrp.Ds))
     ∙≲ ++≲ ahs ak
     ∙≲ ≡≲ (sym (cong (_++ atom C) {y = atom-c Γ' ++ atom-c Δ} (concat++ (List.map atom Γ') (List.map atom Δ)))))
svar _ Γ₂ (⊸l {Γ} {_} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) with svar (A' ∷ Γ') Γ₂ g refl
... | v-s ah ak =
  v-s (ah
       ∙≲ ≲++₂ {ys = atom A} {atom B ++ atom-c (Γ ++ A'  ∷ Γ')}
               (++≲ {zs = atom-c (Γ ++ A' ∷ Γ')}{atom-c (A' ∷ Γ')} (refl≲ (atom B))
                    (subst (atom-c (A' ∷ Γ') ≲_) (sym (concat++ (List.map atom Γ) (List.map atom (A' ∷ Γ')))) (≲++₂ {ys = atom-c Γ} (refl≲ (atom-c (A' ∷ Γ')))))))
      ak
svar [] [] ax refl = v-s (refl≲ _) (refl≲ _)
svar [] (A ∷ Γ₂) (pass f) refl = v-s []≲ []≲
svar (A ∷ Γ₁) Γ₂ (pass f) refl with svar Γ₁ Γ₂ f refl
... | v-s ah ak = v-s ah ak
svar [] [] Ir refl = v-s []≲ []≲

-- svar Γ₁ Γ₂ (Il f) refl with svar Γ₁ Γ₂ f refl
-- ... | v-s ag ah = v-s ag ah
-- svar Γ₁ Γ₂ (⊗l f) refl with svar (_ ∷ Γ₁) Γ₂ f refl
-- ... | v-s ag ah = v-s ag ah
-- svar Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with svar Γ₁ (Γ₂ ∷ʳ A) f refl
-- ... | v-s ag ah = v-s ag ah'
--   where
--     ah' : ∀{X} → X ∈ atom (sIntrp.D (sintrp Γ₁ (Γ₂ ++ A ∷ []) f refl)) → X ∈ atom-c Γ₂ ++ atom A ++ atom B
--     ah' m with ∈++ (atom-c (Γ₂ ∷ʳ A)) (atom B) (ah m)
--     ... | inj₁ m' = ∈₁ (atom-c Γ₂ ++ atom A) (atom B) (subst (λ x → _ ∈ x) (concat++ (List.map atom Γ₂) [ atom A ]) m')
--     ... | inj₂ m' = ∈₂ (atom-c Γ₂ ++ atom A) (atom B) m'
-- svar Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
-- svar {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (Γ' , refl , refl) with svar Γ [] f refl | svar Γ' Γ₂ g refl
-- ... | v-s ag ah | v-s ak al = v-s ag' ah'
--   where
--     ag' : ∀{X} → X ∈ atom (sIntrp.D (sintrp Γ [] f refl)) ++ atom (sIntrp.D (sintrp Γ' Γ₂ g refl))
--                → X ∈ atom-s S ++ atom-c (Γ ++ Γ')
--     ag' m with ∈++ (atom (sIntrp.D (sintrp Γ [] f refl))) (atom (sIntrp.D (sintrp Γ' Γ₂ g refl))) m
--     ... | inj₂ m' = ∈₂ (atom-s S) (atom-c (Γ ++ Γ')) (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ) (List.map atom Γ'))) (∈₂ (atom-c Γ) (atom-c Γ') (ak m')))
--     ... | inj₁ m' with ∈++ (atom-s S) (atom-c Γ) (ag m')
--     ... | inj₁ m'' = ∈₁ (atom-s S) (atom-c (Γ ++ Γ')) m''
--     ... | inj₂ m'' = ∈₂ (atom-s S) (atom-c (Γ ++ Γ')) (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ) (List.map atom Γ'))) (∈₁ (atom-c Γ) (atom-c Γ') m''))

--     ah' : ∀{X} → X ∈ atom (sIntrp.D (sintrp Γ [] f refl)) ++ atom (sIntrp.D (sintrp Γ' Γ₂ g refl))
--                → X ∈ atom-c Γ₂ ++ atom A ++ atom B
--     ah' m with ∈++ (atom (sIntrp.D (sintrp Γ [] f refl))) (atom (sIntrp.D (sintrp Γ' Γ₂ g refl))) m
--     ... | inj₁ m' = ∈₂ (atom-c Γ₂) (atom A ++ atom B) (∈₁ (atom A) (atom B) (ah m'))
--     ... | inj₂ m' with ∈++ (atom-c Γ₂) (atom B) (al m')
--     ... | inj₁ m'' = ∈₁ (atom-c Γ₂) (atom A ++ atom B) m''
--     ... | inj₂ m'' = ∈₂ (atom-c Γ₂ ++ atom A) (atom B) m''
-- svar Γ₁ _ (⊗r {Γ = _} {Δ = Δ} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) with svar Γ₁ (_ ∷ Γ') f refl
-- ... | v-s ag ak = v-s ag ak'
--   where
--     ak' : ∀{X} → X ∈ atom (sIntrp.D (sintrp Γ₁ (A' ∷ Γ') f refl))
--                 → X ∈ atom A' ++ atom-c (Γ' ++ Δ) ++ atom A ++ atom B
--     ak' m with ∈++ (atom A') (atom-c Γ' ++ atom A) (ak m)
--     ... | inj₁ m' = ∈₁ (atom A') (atom-c (Γ' ++ Δ) ++ atom A ++ atom B) m'
--     ... | inj₂ m' with ∈++ (atom-c Γ') (atom A) m'
--     ... | inj₁ m'' =
--       ∈₂ (atom A') (atom-c (Γ' ++ Δ) ++ atom A ++ atom B)
--         (∈₁ (atom-c (Γ' ++ Δ)) (atom A ++ atom B)
--           (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ') (List.map atom Δ))) (∈₁ (atom-c Γ') (atom-c Δ) m'')))
--     ... | inj₂ m'' = ∈₂ (atom A' ++ atom-c (Γ' ++ Δ)) (atom A ++ atom B) (∈₁ (atom A) (atom B) m'')
-- svar Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ Γ₁ Δ Γ₂ (sym eq)
-- svar Γ₁ .(Γ' ++ Δ) (⊸l {_} {Δ = Δ} {A}{B}{C} f g) refl | inj₁ (Γ' , refl , refl) with svar [] Δ g refl | cvar Γ₁ Γ' [] f refl
-- ... | v-s ah ak | v-c ahs al = v-s ah' ak'
--   where
--     ah' : ∀{X} → X ∈ atom (cIntrp.Ds (cintrp Γ₁ Γ' [] f refl) ⊸⋆ sIntrp.D (sintrp [] Δ g refl))
--                → X ∈ atom A ++ atom B ++ atom-c Γ₁
--     ah' m with ∈atom⊸⋆ (cIntrp.Ds (cintrp Γ₁ Γ' [] f refl)) m
--     ... | inj₂ m' = ∈₁ (atom A ++ atom B) (atom-c Γ₁) (∈₂ (atom A) (atom B) (ah m'))
--     ... | inj₁ m' with ∈++ (atom-c Γ₁) (atom A) (al m')
--     ... | inj₁ m'' = ∈₂ (atom A ++ atom B) (atom-c Γ₁) m''
--     ... | inj₂ m'' = ∈₁ (atom A) (atom B ++ atom-c Γ₁) m''

--     ak' : ∀{X} → X ∈ atom (cIntrp.Ds (cintrp Γ₁ Γ' [] f refl) ⊸⋆ sIntrp.D (sintrp [] Δ g refl))
--                → X ∈ atom-c (Γ' ++ Δ) ++ atom C
--     ak' m with ∈atom⊸⋆ (cIntrp.Ds (cintrp Γ₁ Γ' [] f refl)) m
--     ... | inj₂ m' = 
--        subst (λ x → _ ∈ x ++ atom C) (sym (concat++ (List.map atom Γ') (List.map atom Δ)))
--           (∈₂ (atom-c Γ') (atom-c Δ ++ atom C) (ak m'))
--     ... | inj₁ m' = 
--       ∈₁ (atom-c (Γ' ++ Δ)) (atom C)
--         (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ') (List.map atom Δ)))
--           (∈₁ (atom-c Γ') (atom-c Δ) (ahs m')))
-- svar _ Γ₂ (⊸l {Γ} {_} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) with svar (A' ∷ Γ') Γ₂ g refl
-- ... | v-s ah ak = v-s ah' ak
--   where
--     ah' : ∀{X} → X ∈ atom (sIntrp.D (sintrp (A' ∷ Γ') Γ₂ g refl)) → X ∈ atom A ++ atom B ++ atom-c (Γ ++ A' ∷ Γ')
--     ah' m with ∈++ (atom B) (atom-c (A' ∷ Γ')) (ah m)
--     ... | inj₁ m' = ∈₁ (atom A ++ atom B) (atom-c (Γ ++ A' ∷ Γ')) (∈₂ (atom A) (atom B) m')
--     ... | inj₂ m' =
--       ∈₂ (atom A ++ atom B) (atom-c (Γ ++ A' ∷ Γ'))
--         (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ) (List.map atom (A' ∷ Γ')))) (∈₂ (atom-c Γ) (atom-c (A' ∷ Γ')) m'))
-- svar [] [] ax refl = v-s id id
-- svar [] (A ∷ Γ₂) (pass f) refl = v-s id (λ ())
-- svar (A ∷ Γ₁) Γ₂ (pass f) refl with svar Γ₁ Γ₂ f refl
-- ... | v-s ah ak = v-s ah ak
-- svar [] [] Ir refl = v-s id id

-- cvar Γ₀ Γ₁ Γ₂ (Il f) refl with cvar Γ₀ Γ₁ Γ₂ f refl
-- ... | v-c ahs ag = v-c ahs ag
-- cvar Γ₀ Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
-- cvar {S} .(Γ ++ Γ₀) Γ₁ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (Γ₀ , refl , refl) with cvar Γ₀ Γ₁ Γ₂ g refl
-- ... | v-c ags ah = v-c ags ah'
--   where
--     ah' : ∀{X} → X ∈ atom-c (cIntrp.Ds (cintrp Γ₀ Γ₁ Γ₂ g refl))
--                → X ∈ atom-s S ++ atom-c (Γ ++ Γ₀) ++ atom-c Γ₂ ++ atom A ++ atom B
--     ah' m with ∈++ (atom-c Γ₀) (atom-c Γ₂ ++ atom B) (ah m)
--     ... | inj₁ m' =
--       ∈₁ (atom-s S ++ atom-c (Γ ++ Γ₀)) (atom-c Γ₂ ++ atom A ++ atom B)
--         (∈₂ (atom-s S) (atom-c (Γ ++ Γ₀)) (subst (λ x → _ ∈ x) (sym (concat++ (List.map atom Γ) (List.map atom Γ₀))) (∈₂ (atom-c Γ) (atom-c Γ₀) m')))
--     ... | inj₂ m' with ∈++ (atom-c Γ₂) (atom B) m'
--     ... | inj₁ m'' = ∈₂ (atom-s S ++ atom-c (Γ ++ Γ₀)) (atom-c Γ₂ ++ atom A ++ atom B) (∈₁  (atom-c Γ₂) (atom A ++ atom B) m'')
--     ... | inj₂ m'' = ∈₂ (atom-s S ++ atom-c (Γ ++ Γ₀) ++ atom-c Γ₂ ++ atom A) (atom B) m''
-- cvar Γ₀ [] _ (⊗r f g) refl | inj₂ (A , Γ₁ , refl , refl) = v-c id (λ ())
-- cvar Γ₀ (A ∷ Γ₁) Γ₂ (⊗r {Δ = Δ} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
-- ... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
-- cvar {S} Γ₀ (A ∷ Γ₁) _ (⊗r {Δ = Δ}{A₁}{B₁} f g) refl | inj₂ (A , ._ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) with cvar Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
-- ... | v-c ags ah = v-c ags (ah' ∘ ah)
--   where
--     ah' : ∀{X}
--       → X ∈ atom-s S ++ atom-c Γ₀ ++ atom A' ++ atom-c Γ₂ ++ atom A₁
--       → X ∈ atom-s S ++ atom-c Γ₀ ++ atom A' ++ atom-c (Γ₂ ++ Δ) ++ atom A₁ ++ atom B₁
--     ah' m with ∈++ (atom-s S ++ atom-c Γ₀ ++ atom A' ++ atom-c Γ₂) (atom A₁) m
--     ... | inj₁ m' =
--       ∈₁ (atom-s S ++ atom-c Γ₀ ++ atom A' ++ atom-c (Γ₂ ++ Δ)) (atom A₁ ++ atom B₁)
--         (subst (λ x → _ ∈ atom-s S ++ atom-c Γ₀ ++ atom A' ++ x) (sym (concat++ (List.map atom Γ₂) (List.map atom Δ)))
--           (∈₁ (atom-s S ++ atom-c Γ₀ ++ atom A' ++ atom-c Γ₂) (atom-c Δ) m'))
--     ... | inj₂ m' = ∈₂ (atom-s S ++ atom-c Γ₀ ++ atom A' ++ atom-c (Γ₂ ++ Δ)) (atom A₁ ++ atom B₁) (∈₁ (atom A₁) (atom B₁) m')
-- cvar Γ₀ (A ∷ _) Γ₂ (⊗r f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁ , refl , refl) with cvar Γ₀ (_ ∷ Γ') [] f refl | cvar [] Γ₁ Γ₂ g refl
-- cvar {S} Γ₀ (A ∷ _) Γ₂ (⊗r {A = A₁}{B} f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁@_ , refl , refl) | v-c a-Ξf a-h | v-c a-Ξg a-k = 
--   v-c a-Ξ a-h'
--   where
--     a-Ξ : ∀{X} → X ∈ atom-c (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl) ++ cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl))
--                → X ∈ atom-c (A ∷ Γ' ++ Γ₁)
--     a-Ξ m with ∈++ (atom-c (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl)))
--                    (atom-c (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))
--                    (subst (λ x → _ ∈ x) (concat++ (List.map atom (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl))) (List.map atom (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))) m)
--     ... | inj₁ m' = 
--        subst (λ x → _ ∈ x) (sym (concat++ (List.map atom (A ∷ Γ')) (List.map atom Γ₁)))
--          (∈₁ (atom-c (A ∷ Γ')) (atom-c Γ₁) (a-Ξf m'))
--     ... | inj₂ m' = 
--        subst (λ x → _ ∈ x) (sym (concat++ (List.map atom (A ∷ Γ')) (List.map atom Γ₁)))
--          (∈₂ (atom-c (A ∷ Γ')) (atom-c Γ₁) (a-Ξg m'))

--     a-h' : ∀{X} → X ∈ atom-c (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl) ++ cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)) → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom A₁ ++ atom B
--     a-h' m with ∈++ (atom-c (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl)))
--                     (atom-c (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))
--                     (subst (λ x → _ ∈ x) (concat++ (List.map atom (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl))) (List.map atom (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))) m)
--     a-h' m | inj₂ m' with ∈++ (atom-c Γ₂) (atom B) (a-k m')
--     ... | inj₁ m'' = ∈₁ (atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂) (atom A₁ ++ atom B) (∈₂ (atom-s S ++ atom-c Γ₀) (atom-c Γ₂) m'')
--     ... | inj₂ m'' = ∈₂ (atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom A₁) (atom B) m''
--     a-h' m | inj₁ m' with ∈++ (atom-s S ++ atom-c Γ₀) (atom A₁) (a-h m')
--     ... | inj₁ m'' = ∈₁ (atom-s S ++ atom-c Γ₀) (atom-c Γ₂ ++ atom A₁ ++ atom B) m''
--     ... | inj₂ m'' = ∈₂ (atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂) (atom A₁ ++ atom B) (∈₁ (atom A₁) (atom B) m'')
-- cvar Γ₀ Γ₁ Γ₂ (⊗l f) refl with cvar (_ ∷ Γ₀) Γ₁ Γ₂ f refl
-- ... | v-c ahs ag = v-c ahs ag
-- cvar {S} Γ₀ Γ₁ Γ₂ (⊸r {A = A}{B} f) refl with cvar Γ₀ Γ₁ (Γ₂ ∷ʳ A) f refl
-- ... | v-c ahs ag = v-c ahs (a-h' ∘ ag)
--   where
--     a-h' : ∀{X}
--       → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c (Γ₂ ∷ʳ A) ++ atom B
--       → X ∈ atom-s S ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom A ++ atom B
--     a-h' m = subst (λ x → _ ∈ atom-s S ++ atom-c Γ₀ ++ x ++ atom B) (concat++ (List.map atom Γ₂) [ atom A ]) m  
-- cvar Γ₀ Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
-- cvar _ Γ₁ Γ₂ (⊸l {Γ} f g) refl | inj₁ (Γ₀ , refl , refl) with cvar Γ₀ Γ₁ Γ₂ g refl
-- cvar _ _ Γ₂ (⊸l {Γ} {A = A}{B}{C} f g) refl | inj₁ (Γ₀ , refl , refl) | v-c a-Ξ a-h = 
--   v-c a-Ξ (a-h' ∘ a-h) 
--   where
--     a-h' : ∀{X}
--       → X ∈ atom B ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C
--       → X ∈ atom A ++ atom B ++ atom-c (Γ ++ Γ₀) ++ atom-c Γ₂ ++ atom C
--     a-h' m with ∈++ (atom B) (atom-c Γ₀ ++ atom-c Γ₂ ++ atom C) m
--     ... | inj₁ m' = ∈₁ (atom A ++ atom B) (atom-c (Γ ++ Γ₀) ++ atom-c Γ₂ ++ atom C) (∈₂ (atom A) (atom B) m')
--     ... | inj₂ m' =
--       ∈₂ (atom A ++ atom B) (atom-c (Γ ++ Γ₀) ++ atom-c Γ₂ ++ atom C)
--         (subst (λ x → _ ∈ x ++ atom-c Γ₂ ++ atom C) (sym (concat++ (List.map atom Γ) (List.map atom Γ₀)))
--           (∈₂ (atom-c Γ) (atom-c Γ₀ ++ atom-c Γ₂ ++ atom C) m'))
-- cvar Γ₀ [] _ (⊸l f g) refl | inj₂ (B , Γ' , refl , refl) = v-c (λ ()) (λ ())
-- cvar Γ₀ (A ∷ Γ₁) Γ₂ (⊸l {Δ = Δ} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
-- ... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
-- cvar Γ₀ (A ∷ Γ₁) _ (⊸l {Δ = Δ} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) with cvar Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl
-- cvar Γ₀ (A ∷ Γ₁) _ (⊸l {Δ = Δ} {A₁}{B₁}{C} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) | v-c a-Ξ a-h = 
--   v-c a-Ξ (a-h' ∘ a-h)
--   where
--     a-h' : ∀{X}
--       → X ∈ atom-c Γ₀ ++ atom A' ++ atom-c Γ₂ ++ atom A₁
--       → X ∈ atom A₁ ++ atom B₁ ++ atom-c Γ₀ ++ atom A' ++ atom-c (Γ₂ ++ Δ) ++ atom C
--     a-h' m with ∈++ (atom-c Γ₀ ++ atom A' ++ atom-c Γ₂) (atom A₁) m
--     ... | inj₁ m' =
--       subst (λ x → _ ∈ atom A₁ ++ atom B₁ ++ atom-c Γ₀ ++ atom A' ++ x ++ atom C) (sym (concat++ (List.map atom Γ₂) (List.map atom Δ)))
--         (∈₁ (atom A₁ ++ atom B₁ ++ atom-c Γ₀ ++ atom A' ++ atom-c Γ₂) (atom-c Δ ++ atom C)
--           (∈₂ (atom A₁ ++ atom B₁) (atom-c Γ₀ ++ atom A' ++ atom-c Γ₂) m'))
--     ... | inj₂ m' = ∈₁ (atom A₁) (atom B₁ ++ atom-c Γ₀ ++ atom A' ++ atom-c (Γ₂ ++ Δ) ++ atom C) m'
-- cvar Γ₀ (A ∷ _) Γ₂ (⊸l f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁ , refl , refl) with cvar Γ₀ (_ ∷ Γ') [] f refl | cvar [] Γ₁ Γ₂ g refl
-- cvar Γ₀ (A ∷ _) Γ₂ (⊸l {A = A₁}{B₁}{C} f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁@_ , refl , refl) | v-c a-Ξf a-h | v-c a-Ξg a-k = 
--   v-c a-Ξ a-h'
--   where
--     a-Ξ : ∀{X} → X ∈ atom-c (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl) ++ cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl))
--                → X ∈ atom-c (A ∷ Γ' ++ Γ₁)
--     a-Ξ m with ∈++ (atom-c (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl)))
--                    (atom-c (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))
--                    (subst (λ x → _ ∈ x) (concat++ (List.map atom (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl))) (List.map atom (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))) m)
--     ... | inj₁ m' = 
--        subst (λ x → _ ∈ x) (sym (concat++ (List.map atom (A ∷ Γ')) (List.map atom Γ₁)))
--          (∈₁ (atom-c (A ∷ Γ')) (atom-c Γ₁) (a-Ξf m'))
--     ... | inj₂ m' = 
--        subst (λ x → _ ∈ x) (sym (concat++ (List.map atom (A ∷ Γ')) (List.map atom Γ₁)))
--          (∈₂ (atom-c (A ∷ Γ')) (atom-c Γ₁) (a-Ξg m'))

--     a-h' : ∀{X} → X ∈ atom-c (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl) ++ cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl))
--                 → X ∈ atom A₁ ++ atom B₁ ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C
--     a-h' m with ∈++ (atom-c (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl)))
--                     (atom-c (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))
--                     (subst (λ x → _ ∈ x) (concat++ (List.map atom (cIntrp.Ds (cintrp Γ₀ (A ∷ Γ') [] f refl))) (List.map atom (cIntrp.Ds (cintrp [] Γ₁ Γ₂ g refl)))) m)
--     a-h' m | inj₂ m' with ∈++ (atom B₁) (atom-c Γ₂ ++ atom C) (a-k m')
--     ... | inj₁ m'' = ∈₁ (atom A₁ ++ atom B₁) (atom-c Γ₀ ++ atom-c Γ₂ ++ atom C) (∈₂ (atom A₁) (atom B₁) m'') 
--     ... | inj₂ m'' = ∈₂ (atom A₁ ++ atom B₁ ++ atom-c Γ₀) (atom-c Γ₂ ++ atom C) m''
--     a-h' m | inj₁ m'  with ∈++ (atom-c Γ₀) (atom A₁) (a-h m')
--     ... | inj₁ m'' = ∈₁ (atom A₁ ++ atom B₁ ++ atom-c Γ₀) (atom-c Γ₂ ++ atom C) (∈₂ (atom A₁ ++ atom B₁) (atom-c Γ₀) m'')
--     ... | inj₂ m'' = ∈₁ (atom A₁) (atom B₁ ++ atom-c Γ₀ ++ atom-c Γ₂ ++ atom C) m''
-- cvar [] [] [] ax refl = v-c id (λ ())
-- cvar [] [] Γ₂ (pass f) refl = v-c id (λ ())
-- cvar [] (A ∷ Γ₁) Γ₂ (pass f) refl with svar Γ₁ Γ₂ f refl
-- ... | v-s a-g a-k = v-c a-g a-k
-- cvar (A ∷ Γ₀) Γ₁ Γ₂ (pass f) refl with cvar Γ₀ Γ₁ Γ₂ f refl
-- ... | v-c a-Ξ a-h = v-c a-Ξ a-h
-- cvar [] [] [] Ir refl = v-c (λ ()) (λ ())



-- scut-sintrp : ∀ {S} Γ₁ Γ₂ {Γ C}
--   → (f : S ∣ Γ ⊢ C)
--   → (eq : Γ ≡ Γ₁ ++ Γ₂)
--   →  scut (sIntrp.g (sintrp Γ₁ Γ₂ f eq)) (sIntrp.h (sintrp Γ₁ Γ₂ f eq)) ≗ subst-cxt eq f
-- ccut-cintrp : ∀{S} Γ₀ Γ₁ Γ₂ {Γ C}
--   → (f : S ∣ Γ ⊢ C)
--   → (eq : Γ ≡ Γ₀ ++ Γ₁ ++ Γ₂)
--   → ccut⋆ Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ Γ₁ Γ₂ f eq)) (cIntrp.g (cintrp Γ₀ Γ₁ Γ₂ f eq))
--           ≗ subst-cxt eq f

-- scut-sintrp Γ₁ Γ₂ (Il f) refl = Il (scut-sintrp Γ₁ Γ₂ f refl)
-- scut-sintrp Γ₁ Γ₂ (⊗l f) refl = ⊗l (scut-sintrp (_ ∷ Γ₁) Γ₂ f refl)
-- scut-sintrp Γ₁ Γ₂ (⊸r {A = A}{B} f) refl =
--   scut⊸r (sIntrp.g (sintrp Γ₁ (Γ₂ ∷ʳ _) f refl)) _
--   ∙ ⊸r (scut-sintrp Γ₁ (Γ₂ ∷ʳ _) f refl)
-- scut-sintrp Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₁ Γ Γ₂ Δ eq
-- scut-sintrp {S} _ Γ₂ (⊗r {Γ = Γ} {A = A}{B} f g) refl | inj₁ (Γ' , refl , refl) =
--   scut⊗r (sIntrp.g (sintrp Γ [] f refl)) (sIntrp.h (sintrp Γ [] f refl)) _
--   ∙ ⊗r (scut-sintrp Γ [] f refl) (scut-sintrp Γ' Γ₂ g refl)
-- scut-sintrp Γ₁ _ (⊗r {Δ = Δ} {A}{B} f g) refl | inj₂ (A' , Γ' , refl , refl) =
--   scut⊗r (sIntrp.g (sintrp Γ₁ (_ ∷ Γ') f refl)) (sIntrp.h (sintrp Γ₁ (_ ∷ Γ') f refl)) g
--   ∙ ⊗r (scut-sintrp Γ₁ (A' ∷ Γ') f refl) refl
-- scut-sintrp Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ Γ₁ Δ Γ₂ (sym eq)
-- scut-sintrp Γ₁ .(Γ' ++ Δ) (⊸l {Δ = Δ} {A}{B}{C} f g) refl | inj₁ (Γ' , refl , refl) = 
--   ≡-to-≗ (scut⊸r⋆⊸ls (cIntrp.hs (cintrp Γ₁ Γ' [] f refl)) (⊸l (cIntrp.g (cintrp Γ₁ Γ' [] f refl)) (sIntrp.g (sintrp [] Δ g refl))) _)
--   ∙ cong-scut1 (≡-to-≗ (ccut⋆⊸l1 Γ₁ [] (cIntrp.hs (cintrp Γ₁ Γ' [] f refl)) _ _)) _
--   ∙ ⊸l (ccut-cintrp Γ₁ Γ' [] f refl) (scut-sintrp [] Δ g refl)
-- scut-sintrp _ Γ₂ (⊸l {Γ} {_} f g) refl | inj₂ (A' , Γ' , refl , refl) =
--   ⊸l refl (scut-sintrp (A' ∷ Γ') Γ₂ g refl)
-- scut-sintrp [] [] ax refl = refl
-- scut-sintrp [] (A ∷ Γ₂) (pass f) refl = refl
-- scut-sintrp (A ∷ Γ₁) Γ₂ (pass f) refl = pass (scut-sintrp Γ₁ Γ₂ f refl)
-- scut-sintrp [] [] Ir refl = refl

-- ccut-cintrp Γ₀ Γ₁ Γ₂ (Il f) refl =
--   ≡-to-≗ (ccut⋆Il Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ Γ₁ Γ₂ f refl)) (cIntrp.g (cintrp Γ₀ Γ₁ Γ₂ f refl)))
--   ∙ Il (ccut-cintrp Γ₀ Γ₁ Γ₂ f refl)
-- ccut-cintrp Γ₀ Γ₁ Γ₂ (⊗r {Γ = Γ} {Δ} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
-- ccut-cintrp .(Γ ++ Γ₀) Γ₁ Γ₂ (⊗r {Γ = Γ} f g) refl | inj₁ (Γ₀ , refl , refl) =
--   ≡-to-≗ (ccut⋆⊗r2 Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ Γ₁ Γ₂ g refl)) f (cIntrp.g (cintrp Γ₀ Γ₁ Γ₂ g refl)))
--   ∙ ⊗r refl (ccut-cintrp Γ₀ Γ₁ Γ₂ g refl)
-- ccut-cintrp Γ₀ [] _ (⊗r f g) refl | inj₂ (A , Γ₁ , refl , refl) = refl
-- ccut-cintrp Γ₀ (A ∷ Γ₁) Γ₂ (⊗r {Δ = Δ} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
-- ... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
-- ccut-cintrp Γ₀ (A ∷ Γ₁) _ (⊗r f g) refl | inj₂ (A , ._ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) =
--   ≡-to-≗ (ccut⋆⊗r1 Γ₀ (_ ∷ Γ₂) (cIntrp.hs (cintrp Γ₀ (A ∷ Γ₁) (A' ∷ Γ₂) f refl)) (cIntrp.g (cintrp Γ₀ (A ∷ Γ₁) (A' ∷ Γ₂) f refl)) g)
--   ∙ ⊗r (ccut-cintrp Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl) refl
-- ccut-cintrp Γ₀ (A ∷ _) Γ₂ (⊗r f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁ , refl , refl) =
--   ≡-to-≗ (ccut⋆⊗r Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ (A ∷ Γ') [] f refl)) (cIntrp.hs (cintrp [] Γ₁ Γ₂ g refl)) _ _)
--    ∙ ⊗r (ccut-cintrp Γ₀ (_ ∷ Γ') [] f refl) (ccut-cintrp [] Γ₁ Γ₂ g refl)
-- ccut-cintrp Γ₀ Γ₁ Γ₂ (⊗l f) refl =
--   ≡-to-≗ (ccut⋆⊗l Γ₀ Γ₂ (cIntrp.hs (cintrp (_ ∷ Γ₀) Γ₁ Γ₂ f refl)) (cIntrp.g (cintrp (_ ∷ Γ₀) Γ₁ Γ₂ f refl)))
--   ∙ ⊗l (ccut-cintrp (_ ∷ Γ₀) Γ₁ Γ₂ f refl)
-- ccut-cintrp {S} Γ₀ Γ₁ Γ₂ (⊸r {A = A}{B} f) refl =
--   ≡-to-≗ (ccut⋆⊸r Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ Γ₁ (Γ₂ ++ A ∷ []) f refl)) (cIntrp.g (cintrp Γ₀ Γ₁ (Γ₂ ++ A ∷ []) f refl)))
--   ∙ ⊸r (ccut-cintrp Γ₀ Γ₁ (Γ₂ ∷ʳ _) f refl)
-- ccut-cintrp Γ₀ Γ₁ Γ₂ (⊸l {Γ} {Δ} f g) eq with ++? Γ₀ Γ (Γ₁ ++ Γ₂) Δ eq
-- ccut-cintrp _ Γ₁ Γ₂ (⊸l {Γ} f g) refl | inj₁ (Γ₀ , refl , refl) =
--   ≡-to-≗ (ccut⋆⊸l2 Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ Γ₁ Γ₂ g refl)) f (cIntrp.g (cintrp Γ₀ Γ₁ Γ₂ g refl)))
--   ∙ ⊸l refl (ccut-cintrp Γ₀ Γ₁ Γ₂ g refl)
-- ccut-cintrp Γ₀ [] _ (⊸l f g) refl | inj₂ (B , Γ' , refl , refl) = refl
-- ccut-cintrp Γ₀ (A ∷ Γ₁) Γ₂ (⊸l {Δ = Δ} f g) eq | inj₂ (B , Γ' , refl , q) with cases∷ [] q
-- ... | inj₁ (refl , refl , eq') with ++? Γ₁ Γ' Γ₂ Δ eq'
-- ccut-cintrp Γ₀ (A ∷ Γ₁) _ (⊸l {Δ = Δ} f g) refl | inj₂ (A , _ , refl , q) | inj₁ (refl , refl , refl) | inj₂ (A' , Γ₂ , refl , refl) =
--   ≡-to-≗ (ccut⋆⊸l1 Γ₀ (_ ∷ Γ₂) (cIntrp.hs (cintrp Γ₀ (A ∷ Γ₁) (A' ∷ Γ₂) f refl)) (cIntrp.g (cintrp Γ₀ (A ∷ Γ₁) (A' ∷ Γ₂) f refl)) g)
--   ∙ ⊸l (ccut-cintrp Γ₀ (_ ∷ Γ₁) (_ ∷ Γ₂) f refl) refl
-- ccut-cintrp Γ₀ (A ∷ _) Γ₂ (⊸l f g) refl | inj₂ (A , Γ' , refl , q) | inj₁ (refl , refl , refl) | inj₁ (Γ₁ , refl , refl) =
--   ≡-to-≗ (ccut⋆⊸l Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ (A ∷ Γ') [] f refl)) (cIntrp.hs (cintrp [] Γ₁ Γ₂ g refl)) _ _)
--   ∙ ⊸l (ccut-cintrp Γ₀ (_ ∷ Γ') [] f refl) (ccut-cintrp [] Γ₁ Γ₂ g refl)
-- ccut-cintrp [] [] [] ax refl = refl
-- ccut-cintrp [] [] Γ₂ (pass f) refl = refl
-- ccut-cintrp [] (A ∷ Γ₁) Γ₂ (pass f) refl = pass (scut-sintrp Γ₁ Γ₂ f refl)
-- ccut-cintrp (A ∷ Γ₀) Γ₁ Γ₂ (pass f) refl =
--   ≡-to-≗ (ccut⋆pass Γ₀ Γ₂ (cIntrp.hs (cintrp Γ₀ Γ₁ Γ₂ f refl)) (cIntrp.g (cintrp Γ₀ Γ₁ Γ₂ f refl)))
--   ∙ pass (ccut-cintrp Γ₀ Γ₁ Γ₂ f refl)
-- ccut-cintrp [] [] [] Ir refl = refl


