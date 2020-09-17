{-# OPTIONS --postfix-projections #-}

-- Strong normalization for simply-typed combinatory logic
-- using Girard's reducibility candidates.

module SK-no-bot where

open import Data.Product
open import Function using (case_of_)
open import Level using (suc)
open import Relation.Nullary using (¬_)

-- Logic

¬̇_ : ∀{a} → Set a → Set (suc a)
¬̇ A = ∀{C : Set _} → A → C

-- Types

infixr 6 _⇒_

data Ty : Set where
  o : Ty
  _⇒_ : (a b : Ty) → Ty

variable a b c : Ty

-- Terms
-- Every type is inhabited by ⊥, which replaces free variables.

infixl 5 _∙_

data Tm : (b : Ty) → Set where
  S   : ∀{c a b} → Tm ((c ⇒ (a ⇒ b)) ⇒ (c ⇒ a) ⇒ c ⇒ b)
  K   : Tm (a ⇒ (b ⇒ a))
  _∙_ : (t : Tm (a ⇒ b)) (u : Tm a) → Tm b

variable t t′ u u′ v v′ : Tm a

-- Reduction relations

Rel : Ty → Set₁
Rel a = (t t′ : Tm a) → Set

infix 4 _↦_

-- Full reduction

data _↦_ : Rel a where
  ↦K : K ∙ t ∙ u     ↦ t
  ↦S : S ∙ t ∙ u ∙ v ↦ t ∙ v ∙ (u ∙ v)
  ↦l : t ↦ t′ → t ∙ u ↦ t′ ∙ u
  f↦ : u ↦ u′ → t ∙ u ↦ t ∙ u′

-- Predicates

Pred : Ty → Set₁
Pred a = (t : Tm a) → Set

variable P Q : Pred a

infix 2 _⊂_

_⊂_ : (P Q : Pred a) → Set
P ⊂ Q = ∀{t} (h : P t) → Q t

-- Accessibility

data Acc {A} (R : ∀ (t t′ : A) → Set) (t : A) : Set where
  acc : (h : ∀{t′} (r : R t t′) → Acc R t′) → Acc R t

-- Strong normalization

SN : Pred a
SN = Acc _↦_

-- Reducts of SN terms are SN

sn-red : SN t → t ↦ t′ → SN t′
sn-red (acc sn) r = sn r

-- K is SN

sn-K : SN (K {a} {b})
sn-K = acc λ()

-- Kt is SN

sn-Kt : SN t → SN (K {a} {b} ∙ t)
sn-Kt (acc snt) = acc λ{ (f↦ r) → sn-Kt (snt r) }

-- S is SN

sn-S : SN (S {c} {a} {b})
sn-S = acc λ()

-- St is SN

sn-St : SN t → SN (S {a} {b} ∙ t)
sn-St (acc snt) = acc λ{ (f↦ r) → sn-St (snt r) }

-- Stu is SN

sn-Stu : SN t → SN u → SN (S {a} {b} ∙ t ∙ u)
sn-Stu (acc snt) (acc snu) = acc
  λ{ (↦l (f↦ r)) → sn-Stu (snt r) (acc snu)
   ; (f↦ r)      → sn-Stu (acc snt) (snu r)
   }

-- Neutral (fully applied for →w) a la Girard

data Ne : Pred a where
  Ktu  : Ne (K ∙ t ∙ u)
  Stuv : Ne (S ∙ t ∙ u ∙ v)
  napp : (n : Ne t) → Ne (t ∙ u)

-- Partially applied combinators are not neutral

Kt¬ne : ¬̇ Ne (K {a} {b} ∙ t)
Kt¬ne (napp ())

Stu¬ne : ¬̇ Ne (S ∙ t ∙ u)
Stu¬ne (napp (napp ()))

-- Reducibility candidates

record CR (P : Pred a) : Set where
  field
    cr1 : P ⊂ SN
    cr2 : P t → (t ↦_) ⊂ P
    cr3 : (n : Ne t) (h : t ↦_ ⊂ P) → P t
open CR

-- SN is a reducibility candidate

sn-cr : ∀{a} → CR (SN {a})
sn-cr .cr1 sn = sn
sn-cr .cr2 sn = sn-red sn
sn-cr .cr3 _ h = acc h

-- Function space

_⇨_ : (P : Pred a) (Q : Pred b) → Pred (a ⇒ b)
(P ⇨ Q) t = SN t × ∀ {u} (hu : P u) → Q (t ∙ u)

-- CRs are closed under function space

⇨-cr : (crP : CR P) (crQ : CR Q) → CR (P ⇨ Q)
⇨-cr                crP crQ .cr1 h = h .proj₁
⇨-cr crP crQ .cr2 ht r .proj₁      = sn-red (ht .proj₁) r
⇨-cr crP crQ .cr2 ht r .proj₂ hu   = crQ .cr2 (ht .proj₂ hu) (↦l r)
⇨-cr {P = P} {Q = Q} crP crQ .cr3 {t} n ht .proj₁ = acc (λ r → ht r .proj₁)
⇨-cr {P = P} {Q = Q} crP crQ .cr3 {t} n ht .proj₂ hu = loop hu (crP .cr1 hu)
  where
  -- Side induction on u SN.
  -- Uses that P is closed under reduction.
  loop : ∀{u} → P u → SN u → Q (t ∙ u)
  loop pu (acc snu) = crQ .cr3 (napp n)
    λ{ ↦K     → Kt¬ne n
     ; ↦S     → Stu¬ne n
     ; (↦l r) → ht r .proj₂ pu
     ; (f↦ r) → loop (crP .cr2 pu r) (snu r)
     }

-- Type interpretation

⟦_⟧ : ∀ a → Pred a
⟦ o ⟧     = SN
⟦ a ⇒ b ⟧ = ⟦ a ⟧ ⇨ ⟦ b ⟧

-- Types are interpreted as CRs

ty-cr : ∀ a → CR ⟦ a ⟧
ty-cr o       = sn-cr
ty-cr (a ⇒ b) = ⇨-cr (ty-cr a) (ty-cr b)

-- Soundness

-- Interpretation of S

⦅S⦆ : ⟦ c ⇒ a ⇒ b ⟧ t → SN t
   → ⟦ c ⇒ a ⟧ u     → SN u
   → ⟦ c ⟧ v         → SN v
   → ⟦ b ⟧ (S ∙ t ∙ u ∙ v)

⦅S⦆ {b = b} ht (acc snt) hu (acc snu) hv (acc snv) = ty-cr b .cr3 Stuv
  λ{ ↦S                → ht .proj₂ hv .proj₂ (hu .proj₂ hv)
   ; (↦l (↦l (f↦ rt))) → ⦅S⦆ (ty-cr _ .cr2 ht rt) (snt rt)
                            hu (acc snu)
                            hv (acc snv)
   ; (↦l (f↦ ru))      → ⦅S⦆ ht (acc snt)
                            (ty-cr _ .cr2 hu ru) (snu ru)
                            hv (acc snv)
   ; (f↦ rv)           → ⦅S⦆ ht (acc snt)
                            hu (acc snu)
                            (ty-cr _ .cr2 hv rv) (snv rv)
   }

-- Interpretation of K

⦅K⦆ : ⟦ a ⟧ t → SN t → SN u → ⟦ a ⟧ (K ∙ t ∙ u)
⦅K⦆ {a} at (acc snt) (acc snu) = ty-cr a .cr3 Ktu
  λ{ ↦K           → at
   ; (↦l (f↦ rt)) → ⦅K⦆ (ty-cr a .cr2 at rt) (snt rt) (acc snu)
   ; (f↦ ru)      → ⦅K⦆ at (acc snt) (snu ru)
   }

-- Term interpretation (soundness)

⦅_⦆ : (t : Tm a) → ⟦ a ⟧ t
⦅ S {c} {a} {b} ⦆ .proj₁                        = sn-S
⦅ S {c} {a} {b} ⦆ .proj₂ ht .proj₁              = sn-St (ht .proj₁)
⦅ S {c} {a} {b} ⦆ .proj₂ ht .proj₂ hu .proj₁    = sn-Stu (ht .proj₁) (hu .proj₁)
⦅ S {c} {a} {b} ⦆ .proj₂ ht .proj₂ hu .proj₂ hv = ⦅S⦆ {c} {a} {b}
  ht (ty-cr _ .cr1 ht)
  hu (ty-cr _ .cr1 hu)
  hv (ty-cr c .cr1 hv)
⦅ K {a} ⦆ .proj₁                                = sn-K
⦅ K {a} ⦆ .proj₂ ht .proj₁                      = sn-Kt (ty-cr a .cr1 ht )
⦅ K {a} ⦆ .proj₂ ht .proj₂ hu                   = ⦅K⦆ ht (ty-cr a .cr1 ht) (ty-cr _ .cr1 hu)
⦅ t ∙ u ⦆                                       = ⦅ t ⦆ .proj₂ ⦅ u ⦆

-- Strong normalization

sn : (t : Tm a) → SN t
sn t = ty-cr _ .cr1 ⦅ t ⦆

-- -}
-- -}
-- -}
