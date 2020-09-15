{-# OPTIONS --postfix-projections #-}

-- Strong normalization for simply-typed combinatory logic
-- using Girard's reducibility candidates.

module SK where

open import Relation.Nullary using (¬_)
open import Function
open import Level

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
  ⊥   : Tm a
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

-- Normal forms

Nf : (R : Rel a) → Pred a
Nf R t = ∀{t′} → ¬ R t t′

NF : Pred a
NF = Nf _↦_

-- ⊥ is a normal form

⊥-nf : NF {a} ⊥
⊥-nf ()

-- Accessibility

data Acc {A} (R : ∀ (t t′ : A) → Set) (t : A) : Set where
  acc : (h : ∀{t′} (r : R t t′) → Acc R t′) → Acc R t

-- Strong normalization

SN : Pred a
SN = Acc _↦_

-- Normal forms are SN

nf-sn : NF {a} ⊂ SN
nf-sn h = acc λ r → case h r of λ()

-- ⊥ is SN

⊥-sn : SN {a} ⊥
⊥-sn = nf-sn ⊥-nf

-- Parts of SN terms are SN

sn-fun : SN (t ∙ u) → SN {a ⇒ b} t
sn-fun (acc h) = acc λ r → sn-fun (h (↦l r))

sn-arg : SN {b} (t ∙ u) → SN {a} u
sn-arg (acc h) = acc λ r → sn-arg (h (f↦ r))

-- Neutral (fully applied for →w) a la Girard

data Ne : Pred a where
  ⊥    : Ne {a} ⊥
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
sn-cr .cr2 (acc sn) r = sn r
sn-cr .cr3 _ h = acc h

-- ⊥ is in each CR

⊥-cr : CR {a} P → P ⊥
⊥-cr record { cr3 = cr3 } = cr3 ⊥ (λ r → case ⊥-nf r of λ())

-- Function space

_⇨_ : (P : Pred a) (Q : Pred b) → Pred (a ⇒ b)
(P ⇨ Q) t = ∀ {u} (hu : P u) → Q (t ∙ u)

-- aux : CR P → CR Q → Ne t → (t ↦_ ⊂ P ⇨ Q) → P u → SN u → Q (t ∙ u)
-- aux crP crQ n ht pu (acc snu) = crQ .cr3 (napp n)
--   λ{ ↦K → Kt¬ne n
--    ; ↦S → Stu¬ne n
--    ; (↦l r) → ht r pu
--    ; (f↦ r) → aux crP crQ n ht {!!} (snu r)
--    }

-- CRs are closed under function space

⇨-cr : (crP : CR P) (crQ : CR Q) → CR (P ⇨ Q)
⇨-cr                crP crQ .cr1 h           = sn-fun (crQ .cr1 (h (⊥-cr crP)))
⇨-cr                crP crQ .cr2 ht r hu     = crQ .cr2 (ht hu) (↦l r)
⇨-cr {P = P}{Q = Q} crP crQ .cr3 {t} n ht hu = loop hu (crP .cr1 hu)
  where
  -- Side induction on u SN.
  -- Uses that P is closed under reduction.
  loop : ∀{u} → P u → SN u → Q (t ∙ u)
  loop pu (acc snu) = crQ .cr3 (napp n)
    λ{ ↦K     → Kt¬ne n
     ; ↦S     → Stu¬ne n
     ; (↦l r) → ht r pu
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

-- Interpretation of ⊥

⦅⊥⦆ : ∀ a → ⟦ a ⟧ ⊥
⦅⊥⦆ a = ⊥-cr (ty-cr a)

-- Interpretation of S

⦅S⦆ : ⟦ c ⇒ a ⇒ b ⟧ t → SN t
   → ⟦ c ⇒ a ⟧ u     → SN u
   → ⟦ c ⟧ v         → SN v
   → ⟦ b ⟧ (S ∙ t ∙ u ∙ v)

⦅S⦆ {b = b} ht (acc snt) hu (acc snu) hv (acc snv) = ty-cr b .cr3 Stuv
  λ{ ↦S                → ht hv (hu hv)
   ; (↦l (↦l (f↦ rt))) → ⦅S⦆ (ty-cr _ .cr2 (λ{v} → ht {v}) rt) (snt rt)
                            hu (acc snu)
                            hv (acc snv)
   ; (↦l (f↦ ru))      → ⦅S⦆ ht (acc snt)
                            (ty-cr _ .cr2 (λ{v} → hu {v}) ru) (snu ru)
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
⦅ ⊥ {a} ⦆                  = ⦅⊥⦆ a
⦅ S {c} {a} {b} ⦆ ht hu hv = ⦅S⦆ {c} {a} {b}
  ht (ty-cr _ .cr1 λ{v} → ht {v})
  hu (ty-cr _ .cr1 λ{v} → hu {v})
  hv (ty-cr c .cr1 hv)
⦅ K {a} ⦆ ht hu            = ⦅K⦆ ht (ty-cr a .cr1 ht) (ty-cr _ .cr1 hu)
⦅ t ∙ u ⦆ = ⦅ t ⦆ ⦅ u ⦆

-- Strong normalization

sn : (t : Tm a) → SN t
sn t = ty-cr _ .cr1 ⦅ t ⦆

-- -}
-- -}
-- -}
