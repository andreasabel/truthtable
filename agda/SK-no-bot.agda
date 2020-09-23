{-# OPTIONS --postfix-projections #-}

-- Strong normalization for simply-typed combinatory logic
-- using Girard's reducibility candidates.

module SK-no-bot where

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

-- Strong normalization: t is SN if all of its reducts are, inductively.

data SN (t : Tm a) : Set where
  acc : (h : t ↦_ ⊂ SN) → SN t

-- Reducts of SN terms are SN

sn-red : SN t → t ↦ t′ → SN t′
sn-red (acc sn) r = sn r

-- Values are SN:

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

-- Neutral a la Girard.  In this case, the weak head redexes are neutral.

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

record _⇨_ (P : Pred a) (Q : Pred b) (t : Tm (a ⇒ b)) : Set where
  field
    sn  : SN t
    app : ∀ {u} (hu : P u) → Q (t ∙ u)
open _⇨_

-- CRs are closed under function space

⇨-cr : (crP : CR P) (crQ : CR Q) → CR (P ⇨ Q)
⇨-cr                 crP crQ .cr1 h                = h .sn
⇨-cr                 crP crQ .cr2 ht r .sn         = sn-red (ht .sn) r
⇨-cr                 crP crQ .cr2 ht r .app hu     = crQ .cr2 (ht .app hu) (↦l r)
⇨-cr {P = P} {Q = Q} crP crQ .cr3 {t} n ht .sn     = acc (λ r → ht r .sn)
⇨-cr {P = P} {Q = Q} crP crQ .cr3 {t} n ht .app hu = loop hu (crP .cr1 hu)
  where
  -- Side induction on u SN.
  -- Uses that P is closed under reduction.
  loop : ∀{u} → P u → SN u → Q (t ∙ u)
  loop pu (acc snu) = crQ .cr3 (napp n)
    λ{ ↦K     → Kt¬ne n
     ; ↦S     → Stu¬ne n
     ; (↦l r) → ht r .app pu
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

sem-sn : ⟦ a ⟧ t → SN t
sem-sn ht = ty-cr _ .cr1 ht

-- Soundness

-- Interpretation of S

⦅S⦆ : ⟦ c ⇒ a ⇒ b ⟧ t → SN t
   → ⟦ c ⇒ a ⟧ u     → SN u
   → ⟦ c ⟧ v         → SN v
   → ⟦ b ⟧ (S ∙ t ∙ u ∙ v)

⦅S⦆ {b = b} ht (acc snt) hu (acc snu) hv (acc snv) = ty-cr b .cr3 Stuv
  λ{ ↦S                → ht .app hv .app (hu .app hv)
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
⦅ S {c} {a} {b} ⦆ .sn                     = sn-S
⦅ S {c} {a} {b} ⦆ .app ht .sn             = sn-St  (ht .sn)
⦅ S {c} {a} {b} ⦆ .app ht .app hu .sn     = sn-Stu (ht .sn) (hu .sn)
⦅ S {c} {a} {b} ⦆ .app ht .app hu .app hv = ⦅S⦆ {c} {a} {b}
  ht (sem-sn ht)
  hu (sem-sn hu)
  hv (sem-sn hv)
⦅ K {a} ⦆ .sn                             = sn-K
⦅ K {a} ⦆ .app ht .sn                     = sn-Kt (sem-sn ht)
⦅ K {a} ⦆ .app ht .app hu                 = ⦅K⦆ ht (sem-sn ht) (sem-sn hu)
⦅ t ∙ u ⦆                                 = ⦅ t ⦆ .app ⦅ u ⦆

-- Strong normalization

thm : (t : Tm a) → SN t
thm t = sem-sn ⦅ t ⦆

-- -}
-- -}
-- -}
