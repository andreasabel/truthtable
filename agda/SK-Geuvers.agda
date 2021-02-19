{-# OPTIONS --postfix-projections #-}

module SK-Geuvers where

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

-- data Const : Ty → Set where
--   S : Const ((c ⇒ a) ⇒ (c ⇒ (a ⇒ b)) ⇒ c ⇒ b)
--   K : Const (a ⇒ (b ⇒ a))

-- variable k : Const a

infixl 5 _∙_

-- data Tm (b : Ty) : Set where
--   const : (k : Const b) → Tm b
--   _∙_   : (t : Tm (a ⇒ b)) (u : Tm a) → Tm b

data Tm : (b : Ty) → Set where
  ⊥   : Tm a
  S   : ∀{c a b} → Tm ((c ⇒ (a ⇒ b)) ⇒ (c ⇒ a) ⇒ c ⇒ b)
  K   : Tm (a ⇒ (b ⇒ a))
  _∙_ : (t : Tm (a ⇒ b)) (u : Tm a) → Tm b

variable t t' u u' v v' : Tm a

-- Reduction relations

Rel : Ty → Set₁
Rel a = (t t' : Tm a) → Set

infix 4 _↦_ _→w_ _→f_

-- Contraction

data _↦_ : Rel a where
  ↦K : K ∙ t ∙ u         ↦ t
  ↦S : S ∙ t ∙ u ∙ v ↦ t ∙ v ∙ (u ∙ v)

-- Weak head reduction

data _→w_ : Rel a where
  w↦ : t ↦ t' → t →w t'
  wl : t →w t' → t ∙ u →w t' ∙ u

-- Full reduction

data _→f_ : Rel a where
  f↦ : t ↦ t' → t →f t'
  fl : t →f t' → t ∙ u →f t' ∙ u
  fr : u →f u' → t ∙ u →f t ∙ u'

-- Predicates

Pred : Ty → Set₁
Pred a = (t : Tm a) → Set

variable P Q : Pred a

infix 2 _⊂_

_⊂_ : (P Q : Pred a) → Set
P ⊂ Q = ∀{t} (h : P t) → Q t

-- Normal forms

Nf : (R : Rel a) → Pred a
Nf R t = ∀{t'} → ¬ R t t'

NF : Pred a
NF = Nf _→f_

-- ⊥ is a normal form

⊥-nf↦ : Nf {a} _↦_ ⊥
⊥-nf↦ ()

⊥-nf→w : Nf {a} _→w_ ⊥
⊥-nf→w (w↦ ())

⊥-nf : NF {a} ⊥
⊥-nf (f↦ ())

-- Accessibility

data Acc {A} (R : ∀ (t t' : A) → Set) (t : A) : Set where
  acc : (h : ∀{t'} (r : R t t') → Acc R t') → Acc R t

-- Strong normalization

SN : Pred a
SN = Acc _→f_

-- Normal forms are SN

nf-sn : NF {a} ⊂ SN
nf-sn h = acc λ r → case h r of λ()

⊥-sn : SN {a} ⊥
⊥-sn = nf-sn ⊥-nf

-- Parts of SN terms are SN

sn-fun : SN (t ∙ u) → SN {a ⇒ b} t
sn-fun (acc h) = acc λ r → sn-fun (h (fl r))

sn-arg : SN {b} (t ∙ u) → SN {a} u
sn-arg (acc h) = acc λ r → sn-arg (h (fr r))

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

-- Ne is not closed under reduction!

-- ne→f : Ne t → t →f_ ⊂ Ne
-- ne→f n r = {!!}

-- ne-sn-app : Ne t → SN t → SN u → SN (t ∙ u)
-- ne-sn-app n (acc ht) (acc hu) = acc
--   λ{ (f↦ ↦K) → Kt¬ne n
--    ; (f↦ ↦S) → Stu¬ne n
--    ; (fl r)  → ne-sn-app {!!} (ht r) (acc hu)
--    ; (fr r)  → ne-sn-app n (acc ht) (hu r)
--    }

-- Reducibility candidates

record CR (P : Pred a) : Set where
  field
    cr1 : P ⊂ SN
    cr3 : (n : Ne t) (sn : SN t) (h : t →w_ ⊂ P) → P t
open CR

-- SN is a reducibility candidate

sn-cr : ∀{a} → CR (SN {a})
sn-cr = record { cr1 = λ sn → sn ; cr3 = λ _ sn _ → sn }

-- ⊥ is in each CR

⊥-cr : CR {a} P → P ⊥
⊥-cr record { cr3 = cr3 } = cr3 ⊥ ⊥-sn (λ r → case ⊥-nf→w r of λ())

-- Function space

_⇨_ : (P : Pred a) (Q : Pred b) → Pred (a ⇒ b)
(P ⇨ Q) t = ∀ {u} (hu : P u) → Q (t ∙ u)

sn-app : SN t → (t →w_ ⊂ P ⇨ Q) → P u → SN u → SN (t ∙ u)
sn-app (acc snt) ht pu (acc snu) = acc
  λ{ (f↦ ↦K) → {!!}
   ; (f↦ ↦S) → {!!}
   ; (fl r) → {!ne-sn!}
   ; (fr r) → sn-app (acc snt) ht {!NEED CR2!} (snu r)
   }

-- ne-sn-aux : Ne t → SN t → (t →w_ ⊂ P ⇨ Q) → P u → SN u → SN (t ∙ u)
-- ne-sn-aux n (acc snt) ht pu (acc snu) = acc
--   λ{ (f↦ ↦K) → Kt¬ne n
--    ; (f↦ ↦S) → Stu¬ne n
--    ; (fl r) → {!ne-sn!}
--    ; (fr r) → ne-sn-aux n (acc snt) ht {!NEED CR2!} (snu r)
--    }

⇨-cr : (crP : CR P) (crQ : CR Q) → CR (P ⇨ Q)
⇨-cr crP crQ .cr1 h = sn-fun (crQ .cr1 (h (⊥-cr crP)))
⇨-cr crP crQ .cr3 n sn h hu = crQ .cr3
  (napp n)
  {!ne-sn-aux n sn h hu (crP .cr1 hu)!} -- Not valid: (ne-sn-app n sn (crP .cr1 hu))
  (λ{ (w↦ ↦K) → Kt¬ne n
    ; (w↦ ↦S) → Stu¬ne n
    ; (wl w)  → h w hu
    })

-- -}
-- -}
-- -}
