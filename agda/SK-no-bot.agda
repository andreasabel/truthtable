{-
{-# OPTIONS --postfix-projections #-}

-- Strong normalization for simply-typed combinatory algebra
-- using Girard's reducibility candidates.

module SK-no-bot where -}

-- Preliminaries
------------------------------------------------------------------------

-- We work in type theory with propositions-as types.

Proposition = Set

-- Negation: A proposition is false if it implies any other proposition.

¬̇_ : Proposition → Set₁
¬̇ A = ∀{C : Proposition} → A → C

-- Syntax
------------------------------------------------------------------------

-- Types:
-- For simplicity, we consider a single base type.
-- Types are closed under function space formation.

infixr 6 _⇒_

data Ty : Set where
  o    : Ty
  _⇒_  : (a b : Ty) → Ty

-- We use small latin letters from the beginning of the alphabet to range over types.

variable a b c : Ty

-- Intrinsically well-typed terms of combinatory algebra (CA):
-- these are applicative terms over the constants K and S.

infixl 5 _∙_

data Tm : Ty → Set where
  K    : Tm (a ⇒ (b ⇒ a))
  S    : Tm ((c ⇒ (a ⇒ b)) ⇒ (c ⇒ a) ⇒ c ⇒ b)
  _∙_  : (t : Tm (a ⇒ b)) (u : Tm a) → Tm b

-- We use small latin letters t, u and v to range over terms.

variable t t′ u u′ v v′ : Tm a

-- The reduction relation is given inductively
-- via axioms for fully applied K and S
-- and congruence rules for the reduction
-- in either the function or the argument part
-- of an application.

infix 4 _↦_

data _↦_ : (t t′ : Tm a) → Set where
  ↦K  : K ∙ t ∙ u      ↦ t
  ↦S  : S ∙ t ∙ u ∙ v  ↦ t ∙ v ∙ (u ∙ v)
  ↦l  : t ↦ t′  → t ∙ u ↦ t′ ∙ u
  f↦  : u ↦ u′  → t ∙ u ↦ t ∙ u′

-- Strong normalization
------------------------------------------------------------------------

-- Sets of terms of a fixed type are expressed as predicates on
-- terms of that type.

Pred : Ty → Set₁
Pred a = (t : Tm a) → Proposition

variable P Q : Pred a

-- The subset relation is implication of predicates.

infix 2 _⊂_

_⊂_ : (P Q : Pred a) → Proposition
P ⊂ Q = ∀{t} → P t → Q t

-- Strong normalization: a term is SN if all of its reducts are, inductively.

data SN (t : Tm a) : Proposition where
  acc : t ↦_ ⊂ SN → SN t

-- Reducts of SN terms are SN by definition.

sn-red : SN t → t ↦ t′ → SN t′
sn-red (acc sn) r = sn r

-- In combinatory algebra, the values are the underapplied functions.
-- All values formed from SN components are SN.
-- The proofs proceed by induction on the SN of the arguments,
-- considering all possible one-step reducts of the values.

-- K is SN.

sn-K : SN (K {a} {b})
sn-K = acc λ()

-- K applied to one SN argument is SN.

sn-Kt : SN t → SN (K {a} {b} ∙ t)
sn-Kt (acc snt) = acc λ{ (f↦ r) → sn-Kt (snt r) }

-- S is SN.

sn-S : SN (S {c} {a} {b})
sn-S = acc λ()

-- S applied to one SN argument is SN.

sn-St : SN t → SN (S ∙ t)
sn-St (acc snt) = acc λ{ (f↦ r) → sn-St (snt r) }

-- S applied to two SN arguments is SN.

sn-Stu : SN t → SN u → SN (S ∙ t ∙ u)
sn-Stu (acc snt) (acc snu) = acc λ where
  (↦l (f↦ r))  → sn-Stu (snt r) (acc snu)
  (f↦ r)       → sn-Stu (acc snt) (snu r)

-- Reducibility candidates
------------------------------------------------------------------------

-- Following Girard, terms which are not introductions are called neutral.
-- In CA, the weak head redexes are the neutrals.

data Ne : Pred a where
  Ktu   : Ne (K ∙ t ∙ u)
  Stuv  : Ne (S ∙ t ∙ u ∙ v)
  napp  : (n : Ne t) → Ne (t ∙ u)

-- Partially applied combinators, i.e., values, are thus not neutral.

Kt¬ne : ¬̇ Ne (K {a} {b} ∙ t)
Kt¬ne (napp ())

Stu¬ne : ¬̇ Ne (S ∙ t ∙ u)
Stu¬ne (napp (napp ()))

-- A reducibility candidate (CR) for a type is a set of SN terms of that type
-- (condition CR1).
-- Further, the set needs to be closed under reduction (CR2).
-- Finally, a candidate needs to contain any neutral term of the right type
-- whose reducts are already in the candidate (CR3).

record CR (P : Pred a) : Proposition where
  field
    cr1  : P ⊂ SN
    cr2  : P t → (t ↦_) ⊂ P
    cr3  : (n : Ne t) (h : t ↦_ ⊂ P) → P t
open CR

-- The set SN is a reducibility candidate.

sn-cr : CR (SN {a})
sn-cr .cr1 sn   = sn
sn-cr .cr2 sn   = sn-red sn
sn-cr .cr3 _ h  = acc h

-- Given two reducibility candidates, one acting as the domain
-- and one as the codomain, we form a new reducibility candidate,
-- the function space.
--
-- The function space contains any SN term that, applied to a term
-- in the domain, yields a result in the codomain.

record _⇨_ (P : Pred a) (Q : Pred b) (t : Tm (a ⇒ b)) : Proposition where
  field
    sn   : SN t
    app  : ∀ {u} (⦅u⦆ : P u) → Q (t ∙ u)
open _⇨_

-- The function space construction indeed operates on CRs.
--
-- CR1 holds by definition.
-- The proof of CR2 only needs CR2 of the codomain.
-- The proof of CR3 needs CR3 of the codomain and CR1 and CR2 of the domain.

⇨-cr : (crP : CR P) (crQ : CR Q) → CR (P ⇨ Q)
⇨-cr                  crP crQ .cr1 ⦅t⦆                  = ⦅t⦆ .sn
⇨-cr                  crP crQ .cr2 ⦅t⦆ r .sn            = sn-red (⦅t⦆ .sn) r
⇨-cr                  crP crQ .cr2 ⦅t⦆ r .app ⦅u⦆       = crQ .cr2 (⦅t⦆ .app ⦅u⦆) (↦l r)
⇨-cr                  crP crQ .cr3      n ⦅t⦆ .sn       = acc λ r → ⦅t⦆ r .sn
⇨-cr {P = P} {Q = Q}  crP crQ .cr3 {t}  n ⦅t⦆ .app ⦅u⦆  = loop ⦅u⦆ (crP .cr1 ⦅u⦆)
  -- We perform a side induction on the SN of the function argument,
  -- exploiting that the domain is closed under reduction.
  where
  loop : ∀{u} → P u → SN u → Q (t ∙ u)
  loop ⦅u⦆ (acc snu) = crQ .cr3 (napp n) λ where
    ↦K      → Kt¬ne n
    ↦S      → Stu¬ne n
    (↦l r)  → ⦅t⦆ r .app ⦅u⦆
    (f↦ r)  → loop (crP .cr2 ⦅u⦆ r) (snu r)

-- Soundness
------------------------------------------------------------------------

-- Interpretation of types as semantic types:
-- we interpret the base type as the set of all SN terms of that type
-- and the function type via the function space construction.

⟦_⟧ : ∀ a → Pred a
⟦ o ⟧      = SN
⟦ a ⇒ b ⟧  = ⟦ a ⟧ ⇨ ⟦ b ⟧

-- Types are indeed interpreted as CRs.

ty-cr : ∀ a → CR ⟦ a ⟧
ty-cr o        = sn-cr
ty-cr (a ⇒ b)  = ⇨-cr (ty-cr a) (ty-cr b)

-- Any term in a semantic type is SN.

sem-sn : ⟦ a ⟧ t → SN t
sem-sn ⦅t⦆ = ty-cr _ .cr1 ⦅t⦆

-- Interpretation of S:
-- constant S, fully applied to terms inhabiting the respective semantic types,
-- inhabits the correct semantic type as well.
--
-- This lemma is proven by induction on the SN of the subterms,
-- redundant facts which we add explicitly for the sake of recursion.
-- The induction hypothesis is applicable thanks to CR2.

⦅S⦆  :  ⟦ c ⇒ a ⇒ b ⟧ t  → SN t
     →  ⟦ c ⇒ a ⟧ u      → SN u
     →  ⟦ c ⟧ v          → SN v
     →  ⟦ b ⟧ (S ∙ t ∙ u ∙ v)

⦅S⦆ {b = b} ⦅t⦆ (acc snt) ⦅u⦆ (acc snu) ⦅v⦆ (acc snv) = ty-cr b .cr3 Stuv λ where
  ↦S                 → ⦅t⦆ .app ⦅v⦆ .app (⦅u⦆ .app ⦅v⦆)
  (↦l (↦l (f↦ rt)))  → ⦅S⦆  (ty-cr _ .cr2 ⦅t⦆ rt) (snt rt)
                            ⦅u⦆ (acc snu)
                            ⦅v⦆ (acc snv)
  (↦l (f↦ ru))       → ⦅S⦆  ⦅t⦆ (acc snt)
                            (ty-cr _ .cr2 ⦅u⦆ ru) (snu ru)
                            ⦅v⦆ (acc snv)
  (f↦ rv)            → ⦅S⦆  ⦅t⦆ (acc snt)
                            ⦅u⦆ (acc snu)
                            (ty-cr _ .cr2 ⦅v⦆ rv) (snv rv)


-- Interpretation of K: analogously.

⦅K⦆ : ⟦ a ⟧ t → SN t → SN u → ⟦ a ⟧ (K ∙ t ∙ u)
⦅K⦆ {a} ⦅t⦆ (acc snt) (acc snu) = ty-cr a .cr3 Ktu λ where
  ↦K            → ⦅t⦆
  (↦l (f↦ rt))  → ⦅K⦆ (ty-cr a .cr2 ⦅t⦆ rt) (snt rt) (acc snu)
  (f↦ ru)       → ⦅K⦆ ⦅t⦆ (acc snt) (snu ru)


-- Term interpretation: each term inhabits its respective semantic type.
--
-- Proof by induction on the term.

⦅_⦆ : (t : Tm a) → ⟦ a ⟧ t
⦅ S {b = b} ⦆ .sn                         = sn-S
⦅ S {b = b} ⦆ .app ⦅t⦆ .sn                = sn-St  (⦅t⦆ .sn)
⦅ S {b = b} ⦆ .app ⦅t⦆ .app ⦅u⦆ .sn       = sn-Stu (⦅t⦆ .sn) (⦅u⦆ .sn)
⦅ S {b = b} ⦆ .app ⦅t⦆ .app ⦅u⦆ .app ⦅v⦆  = ⦅S⦆ {b = b}  ⦅t⦆ (sem-sn ⦅t⦆)
                                                         ⦅u⦆ (sem-sn ⦅u⦆)
                                                         ⦅v⦆ (sem-sn ⦅v⦆)
⦅ K ⦆ .sn                                 = sn-K
⦅ K ⦆ .app ⦅t⦆ .sn                        = sn-Kt (sem-sn ⦅t⦆)
⦅ K ⦆ .app ⦅t⦆ .app ⦅u⦆                   = ⦅K⦆ ⦅t⦆ (sem-sn ⦅t⦆) (sem-sn ⦅u⦆)
⦅ t ∙ u ⦆                                 = ⦅ t ⦆ .app ⦅ u ⦆

-- Strong normalization is now a simple corollary.

thm : (t : Tm a) → SN t
thm t = sem-sn ⦅ t ⦆

-- -}
-- -}
-- -}
