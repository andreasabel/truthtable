{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

-- Strong normalization for simply-typed combinatory logic
-- using orthogonality.

module SK-ortho where

open import Data.Unit.Base using () renaming (⊤ to True)
open import Data.Empty using () renaming (⊥ to False)
open import Function using (case_of_)
open import Level using (suc)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; ∃; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

{-# BUILTIN REWRITE _≡_ #-}

-- Types

infixr 6 _⇒_

data Ty : Set where
  o : Ty
  _⇒_ : (a b : Ty) → Ty

variable a b c d : Ty

-- Constants K and S

K-ty : (a b : Ty) → Ty
K-ty a b = a ⇒ (b ⇒ a)

S-ty : (c a b : Ty) → Ty
S-ty c a b = (c ⇒ (a ⇒ b)) ⇒ (c ⇒ a) ⇒ c ⇒ b

data Hd : (d : Ty) → Set where
  K : Hd (K-ty a b)
  S : Hd (S-ty c a b)

variable h : Hd a

-- Terms and stacks

infixl 5 _∙_ _∘_
infixr 6 _∷_ _++_ _⦅++⦆_

mutual

  data Tm : (d : Ty) → Set where
    _∙_ : (h : Hd a) (E : Stack a c) → Tm c

  variable t t′ u u′ v v′ : Tm a

  data Stack : (a c : Ty) → Set where
    ε    : Stack c c
    _∷_  : (u : Tm a) (E : Stack b c) → Stack (a ⇒ b) c

  variable E E' E′ E₀ E₁ E₂ E₃ : Stack a c

-- Stack concatenation

_++_ : Stack a b → Stack b c → Stack a c
ε       ++ E′ = E′
(u ∷ E) ++ E′ = u ∷ (E ++ E′)

++-ε : E ++ ε ≡ E
++-ε {E = ε}     = refl
++-ε {E = u ∷ E} = cong (u ∷_) ++-ε

++-assoc : (E₁ ++ E₂) ++ E₃ ≡ E₁ ++ (E₂ ++ E₃)
++-assoc {E₁ = ε}      = refl
++-assoc {E₁ = u ∷ E₁} = cong (u ∷_) (++-assoc {E₁ = E₁})

{-# REWRITE ++-ε ++-assoc #-}

-- Plugging a term into a stack

_∘_ : Tm a → Stack a c → Tm c
h ∙ E ∘ E′ = h ∙ E ++ E′

app-ε : t ∘ ε ≡ t
app-ε {t = h ∙ E} = refl -- ++-ε

app-app : t ∘ E ∘ E′ ≡ t ∘ E ++ E′
app-app {t = h ∙ E} = refl  -- ++-assoc

{-# REWRITE app-ε app-app #-}

-- Reduction relations

infix 4 _↦_ _↦ₑ_

-- One-step reduction in terms and stacks

mutual

  data _↦_ : (t t′ : Tm a) → Set where
    ↦K : K ∙ t ∷ u     ∷ E ↦ t ∘ E
    ↦S : S ∙ t ∷ u ∷ v ∷ E ↦ t ∘ v ∷ (u ∘ v ∷ ε) ∷ E
    ↦E : (r : E ↦ₑ E′) → h ∙ E ↦ h ∙ E′

  data _↦ₑ_ : (E E′ : Stack a c) → Set where
    here  : (r : t ↦  t′) → t ∷ E ↦ₑ t′ ∷ E
    there : (r : E ↦ₑ E′) → t ∷ E ↦ₑ t  ∷ E′

-- Closure properties of one-step reduction

-- Concatenation ++ is a congruence

++↦ₗ : E ↦ₑ E′ → E ++ E₁ ↦ₑ E′ ++ E₁
++↦ₗ (here  r) = here r
++↦ₗ (there r) = there (++↦ₗ r)

++↦ᵣ : ∀ (E : Stack a b) → E₁ ↦ₑ E₂ → E ++ E₁ ↦ₑ E ++ E₂
++↦ᵣ ε       r = r
++↦ᵣ (u ∷ E) r = there (++↦ᵣ E r)

-- Application ∘ is a congruence

∘↦ₗ : t ↦ t′ → t ∘ E ↦ t′ ∘ E
∘↦ₗ ↦K     = ↦K  -- rewrite app-app
∘↦ₗ ↦S     = ↦S
∘↦ₗ (↦E r) = ↦E (++↦ₗ r)

∘↦ᵣ : E ↦ₑ E′ → t ∘ E ↦ t ∘ E′
∘↦ᵣ {t = h ∙ E} r = ↦E (++↦ᵣ E r)

-- Predicates

infix 2 _⊂_

_⊂_ : {A : Set} (P Q : A → Set) → Set
P ⊂ Q = ∀{t} (r : P t) → Q t

-- Term sets

Pred : Ty → Set₁
Pred a = (t : Tm a) → Set

-- Accessibility

data Acc {A : Set} (R : ∀ (t t′ : A) → Set) (t : A) : Set where
  acc : (h : ∀ {t′} (r : R t t′) → Acc R t′) → Acc R t

-- Reducts of SN things are SN things

sn-red : {A : Set} {R : A → A → Set}{t t′ : A} → Acc R t  → R t t′ → Acc R t′
sn-red (acc sn) r = sn r

-- Strong normalization: t is SN if all of its reducts are, inductively.

SN : {a : Ty} → Pred a
SN  = Acc _↦_

SNₑ : {a c : Ty} (E : Stack a c) → Set
SNₑ = Acc _↦ₑ_

-- Stack constructors preserve SN

sn-ε : SNₑ (ε {c = a})
sn-ε = acc λ()

sn-∷ : SN u → SNₑ E → SNₑ (u ∷ E)
sn-∷ (acc snu) (acc snE) = acc
  λ{ (here r)  → sn-∷ (snu r) (acc snE)
   ; (there r) → sn-∷ (acc snu) (snE r)
   }

-- Values are SN:

-- K is SN

sn-K : SN (K {a} {b} ∙ ε)
sn-K = acc λ{ (↦E ()) }

-- Kt is SN

sn-Kt : SN t → SN (K {a} {b} ∙ t ∷ ε)
sn-Kt (acc snt) = acc λ{ (↦E (here r)) → sn-Kt (snt r) }

-- S is SN

sn-S : SN (S {c} {a} {b} ∙ ε)
sn-S = acc λ{ (↦E ()) }

-- St is SN

sn-St : SN t → SN (S {a} {b} ∙ t ∷ ε)
sn-St (acc snt) = acc λ{ (↦E (here r)) → sn-St (snt r) }

-- Stu is SN

sn-Stu : SN t → SN u → SN (S {a} {b} ∙ t ∷ u ∷ ε)
sn-Stu (acc snt) (acc snu) = acc
  λ{ (↦E (here r))         → sn-Stu (snt r) (acc snu)
   ; (↦E (there (here r))) → sn-Stu (acc snt) (snu r)
   }

-- Redexes are SN

-- KtuE is SN

sn-KtuE : SN (t ∘ E) → SN t → SN u → SNₑ E → SN (K ∙ t ∷ u ∷ E)
sn-KtuE {t = t} sntE (acc snt) (acc snu) (acc snE) = acc
  λ{ ↦K                     → sntE
   ; (↦E (here r))          → sn-KtuE (sn-red sntE (∘↦ₗ r))          (snt r) (acc snu) (acc snE)
   ; (↦E (there (here  r))) → sn-KtuE sntE                          (acc snt) (snu r) (acc snE)
   ; (↦E (there (there r))) → sn-KtuE (sn-red sntE (∘↦ᵣ {t = t} r)) (acc snt) (acc snu) (snE r)
   }

-- StuvE is SN

sn-StuvE : SN (t ∘ v ∷ (u ∘ v ∷ ε) ∷ E) → SN t → SN u → SN v → SNₑ E → SN (S ∙ t ∷ u ∷ v ∷ E)
sn-StuvE {t = t} {u = u} sntvuvE (acc snt) (acc snu) (acc snv) (acc snE) = acc
  λ{ ↦S →
       sntvuvE

   ; (↦E (here r)) →
       sn-StuvE (sn-red sntvuvE (∘↦ₗ r))
         (snt r) (acc snu) (acc snv) (acc snE)

   ; (↦E (there (here  r))) →
       sn-StuvE (sn-red sntvuvE (∘↦ᵣ {t = t} (there (here (∘↦ₗ r)))))
         (acc snt) (snu r) (acc snv) (acc snE)

   ; (↦E (there (there (here r)))) →
       sn-StuvE (sn-red
                  (sn-red sntvuvE  (∘↦ᵣ {t = t} (here r)))
                  (∘↦ᵣ {t = t} (there (here (∘↦ᵣ {t = u} (here r))))))
         (acc snt) (acc snu) (snv r) (acc snE)

   ; (↦E (there (there (there r)))) →
       sn-StuvE (sn-red sntvuvE (∘↦ᵣ {t = t} (there (there r))))
         (acc snt) (acc snu) (acc snv) (snE r)
   }

-- Stack sets

Predₑ : (a : Ty) → Set₁
Predₑ a = (cE : ∃ (Stack a)) → Set

variable A B C D : Predₑ a

-- Elementhood in stack sets

infix 2 _∈_

_∈_ : (E : Stack a c) (A : Predₑ a) → Set
E ∈ A = A (_ , E)

-- Semantic types are specified by sets of SN stacks that contain ε.

record SemTy (A : Predₑ a) : Set where
  field
    sn : E ∈ A → SNₑ E
    id : ε ∈ A
open SemTy

-- Semantic objects

_⊥_ : Tm a → Predₑ a → Set
t ⊥ A = ∀{c E} → A (c , E) → SN (t ∘ E)

Sem-sn : (⟦A⟧ : SemTy A) (⦅t⦆ : t ⊥ A) → SN t
Sem-sn ⟦A⟧ ⦅t⦆ = ⦅t⦆ (⟦A⟧ .id)

Sem-snₑ : (⟦A⟧ : SemTy A) (⦅E⦆ : E ∈ A) → SNₑ E
Sem-snₑ ⟦A⟧ = ⟦A⟧ .sn

-- UNUSED
-- -- Semantic types are closed under reduction of their inhabitants.

-- ⊥-red : t ⊥ A → t ↦ t′ → t′ ⊥ A
-- ⊥-red ⦅t⦆ r ⦅E⦆ = sn-red (⦅t⦆ ⦅E⦆) (∘↦ₗ r)

-- Singleton stack set {ε}

data Idₑ {a} : Predₑ a where
  ε : ε ∈ Idₑ

-- SN is the semantic type given by {ε}

⟦Id⟧ : SemTy (Idₑ {a = a})
⟦Id⟧ .sn ε = sn-ε
⟦Id⟧ .id   = ε

-- Function space on semantic types

data _⇨_ (A : Predₑ a) (B : Predₑ b) : Predₑ (a ⇒ b) where
  ε   : ε ∈ (A ⇨ B)
  _∷_ : (⦅u⦆ : u ⊥ A) (⦅E⦆ : E ∈ B) → (u ∷ E) ∈ (A ⇨ B)

⇨-sem : (⟦A⟧ : SemTy A) (⟦B⟧ : SemTy B) → SemTy (A ⇨ B)
⇨-sem ⟦A⟧ ⟦B⟧ .sn ε         = sn-ε
⇨-sem ⟦A⟧ ⟦B⟧ .sn (⦅u⦆ ∷ ⦅E⦆) = sn-∷ (Sem-sn ⟦A⟧ ⦅u⦆) (⟦B⟧ .sn ⦅E⦆)
⇨-sem ⟦A⟧ ⟦B⟧ .id = ε

-- Type interpretation

⟦_⟧ : ∀ a → Predₑ a
⟦ o ⟧     = Idₑ
⟦ a ⇒ b ⟧ = ⟦ a ⟧ ⇨ ⟦ b ⟧

-- Types are interpreted as semantic types

ty-sem : ∀ a → SemTy ⟦ a ⟧
ty-sem o       = ⟦Id⟧
ty-sem (a ⇒ b) = ⇨-sem (ty-sem a) (ty-sem b)

-- Semantic objects are SN

sem-sn : t ⊥ ⟦ a ⟧ → SN t
sem-sn {a = a} ⦅t⦆ = Sem-sn (ty-sem a) ⦅t⦆

sem-snₑ : E ∈ ⟦ a ⟧ → SNₑ E
sem-snₑ {a = a} ⦅E⦆ = ty-sem a .sn ⦅E⦆

-- Soundness

-- Interpretation of stack constructors

⦅ε_⦆ : ∀ a → ε ∈ ⟦ a ⟧
⦅ε a ⦆ = ty-sem a .id

_⦅++⦆_ : ⟦ a ⟧ (b , E) → ⟦ b ⟧ (c , E′) → ⟦ a ⟧ (c , E ++ E′)
_⦅++⦆_     {E = ε} _         ⦅E′⦆ = ⦅E′⦆
_⦅++⦆_ {a = _ ⇒ _} (⦅u⦆ ∷ ⦅E⦆) ⦅E′⦆ = ⦅u⦆ ∷  ⦅E⦆ ⦅++⦆ ⦅E′⦆

-- Interpretation of K

⦅K⦆ : (K ∙ ε) ⊥ ⟦ K-ty a b ⟧
⦅K⦆ ε                  = sn-K
⦅K⦆ (⦅t⦆ ∷ ε)          = sn-Kt (sem-sn ⦅t⦆)
⦅K⦆ (⦅t⦆ ∷ ⦅u⦆ ∷ ⦅E⦆)  = sn-KtuE (⦅t⦆ ⦅E⦆) (sem-sn ⦅t⦆) (sem-sn ⦅u⦆) (sem-snₑ ⦅E⦆)

-- Interpretation of S

⦅S⦆ : (S ∙ ε) ⊥ ⟦ S-ty c a b ⟧
⦅S⦆ ε                        = sn-S
⦅S⦆ (⦅t⦆ ∷ ε)                = sn-St (sem-sn ⦅t⦆)
⦅S⦆ (⦅t⦆ ∷ ⦅u⦆ ∷ ε)          = sn-Stu (sem-sn ⦅t⦆) (sem-sn ⦅u⦆)
⦅S⦆ (⦅t⦆ ∷ ⦅u⦆ ∷ ⦅v⦆ ∷ ⦅E⦆)  =
  sn-StuvE
   (⦅t⦆ (⦅v⦆ ∷ (λ ⦅E′⦆ → ⦅u⦆ (⦅v⦆ ∷ ⦅E′⦆)) ∷ ⦅E⦆))
   (sem-sn ⦅t⦆) (sem-sn ⦅u⦆) (sem-sn ⦅v⦆) (sem-snₑ ⦅E⦆)

-- Interpretation of constants

⦅_⦆ₕ : (h : Hd a) → (h ∙ ε) ⊥ ⟦ a ⟧
⦅ K ⦆ₕ = ⦅K⦆
⦅ S ⦆ₕ = ⦅S⦆

-- Term interpretation (soundness)

-- infix 100 ⦅_⦆ ⦅_⦆ₑ

mutual
  ⦅_⦆ₑ : (E : Stack a c) → E ∈ ⟦ a ⟧
  ⦅ ε {c = a} ⦆ₑ = ⦅ε a ⦆
  ⦅ u ∷ E ⦆ₑ     = ⦅ u ⦆ ∷ ⦅ E ⦆ₑ

  ⦅_⦆ : (t : Tm a) → t ⊥ ⟦ a ⟧
  ⦅ h ∙ E ⦆ ⦅E′⦆ = ⦅ h ⦆ₕ (⦅ E ⦆ₑ ⦅++⦆ ⦅E′⦆)

-- Strong normalization

thm : (t : Tm a) → SN t
thm t = sem-sn ⦅ t ⦆

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
