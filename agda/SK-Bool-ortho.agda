{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

-- Strong normalization for simply-typed combinatory logic with booleans
-- using orthogonality.

module SK-Bool-ortho where

-- open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Unit.Base using () renaming (⊤ to True)
open import Data.Empty using () renaming (⊥ to False)
open import Function using (case_of_)
open import Level using (suc)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; ∃; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

{-# BUILTIN REWRITE _≡_ #-}

-- variable q q' q′ : Bool

-- Types

infixr 6 _⇒_

data Ty : Set where
  bool : Ty
  _⇒_  : (a b : Ty) → Ty

variable a b c d : Ty

-- Constants K and S

K-ty : (a b : Ty) → Ty
K-ty a b = a ⇒ (b ⇒ a)

S-ty : (c a b : Ty) → Ty
S-ty c a b = (c ⇒ (a ⇒ b)) ⇒ (c ⇒ a) ⇒ c ⇒ b

data Hd : (d : Ty) → Set where
  K : Hd (K-ty a b)
  S : Hd (S-ty c a b)
  -- bit : (q : Bool) → Hd bool
  tt : Hd bool
  ff : Hd bool

variable h : Hd a

-- Terms and stacks

infixl 5 _∙_ _∘_
infixr 6 _∷_ _++_ _⦅++⦆_

mutual

  data Tm : (d : Ty) → Set where
    _∙_ : (h : Hd a) (E : Stack a c) → Tm c

  variable t t′ u u′ v v′ t' u' v' : Tm a

  data Elim : (a c : Ty) → Set where
    app  : (u : Tm a) → Elim (a ⇒ b) b
    case : (u v : Tm a) → Elim bool a

  variable e e′ e' e₀ e₁ e₂ : Elim a c

  data Stack : (a c : Ty) → Set where
    ε    : Stack c c
    _∷_  : (e : Elim a b) (E : Stack b c) → Stack a c

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

infix 4 _↦_ _↦ₑ_ _↦ₛ_

-- One-step reduction in terms and stacks

mutual

  data _↦_ : (t t′ : Tm a) → Set where
    ↦K  : K  ∙ app t ∷ e             ∷ E ↦ t ∘ E
    ↦S  : S  ∙ app t ∷ app u ∷ app v ∷ E ↦ t ∘ app v ∷ app (u ∘ app v ∷ ε) ∷ E
    ↦tt : tt ∙ case u v              ∷ E ↦ u ∘ E
    ↦ff : ff ∙ case u v              ∷ E ↦ v ∘ E
    ↦E  : (r : E ↦ₛ E′) → h ∙ E ↦ h ∙ E′

  data _↦ₑ_ : (e e' : Elim a c) → Set where
    ↦app   : (r : t ↦ t') → app {a} {b} t ↦ₑ app t'
    ↦caseₗ : (r : u ↦ u') → case u v ↦ₑ case u' v
    ↦caseᵣ : (r : v ↦ v') → case u v ↦ₑ case u v'

  -- Contains single frame permutation

  data _↦ₛ_ : (E E′ : Stack a c) → Set where
    π     : (case u v ∷ e ∷ E) ↦ₛ (case (u ∘ e ∷ ε) (v ∘ e ∷ ε) ∷ E)
    here  : (r : e ↦ₑ  e′) → e ∷ E ↦ₛ e′ ∷ E
    there : (r : E ↦ₛ E′) → e ∷ E ↦ₛ e  ∷ E′

-- Closure properties of one-step reduction

-- Concatenation ++ is a congruence

++↦ₗ : E ↦ₛ E′ → E ++ E₁ ↦ₛ E′ ++ E₁
++↦ₗ π         = π
++↦ₗ (here  r) = here r
++↦ₗ (there r) = there (++↦ₗ r)

++↦ᵣ : ∀ (E : Stack a b) → E₁ ↦ₛ E₂ → E ++ E₁ ↦ₛ E ++ E₂
++↦ᵣ ε       r = r
++↦ᵣ (u ∷ E) r = there (++↦ᵣ E r)

-- Application ∘ is a congruence

∘↦ₗ : t ↦ t′ → t ∘ E ↦ t′ ∘ E
∘↦ₗ ↦K     = ↦K  -- rewrite app-app
∘↦ₗ ↦S     = ↦S
∘↦ₗ ↦tt    = ↦tt
∘↦ₗ ↦ff    = ↦ff
∘↦ₗ (↦E r) = ↦E (++↦ₗ r)

∘↦ᵣ : E ↦ₛ E′ → t ∘ E ↦ t ∘ E′
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

SNₑ : {a c : Ty} (e : Elim a c) → Set
SNₑ = Acc _↦ₑ_

SNₛ : {a c : Ty} (E : Stack a c) → Set
SNₛ = Acc _↦ₛ_

-- Deconstruction of SN t

sn-spine : SN (h ∙ E) → SNₛ E
sn-spine (acc sntE) = acc λ r → sn-spine (sntE (↦E r))

-- Elim constructors preserve SN

sn-app : SN u → SNₑ (app {a} {b} u)
sn-app (acc snu) = acc λ{ (↦app r) → sn-app (snu r) }

-- Stack constructors preserve SN

sn-ε : SNₛ (ε {c = a})
sn-ε = acc λ()

sn-app∷ : SN u → SNₛ E → SNₛ (app u ∷ E)
sn-app∷ (acc snu) (acc snE) = acc
  λ{ (here (↦app r)) → sn-app∷ (snu r) (acc snE)
   ; (there r      ) → sn-app∷ (acc snu) (snE r)
   }

sn-case∷ε : SN u → SN v → SNₛ (case u v ∷ ε)
sn-case∷ε (acc snu) (acc snv) = acc
  λ{ (here (↦caseₗ r)) → sn-case∷ε (snu r) (acc snv)
   ; (here (↦caseᵣ r)) → sn-case∷ε (acc snu) (snv r)
   }

{-
sn-case∷ : SNₛ (case (u ∘ e ∷ ε) (v ∘ e ∷ ε) ∷ E) → SN u → SN v → SNₛ (e ∷ E) → SNₛ (case u v ∷ e ∷ E)
sn-case∷ sn (acc snu) (acc snv) (acc sneE) = acc
  λ{ π → sn
   ; (here (↦caseₗ r)) → sn-case∷ {!!} (snu r) (acc snv) (acc sneE)
   ; (here (↦caseᵣ r)) → sn-case∷ {!!} (acc snu) (snv r) (acc sneE)
   ; (there r) → sn-case∷ {!!} (acc snu) (acc snv) {!(sneE r)!}
   }
-}
{-
sn-∷ : SNₑ e → SNₛ E → SNₛ (e ∷ E)
sn-∷ (acc sne) (acc snE) = acc
  λ{ π → {!!}
   ; (here r)  → sn-∷ (sne r) (acc snE)
   ; (there r) → sn-∷ (acc sne) (snE r)
   }
-}
-- Values are SN:

-- Heads are SN

sn-Hd : SN (h ∙ ε)
sn-Hd = acc λ{ (↦E ()) }

-- Underapplied functions are SN

-- Kt is SN

sn-Kt : SN t → SN (K {a} {b} ∙ app t ∷ ε)
sn-Kt (acc snt) = acc λ{ (↦E (here (↦app r))) → sn-Kt (snt r) }

-- St is SN

sn-St : SN t → SN (S {a} {b} ∙ app t ∷ ε)
sn-St (acc snt) = acc λ{ (↦E (here (↦app r))) → sn-St (snt r) }

-- Stu is SN

sn-Stu : SN t → SN u → SN (S {a} {b} ∙ app t ∷ app u ∷ ε)
sn-Stu (acc snt) (acc snu) = acc
  λ{ (↦E (here (↦app r)))         → sn-Stu (snt r) (acc snu)
   ; (↦E (there (here (↦app r)))) → sn-Stu (acc snt) (snu r)
   }

-- Redexes are SN

sn-tt-case : SN (u ∘ E) → SNₛ (case u v ∷ E) → SN (tt ∙ case u v ∷ E)
sn-tt-case {u = u} snuE (acc snuvE) = acc
  λ{ ↦tt → snuE
   ; (↦E π) → sn-tt-case snuE (snuvE π)
   ; (↦E (here (↦caseₗ r)))  → sn-tt-case (sn-red snuE (∘↦ₗ r)) (snuvE (here (↦caseₗ r)))
   ; (↦E (here (↦caseᵣ r))) → sn-tt-case snuE (snuvE (here (↦caseᵣ r)))
   ; (↦E (there r))         → sn-tt-case (sn-red snuE (∘↦ᵣ {t = u} r)) (snuvE (there r))
   }
sn-ff-case : SN (v ∘ E) → SNₛ (case u v ∷ E) → SN (ff ∙ case u v ∷ E)
sn-ff-case {v = v} snuE (acc snuvE) = acc
  λ{ ↦ff → snuE
   ; (↦E π) → sn-ff-case snuE (snuvE π)
   ; (↦E (here (↦caseₗ r)))  → sn-ff-case snuE (snuvE (here (↦caseₗ r)))
   ; (↦E (here (↦caseᵣ r))) → sn-ff-case (sn-red snuE (∘↦ₗ r)) (snuvE (here (↦caseᵣ r)))
   ; (↦E (there r))         → sn-ff-case (sn-red snuE (∘↦ᵣ {t = v} r)) (snuvE (there r))
   }

{-
sn-tt-case : SN (u ∘ E) → SN u → SN v → SNₛ E → SN (tt ∙ case u v ∷ E)
sn-tt-case snuE (acc snu) (acc snv) (acc snE) = acc
  λ{ ↦tt → snuE
   ; (↦E π) → {!!}
   ; (↦E (here r)) → {!!}
   ; (↦E (there r)) → {!!}
   }
-}

-- KtuE is SN

sn-KtuE : SN (t ∘ E) → SN t → SNₑ e → SNₛ E → SN (K ∙ app t ∷ e ∷ E)
sn-KtuE {t = t} sntE (acc snt) (acc sne) (acc snE) = acc
  λ{ ↦K                     → sntE
   ; (↦E (here (↦app r)))          → sn-KtuE (sn-red sntE (∘↦ₗ r))          (snt r) (acc sne) (acc snE)
   ; (↦E (there (here  r))) → sn-KtuE sntE                          (acc snt) (sne r) (acc snE)
   ; (↦E (there (there r))) → sn-KtuE (sn-red sntE (∘↦ᵣ {t = t} r)) (acc snt) (acc sne) (snE r)
   }

-- StuvE is SN

sn-StuvE : SN (t ∘ app v ∷ app (u ∘ app v ∷ ε) ∷ E) → SN t → SN u → SN v → SNₛ E → SN (S ∙ app t ∷ app u ∷ app v ∷ E)
sn-StuvE {t = t} {u = u} sntvuvE (acc snt) (acc snu) (acc snv) (acc snE) = acc
  λ{ ↦S →
       sntvuvE

   ; (↦E (here (↦app r))) →
       sn-StuvE (sn-red sntvuvE (∘↦ₗ r))
         (snt r) (acc snu) (acc snv) (acc snE)

   ; (↦E (there (here (↦app r)))) →
       sn-StuvE (sn-red sntvuvE (∘↦ᵣ {t = t} (there (here (↦app (∘↦ₗ r))))))
         (acc snt) (snu r) (acc snv) (acc snE)

   ; (↦E (there (there (here (↦app r))))) →
       sn-StuvE (sn-red
                  (sn-red sntvuvE  (∘↦ᵣ {t = t} (here (↦app r))))
                  (∘↦ᵣ {t = t} (there (here (↦app (∘↦ᵣ {t = u} (here (↦app r))))))))
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
    id  : ε ∈ A
    sn  : (⦅E⦆ : E ∈ A) → SNₛ E
    red : (⦅E⦆ : E ∈ A) (r : E ↦ₛ E') → E' ∈ A
open SemTy

-- Semantic objects

-- We use a record to help Agda's unifier.
record _⊥_ (t : Tm a) (A : Predₑ a) : Set where
  field
    run : ∀{c E} (⦅E⦆ : A (c , E)) → SN (t ∘ E)
open _⊥_

-- _⊥_ : Tm a → Predₑ a → Set
-- t ⊥ A = ∀{c E} (⦅E⦆ : A (c , E)) → SN (t ∘ E)

Sem-sn : (⟦A⟧ : SemTy A) (⦅t⦆ : t ⊥ A) → SN t
Sem-sn ⟦A⟧ ⦅t⦆ = ⦅t⦆ .run (⟦A⟧ .id)

Sem-snₑ : (⟦A⟧ : SemTy A) (⦅E⦆ : E ∈ A) → SNₛ E
Sem-snₑ ⟦A⟧ = ⟦A⟧ .sn

-- Semantic types are closed under reduction of their inhabitants.

sem-red : t ⊥ A → t ↦ t′ → t′ ⊥ A
sem-red ⦅t⦆ r .run ⦅E⦆ = sn-red (⦅t⦆ .run ⦅E⦆) (∘↦ₗ r)

-- Sem-redₛ :  (⟦A⟧ : SemTy A) (⦅E⦆ : E ∈ A) (r : E ↦ₛ E') → E' ∈ A
-- Sem-redₛ ⟦A⟧ ⦅E⦆ r = {!!}

-- Singleton stack set {ε}

data Idₑ {a} : Predₑ a where
  ε : ε ∈ Idₑ

-- SN is the semantic type given by {ε}

⟦Id⟧ : SemTy (Idₑ {a = a})
⟦Id⟧ .id    = ε
⟦Id⟧ .sn  ε = sn-ε
⟦Id⟧ .red ε ()

-- Semantic booleans

record ⟦bool⟧ (cE : ∃ (Stack bool)) : Set where
  field
    then : let c , E = cE in SN (tt ∙ E)
    else : let c , E = cE in SN (ff ∙ E)
open ⟦bool⟧

bool-sem : SemTy ⟦bool⟧
bool-sem .id .then = sn-Hd
bool-sem .id .else = sn-Hd
bool-sem .sn  ⦅E⦆   = sn-spine (⦅E⦆ .then)
bool-sem .red ⦅E⦆ r .then = sn-red (⦅E⦆ .then) (↦E r)
bool-sem .red ⦅E⦆ r .else = sn-red (⦅E⦆ .else) (↦E r)

-- Boolean values

⦅tt⦆ : (tt ∙ ε) ⊥ ⟦bool⟧
⦅tt⦆ .run ⦅E⦆ = ⦅E⦆ .then

⦅ff⦆ : (ff ∙ ε) ⊥ ⟦bool⟧
⦅ff⦆ .run ⦅E⦆ = ⦅E⦆ .else

--

case-hd : {u v : Tm a} → case u v ∷ E ∈ ⟦bool⟧ → case u v ∷ ε ∈ ⟦bool⟧
case-hd ⦅caseE⦆ .then = {!⦅caseE⦆ .then!}
case-hd ⦅caseE⦆ .else = {!!}


-- Function space on semantic types

data _⇨_ (A : Predₑ a) (B : Predₑ b) : Predₑ (a ⇒ b) where
  ε   : ε ∈ (A ⇨ B)
  _∷_ : (⦅u⦆ : u ⊥ A) (⦅E⦆ : E ∈ B) → (app u ∷ E) ∈ (A ⇨ B)

⇨-sem : (⟦A⟧ : SemTy A) (⟦B⟧ : SemTy B) → SemTy (A ⇨ B)
⇨-sem ⟦A⟧ ⟦B⟧ .id = ε
⇨-sem ⟦A⟧ ⟦B⟧ .sn ε         = sn-ε
⇨-sem ⟦A⟧ ⟦B⟧ .sn (⦅u⦆ ∷ ⦅E⦆) = sn-app∷ (Sem-sn ⟦A⟧ ⦅u⦆) (⟦B⟧ .sn ⦅E⦆)
⇨-sem ⟦A⟧ ⟦B⟧ .red ε ()
⇨-sem ⟦A⟧ ⟦B⟧ .red (⦅u⦆ ∷ ⦅E⦆) (here (↦app r)) = sem-red ⦅u⦆ r ∷ ⦅E⦆
⇨-sem ⟦A⟧ ⟦B⟧ .red (⦅u⦆ ∷ ⦅E⦆) (there r)       = ⦅u⦆ ∷ ⟦B⟧ .red ⦅E⦆ r

-- Application

⦅app⦆ : (⦅t⦆ : t ⊥ (A ⇨ B)) (⦅u⦆ : u ⊥ A) → (t ∘ app u ∷ ε) ⊥ B
⦅app⦆ ⦅t⦆ ⦅u⦆ .run ⦅E⦆ = ⦅t⦆ .run (⦅u⦆ ∷ ⦅E⦆)

-- Type interpretation

⟦_⟧ : ∀ a → Predₑ a
⟦ bool ⟧  = ⟦bool⟧
⟦ a ⇒ b ⟧ = ⟦ a ⟧ ⇨ ⟦ b ⟧

-- Types are interpreted as semantic types

ty-sem : ∀ a → SemTy ⟦ a ⟧
ty-sem bool    = bool-sem
ty-sem (a ⇒ b) = ⇨-sem (ty-sem a) (ty-sem b)

-- Semantic objects are SN

sem-sn : t ⊥ ⟦ a ⟧ → SN t
sem-sn {a = a} ⦅t⦆ = Sem-sn (ty-sem a) ⦅t⦆

sem-snₑ : (e ∷ ε) ∈ ⟦ a ⟧ → SNₑ e
sem-snₑ {a = a} ⦅E⦆ = {! ⦅E⦆ !}

sem-snₛ : E ∈ ⟦ a ⟧ → SNₛ E
sem-snₛ {a = a} ⦅E⦆ = ty-sem a .sn ⦅E⦆

-- Soundness

-- Interpretation of stack constructors

⦅ε_⦆ : ∀ a → ε ∈ ⟦ a ⟧
⦅ε a ⦆ = ty-sem a .id

_⦅++⦆_ : ⟦ a ⟧ (b , E) → ⟦ b ⟧ (c , E′) → ⟦ a ⟧ (c , E ++ E′)
_⦅++⦆_     {E = ε} _         ⦅E′⦆ = ⦅E′⦆
_⦅++⦆_ {a = _ ⇒ _} (⦅u⦆ ∷ ⦅E⦆) ⦅E′⦆ = ⦅u⦆ ∷  ⦅E⦆ ⦅++⦆ ⦅E′⦆
_⦅++⦆_ {a = bool} {E = case u v ∷ E} ⦅E⦆ ⦅E′⦆ = {!!}

-- Interpretation of K

⦅K⦆ : (K ∙ ε) ⊥ ⟦ K-ty a b ⟧
⦅K⦆ .run ε                  = sn-Hd
⦅K⦆ .run (⦅t⦆ ∷ ε)          = sn-Kt (sem-sn ⦅t⦆)
⦅K⦆ .run (⦅t⦆ ∷ ⦅u⦆ ∷ ⦅E⦆)  = sn-KtuE (⦅t⦆ .run ⦅E⦆) (sem-sn ⦅t⦆) (sn-app (sem-sn ⦅u⦆)) (sem-snₛ ⦅E⦆)

-- Interpretation of S

⦅S⦆ : (S ∙ ε) ⊥ ⟦ S-ty c a b ⟧
⦅S⦆ .run ε                        = sn-Hd
⦅S⦆ .run (⦅t⦆ ∷ ε)                = sn-St (sem-sn ⦅t⦆)
⦅S⦆ .run (⦅t⦆ ∷ ⦅u⦆ ∷ ε)          = sn-Stu (sem-sn ⦅t⦆) (sem-sn ⦅u⦆)
⦅S⦆ .run (⦅t⦆ ∷ ⦅u⦆ ∷ ⦅v⦆ ∷ ⦅E⦆)  =
  sn-StuvE
   (⦅t⦆ .run (⦅v⦆ ∷ ⦅app⦆ ⦅u⦆ ⦅v⦆ ∷ ⦅E⦆))
   (sem-sn ⦅t⦆) (sem-sn ⦅u⦆) (sem-sn ⦅v⦆) (sem-snₛ ⦅E⦆)

-- Interpretation of constants

⦅_⦆ₕ : (h : Hd a) → (h ∙ ε) ⊥ ⟦ a ⟧
⦅ K ⦆ₕ = ⦅K⦆
⦅ S ⦆ₕ = ⦅S⦆
⦅ tt ⦆ₕ = ⦅tt⦆
⦅ ff ⦆ₕ = ⦅ff⦆

-- Interpretation of case

-- v ⊥ ⟦ a ⟧ → u ⊥ ⟦ a ⟧ → E ∈ ⟦ a ⟧ → case u v ∷ E ∈ ⟦bool⟧

bar : (⦅e⦆ : case t u ∷ ε ∈ ⟦bool⟧) (⦅E⦆ : E ∈ ⟦bool⟧) → case t u ∷ E ∈ ⟦bool⟧
bar ⦅e⦆ ⦅E⦆ = {!!}

foo : v ⊥ ⟦bool⟧ → case t u ∷ ε ∈ ⟦bool⟧ → (v ∘ case t u ∷ ε) ⊥ ⟦bool⟧
foo ⦅v⦆ ⦅e⦆ .run ⦅E⦆ = ⦅v⦆ .run {!!}

module _ (⟦A⟧ : SemTy A) where

  ⦅case-ε⦆' : (⦅t⦆ : t ⊥ A) (snt : SN t)
             (⦅u⦆ : u ⊥ A) (snu : SN u)
             (r : h ∙ case t u ∷ ε ↦ v) → SN v

  -- Contraction
  ⦅case-ε⦆' ⦅t⦆ (acc snt) ⦅u⦆ (acc snu) ↦tt = Sem-sn ⟦A⟧ ⦅t⦆
  ⦅case-ε⦆' ⦅t⦆ (acc snt) ⦅u⦆ (acc snu) ↦ff = Sem-sn ⟦A⟧ ⦅u⦆

  -- Reduction in t
  ⦅case-ε⦆' ⦅t⦆ (acc snt) ⦅u⦆ (acc snu) (↦E (here (↦caseₗ r))) =
    acc (⦅case-ε⦆' (sem-red ⦅t⦆ r) (snt r) ⦅u⦆ (acc snu))

  -- Reduction in u
  ⦅case-ε⦆' ⦅t⦆ (acc snt) ⦅u⦆ (acc snu) (↦E (here (↦caseᵣ r))) =
    acc (⦅case-ε⦆' ⦅t⦆ (acc snt) (sem-red ⦅u⦆ r) (snu r))

  -- No reduction in ε!
  ⦅case-ε⦆' ⦅t⦆ (acc snt) ⦅u⦆ (acc snu) (↦E (there ()))

  -- This is a special case of the lemma ⦅case⦆ below.
  ⦅case-ε⦆ : (⦅t⦆ : t ⊥ A) (⦅u⦆ : u ⊥ A) → case t u ∷ ε ∈ ⟦bool⟧
  ⦅case-ε⦆ ⦅t⦆ ⦅u⦆ .then = acc (⦅case-ε⦆' ⦅t⦆ (Sem-sn ⟦A⟧ ⦅t⦆) ⦅u⦆ (Sem-sn ⟦A⟧ ⦅u⦆))
  ⦅case-ε⦆ ⦅t⦆ ⦅u⦆ .else = acc (⦅case-ε⦆' ⦅t⦆ (Sem-sn ⟦A⟧ ⦅t⦆) ⦅u⦆ (Sem-sn ⟦A⟧ ⦅u⦆))


mutual
  ⦅case-tt⦆ : (⦅t⦆ : t ⊥ ⟦ a ⟧) (snt : SN t)
             (⦅u⦆ : u ⊥ ⟦ a ⟧) (snu : SN u)
             (⦅E⦆ : E ∈ ⟦ a ⟧) (snE : SNₛ E)
             (r : h ∙ case t u ∷ E ↦ v) → SN v
  ⦅case-tt⦆ ⦅t⦆ (acc snt) ⦅u⦆ (acc snu) ⦅E⦆ (acc snE) ↦tt = ⦅t⦆ .run ⦅E⦆
  ⦅case-tt⦆ ⦅t⦆ (acc snt) ⦅u⦆ (acc snu) ⦅E⦆ (acc snE) ↦ff = ⦅u⦆ .run ⦅E⦆
  ⦅case-tt⦆ ⦅t⦆ (acc snt) ⦅u⦆ (acc snu) ⦅E⦆ (acc snE) (↦E (here (↦caseₗ r))) = {!!}
  ⦅case-tt⦆ ⦅t⦆ (acc snt) ⦅u⦆ (acc snu) ⦅E⦆ (acc snE) (↦E (here (↦caseᵣ r))) = {!!}

  ⦅case-tt⦆ ⦅t⦆ (acc snt) ⦅u⦆ (acc snu) ⦅E⦆ (acc snE) (↦E (there r)) =
    acc (⦅case-tt⦆ {E = {!!}} ⦅t⦆ (acc snt) ⦅u⦆ (acc snu) (ty-sem _ .red ⦅E⦆ r) (snE r))

  ⦅case-tt⦆ {a = bool} {t = t} {u = u} {E = case t' u' ∷ E} ⦅t⦆ (acc snt) ⦅u⦆ (acc snu) ⦅E⦆ (acc snE) (↦E π) =
    acc (⦅case-tt⦆ {t = t ∘ case t' u' ∷ ε} {u = u ∘ case t' u' ∷ ε} {E = E} {!!} {!!} {!!} {!!} {!!} {!!} )
  ⦅case-tt⦆ {a = a ⇒ b} {E = app v ∷ E} ⦅t⦆ (acc snt) ⦅u⦆ (acc snu) (⦅v⦆ ∷ ⦅E⦆) (acc snE) (↦E π) = acc
    (⦅case-tt⦆ {E = E} (⦅app⦆ ⦅t⦆ ⦅v⦆) (⦅t⦆ .run (⦅v⦆ ∷ ⦅ε _ ⦆))
              (⦅app⦆ ⦅u⦆ ⦅v⦆) (⦅u⦆ .run (⦅v⦆ ∷ ⦅ε _ ⦆))
              ⦅E⦆ (sem-snₛ ⦅E⦆))

{-
--  ⦅case-tt⦆ {!!} {!!} {!!} {!!} {!!} {!!} {!!}

-- ⦅case-tt⦆ : (⦅v⦆ : v ⊥ ⟦ a ⟧) (snv : SN v)
--            (⦅u⦆ : u ⊥ ⟦ a ⟧) (snu : SN u)
--            (⦅E⦆ : E ∈ ⟦ a ⟧) (snE : SNₛ E) → SN (tt ∙ case u v ∷ E)
-- ⦅case-tt⦆ ⦅v⦆ (acc snv) ⦅u⦆ (acc snu) ⦅E⦆ (acc snE) = acc
--   λ{ ↦tt → ⦅u⦆ ⦅E⦆
--    ; (↦E π) → {!!}
--    ; (↦E (here (↦caseₗ r))) → {!r!}
--    ; (↦E (here (↦caseᵣ r))) → {!!}
--    ; (↦E (there r)) → {!!}
--    }


mutual

  ⦅case⦆ : (⦅v⦆ : v ⊥ ⟦ a ⟧) (⦅u⦆ : u ⊥ ⟦ a ⟧) (⦅E⦆ : E ∈ ⟦ a ⟧) → case u v ∷ E ∈ ⟦bool⟧
  ⦅case⦆ ⦅v⦆ ⦅u⦆ ⦅E⦆ = case-aux ⦅v⦆ (sem-sn ⦅v⦆) ⦅u⦆ (sem-sn ⦅u⦆) ⦅E⦆ (sem-snₛ ⦅E⦆)

  -- ⦅case⦆ {E = ε} ⦅v⦆ ⦅u⦆ ⦅E⦆ .then = sn-tt-case (sem-sn ⦅u⦆) {!!}
  -- ⦅case⦆ {E = e ∷ E} ⦅v⦆ ⦅u⦆ ⦅E⦆ .then = acc {!loop (sem-sn ⦅u⦆) (sem-sn ⦅v⦆)!}
  --   where
  --   loop :
  -- ⦅case⦆ {E = E} ⦅v⦆ ⦅u⦆ ⦅E⦆ .else = {!!}

  case-aux : (⦅v⦆ : v ⊥ ⟦ a ⟧) (snv : SN v)
             (⦅u⦆ : u ⊥ ⟦ a ⟧) (snu : SN u)
             (⦅E⦆ : E ∈ ⟦ a ⟧) (snE : SNₛ E) → case u v ∷ E ∈ ⟦bool⟧
  case-aux ⦅v⦆ (acc snv) ⦅u⦆ (acc snu) ⦅E⦆ (acc snE) .then = acc
    λ{ ↦tt     → ⦅u⦆ .run ⦅E⦆
     ; (↦E π) → {!!}
     ; (↦E (here r)) → {!!} ; (↦E (there r)) → {!!}
     }
  case-aux ⦅v⦆ (acc snv) ⦅u⦆ (acc snu) ⦅E⦆ (acc snE) .else = {!!}

-- ⦅case⦆ : (⟦A⟧ : SemTy A) (⦅v⦆ : v ⊥ ⟦ a ⟧) (⦅u⦆ : u ⊥ ⟦ a ⟧) (⦅E⦆ : E ∈ ⟦ a ⟧) → case u v ∷ E ∈ ⟦bool⟧
-- ⦅case⦆ ⟦A⟧ ⦅v⦆ ⦅u⦆ ⦅E⦆ .then = {!!}
-- ⦅case⦆ ⟦A⟧ ⦅v⦆ ⦅u⦆ ⦅E⦆ .else = {!!}

-- Term interpretation (soundness)

-- infix 100 ⦅_⦆ ⦅_⦆ₑ

mutual
  ⦅_⦆ₑ : (E : Stack a c) → E ∈ ⟦ a ⟧
  ⦅ ε {c = a} ⦆ₑ = ⦅ε a ⦆
  ⦅ app u ∷ E ⦆ₑ = ⦅ u ⦆ ∷ ⦅ E ⦆ₑ
  ⦅ case u v ∷ E ⦆ₑ .then = {!⦅ u ⦆!}
  ⦅ case u v ∷ E ⦆ₑ .else = sn-ff-case (⦅ v ⦆ .run ⦅ E ⦆ₑ) {!sem-snₛ ⦅ case u v ∷ E ⦆ₑ!}
-- ⦅ u ⦆ ∷ ⦅ E ⦆ₑ

  ⦅_⦆ : (t : Tm a) → t ⊥ ⟦ a ⟧
  ⦅ h ∙ E ⦆ .run ⦅E′⦆ = ⦅ h ⦆ₕ .run (⦅ E ⦆ₑ ⦅++⦆ ⦅E′⦆)

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
