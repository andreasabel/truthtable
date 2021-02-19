-- Strong normalization for simply-typed combinatory logic with booleans
-- using orthogonality.

-- Preamble
---------------------------------------------------------------------------

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Size

{-# BUILTIN REWRITE _≡_ #-}

variable i j : Size

-- Equality lemma

cong : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

-- Syntax
---------------------------------------------------------------------------

-- Types

infixr 6 _⇒_

data Ty : Set where
  o     : Ty
  bool  : Ty
  _⇒_   : (a b : Ty) → Ty

variable a b c d : Ty

-- Types of constants K and S

K-ty : (a b : Ty) → Ty
K-ty a b = a ⇒ (b ⇒ a)

S-ty : (c a b : Ty) → Ty
S-ty c a b = (c ⇒ (a ⇒ b)) ⇒ (c ⇒ a) ⇒ c ⇒ b

-- Heads

data Hd : (d : Ty) → Set where
  K   : Hd (K-ty a b)
  S   : Hd (S-ty c a b)
  tt  : Hd bool
  ff  : Hd bool

variable h : Hd a

-- Terms and stacks

infixl 5 _∙_ _∘_
infixr 6 _∷_ _++_

mutual

  -- Terms are heads under a stack

  data Tm : (d : Ty) → Set where
    _∙_ : (h : Hd a) (E : Stack i a c) → Tm c

  variable t t′ u u′ v v′ t' u' v' : Tm a

  -- Single elimination for function or boolean

  data Elim : (a c : Ty) → Set where
    app   : (u : Tm a)    → Elim (a ⇒ b)  b
    case  : (u v : Tm b)  → Elim bool     b

  variable e e′ e' e₀ e₁ e₂ : Elim a c

  -- Stacks of eliminations (sized type).

  data Stack (i : Size) : (a c : Ty) → Set where
    ε    : Stack i c c
    _∷_  : {j : Size< i} (e : Elim a b) (E : Stack j b c) → Stack i a c

{-
data Stack : (i : Size) (a c : Ty) → Set where
  ε    : Stack (↑ i) c c
  _∷_  : (e : Elim a b) (E : Stack i b c) → Stack (↑ i) a c
-}

  variable E E' E′ E₀ E₁ E₂ E₃ : Stack i a c

-- Stack concatenation

_++_ : Stack ∞ a b → Stack ∞ b c → Stack ∞ a c
ε        ++ E′ = E′
(u ∷ E)  ++ E′ = u ∷ (E ++ E′)

postulate
  ++-ε : (E ++ ε) ≡ E

{- Sized types trouble, see Abel/Vezzosi/Winterhalter, ICFP 2017
++-ε : {E : Stack ∞ a b} → _≡_ {A = Stack ∞ a b} (E ++ ε) E
++-ε {E = ε}     = refl
-- ++-ε {E = u ∷ E} rewrite ++-ε {E = E} = refl
++-ε {E = u ∷ E} = {!++-ε {E = E}!}
  -- cong (_∷_ {∞} u) (++-ε {E = E})
-}

++-assoc : (E₁ ++ E₂) ++ E₃ ≡ E₁ ++ (E₂ ++ E₃)
++-assoc {E₁ = ε}       = refl
++-assoc {E₁ = u ∷ E₁}  = cong (u ∷_) (++-assoc {E₁ = E₁})

{-# REWRITE ++-ε ++-assoc #-}

-- Plugging a term into a stack

_∘_ : Tm a → Stack ∞ a c → Tm c
h ∙ E ∘ E′ = h ∙ E ++ E′

postulate
  app-ε : t ∘ ε ≡ t

{-
app-ε : t ∘ ε ≡ t
app-ε {t = h ∙ E} = {! refl !} -- ++-ε
-}

app-app : t ∘ E ∘ E′ ≡ t ∘ E ++ E′
app-app {t = h ∙ E} = refl  -- ++-assoc

{-# REWRITE app-ε app-app #-}

-- Reduction
---------------------------------------------------------------------------

-- Reduction relations

infix 4 _↦_ _↦⁺_ _↦ₑ_ _↦ₛ_

-- One-step reduction in terms and stacks

mutual

  data _↦_ : (t t′ : Tm a) → Set where
    ↦K   : K   ∙ app t ∷ e              ∷ E ↦ t  ∘ E
    ↦S   : S   ∙ app t ∷ app u ∷ app v  ∷ E ↦ t  ∘ app v ∷ app (u ∘ app v ∷ ε) ∷ E
    ↦tt  : tt  ∙ case u v               ∷ E ↦ u  ∘ E
    ↦ff  : ff  ∙ case u v               ∷ E ↦ v  ∘ E
    ↦E   : (r : E ↦ₛ E′) → h ∙ E ↦ h ∙ E′

  data _↦ₑ_ : (e e' : Elim a c) → Set where
    ↦app    : (r : t ↦ t')  → app {a} {b} t  ↦ₑ app t'
    ↦caseₗ  : (r : u ↦ u')  → case u v       ↦ₑ case u' v
    ↦caseᵣ  : (r : v ↦ v')  → case u v       ↦ₑ case u v'

  -- Contains single frame permutation

  data _↦ₛ_ : (E E′ : Stack i a c) → Set where
    π      : {E : Stack i a c} → (case u v ∷ e ∷ E) ↦ₛ (case (u ∘ e ∷ ε) (v ∘ e ∷ ε) ∷ E)
    here   : (r : e ↦ₑ e′)     → e ∷ E              ↦ₛ e′ ∷ E
    there  : (r : E ↦ₛ E′)     → e ∷ E              ↦ₛ e  ∷ E′

-- Closure properties of one-step reduction

-- Concatenation ++ is a congruence

++↦ₗ  :  E ↦ₛ E′
     →  E ++ E₁ ↦ₛ E′ ++ E₁
++↦ₗ π          = π
++↦ₗ (here  r)  = here r
++↦ₗ (there r)  = there (++↦ₗ r)

++↦ᵣ  :  ∀ (E : Stack i a b)
      →  E₁ ↦ₛ E₂
      →  E ++ E₁ ↦ₛ E ++ E₂
++↦ᵣ ε       r = r
++↦ᵣ(u ∷ E)  r = there (++↦ᵣ E r)

-- Application ∘ is a congruence

∘↦ₗ  :  t ↦ t′
    →  t ∘ E ↦ t′ ∘ E
∘↦ₗ ↦K      = ↦K  -- rewrite app-app
∘↦ₗ ↦S      = ↦S
∘↦ₗ ↦tt     = ↦tt
∘↦ₗ ↦ff     = ↦ff
∘↦ₗ (↦E r)  = ↦E (++↦ₗ r)

∘↦ᵣ  :  ∀ (t : Tm a)
     →  E ↦ₛ E′
     →  t ∘ E ↦ t ∘ E′
∘↦ᵣ (_∙_ h E) r = ↦E (++↦ᵣ E r)

-- Transitive closure

{- infixr 100 _⁺ -}

data _⁺ {A : Set} (R : A → A → Set) (t v : A) : Set where
  sg   : (r : R t v) → (R ⁺) t v
  _∷_  : {u : A} (r : R t u) (rs : (R ⁺) u v) → (R ⁺) t v

_↦⁺_ : (t t′ : Tm a) → Set
_↦⁺_ = _↦_ ⁺

-- Strong normalization
---------------------------------------------------------------------------

-- Predicates

infix 2 _⊂_

_⊂_ : {A : Set} (P Q : A → Set) → Set
P ⊂ Q = ∀{t} (r : P t) → Q t

-- Accessibility

data Acc {A : Set} (R : A → A → Set) (t : A) : Set where
  acc : (h : ∀ {t′} (r : R t t′) → Acc R t′) → Acc R t

-- A relation is wellfounded if its transitive closure is.

wf⁻ : {A : Set} {R : A → A → Set} → Acc (R ⁺) ⊂ Acc R
wf⁻ (acc h) = acc λ r → wf⁻ (h (sg r))

-- If a relation is well-founded, so is its transitive closure.

wf⁺ : {A : Set} {R : A → A → Set} → Acc R ⊂ Acc (R ⁺)
wf⁺ {R = R} h₀ = acc (loop h₀)
  where
  loop : ∀{t} → Acc R t → (R ⁺) t ⊂ Acc (R ⁺)
  loop (acc h) (sg r)    = wf⁺ (h r)
  loop (acc h) (r ∷ rs)  = loop (h r) rs

-- Reducts of SN things are SN things.

sn-red : {A : Set} {R : A → A → Set}{t t′ : A} → Acc R t → R t t′ → Acc R t′
sn-red (acc sn) r = sn r

-- Strong normalization: t is SN if all of its reducts are, inductively.

SN SN⁺ : Tm a → Set
SN   = Acc _↦_
SN⁺  = Acc _↦⁺_

SNₑ : Elim a c → Set
SNₑ = Acc _↦ₑ_

SNₛ : Stack i a c → Set
SNₛ = Acc _↦ₛ_

-- Deconstruction of SN t.

sn-spine : SN (h ∙ E) → SNₛ E
sn-spine (acc sntE) = acc λ r → sn-spine (sntE (↦E r))

-- Constants are SN.

-- Heads are SN.

sn-Hd : SN (h ∙ ε)
sn-Hd = acc λ{ (↦E ()) }

-- The empty stack is SN.

sn-ε : SNₛ (ε {c = a})
sn-ε = acc λ()

-- Function elimination preserves SN.

sn-app∷ : SN u → SNₛ E → SNₛ (app u ∷ E)
sn-app∷ (acc snu) snE@(acc snE') = acc λ where
   (here (↦app r))  → sn-app∷ (snu r)    snE
   (there r)        → sn-app∷ (acc snu)  (snE' r)

-- Underapplied functions are SN.

-- Kt is SN.

sn-Kt : SN t → SN (K {a} {b} ∙ app t ∷ ε)
sn-Kt (acc snt) = acc λ{ (↦E (here (↦app r))) → sn-Kt (snt r) }

-- St is SN.

sn-St : SN t → SN (S {a} {b} ∙ app t ∷ ε)
sn-St (acc snt) = acc λ{ (↦E (here (↦app r))) → sn-St (snt r) }

-- Stu is SN.

sn-Stu : SN t → SN u → SN (S {a} {b} ∙ app t ∷ app u ∷ ε)
sn-Stu (acc snt) (acc snu) = acc λ where
   (↦E (here (↦app r)))          → sn-Stu (snt r)    (acc snu)
   (↦E (there (here (↦app r))))  → sn-Stu (acc snt)  (snu r)

-- Redexes are SN.

-- KtuE is SN.

sn-KtuE : SN (t ∘ E) → SN u → SN (K ∙ app t ∷ app u ∷ E)
sn-KtuE {t = t} sntE@(acc h) (acc snu)  = acc λ where
   ↦K                            → sntE
   (↦E (here (↦app r)))          → sn-KtuE (h (∘↦ₗ r))    (acc snu)
   (↦E (there (here (↦app r))))  → sn-KtuE sntE           (snu r)
   (↦E (there (there r)))        → sn-KtuE (h (∘↦ᵣ t r))  (acc snu)

-- StuvE is SN.

sn-StuvE : SN⁺ (t ∘ app v ∷ app (u ∘ app v ∷ ε) ∷ E)
          → SN (S ∙ app t ∷ app u ∷ app v ∷ E)
sn-StuvE {t = t} {u = u} sntvuvE@(acc h) = acc λ where
  ↦S →
    wf⁻ sntvuvE

  (↦E (here (↦app r))) →
    sn-StuvE (h (sg (∘↦ₗ r)))

  (↦E (there (here (↦app r)))) →
    sn-StuvE (h (sg (∘↦ᵣ t (there (here (↦app (∘↦ₗ r)))))))

  (↦E (there (there (here (↦app r))))) →
    sn-StuvE (h (∘↦ᵣ t (here (↦app r)) ∷
                 sg (∘↦ᵣ t (there (here (↦app (∘↦ᵣ u (here (↦app r)))))))))

  (↦E (there (there (there r)))) →
    sn-StuvE (h (sg (∘↦ᵣ t (there (there r)))))


-- This is the key lemma:

mutual

  sn-case : {E : Stack i a c} (sntE : SN (t ∘ E)) (snuE : SN (u ∘ E)) → SN (h ∙ case t u ∷ E)
  sn-case sntE snuE = acc (sn-case' sntE snuE)

  -- Case distinction on reductions of (h ∙ case t u ∷ E):

  sn-case' : {E : Stack i a c}
            (sntE : SN (t ∘ E))
            (snuE : SN (u ∘ E))
            (r : h ∙ case t u ∷ E ↦ v) → SN v
  sn-case'  sntE snuE ↦tt = sntE
  sn-case'  sntE snuE ↦ff = snuE
  sn-case'  (acc sntE) snuE (↦E (here (↦caseₗ r)))   = sn-case (sntE (∘↦ₗ r)) snuE
  sn-case'  sntE (acc snuE) (↦E (here (↦caseᵣ r)))   = sn-case sntE (snuE (∘↦ₗ r))
  sn-case'  {t = t} {u = u}
            (acc sntE) (acc snuE) (↦E (there r))     = sn-case (sntE (∘↦ᵣ t r)) (snuE (∘↦ᵣ u r))
  sn-case'  {i = .(↑ i)} sntE snuE (↦E (π {i = i}))  = sn-case {i = i} sntE snuE

{- -- Internal error with this version (#4929)
sn-case : {E : Stack i a c}
          (sntE : SN (t ∘ E))
          (snuE : SN (u ∘ E))
          → SN (h ∙ case t u ∷ E)
sn-case {i = i} {t = t} {u = u} (acc sntE) (acc snuE) = acc
  λ { ↦tt → acc sntE
    ; ↦ff → acc snuE
    ; (↦E (here (↦caseₗ r)))  → sn-case (sntE (∘↦ₗ r)) (acc snuE)
    ; (↦E (here (↦caseᵣ r))) → sn-case (acc sntE) (snuE (∘↦ₗ r))
    ; (↦E (there r))         → sn-case (sntE (∘↦ᵣ t r)) (snuE (∘↦ᵣ u r))
    ; (↦E (π {i = j}))       → sn-case {i = j} (acc sntE) (acc snuE)
    }
-}

-- Semantic types
---------------------------------------------------------------------------

-- Stack sets

record Cont a : Set where
  constructor cont
  field
    {len}  : Size
    {tgt}  : Ty
    st     : Stack len a tgt

Predₛ : (a : Ty) → Set₁
Predₛ a = (cE : Cont a) → Set

variable A B C D : Predₛ a

-- Elementhood in stack sets

infix 2 _∈_

_∈_ : (E : Stack i a c) (A : Predₛ a) → Set
E ∈ A = A (cont E)

-- Semantic objects

-- We use a record to help Agda's unifier.
record _⊥_ (t : Tm a) (A : Predₛ a) : Set where
  field run : (⦅E⦆ : E ∈ A) → SN (t ∘ E)
open _⊥_

module Remark1 where

  -- Semantic objects are closed under reduction.

  sem-red : t ⊥ A → t ↦ t′ → t′ ⊥ A
  sem-red ⦅t⦆ r .run ⦅E⦆ = sn-red (⦅t⦆ .run ⦅E⦆) (∘↦ₗ r)

-- Singleton stack set {ε}

data ⟦o⟧ {a} : Predₛ a where
  ε : ε ∈ ⟦o⟧

-- Semantic booleans

record ⟦bool⟧ (cE : Cont bool) : Set where
  field br : let cont E = cE in ∀ h → SN (h ∙ E)
open ⟦bool⟧

-- Boolean values

⦅tt⦆ : (tt ∙ ε) ⊥ ⟦bool⟧
⦅tt⦆ .run ⦅E⦆ = ⦅E⦆ .br tt

⦅ff⦆ : (ff ∙ ε) ⊥ ⟦bool⟧
⦅ff⦆ .run ⦅E⦆ = ⦅E⦆ .br ff

-- Interpretation of case

⦅case⦆  :  (⦅t⦆ : t ⊥ A)
           (⦅u⦆ : u ⊥ A)
           (⦅E⦆ : E ∈ A)
        →  case t u ∷ E ∈ ⟦bool⟧
⦅case⦆ ⦅t⦆ ⦅u⦆ ⦅E⦆ .br h = sn-case (⦅t⦆ .run ⦅E⦆) (⦅u⦆ .run ⦅E⦆)

-- Function space on semantic types

data _⟦→⟧_ (A : Predₛ a) (B : Predₛ b) : Predₛ (a ⇒ b) where
  ε    : ε ∈ (A ⟦→⟧ B)
  _∷_  : (⦅u⦆ : u ⊥ A) (⦅E⦆ : E ∈ B) → (app u ∷ E) ∈ (A ⟦→⟧ B)

-- Application

⦅app⦆  :  (⦅t⦆ : t ⊥ (A ⟦→⟧ B))
          (⦅u⦆ : u ⊥ A)
       →  (t ∘ app u ∷ ε) ⊥ B
⦅app⦆ ⦅t⦆ ⦅u⦆ .run ⦅E⦆ = ⦅t⦆ .run (⦅u⦆ ∷ ⦅E⦆)

-- Semantic Types
---------------------------------------------------------------------------

-- Semantic types are specified by sets of SN stacks that contain ε.

record SemTy (A : Predₛ a) : Set where
  field
    id  : ε ∈ A
    sn  : (⦅E⦆ : E ∈ A) → SNₛ E
open SemTy

Sem-sn : (⟨A⟩ : SemTy A) (⦅t⦆ : t ⊥ A) → SN t
Sem-sn ⟨A⟩ ⦅t⦆ = ⦅t⦆ .run (⟨A⟩ .id)

{-
Sem-snₑ : (⟨A⟩ : SemTy A) (⦅E⦆ : E ∈ A) → SNₛ E
Sem-snₑ ⟨A⟩ = ⟨A⟩ .sn
-}

-- SN is the semantic type given by {ε}

⟨o⟩ : SemTy (⟦o⟧ {a = a})
⟨o⟩ .id    = ε
⟨o⟩ .sn ε  = sn-ε

⟨bool⟩ : SemTy ⟦bool⟧
⟨bool⟩ .id .br h  = sn-Hd
⟨bool⟩ .sn  ⦅E⦆    = sn-spine (⦅E⦆ .br tt)

_⟨→⟩_ : (⟨A⟩ : SemTy A) (⟨B⟩ : SemTy B) → SemTy (A ⟦→⟧ B)
(⟨A⟩ ⟨→⟩ ⟨B⟩) .id            = ε
(⟨A⟩ ⟨→⟩ ⟨B⟩) .sn ε          = sn-ε
(⟨A⟩ ⟨→⟩ ⟨B⟩) .sn (⦅u⦆ ∷ ⦅E⦆)  = sn-app∷ (Sem-sn ⟨A⟩ ⦅u⦆) (⟨B⟩ .sn ⦅E⦆)

-- Soundness
---------------------------------------------------------------------------

-- Type interpretation

⟦_⟧ : ∀ a → Predₛ a
⟦ o ⟧      = ⟦o⟧
⟦ bool ⟧   = ⟦bool⟧
⟦ a ⇒ b ⟧  = ⟦ a ⟧ ⟦→⟧ ⟦ b ⟧

-- Types are interpreted as semantic types

⟨_⟩ : ∀ a → SemTy ⟦ a ⟧
⟨ o     ⟩  = ⟨o⟩
⟨ bool  ⟩  = ⟨bool⟩
⟨ a ⇒ b ⟩  = ⟨ a ⟩ ⟨→⟩ ⟨ b ⟩

-- Semantic objects are SN

sem-sn : t ⊥ ⟦ a ⟧ → SN t
sem-sn {a = a} ⦅t⦆ = Sem-sn ⟨ a ⟩ ⦅t⦆

{-
sem-snₛ : E ∈ ⟦ a ⟧ → SNₛ E
sem-snₛ {a = a} ⦅E⦆ = ⟨ a ⟩ .sn ⦅E⦆
-}

-- Interpretation of K

⦅K⦆ : (K ∙ ε) ⊥ ⟦ K-ty a b ⟧
⦅K⦆ .run ε                  = sn-Hd
⦅K⦆ .run (⦅t⦆ ∷ ε)          = sn-Kt (sem-sn ⦅t⦆)
⦅K⦆ .run (⦅t⦆ ∷ ⦅u⦆ ∷ ⦅E⦆)  = sn-KtuE (⦅t⦆ .run ⦅E⦆) (sem-sn ⦅u⦆)
{- ⦅K⦆ .run (⦅t⦆ ∷ ⦅u⦆ ∷ ⦅E⦆)  = sn-KtuE (⦅t⦆ .run ⦅E⦆) (sem-sn ⦅t⦆) (sn-app (sem-sn ⦅u⦆)) (sem-snₛ ⦅E⦆)
-}

-- Interpretation of S

⦅S⦆ : (S ∙ ε) ⊥ ⟦ S-ty c a b ⟧
⦅S⦆ .run ε                        = sn-Hd
⦅S⦆ .run (⦅t⦆ ∷ ε)                = sn-St (sem-sn ⦅t⦆)
⦅S⦆ .run (⦅t⦆ ∷ ⦅u⦆ ∷ ε)          = sn-Stu (sem-sn ⦅t⦆) (sem-sn ⦅u⦆)
⦅S⦆ .run (⦅t⦆ ∷ ⦅u⦆ ∷ ⦅v⦆ ∷ ⦅E⦆)  = sn-StuvE (wf⁺ (⦅t⦆ .run (⦅v⦆ ∷ ⦅app⦆ ⦅u⦆ ⦅v⦆ ∷ ⦅E⦆)))
{-
⦅S⦆ .run (⦅t⦆ ∷ ⦅u⦆ ∷ ⦅v⦆ ∷ ⦅E⦆)  =
  sn-StuvE
   (⦅t⦆ .run (⦅v⦆ ∷ ⦅app⦆ ⦅u⦆ ⦅v⦆ ∷ ⦅E⦆))
   (sem-sn ⦅t⦆) (sem-sn ⦅u⦆) (sem-sn ⦅v⦆) (sem-snₛ ⦅E⦆)
-}

-- Interpretation of constants

⦅_⦆ₕ : (h : Hd a) → (h ∙ ε) ⊥ ⟦ a ⟧
⦅ K ⦆ₕ   = ⦅K⦆
⦅ S ⦆ₕ   = ⦅S⦆
⦅ tt ⦆ₕ  = ⦅tt⦆
⦅ ff ⦆ₕ  = ⦅ff⦆

-- Term interpretation (soundness)

mutual
  ⦅_⦆ : (t : Tm a) → t ⊥ ⟦ a ⟧
  ⦅ h ∙ E ⦆ .run ⦅E′⦆ = ⦅ h ⦆ₕ .run (⦅ E ⦆ₛ ⦅E′⦆)

  ⦅_⦆ₛ : (E : Stack i a c) (⦅E'⦆ : E' ∈ ⟦ c ⟧) → (E ++ E') ∈ ⟦ a ⟧
  ⦅ ε {c = a}    ⦆ₛ  ⦅E'⦆ = ⦅E'⦆
  ⦅ app u ∷ E    ⦆ₛ  ⦅E'⦆ = ⦅ u ⦆ ∷ ⦅ E ⦆ₛ ⦅E'⦆
  ⦅ case u v ∷ E ⦆ₛ  ⦅E'⦆ = ⦅case⦆ ⦅ u ⦆ ⦅ v ⦆ (⦅ E ⦆ₛ ⦅E'⦆)

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
