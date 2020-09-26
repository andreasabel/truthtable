{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

-- Strong normalization for simply-typed combinatory logic with booleans
-- using orthogonality.

module SK-Bool-ortho where

-- open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _≥_; _<_; _>_; s≤s) renaming (z≤n to z≤)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-assoc; ≤-refl; ≤-trans; n≤1+n; +-monoˡ-≤; +-monoʳ-≤)
open import Data.Unit.Base using () renaming (⊤ to True)
open import Data.Empty using () renaming (⊥ to False)
open import Function using (case_of_)
-- open import Level using (suc)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; ∃; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Size

{-# BUILTIN REWRITE _≡_ #-}

-- variable q q' q′ : Bool

variable k n m : ℕ
variable p : n ≤ m

variable i : Size

data WF (i : Size) (n : ℕ) : Set where
  acc : {j : Size< i} (h : ∀{m} → m < n → WF j m) → WF i n

postulate wf-≤ : WF i n → m ≤ n → WF i m
-- wf-≤ (acc h)

wf-aux : (p : m ≤ n) → WF ∞ m
wf-aux z≤ = acc λ()
wf-aux (s≤s p) = acc λ{ (s≤s r) → wf-aux (≤-trans r p)}

wf-ℕ : WF ∞ n
wf-ℕ = wf-aux ≤-refl

{-# REWRITE +-suc +-identityʳ +-assoc #-}

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
infixr 6 _∷_ _++_

mutual

  data Tm : (d : Ty) → Set where
    _∙_ : (h : Hd a) (E : Stack n a c) → Tm c

  variable t t′ u u′ v v′ t' u' v' : Tm a

  data Elim : (a c : Ty) → Set where
    app  : (u : Tm a) → Elim (a ⇒ b) b
    case : (u v : Tm a) → Elim bool a

  variable e e′ e' e₀ e₁ e₂ : Elim a c

  data Stack : (n : ℕ) (a c : Ty) → Set where
    ε    : Stack zero c c
    _∷_  : (e : Elim a b) (E : Stack n b c) → Stack (suc n) a c

  variable E E' E′ E₀ E₁ E₂ E₃ : Stack n a c

-- Stack concatenation

_++_ : Stack n a b → Stack m b c → Stack (n + m) a c
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

_∘_ : Tm a → Stack n a c → Tm c
h ∙ E ∘ E′ = h ∙ E ++ E′

app-ε : t ∘ ε ≡ t
app-ε {t = h ∙ E} = refl -- ++-ε

app-app : t ∘ E ∘ E′ ≡ t ∘ E ++ E′
app-app {t = h ∙ E} = refl  -- ++-assoc

{-# REWRITE app-ε app-app #-}

-- Reduction relations

infix 4 _↦_ _↦ₑ_ _↦ₛ[_]_

-- One-step reduction in terms and stacks

mutual

  data _↦_ : (t t′ : Tm a) → Set where
    ↦K  : K  ∙ app t ∷ e             ∷ E ↦ t ∘ E
    ↦S  : S  ∙ app t ∷ app u ∷ app v ∷ E ↦ t ∘ app v ∷ app (u ∘ app v ∷ ε) ∷ E
    ↦tt : tt ∙ case u v              ∷ E ↦ u ∘ E
    ↦ff : ff ∙ case u v              ∷ E ↦ v ∘ E
    ↦E  : (r : E ↦ₛ[ p ] E′) → h ∙ E ↦ h ∙ E′

  data _↦ₑ_ : (e e' : Elim a c) → Set where
    ↦app   : (r : t ↦ t') → app {a} {b} t ↦ₑ app t'
    ↦caseₗ : (r : u ↦ u') → case u v ↦ₑ case u' v
    ↦caseᵣ : (r : v ↦ v') → case u v ↦ₑ case u v'

  -- Contains single frame permutation

  data _↦ₛ[_]_ : (E : Stack n a c) .(n≥m : n ≥ m) (E′ : Stack m a c) → Set where
    π     : (case u v ∷ e ∷ E) ↦ₛ[ n≤1+n _ ] (case (u ∘ e ∷ ε) (v ∘ e ∷ ε) ∷ E)
    here  : (r : e ↦ₑ  e′) → e ∷ E ↦ₛ[ ≤-refl ] e′ ∷ E
    there : (r : E ↦ₛ[ p ] E′) → e ∷ E ↦ₛ[ s≤s p ] e  ∷ E′

-- Closure properties of one-step reduction

-- Concatenation ++ is a congruence

++↦ₗ : ∀ -- {p : m ≤ n}{E : Stack n a b}{E′ : Stack m a b}
       {E₁ : Stack k b c}
    → E ↦ₛ[ p ] E′ → E ++ E₁ ↦ₛ[ +-monoˡ-≤ k p ] E′ ++ E₁
++↦ₗ π         = π
++↦ₗ (here  r) = here r
++↦ₗ {k = k} (there {p = p} r) = there {p = +-monoˡ-≤ k p} (++↦ₗ {p = p} r)

++↦ᵣ : ∀ (E : Stack k a b) → E₁ ↦ₛ[ p ] E₂ → E ++ E₁ ↦ₛ[ +-monoʳ-≤ k p ] E ++ E₂
++↦ᵣ ε r = r
++↦ᵣ {k = suc k} {p = p} (u ∷ E) r = there {p = +-monoʳ-≤ k p} (++↦ᵣ {p = p} E r)

-- Application ∘ is a congruence

∘↦ₗ : ∀{E : Stack n a c} → t ↦ t′ → t ∘ E ↦ t′ ∘ E
∘↦ₗ ↦K     = ↦K  -- rewrite app-app
∘↦ₗ ↦S     = ↦S
∘↦ₗ ↦tt    = ↦tt
∘↦ₗ ↦ff    = ↦ff
∘↦ₗ {n = n} (↦E {p = p} r) = ↦E {p = +-monoˡ-≤ n p} (++↦ₗ {p = p} r)

∘↦ᵣ : E ↦ₛ[ p ] E′ → t ∘ E ↦ t ∘ E′
∘↦ᵣ {p = p} {t = _∙_ {n = n} h E} r = ↦E {p = +-monoʳ-≤ n p} (++↦ᵣ {p = p} E r)

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

data SNₛ (E : Stack n a c) : Set where
  acc : (∀ {m p} {E' : Stack m a c} (r : E ↦ₛ[ p ] E') → SNₛ E') → SNₛ E

-- Deconstruction of SN t

sn-spine : SN (h ∙ E) → SNₛ E
sn-spine (acc sntE) = acc λ {m} {p} r → sn-spine (sntE (↦E {p = p} r))

-- Elim constructors preserve SN

sn-app : SN u → SNₑ (app {a} {b} u)
sn-app (acc snu) = acc λ{ (↦app r) → sn-app (snu r) }

-- Stack constructors preserve SN

sn-ε : SNₛ (ε {c = a})
sn-ε = acc λ()

sn-app∷ : SN u → SNₛ E → SNₛ (app u ∷ E)
sn-app∷ (acc snu) snE@(acc snE') = acc
  λ{ (here (↦app r)) → sn-app∷ (snu r) snE
   ; (there {p = p} r) → sn-app∷ (acc snu) (snE' {p = p} r)
   }

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

-- This is the key lemma:

case-sn' : {E : Stack n a c} (i : Size) (w : WF i n)
          (sntE : SN (t ∘ E))
          (snuE : SN (u ∘ E))
          (r : h ∙ case t u ∷ E ↦ v) → SN v
case-sn' i w sntE snuE ↦tt = sntE
case-sn' i w sntE snuE ↦ff = snuE
case-sn' i w (acc sntE) snuE (↦E (here (↦caseₗ r))) = acc (case-sn' i w (sntE (∘↦ₗ r)) snuE)
case-sn' i w sntE (acc snuE) (↦E (here (↦caseᵣ r))) = acc (case-sn' i w sntE (snuE (∘↦ₗ r)))
case-sn' {t = t} {u = u} i w (acc sntE) (acc snuE) (↦E (there {p = p} r)) = acc
  (case-sn' i (wf-≤ w p)
    (sntE (∘↦ᵣ {p = p} {t = t} r))
    (snuE (∘↦ᵣ {p = p} {t = u} r))
  )
case-sn' i (acc {j} w) sntE snuE (↦E π) = acc (case-sn' j (w ≤-refl) sntE snuE )

case-sn : (sntE : SN (t ∘ E)) (snuE : SN (u ∘ E)) → SN (h ∙ case t u ∷ E)
case-sn sntE snuE = acc (case-sn' ∞ wf-ℕ sntE snuE)

-- KtuE is SN

sn-KtuE : SN (t ∘ E) → SN t → SNₑ e → SNₛ E → SN (K ∙ app t ∷ e ∷ E)
sn-KtuE {t = t} sntE (acc snt) (acc sne) snE@(acc snE') = acc
  λ{ ↦K                     → sntE
   ; (↦E (here (↦app r)))   → sn-KtuE (sn-red sntE (∘↦ₗ r)) (snt r) (acc sne) snE
   ; (↦E (there (here  r))) → sn-KtuE sntE                 (acc snt) (sne r) snE
   ; (↦E {p = s≤s (s≤s p)} (there (there r))) →
       sn-KtuE (sn-red sntE (∘↦ᵣ {p = p} {t = t} r)) (acc snt) (acc sne) (snE' {p = p} r)
   }

sn-KtuE' : SN (t ∘ E) → SNₑ e → SN (K ∙ app t ∷ e ∷ E)
sn-KtuE' {t = t} sntE@(acc h) (acc sne)  = acc
  λ{ ↦K                     → sntE
   ; (↦E (here (↦app r)))   → sn-KtuE' (h (∘↦ₗ r)) (acc sne)
   ; (↦E (there (here  r))) → sn-KtuE' sntE       (sne r)
   ; (↦E {p = s≤s (s≤s p)} (there (there r))) →
       sn-KtuE' (h (∘↦ᵣ {p = p} {t = t} r)) (acc sne)
   }

-- StuvE is SN

sn-StuvE : SN (t ∘ app v ∷ app (u ∘ app v ∷ ε) ∷ E) → SN t → SN u → SN v → SNₛ E → SN (S ∙ app t ∷ app u ∷ app v ∷ E)
sn-StuvE {t = t} {u = u} sntvuvE (acc snt) (acc snu) (acc snv) snE@(acc snE') = acc
  λ{ ↦S →
       sntvuvE

   ; (↦E (here (↦app r))) →
       sn-StuvE (sn-red sntvuvE (∘↦ₗ r))
         (snt r) (acc snu) (acc snv) snE

   ; (↦E (there {p = p} (here (↦app r)))) →
       sn-StuvE (sn-red sntvuvE (∘↦ᵣ {p = p} {t = t} (there {p = ≤-refl} (here (↦app (∘↦ₗ r))))))
         (acc snt) (snu r) (acc snv) snE

   ; (↦E (there (there {p = p} (here (↦app r))))) →
       sn-StuvE (sn-red
                  (sn-red sntvuvE  (∘↦ᵣ {p = s≤s p} {t = t} (here (↦app r))))
                  (∘↦ᵣ {p = s≤s p} {t = t} (there {p = p} (here (↦app (∘↦ᵣ {p = ≤-refl} {t = u} (here (↦app r))))))))
         (acc snt) (acc snu) (snv r) snE

   ; (↦E (there (there (there {p = p} r)))) →
       sn-StuvE (sn-red sntvuvE (∘↦ᵣ {p = s≤s (s≤s p)} {t = t} (there {p = s≤s p} (there {p = p} r))))
         (acc snt) (acc snu) (acc snv) (snE' {p = p} r)
   }

{-
-- NEED sized SN
sn-StuvE' : SN (t ∘ app v ∷ app (u ∘ app v ∷ ε) ∷ E) → SN (S ∙ app t ∷ app u ∷ app v ∷ E)
sn-StuvE' {t = t} {u = u} sntvuvE@(acc h)  = acc
  λ{ ↦S →
       sntvuvE

   ; (↦E (here (↦app r))) →
       sn-StuvE' (h (∘↦ₗ r))

   ; (↦E (there {p = p} (here (↦app r)))) →
       sn-StuvE' (h (∘↦ᵣ {p = p} {t = t} (there {p = ≤-refl} (here (↦app (∘↦ₗ r))))))

   ; (↦E (there (there {p = p} (here (↦app r))))) →
       sn-StuvE' (sn-red
                  (h (∘↦ᵣ {p = s≤s p} {t = t} (here (↦app r))))
                  (∘↦ᵣ {p = s≤s p} {t = t} (there {p = p} (here (↦app (∘↦ᵣ {p = ≤-refl} {t = u} (here (↦app r))))))))

   ; (↦E (there (there (there {p = p} r)))) →
       sn-StuvE' (h (∘↦ᵣ {p = s≤s (s≤s p)} {t = t} (there {p = s≤s p} (there {p = p} r))))
   }
-}

-- Stack sets

record Cont a : Set where
  constructor cont
  field
    {len} : ℕ
    {tgt} : Ty
    st    : Stack len a tgt

Predₑ : (a : Ty) → Set₁
Predₑ a = (cE : Cont a) → Set

variable A B C D : Predₑ a

-- Elementhood in stack sets

infix 2 _∈_

_∈_ : (E : Stack n a c) (A : Predₑ a) → Set
E ∈ A = A (cont E)

-- Semantic types are specified by sets of SN stacks that contain ε.

record SemTy (A : Predₑ a) : Set where
  field
    id  : ε ∈ A
    sn  : (⦅E⦆ : E ∈ A) → SNₛ E
open SemTy

-- Semantic objects

-- We use a record to help Agda's unifier.
record _⊥_ (t : Tm a) (A : Predₑ a) : Set where
  field
    run : (⦅E⦆ : E ∈ A) → SN (t ∘ E)
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

-- Singleton stack set {ε}

data Idₑ {a} : Predₑ a where
  ε : ε ∈ Idₑ

-- SN is the semantic type given by {ε}

⟦Id⟧ : SemTy (Idₑ {a = a})
⟦Id⟧ .id    = ε
⟦Id⟧ .sn  ε = sn-ε

-- Semantic booleans

record ⟦bool⟧ (cE : Cont bool) : Set where
  field
    br : let cont E = cE in ∀ h → SN (h ∙ E)
open ⟦bool⟧

bool-sem : SemTy ⟦bool⟧
bool-sem .id .br h = sn-Hd
bool-sem .sn  ⦅E⦆   = sn-spine (⦅E⦆ .br tt)

-- Boolean values

⦅tt⦆ : (tt ∙ ε) ⊥ ⟦bool⟧
⦅tt⦆ .run ⦅E⦆ = ⦅E⦆ .br tt

⦅ff⦆ : (ff ∙ ε) ⊥ ⟦bool⟧
⦅ff⦆ .run ⦅E⦆ = ⦅E⦆ .br ff

-- Function space on semantic types

data _⇨_ (A : Predₑ a) (B : Predₑ b) : Predₑ (a ⇒ b) where
  ε   : ε ∈ (A ⇨ B)
  _∷_ : (⦅u⦆ : u ⊥ A) (⦅E⦆ : E ∈ B) → (app u ∷ E) ∈ (A ⇨ B)

⇨-sem : (⟦A⟧ : SemTy A) (⟦B⟧ : SemTy B) → SemTy (A ⇨ B)
⇨-sem ⟦A⟧ ⟦B⟧ .id = ε
⇨-sem ⟦A⟧ ⟦B⟧ .sn ε         = sn-ε
⇨-sem ⟦A⟧ ⟦B⟧ .sn (⦅u⦆ ∷ ⦅E⦆) = sn-app∷ (Sem-sn ⟦A⟧ ⦅u⦆) (⟦B⟧ .sn ⦅E⦆)

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

sem-snₛ : E ∈ ⟦ a ⟧ → SNₛ E
sem-snₛ {a = a} ⦅E⦆ = ty-sem a .sn ⦅E⦆

-- Soundness

-- Interpretation of stack constructors

⦅ε_⦆ : ∀ a → ε ∈ ⟦ a ⟧
⦅ε a ⦆ = ty-sem a .id

-- Interpretation of K

⦅K⦆ : (K ∙ ε) ⊥ ⟦ K-ty a b ⟧
⦅K⦆ .run ε                  = sn-Hd
⦅K⦆ .run (⦅t⦆ ∷ ε)          = sn-Kt (sem-sn ⦅t⦆)
⦅K⦆ .run (⦅t⦆ ∷ ⦅u⦆ ∷ ⦅E⦆)  = sn-KtuE' (⦅t⦆ .run ⦅E⦆) (sn-app (sem-sn ⦅u⦆))
-- ⦅K⦆ .run (⦅t⦆ ∷ ⦅u⦆ ∷ ⦅E⦆)  = sn-KtuE (⦅t⦆ .run ⦅E⦆) (sem-sn ⦅t⦆) (sn-app (sem-sn ⦅u⦆)) (sem-snₛ ⦅E⦆)

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

⦅case⦆ : (⦅t⦆ : t ⊥ ⟦ a ⟧) (⦅u⦆ : u ⊥ ⟦ a ⟧) (⦅E⦆ : E ∈ ⟦ a ⟧) → case t u ∷ E ∈ ⟦bool⟧
⦅case⦆ ⦅t⦆ ⦅u⦆ ⦅E⦆ .br h = case-sn (⦅t⦆ .run ⦅E⦆) (⦅u⦆ .run ⦅E⦆)


-- Term interpretation (soundness)

-- infix 100 ⦅_⦆ ⦅_⦆ₑ

mutual
  ⦅_⦆ : (t : Tm a) → t ⊥ ⟦ a ⟧
  ⦅ h ∙ E ⦆ .run ⦅E′⦆ = ⦅ h ⦆ₕ .run (⦅ E ⦆ₛ ⦅E′⦆)

  ⦅_⦆ₛ : (E : Stack n a c) (⦅E'⦆ : E' ∈ ⟦ c ⟧) → (E ++ E') ∈ ⟦ a ⟧
  ⦅ ε {c = a}    ⦆ₛ ⦅E'⦆ = ⦅E'⦆
  ⦅ app u ∷ E    ⦆ₛ ⦅E'⦆ = ⦅ u ⦆ ∷ ⦅ E ⦆ₛ ⦅E'⦆
  ⦅ case u v ∷ E ⦆ₛ ⦅E'⦆ = ⦅case⦆ ⦅ u ⦆ ⦅ v ⦆ (⦅ E ⦆ₛ ⦅E'⦆)

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
