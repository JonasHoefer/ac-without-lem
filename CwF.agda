{-# OPTIONS --rewriting #-}

-- Related work:
-- - van den Berg shows for higher order logic that AC does not imply EM without prop ext
--   https://web.archive.org/web/20080418230344/http://www.mathematik.tu-darmstadt.de/~berg/papers/diaco.pdf
--   I think this construction is different since he mentions that choice holds since ∃ is interpreted as Σ
-- - https://www.math.nagoya-u.ac.jp/~garrigue/papers/modelccomega-mscs2023.pdf
--   Sato and Garrigue build a model of CC^ω (i.e. CIC without inductive types and without Prop ⊆ Type)
--   They mention that in their construction the interpretation of Prop and Type is too different to incorporate this rule.
--   (They interpret Type in context Γ as Γ → U for a meta-universe U while interpreting Prop in context Γ as Γ → 𝓞(X) for an Alexandroff space X)
-- - the skeleton of this formalization is based on https://github.com/AndrasKovacs/antifunext/blob/main/Model.agda by András Kovács
--
-- The model formalized here is essentially the Quasitopos ℰ of separated presheaves on {0 < 1} for the topology where 0 covers 1 (i.e. two sets and a mono between them).
-- Types are interpreted slightly unexpectedly: The global sections comonad □ = Δ∘Γ lands in separated presheaves.
-- Hence, for the subuniverse of the Hofmann-Streicher universe on separated presheaves U, the presheaf □U is separated.
-- Pulling back the universal family yields a universe in ℰ. Concretely, it is given by the constant presheaf on the set of separated presheaves on {0 < 1}.
-- The presheaf of types is the one represented by U.
--
-- We produce a model of extensional type theory.
-- In particular, we validate equality reflection, meaning that strict propositions and homotopy propositions collapse in this model.
-- We can therefore simply define propositions as homotopy propositions.
-- This model is impredicative in the sense that it satisfies propositional resizing: every proposition is logically equivalent to one in the lowest universe.
-- We do not address strict cumulatively of universes (although we should inherit it from the meta-theory).
--
-- Note that this model does not satisfy propositional extensionality.
-- In the context with the type (1, λₓ.0) the propositions (1, λₓ.0) and (1, λₓ.1) imply each other but are not equal.

module CwF where

open import Agda.Primitive hiding (Prop)
open import Agda.Builtin.Equality.Rewrite

open import Data.Unit
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty
open import Data.Product
open import Data.Sum renaming (map to map-⊎)

open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Relation.Nullary.Negation

private variable ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

elim-ℕ : (P : ℕ → Set ℓ) → P zero → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
elim-ℕ P z s zero = z
elim-ℕ P z s (suc n) = s n (elim-ℕ P z s n)

record Lift {i} j (A : Set i) : Set (i ⊔ j) where
  constructor ↑
  field ↓ : A
open Lift

is-prop : Set ℓ → Set ℓ
is-prop A = (x y : A) → x ≡ y

is-prop-⊤ : is-prop ⊤
is-prop-⊤ _ _ = refl

record Prop (ℓ : Level) : Set (lsuc ℓ) where
  no-eta-equality
  pattern
  constructor  _,_
  field
    P : Set ℓ
    prop : is-prop P

Prop₀ : Set₁
Prop₀ = Prop lzero

⟨_⟩ : Prop ℓ → Set ℓ
⟨ A , _ ⟩ = A

_↔_ : Prop ℓ → Prop ℓ' → Set (ℓ ⊔ ℓ')
P ↔ Q = (⟨ P ⟩ → ⟨ Q ⟩) × (⟨ Q ⟩ → ⟨ P ⟩)

prop : (P : Prop ℓ) → is-prop ⟨ P ⟩
prop (_ , p) = p

Liftᵖ : (ℓ' : Level) → Prop ℓ → Prop (ℓ ⊔ ℓ')
Liftᵖ ℓ' P = Lift ℓ' ⟨ P ⟩ , λ (↑ x) (↑ y) → cong ↑ (prop P x y)

pair⁼ : {A : Set ℓ} {B : A → Set ℓ'} {a₀ a₁ : A} (α : a₀ ≡ a₁) {b₀ : B a₀} {b₁ : B a₁} → subst B α b₀ ≡ b₁ → _≡_ {A = Σ A B} (a₀ , b₀) (a₁ , b₁)
pair⁼ refl refl = refl

Σᵖ : (A : Prop ℓ) (B : ⟨ A ⟩ → Prop ℓ') → Prop (ℓ ⊔ ℓ')
Σᵖ A B = (Σ[ a ∈ ⟨ A ⟩ ] ⟨ B a ⟩) , λ (a₀ , b₀) (a₁ , b₁) → pair⁼ (prop A a₀ a₁) (prop (B a₁) (subst (λ a → ⟨ B a ⟩) (prop A a₀ a₁) b₀) b₁)

_×ᵖ_ : (A : Prop ℓ) (B : Prop ℓ') → Prop (ℓ ⊔ ℓ')
A ×ᵖ B = Σᵖ A (λ _ → B)

⊤ᵖ : Prop ℓ
⊤ᵖ = Lift _ ⊤ , λ _ _ → refl

⊥ᵖ : Prop ℓ
⊥ᵖ = Lift _ ⊥ , λ ()

postulate FE : {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g

Πᵖ : (A : Set ℓ) (B : A → Prop ℓ') → Prop (ℓ ⊔ ℓ')
Πᵖ A B = ((a : A) → ⟨ B a ⟩) , λ f g → FE λ x → prop (B x) (f x) (g x)

syntax Πᵖ A (λ x → B) = Πᵖ[ x ∈ A ] B

postulate
  ∥_∥ : Set ℓ → Set ℓ
  η : {A : Set ℓ} → A → ∥ A ∥
  is-prop-∥∥ : {A : Set ℓ} → is-prop ∥ A ∥
  elim-∥∥ : {A : Set ℓ} {P : ∥ A ∥ → Set ℓ'} → ((u : ∥ A ∥) → is-prop (P u)) → ((a : A) → P (η a)) → (u : ∥ A ∥) → P u
  elim-∥∥-β : {A : Set ℓ} {P : ∥ A ∥ → Set ℓ'} {p : (u : ∥ A ∥) → is-prop (P u)} {f : (a : A) → P (η a)} {a : A} → elim-∥∥ p f (η a) ≡ f a

∥_∥ᵖ : Set ℓ → Prop ℓ
∥ A ∥ᵖ = ∥ A ∥ , is-prop-∥∥

rec-∥∥ : {A : Set ℓ} (P : Set ℓ') → is-prop P → (A → P) → ∥ A ∥ → P
rec-∥∥ P p f u = elim-∥∥ (λ u₁ → p) f u

{-# REWRITE elim-∥∥-β #-}

-- choice as Hilbert style ε-operator
postulate ac : {A : Set ℓ} → ∥ A ∥ → A

postulate em : (P : Set ℓ) → is-prop P → P ⊎ ¬ P

uip : {A : Set ℓ} {a₀ a₁ : A} (p₀ p₁ : a₀ ≡ a₁) → p₀ ≡ p₁
uip refl refl = refl

substd : {A : Set ℓ} {P : A → Set ℓ'} (Q : (a : A) → P a → Set ℓ'') {a₀ a₁ : A} (α : a₀ ≡ a₁) (p₀ : P a₀) (q₀ : Q a₀ p₀) → Q a₁ (subst P α p₀)
substd Q refl p₀ q₀ = q₀

congd : {A : Set ℓ} {P : A → Set ℓ'} {Q : Set ℓ''} (f : (a : A) (p : P a) → Q) {a₀ a₁ : A} (α : a₀ ≡ a₁) {p₀ : P a₀} {p₁ : P a₁} → subst P α p₀ ≡ p₁ → f a₀ p₀ ≡ f a₁ p₁
congd f refl refl = refl

resize : (P : Prop ℓ) → Σ[ Q ∈ Prop₀ ] (P ↔ Q)
resize (P , P-prop) with em P P-prop
... | inj₁ p = ⊤ᵖ , (λ _ → ↑ tt) , (λ _ → p)
... | inj₂ ¬p = ⊥ᵖ , (λ z → ↑ (¬p z)) , λ ()


--------------------------------------------------------------------------------
---- Basic CwF structure

module CwF where
  record Cxt (ℓ : Level) : Set (lsuc ℓ) where
    constructor _◁_
    field
      S : Set ℓ
      P : S → Prop ℓ
  open Cxt public

  variable
    Γ : Cxt ℓ
    Δ : Cxt ℓ'
    Θ : Cxt ℓ''
    Ρ : Cxt ℓ'''

  ∙ : Cxt lzero
  ∙ .S = ⊤
  ∙ .P _ = ⊤ , is-prop-⊤

  record Sub (Γ : Cxt ℓ) (Δ : Cxt ℓ') : Set (ℓ ⊔ ℓ') where
    constructor _◁_
    field
      S : Γ .S → Δ .S
      P : (γ : Γ .Cxt.S) → ⟨ Γ .P γ ⟩ → ⟨ Δ .P (S γ) ⟩
  open Sub public

  variable
    σ : Sub Δ Γ
    τ : Sub Θ Δ

  id : Sub Γ Γ
  id .S γ = γ
  id .P γ γᵖ = γᵖ

  infixr 5 _∘_
  _∘_ : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  (σ ◁ σᵖ) ∘ (τ ◁ τᵖ) = (λ z → σ (τ z)) ◁ (λ γ z → σᵖ (τ γ) (τᵖ γ z))

  ε : Sub Γ ∙
  ε .S _ = tt
  ε .P _ _ = tt

  εη : {σ : Sub Γ ∙} → σ ≡ ε
  εη = refl

  unit-l : {σ : Sub Δ Γ} → id ∘ σ ≡ σ
  unit-l = refl

  unit-r : {σ : Sub Δ Γ} → σ ∘ id ≡ σ
  unit-r = refl

  assoc :  {σ : Sub Δ Γ} {τ : Sub Θ Δ} {δ : Sub Ρ Θ} → (σ ∘ τ) ∘ δ ≡ σ ∘ (τ ∘ δ)
  assoc = refl

  record Ty (Γ : Cxt ℓ) (ℓ' : Level) : Set (ℓ ⊔ lsuc ℓ') where
    constructor _◁_
    field
      S : Γ .S → Set ℓ'
      P : (γ : Γ .Cxt.S) → S γ → Prop ℓ'

  variable A : Ty Γ ℓ

  infixl 3 _▶_
  _▶_ : (Γ : Cxt ℓ) (A : Ty Γ ℓ') → Cxt (ℓ ⊔ ℓ')
  ((Γ ◁ Γᴾ) ▶ (A ◁ Aᵖ)) .S = Σ Γ A
  ((Γ ◁ Γᴾ) ▶ (A ◁ Aᵖ)) .P (γ , a) = Γᴾ γ ×ᵖ Aᵖ γ a

  record Tm (Γ : Cxt ℓ) (A : Ty Γ ℓ') : Set (ℓ ⊔ lsuc ℓ') where
    constructor _◁_
    field
      S : (γ : Γ .S) → A .Ty.S γ
      P : (γ : Γ .Cxt.S) (γᵖ : ⟨ Γ .P γ ⟩) → ⟨ A .Ty.P γ (S γ) ⟩

  TmExt : {Γ : Cxt ℓ} {A : Ty Γ ℓ'} (s t : Tm Γ A) → ((γ : Γ .S) → s .Tm.S γ ≡ t . Tm.S γ) → s ≡ t
  TmExt {A = A} s t p = congd _◁_ (FE p) (FE λ γ → FE λ γᵖ → prop (A .Ty.P γ (t .Tm.S γ)) _ (t .Tm.P γ γᵖ))

  infix 5 _[_]T
  _[_]T : Ty Γ ℓ → Sub {ℓ'}{ℓ''} Δ Γ → Ty Δ ℓ
  (A ◁ Aᵖ) [ σ ◁ σᵖ ]T = (λ γ → A (σ γ)) ◁ (λ γ a → Aᵖ (σ γ) a)

  [id]T : A [ id ]T ≡ A
  [id]T = refl

  [∘]T : A [ σ ]T [ τ ]T ≡ (A [ σ ]T) [ τ ]T
  [∘]T = refl

  infix 5 _[_]
  _[_] : Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ]T)
  (a ◁ aᵖ) [ σ ◁ σᵖ  ] = (λ γ → a (σ γ)) ◁ (λ γ γᵖ → aᵖ (σ γ) (σᵖ γ γᵖ))

  [id] : {Γ : Cxt ℓ} {A : Ty Γ ℓ''} {a : Tm Γ A} → a [ id ] ≡ a
  [id] = refl

  [∘] : {a : Tm Γ A} → a [ σ ] [ τ ] ≡ (a [ σ ]) [ τ ]
  [∘] = refl

  p : (A : Ty {ℓ} Γ ℓ') → Sub (Γ ▶ A) Γ
  p (A ◁ Aᵖ) = (λ (γ , a) → γ) ◁ (λ (γ , a) (γᵖ , aᵖ) → γᵖ)

  q : {Γ : Cxt ℓ} (A : Ty Γ ℓ') → Tm (Γ ▶ A) (A [ p A ]T)
  q (A ◁ Aᵖ) = (λ (γ , a) → a) ◁ (λ (γ , a) (γᵖ , aᵖ) → aᵖ)

  qp : {Γ : Cxt ℓ} (A : Ty Γ ℓ') (B : Ty (Γ ▶ A) ℓ'') → Tm (Γ ▶ A ▶ B) (A [ p A ∘ p B ]T)
  qp A B = q A [ p B ]

  pairˢ : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} (σ : Sub Γ Δ) (A : Ty Δ ℓ'') → Tm {ℓ} {ℓ''} Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
  pairˢ (σ ◁ σᵖ) A (a ◁ aᵖ) .S γ = σ γ , a γ
  pairˢ (σ ◁ σᵖ) A (a ◁ aᵖ) .P γ γᵖ = σᵖ γ γᵖ , aᵖ γ γᵖ

  _,ₛ_ : (σ : Sub Γ Δ) → Tm {ℓ}{ℓ'} Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
  _,ₛ_ {A = A} σ a = pairˢ σ A a

  pβ : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {A : Ty Γ ℓ''} {σ : Sub Δ Γ} {a : Tm Δ (A [ σ ]T)} → p A ∘ pairˢ σ A a ≡ σ
  pβ = refl

  qβ : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {A : Ty Γ ℓ''} {σ : Sub Δ Γ} {a : Tm Δ (A [ σ ]T)} → q A [ pairˢ σ A a ] ≡ a
  qβ = refl

  liftˢ : (σ : Sub Δ Γ) (A : Ty Γ ℓ'') → Sub (Δ ▶ A [ σ ]T) (Γ ▶ A)
  liftˢ σ A = pairˢ (σ ∘ p (A [ σ ]T)) A (q (A [ σ ]T))

  ,ₛη : (p A ,ₛ q A) ≡ id
  ,ₛη = refl

  ,ₛ∘ : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {Θ : Cxt ℓ''} {A : Ty Γ ℓ'''} {σ : Sub Δ Γ} {τ : Sub Θ Δ} {a : Tm Δ (A [ σ ]T)} → (pairˢ σ A a ∘ τ) ≡ (pairˢ (σ ∘ τ) A (a [ τ ]))
  ,ₛ∘ = refl
open CwF

--------------------------------------------------------------------------------
---- Universes

module Universe where
  U : (ℓ : Level) → Ty Γ (lsuc ℓ)
  U ℓ .Ty.S γ = Σ[ A ∈ Set ℓ ] (A → Prop ℓ)
  U ℓ .Ty.P γ (A , Aᵖ) = ⊤ᵖ

  U[] : {σ : Sub Δ Γ} {ℓ : Level} → U ℓ [ σ ]T ≡ U ℓ
  U[] = refl

  El : Tm Γ (U ℓ) → Ty Γ ℓ
  El (A ◁ _) .Ty.S γ = A γ .proj₁
  El (A ◁ _) .Ty.P γ a = A γ .proj₂ a

  El[] : {σ : Sub Δ Γ} {ℓ : Level} {A : Tm Γ (U ℓ)} → El A [ σ ]T ≡ El (A [ σ ])
  El[] = refl

  code : Ty Γ ℓ → Tm Γ (U ℓ)
  code (A ◁ Aᵖ) .Tm.S γ = A γ , Aᵖ γ
  code (A ◁ Aᵖ) .Tm.P γ γᵖ = ↑ tt

  code[] : {σ : Sub Δ Γ} {A : Ty Γ ℓ''} → code A [ σ ] ≡ code (A [ σ ]T)
  code[] = refl

  Elcode : {A : Ty Γ ℓ} → El (code A) ≡ A
  Elcode = refl

  codeEl : {A : Tm Γ (U ℓ)} → code (El A) ≡ A
  codeEl = refl
open Universe using (U; El; code)

--------------------------------------------------------------------------------
---- Π

module Pi where
  Pi : (A : Ty Γ ℓ') → Ty (Γ ▶ A) ℓ'' → Ty Γ (ℓ' ⊔ ℓ'')
  Pi (A ◁ Aᵖ) (B ◁ Bᵖ) .Ty.S γ = (a : A γ) → B (γ , a)
  Pi (A ◁ Aᵖ) (B ◁ Bᵖ) .Ty.P γ f = Πᵖ[ a ∈ A γ ] Πᵖ[ _ ∈ ⟨ Aᵖ γ a ⟩ ] Bᵖ (γ , a) (f a)

  Pi[] : {σ : Sub Δ Γ} {A : Ty Γ ℓ'} {B : Ty (Γ ▶ A) ℓ''} → Pi A B [ σ ]T ≡ Pi (A [ σ ]T) (B [ liftˢ σ A ]T)
  Pi[] = refl

  Fun : (A : Ty Γ ℓ') → Ty Γ ℓ'' → Ty Γ (ℓ' ⊔ ℓ'')
  Fun A B = Pi A (B [ p A ]T)

  module _ (A : Ty Γ ℓ') (B : Ty (Γ ▶ A) ℓ'') where
    Lam : Tm (Γ ▶ A) B → Tm Γ (Pi A B)
    Lam (b ◁ bᵖ) .Tm.S γ a = b (γ , a)
    Lam (b ◁ bᵖ) .Tm.P γ γᵖ a aᵖ = bᵖ (γ , a) (γᵖ , aᵖ)

    App : Tm Γ (Pi A B) → Tm (Γ ▶ A) B
    App (f ◁ fᵖ) .Tm.S (γ , a) = f γ a
    App (f ◁ fᵖ) .Tm.P (γ , a) (γᵖ , aᵖ) = fᵖ γ γᵖ a aᵖ

    Piβ : {b : Tm (Γ ▶ A) B} → (App (Lam b)) ≡ b
    Piβ = refl

    Piη : (f : Tm Γ (Pi A B)) → Lam (App f) ≡ f
    Piη b = refl

  module _ {Γ : Cxt ℓ} {Δ : Cxt ℓ''} {σ : Sub Δ Γ} (A : Ty Γ ℓ''') (B : Ty (Γ ▶ A) ℓ'''') where
    Lam[] : {t : Tm (Γ ▶ A) B} → Lam A B t [ σ ] ≡ Lam (A [ σ ]T) (B [ liftˢ σ A ]T) (t [ liftˢ σ A ])
    Lam[] = refl

    App[] : {t : Tm Γ (Pi A B)} → App A B t [ liftˢ σ A ] ≡ App (A [ σ ]T) (B [ liftˢ σ A ]T) (t [ σ ])
    App[] = refl
open Pi using (Pi; Fun; Lam; App)

--------------------------------------------------------------------------------
---- Σ

module Sigma where
  Sg : (A : Ty Γ ℓ') → Ty (Γ ▶ A) ℓ'' → Ty Γ (ℓ' ⊔ ℓ'')
  Sg (A ◁ Aᵖ) (B ◁ Bᵖ) .Ty.S γ = Σ[ a ∈ A γ ] B (γ , a)
  Sg (A ◁ Aᵖ) (B ◁ Bᵖ) .Ty.P γ (a , b) = Aᵖ γ a ×ᵖ Bᵖ (γ , a) b

  Sg[] : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ} {A : Ty Γ ℓ''} {B : Ty (Γ ▶ A) ℓ'''} → Sg A B [ σ ]T ≡ Sg (A [ σ ]T) (B [ liftˢ σ A ]T)
  Sg[] = refl

  Prod : (A : Ty Γ ℓ') (B : Ty Γ ℓ'') → Ty Γ (ℓ' ⊔ ℓ'')
  Prod A B = Sg A (B [ p A ]T)

  module _ (A : Ty Γ ℓ') (B : Ty (Γ ▶ A) ℓ'') where
    Pair : (a : Tm Γ A) → Tm Γ (B [ id ,ₛ a ]T) → Tm Γ (Sg A B)
    Pair a b .Tm.S γ = a .Tm.S γ , b .Tm.S γ
    Pair a b .Tm.P γ γᵖ = a .Tm.P γ γᵖ , b .Tm.P γ γᵖ

    Fst : Tm Γ (Sg A B) → Tm Γ A
    Fst (w ◁ wᵖ) .Tm.S γ = w γ .proj₁
    Fst (w ◁ wᵖ) .Tm.P γ γᵖ = wᵖ γ γᵖ .proj₁

    Snd : (w : Tm Γ (Sg A B)) → Tm Γ (B [ pairˢ id A (Fst w) ]T)
    Snd (w ◁ wᵖ) .Tm.S γ = w γ .proj₂
    Snd (w ◁ wᵖ) .Tm.P γ γᵖ = wᵖ γ γᵖ .proj₂

    Sgη : {w : Tm Γ (Sg A B)} → Pair (Fst w) (Snd w) ≡ w
    Sgη = refl

    Sgβ₁ : {a : Tm Γ A} {b : Tm Γ (B [ id ,ₛ a ]T)} → Fst (Pair a b) ≡ a
    Sgβ₁ = refl

    Sgβ₂ : {a : Tm Γ A} {b : Tm Γ (B [ id ,ₛ a ]T)} → Snd (Pair a b) ≡ b
    Sgβ₂ = refl

  module _ {Γ : Cxt ℓ} {Δ : Cxt ℓ''} {σ : Sub Δ Γ} (A : Ty Γ ℓ''') (B : Ty (Γ ▶ A) ℓ'''') where
    Pair[] : {a : Tm Γ A} {b : Tm Γ (B [ id ,ₛ a ]T)} → Pair A B a b [ σ ] ≡ Pair (A [ σ ]T) (B [ liftˢ σ A ]T) (a [ σ ]) (b [ σ ])
    Pair[] = refl

    Fst[] : {w : Tm Γ (Sg A B)} → Fst A B w [ σ ] ≡ Fst (A [ σ ]T) (B [ liftˢ σ A ]T) (w [ σ ])
    Fst[] = refl

    Snd[] : {w : Tm Γ (Sg A B)} → Snd A B w [ σ ] ≡ Snd (A [ σ ]T) (B [ liftˢ σ A ]T) (w [ σ ])
    Snd[] = refl
open Sigma using (Sg; Pair; Fst; Snd; Prod)


--------------------------------------------------------------------------------
---- Identity

module Identity where
  Id : (A : Ty Γ ℓ') (s t : Tm Γ A) → Ty Γ ℓ'
  Id A (s ◁ _) (t ◁ _) .Ty.S γ = (s γ ≡ t γ)
  Id A (s ◁ _) (t ◁ _) .Ty.P γ _ = ⊤ᵖ

  Id[] : {σ : Sub Δ Γ} {A : Ty Γ ℓ'} {u v : Tm Γ A} → Id A u v [ σ ]T ≡ Id (A [ σ ]T) (u [ σ ]) (v [ σ ])
  Id[] = refl

  Refl : (t : Tm Γ A) → Tm Γ (Id A t t)
  Refl t .Tm.S γ    = refl
  Refl t .Tm.P γ γᵖ = ↑ tt

  Refl[] : {σ : Sub Δ Γ} {A : Ty Γ ℓ''} {t : Tm Γ A} → Refl t [ σ ] ≡ Refl (t [ σ ])
  Refl[] = refl

  Tr : {Γ : Cxt ℓ} (A : Ty Γ ℓ') (P : Ty (Γ ▶ A) ℓ'') (t₀ t₁ : Tm Γ A) (t : Tm Γ (Id A t₀ t₁)) → Tm Γ (P [ id ,ₛ t₀ ]T) → Tm Γ (P [ id ,ₛ t₁ ]T)
  Tr (A ◁ Aᵖ) (P ◁ Pᵖ) (t₀ ◁ t₀ᵖ) (t₁ ◁ t₁ᵖ) (t ◁ tᵖ) (u ◁ uᵖ) .Tm.S γ = subst (λ tᵢ → P (γ , tᵢ)) (t γ) (u γ)
  Tr (A ◁ Aᵖ) (P ◁ Pᵖ) (t₀ ◁ t₀ᵖ) (t₁ ◁ t₁ᵖ) (t ◁ tᵖ) (u ◁ uᵖ) .Tm.P γ γᵖ = substd (λ a p → ⟨ Pᵖ (γ , a) p ⟩) (t γ) (u γ) (uᵖ γ γᵖ)

  Tr[] : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ} {A : Ty Γ ℓ''} {P : Ty (Γ ▶ A) ℓ'''} {t₀ t₁ : Tm Γ A} {t : Tm Γ (Id A t₀ t₁)} {u : Tm Γ (P [ id ,ₛ t₀ ]T)}
    → Tr A P t₀ t₁ t u [ σ ] ≡ Tr (A [ σ ]T) (P [ liftˢ σ A ]T) (t₀ [ σ ]) (t₁ [ σ ]) (t [ σ ]) (u [ σ ])
  Tr[] = refl

  Trβ : {Γ : Cxt ℓ} {A : Ty Γ ℓ'} {P : Ty (Γ ▶ A) ℓ''} {t : Tm Γ A} {u : Tm Γ (P [ id ,ₛ t ]T)} → Tr A P t t (Refl t) u ≡ u
  Trβ = refl

  -- We have that singleton types are contractible, which yields J in combination with Tr
  Singl : (A : Ty Γ ℓ') (a : Tm Γ A) → Ty Γ ℓ'
  Singl A a = Sg A (Id (A [ p A ]T) (a [ p A ]) (q A))

  MkSingl : (A : Ty Γ ℓ') (a₀ a₁ : Tm Γ A) (a : Tm Γ (Id A a₀ a₁)) → Tm Γ (Singl A a₀)
  MkSingl A a₀ a₁ a = Pair A _ a₁ a

  Centre : (A : Ty Γ ℓ') (a : Tm Γ A) → Tm Γ (Singl A a)
  Centre A a = MkSingl A a a (Refl a)

  ContrSingl : (A : Ty Γ ℓ') (a₀ a₁ : Tm Γ A) (a : Tm Γ (Id A a₀ a₁)) → Tm Γ (Id (Singl A a₀) (Centre A a₀) (MkSingl A a₀ a₁ a))
  ContrSingl A a₀ a₁ a .Tm.S γ = pair⁼ (a .Tm.S γ) (uip _ (a .Tm.S γ))
  ContrSingl A a₀ a₁ a .Tm.P γ γᵖ = ↑ tt

  ContrSingl[] : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ} {A : Ty Γ ℓ''} {a₀ a₁ : Tm Γ A} {a : Tm Γ (Id A a₀ a₁)} →
    ContrSingl A a₀ a₁ a [ σ ] ≡ ContrSingl (A [ σ ]T) (a₀ [ σ ]) (a₁ [ σ ]) (a [ σ ])
  ContrSingl[] = refl

  -- The identity type inherits UIP from the meta theory
  UIP : (A : Ty Γ ℓ') (a₀ a₁ : Tm Γ A) (p₀ p₁ : Tm Γ (Id A a₀ a₁)) → Tm Γ (Id (Id A a₀ a₁) p₀ p₁)
  UIP A a₀ a₁ p₀ p₁ .Tm.S γ = uip (p₀ .Tm.S γ) (p₁ .Tm.S γ)
  UIP A a₀ a₁ p₀ p₁ .Tm.P γ γᵖ = ↑ tt

  UIP[] : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ} {A : Ty Γ ℓ''} {a₀ a₁ : Tm Γ A} {p₀ p₁ : Tm Γ (Id A a₀ a₁)} →
    UIP A a₀ a₁ p₀ p₁ [ σ ] ≡ UIP (A [ σ ]T) (a₀ [ σ ]) (a₁ [ σ ]) (p₀ [ σ ]) (p₁ [ σ ])
  UIP[] = refl

  -- We even get equality reflection since we requiered the morphism A₀ → A₁ in a type to be fibred in propositions.
  Idη : (A : Ty Γ ℓ') (s t : Tm Γ A) → Tm Γ (Id A s t) → s ≡ t
  Idη A s t (p ◁ pᵖ) = TmExt s t p
open Identity using (Id; Refl)


--------------------------------------------------------------------------------
---- Trunc

module Trunc where
  Trunc : (A : Ty Γ ℓ') → Ty Γ ℓ'
  Trunc (A ◁ Aᵖ) .Ty.S γ = ∥ A γ ∥
  Trunc (A ◁ Aᵖ) .Ty.P γ _ = ∥ Σ[ a ∈ A γ ] ⟨ Aᵖ γ a ⟩ ∥ᵖ
  -- In the fibred point of view we just send A₀ ↣ A₁ to ∥A₀∥ ↣ ∥A₁∥
  -- In the indexed point of view we have to give the fibre of this map over a point.
  -- But given a point the type ∥A₁∥ is contractible so we can can give the total space.

  Trunc[] : Trunc A [ σ ]T ≡ Trunc (A [ σ ]T)
  Trunc[] = refl

  TruncIsProp : (A : Ty Γ ℓ') (u v : Tm Γ (Trunc A)) → Tm Γ (Id (Trunc A) u v)
  TruncIsProp A u v .Tm.S γ = is-prop-∥∥ (u .Tm.S γ) (v .Tm.S γ)
  TruncIsProp A u v .Tm.P γ γᵖ = ↑ tt

  TruncIsProp[] : {u v : Tm Γ (Trunc A)} → TruncIsProp A u v [ σ ] ≡ TruncIsProp (A [ σ ]T) (u [ σ ]) (v [ σ ])
  TruncIsProp[] = refl

  Inc : {A : Ty Γ ℓ'} → Tm Γ A → Tm Γ (Trunc A)
  Inc u .Tm.S γ = η (u .Tm.S γ)
  Inc u .Tm.P γ γᵖ = η (u .Tm.S γ , u .Tm.P γ γᵖ)

  Inc[] : {t : Tm Γ A} → Inc t [ σ ] ≡ Inc (t [ σ ])
  Inc[] = refl

  RecTrunc : {A : Ty Γ ℓ'} {Q : Ty Γ ℓ''} →
    Tm (Γ ▶ Q ▶ Q [ p Q ]T) (Id (Q [ p Q ∘ p (Q [ p Q ]T) ]T) (qp Q (Q [ p Q ]T)) (q (Q [ p Q ]T))) →
    Tm (Γ ▶ A) (Q [ p A ]T) →
    Tm (Γ ▶ Trunc A) (Q [ p (Trunc A) ]T)
  RecTrunc {Q = Q ◁ Qᵖ} is-prop-Q f .Tm.S (γ , a) = rec-∥∥ (Q γ) (λ x y → is-prop-Q .Tm.S ((γ , x) , y)) (λ a → f .Tm.S (γ , a)) a
  RecTrunc {Γ = Γ} {A = A ◁ Aᵖ} {Q = Q ◁ Qᵖ} is-prop-Q f .Tm.P (γ , a) (γᵖ , aᵖ) = rec-∥∥ ⟨ Qᵖ γ v ⟩ (prop (Qᵖ γ v)) lem aᵖ
    where
      v : Q γ
      v = RecTrunc {Γ = Γ} {A = A ◁ Aᵖ} {Q = Q ◁ Qᵖ} is-prop-Q f .Tm.S (γ , a)

      u : (a : A γ) → f .Tm.S (γ , a) ≡ v
      u a = is-prop-Q .Tm.S ((γ , f .Tm.S (γ , a)) , _)

      lem : (Σ[ a ∈ A γ ] ⟨ Aᵖ γ a ⟩) → ⟨ Qᵖ γ v ⟩
      lem (a , aᵖ) = subst (λ v → ⟨ Qᵖ γ v ⟩) (u a) (f .Tm.P (γ , a) (γᵖ , aᵖ))

  RecTrunc[] : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ} {A : Ty Γ ℓ''} {Q : Ty Γ ℓ'''}
    {is-prop-Q : Tm (Γ ▶ Q ▶ Q [ p Q ]T) (Id (Q [ p Q ∘ p (Q [ p Q ]T) ]T) (qp Q (Q [ p Q ]T)) (q (Q [ p Q ]T)))} {f : Tm (Γ ▶ A) (Q [ p A ]T)} →
      RecTrunc {Γ = Γ} {A = A} is-prop-Q f [ liftˢ σ (Trunc A) ] ≡ RecTrunc {Γ = Δ} {A = A [ σ ]T} (is-prop-Q [ liftˢ (liftˢ σ Q) (Q [ p Q ]T) ]) (f [ liftˢ σ A ])
  RecTrunc[] = refl
open Trunc using (Trunc; TruncIsProp; Inc; RecTrunc)


--------------------------------------------------------------------------------
---- Unit

module Unit where
  𝟙 : Ty Γ lzero
  𝟙 .Ty.S γ = ⊤
  𝟙 .Ty.P γ _ = ⊤ᵖ

  𝟙[] : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ} → 𝟙 [ σ ]T ≡ 𝟙
  𝟙[] = refl

  Pt : Tm Γ 𝟙
  Pt .Tm.S γ = tt
  Pt .Tm.P γ γᵖ = ↑ tt

  Pt[] : Pt [ σ ] ≡ Pt
  Pt[] = refl

  𝟙η : (t : Tm Γ 𝟙) → t ≡ Pt
  𝟙η t = refl
open Unit using (𝟙)


--------------------------------------------------------------------------------
---- Empty

module Empty where
  𝟘 : Ty Γ lzero
  𝟘 .Ty.S γ = ⊥
  𝟘 .Ty.P γ = ⊥-elim

  𝟘[] : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ} → 𝟘 [ σ ]T ≡ 𝟘
  𝟘[] = refl

  Elim𝟘 : (Q : Ty (Γ ▶ 𝟘) ℓ) → Tm (Γ ▶ 𝟘) Q
  Elim𝟘 Q .Tm.S (γ , u) = ⊥-elim u
  Elim𝟘 Q .Tm.P γ γᵖ = ⊥-elim (γ .proj₂)

  Elim𝟘[] : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ} {Q : Ty (Γ ▶ 𝟘) ℓ} → Elim𝟘 {Γ = Γ} Q [ liftˢ σ 𝟘 ] ≡ Elim𝟘 {Γ = Δ} (Q [ liftˢ σ 𝟘 ]T)
  Elim𝟘[] = refl
open Empty using (𝟘; Elim𝟘)


--------------------------------------------------------------------------------
---- Sum

module Sum where
  Sum : {Γ : Cxt ℓ} (A : Ty Γ ℓ') (B : Ty Γ ℓ'') → Ty Γ (ℓ' ⊔ ℓ'')
  Sum (A ◁ Aᵖ) (B ◁ Bᵖ) .Ty.S γ = A γ ⊎ B γ
  Sum {ℓ' = ℓ'} {ℓ'' = ℓ''} (A ◁ Aᵖ) (B ◁ Bᵖ) .Ty.P γ = [ (λ a → Liftᵖ ℓ'' (Aᵖ γ a)) , (λ b → Liftᵖ ℓ' (Bᵖ γ b)) ]

  Sum[] : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ} {A : Ty Γ ℓ''} {B : Ty Γ ℓ'''} →
    Sum A B [ σ ]T ≡ Sum (A [ σ ]T) (B [ σ ]T)
  Sum[] = refl

  module _ {Γ : Cxt ℓ} (A : Ty Γ ℓ'') (B : Ty Γ ℓ''') where
    Inj1 : Tm Γ A → Tm Γ (Sum A B)
    Inj1 (u ◁ uᵖ) .Tm.S γ = inj₁ (u γ)
    Inj1 (u ◁ uᵖ) .Tm.P γ γᵖ = ↑ (uᵖ γ γᵖ)

    Inj2 : Tm Γ B → Tm Γ (Sum A B)
    Inj2 (u ◁ uᵖ) .Tm.S γ = inj₂ (u γ)
    Inj2 (u ◁ uᵖ) .Tm.P γ γᵖ = ↑ (uᵖ γ γᵖ)

  module _ {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ} (A : Ty Γ ℓ'') (B : Ty Γ ℓ''') where
    Inj1[] : {a : Tm Γ A} → Inj1 A B a [ σ ] ≡ Inj1 (A [ σ ]T) (B [ σ ]T) (a [ σ ])
    Inj1[] = refl

    Inj2[] : {b : Tm Γ B} → Inj2 A B b [ σ ] ≡ Inj2 (A [ σ ]T) (B [ σ ]T) (b [ σ ])
    Inj2[] = refl

  module _ {Γ : Cxt ℓ} (A : Ty Γ ℓ'') (B : Ty Γ ℓ''') where
    Inj1ˢ : Sub (Γ ▶ A) (Γ ▶ Sum A B)
    Inj1ˢ = pairˢ (p A) (Sum A B) (Inj1 (A [ p A ]T) (B [ p A ]T) (q A))

    Inj2ˢ : Sub (Γ ▶ B) (Γ ▶ Sum A B)
    Inj2ˢ = pairˢ (p B) (Sum A B) (Inj2 (A [ p B ]T) (B [ p B ]T) (q B))

    ElimSum : (Q : Ty (Γ ▶ Sum A B) ℓ'''') → Tm (Γ ▶ A) (Q [ Inj1ˢ ]T) → Tm (Γ ▶ B) (Q [ Inj2ˢ ]T) → (w : Tm Γ (Sum A B)) → Tm Γ (Q [ id ,ₛ w ]T)
    ElimSum (Q ◁ Qᵖ) s t w .Tm.S γ =
      [_,_] {C = λ w → Q (γ , w)} (λ a → s .Tm.S (γ , a)) (λ b → t .Tm.S (γ , b)) (w .Tm.S γ)
    ElimSum (Q ◁ Qᵖ) s t w .Tm.P γ γᵖ =
      [_,_]
        {C = λ u → (v : ⟨ Sum A B .Ty.P γ u ⟩) → ⟨ Qᵖ (γ , u) ([_,_] {C = λ w → Q (γ , w)} (λ a → s .Tm.S (γ , a)) (λ b → t .Tm.S (γ , b)) u) ⟩}
        (λ a aᵖ → s .Tm.P (γ , a) (γᵖ , aᵖ .↓))
        (λ b bᵖ → t .Tm.P (γ , b) (γᵖ , bᵖ .↓))
        (w .Tm.S γ)
        (w .Tm.P γ γᵖ)

    ElimSumβ₁ : {Q : Ty (Γ ▶ Sum A B) ℓ''''} {u : Tm (Γ ▶ A) (Q [ Inj1ˢ ]T)} {v : Tm (Γ ▶ B) (Q [ Inj2ˢ ]T)} {a : Tm Γ A} →
      ElimSum Q u v (Inj1 A B a) ≡ u [ id ,ₛ a ]
    ElimSumβ₁ = refl

    ElimSumβ₂ : {Q : Ty (Γ ▶ Sum A B) ℓ''''} {u : Tm (Γ ▶ A) (Q [ Inj1ˢ ]T)} {v : Tm (Γ ▶ B) (Q [ Inj2ˢ ]T)} {b : Tm Γ B} →
      ElimSum Q u v (Inj2 A B b) ≡ v [ id ,ₛ b ]
    ElimSumβ₂ = refl

  module _ {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ} {A : Ty Γ ℓ''} {B : Ty Γ ℓ'''} where
    ElimSum[] : {Q : Ty (Γ ▶ Sum A B) ℓ''''} {u : Tm (Γ ▶ A) (Q [ Inj1ˢ A B ]T)} {v : Tm (Γ ▶ B) (Q [ Inj2ˢ A B ]T)} {w : Tm Γ (Sum A B)} →
      ElimSum A B Q u v w [ σ ] ≡ ElimSum (A [ σ ]T) (B [ σ ]T) (Q [ liftˢ σ (Sum A B) ]T) (u [ liftˢ σ A ]) (v [ liftˢ σ B ]) (w [ σ ])
    ElimSum[] = refl
open Sum using (Sum; Inj1; Inj2; ElimSum)

--------------------------------------------------------------------------------
---- ℕ

module Nat where
  Nat : Ty Γ lzero
  Nat .Ty.S γ = ℕ
  Nat .Ty.P γ n = ⊤ᵖ

  Nat[] : Nat [ σ ]T ≡ Nat
  Nat[] = refl

  Zero : Tm Γ Nat
  Zero .Tm.S γ = zero
  Zero .Tm.P γ γᵖ = ↑ tt

  Zero[] : Zero [ σ ] ≡ Zero
  Zero[] = refl

  Suc : Tm Γ Nat → Tm Γ Nat
  Suc (n ◁ nᵖ) .Tm.S γ = suc (n γ)
  Suc (n ◁ nᵖ) .Tm.P γ γᵖ = ↑ tt

  Suc[] : {t : Tm Γ Nat} → Suc t [ σ ] ≡ Suc (t [ σ ])
  Suc[] = refl

  ElimNatSubst : (Γ : Cxt ℓ) (P : Ty (Γ ▶ Nat) ℓ') → Sub (Γ ▶ Nat ▶ P) (Γ ▶ Nat)
  ElimNatSubst Γ P = pairˢ pp Nat (Suc (qp {Γ = Γ} Nat P))
    where
      pp : Sub (Γ ▶ Nat ▶ P) Γ
      pp = p Nat ∘ p P

  ElimNat : (Q : Ty (Γ ▶ Nat) ℓ')
    (z : Tm Γ (Q [ pairˢ id Nat Zero ]T))
    (s : Tm (Γ ▶ Nat ▶ Q) (Q [ ElimNatSubst Γ Q ]T))
    (n : Tm Γ Nat) →
    Tm Γ (Q [ pairˢ id Nat n ]T)
  ElimNat (Q ◁ Qᵖ) z s n .Tm.S γ =
    elim-ℕ (λ m → Q (γ , m)) (z .Tm.S γ) (λ m u → s .Tm.S ((γ , m) , u)) (n .Tm.S γ)
  ElimNat (Q ◁ Qᵖ) z s n .Tm.P γ γᵖ =
    elim-ℕ
      (λ m → ⟨ Qᵖ (γ , m) (elim-ℕ (λ m → Q (γ , m)) (z .Tm.S γ) (λ m u → s .Tm.S ((γ , m) , u)) m) ⟩)
      (z .Tm.P γ γᵖ)
      (λ m u → s .Tm.P _ ((γᵖ , ↑ tt) , u))
      (n .Tm.S γ)

  ElimNat[] : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ}
    {Q : Ty (Γ ▶ Nat) ℓ''}
    {z : Tm Γ (Q [ pairˢ id Nat Zero ]T)}
    {s : Tm (Γ ▶ Nat ▶ Q) (Q [ ElimNatSubst Γ Q ]T)}
    {n : Tm Γ Nat} →
    ElimNat Q z s n [ σ ] ≡ ElimNat (Q [ liftˢ σ Nat ]T) (z [ σ ]) (s [ liftˢ (liftˢ σ Nat) Q ]) (n [ σ ])
  ElimNat[] = refl

  Natβ₁ : {Γ : Cxt ℓ} {Q : Ty (Γ ▶ Nat) ℓ''}
    {z : Tm Γ (Q [ pairˢ id Nat Zero ]T)}
    {s : Tm (Γ ▶ Nat ▶ Q) (Q [ ElimNatSubst Γ Q ]T)} →
    ElimNat Q z s Zero ≡ z
  Natβ₁ = refl

  Natβ₂ : {Γ : Cxt ℓ} {Q : Ty (Γ ▶ Nat) ℓ''}
    {z : Tm Γ (Q [ pairˢ id Nat Zero ]T)}
    {s : Tm (Γ ▶ Nat ▶ Q) (Q [ ElimNatSubst Γ Q ]T)}
    {n : Tm Γ Nat} →
    ElimNat Q z s (Suc n) ≡ s [ pairˢ (pairˢ id Nat n) Q (ElimNat Q z s n) ]
  Natβ₂ = refl
open Nat using (Nat; Zero; Suc; ElimNat)


--------------------------------------------------------------------------------
---- Choice

module Choice where
  -- We produce an element ε of type A : U, _ : ∥ El A ∥ ⊢ ε : El A
  AC-cxt : (ℓ : Level) → Cxt (lsuc ℓ)
  AC-cxt ℓ = ∙ ▶ U ℓ ▶ Trunc (El (q {Γ = ∙} (U ℓ)))

  AC-U : (ℓ : Level) → Tm (AC-cxt ℓ) (El (qp {Γ = ∙} (U ℓ) (Trunc (El (q {Γ = ∙} (U ℓ))))))
  AC-U ℓ = (λ ((tt , A) , u) → lem' A u .proj₁) ◁ (λ ((tt , A) , u) ((tt , ↑ tt) , w) → lem' A u .proj₂ w)
    where
      lem : ((A , Aᵖ) :
        Σ[ A ∈ Set ℓ ] (A → Prop ℓ)) → ∥ A ∥ → ∥ (Σ[ a' ∈ A ] ⟨ Aᵖ a' ⟩) ∥ ⊎ ¬ ∥ (Σ[ a' ∈ A ] ⟨ Aᵖ a' ⟩) ∥ → Σ[ a ∈ A ] (∥ (Σ[ a' ∈ A ] ⟨ Aᵖ a' ⟩) ∥ → ⟨ Aᵖ a ⟩)
      lem (A , Aᵖ) u (inj₁ v) = let (a , aᵖ) = ac v in a , λ _ → aᵖ
      lem (A , Aᵖ) u (inj₂ v) = ac u , λ x → ⊥-elim (v x)

      lem' : ((A , Aᵖ) : Σ[ A ∈ Set ℓ ] (A → Prop ℓ)) → ∥ A ∥ → Σ[ a ∈ A ] (∥ (Σ[ a' ∈ A ] ⟨ Aᵖ a' ⟩) ∥ → ⟨ Aᵖ a ⟩)
      lem' (A , Aᵖ) u = lem (A , Aᵖ) u (em ∥ (Σ[ a' ∈ A ] ⟨ Aᵖ a' ⟩) ∥ is-prop-∥∥)

  AC : {ℓ ℓ' : Level} {Γ : Cxt ℓ} (A : Ty Γ ℓ') → Tm Γ (Trunc A) → Tm Γ A
  AC {ℓ = ℓ} {ℓ' = ℓ'} {Γ = Γ} A u = AC-U ℓ' [ s ]
    where
      s : Sub Γ (AC-cxt ℓ')
      s .S γ = (tt , A .Ty.S γ , A .Ty.P γ) , u .Tm.S γ
      s .P γ γᵖ = (tt , ↑ tt) , u .Tm.P γ γᵖ

  AC[] : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ} {A : Ty Γ ℓ''} {u : Tm Γ (Trunc A)} → AC A u [ σ ] ≡ AC (A [ σ ]T) (u [ σ ])
  AC[] = refl


--------------------------------------------------------------------------------
---- no excluded middle

module NoExcludedMiddle where
  ⊤-🔫 : (ℓ : Level) → Ty ∙ ℓ
  ⊤-🔫 ℓ .Ty.S γ = Lift ℓ ⊤
  ⊤-🔫 ℓ .Ty.P γ γᵖ = ⊥ᵖ

  ⊤-🔫-not-dec : (ℓ : Level) → Tm ∙ (Sum (⊤-🔫 ℓ) (Fun (⊤-🔫 ℓ) 𝟘)) → ⊥
  ⊤-🔫-not-dec ℓ (u ◁ uᵖ) = lem (u tt) (uᵖ tt tt)
    where
      lem : (w : ⊤-🔫 ℓ .Ty.S tt ⊎ Fun (⊤-🔫 ℓ) 𝟘 .Ty.S tt) → ⟨ Sum (⊤-🔫 ℓ) (Fun (⊤-🔫 ℓ) 𝟘) .Ty.P tt w ⟩ → ⊥
      lem (inj₁ (↑ tt)) (↑ p) = p .↓
      lem (inj₂ u)      _     = u (↑ tt)

  EM-Ty : (ℓ : Level) → Ty (∙ ▶ U ℓ) ℓ
  EM-Ty ℓ = Sum (El (q {Γ = ∙} (U ℓ))) (Fun (El (q {Γ = ∙} (U ℓ))) 𝟘)

  not-EM : (ℓ : Level) → ¬ Tm (∙ ▶ U ℓ) (EM-Ty ℓ)
  not-EM ℓ t = ⊤-🔫-not-dec ℓ EM-⊤-🔫
    where
      EM-⊤-🔫 : Tm ∙ (EM-Ty ℓ [ pairˢ ε (U ℓ) (code (⊤-🔫 ℓ)) ]T)
      EM-⊤-🔫 = t [ pairˢ ε (U ℓ) (code (⊤-🔫 ℓ)) ]


--------------------------------------------------------------------------------
--- Resizing

module Resizing where
  IsProp : Ty Γ ℓ → Ty Γ ℓ
  IsProp A = Pi A (Pi (A [ p A ]T) (Id (A [ p A ∘ p (A [ p A ]T) ]T) (qp A (A [ p A ]T)) (q (A [ p A ]T))))

  U₀ : Ty Γ (lsuc lzero)
  U₀ = U lzero

  BiImpl : (A : Ty Γ ℓ') (B : Ty Γ ℓ'') → Ty Γ (ℓ' ⊔ ℓ'')
  BiImpl A B = Prod (Fun A B) (Fun B A)

  Resize : {ℓ : Level} {Γ : Cxt ℓ} → Ty Γ ℓ' → Ty Γ (ℓ' ⊔ lsuc lzero)
  Resize {Γ = Γ} A = Sg U₀ (BiImpl (A [ p U₀ ]T) (El (q {Γ = Γ} U₀)))

  CxtRS : (ℓ : Level) → Cxt (lsuc ℓ)
  CxtRS ℓ = ∙ ▶ U ℓ ▶ IsProp (El (q {Γ = ∙} (U ℓ)))

  CxtRSCode : (ℓ : Level) → Tm (CxtRS ℓ) (U ℓ)
  CxtRSCode ℓ = qp {Γ = ∙} (U ℓ) (IsProp (El (q {Γ = ∙} (U ℓ))))

  CxtRSType : (ℓ : Level) → Ty (CxtRS ℓ) ℓ
  CxtRSType ℓ = El (CxtRSCode ℓ)

  RS-lemma : (ℓ : Level) (A : Prop ℓ) (Aᵖ : ⟨ A ⟩ → Prop ℓ) →
    Σ[ B ∈ Prop₀ ] Σ[ p ∈ A ↔ B ] Σ[ Bᵖ ∈ (⟨ B ⟩ → Prop₀) ]
      (((a : ⟨ A ⟩) → ⟨ Aᵖ a ⟩ → ⟨ Bᵖ (p .proj₁ a) ⟩) × ((b : ⟨ B ⟩) → ⟨ Bᵖ b ⟩ → ⟨ Aᵖ (p .proj₂ b) ⟩))
  RS-lemma ℓ A Aᵖ = B , B' .proj₂ , Bᵖ , fwd' , (λ b → Bᵖ' b .proj₂ .proj₂)
    where
      B' : Σ[ B ∈ Prop₀ ] (A ↔ B)
      B' = resize A

      B : Prop₀
      B = B' .proj₁

      fwd : ⟨ A ⟩ → ⟨ B ⟩
      fwd = B' .proj₂ .proj₁

      bwd : ⟨ B ⟩ → ⟨ A ⟩
      bwd = B' .proj₂ .proj₂

      Bᵖ' : (b : ⟨ B ⟩) → Σ[ Bᵖb ∈ Prop₀ ] (Aᵖ (bwd b) ↔ Bᵖb)
      Bᵖ' b' = resize (Aᵖ (bwd b'))

      Bᵖ : (b : ⟨ B ⟩) → Prop₀
      Bᵖ b = Bᵖ' b .proj₁

      fwd' : (a : ⟨ A ⟩) → ⟨ Aᵖ a ⟩ → ⟨ Bᵖ (fwd a) ⟩
      fwd' a u = Bᵖ' (fwd a) .proj₂ .proj₁ (subst (λ a → ⟨ Aᵖ a ⟩) (prop A a (bwd (fwd a))) u)

  RS : (ℓ : Level) → Tm (CxtRS ℓ) (Resize (CxtRSType ℓ))
  RS ℓ .Tm.S ((tt , (A , Aᵖ)) , u) with RS-lemma ℓ (A , u) Aᵖ
  ... | (B , is-prop-B) , (fwd , bwd) , Bᵖ , fwd' , bwd' = (B , Bᵖ) , (fwd , bwd)
  RS ℓ .Tm.P ((tt , (A , Aᵖ)) , u) γᵖ with RS-lemma ℓ (A , u) Aᵖ
  ... | (B , is-prop-B) , (fwd , bwd) , Bᵖ , fwd' , bwd' = ↑ tt , fwd' , bwd'
