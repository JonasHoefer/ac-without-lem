module CwF where

open import Agda.Primitive
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

private
  variable ℓ ℓ' ℓ'' ℓ''' : Level

record Lift {i} j (A : Set i) : Set (i ⊔ j) where
  constructor ↑
  field
    ↓ : A
open Lift

record Cxt (ℓ : Level) : Set (lsuc ℓ) where
  constructor _◁_
  field
    S : Set ℓ
    P : S → Set ℓ -- should be thought of as a proposition; maybe we have to actually make it one
open Cxt

private
  variable
    Γ : Cxt ℓ
    Δ : Cxt ℓ'
    Θ : Cxt ℓ''
    Ρ : Cxt ℓ'''

∙ : Cxt lzero
∙ = ⊤ ◁ (λ _ → ⊤)

record Sub (Γ : Cxt ℓ) (Δ : Cxt ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _◁_
  field
    S : Γ .S → Δ .S
    P : (γ : Γ .Cxt.S) → Γ .P γ → Δ .P (S γ)
open Sub

private
  variable
    σ : Sub Δ Γ
    τ : Sub Θ Δ

id : Sub Γ Γ
id = (λ z → z) ◁ (λ γ z → z)

infixr 5 _∘_
_∘_ : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
(σ ◁ σᵖ) ∘ (τ ◁ τᵖ) = (λ z → σ (τ z)) ◁ (λ γ z → σᵖ (τ γ) (τᵖ γ z))

ε : Sub Γ ∙
ε = (λ _ → tt) ◁ (λ γ _ → tt)

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
    P : (γ : Γ .Cxt.S) → S γ → Set ℓ'

private variable A : Ty Γ ℓ

infixl 3 _▶_
_▶_ : (Γ : Cxt ℓ) (A : Ty Γ ℓ') → Cxt (ℓ ⊔ ℓ')
(Γ ◁ Γᴾ) ▶ (A ◁ Aᵖ) = Σ Γ A ◁ (λ (γ , a) → Σ[ γᵖ ∈ Γᴾ γ ] Aᵖ γ a)

record Tm (Γ : Cxt ℓ) (A : Ty Γ ℓ') : Set (ℓ ⊔ lsuc ℓ') where
  constructor _◁_
  field
    S : (γ : Γ .S) → A .Ty.S γ
    P : (γ : Γ .Cxt.S) (γᵖ : Γ .P γ) → A .Ty.P γ (S γ)

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

p : (A : Ty {ℓ} Γ ℓ') → Sub (Γ ▶ A) Γ
p (A ◁ Aᵖ) = (λ (γ , a) → γ) ◁ (λ (γ , a) (γᵖ , aᵖ) → γᵖ)

q : {Γ : Cxt ℓ} (A : Ty Γ ℓ') → Tm (Γ ▶ A) (A [ p A ]T)
q (A ◁ Aᵖ) = (λ (γ , a) → a) ◁ (λ (γ , a) (γᵖ , aᵖ) → aᵖ)

_,ₛ_ : (σ : Sub Γ Δ) → Tm {ℓ}{ℓ'} Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
(σ ◁ σᵖ) ,ₛ (a ◁ aᵖ) = (λ γ → σ γ , a γ) ◁ (λ γ γᵖ → σᵖ γ γᵖ , aᵖ γ γᵖ)

pβ : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {A : Ty Γ ℓ''} {σ : Sub Δ Γ} {a : Tm Δ (A [ σ ]T)} → p A ∘ (σ ,ₛ a) ≡ σ
pβ = refl

qβ : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {A : Ty Γ ℓ''} {σ : Sub Δ Γ} {a : Tm Δ (A [ σ ]T)} → q A [ σ ,ₛ a ] ≡ a
qβ = refl

,ₛη : (p A ,ₛ q A) ≡ id
,ₛη = refl

,ₛ∘ : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {Θ : Cxt ℓ''} {A : Ty Γ ℓ'''} {σ : Sub Δ Γ} {τ : Sub Θ Δ} {a : Tm Δ (A [ σ ]T)} → ((_,ₛ_ {A = A} σ a) ∘ τ) ≡ ((σ ∘ τ) ,ₛ (a [ τ ]))
,ₛ∘ = refl

--------------------------------------------------------------------------------
---- Universes

-- This is different from the exceptional thing!
-- we still get a Coquand style universe since we redfined the presheaf of types to be represented by U

U : (ℓ : Level) → Ty Γ (lsuc ℓ)
U ℓ .Ty.S γ = Σ[ A ∈ Set ℓ ] (A → Set ℓ) -- same here; maybe this should be prop
U ℓ .Ty.P γ (A , Aᵖ) = Lift (lsuc ℓ) ⊤

El : Tm Γ (U ℓ) → Ty Γ ℓ
El (A ◁ _) = (λ γ → A γ .proj₁) ◁ (λ γ a → A γ .proj₂ a)

code : Ty Γ ℓ → Tm Γ (U ℓ)
code (A ◁ Aᵖ) = (λ γ → A γ , λ a → Aᵖ γ a) ◁ (λ γ γᵖ → ↑ tt)

--------------------------------------------------------------------------------
---- Π

Pi : (A : Ty Γ ℓ') → Ty (Γ ▶ A) ℓ'' → Ty Γ (ℓ' ⊔ ℓ'')
Pi (A ◁ Aᵖ) (B ◁ Bᵖ) .Ty.S γ = (a : A γ) → B (γ , a)
Pi (A ◁ Aᵖ) (B ◁ Bᵖ) .Ty.P γ f = (a : A γ) → Aᵖ γ a → Bᵖ (γ , a) (f a)

Lam : {A : Ty Γ ℓ'} {B : Ty (Γ ▶ A) ℓ''} → Tm (Γ ▶ A) B → Tm Γ (Pi A B)
Lam (b ◁ bᵖ) .Tm.S γ a = b (γ , a)
Lam (b ◁ bᵖ) .Tm.P γ γᵖ a aᵖ = bᵖ (γ , a) (γᵖ , aᵖ)

App : {A : Ty Γ ℓ'} {B : Ty (Γ ▶ A) ℓ''} → Tm Γ (Pi A B) → Tm (Γ ▶ A) B
App (f ◁ fᵖ) .Tm.S (γ , a) = f γ a
App (f ◁ fᵖ) .Tm.P (γ , a) (γᵖ , aᵖ) = fᵖ γ γᵖ a aᵖ

Πβ : {A : Ty Γ ℓ'} {B : Ty (Γ ▶ A) ℓ''} (b : Tm (Γ ▶ A) B) → App (Lam b) ≡ b
Πβ b = refl

Πη : {A : Ty Γ ℓ'} {B : Ty (Γ ▶ A) ℓ''} (f : Tm Γ (Pi A B)) → Lam (App {A = A} {B = B} f) ≡ f -- maybe no-eta on type?
Πη b = refl


--------------------------------------------------------------------------------
---- Id

Id : (A : Ty Γ ℓ') (u v : Tm Γ A) → Ty Γ ℓ'
Id A (u ◁ _) (v ◁ _) .Ty.S γ = (u γ ≡ v γ)
Id A (u ◁ _) (v ◁ _) .Ty.P γ _ = Lift _ ⊤

Refl : (t : Tm Γ A) → Tm Γ (Id A t t)
Refl t = (λ γ → refl) ◁ (λ γ γᵖ → ↑ tt)

Tr : (A : Ty Γ ℓ') (P : Ty (Γ ▶ A) ℓ'') {t₀ t₁ : Tm Γ A} (t : Tm Γ (Id A t₀ t₁)) → Tm Γ (P [ id ,ₛ t₀ ]T) → Tm Γ (P [ id ,ₛ t₁ ]T)
Tr (A ◁ Aᵖ) (P ◁ Pᵖ) (t ◁ tᵖ) (u ◁ uᵖ) .Tm.S γ = subst (λ tᵢ → P (γ , tᵢ)) (t γ) (u γ)
Tr (A ◁ Aᵖ) (P ◁ Pᵖ) (t ◁ tᵖ) (u ◁ uᵖ) .Tm.P γ γᵖ = subst (λ tᵢ → Pᵖ (γ , tᵢ) {!!}) (t γ) {!uᵖ γ!}
