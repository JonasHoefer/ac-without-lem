module CwF where

open import Agda.Primitive
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum
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
    P : S → Set ℓ -- should be thought of as a proposition; maybe we have to actually make it one (it is needed for reflection)
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

Elcode : {A : Ty Γ ℓ} → El (code A) ≡ A
Elcode = refl

codeEl : {A : Tm Γ (U ℓ)} → code (El A) ≡ A
codeEl = refl


--------------------------------------------------------------------------------
---- Π

Pi : (A : Ty Γ ℓ') → Ty (Γ ▶ A) ℓ'' → Ty Γ (ℓ' ⊔ ℓ'')
Pi (A ◁ Aᵖ) (B ◁ Bᵖ) .Ty.S γ = (a : A γ) → B (γ , a)
Pi (A ◁ Aᵖ) (B ◁ Bᵖ) .Ty.P γ f = (a : A γ) → Aᵖ γ a → Bᵖ (γ , a) (f a)

Fun : (A : Ty Γ ℓ') → Ty Γ ℓ'' → Ty Γ (ℓ' ⊔ ℓ'')
Fun A B = Pi A (B [ p A ]T)

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

substd : {A : Set ℓ} {P : A → Set ℓ'} (Q : (a : A) → P a → Set ℓ'') {a₀ a₁ : A} (α : a₀ ≡ a₁) (p₀ : P a₀) (q₀ : Q a₀ p₀) → Q a₁ (subst P α p₀)
substd Q refl p₀ q₀ = q₀

Tr : (A : Ty Γ ℓ') (P : Ty (Γ ▶ A) ℓ'') (t₀ t₁ : Tm Γ A) (t : Tm Γ (Id A t₀ t₁)) → Tm Γ (P [ id ,ₛ t₀ ]T) → Tm Γ (P [ id ,ₛ t₁ ]T)
Tr (A ◁ Aᵖ) (P ◁ Pᵖ) (t₀ ◁ t₀ᵖ) (t₁ ◁ t₁ᵖ) (t ◁ tᵖ) (u ◁ uᵖ) .Tm.S γ = subst (λ tᵢ → P (γ , tᵢ)) (t γ) (u γ)
Tr (A ◁ Aᵖ) (P ◁ Pᵖ) (t₀ ◁ t₀ᵖ) (t₁ ◁ t₁ᵖ) (t ◁ tᵖ) (u ◁ uᵖ) .Tm.P γ γᵖ = substd (λ a → Pᵖ (γ , a)) (t γ) (u γ) (uᵖ γ γᵖ)

Trβ : (A : Ty Γ ℓ') (P : Ty (Γ ▶ A) ℓ'') (t : Tm Γ A) (u : Tm Γ (P [ id ,ₛ t ]T)) → Tr A P t t (Refl t) u ≡ u
Trβ A P t u = refl

uip : {A : Set ℓ} {a₀ a₁ : A} (p₀ p₁ : a₀ ≡ a₁) → p₀ ≡ p₁
uip refl refl = refl

UIP : (A : Ty Γ ℓ') (a₀ a₁ : Tm Γ A) (p₀ p₁ : Tm Γ (Id A a₀ a₁)) → Tm Γ (Id (Id A a₀ a₁) p₀ p₁)
UIP A a₀ a₁ p₀ p₁ .Tm.S γ = uip (p₀ .Tm.S γ) (p₁ .Tm.S γ)
UIP A a₀ a₁ p₀ p₁ .Tm.P γ γᵖ = ↑ tt

UIP[] : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ} {A : Ty Γ ℓ''} {a₀ a₁ : Tm Γ A} {p₀ p₁ : Tm Γ (Id A a₀ a₁)} →
  UIP A a₀ a₁ p₀ p₁ [ σ ] ≡ UIP (A [ σ ]T) (a₀ [ σ ]) (a₁ [ σ ]) (p₀ [ σ ]) (p₁ [ σ ])
UIP[] = refl


--------------------------------------------------------------------------------
---- Empty

𝟘 : Ty Γ lzero
𝟘 .Ty.S γ = ⊥
𝟘 .Ty.P γ ()


--------------------------------------------------------------------------------
---- Coprod

Sum : (A : Ty Γ ℓ') (B : Ty Γ ℓ'') → Ty Γ (ℓ' ⊔ ℓ'')
Sum (A ◁ Aᵖ) (B ◁ Bᵖ) .Ty.S γ = A γ ⊎ B γ
Sum {ℓ' = ℓ'} {ℓ'' = ℓ''} (A ◁ Aᵖ) (B ◁ Bᵖ) .Ty.P γ = [ (λ a → Lift ℓ'' (Aᵖ γ a)) , (λ b → Lift ℓ' (Bᵖ γ b)) ]

Sum[] : {Γ : Cxt ℓ} {Δ : Cxt ℓ'} {σ : Sub Δ Γ} {A : Ty Γ ℓ''} {B : Ty Γ ℓ'''} →
  Sum A B [ σ ]T ≡ Sum (A [ σ ]T) (B [ σ ]T)
Sum[] = refl

Inj1 : {A : Ty Γ ℓ'} {B : Ty Γ ℓ''} → Tm Γ A → Tm Γ (Sum A B)
Inj1 (u ◁ uᵖ) .Tm.S γ = inj₁ (u γ)
Inj1 (u ◁ uᵖ) .Tm.P γ γᵖ = ↑ (uᵖ γ γᵖ)

Inj2 : {A : Ty Γ ℓ'} {B : Ty Γ ℓ''} → Tm Γ B → Tm Γ (Sum A B)
Inj2 (u ◁ uᵖ) .Tm.S γ = inj₂ (u γ)
Inj2 (u ◁ uᵖ) .Tm.P γ γᵖ = ↑ (uᵖ γ γᵖ)

Inj1ˢ : {A : Ty Γ ℓ'} {B : Ty Γ ℓ''} → Sub (Γ ▶ A) (Γ ▶ Sum A B)
Inj1ˢ {A = A} = p A ,ₛ Inj1 (q A)

Inj2ˢ : {A : Ty Γ ℓ'} {B : Ty Γ ℓ''} → Sub (Γ ▶ B) (Γ ▶ Sum A B)
Inj2ˢ {B = B} = p B ,ₛ Inj2 (q B)

ElimSum : (A : Ty Γ ℓ') (B : Ty Γ ℓ'') (Q : Ty (Γ ▶ Sum A B) ℓ''') →
  Tm (Γ ▶ A) (Q [ Inj1ˢ ]T) → Tm (Γ ▶ B) (Q [ Inj2ˢ ]T) → Tm (Γ ▶ Sum A B) Q
ElimSum A B Q u v .Tm.S (γ , inj₁ a) = u .Tm.S (γ , a)
ElimSum A B Q u v .Tm.S (γ , inj₂ b) = v .Tm.S (γ , b)
ElimSum A B Q u v .Tm.P (γ , inj₁ a) (γᵖ , ↑ aᵖ) = u .Tm.P (γ , a) (γᵖ , aᵖ)
ElimSum A B Q u v .Tm.P (γ , inj₂ b) (γᵖ , ↑ bᵖ) = v .Tm.P (γ , b) (γᵖ , bᵖ)


--------------------------------------------------------------------------------
---- LEM shit

TG : Ty ∙ lzero
TG .Ty.S γ = ⊤
TG .Ty.P γ γᵖ = ⊥

-- LEM cannot be inhabited since it would yield a term of the following type
not-LEM : Tm ∙ (Sum TG (Fun TG 𝟘)) → ⊥
not-LEM (u ◁ uᵖ) = lem (u tt) (uᵖ tt tt)
  where
    lem : (w : TG .Ty.S tt ⊎ Fun TG 𝟘 .Ty.S tt) → Sum TG (Fun TG 𝟘) .Ty.P tt w → ⊥
    lem (inj₁ tt) (↑ p) = p
    lem (inj₂ u)  _     = u tt
