module correctCompiler3 where
-- Del paper McKinna "A type-correct, stack-safe, provably correct, expression...

open import Data.Bool
open import Data.Nat
open import Data.Product
open import Function
open import Data.List hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.EqReasoning 
open import Data.String


-- Tipos
data Type : Set where
  bool : Type
  nat  : Type

-- Valores
Val : Type → Set
Val bool = Bool
Val nat  = ℕ

-- Variables
Var : Set
Var = String

-- Estado de asignaciones de variables a valores
State : Set
State = Var → ℕ

-- Estado inicial
emptyS : State
emptyS = (λ x → 0)

-- Modificación del estado
_[_←_] : State → Var → ℕ → State
σ [ x ← n ] = λ y → if y == x then n
                              else σ y

-- Expresiones del lenguaje
data Expr : Type → Set where
  ∣_∣            : ∀ {t} → Val t → Expr t
  _⊕_           : Expr nat → Expr nat → Expr nat
  var           : Var → Expr nat

data Statement : Set where
  _:=_          : Var → Expr nat → Statement
  _,_           : Statement → Statement → Statement
  If_Then_Else_ : Expr bool → Statement → Statement → Statement


-- Semántica de expresiones
⟦_⟧_  : {t : Type} → Expr t → State → Val t
⟦ ∣ v ∣ ⟧ σ                  = v
⟦ e ⊕ e' ⟧ σ                = ⟦ e ⟧ σ + ⟦ e' ⟧ σ
⟦ var x ⟧ σ                 = σ x

-- Evaluador de sentencias
⟨_⟩_ : Statement → State → State
⟨ x := e ⟩ σ               = σ [ x ← ⟦ e ⟧ σ ]
⟨ s₁ , s₂ ⟩ σ              = ⟨ s₂ ⟩ (⟨ s₁ ⟩ σ)
⟨ If e Then s₁ Else s₂ ⟩ σ = if ⟦ e ⟧ σ then ⟨ s₁ ⟩ σ
                                        else ⟨ s₂ ⟩ σ

{- StackType representa los tipos de los elementos que
   estan en el stack -}
StackType : Set
StackType = List Type

-- Stack de valores
data Stack : (s : StackType) → Set where
  ε   : Stack []
  _▹_ : ∀ {t} {s} → Val t → Stack s → Stack (t ∷ s)


-- La "configuración" de una máquina está determinada
-- por el stack y el estado
Conf : StackType → Set
Conf st = Stack st × State


data Code : ∀ {st} {st'} → (sσ₁ : Conf st) → (sσ₂ : Conf st') → Set where
  skip      : ∀ {st} {sσ : Stack st × State} → Code sσ sσ
  _,_       : ∀ {st₀} {st₁} {st₂} 
                {sσ₀ : Conf st₀} {sσ₁ : Conf st₁} {sσ₂ : Conf st₂}  → 
                (c₁ : Code sσ₀ sσ₁) → (c₂ : Code sσ₁ sσ₂)  → Code sσ₀ sσ₂
  push      :  ∀ {t} → (v : Val t) → {st : StackType} {sσ : Conf st} → 
                 Code sσ (v ▹ proj₁ sσ , proj₂ sσ)
  add       : ∀ {st} {s : Stack st} {σ : State} {m} {n} → 
                Code {nat ∷ nat ∷ st} {nat ∷ st} 
                     (m ▹ (n ▹ s) , σ) ((m + n) ▹ s , σ)
  cond[_,_] : ∀ {st} {st'} {sσ₁} {sσ₂} {b} {s} {σ} → 
              (c₁ : Code {st} {st'} (s , σ) sσ₁) → 
              (c₂ : Code {st} {st'} (s , σ) sσ₂) →
              Code {bool ∷ st} {st'} (b ▹ s , σ) (if b then sσ₁ else sσ₂)
  load      : ∀ {st} {s : Stack st} {σ} → (x : Var) → 
              Code (s , σ) (σ x ▹ s , σ)
  store     : ∀ {st} {s : Stack st} {σ} {n} → (x : Var) → 
              Code {nat ∷ st} {st} (n ▹ s , σ) (s , σ [ x ← n ]) 
 
-- Compilador de expresiones
compₑ : ∀ {st} {t} {s : Stack st} {σ}→ (e : Expr t) → 
        Code (s , σ) (⟦ e ⟧ σ ▹ s , σ)
compₑ ∣ v ∣      = push v
compₑ (e₁ ⊕ e₂) = compₑ e₂ , (compₑ e₁ , add)
compₑ (var x)   = load x


-- Propiedades del if
prop : ∀ {θ : Set} {θ' : Set} {t₁ : θ} {t₂ : θ} {b : Bool} →
         (f : θ → θ') → 
         f (if b then t₁ else t₂) ≡
         (if b then f t₁ else f t₂)
prop {b = b} f with b
... | true = refl
... | false = refl

prop₂ : ∀ {θ : Set} {t : θ} {b : Bool} → (if b then t else t) ≡ t
prop₂ {θ} {t} {b} with b
... | true = refl
... | false = refl

-- Compilador de sentencias
compₛ : ∀ {st} {s : Stack st} {σ} → (c : Statement) → 
        Code {st} {st} (s , σ) (s , ⟨ c ⟩ σ)
compₛ (x := e)               = compₑ e , store x
compₛ (s₁ , s₂)              = compₛ s₁ , compₛ s₂
compₛ {st} {s} {σ} (If e Then s₁ Else s₂) = 
      subst₂ (λ s' σ' → Code (s , σ) (s' , σ')) 
             aux aux₂ (compₑ e , cond[ compₛ s₁ , compₛ s₂ ])
  where aux : proj₁ (if ⟦ e ⟧ σ then s , ⟨ s₁ ⟩ σ else s , ⟨ s₂ ⟩ σ) ≡ s
        aux = trans (prop {Conf st} {Stack st} {s , ⟨ s₁ ⟩ σ} {s , ⟨ s₂ ⟩ σ}
                          {⟦ e ⟧ σ} proj₁) (prop₂ {Stack st} {s} {⟦ e ⟧ σ})
        aux₂ : proj₂ (if ⟦ e ⟧ σ then s , ⟨ s₁ ⟩ σ else s , ⟨ s₂ ⟩ σ) ≡
               (if ⟦ e ⟧ σ then ⟨ s₁ ⟩ σ else ⟨ s₂ ⟩ σ)
        aux₂ = prop {Conf st} {State} {s , ⟨ s₁ ⟩ σ} {s , ⟨ s₂ ⟩ σ} 
                    {⟦ e ⟧ σ} proj₂

