module correctCompiler4 where

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
  If_then_else_ : Expr bool → Statement → Statement → Statement
  for_do_       : Expr nat → Statement → Statement


-- Semántica de expresiones
⟦_⟧_  : {t : Type} → Expr t → State → Val t
⟦ ∣ v ∣ ⟧ σ                  = v
⟦ e ⊕ e' ⟧ σ                = ⟦ e ⟧ σ + ⟦ e' ⟧ σ
⟦ var x ⟧ σ                 = σ x



-- Evaluador de sentencias
⟪_⟫_ : Statement → State → State
⟪ x := e ⟫ σ               = σ [ x ← ⟦ e ⟧ σ ]
⟪ s₁ , s₂ ⟫ σ              = ⟪ s₂ ⟫ (⟪ s₁ ⟫ σ)
⟪ If e then s₁ else s₂ ⟫ σ = if ⟦ e ⟧ σ then ⟪ s₁ ⟫ σ
                                           else ⟪ s₂ ⟫ σ
⟪ for e do s ⟫ σ = rec (⟦ e ⟧ σ) s σ
  where rec : ℕ → Statement → State → State
        rec zero s' σ' = σ'
        rec (suc n) s' σ' = rec n s' (⟪ s' ⟫ σ')

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

looprec : ∀ {st} → ℕ → (Conf st → Conf st) → Conf st → Conf st
looprec zero f sσ = sσ
looprec (suc n) f sσ = looprec n f (f sσ)


data Code :   ∀ {st'} → (st : StackType) → (f : Conf st → Conf st') → Set where
  skip      : ∀ {st} → Code st id
  _,_       : ∀ {st₀} {st₁} {st₂} →
              {f₁ : Conf st₀ → Conf st₁} →
              {f₂ : Conf st₁  → Conf st₂} →
              (c₁ : Code st₀ f₁) → (c₂ : Code st₁ f₂) →
              Code st₀ (f₂ ∘ f₁)
  push      :  ∀ {t} {st} → (v : Val t) → 
               Code st (λ sσ → v ▹ proj₁ sσ , proj₂ sσ)
  add       : ∀ {st}  → 
              Code (nat ∷ nat ∷ st)
                   (λ {(m ▹ (n ▹ s) , σ) → ((m + n) ▹ s , σ)})
  cond[_,_] : ∀ {st} {st'} → 
              {f₁ : Conf st → Conf st'} → {f₂ : Conf st → Conf st'} →
              (c₁ : Code st f₁) → (c₂ : Code st f₂) →
              Code (bool ∷ st)
                   (λ {(b ▹ s , σ)  → (if b then f₁ (s , σ) 
                                            else f₂ (s , σ))})
  load      : ∀ {st} → (x : Var) → 
                Code st (λ {(s , σ) → (σ x ▹ s , σ)})
  store     : ∀ {st} → (x : Var) → 
                 Code (nat ∷ st) (λ {(n ▹ s , σ)  → (s , σ [ x ← n ])})
  loop      : ∀ {st} {f : Conf st → Conf st} → 
                Code st f → Code (nat ∷ st)
                                 (λ {(n ▹ s , σ) → looprec n f (s , σ)})


-- Compilador de expresiones
compₑ : ∀ {st} {t}  → 
        (e : Expr t) → Code st (λ {(s , σ) → (⟦ e ⟧ σ ▹ s , σ)})
compₑ ∣ v ∣      = push v
compₑ (e₁ ⊕ e₂) = compₑ e₂ , (compₑ e₁ , add)
compₑ (var x)   = load x


-- Propiedades del if
propIf₁ : ∀ {θ : Set} {θ' : Set} {t₁ : θ} {t₂ : θ} {b : Bool} →
         (f : θ → θ') → 
         f (if b then t₁ else t₂) ≡
         (if b then f t₁ else f t₂)
propIf₁ {b = b} f with b
... | true = refl
... | false = refl

propIf₂ : ∀ {θ : Set} {t : θ} {t' : θ} {b : Bool} → t' ≡ t →
        (if b then t else t') ≡ t
propIf₂ {θ} {t} {t'} {b} t'≡t with b
... | true = refl
... | false = t'≡t


propIf× : ∀ {A B : Set} → (b : Bool) → (t₁ : A × B) → 
           (t₂ : A × B) → proj₁ t₂ ≡ proj₁ t₁ →
           (if b then t₁ else t₂)
           ≡
           (proj₁ t₁ , (if b then proj₂ t₁ else proj₂ t₂))
propIf× {A} {B} b t₁ t₂ p  = 
           cong₂ (λ x y → x , y) 
           (trans (propIf₁ {A × B} {A} {t₁} {t₂} {b} proj₁)
                  (propIf₂ {A} {proj₁ t₁} {proj₁ t₂} {b} p)) 
           (propIf₁ {A × B} {B} {t₁} {t₂} {b} proj₂)

-- Postulado de Extensionalidad
postulate pointwiseEq : ∀ {l} {A B : Set l} {f₁ : A → B} {f₂ : A → B}
                        → ((x : A) → f₁ x ≡ f₂ x) → f₁ ≡ f₂

-- Compilador de sentencias
compₛ : ∀ {st}  → (c : Statement) → 
        Code st (λ {(s , σ) → (s , ⟪ c ⟫ σ)})
compₛ (x := e)               = compₑ e , store x
compₛ (s₁ , s₂)              = compₛ s₁ , compₛ s₂
compₛ {st} (If e then s₁ else s₂) = 
      subst (λ f → Code st f) (pointwiseEq aux')
                              (compₑ e , cond[ compₛ s₁ , compₛ s₂ ]) 
      where aux' : (sσ : Conf st) →
                   (if ⟦ e ⟧ (proj₂ sσ) then (proj₁ sσ , ⟪ s₁ ⟫ proj₂ sσ)
                                        else (proj₁ sσ , ⟪ s₂ ⟫ proj₂ sσ))
                   ≡
                   (proj₁ sσ , (if ⟦ e ⟧ (proj₂ sσ) then ⟪ s₁ ⟫ (proj₂ sσ)
                                                   else ⟪ s₂ ⟫ (proj₂ sσ)))
            aux' sσ = propIf× (⟦ e ⟧ proj₂ sσ) (proj₁ sσ , ⟪ s₁ ⟫ proj₂ sσ) 
                                               (proj₁ sσ , ⟪ s₂ ⟫ proj₂ sσ)
                                               refl
compₛ (for e do c) = {!!} --compₑ e , loop (compₛ c)
