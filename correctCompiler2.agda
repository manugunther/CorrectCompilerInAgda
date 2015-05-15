module correctCompiler2 where
-- Del paper McKinna "A type-correct, stack-safe, provably correct, expression...

open import Data.Bool
open import Data.Nat
open import Data.Sum
open import Function
open import Data.List
open import Relation.Binary.PropositionalEquality


-- Tipos
data Type : Set where
  bool : Type
  nat  : Type

-- Valores
Val : Type → Set
Val bool = Bool
Val nat  = ℕ

-- Expresiones del lenguaje
data Expr : Type → Set where
  ∣_∣            : ∀ {t} → Val t → Expr t
  _⊕_           : Expr nat → Expr nat → Expr nat
  If_Then_Else_ : {t : Type} → Expr bool → Expr t → Expr t → Expr t

-- Evaluador
eval : {t : Type} → Expr t → Val t
eval ∣ v ∣                    = v
eval (e ⊕ e')                = eval e + eval e'
eval (If e₁ Then e₂ Else e₃) = if eval e₁ then eval e₂ else eval e₃

{- StackType representa los tipos de los elementos que
   estan en el stack -}
StackType : Set
StackType = List Type

-- Stack de valores
data Stack : (s : StackType) → Set where
  ε   : Stack []
  _▹_ : ∀ {t} {s} → Val t → Stack s → Stack (t ∷ s)

-- Lenguaje de máquina, conteniendo información de cómo queda el stack
-- luego de la ejecución del código, para poder asegurar la corrección.
data Code : ∀ {st} {st'} → Stack st → Stack st' → Set where
  skip      : ∀ {st} → {s : Stack st} → Code s s
  _,_       : ∀ {st₀} {st₁} {st₂} → 
                {s₀ : Stack st₀} {s₁ : Stack st₁} {s₂ : Stack st₂} → 
                (c₁ : Code s₀ s₁) → (c₂ : Code s₁ s₂)  → Code s₀ s₂
  push      : ∀ {st} {s : Stack st} {t} → (v : Val t) → Code s (v ▹ s)
  add       : ∀ {st} {s : Stack st} {m} {n} → 
                Code {nat ∷ nat ∷ st} {nat ∷ st} (m ▹ (n ▹ s)) ((m + n) ▹ s)
  cond[_,_] : ∀ {st} {st'} {s} {s₁} {s₂} {b} → 
              (c₁ : Code {st} {st'} s s₁) → (c₂ : Code {st} {st'} s s₂) →
              Code {bool ∷ st} {st'} (b ▹ s) (if b then s₁ else s₂)

-- Ejecucion de código
exec : ∀ {st} {st'} {s : Stack st} {s' : Stack st'} → Code s s' → Stack st'
exec {st} {st'} {s} {s'} c = s'

-- Propiedad del if
prop : ∀ {θ : Set} {θ' : Set} {t₁ : θ} {t₂ : θ} → 
         (f : θ → θ') → (b : Bool) → 
         (if b then f t₁ else f t₂) ≡
         f (if b then t₁ else t₂)
prop f b with b
prop f b | true = refl
prop f b | false = refl

-- Compilador
compile : ∀ {st} {t} → {s : Stack st} → (e : Expr t) → Code s (eval e ▹ s)
compile ∣ v ∣ = push v
compile (e₁ ⊕ e₂) = compile e₂ , (compile e₁ , add)
compile {st} {t} {s} (If e₁ Then e₂ Else e₃) = 
        subst (λ s' → Code s s') (prop (λ v → v ▹ s) (eval e₁)) 
              (compile e₁ , cond[ compile e₂ , compile e₃ ])

-- Prueba de corrección trivial
correct : ∀ {t} {st} → (e : Expr t) → (s : Stack st) →
                    eval e ▹ s ≡ exec (compile e)
correct e s = refl



-- Algun ejemplo
exprExample : Expr bool → Expr nat → Expr nat
exprExample eb en = 
            If eb Then (en ⊕ ∣ 2 ∣) Else (en ⊕ ∣ 1 ∣)

evalExample : Expr bool → Expr nat → Val nat
evalExample eb = eval ∘ exprExample eb

execExample : ∀ {t} → Expr bool → Expr nat → Stack t → Stack (nat ∷ t)
execExample {t} eb en s = exec {t} {nat ∷ t} {s} (compile (exprExample eb en))