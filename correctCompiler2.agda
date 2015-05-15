module correctCompiler2 where
-- Del paper McKinna "A type-correct, stack-safe, provably correct, expression...

open import Data.Bool
open import Data.Nat
open import Data.Sum
open import Data.Maybe
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
  val           : ∀ {t} → Val t → Expr t
  _⊕_           : Expr nat → Expr nat → Expr nat
  If_Then_Else_ : {t : Type} → Expr bool → Expr t → Expr t → Expr t

-- Evaluador
eval : {t : Type} → Expr t → Val t
eval (val v)                 = v
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

top : ∀ {t} {s} → Stack (t ∷ s) → Val t
top (v ▹ st) = v

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
  cond[_,_] : ∀ {st} {st'} {s} {s₁'} {s₂'} {b} → 
              (c₁ : Code {st} {st'} s s₁') → (c₂ : Code {st} {st'} s s₂') →
              Code {bool ∷ st} {st'} (b ▹ s) (if b then s₁' else s₂')

-- Ejecucion de código
exec : ∀ {st} {st'} {s : Stack st} {s' : Stack st'} → Code s s' → Stack st'
exec {st} {st'} {s} {s'} c = s'

-- Propiedad
prop : ∀ {st} {t} {v₁ : Val t} {v₂ : Val t} {s : Stack st} → (b : Bool) → 
         (if b then (v₁ ▹ s) else (v₂ ▹ s)) ≡ 
         (if b then v₁ else v₂) ▹ s
prop b with b
prop b | true = refl
prop b | false = refl

-- Compilador
compile : ∀ {st} {t} → {s : Stack st} → (e : Expr t) → Code s (eval e ▹ s)
compile (val v) = push v
compile (e₁ ⊕ e₂) = compile e₂ , (compile e₁ , add)
compile {st} {t} {s} (If e₁ Then e₂ Else e₃) = 
        subst (λ s' → Code s s') (prop (eval e₁)) 
              (compile e₁ , cond[ compile e₂ , compile e₃ ])

-- Prueba de corrección trivial
correct : ∀ {t} {st} → (e : Expr t) → (s : Stack st) →
                    eval e ▹ s ≡ exec (compile {st} {t} {s} e)
correct e s = refl

