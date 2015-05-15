module correctCompiler where
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

-- Lenguaje compilado
data Code : StackType → StackType → Set where
  skip      : ∀ {s} → Code s s
  _,_       : ∀ {s₀} {s₁} {s₂} → (c₁ : Code s₀ s₁) → (c₂ : Code s₁ s₂) 
                                                   → Code s₀ s₂
  push      : ∀ {s} {t} → (v : Val t) → Code s (t ∷ s)
  add       : ∀ {s} → Code (nat ∷ nat ∷ s) (nat ∷ s)
  cond[_,_] : ∀ {s} {s'} → (c₁ : Code s s') → (c₂ : Code s s') 
                                            → Code (bool ∷ s) s'

-- Ejecucion de código
exec : ∀ {s} {s'} → Code s s' → Stack s → Stack s'
exec skip s = s
exec (c₁ , c₂) s = exec c₂ (exec c₁ s)
exec (push v) s = v ▹ s
exec add (n ▹ (m ▹ s)) = (n + m) ▹ s
exec cond[ c₁ , c₂ ] (b ▹ s) with b
... | true = exec c₁ s
... | false = exec c₂ s

-- Compilador
compile : ∀ {t} {s} → Expr t → Code s (t ∷ s)
compile (val v) = push v
compile (e₁ ⊕ e₂) = compile e₂ , (compile e₁ , add)
compile (If e₁ Then e₂ Else e₃) = compile e₁ , cond[ compile e₂ , compile e₃ ]


-- Corrección
correct : ∀ {t} {s} → (e : Expr t) → (st : Stack s) →
                    eval e ▹ st ≡ exec (compile e) st
correct (val v) st = refl 
correct (e₁ ⊕ e₂) st = trans refl (cong (λ st' → exec add st') p)
  where p : eval e₁ ▹ (eval e₂ ▹ st) ≡ exec (compile e₁) (exec (compile e₂) st)
        p = trans (correct e₁ (eval e₂ ▹ st)) 
                  (cong (λ st → exec (compile e₁) st) (correct e₂ st))
correct (If b Then e₁ Else e₂) st' = trans p₂ p₁
  where p₁ : exec cond[ compile e₁ , compile e₂ ] (eval b ▹ st') ≡ 
             exec cond[ compile e₁ , compile e₂ ] (exec (compile b) st')
        p₁ = cong (λ st → exec cond[ compile e₁ , compile e₂ ] st) 
                  (correct b st')
        p₂ : (if eval b then eval e₁ else eval e₂) ▹ st' ≡
             exec cond[ compile e₁ , compile e₂ ] (eval b ▹ st')
        p₂ with eval b
        p₂ | true = correct e₁ st'
        p₂ | false = correct e₂ st'
