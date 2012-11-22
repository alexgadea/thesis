-- Primer prototipo de evaluador para un lenguaje con tipos simples.
module Main

-- Esto representa los tipos de las frases de nuetro lenguaje.
data PhraseType = IntExp | RealExp | BoolExp 
                | (:->) PhraseType PhraseType

infixr 10 :->

{- 
Semántica para los tipos 
    [[IntExp]]  = int
    [[RealExp]] = real
    [[BoolExp]] = bool
    [[Theta :-> Theta]] = [[Theta]] -> [[Theta]]
-}
evalTy : PhraseType -> Set
evalTy IntExp    = Int
evalTy RealExp   = Float
evalTy BoolExp   = Bool
evalTy (Theta :-> Theta') = evalTy Theta -> evalTy Theta'

using (Pi:Vect PhraseType n)
    
    data HasType : (i : Fin n) -> Vect PhraseType n -> PhraseType -> Set where
        stop : HasType fO (t :: Pi) t
        pop  : HasType k Pi t -> HasType (fS k) (u :: Pi) t
    
    -- Definimos la semántica para un environment.
    data Env : Vect PhraseType n -> Set where
        Nil : Env Nil
        (::) : evalTy a -> Env Pi -> Env (a :: Pi)
    
    lookup : HasType i Pi t -> Env Pi -> evalTy t
    lookup stop (x :: xs) = x
    lookup (pop k) (x :: xs) = lookup k xs
    
    -- Este tipo representa un juicio de tipado
    -- pi : Vect PhraseType n
    -- theta : PhraseType
    -- pi |-- e : theta
    -- Donde e son las frases del lenguaje.
    data Expr : Vect PhraseType n -> PhraseType -> Set where
        Var   : HasType i Pi theta -> Expr Pi theta
        ValI  : Int   -> Expr Pi IntExp
        ValB  : Bool  -> Expr Pi BoolExp
        ValR  : Float -> Expr Pi RealExp
        Lam   : Expr (theta :: Pi) theta' -> Expr Pi (theta :-> theta')
        App   : Expr Pi (theta :-> theta') -> Expr Pi theta -> Expr Pi theta'
        If    : Expr Pi BoolExp -> Expr Pi theta -> Expr Pi theta -> Expr Pi theta
        BinOp : (evalTy a -> evalTy b -> evalTy c) -> Expr Pi a -> Expr Pi b -> Expr Pi c
        UnOp  : (evalTy a -> evalTy b) -> Expr Pi a -> Expr Pi b
    
    -- Definimos la semántica para los juicios de tipado del lenguaje.
    eval : Expr Pi t -> Env Pi -> evalTy t
    -- [[Pi |-- Var i : theta]]eta = eta i
    eval (Var i)     env = lookup i env
    -- [[Pi |-- ValI x : IntExp]]eta = x
    eval (ValI x)    env = x
    -- [[Pi |-- ValB x : IntExp]]eta = x
    eval (ValB x)    env = x
    -- [[Pi |-- ValR x : IntExp]]eta = x
    eval (ValR x)    env = x    
    -- [[Pi |-- \-> b : theta :-> theta']]eta = \x -> [[Pi,x:theta |-- b : theta']](x|eta)
    eval (Lam b)    env = \x => eval b (x :: env)
    -- [[Pi |-- ee' : theta']]eta = ([[Pi |-- e: theta :-> theta']]eta)([[Pi |-- e:theta]]eta)
    eval (App e e')   env = (eval e env) (eval e' env)
    -- [[Pi |-- x op y : theta]]eta = [[Pi |-- x:theta]]eta op [[Pi |-- y:theta]]eta
    -- con op : theta -> theta -> theta.
    eval (BinOp op x y) env = op (eval x env) (eval y env)
    -- [[Pi |-- op x : theta]]eta = op [[Pi |-- x:theta]]eta
    -- con op : theta -> theta.
    eval (UnOp op x) env = op (eval x env)
    -- [[Pi |-- if b then e else e' : theta]]eta = 
    --                  if [[Pi |-- b : BoolExp]]eta 
    --                     then [[Pi |-- e:theta]]eta 
    --                     else [[Pi |-- e':theta]]eta 
    eval (If b e e')  env = if eval b env then eval e env else eval e' env
    
    -- /////////////// Ejemplos /////////////// 
    add : Expr Pi (IntExp :-> IntExp :-> IntExp)
    add = Lam (Lam (BinOp (+) (Var stop) (Var (pop stop))))
    
    andt : Expr Pi (BoolExp :-> BoolExp :-> BoolExp)
    andt = Lam (Lam (BinOp (&&) (Var stop) (Var (pop stop))))
    
    add' : Expr Pi IntExp
    add' = App (App add (ValI 0)) (ValI 1)
    
    and' : Expr Pi BoolExp
    and' = App (App andt (ValB True)) (ValB False)
    
    fact :    Expr Pi (IntExp :-> IntExp)
    fact = Lam (If (BinOp (==) (Var stop) (ValI 0)) 
                {-Then-} (ValI 1) 
                {-Else-} (BinOp (*) (App fact (BinOp (-) (Var stop) (ValI 1))) (Var stop)))
    -- /////////////// Ejemplos /////////////// 

main : IO ()
main = print (eval add' [])
