-- Segundo prototipo de un evaluador de un lenguaje funcional con imperativo.
module Main

-- Esto representa los tipos de las frases de nuetro lenguaje.
data PhraseType = IntExp | RealExp | BoolExp 
                | IntAcc | RealAcc | BoolAcc
                | IntVar | RealVar | BoolVar
                | (:->) PhraseType PhraseType
                | Comm

infixr 10 :->

-- Operador de punto fijo.
fix : (a -> a) -> a
fix f = f (fix f)

{- 
Semántica para los tipos 
    [[IntExp]]  = int
    [[RealExp]] = real
    [[BoolExp]] = bool
    [[Comm]]    = State -> State
    [[Theta -> Theta']] = [[Theta]] -> [[Theta']]
    
    donde un State es una lista de pares nombre de
    variable, valor de tipo int.
-}
evalTy : PhraseType -> Set
evalTy IntExp    = Int
evalTy RealExp   = Float
evalTy BoolExp   = Bool
evalTy IntAcc    = Int -> evalTy Comm
evalTy IntVar    = (evalTy IntAcc, evalTy IntExp)
evalTy Comm      = List Int -> List Int
evalTy (Theta :-> Theta') = evalTy Theta -> evalTy Theta'

using (Pi:Vect PhraseType n)
    
    data HasType : (i : Fin n) -> Vect PhraseType n -> PhraseType -> Set where
        stop : HasType fO (t :: Pi) t
        pop  : HasType k Pi t -> HasType (fS k) (u :: Pi) t
    
    {- Este tipo representa un juicio de tipado
        pi : Vect PhraseType n
        theta : PhraseType
        pi |-- e : theta
        Donde e son las frases del lenguaje.
    -}
    data Expr : Vect PhraseType n -> PhraseType -> Set where
        Skip    : Expr Pi Comm
        Seq     : Expr Pi Comm    -> Expr Pi Comm   -> Expr Pi Comm
        Assig   : Expr Pi IntVar  -> Expr Pi IntExp -> Expr Pi Comm
        While   : Expr Pi BoolExp -> Expr Pi Comm   -> Expr Pi Comm
        NewVar  : Expr Pi IntVar  -> Expr Pi Comm   -> Expr Pi Comm
        
        Var     : HasType i Pi theta -> Expr Pi theta
        ImpVar  : HasType i Pi IntVar -> Expr Pi IntVar
        
        ValInt  : Int  -> Expr Pi IntExp
        ValBool : Bool -> Expr Pi BoolExp
        
        Lam     : Expr (theta :: Pi) theta'  -> Expr Pi (theta :-> theta')
        App     : Expr Pi (theta :-> theta') -> Expr Pi theta -> Expr Pi theta'
        
        If      : Expr Pi BoolExp -> Expr Pi theta -> Expr Pi theta -> Expr Pi theta
        
        BinOp   : (evalTy a -> evalTy b -> evalTy c)  -> Expr Pi a -> Expr Pi b -> Expr Pi c
        UnaryOp : (evalTy a -> evalTy b) -> Expr Pi a -> Expr Pi b
    
    data Env : Vect PhraseType n -> Set where
        Nil : Env Nil
        (::) : evalTy a -> Env Pi -> Env (a :: Pi)

    lookup : HasType i Pi t -> Env Pi -> evalTy t
    lookup stop (x :: xs) = x
    lookup (pop k) (x :: xs) = lookup k xs
    
    eval : Expr Pi t -> Env Pi -> evalTy t
--     eval (NewVar v c) env = \o => eval c ((a,e) :: env) (0 :: o)
--         where
--             a : evalTy IntAcc
--             a = \x => \o => (x::o)
--             e : evalTy IntExp
--             e = 0
    eval Skip        env = \o => o
    eval (Assig v x) env = \o => (\x => fst (eval v env) x o)(eval x env)
    eval (Seq c c')  env = \o => eval c' env (eval c env o)
    eval (Var i)     env = lookup i env
    eval (ImpVar i)  env = lookup i env
    eval (Lam sc)    env = \x => eval sc (x :: env)
    eval (App f s)   env = (eval f env) (eval s env)
    eval (BinOp op x y) env = op (eval x env) (eval y env)
    eval (If x t e)  env = if eval x env then eval t env else eval e env
    eval (While b c) env = fix uf
        where
            uf : evalTy Comm -> evalTy Comm
            uf f o = if eval b env then f (eval c env o) else o
    
    -- /////////////// Ejemplos /////////////// 
    id : Expr Pi (IntExp :-> IntExp)
    id = Lam (Var stop)
    -- /////////////// Ejemplos /////////////// 
    
main : IO ()
main = print (eval id [] 3)
