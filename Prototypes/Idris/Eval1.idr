
-- Segundo prototipo de un evaluador de un lenguaje funcional con imperativo.
module Main

data DataType = IntDT | RealDT | BoolDT

-- Esto representa los tipos de las frases de nuetro lenguaje.
data PhraseType = IntExp | RealExp | BoolExp 
                | IntAcc | RealAcc | BoolAcc
                | IntVar | RealVar | BoolVar
                | (:->) PhraseType PhraseType
                | Comm

infixr 10 :->
infixr 10 <~
infixr 10 :>
infixr 10 :~

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
    
    data Env : {n:Nat} -> Vect PhraseType n -> Set where
        ENil : Env Nil
        (:>) : {xs : Vect PhraseType n} -> evalTy a -> Env xs -> Env (a :: xs)
    
    lookup : HasType i Pi t -> Env Pi -> evalTy t
    lookup stop (x :> xs) = x
    lookup (pop k) (x :> xs) = lookup k xs
    
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
        NewVar  : Expr Pi IntExp  -> Expr (IntVar :: Pi) Comm -> Expr Pi Comm
        
        Var     : HasType i Pi theta -> Expr Pi theta
        
        ValInt  : Int  -> Expr Pi IntExp
        ValBool : Bool -> Expr Pi BoolExp
        
        Lam     : Expr (theta :: Pi) theta'  -> Expr Pi (theta :-> theta')
        App     : Expr Pi (theta :-> theta') -> Expr Pi theta -> Expr Pi theta'
        
        If      : Expr Pi BoolExp -> Expr Pi theta -> Expr Pi theta -> Expr Pi theta
        
        BinOp   : (evalTy a -> evalTy b -> evalTy c)  -> Expr Pi a -> Expr Pi b -> Expr Pi c
        UnaryOp : (evalTy a -> evalTy b) -> Expr Pi a -> Expr Pi b
        
    data (<~) : PhraseType -> PhraseType -> Set where
        VarToAcc : IntVar <~ IntAcc
        VarToExp : IntVar <~ IntExp
    
    evalLeq : t <~ t' -> evalTy t -> evalTy t'
    evalLeq (VarToAcc) (a,e) = a
    evalLeq (VarToExp) (a,e) = e
    
    eval : Expr Pi t -> Env Pi -> evalTy t
    eval (NewVar v c) env = \o => eval c ((a,e) :> env) ((eval v env) :: o)
        where
            a : evalTy IntAcc
            a = (::)--\x => \o => x::tail o
            e : evalTy IntExp
            e = 0--lookup stop (0::Nil)
    eval Skip        env = \o => o
    eval (Assig v x) env = \o => (\x => fst (eval v env) x o) (eval x env)
    eval (Seq c c')  env = \o => eval c' env (eval c env o)
    eval (Var i)     env = lookup i env
    eval (ValInt i)  env = i
    eval (ValBool b) env = b
    eval (Lam sc)    env = \x => eval sc (x :> env)
    eval (App f s)   env = (eval f env) (eval s env)
    eval (BinOp op x y) env = op (eval x env) (eval y env)
    eval (If x t e)  env = if eval x env then eval t env else eval e env
    eval (While b c) env = fix (\f => \o => if eval b env then f (eval c env o) else o)
        where
            uf : evalTy Comm -> evalTy Comm
            uf f o = if eval b env then f (eval c env o) else o
    
    
    -- /////////////// Ejemplos /////////////// 
    test : Expr Pi Comm
    test = NewVar (ValInt 2) (Assig (Var stop) (ValInt 3))
    -- /////////////// Ejemplos /////////////// 
    {-
main : IO ()
main = print (eval test (((::),0)::ENil) [])-}
