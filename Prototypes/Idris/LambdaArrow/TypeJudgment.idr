-- Primer prototipo de evaluador para un lenguaje con tipos simples.
module TypeJudgment

import Ctx
import PhraseType

-- Operador de punto fijo.
fix : (a -> a) -> a
fix f = f (fix f)

using (Pi:Ctx, Theta:PhraseType, Theta':PhraseType)
    -- Este tipo representa un juicio de tipado
    -- pi : Vect PhraseType n
    -- theta : PhraseType
    -- pi |-- e : theta
    -- Donde e son las frases del lenguaje.
    data Phrase : Ctx -> PhraseType -> Set where
        Var   : Identifier -> Phrase Pi Theta
        ValI  : Int   -> Phrase Pi IntExp
        ValB  : Bool  -> Phrase Pi BoolExp
        ValR  : Float -> Phrase Pi RealExp
        
        Lam   : {j:Identifier} -> Phrase Pi Theta -> 
                 Phrase (Pi <: (j,Theta)) Theta' -> Phrase Pi (Theta :-> Theta')
        
        App   : Phrase Pi (theta :-> theta') -> Phrase Pi theta -> Phrase Pi theta'
        If    : Phrase Pi BoolExp -> Phrase Pi theta -> Phrase Pi theta -> Phrase Pi theta
        BinOp : (evalTy a -> evalTy b -> evalTy c) -> Phrase Pi a -> Phrase Pi b -> Phrase Pi c
        UnOp  : (evalTy a -> evalTy b) -> Phrase Pi a -> Phrase Pi b
    
-- Definimos la semántica para los juicios de tipado del lenguaje.
eval : {Pi:Ctx} -> {Theta:PhraseType} ->
       Phrase Pi Theta -> evalCtx Pi -> evalTy Theta
-- [[Pi |-- Var i : theta]]eta = eta i
eval (Var i)     eta = search i eta
-- [[Pi |-- ValI x : IntExp]]eta = x
eval (ValI x)    eta = x
-- [[Pi |-- ValB x : IntExp]]eta = x
eval (ValB x)    eta = x
-- [[Pi |-- ValR x : IntExp]]eta = x
eval (ValR x)    eta = x
-- [[Pi |-- \-> b : theta :-> theta']]eta = \x -> [[Pi,x:theta |-- b : theta']](x|eta)
eval {Theta=(t :-> t')} (Lam {j=i} (Var i) b) eta = \z => eval b (prependCtx t eta i z)
-- [[Pi |-- ee' : theta']]eta = ([[Pi |-- e: theta :-> theta']]eta)([[Pi |-- e:theta]]eta)
eval (App e e')   eta = (eval e eta) (eval e' eta)
-- [[Pi |-- x op y : theta]]eta = [[Pi |-- x:theta]]eta op [[Pi |-- y:theta]]eta
-- con op : theta -> theta -> theta.
eval (BinOp op x y) eta = op (eval x eta) (eval y eta)
-- [[Pi |-- op x : theta]]eta = op [[Pi |-- x:theta]]eta
-- con op : theta -> theta.
eval (UnOp op x) eta = op (eval x eta)
-- [[Pi |-- if b then e else e' : theta]]eta = 
--                  if [[Pi |-- b : BoolExp]]eta 
--                     then [[Pi |-- e:theta]]eta 
--                     else [[Pi |-- e':theta]]eta 
eval (If b e e')  eta = if eval b eta then eval e eta else eval e' eta
