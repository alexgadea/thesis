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
    data TypeJugdmnt : Ctx -> PhraseType -> Set where
        Var   : Identifier -> TypeJugdmnt Pi Theta
        ValI  : Int   -> TypeJugdmnt Pi IntExp
        ValB  : Bool  -> TypeJugdmnt Pi BoolExp
        ValR  : Float -> TypeJugdmnt Pi RealExp
        
        Lam   : {j:Identifier} -> TypeJugdmnt Pi Theta -> 
                 TypeJugdmnt (Pi <: (j,Theta)) Theta' -> TypeJugdmnt Pi (Theta :-> Theta')
        App   : TypeJugdmnt Pi (theta :-> theta') -> TypeJugdmnt Pi theta -> TypeJugdmnt Pi theta'
        Rec   : TypeJugdmnt Pi (theta :-> theta) -> TypeJugdmnt Pi theta
        
        If    : TypeJugdmnt Pi BoolExp -> TypeJugdmnt Pi theta -> TypeJugdmnt Pi theta -> TypeJugdmnt Pi theta
        BinOp : (evalTy a -> evalTy b -> evalTy c) -> TypeJugdmnt Pi a -> TypeJugdmnt Pi b -> TypeJugdmnt Pi c
        UnOp  : (evalTy a -> evalTy b) -> TypeJugdmnt Pi a -> TypeJugdmnt Pi b
    
-- Definimos la semántica para los juicios de tipado del lenguaje.
eval : {Pi:Ctx} -> {Theta:PhraseType} ->
       TypeJugdmnt Pi Theta -> evalCtx Pi -> evalTy Theta
-- [[Pi |-- Var i : theta]]eta = eta i
eval (Var i)     eta = search i eta
-- [[Pi |-- ValI x : IntExp]]eta = x
eval (ValI x)    eta = x
-- [[Pi |-- ValB x : IntExp]]eta = x
eval (ValB x)    eta = x
-- [[Pi |-- ValR x : IntExp]]eta = x
eval (ValR x)    eta = x
-- [[Pi |-- \-> b : theta :-> theta']]eta = \x -> [[Pi,x:theta |-- b : theta']](x|eta)
eval (Lam {j=i} (Var i) b) eta = \z => eval b (prependCtx eta i z)
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
-- [[Pi |-- rec e : theta]]eta = Y_[[theta]] ([[Pi |-- e : theta -> theta]]eta)
eval (Rec e) eta = fix (eval e eta)