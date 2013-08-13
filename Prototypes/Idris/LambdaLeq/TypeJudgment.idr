-- Prototipo de evaluador para un lenguaje con tipos simples + subtipado.
module TypeJudgment

import Ctx
import PType

-- Operador de punto fijo.
fix : (a -> a) -> a
fix f = f (fix f)

infixr 10 <~

prim__boolToInt : Bool -> Int
prim__boolToInt True = 0
prim__boolToInt False = 1

-- Representa el jucio de tipado para el subtipado.
data (<~) : PType -> PType -> Type where
    IntExpToRealExp : IntExp  <~ RealExp
    BoolExpToIntExp : BoolExp <~ IntExp
    
    Reflx : (t:PType) -> t <~ t
    Trans : {t:PType} -> {t':PType} -> {t'':PType} -> 
            t <~ t' -> t' <~ t'' -> t <~ t''
            
    SubsFun : {t0:PType} -> {t0':PType} -> 
              {t1:PType} -> {t1':PType} -> 
              t0 <~ t0' -> t1 <~ t1' -> (t0' :-> t1) <~ (t0 :-> t1')

-- Definimos la semántica para los juicios de subtipado del lenguaje.
evalLeq : {t:PType} -> {t':PType} -> t <~ t' -> evalTy t -> evalTy t'
-- [[Int <~ Real]] = J, con J inyección de enteros en reales.
evalLeq IntExpToRealExp    = prim__intToFloat
-- [[Bool <~ Int]] = if True then 0 else 1.
evalLeq BoolExpToIntExp    = prim__boolToInt
-- [[theta <~ theta]] = id_[[Theta]]
evalLeq {t'=t} (Reflx t)   = id
-- [[theta <~ theta'']] = [[theta' <~ theta'']] . [[theta <~ theta']]
evalLeq (Trans leq leq')   = evalLeq leq' . evalLeq leq
-- [[theta0' :-> theta1 <~ theta0 <~ theta1']] = 
-- \f : [[theta0']] -> [[theta1]] => [[theta1 <~ theta1']] . f . [[theta0 <~ theta0']]
evalLeq (SubsFun leq leq') = \f => evalLeq leq' . f . evalLeq leq

using (Pi:Ctx, Theta:PType, Theta':PType)
    -- Este tipo representa un juicio de tipado
    -- pi : Vect PType n
    -- theta : PType
    -- pi |-- e : theta
    -- Donde e son las frases del lenguaje.
    data TypeJugdmnt : Ctx -> PType -> Type where
        I     : (i:Identifier) -> InCtx Pi i -> TypeJugdmnt Pi Theta
        CInt  : Int   -> TypeJugdmnt Pi IntExp
        CBool : Bool  -> TypeJugdmnt Pi BoolExp
        CReal : Float -> TypeJugdmnt Pi RealExp
        
        Lam   : (i:Identifier) -> (pt:PType) -> (fi:Fresh Pi i) ->
                TypeJugdmnt (Prepend Pi i pt fi) Theta' -> 
                TypeJugdmnt Pi (pt :-> Theta')
        App   : TypeJugdmnt Pi (Theta :-> Theta') -> TypeJugdmnt Pi Theta -> 
                TypeJugdmnt Pi Theta'
        Rec   : TypeJugdmnt Pi (Theta :-> Theta) -> TypeJugdmnt Pi Theta
        
        If    : TypeJugdmnt Pi BoolExp -> TypeJugdmnt Pi Theta -> 
                TypeJugdmnt Pi Theta -> TypeJugdmnt Pi Theta
        BinOp : (evalTy a -> evalTy b -> evalTy c) -> 
                TypeJugdmnt Pi a -> TypeJugdmnt Pi b -> TypeJugdmnt Pi c
        UnOp  : (evalTy a -> evalTy b) -> TypeJugdmnt Pi a -> TypeJugdmnt Pi b
        
        Subs    : Theta <~ Theta' -> TypeJugdmnt Pi Theta -> TypeJugdmnt Pi Theta'

-- Definimos la semántica para los juicios de tipado del lenguaje.
eval : {Pi:Ctx} -> {Theta:PType} ->
       TypeJugdmnt Pi Theta -> evalCtx Pi -> evalTy Theta
-- [[Pi |--  : theta]] eta = eta i
eval (Subs leq p) eta = evalLeq leq $ eval p eta
-- [[Pi |-- Var i : theta]] eta = eta i
eval {Pi=p} {Theta=pt} (I i iIn) eta = search p i pt iIn eta
-- [[Pi |-- CInt x : IntExp]] eta = x
eval (CInt x)    eta = x
-- [[Pi |-- CBool x : IntExp]] eta = x
eval (CBool x)    eta = x
-- [[Pi |-- CReal x : IntExp]] eta = x
eval (CReal x)    eta = x
-- [[Pi |-- \-> b : theta :-> theta']] eta = \z -> [[Pi,z:theta |-- b : theta']] (eta|z)
eval {Pi=p} (Lam i pt fi b) eta = \z => eval b (update p eta i pt z fi)
-- [[Pi |-- ee' : theta']]eta = ([[Pi |-- e: theta :-> theta']] eta) ([[Pi |-- e:theta]] eta)
eval (App e e')   eta = (eval e eta) (eval e' eta)
-- [[Pi |-- rec e : theta]]eta = Y_[[theta]] ([[Pi |-- e : theta -> theta]] eta)
eval (Rec e) eta = fix (eval e eta)
-- [[Pi |-- if b then e else e' : theta]] eta = 
--                  if [[Pi |-- b : BoolExp]] eta 
--                     then [[Pi |-- e:theta]] eta 
--                     else [[Pi |-- e':theta]] eta 
eval (If b e e')  eta = if eval b eta then eval e eta else eval e' eta
-- [[Pi |-- x op y : theta'']] eta = [[Pi |-- x:theta]] eta op [[Pi |-- y:theta']] eta
-- con op : theta -> theta' -> theta''.
eval (BinOp op x y) eta = op (eval x eta) (eval y eta)
-- [[Pi |-- op x : theta']]eta = op [[Pi |-- x:theta]] eta
-- con op : theta -> theta'.
eval (UnOp op x) eta = op (eval x eta)
