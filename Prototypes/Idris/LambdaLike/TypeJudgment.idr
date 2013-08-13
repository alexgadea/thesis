-- Módulo que representa los juicios de tipado del lenguaje.
module TypeJudgement

import Ctx
import Shp
import DataType
import PhraseType

-- Operador de punto fijo.
fix : (a -> a) -> a
fix f = f (fix f)

-- Representa el jucio de tipado para el subtipado.
data (<~) : PhraseType -> PhraseType -> Type where
    VarToAcc : BoolVar <~ BoolAcc
    VarToExp : BoolVar <~ BoolExp
    
    IntExpToRealExp : IntExp <~ RealExp
    RealAccToIntAcc : RealAcc <~ IntAcc
    
    Reflx : (t:PhraseType) -> t <~ t
    Trans : {t:PhraseType} -> {t':PhraseType} -> {t'':PhraseType} -> 
            t <~ t' -> t' <~ t'' -> t <~ t''
    
    SubsFun : {t0:PhraseType} -> {t0':PhraseType} -> 
              {t1:PhraseType} -> {t1':PhraseType} -> 
              t0 <~ t0' -> t1 <~ t1' -> (t0' :-> t1) <~ (t0 :-> t1')

-- Definimos la semántica para los juicios de subtipado del lenguaje.
evalLeq : t <~ t' -> (C:Shp) -> evalTyO t C -> evalTyO t' C
evalLeq VarToAcc c (a,e)    = a
evalLeq VarToExp c (a,e)    = e
evalLeq IntExpToRealExp c f = prim__intToFloat . f
evalLeq {t'=t} (Reflx t) c f = f
evalLeq (Trans leq leq') c f = evalLeq leq' c $ evalLeq leq c f
evalLeq (SubsFun leq leq') c f = \c' => evalLeq leq' (c ++ c') . (f c') . evalLeq leq (c ++ c')

-- Representa lo juicios de tipado del lenguaje.
using (Pi:Ctx,Theta:PhraseType,Theta':PhraseType)
    data TypeJudgment : Ctx -> PhraseType -> Type where
        Skip    : TypeJudgment Pi Comm
        Seq     : TypeJudgment Pi Comm -> TypeJudgment Pi Comm -> TypeJudgment Pi Comm
        While   : TypeJudgment Pi BoolExp -> TypeJudgment Pi Comm -> TypeJudgment Pi Comm
        If      : {pt :PhraseType} -> TypeJudgment Pi BoolExp -> 
                  TypeJudgment Pi pt -> TypeJudgment Pi pt -> TypeJudgment Pi pt
        
        I       : (i:Identifier) -> InCtx Pi i -> TypeJudgment Pi Theta
        Assig   : (d:DataType) -> TypeJudgment Pi (dtTOacc d) -> 
                  TypeJudgment Pi (dtTOexp d) -> TypeJudgment Pi Comm
        NewVar : (d:DataType) -> (i:Identifier) -> TypeJudgment Pi (dtTOexp d) -> 
                 (fi:Fresh Pi i) -> TypeJudgment (Prepend Pi i (dtTOvar d) fi) Comm -> 
                 TypeJudgment Pi Comm
        
        CInt    : Int   -> TypeJudgment Pi IntExp
        CFloat  : Float -> TypeJudgment Pi RealExp
        CBool   : Bool  -> TypeJudgment Pi BoolExp
        
        BinOp : {a : DataType} -> {b : DataType} -> {d : DataType} -> 
                (evalDTy a -> evalDTy b -> evalDTy d) -> 
                TypeJudgment Pi (dtTOexp a) -> TypeJudgment Pi (dtTOexp b) -> TypeJudgment Pi (dtTOexp d)
        UnOp  : {a:DataType} -> {b:DataType} -> 
                (evalDTy a -> evalDTy b) -> 
                TypeJudgment Pi (dtTOexp a)  -> TypeJudgment Pi (dtTOexp b) 

        Lam   : (i:Identifier) -> (pt:PhraseType) -> (fi:Fresh Pi i) ->
                TypeJudgment (Prepend Pi i pt fi) Theta' -> 
                TypeJudgment Pi (pt :-> Theta')
        App    : TypeJudgment Pi (Theta :-> Theta') -> TypeJudgment Pi Theta -> 
                 TypeJudgment Pi Theta'
        Rec    : TypeJudgment Pi (Theta :-> Theta) -> TypeJudgment Pi Theta
        
        Subs   : t <~ t' -> TypeJudgment Pi t -> TypeJudgment Pi t'

-- Semántica de los juicios de tipado del lenguaje.
-- [[\pi |-- e : \theta]]C : [[\pi]]*C -> [[\theta]]]C
eval : {Pi:Ctx} -> {Theta:PhraseType} ->
             TypeJudgment Pi Theta -> (C:Shp) -> evalCtxO Pi C -> evalTyO Theta C
eval (Subs leq var) c eta = evalLeq leq c (eval var c eta)
-- Semántica para los comandos.
eval (Assig d a e) c eta = \sigma => (\x => evalAcc x sigma) (evalExp sigma)
    where
        evalAcc : evalDTy d -> shapes c -> shapes c
        evalAcc = toAcc d $ eval a c eta
        evalExp : shapes c -> evalDTy d
        evalExp = toExp d $ eval e c eta
eval Skip c eta = \sigma => sigma
eval (Seq comm comm') c eta = \sigma => eval comm' c eta (eval comm c eta sigma)
eval (While b comm) c eta = fix (\f => \sigma => 
                                            if eval b c eta sigma 
                                                then f (eval comm c eta sigma)
                                                else sigma)
eval {Pi=p} {Theta=pt} (I i iIn) c eta = search c p i pt iIn eta
-- Semántica para los valores constantes.
eval (CInt i)   c eta = \sigma => i
eval (CFloat r) c eta = \sigma => r
eval (CBool b)  c eta = \sigma => b
eval (BinOp {a} {b} {d} op x y) c eta = fromExp d (\sigma => (op (z sigma) (z' sigma)))
    where z : shapes c -> evalDTy a
          z = toExp a $ eval x c eta
          z' : shapes c -> evalDTy b
          z' = toExp b $ eval y c eta
eval (UnOp {a} {b} op x) c eta = fromExp b (\sigma => op (z sigma))
    where
        z : shapes c -> evalDTy a
        z = toExp a $ eval x c eta
eval {Theta=(pt :-> t')} {Pi=p} (Lam i pt fi b) c eta = evalLambda
    where
        newLeta : (C':Shp) -> evalTyO pt (c ++ C') -> evalCtxO (Prepend p i pt fi) (c ++ C')
        newLeta c' z = update (c++c') p (liftEta' c c' p eta) i pt z fi
        
        evalLambda : (C':Shp) -> evalTyO pt (c ++ C') -> evalTyO t' (c ++ C')
        evalLambda c' z = eval b (c++c') (newLeta c' z)
eval (App e e') c eta = convR $ (eval e c eta ShpUnit) (convL $ eval e' c eta)
eval (Rec e) c eta = fix $ convR . (eval e c eta ShpUnit) . convL
eval {Theta=pt} (If {pt} b e e') c eta =
            case pt of
                --lpt :-> rpt => makeFun c (lpt :-> rpt)
                Comm        => makeComm Comm
                IntExp      => makeExp IntDT
                RealExp     => makeExp RealDT
                BoolExp     => makeExp BoolDT
                IntAcc      => makeAcc IntDT
                RealAcc     => makeAcc RealDT
                BoolAcc     => makeAcc BoolDT
    where
        makeComm : (pt:PhraseType) -> evalTyO pt c
        makeComm Comm = \sigma => if eval b c eta sigma
                                    then toComm (eval e c eta) sigma
                                    else toComm (eval e' c eta) sigma
        makeAcc : DataType -> evalTyO pt c
        makeAcc dt = fromAcc dt (\z => \sigma => if eval b c eta sigma
                                                    then toAcc dt (eval e c eta) z sigma
                                                    else toAcc dt (eval e' c eta) z sigma)
        makeExp : DataType -> evalTyO pt c
        makeExp dt = fromExp dt (\sigma => if eval b c eta sigma
                                                then toExp dt (eval e c eta) sigma
                                                else toExp dt (eval e' c eta) sigma)
        
--         makeFun : {cc:Shp} -> (fpt:PhraseType) -> evalTyO fpt cc
--         makeFun (lpt :-> Comm) = \c' => \z => 
--                                  (\sigma => if eval b c eta sigma
--                                                 then toComm (eval e c eta c' z) sigma
--                                                 else toComm (eval e' c eta c' z) sigma)
--         makeFun cc (lpt :-> RealExp) = \c' => makeExp (cc++c') (ptToDt lpt)
--         makeFun cc (lpt :-> BoolExp) = \c' => makeExp (cc++c') (ptToDt lpt)
--         makeFun cc (lpt :-> rpt) = (\c' => \sigma => makeFun (c++c') rpt)
eval {Pi=p} (NewVar d i vInit fi comm) c eta = 
        \sigma => head c shpDT (evalComm (prependShp {dt=d} sigma (evalInit sigma)))
    where
        shpDT : Shp
        shpDT = ShpUnit ~: d
        
        a : evalDTy d -> shapes (c ~: d) -> shapes (c ~: d)
        a = \x => \sigma' => prependShp (head c shpDT sigma') x
        e : shapes (c ~: d) -> evalDTy d
        e = last (c ~: d) d
        
        evalInit : shapes c -> evalDTy d
        evalInit = toExp d $ eval vInit c eta
        
        zvar : evalTyO (dtTOvar d) (c ~: d)
        zvar = fromVar d (a,e)
        
        newAeta : evalCtxO (Prepend p i (dtTOvar d) fi) (c ~: d)
        newAeta = update (c ~: d) p (liftEta c d p eta) i (dtTOvar d) zvar fi
        
        evalComm : evalTyO Comm (c ~: d)
        evalComm = eval comm (c ~: d) newAeta
