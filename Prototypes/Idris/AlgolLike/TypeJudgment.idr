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

-- Representa las frases del lenguaje.
using (Pi:Ctx,Theta:PhraseType,Theta':PhraseType)
    data Phrase : Ctx -> PhraseType -> Type where
        Skip    : Phrase Pi Comm
        Seq     : Phrase Pi Comm -> Phrase Pi Comm -> Phrase Pi Comm
        While   : Phrase Pi BoolExp -> Phrase Pi Comm -> Phrase Pi Comm
        If      : {pt :PhraseType} -> Phrase Pi BoolExp -> 
                  Phrase Pi pt -> Phrase Pi pt -> Phrase Pi pt
        
        I       : (i:Identifier) -> InCtx Pi i -> Phrase Pi Theta
        Assig   : (d:DataType) -> Phrase Pi (dtTOacc d) -> 
                  Phrase Pi (dtTOexp d) -> Phrase Pi Comm
        NewVar : (d:DataType) -> (i:Identifier) -> Phrase Pi (dtTOexp d) -> 
                 (fi:Fresh Pi i) -> Phrase (Prepend Pi i (dtTOvar d) fi) Comm -> 
                 Phrase Pi Comm
        
        CInt    : Int   -> Phrase Pi IntExp
        CFloat  : Float -> Phrase Pi RealExp
        CBool   : Bool  -> Phrase Pi BoolExp
        
        BinOp : {a : DataType} -> {b : DataType} -> {d : DataType} -> 
                (evalDTy a -> evalDTy b -> evalDTy d) -> 
                Phrase Pi (dtTOexp a) -> Phrase Pi (dtTOexp b) -> Phrase Pi (dtTOexp d)
        UnOp  : {a:DataType} -> {b:DataType} -> 
                (evalDTy a -> evalDTy b) -> 
                Phrase Pi (dtTOexp a)  -> Phrase Pi (dtTOexp b) 

        Lam   : (i:Identifier) -> (pt:PhraseType) -> (fi:Fresh Pi i) ->
                Phrase (Prepend Pi i pt fi) Theta' -> 
                Phrase Pi (pt :-> Theta')
        App    : Phrase Pi (Theta :-> Theta') -> Phrase Pi Theta -> 
                 Phrase Pi Theta'
        Rec    : Phrase Pi (Theta :-> Theta) -> Phrase Pi Theta
        
        Subs   : t <~ t' -> Phrase Pi t -> Phrase Pi t'

-- Semántica de las frases del lenguaje.
-- [[\pi |-- e : \theta]]C : [[\pi]]*C -> [[\theta]]]C
evalPhrase : {Pi:Ctx} -> {Theta:PhraseType} ->
             Phrase Pi Theta -> (C:Shp) -> evalCtxO Pi C -> evalTyO Theta C
evalPhrase (Subs leq var) c eta = evalLeq leq c (evalPhrase var c eta)
-- Semántica para los comandos.
evalPhrase (Assig d a e) c eta = \sigma => (\x => evalAcc x sigma) (evalExp sigma)
    where
        evalAcc : evalDTy d -> shapes c -> shapes c
        evalAcc = toAcc d $ evalPhrase a c eta
        evalExp : shapes c -> evalDTy d
        evalExp = toExp d $ evalPhrase e c eta
evalPhrase Skip c eta = \sigma => sigma
evalPhrase (Seq comm comm') c eta = \sigma => evalPhrase comm' c eta (evalPhrase comm c eta sigma)
evalPhrase (While b comm) c eta = fix (\f => \sigma => 
                                            if evalPhrase b c eta sigma 
                                                then f (evalPhrase comm c eta sigma)
                                                else sigma)
evalPhrase {Pi=p} {Theta=pt} (I i iIn) c eta = search c p i pt iIn eta
-- Semántica para los valores constantes.
evalPhrase (CInt i)   c eta = \sigma => i
evalPhrase (CFloat r) c eta = \sigma => r
evalPhrase (CBool b)  c eta = \sigma => b
evalPhrase (BinOp {a} {b} {d} op x y) c eta = fromExp d (\sigma => (op (z sigma) (z' sigma)))
    where z : shapes c -> evalDTy a
          z = toExp a $ evalPhrase x c eta
          z' : shapes c -> evalDTy b
          z' = toExp b $ evalPhrase y c eta
evalPhrase (UnOp {a} {b} op x) c eta = fromExp b (\sigma => op (z sigma))
    where
        z : shapes c -> evalDTy a
        z = toExp a $ evalPhrase x c eta
evalPhrase {Theta=(pt :-> t')} {Pi=p} (Lam i pt fi b) c eta = evalLambda
    where
        newLeta : (C':Shp) -> evalTyO pt (c ++ C') -> evalCtxO (Prepend p i pt fi) (c ++ C')
        newLeta c' z = update (c++c') p (liftEta' c c' p eta) i pt z fi
        
        evalLambda : (C':Shp) -> evalTyO pt (c ++ C') -> evalTyO t' (c ++ C')
        evalLambda c' z = evalPhrase b (c++c') (newLeta c' z)
evalPhrase (App e e') c eta = convR $ (evalPhrase e c eta ShpUnit) (convL $ evalPhrase e' c eta)
evalPhrase (Rec e) c eta = fix $ convR . (evalPhrase e c eta ShpUnit) . convL
evalPhrase {Theta=pt} (If {pt} b e e') c eta =
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
        makeComm Comm = \sigma => if evalPhrase b c eta sigma
                                    then toComm (evalPhrase e c eta) sigma
                                    else toComm (evalPhrase e' c eta) sigma
        makeAcc : DataType -> evalTyO pt c
        makeAcc dt = fromAcc dt (\z => \sigma => if evalPhrase b c eta sigma
                                                    then toAcc dt (evalPhrase e c eta) z sigma
                                                    else toAcc dt (evalPhrase e' c eta) z sigma)
        makeExp : DataType -> evalTyO pt c
        makeExp dt = fromExp dt (\sigma => if evalPhrase b c eta sigma
                                                then toExp dt (evalPhrase e c eta) sigma
                                                else toExp dt (evalPhrase e' c eta) sigma)
        
--         makeFun : {cc:Shp} -> (fpt:PhraseType) -> evalTyO fpt cc
--         makeFun (lpt :-> Comm) = \c' => \z => 
--                                  (\sigma => if evalPhrase b c eta sigma
--                                                 then toComm (evalPhrase e c eta c' z) sigma
--                                                 else toComm (evalPhrase e' c eta c' z) sigma)
--         makeFun cc (lpt :-> RealExp) = \c' => makeExp (cc++c') (ptToDt lpt)
--         makeFun cc (lpt :-> BoolExp) = \c' => makeExp (cc++c') (ptToDt lpt)
--         makeFun cc (lpt :-> rpt) = (\c' => \sigma => makeFun (c++c') rpt)
evalPhrase {Pi=p} (NewVar d i vInit fi comm) c eta = 
        \sigma => head c shpDT (evalComm (prependShp {dt=d} sigma (evalInit sigma)))
    where
        shpDT : Shp
        shpDT = ShpUnit ~: d
        
        a : evalDTy d -> shapes (c ~: d) -> shapes (c ~: d)
        a = \x => \sigma' => prependShp (head c shpDT sigma') x
        e : shapes (c ~: d) -> evalDTy d
        e = last (c ~: d) d
        
        evalInit : shapes c -> evalDTy d
        evalInit = toExp d $ evalPhrase vInit c eta
        
        zvar : evalTyO (dtTOvar d) (c ~: d)
        zvar = fromVar d (a,e)
        
        newAeta : evalCtxO (Prepend p i (dtTOvar d) fi) (c ~: d)
        newAeta = update (c ~: d) p (liftEta c d p eta) i (dtTOvar d) zvar fi
        
        evalComm : evalTyO Comm (c ~: d)
        evalComm = evalPhrase comm (c ~: d) newAeta
