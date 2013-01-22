-- Módulo que representa los juicios de tipado del lenguaje.
module TypeJudgement

import Ctx
import Shp
import DataType
import PhraseType

-- Operador de punto fijo.
fix : (a -> a) -> a
fix f = f (fix f)

-- Representa los nombres de operadores binarios.
data BOp : PhraseType -> PhraseType -> PhraseType -> Set where
    IPlus  : BOp IntExp IntExp IntExp
    ISubs  : BOp IntExp IntExp IntExp
    ITimes : BOp IntExp IntExp IntExp
    
    RPlus  : BOp RealExp RealExp RealExp
    RSubs  : BOp RealExp RealExp RealExp
    RTimes : BOp RealExp RealExp RealExp
    
    Div    : BOp IntExp IntExp IntExp
    Rem    : BOp IntExp IntExp IntExp
    RDiv   : BOp RealExp RealExp RealExp
    
    Equal  : {a:PhraseType} -> BOp a a BoolExp
    NEqual : {a:PhraseType} -> BOp a a BoolExp
    Lt     : BOp RealExp RealExp BoolExp
    LtEq   : BOp RealExp RealExp BoolExp
    Gt     : BOp RealExp RealExp BoolExp
    GtEq   : BOp RealExp RealExp BoolExp
    
    And    : BOp BoolExp BoolExp BoolExp
    Or     : BOp BoolExp BoolExp BoolExp
    Impl   : BOp BoolExp BoolExp BoolExp
    Iff    : BOp BoolExp BoolExp BoolExp
    
-- Representa los nombres de operadores unarios.
data UOp : PhraseType -> PhraseType -> Set where
    RNeg : UOp RealExp RealExp
    INeg : UOp IntExp IntExp
    Not  : UOp BoolExp BoolExp

-- Representa el jucio de tipado para el subtipado.
data (<~) : PhraseType -> PhraseType -> Set where
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

dtToAcc : DataType -> PhraseType
dtToAcc IntDT = IntAcc
dtToAcc BoolDT = BoolAcc
dtToAcc RealDT = RealAcc

dtToExp : DataType -> PhraseType
dtToExp IntDT = IntExp
dtToExp BoolDT = BoolExp
dtToExp RealDT = RealExp

-- Representa las frases del lenguaje.
using (Pi:Ctx,Theta:PhraseType,Theta':PhraseType)
    data Phrase : Ctx -> PhraseType -> Set where
        Skip      : Phrase Pi Comm
        Seq       : Phrase Pi Comm -> Phrase Pi Comm -> Phrase Pi Comm
        While     : Phrase Pi BoolExp -> Phrase Pi Comm -> Phrase Pi Comm
        If        : Phrase Pi BoolExp -> Phrase Pi Theta -> Phrase Pi Theta -> 
                    Phrase Pi Theta
        
        Var       : Identifier -> Phrase Pi Theta
        Assig     : Phrase Pi BoolAcc -> Phrase Pi BoolExp -> Phrase Pi Comm
        NewBoolVar : {j:Identifier} -> Phrase Pi BoolVar -> Phrase Pi BoolExp -> 
                    Phrase (Pi<:(j,BoolVar)) Comm -> Phrase Pi Comm
        
        CInt    : Int   -> Phrase Pi IntExp
        CFloat  : Float -> Phrase Pi RealExp
        CBool   : Bool  -> Phrase Pi BoolExp
        
        BinOp : BOp a b c -> Phrase Pi a -> Phrase Pi b -> Phrase Pi c
        UnOp  : UOp a b -> Phrase Pi a -> Phrase Pi b

        Lam    : {j:Identifier} -> Phrase Pi Theta -> 
                 Phrase (Pi <: (j,Theta)) Theta' -> Phrase Pi (Theta :-> Theta')
        App    : Phrase Pi (Theta :-> Theta') -> Phrase Pi Theta -> 
                 Phrase Pi Theta'
        
        Subs   : t <~ t' -> Phrase Pi t -> Phrase Pi t'

-- Semántica de las frases del lenguaje.
-- [[\pi |-- e : \theta]]C : [[\pi]]*C -> [[\theta]]]C
evalPhrase : {Pi:Ctx} -> {Theta:PhraseType} ->
             Phrase Pi Theta -> (C:Shp) -> evalCtxO Pi C -> evalTyO Theta C
evalPhrase (Subs leq var) c eta = evalLeq leq c (evalPhrase var c eta)
-- Semántica para los comandos.
evalPhrase (Assig a e) c eta = \sigma => ((\x => (evalPhrase a c eta) x sigma) (evalPhrase e c eta sigma))
evalPhrase Skip c eta = \sigma => sigma
evalPhrase (Seq comm comm') c eta = \sigma => evalPhrase comm' c eta (evalPhrase comm c eta sigma)
evalPhrase (While b comm) c eta = fix (\f => \sigma => 
                                            if evalPhrase b c eta sigma 
                                                then evalPhrase comm c eta sigma 
                                                else sigma)
evalPhrase (Var i) c eta = search i eta
-- Semántica para los valores constantes.
evalPhrase (CInt i) c eta = \sigma => i
evalPhrase (CFloat r) c eta = \sigma => r
evalPhrase (CBool b) c eta = \sigma => b
--evalPhrase (BinOp IPlus x y) c eta = \sigma => ((evalPhrase x c eta sigma) + (evalPhrase y c eta sigma))
--evalPhrase (UnOp Not x) s eta = \sigma => not (evalPhrase x s eta sigma)
evalPhrase {Theta=(t :-> t')} {Pi=pi} (Lam {j=i} (Var i) b) c eta = evalLambda
    where
        newLeta : (C':Shp) -> evalTyO t (c ++ C') -> evalCtxO (pi <: (i,t)) (c ++ C')
        newLeta c' z = prependCtx t (liftEta' c c' pi eta) i z
        evalLambda : (C':Shp) -> evalTyO t (c ++ C') -> evalTyO t' (c ++ C')
        evalLambda c' z = evalPhrase b (c++c') (newLeta c' z)

evalPhrase (App e e') c eta = convR $ (evalPhrase e c eta ShpUnit) (convL $ evalPhrase e' c eta)
evalPhrase {Theta=Comm} (If b e e') c eta = \sigma => 
                                            if evalPhrase b c eta sigma 
                                                then evalPhrase e c eta sigma 
                                                else evalPhrase e' c eta sigma
evalPhrase {Pi=pi} (NewBoolVar (Var i) vInit comm) c eta = 
        \sigma => head c intdt (evalComm (prependShp sigma (evalInit sigma)))
    where
        intdt : Shp
        intdt = BoolDT :~ ShpUnit
        
        a : evalTyO BoolAcc (c ~: BoolDT)
        a = \x => \sigma' => prependShp (head c intdt sigma') x
        e : evalTyO BoolExp (c ~: BoolDT)
        e = last (c ~: BoolDT) BoolDT
        
        evalInit : evalTyO BoolExp c
        evalInit sigma = evalPhrase vInit c eta sigma
        
        newAeta : {j:Identifier} -> evalCtxO (pi <: (j,BoolVar)) (c ~: BoolDT)
        newAeta {j=i} = prependCtx BoolVar (liftEta c BoolDT pi eta) i (a,e)
        evalComm : evalTyO Comm (c ~: BoolDT)
        evalComm = evalPhrase comm (c ~: BoolDT) newAeta
