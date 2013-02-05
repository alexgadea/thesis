module Examples

import Ctx
import PhraseType
import TypeJudgment

idI : Identifier
idI = Id "i"

idJ : Identifier
idJ = Id "j"

idN : Identifier
idN = Id "n"

idF : Identifier
idF = Id "f"

varI : {Pi:Ctx} -> TypeJugdmnt Pi IntExp
varI = I idI

varJ : {Pi:Ctx} -> TypeJugdmnt Pi IntExp
varJ = I idJ

varN : {Pi:Ctx} -> TypeJugdmnt Pi IntExp
varN = I idN

varBI : {Pi:Ctx} -> TypeJugdmnt Pi BoolExp
varBI = I idI

varBJ : {Pi:Ctx} -> TypeJugdmnt Pi BoolExp
varBJ = I idJ

id' : {Pi:Ctx} -> TypeJugdmnt Pi (IntExp :-> IntExp)
id'= Lam idI IntExp varI

add : {Pi:Ctx} -> TypeJugdmnt Pi (IntExp :-> IntExp :-> IntExp)
add = Lam idJ IntExp (Lam idI IntExp (BinOp (+) varJ varI))

andt : {Pi:Ctx} -> TypeJugdmnt Pi (BoolExp :-> BoolExp :-> BoolExp)
andt = Lam idJ BoolExp (Lam idI BoolExp (BinOp (&&) varBJ varBI))

add' : {Pi:Ctx} -> TypeJugdmnt Pi IntExp
add' = App (App add (ValI 0)) (ValI 1)

and' : {Pi:Ctx} -> TypeJugdmnt Pi BoolExp
and' = App (App andt (ValB True)) (ValB False)

fact : {Pi:Ctx} -> TypeJugdmnt Pi (IntExp :-> IntExp)
fact = Lam idN IntExp 
            ({-If -} If (BinOp (==) varN (ValI 0)) 
                {-Then-} (ValI 1) 
                {-Else-} (BinOp (*) (App fact (BinOp (-) varN (ValI 1))) varN))

varN' : {Pi:Ctx} -> TypeJugdmnt Pi IntExp
varN' = BinOp (-) varN (ValI 1)

valT : {Pi:Ctx} -> TypeJugdmnt Pi BoolExp 
valT = ValB True

ifZero : {Pi:Ctx} -> TypeJugdmnt (Pi<:(idN,IntExp)) IntExp
ifZero = If valT (ValI 0) (ValI 0)

appFact : {Pi:Ctx} -> TypeJugdmnt Pi IntExp
appFact = App fact $ ValI 3

eq : {a:PhraseType} -> evalTy a -> evalTy a -> evalTy BoolExp
eq {a=IntExp} i i' = i == i'
eq {a=RealExp} i i' = i == i'
eq {a=BoolExp} True False = False
eq {a=BoolExp} False True = False
eq {a=BoolExp} i i = True

prod : {a:PhraseType} -> evalTy a -> evalTy a -> evalTy IntExp
prod {a=IntExp} i i' = i * i'

recFact : TypeJugdmnt CtxUnit (IntExp :-> IntExp)
recFact = Rec (Lam idF (IntExp:->IntExp) 
                (Lam idN IntExp (If (BinOp (eq {a=IntExp}) (ValI 0) (I idN))
                                    (ValI 1) 
                                    (BinOp (prod {a=IntExp}) (I idN) (I idF))
                                )
                )
              )
