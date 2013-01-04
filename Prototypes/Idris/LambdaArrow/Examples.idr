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

varI : {Pi:Ctx} -> TypeJugdmnt Pi IntExp
varI = Var idI

varJ : {Pi:Ctx} -> TypeJugdmnt Pi IntExp
varJ = Var idJ

varN : {Pi:Ctx} -> TypeJugdmnt Pi IntExp
varN = Var idN

varBI : {Pi:Ctx} -> TypeJugdmnt Pi BoolExp
varBI = Var idI

varBJ : {Pi:Ctx} -> TypeJugdmnt Pi BoolExp
varBJ = Var idJ

id' : {Pi:Ctx} -> TypeJugdmnt Pi (IntExp :-> IntExp)
id'= Lam {j=idJ} varI varI

add : {Pi:Ctx} -> TypeJugdmnt Pi (IntExp :-> IntExp :-> IntExp)
add = Lam {j=idJ} varJ (Lam {j=idI} varI (BinOp (+) varJ varI))

andt : {Pi:Ctx} -> TypeJugdmnt Pi (BoolExp :-> BoolExp :-> BoolExp)
andt = Lam {j=idJ} varBJ (Lam {j=idI} varBI (BinOp (&&) varBJ varBI))

add' : {Pi:Ctx} -> TypeJugdmnt Pi IntExp
add' = App (App add (ValI 0)) (ValI 1)

and' : {Pi:Ctx} -> TypeJugdmnt Pi BoolExp
and' = App (App andt (ValB True)) (ValB False)

fact : {Pi:Ctx} -> TypeJugdmnt Pi (IntExp :-> IntExp)
fact = Lam {j=idN} varN 
            ({-If -} If (BinOp (==) varN (ValI 0)) 
                {-Then-} (ValI 1) 
                {-Else-} (BinOp (*) (App fact (BinOp (-) varN (ValI 1))) varN))

varN' : {Pi:Ctx} -> TypeJugdmnt Pi IntExp
varN' = BinOp (-) varN (ValI 1)

ifZero : {Pi:Ctx} -> TypeJugdmnt Pi IntExp
ifZero = If (BinOp (>=) varN (ValI 0))
            (ValI 0)
            (ValI 0)
                
recFact : {Pi:Ctx} -> TypeJugdmnt Pi IntExp
recFact =  Rec (Lam {j=idN} varN ifZero)

appFact : {Pi:Ctx} -> TypeJugdmnt Pi IntExp
appFact = App fact $ ValI 3
