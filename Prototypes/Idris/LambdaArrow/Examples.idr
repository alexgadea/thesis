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

varI : {Pi:Ctx} -> Phrase Pi IntExp
varI = Var idI

varJ : {Pi:Ctx} -> Phrase Pi IntExp
varJ = Var idJ

varN : {Pi:Ctx} -> Phrase Pi IntExp
varN = Var idN

varBI : {Pi:Ctx} -> Phrase Pi BoolExp
varBI = Var idI

varBJ : {Pi:Ctx} -> Phrase Pi BoolExp
varBJ = Var idJ

id' : {Pi:Ctx} -> Phrase Pi (IntExp :-> IntExp)
id'= Lam {j=idJ} varI varI

add : {Pi:Ctx} -> Phrase Pi (IntExp :-> IntExp :-> IntExp)
add = Lam {j=idJ} varJ (Lam {j=idI} varI (BinOp (+) varJ varI))

andt : {Pi:Ctx} -> Phrase Pi (BoolExp :-> BoolExp :-> BoolExp)
andt = Lam {j=idJ} varBJ (Lam {j=idI} varBI (BinOp (&&) varBJ varBI))

add' : {Pi:Ctx} -> Phrase Pi IntExp
add' = App (App add (ValI 0)) (ValI 1)

and' : {Pi:Ctx} -> Phrase Pi BoolExp
and' = App (App andt (ValB True)) (ValB False)

fact : {Pi:Ctx} -> Phrase Pi (IntExp :-> IntExp)
fact = Lam {j=idN} varN 
            ({-If -} If (BinOp (==) varN (ValI 0)) 
                {-Then-} (ValI 1) 
                {-Else-} (BinOp (*) (App fact (BinOp (-) varN (ValI 1))) varN))
                
appFact : {Pi:Ctx} -> Phrase Pi IntExp
appFact = App fact $ ValI 1
