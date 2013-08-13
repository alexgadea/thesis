-- Módulo de ejemplos.
-- Tercer prototipo de un evaluador de un lenguaje funcional con imperativo
-- considerando shapes.
module Examples

import Ctx
import Shp
import DataType
import PhraseType
import TypeJudgment

syntax "\\" [x] ":" [pt] "=>" [b] "|" [fx] = Lam x pt fx b
syntax "rec" [e] =  Rec e
syntax [e] "@" [e'] = App e e'

syntax [x] "+" [y]     = BinOp {a=IntDT} {b=IntDT} {d=IntDT} (+) x y
syntax [x] "-" [y]     = BinOp {a=IntDT} {b=IntDT} {d=IntDT} (-) x y
syntax [x] "*" [y]     = BinOp {a=IntDT} {b=IntDT} {d=IntDT} (*) x y
syntax [x] "==" [y]    = BinOp {a=IntDT} {b=IntDT} {d=BoolDT} (==) x y
syntax [x] ".and." [y] = BinOp {a=BoolDT} {b=BoolDT} {d=BoolDT} (&&) x y

syntax "if" [b] "then" [e] "else" [e'] = If b e e'

syntax "while" [b] "do" [c] = While b c
syntax "new boolvar" [x] "<::" [vInit] "|" [fx] "in" [comm] = NewVar BoolDT x vInit fx comm
syntax "new intvar"  [x] "<::" [vInit] "|" [fx] "in" [comm] = NewVar IntDT x vInit fx comm
syntax "new realvar" [x] "<::" [vInit] "|" [fx] "in" [comm] = NewVar RealDT x vInit fx comm
syntax [x] ":=b" [v] = Assig BoolDT x v
syntax [x] ":=i" [v] = Assig IntDT x v
syntax [x] ":=r" [v] = Assig RealDT x v
syntax "skip" = Skip

idI : Identifier
idI = Id "i"

idJ : Identifier
idJ = Id "j"

freshI : Fresh CtxUnit idI
freshI = FUnit idI

ctxI : PhraseType -> Ctx
ctxI pt = Prepend CtxUnit idI pt freshI

freshIJ : (pti:PhraseType) -> Fresh (ctxI pti) idJ
freshIJ pti = FCons idJ pti idI CtxUnit (FUnit idI) oh (FUnit idJ)

ctxIJ : PhraseType -> PhraseType -> Ctx
ctxIJ pti ptj = Prepend (ctxI pti) idJ ptj (freshIJ pti)

testIfLam : TypeJudgment CtxUnit (BoolExp :-> IntExp)
testIfLam = \idI : BoolExp => (if varI then (CInt 1) else (CInt 2)) | freshI
    where
        varI : TypeJudgment (ctxI BoolExp) BoolExp
        varI = I idI (InHead CtxUnit idI BoolExp (FUnit idI))
        

id' : TypeJudgment CtxUnit (IntExp :-> IntExp)
--id' = Lam idI IntExp freshI varI
id' = \idI : IntExp => varI | freshI 
    where
        varI : TypeJudgment (ctxI IntExp) IntExp
        varI = I idI (InHead CtxUnit idI IntExp (FUnit idI))

add : TypeJudgment CtxUnit (IntExp :-> IntExp :-> IntExp)
--add = Lam idI IntExp freshI (Lam idJ IntExp freshIJ (BinOp (-) varI varJ))
add = \idI : IntExp => (\idJ : IntExp => (BinOp {d=IntDT} (+) varI varJ) | (freshIJ IntExp)) | freshI 
    where
        varI : TypeJudgment (ctxIJ IntExp IntExp) IntExp
        varI = I idI (InTail (ctxI IntExp) idI IntExp idJ (freshIJ IntExp) (InHead CtxUnit idI IntExp (FUnit idI)))
        varJ : TypeJudgment (ctxIJ IntExp IntExp) IntExp
        varJ = I idJ (InHead (ctxI IntExp) idJ IntExp (freshIJ IntExp))

ceroPluSone : TypeJudgment CtxUnit IntExp
ceroPluSone = (add @ (CInt 0)) @ (CInt 1)

andt : TypeJudgment CtxUnit (BoolExp :-> BoolExp :-> BoolExp)
andt = \idI : BoolExp => (\idJ : BoolExp => varI .and. varJ | (freshIJ BoolExp)) | freshI 
    where
        varI : TypeJudgment (ctxIJ BoolExp BoolExp) BoolExp
        varI = I idI (InTail (ctxI BoolExp) idI BoolExp idJ (freshIJ BoolExp) (InHead CtxUnit idI BoolExp (FUnit idI)))
        varJ : TypeJudgment (ctxIJ BoolExp BoolExp) BoolExp
        varJ = I idJ (InHead (ctxI BoolExp) idJ BoolExp (freshIJ BoolExp))

trueAnDfalse : TypeJudgment CtxUnit BoolExp
trueAnDfalse = (andt@(CBool True))@(CBool False)

recFact : TypeJudgment CtxUnit (IntExp :-> IntExp)
recFact = rec (\idI : IntExp :-> IntExp => 
                    (\idJ : IntExp => if (CInt 0) == varJ
                                        then CInt 1
                                        else varJ * (varI @ (varJ - (CInt 1)))
                    | (freshIJ intint)) 
                    | freshI
              )
    where
        intint : PhraseType
        intint = IntExp :-> IntExp
        varI : TypeJudgment (ctxIJ intint IntExp) (IntExp :-> IntExp)
        varI = I idI (InTail (ctxI intint) idI IntExp idJ (freshIJ intint) (InHead CtxUnit idI intint (FUnit idI)))
        varJ : TypeJudgment (ctxIJ intint IntExp) IntExp
        varJ = I idJ (InHead (ctxI intint) idJ IntExp (freshIJ intint))

testLamWhile : TypeJudgment CtxUnit (BoolExp :-> Comm)
testLamWhile = \idI : BoolExp => (while varI do skip) | freshI
    where
        varI : TypeJudgment (ctxI BoolExp) BoolExp
        varI = I idI (InHead CtxUnit idI BoolExp (FUnit idI))

testwhile: TypeJudgment CtxUnit Comm
testwhile = new boolvar idI <:: (CBool True) | freshI in
                (while (Subs VarToExp varI) do 
                    ((Subs VarToAcc varI) :=b (CBool False)) 
                )
    where
        varI : TypeJudgment (ctxI BoolVar) BoolVar
        varI = I idI (InHead CtxUnit idI BoolVar (FUnit idI))
