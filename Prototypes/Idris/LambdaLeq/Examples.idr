module Examples

import Ctx
import PType
import TypeJudgment

eq : {a:PType} -> evalTy a -> evalTy a -> evalTy BoolExp
eq {a=IntExp} i i' = i == i'
eq {a=RealExp} i i' = i == i'
eq {a=BoolExp} True False = False
eq {a=BoolExp} False True = False
eq {a=BoolExp} i i = True

syntax "\\" [x] ":" [pt] "=>" [b] "|" [fx] = Lam x pt fx b
syntax "rec" [e] =  Rec e
syntax [e] "@" [e'] = App e e'

syntax [x] "+" [y]  = BinOp (+) x y
syntax [x] "-" [y]  = BinOp (-) x y
syntax [x] "*" [y]  = BinOp (*) x y
syntax [x] "==" [y] = BinOp eq x y
syntax [x] ".and." [y] = BinOp (&&) x y

syntax "if" [b] "then" [e] "else" [e'] = If b e e'

idI : Identifier
idI = Id "i"

idJ : Identifier
idJ = Id "j"

freshI : Fresh CtxUnit idI
freshI = FUnit idI

ctxI : PType -> Ctx
ctxI pt = Prepend CtxUnit idI pt freshI

freshIJ : (pti:PType) -> Fresh (ctxI pti) idJ
freshIJ pti = FCons idJ pti idI CtxUnit (FUnit idI) oh (FUnit idJ)

ctxIJ : PType -> PType -> Ctx
ctxIJ pti ptj = Prepend (ctxI pti) idJ ptj (freshIJ pti)

id' : TypeJugdmnt CtxUnit (IntExp :-> IntExp)
--id' = Lam idI IntExp freshI varI
id' = \idI : IntExp => varI | freshI 
    where
        varI : TypeJugdmnt (ctxI IntExp) IntExp
        varI = I idI (InHead CtxUnit idI IntExp (FUnit idI))

add : TypeJugdmnt CtxUnit (IntExp :-> IntExp :-> IntExp)
--add = Lam idI IntExp freshI (Lam idJ IntExp freshIJ (BinOp (-) varI varJ))
add = \idI : IntExp => (\idJ : IntExp => varI + varJ | (freshIJ IntExp)) | freshI 
    where
        varI : TypeJugdmnt (ctxIJ IntExp IntExp) IntExp
        varI = I idI (InTail (ctxI IntExp) idI IntExp idJ (freshIJ IntExp) (InHead CtxUnit idI IntExp (FUnit idI)))
        varJ : TypeJugdmnt (ctxIJ IntExp IntExp) IntExp
        varJ = I idJ (InHead (ctxI IntExp) idJ IntExp (freshIJ IntExp))

addReal : TypeJugdmnt CtxUnit (RealExp :-> RealExp :-> RealExp)
--addReal = Lam idI IntExp freshI (Lam idJ IntExp freshIJ (BinOp (+) varI varJ))
addReal = \idI : RealExp => (\idJ : RealExp => varI + varJ | (freshIJ RealExp)) | freshI 
    where
        varI : TypeJugdmnt (ctxIJ RealExp RealExp) RealExp
        varI = I idI (InTail (ctxI RealExp) idI RealExp idJ (freshIJ RealExp) (InHead CtxUnit idI RealExp (FUnit idI)))
        varJ : TypeJugdmnt (ctxIJ RealExp RealExp) RealExp
        varJ = I idJ (InHead (ctxI RealExp) idJ RealExp (freshIJ RealExp))

ceroPluSone' : TypeJugdmnt CtxUnit IntExp
ceroPluSone' = (add @ e) @ e'
    where
        e : TypeJugdmnt CtxUnit IntExp
        e = Subs (Reflx IntExp) (CInt 0)
        e' : TypeJugdmnt CtxUnit IntExp
        e' = Subs (Reflx IntExp) (CInt 1)

ceroPluSone : TypeJugdmnt CtxUnit RealExp
ceroPluSone = (addReal @ e) @ e'
    where
        e : TypeJugdmnt CtxUnit RealExp
        e = Subs IntExpToRealExp (CInt 0)
        e' : TypeJugdmnt CtxUnit RealExp
        e' = Subs IntExpToRealExp (CInt 1)

andt : TypeJugdmnt CtxUnit (BoolExp :-> BoolExp :-> BoolExp)
andt = \idI : BoolExp => (\idJ : BoolExp => varI .and. varJ | (freshIJ BoolExp)) | freshI 
    where
        varI : TypeJugdmnt (ctxIJ BoolExp BoolExp) BoolExp
        varI = I idI (InTail (ctxI BoolExp) idI BoolExp idJ (freshIJ BoolExp) (InHead CtxUnit idI BoolExp (FUnit idI)))
        varJ : TypeJugdmnt (ctxIJ BoolExp BoolExp) BoolExp
        varJ = I idJ (InHead (ctxI BoolExp) idJ BoolExp (freshIJ BoolExp))

trueAnDfalse : TypeJugdmnt CtxUnit BoolExp
trueAnDfalse = (andt@(CBool True))@(CBool False)

trueAnDfalse' : TypeJugdmnt CtxUnit RealExp
trueAnDfalse' = (addReal @ e) @ e'
    where
        e : TypeJugdmnt CtxUnit RealExp
        e = Subs (Trans BoolExpToIntExp IntExpToRealExp) (CBool False)
        e' : TypeJugdmnt CtxUnit RealExp
        e' = Subs (Trans BoolExpToIntExp IntExpToRealExp) (CBool True)

recFact : TypeJugdmnt CtxUnit (IntExp :-> IntExp)
recFact = rec (\idI : IntExp :-> IntExp => 
                    (\idJ : IntExp => if (CInt 0) == varJ
                                        then CInt 1
                                        else varJ * (varI @ (varJ - (CInt 1)))
                    | (freshIJ intint)) 
                    | freshI
              )
    where
        intint : PType
        intint = IntExp :-> IntExp
        varI : TypeJugdmnt (ctxIJ intint IntExp) (IntExp :-> IntExp)
        varI = I idI (InTail (ctxI intint) idI IntExp idJ (freshIJ intint) (InHead CtxUnit idI intint (FUnit idI)))
        varJ : TypeJugdmnt (ctxIJ intint IntExp) IntExp
        varJ = I idJ (InHead (ctxI intint) idJ IntExp (freshIJ intint))
