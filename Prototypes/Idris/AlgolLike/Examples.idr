-- Módulo de ejemplos.
-- Tercer prototipo de un evaluador de un lenguaje funcional con imperativo
-- considerando shapes.
module Eval

import Ctx
import Shp
import DataType
import PhraseType
import TypeJudgment

idX : Identifier
idX = Id "x"

val1 : Phrase ((idX,IntVar) :> CtxUnit) IntExp
val1 = CInt 1

val2 : Phrase CtxUnit IntExp
val2 = CInt 2

val3 : Phrase ((idX,IntVar) :> CtxUnit) IntExp
val3 = CInt 3

valT : Phrase CtxUnit BoolExp
valT = CBool True

valF : Phrase ((idX,BoolVar) :> CtxUnit) BoolExp
valF = CBool True

-- test : Phrase CtxUnit Comm
-- test = NewIntVar {j=idX} (Var idX) val2 Skip

-- sumOne : Phrase ((idX,IntVar) :> CtxUnit) IntExp
-- sumOne = BinOp IPlus (Subs VarToExp $ Var idX) val1

assig : Phrase ((idX,BoolVar) :> CtxUnit) Comm
assig = Assig (Subs VarToAcc $ Var idX) valF

while : Phrase ((idX,BoolVar) :> CtxUnit) Comm
while = While (Subs VarToExp $ Var idX) assig

while' : Phrase CtxUnit Comm
while' = While (CBool True) Skip

test2 : Phrase CtxUnit Comm
test2 = NewBoolVar {j=idX} (Var idX) valT while

-- test3 : Phrase ((idX,IntExp):>CtxUnit) IntExp
-- test3 = App (Lam (Var idX) val2) val3
