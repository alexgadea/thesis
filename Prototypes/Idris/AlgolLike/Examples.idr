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

idN : Identifier
idN = Id "n"

idF : Identifier
idF = Id "f"

val1 : Phrase ((idX,IntVar) :> CtxUnit) IntExp
val1 = CInt 1

val2 : Phrase CtxUnit IntExp
val2 = CInt 2

val3 : Phrase ((idX,IntVar) :> CtxUnit) IntExp
val3 = CInt 3

valT : Phrase CtxUnit BoolExp
valT = CBool True

valF : Phrase ((idX,BoolVar) :> CtxUnit) BoolExp
valF = CBool False

-- test : Phrase CtxUnit Comm
-- test = NewIntVar {j=idX} (Var idX) val2 Skip

-- sumOne : Phrase ((idX,IntVar) :> CtxUnit) IntExp
-- sumOne = BinOp IPlus (Subs VarToExp $ Var idX) val1

assig : Phrase ((idX,BoolVar) :> CtxUnit) Comm
assig = Assig (Subs VarToAcc $ I idX) valF

-- evalPhrase while (BoolDT :~ ShpUnit) ((idX,(\x => \s => s,\s => False)),()) (False,())
while : Phrase ((idX,BoolVar) :> CtxUnit) Comm
while = While (Subs VarToExp $ I idX) Skip

while' : Phrase CtxUnit Comm
while' = While (CBool False) Skip

test2 : Phrase CtxUnit Comm
test2 = NewBoolVar idX valT while

test3 : Phrase CtxUnit (BoolExp :-> BoolExp)
test3 = Lam idX BoolExp (I idX)

test4 : Phrase CtxUnit BoolExp
test4 = App test3 (CBool True)

recFact : Phrase CtxUnit (IntExp :-> IntExp)
recFact = Rec (Lam idF (IntExp:->IntExp) 
                (Lam idN IntExp (If (BinOp Equal (CInt 0) (I idN))
                                    (CInt 1) 
                                    (BinOp ITimes (I idN) (I idF))
                                )
                )
              )
