-- Módulo de ejemplos.
-- Tercer prototipo de un evaluador de un lenguaje funcional con imperativo
-- considerando shapes.
module Eval

import Ctx
import Shp
import DataType
import PhraseType
import Judge

idX : Identifier
idX = Id "x"

val2 : Phrase CtxUnit IntExp
val2 = CInt 2

val3 : Phrase CtxUnit IntExp
val3 = CInt 3

test : Phrase CtxUnit Comm
test = NewIntVar {j=idX} (Var idX) val2 Skip

-- test2 : Phrase ((idX,IntExp):>CtxUnit) IntExp
-- test2 = App (Lam (Var idX) val2) val3
