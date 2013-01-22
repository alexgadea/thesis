-- Módulo que representa los tipos de dato básicos del lenguaje.
module DataType

-- Gramática de los tipos básicos.
-- <Data types> ::= Int | Real | Bool
data DataType = IntDT | RealDT | BoolDT

instance Eq DataType where
    IntDT  == IntDT  = True
    RealDT == RealDT = True
    BoolDT == BoolDT = True
    _ == _ = False

{- Semántica de los data type.
    [[Int]]  = \Z
    [[Real]] = \R
    [[Bool]] = {true,false}
-}
evalDTy : DataType -> Set
evalDTy IntDT  = Int
evalDTy RealDT = Float
evalDTy BoolDT = Bool
