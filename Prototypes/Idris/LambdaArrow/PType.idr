-- Módulo que representa los tipos de dato básicos para las frases del
-- lenguaje.
module PType

-- Operador flecha para phrase types.
infixr 10 :->

-- Esto representa los tipos de las frases de nuetro lenguaje.
data PType = IntExp | RealExp | BoolExp 
           | (:->) PType PType

infixr 10 :->

-- Tipo de dato para los identificadores de variable.
data Identifier = Id String

instance Eq Identifier where
    (Id i) == (Id i') = i == i'

{- 
Semántica para los tipos 
    [[IntExp]]  = int
    [[RealExp]] = real
    [[BoolExp]] = bool
    [[Theta :-> Theta]] = [[Theta]] -> [[Theta]]
-}
evalTy : PType -> Type
evalTy IntExp    = Int
evalTy RealExp   = Float
evalTy BoolExp   = Bool
evalTy (Theta :-> Theta') = evalTy Theta -> evalTy Theta'
