-- Módulo que representa los tipos de dato básicos para las frases del
-- lenguaje.
module PhraseType

-- Operador flecha para phrase types.
infixr 10 :->

-- Esto representa los tipos de las frases de nuetro lenguaje.
data PhraseType = IntExp | RealExp | BoolExp 
                | (:->) PhraseType PhraseType

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
evalTy : PhraseType -> Type
evalTy IntExp    = Int
evalTy RealExp   = Float
evalTy BoolExp   = Bool
evalTy (Theta :-> Theta') = evalTy Theta -> evalTy Theta'
