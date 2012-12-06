-- Módulo que representa los tipos de dato básicos para las frases del
-- lenguaje.
module PhraseType

import Shp

-- Operador flecha para phrase types.
infixr 10 :->
-- Juicio de tipado para el subtipado.
infixr 10 <~

-- Tipo de dato para los identificadores de variable.
data Identifier = Id String

instance Eq Identifier where
    (Id s) == (Id s') = s == s'

{- Gramática de los tipos de las frases del lenguaje.
   <Phrase type> ::= IntExp | RealExp | BoolExp
                  |  IntAcc | RealAcc | BoolAcc
                  |  IntVar | RealVar | BoolVar
                  |  <Phrase type> :-> <Phrase type>
                  |  Comm

-}
data PhraseType = IntExp | RealExp | BoolExp 
                | IntAcc | RealAcc | BoolAcc
                | IntVar | RealVar | BoolVar
                | (:->) PhraseType PhraseType
                | Comm
    
-- Semántica para los phrase types aplicada a objetos con forma.
evalTyO : PhraseType -> Shp -> Set
evalTyO IntExp             C = shapes C -> Int
evalTyO RealExp            C = shapes C -> Float
evalTyO BoolExp            C = shapes C -> Bool
evalTyO IntAcc             C = Int -> evalTyO Comm C
evalTyO RealAcc            C = Float -> evalTyO Comm C
evalTyO BoolAcc            C = Bool -> evalTyO Comm C
evalTyO IntVar             C = (evalTyO IntAcc  C, evalTyO IntExp C)
evalTyO RealVar            C = (evalTyO RealAcc C, evalTyO RealExp C)
evalTyO BoolVar            C = (evalTyO BoolAcc C, evalTyO BoolExp C)
evalTyO Comm               C = shapes C -> shapes C
evalTyO (Theta :-> Theta') C = (C':Shp) -> 
                               evalTyO Theta (C ++ C') -> 
                               evalTyO Theta' (C ++ C')

-- Semántica para los phrase types aplicada a morfismos entre objetos.
evalTyM : {C:Shp} -> {C':Shp} -> 
          PhraseType -> C <= C' -> evalTyO t C -> evalTyO t C'
evalTyM {t=IntExp}           t (morp (h,s)) e     = e . h
evalTyM {t=RealExp}          t (morp (h,s)) e     = e . h
evalTyM {t=BoolExp}          t (morp (h,s)) e     = e . h
evalTyM {t=IntAcc}           t (morp (h,s)) a     = s . a
evalTyM {t=RealAcc}          t (morp (h,s)) a     = s . a
evalTyM {t=BoolAcc}          t (morp (h,s)) a     = s . a
evalTyM {t=IntVar}           t (morp (h,s)) (a,e) = (s . a, e . h)
evalTyM {t=RealVar}          t (morp (h,s)) (a,e) = (s . a, e . h)
evalTyM {t=BoolVar}          t (morp (h,s)) (a,e) = (s . a, e . h)
evalTyM {t=Comm}             t (morp (h,s)) c     = s c
-- evalTyM {C=c} {C'=c++c'} {t=Theta :-> Theta'} t (morp (h,s)) f = app (c++c')
--     where
--         app : (C':Shp) -> (C'':Shp) -> evalTyO Theta (C' ++ C'') -> evalTyO Theta' (C' ++ C'')
--         app c' c'' = f(c'++c'')

-- Eval2.idr:340:Can't unify evalTyO Theta c with evalTyO Theta (Main.++ c ShpUnit)

-- Transforma la semántica de un tipo en un cierto objeto c, en la semántica
-- de un tipo en otro objeto c', pero mientras c=c' .
convEvTyCtx : {Pt : PhraseType} -> (C : Shp) -> (C' : Shp) -> C = C' -> evalTyO Pt C -> evalTyO Pt C'
convEvTyCtx c c refl eval = eval

-- Propiedad de que la semántica de un tipo en un objeto c, es la semántica
-- de ese tipo en el objeto c++ShpUnit.
convL : {Pt : PhraseType} -> {C : Shp} -> evalTyO Pt C -> evalTyO Pt (C ++ ShpUnit)
convL {C=c} eval = convEvTyCtx c (c++ShpUnit) (neutDShp c) eval

-- Propiedad de que la semántica de un tipo en un objeto c++ShpUnit, es la semántica
-- de ese tipo en el objeto c.
convR : {Pt : PhraseType} -> {C : Shp} -> evalTyO Pt (C ++ ShpUnit) -> evalTyO Pt C
convR {C=c} eval = convEvTyCtx (c++ShpUnit) c (neutLShp c) eval
