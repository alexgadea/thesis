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

-- Transforma la semántica de un tipo en un cierto objeto c, en la semántica
-- de un tipo en otro objeto c', pero mientras c=c' .
convEvTyCtx : {Pt : PhraseType} -> (C : Shp) -> (C' : Shp) -> C = C' -> evalTyO Pt C -> evalTyO Pt C'
convEvTyCtx c c refl eval = eval

-- Semántica para los phrase types aplicada a morfismos entre objetos.
evalTyM : {C:Shp} -> {C':Shp} -> 
          (t:PhraseType) -> C <= C' -> evalTyO t C -> evalTyO t C'
evalTyM IntExp             (morp (h,s,_)) e         = e . h
evalTyM RealExp            (morp (h,s,_)) e         = e . h
evalTyM BoolExp            (morp (h,s,_)) e         = e . h
evalTyM IntAcc             (morp (h,s,_)) a         = s . a
evalTyM RealAcc            (morp (h,s,_)) a         = s . a
evalTyM BoolAcc            (morp (h,s,_)) a         = s . a
evalTyM IntVar             (morp (h,s,_)) (a,e)     = (s . a, e . h)
evalTyM BoolVar            (morp (h,s,_)) (a,e)     = (s . a, e . h)
evalTyM RealVar            (morp (h,s,_)) (a,e)     = (s . a, e . h)
evalTyM Comm               (morp (h,s,_)) c         = s c
evalTyM {C=c} {C'=c'} (Theta :-> Theta') (morp (h,s,(c1 ** p))) f = 
                    \c'' => \v => contract c'' (f (c1++c'') (expand c'' v))
    where
        p' : (c'':Shp) -> c' ++ c'' = (c++c1) ++ c''
        p' c'' = eqConcat c' (c++c1) c'' p
        p'' : (c'':Shp) -> (c++c1)++c'' = c++(c1++c'')
        p'' c'' = assocR c c1 c''
        p''' : (c'':Shp) -> c' ++ c'' = c ++ (c1 ++ c'')
        p''' c'' = trans (p' c'') (p'' c'')
        p'''' : (c'':Shp) -> c ++ (c1 ++ c'') = c' ++ c''
        p'''' c'' = symmShp (p''' c'')
        expand : (c'':Shp) -> evalTyO Theta (c'++c'') -> evalTyO Theta (c++(c1++c''))
        expand c'' v = convEvTyCtx (c'++c'') (c ++ (c1 ++ c'')) (p''' c'') v
        contract : (c'':Shp) -> evalTyO Theta' (c++(c1++c'')) -> evalTyO Theta' (c'++c'')
        contract c'' v = convEvTyCtx (c ++ (c1 ++ c'')) (c'++c'') (p'''' c'') v

-- Propiedad de que la semántica de un tipo en un objeto c, es la semántica
-- de ese tipo en el objeto c++ShpUnit.
convL : {Pt : PhraseType} -> {C : Shp} -> evalTyO Pt C -> evalTyO Pt (C ++ ShpUnit)
convL {C=c} eval = convEvTyCtx c (c++ShpUnit) (neutDShp c) eval

-- Propiedad de que la semántica de un tipo en un objeto c++ShpUnit, es la semántica
-- de ese tipo en el objeto c.
convR : {Pt : PhraseType} -> {C : Shp} -> evalTyO Pt (C ++ ShpUnit) -> evalTyO Pt C
convR {C=c} eval = convEvTyCtx (c++ShpUnit) c (neutLShp c) eval
