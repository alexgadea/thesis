-- Módulo que representa los objetos con forma y los morfismos entre
-- esos objetos.
module Shp

import DataType

-- Constructor de morfismo entre dos objetos con forma.
infixr 10 >>>
-- Pegar por delante para objetos con forma.
infixr 10 :~
-- Pegar por detras para objetos con forma.
infixr 10 ~:
-- Concatenar objetos con forma.
infixr 10 ++
-- Concatenar shapes.
infixr 10 <++>

-- Representa la forma del estado de la parte imperativa.
data Shp = ShpUnit | (:~) DataType Shp

instance Eq Shp where
    ShpUnit == ShpUnit = True
    (dt:~c) == (dt':~c') = dt == dt' && c == c'
    _ == _ = False

-- Transformación de un objeto con forma a la representación
-- de un conjunto de estados con esa forma.
shapes : Shp -> Set
shapes ShpUnit = ()
shapes (d:~s) = (evalDTy d,shapes s)

-- Concatena objetos con forma.
(++) : Shp -> Shp -> Shp
ShpUnit ++ C' = C'
(dt:~s) ++ C' = dt :~ (s ++ C')

-- Pegar por dentras.
(~:) : Shp -> DataType -> Shp
C ~: dt = C ++ (dt :~ ShpUnit)

-- Establece la igualdad cuando pegamos por delante a objetos con forma.
cong : (C:Shp) -> (C':Shp) -> (C=C') -> (dt :~ C = dt :~ C')
cong c c refl = refl

-- Propiedad de simetria para los objetos con forma.
symmShp : {C : Shp} -> {C' : Shp} -> C = C' -> C' = C
symmShp cEqc' = sym cEqc'

eqConcat : (C : Shp) -> (C' : Shp) -> (C'':Shp) -> C = C' -> C++C'' = C'++C''
eqConcat c c c'' refl = refl

trans : {C : Shp} -> {C' : Shp} -> {C'' : Shp} -> C = C' -> C' = C'' -> C = C''
trans refl refl = refl

assocL : (C : Shp) -> (C' : Shp) -> (C'' : Shp) -> C ++ (C' ++ C'') = (C ++ C') ++ C''
assocL ShpUnit c' c'' = refl
assocL (dt :~ c) c' c'' = cong (c++(c'++c'')) ((c++c')++c'') (assocL c c' c'')

assocR : (C : Shp) -> (C' : Shp) -> (C'' : Shp) -> (C ++ C') ++ C'' = C ++ (C' ++ C'')
assocR ShpUnit c' c'' = refl
assocR (dt :~ c) c' c'' = cong ((c++c')++c'') (c++(c'++c'')) (assocR c c' c'')

-- Propiedad de neutro a derecha.
neutDShp : (C:Shp) -> C = (C ++ ShpUnit)
neutDShp ShpUnit = refl
neutDShp (dt :~ C) = cong C (C ++ ShpUnit) (neutDShp C)

-- Propiedad de neutro a izquierda.
neutLShp : (C:Shp) -> (C ++ ShpUnit) = C
neutLShp ShpUnit = refl
neutLShp (dt :~ C) = cong (C ++ ShpUnit) C (neutLShp C)

-- Toma el tramo inicial con forma C, de un estado con forma C++C'
head : (C : Shp) -> (C' : Shp) -> shapes (C ++ C') -> shapes C
head ShpUnit c' shp = ()
head (dt :~ c) c' (d',s) = (d' , head c c' s)

-- Toma el tramo final con forma C', de un estado con forma C++C'
tail : (C : Shp) -> (C' : Shp) -> shapes (C ++ C') -> shapes C'
tail ShpUnit c' shp = shp
tail (dt :~ c) c' (d',s)  = tail c c' s

-- Toma el ultimo elemento de tipo Dt del estado con forma C.
last : (C : Shp) -> (Dt:DataType) -> shapes C -> evalDTy Dt
last (dt :~ ShpUnit) dt (v,()) = v
last (dt' :~ c) dt (v,s) = last c dt s

-- Concatena shapes.
(<++>) : {C:Shp} -> {C' : Shp} -> shapes C -> shapes C' -> shapes (C ++ C')
(<++>) {C=ShpUnit} () s' = s'
(<++>) {C=dt:~c} (d,s) s' = (d,s <++> s')

-- Agrega un valor por detras al estado.
prependShp : {c:Shp} -> {dt:DataType} -> 
            shapes c -> evalDTy dt -> shapes (c ~: dt)
prependShp s i = s <++> (i,())

eqShape : Shp -> Shp -> Shp -> Set
eqShape c c' c'' = c' = c ++ c''

-- Representa un morfismo entre dos objetos con forma.
data (<=) : Shp -> Shp -> Set where 
        morp : {C:Shp} -> {C':Shp} -> 
               ( shapes C' -> shapes C
               , (shapes C -> shapes C) -> (shapes C' -> shapes C')
               , ( c'' : Shp ** eqShape C C' c'')
               ) -> C <= C'

-- Constructor de un morfismo entre dos objetos.
(>>>) : (C : Shp) -> (C' : Shp) -> C <= (C ++ C')
c >>> c' = morp (head c c', sim, (c' ** refl))
    where
        sim : (shapes c -> shapes c) -> (shapes (c ++ c') -> shapes (c ++ c'))
        sim f sigma' = f (head c c' sigma') <++> tail c c' sigma'
