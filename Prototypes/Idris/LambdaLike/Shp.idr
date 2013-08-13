-- Módulo que representa los objetos con forma y los morfismos entre
-- esos objetos.
module Shp

import DataType

-- Constructor de morfismo entre dos objetos con forma.
infixr 10 >>>
-- Pegar por detras para objetos con forma.
infixr 10 ~:
-- Concatenar objetos con forma.
infixl 8 ++
-- Concatenar shapes.
infixl 8 <++>

-- Representa la forma del estado de la parte imperativa.
data Shp = ShpUnit | (~:) Shp DataType

instance Eq Shp where
    ShpUnit == ShpUnit = True
    (c~:dt) == (c'~:dt') = dt == dt' && c == c'
    _ == _ = False

-- Transformación de un objeto con forma a la representación
-- de un conjunto de estados con esa forma.
shapes : Shp -> Type
shapes ShpUnit = ()
shapes (c~:dt) = (shapes c,evalDTy dt)

-- Concatena objetos con forma.
(++) : Shp -> Shp -> Shp
C' ++ ShpUnit = C'
C' ++ (c ~: dt) = (C' ++ c) ~: dt

-- Establece la igualdad cuando pegamos por delante a objetos con forma.
cong : (C:Shp) -> (C':Shp) -> (C=C') -> (C ~: dt = C' ~: dt)
cong c c refl = refl

-- Propiedad de simetria para los objetos con forma.
symmShp : {C : Shp} -> {C' : Shp} -> C = C' -> C' = C
symmShp cEqc' = sym cEqc'

eqConcat : (C : Shp) -> (C' : Shp) -> (C'':Shp) -> C = C' -> C++C'' = C'++C''
eqConcat c c c'' refl = refl

trans : {C : Shp} -> {C' : Shp} -> {C'' : Shp} -> C = C' -> C' = C'' -> C = C''
trans refl refl = refl

assocL : (C : Shp) -> (C' : Shp) -> (C'' : Shp) -> C ++ (C' ++ C'') = (C ++ C') ++ C''
assocL c c' ShpUnit = refl
assocL c c' (c'' ~: dt) = cong (c++(c'++c'')) ((c++c')++c'') (assocL c c' c'')

assocR : (C : Shp) -> (C' : Shp) -> (C'' : Shp) -> (C ++ C') ++ C'' = C ++ (C' ++ C'')
assocR c c' ShpUnit = refl
assocR c c' (c'' ~: dt) = cong ((c++c')++c'') (c++(c'++c'')) (assocR c c' c'')

-- Propiedad de neutro a derecha.
neutDShp : (C:Shp) -> C = (C ++ ShpUnit)
neutDShp ShpUnit = refl
neutDShp (c ~: dt) = cong c (c ++ ShpUnit) (neutDShp c)

-- Propiedad de neutro a izquierda.
neutLShp : (C:Shp) -> (C ++ ShpUnit) = C
neutLShp ShpUnit = refl
neutLShp (c ~: dt) = cong (c ++ ShpUnit) c (neutLShp c)

-- Toma el tramo inicial con forma C, de un estado con forma C++C'
head : (C : Shp) -> (C' : Shp) -> shapes (C ++ C') -> shapes C
head c ShpUnit shp = shp
head c (c' ~: dt) (s,d') = head c c' s

-- Toma el tramo final con forma C', de un estado con forma C++C'
tail : (C : Shp) -> (C' : Shp) -> shapes (C ++ C') -> shapes C'
tail c ShpUnit shp = ()
tail c (c' ~: dt) (s,d')  = (tail c c' s,d')

-- Toma el ultimo elemento de tipo Dt del estado con forma C.
last : (C : Shp) -> (Dt:DataType) -> shapes C -> evalDTy Dt
last (c ~: dt) dt (s,v) = v

-- Concatena shapes.
(<++>) : {C:Shp} -> {C' : Shp} -> shapes C -> shapes C' -> shapes (C ++ C')
(<++>) {C'=ShpUnit} s _ = s
(<++>) {C'=c~:dt} s (s',d) = (s <++> s',d)

-- Agrega un valor por detras al estado.
prependShp : {c:Shp} -> {dt:DataType} -> 
            shapes c -> evalDTy dt -> shapes (c ~: dt)
prependShp s z = (s,z)

eqShape : Shp -> Shp -> Shp -> Type
eqShape c c' c'' = c' = c ++ c''

-- Representa un morfismo entre dos objetos con forma.
data (<=) : Shp -> Shp -> Type where 
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
