-- Módulo que representa el contexto de variables.
module Ctx

import Shp
import PhraseType

-- ################## Versión sintácticas ##################
mutual
    -- Representación de un contexto sintáctico.
    data Ctx : Type where
        CtxUnit : Ctx
        Prepend : (p:Ctx) -> (i:Identifier) -> (pt:PhraseType) -> 
                  Fresh p i -> Ctx
    -- Representa si un identificador es fresco para un contexto.
    data Fresh : Ctx -> Identifier -> Type where
        FUnit : (i:Identifier) -> Fresh CtxUnit i
        FCons : (i:Identifier) -> (pt':PhraseType) -> (i':Identifier) -> 
                (p:Ctx) -> (fi':Fresh p i') -> so (i/=i') -> (Fresh p i) -> 
                Fresh (Prepend p i' pt' fi') i

-- Representa la pertenencia de un identificador en un contexto.
data InCtx : Ctx -> Identifier -> Type where
    InHead : (p:Ctx) -> (i:Identifier) -> (pt:PhraseType) -> 
             (fi:Fresh p i) -> InCtx (Prepend p i pt fi) i
    InTail : (p:Ctx) -> (i:Identifier) -> (pt:PhraseType) -> 
             (j:Identifier) -> (fj:Fresh p j) -> 
             InCtx p i -> InCtx (Prepend p j pt fj) i

-- ################## Versión semánticas ##################

-- Semántica de un contexto en un objeto con forma.
-- Representación de un contexto semántico.
evalCtxO : Ctx -> Shp -> Type
evalCtxO CtxUnit C = ()
evalCtxO (Prepend p _ pt _) C = (evalCtxO p C, evalTyO pt C)

-- Semántica de un contexto aplicado a morfismos entre objetos.
evalCtxM : {C:Shp} -> {C':Shp} -> 
           (p:Ctx) -> C <= C' -> evalCtxO p C -> evalCtxO p C'
evalCtxM CtxUnit m _ = ()
evalCtxM (Prepend p i pt _) m (eta,etai) = (evalCtxM p m eta, evalTyM pt m etai)

-- Transforma un environment con forma C, en uno con forma C ~: Dt
liftEta : (c:Shp) -> (dt:DataType) -> (p:Ctx) -> 
          evalCtxO p c -> evalCtxO p (c ~: dt)
liftEta c dt p eta = evalCtxM p (c >>> (ShpUnit ~: dt)) eta

-- Transforma un environment con forma C, en uno con forma C++C'
liftEta' : (c:Shp) -> (c':Shp) -> (p:Ctx) -> evalCtxO p c -> 
           evalCtxO p (c ++ c')
liftEta' c c' p eta = evalCtxM p (c >>> c') eta

-- Buscar el valor de un identificador en un contexto semántico.
search : (c:Shp) -> (p:Ctx) -> (i:Identifier) -> (pt:PhraseType) ->
         InCtx p i -> evalCtxO p c -> evalTyO pt c
search _ (Prepend _ i pt _) i pt (InHead _ i pt fi) (eta,v) = v
search c (Prepend ctx j pt _) i pt (InTail _ _ pt j _ inc) (eta,_) = search c ctx i pt inc eta

-- Actualizar el valor de un identificador.
update : (c:Shp) -> (p:Ctx) -> evalCtxO p c -> (i:Identifier) -> 
         (pt:PhraseType) -> evalTyO pt c -> (fi:Fresh p i) -> evalCtxO (Prepend p i pt fi) c
update _ p eta i pt z fi = (eta,z)
