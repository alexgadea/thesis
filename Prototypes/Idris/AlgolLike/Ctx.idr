-- Módulo que representa el contexto de variables.
module Ctx

import Shp
import PhraseType

-- Pegar por delante para contextos
infixr 10 :>
-- Pegar por detras para contextos
infixr 10 <:
-- Concatenar contextos.
infixr 10 :++:
-- Concatenar contextos semánticos.
infixr 10 <:++:>

-- Representa los contextos de los juicios de tipado del lenguaje.
data Ctx = CtxUnit | (:>) (Identifier,PhraseType) Ctx

-- Concatena contextos.
(:++:) : Ctx -> Ctx -> Ctx
(:++:) CtxUnit ctx' = ctx'
(:++:) (e:>ctx) ctx' = e:> (ctx :++:ctx')

-- Pegar por detras
(<:) : Ctx -> (Identifier,PhraseType) -> Ctx
ctx <: e = ctx :++: (e:>CtxUnit)

-- Semántica de un contexto en un objeto con forma.
evalCtxO : Ctx -> Shp -> Set
evalCtxO CtxUnit C = ()
evalCtxO ((i,t):>ctxs) C = ((Identifier,evalTyO t C), evalCtxO ctxs C)

-- Semántica de un contexto aplicado a morfismos entre objetos.
evalCtxM : {C:Shp} -> {C':Shp} -> 
           (ctx:Ctx) -> C <= C' -> evalCtxO ctx C -> evalCtxO ctx C'
evalCtxM CtxUnit m () = ()
evalCtxM ((i,t):>ctx') m ((i,etai),eta) = ((i,evalTyM t m etai),evalCtxM ctx' m eta)

-- Transforma un environment con forma C, en uno con forma C ~: Dt
liftEta : (C:Shp) -> (Dt:DataType) -> (Pi:Ctx) -> evalCtxO Pi C -> 
          evalCtxO Pi (C ~: Dt)
liftEta c dt p eta = evalCtxM p (c >>> (dt :~ ShpUnit)) eta

-- Transforma un environment con forma C, en uno con forma C++C'
liftEta' : (C:Shp) -> (C':Shp) -> (Pi:Ctx) -> evalCtxO Pi C -> 
           evalCtxO Pi (C ++ C')
liftEta' c c' p eta = evalCtxM p (c >>> c') eta

-- Concatenar environments.
(<:++:>) : {Pi:Ctx} -> {Pi':Ctx} -> {C:Shp} -> 
           evalCtxO Pi C -> evalCtxO Pi' C -> evalCtxO (Pi :++: Pi') C
(<:++:>) {Pi=CtxUnit} () p' = p'
(<:++:>) {Pi=(i,pt):>pi} (e,p) p' = (e, p <:++:> p')

-- Buscar un valor en un environment en base a un identificador.
search : {Pi:Ctx} -> {C:Shp} -> {Theta:PhraseType} -> 
         Identifier -> evalCtxO Pi C -> evalTyO Theta C
search {Pi=(a,t):>ctxs} {Theta=t} i' ((i,e),etas) = 
        if i == i' then e else search i' etas

-- Agregar un valor por detras al environment.
prependCtx : {C:Shp} -> {Pi:Ctx} -> (pt:PhraseType) -> 
            evalCtxO Pi C -> (i:Identifier) -> evalTyO pt C -> evalCtxO (Pi <: (i,pt)) C
prependCtx pt eta j z = eta <:++:> ((j,z),())
