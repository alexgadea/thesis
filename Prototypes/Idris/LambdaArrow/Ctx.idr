-- Módulo que representa el contexto de variables.
module Ctx

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

-- Semántica de un contexto.
evalCtx : Ctx -> Set
evalCtx CtxUnit = ()
evalCtx ((i,t):>ctxs) = ((Identifier,evalTy t), evalCtx ctxs)

-- Concatenar environments.
(<:++:>) : {Pi:Ctx} -> {Pi':Ctx} -> 
           evalCtx Pi -> evalCtx Pi' -> evalCtx (Pi :++: Pi')
(<:++:>) {Pi=CtxUnit} () p' = p'
(<:++:>) {Pi=(i,pt):>pi} (e,p) p' = (e, p <:++:> p')

-- Buscar un valor en un environment en base a un identificador.
search : {Pi:Ctx} -> {Theta:PhraseType} -> 
         Identifier -> evalCtx Pi -> evalTy Theta
search {Pi=(a,t):>ctxs} {Theta=t} i' ((i,e),etas) = 
        if i == i' then e else search i' etas

-- Agregar un valor por detras al environment.
prependCtx : {Pi:Ctx} -> (pt:PhraseType) -> evalCtx Pi -> 
             (i:Identifier) -> evalTy pt -> evalCtx (Pi <: (i,pt))
prependCtx pt eta j z = eta <:++:> ((j,z),())
