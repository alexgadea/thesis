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
search {Pi=(a,t):>ctxs} {Theta=t} i' ((i,e),etas) = search' e i' etas
    where
        search' : {Pi:Ctx} -> {Theta:PhraseType} -> 
                  evalTy Theta -> Identifier -> evalCtx Pi -> evalTy Theta
        search' {Pi=CtxUnit} {Theta=t} e' i' () = e'
        search' {Pi=(a,t):>ctxs} {Theta=t} e' i' ((i,e),etas) = 
                    if i == i' then search' e i' etas else search' e' i' etas

hasI : Identifier -> PhraseType -> Ctx -> Ctx
hasI i pt CtxUnit = (i,pt) :> CtxUnit
hasI i pt ((i',pt') :> ctx) = if i == i'
                                then ((i',pt') :> ctx)
                                else (i',pt') :> hasI i pt ctx

map : {Pi:Ctx} -> {pt:PhraseType} -> 
      ((Identifier,evalTy pt) -> (Identifier,evalTy pt)) -> 
      evalCtx Pi -> evalCtx Pi
map {Pi=CtxUnit} _ () = ()
map {Pi=(i,t):>pi'} {pt=t} f ((i,e),etas) = (f (i,e), etas)
                                
-- Agregar un valor por detras al environment.
-- Estaría bueno poder hacer un prepend que no deje valores 
-- basura, pero tengo problema con los tipos.
prependCtx : {Pi:Ctx} -> {pt:PhraseType} -> evalCtx Pi -> 
             (i:Identifier) -> evalTy pt -> evalCtx (Pi <: (i,pt))--(hasI i pt Pi)
-- prependCtx etas i z = map replace etas
--     where
--         replace : {pt1:PhraseType} -> (Identifier,evalTy pt1) -> (Identifier,evalTy pt1)
--         replace (i',e) = if i == i' then (i',e) else (i',e)
-- prependCtx {Pi=CtxUnit} () i z = ((i,z),())
-- prependCtx {Pi=(i',t):>ctxs} ((i',e),etas) i z = if i == i'
--                                                     then ((i',z),etas)
--                                                     else ((i',e),prependCtx etas i z)
prependCtx eta j z = eta <:++:> ((j,z),())
