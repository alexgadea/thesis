{- Módulo que representa el contexto de identificadores.

Los contextos los vamos a separar en dos "versiones" la sintactica
y la semántica, la idea es implementar los contextos sintacticos de
forma que no haya repetición de nombres de identificador. Es decir,
un contexto va a ser una lista de identificadores y phrase types;

i_0:pt_0, ... , i_n:pt_n

para contextos semánticos simplemente es una lista de la siguiente manera,

evalTy pt_0, ... , evalTy pt_n

y tenemos una correspondencia lugar a lugar con el contexto sintáctico para
buscar el valor.

-}
module Ctx

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

-- Representación de un contexto semántico.
evalCtx : Ctx -> Type
evalCtx CtxUnit = ()
evalCtx (Prepend p _ pt _) = (evalCtx p, evalTy pt)

-- Buscar el valor de un identificador en un contexto semántico.
search : (p:Ctx) -> (i:Identifier) -> (pt:PhraseType) ->
         InCtx p i -> evalCtx p -> evalTy pt
search (Prepend _ i pt _) i pt (InHead _ i pt fi) (eta,v) = v
search (Prepend ctx j pt _) i pt (InTail _ _ pt j _ inc) (eta,_) = search ctx i pt inc eta

-- Actualizar el valor de un identificador.
update : (p:Ctx) -> evalCtx p -> (i:Identifier) -> 
         (pt:PhraseType) -> evalTy pt -> (fi:Fresh p i) -> evalCtx (Prepend p i pt fi)
update p eta i pt z fi = (eta,z)
