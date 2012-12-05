-- Tercer prototipo de un evaluador de un lenguaje funcional con imperativo
-- considerando shapes.
module Main

-- Operador de punto fijo.
fix : (a -> a) -> a
fix f = f (fix f)

-- Tipo de dato para los identificadores de variable.
data Identifier = Id String

instance Eq Identifier where
    (Id s) == (Id s') = s == s'

-- Gramática de los tipos básicos.
-- <Data types> ::= Int | Real | Bool
data DataType = IntDT | RealDT | BoolDT

instance Eq DataType where
    IntDT  == IntDT  = True
    RealDT == RealDT = True
    BoolDT == BoolDT = True
    _ == _ = False

{- Semántica de los data type.
    [[Int]]  = \Z
    [[Real]] = \R
    [[Bool]] = {true,false}
-}
evalDTy : DataType -> Set
evalDTy IntDT = Int
evalDTy RealDT = Bool
evalDTy BoolDT = Float

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

-- Operador flecha para phrase types.
infixr 10 :->
-- Juicio de tipado para el subtipado.
infixr 10 <~
-- Pegar por delante para contextos
infixr 10 :>
-- Pegar por detras para contextos
infixr 10 <:
-- Concatenar contextos.
infixr 10 :++:
-- Concatenar contextos semánticos.
infixr 10 <:++:>
-- Pegar por delante para objetos con forma.
infixr 10 :~
-- Pegar por detras para objetos con forma.
infixr 10 ~:
-- Concatenar objetos con forma.
infixr 10 ++
-- Concatenar shapes.
infixr 10 <++>
-- Constructor de morfismo entre dos objetos con forma.
infixr 10 >>>

-- ######################### Objetos con forma #########################

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

-- Representa un morfismo entre dos objetos con forma.
data (<=) : Shp -> Shp -> Set where 
        morp : {C:Shp} -> {C':Shp} -> 
               ( shapes C' -> shapes C
               , (shapes C -> shapes C) -> (shapes C' -> shapes C')
               ) -> C <= C'

-- Constructor de un morfismo entre dos objetos.
(>>>) : (C : Shp) -> (C' : Shp) -> C <= (C ++ C')
c >>> c' = morp (head c c', sim)
    where
        sim : (shapes c -> shapes c) -> (shapes (c ++ c') -> shapes (c ++ c'))
        sim f sigma' = f (head c c' sigma') <++> tail c c' sigma'


-- ######################### Objetos con forma #########################

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
evalTyM {t=IntExp}  t (morp (h,s)) e = e . h
evalTyM {t=RealExp} t (morp (h,s)) e = e . h
evalTyM {t=BoolExp} t (morp (h,s)) e = e . h
evalTyM {t=IntAcc}  t (morp (h,s)) a = s . a
evalTyM {t=RealAcc} t (morp (h,s)) a = s . a
evalTyM {t=BoolAcc} t (morp (h,s)) a = s . a
evalTyM {t=IntVar}  t (morp (h,s)) (a,e) = (s . a, e . h)
evalTyM {t=RealVar} t (morp (h,s)) (a,e) = (s . a, e . h)
evalTyM {t=BoolVar} t (morp (h,s)) (a,e) = (s . a, e . h)
evalTyM {t=Comm}    t (morp (h,s)) c = s c

-- Eval2.idr:340:Can't unify evalTyO Theta c with evalTyO Theta (Main.++ c ShpUnit)

symmShp : {C : Shp} -> {C' : Shp} -> C = C' -> C' = C
symmShp cEqc' = sym cEqc'

cong : (C:Shp) -> (C':Shp) -> (C=C') -> (dt :~ C = dt :~ C')
cong c c refl = refl

neutDShp : (C:Shp) -> C = (C ++ ShpUnit)
neutDShp ShpUnit = refl
neutDShp (dt :~ C) = cong C (C ++ ShpUnit) (neutDShp C)

neutLShp : (C:Shp) -> (C ++ ShpUnit) = C
neutLShp ShpUnit = refl
neutLShp (dt :~ C) = cong (C ++ ShpUnit) C (neutLShp C)

convEvTyCtx : {Pt : PhraseType} -> (C : Shp) -> (C' : Shp) -> C = C' -> evalTyO Pt C -> evalTyO Pt C'
convEvTyCtx c c refl eval = eval

convL : {Pt : PhraseType} -> {C : Shp} -> evalTyO Pt C -> evalTyO Pt (C ++ ShpUnit)
convL {C=c} eval = convEvTyCtx c (c++ShpUnit) (neutDShp c) eval

convR : {Pt : PhraseType} -> {C : Shp} -> evalTyO Pt (C ++ ShpUnit) -> evalTyO Pt C
convR {C=c} eval = convEvTyCtx (c++ShpUnit) c (neutLShp c) eval

-- ######################### Contextos #########################

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
           Ctx -> C <= C' -> evalCtxO ctx C -> evalCtxO ctx C'
evalCtxM {ctx=CtxUnit} ctx m () = ()
evalCtxM {ctx=(Identifier,PhraseType):>ctx'} ((i,t):>ctx') m ((i,etai),eta) = 
                                ((i,evalTyM t m etai),evalCtxM ctx' m eta)

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

-- ######################### Contextos #########################

-- Representa los nombres de operadores binarios.
data BOp : PhraseType -> PhraseType -> PhraseType -> Set where
    IPlus  : BOp IntExp IntExp IntExp
    ISubs  : BOp IntExp IntExp IntExp
    ITimes : BOp IntExp IntExp IntExp
    
    RPlus  : BOp RealExp RealExp RealExp
    RSubs  : BOp RealExp RealExp RealExp
    RTimes : BOp RealExp RealExp RealExp
    
    Div    : BOp IntExp IntExp IntExp
    Rem    : BOp IntExp IntExp IntExp
    RDiv   : BOp RealExp RealExp RealExp
    
    Equal  : {a:PhraseType} -> BOp a a BoolExp
    NEqual : {a:PhraseType} -> BOp a a BoolExp
    Lt     : BOp RealExp RealExp BoolExp
    LtEq   : BOp RealExp RealExp BoolExp
    Gt     : BOp RealExp RealExp BoolExp
    GtEq   : BOp RealExp RealExp BoolExp
    
    And    : BOp BoolExp BoolExp BoolExp
    Or     : BOp BoolExp BoolExp BoolExp
    Impl   : BOp BoolExp BoolExp BoolExp
    Iff    : BOp BoolExp BoolExp BoolExp
    
-- Representa los nombres de operadores unarios.
data UOp : PhraseType -> PhraseType -> Set where
    RNeg : UOp RealExp RealExp
    INeg : UOp IntExp IntExp
    Not  : UOp BoolExp BoolExp

-- Representa las frases del lenguaje.
using (Pi:Ctx,Theta:PhraseType,Theta':PhraseType)
    data Phrase : Ctx -> PhraseType -> Set where
        Skip      : Phrase Pi Comm
        Seq       : Phrase Pi Comm -> Phrase Pi Comm -> Phrase Pi Comm
        While     : Phrase Pi BoolExp -> Phrase Pi Comm -> Phrase Pi Comm
        If        : Phrase Pi BoolExp -> Phrase Pi Theta -> Phrase Pi Theta -> 
                    Phrase Pi Theta
        
        Var       : Identifier -> Phrase Pi Theta
        Assig     : Phrase Pi IntAcc -> Phrase Pi IntExp -> Phrase Pi Comm
        NewIntVar : {j:Identifier} -> Phrase Pi IntVar -> Phrase Pi IntExp -> 
                    Phrase (Pi<:(j,IntVar)) Comm -> Phrase Pi Comm
        
        CInt    : Int   -> Phrase Pi IntExp
        CFloat  : Float -> Phrase Pi RealExp
        CBool   : Bool  -> Phrase Pi BoolExp
        
        BinOp : BOp a b c -> Phrase Pi a -> Phrase Pi b -> Phrase Pi c
        UnOp  : UOp a b -> Phrase Pi a -> Phrase Pi b

        Lam    : Phrase Pi Theta -> Phrase ((i,Theta):>Pi) Theta' -> 
                 Phrase Pi (Theta :-> Theta')
        App    : Phrase Pi (Theta :-> Theta') -> Phrase Pi Theta -> 
                 Phrase Pi Theta'

-- Representa el jucio de tipado para el subtipado.
data (<~) : PhraseType -> PhraseType -> Set where
    VarToAcc : IntVar <~ IntAcc
    VarToExp : IntVar <~ IntExp
    
    IntExpToRealExp : IntExp <~ RealExp
    RealAccToIntAcc : RealAcc <~ IntAcc

-- Semántica del subtipado.
evalLeq : {C:Shp} -> t <~ t' -> evalTyO t C -> evalTyO t' C
evalLeq (VarToAcc) (a,e) = a
evalLeq (VarToExp) (a,e) = e

-- Semántica de las frases del lenguaje.
-- [[\pi |-- e : \theta]]C : [[\pi]]*C -> [[\theta]]]C
evalPhrase : {Pi:Ctx} -> {Theta:PhraseType} ->
             Phrase Pi Theta -> (C:Shp) -> evalCtxO Pi C -> evalTyO Theta C
-- Semántica para los comandos.
evalPhrase (Assig a e) c eta = \sigma => ((\x => (evalPhrase a c eta) x sigma) (evalPhrase e c eta sigma))
evalPhrase Skip c eta = \sigma => sigma
evalPhrase (Seq comm comm') c eta = \sigma => evalPhrase comm' c eta (evalPhrase comm c eta sigma)
evalPhrase (While b comm) c eta = fix (\f => \sigma => 
                                            if evalPhrase b c eta sigma 
                                                then evalPhrase comm c eta sigma 
                                                else sigma)
evalPhrase (Var i) c eta = search i eta
-- Semántica para los valores constantes.
evalPhrase (CInt i) c eta = \sigma => i
evalPhrase (CFloat r) c eta = \sigma => r
evalPhrase (CBool b) c eta = \sigma => b
-- evalPhrase (BinOp Plus x y) c eta = \sigma => ((evalPhrase x c eta sigma) + (evalPhrase y c eta sigma))
-- evalPhrase (BinOp Subs x y) c eta = \sigma => ((evalPhrase x c eta sigma) - (evalPhrase y c eta sigma))
-- evalPhrase (UnOp Not x) s eta = \sigma => not (evalPhrase x s eta sigma)
--evalPhrase {Theta=(t :-> t')} {Pi=pi} (Lam (Var i) b) c eta = \c' => \z => evalPhrase b (c++c') (prependCtx t (liftEta' c c' pi eta) i z)
evalPhrase (App e e') c eta = convR $ (evalPhrase e c eta ShpUnit) (convL $ evalPhrase e' c eta)
evalPhrase {Theta=Comm} (If b e e') c eta = \sigma => 
                                            if evalPhrase b c eta sigma 
                                                then evalPhrase e c eta sigma 
                                                else evalPhrase e' c eta sigma
evalPhrase {Pi=pi} (NewIntVar (Var i) vInit comm) c eta = 
        \sigma => head c intdt (evalComm (prependShp sigma (evalInit sigma)))
    where
        intdt : Shp
        intdt = IntDT :~ ShpUnit
        
        a : evalTyO IntAcc (c ~: IntDT)
        a = \x => \sigma' => prependShp (head c intdt sigma') x
        e : evalTyO IntExp (c ~: IntDT)
        e = last (c ~: IntDT) IntDT
        
        evalInit : evalTyO IntExp c
        evalInit sigma = evalPhrase vInit c eta sigma
        
        eta' : {j:Identifier} -> evalCtxO (pi <: (j,IntVar)) (c ~: IntDT)
        eta' {j=i} = prependCtx IntVar (liftEta c IntDT pi eta) i (a,e)
        evalComm : evalTyO Comm (c ~: IntDT)
        evalComm = evalPhrase comm (c ~: IntDT) eta'

-- /////////////// Ejemplos ///////////////
idX : Identifier
idX = Id "x"

val2 : Phrase CtxUnit IntExp
val2 = CInt 2

val3 : Phrase CtxUnit IntExp
val3 = CInt 3

test : Phrase CtxUnit Comm
test = NewIntVar {j=idX} (Var idX) val2 Skip

test2 : Phrase CtxUnit Comm
test2 = NewIntVar {j=idX} (Var idX) val2 Skip
-- /////////////// Ejemplos ///////////////
