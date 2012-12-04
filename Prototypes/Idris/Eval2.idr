-- Tercer prototipo de un evaluador de un lenguaje funcional con imperativo
-- considerando shapes.
module Main

-- Operador de punto fijo.
fix : (a -> a) -> a
fix f = f (fix f)

data Identifier = Id String

instance Eq Identifier where
    (Id s) == (Id s') = s == s'

data DataType = IntDT | RealDT | BoolDT

instance Eq DataType where
    IntDT  == IntDT  = True
    RealDT == RealDT = True
    BoolDT == BoolDT = True
    _ == _ = False

evalDTy : DataType -> Set
evalDTy IntDT = Int
evalDTy RealDT = Bool
evalDTy BoolDT = Float

data PhraseType = IntExp | RealExp | BoolExp 
                | IntAcc | RealAcc | BoolAcc
                | IntVar | RealVar | BoolVar
                | (:->) PhraseType PhraseType
                | Comm

infixr 10 :->
infixr 10 <~
infixr 10 :>
infixr 10 <:
infixr 10 :++:
infixr 10 <:++:>
infixr 10 :~
infixr 10 ~:
infixr 10 ++
infixr 10 >>>
infixr 10 <++>
infixr 10 <++

data Shp = ShpUnit | (:~) DataType Shp

shapes : Shp -> Set
shapes ShpUnit = ()
shapes (d:~s) = (evalDTy d,shapes s)

(++) : Shp -> Shp -> Shp
ShpUnit ++ C' = C'
(dt:~s) ++ C' = dt :~ (s ++ C')

instance Eq Shp where
    ShpUnit == ShpUnit = True
    (dt:~c) == (dt':~c') = dt == dt' && c == c'
    _ == _ = False

(~:) : Shp -> DataType -> Shp
C ~: dt = C ++ (dt :~ ShpUnit)

(<++>) : {C:Shp} -> {C' : Shp} -> shapes C -> shapes C' -> shapes (C ++ C')
(<++>) {C=ShpUnit} () s' = s'
(<++>) {C=dt:~c} (d,s) s' = (d,s <++> s')

data (<=) : Shp -> Shp -> Set where 
        morp : {C:Shp} -> {C':Shp} -> 
               ( shapes C' -> shapes C
               , (shapes C -> shapes C) -> (shapes C' -> shapes C')
               ) -> C <= C'

head : (C : Shp) -> (C' : Shp) -> shapes (C ++ C') -> shapes C
head ShpUnit c' shp = ()
head (dt :~ c) c' (d',s) = (d' , head c c' s)

tail : (C : Shp) -> (C' : Shp) -> shapes (C ++ C') -> shapes C'
tail ShpUnit c' shp = shp
tail (dt :~ c) c' (d',s)  = tail c c' s

last : (C : Shp) -> (Dt:DataType) -> shapes C -> evalDTy Dt
last (dt :~ ShpUnit) dt (v,()) = v
last (dt' :~ c) dt (v,s) = last c dt s

(>>>) : (C : Shp) -> (C' : Shp) -> C <= (C ++ C')
c >>> c' = morp (head c c', sim)
    where
        sim : (shapes c -> shapes c) -> (shapes (c ++ c') -> shapes (c ++ c'))
        sim f sigma' = f (head c c' sigma') <++> tail c c' sigma'

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
evalTyO (Theta :-> Theta') C = (C':Shp) -> evalTyO Theta (C ++ C') -> evalTyO Theta' (C ++ C')

evalTyM : {C:Shp} -> {C':Shp} -> PhraseType -> C <= C' -> evalTyO t C -> evalTyO t C'
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

data Ctx = CtxUnit | (:>) (Identifier,PhraseType) Ctx

(:++:) : Ctx -> Ctx -> Ctx
(:++:) CtxUnit ctx' = ctx'
(:++:) (e:>ctx) ctx' = e:> (ctx :++:ctx')

(<:) : Ctx -> (Identifier,PhraseType) -> Ctx
ctx <: e = ctx :++: (e:>CtxUnit)

evalCtxO : Ctx -> Shp -> Set
evalCtxO CtxUnit C = ()
evalCtxO ((i,t):>ctxs) C = ((Identifier,evalTyO t C), evalCtxO ctxs C)

evalCtxM : {C:Shp} -> {C':Shp} -> Ctx -> C <= C' -> evalCtxO ctx C -> evalCtxO ctx C'
evalCtxM {ctx=CtxUnit} ctx m () = ()
evalCtxM {ctx=(Identifier,PhraseType):>ctx'} ((i,t):>ctx') m ((i,etai),eta) = ((i,evalTyM t m etai),evalCtxM ctx' m eta)

liftEta : (C:Shp) -> (Dt:DataType) -> (Pi:Ctx) -> evalCtxO Pi C -> evalCtxO Pi (C ~: Dt)
liftEta c dt p eta = evalCtxM p (c >>> (dt :~ ShpUnit)) eta

(<:++:>) : {Pi:Ctx} -> {Pi':Ctx} -> {C:Shp} -> 
           evalCtxO Pi C -> evalCtxO Pi' C -> evalCtxO (Pi :++: Pi') C
(<:++:>) {Pi=CtxUnit} () p' = p'
(<:++:>) {Pi=(i,pt):>pi} (e,p) p' = (e, p <:++:> p')

search : {Pi:Ctx} -> {C:Shp} -> {Theta:PhraseType} -> 
         Identifier -> evalCtxO Pi C -> evalTyO Theta C
search {Pi=(a,t):>ctxs} {Theta=t} i' ((i,e),etas) = 
        if i == i' then e else search i' etas

append : {c:Shp} -> {dt:DataType} -> shapes c -> evalDTy dt -> shapes (c ~: dt)
append s i = s <++> (i,())

appendCtx : {C:Shp} -> {Pi:Ctx} -> (pt:PhraseType) -> 
            evalCtxO Pi C -> (i:Identifier) -> evalTyO pt C -> evalCtxO (Pi <: (i,pt)) C
appendCtx pt eta j z = eta <:++:> ((j,z),())

data BOp : PhraseType -> PhraseType -> PhraseType -> Set where
    Add  : BOp IntExp IntExp IntExp
    Subs : BOp IntExp IntExp IntExp
    
data UOp : PhraseType -> PhraseType -> Set where
    Neg  : UOp BoolExp BoolExp

using (Pi:Ctx,Theta:PhraseType,Theta':PhraseType)
    data Phrase : Ctx -> PhraseType -> Set where
        Skip   : Phrase Pi Comm
        Seq    : Phrase Pi Comm -> Phrase Pi Comm -> Phrase Pi Comm
        While  : Phrase Pi BoolExp -> Phrase Pi Comm -> Phrase Pi Comm
        If     : Phrase Pi BoolExp -> Phrase Pi Theta -> Phrase Pi Theta -> Phrase Pi Theta
        Assig  : Phrase Pi IntAcc -> Phrase Pi IntExp -> Phrase Pi Comm
        Var : Identifier -> Phrase Pi Theta
        NewIntVar : {j:Identifier} -> Phrase Pi IntVar -> Phrase Pi IntExp -> 
                    Phrase (Pi<:(j,IntVar)) Comm -> Phrase Pi Comm
        
        CInt    : Int   -> Phrase Pi IntExp
        CFloat  : Float -> Phrase Pi RealExp
        CBool   : Bool  -> Phrase Pi BoolExp
        
        BinOp : BOp a b c -> Phrase Pi a -> Phrase Pi b -> Phrase Pi c
        UnOp  : UOp a b -> Phrase Pi a -> Phrase Pi b

        Lam    : Phrase Pi Theta -> Phrase ((i,Theta):>Pi) Theta' -> Phrase Pi (Theta :-> Theta')
        App    : Phrase Pi (Theta :-> Theta') -> Phrase Pi Theta -> Phrase Pi Theta'

data (<~) : PhraseType -> PhraseType -> Set where
        VarToAcc : IntVar <~ IntAcc
        VarToExp : IntVar <~ IntExp

-- /////////////// Ejemplos ///////////////
idX : Identifier
idX = Id "x"

val2 : Phrase CtxUnit IntExp
val2 = CInt 2

val3 : Phrase CtxUnit IntExp
val3 = CInt 3

test : Phrase CtxUnit Comm
test = NewIntVar {j=idX} (Var idX) val2 Skip

-- assig : Phrase ((idX,IntVar):>CtxUnit) Comm
-- assig = Assig (Var idX) val3

test2 : Phrase CtxUnit Comm
test2 = NewIntVar {j=idX} (Var idX) val2 Skip
-- /////////////// Ejemplos ///////////////

evalLeq : {C:Shp} -> t <~ t' -> evalTyO t C -> evalTyO t' C
evalLeq (VarToAcc) (a,e) = a
evalLeq (VarToExp) (a,e) = e

evalPhrase : {Pi:Ctx} -> {Theta:PhraseType} ->
             Phrase Pi Theta -> (C:Shp) -> evalCtxO Pi C -> evalTyO Theta C
evalPhrase (Assig a e) c eta = \sigma => ((\x => (evalPhrase a c eta) x sigma) (evalPhrase e c eta sigma))
evalPhrase Skip c eta = \sigma => sigma
evalPhrase (Seq comm comm') c eta = \sigma => evalPhrase comm' c eta (evalPhrase comm c eta sigma)
evalPhrase (While b comm) c eta = fix (\f => \sigma => if evalPhrase b c eta sigma then evalPhrase comm c eta sigma else sigma)
evalPhrase {Theta=Comm} (If b e e') c eta = \sigma => if evalPhrase b c eta sigma then evalPhrase e c eta sigma else evalPhrase e' c eta sigma
evalPhrase (Var i) c eta = search i eta
evalPhrase (CInt i) c eta = \sigma => i
evalPhrase (CFloat r) c eta = \sigma => r
evalPhrase (CBool b) c eta = \sigma => b
-- evalPhrase (BinOp Add x y) c eta = \sigma => ((evalPhrase x c eta sigma) + (evalPhrase y c eta sigma))
-- evalPhrase (BinOp Subs x y) c eta = \sigma => ((evalPhrase x c eta sigma) - (evalPhrase y c eta sigma))
-- evalPhrase (UnOp Neg x) s eta = \sigma => not (evalPhrase x s eta sigma)
-- evalPhrase {Theta=t} {Pi=pi} (Lam (Var i) b) c eta c' z = evalPhrase b (c++c') (appendCtx t (liftEta c ... pi eta) i z)
-- evalPhrase (App e e') c eta = (evalPhrase e c eta ShpUnit) (evalPhrase e' c eta)
evalPhrase {Pi=pi} (NewIntVar (Var i) vInit comm) c eta = 
        \sigma => head c intdt (evalComm (append sigma (evalInit sigma)))
    where
        intdt : Shp
        intdt = IntDT :~ ShpUnit
        
        a : evalTyO IntAcc (c ~: IntDT)
        a = \x => \sigma' => append (head c intdt sigma') x
        e : evalTyO IntExp (c ~: IntDT)
        e = last (c ~: IntDT) IntDT
        
        evalInit : evalTyO IntExp c
        evalInit sigma = evalPhrase vInit c eta sigma
        
        eta' : {j:Identifier} -> evalCtxO (pi <: (j,IntVar)) (c ~: IntDT)
        eta' {j=i} = appendCtx IntVar (liftEta c IntDT pi eta) i (a,e)
        evalComm : evalTyO Comm (c ~: IntDT)
        evalComm = evalPhrase comm (c ~: IntDT) eta'

--evalComm sigma = evalPhrase comm (c ̣~: IntDT) eta sigma
