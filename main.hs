{-# LANGUAGE UnicodeSyntax #-}

import Control.Monad.Except

main = return ()

data ITerm
  = Ann CTerm CTerm
  | Star
  | Pi CTerm CTerm
  | Bound Int
  | Free Name
  | ITerm :@: CTerm
  deriving (Show, Eq)

data CTerm
  = Inf ITerm
  | Lam CTerm
  deriving (Show, Eq)

data Name
  = Global String
  | Local Int
  | Quote Int
  deriving (Show, Eq)

data Value
  = VLam (Value → Value)
  | VNeutral Neutral
  | VStar
  | VPi Value (Value -> Value)

data Neutral
  = NFree Name
  | NApp Neutral Value

vfree :: Name → Value
vfree n = VNeutral (NFree n)

type Env = [Value]

iEval :: ITerm → Env → Value
iEval (Ann e _) d = cEval e d
iEval (Free x) d = vfree x
iEval (Bound i) d = d !! i
iEval (e :@: e') d = vapp (iEval e d) (cEval e' d)
iEval Star d = VStar
iEval (Pi t t') d = VPi (cEval t d) (\x -> cEval t' (x:d))

vapp :: Value → Value → Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

cEval :: CTerm → Env → Value
cEval (Inf i) d = iEval i d
cEval (Lam e) d = VLam (\x → cEval e (x:d))

type Type = Value
type Context = [(Name, Value)]

type Result a = Either String a

iType0 ∷ Context → ITerm → Result Type
iType0 = iType 0

iType ∷ Int → Context → ITerm → Result Type
iType i g (Ann e t)
  = do cType i g t VStar
       let t' = cEval t []
       cType i g e t'
       return t'

iType i g Star = return VStar

iType i g (Pi t t')
  = do cType i g t VStar
       let p = cEval t []
       cType (i + 1) ((Local i, p) : g) (cSubst 0 (Free (Local i)) t') VStar
       return VStar
       

iType i g (Free x)
   = case lookup x g of
       Just t → return t
       Nothing → throwError "unknown identifier"

iType i g (e :@: e')
  = do s ← iType i g e
       case s of
         VPi t t' → do cType i g e' t
                       return (t' (cEval e' []))
         _ → throwError "illegal application"

cType ∷ Int → Context → CTerm → Type → Result ()
cType i g (Inf e) t
  = do t' ← iType i g e
       unless (quote0 t == quote0 t') (throwError "type mismatch")

cType i g (Lam e) (VPi t t')
  = cType (i + 1) ((Local i, t) : g) (cSubst 0 (Free (Local i)) e) (t' (vfree (Local i)))

cType i g _ _
  = throwError "type mismatch"

iSubst ∷ Int → ITerm → ITerm → ITerm
iSubst i r (Ann e t) = Ann (cSubst i r e) (cSubst i r t)
iSubst i r (Bound j) = if i == j then r else Bound j
iSubst i r (Free y) = Free y
iSubst i r (e :@: e') = iSubst i r e :@: cSubst i r e'
iSubst i r Star = Star
iSubst i r (Pi t t') = Pi (cSubst i r t) (cSubst (i+1) r t')

cSubst ∷ Int → ITerm → CTerm → CTerm
cSubst i r (Inf e) = Inf (iSubst i r e)
cSubst i r (Lam e) = Lam (cSubst (i + 1) r e)

quote0 ∷ Value → CTerm
quote0 = quote 0

quote ∷ Int → Value → CTerm
quote i (VLam f) = Lam (quote (i + 1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)
quote i VStar = Inf Star
quote i (VPi v f) = Inf (Pi (quote i v) (quote (i+1) (f . vfree $ Quote i)))

neutralQuote ∷ Int → Neutral → ITerm
neutralQuote i (NFree x) = boundFree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundFree ∷ Int → Name → ITerm
boundFree i (Quote k) = Bound (i - k - 1)
boundFree i x = Free x
