-- Language Engineering
-- Denotational Semantics
-- CWK2

{- Export for testing purposes -}
module CWK2
(   module CWK2
) where

import Prelude hiding (lookup)

-- Type Definitions (Given)

data Aexp = N Integer | V Var | Add Aexp Aexp | Mult Aexp Aexp | Sub Aexp Aexp  deriving (Show)
data Bexp = TRUE | FALSE | Eq Aexp Aexp | Le Aexp Aexp | Neg Bexp | And Bexp Bexp   deriving (Show)
data Stm  = Ass Var Aexp | Skip | Comp Stm Stm | If Bexp Stm Stm | While Bexp Stm | Block DecV DecP Stm | Call Pname    deriving (Show)

type Var = String
type Pname = String
type DecV = [(Var,Aexp)]
type DecP = [(Pname,Stm)]

type Z = Integer
type T = Bool
type State = Var -> Z
type Loc = Z
type Store = Loc -> Z
type EnvV = Var -> Loc
type EnvP = Pname -> Store -> Store

next = 0

-- Semantic Functions (Copied from parts 1 and 2 of the coursework)

a_val :: Aexp -> State -> Z
a_val (N n) s = n
a_val (V x) s = s x
a_val (Add a1 a2) s = (a_val a1 s) + (a_val a2 s)
a_val (Sub a1 a2) s = (a_val a1 s) - (a_val a2 s)
a_val (Mult a1 a2) s = (a_val a1 s) * (a_val a2 s)

b_val :: Bexp -> State -> T
b_val TRUE s = True
b_val FALSE s = False
b_val (Eq a1 a2) s = (a_val a1 s) == (a_val a2 s)
b_val (Le a1 a2) s = (a_val a1 s) <= (a_val a2 s)
b_val (Neg b) s = not(b_val b s)
b_val (And b1 b2) s = (b_val b1 s) && (b_val b2 s)


fix :: (a -> a) -> a
fix ff = ff (fix ff)

fac :: Integer -> Integer
fac x
    | x == 0 = 1
    | otherwise = x * (fac (x - 1))

    
-- Semantic Functions (New)

{- TEST FUNCTIONs -}

ev :: EnvV
ev "x" = 1
ev "y" = 2
ev "z" = 3
ev _ = 0

s :: Stm
s = Comp (Ass "x" (N 365)) (Ass "y" (N 3))
{-s = (Block ([("x",N 7)]) ([("p",Ass "x" (N 7))]) (Block ([("x",N 5)]) ([]) (Call "p")))-}

t :: Store
t 1 = 10
t 2 = 11
t 3 = 12
t _ = undefined

n :: Integer -> Integer
n x = (s_ds s ev undefined t) x

{-END TEST FUNCTIONS -}
    
new :: Loc -> Loc
new x = succ x

lookup :: EnvV -> Store -> State
lookup e s = s.e

update :: Eq a => (a->b) -> b -> a -> (a->b)
update f v x = g where g y = if x == y then v else f y

cond :: (a->T, a->a, a->a) -> (a->a)
cond (p, g1, g2) s = if p s then g1 s else g2 s



s_ds' :: Stm -> EnvV -> Store -> Store
s_ds' (Ass x a) e s = update s (a_val a (lookup e s)) (e x)
s_ds' Skip e s = id
s_ds' (Comp ss1 ss2) e s = ((s_ds' ss2 e) . (s_ds' ss1 e)) s
s_ds' (If b ss1 ss2) e s = cond ((b_val b).(lookup e), s_ds' ss1 e, s_ds' ss2 e) s  {- WHY s ON THE END? -}
s_ds' (While b ss) e s = fix ff s where ff g = cond((b_val b).(lookup e), g . (s_ds' ss e), id) {- WHY id ON THE END? -}



s_ds :: Stm -> EnvV -> EnvP -> Store -> Store
s_ds (Ass x a) ev ep s = update s (a_val a (lookup ev s)) l
    where l = ev x
s_ds Skip ev ep s = id
s_ds (Comp ss1 ss2) ev ep s = ((s_ds ss2 ev ep) . (s_ds ss1 ev ep)) s
s_ds (If b ss1 ss2) ev ep s = cond ((b_val b).(lookup ev), s_ds ss1 ev ep, s_ds ss2 ev ep) s
s_ds (While b ss) ev ep s = fix ff s where ff g = cond((b_val b).(lookup ev), g.(s_ds ss ev ep), id)
s_ds (Block dv dp ss) ev ep s = s_ds ss ev'  ep' s'
    where   (ev', s') = d_v_ds dv (ev, s)
            ep' = d_p_ds dp ev' ep
s_ds (Call p) ev ep s = ep p s



d_v_ds :: DecV -> (EnvV, Store) -> (EnvV, Store)
d_v_ds ((x,a):xs) (e,s) = d_v_ds xs (update e l x, update (update s (new l) next) v l)
    where   l = s next
            v = a_val a (lookup e s)
d_v_ds [] (e,s) = id (e,s)



d_p_ds :: DecP -> EnvV -> EnvP -> EnvP	
d_p_ds ((p,stm):xs) ev ep = d_p_ds xs ev (update ep g p)
    where g = s_ds stm ev ep
d_p_ds [] ev ep = id ep



























