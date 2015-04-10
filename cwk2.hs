-- Language Engineering
-- Denotational Semantics
-- CWK2

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

-- Semantic Functions (To Do)

{-
new :: Loc -> Loc
lookup :: EnvV -> Store -> State
update :: Eq a => (a->b) -> b -> a -> (a->b)
s_ds' :: Stm -> EnvV -> Store -> Store
d_v_ds :: DecV -> (EnvV, Store) -> (EnvV, Store)	
d_p_ds :: DecP -> EnvV -> EnvP -> EnvP	
s_ds :: Stm -> EnvV -> EnvP -> Store -> Store
-}

{- TEST FUNCTIONs -}

ev :: EnvV
ev "x" = 1
ev _ = 0

q :: Store
q x 
    | x == 0 = 2
    | x == 1 = 0
    | otherwise = undefined

{-END TEST FUNCTIONS -}
    
    
    
new :: Loc -> Loc
new x = succ x

lookup :: EnvV -> Store -> State
lookup e s = s.e

update :: Eq a => (a->b) -> b -> a -> (a->b)
update f v x = g where g x = v


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

t :: Store
t 0 = 1     {- Should be t next = 1  ? -}
t _ = undefined

{-
    DecV is a list of (Var, Aexp) tuples, describing the current 'state' of vars,
    that is, the current variable environment and the current store. These need to be
    updated when a new block with local declarations is entered.
    
    Input
    (x,a):xs        (x,a) is the first (Var,Aexp) tuple in DecV (at the head).
    (e,s)           is the current var env and store.
    
    Output          The updated var env and store after all declarations.
                    Strategy: Recursively call d_v_ds until the list is empty.
    update e l x
    ===> Update the var env (e) so that on receiving x the elem in the store pointed to by 'next' is returned
    
    update (update s (new l) next) v l
    ===> update the store (s) so that on receiving 'next' a new location is returned
    ^^ DOUBLE UPDATED WTF?
    
-}
d_v_ds :: DecV -> (EnvV, Store) -> (EnvV, Store)
d_v_ds ((x,a):xs) (e,s) = d_v_ds xs (update e l x, update (update s (new l) next) v l)
    where   l = s next
            v = a_val a (lookup e s)
d_v_ds [] (e,s) = id (e,s)

{-
    type EnvP = Pname -> Store -> Store
    ===>    EnvP associates each procedure with the 'effect' of its execution, i.e. the change
            in the state of the variables.
    
    d_p_ds accepts the current var env and proc env in order to update the proc env.

    DecP is a list of (Pname,Stm) tuples, describing the current set of procedures by
    their names and the statements the
-}
d_p_ds :: DecP -> EnvV -> EnvP -> EnvP	
d_p_ds ((p,stm):xs) ev ep = d_p_ds xs ev (update ep g p)
    where g = s_ds stm ev ep


{-s :: Stm
s = begin var x:=7; proc p is x:=0; begin var x:=5; call p end end-}



























