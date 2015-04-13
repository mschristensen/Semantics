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

{- Evaluate arithmetic expressions -}
a_val :: Aexp -> State -> Z
a_val (N n) s = n
a_val (V x) s = s x
a_val (Add a1 a2) s = (a_val a1 s) + (a_val a2 s)
a_val (Sub a1 a2) s = (a_val a1 s) - (a_val a2 s)
a_val (Mult a1 a2) s = (a_val a1 s) * (a_val a2 s)

{- Evaluate boolean expressions -}
b_val :: Bexp -> State -> T
b_val TRUE s = True
b_val FALSE s = False
b_val (Eq a1 a2) s = (a_val a1 s) == (a_val a2 s)
b_val (Le a1 a2) s = (a_val a1 s) <= (a_val a2 s)
b_val (Neg b) s = not(b_val b s)
b_val (And b1 b2) s = (b_val b1 s) && (b_val b2 s)

{- if b evaluates to true then return function f1, else f2 -}
cond :: (a->T, a->a, a->a) -> (a->a)
cond (b, f1, f2) s = if b s then f1 s else f2 s

{- fixpoint function -}
fix :: (a -> a) -> a
fix ff = ff (fix ff)

-- Semantic Functions (New)

{- UTIL FUNCTIONs -}  

{-  Simple program:
    begin var x:=7; proc p is x:=0;
        begin var x:=5;
            call p
        end
    end
-}
s :: Stm
s = (Block ([("x",N 7)]) ([("p",Ass "x" (N 0))]) (Block ([("x",N 5)]) ([]) (Call "p")))


{- The initial store.
   Location 0 is reserved for the 'next' token, (next = 0).
   The value of that location gives the next free location.
   All other locations are undefined. -}
t :: Store
t 0 = 1
t _ = undefined

{-  Returns the number of defined locations in the store 
    given by: s_ds s undefined undefined t
    This is the value of the next free location minus one. -}
n :: Integer
n = ((s_ds s undefined undefined t) 0) - 1

{- A procedure declaration for a factorial program. -}
f :: DecP
f = [("fac", Block [("z", (V "x"))] [] (If (Eq (V "x") (N 1)) (Skip) (Comp (Ass "x" (Sub (V "x") (N 1))) (Comp (Call "fac") (Ass "y" (Mult (V "z") (V "y")))))))]

{-  A wrapper for the factorial program given by f,
    which initialises x to 5 and y to 1.
    (therefore 5! = 120 is calculated) -}
g :: Stm
g = Block [("x", (N 5)), ("y", (N 1))] f (Call "fac")

{-END UTIL FUNCTIONS -}

{- Get a new location -}
new :: Loc -> Loc
new x = succ x

{- Function to return a direct mapping from var to value -}
lookup :: EnvV -> Store -> State
lookup e s = s.e

{- Set function f to output v on input x -}
update :: Eq a => (a->b) -> b -> a -> (a->b)
update f v x = g where g y = if x == y then v else f y

{- A function describing the effect of the execution of a
   statement on the program variables. (While language) -}
s_ds' :: Stm -> EnvV -> Store -> Store
s_ds' (Ass x a) e s = update s (a_val a (lookup e s)) (e x)
s_ds' Skip e s = s
s_ds' (Comp ss1 ss2) e s = ((s_ds' ss2 e) . (s_ds' ss1 e)) s
s_ds' (If b ss1 ss2) e s = cond ((b_val b).(lookup e), s_ds' ss1 e, s_ds' ss2 e) s  {- WHY s ON THE END? -}
s_ds' (While b ss) e s = fix ff s where ff g = cond((b_val b).(lookup e), g . (s_ds' ss e), id) {- WHY id ON THE END? -}


{- A function describing the effect of the execution of a
   statement on the program variables.
   (Proc language: procedures are now implemented) -}
s_ds :: Stm -> EnvV -> EnvP -> Store -> Store
s_ds (Ass x a) ev ep s = update s (a_val a (lookup ev s)) l
    where l = ev x
s_ds Skip ev ep s = s
s_ds (Comp ss1 ss2) ev ep s = ((s_ds ss2 ev ep) . (s_ds ss1 ev ep)) s
s_ds (If b ss1 ss2) ev ep s = cond ((b_val b).(lookup ev), s_ds ss1 ev ep, s_ds ss2 ev ep) s
s_ds (While b ss) ev ep s = fix ff s where ff g = cond((b_val b).(lookup ev), g.(s_ds ss ev ep), id)
s_ds (Block dv dp ss) ev ep s = s_ds ss ev' ep' s'
    where   (ev', s') = d_v_ds dv (ev, s)
            ep' = d_p_ds dp ev' ep
s_ds (Call p) ev ep s = ep p s


{- A function to update the var env and store given a list of new variable declarations -}
d_v_ds :: DecV -> (EnvV, Store) -> (EnvV, Store)
d_v_ds ((x,a):xs) (e,s) = d_v_ds xs (update e l x, update (update s (new l) next) v l)
    where   l = s next
            v = a_val a (lookup e s)
d_v_ds [] (e,s) = id (e,s)

{- A function to update the proc env and store given a list of new proc declarations -}
{- Version of d_p_ds for *non-recursive* procedures, (part h). -}
{-
d_p_ds :: DecP -> EnvV -> EnvP -> EnvP	
d_p_ds ((p,stm):xs) ev ep = d_p_ds xs ev (update ep g p)
    where g = s_ds stm ev ep
d_p_ds [] ev ep = id ep
-}

{- A function to update the proc env and store given a list of new proc declarations -}
{- Version of d_p_ds for *recursive* procedures (part l) -}
d_p_ds :: DecP -> EnvV -> EnvP -> EnvP	
d_p_ds ((p,stm):xs) ev ep = d_p_ds xs ev (update ep (fix ff) p)
    where ff g = s_ds stm ev (update ep g p)
d_p_ds [] ev ep = id ep


{- DYNAMIC SCOPING (part n) - see ~p54 of the book. -}

{- Create a new type of procedure environment which 
   maps procedure name to procedure body -}
type EnvP' = Pname -> Stm

{- Function to update the proc env so that procs declared
   in DecP are now available -}
updateEnvP' :: DecP -> EnvP' -> EnvP'
updateEnvP' ((p,s):xs) ep = updateEnvP' xs (update ep s p)
updateEnvP' [] ep = ep

{- A function describing the effect of the execution of a
   statement on the program variables.
   Uses DYNAMIC scope. -}
s_ds'' :: Stm -> EnvV -> EnvP' -> Store -> Store
s_ds'' (Ass x a) ev ep s = update s (a_val a (lookup ev s)) l
            where l = ev x
s_ds'' Skip ev ep s = s
s_ds'' (Comp ss1 ss2) ev ep s = ((s_ds'' ss2 ev ep) . (s_ds'' ss1 ev ep)) s
s_ds'' (If b ss1 ss2) ev ep s = cond ((b_val b).(lookup ev), s_ds'' ss1 ev ep, s_ds'' ss2 ev ep) s
s_ds'' (While b ss) ev ep s = fix ff s where ff g = cond((b_val b).(lookup ev), g.(s_ds'' ss ev ep), id)
s_ds'' (Block dv dp ss) ev ep s = s_ds'' ss ev' ep' s'
    where   (ev', s') = d_v_ds dv (ev, s)
            ep' = updateEnvP' dp ep
s_ds'' (Call p) ev ep s = s_ds'' (ep p) ev ep s

