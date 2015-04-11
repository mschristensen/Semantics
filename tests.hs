{- TESTS -}

import Prelude hiding (lookup)
import CWK2
{-
ev :: EnvV
ev "x" = 1
ev "y" = 2
ev "z" = 3
ev _ = 0

t :: Store
t 1 = 10
t 2 = 11
t 3 = 12
t _ = undefined -}

b_t :: Bexp
b_t = Le (N 4) (N 5)

b_f :: Bexp
b_f = Le (N 6) (N 5)

b_1 :: Bexp
b_1 = Le (V "x") (N 20)

ss1 :: Stm
ss1 = (Ass "x" (N 9))

ss2 :: Stm
ss2 = (Ass "y" (N 8))

ss3 :: Stm
ss3 = Comp ss1 ss2

ss4 :: Stm
ss4 = Ass "x" (Add (V "x") (N 1))



test1 = (lookup ev t) "x"                   {- 10 -}
test2 = (lookup ev t) "y"                   {- 11 -}
test3 = (lookup ev t) "z"                   {- 12 -}

test4 = (update t 100 1) 1                  {- 100 -}
test5 = (update (update t 200 1) 300 2) 1   {- 200 -}
test6 = (update (update t 200 1) 300 2) 2   {- 300 -}

test7 = cond ( (>4) , (+1) , (*2) ) 2       {- 4 -}
test8 = cond ( (>4) , (+1) , (*2) ) 5       {- 6 -}

test9 = (s_ds' ss1 ev t) 1                  {- 9 -}
test10 = (s_ds' ss1 ev t) 2                 {- 11 -}
test11 = (s_ds' Skip ev t) 1                {- 1 -}

test12 = (s_ds' ss3 ev t) 1                 {- 9 -}
test13 = (s_ds' ss3 ev t) 2                 {- 8 -}

test14 = (s_ds' (If b_f ss1 ss2) ev t) 1    {- 10 -}
test15 = (s_ds' (If b_f ss1 ss2) ev t) 2    {- 8 -}
test16 = (s_ds' (If b_t ss1 ss2) ev t) 1    {- 9 -}
test17 = (s_ds' (If b_t ss1 ss2) ev t) 2    {- 11 -}

test18 = (s_ds' (While b_1 ss4) ev t) 1     {- 21 -}

test19 = (s_ds ss1 ev undefined t) 1
test20 = (s_ds ss1 ev undefined t) 2                 {- 11 -}
test21 = (s_ds Skip ev undefined t) 1                {- 1 -}

test22 = (s_ds ss3 ev undefined t) 1                 {- 9 -}
test23 = (s_ds ss3 ev undefined t) 2                 {- 8 -}

test24 = (s_ds (If b_f ss1 ss2) ev undefined t) 1    {- 10 -}
test25 = (s_ds (If b_f ss1 ss2) ev undefined t) 2    {- 8 -}
test26 = (s_ds (If b_t ss1 ss2) ev undefined t) 1    {- 9 -}
test27 = (s_ds (If b_t ss1 ss2) ev undefined t) 2    {- 11 -}

test28 = (s_ds (While b_1 ss4) ev undefined t) 1     {- 21 -}


main = do
    print $ test1
    print $ test2
    print $ test3
    print $ test4
    print $ test5
    print $ test6
    print $ test7
    print $ test8
    print $ test9
    print $ test10
    print $ test11
    print $ test12
    print $ test13
    print $ test14
    print $ test15
    print $ test16
    print $ test17
    print $ test18
    print $ test19
    print $ test20
    print $ test21
    print $ test22
    print $ test23
    print $ test24
    print $ test25
    print $ test26
    print $ test27
    print $ test28