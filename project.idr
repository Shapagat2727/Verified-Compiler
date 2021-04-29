--
-- import data.Vect
-- %default total
--
--
--
--
--
--
--
-- -- data EqNat : (num : Nat) -> (num2 : Nat) -> Type where
-- --       Same : (num : Nat) -> EqNat num num
-- --
-- -- sameS : (k:Nat) -> (j:Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
-- -- sameS k k (Same k) = Same (S k)
-- --
-- -- checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
-- -- checkEqNat Z Z = Just (Same 0)
-- -- checkEqNat Z (S k) = Nothing
-- -- checkEqNat (S k) Z = Nothing
-- -- checkEqNat (S k) (S j) = case checkEqNat k j of
-- --                               Nothing => Nothing
-- --                               Just eq => Just (sameS _ _ eq)
-- --
-- --
-- -- data EqList : (list1 : List Nat) -> (list2 : List Nat) -> Type where
-- --   SameList : (list : List Nat) -> EqList list list
-- --
-- --
-- -- sameL :(x: Nat) -> (y: Nat) -> (eqn : EqNat x y) -> (xs : List Nat) -> (ys : List Nat)
-- --                 -> (eq : EqList xs ys) -> EqList (x :: xs) (y :: ys)
-- -- sameL y y (Same y) ys ys (SameList ys) = SameList (y :: ys)
-- --
-- -- checkEqList : (list1 : List Nat) -> (list2 : List Nat) -> Maybe (EqList list1 list2)
-- -- checkEqList [] [] = Just (SameList [])
-- -- checkEqList [] (x :: xs) = Nothing
-- -- checkEqList (x :: xs) [] = Nothing
-- -- checkEqList (x :: xs) (y :: ys) = case checkEqList xs ys of
-- --                                        Nothing => Nothing
-- --                                        (Just eq) => (case checkEqNat x y of
-- --                                                           Nothing => Nothing
-- --                                                           (Just eqn) => Just (sameL x y eqn xs ys eq))
--
-- -- --------------------------------------------------------------------------
-- --
-- --
-- -- zeroNotSuc : ([] = (x :: xs)) -> Void
-- -- zeroNotSuc Refl impossible
-- --
-- -- sucNotZero : ((x :: xs) = []) -> Void
-- -- sucNotZero Refl impossible
-- --
-- --
-- --
-- -- checkEqList : (list1 : List Nat) -> (list2 : List Nat) -> Dec (list1 = list2)
-- -- checkEqList [] [] = Yes Refl
-- -- checkEqList [] (x :: xs) = No zeroNotSuc
-- -- checkEqList (x :: xs) [] = No sucNotZero
-- -- checkEqList (x :: xs) (y :: ys) = case decEq x y of
-- --                                        (Yes prf) => (case checkEqList xs ys of
-- --                                                           (Yes prf) => Yes (?sdsd_3)
-- --                                                           (No contra) => No (?sdsd_4))
-- --                                        (No contra) => No (?sdsd_2)
--
--
--
-- -- --------------------------------------------------------------------------
-- data Expr = Const Nat
--           | Plus Expr Expr
--           | Minus Expr Expr
--           | Times Expr Expr
--           | Var String
--
-- data Boolean = T
--              | F
--              | Equals Expr Expr
--              | NotEquals Expr Expr
--              | LessThan Expr Expr
--              -- | GreaterThan Expr Expr
--              -- | LessEq Expr Expr
--              -- | GreaterEq Expr Expr
--
--
--
--
--
--
-- data Statement = Initialize String Expr
--                | Update String Expr
--                | If Boolean Statement Statement
--                | While Boolean Statement
--
--
--
--
--
--
-- Program : Type
-- Program = List Statement
--
--
--
--
-- -- TODO: Verify that symbol exist in a memory
-- look_up : String -> Maybe (Vect n (String, Nat)) -> Maybe Nat
-- look_up sym Nothing = Nothing
-- look_up sym (Just []) = Nothing
-- look_up sym (Just (x :: xs)) = case fst x == sym of
--                                     False => look_up sym (Just xs)
--                                     True => Just (snd x)
--
--
-- eval : Maybe (Vect n (String, Nat)) -> Expr -> Maybe Nat
-- eval mem (Const num) = Just num
-- eval mem (Plus ex1 ex2) = case eval mem ex1 of
--                                Nothing => Nothing
--                                Just x => case eval mem ex2 of
--                                               Nothing => Nothing
--                                               Just y => Just (x + y)
-- eval mem (Minus ex1 ex2) = case eval mem ex1 of
--                                Nothing => Nothing
--                                Just x => case eval mem ex2 of
--                                               Nothing => Nothing
--                                               Just y => Just (minus x y)
-- eval mem (Times ex1 ex2) = case eval mem ex1 of
--                                Nothing => Nothing
--                                Just x => case eval mem ex2 of
--                                               Nothing => Nothing
--                                               Just y => Just (x * y)
-- eval mem (Var sym) = case look_up sym mem of
--                       Nothing => Nothing
--                       Just x => Just x
--
--
-- evalB : Maybe (Vect n (String, Nat)) -> Boolean -> Bool
-- evalB mem T = True
-- evalB mem F = False
-- evalB mem (Equals x y) = (eval mem x) == (eval mem y)
-- evalB mem (NotEquals x y) = case (eval mem x) == (eval mem y) of
--                               False => True
--                               True => False
-- evalB mem (LessThan x y) = case compare (eval mem x) (eval mem y) of
--                             LT => True
--                             EQ => False
--                             GT => False
--
--
--
-- get_firsts : Vect n (String, Nat) -> Vect n (String)
-- get_firsts [] = []
-- get_firsts (x :: xs) = (fst x) :: get_firsts xs
--
--
-- -- TODO: only call when we have a proof that (sym) is actually inside the Memory
--
-- update : (old : Vect n (String, Nat)) -> String -> Nat -> (new : Vect k (String, Nat)) -> Maybe (Vect n (String, Nat))
--
--
--
-- evalS : (mem : Maybe (Vect n (String, Nat))) -> Statement -> Maybe (Vect n (String, Nat))
-- -- evalS mem (Initialize sym ex) = case eval mem ex of
-- --                                        Nothing => Nothing
-- --                                        Just a => (case mem of
-- --                                                        Nothing => Nothing
-- --                                                        (Just x) => Just ((sym, a) :: x))
--
-- -- evalS mem (Update sym ex) = case eval mem ex of
-- --                                  Nothing => Nothing
-- --                                  Just a => (case mem of
-- --                                                  Nothing => Nothing
-- --                                                  (Just x) => update x sym a [])
-- --
-- --
-- -- evalS mem (If test thencl elsecl) = case evalB mem test of
-- --                                          False =>  evalS mem elsecl
-- --                                          True => evalS mem thencl
-- --
-- -- evalS mem (While test docl) = case evalB mem test of
-- --                                    False => mem
-- --                                    True => evalS (evalS mem docl) (While test docl)
--
--
-- --
-- -- evalP : Maybe (Vect n (String, Nat)) -> Program -> Maybe (Vect n (String, Nat))
-- -- evalP mem [] = mem
-- -- evalP mem (x :: xs) = case evalS mem x of
-- --                            Nothing => Nothing
-- --                            Just a => evalP (Just a) xs
--
-- ------Stack Machine-----------------------------------------------------------------
--
-- --
-- -- data Instr = Push Nat
-- --            | Add
-- --            | Subtract
-- --            | Multiply
-- --            | LValue String
-- --            | RValue String
-- --            | Store
-- --            | New String
-- --            | Label String
-- --            | IfZero String
-- --            | IfNotZero String
-- --            | GoTo String
-- --            | LT
-- --            | EQ
-- --
-- --
-- -- comp : (exp : Expr) -> List Instr
-- -- comp (Const k) = [Push k]
-- -- comp (Plus x y) = (comp x)++(comp y)++[Add]
-- -- comp (Minus x y) = (comp x)++(comp y)++[Subtract]
-- -- comp (Times x y) = (comp x)++(comp y)++[Multiply]
-- -- comp (Var x) = [RValue x]
-- --
-- -- compB : Memory -> Boolean -> List Instr
-- -- compB mem T = [Push 1]
-- -- compB mem F = [Push 0]
-- -- compB mem (Equals x y) = (comp x)++(comp y) ++ [EQ]
-- -- compB mem (NotEquals x y) = ?aa
-- -- compB mem (LessThan x y) = (comp x)++(comp y) ++ [LT]
-- --
-- --
-- --
-- -- compS : Memory -> (st : Statement) -> List Instr
-- -- compS mem (Initialize x y) = (comp y) ++ [New x]
-- -- compS mem (Update x y) = [LValue x] ++ (comp y) ++ [Store]
-- -- compS mem (If test thencl elsecl) = (compB mem test) ++ [IfZero "L1"] ++ (compS mem thencl) ++ [GoTo "L2"] ++ [Label "L1"] ++ (compS mem elsecl) ++ [Label "L2"]
-- -- compS mem (While test docl) = [GoTo "L2"] ++ [Label "L1"] ++ (compS mem docl) ++ [Label "L2"] ++ (compB mem test) ++ [IfNotZero "L1"]
-- --
-- -- compP : Memory -> (pr: Program) -> List Instr
-- -- compP mem [] = []
-- -- compP mem (x :: xs) = (compS mem x) ++ (compP mem xs)
-- --
-- --
-- --
-- --
-- --
-- --
-- -- Stack : Type
-- -- Stack = List Nat
-- --
-- -- -- TODO change to Maybe Nat
-- -- index_of : Memory -> Nat -> String -> Nat
-- -- index_of [] idx sym = ?aa_1
-- -- index_of (x :: xs) idx sym = let a = (case fst x == sym of
-- --                                            False => index_of xs (idx + 1) sym
-- --                                            True => idx) in a
-- --
-- -- -- TODO - change to look_up
-- -- value_of : Memory -> String -> Nat
-- -- value_of [] y = ?value_of_rhs_1
-- -- value_of (x :: xs) sym = case fst x == sym of
-- --                               False => value_of xs sym
-- --                               True => snd x
-- --
-- --
-- -- update_by_index : Memory -> (pos: Nat) -> Nat -> Memory
-- -- update_by_index [] pos val = []
-- -- update_by_index ((x,y) :: xs) Z val = (x, val) :: xs
-- -- update_by_index (x :: xs) (S k) val = x :: (update_by_index xs k val)
-- --
-- -- add_to_mem : Memory -> String -> Nat -> Memory
-- -- add_to_mem mem sym val = (sym, val) :: mem
-- --
-- --
-- -- -- TODO: change function so that it returns list of all instructions without a certain label
-- -- find_label : (label : String) -> (old : List Instr) -> List Instr
-- -- find_label label [] = []
-- -- find_label label ((Label x) :: xs) = case x == label of
-- --                                           False => find_label label xs
-- --                                           True => xs
-- -- find_label label (_ :: xs) = find_label label xs
-- -- -- example
-- -- -- [Push 4, New "a", Push 1, IfZero "L1", LValue "a", RValue "a", Push 1, Subtract, Store, GoTo "L2", Label "L1", LValue "a", RValue "a", Push 1, Add, Store, Label "L2"]
-- -- -- [LValue "a", RValue "a", Push 1, Add, Store, Label "L2"]
-- --
-- --
-- --
-- -- run : (mem : Memory) ->  (instr:List Instr) -> (stc:Stack) -> Memory
-- -- run mem [] stc = mem
-- -- run mem ((Push k) :: xs) stc = run mem xs (k :: stc)
-- -- run mem (Add :: xs) [] = mem
-- -- run mem (Add :: xs) (x :: y :: ys) = run mem xs (x + y  :: ys)
-- -- run mem (Add :: xs) [x] = mem
-- -- run mem (Subtract :: xs) [] = mem
-- -- run mem (Subtract :: xs) (x :: y :: ys) = run mem xs (minus y x  :: ys)
-- -- run mem (Subtract :: xs) [x] = mem
-- -- run mem (Multiply :: xs) [] = mem
-- -- run mem (Multiply :: xs) (x :: y :: ys) = run mem xs (x * y  :: ys)
-- -- run mem (Multiply :: xs) [x] = mem
-- -- run mem ((LValue x) :: xs) stc = run mem xs ((index_of mem 0 x) :: stc)
-- -- run mem ((RValue x) :: xs) stc = run mem xs ((value_of mem x) :: stc)
-- -- run mem (Store :: xs) [] = mem
-- -- run mem (Store :: xs) (val :: pos :: ys) = run (update_by_index mem pos val) xs ys
-- -- run mem (Store :: xs) [x] = mem
-- -- run mem ((New sym) :: xs) [] = mem
-- -- run mem ((New sym) :: xs) (val :: ys) = run (add_to_mem mem sym val) xs ys
-- -- run mem ((New sym) :: xs) [x] = mem
-- -- run mem ((Label x) :: xs) stc = run mem xs stc
-- -- run mem ((IfZero x) :: xs) (test :: ys) = case test == 0 of
-- --                                                False => run mem xs ys
-- --                                                True => run mem ((GoTo x) :: xs) ys
-- -- run mem ((IfNotZero x) :: xs) (test :: ys) = case test == 1 of
-- --                                                False => run mem xs ys
-- --                                                True => run mem ((GoTo x) :: xs) ys
-- -- run mem ((GoTo x) :: xs) stc = run mem (find_label x xs) stc
-- -- run mem (EQ :: xs) (x :: y :: ys) = case x == y of
-- --                                          False => run mem ((Push 0)::xs) ys
-- --                                          True => run mem ((Push 1)::xs) ys
-- -- run mem (LT :: xs) (x :: y :: ys) = (case compare y x of
-- --                                           LT => run mem ((Push 1)::xs) ys
-- --                                           EQ => run mem ((Push 0)::xs) ys
-- --                                           GT => run mem ((Push 0)::xs) ys)
-- --
-- --
-- --
-- --
--
--
--
--
--
--
--
--
--
--
-- -- How to run:
-- -- evalP (Just []) [(Initialize "a" (Const 4)), (While (LessThan (Var "a") (Const 55)) (Update "a" (Plus (Var "a") (Const 1))))]
-- -- run [] (compP [] [(Initialize "a" (Const 4)), (If (T) (Update "a" (Plus (Var "a") (Const 1))) (Update "a" (Minus (Var "a") (Const 1))))]) []
-- -- run [] (compP [] [(Initialize "a" (Const 4)), (While (LessThan (Var "a") (Const 55)) (Update "a" (Plus (Var "a") (Const 1))))]) []
--
--
-- -- correct : (e : Expr) -> Dec ([eval e] = run (comp e) [])
-- -- correct e = case decEq [eval e] (run (comp e) []) of
-- --                  (Yes prf) => Yes prf
-- --                  (No contra) => No contra
-- --
--
--
-- -- correct e = case checkEqList [eval e] (run (comp e) [])  of
-- --                  Nothing => ?correct_rhs_1
-- --                  (Just (SameList x)) => ?correct_rhs_2



import Data.List
%default total






-- data EqNat : (num : Nat) -> (num2 : Nat) -> Type where
--       Same : (num : Nat) -> EqNat num num
--
-- sameS : (k:Nat) -> (j:Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
-- sameS k k (Same k) = Same (S k)
--
-- checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
-- checkEqNat Z Z = Just (Same 0)
-- checkEqNat Z (S k) = Nothing
-- checkEqNat (S k) Z = Nothing
-- checkEqNat (S k) (S j) = case checkEqNat k j of
--                               Nothing => Nothing
--                               Just eq => Just (sameS _ _ eq)
--
--
-- data EqList : (list1 : List Nat) -> (list2 : List Nat) -> Type where
--   SameList : (list : List Nat) -> EqList list list
--
--
-- sameL :(x: Nat) -> (y: Nat) -> (eqn : EqNat x y) -> (xs : List Nat) -> (ys : List Nat)
--                 -> (eq : EqList xs ys) -> EqList (x :: xs) (y :: ys)
-- sameL y y (Same y) ys ys (SameList ys) = SameList (y :: ys)
--
-- checkEqList : (list1 : List Nat) -> (list2 : List Nat) -> Maybe (EqList list1 list2)
-- checkEqList [] [] = Just (SameList [])
-- checkEqList [] (x :: xs) = Nothing
-- checkEqList (x :: xs) [] = Nothing
-- checkEqList (x :: xs) (y :: ys) = case checkEqList xs ys of
--                                        Nothing => Nothing
--                                        (Just eq) => (case checkEqNat x y of
--                                                           Nothing => Nothing
--                                                           (Just eqn) => Just (sameL x y eqn xs ys eq))

-- --------------------------------------------------------------------------
--
--
-- zeroNotSuc : ([] = (x :: xs)) -> Void
-- zeroNotSuc Refl impossible
--
-- sucNotZero : ((x :: xs) = []) -> Void
-- sucNotZero Refl impossible
--
--
--
-- checkEqList : (list1 : List Nat) -> (list2 : List Nat) -> Dec (list1 = list2)
-- checkEqList [] [] = Yes Refl
-- checkEqList [] (x :: xs) = No zeroNotSuc
-- checkEqList (x :: xs) [] = No sucNotZero
-- checkEqList (x :: xs) (y :: ys) = case decEq x y of
--                                        (Yes prf) => (case checkEqList xs ys of
--                                                           (Yes prf) => Yes (?sdsd_3)
--                                                           (No contra) => No (?sdsd_4))
--                                        (No contra) => No (?sdsd_2)



-- --------------------------------------------------------------------------
data Expr = Const Nat
          | Plus Expr Expr
          | Minus Expr Expr
          | Times Expr Expr
          | Var String

data Boolean = T
             | F
             | Equals Expr Expr
             | NotEquals Expr Expr
             | LessThan Expr Expr
             -- | GreaterThan Expr Expr
             -- | LessEq Expr Expr
             -- | GreaterEq Expr Expr






data Statement = Initialize String Expr
               | Update String Expr
               | If Boolean Statement Statement
               | While Boolean Statement



Memory : Type
Memory = List (String, Nat)


Program : Type
Program = List Statement

get_firsts : Maybe (List (String, Nat)) -> (List String)
get_firsts Nothing = []
get_firsts (Just []) = []
get_firsts (Just (x :: xs)) = (fst x) :: (get_firsts (Just xs))


look_up : String -> Maybe Memory -> Maybe Nat
look_up sym Nothing = Nothing
look_up sym (Just []) = Nothing
look_up sym (Just (x :: xs)) = case fst x == sym of
                                    False => look_up sym (Just xs)
                                    True => Just (snd x)




eval : Maybe Memory -> Expr -> Maybe Nat

eval mem (Const num) = Just num
eval mem (Plus ex1 ex2) = case eval mem ex1 of
                               Nothing => Nothing
                               Just x => case eval mem ex2 of
                                              Nothing => Nothing
                                              Just y => Just (x + y)
eval mem (Minus ex1 ex2) = case eval mem ex1 of
                               Nothing => Nothing
                               Just x => case eval mem ex2 of
                                              Nothing => Nothing
                                              Just y => Just (minus x y)
eval mem (Times ex1 ex2) = case eval mem ex1 of
                               Nothing => Nothing
                               Just x => case eval mem ex2 of
                                              Nothing => Nothing
                                              Just y => Just (x * y)
eval mem (Var sym) = case isElem sym (get_firsts mem) of
                          (Yes prf) => look_up sym mem
                          (No contra) => Nothing



evalB : Maybe Memory -> Boolean -> Bool
evalB mem T = True
evalB mem F = False
evalB mem (Equals x y) = (eval mem x) == (eval mem y)
evalB mem (NotEquals x y) = case (eval mem x) == (eval mem y) of
                              False => True
                              True => False
evalB mem (LessThan x y) = case compare (eval mem x) (eval mem y) of
                            LT => True
                            EQ => False
                            GT => False



update : (old : Memory) -> String -> Nat -> (new : Memory) -> Memory
update [] sym num new = new
update (x :: xs) sym num new = (case fst x == sym of
                                                  False => update xs sym num (x::new)
                                                  True => update xs sym num ((sym, num)::new))



evalS : (mem : Maybe Memory) -> Statement -> Maybe Memory
evalS mem (Initialize sym ex) = case eval mem ex of
                                       Nothing => Nothing
                                       Just a => (case mem of
                                                       Nothing => Nothing
                                                       (Just x) => Just ((sym, a) :: x))

evalS mem (Update sym ex) = case eval mem ex of
                                 Nothing => Nothing
                                 Just a => (case mem of
                                                 Nothing => Nothing
                                                 (Just x) => (case isElem sym (get_firsts (Just x)) of
                                                                   (Yes prf) => Just (update x sym a [])
                                                                   (No contra) => Nothing))


evalS mem (If test thencl elsecl) = case evalB mem test of
                                         False =>  evalS mem elsecl
                                         True => evalS mem thencl

evalS mem (While test docl) = case evalB mem test of
                                   False => mem
                                   True => evalS (evalS mem docl) (While test docl)



evalP : Maybe Memory -> Program -> Maybe Memory
evalP mem [] = mem
evalP mem (x :: xs) = case evalS mem x of
                           Nothing => Nothing
                           Just a => evalP (Just a) xs

------Stack Machine-----------------------------------------------------------------


data Instr = Push Nat
           | Add
           | Subtract
           | Multiply
           | LValue String
           | RValue String
           | Store
           | New String
           | Label Nat
           | IfZero Nat
           | IfNotZero Nat
           | GoTo Nat
           | LT
           | EQ


comp : (exp : Expr) -> List Instr
comp (Const k) = [Push k]
comp (Plus x y) = (comp x)++(comp y)++[Add]
comp (Minus x y) = (comp x)++(comp y)++[Subtract]
comp (Times x y) = (comp x)++(comp y)++[Multiply]
comp (Var x) = [RValue x]

compB : Memory -> Boolean -> List Instr
compB mem T = [Push 1]
compB mem F = [Push 0]
compB mem (Equals x y) = (comp x)++(comp y) ++ [EQ]
compB mem (NotEquals x y) = ?aa
compB mem (LessThan x y) = (comp x)++(comp y) ++ [LT]






-- compS : Memory -> (st : Statement) -> List Instr
-- compS mem (Initialize x y) = (comp y) ++ [New x]
-- compS mem (Update x y) = [LValue x] ++ (comp y) ++ [Store]
-- compS mem (If test thencl elsecl) = (compB mem test) ++ [IfZero "L1"] ++ (compS mem thencl) ++ [GoTo "L2"] ++ [Label "L1"] ++ (compS mem elsecl) ++ [Label "L2"]
-- compS mem (While test docl) = [GoTo "L2"] ++ [Label "L1"] ++ (compS mem docl) ++ [Label "L2"] ++ (compB mem test) ++ [IfNotZero "L1"]

increment_label : Nat -> Nat
increment_label val = val + 1


compS : Memory -> (label : Nat) -> (st : Statement) -> List Instr
compS mem label (Initialize x y) = (comp y) ++ [New x]
compS mem label (Update x y) = [LValue x] ++ (comp y) ++ [Store]
compS mem label (If test thencl elsecl) = (compB mem test) ++ [IfZero label] ++ (compS mem (increment_label label) thencl) ++ [GoTo (increment_label (increment_label label))] ++ [Label label] ++ (compS mem (increment_label label) elsecl) ++ [Label (increment_label (increment_label label))]
compS mem label (While test docl) = [GoTo (increment_label label)] ++ [Label label] ++ (compS mem (increment_label label) docl) ++ [Label (increment_label label)] ++ (compB mem test) ++ [IfNotZero label]

compP : Memory -> (pr: Program) -> List Instr
compP mem [] = []
compP mem (x :: xs) = (compS mem 0 x) ++ (compP mem xs)






Stack : Type
Stack = List Nat

-- TODO change to Maybe Nat
index_of : Memory -> Nat -> String -> Nat
index_of [] idx sym = ?aa_1
index_of (x :: xs) idx sym = let a = (case fst x == sym of
                                           False => index_of xs (idx + 1) sym
                                           True => idx) in a

-- TODO - change to look_up
value_of : Memory -> String -> Nat
value_of [] y = ?value_of_rhs_1
value_of (x :: xs) sym = case fst x == sym of
                              False => value_of xs sym
                              True => snd x


update_by_index : Memory -> (pos: Nat) -> Nat -> Memory
update_by_index [] pos val = []
update_by_index ((x,y) :: xs) Z val = (x, val) :: xs
update_by_index (x :: xs) (S k) val = x :: (update_by_index xs k val)

add_to_mem : Memory -> String -> Nat -> Memory
add_to_mem mem sym val = (sym, val) :: mem


-- TODO: change function so that it returns list of all instructions without a certain label
find_label : (label : Nat) -> (all : List Instr) -> List Instr
find_label label [] = []
find_label label ((Label x) :: xs) = case x == label of
                                          False => find_label label xs
                                          True => xs
find_label label (_ :: xs) = find_label label xs
-- example
-- [Push 4, New "a", Push 1, IfZero "L1", LValue "a", RValue "a", Push 1, Subtract, Store, GoTo "L2", Label "L1", LValue "a", RValue "a", Push 1, Add, Store, Label "L2"]
-- [LValue "a", RValue "a", Push 1, Add, Store, Label "L2"]



run : (mem : Memory) -> (all : List Instr) -> (instr:List Instr) -> (stc:Stack) -> Memory
run mem all [] stc = mem
run mem all ((Push k) :: xs) stc = run mem all xs (k :: stc)
run mem all (Add :: xs) [] = mem
run mem all (Add :: xs) (x :: y :: ys) = run mem all xs (x + y  :: ys)
run mem all (Add :: xs) [x] = mem
run mem all (Subtract :: xs) [] = mem
run mem all (Subtract :: xs) (x :: y :: ys) = run mem all xs (minus y x  :: ys)
run mem all (Subtract :: xs) [x] = mem
run mem all (Multiply :: xs) [] = mem
run mem all (Multiply :: xs) (x :: y :: ys) = run mem all xs (x * y  :: ys)
run mem all (Multiply :: xs) [x] = mem
run mem all ((LValue x) :: xs) stc = run mem all xs ((index_of mem 0 x) :: stc)
run mem all ((RValue x) :: xs) stc = run mem all xs ((value_of mem x) :: stc)
run mem all (Store :: xs) [] = mem
run mem all (Store :: xs) (val :: pos :: ys) = run (update_by_index mem pos val) all xs ys
run mem all (Store :: xs) [x] = mem
run mem all ((New sym) :: xs) [] = mem
run mem all ((New sym) :: xs) (val :: ys) = run (add_to_mem mem sym val) all xs ys
run mem all ((New sym) :: xs) [x] = mem
run mem all ((Label x) :: xs) stc = run mem all xs stc
run mem all ((IfZero x) :: xs) (test :: ys) = case test == 0 of
                                               False => run mem all xs ys
                                               True => run mem all ((GoTo x) :: xs) ys
run mem all ((IfNotZero x) :: xs) (test :: ys) = case test == 1 of
                                               False => run mem all xs ys
                                               True => run mem all ((GoTo x) :: xs) ys
run mem all ((GoTo x) :: xs) stc = run mem all (find_label x all) stc
run mem all (EQ :: xs) (x :: y :: ys) = case x == y of
                                         False => run mem all ((Push 0)::xs) ys
                                         True => run mem all ((Push 1)::xs) ys
run mem all (LT :: xs) (x :: y :: ys) = (case compare y x of
                                          LT => run mem all ((Push 1)::xs) ys
                                          EQ => run mem all ((Push 0)::xs) ys
                                          GT => run mem all ((Push 0)::xs) ys)














-- How to run:
-- evalP (Just []) [(Initialize "a" (Const 4)), (While (LessThan (Var "a") (Const 55)) (Update "a" (Plus (Var "a") (Const 1))))]
-- run [] (compP [] [(Initialize "a" (Const 4)), (If (T) (If (T) (Update "a" (Plus (Var "a") (Const 1))) (Update "a" (Plus (Var "a") (Const 2)))) (Update "a" (Plus (Var "a") (Const 3))) )]) []

-- (Update "a" (Plus (Var "a") (Const 1))) (Update "a" (Minus (Var "a") (Const 1))))]) []
-- run [] (compP [] [(Initialize "a" (Const 4)), (While (LessThan (Var "a") (Const 55)) (Update "a" (Plus (Var "a") (Const 1))))]) []


-- correct : (e : Expr) -> Dec ([eval e] = run (comp e) [])
-- correct e = case decEq [eval e] (run (comp e) []) of
--                  (Yes prf) => Yes prf
--                  (No contra) => No contra
--


-- correct e = case checkEqList [eval e] (run (comp e) [])  of
--                  Nothing => ?correct_rhs_1
--                  (Just (SameList x)) => ?correct_rhs_2
