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


eval : Expr -> Nat
eval (Const num) = num
eval (Plus ex1 ex2) = eval ex1 + eval ex2


data Instr = Push Nat
           | Add

comp : (exp : Expr) -> List Instr
comp (Const k) = [Push k]
comp (Plus x y) = (comp x)++(comp y)++[Add]

Stack : Type
Stack = List Nat


run : (instr:List Instr) -> (stc:Stack) -> Stack
run [] stc = stc
run ((Push k) :: xs) stc = run xs (k :: stc)
run (Add :: xs) [] = []
run (Add :: xs) (x :: y :: ys) = run xs (x + y  :: ys)
run (Add :: xs) [x] = [x]

correct : (e : Expr) -> Dec ([eval e] = run (comp e) [])
-- correct e = case checkEqList [eval e] (run (comp e) [])  of
--                  Nothing => ?correct_rhs_1
--                  (Just (SameList x)) => ?correct_rhs_2


correct e = case decEq [eval e] (run (comp e) []) of
                 (Yes prf) => Yes prf
                 (No contra) => No contra
