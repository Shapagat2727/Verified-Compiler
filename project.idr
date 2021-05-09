module project
import Data.List
-- %default total

public export
data Expr = Const Nat
          | Plus Expr Expr
          | Minus Expr Expr
          | Times Expr Expr
          | Var String

public export
data Boolean = T
             | F
             | Equals Expr Expr
             | LessThan Expr Expr

public export
data Statement = Initialize String Expr
               | Update String Expr
               | If Boolean Statement Statement
               | While Boolean Statement


public export
Memory : Type
Memory = List (String, Nat)

public export
Program : Type
Program = List Statement

-----------------------------------------------------------------------
export
get_firsts : Maybe Memory -> (List String)
get_firsts Nothing = []
get_firsts (Just []) = []
get_firsts (Just (x :: xs)) = (fst x) :: (get_firsts (Just xs))

export
look_up : String -> Maybe Memory -> Maybe Nat
look_up sym Nothing = Nothing
look_up sym (Just []) = Nothing
look_up sym (Just (x :: xs)) = case fst x == sym of
                                    False => look_up sym (Just xs)
                                    True => Just (snd x)



export
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


export
evalB : Maybe Memory -> Boolean -> Bool
evalB mem T = True
evalB mem F = False
evalB mem (Equals x y) = (eval mem x) == (eval mem y)
evalB mem (LessThan x y) = case compare (eval mem x) (eval mem y) of
                            LT => True
                            EQ => False
                            GT => False


export
update : (old : Memory) -> String -> Nat -> (new : Memory) -> Memory
update [] sym num new = new
update (x :: xs) sym num new = (case fst x == sym of
                                                  False => update xs sym num (x::new)
                                                  True => update xs sym num ((sym, num)::new))


export
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


export
evalP : Maybe Memory -> Program -> Maybe Memory
evalP mem [] = mem
evalP mem (x :: xs) = case evalS mem x of
                           Nothing => Nothing
                           Just a => evalP (Just a) xs

------Stack Machine-----------------------------------------------------------------

public export
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

export
comp : (exp : Expr) -> List Instr
comp (Const k) = [Push k]
comp (Plus x y) = (comp x)++(comp y)++[Add]
comp (Minus x y) = (comp x)++(comp y)++[Subtract]
comp (Times x y) = (comp x)++(comp y)++[Multiply]
comp (Var x) = [RValue x]

export
compB : Memory -> Boolean -> List Instr
compB mem T = [Push 1]
compB mem F = [Push 0]
compB mem (Equals x y) = (comp x)++(comp y) ++ [EQ]
compB mem (LessThan x y) = (comp x)++(comp y) ++ [LT]

export
increment : Nat -> Nat
increment val = val + 1

export
compS : Memory -> (label : Nat) -> (st : Statement) -> List Instr
compS mem label (Initialize x y) = (comp y) ++ [New x]
compS mem label (Update x y) = [LValue x] ++ (comp y) ++ [Store]
compS mem label (If test thencl elsecl) = (compB mem test) ++ [IfZero (increment label)] ++ (compS mem (increment (increment label)) thencl) ++ [GoTo (increment (increment label))] ++ [Label (increment label)] ++ (compS mem (increment (increment label)) elsecl) ++ [Label (increment (increment label))]
compS mem label (While test docl) = [GoTo (increment (increment label))] ++ [Label (increment label)] ++ (compS mem (increment (increment label)) docl) ++ [Label (increment (increment label))] ++ (compB mem test) ++ [IfNotZero (increment label)]

export
compP : Memory -> (pr: Program) -> List Instr
compP mem [] = []
compP mem (x :: xs) = (compS mem 0 x) ++ (compP mem xs)





public export
Stack : Type
Stack = List Nat

export
index_of : Memory -> Nat -> String -> Nat
index_of [] idx sym = ?aa_1
index_of (x :: xs) idx sym = case fst x == sym of
                                  False => index_of xs (idx + 1) sym
                                  True => idx

export
value_of : Memory -> String -> Nat
value_of [] y = ?value_of_rhs_1
value_of (x :: xs) sym = case fst x == sym of
                              False => value_of xs sym
                              True => snd x

export
update_by_index : Memory -> (pos: Nat) -> Nat -> Memory
update_by_index [] pos val = []
update_by_index ((x,y) :: xs) Z val = (x, val) :: xs
update_by_index (x :: xs) (S k) val = x :: (update_by_index xs k val)

export
add_to_mem : Memory -> String -> Nat -> Memory
add_to_mem mem sym val = (sym, val) :: mem


export
find_label : (label : Nat) -> (all : List Instr) -> List Instr
find_label label [] = []
find_label label ((Label x) :: xs) = case x == label of
                                          False => find_label label xs
                                          True => xs
find_label label (_ :: xs) = find_label label xs


export
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
run mem all ((LValue x) :: xs) stc = case isElem x (get_firsts (Just mem))  of
                                          (Yes prf) => run mem all xs ((index_of mem 0 x) :: stc)
                                          (No contra) => mem
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
