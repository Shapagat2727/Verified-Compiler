module project
import Data.List
import Data.Vect
%default total



-- memory type to store variables and corresponding values
public export
Memory : Type
Memory = List (String, Nat)


-- returns list of all variables in memory
export
get_firsts : Memory -> (List String)
get_firsts [] = []
get_firsts (x :: xs) = (fst x) :: (get_firsts xs)

-- expression type
public export
data Expr: Type where
    Const: Nat -> Expr
    Plus : Expr -> Expr -> Expr
    Minus: Expr -> Expr -> Expr
    Times: Expr -> Expr -> Expr
    Over : Expr -> Expr -> Expr
    Var: (name : String) -> (firsts: List String) -> (Elem name firsts) -> Expr
    Access: (name : String) -> (index : Nat) -> (firsts: List String)->(Elem (name ++ (show index)) firsts) -> Expr

-- array type
public export
data Array: Type where
    ArrayNat: (length : Nat) -> Array


-- boolean type
public export
data Boolean = T
             | F
             | Equals Expr Expr
             | LessThan Expr Expr


-- type statement
public export
data Statement: Type where
    Initialize : (name : Vect (S k) Char) -> Expr -> Statement
    Update: String -> Expr -> Statement
    If: Boolean -> Statement -> Statement -> Statement
    While: Boolean -> Statement -> Statement
    InitArray: String -> Array -> Statement
    UpdateArray: (name : String) -> (index : Nat) -> (new: Expr) -> (firsts: List String)->(Elem (name ++ (show index)) firsts) -> Statement

-- type program
public export
Program : Type
Program = List Statement

-----------------------------------------------------------------------

-- returns a value of variable in memory
export
look_up : String -> Memory -> Maybe Nat
look_up x [] = Nothing
look_up x (y :: ys) = case fst y == x of
                             False => look_up x ys
                             True => Just (snd y)


-- evaluates an expression
export
eval : Memory -> Expr -> Maybe Nat
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
eval mem (Over ex1 ex2) = case eval mem ex1 of
                               Nothing => Nothing
                               Just x => (case eval mem ex2 of
                                               Nothing => Nothing
                                               Just y => assert_total (Just (divNat x y)))
eval mem (Var sym memory prf) = look_up sym mem
eval mem (Access arr ind memory prf) = look_up (arr ++ (show ind)) mem


-- evaluates boolean
export
evalB : Memory -> Boolean -> Bool
evalB mem T = True
evalB mem F = False
evalB mem (Equals x y) = (eval mem x) == (eval mem y)
evalB mem (LessThan x y) = case compare (eval mem x) (eval mem y) of
                            LT => True
                            EQ => False
                            GT => False

-- updates variable with a new value
export
update : (old : Memory) -> String -> Nat -> (new : Memory) -> Memory
update [] sym num new = new
update (x :: xs) sym num new = (case fst x == sym of
                                                  False => update xs sym num (x::new)
                                                  True => update xs sym num ((sym, num)::new))


-- adds a variable and a corresponding value to memory
export
add_to_mem : Memory -> String -> Nat -> Memory
add_to_mem mem sym val = (sym, val) :: mem

-- evaluates a statement

fromVect : (xs : Vect n Char) -> String
fromVect [] = ""
fromVect (x :: xs) = (singleton x) ++ (fromVect xs)

export
evalS : (mem : Memory) -> Statement -> Memory
evalS mem (Initialize sym ex) = case eval mem ex of
                                     Nothing => mem
                                     (Just x) => add_to_mem mem (fromVect sym) x
evalS mem (Update sym ex) = case eval mem ex of
                                 Nothing => mem
                                 (Just x) => (case isElem sym (get_firsts mem) of
                                                   (Yes prf) => update mem sym x []
                                                   (No contra) => mem)
evalS mem (If test thencl elsecl) = case evalB mem test of
                                         False =>  evalS mem elsecl
                                         True => evalS mem thencl
evalS mem (While test docl) = case evalB mem test of
                                   False => mem
                                   True => assert_total (evalS (evalS mem docl) (While test docl))
evalS mem (InitArray sym (ArrayNat Z )) = mem
evalS mem (InitArray sym (ArrayNat (S len))) = assert_total (evalS ((sym ++ (show len), 0) :: mem) (InitArray sym (ArrayNat len)))
evalS mem (UpdateArray sym ind ex firsts prf) = case eval mem ex of
                                                     Nothing => mem
                                                     (Just x) => update mem (sym ++ (show ind)) x []


-- evaluates a program
export
evalP : Memory -> Program -> Memory
evalP mem [] = mem
evalP mem (x :: xs) = evalP (evalS mem x) xs


------STACK - MACHINE -----------------------------------------------------------------

-- type instruction
public export
data Instr = Push Nat
           | Add
           | Subtract
           | Multiply
           | Divide
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

-- compiles an expression
export
comp : (exp : Expr) -> List Instr
comp (Const k) = [Push k]
comp (Plus x y) = (comp x)++(comp y)++[Add]
comp (Minus x y) = (comp x)++(comp y)++[Subtract]
comp (Times x y) = (comp x)++(comp y)++[Multiply]
comp (Over ex1 ex2) = (comp ex1) ++ (comp ex2) ++ [Divide]
comp (Var x y z) = [RValue x]
comp (Access x y z p) = [RValue (x ++ show (y))]

-- compiles a boolean
export
compB : Memory -> Boolean -> List Instr
compB mem T = [Push 1]
compB mem F = [Push 0]
compB mem (Equals x y) = (comp x)++(comp y) ++ [EQ]
compB mem (LessThan x y) = (comp x)++(comp y) ++ [LT]

-- increments a label by 1
export
increment : Nat -> Nat
increment val = val + 1

-- compiles a statement
export
compS : Memory -> (label : Nat) -> (st : Statement) -> List Instr
compS mem label (Initialize x y) = (comp y) ++ [New (fromVect x)]
compS mem label (Update x y) = [LValue x] ++ (comp y) ++ [Store]
compS mem label (If test thencl elsecl) = (compB mem test) ++ [IfZero (increment label)] ++ (compS mem (increment (increment label)) thencl) ++ [GoTo (increment (increment label))] ++ [Label (increment label)] ++ (compS mem (increment (increment label)) elsecl) ++ [Label (increment (increment label))]
compS mem label (While test docl) = [GoTo (increment (increment label))] ++ [Label (increment label)] ++ (compS mem (increment (increment label)) docl) ++ [Label (increment (increment label))] ++ (compB mem test) ++ [IfNotZero (increment label)]
compS mem label (InitArray sym (ArrayNat Z)) = []
compS mem label (InitArray sym (ArrayNat (S k))) = assert_total ([Push 0] ++ [New (sym ++ (show k))] ++ (compS mem label (InitArray sym (ArrayNat (k)))))
compS mem label (UpdateArray sym ind new firsts prf) = [LValue (sym ++ (show ind))] ++ (comp new) ++ [Store]

-- compiles a program
export
compP : Memory -> (pr: Program) -> List Instr
compP mem [] = []
compP mem (x :: xs) = (compS mem 0 x) ++ (compP mem xs)


-- type stack
public export
Stack : Type
Stack = List Nat

-- returns index of a variable in memory
export
index_of : Memory -> (idx : Nat) -> (sym : String) -> Maybe Nat
index_of [] idx sym = Nothing
index_of (x :: xs) idx sym = case fst x == sym of
                                  False => index_of xs (idx + 1) sym
                                  True => Just idx



-- update a value of a variable at certain index
export
update_by_index : Memory -> (pos: Nat) -> Nat -> Memory
update_by_index [] pos val = []
update_by_index ((x,y) :: xs) Z val = (x, val) :: xs
update_by_index (x :: xs) (S k) val = x :: (update_by_index xs k val)


-- returns list of instructions after a certain label
export
find_label : (label : Nat) -> (all : List Instr) -> List Instr
find_label label [] = []
find_label label ((Label x) :: xs) = case x == label of
                                          False => find_label label xs
                                          True => xs
find_label label (_ :: xs) = find_label label xs


-- runs instructions
export
run : (mem : Memory) -> (all : List Instr) -> (instr:List Instr) -> (stc:Stack) -> Memory
run mem all [] stc = mem
run mem all ((Push k) :: xs) stc = assert_total (run mem all xs (k :: stc))
run mem all (Add :: xs) [] = mem
run mem all (Add :: xs) (x :: y :: ys) = assert_total (run mem all xs (x + y :: ys))
run mem all (Add :: xs) [x] = mem
run mem all (Subtract :: xs) [] = mem
run mem all (Subtract :: xs) (x :: y :: ys) = assert_total (run mem all xs (minus y x  :: ys))
run mem all (Subtract :: xs) [x] = mem
run mem all (Multiply :: xs) [] = mem
run mem all (Multiply :: xs) (x :: y :: ys) = assert_total (run mem all xs (x * y  :: ys))
run mem all (Multiply :: xs) [x] = mem
run mem all (Divide :: xs) [] = mem
run mem all (Divide :: xs) [x] = mem
run mem all (Divide :: xs) (x :: y :: ys) = assert_total (run mem all xs (divNat y x :: ys))
run mem all ((LValue x) :: xs) stc = case isElem x (get_firsts mem) of
                                          Yes prf => (case assert_total (index_of mem 0 x) of
                                                             Just x => assert_total (run mem all xs (x :: stc))
                                                             Nothing => mem)
                                          No contra => mem
run mem all ((RValue x) :: xs) stc = case look_up x mem of
                                          Just a => assert_total (run mem all xs (a :: stc))
                                          Nothing => mem
run mem all (Store :: xs) [] = mem
run mem all (Store :: xs) (val :: pos :: ys) = run (update_by_index mem pos val) all xs ys
run mem all (Store :: xs) [x] = mem
run mem all ((New sym) :: xs) [] = mem
run mem all ((New sym) :: xs) (val :: ys) = run (add_to_mem mem sym val) all xs ys
run mem all ((New sym) :: xs) [x] = mem
run mem all ((Label x) :: xs) stc = run mem all xs stc
run mem all ((IfZero x) :: xs) [] =  mem
run mem all ((IfZero x) :: xs) (test :: ys) = case test == 0 of
                                               False => run mem all xs ys
                                               True => run mem all ((GoTo x) :: xs) ys
run mem all ((IfNotZero x) :: xs) [] =  mem
run mem all ((IfNotZero x) :: xs) (test :: ys) = case test == 1 of
                                               False => run mem all xs ys
                                               True => run mem all ((GoTo x) :: xs) ys
run mem all ((GoTo x) :: xs) stc = assert_total (run mem all (find_label x all) stc)
run mem all (EQ :: xs) [] =  mem
run mem all (EQ :: xs) [x] = mem
run mem all (EQ :: xs) (x :: y :: ys) = case x == y of
                                         False => run mem all ((Push 0)::xs) ys
                                         True => run mem all ((Push 1)::xs) ys
run mem all (LT :: xs) [] =  mem
run mem all (LT :: xs) [x] =  mem
run mem all (LT :: xs) (x :: y :: ys) = (case compare y x of
                                          LT => run mem all ((Push 1)::xs) ys
                                          EQ => run mem all ((Push 0)::xs) ys
                                          GT => run mem all ((Push 0)::xs) ys)
