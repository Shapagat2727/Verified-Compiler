%default total

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

correct : (e : Expr) -> ([eval e] = run (comp e) [])
correct e = ?correct_rhs
