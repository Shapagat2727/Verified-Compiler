module Main
import Data.List
import project


-- test: List (String, Nat) -> IO()
-- test [] = ?test_rhs_1
-- test (x :: xs) = ?test_rhs_2


main : IO ()

          -- initialization
main = do let instr = compP [] [(Initialize "a" (Const 6))]
          putStr ("Test 1 : ")
          putStrLn (show ((run [] instr instr []) == [("a", 6)]))


          -- addition
          let mem = (the Memory) []
          let instr = compP mem [(Initialize "a" (Const 6)), (Initialize "b" (Const 4)), (Initialize "c" (Plus (Var "a" mem (isElem "a" (get_firsts mem))) (Var "b" mem (isElem "b" (get_firsts mem)))))]
          putStr ("Test 2 : ")
          putStrLn (show ((run [] instr instr []) == [("c", 10), ("b", 4), ("a", 6)]))

          -- subtraction
          let instr = compP [] [(Initialize "a" (Const 6)), (Initialize "b" (Const 4)), (Initialize "c" (Minus (Var "a" mem (isElem "a" (get_firsts mem))) (Var "b" mem (isElem "b" (get_firsts mem)))))]
          putStr ("Test 3 : ")
          putStrLn (show ((run [] instr instr []) == [("c", 2), ("b", 4), ("a", 6)]))

          -- multiplication
          let instr = compP [] [(Initialize "a" (Const 6)), (Initialize "b" (Const 4)), (Initialize "c" (Times (Var "a" mem (isElem "a" (get_firsts mem))) (Var "b" mem (isElem "b" (get_firsts mem)))))]
          putStr ("Test 4 : ")
          putStrLn (show ((run [] instr instr []) == [("c", 24), ("b", 4), ("a", 6)]))

          -- single if true
          let instr = compP [] [(Initialize "a" (Const 6)), (Initialize "b" (Const 4)), (If (T) (Initialize "c" (Times (Var "a" mem (isElem "a" (get_firsts mem))) (Var "b" mem (isElem "b" (get_firsts mem))))) (Initialize "c" (Const 3)))]
          putStr ("Test 5 : ")
          putStrLn (show ((run [] instr instr []) == [("c", 24), ("b", 4), ("a", 6)]))

          -- single if false
          let instr = compP [] [(Initialize "a" (Const 6)), (Initialize "b" (Const 4)), (If (F) (Initialize "c" (Times (Var "a" mem (isElem "a" (get_firsts mem))) (Var "b" mem (isElem "b" (get_firsts mem))))) (Initialize "c" (Const 3)))]
          putStr ("Test 6 : ")
          putStrLn (show ((run [] instr instr []) == [("c", 3), ("b", 4), ("a", 6)]))

          -- double if true true
          let instr = compP [] [(Initialize "a" (Const 6)), (Initialize "b" (Const 4)), (If (T) (If (T) (Initialize "c" (Times (Var "a" mem (isElem "a" (get_firsts mem))) (Var "b" mem (isElem "b" (get_firsts mem))))) (Initialize "c" (Const 2))) (Initialize "c" (Const 3)))]
          putStr ("Test 7 : ")
          putStrLn (show ((run [] instr instr []) == [("c", 24), ("b", 4), ("a", 6)]))

          -- double if false true
          let instr = compP [] [(Initialize "a" (Const 6)), (Initialize "b" (Const 4)), (If (F) (If (T) (Initialize "c" (Times (Var "a" mem (isElem "a" (get_firsts mem))) (Var "b" mem (isElem "b" (get_firsts mem))))) (Initialize "c" (Const 2))) (Initialize "c" (Const 3)))]
          putStr ("Test 8 : ")
          putStrLn (show ((run [] instr instr []) == [("c", 3), ("b", 4), ("a", 6)]))

          -- double if true false
          let instr = compP [] [(Initialize "a" (Const 6)), (Initialize "b" (Const 4)), (If (T) (If (F) (Initialize "c" (Times (Var "a" mem (isElem "a" (get_firsts mem))) (Var "b" mem (isElem "b" (get_firsts mem))))) (Initialize "c" (Const 2))) (Initialize "c" (Const 3)))]
          putStr ("Test 9 : ")
          putStrLn (show ((run [] instr instr []) == [("c", 2), ("b", 4), ("a", 6)]))

          -- triple if true true true
          let instr = compP [] [(Initialize "a" (Const 6)), (Initialize "b" (Const 4)), (If (T) (If (T) (If (T) (Initialize "c" (Times (Var "a" mem (isElem "a" (get_firsts mem))) (Var "b" mem (isElem "b" (get_firsts mem))))) (Initialize "c" (Const 1))) (Initialize "c" (Const 2))) (Initialize "c" (Const 3)))]
          putStr ("Test 10 : ")
          putStrLn (show ((run [] instr instr []) == [("c", 24), ("b", 4), ("a", 6)]))

          -- triple if false true true
          let instr = compP [] [(Initialize "a" (Const 6)), (Initialize "b" (Const 4)), (If (F) (If (T) (If (T) (Initialize "c" (Times (Var "a" mem (isElem "a" (get_firsts mem))) (Var "b" mem (isElem "b" (get_firsts mem))))) (Initialize "c" (Const 1))) (Initialize "c" (Const 2))) (Initialize "c" (Const 3)))]
          putStr ("Test 11 : ")
          putStrLn (show ((run [] instr instr []) == [("c", 3), ("b", 4), ("a", 6)]))

          -- triple if true false true
          let instr = compP [] [(Initialize "a" (Const 6)), (Initialize "b" (Const 4)), (If (T) (If (F) (If (T) (Initialize "c" (Times (Var "a" mem (isElem "a" (get_firsts mem))) (Var "b" mem (isElem "b" (get_firsts mem))))) (Initialize "c" (Const 1))) (Initialize "c" (Const 2))) (Initialize "c" (Const 3)))]
          putStr ("Test 12 : ")
          putStrLn (show ((run [] instr instr []) == [("c", 2), ("b", 4), ("a", 6)]))

          -- triple if true true false
          let instr = compP [] [(Initialize "a" (Const 6)), (Initialize "b" (Const 4)), (If (T) (If (T) (If (F) (Initialize "c" (Times (Var "a" mem (isElem "a" (get_firsts mem))) (Var "b" mem (isElem "b" (get_firsts mem))))) (Initialize "c" (Const 1))) (Initialize "c" (Const 2))) (Initialize "c" (Const 3)))]
          putStr ("Test 13 : ")
          putStrLn (show ((run [] instr instr []) == [("c", 1), ("b", 4), ("a", 6)]))

          -- while loop
          let instr = compP [] [(Initialize "a" (Const 6)), (Initialize "b" (Const 4)), (While (LessThan (Var "b" mem (isElem "b" (get_firsts mem))) (Var "a" mem (isElem "a" (get_firsts mem)))) (Update "b" (Plus (Var "b" mem (isElem "b" (get_firsts mem))) (Const 1))))]
          putStr ("Test 14 : ")
          putStrLn (show ((run [] instr instr []) == [("b", 6), ("a", 6)]))

          let instr = compP [] [(Initialize "a" (Const 6)), (Update "a" (Const 5))]
          putStr ("Test 15 : ")
          putStrLn (show ((run [] instr instr []) == [("a", 5)]))
