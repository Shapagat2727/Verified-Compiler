module Main
import Data.List
import project


main : IO ()
-- initialization

main = do     let mem = (the Memory) []
              -- initialization

              let program = (the Program) [(Initialize "a" (Const 6) (isValidString "a"))]
              let instr = compP mem program
              putStr ("Test 1 : ")
              putStr (show ((run mem instr instr []) == [("a", 6)]))
              putStrLn (show ((evalP mem program) == [("a", 6)]))

              -- initialization wrong
              let program = [(Initialize "" (Const 6) (isValidString ""))]
              let instr = compP mem program
              putStr ("Test 2 : ")
              putStr (show ((run mem instr instr []) == []))
              putStrLn (show ((evalP mem program) == []))

              -- addition
              let program = (the Program) [(Initialize "a" (Const 6) (isValidString "a")), (Initialize "b" (Const 4) (isValidString "b")), (Initialize "c" (Plus (Var "b" [("b"), ("a")] (Here)) (Var "a" [("b"), ("a")] (There Here))) (isValidString "c"))]
              let instr = compP mem program
              putStr ("Test 3 : ")
              putStr(show ((run mem instr instr []) == [("c", 10), ("b", 4), ("a", 6)]))
              putStrLn (show ((evalP mem program) == [("c", 10), ("b", 4), ("a", 6)]))

              -- triple if true true false
              let program = (the Program) [(Initialize "a" (Const 6) (isValidString "a")), (Initialize "b" (Const 4) (isValidString "b")), (If (T) (If (T) (If (F) (Initialize "c" (Times (Var "a" [("b"), ("a")] (There Here)) (Var "b" [("b"), ("a")] (Here))) (isValidString "c")) (Initialize "c" (Const 1) (isValidString "c"))) (Initialize "c" (Const 2) (isValidString "c"))) (Initialize "c" (Const 3) (isValidString "c")))]
              let instr = compP mem program
              putStr ("Test 4 : ")
              putStr (show ((run mem instr instr []) == [("c", 1), ("b", 4), ("a", 6)]))
              putStrLn (show ((evalP mem program) == [("c", 1), ("b", 4), ("a", 6)]))

              -- while loop
              let program = (the Program) [(Initialize "a" (Const 6) (isValidString "a")), (Initialize "b" (Const 4) (isValidString "b")), (While (LessThan (Var "b" [("b"), ("a")] (Here)) (Var "a" [("b"), ("a")] (There Here))) (Update "b" (Plus (Var "b" [("b"), ("a")] (Here)) (Const 1))))]
              let instr = compP mem program
              putStr ("Test 5 : ")
              putStr (show ((run mem instr instr []) == [("b", 6), ("a", 6)]))
              putStrLn (show ((evalP mem program) == [("b", 6), ("a", 6)]))

              -- initialize array
              let program = (the Program) [(InitArray "arr" (ArrayNat 5))]
              let instr = compP mem program
              putStr ("Test 6 : ")
              putStr (show ((run mem instr instr []) == [("arr0", 0), ("arr1", 0), ("arr2", 0), ("arr3", 0), ("arr4", 0)]))
              putStrLn (show ((evalP mem program) == [("arr0", 0), ("arr1", 0), ("arr2", 0), ("arr3", 0), ("arr4", 0)]))

              --access array
              let program = (the Program) [(InitArray "arr" (ArrayNat 5)), (Initialize "a" (Access "arr" 0 ["arr0", "arr1", "arr2", "arr3", "arr4"] (Here)) (isValidString "a"))]
              let instr = compP mem program
              putStr ("Test 7 : ")
              putStr (show ((run mem instr instr []) == [("a", 0), ("arr0", 0), ("arr1", 0), ("arr2", 0), ("arr3", 0), ("arr4", 0)]))
              putStrLn (show ((evalP mem program) == [("a", 0), ("arr0", 0), ("arr1", 0), ("arr2", 0), ("arr3", 0), ("arr4", 0)]))

              --update array
              let program = (the Program) [(InitArray "arr" (ArrayNat 5)), (UpdateArray "arr" 0 (Const 6) ["arr0", "arr1", "arr2", "arr3", "arr4"] (Here))]
              let instr = compP mem program
              putStr ("Test 8 : ")
              putStr (show ((run mem instr instr []) == [("arr0", 6), ("arr1", 0), ("arr2", 0), ("arr3", 0), ("arr4", 0)]))
              putStrLn (show ((evalP mem program) == [("arr4", 0), ("arr3", 0), ("arr2", 0), ("arr1", 0), ("arr0", 6)]))
