module Main
import Data.List
import Data.Vect
import project


main : IO ()

main = do     let mem = (the Memory) []
              -- initialization

              let program = (the Program) [(Initialize (fromList (unpack "a")) (Const 6))]
              let instr = compP mem program
              putStr ("Test 1 : ")
              putStr (show ((run mem instr instr []) == [("a", 6)]))
              putStrLn (show ((evalP mem program) == [("a", 6)]))


              -- addition
              let program = (the Program) [(Initialize (fromList (unpack "a")) (Const 6)), (Initialize (fromList (unpack "b")) (Const 4)), (Initialize (fromList (unpack "c")) (Plus (Var "b" [("b"), ("a")] (Here)) (Var "a" [("b"), ("a")] (There Here))))]
              let instr = compP mem program
              putStr ("Test 2.1 : ")
              putStr(show ((run mem instr instr []) == [("c", 10), ("b", 4), ("a", 6)]))
              putStrLn (show ((evalP mem program) == [("c", 10), ("b", 4), ("a", 6)]))

              -- division
              let program = (the Program) [(Initialize (fromList (unpack "a")) (Const 3)), (Initialize (fromList (unpack "b")) (Const 6)), (Initialize (fromList (unpack "c")) (Over (Var "b" [("b"), ("a")] (Here)) (Var "a" [("b"), ("a")] (There Here))))]
              let instr = compP mem program
              putStr ("Test 2.2 : ")
              putStr(show ((run mem instr instr []) == [("c", 2), ("b", 6), ("a", 3)]))
              putStrLn (show ((evalP mem program) == [("c", 2), ("b", 6), ("a", 3)]))



              -- triple if true true false
              let program = (the Program) [(Initialize (fromList (unpack "a")) (Const 6)), (Initialize (fromList (unpack "b")) (Const 4)), (If (T) (If (T) (If (F) (Initialize (fromList (unpack "c")) (Times (Var "a" [("b"), ("a")] (There Here)) (Var "b" [("b"), ("a")] (Here)))) (Initialize (fromList (unpack "c")) (Const 1))) (Initialize (fromList (unpack "c")) (Const 2))) (Initialize (fromList (unpack "c")) (Const 3)))]
              let instr = compP mem program
              putStr ("Test 3 : ")
              putStr (show ((run mem instr instr []) == [("c", 1), ("b", 4), ("a", 6)]))
              putStrLn (show ((evalP mem program) == [("c", 1), ("b", 4), ("a", 6)]))

              -- while loop
              let program = (the Program) [(Initialize (fromList (unpack "a")) (Const 6)), (Initialize (fromList (unpack "b")) (Const 4)), (While (LessThan (Var "b" [("b"), ("a")] (Here)) (Var "a" [("b"), ("a")] (There Here))) (Update "b" (Plus (Var "b" [("b"), ("a")] (Here)) (Const 1))))]
              let instr = compP mem program
              putStr ("Test 4 : ")
              putStr (show ((run mem instr instr []) == [("b", 6), ("a", 6)]))
              putStrLn (show ((evalP mem program) == [("b", 6), ("a", 6)]))

              -- initialize array
              let program = (the Program) [(InitArray "arr" (ArrayNat 5))]
              let instr = compP mem program
              putStr ("Test 5 : ")
              putStr (show ((run mem instr instr []) == [("arr0", 0), ("arr1", 0), ("arr2", 0), ("arr3", 0), ("arr4", 0)]))
              putStrLn (show ((evalP mem program) == [("arr0", 0), ("arr1", 0), ("arr2", 0), ("arr3", 0), ("arr4", 0)]))

              --access array
              let program = (the Program) [(InitArray "arr" (ArrayNat 5)), (Initialize (fromList (unpack "a"))  (Access "arr" 0 ["arr0", "arr1", "arr2", "arr3", "arr4"] (Here)))]
              let instr = compP mem program
              putStr ("Test 6 : ")
              putStr (show ((run mem instr instr []) == [("a", 0), ("arr0", 0), ("arr1", 0), ("arr2", 0), ("arr3", 0), ("arr4", 0)]))
              putStrLn (show ((evalP mem program) == [("a", 0), ("arr0", 0), ("arr1", 0), ("arr2", 0), ("arr3", 0), ("arr4", 0)]))

              --update array
              let program = (the Program) [(InitArray "arr" (ArrayNat 5)), (UpdateArray "arr" 0 (Const 6) ["arr0", "arr1", "arr2", "arr3", "arr4"] (Here))]
              let instr = compP mem program
              putStr ("Test 7 : ")
              putStr (show ((run mem instr instr []) == [("arr0", 6), ("arr1", 0), ("arr2", 0), ("arr3", 0), ("arr4", 0)]))
              putStrLn (show ((evalP mem program) == [("arr4", 0), ("arr3", 0), ("arr2", 0), ("arr1", 0), ("arr0", 6)]))
