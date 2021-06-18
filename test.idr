module Main
import Data.List
import Data.Vect
import project


main : IO ()

main = do     let mem = []
              -- variable initialisation
              let program = [(Initialise (fromList (unpack "a")) (Const 6))]
              let instr = compP mem program
              let expected = [("a", 6)]
              putStr ("Test 1 : ")
              putStr (show ((run mem instr instr []) == expected))
              putStrLn (show ((evalP mem program) == expected))

              -- update variable
              let program = [(Initialise (fromList (unpack "a")) (Const 6)), (Update "a" (Const 1))]
              let instr = compP mem program
              let expected = [("a", 1)]
              putStr ("Test 2 : ")
              putStr (show ((run mem instr instr []) == expected))
              putStrLn (show ((evalP mem program) == expected))


              -- addition
              let program = (the Program) [(Initialise (fromList (unpack "a")) (Const 6)), (Initialise (fromList (unpack "b")) (Const 4)), (Initialise (fromList (unpack "c")) (Plus (Var "b" [("a"), ("b")] (There Here)) (Var "a" [("a"), ("b")] (Here))))]
              let instr = compP mem program
              let expected = [("a", 6), ("b", 4), ("c", 10)]
              putStr ("Test 3 : ")
              putStr (show ((run mem instr instr []) == expected))
              putStrLn (show ((evalP mem program) == expected))

              -- subtraction
              let program = (the Program) [(Initialise (fromList (unpack "a")) (Const 6)), (Initialise (fromList (unpack "b")) (Const 4)), (Initialise (fromList (unpack "c")) (Minus (Var "a" [("a"), ("b")] (Here)) (Var "b" [("a"), ("b")] (There Here))))]
              let instr = compP mem program
              let expected = [("a", 6), ("b", 4), ("c", 2)]
              putStr ("Test 4 : ")
              putStr (show ((run mem instr instr []) == expected))
              putStrLn (show ((evalP mem program) == expected))

              -- multiplication
              let program = (the Program) [(Initialise (fromList (unpack "a")) (Const 6)), (Initialise (fromList (unpack "b")) (Const 4)), (Initialise (fromList (unpack "c")) (Times (Var "b" [("a"), ("b")] (There Here)) (Var "a" [("a"), ("b")] (Here))))]
              let instr = compP mem program
              let expected = [("a", 6), ("b", 4), ("c", 24)]
              putStr ("Test 5 : ")
              putStr (show ((run mem instr instr []) == expected))
              putStrLn (show ((evalP mem program) == expected))

              -- division
              let program = (the Program) [(Initialise (fromList (unpack "a")) (Const 3)), (Initialise (fromList (unpack "b")) (Const 6)), (Initialise (fromList (unpack "c")) (Over (Var "b" [("a"), ("b")] (There Here)) (Var "a" [("a"), ("b")] (Here))))]
              let instr = compP mem program
              let expected = [("a", 3), ("b", 6), ("c", 2)]
              putStr ("Test 6 : ")
              putStr (show ((run mem instr instr []) == expected))
              putStrLn (show ((evalP mem program) == expected))



              -- if true
              let program = (the Program) [(If (T) (Initialise (fromList (unpack "b")) (Const 2)) (Initialise (fromList (unpack "b")) (Const 3)))]
              let instr = compP mem program
              let expected = [("b", 2)]
              putStr ("Test 7 : ")
              putStr (show ((run mem instr instr []) == expected))
              putStrLn (show ((evalP mem program) == expected))

              -- if false
              let program = (the Program) [(If (F) (Initialise (fromList (unpack "b")) (Const 2)) (Initialise (fromList (unpack "b")) (Const 3)))]
              let instr = compP mem program
              let expected = [("b", 3)]
              putStr ("Test 8 : ")
              putStr (show ((run mem instr instr []) == expected))
              putStrLn (show ((evalP mem program) == expected))


              -- triple if true true false
              let program = (the Program) [(Initialise (fromList (unpack "a")) (Const 6)), (Initialise (fromList (unpack "b")) (Const 4)), (If (T) (If (T) (If (F) (Initialise (fromList (unpack "c")) (Times (Var "a" [("a"), ("b")] (Here)) (Var "b" [("a"), ("b")] (There Here)))) (Initialise (fromList (unpack "c")) (Const 1))) (Initialise (fromList (unpack "c")) (Const 2))) (Initialise (fromList (unpack "c")) (Const 3)))]
              let instr = compP mem program
              let expected = [("a", 6), ("b", 4), ("c", 1)]
              putStr ("Test 9 : ")
              putStr (show ((run mem instr instr []) == expected))
              putStrLn (show ((evalP mem program) == expected))


              -- while loop
              let program = (the Program) [(Initialise (fromList (unpack "a")) (Const 6)), (Initialise (fromList (unpack "b")) (Const 4)), (While (LessThan (Var "b" [("a"), ("b")] (There Here)) (Var "a" [("a"), ("b")] (Here))) (Update "b" (Plus (Var "b" [("a"), ("b")] (There Here)) (Const 1))))]
              let instr = compP mem program
              let expected = [("a", 6), ("b", 6)]
              putStr ("Test 10 : ")
              putStr (show ((run mem instr instr []) == expected))
              putStrLn (show ((evalP mem program) == expected))

              -- initialise array
              let program = (the Program) [(InitArray "arr" (ArrayNat 5))]
              let instr = compP mem program
              let expected = [("arr0", 0), ("arr1", 0), ("arr2", 0), ("arr3", 0), ("arr4", 0)]
              putStr ("Test 11 : ")
              putStr (show ((run mem instr instr []) == expected))
              putStrLn (show ((evalP mem program) == expected))

              --access array
              let program = (the Program) [(InitArray "arr" (ArrayNat 5)), (Initialise (fromList (unpack "a"))  (Access "arr" 0 ["arr0", "arr1", "arr2", "arr3", "arr4"] (Here)))]
              let instr = compP mem program
              let expected = [("arr0", 0), ("arr1", 0), ("arr2", 0), ("arr3", 0), ("arr4", 0), ("a", 0)]
              putStr ("Test 12 : ")
              putStr (show ((run mem instr instr []) == expected))
              putStrLn (show ((evalP mem program) == expected))

              --update array
              let program = (the Program) [(InitArray "arr" (ArrayNat 5)), (UpdateArray "arr" 0 (Const 6) ["arr0", "arr1", "arr2", "arr3", "arr4"] (Here))]
              let instr = compP mem program
              let expected = [("arr0", 6), ("arr1", 0), ("arr2", 0), ("arr3", 0), ("arr4", 0)]
              putStr ("Test 13 : ")
              putStr (show ((run mem instr instr []) == expected))
              putStrLn (show ((evalP mem program) == expected))
