readCommand :: IO ()
readCommand = do
  putStr "Input a command:"
  s <- getLine
  let ws = words s
  if null ws then readCommand
             else processCommand (head ws) (tail ws)

processCommand :: String -> [String] -> IO ()
processCommand cmd args =
  putStrLn (unwords (cmd:args))
