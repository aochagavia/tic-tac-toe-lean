import TicTacToe

instance : ToString Player where
  toString
  | Player.X => "X"
  | Player.O => "O"

def displayCell (cell : Cell) : String :=
  match cell with
  | Cell.Empty => " "
  | Cell.Occupied p => toString p

def displayBoard (board : Board) : IO Unit := do
  IO.println "   0   1   2"
  for i in [0, 3, 6] do
    let row := i / 3
    IO.print s!"{row}  "
    for j in [0, 1, 2] do
      let pos := i + j
      if h : pos < 9 then
        IO.print (displayCell (board.get ⟨pos, h⟩))
        if j < 2 then IO.print " | "
      else
        IO.print " "
    IO.println ""
    if i < 6 then
      IO.println "   ---------"

def displayPositionGuide : IO Unit := do
  IO.println "\nPosition guide:"
  IO.println "   0   1   2"
  IO.println "0  0 | 1 | 2"
  IO.println "   ---------"
  IO.println "1  3 | 4 | 5"
  IO.println "   ---------"
  IO.println "2  6 | 7 | 8"

def getPlayerMove : IO (Option (Fin 9)) := do
  let parseCoordinate (s : String) : Option (Fin 3) :=
    s.trim.toNat? >>= (fun n =>
      if h : n < 3 then
        some ⟨n, h⟩
      else
        none
    )
  let errorMsg := "Invalid position! Please enter the x and y coordinates separated by a space, and with values between 0 and 2."

  IO.print "Enter coordinates (e.g. 0 2): "
  let input ← (← IO.getStdin).getLine
  let coords := input.split (fun c => c.isWhitespace)
  |> List.filter (fun c => c != "")
  |> List.map parseCoordinate
  match coords with
  | [.some x, .some y] =>
    let x' : Fin 9 := x.castLT (by cases x; simp; omega)
    let y' : Fin 9 := y.castLT (by cases y; simp; omega)
    return (Option.some (y' * 3 + x'))
  | _ =>
    IO.println errorMsg
    return none

def displayGameStatus (state : TicTacToeState) : IO Unit :=
  match state.status with
  | GameStatus.InProgress =>
    IO.println s!"Player {currentPlayer state}'s turn..."
  | GameStatus.Won player =>
    IO.println s!"Player {player} wins!"
  | GameStatus.Draw =>
    IO.println "It's a draw!"

partial def gameLoop (state : TicTacToeState) (hWellFormed : wellFormedGame state) : IO Unit := do
  IO.println ""
  displayBoard state.board
  IO.println ""
  displayGameStatus state

  match hInProgress : state.status with
  | GameStatus.InProgress => do
    -- Get player move
    match ← getPlayerMove with
    | none =>
      -- Invalid input, try again
      gameLoop state hWellFormed
    | some pos =>
      -- Make the move if the position is empty
      match hIsEmpty : isEmptyPosition state.board pos with
      | true =>
        let newState := makeMove state pos hInProgress hIsEmpty hWellFormed
        gameLoop newState makeMovePreservesWellFormedness
      | false =>
        -- The position is already occupied
        IO.println "Invalid move! Position already occupied..."
        gameLoop state hWellFormed
  | _ =>
    IO.println "\nThanks for playing!"

def main : IO Unit := do
  IO.println "Welcome to Tic-Tac-Toe!"
  gameLoop initialGameState (@initialGameStateIsWellFormed initialGameState (by trivial))
