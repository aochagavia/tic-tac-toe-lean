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
  IO.println "Current board:"
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

def getPlayerMove (player : Player) : IO (Option Position) := do
  IO.println s!"\nPlayer {player}'s turn"
  IO.print "Enter position (0-8): "
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trim
  match trimmed.toNat? with
  | some n =>
    if h : n < 9 then
      return some ⟨n, h⟩
    else
      IO.println "Invalid position! Please enter a number between 0 and 8."
      return none
  | none =>
    IO.println "Invalid input! Please enter a number between 0 and 8."
    return none

def displayGameStatus (state : TicTacToeState) : IO Unit :=
  match state.status with
  | GameStatus.InProgress =>
    IO.println s!"Game in progress. Current player: {currentPlayer state}"
  | GameStatus.Won player =>
    IO.println s!"Player {player} wins!"
  | GameStatus.Draw =>
    IO.println "It's a draw!"

partial def gameLoop (state : TicTacToeState) (hWellFormed : wellFormedGame state) : IO Unit := do
  displayBoard state.board
  displayGameStatus state

  match hInProgress : state.status with
  | GameStatus.InProgress => do
    -- Get player move
    let moveOpt ← getPlayerMove (currentPlayer state)
    match moveOpt with
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
        IO.println "Invalid move! Position already occupied. Try again."
        gameLoop state hWellFormed
  | _ =>
    IO.println "\nThanks for playing!"

def main : IO Unit := do
  IO.println "Welcome to Tic-Tac-Toe!"
  displayPositionGuide
  IO.println "\nLet's start the game!"
  IO.println ""
  gameLoop initialGameState (@initialGameStateIsWellFormed initialGameState (by trivial))
