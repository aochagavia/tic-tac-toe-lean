-- Tic-tac-toe game

inductive Player where
  | X : Player
  | O : Player
deriving Repr, DecidableEq

inductive Cell where
  | Empty : Cell
  | Occupied : Player → Cell
deriving Repr, DecidableEq

def Board := Vector Cell 9
def Position := Fin 9

inductive GameStatus where
  | InProgress : Player → GameStatus -- `Player` indicates who's turn it is
  | Won : Player → GameStatus        -- `Player` indicates who won
  | Draw : GameStatus
deriving Repr, DecidableEq

structure TicTacToeState where
  board : Board
  status : GameStatus

def emptyBoard : Board :=
  Vector.replicate 9 Cell.Empty

def initialGameState : TicTacToeState :=
  { board := emptyBoard, status := GameStatus.InProgress Player.X }

def isEmptyPosition (board : Board) (pos : Position) : Bool :=
  match board.get pos with
  | Cell.Empty => true
  | Cell.Occupied _ => false

def switchPlayer (player : Player) : Player :=
  match player with
  | Player.X => Player.O
  | Player.O => Player.X

def isBoardFull (board : Board) : Bool :=
  (List.finRange 9).all (fun i =>
    match board.get i with
    | Cell.Empty => false
    | Cell.Occupied _ => true)

def checkWin (board : Board) (player : Player) : Bool :=
  let playerCell := Cell.Occupied player
  let winningLines : List (List (Fin 9)) := [
    -- Rows
    [0, 1, 2], [3, 4, 5], [6, 7, 8],
    -- Columns
    [0, 3, 6], [1, 4, 7], [2, 5, 8],
    -- Diagonals
    [0, 4, 8], [2, 4, 6]
  ]
  winningLines.any (fun line =>
    line.all (fun pos =>
      board.get pos == playerCell))

def makeMove {player : Player} (state : TicTacToeState) (pos : Position) (_ : state.status = GameStatus.InProgress player) (_ : isEmptyPosition state.board pos) : TicTacToeState :=
  let newBoard := state.board.set pos.val (Cell.Occupied player)
  let newStatus :=
    if checkWin newBoard player then
      GameStatus.Won player
    else if isBoardFull newBoard then
      GameStatus.Draw
    else
      GameStatus.InProgress (switchPlayer player)
  { board := newBoard, status := newStatus }

-- Proof: players alternate after each move
theorem playersAlternateAfterMove
  {state : TicTacToeState}
  {currentPlayer : Player}
  {pos : Position}
  {hInProgress : state.status = GameStatus.InProgress currentPlayer}
  {hIsEmpty : isEmptyPosition state.board pos}
  {newState : TicTacToeState}
  (
    h: makeMove state pos hInProgress hIsEmpty = newState
  ) : (
    newState.status = GameStatus.InProgress (switchPlayer currentPlayer) ∨
    newState.status = GameStatus.Won currentPlayer ∨
    newState.status = GameStatus.Draw
  ) := by
  let h' := congrArg (fun x : TicTacToeState => x.status) h
  simp at h'
  rw [Eq.symm h']

  match hMatch : (makeMove state pos hInProgress hIsEmpty).status with
  | GameStatus.Won winner =>
    -- Get ourselves a clear goal
    right
    left
    simp

    -- Now work towards it
    rw [h] at hMatch
    unfold makeMove at h'
    rw [hMatch] at h'
    grind
  | GameStatus.InProgress nextPlayer =>
    -- Get ourselves a clear goal
    left
    simp

    -- Now work towards it
    rw [h] at hMatch
    unfold makeMove at h'
    rw [hMatch] at h'
    grind
  | GameStatus.Draw =>
    right
    right
    simp

-- Proof: cell gets marked after move with the player's mark
theorem cellMarkedAfterMove
  {state : TicTacToeState}
  {currentPlayer : Player}
  {pos : Position}
  {hInProgress : state.status = GameStatus.InProgress currentPlayer}
  {hIsEmpty : isEmptyPosition state.board pos}
  {newState : TicTacToeState}
  (
    h: makeMove state pos hInProgress hIsEmpty = newState
  ) : (
    newState.board.get pos = Cell.Occupied currentPlayer
  ) := by
  unfold makeMove at h
  let h' := congrArg (fun x : TicTacToeState => x.board) h
  simp at h'
  rw [Eq.symm h']
  unfold Vector.set Vector.get
  simp
