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

def makeMove {player : Player} (state : TicTacToeState) (hInProgress : state.status = GameStatus.InProgress player) (pos : Position) (_ : isEmptyPosition state.board pos) : TicTacToeState :=
  match hInProgress' : state.status with
  | GameStatus.InProgress currentPlayer =>
    let newBoard := state.board.set pos.val (Cell.Occupied currentPlayer)
    let newStatus :=
      if checkWin newBoard currentPlayer then
        GameStatus.Won currentPlayer
      else if isBoardFull newBoard then
        GameStatus.Draw
      else
        GameStatus.InProgress (switchPlayer currentPlayer)
    { board := newBoard, status := newStatus }
  | GameStatus.Won _ | GameStatus.Draw => by
    rw [hInProgress'] at hInProgress
    simp at hInProgress

-- Proof: players alternate after each move
theorem playersAlternateAfterMove
  {state : TicTacToeState}
  {currentPlayer : Player}
  {pos : Position}
  {hInProgress : state.status = GameStatus.InProgress currentPlayer}
  {hIsEmpty : isEmptyPosition state.board pos}
  {newState : TicTacToeState}
  (
    h: makeMove state hInProgress pos hIsEmpty = newState
  ) : (
    newState.status = GameStatus.InProgress (switchPlayer currentPlayer) ∨
    newState.status = GameStatus.Won currentPlayer ∨
    newState.status = GameStatus.Draw
  ) := by
  let h' := congrArg (fun x : TicTacToeState => x.status) h
  simp at h'
  rw [Eq.symm h']

  match hMatch : (makeMove state hInProgress pos hIsEmpty).status with
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
