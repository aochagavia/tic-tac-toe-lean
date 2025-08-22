-- Helper theorems

def vector_cons : α → Vector α n → Vector α (Nat.succ n)
  | a, ⟨v, h⟩ =>
    have hSize : (a :: v.toList).toArray.size = Nat.succ n := by grind
    Vector.mk (n := Nat.succ n) (List.toArray (a :: Array.toList v)) hSize

theorem vector_cons_equivalence {α} {xs : Vector α (Nat.succ n)} : xs = vector_cons xs.head xs.tail := by
  apply Vector.ext
  intro i
  induction i with
  | zero => simp [vector_cons, Vector.head]
  | succ i ih =>
    intro hIndexWithinBounds
    unfold vector_cons
    simp

theorem vector_cons_set {xs : Vector α n} {i : Fin (Nat.succ n)} : (vector_cons x xs).set i a = if hEq : i.val == 0 then vector_cons a xs else let n' := i.pred (by simp at hEq; simp [hEq]); vector_cons x (xs.set n' a) := by
  by_cases h : (i = 0)
  . simp [h, vector_cons, Vector.set]
  . simp [h, vector_cons, Vector.set]
    let i' := Fin.pred i h
    rw [List.set.eq_def]
    cases i using Fin.cases with
    | zero => simp; grind
    | succ => simp

theorem vector_cons_get {xs : Vector α n} {i : Fin (Nat.succ n)} : (vector_cons x xs).get i = if hEq : i.val == 0 then x else let n' := i.pred (by simp at hEq; simp [hEq]); xs.get n' := by
  by_cases h : (i = 0)
  . simp [h, vector_cons, Vector.get]
  . simp [h, vector_cons, Vector.get]
    let i' := Fin.pred i h
    simp only [GetElem.getElem]
    rw [List.get.eq_def]
    simp
    cases i using Fin.cases with
    | zero => simp; grind
    | succ => simp [Vector.get]

theorem vectorSetGetUnchanged
    {α : Type} {n : Nat} (xs : Vector α n) (value : α)
    (iSet iGet : Fin n) (hDistinct : iSet ≠ iGet) :
    (Vector.set xs iSet value).get iGet = xs.get iGet := by
  -- Revert these values, because their types vary per case
  revert xs iSet iGet
  cases n with
  | zero =>
      intro _ iSet
      exact Fin.elim0 iSet
  | succ n' =>
      -- Going into the structure of the indices lets Lean see that they target different places
      -- in the array
      intro xs iSet iGet hDistinct
      cases iSet using Fin.cases with
      | zero =>
          cases iGet using Fin.cases with
          | zero => contradiction -- iSet = iGet = zero
          | succ iGet' => simp [Vector.set, Vector.get] -- iGet > iSet
      | succ iSet' =>
          cases iGet using Fin.cases with
          | zero => simp [Vector.set, Vector.get] -- iGet < iSet
          | succ iGet' =>
              -- iGet != iSet, but Lean can't see it because they are both `succ`, so we'll use
              -- induction

              rw [
                vector_cons_equivalence (xs := xs),
                vector_cons_set (x := xs.head) (xs := xs.tail) (i := iSet'.succ) (a := value),
                vector_cons_get (x := xs.head) (xs := xs.tail) (i := iGet'.succ),
              ]

              have hDistinct' : iSet' ≠ iGet' := by grind
              let ih := vectorSetGetUnchanged xs.tail value iSet' iGet' hDistinct'
              by_cases h : (↑iSet'.succ == 0)
              . simpa [h]
              . simpa [h]

-- Tic-tac-toe game

inductive Player where
  | X : Player
  | O : Player
deriving Repr, DecidableEq

inductive Cell where
  | Empty : Cell
  | Occupied : Player → Cell
deriving Repr, DecidableEq

theorem cellNeqEmptyOccupied {player} : (Cell.Empty == Cell.Occupied player) = false := by
  grind

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

def isEmptyPosition (board : Board) (pos : Position) : Bool := board.get pos == Cell.Empty

def switchPlayer (player : Player) : Player :=
  match player with
  | Player.X => Player.O
  | Player.O => Player.X

theorem switchPlayerIdentity (player : Player) : switchPlayer (switchPlayer player) = player := by
  simp [switchPlayer]
  match player with
  | Player.X => trivial
  | Player.O => trivial

theorem switchPlayerNeg (player : Player) : ¬switchPlayer player = player := by
  simp [switchPlayer]
  match player with
  | Player.X => trivial
  | Player.O => trivial

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

  -- We use ≥ here to make our proofs easier
  winningLines.any (fun line =>
    line.countP (fun pos => board.get pos == playerCell) >= 3)

def wellFormedGame (state : TicTacToeState) : Bool :=
  match state.status with
  | GameStatus.InProgress _ =>
      !isBoardFull state.board
      && !checkWin state.board Player.X
      && !checkWin state.board Player.O
  | GameStatus.Won player =>
      checkWin state.board player && !checkWin state.board (switchPlayer player)
  | GameStatus.Draw =>
      isBoardFull state.board
      && !checkWin state.board Player.X
      && !checkWin state.board Player.O

theorem initialGameStateIsWellFormed (state : TicTacToeState) {h: state = initialGameState} : wellFormedGame state := by
  unfold initialGameState at h
  unfold wellFormedGame
  let hStatus := congrArg (fun s => s.status) h
  simp at hStatus
  rw [hStatus]
  simp

  let hBoard := congrArg (fun s => s.board) h
  simp at hBoard
  rw [hBoard]

  have hGetFromEmptyBoard (i : Position) : Vector.get emptyBoard i = Cell.Empty := by
    unfold emptyBoard Vector.replicate Vector.get Vector.toArray
    simp

  have hBoardNotFull : isBoardFull emptyBoard = false := by
    unfold isBoardFull
    simp
    refine ⟨0, ?_⟩
    rw [hGetFromEmptyBoard (0 : Fin 9 )]
    simp
    trivial

  have hCheckWinEmpty (p : Player) : checkWin emptyBoard p = false := by
    unfold checkWin
    simp [hGetFromEmptyBoard]

  simp [hCheckWinEmpty Player.X, hCheckWinEmpty Player.O, hBoardNotFull]

def makeMove {player : Player} (state : TicTacToeState) (pos : Position) (_ : state.status = GameStatus.InProgress player) (_ : isEmptyPosition state.board pos) (_ : wellFormedGame state) : TicTacToeState :=
  let newBoard := state.board.set pos.val (Cell.Occupied player)
  let newStatus :=
    if checkWin newBoard player then
      GameStatus.Won player
    else if isBoardFull newBoard then
      GameStatus.Draw
    else
      GameStatus.InProgress (switchPlayer player)
  { board := newBoard, status := newStatus }

theorem noWinWithoutOwnMove
  (board : Board) (player : Player) (pos : Position) (hIsEmpty : isEmptyPosition board pos) (hNoWin : checkWin board player = false)
  : checkWin (Vector.set board pos.val (Cell.Occupied (switchPlayer player))) player = false := by

  -- `newBoard` is the board after the other player has made a move
  let newBoard := Vector.set board pos.val (Cell.Occupied (switchPlayer player))

  -- The cell at pos is now occupied by them
  have cellAtPosIsOccupiedByOtherPlayer : Vector.get newBoard pos = Cell.Occupied (switchPlayer player) := by
    simp [isEmptyPosition] at hIsEmpty
    match hMatch : Vector.get board pos with
    | Cell.Occupied a => simp [hMatch] at hIsEmpty
    | Cell.Empty => simp [newBoard, Vector.set, Vector.get]

  -- Other cells were not modified
  have getFromNewBoardRespectsPreviouslyOccupied {i} {hIsNotPos : ¬pos = i}
    : Vector.get newBoard i = Vector.get board i := by
    simp at hIsNotPos
    let hGetFromBoardUnchanged := vectorSetGetUnchanged (xs := board) (value := Cell.Occupied (switchPlayer player)) (hDistinct := hIsNotPos)
    simp [newBoard, hGetFromBoardUnchanged]

  simp [checkWin] at hNoWin
  simp [checkWin]

  have setAnywhereLeavesSelectionUntouched {i}
    : (Vector.get board i == Cell.Occupied player) = (Vector.get newBoard i == Cell.Occupied player) := by
    by_cases hPos : pos = i
    .
      simp [isEmptyPosition] at hIsEmpty
      simp [← hPos, cellAtPosIsOccupiedByOtherPlayer, hIsEmpty, cellNeqEmptyOccupied, switchPlayerNeg]
    .
      let hGetFromBoardUnchanged := getFromNewBoardRespectsPreviouslyOccupied (hIsNotPos := hPos)
      exact Eq.symm (congrArg (· == Cell.Occupied player) hGetFromBoardUnchanged)

  -- For each count, we know that it doesn't change after the Vector.set
  have noCountChange
    {x y z : Position}
    (hCountBeforeMove : List.countP (fun i => Vector.get board i == Cell.Occupied player) [x, y, z] < 3)
    : List.countP (fun i => Vector.get newBoard i == Cell.Occupied player) [x, y, z] < 3 := by

    -- Unfold
    simp [List.countP, List.countP.go, List.countP.go, List.countP.go]

    -- Rewrite
    simp [
      (setAnywhereLeavesSelectionUntouched (i := x)).symm,
      (setAnywhereLeavesSelectionUntouched (i := y)).symm,
      (setAnywhereLeavesSelectionUntouched (i := z)).symm,
    ]

    -- Fold back
    change List.countP (fun i => Vector.get board i == Cell.Occupied player) [x, y, z] < 3
    exact hCountBeforeMove

  simp [
    newBoard,
    noCountChange hNoWin.left,
    noCountChange hNoWin.right.left,
    noCountChange hNoWin.right.right.left,
    noCountChange hNoWin.right.right.right.left,
    noCountChange hNoWin.right.right.right.right.left,
    noCountChange hNoWin.right.right.right.right.right.left,
    noCountChange hNoWin.right.right.right.right.right.right.left,
    noCountChange hNoWin.right.right.right.right.right.right.right,
  ]

theorem makeMovePreservesWellFormedness
  {state : TicTacToeState}
  {currentPlayer : Player}
  {pos : Position}
  {hInProgress : state.status = GameStatus.InProgress currentPlayer}
  {hIsEmpty : isEmptyPosition state.board pos}
  {hWellFormed : wellFormedGame state}
  : wellFormedGame (makeMove state pos hInProgress hIsEmpty hWellFormed) := by
  let newState := (makeMove state pos hInProgress hIsEmpty hWellFormed)
  let newBoard := newState.board
  have hNewBoard : newBoard = Vector.set state.board pos.val (Cell.Occupied currentPlayer) := by
    trivial

  have hNoWinnersYet : checkWin state.board currentPlayer = false ∧ checkWin state.board (switchPlayer currentPlayer) = false := by
    unfold wellFormedGame at hWellFormed
    simp [hInProgress] at hWellFormed
    match currentPlayer with
    | Player.X => simp [switchPlayer, hWellFormed]
    | Player.O => simp [switchPlayer, hWellFormed]

  simp [wellFormedGame, hInProgress] at hWellFormed
  simp [makeMove]

  match hMatch : (checkWin newBoard currentPlayer, checkWin newBoard (switchPlayer currentPlayer)) with
  | (true, false) =>
    -- We have a winner!
    let hWonLeft := congrArg (fun x => x.1) hMatch
    simp at hWonLeft
    let hWonRight := congrArg (fun x => x.2) hMatch
    simp at hWonRight
    simp [wellFormedGame, ← hNewBoard, hWonLeft, hWonRight]
  | (false, false) =>
    let hWonLeft := congrArg (fun x => x.1) hMatch
    simp at hWonLeft
    let hWonRight := congrArg (fun x => x.2) hMatch
    simp at hWonRight
    simp [wellFormedGame, ← hNewBoard, hWonLeft]
    by_cases hDraw : isBoardFull newBoard
    . -- Draw
      simp [hDraw]
      match hCurrentPlayer : currentPlayer with
      | Player.X =>
        simp [hCurrentPlayer] at hWonLeft
        simp [switchPlayer, hCurrentPlayer] at hWonRight
        simp [hWonLeft, hWonRight]
      | Player.O =>
        simp [hCurrentPlayer] at hWonLeft
        simp [switchPlayer, hCurrentPlayer] at hWonRight
        simp [hWonLeft, hWonRight]
    . -- The game goes on
      simp [hDraw]
      match hCurrentPlayer : currentPlayer with
      | Player.X =>
        simp [hCurrentPlayer] at hWonLeft
        simp [switchPlayer, hCurrentPlayer] at hWonRight
        simp [hWonLeft, hWonRight]
      | Player.O =>
        simp [hCurrentPlayer] at hWonLeft
        simp [switchPlayer, hCurrentPlayer] at hWonRight
        simp [hWonLeft, hWonRight]
  | (_, true) =>
    -- This branch is unreachable, so the known facts at this point must lead to a contradiction.
    let hWonLeft := congrArg (fun x => x.1) hMatch
    simp at hWonLeft
    let hWonRight := congrArg (fun x => x.2) hMatch
    simp at hWonRight

    -- If the other player already won, it must have won before the last move, which
    -- is impossible (it would mean the game state was not well formed at the last move)
    let hNoPreviousWinner := noWinWithoutOwnMove state.board (switchPlayer currentPlayer) pos hIsEmpty hNoWinnersYet.right
    simp [switchPlayerIdentity, ← hNewBoard] at hNoPreviousWinner
    simp [hNoPreviousWinner] at hWonRight

-- Proof: players alternate after each move
theorem playersAlternateAfterMove
  {state : TicTacToeState}
  {currentPlayer : Player}
  {pos : Position}
  {hInProgress : state.status = GameStatus.InProgress currentPlayer}
  {hIsEmpty : isEmptyPosition state.board pos}
  {hWellFormed : wellFormedGame state}
  {newState : TicTacToeState}
  (
    h: makeMove state pos hInProgress hIsEmpty hWellFormed = newState
  ) : (
    newState.status = GameStatus.InProgress (switchPlayer currentPlayer) ∨
    newState.status = GameStatus.Won currentPlayer ∨
    newState.status = GameStatus.Draw
  ) := by
  let h' := congrArg (fun x : TicTacToeState => x.status) h
  simp at h'
  rw [Eq.symm h']

  match hMatch : (makeMove state pos hInProgress hIsEmpty hWellFormed).status with
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
  {hWellFormed : wellFormedGame state}
  {newState : TicTacToeState}
  (
    h: makeMove state pos hInProgress hIsEmpty hWellFormed = newState
  ) : (
    newState.board.get pos = Cell.Occupied currentPlayer
  ) := by
  unfold makeMove at h
  let h' := congrArg (fun x : TicTacToeState => x.board) h
  simp at h'
  rw [Eq.symm h']
  unfold Vector.set Vector.get
  simp
