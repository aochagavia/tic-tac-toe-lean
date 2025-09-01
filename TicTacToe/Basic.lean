-- Helper theorems

theorem vector_count_set {α n} {i : Fin n} {pred : α → Bool} {value : α} {xs : Vector α n} {hOld : ¬pred xs[i]} {hNew : pred value} : Vector.countP pred (Vector.set xs i value) = Vector.countP pred xs + 1 := by
  simp at hOld
  let hCountSet := Vector.countP_set (p := pred) (xs := xs) (a := value) i.2
  simp [hCountSet, hNew, hOld]

theorem vector_count_set_other {α n} {i : Fin n} {pred : α → Bool} {value : α} {xs : Vector α n} {hOld : ¬pred xs[i]} {hNew : ¬pred value} : Vector.countP pred (Vector.set xs i value) = Vector.countP pred xs := by
  simp at hOld
  let hCountSet := Vector.countP_set (p := pred) (xs := xs) (a := value) i.2
  simp [hCountSet, hNew, hOld]

theorem tupToAnd {a b c d : Bool} (h : (a, b) = (c, d)) : (a = c) ∧ b = d := by grind

theorem countDisjointList {xs} (hDisjoint : ∀ a, (pred1 a → ¬pred2 a) ∧ (pred2 a → ¬pred1 a)) : List.countP pred1 xs + List.countP pred2 xs = List.countP (fun x => pred1 x || pred2 x) xs := by
  match xs with
  | .nil => simp
  | .cons head .nil =>
    simp
    match hPred : (pred1 head, pred2 head) with
    | (true, true)   =>
      let hDisjoint := hDisjoint head
      simp [tupToAnd hPred] at hDisjoint
    | (true, false)  => simp [tupToAnd hPred]
    | (false, true)  => simp [tupToAnd hPred]
    | (false, false) => simp [tupToAnd hPred]
  | .cons head tail =>
    let hRec := countDisjointList (xs := tail) hDisjoint
    simp [List.countP_cons]
    match hPred : (pred1 head, pred2 head) with
    | (true, true)   =>
      let hDisjoint := hDisjoint head
      simp [tupToAnd hPred] at hDisjoint
    | (true, false)  =>
      simp [tupToAnd hPred]
      let hAssoc := Nat.add_assoc (List.countP pred1 tail) 1 (List.countP pred2 tail)
      let hComm := Nat.add_comm 1 (List.countP pred2 tail)
      rw [hAssoc, hComm]
      let hAssoc' := Nat.add_assoc (List.countP pred1 tail) (List.countP pred2 tail) 1
      simp [← hAssoc', hRec]
    | (false, true)  =>
      simp [tupToAnd hPred]
      let hAssoc := Nat.add_assoc (List.countP pred1 tail) (List.countP pred2 tail) 1
      let hComm := Nat.add_comm 1 (List.countP pred2 tail)
      rw [← hAssoc, hRec]
    | (false, false) => simp [tupToAnd hPred, hRec]

theorem countDisjoint {n} {pred1 pred2 : α → Bool} {xs : Vector α n} (hDisjoint : ∀ a, (pred1 a → ¬pred2 a) ∧ (pred2 a → ¬pred1 a)) : Vector.countP pred1 xs + Vector.countP pred2 xs = Vector.countP (fun x => pred1 x || pred2 x) xs := by
  simp [← Vector.countP_toList]
  exact countDisjointList (xs := xs.toList) hDisjoint

theorem countCompleteList {pred1 pred2 : α → Bool} {xs : List α} (hDisjoint : ∀ a, pred1 a != pred2 a) (hComplete : ∀ a, pred1 a || pred2 a)
  : List.countP pred1 xs + List.countP pred2 xs = List.length xs := by
  match xs with
  | .nil => simp
  | .cons head .nil =>
    simp
    match hPred : (pred1 head, pred2 head) with
    | (true, true)   =>
      let hDisjoint := hDisjoint head
      simp [tupToAnd hPred] at hDisjoint
    | (true, false)  => simp [tupToAnd hPred]
    | (false, true)  => simp [tupToAnd hPred]
    | (false, false) =>
      let h := hComplete head
      simp [tupToAnd hPred] at h
  | .cons head tail =>
    let hRec := countCompleteList (xs := tail) hDisjoint hComplete
    simp [List.countP_cons]
    match hPred : (pred1 head, pred2 head) with
    | (true, true)   =>
      let hDisjoint := hDisjoint head
      simp [tupToAnd hPred] at hDisjoint
    | (true, false)  =>
      simp [tupToAnd hPred]
      let hAssoc := Nat.add_assoc (List.countP pred1 tail) 1 (List.countP pred2 tail)
      let hComm := Nat.add_comm 1 (List.countP pred2 tail)
      rw [hAssoc, hComm]
      let hAssoc' := Nat.add_assoc (List.countP pred1 tail) (List.countP pred2 tail) 1
      simp [← hAssoc', hRec]
    | (false, true)  =>
      simp [tupToAnd hPred]
      let hAssoc := Nat.add_assoc (List.countP pred1 tail) (List.countP pred2 tail) 1
      let hComm := Nat.add_comm 1 (List.countP pred2 tail)
      rw [← hAssoc, hRec]
    | (false, false) =>
      let h := hComplete head
      simp [tupToAnd hPred] at h

theorem countComplete {pred1 pred2 : α → Bool} {xs : Vector α n} (hDisjoint : ∀ a, pred1 a != pred2 a) (hComplete : ∀ a, pred1 a || pred2 a)
  : Vector.countP pred1 xs + Vector.countP pred2 xs = Vector.size xs := by
  have h : Vector.size xs = xs.toList.length := by simp
  rw [h]
  simp only [← Vector.countP_toList]
  exact countCompleteList (xs := xs.toList) hDisjoint hComplete

-- Tic-tac-toe game

inductive Player where
  | X
  | O
deriving Repr, DecidableEq

inductive Cell where
  | empty
  | occupied : Player → Cell
deriving Repr, DecidableEq

theorem cellNeqEmptyOccupied {player} : (Cell.empty == .occupied player) = false := by
  grind

def Board := Vector Cell 9 deriving Repr
def Position := Fin 9

instance : Membership Cell Board := by
  dsimp [Board]
  infer_instance

inductive GameStatus where
  | inProgress
  | won : Player → GameStatus -- `Player` indicates who won
  | draw
deriving Repr, DecidableEq

structure TicTacToeState where
  board : Board
  status : GameStatus
deriving Repr

def emptyBoard : Board :=
  Vector.replicate 9 .empty

def initialGameState : TicTacToeState :=
  { board := emptyBoard, status := .inProgress }

def isEmptyPosition (board : Board) (pos : Position) : Bool := board.get pos == .empty

def switchPlayer (player : Player) : Player :=
  match player with
  | .X => .O
  | .O => .X

theorem switchPlayerIdentity (player : Player) : switchPlayer (switchPlayer player) = player := by
  simp [switchPlayer]
  match player with
  | .X => trivial
  | .O => trivial

theorem switchPlayerNeg (player : Player) : ¬switchPlayer player = player := by
  simp [switchPlayer]
  match player with
  | .X => trivial
  | .O => trivial

def isBoardFull (board : Board) : Bool := Vector.count .empty board == 0

def countMarkedCells (board : Board) (player : Player) : Nat :=
  board.countP (· == .occupied player)

def checkWin (board : Board) (player : Player) : Bool :=
  let playerCell := .occupied player
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

def turnNumber (state : TicTacToeState) : Nat :=
  9 - state.board.count .empty

def currentPlayer (state : TicTacToeState) : Player :=
  if turnNumber state % 2 == 0 then .X else .O

def wellFormedGame (state : TicTacToeState) : Bool :=
  match state.status with
  | .inProgress =>
      !isBoardFull state.board
      && !checkWin state.board .X
      && !checkWin state.board .O
      && (currentPlayer state == .O && countMarkedCells state.board .O + 1 == countMarkedCells state.board .X || currentPlayer state == .X && countMarkedCells state.board .O == countMarkedCells state.board .X)
  | .won victoriousPlayer =>
      checkWin state.board victoriousPlayer
      && !checkWin state.board (switchPlayer victoriousPlayer)
      && (victoriousPlayer == .O && countMarkedCells state.board .O == countMarkedCells state.board .X || victoriousPlayer == .X && countMarkedCells state.board .O + 1 == countMarkedCells state.board .X)
  | .draw =>
      isBoardFull state.board
      && !checkWin state.board .X
      && !checkWin state.board .O
      && countMarkedCells state.board .O == 4
      && countMarkedCells state.board .X == 5

theorem initialGameStateIsWellFormed (state : TicTacToeState) {h: state = initialGameState} : wellFormedGame state := by
  unfold initialGameState at h
  simp [wellFormedGame]

  let hStatus := congrArg (fun s => s.status) h
  simp at hStatus
  rw [hStatus]
  simp

  let hBoard := congrArg (fun s => s.board) h
  simp at hBoard
  rw [hBoard]

  have hCurrentPlayer : currentPlayer state = .X := by
    simp [currentPlayer, turnNumber, hBoard, emptyBoard]

  simp [hCurrentPlayer]

  have hGetFromEmptyBoard (i : Position) : Vector.get emptyBoard i = .empty := by
    unfold emptyBoard Vector.replicate Vector.get Vector.toArray
    simp

  have hBoardNotFull : isBoardFull emptyBoard = false := by
    simp [isBoardFull, emptyBoard]

  have hCheckWinEmpty (p : Player) : checkWin emptyBoard p = false := by simp [checkWin, hGetFromEmptyBoard]

  have hCheckMarkedCells (p : Player) : countMarkedCells emptyBoard p = 0 := by
    simp [countMarkedCells, emptyBoard]

  simp [
    hCheckWinEmpty .X,
    hCheckWinEmpty .O,
    hBoardNotFull,
    hCheckMarkedCells .X,
    hCheckMarkedCells .O
  ]

def makeMove (state : TicTacToeState) (pos : Position) (_ : state.status = .inProgress) (_ : isEmptyPosition state.board pos) (_ : wellFormedGame state) : TicTacToeState :=
  let player := currentPlayer state
  let newBoard := state.board.set pos.val (.occupied player)
  let newStatus :=
    if checkWin newBoard player then
      .won player
    else if isBoardFull newBoard then
      .draw
    else
      .inProgress
  { board := newBoard, status := newStatus }

theorem noWinWithoutOwnMove
  (board : Board) (player : Player) (pos : Position) (hIsEmpty : isEmptyPosition board pos) (hNoWin : checkWin board player = false)
  : checkWin (Vector.set board pos.val (.occupied (switchPlayer player))) player = false := by

  -- `newBoard` is the board after the other player has made a move
  let newBoard := Vector.set board pos.val (.occupied (switchPlayer player))

  -- The cell at pos is now occupied by them
  have cellAtPosIsOccupiedByOtherPlayer : Vector.get newBoard pos = .occupied (switchPlayer player) := by
    simp [isEmptyPosition] at hIsEmpty
    match hMatch : Vector.get board pos with
    | .occupied a => simp [hMatch] at hIsEmpty
    | .empty => simp [newBoard, Vector.set, Vector.get]

  -- Other cells were not modified
  have getFromNewBoardRespectsPreviouslyOccupied {i} {hIsNotPos : ¬pos = i}
    : Vector.get newBoard i = Vector.get board i := by
    have hDistinct : pos.val ≠ i.val := by
      intro h
      apply hIsNotPos
      apply Fin.ext
      simp [h]

    let hGetFromBoardUnchanged := Vector.getElem_set_ne (xs := board) (x := .occupied (switchPlayer player)) pos.2 i.2 (h := hDistinct)
    simp [newBoard]
    simp only [Vector.get, Fin.cast, Vector.getElem_toArray]
    simp [hGetFromBoardUnchanged]

  simp [checkWin] at hNoWin
  simp [checkWin]

  have setAnywhereLeavesSelectionUntouched {i}
    : (Vector.get board i == .occupied player) = (Vector.get newBoard i == .occupied player) := by
    by_cases hPos : pos = i
    .
      simp [isEmptyPosition] at hIsEmpty
      simp [← hPos, cellAtPosIsOccupiedByOtherPlayer, hIsEmpty, cellNeqEmptyOccupied, switchPlayerNeg]
    .
      let hGetFromBoardUnchanged := getFromNewBoardRespectsPreviouslyOccupied (hIsNotPos := hPos)
      exact Eq.symm (congrArg (· == .occupied player) hGetFromBoardUnchanged)

  -- For each count, we know that it doesn't change after the Vector.set
  have noCountChange
    {x y z : Position}
    (hCountBeforeMove : List.countP (fun i => Vector.get board i == .occupied player) [x, y, z] < 3)
    : List.countP (fun i => Vector.get newBoard i == .occupied player) [x, y, z] < 3 := by

    -- Unfold
    simp [List.countP, List.countP.go, List.countP.go, List.countP.go]

    -- Rewrite
    simp [
      (setAnywhereLeavesSelectionUntouched (i := x)).symm,
      (setAnywhereLeavesSelectionUntouched (i := y)).symm,
      (setAnywhereLeavesSelectionUntouched (i := z)).symm,
    ]

    -- Fold back
    change List.countP (fun i => Vector.get board i == .occupied player) [x, y, z] < 3
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

theorem moveIncrementsTurnNumber
  (state : TicTacToeState)
  (newState : TicTacToeState)
  (pos : Position)
  (hIsEmpty : isEmptyPosition state.board pos)
  (hNewBoard : newState.board = Vector.set state.board pos.val (.occupied (currentPlayer state)))
  : turnNumber newState = turnNumber state + 1 := by
  simp [turnNumber]

  have hAtLeastOneNonEmpty : .empty ∈ state.board := by
    simp [isEmptyPosition, Vector.get] at hIsEmpty
    let hIsMember := Vector.getElem_mem (xs := state.board) (i := pos.val) pos.2
    simp [hIsEmpty] at hIsMember
    exact hIsMember

  have hCount := Vector.count_pos_iff (xs := state.board) (a := .empty)
  have hCountSet := Vector.count_set (xs := state.board) (b := .empty) (a := .occupied (currentPlayer state)) (i := pos.val) pos.2

  simp [isEmptyPosition, Vector.get] at hIsEmpty
  simp [hIsEmpty] at hCountSet

  have hLemma : Vector.count .empty newState.board + 1 = Vector.count .empty state.board := by
    simp [hNewBoard]
    simp [hCountSet]
    exact Nat.sub_add_cancel (hCount.mpr hAtLeastOneNonEmpty)

  simp [← hLemma]
  have hNewStateCellEmptyLemma : Vector.count .empty newState.board ≤ 8 := by
    simp [hNewBoard, hCountSet, Vector.count_le_size]

  let hNatSub := Nat.sub_add_comm hNewStateCellEmptyLemma (n := 8) (m := 1) (k := Vector.count .empty newState.board)
  simp at hNatSub
  exact hNatSub

theorem hBoardNotFullIfCellEmpty
  (state : TicTacToeState)
  (pos : Position)
  (hIsEmpty : isEmptyPosition state.board pos)
  : ¬isBoardFull state.board := by
  simp [isBoardFull]
  simp [isEmptyPosition, Vector.get] at hIsEmpty
  by_cases h : state.board.count .empty = 0
  .
    let hNoEmpty := state.board.not_mem_of_count_eq_zero h
    let hPosEmpty := state.board.getElem_mem pos.2
    simp [hIsEmpty] at hPosEmpty
    contradiction
  . trivial

theorem cellEmptyCountOfIsEmpty (hIsEmpty : isEmptyPosition board pos) : board.count .empty ≥ 1 := by
  simp [isEmptyPosition, Vector.get] at hIsEmpty
  let hPosEmpty := board.getElem_mem pos.2
  simp [hIsEmpty] at hPosEmpty
  simp [hPosEmpty]

theorem moveDecrementsEmptyCellCount
  (state : TicTacToeState)
  (newState : TicTacToeState)
  (pos : Position)
  (hIsEmpty : isEmptyPosition state.board pos)
  (hNewBoard : newState.board = Vector.set state.board pos.val (.occupied (currentPlayer state)))
  : newState.board.count .empty + 1 = state.board.count .empty := by
  simp [hNewBoard]
  let hCountSet := Vector.count_set (xs := state.board) (a := .occupied (currentPlayer state)) (b := .empty) pos.2
  simp [hCountSet]

  let hIsEmpty' := hIsEmpty
  simp [isEmptyPosition, Vector.get] at hIsEmpty'
  simp [hIsEmpty']

  let hCount := cellEmptyCountOfIsEmpty hIsEmpty
  simp [Nat.sub_add_cancel hCount]

theorem newBoardIsFullAfterTurn8
  (state : TicTacToeState)
  (newState : TicTacToeState)
  (pos : Position)
  (_ : state.status = .inProgress)
  (hIsEmpty : isEmptyPosition state.board pos)
  (_ : wellFormedGame state)
  (hNewBoard : newState.board = Vector.set state.board pos.val (.occupied (currentPlayer state)))
  : isBoardFull newState.board = (turnNumber state == 8) := by

  let hAtLeastOneEmpty := hBoardNotFullIfCellEmpty state pos hIsEmpty
  simp [isBoardFull] at hAtLeastOneEmpty
  let hAtLeastOneEmpty := Nat.pos_of_ne_zero hAtLeastOneEmpty

  simp [isBoardFull, turnNumber]
  by_cases h : Vector.count .empty newState.board == 0
  .
    simp [h]

    let hMoveDecrementsEmptyCellCount := moveDecrementsEmptyCellCount state newState pos hIsEmpty hNewBoard
    let hMoveDecrementsEmptyCellCount := congrArg (· - 1) hMoveDecrementsEmptyCellCount
    simp at hMoveDecrementsEmptyCellCount
    simp [hMoveDecrementsEmptyCellCount] at h
    let h := congrArg (· + 1) h
    simp only at h

    simp [Nat.sub_add_cancel hAtLeastOneEmpty] at h
    simp [h]
  .
    simp [h]
    simp at h

    let h' := Nat.pos_of_ne_zero h
    let hMoveDecrementsEmptyCellCount := moveDecrementsEmptyCellCount state newState pos hIsEmpty hNewBoard
    let hMoveDecrementsEmptyCellCount := congrArg (· - 1) hMoveDecrementsEmptyCellCount
    simp at hMoveDecrementsEmptyCellCount
    simp [hMoveDecrementsEmptyCellCount] at h'

    let h' := Nat.add_lt_add_right h' 9
    simp only [Nat.zero_add] at h'

    have hTrivial : state.board.count .empty ≤ 9 := Vector.count_le_size
    let h' := Nat.sub_lt_sub_right hTrivial h'

    have hSimplify : Vector.count .empty state.board - 1 + 9 - Vector.count .empty state.board = 8 := by
      -- Swap (· - 1 + 9) to (· + 9 - 1) so it simplifies
      let hCount := cellEmptyCountOfIsEmpty hIsEmpty
      simp [← Nat.sub_add_comm hCount (m := 9)]

    simp [hSimplify] at h'

    let hNotEquals := (Iff.mp Nat.lt_iff_le_and_ne h').right
    simp at hNotEquals
    exact hNotEquals

theorem noWinnersWhileInProgress
  (state : TicTacToeState)
  (hInProgress : state.status = .inProgress)
  (hWellFormed : wellFormedGame state)
  : checkWin state.board .X = false ∧ checkWin state.board .O = false := by
  simp [wellFormedGame, hInProgress] at hWellFormed
  simp [hWellFormed]

theorem singleWinner
  (state : TicTacToeState)
  (hWon : state.status = .won winner)
  (hWellFormed : wellFormedGame state)
  : checkWin state.board (switchPlayer winner) = false := by
  simp [wellFormedGame, hWon] at hWellFormed
  simp [hWellFormed]

theorem playerXCellCount
  (state : TicTacToeState)
  (hWellFormed : wellFormedGame state)
  : countMarkedCells state.board .X = (turnNumber state + 1 ) / 2 := by
  let hWellFormed' := hWellFormed
  simp [countMarkedCells, turnNumber]

  have playerCellCount
    : countMarkedCells state.board .X + countMarkedCells state.board .O = 9 - Vector.count .empty state.board := by
    simp [countMarkedCells, Vector.count_eq_countP]

    have hDisjoint : ∀ a : Cell, (a == .occupied .X -> ¬(a == .occupied .O)) ∧ (a == .occupied .O -> ¬(a == .occupied .X)) := by
      intro a
      match a with
      | .empty => trivial
      | .occupied .X => trivial
      | .occupied .O => trivial

    have hDisjoint' : ∀ a : Cell, (a == .occupied .X || a == .occupied .O) != (a == .empty) := by
      intro a
      match a with
      | .empty => trivial
      | .occupied .X => trivial
      | .occupied .O => trivial

    have hComplete : ∀ a : Cell, a == .occupied .X || a == .occupied .O || a == .empty := by
      intro a
      match a with
      | .empty => trivial
      | .occupied .X => trivial
      | .occupied .O => trivial

    simp [countDisjoint (xs := state.board) (pred1 := (fun x => x == .occupied .X)) (pred2 := (fun x => x == .occupied .O)) hDisjoint]
    let hCountComplete := countComplete (xs := state.board) (pred1 := fun x => x == .occupied .X || x == .occupied .O) (pred2 := fun x => x == .empty) hDisjoint' hComplete
    simp [Vector.size] at hCountComplete
    simp [← hCountComplete]

  simp [← playerCellCount]
  match hStatus : state.status with
  | .draw =>
    simp [wellFormedGame, hStatus] at hWellFormed
    simp [hWellFormed]
    rw [← countMarkedCells]
    simp [hWellFormed]
  | .inProgress =>
    simp [wellFormedGame, hStatus] at hWellFormed
    match hCurrentPlayer : currentPlayer state with
    | .X =>
      simp [hCurrentPlayer] at hWellFormed
      simp [hWellFormed, ← Nat.two_mul, Nat.add_div (a := 2 * countMarkedCells state.board .X) (b := 1) (c := 2) (by trivial)]
      simp [countMarkedCells]
    | .O =>
      simp [hCurrentPlayer] at hWellFormed
      simp [
        Nat.add_assoc,
        hWellFormed,
        ← Nat.two_mul,
      ]
      simp [countMarkedCells]
  | .won winner =>
    simp [wellFormedGame, hStatus] at hWellFormed
    let hSingleWinner := singleWinner state hStatus hWellFormed'
    simp [hSingleWinner] at hWellFormed
    match winner with
    | .X =>
      simp at hWellFormed
      simp [Nat.add_assoc, hWellFormed, ← Nat.two_mul]
      simp [countMarkedCells]
    | .O =>
      simp at hWellFormed
      simp [
        ← hWellFormed,
        ← Nat.two_mul,
        Nat.add_div (a := 2 * countMarkedCells state.board .O) (b := 1) (c := 2) (by trivial)
      ]
      simp [hWellFormed]
      simp [countMarkedCells]

theorem makeMovePreservesWellFormedness
  {state : TicTacToeState}
  {pos : Position}
  {hInProgress : state.status = .inProgress}
  {hIsEmpty : isEmptyPosition state.board pos}
  {hWellFormed : wellFormedGame state}
  : wellFormedGame (makeMove state pos hInProgress hIsEmpty hWellFormed) := by
  let player := currentPlayer state
  let hPlayer : player = currentPlayer state := by trivial
  let newState := (makeMove state pos hInProgress hIsEmpty hWellFormed)
  let newBoard := newState.board
  have hNewBoard : newBoard = Vector.set state.board pos.val (.occupied player) := by
    trivial
  have hNewBoard' : newBoard = newState.board := by
    trivial

  let hWellFormed' := hWellFormed
  simp [wellFormedGame, hInProgress] at hWellFormed

  have hNoWinnersYet : checkWin state.board player = false ∧ checkWin state.board (switchPlayer player) = false := by
    match player with
    | .X => simp [switchPlayer, hWellFormed]
    | .O => simp [switchPlayer, hWellFormed]

  let pMarkedO := fun x : Cell => x == .occupied .O
  let pMarkedX := fun x : Cell => x == .occupied .X
  let hIsEmpty' := hIsEmpty
  simp [isEmptyPosition, Vector.get] at hIsEmpty'
  let hNotMarkedO : ¬pMarkedO (state.board.get pos) := by
    simp [pMarkedO, Vector.get, hIsEmpty']
  let hNotMarkedX : ¬pMarkedX (state.board.get pos) := by
    simp [pMarkedX, Vector.get, hIsEmpty']

  let xMarksUntouched := vector_count_set_other (i := pos) (xs := state.board) (pred := pMarkedO) (value := .occupied .X) (hOld := (by trivial)) (hNew := (by trivial))
  let oMarksUntouched := vector_count_set_other (i := pos) (xs := state.board) (pred := pMarkedX) (value := .occupied .O) (hOld := (by trivial)) (hNew := (by trivial))
  let xMarksIncreasedByOne := vector_count_set (i := pos) (xs := state.board) (pred := pMarkedX) (value := .occupied .X) (hOld := (by trivial)) (hNew := (by trivial))
  let oMarksIncreasedByOne := vector_count_set (i := pos) (xs := state.board) (pred := pMarkedO) (value := .occupied .O) (hOld := (by trivial)) (hNew := (by trivial))
  simp [pMarkedO] at xMarksUntouched
  simp [pMarkedX] at xMarksIncreasedByOne
  simp [pMarkedX] at oMarksUntouched
  simp [pMarkedO] at oMarksIncreasedByOne

  rw [makeMove, wellFormedGame, ← hNewBoard]
  simp
  let hPreviousCellCount := hWellFormed.right

  -- State-specific properties
  match hMatch : (checkWin newBoard player, checkWin newBoard (switchPlayer player)) with
  | (true, false) =>
    -- We have a winner!
    let hWonLeft := congrArg (fun x => x.1) hMatch
    simp at hWonLeft
    let hWonRight := congrArg (fun x => x.2) hMatch
    simp at hWonRight
    simp [← hPlayer, hWonLeft, hWonRight]

    -- The cell distribution is well formed
    simp [hNewBoard]
    match hCurrentPlayer : player with
    | .X =>
      simp [← hPlayer, hCurrentPlayer, countMarkedCells] at hPreviousCellCount
      simp [
        countMarkedCells,
        xMarksUntouched,
        congrArg (· + 1) hPreviousCellCount,
        xMarksIncreasedByOne
      ]
    | .O =>
      simp [← hPlayer, hCurrentPlayer, countMarkedCells] at hPreviousCellCount
      simp [
        countMarkedCells,
        oMarksUntouched,
        ← hPreviousCellCount,
        oMarksIncreasedByOne
      ]
  | (false, false) =>
    let hWonLeft := congrArg (fun x => x.1) hMatch
    simp at hWonLeft
    let hWonRight := congrArg (fun x => x.2) hMatch
    simp at hWonRight
    simp [← hPlayer, hWonLeft]

    by_cases hDraw : isBoardFull newBoard
    . -- Draw
      simp [hDraw]

      -- We know player = Player.X, since they will always have the last turn
      let hDrawAfterEigthTurn := newBoardIsFullAfterTurn8 state newState pos hInProgress hIsEmpty hWellFormed' hNewBoard
      conv at hDrawAfterEigthTurn =>
        pattern newState.board
        change newBoard
      simp [hDraw] at hDrawAfterEigthTurn
      simp [← hPlayer] at hPreviousCellCount
      simp [currentPlayer, hDrawAfterEigthTurn] at hPlayer
      simp [hPlayer, countMarkedCells] at hPreviousCellCount

      simp [hPlayer] at hWonLeft
      simp [switchPlayer, hPlayer] at hWonRight
      simp [hWonLeft, hWonRight]

      -- Well-formed cell distribution
      simp [
        countMarkedCells,
        hNewBoard,
        hPlayer,
        xMarksUntouched,
        hPreviousCellCount,
        xMarksIncreasedByOne
      ]

      -- We know Player.X has 4 cells at the beginning of move 8
      let hPlayerXHas4Cells := playerXCellCount state hWellFormed'
      simp [hDrawAfterEigthTurn] at hPlayerXHas4Cells
      rw [← countMarkedCells, hPlayerXHas4Cells]

    . -- The game goes on
      simp [hDraw]

      have hNoWinners : checkWin newBoard .X = false ∧ checkWin newBoard .O = false := by
        match hPlayerToCheck : player with
        | .X =>
            simp [hPlayerToCheck] at hWonLeft
            simp [hPlayerToCheck, switchPlayer] at hWonRight
            simp [hWonLeft, hWonRight]
        | .O =>
            simp [hPlayerToCheck] at hWonLeft
            simp [hPlayerToCheck, switchPlayer] at hWonRight
            simp [hWonLeft, hWonRight]

      have modLemma {x : Nat} : (x % 2 = 0) = ((x + 1) % 2 = 1) := by
        simp
        by_cases hCase : x % 2 = 0
        . simp at hCase
          simp [hCase, Nat.add_mod]
        . simp at hCase
          simp [hCase]
          simp [← hCase, ← Nat.two_mul]

      have hNextPlayer : currentPlayer newState = switchPlayer (currentPlayer state) := by
        simp [currentPlayer, switchPlayer]
        let hTurnNumber := moveIncrementsTurnNumber state newState pos hIsEmpty hNewBoard
        let hModLemma := modLemma (x := turnNumber state)
        by_cases hIf : turnNumber newState % 2 = 0
        . simp [hIf]
          simp [hModLemma, ← hTurnNumber, hIf]
        . simp at hIf
          simp [hIf]
          simp [hModLemma, ← hTurnNumber, hIf]

      simp [hNoWinners]
      match hCurrentPlayer : player with
      | .X =>
        rw [hPlayer] at hCurrentPlayer
        conv =>
          pattern currentPlayer { board := newBoard, status := .inProgress }
          change currentPlayer newState
        conv =>
          pattern currentPlayer { board := newBoard, status := .inProgress }
          change currentPlayer newState
        simp [hNextPlayer, hCurrentPlayer, switchPlayer]
        simp [noWinnersWhileInProgress state hInProgress hWellFormed', hCurrentPlayer] at hWellFormed
        simp [hNewBoard, countMarkedCells, xMarksUntouched]
        rw [← countMarkedCells]
        simp [hWellFormed]
        simp [countMarkedCells, xMarksIncreasedByOne]
      | .O =>
        rw [hPlayer] at hCurrentPlayer
        conv =>
          pattern currentPlayer { board := newBoard, status := .inProgress }
          change currentPlayer newState
        conv =>
          pattern currentPlayer { board := newBoard, status := .inProgress }
          change currentPlayer newState
        simp [hNextPlayer, hCurrentPlayer, switchPlayer]
        simp [noWinnersWhileInProgress state hInProgress hWellFormed', hCurrentPlayer] at hWellFormed
        simp [hNewBoard, countMarkedCells, oMarksUntouched]
        rw [← countMarkedCells, ← countMarkedCells]
        simp [← hWellFormed]
        simp [countMarkedCells, oMarksIncreasedByOne]
  | (_, true) =>
    -- This branch is unreachable, so the known facts at this point must lead to a contradiction.
    let hWonLeft := congrArg (fun x => x.1) hMatch
    simp at hWonLeft
    let hWonRight := congrArg (fun x => x.2) hMatch
    simp at hWonRight

    -- If the other player already won, it must have won before the last move, which
    -- is impossible (it would mean the game state was not well formed at the last move)
    let hNoPreviousWinner := noWinWithoutOwnMove state.board (switchPlayer player) pos hIsEmpty hNoWinnersYet.right
    simp [switchPlayerIdentity, ← hNewBoard] at hNoPreviousWinner
    simp [hNoPreviousWinner] at hWonRight

-- Proof: players alternate after each move
theorem playersAlternateAfterMove
  {state : TicTacToeState}
  {pos : Position}
  {hInProgress : state.status = .inProgress}
  {hIsEmpty : isEmptyPosition state.board pos}
  {hWellFormed : wellFormedGame state}
  {newState : TicTacToeState}
  (hNewState: newState = makeMove state pos hInProgress hIsEmpty hWellFormed)
  : currentPlayer state = switchPlayer (currentPlayer newState) := by
  let hNewBoard := congrArg (fun s => s.board) hNewState
  simp at hNewBoard
  let hMoveIncrementsTurnNumber := moveIncrementsTurnNumber state newState pos hIsEmpty hNewBoard
  simp [currentPlayer, hMoveIncrementsTurnNumber]
  by_cases hCase : turnNumber state % 2 = 0
  . simp [hCase]
    have hNextTurnNumber : (turnNumber state + 1) % 2 = 1 := by
      simp [Nat.add_mod, hCase]
    simp [hNextTurnNumber, switchPlayer]
  . simp at hCase
    simp [hCase]
    have hNextTurnNumber : (turnNumber state + 1) % 2 = 0 := by
      simp [Nat.add_mod, hCase]
    simp [hNextTurnNumber, switchPlayer]

-- Proof: cell gets marked after move with the player's mark
theorem cellMarkedAfterMove
  {state : TicTacToeState}
  {pos : Position}
  {hInProgress : state.status = .inProgress}
  {hIsEmpty : isEmptyPosition state.board pos}
  {hWellFormed : wellFormedGame state}
  {newState : TicTacToeState}
  (h: makeMove state pos hInProgress hIsEmpty hWellFormed = newState)
  : newState.board.get pos = .occupied (currentPlayer state) := by
  unfold makeMove at h
  let h' := congrArg (fun x : TicTacToeState => x.board) h
  simp at h'
  rw [Eq.symm h']
  unfold Vector.set Vector.get
  simp
