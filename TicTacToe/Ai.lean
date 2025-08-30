import TicTacToe.Basic

theorem finCastCancel {i : Fin n} {h : n = m} : Fin.cast h.symm (Fin.cast h i) = i := by simp

theorem getOfFindFinIdx
  {xs : Vector α n}
  {i : Fin n}
  (hFindIdx : xs.findFinIdx? p = some i)
  : p (xs.get i) := by
   -- Rewrite `hFindIdx` to use `Array.findFinIdx?`
  rw [Vector.findFinIdx?] at hFindIdx
  let hFindIdx' := congrArg (fun x => Option.map (Fin.cast xs.size_toArray.symm) x) hFindIdx
  simp only [Option.map_map, Option.map_some] at hFindIdx'

  -- Some juggling to get rid of Fin.cast in `hFindIdx'`
  conv at hFindIdx' =>
    pattern Fin.cast _ ∘ Fin.cast _
    change (fun x => Fin.cast xs.size_toArray.symm (Fin.cast xs.size_toArray x))

  let hCastCancel := fun x => finCastCancel (h := xs.size_toArray) (i := x)
  simp only [hCastCancel] at hFindIdx'

  conv at hFindIdx' =>
    pattern (fun x => x)
    change id

  simp only [Option.map_id, id] at hFindIdx'

  -- Now work out the proof in terms of `Array.findFinIdx?`
  let hFindFinIdxEqSome := Iff.mp <| Array.findFinIdx?_eq_some_iff (xs := xs.toArray) (p := p) (i := Fin.cast xs.size_toArray.symm i)
  let h := hFindFinIdxEqSome hFindIdx'
  simp at h
  simp [Vector.get, h]

-- Marks the first empty cell that is found
def trivialAiMove
  (state : TicTacToeState)
  (hInProgress : state.status = GameStatus.InProgress)
  (hWellFormed : wellFormedGame state)
  : { pos : Position // state.board.get pos == Cell.Empty } :=
  match hMatch : state.board.findFinIdx? (· == Cell.Empty) with
  | some i => ⟨i, getOfFindFinIdx hMatch⟩
  | none => by
    -- According to `hMatch`, there is no Cell.Empty in the board
    have hNoEmptyCells : ¬Cell.Empty ∈ state.board := by grind

    -- But we know the board is not full
    simp [wellFormedGame, hInProgress] at hWellFormed
    have h : isBoardFull state.board = false := by
      revert hWellFormed
      match currentPlayer state with
      | Player.X => intro hWellFormed; simp at hWellFormed; exact hWellFormed.left.left.left
      | Player.O => intro hWellFormed; simp at hWellFormed; exact hWellFormed.left.left.left
    simp [isBoardFull] at h

    -- Which implies that the board count is zero, which contradicts `isBoardFull = false`
    let hCountIsZero := Vector.count_eq_zero_of_not_mem (xs := state.board) hNoEmptyCells
    contradiction

def defensiveAiMove
  (state : TicTacToeState)
  (hInProgress : state.status = GameStatus.InProgress)
  (hWellFormed : wellFormedGame state)
  : { pos : Position // state.board.get pos == Cell.Empty } :=
  let player := currentPlayer state

  -- A cell is considered under attack if it's empty and the opponent can win by marking it
  let opponent := switchPlayer player
  let underAttack (i : Position) : Bool :=
    let newBoard := state.board.set i.val (Cell.Occupied opponent)
    state.board.get i == Cell.Empty && checkWin newBoard opponent

  -- Find the first cell under attack and defend it
  let posUnderAttack := Vector.finRange state.board.size
  |> Vector.findFinIdx? underAttack

  match hMatch : posUnderAttack with
  | some i => ⟨i, by
    -- Derive `h`, the main hypothesis for our proof
    simp [posUnderAttack] at hMatch
    let hMatch' := getOfFindFinIdx (xs := Vector.finRange state.board.size) (i := i) (p := underAttack) hMatch
    simp [underAttack, Vector.get] at hMatch'
    let h := hMatch'.left
    conv at h =>
      change state.board.get (Vector.finRange (Vector.size state.board))[i] = Cell.Empty

    -- Simplify index `i` in our main hypothesis
    have hGetIdx : (Vector.finRange state.board.size)[i] = i := Vector.getElem_finRange i.2
    rw [hGetIdx] at h
    simp [h]
    ⟩
  | none =>
    -- No cell under attack, fall back to trivial move
    trivialAiMove state hInProgress hWellFormed

def simulateGameInner
  (playerMoves : List Position)
  (aiMove : (state : TicTacToeState) →
       state.status = GameStatus.InProgress →
       wellFormedGame state →
       { pos : Position // state.board.get pos == Cell.Empty })
  (state : TicTacToeState)
  (hInProgress : state.status = GameStatus.InProgress)
  (hWellFormed : wellFormedGame state)
  : Option TicTacToeState :=
  match playerMoves with
  | .nil => state
  | .cons pos tail =>
    match hIsEmpty : isEmptyPosition state.board pos with
    | false => none
    | true =>
      -- Player's turn
      let stateAfterPlayer := makeMove state pos hInProgress hIsEmpty hWellFormed
      match hMatch : stateAfterPlayer.status with
      | GameStatus.Won _ => stateAfterPlayer
      | GameStatus.Draw => stateAfterPlayer
      | GameStatus.InProgress =>
        -- AI's turn
        let ⟨aiPos, hIsEmpty'⟩ := aiMove stateAfterPlayer hMatch makeMovePreservesWellFormedness
        let stateAfterAi := makeMove stateAfterPlayer aiPos hMatch hIsEmpty' makeMovePreservesWellFormedness
        match hMatch' : stateAfterAi.status with
        | GameStatus.Won _ => stateAfterAi
        | GameStatus.Draw => stateAfterAi
        | GameStatus.InProgress => simulateGameInner tail aiMove stateAfterAi hMatch' makeMovePreservesWellFormedness

def simulateGame
  (aiMove : (state : TicTacToeState) →
       state.status = GameStatus.InProgress →
       wellFormedGame state →
       { pos : Position // state.board.get pos == Cell.Empty })
  (playerMoves : List Position)
  : Option TicTacToeState :=
  let state := initialGameState
  simulateGameInner playerMoves aiMove initialGameState (by trivial) (initialGameStateIsWellFormed state (h := by trivial))

def movesLeadTo
  (status : GameStatus)
  (aiMove : (state : TicTacToeState) →
       state.status = GameStatus.InProgress →
       wellFormedGame state →
       { pos : Position // state.board.get pos == Cell.Empty })
  (moves : List Position)
  : Bool :=
  match simulateGame aiMove moves with
  | none => false
  | some state => state.status == status

#guard movesLeadTo (GameStatus.Won Player.X) trivialAiMove [Fin.mk 0 (by trivial), Fin.mk 3 (by trivial), Fin.mk 6 (by trivial)]
#guard movesLeadTo (GameStatus.Won Player.O) trivialAiMove [Fin.mk 3 (by trivial), Fin.mk 4 (by trivial), Fin.mk 6 (by trivial)]

#guard movesLeadTo GameStatus.InProgress defensiveAiMove [Fin.mk 0 (by trivial), Fin.mk 3 (by trivial), Fin.mk 2 (by trivial)]
#guard movesLeadTo (GameStatus.Won Player.X) defensiveAiMove [Fin.mk 0 (by trivial), Fin.mk 4 (by trivial), Fin.mk 6 (by trivial), Fin.mk 3 (by trivial)]
#guard movesLeadTo GameStatus.Draw defensiveAiMove [Fin.mk 0 (by trivial), Fin.mk 3 (by trivial), Fin.mk 2 (by trivial), Fin.mk 7 (by trivial), Fin.mk 8 (by trivial)]
