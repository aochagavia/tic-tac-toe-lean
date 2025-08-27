import TicTacToe.Basic

def toVec9 (xs : Vector α n) : Option (Vector α 9) :=
  if h : xs.size = 9 then
    some ⟨xs.toArray, by simp [h]⟩
  else
    none

def parseBoard (boardParts : List String) : Option Board :=
  let boardParts := boardParts.filter (fun s => s != "")
  let cells := boardParts.map (fun boardPart => match boardPart with
  | "_" => Option.some Cell.Empty
  | "X" => Option.some (Cell.Occupied Player.X)
  | "O" => Option.some (Cell.Occupied Player.O)
  | asdf => panic ("OH NO `".append (ToString.toString asdf.length))
  )
  if cells.any Option.isNone then
    Option.none
  else
    let board := (cells.flatMap Option.toList).toArray.toVector
    match toVec9 board with
    | .some b => Option.some b
    | _ => Option.none

def parseGame (s : String) : Option TicTacToeState :=
  match s.trimLeft.split Char.isWhitespace with
  | .nil => none
  | .cons "in-progress" tail => parseBoard tail |> Option.map (fun b => { status := GameStatus.InProgress, board := b })
  | .cons "draw" tail => parseBoard tail |> Option.map (fun b => { status := GameStatus.Draw, board := b })
  | .cons "won" (.cons "X" tail) => parseBoard tail |> Option.map (fun b => { status := GameStatus.Won Player.X, board := b })
  | .cons "won" (.cons "O" tail) => parseBoard tail |> Option.map (fun b => { status := GameStatus.Won Player.O, board := b })
  | _ => none

def wellFormed (s : String) : Bool :=
  let game_opt := parseGame s
  match game_opt with
  | .none => false
  | .some game => wellFormedGame game

def illFormed (s : String) : Bool :=
  let board_opt := parseGame s
  match board_opt with
  | .none => false
  | .some game => !wellFormedGame game

--
-- Well formed
--
#guard wellFormed "in-progress
  _ _ _
  _ _ _
  _ _ _
"

#guard wellFormed "in-progress
  _ _ _
  _ X _
  _ _ _
"

#guard wellFormed "in-progress
  _ _ _
  _ X _
  _ _ O
"

#guard wellFormed "won X
  _ X _
  _ X O
  _ X O
"

#guard wellFormed "won O
  _ _ O
  X X O
  _ X O
"

#guard wellFormed "draw
  X O X
  O X X
  O X O
"

--
-- Ill formed
--
#guard illFormed "in-progress
  _ _ _
  _ O _
  _ _ _
"

#guard illFormed "in-progress
  _ _ _
  _ X _
  _ O O
"

#guard illFormed "won O
  _ X _
  _ X _
  O O O
"

#guard illFormed "won X
  _ X O
  _ X O
  _ X O
"

#guard illFormed "won O
  _ X O
  _ X O
  _ X O
"

#guard illFormed "draw
  X O O
  X X O
  X X O
"

#guard illFormed "draw
  X O X
  O X O
  O X O
"
