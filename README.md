# Formalized tic-tac-toe, using Lean 4

### Play

Assuming you have Lean 4 [installed](https://lean-lang.org/install/manual/), you can play
tic-tac-toe against yourself by running the following command:

```bash
lake exe tic-tac-toe
```

### Proofs

The [TicTacToe.Basic](./TicTacToe/Basic.lean) module contains a definition of a tic-tac-toe game
along with the following proofs:

- Players alternate after each move (see `playersAlternateAfterMove`)
- A cell gets marked after each move, with the mark of the current player (see
  `cellMarkedAfterMove`)
- There is always a correct distribution of cells (e.g. you can't have two `X` marks and zero `O`
  marks on the board, as that would mean player `X` got two moves and player `O` zero)
- If the game is in-progress, there are no winning configurations on the board (i.e. no line of
  three similar marks)
- If the game has a winner, only that player has a winning board configuration
- If the game ended in a draw, the board is full and there are there are no winning configurations
  on it

Note: the proofs that don't reference a specific theorem are proven by
`makeMovePreservesWellFormedness`, which ensures a board is always well-formed. See also
[TicTacToe.Tests](./TicTacToe/Tests.lean) for examples of well-formed and ill-formed game states.

### TODO

- Implement "trivial" AI, that marks the first empty cell it sees.
- Implement "simple" AI, that marks the first empty cell it sees, unless there is immediate danger
  that should be averted.
- Implement unbeatable AI, that looks two steps ahead and never loses. Prove that it can't lose.
