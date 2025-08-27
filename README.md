# Formalized tic-tac-toe, using Lean 4

Proofs (see `makeMovePreservesWellFormedness` when no other proof is referenced):

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

### TODO

- Implement "trivial" AI, that marks the first empty cell it sees. Prove that it can lose.
- Implement "simple" AI, that marks the first empty cell it sees, unless there is immediate danger
  that should be averted. Prove that it can lose.
- Implement unbeatable AI, that looks two steps ahead and never loses. Prove that it can't lose.
- Write out examples of well-formed and ill-formed states, and ensure that our `wellFormedGame` definition matches what we expect.
