# Mathematically proven, unbeatable tic-tac-toe!

Proofs:

- Players alternate after each move

Pending:

- Implement "trivial" AI, that marks the first empty cell it sees. Prove that it can lose. Should be easy to prove by contradiction (i.e. assume the player never loses, then provide a counterexample).
- Implement "simple" AI, that marks the first empty cell it sees, unless there is immediate danger that should be averted. Prove that it can lose. Should be easy to prove by contradiction (i.e. assume the player never loses, then provide a counterexample).
- Implement unbeatable AI, that looks two steps ahead and never loses. Prove that it can't lose.

Other interesting proofs we could write:

-- The game ends after a maximum of 9 valid moves
-- If the board has a winning line after X moves, the game is in the Win state.
-- If the board has a winning line after X moves, there are no other winning lines.
-- If there is a draw, there are no winning lines.
