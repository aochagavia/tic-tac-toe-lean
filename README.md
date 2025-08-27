# Mathematically proven, unbeatable tic-tac-toe!

Proofs:

- Players alternate after each move (`playersAlternateAfterMove`)
- A cell gets marked after each move (`cellMarkedAfterMove`)
- The initial game state is well-formed (`initialGameStateIsWellFormed`)
- Any well-formed game that has passed through the `makeMove` function is also well-formed (`makeMovePreservesWellFormedness`)

Later:

- Implement "trivial" AI, that marks the first empty cell it sees. Prove that it can lose.
- Implement "simple" AI, that marks the first empty cell it sees, unless there is immediate danger that should be averted. Prove that it can lose.
- Implement unbeatable AI, that looks two steps ahead and never loses. Prove that it can't lose.
