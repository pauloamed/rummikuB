# rummikuB
Rummikub game implemented in B language.

## Rules
The game rules can be found at , but some of them are highlighted below:
- Each player’s initial move has to be at least 30 points
- A run is 3 or more in a row of the same color
- A group is 3 or more of the same number that are all different colors 
- If a person cannot make a move, they must take an unknown tile from the sack and pass their turn.

## Current simplifications
This will be a multi-phase project. Thus, some features will be implemented only in advanced versions. 
Currently, the following simplifications are being used:
- The `0` player is always the first to play
- There are no joker tiles
- There is only one round

## Supported operations
- Start a new game parametrized by the number of players
- Draw starting tiles
- Change players turns
- Make a move (alter table's state)
- Draw tile from the sack
- Query current game status
- Query player in turn
- Finish game
