# rummikuB
Rummikub game implemented in B language.

## Rules
The game rules can be found at https://www.boardgamehalv.com/how-to-play-rummikub/ , but some of them are highlighted below:
- Each player’s initial move has to be at least 30 points
- A run is 3 or more in a row of the same color
- A group is 3 or more of the same number that are all different colors 
- In each turn, a person must either take an unknown tile from the sack or meld some pieces.
- 106x Tiles (2x sets of 1 to 13 in 4 colors, 2x jokers)

## Current simplifications
This will be a multi-phase project. Thus, some features will be implemented only in advanced versions. 

### Part 1
TODO Update
The following simplifications are being used:
- The player `0` is always the first to play;
- There is only one round

### Part 2

TODO

## Supported operations
- Start a new game parametrized by the number of players
- Draw starting tiles
- Change players turns
- Make a move (alter table's state)
- Draw tile from the sack
- Query current game status
- Query player in turn
- Finish game
