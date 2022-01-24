MACHINE Tiles

CONSTANTS
  TILES, TILES_PER_SET, COLOR, NUMBER,
  JOKER_A, JOKER_B,
  TILES_JOKER, TILES_NO_JOKER,
  SET_PER_COLOR 

PROPERTIES

/**************************************** TILES **************************************************/
// Tiles are actually naturals. 
// Color from tile X can be retrived using: (i//(TILES_PER_SET*SET_PER_COLOR)) (floor division)
// Number from tile X can be retrived using: (i%TILES_PER_SET) 
// Tile 104: Joker A, Number 104, Color 104
// Tile 105: Joker B, Number 105, Color 105

TILES_NO_JOKER = 0..103 &
JOKER_A = 104 & JOKER_B = 105 &
TILES_JOKER = {JOKER_A, JOKER_B} &
TILES = TILES_NO_JOKER \/ TILES_JOKER &
TILES_PER_SET = 13 & 
SET_PER_COLOR = 2 & 


// Color of a tile
COLOR : TILES -->> (0..3 \/ TILES_JOKER)  &
!xx.(xx : TILES & xx > 103 => {xx |-> xx} <: COLOR) &
!xx.(xx : TILES & xx <= 103 => {xx |-> xx /(TILES_PER_SET*SET_PER_COLOR)} <: COLOR) &

// Number of a tile
NUMBER : TILES -->> (0..12 \/ TILES_JOKER) &
!xx.(xx : TILES & xx > 103 => {xx |-> xx} <: NUMBER) &
!xx.(xx : TILES & xx <= 103 => {xx |-> xx mod TILES_PER_SET} <: NUMBER)

END
