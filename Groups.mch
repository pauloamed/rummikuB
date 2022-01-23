MACHINE Groups

SEES Tiles, TileGames

VARIABLES
  groups

INVARIANT
  // A group is 3 or more of the same number that are all different colors
  // Number of unique colors must be equal to the group size
  // Number of unique numbers must be equal 1
  groups <: POW(TILES) & groups : FIN(groups) &
  !xx.(xx : groups => (card(xx) >= MIN_TILES_PER_GAME) & (card(COLOR[xx]) = card(xx)) & (card(NUMBER[xx]) = 1))


INITIALISATION
  groups := {}

OPERATIONS

add_group(gg) = 
  PRE 1=1
  THEN groups := groups \/ gg
  END;

rmv_group(gg) =
  PRE gg : groups
  THEN groups := groups - {gg}
  END

END