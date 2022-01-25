MACHINE Groups

SEES Tiles, TileGames

CONSTANTS
  MAX_TILES_PER_GROUPS

PROPERTIES
  MAX_TILES_PER_GROUPS = 4

VARIABLES
  groups

INVARIANT
  // A group is 3 or more of the same number that are all different colors
  // Number of unique colors must be equal to the group size
  // Number of unique numbers must be equal 1
  groups <: POW(TILES) & groups : FIN(groups) &
  !xx.(xx : groups => (card(xx) >= MIN_TILES_PER_GAME) & (card(COLOR[xx]) = card(xx)) & 
  (card(NUMBER[xx - TILES_JOKER]) = 1) & card(xx) <= MAX_TILES_PER_GROUPS)


INITIALISATION
  groups := {}

OPERATIONS

add_group(gg) = 
  PRE 
    (card(gg) >= MIN_TILES_PER_GAME) & (card(COLOR[gg]) = card(gg)) & (card(NUMBER[gg - TILES_JOKER]) = 1) &
    card(gg) <= MAX_TILES_PER_GROUPS
  THEN groups := groups \/ {gg}
  END;

rmv_group(gg) =
  PRE gg : groups
  THEN groups := groups - {gg}
  END;

set_groups(ggs) =
  PRE ggs <: POW(TILES) & ggs : FIN(ggs)
  THEN
    groups := ggs
  END;

clear_groups = 
  PRE 1=1
  THEN
    groups := {}
  END

END