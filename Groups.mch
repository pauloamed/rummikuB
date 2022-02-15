MACHINE Groups

SEES Tiles, TileGames

CONSTANTS
  MAX_TILES_PER_GROUPS

PROPERTIES
  MAX_TILES_PER_GROUPS = 4

VARIABLES
  free_indexes, groups

INVARIANT
  free_indexes : GAME_INDEXES --> BOOL &

  // A group is 3 or more of the same number that are all different colors
  // Number of unique colors must be equal to the group size
  // Number of unique numbers must be equal 1
  groups : TILES --> GAME_INDEXES &

  !xx.(xx : ran(groups) => 
    xx = 0 or
    (
      // dom(groups|>{xx}): todas tiles que fazem parte do grupo com id xx
      card(dom(groups|>{xx})) >= MIN_TILES_PER_GAME & 
      card(dom(groups|>{xx})) <= MAX_TILES_PER_GROUPS &
      card(COLOR[dom(groups|>{xx})]) = card(dom(groups|>{xx})) & 
      card(NUMBER[dom(groups|>{xx}) - TILES_JOKER]) = 1 
    )
  ) 


INITIALISATION
  groups := TILES * {0} || free_indexes := GAME_INDEXES * {TRUE}

OPERATIONS

add_group(gg) = 
  PRE
    gg : TILES --> BOOL & // dom(gg|>{TRUE})
    card(dom(gg|>{TRUE})) >= MIN_TILES_PER_GAME & 
    card(dom(gg|>{TRUE})) <= MAX_TILES_PER_GROUPS &
    card(COLOR[dom(gg|>{TRUE})]) = card(dom(gg|>{TRUE})) & 
    card(NUMBER[dom(gg|>{TRUE}) - TILES_JOKER]) = 1
  THEN
      ANY next_idx WHERE next_idx = min(dom(free_indexes|>{FALSE})) THEN
      groups := groups <+ dom(gg|>{TRUE}) * {next_idx} || 
      free_indexes(next_idx) := FALSE
      END
  END;

rmv_group(gg) =
  PRE 
    // dom(gg |> {TRUE}): ids que estao no grupo removido
    // groups[dom(gg |> {TRUE})]: indice do grupo a ser removido
    gg : TILES --> BOOL &
    card(groups[dom(gg |> {TRUE})]) = 1 &
    groups[dom(gg |> {TRUE})] /= {0} &
    card( dom(gg |> {TRUE}) <<| groups) = card(groups) - 1
  THEN 
    groups := groups <+ dom(gg |> {TRUE}) * {0} || 
    free_indexes := free_indexes <+ groups[dom(gg |> {TRUE})] * {TRUE}
    
  END;

set_groups(ggs) =
  PRE 
    ggs : TILES --> GAME_INDEXES &
    !xx.(xx : ran(ggs) => 
      xx = 0 or
      (
        // dom(ggs|>{xx}): todas tiles que fazem parte do grupo com id xx
        card(dom(ggs|>{xx})) >= MIN_TILES_PER_GAME & 
        card(dom(ggs|>{xx})) <= MAX_TILES_PER_GROUPS &
        card(COLOR[dom(ggs|>{xx})]) = card(dom(ggs|>{xx})) & 
        card(NUMBER[dom(ggs|>{xx}) - TILES_JOKER]) = 1 
      )
    ) 
  THEN
    groups := ggs
  END;

clear_groups = groups := TILES * {0}

END