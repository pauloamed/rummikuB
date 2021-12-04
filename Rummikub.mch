MACHINE Rummikub

SETS
  NAME;
  GAME_STATE = {NOT_RUNNING, ADDING_PLAYERS, DRAWING_INITIAL_TILES, PLAYING, FINISHED}

CONSTANTS
  VALID_PLAYERS_NUMS, VALID_PLAYERS_IDS,
  TILES, NUM_STARTING_TILES, TILES_PER_SET, SET_PER_COLOR, TILE_2_COLOR, TILE_2_NUMBER, MIN_TILES_PER_GAME

PROPERTIES        
  VALID_PLAYERS_NUMS = 2..4 & 
  VALID_PLAYERS_IDS = 1..4 & 

  /**************************************** TILES **************************************************/
  // Tiles are actually naturals. 
  // Color from tile X can be retrived using: (i//(TILES_PER_SET*SET_PER_COLOR)) (floor division)
  // Number from tile X can be retrived using: (i%TILES_PER_SET) 

  TILES = 0..104 & TILES : FIN(0..103) &
  NUM_STARTING_TILES = 14 & 
  TILES_PER_SET = 13 & 
  SET_PER_COLOR = 2 & 
  MIN_TILES_PER_GAME = 3 &

  TILE_2_COLOR : TILES --> 0..3 & 
  !xx.(xx : TILES => {xx |-> xx /(TILES_PER_SET*SET_PER_COLOR)} <: TILE_2_COLOR) & 

  TILE_2_NUMBER : TILES --> 0..12 & 
  !xx.(xx : TILES => {xx |-> xx mod TILES_PER_SET} <: TILE_2_NUMBER)

VARIABLES in_sack, players_racks, players, state, num_players, player_turn, runs, groups

INVARIANT
  state : GAME_STATE & 

  /**************************************** PLAYERS **************************************************/

  // Number of players: if the game has started, there should be a valid number of players
  (state /= NOT_RUNNING => num_players : VALID_PLAYERS_NUMS) & 

  // Players: a function of names (but parcial injective and indexed by naturals)
  (state /= NOT_RUNNING => players : VALID_PLAYERS_IDS >+> NAME) &

  // Player turn
  (state /= NOT_RUNNING => player_turn <= num_players) &
  player_turn : NATURAL1 &

  /************************************** PLAYERS RACKS AND SACK *************************************/

  in_sack <: TILES &

  players_racks : VALID_PLAYERS_IDS +-> POW(TILES) &
  dom(players_racks) = dom(players) & // 
  UNION ( ss ) . (ss : dom(players_racks) | players_racks(ss)) /\ in_sack = {} &

  // Exclusive or: a piece is either in the sack or in (exactly) 1 player rack
  !xx.(xx : TILES => (xx : in_sack) or (card({yy | yy : ran(players_racks) & xx : yy }) = 1)) &
  !xx.(xx : TILES => not ((xx : in_sack) & (card({yy | yy : ran(players_racks) & xx : yy }) = 1))) &

  /********************************** RUNS AND GROUPS ************************************************/

  // A run is 3 or more in a row of the same color
  // Number of unique colors must be equal to 1
  // Number of unique numbers must be equal to run size
  // Diference from minimal to maximal element must be equal to run size
  runs <: POW(TILES) &
  !xx.(xx : runs => (card(xx) >= MIN_TILES_PER_GAME) & (card(TILE_2_COLOR[xx]) = 1) & (card(TILE_2_NUMBER[xx]) = card(xx))) &
  !xx.(xx : runs => (max(xx) - min(xx) + 1) = card(xx)) &

  // A group is 3 or more of the same number that are all different colors
  // Number of unique colors must be equal to the group size
  // Number of unique numbers must be equal 1
  groups <: POW(TILES) &
  !xx.(xx : groups => (card(xx) >= MIN_TILES_PER_GAME) & (card(TILE_2_COLOR[xx]) = card(xx)) & (card(TILE_2_NUMBER[xx]) = 1))

INITIALISATION 
  state := NOT_RUNNING || in_sack := {} || players_racks := {} || players := {} || num_players := 0 || player_turn := 1 || runs := {} || groups := {}

OPERATIONS

  /********************************** STATE: NOT_RUNNING ************************************************/

  start_game(nn) =
    PRE state = NOT_RUNNING & nn : VALID_PLAYERS_NUMS 
    THEN num_players := nn || state := ADDING_PLAYERS
    END;

  /********************************** STATE: ADDING_PLAYERS **********************************************/

  add_player(xx) = 
    PRE xx : NAME & xx /: ran(players) & state = ADDING_PLAYERS & card(players) < num_players
    THEN 
      IF card(players) + 1 = num_players THEN
        players := players <+ {card(players) + 1 |-> xx} || players_racks := players_racks <+ {card(players) + 1 |-> {}} || state := DRAWING_INITIAL_TILES || in_sack := TILES
      ELSE
        players := players <+ {card(players) + 1 |-> xx} || players_racks := players_racks <+ {card(players) + 1 |-> {}}
      END
    END;

  /********************************** STATE: DRAWING_INITIAL_TILES **********************************************/

  draw_initial_tiles(xx) = 
    PRE xx : ran(players) & players_racks(players~(xx)) = {} & state = DRAWING_INITIAL_TILES
    THEN
      ANY subset_tiles 
      WHERE subset_tiles <: in_sack & card(subset_tiles) = NUM_STARTING_TILES
      THEN 
        IF card(players_racks |> { {} }) = 1 THEN
          players_racks := players_racks <+ {players~(xx) |-> subset_tiles} || in_sack := in_sack - subset_tiles || state := PLAYING
        ELSE
          players_racks := players_racks <+ {players~(xx) |-> subset_tiles} || in_sack := in_sack - subset_tiles
        END
      END
    END;

  /********************************** STATE: PLAYING **********************************************/
     
  play(xx) = 
    PRE xx : ran(players) & players~(xx) = player_turn & state = PLAYING
    THEN
      // select: if theres a tile in the sack
      // if can make a move
      IF player_turn = num_players THEN
        player_turn := 1
      ELSE
        player_turn := player_turn + 1
      END
    END;

  
  yy <-- is_players_turn(xx) = 
    PRE xx : ran(players) & state = PLAYING
    THEN
      IF players~(xx) = player_turn THEN
        yy := TRUE
      ELSE
        yy := FALSE
      END
    END;

// Funções para alívio mental
  xx <-- draw_initial_tiless =
    xx := card(players_racks |> { {} })

END
