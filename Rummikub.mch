MACHINE Rummikub

SETS
  NAME;
  GAME_STATE = {NOT_RUNNING, ADDING_PLAYERS, DRAWING_INITIAL_TILES, RUNNING, FINISHED}

CONSTANTS
  tiles, NUM_STARTING_TILES, valid_players_nums

PROPERTIES        
  tiles = 1..103 &
  NUM_STARTING_TILES = 14 & 
  valid_players_nums = 2..4

VARIABLES in_sack, players_racks, players, state, num_players, player_turn

INVARIANT
  // Current game state
  state : GAME_STATE & 

  // Number of players: if the game has started, there should be a valid number of players
  (state /= NOT_RUNNING => num_players : valid_players_nums) & 

  // Player turn
  (state /= NOT_RUNNING => player_turn <= num_players) &
  player_turn : NATURAL1 &

  // Sack contains valid tiles
  in_sack <: tiles &

  // Players: a function of names (but parcial injective and indexed by naturals)
(state /= NOT_RUNNING => players : 1..10 >+> NAME) &

  // Players racks
  players_racks : 1..10 +-> POW(tiles) &
  dom(players_racks) = dom(players) & // 
  UNION ( ss ) . (ss : dom(players_racks) | players_racks(ss)) /\ in_sack = {}
  //INTER ( ss ) . (ss : dom(players_racks) | players_racks(ss)) = {}

INITIALISATION 
  state := NOT_RUNNING || in_sack := {} || players_racks := {} || players := {} || num_players := 0 || player_turn := 1

OPERATIONS

  start_game(nn) =
    PRE state = NOT_RUNNING & nn : valid_players_nums
    THEN num_players := nn || state := ADDING_PLAYERS
    END;


  add_player(xx) = 
    PRE xx : NAME & xx /: ran(players) & state = ADDING_PLAYERS & card(players) < num_players
    THEN 
      IF card(players) + 1 = num_players THEN
        players := players <+ {card(players) + 1 |-> xx} || players_racks := players_racks <+ {card(players) + 1 |-> {}} || state := DRAWING_INITIAL_TILES || in_sack := tiles
      ELSE
        players := players <+ {card(players) + 1 |-> xx} || players_racks := players_racks <+ {card(players) + 1 |-> {}}
      END
    END;

  draw_initial_tiles(xx) = 
    PRE xx : ran(players) & players_racks(players~(xx)) = {} & state = DRAWING_INITIAL_TILES
    THEN
      ANY subset_tiles 
      WHERE subset_tiles <: in_sack & card(subset_tiles) = NUM_STARTING_TILES
      THEN 
        IF card(players_racks |> { {} }) = 1 THEN
          players_racks := players_racks <+ {players~(xx) |-> subset_tiles} || in_sack := in_sack - subset_tiles || state := RUNNING
        ELSE
          players_racks := players_racks <+ {players~(xx) |-> subset_tiles} || in_sack := in_sack - subset_tiles
        END
      END
    END;
     
  play(xx) = 
    PRE xx : ran(players) & players~(xx) = player_turn & state = RUNNING
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
    PRE xx : ran(players) & state = RUNNING
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
