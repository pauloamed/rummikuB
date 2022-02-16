MACHINE Rummikub

SEES Tiles, GameState, Names

INCLUDES Table

VARIABLES 
  state, player_turn
  

INVARIANT
  state : GAME_STATE & 

  /**************************************** PLAYERS **************************************************/

  player_turn : NATURAL1 & 

  // Number of players: if the game has started, there should be a valid number of players
  (state /= NOT_RUNNING => round_players : VALID_PLAYERS_NUMS) & 

  // Player turn
  (state /= NOT_RUNNING => (player_turn <= round_players)) &

  (state /= MELDING => backup_groups <: groups) &
  (state /= MELDING => backup_runs <: runs)

INITIALISATION 
  state := NOT_RUNNING || 
  player_turn := 1


OPERATIONS

  /********************************** STATE: NOT_RUNNING ************************************************/

  start_game(nn) =
    PRE state = NOT_RUNNING & nn : VALID_PLAYERS_NUMS 
    THEN 
      set_round_players(nn) || state := ADDING_PLAYERS
    END;

  /********************************** STATE: ADDING_PLAYERS **********************************************/

  add_player(xx) = // NAOM EXE EM XX
    PRE state = ADDING_PLAYERS & xx : NAME & xx /: ran(players) & card(players) < round_players
    THEN 
      IF card(players) + 1 = round_players THEN
        add_racked_player(xx) || state := DRAWING_INITIAL_TILES
      ELSE
        add_racked_player(xx)
      END
    END;

  /********************************** STATE: DRAWING_INITIAL_TILES **********************************************/

  draw_initial_tiles(xx) = 
    PRE state = DRAWING_INITIAL_TILES & xx : VALID_PLAYERS_IDS & players(xx) /= NILL & players_racks(xx) = {}
    THEN
      ANY subset_tiles 
      WHERE subset_tiles <: in_sack & card(subset_tiles) = NUM_STARTING_TILES
      THEN 
        IF card(players_racks |> { {} }) = 1 THEN
          draw_tiles(xx, subset_tiles) || state := START_TURN
        ELSE
          draw_tiles(xx, subset_tiles)
        END
      END
    END;

  /********************************** STATE: PLAYING **********************************************/
     
  next_turn(xx) = 
    PRE state = FINISH_TURN & xx : VALID_PLAYERS_IDS & players(xx) /= NILL & xx = player_turn
    THEN
      // first checks if there is a winner
      IF players_racks(xx) = {} THEN state := FINISHED
      // select: if theres a tile in the sack
      // if can make a move
      ELSIF player_turn = round_players THEN
        player_turn := 1 || state := START_TURN
      ELSE
        player_turn := player_turn + 1 || state := START_TURN
      END
    END;

  draw_tile(xx) =
    PRE state = START_TURN & xx : VALID_PLAYERS_IDS & players(xx) /= NILL & xx = player_turn
    THEN
      IF card(in_sack) > 0 THEN
        ANY yy
        WHERE yy : in_sack
        THEN 
          draw_tiles(xx, {yy}) || state := FINISH_TURN
        END
      ELSE
        state := FINISH_TURN
      END
    END;
 
  start_melding(xx) = 
    PRE state = START_TURN & xx : VALID_PLAYERS_IDS & players(xx) /= NILL & xx = player_turn
    THEN
    // NAO PODE CHAMAR SIMULTANEAMENTE OPERACOES DE UM MSM INCLUDE
    // todas essas 3 operações vem de Table
    // set_hand(players_racks(players~(xx))) || reset_rack(xx) || set_backups(xx)
      set_backups_and_more(xx) ||
      state := MELDING
    END;

  remove_group_from_table_2(xx, gg) = 
    PRE state = MELDING & xx : VALID_PLAYERS_IDS & players(xx) /= NILL & xx = player_turn & gg : TILES --> BOOL
    THEN
      remove_group_from_table(gg)
    END;

  remove_run_from_table_2(xx, rr) = 
    PRE state = MELDING & xx : VALID_PLAYERS_IDS & players(xx) /= NILL & xx = player_turn &
    rr : TILES --> RUNS_INDEXES &
    rr : ran(runs)
    THEN
      remove_run_from_table(rr)
    END;

  add_group_to_table_2(xx, gg) =
    PRE state = MELDING & xx : VALID_PLAYERS_IDS & players(xx) /= NILL & xx = player_turn &
    gg : TILES --> BOOL &
    dom(gg |> {TRUE}) <: dom(in_hand |> {TRUE})
    THEN
      add_group_to_table(gg)
    END;

  add_run_to_table_2(xx, rr) =
    PRE state = MELDING & xx : VALID_PLAYERS_IDS & players(xx) /= NILL & xx = player_turn & rr : TILES --> RUNS_INDEXES &
    dom(rr |>> {-1}) <: dom(in_hand |> {TRUE})
    THEN
      add_run_to_table(rr)
    END;

  finish_melding(xx) = 
    PRE state = MELDING & xx : VALID_PLAYERS_IDS & players(xx) /= NILL & xx = player_turn & 
    dom(in_hand |> {TRUE}) <<: dom(backup_rack |> {TRUE})
    THEN
      reset_move(xx) || state := FINISH_TURN
    END;
  
  reset_turn(xx) = 
    PRE state = MELDING & xx : VALID_PLAYERS_IDS & players(xx) /= NILL & xx = player_turn
    THEN
      recover_backups(xx) || state := START_TURN 
    END
    
  /**************************** QUERIES OPERATIONS ****************************/

/*
  yy <-- winner =
    IF state = FINISHED THEN 
      yy := {xx | xx : VALID_PLAYERS_IDS & players(xx) /= NILL & players_racks(xx) = {} }
    ELSE
      yy := {}
    END
*/
    
END
