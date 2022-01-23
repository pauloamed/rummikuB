MACHINE Rummikub

SEES Tiles

INCLUDES RackedPlayers, Sack, Groups, Runs

SETS
  
  GAME_STATE = {NOT_RUNNING, ADDING_PLAYERS, DRAWING_INITIAL_TILES, START_TURN, MELDING, FINISH_TURN, FINISHED}

CONSTANTS
  MIN_TILES_PER_GAME, MAX_TILES_PER_GAME

PROPERTIES        
  MIN_TILES_PER_GAME = 3 &
  MAX_TILES_PER_GAME = 13


VARIABLES 
  state, 
  player_turn, 
  runs, groups,
  backup_runs, backup_groups, backup_rack, in_hand

INVARIANT
  state : GAME_STATE & 

  /**************************************** PLAYERS **************************************************/

  player_turn : NATURAL1 & 


  // Number of players: if the game has started, there should be a valid number of players
  (state /= NOT_RUNNING => max_players : VALID_PLAYERS_NUMS) & 



  // Player turn
  (state /= NOT_RUNNING => (player_turn <= max_players)) &


  in_hand <: TILES &

  /************************************** PLAYERS RACKS AND SACK *************************************/

  
  UNION(xx).(xx : (ran(players_racks) \/ {aa | aa : POW(TILES) & #bb.(bb : runs & ran(bb) = aa)} \/ groups \/ {in_sack, in_hand}) | xx) = TILES &

  !xx.(xx: TILES => (card({yy | yy : (ran(players_racks) \/ {aa | aa : POW(TILES) & #bb.(bb : runs & ran(bb) = aa)} \/ groups \/ {in_sack, in_hand}) & xx : yy}) = 1)) & 

  /********************************** BACKUPS ************************************************/

  
  backup_rack <: TILES &
  backup_groups <: POW(TILES) & 
  backup_runs : POW(iseq1(TILES)) & backup_runs : FIN(backup_runs) &
  (state /= MELDING => backup_groups <: groups) &
  (state /= MELDING => backup_runs <: runs)
  

INITIALISATION 
  state := NOT_RUNNING || 
  player_turn := 1 ||
  backup_groups := {} || backup_runs := {} || backup_rack := {} || in_hand := {}

OPERATIONS

  /********************************** STATE: NOT_RUNNING ************************************************/

  start_game(nn) =
    PRE state = NOT_RUNNING & nn : VALID_PLAYERS_NUMS 
    THEN 
      num_players := nn || 
      state := ADDING_PLAYERS
    END;

  /********************************** STATE: ADDING_PLAYERS **********************************************/

  add_player(xx) = 
    PRE state = ADDING_PLAYERS & xx : NAME & xx /: ran(players) & card(players) < num_players
    THEN 
      IF card(players) + 1 = num_players THEN
        add_players(xx) || players_racks := players_racks <+ {card(players) + 1 |-> {}} || 
        state := DRAWING_INITIAL_TILES
      ELSE
        players := players <+ {card(players) + 1 |-> xx} || players_racks := players_racks <+ {card(players) + 1 |-> {}}
      END
    END;

  /********************************** STATE: DRAWING_INITIAL_TILES **********************************************/

  draw_initial_tiles(xx) = 
    PRE state = DRAWING_INITIAL_TILES & xx : ran(players) & players_racks(players~(xx)) = {}
    THEN
      ANY subset_tiles 
      WHERE subset_tiles <: in_sack & card(subset_tiles) = NUM_STARTING_TILES
      THEN 
        IF card(players_racks |> { {} }) = 1 THEN
          add_tiles_to_hand(xx, subset_tiles) || rmv_from_sack(subset_tiles) || 
          state := START_TURN
        ELSE
          add_tiles_to_hand(xx, subset_tiles) || rmv_from_sack(subset_tiles)
        END
      END
    END;

  /********************************** STATE: PLAYING **********************************************/
     
  next_turn(xx) = 
    PRE state = FINISH_TURN & xx : ran(players) & players~(xx) = player_turn
    THEN
      // first checks if there is a winner
      IF players_racks(players~(xx)) = {} THEN
        state := FINISHED
      // select: if theres a tile in the sack
      // if can make a move
      ELSIF player_turn = num_players THEN
        player_turn := 1 || state := START_TURN
      ELSE
        player_turn := player_turn + 1 || 
        state := START_TURN
      END
    END;

  draw_tile(xx) =
    PRE state = START_TURN & xx : ran(players) & players~(xx) = player_turn
    THEN
      IF card(in_sack) > 0 THEN
        ANY yy
        WHERE yy : in_sack
        THEN 
          rmv_from_sack({yy}) || add_tiles_to_hand(xx, {yy}) || 
          state := FINISH_TURN
        END
      ELSE
        state := FINISH_TURN
      END
    END;
 
  start_melding(xx) = 
    PRE state = START_TURN & xx : ran(players) & players~(xx) = player_turn
    THEN
      in_hand := players_racks(players~(xx)) || reset_hand(xx) ||
      backup_groups := groups || backup_runs := runs || backup_rack := players_racks(players~(xx)) ||
      state := MELDING
    END;

  remove_group(xx, gg) = 
    PRE state = MELDING & xx : ran(players) & players~(xx) = player_turn & gg : groups
    THEN
      rmv_group(gg) || in_hand := in_hand \/ gg
    END;

  remove_run(xx, rr) = 
    PRE state = MELDING & xx : ran(players) & players~(xx) = player_turn & rr : runs
    THEN
      rmv_run(rr) || in_hand := in_hand \/ ran(rr)
    END;

  add_group(xx, gg) =
    PRE state = MELDING & xx : ran(players) & players~(xx) = player_turn &
    gg <: in_hand &
    (card(gg) >= MIN_TILES_PER_GAME) & (card(COLOR[gg]) = card(gg)) & (card(NUMBER[gg - TILES_JOKER]) = 1)
    THEN
      add_group(gg) || in_hand := in_hand - gg
    END;

  add_run(xx, rr) =
    PRE state = MELDING & xx : ran(players) & players~(xx) = player_turn & 
    rr : iseq1(TILES) & ran(rr) <: in_hand &
    (size(rr) >= MIN_TILES_PER_GAME) & (card(COLOR[ran(rr) - TILES_JOKER]) = 1) &
    !(xx,yy).( (xx : dom(rr) & yy : dom(rr) & xx > yy & rr[{xx,yy}] /\ TILES_JOKER = {}) => ( xx - yy = NUMBER(rr(xx)) - NUMBER(rr(yy)))) &
    !xx.((xx : dom(rr) & rr(xx) /: TILES_JOKER) => (xx <= NUMBER(rr(xx)) & (size(rr) - xx - 1) <= (12 - NUMBER(rr(xx)))))
    THEN
      add_run(rr) || in_hand := in_hand - ran(rr)
    END;

  finish_melding(xx) = 
    PRE state = MELDING & xx : ran(players) & players~(xx) = player_turn & in_hand <<: backup_rack
    THEN
      state := FINISH_TURN || backup_runs := {} || backup_groups := {} || backup_rack := {} || set_hand(xx,in_hand) || in_hand := {}
    END;
  
  reset_turn(xx) = 
    PRE state = MELDING & xx : ran(players) & players~(xx) = player_turn
    THEN
      runs := backup_runs || groups := backup_groups || set_hand(xx,backup_rack) || in_hand := {} ||
      state := START_TURN 
    END;


  // A primeira linha tem que ser um PRE ao invés de IF, mas fica assim pra visualizar o processo
  yy <-- winner =
    IF state = FINISHED THEN 
      yy := {xx | xx : ran(players) & players_racks(players~(xx)) = {} }
    ELSE
      yy := {}
    END
    
//  yy <-- player_score(xx) =
//    yy := SIGMA (zz) . (zz : players_racks(players~(xx)) | NUMBER(zz) + 1)

END
