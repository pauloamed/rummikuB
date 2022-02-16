MACHINE Table

SEES Tiles, Names, TileGames

INCLUDES RackedPlayers, Sack, Groups, Runs, Hand

CONSTANTS
  bool2int

PROPERTIES
  bool2int : BOOL --> 0..1 & bool2int(TRUE) = 1 & bool2int(FALSE) = 0

PROMOTES 
  add_group, rmv_group, 
  add_run, rmv_run,
  add_racked_player, set_round_players

VARIABLES
  backup_runs, backup_groups, backup_rack

INVARIANT

  !xx.(xx: TILES =>
    (SIGMA yy . (yy : ran(players_racks) | bool2int(yy(xx)))) + 
    (SIGMA yy . (yy : ran(runs) | bool2int(bool(yy(xx) /= -1)))) + 
    bool2int(bool(groups(xx) /= 0)) +
    bool2int(in_hand(xx)) +
    bool2int(in_sack(xx)) 
    = 1
  ) & 

  /********************************** BACKUPS ************************************************/

  backup_rack : TILES --> BOOL &
  backup_groups : TILES --> GAME_INDEXES & 
  backup_runs : GAME_INDEXES --> (TILES --> RUNS_INDEXES)

INITIALISATION
  backup_groups := {} || backup_runs := {} || backup_rack := {}

OPERATIONS

draw_tiles(xx, tts) = 
  PRE xx : NAME & xx : ran(players) & tts : TILES --> BOOL
  THEN
    add_tiles_to_hand(xx, tts) || rmv_from_sack(tts)
  END;

// antigo reset_backup
reset_move(xx) =
  PRE xx : NAME & xx : ran(players)
  THEN
    backup_runs := {} || backup_groups := {} || backup_rack := {}/*Adicionado->*/ || reset_hand || set_rack(xx,in_hand)
  END;
  

remove_group_from_table(gg) = 
  PRE gg : TILES --> BOOL
  THEN
    rmv_group(gg) || add_to_hand(gg)
  END;

remove_run_from_table(rr) = 
  PRE rr : TILES --> -1..200 & rr : ran(runs)
  THEN
    rmv_run(rr) || add_to_hand(((TILES * {FALSE}) <+ dom(rr |>> {-1}) * {TRUE}))
  END;

add_group_to_table(gg) =
  PRE gg : TILES --> BOOL & dom(gg |> {TRUE}) <: dom(in_hand |> {TRUE})
  THEN
    add_group(gg) || rmv_from_hand(gg)
  END;

add_run_to_table(rr) =
  PRE rr : TILES --> -1..200 & dom(rr |>> {-1}) <: dom(in_hand |> {TRUE})
  THEN
    add_run(rr) || rmv_from_hand((TILES * {FALSE}) <+ dom(rr |>> {-1}) * {TRUE})
  END;

set_backups_and_more(xx) =
  PRE xx : NAME
  THEN
    backup_runs := runs || backup_groups := groups || backup_rack := players_racks(players~(xx)) ||
    set_hand(players_racks(players~(xx))) || reset_rack(xx)
  END;
  
recover_backups(xx) =
  PRE xx : NAME /*&
      backup_runs : POW(iseq(TILES)) &
      backup_groups : FIN(backup_groups) &
      backup_rack <: TILES*/
  THEN
    set_runs(backup_runs) || set_groups(backup_groups) || set_rack(xx, backup_rack) || reset_hand
  END

END
