MACHINE Table

SEES Tiles, Names

INCLUDES RackedPlayers, Sack, Groups, Runs, Hand

PROMOTES 
  add_group, rmv_group, 
  add_run, rmv_run,
  set_sack,
  add_racked_player, set_rack, reset_rack, set_round_players,
  reset_hand, set_hand

VARIABLES
  backup_runs, backup_groups, backup_rack

INVARIANT
  UNION(xx).(xx :                                               // the union between
    (ran(players_racks) \/                                      // player racks
    {aa | aa : POW(TILES) & #bb.(bb : runs & ran(bb) = aa)} \/  // runs
    groups \/                                                   // groups
    {in_sack, in_hand}                                          // in_sack and in_hand
  ) | xx) = TILES &                                             // comprises all tiles

  !xx.(xx: TILES =>                                               // each tile
    (card({yy | yy : 
      (ran(players_racks) \/                                      // either belongs to a player rack
      {aa | aa : POW(TILES) & #bb.(bb : runs & ran(bb) = aa)} \/  // or to a run
      groups \/                                                   // or to a group
      {in_sack, in_hand}) & xx : yy}                              // or into sack or to in_hand
    ) = 1)
  ) & 

  /********************************** BACKUPS ************************************************/

  backup_rack <: TILES &
  backup_groups <: POW(TILES) & 
  backup_runs : POW(iseq1(TILES)) & backup_runs : FIN(backup_runs)

INITIALISATION
  backup_groups := {} || backup_runs := {} || backup_rack := {}

OPERATIONS

draw_tiles(xx, tts) = 
  PRE xx : ran(players)
  THEN
    add_tiles_to_hand(xx, tts) || rmv_from_sack(tts)
  END;

reset_backups =
  backup_runs := {} || backup_groups := {} || backup_rack := {};

remove_group_from_table(gg) = 
  PRE gg : groups
  THEN
    rmv_group(gg) || add_to_hand(gg)
  END;

remove_run_from_table(rr) = 
  PRE rr : runs
  THEN
    rmv_run(rr) || add_to_hand(ran(rr))
  END;

add_group_to_table(gg) =
  PRE gg <: in_hand
  THEN
    add_group(gg) || rmv_from_hand(gg)
  END;

add_run_to_table(rr) =
  PRE rr : iseq1(TILES) & ran(rr) <: in_hand
  THEN
    add_run(rr) || rmv_from_hand(ran(rr))
  END;

set_backups(xx) =
  PRE xx : NAME
  THEN backup_runs := runs || backup_groups := groups || backup_rack := players_racks(players~(xx))
  END;
  
recover_backups(xx) =
  set_runs(backup_runs) || set_groups(backup_groups) || set_rack(xx, backup_rack)



END