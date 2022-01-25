MACHINE Table

SEES Tiles, Names, TileGames

INCLUDES RackedPlayers, Sack, Groups, Runs, Hand

PROMOTES 
  add_group, rmv_group, 
  add_run, rmv_run,
  add_racked_player, set_round_players

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
  PRE xx : ran(players) & tts <: in_sack & tts /\ players_racks(players~(xx)) = {} &
    UNION(xx1).(xx1 :                                               // the union between
    (ran(players_racks <+ {players~(xx) |-> (players_racks(players~(xx)) \/ tts)}) \/                                      // player racks
    {aa | aa : POW(TILES) & #bb.(bb : runs & ran(bb) = aa)} \/  // runs
    groups \/                                                   // groups
    {in_sack - tts, in_hand}                                          // in_sack and in_hand
  ) | xx1) = TILES                                              // comprises all tiles
  THEN
    add_tiles_to_hand(xx, tts) || rmv_from_sack(tts)
  END;

// antigo reset_backup
reset_move(xx) =
  PRE xx : ran(players) &
    UNION(xx1).(xx1 :                                                 // the union between
        (ran(players_racks) \/                                      // player racks
        {aa | aa : POW(TILES) & #bb.(bb : runs & ran(bb) = aa)} \/  // runs
        groups \/                                                   // groups
        {in_sack, in_hand}                                          // in_sack and in_hand
      ) | xx1) = TILES &                                           // comprises all tiles

  !xx1.(xx1: TILES =>                                               // each tile
    (card({yy | yy : 
      (ran(players_racks) \/                                      // either belongs to a player rack
      {aa | aa : POW(TILES) & #bb.(bb : runs & ran(bb) = aa)} \/  // or to a run
      groups \/                                                   // or to a group
      {in_sack, in_hand}) & xx1 : yy}                              // or into sack or to in_hand
    ) = 1)
      )
  THEN
    backup_runs := {} || backup_groups := {} || backup_rack := {}/*Adicionado->*/ || reset_hand || set_rack(xx,in_hand)
  END;

remove_group_from_table(gg) = 
  PRE gg : groups &
      gg : FIN(gg) &
      gg <: TILES &
      gg /\ in_hand = {} &
      UNION(xx).(xx :                                               // the union between
        (ran(players_racks) \/                                      // player racks
        {aa | aa : POW(TILES) & #bb.(bb : runs & ran(bb) = aa)} \/  // runs
        groups - {gg} \/                                                   // groups
        {in_sack, in_hand \/ gg}                                          // in_sack and in_hand
      ) | xx) = TILES &                                           // comprises all tiles

  !xx.(xx: TILES =>                                               // each tile
    (card({yy | yy : 
      (ran(players_racks) \/                                      // either belongs to a player rack
      {aa | aa : POW(TILES) & #bb.(bb : runs & ran(bb) = aa)} \/  // or to a run
      groups - {gg}\/                                                   // or to a group
      {in_sack, in_hand \/ gg}) & xx : yy}                              // or into sack or to in_hand
    ) = 1)
        )
  THEN
    rmv_group(gg) || add_to_hand(gg)
  END;

remove_run_from_table(rr) = 
  PRE rr : runs &
      ran(rr) : FIN(ran(rr)) &
      ran(rr) <: TILES &
      ran(rr) /\ in_hand = {} &
      UNION(xx).(xx :                                               // the union between
        (ran(players_racks) \/                                      // player racks
        {aa | aa : POW(TILES) & #bb.(bb : runs - {rr} & ran(bb) = aa)} \/  // runs
        groups \/                                                   // groups
        {in_sack, in_hand \/ ran(rr)}                                          // in_sack and in_hand
      ) | xx) = TILES &                                           // comprises all tiles

  !xx.(xx: TILES =>                                               // each tile
    (card({yy | yy : 
      (ran(players_racks) \/                                      // either belongs to a player rack
      {aa | aa : POW(TILES) & #bb.(bb : runs - {rr} & ran(bb) = aa)} \/  // or to a run
      groups \/                                                   // or to a group
      {in_sack, in_hand \/ ran(rr)}) & xx : yy}                              // or into sack or to in_hand
    ) = 1)
        )
  THEN
    rmv_run(rr) || add_to_hand(ran(rr))
  END;

add_group_to_table(gg) =
  PRE gg : POW(TILES) & gg /: groups & gg <: in_hand &
      !xx.(xx : groups \/ {gg} => 
          (card(xx) >= MIN_TILES_PER_GAME) &
          (card(COLOR[xx]) = card(xx)) & 
          (card(NUMBER[xx - TILES_JOKER]) = 1) &
          card(xx) <= MAX_TILES_PER_GROUPS
      ) &
      UNION(xx).(xx :                                               // the union between
        (ran(players_racks) \/                                      // player racks
        {aa | aa : POW(TILES) & #bb.(bb : runs & ran(bb) = aa)} \/  // runs
        (groups \/ {gg}) \/                                                   // groups
        {in_sack, in_hand - gg}                                          // in_sack and in_hand
      ) | xx) = TILES &                                           // comprises all tiles

  !xx.(xx: TILES =>                                               // each tile
    (card({yy | yy : 
      (ran(players_racks) \/                                      // either belongs to a player rack
      {aa | aa : POW(TILES) & #bb.(bb : runs & ran(bb) = aa)} \/  // or to a run
      (groups \/ {gg}) \/                                                   // or to a group
      {in_sack, in_hand - gg}) & xx : yy}                              // or into sack or to in_hand
    ) = 1)
        )
  THEN
    add_group(gg) || rmv_from_hand(gg)
  END;

add_run_to_table(rr) =
  PRE rr : iseq1(TILES) & 
    rr : seq(ran(rr)) &// sequence 
    ran(rr) <: in_hand &
    COLOR[ran(rr) - TILES_JOKER] : FIN(COLOR[ran(rr) - TILES_JOKER]) &
    !xx.(xx : runs \/ {rr} => ((size(xx) >= MIN_TILES_PER_GAME) & (card(COLOR[ran(xx) - TILES_JOKER]) = 1))) & // has minimum amount of tiles and has only one color
    !rr2.(rr2 : runs \/ {rr} => !(xx,yy).( (xx : dom(rr2) & yy : dom(rr2) & xx > yy & rr2[{xx,yy}] /\ TILES_JOKER = {}) => ( xx - yy = NUMBER(rr2(xx)) - NUMBER(rr2(yy))))) &
    !rr2.(rr2 : runs \/ {rr} => !xx.((xx : dom(rr2) & rr2(xx) /: TILES_JOKER) => (xx - 1 <= NUMBER(rr2(xx)) & (size(rr2) - xx - 2) <= (12 - NUMBER(rr2(xx)))))) &// is a contiguos sequence
    UNION(xx).(xx :                                               // the union between
        (ran(players_racks) \/                                      // player racks
        {aa | aa : POW(TILES) & #bb.(bb : (runs \/ {rr}) & ran(bb) = aa)} \/  // runs
        groups \/                                                   // groups
        {in_sack, in_hand - ran(rr)}                                          // in_sack and in_hand
      ) | xx) = TILES &                                           // comprises all tiles

  !xx.(xx: TILES =>                                               // each tile
    (card({yy | yy : 
      (ran(players_racks) \/                                      // either belongs to a player rack
      {aa | aa : POW(TILES) & #bb.(bb : (runs \/ {rr}) & ran(bb) = aa)} \/  // or to a run
      groups \/                                                   // or to a group
      {in_sack, in_hand - ran(rr)}) & xx : yy}                              // or into sack or to in_hand
    ) = 1)
        )
  THEN
    add_run(rr) || rmv_from_hand(ran(rr))
  END;

set_backups_and_more(xx) =
  PRE xx : dom(players~)
  THEN
    backup_runs := runs || backup_groups := groups || backup_rack := players_racks(players~(xx)) ||
    /*Adicionado->*/set_hand(players_racks(players~(xx))) || reset_rack(xx)
  END;
  
recover_backups(xx) =
  PRE xx : ran(players) &
      backup_runs : POW(iseq(TILES)) &
      backup_groups : FIN(backup_groups) &
      backup_rack <: TILES &
      UNION(xx1).(xx1 : 
         (ran(players_racks <+ {players~(xx) |-> backup_rack}) \/
         {aa | aa : POW(TILES) & #(bb).(bb : backup_runs & ran(bb) = aa) } \/ 
         backup_groups \/
         {in_sack, in_hand}
      ) | xx1) = TILES & // End Union
      !xx1.(xx1 : backup_runs => ((size(xx1) >= MIN_TILES_PER_GAME) & (card(COLOR[ran(xx1) - TILES_JOKER]) = 1))) &
      !rr.(rr : backup_runs => !(xx1,yy).( (xx1 : dom(rr) & yy : dom(rr) & xx1 > yy & rr[{xx1,yy}] /\ TILES_JOKER = {}) => ( xx1 - yy = NUMBER(rr(xx1)) - NUMBER(rr(yy))))) &
      !rr.(rr : backup_runs => !xx1.((xx1 : dom(rr) & rr(xx1) /: TILES_JOKER) => (xx1 - 1 <= NUMBER(rr(xx1)) & (size(rr) - xx1 - 2) <= (12 - NUMBER(rr(xx1)))))) &
      !xx1.(xx1 : backup_groups => 
        (card(xx1) >= MIN_TILES_PER_GAME) &
        (card(COLOR[xx1]) = card(xx1)) & 
        (card(NUMBER[xx1 - TILES_JOKER]) = 1) &
        card(xx1) <= MAX_TILES_PER_GROUPS
       )
  THEN
    set_runs(backup_runs) || set_groups(backup_groups) || set_rack(xx, backup_rack) || reset_hand
  END


END