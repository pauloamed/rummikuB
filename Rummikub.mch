MACHINE Rummikub

SEES Tiles, GameState, Names, TileGames

INCLUDES Table

VARIABLES 
  state, player_turn
  

INVARIANT
  state : GAME_STATE & 

  /**************************************** PLAYERS **************************************************/

  player_turn : NATURAL1 & 

  // Number of players: if the game has started, there should be a valid number of players
  (state /= NOT_RUNNING => (round_players : VALID_PLAYERS_NUMS) & (player_turn <= round_players)) &

  (state /= MELDING => (backup_groups <: groups) & (backup_runs <: runs))

INITIALISATION 
  state := NOT_RUNNING || 
  player_turn := 1


OPERATIONS

  /********************************** STATE: NOT_RUNNING ************************************************/

  start_game(nn) =
    PRE state = NOT_RUNNING & nn : VALID_PLAYERS_NUMS & card(players) = 0 &
        player_turn <= nn & backup_groups <: groups & backup_runs <: runs
    THEN 
      set_round_players(nn) || state := ADDING_PLAYERS
    END;

  /********************************** STATE: ADDING_PLAYERS **********************************************/

  add_player(xx) = 
    PRE state = ADDING_PLAYERS & xx : NAME & xx /: ran(players) &
        card(players) < round_players &
        players <+ {card(players) + 1 |-> xx} : VALID_PLAYERS_IDS >+> NAME &
        players_racks <+ {card(players) + 1 |-> {}} : VALID_PLAYERS_IDS +-> POW(TILES) &
        round_players : VALID_PLAYERS_NUMS & player_turn <= round_players &
        backup_groups <: groups & backup_runs <: runs
    THEN 
      IF card(players) + 1 = round_players THEN
        add_racked_player(xx) || state := DRAWING_INITIAL_TILES
      ELSE IF card(players <+ {card(players) + 1 |-> xx}) <= round_players THEN
        add_racked_player(xx)
      END
      END
    END;

  /********************************** STATE: DRAWING_INITIAL_TILES **********************************************/

  draw_initial_tiles(xx) = 
    PRE state = DRAWING_INITIAL_TILES & xx : ran(players) & players_racks(players~(xx)) = {} &
        round_players : VALID_PLAYERS_NUMS &
        player_turn <= round_players & backup_groups <: groups & backup_runs <: runs
    THEN
      ANY subset_tiles 
      WHERE subset_tiles <: in_sack & subset_tiles : FIN(subset_tiles) & card(subset_tiles) = NUM_STARTING_TILES &
          UNION(xx1).(xx1 :
              ran(players_racks <+ {players~(xx) |-> (players_racks(players~(xx)) \/subset_tiles)}) \/
              { aa | aa : POW(TILES) & #(bb).(bb : runs & ran(bb) = aa) } \/
              groups \/
              {in_sack - subset_tiles, in_hand} | xx1) = TILES &
          players_racks |> {{}} : FIN(players_racks |> {{}})
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
    PRE player_turn + 1 : NATURAL1 & state = FINISH_TURN & xx : ran(players) & players~(xx) = player_turn & round_players : VALID_PLAYERS_NUMS & backup_groups <: groups & backup_runs <: runs
    THEN
      // first checks if there is a winner
      IF players_racks(players~(xx)) = {} THEN state := FINISHED
      // select: if theres a tile in the sack
      // if can make a move
      ELSIF player_turn = round_players THEN
        player_turn := 1 || state := START_TURN
      ELSE
        player_turn := player_turn + 1 || state := START_TURN
      END
    END;

  draw_tile(xx) =
    PRE state = START_TURN & xx : ran(players) & players~(xx) = player_turn & round_players : VALID_PLAYERS_NUMS & backup_groups <: groups & backup_runs <: runs
    THEN
      IF card(in_sack) > 0 THEN
        ANY yy
        WHERE yy : in_sack & {yy} /\ players_racks(players~(xx)) = {} &
            UNION(xx1).(xx1 : ran(players_racks <+ {players~(xx) |->
            (players_racks(players~(xx)) \/ {yy})}) \/
            { aa | aa : POW(TILES) & #(bb).(bb : runs & ran(bb) = aa) } \/
            groups \/
            {in_sack - {yy}, in_hand} | xx1) = TILES
        THEN 
          draw_tiles(xx, {yy}) || state := FINISH_TURN
        END
      ELSE
        state := FINISH_TURN
      END
    END;
 
  start_melding(xx) = 
    PRE state = START_TURN & xx : ran(players) & players~(xx) = player_turn &
        players_racks(players~(xx)) : FIN(players_racks(players~(xx))) &
        round_players : VALID_PLAYERS_NUMS & backup_groups <: groups & backup_runs <: runs
    THEN
    // NAO PODE CHAMAR SIMULTANEAMENTE OPERACOES DE UM MSM INCLUDE
    // todas essas 3 operações vem de Table
    // set_hand(players_racks(players~(xx))) || reset_rack(xx) || set_backups(xx)
      set_backups_and_more(xx) ||
      state := MELDING
    END;

  remove_group_from_table_2(xx, gg) = 
    PRE state = MELDING & xx : ran(players) &
        gg : groups &
        gg : FIN(gg) &
        gg /\ in_hand = {} &
        UNION(xx).(xx : ran(players_racks) \/
            { aa | aa : POW(TILES) & #(bb).(bb : runs & ran(bb) = aa) } \/
            groups - {gg} \/
            {in_sack, in_hand \/ gg} | xx) = TILES &
        players~(xx) = player_turn &
        !xx1.(xx1: TILES => (card({yy | yy : 
          (ran(players_racks) \/
          {aa | aa : POW(TILES) & #bb.(bb : runs & ran(bb) = aa)} \/
          groups - {gg} \/
          {in_sack, in_hand \/ gg}) & xx1 : yy}) = 1)
        )
    THEN
      remove_group_from_table(gg)
    END;

  remove_run_from_table_2(xx, rr) = 
    PRE state = MELDING & xx : ran(players) & players~(xx) = player_turn &
        rr : runs & ran(rr) : FIN(ran(rr)) & ran(rr) <: TILES &
        ran(rr) /\ in_hand = {} &
        UNION(xx).(xx :
            ran(players_racks) \/
            { aa | aa : POW(TILES) & #(bb).(bb : runs - {rr} & ran(bb) = aa) } \/
            groups \/
            {in_sack, in_hand \/ ran(rr)} | xx) = TILES &
        !xx1.(xx1 : TILES => card({ yy | yy :
            ran(players_racks) \/
            { aa | aa : POW(TILES) & #(bb).(bb : runs - {rr} & ran(bb) = aa) } \/
            groups \/
            {in_sack, in_hand \/ ran(rr)} & xx1 : yy }) = 1)
    THEN
      remove_run_from_table(rr)
    END;

  add_group_to_table_2(xx, gg) =
    PRE state = MELDING & xx : ran(players) & players~(xx) = player_turn &
        gg <: in_hand & gg /: groups &
        UNION(xx).(xx :
            ran(players_racks) \/
            { aa | aa : POW(TILES) & #(bb).(bb : runs & ran(bb) = aa) } \/
            (groups \/ {gg}) \/
            {in_sack, in_hand - gg} | xx) = TILES &
        !xx1.(xx1 : TILES => card({ yy | yy :
            ran(players_racks) \/
            { aa | aa : POW(TILES) & #(bb).(bb : runs & ran(bb) = aa) } \/
            (groups \/ {gg}) \/
            {in_sack, in_hand - gg} & xx1 : yy }) = 1) &
        !xx1.(xx1 : groups \/ {gg} => 
            (card(xx1) >= MIN_TILES_PER_GAME) &
            (card(COLOR[xx1]) = card(xx1)) & 
            (card(NUMBER[xx1 - TILES_JOKER]) = 1) &
            card(xx1) <= MAX_TILES_PER_GROUPS)
    THEN
      add_group_to_table(gg)
    END;

  add_run_to_table_2(xx, rr) =
    PRE state = MELDING & xx : ran(players) & players~(xx) = player_turn & 
        rr : iseq1(TILES) & ran(rr) <: in_hand &
        rr /: runs &
        rr : seq(ran(rr)) &
        COLOR[ran(rr) - TILES_JOKER] : FIN(COLOR[ran(rr) - TILES_JOKER]) &
        UNION(xx).(xx :
            ran(players_racks) \/
            { aa | aa : POW(TILES) & #(bb).(bb : runs \/ {rr} & ran(bb) = aa) } \/
            groups \/
            {in_sack, in_hand - ran(rr)} | xx) = TILES &
        !xx1.(xx1 : runs \/ {rr} => ((size(xx1) >= MIN_TILES_PER_GAME) &
            (card(COLOR[ran(xx1) - TILES_JOKER]) = 1))) &
        !rr1.(rr1 : runs \/ {rr} => !(xx1,yy).( (xx1 : dom(rr1) & yy : dom(rr1) & xx1 > yy & rr1[{xx1,yy}] /\ TILES_JOKER = {}) => ( xx1 - yy = NUMBER(rr1(xx1)) - NUMBER(rr1(yy))))) &
        !rr1.(rr1 : runs \/ {rr} => !xx1.((xx1 : dom(rr1) & rr1(xx1) /: TILES_JOKER) => (xx1 - 1 <= NUMBER(rr1(xx1)) & (size(rr1) - xx1 - 2) <= (12 - NUMBER(rr1(xx1)))))) &
        !xx1.(xx1: TILES => (card({yy | yy : 
            (ran(players_racks) \/ 
            {aa | aa : POW(TILES) & #bb.(bb : (runs \/ {rr}) & ran(bb) = aa)} \/
            groups \/
            {in_sack, in_hand - ran(rr)}) & xx1 : yy}) = 1)
        )
    THEN
      add_run_to_table(rr)
    END;

  finish_melding(xx) = 
    PRE state = MELDING & xx : ran(players) & players~(xx) = player_turn & in_hand <<: backup_rack & round_players : VALID_PLAYERS_NUMS &
        UNION(xx1).(xx1 :
            ran(players_racks) \/
            { aa | aa : POW(TILES) & #(bb).(bb : runs & ran(bb) = aa) } \/
            groups \/
            {in_sack, in_hand} | xx1) = TILES
    THEN
    // NAO PODE CHAMAR SIMULTANEAMENTE OPERACOES DE UM MSM INCLUDE
    // reset_backup || reset_hand || set_rack(xx, in_hand) || state := FINISH_TURN
    // Oq tava antes era o reset_backup, e como ele só era usado aqui e em conjunto com aquelas outras operações,
    // dava pra colocar elas dentro do reset_backup pra fzr funcionar. Falta só achar um nome melhor.
      reset_move(xx) || state := FINISH_TURN
    END;
  
  reset_turn(xx) = 
    PRE state = MELDING & xx : ran(players) &
        players~(xx) = player_turn & round_players : VALID_PLAYERS_NUMS &
        backup_runs : POW(iseq(TILES)) &
        backup_groups : FIN(backup_groups) &
        backup_rack <: TILES & backup_rack : FIN(backup_rack) &
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
          card(xx1) <= MAX_TILES_PER_GROUPS)
    THEN
    // NAO PODE CHAMAR SIMULTANEAMENTE OPERACOES DE UM MSM INCLUDE
    // recover_backups(xx) || reset_hand || state := START_TURN 
    // recover_backups só é chamado aqui, então bora por o reset_hand dentro (é oq funciona man k)
      recover_backups(xx) || state := START_TURN 
    END;

  /**************************** QUERIES OPERATIONS ****************************/

  yy <-- winner =
    IF state = FINISHED THEN 
      yy := {xx | xx : ran(players) & players_racks(players~(xx)) = {} }
    ELSE
      yy := {}
    END
    
END
