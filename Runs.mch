MACHINE Runs

SEES Tiles, TileGames

CONSTANTS RUNS_INDEXES
PROPERTIES RUNS_INDEXES = 0..13


VARIABLES
  free_indexes, runs

INVARIANT
  free_indexes : GAME_INDEXES --> BOOL &
  runs : GAME_INDEXES --> (TILES --> RUNS_INDEXES) &
  

  // A run is 3 or more in a row of the same color
  // Number of unique colors must be equal to 1
  // Adjacent tiles must be successors
  !rr.(rr : ran(runs) => ((card(rr) >= MIN_TILES_PER_GAME) & (card(COLOR[ran(rr) - TILES_JOKER]) = 1))) &
  !rr.(rr : ran(runs) => !(xx,yy).( (xx : dom(rr) & yy : dom(rr) & xx > yy & rr[{xx,yy}] /\ TILES_JOKER = {}) => ( xx - yy = NUMBER(rr(xx)) - NUMBER(rr(yy))))) &
  !rr.(rr : ran(runs) => !xx.((xx : dom(rr) & rr(xx) /: TILES_JOKER) => (xx - 1 <= NUMBER(rr(xx)) & (size(rr) - xx - 2) <= (12 - NUMBER(rr(xx))))))


INITIALISATION
  runs := {} || free_indexes := GAME_INDEXES * {TRUE}

OPERATIONS

add_run(rr) = 
  PRE
    rr : TILES --> RUNS_INDEXES & // sequence 
    (size(rr) >= MIN_TILES_PER_GAME) & // has minimum amount of tiles
    (card(COLOR[ran(rr) - TILES_JOKER]) = 1) & // has only one color
    // is a contiguos sequence
    !(zz,yy).( (zz : dom(rr) & yy : dom(rr) & zz > yy & rr[{zz,yy}] /\ TILES_JOKER = {}) => ( zz - yy = NUMBER(rr(zz)) - NUMBER(rr(yy)))) &
    !zz.( (zz : dom(rr) & rr(zz) /: TILES_JOKER) => (zz - 1 <= NUMBER(rr(zz)) ) & (size(rr) - zz) <= (12 - NUMBER(rr(zz))))
  THEN 
    ANY next_idx WHERE next_idx = min(dom(free_indexes|>{FALSE})) THEN
    runs(next_idx) := rr ||
    free_indexes(next_idx) := FALSE
    END
  END;

rmv_run(rr) =
  PRE 
    rr : TILES --> RUNS_INDEXES
  THEN 
    runs := runs |>> {rr} // ainda falta livrar o indice
  END;

set_runs(rrs) =
  PRE rrs: GAME_INDEXES --> (TILES --> RUNS_INDEXES)
  THEN
    runs := rrs
  END;

clear_runs = 
  PRE 1=1
  THEN
    runs := {}
  END

END
