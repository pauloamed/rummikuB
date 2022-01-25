MACHINE Runs

SEES Tiles, TileGames

VARIABLES
  runs

INVARIANT
  // A run is 3 or more in a row of the same color
  // Number of unique colors must be equal to 1
  // Adjacent tiles must be successors
  runs : POW(iseq1(TILES)) & runs : FIN(runs) &
  !xx.(xx : runs => ((size(xx) >= MIN_TILES_PER_GAME) & (card(COLOR[ran(xx) - TILES_JOKER]) = 1))) &
  !rr.(rr : runs => !(xx,yy).( (xx : dom(rr) & yy : dom(rr) & xx > yy & rr[{xx,yy}] /\ TILES_JOKER = {}) => ( xx - yy = NUMBER(rr(xx)) - NUMBER(rr(yy))))) &
  !rr.(rr : runs => !xx.((xx : dom(rr) & rr(xx) /: TILES_JOKER) => (xx - 1 <= NUMBER(rr(xx)) & (size(rr) - xx - 2) <= (12 - NUMBER(rr(xx))))))


INITIALISATION
  runs := {}

OPERATIONS

add_run(rr) = 
  PRE
    rr : iseq1(TILES) & // sequence 
    (size(rr) >= MIN_TILES_PER_GAME) & // has minimum amount of tiles
    (card(COLOR[ran(rr) - TILES_JOKER]) = 1) & // has only one color
    // is a contiguos sequence
    !(zz,yy).( (zz : dom(rr) & yy : dom(rr) & zz > yy & rr[{zz,yy}] /\ TILES_JOKER = {}) => ( zz - yy = NUMBER(rr(zz)) - NUMBER(rr(yy)))) &
    !zz.( (zz : dom(rr) & rr(zz) /: TILES_JOKER) => (zz - 1 <= NUMBER(rr(zz)) ) & (size(rr) - zz) <= (12 - NUMBER(rr(zz))))
  THEN runs := runs \/ {rr}
  END;

rmv_run(rr) =
  PRE rr : runs
  THEN runs := runs - {rr}
  END;

set_runs(rrs) =
  PRE rrs : POW(iseq1(TILES)) & rrs : FIN(runs)
  THEN
    runs := rrs
  END;

clear_runs = 
  PRE 1=1
  THEN
    runs := {}
  END

END
