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
    rr : iseq1(TILES) & 
    rr : seq(ran(rr)) &// sequence 
    COLOR[ran(rr) - TILES_JOKER] : FIN(COLOR[ran(rr) - TILES_JOKER]) &
    !xx.(xx : runs \/ {rr} => ((size(xx) >= MIN_TILES_PER_GAME) & (card(COLOR[ran(xx) - TILES_JOKER]) = 1))) & // has minimum amount of tiles and has only one color
    !rr2.(rr2 : runs \/ {rr} => !(xx,yy).( (xx : dom(rr2) & yy : dom(rr2) & xx > yy & rr2[{xx,yy}] /\ TILES_JOKER = {}) => ( xx - yy = NUMBER(rr2(xx)) - NUMBER(rr2(yy))))) &
    !rr2.(rr2 : runs \/ {rr} => !xx.((xx : dom(rr2) & rr2(xx) /: TILES_JOKER) => (xx - 1 <= NUMBER(rr2(xx)) & (size(rr2) - xx - 2) <= (12 - NUMBER(rr2(xx)))))) // is a contiguos sequence
  THEN runs := runs \/ {rr}
  END;

rmv_run(rr) =
  PRE rr : runs
  THEN runs := runs - {rr}
  END;

set_runs(rrs) =
  PRE rrs : POW(iseq1(TILES)) &
      rrs : FIN(rrs) &
      !xx.(xx : rrs => ((size(xx) >= MIN_TILES_PER_GAME) & (card(COLOR[ran(xx) - TILES_JOKER]) = 1))) &
      !rr.(rr : rrs => !(xx,yy).( (xx : dom(rr) & yy : dom(rr) & xx > yy & rr[{xx,yy}] /\ TILES_JOKER = {}) => ( xx - yy = NUMBER(rr(xx)) - NUMBER(rr(yy))))) &
  !rr.(rr : rrs => !xx.((xx : dom(rr) & rr(xx) /: TILES_JOKER) => (xx - 1 <= NUMBER(rr(xx)) & (size(rr) - xx - 2) <= (12 - NUMBER(rr(xx))))))
  THEN
    runs := rrs
  END;

clear_runs = 
  PRE 1=1
  THEN
    runs := {}
  END

END
