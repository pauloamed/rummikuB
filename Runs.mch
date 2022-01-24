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
  PRE 1=1
  THEN runs := runs \/ rr
  END;

rmv_run(rr) =
  PRE rr : runs
  THEN runs := runs - {rr}
  END

END
