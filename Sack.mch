MACHINE Sack

SEES Tiles

VARIABLES
  in_sack

INVARIANT
  in_sack : TILES --> BOOL

INITIALISATION
  in_sack := TILES * {FALSE}


OPERATIONS

set_sack =  in_sack := TILES * {TRUE};

rmv_from_sack(tt) = 
  PRE tt : TILES --> BOOL & dom(tt |> {TRUE}) <: dom(in_sack |> {TRUE})
  THEN in_sack := in_sack <+ dom(tt |> {TRUE}) * {FALSE}
  END;

xx <-- get_in_sack = xx := in_sack

END
