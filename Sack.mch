MACHINE Sack

SEES Tiles

VARIABLES
  in_sack

INVARIANT
  in_sack <: TILES & in_sack : FIN(in_sack)

INITIALISATION
  in_sack := TILES


OPERATIONS

add_to_sack(tt) = 
  PRE tt /\ in_sack = {}
  THEN in_sack := in_sack \/ tt
  END;

rmv_from_sack(tt) = 
  PRE tt <: in_sack
  THEN in_sack := in_sack - tt
  END

END