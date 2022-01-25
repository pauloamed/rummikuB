MACHINE Hand

SEES Tiles

VARIABLES
  in_hand

INVARIANT
  in_hand <: TILES & in_hand : FIN ( in_hand )

INITIALISATION
  in_hand := {}

OPERATIONS

add_to_hand ( tts ) =
  PRE tts <: TILES & tts /\ in_hand = {} & tts : FIN(tts)
  THEN
    in_hand := in_hand \/ tts
  END;

set_hand ( tts ) =
  PRE tts <: TILES & tts : FIN(tts)
  THEN 
    in_hand := tts
  END;

reset_hand =
  in_hand := {};

rmv_from_hand ( tts ) =
  PRE tts <: TILES & tts <: in_hand
  THEN
    in_hand := in_hand - tts
  END

END
