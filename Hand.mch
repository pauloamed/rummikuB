MACHINE Hand

SEES Tiles

VARIABLES
  in_hand

INVARIANT
  in_hand : TILES --> BOOL

INITIALISATION
  in_hand := TILES * {FALSE}

OPERATIONS

set_hand(tts) =   
  PRE tts : TILES --> BOOL
  THEN
    in_hand := tts
  END;

reset_hand = in_hand := TILES * {FALSE};

add_to_hand(tts) = 
  PRE tts : TILES --> BOOL & dom(tts |> {TRUE}) /\ dom(in_hand |> {TRUE}) = {}
  THEN
    in_hand := in_hand <+ (tts |> {TRUE})
  END;

rmv_from_hand(tts) = 
  PRE tts : TILES --> BOOL & dom(tts |> {TRUE}) <: dom(in_hand |> {TRUE})
  THEN in_hand := in_hand <+ dom(tts |> {TRUE}) * {FALSE}
  END;

xx <-- get_in_hand = xx := in_hand

END
