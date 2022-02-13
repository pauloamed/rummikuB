MACHINE Hand

SEES Tiles

VARIABLES
  in_hand

INVARIANT
  in_hand : TILES --> BOOL

INITIALISATION
  in_hand := TILES * {FALSE}

OPERATIONS

set_hand(tts) = in_hand := tts;

add_to_hand(tts) = 
  PRE tts : TILES --> BOOL & dom(tts |> {TRUE}) /\ dom(in_hand |> {TRUE}) = {}
  THEN
    in_hand := in_hand <+ (tts |> {TRUE})
  END;


reset_hand = in_hand := TILES * {FALSE};

rmv_from_hand(tt) = 
  PRE tt : TILES --> BOOL & dom(tt |> {TRUE}) <: dom(in_hand |> {TRUE})
  THEN in_hand := in_hand <+ dom(tt |> {TRUE}) * {FALSE}
  END

END