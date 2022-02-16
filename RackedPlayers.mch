MACHINE RackedPlayers

SEES Tiles, Names
INCLUDES Players

PROMOTES set_round_players

CONSTANTS 
  NUM_STARTING_TILES

PROPERTIES
  NUM_STARTING_TILES = 14

VARIABLES
  players_racks

INVARIANT
  players_racks : VALID_PLAYERS_IDS +-> (TILES --> BOOL) &
  dom(players_racks) = dom(players)

INITIALISATION
  players_racks := {}

OPERATIONS

add_racked_player(xx) = 
  PRE xx : NAME & xx /: ran(players) & card(players) < round_players
  THEN 
    add_player(xx) || players_racks := players_racks <+ {card(players) + 1 |-> {}}
  END;

add_tiles_to_hand(xx, tts) =
  PRE xx : NAME & xx : ran(players) & tts : TILES --> BOOL & players_racks(players~(xx))[dom(tts |> {TRUE})] = {FALSE}
  THEN
    players_racks(players~(xx)) := players_racks(players~(xx)) <+ dom(tts |> {TRUE}) * {TRUE}
  END;

rmv_tiles_from_hand(xx, tts) =
  PRE xx : NAME & xx : ran(players) & tts : TILES --> BOOL & players_racks(players~(xx))[dom(tts |> {TRUE})] = {TRUE}
  THEN
    players_racks(players~(xx)) := players_racks(players~(xx)) <+ dom(tts |> {TRUE}) * {FALSE}
  END;

reset_rack(xx) = 
  PRE xx : NAME & xx : ran(players)
  THEN
    players_racks(players~(xx)) := TILES * {FALSE}
  END;

set_rack(xx, tt) =
  PRE xx : NAME & xx : ran(players) & tt : TILES --> BOOL
  THEN
    players_racks(players~(xx)) := tt
  END

END
