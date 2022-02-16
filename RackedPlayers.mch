MACHINE RackedPlayers

SEES Tiles, Names
INCLUDES Players

PROMOTES set_round_players

CONSTANTS 
  NUM_STARTING_TILES, MAX_PLAYER_ID

PROPERTIES
  NUM_STARTING_TILES = 14 & MAX_PLAYER_ID = 5

VARIABLES
  players_racks

INVARIANT
  players_racks : VALID_PLAYERS_IDS --> (TILES --> BOOL) &
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
  PRE xx : VALID_PLAYERS_IDS & players(xx) /= NILL & tts : TILES --> BOOL & players_racks(xx)[dom(tts |> {TRUE})] = {FALSE}
  THEN
    players_racks(xx) := players_racks(xx) <+ dom(tts |> {TRUE}) * {TRUE}
  END;

rmv_tiles_from_hand(xx, tts) =
  PRE xx : VALID_PLAYERS_IDS & players(xx) /= NILL & tts : TILES --> BOOL & players_racks(xx)[dom(tts |> {TRUE})] = {TRUE}
  THEN
    players_racks(xx) := players_racks(xx) <+ dom(tts |> {TRUE}) * {FALSE}
  END;

reset_rack(xx) = 
  PRE xx : VALID_PLAYERS_IDS & players(xx) /= NILL
  THEN
    players_racks(xx) := TILES * {FALSE}
  END;

set_rack(xx, tt) =
  PRE xx : VALID_PLAYERS_IDS & players(xx) /= NILL & tt : TILES --> BOOL
  THEN
    players_racks(xx) := tt
  END;

xx <-- get_players_racks = xx := players_racks

END
