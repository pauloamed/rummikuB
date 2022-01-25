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
  players_racks : VALID_PLAYERS_IDS +-> POW(TILES) &
  dom(players_racks) = dom(players)

INITIALISATION
  players_racks := {}

OPERATIONS

add_racked_player(xx) = 
  PRE xx : NAME & xx /: ran(players) & card(players <+ {card(players) + 1 |-> xx}) <= round_players &
      (players_racks <+ {card(players) + 1 |-> {}}) : VALID_PLAYERS_IDS +-> POW(TILES) &
      (players <+ {card(players) + 1 |-> xx}): VALID_PLAYERS_IDS >+> NAME
  THEN 
    add_player(xx) || players_racks := players_racks <+ {card(players) + 1 |-> {}}
  END;

add_tiles_to_hand(xx, tts) =
  PRE xx : ran(players) & tts <: TILES & tts /\ players_racks(players~(xx)) = {}
  THEN
    players_racks(players~(xx)) := players_racks(players~(xx)) \/ tts
  END;

rmv_tiles_from_hand(xx, tt) =
  PRE xx : ran(players) & tt <: players_racks(players~(xx))
  THEN
    players_racks(players~(xx)) := players_racks(players~(xx)) - tt
  END;

reset_rack(xx) = 
  PRE xx : ran(players)
  THEN
    players_racks(players~(xx)) := {}
  END;

set_rack(xx, tt) =
  PRE xx : ran(players) & tt <: TILES
  THEN
    players_racks(players~(xx)) := tt
  END

END