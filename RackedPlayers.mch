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
  PRE xx : NAME & xx /: ran(players) & card(players) < round_players
  THEN 
    add_player(xx) || players_racks := players_racks <+ {card(players) + 1 |-> {}}
  END;

add_tiles_to_hand(xx, tt) =
  PRE xx : ran(players) & tt /\ players_racks(players~(xx)) = {}
  THEN
    players_racks(players~(xx)) := players_racks(players~(xx)) \/ tt
  END;

rmv_tiles_from_hand(xx, tt) =
  PRE xx : ran(players) & tt <: players_racks(players~(xx))
  THEN
    players_racks(players~(xx)) := players_racks(players~(xx)) - tt
  END;

reset_hand(xx) = 
  PRE xx : ran(players)
  THEN
    players_racks(players~(xx)) := {}
  END;

set_hand(xx, tt) =
  PRE xx : ran(players) & tt <: TILES
  THEN
    players_racks(players~(xx)) := tt
  END

END