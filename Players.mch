MACHINE Players

SEES Names

CONSTANTS
  VALID_PLAYERS_NUMS, VALID_PLAYERS_IDS

PROPERTIES
  VALID_PLAYERS_NUMS = 2..12 &
  VALID_PLAYERS_IDS = 1..12

VARIABLES
  round_players, players

INVARIANT
  round_players : NATURAL &

  // Players: a function of names (but partial injective and indexed by naturals)
  players : VALID_PLAYERS_IDS >+> NAME & players : FIN(players) &

  card(players) <= round_players

INITIALISATION
  players := {} || round_players := 0

OPERATIONS

set_round_players(nn) =
  PRE nn : VALID_PLAYERS_NUMS & card(players) = 0
  THEN round_players := nn
  END;

add_player(xx) = 
  PRE xx : NAME & xx /: ran(players) &
      card(players <+ {card(players) + 1 |-> xx}) <= round_players &
      (players <+ {card(players) + 1 |-> xx}): VALID_PLAYERS_IDS >+> NAME
  THEN players := players <+ {card(players) + 1 |-> xx}
  END

END