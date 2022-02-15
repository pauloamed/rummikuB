MACHINE Players

SEES Names

CONSTANTS
  VALID_PLAYERS_NUMS, VALID_PLAYERS_IDS, VALID_ROUNDS

PROPERTIES
  VALID_PLAYERS_NUMS = 2..5 &
  VALID_PLAYERS_IDS = 1..5 &
  VALID_ROUNDS = 0..4

VARIABLES
  round_players, players

INVARIANT
  round_players : VALID_ROUNDS &

  // Players: a function of names (but partial injective and indexed by naturals)
  players : VALID_PLAYERS_IDS >+> NAME & players : FIN(players) &

  card(players) < round_players

INITIALISATION
  players := VALID_PLAYERS_IDS * {NILL} || round_players := 0

OPERATIONS

set_round_players(nn) =
  PRE nn : VALID_PLAYERS_NUMS
  THEN round_players := nn
  END;

add_player(xx) = 
  PRE xx : NAME & xx /: ran(players) & card(players) < round_players
  THEN players := players <+ {card(players) + 1 |-> xx}
  END

END