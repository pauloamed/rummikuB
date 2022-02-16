MACHINE Players

SEES Names

CONSTANTS
  VALID_PLAYERS_NUMS, VALID_PLAYERS_IDS, VALID_ROUNDS

PROPERTIES
  VALID_PLAYERS_NUMS = 2..5 &
  VALID_PLAYERS_IDS = 1..5 &
  VALID_ROUNDS = 0..4

VARIABLES
  round_players, players, idx

INVARIANT
  round_players : VALID_ROUNDS &
  idx : 0..6 &

  // Players: a function of names (but partial injective and indexed by naturals)
  players : VALID_PLAYERS_IDS --> NAME & players : FIN(players) &

  card(players |>> {NILL}) < round_players

INITIALISATION
  players := VALID_PLAYERS_IDS * {NILL} || round_players := MAXINT || idx := 0

OPERATIONS

set_round_players(nn) =
  PRE nn : VALID_PLAYERS_NUMS
  THEN round_players := nn
  END;

add_player(xx) = 
  PRE xx : NAME & xx /: ran(players) & card(players) < round_players
  THEN players := players <+ {idx |-> xx} || idx := idx + 1
  END;

xx <-- get_idx = xx := idx;
xx <-- get_players = xx := players;
xx <-- get_round_players = xx := round_players

END
