/* Tournament
 * Author: Joshh
 * Creation date: 11/12/2026
 */
MACHINE Tournament

SETS
    // Enumerated sets cuz these are distinct, known, finite values with no numeric values
    PLAYERS = {Alice, Bob, Christine, Dennis, Eloise, Frank, Gabrielle, Hugo, Ida, John, Kate, Louis};
    TEAMS = {red, blue, green};
    PHASES = {team_selection, match_setup, game_play};
    REPORTS = {
        success, 
        failure, 
        teams_completed,
        invalid_phase, 
        team_not_empty, 
        invalid_member_count,
        player_already_assigned, 
        duplicate_match, 
        same_team,
        player_match_limit, 
        team_match_limit
    }

CONSTANTS
    ability

PROPERTIES
    ability : PLAYERS >-> 1..12 & // Total injection function. Every player must have an ability valuer but two players can't share the same value
    ability = { // Range. Where 1 is strongest and 12 is weakest
        Alice    |-> 1, //
        Bob      |-> 2,
        Christine|-> 3,
        Dennis   |-> 4,
        Eloise   |-> 5,
        Frank    |-> 6,
        Gabrielle|-> 7,
        Hugo     |-> 8,
        Ida      |-> 9,
        John     |-> 10,
        Kate     |-> 11,
        Louis    |-> 12
    } 
    
DEFINITIONS
    //Projection function. match is stored as a pair so these extract each player from that pair
    player_one(mm) == prj1(PLAYERS, PLAYERS)(mm);
    player_two(mm) == prj2(PLAYERS, PLAYERS)(mm);
    
    current_match == first(scheduled_matches); // returns first element from sequence(next match to be played in next game) 
    assigned_players == {pp | pp: PLAYERS & #(tt).(tt : TEAMS & pp : team_members(tt))}; 
    team_of(pp) == {qq | qq : PLAYERS & #(tt).(tt : TEAMS & pp : team_members(tt) & qq : team_members(tt))}; // returns 
    team_name_of(pp) == (team_members~)(team_of(pp)); 
    match_count(pp) == card(scheduled_matches |> ({pp} * PLAYERS \/ PLAYERS * {pp})); // Counts how many scheduled matches involve player pp in either position. Used to enforce the 6-match limit
    matches_between(aa, bb) == card(scheduled_matches |> (aa * bb \/ bb * aa))

VARIABLES
    current_phase,
    team_members,
    scheduled_matches,
    player_scores,
    team_scores

INVARIANT
    current_phase : PHASES &
    team_members : TEAMS --> POW(PLAYERS) &
    !(t1, t2).(t1 : TEAMS & t2 : TEAMS & t1 /= t2 => team_members(t1) /\ team_members(t2) = {}) &
    !(tt).(tt : TEAMS => card(team_members(tt)) <= 4) &
    scheduled_matches : iseq(PLAYERS * PLAYERS) &
    !(xx, yy).(xx : PLAYERS & yy : PLAYERS & xx |-> yy : ran(scheduled_matches) => 
        xx /= yy & yy /: team_of(xx) & (yy |-> xx) /: ran(scheduled_matches)) &
    !(pp).(pp : PLAYERS => match_count(pp) <= 6) &
    !(t1, t2).(t1 : TEAMS & t2 : TEAMS & t1 /= t2 => 
        matches_between(team_members(t1), team_members(t2)) <= 12) &
    player_scores : PLAYERS --> NAT &
    team_scores : TEAMS --> NAT &
    (current_phase = team_selection => scheduled_matches = []) &
    (current_phase /= team_selection => assigned_players = PLAYERS)

INITIALISATION
    current_phase := team_selection || // Tournament starts at team selection
    team_members := TEAMS * {{}} ||
    scheduled_matches := [] ||
    player_scores := PLAYERS * {0} ||
    team_scores := TEAMS * {0}

OPERATIONS
    
    // (1) SET PLAYER
    // assign 4 players to a team during team selection
    report <-- setPlayers(team, members) =
    PRE
        team : TEAMS &
        members <: PLAYERS
    THEN
        IF current_phase /= team_selection
        THEN report := invalid_phase
        ELSIF team_members(team) /= {}
        THEN report := team_not_empty
        ELSIF card(members) /= 4
        THEN report := invalid_member_count
        ELSIF members /\ assigned_players /= {}
        THEN report := player_already_assigned
        ELSIF card({tt | tt : TEAMS & team_members(tt) /= {}}) = 1 
        THEN
            team_members := team_members <+ ({tt | tt : TEAMS & tt /= team & team_members(tt) = {}} * {PLAYERS - (assigned_players \/ members)}) <+ {team |-> members} ||
            current_phase := match_setup ||
            report := teams_completed
        ELSE
            team_members := team_members <+ {team|-> members} ||
            report := success
        END
    END;

    // (2) SET MATCH
    // Schedules a match between two players
    report <-- setupMatch(players) =
    PRE
        players : PLAYERS * PLAYERS
    THEN
        IF current_phase /= match_setup
        THEN report := invalid_phase
        ELSIF (players) : ran(scheduled_matches) or (player_two(players) |-> player_one(players)) : ran(scheduled_matches)
        THEN report := duplicate_match
        ELSIF player_two(players) : team_of(player_one(players))
        THEN report := same_team
        ELSIF match_count(player_one(players)) >= 6 or match_count(player_two(players)) >= 6 
        THEN report := player_match_limit
        ELSIF matches_between(team_of(player_one(players)), team_of(player_two(players))) >= 12 
        THEN report := team_match_limit
        ELSE
            scheduled_matches := scheduled_matches  <- players ||
            report := success
        END
    END;

    // (3) UNDO
    // Removes the most recently scheduled match
    report <-- undo =
    BEGIN
        IF current_phase /= match_setup or scheduled_matches = []
        THEN report := failure
        ELSE
            scheduled_matches := front(scheduled_matches) ||
            report := success
        END
    END;

    // (4) PROCEED 
    // advances from match setup to game play
    report <-- proceed =
    BEGIN 
        IF current_phase = match_setup & 
            (!(pp).(pp : PLAYERS => match_count(pp) =6) & 
                !(t1, t2).(t1 : TEAMS & t2 : TEAMS & t1 /= t2 => matches_between(team_members(t1), team_members(t2)) = 12))
        THEN 
            current_phase := game_play ||
            report := success 
        ELSE 
            report := failure 
        END 
    END;

    // (5) NEXT GAME
    // plays the first scheduled match, awards a point to the winner
    report <-- nextGame =
    BEGIN
        IF current_phase /= game_play or scheduled_matches = []
        THEN report := failure 
        ELSIF ability(player_one(current_match)) < ability(player_two(current_match))
        THEN
            scheduled_matches := tail(scheduled_matches) ||
            player_scores := player_scores <+ {player_one(current_match) |-> player_scores(player_one(current_match)) + 1} ||
            team_scores := team_scores <+
            {team_name_of(player_one(current_match)) |-> team_scores(team_name_of(player_one(current_match))) + 1} ||
            report := success
        ELSE
            scheduled_matches := tail(scheduled_matches) ||
            player_scores := player_scores <+
            {player_two(current_match) |-> player_scores(player_two(current_match)) + 1} ||
            team_scores := team_scores <+ {team_name_of(player_two(current_match)) |-> team_scores(team_name_of(player_two(current_match))) +1} ||
            report := success
        END
    END;
    
    // (6) RESTART
    // resets the tournament back to team selection
    report <-- restart =
    BEGIN 
        IF current_phase = game_play & scheduled_matches = []
        THEN
            current_phase := team_selection ||
            team_members := TEAMS * {{}} ||
            player_scores := PLAYERS * {0} ||
            team_scores := TEAMS * {0} ||
            report := success
        ELSE
            report := failure
        END
    END;
    
    //(7) PLAYER SCORES
    // returns the scores of all players in a given team
    scores <-- playerScores(team) =
    PRE
        team : TEAMS
    THEN
        scores := team_members(team) <| player_scores // domain restriction. filter player_scores to only the players in this team filter
    END
END