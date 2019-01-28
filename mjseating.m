% Copyright (C) 2015-2019 Max Ulidtko <ulidtko@gmail.com>. All rights reserved.
% SPDX-License-Identifier: MIT

% This file is written in [Mercury], a statically-typed Prolog variant.
%
% What does this program compute?
% Tournament grids (player seatings) for the [Riichi Mahjong] game.
% Players are represented simply by integers: 1, 2, 3, 4, and so on.
% The generated results comprise a full tournament schedule, listing tables of
% every hanchan. Each table lists 4 players. Solutions contain no "intersections":
% not a single pair of players meet more than once during the whole tournament.
%
% Once compiled, usage is as simple as:
%     ./mjseating -P <NUM_PLAYERS> -H <NUM_HANCHANS>
%
% See the Mercury user guide for details on how to compile. TL;DR:
%     mmc --grade hlc.gc mjseating.m
%
% Be aware that the search will likely take a long time. 24-player-6-hanchan
% computation been running for *23 to 29 hours* on my machine to find any results.
% Smaller parameters of course will run faster. 20-player-5-hanchan solves in <1s.
%
% You'll find samples of generated seatings under data/. There's also a little
% python helper script to re-check solution correctness (0 intersections).
%
% Please let me know if you find this useful.
%
% [Mercury]: https://mercurylang.org/
% [Riichi Mahjong]: https://en.wikipedia.org/wiki/Japanese_Mahjong

:- module mjseating.

:- interface.
:- import_module io.
:- import_module list.
:- import_module set.

:- type player == int.

:- type table == quad(player).
:- type hanchan == list(table).

:- type metDB == set({player, player}).

:- type quad(T) == {T, T, T, T}.
:- type pquads == set(quad(player)).

:- pred main(io::di, io::uo) is cc_multi.


:- implementation.
:- import_module bool, int.
:- import_module char, string.
:- import_module solutions.

%----- UTILITIES -----

:- pred neverMet(metDB::in, {player,player}::in) is semidet.
neverMet(D, PP) :- not member(PP, D).

:- func fst({T1, T2, T3, T4}) = T1.
fst({X, _, _, _}) = X.
:- func snd({T1, T2, T3, T4}) = T2.
snd({_, X, _, _}) = X.
:- func thd({T1, T2, T3, T4}) = T3.
thd({_, _, X, _}) = X.
:- func fth({T1, T2, T3, T4}) = T4.
fth({_, _, _, X}) = X.

:- func quadToSet(quad(T)) = set(T).
quadToSet({PA,PB,PC,PD}) = sorted_list_to_set([PA,PB,PC,PD]).

:- func tablePairs(table) = list({player,player}).
tablePairs({A,B,C,D}) = [{A,B}, {A,C}, {A,D}, {B,C}, {B,D}, {C,D}].

:- pred listChoice(list(T)::in, T::out, list(T)::out) is nondet.
listChoice([X | T], X, T).
listChoice([_ | T], X, R) :- listChoice(T, X, R).


%----- CORE LOGIC -----

:- pred allQuads(set(player)::in, pquads::out) is det.
allQuads(Players, Quads) :-
    solutions_set((
        pred({PA,PB,PC,PD}::out) is nondet :-
            member(PA, Players),
            member(PB, Players), PB > PA,
            member(PC, Players), PC > PB,
            member(PD, Players), PD > PC
    ), Quads).

:- pred freePlayersInQuad(set(player)::in, quad(player)::in) is semidet.
freePlayersInQuad(FreePlayers, {PA,PB,PC,PD}) :-
    member(PA, FreePlayers),
    member(PB, FreePlayers),
    member(PC, FreePlayers),
    member(PD, FreePlayers).

:- func cullConflictingQuads(pquads, quad(player)) = pquads.
cullConflictingQuads(QSi, Qc) = set.filter(quadConflict(Qc), QSi).

:- pred quadConflict(quad(T)::in, quad(T)::in) is semidet.
quadConflict({PA1, PB1, PC1, PD1}, {PA2, PB2, PC2, PD2}) :-
    %-- success when no intersecting pairs
    set.intersect(Pairs1, Pairs2, set.init),
    Pairs1 = sorted_list_to_set([{PA1,PB1},{PA1,PC1},{PA1,PD1},{PB1,PC1},{PB1,PD1},{PC1,PD1}]),
    Pairs2 = sorted_list_to_set([{PA2,PB2},{PA2,PC2},{PA2,PD2},{PB2,PC2},{PB2,PD2},{PC2,PD2}]).

:- func cullHanchanQuads(hanchan, pquads) = pquads.
cullHanchanQuads(Hanchan, Qs) = set.filter((
        pred({A,B,C,D}::in) is semidet :- set.intersect(
            HanchanPairs,
            sorted_list_to_set([{A,B},{A,C},{A,D},{B,C},{B,D},{C,D}]),
            set.init
        )
    ), Qs) :-
    HanchanPairs = set(condense(map(tablePairs, Hanchan)))
    .




:- pred fillAllTables(
      list(table)::out
    , set(player)::in
    , pquads::in
    , pquads::out
    ) is nondet.
fillAllTables([],        set.init, Q, Q).
fillAllTables([Q0 | QN1], Players, Quads, QuadsOut) :-
    %-- here we're interested in quads consisting of only free players
    NonBoringQuads = set.filter(freePlayersInQuad(Players), Quads),

    %-- select a table configuration (quad)
    listChoice(to_sorted_list(NonBoringQuads), Q0, QuadsRest),

    %-- exclude impossible quads according to our choice of Q0
    QuadsCulled = cullConflictingQuads(sorted_list_to_set(QuadsRest), Q0),

    %-- recurse for rest of players
    PlayersRest = set.difference(Players, quadToSet(Q0)),
    fillAllTables(QN1, PlayersRest, QuadsCulled, QuadsOut)
    .


:- pred searchNHanchans(
      int::in
    , set(player)::in
    , list(hanchan)::out
    , pquads::out
    ) is nondet.
searchNHanchans(0, Players, [], Q) :- allQuads(Players, Q).
searchNHanchans(N, Players, [H0 | Hn1], QuadsUpd) :-
    N > 0,
    searchNHanchans(N - 1, Players, Hn1, QuadsBase),
    fillAllTables(H0, Players, QuadsBase, _),
    QuadsUpd = cullHanchanQuads(H0, QuadsBase),

    trace [run_time(env("TRACE")), io(!IO)] (
        io.write_string("=== Candidate hanchan " ++ string(N) ++ " ===", !IO), io.nl(!IO),
        io.write_string("    Tables: " ++ string([H0 | Hn1]), !IO), io.nl(!IO),
        io.write_string("    Quads: " ++ string(QuadsUpd), !IO), io.nl(!IO)
        %io.write_string("  C(DB): " ++ pprintDB2Dot(dbComplement(QuadsUpd)), !IO), io.nl(!IO)
    )
    .


%----- PRETTY PRINTING -----

%:- func pprintHanchan(list(quad(player))) = list(list(player)).
%pprintHanchan(H) = map(to_sorted_list, H).

:- func pprintDB2Dot(metDB) = string.
pprintDB2Dot(DB) = "strict graph { " ++ join_list("; ", Lines) ++ "}" :-
    Lines = map(func({P1,P2}) = string(P1) ++ " -- " ++ string(P2), to_sorted_list(DB))
    .

%----- CMDLINE -----

:- import_module getopt_io.
:- type myoption ---> help; playerCount; hanchanCount.
:- pred shortOpt(char::in, myoption::out) is semidet.
shortOpt('h', help).
shortOpt('P', playerCount).
shortOpt('H', hanchanCount).
:- pred longOpt(string::in, myoption::out) is semidet.
longOpt("help", help).
longOpt("players", playerCount).
longOpt("hanchans", hanchanCount).
:- pred defOpt(myoption::out, option_data::out) is multi.
defOpt(help, bool(no)).
defOpt(playerCount, int(24)).
defOpt(hanchanCount, int(8)).

:- func usage = string.
usage = join_list("\n", [
        "Usage: mjseating [OPTIONS]",
        "",
        "Options:",
        "    -h, --help            Show this message and exit",
        "    -P, --players         Set the player count (default is 24)",
        "    -H, --hanchans        Set the number of hanchans (default is 8)",
        ""
    ]).

main -->
    command_line_arguments(Args),
    process_options(option_ops_multi(shortOpt, longOpt, defOpt), Args, _, ParsedOpts),
    (
        { ParsedOpts = ok(Options) },
        (
            { lookup_bool_option(Options, help, HelpRequested) },
            { HelpRequested = yes }
                -> print(usage)
        ;
            main(Options)
        )
    ;
        { ParsedOpts = error(E) },
        write_string("Couldn't parse cmdline: " ++ E ++ "\n\n"),
        print(usage),
        set_exit_status(1)
    ).

%----- MAIN -----

:- pred main(option_table(myoption)::in, io::di, io::uo) is cc_multi.
main(Options, !IO) :-
    NPlayers = lookup_int_option(Options, playerCount),
    NHanchans = lookup_int_option(Options, hanchanCount),
    (
        NPlayers \= NPlayers // 4 * 4 ->
        write_string("Players count must be a multiple of 4.\n", !IO),
        set_exit_status(2, !IO)
    ;
        NHanchans * 3 >= NPlayers ->
        write_string(format("Too many hanchans!\n" ++
            "In %d hanchans, each player is going to meet %d distinct opponents. " ++
            "With %d players, this isn't possible without intersections.\n",
            [i(NHanchans), i(NHanchans * 3), i(NPlayers)]), !IO),
        set_exit_status(3, !IO)
    ;
        run_search({NPlayers, NHanchans}, !IO)
    ).

:- pred run_search({int, int}::in, io::di, io::uo) is cc_multi.
run_search({NP, NH}, !IO) :-
    % TODO generate no more than a user-requested number of solutions
    do_while(
        (pred(Solution::out) is nondet :-
            searchNHanchans(NH, set(1..NP), Solution, _)
        ),
        process_solution,
        !IO
    ),
    io.write_string("Printing no more solutions.\n", !IO)
    .

:- mutable(nSolutions, int, 0, ground, [untrailed,attach_to_io_state]).

:- pred process_solution(list(hanchan)::in, bool::out, io::di, io::uo) is det.
process_solution(S, DoContinue) -->
    printSolution(S),
    get_nSolutions(N),
    set_nSolutions(N + 1),
    { DoContinue = pred_to_bool(N + 1 < 20) }.

:- pred printSolution(list(hanchan)::in, io::di, io::uo).
printSolution(S) -->
    io.print(S),
    io.write_string("\n\n")
    .

% vim: filetype=prolog
