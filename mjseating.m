:- module mjseating.

:- interface.
:- import_module io.
:- import_module list.
:- import_module set.

:- type player == int.

:- type table == set(player). % exactly 4 players
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


:- func tablePairs(table) = set({player,player}).
tablePairs(T) = set([{A,B}, {A,C}, {A,D}, {B,C}, {B,D}, {C,D}]) :-
    L = to_sorted_list(T),
    A = det_index1(L, 1),
    B = det_index1(L, 2),
    C = det_index1(L, 3),
    D = det_index1(L, 4).


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


:- pred fillTable(
      table::out
    , set(player)::in
    , set(player)::out
    , metDB::in
    , metDB::out
    ) is nondet.

fillTable(Table, Ps, PsRest, DB, DBout) :-
    %(compare((>), count(Ps), 4); checkConstraints(Ps, _, DB, _)),

    subsetExact4(Ps, Table, Pairs, neverMet(DB)),
    %is_empty(intersect(Pairs, DB)),
    PsRest = set.difference(Ps, Table),
    DBout = set.union(DB, Pairs).


:- pred subsetExact4(
      set(player)::in
    , set(player)::out
    , metDB::out
    , pred({player,player})::(pred(in) is semidet)
    ) is nondet.
subsetExact4(SIn, SOut, Pairs, UserCond) :-
    N = count(SIn),
    N >= 4, % -> K1 = 1, K2 = 2, K3 = 3, K4 = 4

    K1 = 1,
    nondet_int_in_range(K1+1, N, K2),
        UserCond({L1,L2}),
    nondet_int_in_range(K2+1, N, K3),
        UserCond({L1,L3}),
        UserCond({L2,L3}),
    nondet_int_in_range(K3+1, N, K4),
        UserCond({L1,L4}),
        UserCond({L2,L4}),
        UserCond({L3,L4}),

    L = to_sorted_list(SIn),
    (L1:player) = det_index1(L, K1),
    (L2:player) = det_index1(L, K2),
    (L3:player) = det_index1(L, K3),
    (L4:player) = det_index1(L, K4),

    SOut = sorted_list_to_set([L1, L2, L3, L4]),
    Pairs = sorted_list_to_set([{L1,L2},{L1,L3},{L1,L4},{L2,L3},{L2,L4},{L3,L4}]).


:- pred fillNTables(
      int::in
    , list(table)::out
    , set(player)::in
    , metDB::in
    , metDB::out) is nondet.

fillNTables(0, [], _, D, D).

fillNTables(N, Tables, Players, DB, DBout) :-
    fillTable(Table0, Players, PlayersRest, DB, DBupd1),
    fillNTables(N - 1, TablesN1, PlayersRest, DB, DBupd2),
    DBout = set.union(DBupd1, DBupd2),
    Tables = [Table0 | TablesN1].


:- pred fillAllTables(
      list(table)::out
    , set(player)::in
    , metDB::in
    , metDB::out
    ) is nondet.

fillAllTables([], set([]), D, D).

fillAllTables(Tables, Players, DB, DBout) :-
    fillTable(Table0, Players, PlayersRest, DB, DBupd1),
    fillAllTables(TablesN1, PlayersRest, DB, DBupd2),
    DBout = set.union(DBupd1, DBupd2),
    Tables = [Table0 | TablesN1].


:- pred searchNHanchans(
      int::in
    , set(player)::in
    , list(hanchan)::out
    , metDB::out
    ) is nondet.
searchNHanchans(0,       _, [], set.init).
searchNHanchans(N, Players, [H0 | Hn1], DBupd) :-
    N > 0,
    fillAllTables(H0, Players, DBbase, DBupd),
    trace [io(!IO)] (
        io.write_string("== Candidate hanchan " ++ string(N) ++ " ==", !IO), io.nl(!IO),
        io.write_string("  Tables: " ++ string(H0), !IO), io.nl(!IO),
        io.write_string("  DB: " ++ pprintDB2Dot(DBupd), !IO), io.nl(!IO)
        %io.write_string("  C(DB): " ++ pprintDB2Dot(dbComplement(DBupd)), !IO), io.nl(!IO)
    ),
    searchNHanchans(N - 1, Players, Hn1, DBbase).


%----- PRETTY PRINTING -----

:- func pprintHanchan(list(table)) = list(list(player)).
pprintHanchan(H) = map(to_sorted_list, H).

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
        NPlayers * (NPlayers - 1) / 2 < 6 * NHanchans * NPlayers / 4 ->
        write_string(format("Not enough players!\n%d players form %d distinct pairs - that is too few for %d hanchans.\n",
            [i(NPlayers), i(NPlayers * (NPlayers - 1) / 2), i(NHanchans)]), !IO),
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
    { DoContinue = no }.% pred_to_bool(N + 1 < 200) }.

:- pred printSolution(list(hanchan)::in, io::di, io::uo).
printSolution(S) -->
    io.print(map(pprintHanchan, S)),
    io.write_string("\n\n")
    .
