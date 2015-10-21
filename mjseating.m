:- module mjseating.

:- interface.
:- import_module io.
:- import_module list.
:- import_module set.

:- type player == int.
%:- type player ---> p1; p2; p3; p4; p5; p6; p7; p8; p9; p10; p11; p12; p13; p14; p15; p16.
%Players = set([p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16]).

:- type table == set(player). % exactly 4 players
:- type hanchan == list(table).

:- type metDB == set({player, player}).
:- func emptyDB = metDB.
:- func mergeDBs(metDB, metDB) = metDB.

:- pred main(io::di, io::uo) is cc_multi.


:- implementation.
:- import_module bool, int.
:- import_module char, string.
:- import_module solutions.

:- func fst({T1, T2}) = T1.
fst({X, _}) = X.
:- func snd({T1, T2}) = T2.
snd({_, X}) = X.

emptyDB = set([]).
mergeDBs(A, B) = union(A, B).

:- pred alreadyMet(metDB::in, player::in, player::in) is semidet.
alreadyMet(D, P1, P2) :- member({P1, P2}, D); member({P2, P1}, D).

:- pred neverMet(metDB::in, {player, player}::in) is semidet.
neverMet(D, PP) :- not member(PP, D).

:- func tablePairs(table) = metDB.
%tablePairs(T) = solutions_set(
%        (pred({X1, X2}::out) is nondet :-
%            member(X1, T), member(X2, T), compare((<), X1, X2))
%    ).
tablePairs(T) = set([{A,B}, {A,C}, {A,D}, {B,C}, {B,D}, {C,D}]) :-
    L = to_sorted_list(T),
    A = det_index1(L, 1),
    B = det_index1(L, 2),
    C = det_index1(L, 3),
    D = det_index1(L, 4).


:- pred fillTable(
      table::out
    , set(player)::in
    , set(player)::out
    , metDB::in
    , metDB::out
    ) is nondet.

fillTable(Table, Ps, PsRest, DB, DBout) :-
    (compare((>), count(Ps), 4); checkConstraints(Ps, _, DB, _)),

    subsetExact4(Ps, Table, Pairs, neverMet(DB)),
    %is_empty(intersect(Pairs, DB)),
    PsRest = difference(Ps, Table),
    DBout = mergeDBs(DB, Pairs).


:- pred checkConstraints(
      set(player)::in
    , table::out
    , metDB::in
    , metDB::out
    ) is nondet.
checkConstraints(FreePlayers, set([]), DB, DB) :-
    FreePlayersL = to_sorted_list(FreePlayers),
    N = count(FreePlayers),

    %-- filter out EligiblePairs
    solutions(
        (pred({P1,P2}::out) is nondet :-
            member(K1,    1..N), P1 = det_index1(FreePlayersL, K1),
            member(K2, K1+1..N), P2 = det_index1(FreePlayersL, K2),
            neverMet(DB, {P1, P2})
        ),
        EligiblePairs
    ),

    EligiblePair = (pred(PA::in, PB::out) is nondet :-
        member({PA,PB}, EligiblePairs); member({PB,PA}, EligiblePairs)
    ),

    %-- every FreePlayer has at least 3 eligible partners
    all [P] (member(P, FreePlayersL),
        Partners = solutions(pred(Q::out) is nondet :- EligiblePair(P, Q)),
        length(Partners) >= 3
    )
    .

:- pred eligiblePartner(
      metDB::in
    , player::out
    , player::out
    ) is nondet.
eligiblePartner(DB, PA, PB) :- member({PA,PB}, DB).
eligiblePartner(DB, PB, PA) :- member({PA,PB}, DB).


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
    DBout = mergeDBs(DBupd1, DBupd2),
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
    DBout = mergeDBs(DBupd1, DBupd2),
    Tables = [Table0 | TablesN1].


:- pred searchNHanchans(
      int::in
    , set(player)::in
    , list(hanchan)::out
    , metDB::out
    ) is nondet.
searchNHanchans(0,       _, [], emptyDB).
searchNHanchans(N, Players, [H0 | Hn1], DBupd) :-
    N > 0,
    fillAllTables(H0, Players, DBbase, DBupd),
    trace [io(!IO)] (
        io.write_string("== Candidate hanchan " ++ string(N) ++ " ==", !IO), io.nl(!IO),
        io.write_string("  Tables: " ++ string(H0), !IO), io.nl(!IO),
        io.write_string("  DB: " ++ pprintDB2Dot(DBupd), !IO), io.nl(!IO),
        io.write_string("  C(DB): " ++ pprintDB2Dot(dbComplement(DBupd)), !IO), io.nl(!IO)
    ),
    searchNHanchans(N - 1, Players, Hn1, DBbase).


:- pred fourHanchan4Tables(
      set(player)::in
    , list(table)::out
    , list(table)::out
    , list(table)::out
    , list(table)::out
    ) is nondet.
fourHanchan4Tables(Players, H1, H2, H3, H4) :-
    fillNTables(4, H1, Players, emptyDB, DB2),
    fillNTables(4, H2, Players, DB2, DB3),
    fillNTables(4, H3, Players, DB3, DB4),
    fillNTables(4, H4, Players, DB4, _).



:- pred subsetExactN(int::in, set(T)::in, set(T)::out) is nondet.
:- pred subsetExactNCond(
      int::in
    , pred(T)::in(pred(in) is semidet)
    , set(T)::in
    , set(T)::out
    ) is nondet.

subsetExactN(0,   _, set([])).
subsetExactN(N, SIn, Ans) :-
    %member(X, SIn),
    %remove(X, SIn, S),
    %P = (pred(Y::in) is semidet :- compare((<), X, Y)),
    %divide(P, S, SRest, _),
    setSplit(SIn, _, X, SRest),

    subsetExactN(N - 1, SRest, AnsRest),
    Ans = insert(AnsRest, X).

:- pred setSplit(set(T)::in, set(T)::out, T::out, set(T)::out) is nondet.
% intentionally fails on empty input set
setSplit(S, init, X, init) :- singleton_set(X, S).
setSplit(S, set(Prefix), X, set(Suffix)) :-
    N = count(S),
    N > 1,
    L = to_sorted_list(S),
    list.member(K, 1..N),
    split_list(K-1, L, Prefix, [X | Suffix])
    .


:- func dbComplement(metDB) = metDB.
dbComplement(D) = R :-
    Nodes = to_sorted_list(union(map(fst, D), map(snd, D))),
    R = solutions_set((
        pred({N1, N2}::out) is nondet :-
            member(N1, Nodes),
            member(N2, Nodes),
            N2 > N1,
            neverMet(D, {N1, N2})
    )).

subsetExactNCond(0,  _,   _, set([])).
subsetExactNCond(N, UP, SIn, Ans) :-
    member(X, SIn),
    remove(X, SIn, S),

    P = (pred(Y::in) is semidet :- compare((<), X, Y), UP(Y)),
    divide(P, S, SRest, _),

    subsetExactNCond(N - 1, UP, SRest, AnsRest),
    Ans = insert(AnsRest, X).




:- func pprintHanchan(list(table)) = list(list(player)).
pprintHanchan(H) = map(to_sorted_list, H).

:- func pprintDB2Dot(metDB) = string.
pprintDB2Dot(DB) = "strict graph { " ++ join_list("; ", Lines) ++ "}" :-
    Lines = map(func({P1,P2}) = string(P1) ++ " -- " ++ string(P2), to_sorted_list(DB))
    .


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

:- pred main(option_table(myoption)::in, io::di, io::uo) is cc_multi.
main(Options, !IO) :-
    NPlayers = lookup_int_option(Options, playerCount),
    NHanchans = lookup_int_option(Options, hanchanCount),
    (
        NPlayers \= NPlayers // 4 * 4 ->
        write_string("Players count must be a multiple of 4.\n", !IO),
        set_exit_status(2, !IO)
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
