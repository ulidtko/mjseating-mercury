% Copyright (C) 2015-2020 Max Ulidtko <ulidtko@gmail.com>. All rights reserved.
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
%     mmc --grade hlc.gc -O2 mjseating.m
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
:- import_module set_tree234.

:- type player == int.

:- type table == quad(player).
:- type hanchan == list(table).
:- type schedule == list(hanchan).

:- type quad(T) == {T, T, T, T}.
:- type pquad  == quad(player).
:- type pquads == set(pquad).
:- type iquad  == int.
:- type iquads == set_tree234(iquad).


:- pred main(io::di, io::uo) is cc_multi.

%------------------------------------------------------------------------------%
:- implementation.

:- import_module bool, int, float, char, string.
:- import_module bimap.
:- import_module map.
:- import_module sparse_bitset.
:- import_module version_array.
:- import_module solutions.
:- import_module time.


% The context gathers all "almost static" data: things we can precompute
% before starting search, and query efficiently during the search.
% None of this mutates at search-time (the whole ctx is read-only),
% but it depends on input parameters and so can't be completely static.
:- type ctx ---> ctx(
        allplayers :: set_tree234(player),
        numtables :: int,
        numhanchans :: int,
        quadmap :: quadenum,
        playerquads :: map(player, iquads),
        xsects :: xsects
    ).

:- type quadenum == bimap(int, pquad).
:- type xsects == version_array(sparse_bitset(iquad)).

%------------------------------ UTILITIES -------------------------------------%

:- func initCtx(int, int) = ctx is det.
initCtx(NTables, NHanchans) = ctx(
        PlayerSet,
        NTables,
        NHanchans,
        QuadsEnum,
        PlayerQuadsMap,
        Intersections
    ) :- PlayerSet = from_list(1..(NTables * 4)),
         AllQuads = allQuads(to_set(PlayerSet)),
         QuadsEnum = quadNumbering(AllQuads),
         Intersections = precomputeXsectBitmaps(QuadsEnum),
         PlayerQuadsMap = precomputePlayerQuadMap(PlayerSet, QuadsEnum).

:- func quadToSet(quad(T)) = set(T).
quadToSet({PA,PB,PC,PD}) = sorted_list_to_set([PA,PB,PC,PD]).

:- func tablePairs(table) = list({player,player}).
tablePairs({A,B,C,D}) = [{A,B}, {A,C}, {A,D}, {B,C}, {B,D}, {C,D}].

:- pred listChoice(list(T)::in, T::out, list(T)::out) is nondet.
listChoice([X | T], X, T).
listChoice([_ | T], X, R) :- listChoice(T, X, R).

:- pred freePlayersInQuad(set(player)::in, pquad::in) is semidet.
freePlayersInQuad(FreePlayers, {PA,PB,PC,PD}) :-
    member(PA, FreePlayers),
    member(PB, FreePlayers),
    member(PC, FreePlayers),
    member(PD, FreePlayers).

:- pred freePlayersAndFirst(set(player)::in, player::in, pquad::in) is semidet.
freePlayersAndFirst(FreePlayers, SpecificFirst, {PA,PB,PC,PD}) :-
    PA = SpecificFirst,
    member(PB, FreePlayers),
    member(PC, FreePlayers),
    member(PD, FreePlayers).

% two quads "intersect" iff they share a player pair.
:- pred quadXsect(pquad::in, pquad::in) is semidet.
quadXsect({PA1, PB1, PC1, PD1}, {PA2, PB2, PC2, PD2}) :-
    %not set.intersect(from_list(tablePairs(Q1)), from_list(tablePairs(Q2)), set.init).
    %-- this way it's much faster (due to no allocations):
    {PA1,PB1} = {PA2,PB2}; {PA1,PC1} = {PA2,PB2}; {PA1,PD1} = {PA2,PB2};
        {PB1,PC1} = {PA2,PB2}; {PB1,PD1} = {PA2,PB2}; {PC1,PD1} = {PA2,PB2};
    {PA1,PB1} = {PA2,PC2}; {PA1,PC1} = {PA2,PC2}; {PA1,PD1} = {PA2,PC2};
        {PB1,PC1} = {PA2,PC2}; {PB1,PD1} = {PA2,PC2}; {PC1,PD1} = {PA2,PC2};
    {PA1,PB1} = {PA2,PD2}; {PA1,PC1} = {PA2,PD2}; {PA1,PD1} = {PA2,PD2};
        {PB1,PC1} = {PA2,PD2}; {PB1,PD1} = {PA2,PD2}; {PC1,PD1} = {PA2,PD2};
    {PA1,PB1} = {PB2,PC2}; {PA1,PC1} = {PB2,PC2}; {PA1,PD1} = {PB2,PC2};
        {PB1,PC1} = {PB2,PC2}; {PB1,PD1} = {PB2,PC2}; {PC1,PD1} = {PB2,PC2};
    {PA1,PB1} = {PB2,PD2}; {PA1,PC1} = {PB2,PD2}; {PA1,PD1} = {PB2,PD2};
        {PB1,PC1} = {PB2,PD2}; {PB1,PD1} = {PB2,PD2}; {PC1,PD1} = {PB2,PD2};
    {PA1,PB1} = {PC2,PD2}; {PA1,PC1} = {PC2,PD2}; {PA1,PD1} = {PC2,PD2};
        {PB1,PC1} = {PC2,PD2}; {PB1,PD1} = {PC2,PD2}; {PC1,PD1} = {PC2,PD2}.

% two quads "conflict" iff they can't be scheduled both into a single hanchan.
:- pred quadConflictNot(pquad::in, pquad::in) is semidet.
quadConflictNot({PA1, PB1, PC1, PD1}, {PA2, PB2, PC2, PD2}) :-
    PA1 \= PA2, PB1 \= PA2, PC1 \= PA2, PD1 \= PA2,
    PA1 \= PB2, PB1 \= PB2, PC1 \= PB2, PD1 \= PB2,
    PA1 \= PC2, PB1 \= PC2, PC1 \= PC2, PD1 \= PC2,
    PA1 \= PD2, PB1 \= PD2, PC1 \= PD2, PD1 \= PD2.
%:- pragma memo(quadConflictNot/2).
:- pred quadConflict(pquad::in, pquad::in) is semidet.
quadConflict(Q1, Q2) :- not quadConflictNot(Q1, Q2).


%------------------------------ CORE LOGIC ------------------------------------%

% allQuads computes exactly C(NPlayers, 4) possible quads.
:- func allQuads(set(player)) = pquads is det.
allQuads(Ps) = Qs :- allQuads(Ps, Qs).
:- pred allQuads(set(player)::in, pquads::out) is det.
allQuads(Players, Quads) :-
    solutions_set((
        pred({PA,PB,PC,PD}::out) is nondet :-
            member(PA, Players),
            member(PB, Players), PB > PA,
            member(PC, Players), PC > PB,
            member(PD, Players), PD > PC
    ), Quads).

% establishes quad numbering -- a quad(player) <-> int bijection.
:- func quadNumbering(pquads) = quadenum is det.
quadNumbering(Qs) =
    bimap.det_insert_from_corresponding_lists(
        0..(count(Qs)-1), to_sorted_list(Qs), bimap.init).

% compute once the "quads intersect" relation over all quads.
:- func precomputeXsectBitmaps(quadenum) = xsects is det.
precomputeXsectBitmaps(QN) = from_list( list.reverse( bimap.foldl(
    func(_IQ, Q, LAcc) = [precomputeXsectBitmap(Q, QN) | LAcc],
    QN, [] ))).

:- func precomputeXsectBitmap(pquad, quadenum) = sparse_bitset(iquad) is det.
precomputeXsectBitmap(Q0, QN) = sorted_list_to_set(list.reverse(bimap.foldl(
    func(IQ, Q, LAcc) = (if quadXsect(Q0, Q) then [IQ | LAcc] else LAcc),
    QN, []))).

% cached lookup "which quads given player appears in"
:- func precomputePlayerQuadMap(
    set_tree234(player), quadenum) = map(player, iquads) is det.
precomputePlayerQuadMap(Players, QuadMap) = map.optimize(R) :-
    bimap.foldl(
        pred(IQ::in, {A,B,C,D}::in, MAcc0::in, MNew::out) is det :- (
            map.det_transform_value(insert(IQ), A, MAcc0, MAcc1),
            map.det_transform_value(insert(IQ), B, MAcc1, MAcc2),
            map.det_transform_value(insert(IQ), C, MAcc2, MAcc3),
            map.det_transform_value(insert(IQ), D, MAcc3, MNew)
        ),
        QuadMap, Map0, R),
    Map0 = map.from_corresponding_lists(
        L @ to_sorted_list(Players),
        list.duplicate(length(L), set_tree234.init)
    ).

:- func cullConflictingQuads(pquads, pquad) = pquads.
cullConflictingQuads(QS, Qc) = filter(quadConflictNot(Qc), QS).

:- func cullConflictingIquads(quadenum, iquads, iquad) = iquads.
cullConflictingIquads(QM, IQs, IQx) = filter(
    %-- TODO optimize here using Ctx^playerquads
    (pred(IQy::in) is semidet :- quadConflictNot(lookup(QM, IQx), lookup(QM, IQy))),
    IQs).

:- func cullHanchanQuads(hanchan, pquads) = pquads.
cullHanchanQuads(Hanchan, Qs) = set.filter((
        pred({A,B,C,D}::in) is semidet :- set.intersect(
            HanchanPairs,
            sorted_list_to_set([{A,B},{A,C},{A,D},{B,C},{B,D},{C,D}]),
            set.init
        )
    ), Qs) :-
    HanchanPairs = set(condense(map(tablePairs, Hanchan)))
    . %-- 29% allocs here

:- pred sufficientQuadsCut(int::in, set(player)::in, pquads::in) is semidet.
sufficientQuadsCut(NH, Players, Quads) :-
    %-- assert there's enough Quads for each player for NH more hanchans
    set.all_true(
        pred(P::in) is semidet :- countPlayersQuads(P, Quads) >= NH,
        Players).

:- func countPlayersQuads(player, pquads) = int.
countPlayersQuads(P, Quads) = set.count(set.filter(
    (pred({A,B,C,D}::in) is semidet :- P = A; P = B; P = C; P = D),
    Quads)).

:- pred sufficientIquadsCut(
    ctx::in,
    int::in,
    set_tree234(player)::in,
    iquads::in) is semidet.
sufficientIquadsCut(Ctx, NH, Players, Iquads) :-
    %count(Players) =< count(Iquads),
    all_true(
        pred(P::in) is semidet :- count(
            lookup(Ctx^playerquads, P) `intersect` Iquads
            ) >= NH,
        Players).


:- pred fillAllTables(
      list(table)::out
    , set(player)::in
    , pquads::in
    ) is nondet.
fillAllTables(   []    , set.init, _).
fillAllTables([Q0 | QN1], Players, Quads) :-
    %-- due to table symmetry, we only ever try to schedule the minimum player.
    %-- if even this can't be done: we fail and cut the search branch early.
    [MinPlayer | _] = to_sorted_list(Players),

    %-- select quads consisting of only free players
    NonBoringQuads = set.filter(freePlayersAndFirst(Players, MinPlayer), Quads),
    %NonBoringQuads = set.filter(freePlayersInQuad(Players), Quads),

    %-- select a table configuration (quad)
    listChoice(to_sorted_list(NonBoringQuads), Q0, _),

    %-- exclude impossible candidate quads according to our choice of Q0
    QuadsCulled = cullConflictingQuads(Quads, Q0),

    %-- ensure there's at least 1 quad for each player remaining
    sufficientQuadsCut(1, PlayersRest, QuadsCulled),

    %-- recurse for rest of players
    PlayersRest = set.difference(Players, quadToSet(Q0)),
    fillAllTables(QN1, PlayersRest, QuadsCulled).


:- pred searchNHanchans(
      {int, int}::in
    , set(player)::in
    , schedule::out
    , pquads::out
    ) is nondet.
searchNHanchans({0, _}, Players, [], Q) :- allQuads(Players, Q).
searchNHanchans({N, NH}, Players, [H0 | Hn1], QuadsUpd) :-
    N > 0,
    searchNHanchans({N - 1, NH}, Players, Hn1, QuadsBase),
    fillAllTables(H0, Players, QuadsBase),
    QuadsUpd = cullHanchanQuads(H0, QuadsBase),
    sufficientQuadsCut(NH - N, Players, QuadsUpd),

    trace [run_time(env("TRACE")), io(!IO)] (
        io.format("=== Candidate hanchan %d/%d ===\n", [i(N), i(NH)], !IO),
        io.write_string("    Tables: " ++ string([H0 | Hn1]), !IO), io.nl(!IO),
        io.write_string("    Quads: " ++ string(QuadsUpd), !IO), io.nl(!IO)
    )
    .


:- pred fillHanchan(
    ctx::in,
    set_tree234(player)::in,
    set_tree234(iquad)::in,
    list(iquad)::in,
    list(iquad)::out,
    sparse_bitset(iquad)::out) is nondet.
fillHanchan(_,   init,    _,           _,                  [],        init).
fillHanchan(Ctx, Players, AvailIquads, [TMin0i|TMins], [T0i|TTi], NewXsects) :-
    %-- symmbreak tables-per-hanchan
    remove_least(MinPlayer, Players, PlayersSansMin),
    NonBoringIquads = filter(
        pred(IQ::in) is semidet :- (
            IQ >= TMin0i, %-- symmbreak hanchans-per-schedule
            {A,B,C,D} = lookup(Ctx^quadmap, IQ),
            MinPlayer = A,
            member(B, PlayersSansMin),
            member(C, PlayersSansMin),
            member(D, PlayersSansMin)
        ), AvailIquads),

    %-- the choice point
    member(T0i, NonBoringIquads),

    HereXsects = Ctx^xsects^elem(T0i),
    IquadsNX = AvailIquads `difference` from_set(to_set(HereXsects)),
    IquadsRestPlayers = cullConflictingIquads(Ctx^quadmap, IquadsNX, T0i),
    {MinPlayer, PB, PC, PD} = lookup(Ctx^quadmap, T0i),
    PlayersRest = PlayersSansMin `difference` from_list([PB, PC, PD]),
    sufficientIquadsCut(Ctx, 1, PlayersRest, IquadsRestPlayers),
    fillHanchan(Ctx, PlayersRest, IquadsRestPlayers, TMins, TTi, MoreXsects),
    NewXsects = HereXsects `union` MoreXsects.

:- pred searchSchedule(ctx::in, schedule::out) is nondet.
searchSchedule(Ctx, Solution) :-
    NP = 4 * NT @ (Ctx^numtables),
    NH = Ctx ^ numhanchans,

    MinIquads = duplicate(NT, -1),
    AvailIquads0 = from_list(bimap.ordinates(Ctx^quadmap))
                `with_type` set_tree234(iquad), %-- [0..NQ)

    trace [io(!IO)] (
        io.format("--- searchSchedule entry init done ---\n", [], !IO),
        io.report_stats("full_memory_stats", !IO)
        ),

    foldl3(
        pred(HanchanIndex::in,
            AvailIquads::in,
            AvailIquads1::out,
            MinIquads0::in,
            MinIquads1::out,
            S0::in,
            [TakenHanchan|S0]::out) is nondet :-
        (
            %-- the choice point
            fillHanchan(Ctx, Ctx^allplayers, AvailIquads, MinIquads0,
                TakenHanchan, XsectIquads_out),
            AvailIquads1 = AvailIquads `difference`
                from_set(to_set(XsectIquads_out)) `with_type` iquads,

            %-- the whole last hanchan (+1) is used to set MinIquads1
            split_last(TakenHanchan, MinIquadsPre, MinIquadsLast),
            MinIquads1 = MinIquadsPre ++ [MinIquadsLast + 1],

            %-- heuristic check
            sufficientIquadsCut(Ctx, NH - HanchanIndex, Ctx^allplayers, AvailIquads1)
        ),
        1..NH,
        AvailIquads0, _,
        MinIquads, _,
        [], SolIqs
    ),

    %-- remap list(list(iquad)) back to expected Solution
    Solution = map(func(H) = map(func(IQ) = lookup(Ctx^quadmap, IQ), H), SolIqs)
    .

%---------------------------------- CMDLINE -----------------------------------%

:- import_module getopt_io.
:- type myoption ---> help; playerCount; hanchanCount; solutionsLimit.
:- pred shortOpt(char::in, myoption::out) is semidet.
shortOpt('h', help).
shortOpt('P', playerCount).
shortOpt('H', hanchanCount).
shortOpt('L', solutionsLimit).
:- pred longOpt(string::in, myoption::out) is semidet.
longOpt("help", help).
longOpt("players", playerCount).
longOpt("hanchans", hanchanCount).
longOpt("limit", solutionsLimit).
:- pred defOpt(myoption::out, option_data::out) is multi.
defOpt(help, bool(no)).
defOpt(playerCount, int(24)).
defOpt(hanchanCount, int(8)).
defOpt(solutionsLimit, int(20)).

:- func usage = string.
usage = join_list("\n", [
        "Usage: mjseating [OPTIONS]",
        "",
        "Options:",
        "    -h, --help            Show this message and exit",
        "    -P, --players         Set the player count (default is 24)",
        "    -H, --hanchans        Set the number of hanchans (default is 8)",
        "    -L, --limit           Stop after this many solutions found [20]",
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

%------------------------------------ MAIN ------------------------------------%

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
        set_solutionsCap(lookup_int_option(Options, solutionsLimit), !IO),

        run_search({NPlayers, NHanchans}, !IO)
    ).

:- pred wallclock(float, pred(io, io), io, io).
:- mode wallclock(out, pred(di, uo) is det, di, uo) is det.
wallclock(ResultSeconds, Action, !IO) :-
    time.clock(ActionTimestamp0, !IO),
    Action(!IO),
    time.clock(ActionTimestamp1, !IO),
    ResultSeconds = float(ActionTimestamp1 - ActionTimestamp0)
                    / float(time.clocks_per_sec).

:- pred run_search({int, int}::in, io::di, io::uo) is cc_multi.
run_search({NP, NH}, !IO) :-
    %io.write_string("Warming up...", !IO), io.flush_output(!IO),
    %time.clock(InitT0, !IO),
    %
    %Ctx = initCtx(NP // 4, NH),
    %
    %time.clock(InitT1, !IO),
    %SecondsElapsed = float(InitT1 - InitT0) / float(time.clocks_per_sec),
    %io.format(" done in %.3fs.\n", [f(SecondsElapsed)], !IO),

    do_while(
        pred(Solution::out) is nondet :-
            searchNHanchans({NH, NH}, set(1..NP), Solution, _),
            %searchSchedule(Ctx, Solution),
        process_solution,
        !IO
    ),
    %io.report_stats(!IO),
    %io.report_stats("standard", !IO),
    %io.report_stats("full_memory_stats", !IO),
    %io.report_stats("tabling", !IO),
    %benchmarking.report_stats(),
    io.write_string("Printing no more solutions.\n", !IO)
    .

%---------------------------- PRETTY PRINTING ---------------------------------%

:- mutable(nSolutions, int, 0, ground, [untrailed,attach_to_io_state]).
:- mutable(solutionsCap, int, 20, ground, [untrailed,attach_to_io_state]).

:- pred process_solution(list(hanchan)::in, bool::out, io::di, io::uo) is det.
process_solution(S, DoContinue) -->
    print_solution(S),
    get_nSolutions(N),
    set_nSolutions(N + 1),
    get_solutionsCap(Limit),
    { DoContinue = pred_to_bool(N + 1 < Limit) }.

:- mutable(iFmtHanchan, int, 1, ground, [untrailed, attach_to_io_state]).

:- pred print_solution(schedule::in, io::di, io::uo) is det.
print_solution(S) -->
    io.write_string("{\n"),
    set_iFmtHanchan(1),
    io.write_list(reverse(S), ",\n", print_hanchan),
    io.write_string("\n}\n").

:- pred print_hanchan(hanchan::in, io::di, io::uo) is det.
print_hanchan(H) -->
    get_iFmtHanchan(IH),
    set_iFmtHanchan(IH + 1),
    io.format("  \"H%d\": ", [i(IH)]),
    io.write_string(format_hanchan(H)).

:- func format_hanchan(hanchan) = string.
format_hanchan(H) = "[" ++ join_list(", ", map(format_table, H)) ++ "]".
:- func format_table(table) = string.
format_table({PA, PB, PC, PD}) =
    string.format("[%2d, %2d, %2d, %2d]", [i(PA), i(PB), i(PC), i(PD)]).

% vim: filetype=mercury
