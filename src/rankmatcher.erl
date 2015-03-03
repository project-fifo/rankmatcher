%%%-------------------------------------------------------------------
%%% @author Heinz Nikolaus Gies <heinz@licenser.net>
%%% @copyright (C) 2012, Heinz Nikolaus Gies
%%% @doc
%%%
%%% @end
%%% Created : 19 Oct 2012 by Heinz Nikolaus Gies <heinz@licenser.net>
%%%-------------------------------------------------------------------
-module(rankmatcher).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-export([match/3,
         apply_scales/1]).

-type rankmatcher_weighting() :: cant |
                                 must |
                                 integer().

-type path() :: [{binary(), integer()}].

-type rankmatcher_flat_condition() ::
        '>=' | '>' | '=<' | '<' | '=:=' | '=/='.

-type rankmatcher_set_condition() ::
        'subset' | 'superset' | 'disjoint' | 'element' | 'oneof'.

-type rankmatcher_dist_condition() ::
        {'min-distance', path()} | {'max-distance', path()}.

-type rankmatcher_permission_condition() ::
        'allowed'.

-type rankmatcher_flat_reference() ::
        binary() | ordsets:ordset(term()) | number() | tuple().

-type rankmatcher_set_reference() ::
        ordsets:ordset(term()) | path().

-type rankmatcher_permission_reference() ::
        [libsnarlmatch:permission()].

-type rankmatcher_dist_reference() ::
        integer().



-type rankmatcher_rule() ::
        {'rand', Min::integer(), Max::integer()} |
        {'scale', Attribute::binary(), Low::integer(), High::integer()} |
        {'scale-distance', Path::path(), Attribute::binary(), Low::integer(), High::integer()} |
        {Weight::rankmatcher_weighting(),
         Condituion::rankmatcher_flat_condition(),
         Attribute::binary(),
         Reference::rankmatcher_flat_reference()} |
        {Weight::rankmatcher_weighting(),
         Condituion::rankmatcher_set_condition(),
         Attribute::binary(),
         Reference::rankmatcher_set_reference()} |
        {Weight::rankmatcher_weighting(),
         Condituion::rankmatcher_dist_condition(),
         Attribute::binary(),
         Reference::rankmatcher_dist_reference()} |
        {Weight::rankmatcher_weighting(),
         Condituion::rankmatcher_permission_condition(),
         Permission::[binary() | {binary(), binary()}],
         Reference::rankmatcher_permission_reference()}.

-export_type([rankmatcher_rule/0]).

apply_scales([]) ->
    [];

apply_scales([{{_, []}, _} | _] = Res) ->
    [{N, Key} || {{N, []}, Key} <- Res];

apply_scales([{{_, [{scale, _, V, _, _} | _]}, _} | _] = Res) ->
    {_, _, R} = apply_scale(Res, V, V),
    apply_scales(R);

apply_scales([{{_, [{random, _, _} | _]}, _} | _] = Res) ->
    random:seed(erlang:now()),
    apply_scales(apply_random(Res)).

apply_scale([{{N, [{scale, _, V, Low, High} | RScales] }, Key} | R],
            Min, Max) when V < Min->
    {MinR, MaxR, Res} = apply_scale(R, V, Max),
    {MinR, MaxR, [{{N + scale(Low, High, MinR, MaxR, V), RScales}, Key} | Res]};

apply_scale([{{N, [{scale, _, V, Low, High} | RScales] }, Key} | R],
            Min, Max) when V > Max->
    {MinR, MaxR, Res} = apply_scale(R, Min, V),
    {MinR, MaxR, [{{N + scale(Low, High, MinR, MaxR, V), RScales}, Key} | Res]};

apply_scale([{{N, [{scale, _, V, Low, High} | RScales] }, Key} | R],
            Min, Max) ->
    {MinR, MaxR, Res} = apply_scale(R, Min, Max),
    {MinR, MaxR, [{{N + scale(Low, High, MinR, MaxR, V), RScales}, Key} | Res]};

apply_scale([], Min, Max) ->
    {Min, Max, []}.

apply_random([]) ->
    [];

apply_random([{{N, [{random, Min, Max} | RScales] }, Key} | R]) ->
    Rand = Min + random:uniform(Max - Min) -1,
    [{{N + Rand, RScales}, Key} | apply_random(R)].


scale(Low, High, Min, Max, V) ->
    DOut = High - Low,
    DIn = case Max - Min of
              0 ->
                  1;
              R ->
                  R
          end,
    round(Low + ((V - Min) / DIn) * DOut).

match(Element, Getter, [{must, Op, Res, V}]) ->
    match(Element, Getter, {Op, Res, V}) andalso {0, []};

match(Element, Getter, [{cant, Op, Res, V}]) ->
    (not match(Element, Getter, {Op, Res, V})) andalso {0, []};

match(Element, Getter, [{scale, Res, Min, Max}]) ->
    {0, [{scale, Res, Getter(Element, Res), Min, Max}]};

match(_Element, _Getter, [{random, Min, Max}]) ->
    {0, [{random, Min, Max}]};

match(Element, Getter, [{N, Op, Res, V}]) when is_integer(N) ->
    case match(Element, Getter, {Op, Res, V}) of
        true ->
            {N, []};
        false ->
            {0, []}
    end;

match(_, _, [])  ->
    {0, []};

match(Element, Getter, [{must, Op, Res, V} | R]) ->
    match(Element, Getter, {Op, Res, V}) andalso match(Element, Getter, R);

match(Element, Getter, [{cant, Op, Res, V} | R]) ->
    (not match(Element, Getter, {Op, Res, V})) andalso match(Element, Getter, R);

match(Element, Getter, [{scale, Res, Min, Max} | R]) ->
    case match(Element, Getter, R) of
        false ->
            false;
        {N, Scales} when is_integer(N) ->
            {N, [{scale, Res, Getter(Element, Res), Min, Max} | Scales]}
    end;

match(Element, Getter, [{'scale-distance', Path, Res, Min, Max} | R]) ->
    case match(Element, Getter, R) of
        false ->
            false;
        {N, Scales} when is_integer(N) ->
            {N, [{scale, Res, distance(Path, Getter(Element, Res)), Min, Max} | Scales]}
    end;

match(Element, Getter, [{random, Min, Max} | R]) ->
    case match(Element, Getter, R) of
        false ->
            false;
        {N, Scales} when is_integer(N) ->
            {N, [{random, Min, Max} | Scales]}
    end;

match(Element, Getter, [{N, Op, Res, V} | R]) when is_integer(N) ->
    case match(Element, Getter, {Op, Res, V}) of
        false ->
            match(Element, Getter, R);
        true ->
            case match(Element, Getter, R) of
                false ->
                    false;
                {M, Scales} when is_integer(M) ->
                    {N + M, Scales}
            end
    end;

match(Element, Getter, {'>=', Resource, Value}) ->
    Getter(Element, Resource) >= Value;

match(Element, Getter, {'=<', Resource, Value}) ->
    Getter(Element, Resource) =< Value;

match(Element, Getter, {'>', Resource, Value}) ->
    Getter(Element, Resource) > Value;

match(Element, Getter, {'<', Resource, Value}) ->
    Getter(Element, Resource) < Value;

match(Element, Getter, {'=:=', Resource, Value}) ->
    Getter(Element, Resource) =:= Value;

match(Element, Getter, {'=/=', Resource, Value}) ->
    Getter(Element, Resource) =/= Value;

match(Element, Getter, {{'min-distance', Path}, Resource, Value}) ->
    distance(Path, Getter(Element, Resource)) >= Value;

match(Element, Getter, {{'max-distance', Path}, Resource, Value}) ->
    distance(Path, Getter(Element, Resource)) =< Value;

match(Element, Getter, {'subset', Resource, Value}) ->
    ordsets:is_subset(
      ordsets:from_list(Value),
      ordsets:from_list(Getter(Element, Resource)));

match(Element, Getter, {'superset', Resource, Value}) ->
    ordsets:is_subset(
      ordsets:from_list(Getter(Element, Resource)),
      ordsets:from_list(Value));

match(Element, Getter, {'disjoint', Resource, Value}) ->
    ordsets:is_disjoint(
      ordsets:from_list(Value),
      ordsets:from_list(Getter(Element, Resource)));

match(Element, Getter, {'element', Resource, Value}) ->
    ordsets:is_element(
      Value,
      ordsets:from_list(Getter(Element, Resource)));

match(Element, Getter, {'oneof', Resource, Value}) ->
    ordsets:is_element(
      Getter(Element, Resource),
      ordsets:from_list(Value));

match(Element, Getter, {'allowed', Perission, Permissions}) ->
    libsnarlmatch:test_perms(create_permission(Element, Getter, Perission, []), Permissions).

create_permission(_, _, [], Out) ->
    lists:reverse(Out);

create_permission(Element, Getter, [{<<"res">>, R} | In], Out) ->
    create_permission(Element, Getter,  In, [Getter(Element, R) | Out]);

create_permission(Element, Getter, [P | In], Out) ->
    create_permission(Element, Getter, In, [ P | Out]).

distance([A | Ra], [A | Rb]) ->
    distance(Ra, Rb);

distance(A, B) ->
    lists:sum([V || {_, V} <- A]) + lists:sum([V || {_, V} <- B]).

-ifdef(TEST).

test_hypervisort() ->
    {<<"test-hypervisor">>,
     dict:from_list(
       [{<<"path">>, [{<<"a">>, 3}, {<<"b">>, 2}, {<<"c">>, 1}]},
        {<<"num-res">>, 1024},
        {<<"set-res">>, [1,2,3]},
        {<<"str-res">>, <<"str">>}])}.

test_getter({Name, _}, <<"name">>) ->
    Name;

test_getter({_, Resources}, Resource) ->
    dict:fetch(Resource, Resources).

oneof_test() ->
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'oneof', <<"num-res">>, [1023, 1024, 1025]})),
    ?assertNot(match(test_hypervisort(),
                     fun test_getter/2,
                     {'oneof', <<"num-res">>, [1023, 1025, 1026]})).

number_gt_test() ->
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'=<', <<"num-res">>, 1024})),
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'=<', <<"num-res">>, 2000})),
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'<', <<"num-res">>, 2000})),
    ?assertNot(match(test_hypervisort(),
                     fun test_getter/2,
                     {'<', <<"num-res">>, 1000})),
    ?assertNot(match(test_hypervisort(),
                     fun test_getter/2,
                     {'=<', <<"num-res">>, 1000})).

number_lt_test() ->
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'>=', <<"num-res">>, 1024})),
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'>=', <<"num-res">>, 1000})),
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'>', <<"num-res">>, 1000})),
    ?assertNot(match(test_hypervisort(),
                     fun test_getter/2,
                     {'>', <<"num-res">>, 2000})),
    ?assertNot(match(test_hypervisort(),
                     fun test_getter/2,
                     {'>=', <<"num-res">>, 2000})).

number_eq_test() ->
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'=:=', <<"num-res">>, 1024})),
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'=:=', <<"str-res">>, <<"str">>})),
    ?assertNot(match(test_hypervisort(),
                     fun test_getter/2,
                     {'=:=', <<"num-res">>, 1000})).

number_meq_test() ->
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'=/=', <<"num-res">>, 1000})),
    ?assertNot(match(test_hypervisort(),
                     fun test_getter/2,
                     {'=/=', <<"num-res">>, 1024})).

number_element_test() ->
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'element', <<"set-res">>, 1})),
    ?assertNot(match(test_hypervisort(),
                     fun test_getter/2,
                     {'element', <<"set-res">>, 4})).

number_subset_test() ->
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'subset', <<"set-res">>, [1,2,3]})),
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'subset', <<"set-res">>, [1,2]})),
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'subset', <<"set-res">>, [1,3]})),
    ?assertNot(match(test_hypervisort(),
                     fun test_getter/2,
                     {'subset', <<"set-res">>, [1,2,3,4]})).

number_superset_test() ->
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'superset', <<"set-res">>, [1,2,3]})),
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'superset', <<"set-res">>, [1,2,3,4]})),
    ?assertNot(match(test_hypervisort(),
                     fun test_getter/2,
                     {'superset', <<"set-res">>, [1,2]})),
    ?assertNot(match(test_hypervisort(),
                     fun test_getter/2,
                     {'superset', <<"set-res">>, [1,4]})).

number_disjoint_test() ->
    ?assert(match(test_hypervisort(),
                  fun test_getter/2,
                  {'disjoint', <<"set-res">>, [4,5,6]})),
    ?assertNot(match(test_hypervisort(),
                     fun test_getter/2,
                     {'disjoint', <<"set-res">>, [1]})),
    ?assertNot(match(test_hypervisort(),
                     fun test_getter/2,
                     {'disjoint', <<"set-res">>, [1,4]})).

multi_must_one_ok_test() ->
    ?assertEqual({0, []},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{must, '=<', <<"num-res">>, 1024}])),
    ?assertEqual({0, []},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{must, '=:=', <<"num-res">>, 1024}])).

multi_must_two_ok_test() ->
    ?assertEqual({0, []},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{must, '=<', <<"num-res">>, 1024},
                        {must, '=:=', <<"num-res">>, 1024}])).

multi_must_one_not_ok_test() ->
    ?assertEqual(false,
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{must, '<', <<"num-res">>, 1024}])),
    ?assertEqual(false,
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{must, '=/=', <<"num-res">>, 1024}])).

multi_must_two_not_ok_test() ->
    ?assertEqual(false,
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{must, '<', <<"num-res">>, 1024},
                        {must, '=:=', <<"num-res">>, 1024}])),
    ?assertEqual(false,
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{must, '=<', <<"num-res">>, 1024},
                        {must, '=/=', <<"num-res">>, 1024}])).

multi_cant_one_ok_test() ->
    ?assertEqual(false,
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{cant, '=<', <<"num-res">>, 1024}])),
    ?assertEqual(false,
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{cant, '=:=', <<"num-res">>, 1024}])).

multi_cant_two_ok_test() ->
    ?assertEqual(false,
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{cant, '=<', <<"num-res">>, 1024},
                        {cant, '=:=', <<"num-res">>, 1024}])).
multi_cant_one_not_ok_test() ->
    ?assertEqual({0, []},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{cant, '<', <<"num-res">>, 1024}])),
    ?assertEqual({0, []},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{cant, '=/=', <<"num-res">>, 1024}])).

multi_cant_two_not_ok_test() ->
    ?assertEqual(false,
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{cant, '<', <<"num-res">>, 1024},
                        {cant, '=:=', <<"num-res">>, 1024}])),
    ?assertEqual(false,
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{cant, '=<', <<"num-res">>, 1024},
                        {cant, '=/=', <<"num-res">>, 1024}])).
count_test() ->
    ?assertEqual({2, []},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{1, '<', <<"num-res">>, 1024},
                        {2, '=:=', <<"num-res">>, 1024}])),
    ?assertEqual({1, []},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{1, '=<', <<"num-res">>, 1024},
                        {2, '=/=', <<"num-res">>, 1024}])).

mix_test() ->
    ?assertEqual(false,
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{must, '<', <<"num-res">>, 1024},
                        {2, '=:=', <<"num-res">>, 1024}])),
    ?assertEqual({0, []},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{1, '<', <<"num-res">>, 1024},
                        {must, '=:=', <<"num-res">>, 1024}])).

scale_gen_test() ->
    ?assertEqual({0, [{scale, <<"num-res">>, 1024, 0, 10}]},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{scale, <<"num-res">>, 0, 10}])).

scale_calc_test() ->
    ?assertEqual(0, scale(0, 10, 0, 20, 0)),
    ?assertEqual(10, scale(0, 10, 0, 20, 20)),
    ?assertEqual(5, scale(0, 10, 0, 20, 10)).

scale_full_test() ->
    ?assertEqual(
       [{0, a}, {5, b}, {10, c}],
       apply_scales(
         [{{0, [{scale, <<"num-res">>, 0, 0, 10}]}, a},
          {{0, [{scale, <<"num-res">>, 1024, 0, 10}]}, b},
          {{0, [{scale, <<"num-res">>, 2048, 0, 10}]}, c}])).

scale_reverse_test() ->
    ?assertEqual(
       [{10, a}, {5, b}, {0, c}],
       apply_scales(
         [{{0, [{scale, <<"num-res">>, 0, 10, 0}]}, a},
          {{0, [{scale, <<"num-res">>, 1024, 10, 0}]}, b},
          {{0, [{scale, <<"num-res">>, 2048, 10, 0}]}, c}])).

random_test() ->
    [{A, a}, {B, b}, {C, c}] =
        apply_scales(
          [{{0, [{random, 0, 10}]}, a},
           {{0, [{random, 0, 10}]}, b},
           {{0, [{random, 0, 10}]}, c}]),
    ?assert(A >= 0),
    ?assert(A =< 10),
    ?assert(B >= 0),
    ?assert(B =< 10),
    ?assert(C >= 0),
    ?assert(C =< 10).

empty_test() ->
    ?assertEqual({0, []},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [])).

create_permission_test() ->
    ?assertEqual(create_permission(test_hypervisort(), fun test_getter/2,
                                   [some, permission], []), [some, permission]),
    ?assertEqual(create_permission(test_hypervisort(), fun test_getter/2,
                                   [some, <<"test">>, permission], []),
                 [some, <<"test">>, permission]).

create_permission_res_test() ->
    ?assertEqual(create_permission(test_hypervisort(), fun test_getter/2, [some, {<<"res">>, <<"str-res">>}, permission], []), [some, <<"str">>, permission]).

create_permission_name_test() ->
    ?assertEqual(create_permission(test_hypervisort(), fun test_getter/2, [some, {<<"res">>, <<"name">>}, permission], []), [some, <<"test-hypervisor">>, permission]).

raw_distance_test() ->
    P1 = [{a, 1}, {b, 2}, {c, 3}],
    P2 = [{a, 1}, {d, 4}, {c, 5}],
    P3 = [{a, 1}, {b, 2}, {d, 4}],
    ?assertEqual(6, distance([], P1)),
    ?assertEqual(0, distance(P1, P1)),
    ?assertEqual(14, distance(P1, P2)),
    ?assertEqual(7, distance(P1, P3)).

scale_distance_test() ->
    P1 = [{<<"a">>, 3}, {<<"b">>, 2}, {<<"c">>, 1}],
    P2 = [{<<"a">>, 3}, {<<"b">>, 2}, {<<"d">>, 1}],
    P3 = [{<<"a">>, 3}, {<<"a">>, 2}, {<<"d">>, 1}],
    ?assertEqual({0,[{scale,<<"path">>,0,0,10}]},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{'scale-distance', P1, <<"path">>, 0, 10}])),
    ?assertEqual({0,[{scale,<<"path">>,2,0,10}]},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{'scale-distance', P2, <<"path">>, 0, 10}])),
    ?assertEqual({0,[{scale,<<"path">>,6,0,10}]},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{'scale-distance', P3, <<"path">>, 0, 10}])).

min_max_distance_test() ->
    P1 = [{<<"a">>, 3}, {<<"b">>, 2}, {<<"c">>, 1}],
    P2 = [{<<"a">>, 3}, {<<"b">>, 2}, {<<"d">>, 1}],
    P3 = [{<<"a">>, 3}, {<<"a">>, 2}, {<<"d">>, 1}],
    ?assertEqual({0, []},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{must, {'max-distance', P1}, <<"path">>, 1}])),
    ?assertEqual(false,
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{must, {'min-distance', P1}, <<"path">>, 1}])),
    %% Dist(P1, P2) should be 2
    ?assertEqual({0, []},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{must, {'max-distance', P2}, <<"path">>, 2}])),
    ?assertEqual(false,
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{must, {'max-distance', P2}, <<"path">>, 1}])),
    %% Dist(P1, P3) should be 6
    ?assertEqual({0, []},
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{must, {'min-distance', P3}, <<"path">>, 5}])),
    ?assertEqual(false,
                 match(test_hypervisort(),
                       fun test_getter/2,
                       [{must, {'min-distance', P3}, <<"path">>, 7}])),
    ok.

-endif.
