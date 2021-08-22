-module(blockchain_txn_bundle_SUITE).

-include_lib("common_test/include/ct.hrl").
-include_lib("eunit/include/eunit.hrl").
-include_lib("kernel/include/inet.hrl").
-include_lib("blockchain/include/blockchain_vars.hrl").

-export([
         init_per_suite/1,
         end_per_suite/1,
         init_per_testcase/2,
         end_per_testcase/2,
         all/0
        ]).

-export([
         basic_test/1,
         negative_test/1,
         double_spend_test/1,
         successive_test/1,
         invalid_successive_test/1,
         single_payer_test/1,
         single_payer_invalid_test/1,
         full_circle_test/1,
         add_assert_test/1,
         invalid_add_assert_test/1,
         single_txn_bundle_test/1,
         bundleception_test/1
        ]).

%% Setup ----------------------------------------------------------------------

all() -> [
          basic_test,
          negative_test,
          double_spend_test,
          successive_test,
          invalid_successive_test,
          single_payer_test,
          single_payer_invalid_test,
          full_circle_test,
          %add_assert_test,  % FIXME dc_entry_not_found
          invalid_add_assert_test,
          single_txn_bundle_test,
          bundleception_test
         ].

init_per_suite(Config) ->
    Config.

end_per_suite(Config) ->
    Config.

init_per_testcase(TestCase, Cfg0) ->
    Cfg1 = blockchain_ct_utils:init_base_dir_config(?MODULE, TestCase, Cfg0),
    Dir = ?config(base_dir, Cfg1),
    StartingBalance = 5000,
    {ok, Sup, Keys={_, _}, _Opts} = test_utils:init(Dir),
    {
        ok,
        _GenesisMembers,
        _GenesisBlock,
        ConsensusMembers0,
        {master_key, MasterKey={_, _}}
    } =
        test_utils:init_chain(
            StartingBalance,
            Keys,
            true,
            #{
                %% Setting vars_commit_delay to 1 is crucial,
                %% otherwise var changes will not take effect.
                ?vars_commit_delay => 1
            }
        ),
    %% Shuffling to discourage reliance on order.
    ConsensusMembers = blockchain_ct_utils:shuffle(ConsensusMembers0),
    N = length(ConsensusMembers),
    ?assert(N > 0, N),
    ?assertEqual(7, N),
    Chain = blockchain_worker:blockchain(), % TODO Return from init_chain instead
    [
        {sup, Sup},
        {master_key, MasterKey},
        {consensus_members, ConsensusMembers},
        {chain, Chain}
    |
        Cfg1
    ].

end_per_testcase(_TestCase, Cfg) ->
    Sup = ?config(sup, Cfg),
    case erlang:is_process_alive(Sup) of
        true ->
            true = erlang:exit(Sup, normal),
            ok = test_utils:wait_until(fun() -> false =:= erlang:is_process_alive(Sup) end);
        false ->
            ok
    end,
    ok.

%% Cases ----------------------------------------------------------------------

basic_test(Cfg) ->
    ConsensusMembers = ?config(consensus_members, Cfg),
    Chain = ?config(chain, Cfg),

    %% Src needs a starting balance, so we pick one from the consensus group.
    %% Dst has no need for a starting balance, so we use an arbitrary address.
    {Src, _} = user_pick_from_cg(ConsensusMembers),
    Dst = user_new(),

    SrcBalance0 = user_balance(Chain, Src),
    DstBalance0 = user_balance(Chain, Dst),

    %% Expected initial balances:
    ?assertEqual(5000, SrcBalance0),
    ?assertEqual(   0, DstBalance0),

    AmountPerTxn = 1000,
    Txns =
        [
            user_txn_pay(Src, Dst, AmountPerTxn, 1),
            user_txn_pay(Src, Dst, AmountPerTxn, 2)
        ],
    TxnBundle = blockchain_txn_bundle_v1:new(Txns),
    ?assertMatch(ok, chain_commit(Chain, ConsensusMembers, TxnBundle)),

    AmountTotal = length(Txns) * AmountPerTxn,
    ?assertEqual(SrcBalance0 - AmountTotal, user_balance(Chain, Src)),
    ?assertEqual(DstBalance0 + AmountTotal, user_balance(Chain, Dst)),

    ok.

negative_test(Cfg) ->
    ConsensusMembers = ?config(consensus_members, Cfg),
    Chain = ?config(chain, Cfg),

    %% Src needs a starting balance, so we pick one from the consensus group.
    {Src, _} = user_pick_from_cg(ConsensusMembers),
    SrcBalance0 = user_balance(Chain, Src),

    %% Dst has no need for a starting balance, so we use an arbitrary address.
    Dst = user_new(),
    DstBalance0 = user_balance(Chain, Dst),

    %% Expected initial balances:
    ?assertEqual(5000, SrcBalance0),
    ?assertEqual(   0, DstBalance0),

    AmountPerTxn = 1000,
    Txns =
        %% Reversed order of nonces, invalidating the bundle:
        [
            user_txn_pay(Src, Dst, AmountPerTxn, 2),
            user_txn_pay(Src, Dst, AmountPerTxn, 1)
        ],
    TxnBundle = blockchain_txn_bundle_v1:new(Txns),

    ?assertMatch(
        {error, {invalid_txns, [{_, invalid_bundled_txns}]}},
        chain_commit(Chain, ConsensusMembers, TxnBundle)
    ),

    %% Balances should not have changed since the bundle was invalid:
    ?assertEqual(SrcBalance0, user_balance(Chain, Src)),
    ?assertEqual(DstBalance0, user_balance(Chain, Dst)),

    ok.

double_spend_test(Cfg) ->
    ConsensusMembers = ?config(consensus_members, Cfg),
    Chain = ?config(chain, Cfg),

    %% Src needs a starting balance, so we pick one from the consensus group.
    {Src, _} = user_pick_from_cg(ConsensusMembers),
    SrcBalance0 = user_balance(Chain, Src),
    SrcNonce = 1,

    %% A destination can be arbitrary, since it has no need for a starting balance.
    %% A destination can be dead-end (no priv key), since we'll never pay from it.
    Dst1 = user_new(),
    Dst2 = user_new(),
    Dst1Balance0 = user_balance(Chain, Dst1),
    Dst2Balance0 = user_balance(Chain, Dst2),

    %% Expected initial balances:
    ?assertEqual(5000, SrcBalance0),
    ?assertEqual(   0, Dst1Balance0),
    ?assertEqual(   0, Dst2Balance0),

    AmountPerTxn = 1000,
    Txns =
        [
            %% good txn: first spend
            user_txn_pay(Src, Dst1, AmountPerTxn, SrcNonce),

            %% bad txn: double-spend = same nonce, diff dst
            user_txn_pay(Src, Dst2, AmountPerTxn, SrcNonce)
        ],
    TxnBundle = blockchain_txn_bundle_v1:new(Txns),

    ?assertMatch(
        {error, {invalid_txns, [{_, invalid_bundled_txns}]}},
        chain_commit(Chain, ConsensusMembers, TxnBundle)
    ),

    %% All balances remain, since all txns were rejected, not just the bad one.
    ?assertEqual(SrcBalance0 , user_balance(Chain, Src)),
    ?assertEqual(Dst1Balance0, user_balance(Chain, Dst1)),
    ?assertEqual(Dst2Balance0, user_balance(Chain, Dst2)),

    ok.

successive_test(Cfg) ->
    %% Test a successive valid bundle payment
    %% A -> B
    %% B -> C
    ConsensusMembers = ?config(consensus_members, Cfg),
    Chain = ?config(chain, Cfg),

    %% A needs a starting balance, so we pick one from the consensus group.
    %% B and C can be arbitrary, since they have no need for a starting balance
    %% - all funds will originate from A.
    {A, _} = user_pick_from_cg(ConsensusMembers),
    B = user_new(),
    C = user_new(),

    A_Balance0 = user_balance(Chain, A),
    B_Balance0 = user_balance(Chain, B),
    C_Balance0 = user_balance(Chain, C),

    %% Expected initial balances:
    ?assertEqual(5000, A_Balance0),
    ?assertEqual(   0, B_Balance0),
    ?assertEqual(   0, C_Balance0),

    AmountAToB = A_Balance0,
    AmountBToC = AmountAToB - 1,
    Txns =
        [
            user_txn_pay(A, B, AmountAToB, 1),
            user_txn_pay(B, C, AmountBToC, 1)
        ],
    TxnBundle = blockchain_txn_bundle_v1:new(Txns),

    ?assertMatch(ok, chain_commit(Chain, ConsensusMembers, TxnBundle)),
    ?assertEqual(A_Balance0 - AmountAToB             , user_balance(Chain, A)),
    ?assertEqual(B_Balance0 + AmountAToB - AmountBToC, user_balance(Chain, B)),
    ?assertEqual(C_Balance0 + AmountBToC             , user_balance(Chain, C)),

    ok.

invalid_successive_test(Cfg) ->
    %% Test a successive invalid bundle payment
    %% A -> B
    %% B -> C <-- this is invalid
    ConsensusMembers = ?config(consensus_members, Cfg),
    Chain = ?config(chain, Cfg),

    %% A needs a starting balance, so we pick one from the consensus group.
    %% B and C can be arbitrary, since they have no need for a starting balance
    %% - all funds will originate from A.
    {A, _} = user_pick_from_cg(ConsensusMembers),
    B = user_new(),
    C = user_new(),

    A_Balance0 = user_balance(Chain, A),
    B_Balance0 = user_balance(Chain, B),
    C_Balance0 = user_balance(Chain, C),

    %% Expected initial balances:
    ?assertEqual(5000, A_Balance0),
    ?assertEqual(   0, B_Balance0),
    ?assertEqual(   0, C_Balance0),

    AmountAToB = A_Balance0,
    AmountBToC = B_Balance0 + AmountAToB + 1,  % overdraw attempt
    Txns =
        [
            user_txn_pay(A, B, AmountAToB, 1),
            user_txn_pay(B, C, AmountBToC, 1)
        ],
    TxnBundle = blockchain_txn_bundle_v1:new(Txns),

    ?assertMatch(
        {error, {invalid_txns, [{_, invalid_bundled_txns}]}},
        chain_commit(Chain, ConsensusMembers, TxnBundle)
    ),
    ?assertEqual(A_Balance0, user_balance(Chain, A)),
    ?assertEqual(B_Balance0, user_balance(Chain, B)),
    ?assertEqual(C_Balance0, user_balance(Chain, C)),

    ok.

single_payer_test(Cfg) ->
    %% Test a bundled payment from single payer
    %% A -> B
    %% A -> C
    ConsensusMembers = ?config(consensus_members, Cfg),
    Chain = ?config(chain, Cfg),

    %% A needs a starting balance, so we pick one from the consensus group.
    %% B and C can be arbitrary, since they have no need for a starting balance
    %% - all funds will originate from A.
    {A, _} = user_pick_from_cg(ConsensusMembers),
    B = user_new(),
    C = user_new(),

    A_Balance0 = user_balance(Chain, A),
    B_Balance0 = user_balance(Chain, B),
    C_Balance0 = user_balance(Chain, C),

    %% Expected initial values:
    ?assertEqual(5000, A_Balance0),
    ?assertEqual(   0, B_Balance0),
    ?assertEqual(   0, C_Balance0),

    AmountAToB = 2000,
    AmountAToC = 3000,
    Txns =
        [
            user_txn_pay(A, B, AmountAToB, 1),
            user_txn_pay(A, C, AmountAToC, 2)
        ],
    TxnBundle = blockchain_txn_bundle_v1:new(Txns),

    ?assertMatch(ok, chain_commit(Chain, ConsensusMembers, TxnBundle)),
    ?assertEqual(A_Balance0 - AmountAToB - AmountAToC, user_balance(Chain, A)),
    ?assertEqual(B_Balance0 + AmountAToB             , user_balance(Chain, B)),
    ?assertEqual(C_Balance0 + AmountAToC             , user_balance(Chain, C)),

    ok.

single_payer_invalid_test(Cfg) ->
    %% Test a bundled payment from single payer
    %% Given:
    %%   N < (K + M)
    %%   A: N
    %%   B: 0
    %% Attempt:
    %%   A -M-> B : OK
    %%   A -K-> C : insufficient funds
    ConsensusMembers = ?config(consensus_members, Cfg),
    Chain = ?config(chain, Cfg),

    %% A needs a starting balance, so we pick one from the consensus group.
    %% B and C can be arbitrary, since they have no need for a starting balance
    %% - all funds will originate from A.
    {A, _} = user_pick_from_cg(ConsensusMembers),
    B = user_new(),
    C = user_new(),

    A_Balance0 = user_balance(Chain, A),
    B_Balance0 = user_balance(Chain, B),
    C_Balance0 = user_balance(Chain, C),

    %% Expected initial values:
    ?assertEqual(5000, A_Balance0),
    ?assertEqual(   0, B_Balance0),
    ?assertEqual(   0, C_Balance0),

    Overage = 1000,
    AmountAToB = 2000,
    AmountAToC = (A_Balance0 - AmountAToB) + Overage,

    % Sanity checks
    ?assert(A_Balance0 >= AmountAToB),
    ?assert(A_Balance0 <  (AmountAToB + AmountAToC)),

    Txns =
        [
            user_txn_pay(A, B, AmountAToB, 1),
            user_txn_pay(A, C, AmountAToC, 2)
        ],
    TxnBundle = blockchain_txn_bundle_v1:new(Txns),

    ?assertMatch(
        {error, {invalid_txns, [{_, invalid_bundled_txns}]}},
        chain_commit(Chain, ConsensusMembers, TxnBundle)
    ),

    %% Because of one invalid txn (A->C), the whole bundle was rejected, so
    %% nothing changed:
    ?assertEqual(A_Balance0, user_balance(Chain, A)),
    ?assertEqual(B_Balance0, user_balance(Chain, B)),
    ?assertEqual(C_Balance0, user_balance(Chain, C)),

    ok.

full_circle_test(Cfg) ->
    %% Test a full-circle transfer of funds:
    %% Given:
    %%   A: NA
    %%   B: NB
    %%   C: NC
    %% Attempt:
    %%   A -(NA      )-> B
    %%   B -(NA+NB   )-> C
    %%   C -(NA+NB+NC)-> A
    %% Expect:
    %%   A: NA + NB + NC
    %%   B: 0
    %%   C: 0
    ConsensusMembers = ?config(consensus_members, Cfg),
    Chain = ?config(chain, Cfg),

    %% A needs a starting balance, so we pick one from the consensus group.
    %% B and C can be arbitrary, since they have no need for a starting balance
    %% - all funds will originate from A.
    {A, _} = user_pick_from_cg(ConsensusMembers),
    B = user_new(),
    C = user_new(),

    A_Balance0 = user_balance(Chain, A),
    B_Balance0 = user_balance(Chain, B),
    C_Balance0 = user_balance(Chain, C),

    %% Expected initial values:
    ?assertEqual(5000, A_Balance0),
    ?assertEqual(   0, B_Balance0),
    ?assertEqual(   0, C_Balance0),

    AmountAToB = A_Balance0,
    AmountBToC = A_Balance0 + B_Balance0,
    AmountCToA = A_Balance0 + B_Balance0 + C_Balance0,
    BalanceExpectedA = AmountCToA,
    BalanceExpectedB = 0,
    BalanceExpectedC = 0,

    Txns =
        [
            user_txn_pay(A, B, AmountAToB, 1),
            user_txn_pay(B, C, AmountBToC, 1),
            user_txn_pay(C, A, AmountCToA, 1)
        ],
    TxnBundle = blockchain_txn_bundle_v1:new(Txns),

    ?assertMatch(ok, chain_commit(Chain, ConsensusMembers, TxnBundle)),
    ?assertEqual(BalanceExpectedA, user_balance(Chain, A)),
    ?assertEqual(BalanceExpectedB, user_balance(Chain, B)),
    ?assertEqual(BalanceExpectedC, user_balance(Chain, C)),

    ok.

add_assert_test(Cfg) ->
    %% FIXME Doesn' work here or in miner. Error: dc_entry_not_found for owner addr.
    %% Test add + assert in a bundled txn
    %% A -> [add_gateway, assert_location]

    ConsensusMembers = ?config(consensus_members, Cfg),
    Chain = ?config(chain, Cfg),

    Owner = user_from_swarm(),
    Gateway = user_new(),
    ct:pal(">>> Addr of Owner: ~p", [user_addr(Owner)]),
    ct:pal(">>> Addr of Gateway: ~p", [user_addr(Gateway)]),

    LocationIndex = 631210968910285823,
    Txns =
        [
            user_txn_gateway_add(Owner, Gateway),
            user_txn_assert_location(Owner, Gateway, LocationIndex, 1)
        ],
    TxnBundle = blockchain_txn_bundle_v1:new(Txns),
    ?assertMatch(ok, chain_commit(Chain, ConsensusMembers, TxnBundle)),

    %% Get active gateways
    ActiveGateways = chain_get_active_gateways(Chain),

    %% Check that the gateway got added
    9 = maps:size(ActiveGateways),

    %% Check that it has the correct location
    AddedGw = maps:get(user_addr(Gateway), ActiveGateways),
    GwLoc = blockchain_ledger_gateway_v2:location(AddedGw),
    ?assertEqual(GwLoc, LocationIndex),

    ok.

invalid_add_assert_test(Cfg) ->
    %% Test add + assert in a bundled txn
    %% A -> [add_gateway, assert_location]
    %%
    %% FIXME It's unclear whether this passes for the right reasons, since
    %% valid gateway addition fails in add_assert_test. We should probably
    %% compabine these two test cases and first ensure that adding works then
    %% try wrong order and ensure it's rejected, then perhaps try another valid
    %% add.

    ConsensusMembers = ?config(consensus_members, Cfg),
    Chain = ?config(chain, Cfg),

    Owner = user_from_swarm(),
    Gateway = user_new(),

    LocationIndex = 631210968910285823,
    Txns =
        [
            user_txn_gateway_add(Owner, Gateway),
            user_txn_assert_location(Owner, Gateway, LocationIndex, 1)
        ],
    TxnBundle = blockchain_txn_bundle_v1:new(Txns),
    NumActiveGateways0 = maps:size(chain_get_active_gateways(Chain)),
    ?assertMatch(
        {error, {invalid_txns, [{_, invalid_bundled_txns}]}},
        chain_commit(Chain, ConsensusMembers, TxnBundle)
    ),

    %% Check that the gateway did not get added
    ?assertEqual(
        NumActiveGateways0,
        maps:size(chain_get_active_gateways(Chain))
    ),

    ok.

single_txn_bundle_test(Cfg) ->
    ConsensusMembers = ?config(consensus_members, Cfg),
    Chain = ?config(chain, Cfg),

    %% Src needs a starting balance, so we pick one from the consensus group.
    %% Dst has no need for a starting balance, so we use an arbitrary address.
    {Src, _} = user_pick_from_cg(ConsensusMembers),
    Dst = user_new(),

    SrcBalance0 = user_balance(Chain, Src),
    DstBalance0 = user_balance(Chain, Dst),

    %% Expected initial balances:
    ?assertEqual(5000, SrcBalance0),
    ?assertEqual(   0, DstBalance0),

    Amount = 1000,
    Txns = [user_txn_pay(Src, Dst, Amount, 1)],
    TxnBundle = blockchain_txn_bundle_v1:new(Txns),

    %% The bundle is invalid since it does not contain atleast two txns in it
    ?assertMatch(
        {error, {invalid_txns, [{_, invalid_min_bundle_size}]}},
        chain_commit(Chain, ConsensusMembers, TxnBundle)
    ),

    %% Sanity check that balances haven't changed:
    ?assertEqual(SrcBalance0, user_balance(Chain, Src)),
    ?assertEqual(DstBalance0, user_balance(Chain, Dst)),

    ok.

bundleception_test(Cfg) ->
    ConsensusMembers0 = ?config(consensus_members, Cfg),
    Chain = ?config(chain, Cfg),
    {Src, ConsensusMembers1} = user_pick_from_cg(ConsensusMembers0),
    {Dst, _ConsensusMembers} = user_pick_from_cg(ConsensusMembers1),
    SrcBalance0 = user_balance(Chain, Src),
    DstBalance0 = user_balance(Chain, Dst),

    ?assertEqual(5000, SrcBalance0),
    ?assertEqual(5000, DstBalance0),

    AmountPerTxn = 1000,
    TxnBundle1 =
        blockchain_txn_bundle_v1:new(
            [
                user_txn_pay(Src, Dst, AmountPerTxn, 1),
                user_txn_pay(Src, Dst, AmountPerTxn, 2)
            ]
        ),
    TxnBundle2 =
        blockchain_txn_bundle_v1:new(
            [
                user_txn_pay(Src, Dst, AmountPerTxn, 3),
                user_txn_pay(Src, Dst, AmountPerTxn, 4)
            ]
        ),
    TxnBundleCeption = blockchain_txn_bundle_v1:new([TxnBundle1, TxnBundle2]),

    ?assertMatch(
        {error, {invalid_txns, [{_, invalid_bundleception}]}},
        chain_commit(Chain, ConsensusMembers0, TxnBundleCeption)
    ),

    ?assertEqual(SrcBalance0, user_balance(Chain, Src)),
    ?assertEqual(DstBalance0, user_balance(Chain, Dst)),

    ok.

%% Helpers --------------------------------------------------------------------

-type user() :: % Should be opaque when moved to a module.
    {Addr :: binary(), SigFun :: fun((binary()) -> binary())}.

-type consensus_member() ::
    {
        Addr :: binary(),
        {
            Pub  :: libp2p_crypto:pubkey(),
            Priv :: libp2p_crypto:privkey(),
            Sign :: fun((binary()) -> binary())
        }
    }.

-type consensus_group() ::
    [consensus_member()].

-spec user_new() -> user().
user_new() ->
    #{public := Pub, secret := Priv} = libp2p_crypto:generate_keys(ecc_compact),
    Addr = libp2p_crypto:pubkey_to_bin(Pub),
    SigFun = libp2p_crypto:mk_sig_fun(Priv),
    ?assert(is_binary(Addr)),
    ?assert(is_function(SigFun)),
    {Addr, SigFun}.

user_from_swarm() ->
    {ok, Pub, SigFun, _ECDHFun} = blockchain_swarm:keys(),
    ?assert(is_function(SigFun)),
    Addr = libp2p_crypto:pubkey_to_bin(Pub),
    {Addr, SigFun}.

-spec user_addr(user()) -> binary().
user_addr({Addr, SigFun}) ->
    ?assert(is_binary(Addr)),
    ?assert(is_function(SigFun)),
    Addr.

-spec user_sig_fun(user()) -> fun((binary()) -> binary()).
user_sig_fun({Addr, SigFun}) ->
    ?assert(is_binary(Addr)),
    ?assert(is_function(SigFun)),
    SigFun.

-spec user_pick_from_cg(consensus_group()) -> {user(), consensus_group()}.
user_pick_from_cg([{Addr, {_, _, SigFun}} | CG]) ->
    ?assert(is_binary(Addr)),
    ?assert(is_function(SigFun)),
    {{Addr, SigFun}, CG}.

-spec user_balance(blockchain:blockchain(), user()) ->
    non_neg_integer().
user_balance(Chain, User) ->
    Addr = user_addr(User),
    Ledger = blockchain:ledger(Chain),
    case blockchain_ledger_v1:find_entry(Addr, Ledger) of
        {error, address_entry_not_found} ->
            0;
        {ok, Entry} ->
            blockchain_ledger_entry_v1:balance(Entry)
    end.

-spec user_txn_pay(user(), user(), non_neg_integer(), non_neg_integer()) ->
    Txn :: term(). % TODO Txn type
user_txn_pay(Src, Dst, Amount, Nonce) ->
    Txn = blockchain_txn_payment_v1:new(user_addr(Src), user_addr(Dst), Amount, Nonce),
    blockchain_txn_payment_v1:sign(Txn, user_sig_fun(Src)).

user_txn_gateway_add(Owner, Gateway) ->
    Tx1 = blockchain_txn_add_gateway_v1:new(user_addr(Owner), user_addr(Gateway)),
    Tx2 = blockchain_txn_add_gateway_v1:sign(Tx1, user_sig_fun(Owner)),
    Tx3 = blockchain_txn_add_gateway_v1:sign_request(Tx2, user_sig_fun(Gateway)),
    Tx3.

user_txn_assert_location(Owner, Gateway, Index, Nonce) ->
    Tx1 = blockchain_txn_assert_location_v1:new(user_addr(Gateway), user_addr(Owner), Index, Nonce),
    Tx2 = blockchain_txn_assert_location_v1:sign_request(Tx1, user_sig_fun(Gateway)),
    Tx3 = blockchain_txn_assert_location_v1:sign(Tx2, user_sig_fun(Owner)),
    Tx3.

-spec chain_commit(blockchain:blockchain(), [{_, {_, _, _}}], _) ->
    ok | {error, _}.
chain_commit(Chain, ConsensusMembers, Txn) ->
    case test_utils:create_block(ConsensusMembers, [Txn]) of
        {ok, Block} ->
            {ok, Height0} = blockchain:height(Chain),
            ok = blockchain:add_block(Block, Chain),
            {ok, Height1} = blockchain:height(Chain),
            ?assertEqual(1 + Height0, Height1),
            ok;
        {error, _}=Err ->
            Err
    end.

chain_get_active_gateways(Chain) ->
    Ledger = blockchain:ledger(Chain),
    blockchain_ledger_v1:active_gateways(Ledger).
