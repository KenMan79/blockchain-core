%%%-------------------------------------------------------------------
%% @doc
%% == Blockchain Transaction Assert Location V2 ==
%% @end
%%%-------------------------------------------------------------------
-module(blockchain_txn_assert_location_v2).
-include_lib("common_test/include/ct.hrl").

-behavior(blockchain_txn).

-behavior(blockchain_json).
-include("blockchain_json.hrl").
-include("blockchain_txn_fees.hrl").
-include_lib("helium_proto/include/blockchain_txn_assert_location_v2_pb.hrl").
-include("blockchain_vars.hrl").
-include("blockchain_utils.hrl").

-export([
    new/4, new/5,
    hash/1,
    gateway/1,
    owner/1,
    payer/1,
    location/1, location/2,
    gain/1, gain/2,
    elevation/1, elevation/2,
    owner_signature/1,
    payer_signature/1,
    nonce/1,
    staking_fee/1, staking_fee/2,
    fee/1, fee/2,
    sign_payer/2,
    sign/2,
    is_valid_owner/1,
    is_valid_location/2,
    is_valid_payer/1,
    is_well_formed/1,
    is_absorbable/2,
    is_valid/2,
    absorb/2,
    calculate_fee/2, calculate_fee/5, calculate_staking_fee/2, calculate_staking_fee/5,
    print/1,
    to_json/2
]).

-ifdef(EQC).
-include_lib("eqc/include/eqc.hrl").
-export([gen/1]).
-endif.


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-type location() :: h3:h3index().
-type txn_assert_location() :: #blockchain_txn_assert_location_v2_pb{}.
-export_type([txn_assert_location/0]).

-spec new(Gateway :: libp2p_crypto:pubkey_bin(),
          Owner :: libp2p_crypto:pubkey_bin(),
          Location :: location(),
          Nonce :: non_neg_integer()) -> txn_assert_location().
new(Gateway, Owner, Location, Nonce) ->
    #blockchain_txn_assert_location_v2_pb{
        gateway=Gateway,
        owner=Owner,
        payer = <<>>,
        location=h3:to_string(Location),
        owner_signature = <<>>,
        payer_signature = <<>>,
        nonce=Nonce,
        gain=?DEFAULT_GAIN,
        elevation=?DEFAULT_ELEVATION,
        staking_fee=?LEGACY_STAKING_FEE,
        fee=?LEGACY_TXN_FEE
    }.

-spec new(Gateway :: libp2p_crypto:pubkey_bin(),
          Owner :: libp2p_crypto:pubkey_bin(),
          Payer :: libp2p_crypto:pubkey_bin(),
          Location :: location(),
          Nonce :: non_neg_integer()) -> txn_assert_location().
new(Gateway, Owner, Payer, Location, Nonce) ->
    #blockchain_txn_assert_location_v2_pb{
        gateway=Gateway,
        owner=Owner,
        payer = Payer,
        location=h3:to_string(Location),
        owner_signature = <<>>,
        payer_signature = <<>>,
        nonce=Nonce,
        gain=?DEFAULT_GAIN,
        elevation=?DEFAULT_ELEVATION,
        staking_fee=?LEGACY_STAKING_FEE,
        fee=?LEGACY_TXN_FEE
    }.

-spec hash(txn_assert_location()) -> blockchain_txn:hash().
hash(Txn) ->
    BaseTxn = Txn#blockchain_txn_assert_location_v2_pb{owner_signature = <<>>},
    EncodedTxn = blockchain_txn_assert_location_v2_pb:encode_msg(BaseTxn),
    crypto:hash(sha256, EncodedTxn).

-spec gateway(txn_assert_location()) -> libp2p_crypto:pubkey_bin().
gateway(Txn) ->
    Txn#blockchain_txn_assert_location_v2_pb.gateway.

-spec owner(txn_assert_location()) -> libp2p_crypto:pubkey_bin().
owner(Txn) ->
    Txn#blockchain_txn_assert_location_v2_pb.owner.

-spec payer(txn_assert_location()) -> libp2p_crypto:pubkey_bin() | <<>> | undefined.
payer(Txn) ->
    Txn#blockchain_txn_assert_location_v2_pb.payer.

-spec location(txn_assert_location()) -> location().
location(Txn) ->
    h3:from_string(Txn#blockchain_txn_assert_location_v2_pb.location).

-spec location(Location :: h3:index(), Txn :: txn_assert_location()) -> location().
location(Location, Txn) ->
    Txn#blockchain_txn_assert_location_v2_pb{location = h3:to_string(Location)}.

-spec gain(Txn :: txn_assert_location()) -> integer().
gain(Txn) ->
    Txn#blockchain_txn_assert_location_v2_pb.gain.

-spec gain(Txn :: txn_assert_location(), Gain :: integer()) -> txn_assert_location().
gain(Txn, Gain) ->
    Txn#blockchain_txn_assert_location_v2_pb{gain = Gain}.

-spec elevation(txn_assert_location()) -> integer().
elevation(Txn) ->
    Txn#blockchain_txn_assert_location_v2_pb.elevation.

-spec elevation(Txn :: txn_assert_location(), Elevation :: integer()) -> txn_assert_location().
elevation(Txn, Elevation) ->
    Txn#blockchain_txn_assert_location_v2_pb{elevation = Elevation}.

-spec owner_signature(txn_assert_location()) -> binary().
owner_signature(Txn) ->
    Txn#blockchain_txn_assert_location_v2_pb.owner_signature.

-spec payer_signature(txn_assert_location()) -> binary().
payer_signature(Txn) ->
    Txn#blockchain_txn_assert_location_v2_pb.payer_signature.

-spec nonce(txn_assert_location()) -> non_neg_integer().
nonce(Txn) ->
    Txn#blockchain_txn_assert_location_v2_pb.nonce.

-spec staking_fee(txn_assert_location()) -> non_neg_integer().
staking_fee(Txn) ->
    Txn#blockchain_txn_assert_location_v2_pb.staking_fee.

-spec staking_fee(txn_assert_location(), non_neg_integer()) -> txn_assert_location().
staking_fee(Txn, Fee) ->
    Txn#blockchain_txn_assert_location_v2_pb{staking_fee=Fee}.

-spec fee(txn_assert_location()) -> non_neg_integer().
fee(Txn) ->
    Txn#blockchain_txn_assert_location_v2_pb.fee.

-spec fee(txn_assert_location(), non_neg_integer()) -> txn_assert_location().
fee(Txn, Fee) ->
    Txn#blockchain_txn_assert_location_v2_pb{fee=Fee}.

%%--------------------------------------------------------------------
%% @doc
%% Calculate the txn fee
%% Returned value is txn_byte_size / 24
%% @end
%%--------------------------------------------------------------------
-spec calculate_fee(txn_assert_location(), blockchain:blockchain()) -> non_neg_integer().
calculate_fee(Txn, Chain) ->
    ?calculate_fee_prep(Txn, Chain).

-spec calculate_fee(txn_assert_location(), blockchain_ledger_v1:ledger(), pos_integer(), pos_integer(), boolean()) -> non_neg_integer().
calculate_fee(_Txn, _Ledger, _DCPayloadSize, _TxnFeeMultiplier, false) ->
    ?LEGACY_TXN_FEE;
calculate_fee(Txn, Ledger, DCPayloadSize, TxnFeeMultiplier, true) ->
    case Txn#blockchain_txn_assert_location_v2_pb.payer of
        Payer when Payer == undefined; Payer == <<>> ->
          %% no payer signature if there's no payer
          ?calculate_fee(Txn#blockchain_txn_assert_location_v2_pb{fee=0, staking_fee=0,
                                                       owner_signature= <<0:512>>,
                                                       payer_signature= <<>>}, Ledger, DCPayloadSize, TxnFeeMultiplier);
        _ ->
          ?calculate_fee(Txn#blockchain_txn_assert_location_v2_pb{fee=0, staking_fee=0,
                                                       owner_signature= <<0:512>>,
                                                       payer_signature= <<0:512>>}, Ledger, DCPayloadSize, TxnFeeMultiplier)
    end.

%%--------------------------------------------------------------------
%% @doc
%% Calculate the staking fee using the price oracles
%% returns the fee in DC
%% @end
%%--------------------------------------------------------------------
-spec calculate_staking_fee(txn_assert_location(), blockchain:blockchain()) -> non_neg_integer().
calculate_staking_fee(Txn, Chain) ->
    Ledger = blockchain:ledger(Chain),
    Fee = blockchain_ledger_v1:staking_fee_txn_assert_location_v1(Ledger),
    calculate_staking_fee(Txn, Ledger, Fee, [], blockchain_ledger_v1:txn_fees_active(Ledger)).

-spec calculate_staking_fee(txn_assert_location(), blockchain_ledger_v1:ledger(), non_neg_integer(), [{atom(), non_neg_integer()}], boolean()) -> non_neg_integer().
calculate_staking_fee(_Txn, _Ledger, _Fee, _ExtraData, false) ->
    ?LEGACY_STAKING_FEE;
calculate_staking_fee(_Txn, ignore_ledger, Fee, _ExtraData, true) ->
    %% For testing
    Fee;
calculate_staking_fee(Txn, Ledger, Fee, _ExtraData, true) ->
    %% fee is active
    %% 0 staking_fee if the location hasn't actually changed
    %% it's possible that the only change are gain/elevation
    case is_new_location(Txn, Ledger) of
        true -> Fee;
        false -> 0
    end.

-spec sign_payer(txn_assert_location(), fun()) -> txn_assert_location().
sign_payer(Txn, SigFun) ->
    BaseTxn = Txn#blockchain_txn_assert_location_v2_pb{owner_signature= <<>>,
                                                       payer_signature= <<>>},
    EncodedTxn = blockchain_txn_assert_location_v2_pb:encode_msg(BaseTxn),
    Txn#blockchain_txn_assert_location_v2_pb{payer_signature=SigFun(EncodedTxn)}.

-spec sign(Txn :: txn_assert_location(),
           SigFun :: libp2p_crypto:sig_fun()) -> txn_assert_location().
sign(Txn, SigFun) ->
    BaseTxn = Txn#blockchain_txn_assert_location_v2_pb{owner_signature= <<>>,
                                                       payer_signature= <<>>},
    BinTxn = blockchain_txn_assert_location_v2_pb:encode_msg(BaseTxn),
    Txn#blockchain_txn_assert_location_v2_pb{owner_signature=SigFun(BinTxn)}.

-spec is_valid_owner(txn_assert_location()) -> boolean().
is_valid_owner(#blockchain_txn_assert_location_v2_pb{owner=PubKeyBin,
                                                     owner_signature=Signature}=Txn) ->
    BaseTxn = Txn#blockchain_txn_assert_location_v2_pb{owner_signature= <<>>,
                                                       payer_signature= <<>>},
    EncodedTxn = blockchain_txn_assert_location_v2_pb:encode_msg(BaseTxn),
    PubKey = libp2p_crypto:bin_to_pubkey(PubKeyBin),
    libp2p_crypto:verify(EncodedTxn, Signature, PubKey).

-spec is_valid_location(txn_assert_location(), pos_integer()) -> boolean().
is_valid_location(#blockchain_txn_assert_location_v2_pb{location=Location}, MinH3Res) ->
    h3:get_resolution(h3:from_string(Location)) >= MinH3Res.

-spec is_valid_gain(txn_assert_location(), pos_integer(), pos_integer()) -> boolean().
is_valid_gain(#blockchain_txn_assert_location_v2_pb{gain=Gain}, MinGain, MaxGain) ->
    not (Gain < MinGain orelse Gain > MaxGain).

-spec is_valid_payer(txn_assert_location()) -> boolean().
is_valid_payer(#blockchain_txn_assert_location_v2_pb{payer=undefined}) ->
    %% no payer
    true;
is_valid_payer(#blockchain_txn_assert_location_v2_pb{payer= <<>>,
                                                     payer_signature= <<>>}) ->
    %% empty payer, empty signature
    true;
is_valid_payer(#blockchain_txn_assert_location_v2_pb{payer=PubKeyBin,
                                                     payer_signature=Signature}=Txn) ->

    BaseTxn = Txn#blockchain_txn_assert_location_v2_pb{owner_signature= <<>>,
                                                       payer_signature= <<>>},
    EncodedTxn = blockchain_txn_assert_location_v2_pb:encode_msg(BaseTxn),
    PubKey = libp2p_crypto:bin_to_pubkey(PubKeyBin),
    libp2p_crypto:verify(EncodedTxn, Signature, PubKey).

is_well_formed(Txn) ->
    blockchain_txn:validate_fields([{{gateway, gateway(Txn)}, {address, libp2p}},
                                    {{owner, owner(Txn)}, {address, libp2p}},
                                    {{location, Txn#blockchain_txn_assert_location_v2_pb.location}, is_h3},
                                    {{elevation, elevation(Txn)}, {is_integer, -2147483648}}] ++
                                   [{{payer, payer(Txn)}, {address, libp2p}} || byte_size(payer(Txn)) > 0]).

is_absorbable(Txn, Chain) ->
    Ledger = blockchain:ledger(Chain),
    Gateway = ?MODULE:gateway(Txn),
    case blockchain_gateway_cache:get(Gateway, Ledger) of
        {error, _} ->
            {error, {unknown_gateway, {assert_location_v2, Gateway, Ledger}}};
        {ok, GwInfo} ->
            LedgerNonce = blockchain_ledger_gateway_v2:nonce(GwInfo),
            case nonce(Txn) == LedgerNonce + 1 of
                false ->
                    {error, {bad_nonce, {assert_location_v2, nonce(Txn), LedgerNonce}}};
                true ->
                    true
            end
    end.

-spec is_valid(txn_assert_location(), blockchain:blockchain()) -> ok | {error, any()}.
is_valid(Txn, Chain) ->
    Gain = ?MODULE:gain(Txn),
    Ledger = blockchain:ledger(Chain),

    case blockchain:config(?assert_loc_txn_version, Ledger) of
        {ok, V} when V >= 2 ->
            case blockchain:config(?min_antenna_gain, Ledger) of
                {ok, MinGain} ->
                    case blockchain:config(?max_antenna_gain, Ledger) of
                        {ok, MaxGain} ->
                            case is_valid_gain(Txn, MinGain, MaxGain) of
                                false ->
                                    {error, {invalid_assert_loc_txn_v2, {invalid_antenna_gain, Gain, MinGain, MaxGain}}};
                                true ->
                                    do_is_valid_checks(Txn, Chain)
                            end;
                        _ ->
                            {error, {invalid_assert_loc_txn_v2, max_antenna_gain_not_set}}
                    end;
                _ ->
                    {error, {invalid_assert_loc_txn_v2, min_antenna_gain_not_set}}
            end;
        _ ->
            {error, {invalid_assert_loc_txn_v2, insufficient_assert_loc_txn_version}}
    end.


-spec do_is_valid_checks(Txn :: txn_assert_location(),
                         Chain :: blockchain:blockchain()) -> ok | {error, any()}.
do_is_valid_checks(Txn, Chain) ->
    Ledger = blockchain:ledger(Chain),
    case {?MODULE:is_valid_owner(Txn),
          ?MODULE:is_valid_payer(Txn)} of
        {false, _} ->
            {error, {bad_owner_signature, {assert_location_v2, owner(Txn)}}};
        {_, false} ->
            {error, {bad_payer_signature, {assert_location_v2, payer(Txn)}}};
        {true, true} ->
            AreFeesEnabled = blockchain_ledger_v1:txn_fees_active(Ledger),
            StakingFee = ?MODULE:staking_fee(Txn),
            ExpectedStakingFee = ?MODULE:calculate_staking_fee(Txn, Chain),
            TxnFee = ?MODULE:fee(Txn),
            ExpectedTxnFee = calculate_fee(Txn, Chain),
            case {(ExpectedTxnFee =< TxnFee orelse not AreFeesEnabled), ExpectedStakingFee == StakingFee} of
                {false,_} ->
                    {error, {wrong_txn_fee, {assert_location_v2, ExpectedTxnFee, TxnFee}}};
                {_,false} ->
                    {error, {wrong_staking_fee, {assert_location_v2, ExpectedStakingFee, StakingFee}}};
                {true, true} ->
                    do_remaining_checks(Txn, TxnFee + StakingFee, Ledger)
            end
    end.

-spec is_new_location(Txn :: txn_assert_location(), Ledger :: blockchain_ledger_v1:ledger()) -> boolean().
is_new_location(Txn, Ledger) ->
    GwPubkeyBin = ?MODULE:gateway(Txn),
    NewLoc = ?MODULE:location(Txn),
    {ok, Gw} = blockchain_ledger_v1:find_gateway_info(GwPubkeyBin, Ledger),
    ExistingLoc = blockchain_ledger_gateway_v2:location(Gw),
    NewLoc /= ExistingLoc.

-spec do_remaining_checks(Txn :: txn_assert_location(),
                          TotalFee :: non_neg_integer(),
                          Ledger :: blockchain_ledger_v1:ledger()) -> ok | {error, any()}.
do_remaining_checks(Txn, TotalFee, Ledger) ->
    Owner = ?MODULE:owner(Txn),
    Payer = ?MODULE:payer(Txn),
    AreFeesEnabled = blockchain_ledger_v1:txn_fees_active(Ledger),
    ActualPayer = case Payer == undefined orelse Payer == <<>> of
                      true -> Owner;
                      false -> Payer
                  end,
    case blockchain_ledger_v1:check_dc_or_hnt_balance(ActualPayer, TotalFee, Ledger, AreFeesEnabled) of
        {error, _}=Error ->
            Error;
        ok ->
            Gateway = ?MODULE:gateway(Txn),
            case blockchain_gateway_cache:get(Gateway, Ledger) of
                {error, _} ->
                    {error, {unknown_gateway, {assert_location_v2, Gateway, Ledger}}};
                {ok, GwInfo} ->
                    GwOwner = blockchain_ledger_gateway_v2:owner_address(GwInfo),
                    case Owner == GwOwner of
                        false ->
                            {error, {bad_owner, {assert_location_v2, Owner, GwOwner}}};
                        true ->
                            {ok, MinAssertH3Res} = blockchain:config(?min_assert_h3_res, Ledger),
                            Location = ?MODULE:location(Txn),
                            case ?MODULE:is_valid_location(Txn, MinAssertH3Res) of
                                false ->
                                    {error, {insufficient_assert_res, {assert_location_v2, Location, Gateway}}};
                                true ->
                                    ok
                            end
                    end
            end
    end.

%%--------------------------------------------------------------------
%% @doc
%% @end
%%--------------------------------------------------------------------
-spec absorb(txn_assert_location(), blockchain:blockchain()) -> ok | {error, atom()} | {error, {atom(), any()}}.
absorb(Txn, Chain) ->
    Ledger = blockchain:ledger(Chain),
    AreFeesEnabled = blockchain_ledger_v1:txn_fees_active(Ledger),
    Gateway = ?MODULE:gateway(Txn),
    Owner = ?MODULE:owner(Txn),
    Location = ?MODULE:location(Txn),
    Nonce = ?MODULE:nonce(Txn),
    StakingFee = ?MODULE:staking_fee(Txn),
    Fee = ?MODULE:fee(Txn),
    Payer = ?MODULE:payer(Txn),
    Gain = ?MODULE:gain(Txn),
    Elevation = ?MODULE:elevation(Txn),
    ActualPayer = case Payer == undefined orelse Payer == <<>> of
        true -> Owner;
        false -> Payer
    end,

    {ok, OldGw} = blockchain_gateway_cache:get(Gateway, Ledger, false),
    %% NOTE: It is assumed that the staking_fee is set to 0 at user level for assert_location_v2 transactions
    %% which only update gain/elevation
    case blockchain_ledger_v1:debit_fee(ActualPayer, Fee + StakingFee, Ledger, AreFeesEnabled) of
        {error, _Reason}=Error ->
            Error;
        ok ->
            blockchain_ledger_v1:add_gateway_location(Gateway, Location, Nonce, Ledger),
            blockchain_ledger_v1:add_gateway_gain(Gateway, Gain, Nonce, Ledger),
            blockchain_ledger_v1:add_gateway_elevation(Gateway, Elevation, Nonce, Ledger),
            maybe_alter_hex(OldGw, Gateway, Location, Ledger),
            maybe_update_neighbors(Gateway, Ledger)
    end.

-spec maybe_update_neighbors(Gateway :: libp2p_crypto:pubkey_bin(),
                             Ledger :: blockchain_ledger_v1:ledger()) -> ok.
maybe_update_neighbors(Gateway, Ledger) ->
    case blockchain:config(?poc_version, Ledger) of
        {ok, V} when V > 3 ->
            %% don't update neighbours anymore
            ok;
        _ ->
            %% TODO gc this nonsense in some deterministic way
            Gateways = blockchain_ledger_v1:active_gateways(Ledger),
            Neighbors = blockchain_poc_path:neighbors(Gateway, Gateways, Ledger),
            {ok, Gw} = blockchain_gateway_cache:get(Gateway, Ledger, false),
            ok = blockchain_ledger_v1:fixup_neighbors(Gateway, Gateways, Neighbors, Ledger),
            Gw1 = blockchain_ledger_gateway_v2:neighbors(Neighbors, Gw),
            ok = blockchain_ledger_v1:update_gateway(Gw1, Gateway, Ledger)
    end.

-spec maybe_alter_hex(OldGw :: blockchain_ledger_gateway_v2:gateway(),
                      Gateway :: libp2p_crypto:pubkey_bin(),
                      Location :: h3:index(),
                      Ledger :: blockchain_ledger_v1:ledger()) -> ok.
maybe_alter_hex(OldGw, Gateway, Location, Ledger) ->
    %% hex index update code needs to be unconditional and hard-coded
    %% until we have chain var update hook
    %% {ok, Res} = blockchain:config(?poc_target_hex_parent_res, Ledger),
    Res = 5,
    OldLoc = blockchain_ledger_gateway_v2:location(OldGw),
    OldHex = case OldLoc of
                 undefined ->
                     undefined;
                 _ ->
                     h3:parent(OldLoc, Res)
             end,

    Hex = h3:parent(Location, Res),

    case {OldLoc, Location, Hex} of
        {undefined, New, H} ->
            %% no previous location

            %% add new hex
            blockchain_ledger_v1:add_to_hex(H, Gateway, Ledger),
            %% add new location of this gateway to h3dex
            blockchain_ledger_v1:add_gw_to_hex(New, Gateway, Ledger);
        {Old, Old, _H} ->
            %% why even check this, same loc as old loc
            ok;
        {Old, New, H} when H == OldHex ->
            %% moved within the same Hex

            %% remove old location of this gateway from h3dex
            blockchain_ledger_v1:remove_gw_from_hex(Old, Gateway, Ledger),

            %% add new location of this gateway to h3dex
            blockchain_ledger_v1:add_gw_to_hex(New, Gateway, Ledger);
        {Old, New, H} ->
            %% moved to a different hex

            %% remove this hex
            blockchain_ledger_v1:remove_from_hex(OldHex, Gateway, Ledger),
            %% add new hex
            blockchain_ledger_v1:add_to_hex(H, Gateway, Ledger),

            %% remove old location of this gateway from h3dex
            blockchain_ledger_v1:remove_gw_from_hex(Old, Gateway, Ledger),
            %% add new location of this gateway to h3dex
            blockchain_ledger_v1:add_gw_to_hex(New, Gateway, Ledger)
    end.

-spec print(txn_assert_location()) -> iodata().
print(undefined) -> <<"type=assert_location, undefined">>;
print(#blockchain_txn_assert_location_v2_pb{
        gateway = Gateway, owner = Owner, payer = Payer,
        location = Loc, gain = Gain, elevation = Elevation,
        owner_signature = OS, payer_signature = PS, nonce = Nonce,
        staking_fee = StakingFee, fee = Fee}) ->
    io_lib:format("type=assert_location, gateway=~p, owner=~p, payer=~p, location=~p, owner_signature=~p, payer_signature=~p, nonce=~p, gain=~p, elevation=~p, staking_fee=~p, fee=~p", [?TO_ANIMAL_NAME(Gateway), ?TO_B58(Owner), ?TO_B58(Payer), Loc, OS, PS, Nonce, Gain, Elevation, StakingFee, Fee]).

-spec to_json(txn_assert_location(), blockchain_json:opts()) -> blockchain_json:json_object().
to_json(Txn, _Opts) ->
    #{
      type => <<"assert_location_v2">>,
      hash => ?BIN_TO_B64(hash(Txn)),
      gateway => ?BIN_TO_B58(gateway(Txn)),
      owner => ?BIN_TO_B58(owner(Txn)),
      payer => ?MAYBE_B58(payer(Txn)),
      location => ?MAYBE_H3(location(Txn)),
      nonce => nonce(Txn),
      staking_fee => staking_fee(Txn),
      fee => fee(Txn),
      gain => gain(Txn),
      elevation => elevation(Txn)
     }.

%% ------------------------------------------------------------------
%% Internal Function Definitions
%% ------------------------------------------------------------------

%% ------------------------------------------------------------------
%% EUNIT Tests
%% ------------------------------------------------------------------
-ifdef(TEST).

-define(TEST_LOCATION, 631210968840687103).

new() ->
    #blockchain_txn_assert_location_v2_pb{
       gateway= <<"gateway_address">>,
       owner= <<"owner_address">>,
       payer= <<>>,
       owner_signature= <<>>,
       payer_signature= <<>>,
       location= h3:to_string(?TEST_LOCATION),
       nonce = 1,
       staking_fee = ?LEGACY_STAKING_FEE,
       fee = ?LEGACY_TXN_FEE,
       gain = ?DEFAULT_GAIN,
       elevation = ?DEFAULT_ELEVATION
      }.

invalid_new() ->
    #blockchain_txn_assert_location_v2_pb{
       gateway= <<"gateway_address">>,
       owner= <<"owner_address">>,
       owner_signature= << >>,
       location= h3:to_string(599685771850416127),
       nonce = 1,
       staking_fee = ?LEGACY_STAKING_FEE,
       fee = ?LEGACY_TXN_FEE
      }.

missing_payer_signature_new() ->
    #{public := PubKey, secret := _PrivKey} = libp2p_crypto:generate_keys(ecc_compact),
    #blockchain_txn_assert_location_v2_pb{
       gateway= <<"gateway_address">>,
       owner= <<"owner_address">>,
       payer= libp2p_crypto:pubkey_to_bin(PubKey),
       payer_signature = <<>>,
       owner_signature= << >>,
       location= h3:to_string(599685771850416127),
       nonce = 1,
       staking_fee = ?LEGACY_STAKING_FEE,
       fee = ?LEGACY_TXN_FEE
      }.

new_test() ->
    Tx = new(),
    ?assertEqual(Tx, new(<<"gateway_address">>, <<"owner_address">>, ?TEST_LOCATION, 1)).

location_test() ->
    Tx = new(),
    ?assertEqual(?TEST_LOCATION, location(Tx)).

nonce_test() ->
    Tx = new(),
    ?assertEqual(1, nonce(Tx)).

staking_fee_test() ->
    Tx = new(),
    ?assertEqual(?LEGACY_STAKING_FEE, staking_fee(Tx)).

fee_test() ->
    Tx = new(),
    ?assertEqual(?LEGACY_TXN_FEE, fee(Tx)).

owner_test() ->
    Tx = new(),
    ?assertEqual(<<"owner_address">>, owner(Tx)).

gateway_test() ->
    Tx = new(),
    ?assertEqual(<<"gateway_address">>, gateway(Tx)).

payer_test() ->
    Tx = new(),
    ?assertEqual(<<>>, payer(Tx)).

owner_signature_test() ->
    Tx = new(),
    ?assertEqual(<<>>, owner_signature(Tx)).

payer_signature_missing_test() ->
    Tx = missing_payer_signature_new(),
    ?assertNot(is_valid_payer(Tx)).

payer_signature_test() ->
    Tx = new(),
    ?assertEqual(<<>>, payer_signature(Tx)).

sign_test() ->
    #{public := PubKey, secret := PrivKey} = libp2p_crypto:generate_keys(ecc_compact),
    Tx0 = new(),
    SigFun = libp2p_crypto:mk_sig_fun(PrivKey),
    Tx1 = sign(Tx0, SigFun),
    Sig1 = owner_signature(Tx1),
    BaseTxn1 = Tx1#blockchain_txn_assert_location_v2_pb{owner_signature = <<>>},
    ?assert(libp2p_crypto:verify(blockchain_txn_assert_location_v2_pb:encode_msg(BaseTxn1), Sig1, PubKey)).

sign_payer_test() ->
    #{public := PubKey, secret := PrivKey} = libp2p_crypto:generate_keys(ecc_compact),
    Tx0 = new(),
    SigFun = libp2p_crypto:mk_sig_fun(PrivKey),
    Tx1 = sign_payer(Tx0, SigFun),
    Tx2 = sign(Tx1, SigFun),
    Sig2 = payer_signature(Tx2),
    BaseTx1 = Tx2#blockchain_txn_assert_location_v2_pb{owner_signature = <<>>, payer_signature= <<>>},
    ?assert(libp2p_crypto:verify(blockchain_txn_assert_location_v2_pb:encode_msg(BaseTx1), Sig2, PubKey)).

valid_location_test() ->
    Tx = new(),
    ?assert(is_valid_location(Tx, 12)).

invalid_location_test() ->
    Tx = invalid_new(),
    ?assertNot(is_valid_location(Tx, 12)).

to_json_test() ->
    Tx = new(),
    Json = to_json(Tx, []),
    ?assert(lists:all(fun(K) -> maps:is_key(K, Json) end,
                      [type, hash, gateway, owner, payer, location, nonce, staking_fee, fee])).

is_valid_gain_test() ->
    MinGain = 10,
    MaxGain = 150,
    Tx = new(),
    InvT1 = gain(Tx, 9),
    InvT2 = gain(Tx, 8),
    InvT3 = gain(Tx, 151),
    InvT4 = gain(Tx, 152),
    ValidT1 = gain(Tx, 10),
    ValidT2 = gain(Tx, 11),
    ValidT3 = gain(Tx, 150),
    ValidT4 = gain(Tx, 149),
    ?assertNot(is_valid_gain(InvT1, MinGain, MaxGain)),
    ?assertNot(is_valid_gain(InvT2, MinGain, MaxGain)),
    ?assertNot(is_valid_gain(InvT3, MinGain, MaxGain)),
    ?assertNot(is_valid_gain(InvT4, MinGain, MaxGain)),
    ?assert(is_valid_gain(ValidT1, MinGain, MaxGain)),
    ?assert(is_valid_gain(ValidT2, MinGain, MaxGain)),
    ?assert(is_valid_gain(ValidT3, MinGain, MaxGain)),
    ?assert(is_valid_gain(ValidT4, MinGain, MaxGain)).

-endif.

-ifdef(EQC).
-define(LOCATIONS, [631210968910285823, 631210968909003263, 631210968912894463, 631210968907949567,631243922668565503, 631243922671147007, 631243922895615999, 631243922665907711]).
gen(Keys) ->
    eqc_gen:oneof([
    {fun(Owner, Gateway, Payer, Location, Nonce) ->
            #{secret := OwnerSK, public := OwnerPK} = libp2p_crypto:keys_from_bin(Owner),
            #{public := GatewayPK} = libp2p_crypto:keys_from_bin(Gateway),
            #{secret := PayerSK, public := PayerPK} = libp2p_crypto:keys_from_bin(Payer),
            sign_payer(sign(new(libp2p_crypto:pubkey_to_bin(GatewayPK), libp2p_crypto:pubkey_to_bin(OwnerPK),  libp2p_crypto:pubkey_to_bin(PayerPK), Location, abs(Nonce)+1), libp2p_crypto:mk_sig_fun(OwnerSK)), libp2p_crypto:mk_sig_fun(PayerSK))
    end, [eqc_gen:oneof(Keys), eqc_gen:oneof(Keys), eqc_gen:oneof(Keys), eqc_gen:oneof(?LOCATIONS), eqc_gen:int()]},
    {fun(Owner, Gateway, Location, Nonce) ->
            #{secret := OwnerSK, public := OwnerPK} = libp2p_crypto:keys_from_bin(Owner),
            #{public := GatewayPK} = libp2p_crypto:keys_from_bin(Gateway),
            sign(new(libp2p_crypto:pubkey_to_bin(GatewayPK), libp2p_crypto:pubkey_to_bin(OwnerPK), Location, abs(Nonce)+1), libp2p_crypto:mk_sig_fun(OwnerSK))
    end, [eqc_gen:oneof(Keys), eqc_gen:oneof(Keys), eqc_gen:oneof(?LOCATIONS), eqc_gen:int()]}]).

-endif.
