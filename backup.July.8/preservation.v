Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Language.
Require Import Lemmas.
Require Import Low_eq.
Require Import Label.
Require Import simulation_full.

Lemma valid_config_preservation : forall T ct
                                          ctn ctns h
                                          ctn' ctns' h',
    config_has_type ct empty_context (Config ct ctn ctns h) T ->
    valid_config (Config ct  ctn ctns h) ->
    Config ct ctn ctns h
           ==> Config ct ctn' ctns' h' ->
    valid_config (Config ct ctn' ctns' h').
Proof with eauto.
Admitted.
Hint Resolve valid_config_preservation.

Lemma typing_preservation : forall T ct
                                   ctn ctns h
                                   ctn' ctns' h',
    config_has_type ct empty_context (Config ct ctn ctns h) T ->
    valid_config (Config ct  ctn ctns h) ->
    Config ct ctn ctns h
           ==> Config ct ctn' ctns' h' ->
    config_has_type ct empty_context (Config ct ctn' ctns' h') T.
Proof with eauto.
Admitted.
Hint Resolve typing_preservation.

