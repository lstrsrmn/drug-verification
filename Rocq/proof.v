From mathcomp Require Import ssreflect all_algebra order reals lra seq tuple ssrbool ssrfun.
Require Import mathcomp.ssreflect.eqtype.
From vehicle Require Import tensor.
Import Num.Theory GRing.Theory Order.POrderTheory.

Open Scope ring_scope.
Open Scope order_scope.

Require Import Spec.

Notation R := Spec.R.

Record state := State
                  { C : R
                  ; T : R
                  ; wbc : R
                  ; age : R
                  ; weight : R
                  ; sex : R }.

Definition state_to_tuple (s : state) : 6.-tuple R :=
  [tuple C s; T s; wbc s; age s; weight s; sex s].

Definition tuple_to_state (t : 6.-tuple R) : state :=
  {| C := tnth t 0
  ; T := tnth t 1
  ; wbc := tnth t 2
  ; age := tnth t 3
  ; weight := tnth t 4
  ; sex := tnth t 5
  |}.

Lemma state_to_tupleK : cancel state_to_tuple tuple_to_state.
Proof. by case. Qed.

Lemma tuple_to_stateK : cancel tuple_to_state state_to_tuple.
Proof.
  Admitted.
  (* move=> t. *)
  (* rewrite /state_to_tuple /tuple_to_state /=. *)
  (* apply val_inj => /=. *)
  (* apply/(eq_from_nth _). *)
  (* by rewrite size_tuple. *)
  (* move=> i Hi. *)

Definition controller x :=
  pk (ntensor_of_tuple x).

Definition max (x y : R) :=
  if x <= y then x else y.

Definition nextTemp (s : state) :=
  s.(T) + (2/25 - (1/200 * s.(C) + (controller (state_to_tuple s))^^=0 / 30) - (3 / 25 * T s - 37)).

(* Definition nextState (s : state) (D_prev : R) := *)
(*   let ke_eff := 1/10 * (1 - 4/1000 * (s.(age) - 50)) in *)
(*   let D_t_raw := (max 0 (s.(T) - 38)) + (max 0 (s.(wbc) - 12)) in *)
(*   let D_t := 7/10 * D_prev + 3/10 * D_t_raw in *)
(*   let vd_eff := 0 in *)
(*   let newC := s.(C) + (-ke_eff * s.(C) + D_t / vd_eff) in *)
(*   let newT := s.(T) in *)
(*   let newwbc := s.(wbc) in *)
(*   {| C := newC *)
(*   ; T := newT *)
(*   ; wbc := newwbc *)
(*   ; age := s.(age) *)
(*   ; weight := s.(weight) *)
(*   ; sex := s.(sex) *)
(*   |}. *)

Definition safeInput s :=
  [&& 0 <= s.(C) <= 30
    , 73/2 <= s.(T) <= 40
    , 15/2 <= s.(wbc) <= 20
    , 18 <= s.(age) <= 89
    , 50 <= s.(weight) <= 100
    & ( (s.(sex) == 0) || (s.(sex) == 1))
  ].

Lemma swap_safety {s} : safeInput s <-> Spec.safeInput (ntensor_of_tuple (state_to_tuple s)).
Proof.
  split.
  move=> /and5P [/andP [H00 H01] /andP [H10 H11] /andP [H02 H12] /andP [H03 H13] /andP [/andP [H04 H14] /orP [/eqP H5 | /eqP H5]]];
 repeat split;
 try by rewrite -tensor_nil_leP nstack_eqE const_tK;
 try by [].
  right.
  apply/eqP.
  by rewrite -tensor_nil_eqP const_tK nstack_eqE.
  left.
  repeat split;
    rewrite -?tensor_nil_leP ?const_tK ?nstack_eqE;
    try by [].
  apply/eqP.
  by rewrite -tensor_nil_eqP const_tK nstack_eqE.
  rewrite /Spec.safeInput.
  rewrite -!tensor_nil_leP -?tensor_nil_eqP !const_tK ?nstack_eqE.
  move=> [[H00 H01] [[H10 H11] [[H20 H21] [[H30 H31]]]]] [[[H40 H41] /eqP H5] | /eqP H5].
  apply/and5P.
  repeat split;
    try apply/andP;
    try by split.
  split.
  apply/andP.
  by split.
  apply/orP.
  right.
  move: H5.
  rewrite -tensor_nil_eqP nstack_eqE const_tK.
  by move=> /eqP H5.
  repeat split;
    try apply/andP;
    try by split.
  split.
  apply/andP.
  by split.
  apply/and5P.
  split;
    try apply/andP;
    try by split.
  admit. (* seems to be some kind of bug here. The VCL spec puts the or only around sex, but for some reason in the generated .v file, the or is around weight and sex, so they only have weight when their sex is 1 *)
  (* Yes this is a bug. Vehicle has abstracted out a bracket around an or statement that messes with the precedent *)
  apply/orP.
  left.
  move: H5.
  rewrite -tensor_nil_eqP nstack_eqE const_tK.
  by move=> /eqP H5.
  Admitted.



Lemma temperature_monotone (s : state) :
  safeInput s -> nextTemp s <= s.(T).
Proof.
  pose x := ntensor_of_tuple (state_to_tuple s).
  have H0 : s = tuple_to_state (tuple_of_ntensor x).
  by rewrite ntensor_of_tupleK state_to_tupleK.
  rewrite swap_safety.
  move=> /tempDecr.
  rewrite /Spec.nextTemp /nextTemp -tensor_nil_leP !tensor_nilr_spec tensor_nilV !const_tK /= !nstack_eqE.
  by rewrite !mul1r /controller /= /normpk.
Qed.
