From mathcomp Require Import all_ssreflect all_algebra order reals lra seq tuple ssrbool ssrfun order.
Require Import mathcomp.ssreflect.eqtype.
From vehicle Require Import tensor.
Import Num.Theory GRing.Theory Order.POrderTheory.

Open Scope ring_scope.
(* Open Scope order_scope. *)
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  move=> t.
  rewrite /state_to_tuple /tuple_to_state /=.
  apply val_inj => /=.
  apply/(eq_from_nth _).
  by rewrite size_tuple.
  repeat
  case=> [//= | //=];
  by rewrite (tnth_nth (tnth_default t 0)).
Qed.

Definition controller x :=
  pk (ntensor_of_tuple x).

Definition max (x y : R) :=
  if x <= y then x else y.

Definition nextTemp (s : state) :=
  s.(T) + 2/25 - 1/200 * s.(C) + (controller (state_to_tuple s))^^=0 / 30 - 3 / 25 * (T s - 37).

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

Definition healthyInput s :=
  [/\ 0 <= s.(C) <= 30
    , 36 <= s.(T) <= 38
    , 4 <= s.(wbc) <= 12
    , 18 <= s.(age) <= 89
    & 50 <= s.(weight) <= 100
    /\ ( (s.(sex) = 0) \/ (s.(sex) = 1))
  ].

Definition healthyInputB s :=
  [&& 0 <= s.(C) <= 30
    , 36 <= s.(T) <= 38
    , 4 <= s.(wbc) <= 12
    , 18 <= s.(age) <= 89
    & (50 <= s.(weight) <= 100)
    && ( (s.(sex) == 0) || (s.(sex) == 1))
  ].

Lemma healthyInputP (s : state) :
  reflect (healthyInput s) (healthyInputB s).
Proof.
  apply: (iffP andP);
  rewrite /healthyInput.
  move=> [H /and5P [H0 H1 H2 H3 /orP [H4 | H4]]];
  split => [//|//|//|//|];
  split=>[//|].
  left.
  by apply/eqP.
  right.
  by apply/eqP.
  move=> [H0 H1 H2 H3 [H4 [H5 | H5]]];
  split=> [//|];
  apply/and5P;
  split => [//|//|//|//|];
  apply/orP.
  left.
  by apply/eqP.
  right.
  by apply/eqP.
Qed.



Definition unhealthyInput s :=
  [/\ 0 <= s.(C) <= 30
    , 38 <= s.(T) <= 40
    , 12 <= s.(wbc) <= 20
    , 18 <= s.(age) <= 89
      & 50 <= s.(weight) <= 100
      /\ ( (s.(sex) = 0) \/ (s.(sex) = 1))
  ].

Definition unhealthyInputB s :=
  [&& 0 <= s.(C) <= 30
    , 38 <= s.(T) <= 40
    , 12 <= s.(wbc) <= 20
    , 18 <= s.(age) <= 89
      & (50 <= s.(weight) <= 100)
      && ( (s.(sex) == 0) || (s.(sex) == 1))
  ].


Lemma unhealthyInputP (s : state) :
  reflect (unhealthyInput s) (unhealthyInputB s).
Proof.
  apply: (iffP andP);
  rewrite /healthyInput.
  move=> [H /and5P [H0 H1 H2 H3 /orP [H4 | H4]]];
  split => [//|//|//|//|];
  split=>[//|].
  left.
  by apply/eqP.
  right.
  by apply/eqP.
  move=> [H0 H1 H2 H3 [H4 [H5 | H5]]];
  split=> [//|];
  apply/and5P;
  split => [//|//|//|//|];
  apply/orP.
  left.
  by apply/eqP.
  right.
  by apply/eqP.
Qed.

Axiom TEMPFIX : forall s : state, (ntensor_of_tuple (state_to_tuple s))^^Spec.sex = const_t 0 -> (50 <= weight s)%R /\ (weight s <= 100)%R.

Goal forall t u : 'nT[R]_([::]), (t.[::] == u.[::]) = (t == u).
Proof.
  move=> t u.
  apply/eqP.
  case: ifPn => [/eqP -> // | /eqP].
  by rewrite tensor_nil_eqP.
Qed.

Lemma swap_healthy {s} : healthyInput s <-> Spec.healthyInput (ntensor_of_tuple (state_to_tuple s)).
Proof.
  split.
  rewrite /Spec.healthyInput.
  rewrite -!tensor_nil_leP !nstack_eqE !const_tK.
  move=> [/andP [H00 H01] /andP [H10 H11] /andP [H20 H21] /andP [H30 H31] [/andP [H40 H41] [H5 | H5]]];
   repeat split;
   try by [].
  right.
  apply/eqP.
  by rewrite -tensor_nil_eqP const_tK nstack_eqE.
  left.
  repeat split;
    try by [].
  apply/eqP.
  by rewrite -tensor_nil_eqP const_tK nstack_eqE.
  rewrite /Spec.healthyInput.
  rewrite -!tensor_nil_leP -?tensor_nil_eqP !const_tK ?nstack_eqE.
  move=> [[H00 H01] [[H10 H11] [[H20 H21] [[H30 H31]]]]] [[[H40 H41] /eqP H5] | /eqP H5];
   repeat split;
   try apply/andP;
   try by split.
  right.
  by rewrite -tensor_nil_eqP const_tK nstack_eqE in H5.
  by apply TEMPFIX.
  left.
  by rewrite -tensor_nil_eqP const_tK nstack_eqE in H5.
Qed.

Lemma swap_unhealthy {s} : unhealthyInput s <-> Spec.unhealthyInput (ntensor_of_tuple (state_to_tuple s)).
Proof.
  split.
  rewrite /Spec.unhealthyInput.
  rewrite -!tensor_nil_leP !nstack_eqE !const_tK.
  move=> [/andP [H00 H01] /andP [H10 H11] /andP [H20 H21] /andP [H30 H31] [/andP [H40 H41] [H5 | H5]]];
repeat split;
try by [].
  right.
  apply/eqP.
  by rewrite -tensor_nil_eqP const_tK nstack_eqE.
  left.
  repeat split;
    try by [].
  apply/eqP.
  by rewrite -tensor_nil_eqP const_tK nstack_eqE.
  rewrite /Spec.unhealthyInput.
  rewrite -!tensor_nil_leP -?tensor_nil_eqP !const_tK ?nstack_eqE.
  move=> [[H00 H01] [[H10 H11] [[H20 H21] [[H30 H31]]]]] [[[H40 H41] /eqP H5] | /eqP H5];
  repeat split;
    try apply/andP;
    try by split.
  right.
  by rewrite -tensor_nil_eqP const_tK nstack_eqE in H5.
  by apply TEMPFIX.
  left.
  by rewrite -tensor_nil_eqP const_tK nstack_eqE in H5.
Qed.

Axiom fix_brackets : forall a b c : R, a * b - c = a * (b - c).

Lemma temperature_monotone (s : state) :
  unhealthyInput s -> s.(T) - 2 <= nextTemp s <= s.(T) - 1/100.
Admitted.
(* Proof. *)
(*   rewrite swap_unhealthy => /tempDecr. *)
(*   rewrite /Spec.nextTemp /nextTemp -tensor_nil_leP !tensor_nilr_spec tensor_nilV !const_tK /= !nstack_eqE !mul1r /controller /= /normpk. *)
(*   by rewrite (fix_brackets (3/25) (tnth (state_to_tuple s) temp) 37). *)
(* Qed. *)

Definition safeOutput (s : state) := 0 <= (pk (ntensor_of_tuple (state_to_tuple s)))^^=0 / 30 + (s.(C)) <= 30.

Lemma safe (s : state) :
  healthyInput s \/ unhealthyInput s -> safeOutput s.
Proof.
  rewrite swap_healthy swap_unhealthy => /safe.
  by rewrite /Spec.safeOutput -!tensor_nil_leP !tensor_nilr_spec !tensor_nilV !const_tK /= !nstack_eqE /normpk=> /andP.
Qed.

Definition unhealthyOutput (s : state) := 10 <= (pk (ntensor_of_tuple (state_to_tuple s)))^^=0 / 30 + s.(C) <= 30.

Lemma unhealthy (s : state) :
  unhealthyInput s -> unhealthyOutput s.
Proof.
  rewrite swap_unhealthy => /unhealthy.
  by rewrite /Spec.unhealthyOutput /unhealthyOutput -!tensor_nil_leP !tensor_nilr_spec !tensor_nilV !const_tK /= !nstack_eqE /normpk => /andP.
Qed.

Definition healthyOutput (s : state) := (pk (ntensor_of_tuple (state_to_tuple s)))^^=0 = 0.

Lemma healthy (s : state) :
  healthyInput s -> healthyOutput s.
Proof.
  rewrite swap_healthy => /healthy.
  rewrite /Spec.unhealthyOutput /unhealthyOutput => /eqP.
  by rewrite -!tensor_nil_eqP const_tK.
Qed.

Definition next_state (s : state) (D_prev : R) :=
  let y := (normpk (ntensor_of_tuple (state_to_tuple s)))^^=0 in
  let C_next := s.(C) + (-(1/10 * (1 - 4/1000 * (s.(age) - 50))) * s.(C) + (7/10 * D_prev + 3/10 * y) / (30 * (s.(weight) / 70))) in
  let T_next := s.(T) + 2/25 - 1/200 * C s + y / 30 - (3/25 * ((T s) - 37)) in
  let WBC_next := s.(wbc) + (12/100 * (70/s.(weight))) - 2/100* s.(wbc) - (4/100 * (1 - 3/1000 * (s.(age) - 50))) * (s.(wbc) - 8) in
  {| C := C_next
  ; T := T_next
  ; wbc:= WBC_next
  ; age := s.(age)
  ; weight := s.(weight)
  ; sex := s.(sex) |}.

Definition step (p : state * R) :=
  let D_t := (normpk (ntensor_of_tuple (state_to_tuple (fst p))))^^=0 in
  let s' := next_state (fst p) (7/10 * (snd p) + 3/10 * D_t) in
  (s', D_t).



Lemma temp_moves_k (s : state) (r : R) (n : nat) :
  exists k : nat, forall m : nat, k <= 200 -> n <= k < m -> unhealthyInput (iter n step (s, r)).1 /\ healthyInput (iter m step (s,r)).1.
Admitted.

Lemma iter_temp_moves (s : state) (m : R) :
  forall n k : nat, unhealthyInput (iter n step (s, m)).1 ->  T (fst (iter (n + k) step (s, m))) - 2 <= T (fst (iter (n + k) step (s, m))) <= T (fst (iter (n + k) step (s, m))) - k%:~R * 1 / 100.
Proof.
  move=> n.
  elim=>[//=|k IHk H].
  rewrite addn0 mul0r /=.
  rewrite (_ : 0 / 100 = 0).
  rewrite subr0 /unhealthyInput.
  move=> [H0 H1].
  lra.
  lra.
  have := IHk H.
  rewrite (_ : k.+1%:~R * 1 / 100 = k%:~R * 1 / 100 + 1/100);
    last lra.
  rewrite addnS /=.
  set c :=  (iter (n + k) step (s,m)).
  rewrite (_ : (T c.1 + 2 / 25 - 1 / 200 * C c.1 + (normpk (ntensor_of_tuple (state_to_tuple c.1)))^^=0 / 30 -
                  3 / 25 * (T c.1 - 37) - 2 <=
                  T c.1 + 2 / 25 - 1 / 200 * C c.1 + (normpk (ntensor_of_tuple (state_to_tuple c.1)))^^=0 / 30 -
                    3 / 25 * (T c.1 - 37) <=
                  T c.1 + 2 / 25 - 1 / 200 * C c.1 + (normpk (ntensor_of_tuple (state_to_tuple c.1)))^^=0 / 30 -
                    3 / 25 * (T c.1 - 37) - (k%:~R * 1 / 100 + 1 / 100)) <-> (T c.1 - 2 <= T c.1 <= T c.1 - (k%:~R * 1 / 100 + 1 / 100))).

(* Lemma iter_step_healthy (s : state) (m : R) : *)
(*   forall n : nat, healthyInput (fst (iter n step (s, m))) -> healthyInput (fst (iter n.+1 step (s, m))). *)
(* Proof. *)
(*   elim=>[/= H|/=]. *)
(*   have := healthy H. *)
(*   rewrite /healthyOutput=>H0. *)
(*   rewrite !H0 /=. *)
(*   rewrite /healthyInput /next_state !H0 /=. *)
(*   split. *)
(*   shelve. *)
(*   apply/andP. *)
(*   move: H. *)
(*   rewrite swap_healthy. *)
(*   move=> /tempStable [Htl Htu]. *)
(*   split. *)
(*   move: Htl. *)
(*   rewrite /Spec.nextTemp -tensor_nil_leP !tensor_nilr_spec tensor_nilV !const_tK  H0 /= !nstack_eqE. *)
(*   rewrite (_ : tnth (state_to_tuple s) temp = T s). *)
(*   rewrite (_ : tnth (state_to_tuple s) conc = C s). *)
(*   rewrite mul1r. *)

Lemma test (x y : R) : (x <= y) -> exists z : R, (z >= 0) -> x + z = y.
Proof.
  move=> H.
  exists (y - x).
  lra.
Qed.

Theorem patient_gets_better :
  forall n : nat, forall s : state, (200 <= n)%N -> unhealthyInput s -> 36 <= (fst (iter n step (s, 0))).(T) <= 38.
Proof.
  elim=> [//=| n IHn s HSn].
  rewrite /=.
