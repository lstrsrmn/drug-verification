From mathcomp Require Import all_ssreflect all_algebra all_classical order reals lra seq tuple ssrbool ssrfun order exp constructive_ereal derive sequences eqtype normed_module Rstruct normedtype topology ring boolp.
From vehicle Require Import tensor.
Import Num.Theory GRing.Theory Order.POrderTheory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
(* Open Scope order_scope. *)
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Spec.

Open Scope classical_set_scope.

Notation R := Spec.R.
(* Parameter R : realFieldType. *)

(** State of patient **)
Record state := State
                  { C : R
                  ; T : R
                  ; wbc : R
                  ; age : R
                  ; weight : R
                  ; sex : R }.

(** Shows [tuple]'s and [state]'s are isomorphic. **)

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

(* Definition Vd : R := 10. *)
(* Definition Ke : R := 3. *)
(* Definition Ka : R := 4. *)

(** All equations and relations **)

Section Eqs.

(** Body constants, which are strictly positive and [Ka] <> [Ke] **)
Variables (Vd Ke Ka ttD : R).

Hypothesis Vd_pos : Vd > 0.
Hypothesis Ke_pos : Ke > 0.
Hypothesis Ka_pos : Ka > 0.
Hypothesis Ke_n_Ka : Ka - Ke != 0.
Hypothesis ttD_pos : ttD > 0.

(** $\frac{D\cdot Ka}{Vd \cdot (Ka - Ke)}\cdot (e^{-Ke \cdot t}-e^{-Ka \cdot t})$ **)
Definition Concentration (D t : R) : R :=
  ((D * Ka) / (Vd * (Ka - Ke))) * (expR ((-Ke) * t) - expR ((-Ka) * t)).

(** $\frac{D\cdot Ka}{Vd \cdot (Ka - Ke)}\cdot (Ka\cdot e^{-Ka\cdot t}-Ke\cdot e^{-Ke\cdot t})$ **)
Definition dCdt (D t : R) : R :=
  ((D * Ka / (Vd * (Ka - Ke)))) * (Ka * (expR (-Ka * t)) - Ke * (expR (-Ke * t))).

Definition d2Cdt2 (D t : R) : R :=
  ((D * Ka / (Vd * (Ka - Ke)))) * (Ke^+2 * (expR (-Ke * t)) - Ka^+2 * (expR (-Ka * t))).

(** $ \frac{ln(\frac{Ka}{Ke})}{Ka - Ke} $ **)
Definition dCdt_root : R :=
  (ln (Ka/Ke)) / (Ka - Ke).

Definition d2Cdt2_root : R :=
  (ln (Ke^+2/Ka^+2)) / (Ke - Ka).

Lemma conc_diff (D t : R) : differentiable (Concentration D) t.
Proof.
  by apply /differentiableZ /differentiableB;
  apply /differentiable_comp /derivable1_diffP /derivable_expR.
Qed.

Lemma derivative_correct (D : R) : (Concentration D)^`() = dCdt D.
Proof.
  apply funext => t.
  rewrite derive1E deriveZ //= deriveB //= -derive1E derive1_comp //= !derive1E deriveZ //= derive_id -!derive1E derive1_comp //= !derive1E deriveZ //= derive_id (congr1 (fun f => f (-Ke * t)) (derive_expR R)) (congr1 (fun f => f (-Ka * t)) (derive_expR R)) scalerBr !scalerA !scaler1 /dCdt.
  ring.
Qed.

Lemma derivative2_correct (D : R) : (Concentration D)^`(2) = d2Cdt2 D.
Proof.
  apply funext => t.
  rewrite /= derivative_correct /dCdt derive1E deriveZ //= deriveB //= !deriveM //= !derive_cst !scaler0 addr0 addr0 -!derive1E derive1_comp //= !derive1E (congr1 (fun f => f (-Ka * t)) (derive_expR R)) deriveM //= derive_id derive_cst scaler0 addr0 -derive1E derive1_comp //= !derive1E (congr1 (fun f => f (-Ke * t)) (derive_expR R)) deriveM //= derive_id derive_cst scaler0 addr0 scalerBr !scalerA !scaler1 /d2Cdt2.
  ring.
Qed.

Lemma unitr_n0expR (x : R) : expR x \is a GRing.unit.
Proof.
  apply/unitrP.
  exists (expR x)^-1.
  split;[apply/mulVf|apply/mulfV];
  by apply/lt0r_neq0/expR_gt0.
Qed.

Lemma unitr_Ke : Ke \is a GRing.unit.
Proof.
  apply/unitrP.
  exists Ke^-1.
  by split; [apply/mulVf|apply/mulfV]; apply lt0r_neq0.
Qed.

Lemma left_is_unit (D : R) (H : D != 0) : D * Ka / (Vd * (Ka - Ke)) \is a GRing.unit.
Proof.
  rewrite unitrM ?unitrV !unitrM.
  apply/and3P.
  split;
  rewrite !unitfE=> //.
  apply/andP.
  by split;
  [ | apply/lt0r_neq0].
  by apply lt0r_neq0.
Qed.

Lemma root_correct (D t : R) :
  D != 0 -> dCdt D t = 0 -> t = dCdt_root.
Proof.
  rewrite/dCdt /dCdt_root mulrBr=> H /subr0_eq /mulrI => /(_ (left_is_unit H)) H0.
  apply/(mulfI Ke_n_Ka).
  rewrite mulrA (mulrC (Ka - Ke) (ln _)) -mulrA mulrV;
  last by apply/unitrP;
  exists ((Ka - Ke)^-1);
  split;
  [apply/mulVf|
  apply/mulfV].
  apply/expR_inj.
  rewrite mulr1 lnK;
  last by apply Num.Internals.pos_divr_closed.
  rewrite mulrBl (_ : Ka * t - Ke * t = Ka * t + ( - Ke * t));
    last lra.
  rewrite exp.expRD.
  apply/(@mulfI _ Ke);
  first by apply/lt0r_neq0.
  rewrite !mulrA (mulrC Ke Ka) -!mulrA (mulrV unitr_Ke) mulr1 mulrA.
  apply/(@mulfI _ (expR (Ka * t))^-1);
  first by apply/lt0r_neq0; rewrite invr_gt0; apply/expR_gt0.
  by rewrite !mulrA (mulrC (expR _)^-1 Ke) -(mulrA Ke _ _) (mulVr (unitr_n0expR _)) mulrC mulr1 /= -expRN -mulNr mulrC (mulrC (expR _) Ka).
Qed.

Lemma root2_correct (D t : R) :
  D != 0 -> d2Cdt2 D t = 0 -> t = d2Cdt2_root.
Proof.
  rewrite /d2Cdt2 /d2Cdt2_root mulrBr => H /subr0_eq /mulrI.
  move=> /(_ (left_is_unit H)) H2.
  have H1: Ke - Ka != 0;
  first by move: Ke_n_Ka;
  lra.
  apply/(mulfI H1).
  rewrite mulrA (mulrC _ (ln _)) -mulrA mulrV;
  last by apply/unitrP;
  exists (Ke - Ka)^-1;
  split;
  [ apply/mulVf |
  apply/mulfV].
  apply expR_inj.
  rewrite mulr1 lnK;
  last by apply Num.Internals.pos_divr_closed;
  apply/exprn_gt0.
  rewrite mulrBl (_ : Ke * t - Ka * t = Ke * t + ( - Ka * t));
    last lra.
  rewrite exp.expRD.
  apply/(@mulfI _ (Ka^+2));
  first by apply/lt0r_neq0 /exprn_gt0.
  rewrite (mulrA (Ka^+2) (Ke ^+ 2) _) (mulrC (Ka^+2) (Ke^+2)) /= -(mulrA (Ke^+2) (Ka ^+ 2)) (@mulfV _ (Ka^+2)) ?mulr1;
  last by apply/lt0r_neq0/exprn_gt0.
  apply/(@mulfI _ (expR (Ke * t))^-1);
  first by apply/lt0r_neq0; rewrite invr_gt0; apply/expR_gt0.
  by rewrite mulrC -mulrA (mulrC (expR (Ke * t)) _) -(mulrA (expR (- Ka * t)) _ _) (mulrV (unitr_n0expR _)) mulr1 -expRN -mulNr (mulrC _ (Ke ^+2)).
Qed.

Lemma ltr_pmul_pos (a b c : R) : 0 < a -> b < c -> a * b < a * c.
Proof.
  rewrite (_ : (b < c) = (b - c < 0)); last lra.
  move=> Ha Hbc.
  rewrite (_ : a * b < a * c = (a * b - a * c < 0));
    last lra.
  by rewrite -mulrBr pmulr_rlt0.
Qed.

Lemma ltr_nmul_pos (a b c : R) : a < 0 -> c < b -> a * b < a * c.
Proof.
  rewrite (_ : (c < b) = (0 < b - c)); last lra.
  move=> Ha Hbc.
  rewrite (_ : a * b < a * c = (a * b - a * c < 0));
    last lra.
  by rewrite -mulrBr nmulr_rlt0.
Qed.

Lemma conc_cont (a b D : R) : {within `[a, b], continuous (Concentration D)}.
Proof.
  apply/(continuous_within_itvP _ _).
  shelve.
  split.
  (* 
continuous_in_subspaceT: *)
  apply continuousM.
  move=> x.
  rewrite in_itv.
  rewrite itvE.
  near=> x.
  rewrite /Concentration.


Admitted.

Lemma root_is_max (D t : R) (HD : D != 0) :
  Concentration D t <= Concentration D dCdt_root.
Proof.
  case: (ltrP t dCdt_root)=> [//=|].
  shelve.
  have : exists c : R, t < c.
  exists (t + 1).
  lra.
  move=> [c Hc].
  have : 0 < dCdt_root.
  rewrite /dCdt_root.
  case: (ltgtP Ka Ke)=> H.
  rewrite (_ : _ / _ = (- ln (Ka / Ke) / -(Ka - Ke)));
  last by lra.
  apply /divr_gt0;
  rewrite oppr_gt0.
  apply/ln_lt0.
  move: Ke_pos.
  rewrite -invr_gt0=> Ke_pos'.
  apply/andP.
  split.
  by apply divr_gt0.
  move: H => /(ltr_pmul_pos Ke_pos').
  rewrite (mulrC (Ke^-1) (Ke)) divff.
  by rewrite mulrC.
  by apply lt0r_neq0.
  lra.
  apply /divr_gt0.
  apply ln_gt0.
  move: Ke_pos.
  rewrite -invr_gt0=> Ke_pos'.
  move: H => /(ltr_pmul_pos Ke_pos').
  rewrite mulrC divff.
  by rewrite mulrC.
  by apply lt0r_neq0.
  lra.
  exfalso.
  move/eqP: Ke_n_Ka.
  lra.
  move=> H0 H1.
  have := (lt_le_trans H0 H1) => {H1} H.
  have := (lt_trans H Hc) => Hc'.
  have := EVT_max (ltW Hc') (conc_cont (ltW Hc')) => /(_ D) [x] H1 H2.
  rewrite (_ : dCdt_root = x)=> //=.
  move: H2.
  have : t \in `[0,c]%R.
  shelve.
  by move=> H2 /(_ t H2) H3.
  symmetry.
  apply (root_correct HD).
  suff : is_derive x 1 (Concentration D) 0.
  case.
  move=> _.
  by rewrite -derive1E derivative_correct.
  apply (derive1_at_max (ltW Hc')).
  move=> z _.
  rewrite derivable1_diffP.
  apply conc_diff.
  shelve.
  move=> t' Ht'.
  apply H2.
  shelve.
Admitted.

(* Need to say that for the Concentration function, dCdt is the derivative and dCdt_root is the global maximum *)

Definition conc_max (D : R) (HD : 0 <= D) :
  Concentration D dCdt_root = ((D * Ka) / (Vd * (Ka - Ke))) * (expR (-Ke * ((ln (Ka/Ke))/(Ka - Ke))) - expR (-Ka * ((ln (Ka/Ke))/(Ka - Ke)))).
Proof.
  case (boolP (D == 0))=> //=.
Qed.

Definition total_conc n (Ds : n.-tuple R) (t : R) := \sum_(i < n) maxr 0 ((Ka / Vd * (Ka - Ke)) * (((tnth Ds i) * (expR (-Ke * (t - i%:R)) - expR (-Ka * (t - i%:R)))))).

Definition total_conc_diff n (Ds : n.-tuple R) (t : R) := \sum_(i < n) maxr 0 ((Ka / Vd * (Ka - Ke)) * (((tnth Ds i) * (Ka * expR (-Ka * (t - i%:R)) - Ke * expR (-Ke * (t - i%:R)))))).

Lemma total_conc_diff_correct n (Ds : n.-tuple R) :
  (total_conc Ds)^`() = total_conc_diff Ds.
  apply/funext=> t.
  rewrite derive1E /total_conc.
  rewrite /=.
  (* this is just an eta reduction but I don't know how to do it properly *)
  rewrite (_ : (fun t0 : R =>
                  \sum_(i < n)
                  maxr 0
                  (Ka / Vd * (Ka - Ke) *
                     (tnth Ds i * (expR (- Ke * (t0 - i%:R)) - expR (- Ka * (t0 - i%:R)))))) = (\sum_(i < n) fun t0 : R => maxr 0
                                                                                                                        (Ka / Vd * (Ka - Ke) *
                                                                                                                           (tnth Ds i * (expR (- Ke * (t0 - i%:R)) - expR (- Ka * (t0 - i%:R))))))).
  rewrite derive_sum.


End Eqs.

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

Definition Vd : R := 10.
Lemma Vd_pos : 0 < Vd.
Proof. lra. Qed.
Definition Ka : R := 4.
Lemma Ka_pos : 0 < Ka.
Proof. lra. Qed.
Definition Ke : R := 3.
Lemma Ke_pos : 0 < Ke.
Proof. lra. Qed.
Lemma Ka_n_Ke : Ka - Ke != 0.
Proof. apply/eqP. lra. Qed.

Axiom dose_non_neg : forall s : state, 0 < (controller (state_to_tuple s))^^=0.

Axiom temp_vehicle_output : forall C : R, forall s : state, healthyInput s -> (controller (state_to_tuple s))^^=0 * (27/640) <= 30.

Theorem max_dose_limited (s : state) (t : R) (Ht : 0 <= t) : healthyInput s -> Concentration Vd Ke Ka (controller (state_to_tuple s))^^=0 t <= 30.
Proof.
  move=> H.
  set D := (controller (state_to_tuple s))^^=0.
  have := @root_is_max _ _ _ Vd_pos Ke_pos Ka_pos Ka_n_Ke D t (lt0r_neq0 (dose_non_neg s)).
  rewrite (conc_max Vd Ke Ka (ltW (dose_non_neg s))).
  rewrite (_ : (controller (state_to_tuple s))^^=0 * Ka / (Vd * (Ka - Ke)) *
                 (expR (- Ke * (ln (Ka / Ke) / (Ka - Ke))) - expR (- Ka * (ln (Ka / Ke) / (Ka - Ke)))) = (controller (state_to_tuple s))^^=0 * (Ka / (Vd * (Ka - Ke)) *
                                                                                                           (expR (- Ke * (ln (Ka / Ke) / (Ka - Ke))) - expR (- Ka * (ln (Ka / Ke) / (Ka - Ke)))))).
  rewrite (_ : Ka / (Vd * (Ka - Ke)) *
                 (expR (- Ke * (ln (Ka / Ke) / (Ka - Ke))) - expR (- Ka * (ln (Ka / Ke) / (Ka - Ke)))) = 27 / 640).
  move=> H'.
  apply  (le_trans H' (temp_vehicle_output 0 H)).
  shelve.
  lra.
  Admitted.
