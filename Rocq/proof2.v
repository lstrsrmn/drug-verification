From mathcomp Require Import all_boot all_order all_algebra all_classical all_analysis all_reals ring lra.
(* From vehicle Require Import tensor. *)
From HB Require Import structures.
Import Num.Theory GRing.Theory Order.POrderTheory.
Import numFieldNormedType.Exports.
Import numFieldTopology.Exports.

Open Scope ring_scope.
Open Scope order_scope.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Require Import Spec. *)

Open Scope classical_set_scope.

(* Notation R := Spec.R. *)
Section Theory.

(* #[export, non_forgetful_inheritance] *)
(* HB.instance Definition _ (R : realType) := *)
(*   Order_isNbhs.Build _ R (@real_order_nbhsE R). *)

Context (R : realType).
Context (R' : realFieldType).

(** State of patient **)
Record state := State
                  { C : R
                  ; T : R
                  ; wbc : R
                  ; age : R
                  ; weight : R
                  ; sex : R }.

(** Shows [tuple]'s and [state]'s are isomorphic. **)

Definition tuple6 := 6.-tuple R.

Definition state_to_tuple (s : state) : tuple6 :=
  [tuple C s; T s; wbc s; age s; weight s; sex s].

Definition tuple_to_state (t : tuple6) : state :=
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


Coercion state_to_tuple : state >-> tuple6.

(* Definition controller x := *)
(*   pk (ntensor_of_tuple x). *)

(* Definition Vd : R := 10. *)
(* Definition Ke : R := 3. *)
(* Definition Ka : R := 4. *)

(** All equations and relations **)

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
  apply/unitrPr.
  exists (expR x)^-1.
  by apply/mulfV/lt0r_neq0/expR_gt0.
Qed.

Lemma unitr_Ke : Ke \is a GRing.unit.
Proof.
  apply/unitrPr.
  exists Ke^-1.
  by apply/mulfV/lt0r_neq0.
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

Lemma left_is_unitV (D : R) (H : D != 0) : (D * Ka / (Vd * (Ka - Ke)))^-1 \is a GRing.unit.
Proof.
  rewrite unitrV.
  by apply left_is_unit.
Qed.

Lemma mulr0I {a b : R} : a \is a GRing.unit -> a * b = 0 <-> b = 0.
Proof.
  move=> H.
  split => H0.
  apply/(mulrI H).
  by rewrite mulr0.
  rewrite H0.
  by rewrite mulr0.
Qed.

Lemma root_correct (D t : R) :
  D != 0 -> dCdt D t = 0 <-> t = dCdt_root.
Proof.
  move=> H.
  split.
  rewrite/dCdt /dCdt_root mulrBr=> /subr0_eq /mulrI => /(_ (left_is_unit H)) H0.
  apply/(mulfI Ke_n_Ka).
  rewrite mulrA (mulrC (Ka - Ke) (ln _)) -mulrA mulrV;
  last by apply/unitrPr;
  exists ((Ka - Ke)^-1);
  apply/mulfV.
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
  move=> H0.
  rewrite H0 /dCdt /dCdt_root (mulr0I (left_is_unit H)) (_ : _ = 0 <-> Ka * expR (- Ka * (ln (Ka / Ke) / (Ka - Ke))) =
                         Ke * expR (- Ke * (ln (Ka / Ke) / (Ka - Ke))));
  last lra.
  apply/ln_inj;
  try apply/mulr_gt0 => //;
         try apply/expR_gt0.
  rewrite !lnM //=.
  by rewrite !expRK /= lnV // !mulrA -(divr1 (ln Ka)) -(divr1 (ln Ke)) !addf_div //=; lra.
  by apply/expR_gt0.
  suff : 0 < Ke^-1 => //.
  by rewrite invr_gt0.
  by apply/expR_gt0.
  suff : 0 < Ke^-1 => //.
  by rewrite invr_gt0.
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
  last by apply/unitrPr;
  exists (Ke - Ka)^-1;
  apply/mulfV.
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

Lemma ler_pmul_pos (a b c : R) : 0 < a -> b <= c -> a * b <= a * c.
Proof.
  rewrite (_ : (b <= c) = (b - c <= 0)); last lra.
  move=> Ha Hbc.
  rewrite (_ : a * b <= a * c = (a * b - a * c <= 0));
    last lra.
  by rewrite -mulrBr pmulr_rle0.
Qed.

Lemma ltr_nmul_pos (a b c : R) : a < 0 -> c < b -> a * b < a * c.
Proof.
  rewrite (_ : (c < b) = (0 < b - c)); last lra.
  move=> Ha Hbc.
  rewrite (_ : a * b < a * c = (a * b - a * c < 0));
  last lra.
  by rewrite -mulrBr nmulr_rlt0.
Qed.

Lemma ler_nmul_pos (a b c : R) : a < 0 -> c <= b -> a * b <= a * c.
Proof.
  rewrite (_ : (c <= b) = (0 <= b - c)); last lra.
  move=> Ha Hbc.
  rewrite (_ : a * b <= a * c = (a * b - a * c <= 0));
  last lra.
  by rewrite -mulrBr nmulr_rle0.
Qed.

Lemma conc_cont (D : R) :  continuous (Concentration D).
Proof.
  move=> x.
  rewrite /Concentration.
  rewrite (_ : (fun t => _) = (cst (D * Ka / (Vd * (Ka - Ke))) \* (fun t => expR (- Ke * t) - expR ( -Ka * t)))) => //=.
  apply/continuousM.
  apply/cst_continuous.
  apply/continuousB => /=.
  rewrite (_ : (fun x1 => expR (- Ke * x1)) = expR \o (fun x1 => -Ke * x1)) => //=.
  apply/continuous_comp.
  apply/scaler_continuous.
  apply/continuous_expR.
  rewrite (_ : (fun x1 => expR (- Ka * x1)) = expR \o (fun x1 => -Ka * x1)) => //=.
  apply/continuous_comp.
  apply/scaler_continuous.
  apply/continuous_expR.
Qed.

  (* apply/diff_derivable/conc_diff. *)
(* Qed. *)

(* Lemma conc_cont (a b D : R) : {within `[a, b], continuous (Concentration D)}. *)
(* Proof. *)
(*   apply/derivable_within_continuous => /= t Ht. *)
(*   apply/diff_derivable/conc_diff. *)
(* Qed. *)

Lemma deriv_is_pos (D t : R) (HD : 0 < D) (Ht : t \in `]-oo, dCdt_root[%R) :
 (0 <= (Concentration D)^`() t).
Proof.
  rewrite derivative_correct /dCdt.
  case: (ltgtP t 0) => Ht0.
  rewrite -(mulr0 (D * Ka / (Vd * (Ka - Ke)))).
  case: (ltgtP Ke Ka) => HKeKa.
  apply/ler_pmul_pos.
  rewrite -(mulr0 (D * Ka)).
  apply/ltr_pmul_pos.
  rewrite -(mulr0 D).
  by apply/ltr_pmul_pos.
  rewrite invr_gt0.
  rewrite -(mulr0 Vd).
  by apply/ltr_pmul_pos => //;
  lra.
  rewrite (_ : (0 <= _) = (Ke * expR (-Ke * t) <= Ka * expR (- Ka * t)));
  last by lra.
  apply/ler_pM => //=.
  by apply/ltW.
  by apply/exp.expR_ge0.
  lra.
  rewrite -ler_ln;
  try by apply/expR_gt0.
  rewrite !expRK.
  rewrite mulrC (mulrC (-Ka)).
  apply/ler_nmul_pos => //.
  lra.
  apply/ler_nmul_pos.
  rewrite -(mulr0 (D * Ka)).
  apply/ltr_pmul_pos.
  rewrite -(mulr0 D).
  by apply/ltr_pmul_pos.
  rewrite invr_lt0.
  rewrite -(mulr0 Vd).
  by apply/ltr_pmul_pos => //;
  lra.
  rewrite (_ : (_ <= 0) = (Ka * expR (-Ka * t) <= Ke * expR (- Ke * t)));
  last by lra.
  apply/ler_pM => //=.
  by apply/ltW.
  by apply/exp.expR_ge0.
  lra.
  rewrite -ler_ln;
  try by apply/expR_gt0.
  rewrite !expRK.
  rewrite mulrC (mulrC (-Ke)).
  apply/ler_nmul_pos => //.
  lra.
  move/eqP: Ke_n_Ka.
  lra.
  (* 0 < t *)
  rewrite -(mulr0 (D * Ka / (Vd * (Ka - Ke)))).
  case: (ltgtP Ke Ka) => HKeKa.
  apply/ler_pmul_pos.
  rewrite -(mulr0 (D * Ka)).
  apply/ltr_pmul_pos.
  rewrite -(mulr0 D).
  by apply/ltr_pmul_pos.
  rewrite invr_gt0.
  rewrite -(mulr0 Vd).
  by apply/ltr_pmul_pos => //;
                          lra.
  rewrite (_ : (0 <= _) = (Ke * expR (-Ke * t) <= Ka * expR (- Ka * t)));
  last by lra.
  rewrite -ler_ln.
  rewrite !lnM //=.
  rewrite !expRK.
  rewrite (_ : (_ <= _) = (((Ka - Ke) * t) <= ((ln Ka - ln Ke))));
  last lra.
  rewrite -ln_div => //.
  rewrite -(@ler_pM2l _ ((Ka - Ke)^-1));
  last by rewrite invr_gt0; lra.
  rewrite mulrC -mulrA mulrC -mulrA (mulVf Ke_n_Ka) mulr1 mulrC.
  apply/ltW.
  move: Ht.
  by rewrite in_itv /= /dCdt_root.
  (* This goal is so obvious for (Ka - Ke) but no lemma exists apparently. I have looked over order to try and find something, but no luck *)
  by apply/expR_gt0.
  by apply/expR_gt0.
  apply mulr_gt0 => //.
  by apply/expR_gt0.
  apply mulr_gt0 => //.
  by apply/expR_gt0.
  apply/ler_nmul_pos.
  rewrite -(mulr0 (D * Ka)).
  apply/ltr_pmul_pos.
  rewrite -(mulr0 D).
  by apply/ltr_pmul_pos.
  rewrite invr_lt0.
  rewrite -(mulr0 Vd).
  by apply/ltr_pmul_pos => //;
                          lra.
  rewrite (_ : (_ <= 0) = (Ka * expR (-Ka * t) <= Ke * expR (- Ke * t)));
  last by lra.
  rewrite -ler_ln.
  rewrite !lnM //=.
  rewrite !expRK.
  rewrite (_ : (_ <= _) = (((Ke - Ka) * t) <= ((ln Ke - ln Ka))));
  last lra.
  rewrite -ln_div => //.
  rewrite -(@ler_pM2l _ ((Ke - Ka)^-1));
  last by rewrite invr_gt0; lra.
  rewrite mulrC -mulrA mulrC -mulrA mulVf;
  last lra.
  rewrite mulr1 mulrC.
  rewrite -(invrK (Ke / Ka)) lnV invf_div.
  rewrite mulNr -divrN opprB.
  apply/ltW.
  move: Ht.
  by rewrite in_itv /= /dCdt_root.
  by apply/divr_gt0.
  (* This goal is so obvious for (Ka - Ke) but no lemma exists apparently. I have looked over order to try and find something, but no luck *)
  by apply expR_gt0.
  by apply expR_gt0.
  apply mulr_gt0 => //.
  by apply expR_gt0.
  apply mulr_gt0 => //.
  by apply expR_gt0.
  move/eqP: Ke_n_Ka.
  lra.
  (* t = 0 *)
  rewrite Ht0 !mulr0 exp.expR0 !mulr1.
  case: (ltgtP Ke Ka) => HKeKa;
  rewrite -(mulr0 (D * Ka / (Vd * (Ka - Ke)))).
  apply/ler_pmul_pos;
  last lra.
  rewrite -(mulr0 (D * Ka)).
  apply/ltr_pmul_pos.
  rewrite -(mulr0 D).
  by apply/ltr_pmul_pos.
  rewrite invr_gt0.
  rewrite -(mulr0 Vd).
  by apply/ltr_pmul_pos => //;
  lra.
  apply/ler_nmul_pos;
  last lra.
  rewrite -(mulr0 (D * Ka)).
  apply/ltr_pmul_pos.
  rewrite -(mulr0 D).
  by apply/ltr_pmul_pos.
  rewrite invr_lt0.
  rewrite -(mulr0 Vd).
  by apply/ltr_pmul_pos => //;
  lra.
  exfalso.
  move/eqP: Ke_n_Ka.
  lra.
Qed.


Lemma deriv_is_neg (D t : R) (HD : 0 < D) (Ht : t \in `]dCdt_root, +oo[%R) :
 ((Concentration D)^`() t <= 0).
Proof.
  rewrite derivative_correct /dCdt.
  rewrite -(mulr0 (D * Ka / (Vd * (Ka - Ke)))).
  case: (ltgtP Ke Ka) => HKeKa.
  apply/ler_pmul_pos.
  rewrite -(mulr0 (D * Ka)).
  apply/ltr_pmul_pos.
  rewrite -(mulr0 D).
  by apply/ltr_pmul_pos.
  rewrite invr_gt0.
  rewrite -(mulr0 Vd).
  by apply/ltr_pmul_pos => //;
  lra.
  rewrite (_ : (_ <= 0) = (Ka * expR (-Ka * t) <= Ke * expR (- Ke * t)));
  last by lra.
  rewrite -ler_ln.
  rewrite !lnM => //.
  rewrite !expRK.
  rewrite (_ : (_ <= _) = (t * (Ke - Ka) <= ln Ke - ln Ka)); last lra.
  rewrite -ln_div => //.
  rewrite -(@ler_nM2l _ ((Ke - Ka)^-1));
  last by rewrite invr_lt0; lra.
  rewrite (mulrC ((Ke - Ka)^-1) (t * _)) -mulrA mulfV;
  last lra.
  rewrite mulr1 mulrC.
  rewrite -(invrK (Ke / Ka)) lnV invf_div.
  rewrite mulNr -divrN opprB.
  apply/ltW.
  move: Ht.
  by rewrite in_itv /= /dCdt_root => /andP [->].
  by apply/divr_gt0.
  (* true but can't find lemma - note that the sign changes because Ke - Ka < 0 *)
  by apply/expR_gt0.
  by apply/expR_gt0.
  apply mulr_gt0 => //.
  by apply/expR_gt0.
  apply mulr_gt0 => //.
  by apply/expR_gt0.

  apply/ler_nmul_pos.
  rewrite -(mulr0 (D * Ka)).
  apply/ltr_pmul_pos.
  rewrite -(mulr0 D).
  by apply/ltr_pmul_pos.
  rewrite invr_lt0.
  rewrite -(mulr0 Vd).
  by apply/ltr_pmul_pos => //;
  lra.
  rewrite (_ : (0 <= _) = (Ke * expR (-Ke * t) <= Ka * expR (- Ka * t)));
  last by lra.
  rewrite -ler_ln.
  rewrite !lnM => //.
  rewrite !expRK.
  rewrite (_ : (_ <= _) = (t * (Ka - Ke) <= ln Ka - ln Ke)); last lra.
  rewrite -ln_div => //.
  rewrite -(@ler_nM2l _ ((Ka - Ke)^-1));
  last by rewrite invr_lt0; lra.
  rewrite (mulrC ((Ka - Ke)^-1) (t * _)) -mulrA mulfV;
  last lra.
  rewrite mulr1 mulrC.
  apply/ltW.
  move: Ht.
  by rewrite in_itv /= /dCdt_root => /andP [->].
  (* true but can't find lemma - note that the sign changes because Ke - Ka < 0 *)
  by apply/expR_gt0.
  by apply/expR_gt0.
  apply mulr_gt0 => //.
  by apply/expR_gt0.
  apply mulr_gt0 => //.
  by apply/expR_gt0.
  move/eqP:Ke_n_Ka.
  lra.
Qed.

Lemma root_is_max (D t : R) (HD : 0 <= D) (Ht : 0 <= t) :
  Concentration D t <= Concentration D dCdt_root.
Proof.
  case: (boolP (D == 0))=> /eqP.
  move=> ->.
  by rewrite /Concentration !mul0r.
  move: HD.
  rewrite le_eqVlt => /orP [/eqP -> //| HD _].
  case: (ltgtP t dCdt_root) => [ | | -> //] Htr.
  apply/(ger0_derive1_ndecrNy) => //.
  move=> x Hx.
  by apply deriv_is_pos.
  apply/derivable_within_continuous => /= t' _.
  rewrite derivable1_diffP.
  by apply conc_diff.
  by apply/ltW.
  apply/(ler0_derive1_nincry) => //.
  move=> x Hx.
  by apply deriv_is_neg.
  apply/derivable_within_continuous => /= t' _.
  rewrite derivable1_diffP.
  by apply conc_diff.
  by apply/ltW.
Qed.

(* Need to say that for the Concentration function, dCdt is the derivative and dCdt_root is the global maximum *)

Definition conc_max (D : R) (HD : 0 <= D) :
  Concentration D dCdt_root = ((D * Ka) / (Vd * (Ka - Ke))) * (expR (-Ke * ((ln (Ka/Ke))/(Ka - Ke))) - expR (-Ka * ((ln (Ka/Ke))/(Ka - Ke)))).
Proof.
  by case (boolP (D == 0)).
Qed.

(** Time to dose **)
Variables ttd : R.

Hypothesis ttd_pos : ttd > 0.

Definition total_conc {n} (Ds : n.-tuple R) (t : R)
  := \sum_(i < n) ((cst 0) \max (Concentration (tnth Ds i)) \o (shift (-ttd * i%:R))) t.

Definition total_conc_diff n (Ds : n.-tuple R) (t : R)
  := \sum_(i < n) (fun x : R => if 0 < Concentration (tnth Ds i) x then (dCdt (tnth Ds i) x) else 0) (t - ttd * i%:R).

Lemma continuous_shift (f : R -> R) (k : R) (H : continuous f) : continuous (f \o (shift k)).
Proof.
  move=> x.
  apply: continuous_comp;
  last by apply H.
  apply/continuousD;
  last by apply:(near_cst_continuous k);
  by near=> t.
  apply/differentiable_continuous /derivable1_diffP /derivable_id.
  Unshelve.
  end_near.
Qed.

Lemma sum_apply {n} (f : 'I_n -> R -> R) :
  (fun t => \sum_(i < n) f i t) = \sum_(i < n) (fun t => f i t).
Proof.
  move: n f.
  elim.
  move=> f.
  apply funext => t.
  by rewrite !big_ord0.
  move=> n IHn f.
  apply funext => t.
  rewrite !big_ord_recr /=.
  move: IHn => /(_ (fun i : 'I_n => f (widen_ord (leqnSn n) i))) IHn.
  by rewrite -IHn.
Qed.

Lemma continuous_sum {n} (f : 'I_n -> R -> R) : (forall i : 'I_n, continuous (f i)) -> continuous (fun t => \sum_(i < n) f i t).
Proof.
  rewrite /=.
  rewrite sum_apply.
  move: n f.
  elim => [f H x | n IHf f H x].
  rewrite big_ord0.
  apply/cst_continuous.
  rewrite big_ord_recr /=.
  apply/continuousD;
  last by apply H.
  apply/IHf.
  by move=> i;
  apply H.
Qed.

Lemma differentiable_sum {n} (f : 'I_n -> R -> R) (t : R) :
  (forall i : 'I_n, differentiable (f i) t) -> differentiable (\sum_(i < n) f i) t.
Proof.
  move: n f.
  elim => [f H | n IHf f H].
  rewrite big_ord0.
  apply differentiable_cst.
  rewrite big_ord_recr /=.
  rewrite -derivable1_diffP.
  apply derivableD.
  rewrite derivable1_diffP.
  apply IHf.
  move=> i.
  apply H.
  rewrite derivable1_diffP.
  apply H.
Qed.

Lemma derive_sum {n} (f : 'I_n -> R -> R) (t : R) :
  (forall i : 'I_n, differentiable (f i) t) -> 'D_1 (fun t => \sum_(i < n) f i t) t = \sum_(i < n) ('D_1 (f i) t).
Proof.
  rewrite /=.
  rewrite sum_apply.
  move: n f.
  elim => [f H | n IHf f H].
  by rewrite !big_ord0 derive_cst.
  rewrite !big_ord_recr /=.
  rewrite deriveD.
  by rewrite IHf => //=.
  rewrite derivable1_diffP.
  apply differentiable_sum.
  move=> i.
  apply H.
  rewrite derivable1_diffP.
  apply H.
Qed.



Lemma total_conc_cont {n} (Ds : n.-tuple R) (x : R):
  continuous (total_conc Ds).
Proof.
  rewrite /total_conc.
  apply continuous_sum.
  move=> i.
  apply/continuous_shift /max_fun_continuous.
  apply/cst_continuous.
  apply/conc_cont.
Qed.

Lemma max_diffl (f g : R -> R) (t : R) (H : f t > g t) (Hf : continuous_at t f) (Hg : continuous_at t g) :
  (f \max g)^`() t = f^`() t.
Proof.
  rewrite !derive1E.
  apply near_eq_derive.
  apply/eqP.
  lra.
  rewrite /Order.max_fun /maxr.
  near=> x.
  rewrite ifN => //.
  rewrite -leNgt.
  rewrite (_ : (g x <= f x) = ((g - f) x <= 0));
  last by rewrite subr_le0.
  near: x.
  apply:cvgr_le;
  last first.
  rewrite -subr_lt0 in H.
  by apply H.
  by apply:cvgB.
  Unshelve.
  end_near.
Qed.

Lemma max_diffr (f g : R -> R) (t : R) (H : f t < g t) (Hf : continuous_at t f) (Hg : continuous_at t g) :
  (f \max g)^`() t = g^`() t.
Proof.
  rewrite !derive1E.
  apply near_eq_derive=> //=.
  lra.
  rewrite /Order.max_fun /maxr.
  near=> x.
  rewrite ifT => //.
  rewrite (_ : f x < g x = ((f - g) x < 0));
  last by rewrite subr_lt0.
  near: x.
  apply: cvgr_lt;
  last first.
  rewrite -subr_lt0 in H.
  apply H.
  by apply:cvgB.
  Unshelve.
  end_near.
Qed.

Lemma differentiable_max (f g : R -> R) (t : R) (H : f t <> g t) (Hf : differentiable f t) (Hg : differentiable g t) :
  differentiable (f \max g) t.
Proof.
  case: (ltgtP (f t) (g t))=> // Hfg.
  rewrite /Order.max_fun /maxr.
  rewrite -derivable1_diffP.
  rewrite /derivable.
  rewrite Hfg.
  have Hnear : \forall x \near nbhs 0^', (f (x%:A + t)%E < g (x%:A + t)%E)%R.
  near=> x.
  rewrite scaler1.
  rewrite - subr_lt0.
  rewrite (_ : f (x + t) - _ = ((f - g) \o shift t) x) => //.
  near: x.
  apply/cvgr_lt;
  last first.
  move: Hfg.
  rewrite -subr_lt0.
  by apply.
  apply:cvgB;
  rewrite cvgr_dnbhsP;
  move=> u [Hne Hu].
(* ∞ *)
  have Hshift : u n + t @[n --> \oo] --> t.
  rewrite -(add0r t).
  apply:cvgD.
  apply Hu.
  rewrite add0r /=.
  apply:cvg_cst.
  rewrite (_ : f (u n + t)%E @[n--> \oo] = (f \o shift t) (u n) @[n --> \oo]) => //=.
  rewrite //=.
  apply: cvg_comp.
  apply Hshift.
  move:Hf => /differentiable_continuous.
  by apply.
  have Hshift : u n + t @[n --> \oo] --> t.
  rewrite -(add0r t).
  apply:cvgD.
  by apply Hu.
  rewrite add0r /=.
  by apply:cvg_cst.
  rewrite (_ : g (u n + t)%E @[n--> \oo] = (g \o shift t) (u n) @[n --> \oo]) => //=.
  rewrite //=.
  apply: cvg_comp.
  by apply Hshift.
  move:Hg => /differentiable_continuous.
  by apply.
  (* have stops here *)
  rewrite (_ : (h^-1 *: (((fun x : R => if (f x < g x)%R then g x else f x) \o shift t) h%:A - g t) @[h --> 0^']) = (fun x => x^-1 *: (shift (- g t) \o (g \o shift t)) x%:A) h @[h --> 0^']).
  move: Hg.
  rewrite -derivable1_diffP /derivable /=.
  by apply.
  apply/funext => /= x.
  apply/propext;
  split.
  apply: near_eq_cvg.
  near=> x'.
  rewrite ifT //=.
  near: x'.
  apply Hnear.
  apply: near_eq_cvg.
  near=> x'.
  rewrite ifT //=.
  near: x'.
  by apply Hnear.
  (* end of first half *)
  rewrite /Order.max_fun /maxr.
  rewrite -derivable1_diffP.
  rewrite /derivable.
  have := Hfg.
  rewrite ltNge le_eqVlt negb_or => /andP [_ Hfg'].
  rewrite ifN //.
  have Hnear : \forall x \near nbhs 0^', ~~ (f (x%:A + t)%E < g (x%:A + t)%E)%R.
  near=> x.
  rewrite ltNge negbK.
  rewrite scaler1.
  rewrite - subr_le0.
  rewrite (_ : g (x + t) - _ = ((g - f) \o shift t) x) => //.
  near: x.
  apply/cvgr_le;
  last first.
  move: Hfg.
  rewrite -subr_lt0.
  by apply.
  apply:cvgB;
  rewrite cvgr_dnbhsP;
  move=> u [Hne Hu].
(* ∞ *)
  have Hshift : u n + t @[n --> \oo] --> t.
  rewrite -(add0r t).
  apply:cvgD.
  apply Hu.
  rewrite add0r /=.
  apply:cvg_cst.
  rewrite (_ : g (u n + t)%E @[n--> \oo] = (g \o shift t) (u n) @[n --> \oo]) => //=.
  rewrite //=.
  apply: cvg_comp.
  apply Hshift.
  move:Hg => /differentiable_continuous.
  by apply.
  have Hshift : u n + t @[n --> \oo] --> t.
  rewrite -(add0r t).
  apply:cvgD.
  by apply Hu.
  rewrite add0r /=.
  by apply:cvg_cst.
  rewrite (_ : f (u n + t)%E @[n--> \oo] = (f \o shift t) (u n) @[n --> \oo]) => //=.
  rewrite //=.
  apply: cvg_comp.
  by apply Hshift.
  move:Hf => /differentiable_continuous.
  by apply.
  (* have stops here *)
  rewrite (_ : (h^-1 *: (((fun x : R => if (f x < g x)%R then g x else f x) \o shift t) h%:A - f t) @[h --> 0^']) = (fun x => x^-1 *: (shift (- f t) \o (f \o shift t)) x%:A) h @[h --> 0^']).
  move: Hf.
  rewrite -derivable1_diffP /derivable /=.
  by apply.
  apply/funext => /= x.
  apply/propext;
  split.
  apply: near_eq_cvg.
  near=> x'.
  rewrite ifN //=.
  near: x'.
  apply Hnear.
  apply: near_eq_cvg.
  near=> x'.
  rewrite ifN //=.
  near: x'.
  by apply Hnear.
  Unshelve.
  all: end_near.
Qed.


Lemma total_conc_diff_correct n (t : R) (Ds : n.-tuple R) (HDs : all [pred x | 0 < x] Ds) (Ht : forall m : nat, t <> ttd * m%:R) :
  (total_conc Ds)^`() t = total_conc_diff Ds t.
  rewrite derive1E /total_conc.
  rewrite derive_sum.
  rewrite /total_conc_diff.
  apply/eq_bigr => i _.
  case (ltgtP 0 (Concentration (tnth Ds i) (t - ttd * i %:R))) => /eqP /eqP H.
  rewrite H.
  rewrite -derive1E.
  rewrite derive1_comp //.
  rewrite derive1_id mulr1 // derive1_comp //.
  rewrite !derive1E /= deriveD // derive_id derive_cst addr0 mulr1.
  rewrite -derive1E.
  rewrite max_diffr /=.
  rewrite derivative_correct /=.
  by rewrite (_ : t + (- ttd * i%:R) = t - ttd * i%:R);
  last ring.
  by rewrite (_ : t + (- ttd * i%:R) = t - ttd * i%:R);
  last ring.
  apply:cst_continuous.
  apply conc_cont.
  rewrite derivable1_diffP.
  apply differentiable_max.
  rewrite /=.
  apply/eqP.
  rewrite eq_sym.
  rewrite lt0r_neq0 //.
  by rewrite (_ : t + (- ttd * i%:R) = t - ttd * i%:R);
  last ring.
  apply differentiable_cst.
  apply conc_diff.
  rewrite derivable1_diffP.
  apply differentiable_comp.
  have := is_derive_shift t 1 (-ttd * i%:R).
  by case.
  apply/differentiable_max.
  rewrite /=.
  apply/eqP.
  rewrite eq_sym.
  rewrite lt0r_neq0 //.
  by rewrite (_ : t + (- ttd * i%:R) = t - ttd * i%:R);
  last ring.
  apply differentiable_cst.
  apply conc_diff.
  rewrite ifF.
  rewrite -derive1E derive1_comp //.
  rewrite !derive1E derive_id mulr1 -derive1E derive1_comp //.
  rewrite !derive1E /= deriveD // derive_id derive_cst addr0 mulr1.
  rewrite -derive1E.
  rewrite max_diffl.
  by rewrite derive1_cst.
  rewrite /=.
  by rewrite (_ : t + (- ttd * i%:R) = t - ttd * i%:R);
  last ring.
  apply:cst_continuous.
  apply conc_cont.
  rewrite derivable1_diffP.
  apply:differentiable_max => [/= | // | ].
  apply/eqP.
  rewrite eq_sym.
  rewrite ltr0_neq0 //.
  by rewrite (_ : t + (- ttd * i%:R) = t - ttd * i%:R);
  last ring.
  apply/conc_diff.
  rewrite derivable1_diffP.
  apply/differentiable_max => [/= | // | ].
  apply/eqP.
  rewrite eq_sym.
  rewrite ltr0_neq0 //.
  by rewrite (_ : t + (- ttd * i%:R) = t - ttd * i%:R);
  last ring.
  apply/differentiable_comp => [// | ].
  apply/conc_diff.
  lra.
  exfalso.
  apply (Ht i).
  move: H.
  rewrite /Concentration.
  move=> /eqP.
  rewrite eq_sym => /eqP.
  rewrite mulr0I.
  move=> /subr0_eq /expR_inj /eqP.
  rewrite -subr_eq0 => /= /eqP.
  rewrite (_ : - Ke * _ - _ * _ = (Ka - Ke) * (t - ttd * i%:R));
  last lra.
  move=> /eqP.
  rewrite mulrI_eq0 => [/eqP | ];
  last by apply mulfI.
  lra.
  rewrite unitrM.
  apply/andP.
  split.
  rewrite unitrM.
  apply/andP.
  split.
  apply/unitrPr.
  exists (tnth Ds i)^-1.
  rewrite mulfV //.
  apply lt0r_neq0.
  move: HDs => /allP.
  by move=> /(_ (tnth Ds i) (mem_tnth i Ds)) /=.
  apply/unitrPr.
  exists Ka^-1.
  rewrite mulfV //.
  by apply lt0r_neq0.
  rewrite unitrV unitrM.
  apply/andP.
  split.
  apply/unitrPr.
  exists Vd^-1.
  rewrite mulfV //.
  by apply lt0r_neq0.
  apply/unitrPr.
  exists (Ka - Ke)^-1.
  rewrite mulfV //.
  move=> i.
  apply/differentiable_comp => //.
  apply/differentiable_comp => //.
  apply/differentiable_max => /=.
  rewrite /Concentration.
  symmetry.
  rewrite mulr0I.
  move=> /subr0_eq/expR_inj /= /eqP.
  rewrite -subr_eq0.
  rewrite (_ : - Ke * _ - - _ * _ = (Ka - Ke) * (t - ttd * i%:R));
  last lra.
  rewrite mulrI_eq0  => [/eqP | ];
           last by apply mulfI.
  move=> /subr0_eq.
  by apply/(Ht i).
  rewrite unitrM unitrV unitrM unitrM.
  apply/and3P.
  split.
  apply/andP.
  split.
  apply/unitrPr.
  exists (tnth Ds i)^-1.
  rewrite mulfV //.
  apply/lt0r_neq0.
  by move: HDs => /allP /(_ (tnth Ds i) (mem_tnth i Ds)).
  apply/unitrPr.
  exists Ka^-1.
  rewrite mulfV //.
  by apply/lt0r_neq0.
  apply/unitrPr.
  exists Vd^-1.
  rewrite mulfV //.
  by apply/lt0r_neq0.
  apply/unitrPr.
  exists (Ka - Ke)^-1.
  rewrite mulfV //.
  apply/differentiable_cst.
  apply conc_diff.
Qed.

(* Reduced network because im only reasoning on the concentration atm *)
Parameter network : R -> R.

Axiom safe : forall C : R, 0 <= C + (Concentration (network C) dCdt_root) <= 30.
Axiom non_neg : forall C : R, 0 <= network C.

Fixpoint n_doses (initial : R) (n : nat) : n.+1.-tuple R :=
  match n with
  | 0 => [:: (network initial)]
  | n'.+1 =>
      let Doses := n_doses initial n' in
      rcons Doses (network (total_conc Doses (ttd *+ (n'.+1))))
  end.

Lemma unfold_n_dose_once {n} (initial t : R) :
  total_conc (n_doses initial n.+1) t = total_conc (n_doses initial n) t + maxr 0 (Concentration (network (total_conc (n_doses initial n) t)) t).
Proof.
  rewrite /total_conc big_ord_recr /total_conc /=.
  rewrite (_ : (tnth
(rcons (n_doses initial n)
(network (total_conc (n_doses initial n) (ttd *+ n.+1))))
ord_max) = network (total_conc (n_doses initial n) (ttd *+ n.+1)));
  last by rewrite (tnth_nth (network initial)) /= nth_rcons ifF ?ifT // size_tuple // -(ltxx (n.+1)).
  rewrite /total_conc /=.
  set C := maxr 0%R _.
Admitted.


Theorem doses_safe (n : nat) (initial t : R) (HC : 0 <= initial) (Ht : 0 <= t) :
  total_conc (n_doses initial n) t <= 30.
Proof.
  move: n.
  elim.
  rewrite //= /total_conc big_ord1 /= (tnth_nth 0) /= mulr0 addr0 /maxr.
  case: (ltgtP 0 (Concentration (network initial) t)) => // _.
  have := (safe initial) => /andP [H H'].
  apply/le_trans;
  last first.
  apply H'.
  rewrite -(addr0 (Concentration (network initial) t)) addrC.
  apply/lerD => //.
  apply root_is_max => //=.
  apply/non_neg.
  move=> n IHn.
  rewrite unfold_n_dose_once /=.
  set C' := (Concentration (network (total_conc (n_doses initial n) t)) t).
  case (ltgtP 0 C').
  rewrite /maxr => ->.
  rewrite /C'.
  have := (safe (total_conc (n_doses initial n) t)) => /andP [_].
  apply: le_trans.
  rewrite (_ : (_ <= _) = ((
                             Concentration (network (total_conc (n_doses initial n) t)) t) <= (
                                                                                                            Concentration (network (total_conc (n_doses initial n) t)) dCdt_root)));
  last lra.
  apply root_is_max => //.
  apply non_neg.
  move=> HC'.
  rewrite /maxr.
  rewrite ifN.
  rewrite addr0.
  apply IHn.
  rewrite ltNge negbK le_eqVlt.
  apply/orP.
  by right.
  move=> HC'.
  rewrite /maxr.
  rewrite ifN.
  rewrite addr0.
  apply IHn.
  rewrite ltNge negbK le_eqVlt.
  apply/orP.
  left.
  lra.
Qed.



(* Definition healthyInput s := *)
(*   [/\ 0 <= s.(C) <= 30 *)
(*     , 36 <= s.(T) <= 38 *)
(*     , 4 <= s.(wbc) <= 12 *)
(*     , 18 <= s.(age) <= 89 *)
(*       & 50 <= s.(weight) <= 100 *)
(*       /\ ( (s.(sex) = 0) \/ (s.(sex) = 1)) *)
(*   ]. *)

(* Definition healthyInputB s := *)
(*   [&& 0 <= s.(C) <= 30 *)
(*     , 36 <= s.(T) <= 38 *)
(*     , 4 <= s.(wbc) <= 12 *)
(*     , 18 <= s.(age) <= 89 *)
(*       & (50 <= s.(weight) <= 100) *)
(*         && ( (s.(sex) == 0) || (s.(sex) == 1)) *)
(*   ]. *)

(* Lemma healthyInputP (s : state) : *)
(*   reflect (healthyInput s) (healthyInputB s). *)
(* Proof. *)
(*   apply: (iffP andP); *)
(*   rewrite /healthyInput. *)
(*   move=> [H /and5P [H0 H1 H2 H3 /orP [H4 | H4]]]; *)
(*          split => [//|//|//|//|]; *)
(*                   split=>[//|]. *)
(*   left. *)
(*   by apply/eqP. *)
(*   right. *)
(*   by apply/eqP. *)
(*   move=> [H0 H1 H2 H3 [H4 [H5 | H5]]]; *)
(*          split=> [//|]; *)
(*                  apply/and5P; *)
(*                  split => [//|//|//|//|]; *)
(*                           apply/orP. *)
(*   left. *)
(*   by apply/eqP. *)
(*   right. *)
(*   by apply/eqP. *)
(* Qed. *)

(* Definition Vd : R := 10. *)
(* Lemma Vd_pos : 0 < Vd. *)
(* Proof. lra. Qed. *)
(* Definition Ka : R := 4. *)
(* Lemma Ka_pos : 0 < Ka. *)
(* Proof. lra. Qed. *)
(* Definition Ke : R := 3. *)
(* Lemma Ke_pos : 0 < Ke. *)
(* Proof. lra. Qed. *)
(* Lemma Ka_n_Ke : Ka - Ke != 0. *)
(* Proof. apply/eqP. lra. Qed. *)

(* Axiom dose_non_neg : forall s : state, 0 < (controller (state_to_tuple s))^^=0. *)

(* Axiom temp_vehicle_output : forall C : R, forall s : state, healthyInput s -> (controller (state_to_tuple s))^^=0 * (27/640) <= 30. *)

(* Theorem max_dose_limited (s : state) (t : R) (Ht : 0 <= t) : healthyInput s -> Concentration Vd Ke Ka (controller (state_to_tuple s))^^=0 t <= 30. *)
(* Proof. *)
(*   move=> H. *)
(*   set D := (controller (state_to_tuple s))^^=0. *)
(*   have := @root_is_max _ _ _ Vd_pos Ke_pos Ka_pos Ka_n_Ke D t (lt0r_neq0 (dose_non_neg s)). *)
(*   rewrite (conc_max Vd Ke Ka (ltW (dose_non_neg s))). *)
(*   rewrite (_ : (controller (state_to_tuple s))^^=0 * Ka / (Vd * (Ka - Ke)) * *)
(*                  (expR (- Ke * (ln (Ka / Ke) / (Ka - Ke))) - expR (- Ka * (ln (Ka / Ke) / (Ka - Ke)))) = (controller (state_to_tuple s))^^=0 * (Ka / (Vd * (Ka - Ke)) * *)
(*                                                                                                            (expR (- Ke * (ln (Ka / Ke) / (Ka - Ke))) - expR (- Ka * (ln (Ka / Ke) / (Ka - Ke)))))). *)
(*   rewrite (_ : Ka / (Vd * (Ka - Ke)) * *)
(*                  (expR (- Ke * (ln (Ka / Ke) / (Ka - Ke))) - expR (- Ka * (ln (Ka / Ke) / (Ka - Ke)))) = 27 / 640). *)
(*   move=> H'. *)
(*   apply  (le_trans H' (temp_vehicle_output 0 H)). *)
(*   shelve. *)
(*   lra. *)
(*   Admitted. *)
