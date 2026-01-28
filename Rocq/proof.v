From Coq Require Lra.
Tactic Notation "std_lra" := Lra.lra.
From Stdlib Require Import Reals.
From mathcomp Require Import all_boot all_order all_algebra all_classical all_analysis all_reals ring lra Rstruct Rstruct_topology.
From Interval Require Import Tactic.
Require Import vehicle.tensor.
(* From vehicle Require Import tensor. *)
From HB Require Import structures.
Import Num.Theory GRing.Theory Order.POrderTheory.
Import numFieldNormedType.Exports.
(* Import numFieldTopology.Exports. *)

Open Scope order_scope.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Spec.

Notation R := Rdefinitions.R.


Section Theory.

Context {R : realType}.
(* Parameter R : realType. *)
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** All equations and relations **)

(** Body constants, which are strictly positive and [Ka] <> [Ke] **)
Variables (Vd Ke Ka ttd C_safe Ka_under Ka_over Ke_under Ke_over : R).

Hypothesis Vd_pos : Vd > 0.
Hypothesis Ke_pos : Ke > 0.
Hypothesis Ka_pos : Ka > 0.
Hypothesis ttd_pos : ttd > 0.
Hypothesis C_safe_pos : C_safe > 0.
Hypothesis Ke_n_Ka : Ka - Ke != 0.

(* Definition Ke : R := Spec.Ke.[::]. *)
(* Definition Ka : R := Spec.Ka.[::]. *)
(* Definition Vd : R := Spec.Vd.[::]. *)
(* Definition ttd : R := Spec.ttd.[::]. *)
(* Definition C_safe : R := Spec.C_safe.[::]. *)
(* Definition Ka_over : R := Spec.Ka_over.[::]. *)
(* Definition Ka_under : R := Spec.Ka_under.[::]. *)
(* Definition Ke_over: R := Spec.Ke_over.[::]. *)
(* Definition Ke_under : R := Spec.Ke_under.[::]. *)

(** $ \frac{ln(\frac{Ka}{Ke})}{Ka - Ke} $ **)
Definition dCdt_root : R :=
  (ln (Ka/Ke)) / (Ka - Ke).

Hypothesis ttd_dCdt_root : dCdt_root < ttd.


(** $\frac{D\cdot Ka}{Vd \cdot (Ka - Ke)}\cdot (e^{-Ke \cdot t}-e^{-Ka \cdot t})$ **)
Definition Concentration (D t : R) : R :=
  ((D * Ka) / (Vd * (Ka - Ke))) * (expR ((-Ke) * t) - expR ((-Ka) * t)).

Definition conc_f (D : R) : R -> R :=
  cst ((D * Ka) / (Vd * (Ka - Ke))) \* ((expR \o *%R (- Ke)) - (expR \o *%R (- Ka)))%R.

Lemma conc_equiv (D : R) : Concentration D = conc_f D.
Proof.
  apply/funext => t.
  by rewrite /Concentration /conc_f /=.
Qed.

Definition dCdt (D t : R) : R :=
  ((D * Ka / (Vd * (Ka - Ke)))) * (Ka * (expR (-Ka * t)) - Ke * (expR (-Ke * t))).

Definition d2Cdt2 (D t : R) : R :=
  ((D * Ka / (Vd * (Ka - Ke)))) * (Ke^+2 * (expR (-Ke * t)) - Ka^+2 * (expR (-Ka * t))).

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
  apply/mulfV/lt0r_neq0/Ke_pos.
Qed.

Lemma left_is_unit (D : R) (H : D != 0) : D * Ka / (Vd * (Ka - Ke)) \is a GRing.unit.
Proof.
  rewrite unitrM ?unitrV !unitrM.
  apply/and3P.
  split;
  rewrite !unitfE => //.
  apply/andP.
  by split;
  [ | apply/lt0r_neq0/Ka_pos].
  by apply/lt0r_neq0/Vd_pos.
Qed.

Lemma mulr0I {a b : R} : a \is a GRing.unit -> a * b = 0 <-> b = 0.
Proof.
  move=> a1.
  split => H;
  apply/(mulrI a1);
  by rewrite ?H !mulr0.
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
  apply/mulfV/Ke_n_Ka.
  apply/expR_inj.
  rewrite mulr1 lnK;
  last by apply Num.Internals.pos_divr_closed; [apply/Ka_pos|  apply/Ke_pos].
  rewrite mulrBl exp.expRB -expRN.
  apply/(@mulfI _ Ke);
  first by apply/lt0r_neq0/Ke_pos.
  rewrite !mulrA (mulrC Ke Ka) -!mulrA (mulrV unitr_Ke) mulr1 mulrA.
  apply/(@mulfI _ (expR (Ka * t))^-1);
  first by apply/lt0r_neq0; rewrite invr_gt0; apply/expR_gt0.
  by rewrite !mulrA (mulrC (expR _)^-1 Ke) -(mulrA Ke _ _) (mulVr (unitr_n0expR _)) mulrC mulr1 /= -expRN -mulNr mulrC (mulrC (expR _) Ka) -mulNr.
  move=> H0.
  rewrite H0 /dCdt /dCdt_root (mulr0I (left_is_unit H)).
  apply/eqP.
  rewrite subr_eq0.
  apply/eqP/ln_inj;
  (* apply/mulr_gt0. *)
  (* try apply/mulr_gt0 => //; *)
  (*        try apply/expR_gt0. *)
  last first.
  rewrite !lnM //= ?posrE ?Ka_pos ?expR_gt0 ?invr_gt0 ?Ke_pos //.
  rewrite !expRK /= lnV ?posrE ?Ke_pos // !mulrA -(divr1 (ln Ka)).
  rewrite -(divr1 (ln Ke)) !addf_div ?Ke_n_Ka //=; lra.
  all: apply/mulr_gt0; [|apply/expR_gt0].
  by apply/Ke_pos.
  by apply/Ka_pos.
Qed.

Lemma ltr_pmul_pos (a b c : R) : 0 < a -> b < c -> a * b < a * c.
Proof.
  rewrite -(subr_lt0 c b) -(subr_lt0 _ (a * b)) -mulrBr => H.
  by rewrite (pmulr_rlt0 _ H).
Qed.

Lemma ler_pmul_pos (a b c : R) : 0 < a -> b <= c -> a * b <= a * c.
Proof.
  rewrite -(subr_le0 c b) -(subr_le0 _ (a * b)) -mulrBr => H.
  by rewrite (pmulr_rle0 _ H).
Qed.

Lemma ltr_nmul_pos (a b c : R) : a < 0 -> c < b -> a * b < a * c.
Proof.
  rewrite -(subr_gt0 c b) -(subr_lt0 _ (a * b)) -mulrBr => H.
  by rewrite -(nmulr_rlt0 _ H).
Qed.

Lemma ler_nmul_pos (a b c : R) : a <= 0 -> c <= b -> a * b <= a * c.
Proof.
  case: (boolP (a == 0)) => [/eqP -> | /eqP].
  by rewrite !mul0r.
  rewrite le_eqVlt => H /orP [/eqP // | {H}].
  rewrite -(subr_ge0 c b) -(subr_le0 _ (a * b)) -mulrBr => H.
  by rewrite -(nmulr_rle0 _ H).
Qed.

Lemma conc_cont (D : R) :  continuous (Concentration D).
Proof.
  move=> x.
  rewrite conc_equiv.
  apply/continuousM; [apply/cst_continuous | apply/continuousB; [ apply/continuous_comp; [apply/scaler_continuous | apply/continuous_expR] | apply/continuous_comp; [apply/scaler_continuous| apply/continuous_expR]]].
Qed.

Lemma deriv_is_pos (D t : R) (HD : 0 < D) (Ht : t \in `]-oo, dCdt_root[%R) :
  (0 <= (Concentration D)^`() t).
Proof.
  rewrite derivative_correct /dCdt.
  case: (ltgtP t 0) => Ht0.
  case: (ltgtP Ke Ka) => HKeKa.
  rewrite pmulr_rge0.
  rewrite subr_ge0.
  apply/ler_pM; [by apply/ltW/Ke_pos | by apply/expR_ge0 | by apply/ltW | ].
  rewrite ler_expR -subr_le0 addrC !mulNr opprK subr_le0 mulrC (mulrC Ke).
  rewrite ler_nM2l //.
  by apply/ltW.
  apply divr_gt0; rewrite pmulr_lgt0 //.
  by rewrite subr_gt0.
  rewrite nmulr_rge0 ?subr_le0.
  apply/ler_pM; [by apply/ltW/Ka_pos | by apply/expR_ge0 | by apply/ltW | ].
  rewrite ler_expR -subr_le0 addrC !mulNr opprK subr_le0 mulrC (mulrC Ka) ler_nM2l //.
  by apply/ltW.
  rewrite nmulr_llt0.
  by rewrite pmulr_lgt0 ?Ka_pos.
  by rewrite invr_lt0 nmulr_llt0; [apply/Vd_pos | rewrite subr_lt0].
  exfalso.
  move/eqP: Ke_n_Ka.
  lra.
  (* 0 < t *)
  case: (ltgtP Ke Ka) => HKeKa.
  rewrite pmulr_rge0.
  rewrite subr_ge0.
  rewrite -ler_ln ?lnM ?posrE ?pmulr_rgt0 ?expR_gt0 //;
  rewrite ?Ke_pos ?Ka_pos //.
  rewrite !expRK -subr_le0 !mulNr.
  rewrite (_ : (ln Ke - Ke * t - (ln Ka - Ka * t)) = (- (ln Ka - ln Ke) + Ka * t - Ke * t)); last lra.
  rewrite -ln_div ?posrE ?Ka_pos ?Ke_pos // -mulNr -addrA -mulrDl addrC subr_le0.
  rewrite -(@ler_pM2l _ ((Ka - Ke)^-1));
  last by rewrite invr_gt0; lra.
  rewrite (mulrC (Ka - Ke) t) mulrA (mulrC _ t) -mulrA mulVf.
  rewrite mulr1 mulrC.
  apply/ltW.
  move: Ht.
  by rewrite in_itv //= /dCdt_root.
  lra.
  rewrite pmulr_rgt0.
  rewrite invr_gt0 pmulr_rgt0 ?Vd_pos //.
  lra.
  by rewrite pmulr_rgt0 ?Ka_pos.
  rewrite nmulr_rge0.
  rewrite subr_le0.
  rewrite -ler_ln ?lnM ?posrE ?pmulr_rgt0 ?expR_gt0 ?Ka_pos ?Ke_pos // !expRK.
  rewrite -subr_le0 !mulNr.
  rewrite (_ : (ln Ka - Ka * t - (ln Ke - Ke * t)) = ((ln Ka - ln Ke) - (Ka * t - Ke * t))); last lra.
  rewrite -ln_div ?posrE ?Ka_pos ?Ke_pos // -mulNr -mulrDl subr_le0.
  rewrite -(@ler_nM2l _ ((Ka - Ke)^-1));
  last by rewrite invr_lt0; lra.
  rewrite mulrA (mulrC _ t) mulVf.
  rewrite mulr1 mulrC.
  apply/ltW.
  move: Ht.
  by rewrite in_itv //= /dCdt_root.
  lra.
  rewrite pmulr_rlt0.
  rewrite invr_lt0 pmulr_rlt0 ?Vd_pos //.
  lra.
  by rewrite pmulr_rgt0 ?Ka_pos.
  exfalso.
  move/eqP: Ke_n_Ka.
  lra.
  (* t = 0 *)
  rewrite Ht0 !mulr0 exp.expR0 !mulr1.
  case: (ltgtP Ke Ka) => HKeKa.
  rewrite pmulr_rge0.
  by apply/ltW; rewrite subr_gt0.
  rewrite pmulr_rgt0.
  rewrite invr_gt0 pmulr_rgt0 ?Vd_pos // subr_gt0.
  lra.
  by rewrite pmulr_rgt0 ?Ka_pos.
  rewrite nmulr_rge0.
  by apply/ltW; rewrite subr_lt0.
  rewrite pmulr_rlt0.
  by rewrite invr_lt0 pmulr_rlt0 ?Vd_pos // subr_lt0.
  by rewrite pmulr_rgt0 ?Ka_pos.
  exfalso.
  move/eqP: Ke_n_Ka.
  lra.
Qed.

Lemma conc_D0 : Concentration 0 = 0.
Proof.
  apply funext => t.
  by rewrite /Concentration !mul0r.
Qed.

Lemma deriv_is_non_pos (D t : R) (HD : 0 <= D) (Ht : t \in `]dCdt_root, +oo[%R) :
 ((Concentration D)^`() t <= 0).
Proof.
  case: (boolP (0 == D)) => [/eqP <- | /eqP H].
  by rewrite conc_D0 derive1_cst.
  move:HD.
  rewrite le_eqVlt => /orP [/eqP // | ] {H} HD.
  rewrite derivative_correct /dCdt.
  case: (ltgtP Ke Ka) => HKeKa.
  rewrite pmulr_rle0.
  rewrite subr_le0.
  rewrite -ler_ln ?lnM ?posrE ?pmulr_rgt0 ?expR_gt0 ?Ka_pos ?Ke_pos // !expRK.
  rewrite -subr_le0 !mulNr.
  rewrite (_ : (ln Ka - Ka * t - (ln Ke - Ke * t)) = ((ln Ka - ln Ke) - (Ka * t - Ke * t))); last lra.
  rewrite -ln_div ?posrE ?Ka_pos ?Ke_pos // -mulNr -mulrDl subr_le0.
  rewrite -(@ler_pM2l _ ((Ka - Ke)^-1));
  last by rewrite invr_gt0; lra.
  rewrite (mulrC (Ka - Ke) t) mulrA (mulrC _ t) -mulrA mulVf.
  rewrite mulr1 mulrC.
  apply/ltW.
  move: Ht.
  by rewrite in_itv //= /dCdt_root => /andP [].
  lra.
  rewrite pmulr_rgt0.
  rewrite invr_gt0 pmulr_rgt0 ?Vd_pos //.
  lra.
  by rewrite pmulr_rgt0 ?Ka_pos.
  rewrite nmulr_rle0.
  rewrite subr_ge0.
  rewrite -ler_ln ?lnM ?posrE ?pmulr_rgt0 ?expR_gt0 ?Ka_pos ?Ke_pos // !expRK.
  rewrite -subr_le0 !mulNr.
  rewrite (_ : (ln Ke - Ke * t - (ln Ka - Ka * t)) = (-(ln Ka - ln Ke) + (Ka * t - Ke * t))); last lra.
  rewrite -ln_div ?posrE ?Ka_pos ?Ke_pos // -mulNr -mulrDl addrC subr_le0.
  rewrite -(@ler_nM2l _ ((Ka - Ke)^-1));
  last by rewrite invr_lt0; lra.
  rewrite mulrA (mulrC _ t) mulVf.
  rewrite mulr1 mulrC.
  apply/ltW.
  move: Ht.
  by rewrite in_itv //= /dCdt_root => /andP [].
  lra.
  rewrite pmulr_rlt0.
  rewrite invr_lt0 pmulr_rlt0 ?Vd_pos //.
  lra.
  by rewrite pmulr_rgt0 ?Ka_pos.
  exfalso.
  move/eqP: Ke_n_Ka.
  lra.
Qed.

Lemma conc_neg (D t : R) : 0 < D -> t < 0 -> Concentration D t < 0.
Proof.
  move=> HD Ht.
  rewrite /Concentration.
  move: Ke_n_Ka.
  case: (ltgtP Ke Ka) => [ HKeKa _ | HKeKa _ | ->]; last lra.
  rewrite pmulr_rlt0.
  rewrite subr_lt0 ltr_expR mulrC (mulrC (- Ka)).
  apply/ltr_nmul_pos => //.
  lra.
  rewrite pmulr_rgt0.
  by rewrite invr_gt0 pmulr_rgt0 ?Vd_pos // subr_gt0.
  by rewrite pmulr_rgt0 ?Ka_pos.
  rewrite nmulr_rlt0.
  rewrite subr_gt0 ltr_expR mulrC (mulrC (-Ke)).
  apply/ltr_nmul_pos => //.
  lra.
  rewrite pmulr_rlt0.
  by rewrite invr_lt0 pmulr_rlt0 ?Vd_pos // subr_lt0.
  by rewrite pmulr_rgt0 ?Ka_pos.
Qed.

Lemma conc_non_neg (D t : R) : 0 <= D -> 0 <= t -> 0 <= Concentration D t.
Proof.
  move=> HD Ht.
  rewrite /Concentration.
  case (boolP (D == 0)) => [/eqP -> | ];
                          first by rewrite !mul0r lexx.
  case (boolP (t == 0)) => [/eqP -> | ].
  by rewrite !mulr0 !exp.expR0 subrr mulr0 lexx.
  move: Ht.
  rewrite le_eqVlt => /orP [/eqP -> /eqP //| Ht _].
  move: HD.
  rewrite le_eqVlt => /orP [/eqP -> /eqP // | HD _].
  case: (ltgtP Ke Ka) => HKeKa.
  rewrite pmulr_rge0.
  rewrite subr_ge0 ler_expR -subr_ge0 addrC mulNr opprK -mulrDl pmulr_rge0;
  [ by apply/ltW
  | by rewrite subr_gt0].
  rewrite pmulr_rgt0.
  by rewrite ?invr_gt0 pmulr_rgt0 ?Vd_pos // subr_gt0.
  by rewrite pmulr_rgt0 ?Ka_pos.
  rewrite nmulr_rge0.
  rewrite subr_le0 ler_expR -subr_ge0 addrC mulNr opprK -mulrDl pmulr_rge0;
  [ by apply/ltW
  | by rewrite subr_gt0].
  rewrite pmulr_rlt0.
  by rewrite invr_lt0 pmulr_rlt0 ?Vd_pos // subr_lt0.
  by rewrite pmulr_rgt0 ?Ka_pos.
  move: Ke_n_Ka.
  rewrite HKeKa.
  lra.
Qed.

Lemma conc_t0 (D : R) : Concentration D 0 = 0.
Proof.
  rewrite /Concentration !mulr0 !exp.expR0.
  lra.
Qed.

Lemma conc_pos (D t : R) : 0 < D -> 0 < t -> 0 < Concentration D t.
Proof.
  move=> HD Ht.
  rewrite /Concentration.
  case: (ltgtP Ke Ka) => H.
  rewrite pmulr_rgt0.
  by rewrite subr_gt0 ltr_expR -subr_gt0 addrC mulNr opprK -mulrDl pmulr_rgt0 // subr_gt0.
  rewrite pmulr_rgt0.
  by rewrite invr_gt0 pmulr_rgt0 ?Vd_pos // subr_gt0.
  by rewrite pmulr_rgt0 ?Ka_pos.
  rewrite nmulr_rgt0.
  by rewrite subr_lt0 ltr_expR -subr_lt0 addrC mulNr opprK -mulrDl nmulr_rlt0 // subr_lt0.
  rewrite pmulr_rlt0.
  by rewrite invr_lt0 pmulr_rlt0 ?Vd_pos // subr_lt0.
  by rewrite pmulr_rgt0 ?Ka_pos.
  move: Ke_n_Ka.
  lra.
Qed.

Lemma conc_non_pos (D t : R) : 0 <= D -> t <= 0 -> Concentration D t <= 0.
Proof.
  rewrite le_eqVlt => /orP [/eqP <- _| HD ].
  by rewrite conc_D0.
  rewrite le_eqVlt => /orP [/eqP -> | Ht].
  by rewrite conc_t0.
  by apply/ltW/conc_neg.
Qed.



Lemma root_is_max (D t : R) (HD : 0 <= D) :
  Concentration D t <= Concentration D dCdt_root.
Proof.
  case: (boolP (0 <= t)) => Ht.
  case: (boolP (D == 0))=> [/eqP -> | /eqP ].
  by rewrite conc_D0.
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
  by apply deriv_is_non_pos => //; apply/ltW.
  apply/derivable_within_continuous => /= t' _.
  rewrite derivable1_diffP.
  by apply conc_diff.
  by apply/ltW.
  move:Ht.
  rewrite -ltNge => Ht.
  apply/le_trans.
  apply/conc_non_pos => //.
  by apply/ltW.
  apply/conc_non_neg => //.
  rewrite /dCdt_root.
  case: (ltgtP Ke Ka) => KeKa.
  apply/divr_ge0.
  apply/ln_ge0.
rewrite ler_pdivlMr // mul1r.
by apply/ltW.
rewrite subr_ge0.
by apply/ltW.
rewrite -(opprK ( ln _)) -lnV.
rewrite mulNr -mulrN -invrN opprB invf_div.
apply/divr_ge0.
apply/ln_ge0.
rewrite ler_pdivlMr // mul1r.
by apply/ltW.
rewrite subr_ge0.
by apply/ltW.
by rewrite posrE ltr_pdivlMr ?mul0r.
move/eqP: Ke_n_Ka.
lra.
Qed.

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
  elim => [f | n IHn f];
  apply funext => t.
  by rewrite !big_ord0.
  rewrite !big_ord_recr /=.
  by rewrite -IHn.
Qed.

(* should be generalised as much as possible *)
(* Lemma continuous_sum {n : nat} {K : numFieldType} {T U : normedModType K} (f : 'I_n -> T -> U) : *)
(*   (forall i : 'I_n, continuous (f i)) -> continuous (\sum_(i < n) f i). *)
(* Proof. *)
(*   move: n f. *)
(*   elim => [f H x | n IHf f H x]. *)
(*   rewrite big_ord0. *)
(*   by apply/cst_continuous. *)
(*   rewrite big_ord_recr /=. *)
(*   apply/continuousD; last by apply H. *)
(*   apply/IHf. *)
(*   by move => i; apply H. *)
(* Qed. *)

Lemma total_conc_cont {n} (Ds : n.-tuple R) :
  continuous (total_conc Ds).
Proof.
  rewrite /total_conc.
  apply/continuous_big.
  apply/tvs.standard_add_continuous.
  move=> i _.
  by apply/continuous_shift /max_fun_continuous; [ apply/cst_continuous | apply/conc_cont].
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
  rewrite ifN // -leNgt -subr_le0.
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
  rewrite ifT // -subr_lt0.
  near: x.
  apply: cvgr_lt;
  last first.
  rewrite -subr_lt0 in H.
  apply H.
  by apply:cvgB.
  Unshelve.
  end_near.
Qed.

Lemma max_eq (f : R -> R) : f \max f = f.
Proof.
  apply funext=> x.
  by rewrite /Order.max_fun /maxr ltxx.
Qed.

Lemma max_swap (f g : R -> R) : f \max g = g \max f.
Proof.
  apply/funext=> x.
  rewrite /Order.max_fun /maxr.
  by case: (ltgtP (f x) (g x)).
Qed.

Lemma maxr_swap (x y : R) : maxr x y = maxr y x.
Proof.
  case (ltgtP x y) => [ | | -> //] H.
  rewrite /maxr ifT // ifN // ltNge negbK.
  by apply/ltW.
  rewrite /maxr ifN ?ifT // ltNge negbK.
  by apply/ltW.
Qed.

(* Should be generalised and maybe added to mathcomp *)
Lemma differentiable_max (f g : R -> R) (t : R) (H : f t <> g t) (Hf : differentiable f t) (Hg : differentiable g t) :
  differentiable (f \max g) t.
Proof.
  case: (ltgtP (f t) (g t))=> // Hfg.
  rewrite /Order.max_fun /maxr -derivable1_diffP /derivable Hfg.
 have Hnear : \forall x \near nbhs 0^', (f (x%:A + t)%E < g (x%:A + t)%E)%R.
  near=> x.
  rewrite scaler1 -subr_lt0.
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
  have Hshift : u n + t @[n --> \oo] --> t.
  rewrite -(add0r t).
  apply:cvgD.
  by apply Hu.
  rewrite add0r /=.
  by apply:cvg_cst.
  rewrite /=.
  apply: cvg_comp.
  by apply Hshift.
  move:Hf => /differentiable_continuous.
  by apply.
  have Hshift : u n + t @[n --> \oo] --> t.
  rewrite -(add0r t).
  apply:cvgD.
  by apply Hu.
  rewrite add0r /=.
  by apply:cvg_cst.
  rewrite (_ : g (u n + t)%E @[n--> \oo] = (g \o shift t) (u n) @[n --> \oo]) => //=.
  apply: cvg_comp.
  by apply Hshift.
  move:Hg => /differentiable_continuous.
  by apply.
  (* have stops here *)
  rewrite (_ : (h^-1 *: (((fun x : R => if (f x < g x)%R then g x else f x) \o shift t) h%:A - g t) @[h --> 0^']) = (fun x => x^-1 *: (shift (- g t) \o (g \o shift t)) x%:A) h @[h --> 0^']).
  move: Hg.
  by rewrite -derivable1_diffP /derivable /=.
  apply/funext => /= x.
  apply/propext;
  split.
  apply: near_eq_cvg.
  near=> x'.
  rewrite ifT //=.
  near: x'.
  by apply Hnear.
  apply: near_eq_cvg.
  near=> x'.
  rewrite ifT //=.
  near: x'.
  by apply Hnear.
  (* end of first half *)
  rewrite /Order.max_fun /maxr -derivable1_diffP /derivable.
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
  apply:(cvgD Hu).
  rewrite add0r /=.
  by apply:cvg_cst.
  rewrite /=.
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

Lemma total_conc_diff_correct n (t : R) (Ds : n.-tuple R) (HDs : all (>= 0) Ds) (Ht : forall m : nat, (m < n)%O -> t <> ttd * m%:R) :
  (total_conc Ds)^`() t = total_conc_diff Ds t.
  rewrite derive1E /total_conc sum_apply derive_sum.
  rewrite /total_conc_diff.
  apply/eq_bigr => i _.
  case (ltgtP 0 (Concentration (tnth Ds i) (t - ttd * i %:R))) => /eqP /eqP H.
  rewrite H.
  rewrite -derive1E derive1_comp //.
  rewrite derive1_id mulr1 // derive1_comp //.
  rewrite !derive1E /= deriveD // derive_id derive_cst addr0 mulr1 -derive1E.
  by rewrite max_diffr /=; [ rewrite derivative_correct mulNr | rewrite mulNr | apply/cst_continuous | apply/conc_cont].
  rewrite derivable1_diffP.
  by apply/differentiable_max; [ apply/eqP; by rewrite eq_sym lt0r_neq0 // mulNr | apply/differentiable_cst | apply/conc_diff].
  rewrite derivable1_diffP.
  apply differentiable_comp => //.
  apply/differentiable_max; [ apply/eqP; by rewrite eq_sym lt0r_neq0 // mulNr | apply/differentiable_cst | apply/conc_diff].
  rewrite ifF.
  rewrite -derive1E derive1_comp //.
  rewrite !derive1E derive_id mulr1 -derive1E derive1_comp //.
  by rewrite !derive1E /= deriveD // derive_id derive_cst addr0 mulr1 -derive1E max_diffl /=;[ by rewrite derive1_cst | by rewrite mulNr | by apply:cst_continuous | by apply conc_cont].
  case: (boolP ((tnth Ds i) == 0)) => [/eqP -> | /eqP HDs_i];
  rewrite derivable1_diffP.
  rewrite conc_D0 max_eq.
  by apply:differentiable_cst.
  by apply:differentiable_max => [/= | // | ];
  [ by apply/eqP;
  rewrite eq_sym ltr0_neq0 // mulNr
  | by apply/conc_diff].
  rewrite derivable1_diffP.
  by apply/differentiable_max => [/= | // | ];
  [ apply/eqP;
  by rewrite eq_sym ltr0_neq0 // mulNr
  | by apply/differentiable_comp; [| apply/conc_diff]].
  lra.
  case: (boolP ((tnth Ds i) == 0)) => /eqP HDs_i.
  rewrite -derive1E derive1_comp //.
  rewrite derive1_id mulr1 derive1_comp => //.
  by rewrite HDs_i conc_D0 max_eq derive1E derive_cst mul0r ifF //.
  rewrite HDs_i conc_D0 derivable1_diffP max_eq.
  by apply differentiable_cst.
  rewrite HDs_i conc_D0 derivable1_diffP max_eq.
  by apply differentiable_cst.
  exfalso.
  apply (Ht i).
  by apply: ltn_ord.
  move: H.
  rewrite /Concentration => /eqP.
  rewrite eq_sym => /eqP.
  rewrite mulr0I.
  move=> /subr0_eq /expR_inj /eqP.
  rewrite -subr_eq0 => /= /eqP.
  rewrite addrC mulNr opprK -mulrDl=> /eqP.
  rewrite mulrI_eq0 => [ /eqP | ];
  [ lra
  | by apply/mulfI/Ke_n_Ka].
  apply/unitrPr.
  exists (tnth Ds i * Ka / (Vd * (Ka - Ke)))^-1.
  apply/mulfV/mulf_neq0;
  [ apply/mulf_neq0; [ by apply/eqP | by apply/lt0r_neq0/Ka_pos] |
  apply/invr_neq0/mulf_neq0; [by apply/lt0r_neq0/Vd_pos | by apply Ke_n_Ka]].
  move=> i.
  rewrite derivable1_diffP.
  apply/differentiable_comp.
  by rewrite -derivable1_diffP; apply/derivable_id.
  apply/differentiable_comp => //.
  case: (boolP ((tnth Ds i) == 0)) => /eqP HDs_i.
  rewrite HDs_i conc_D0 max_eq.
  by apply differentiable_cst.
  rewrite max_swap.
  apply/differentiable_max; [ | by apply/conc_diff | by apply/differentiable_cst].
  rewrite /Concentration.
  apply/eqP/mulf_neq0.
  by apply/mulf_neq0;
  [ apply/mulf_neq0; [ by apply/eqP | by apply/lt0r_neq0/Ka_pos]
  | apply/invr_neq0/mulf_neq0;[ by apply/lt0r_neq0/Vd_pos | by apply Ke_n_Ka]].
  apply/eqP => /subr0_eq/expR_inj /= /eqP.
  rewrite -subr_eq0 addrC mulNr opprK -mulrDl mulNr mulrI_eq0  => [/eqP/subr0_eq | ];
  [ by apply/ (Ht i)/ltn_ord
  | by apply/mulfI/Ke_n_Ka].
Qed.

Lemma total_conc_differentiable {n} (Ds : n.-tuple R) (t : R) (Ht : forall m : nat, (m < n)%O -> t <> ttd * m%:R) (HDs : all (>= 0) Ds) : differentiable (total_conc Ds) t.
Proof.
  rewrite /total_conc.
  rewrite sum_apply.
  rewrite -derivable1_diffP.
  apply derivable_sum => i.
  rewrite derivable1_diffP.
  apply differentiable_comp => //.
  case: (boolP ((tnth Ds i) == 0)) => [/eqP -> | /eqP H'].
  rewrite conc_D0 max_eq.
  by apply differentiable_cst.
  rewrite max_swap.
  apply differentiable_max => /=.
  case (ltgtP t (ttd * i%:R)) => /= H.
  apply/eqP/ltr0_neq0/conc_neg.
  move: HDs => /allP /(_ (tnth Ds i) (mem_tnth i Ds)) /=.
  rewrite le_eqVlt => /orP [ /eqP //= | //=].
  lra.
  lra.
  apply/eqP/lt0r_neq0/conc_pos.
  move: HDs => /allP /(_ (tnth Ds i) (mem_tnth i Ds)) /=.
  rewrite le_eqVlt => /orP [ /eqP //= | //=].
  lra.
  lra.
  move: Ht => /(_ i (ltn_ord i)).
  rewrite H.
  contradiction.
  by apply/conc_diff.
  by apply/derivable1_diffP/derivable_cst.
Qed.

Context {network : R -> R}.

Hypothesis safe : forall C : R, 0 <= C <= C_safe -> C + (Concentration (network C) dCdt_root) <= C_safe.

Hypothesis non_neg : forall C : R, 0 <= C <= C_safe -> 0 <= network C.

Fixpoint n_doses (initial : R) (n : nat) : n.+1.-tuple R :=
  match n with
  | 0 => [:: network initial]
  | n'.+1 =>
      let Doses := n_doses initial n' in
      rcons Doses (network (total_conc Doses (ttd *+ (n'.+1))%R))
  end.

Lemma unfold_n_dose_once {n} (initial t : R) :
  total_conc (n_doses initial n.+1) t = total_conc (n_doses initial n) t + maxr 0 (Concentration (network (total_conc (n_doses initial n) ((ttd * n.+1%:R)%R))) (t + (- ttd * n.+1%:R)%R)).
Proof.
  rewrite /total_conc big_ord_recr /total_conc /=.
  rewrite (tnth_nth (network initial)) /= nth_rcons ifF;
  [ rewrite ifT; [ rewrite /total_conc /= | by rewrite size_tuple] |
  by rewrite size_tuple -(ltxx n.+1)].
  apply f_equal2.
  apply eq_bigr => i _.
  apply f_equal2 => //.
  apply f_equal2 => //.
  by rewrite !(tnth_nth 0) nth_rcons /= size_tuple ifT.
  apply f_equal2 => //.
  apply f_equal2 => //.
  apply f_equal.
  apply eq_bigr => i _.
  apply f_equal2 => //.
  by rewrite -(mulr_natr ttd).
Qed.

Lemma total_conc_non_neg {n : nat} (initial t : R) (Hi : 0 <= initial) (Ht : 0 <= t) :
  all [pred x | 0 <= x] (n_doses initial n) -> 0 <= (total_conc (n_doses initial n) t).
Proof.
  case: (boolP (t == 0)) => [/eqP -> H | Ht'].
  rewrite /total_conc /=.
  rewrite big1 => // i _.
  rewrite /maxr.
  case: ifP => //.
  rewrite ltNge => /negP H'.
  exfalso.
  apply/H'.
  case: (boolP (0 == i)) => [/eqP <- /=| /eqP Hi'];
  rewrite add0r.
  by rewrite mulr0 conc_t0.
  (* by left. *)
  case: (boolP (0 == (tnth (n_doses initial n) i))) => [/eqP <- /= | H''].
  (* left. *)
  by rewrite conc_D0.
  apply/ltW/conc_neg.
  rewrite lt_neqAle.
  apply/andP.
  split => //.
  move/allP : H.
  apply.
  by apply/mem_tnth.
  rewrite pmulr_llt0.
  by rewrite oppr_lt0.
  rewrite lt_neqAle.
  apply/andP.
  split => //=.
  apply/eqP => Hi''.
  apply/Hi'.
  apply/esym/eqP.
  move/esym/eqP:Hi''.
  by rewrite pnatr_eq0.
  move: n.
  elim => [H | n IHn H].
  rewrite /total_conc big_ord1 /=.
  rewrite /maxr.
  case: ifP => //.
  by apply/ltW.
  rewrite /total_conc big_ord_recr /=.
  apply/addr_ge0.
  apply/sumr_ge0 => i _.
  rewrite /maxr.
  case: ifP => //.
  by apply/ltW.
  rewrite /maxr.
  case: ifP => //.
  by apply/ltW.
Qed.

(* Lemma n_doses_pos (n : nat) (initial : R) (Hi : 0 <= initial) : *)
(*   all [pred x | 0 <= x] (n_doses initial n). *)
(* Proof. *)
(*   apply/allP => /=. *)
(*   move: n. *)
(*   elim => /= [n | n IHn x] /=. *)
(*   rewrite mem_seq1 => /eqP ->. *)
(*   by apply/non_neg. *)
(*   rewrite mem_rcons in_cons => /orP [/eqP -> | H]. *)
(*   apply non_neg. *)
(*   apply/total_conc_non_neg => //=. *)
(*   rewrite -mulr_natr. *)
(*   apply/mulr_ge0 => //. *)
(*   by apply/ltW. *)
(*   by apply/allP. *)
(*   by apply IHn. *)
(* Qed. *)

Lemma doses_reduce (n : nat) (i : 'I_n.+1) (initial : R) :
  tnth (n_doses initial n) i = tnth (n_doses initial i) (Ordinal (ltnSn i)).
Proof.
elim: n i => [i | n IHn i ].
by rewrite ord1 /=.
rewrite !(tnth_nth 0) /= nth_rcons.
case: (boolP (i == ord_max)) => [/eqP -> | /eqP H].
  by rewrite nth_rcons size_tuple /= ltnn eqxx.
rewrite size_tuple.
case: ifP => [H' | ].
  have := IHn (Ordinal H').
  by rewrite /= !(tnth_nth 0) /=.
have := ltn_ord i.
rewrite ltnS leq_eqVlt => /orP [-> H' | -> //=].
have := ltn_ord i.
rewrite ltnS leq_eqVlt => /orP [ | //].
  move/eqP: H.
  by rewrite -val_eqE /= => /eqP H /eqP.
by move/negP: H'.
Qed.

Lemma dose_pos (n : nat) (i : 'I_n.+1) (initial : R) (Hi : 0 <= initial <= C_safe) :
  0 <= total_conc (n_doses initial i) (ttd *+ i) <= C_safe ->
  0 <= tnth (n_doses initial n) i.
Proof.
  rewrite doses_reduce.
  rewrite (tnth_nth 0).
  case: i.
  case => [/= _ _ | m Hm H].
  by apply/non_neg.
  rewrite nth_rcons size_tuple /= ltnn eqxx.
  apply/non_neg.
  fold n_doses.
  move: H => /=.
  congr (0 <= _ <= C_safe).
  rewrite /total_conc big_ord_recr /=.
  rewrite (_ : maxr 0%R _ = 0).
  rewrite addr0.
  apply/eq_bigr => i _.
  apply/f_equal2 => //.
  apply/f_equal2 => //.
  by rewrite !(tnth_nth 0) nth_rcons size_tuple /= ltn_ord.
  rewrite -[ttd *+ m.+1]mulr_natr mulNr -mulrBr subrr mulr0 conc_t0.
  by rewrite /maxr ltxx.
  rewrite /total_conc big_ord_recr /=.
  rewrite (_ : maxr 0%R _ = 0).
  rewrite addr0.
  apply/eq_bigr => i _.
  apply/f_equal2 => //.
  apply/f_equal2 => //.
  by rewrite !(tnth_nth 0) nth_rcons size_tuple /= ltn_ord.
  rewrite -[ttd *+ m.+1]mulr_natr mulNr -mulrBr subrr mulr0 conc_t0.
  by rewrite /maxr ltxx.
Qed.

Lemma doses_pos (n : nat) (initial : R) (HC : 0 <= initial <= C_safe) :
    (forall m : nat,
    (m < n.+1)%N -> forall t : R, 0 <= total_conc (n_doses initial m) t <= C_safe) ->
    all (>= 0) (n_doses initial n).
Proof.
  elim: n.
  move=> _.
  apply/andP.
  split => //.
  by apply/non_neg.
  move=> n IHn H.
  apply/allP => /= x.
  rewrite /= mem_rcons in_cons => /orP [/eqP -> |].
  apply/non_neg.
  apply: (H n _ (ttd *+ n.+1)).
  by apply/ltn_trans; apply/ltnSn.
  apply/allP/IHn.
  move=> m Hm t'.
  apply/H.
  apply/ltn_trans.
  by apply/Hm.
  by apply/ltnSn.
Qed.

Theorem doses_safe (n : nat) (initial t : R) (HC : 0 <= initial <= C_safe) :
  0 <= total_conc (n_doses initial n) t <= C_safe.
Proof.
  elim/ltn_ind: n t => n IHn t.
  case: (boolP (t < 0)) => Ht.
  rewrite /total_conc.
  rewrite (_ : \sum_(i < n.+1) _ = 0).
  apply/andP.
  split => //.
  by apply/ltW.
  apply/big1 => /= i _.
  rewrite /maxr ifN //.
  rewrite ltNge negbK.
  apply/conc_non_pos.
  apply/dose_pos => //.
  case: (boolP (n == i)) => [/eqP <- | /eqP].
  case: n IHn i.
  move=> _ _.
  rewrite -mulr_natr mulr0 /total_conc big1.
  apply/andP.
  split => //.
  by apply/ltW.
  move=> i _.
  by rewrite ord1 /= mulr0 addr0 conc_t0 /maxr ltxx.
  move=> n IHn _.
  move: (IHn n (ltnSn n) (ttd *+ n.+1)).
  rewrite /total_conc.
  rewrite [\sum_(i < n.+2) _]big_ord_recr /=.
  rewrite -[ttd *+ n.+1]mulr_natr mulNr -mulrBr subrr mulr0 conc_t0.
  rewrite [in maxr 0 0]/maxr ltxx addr0.
  congr (0 <= _ <= C_safe).
  apply/f_equal3 => //.
  apply/funext=> i.
  apply/f_equal3 => //.
  apply/f_equal2 => //.
  apply/f_equal2 => //.
  by rewrite !(tnth_nth 0) nth_rcons size_tuple /= ltn_ord.
  apply/f_equal3 => //.
  apply/funext=> i.
  apply/f_equal3 => //.
  apply/f_equal2 => //.
  apply/f_equal2 => //.
  by rewrite !(tnth_nth 0) nth_rcons size_tuple /= ltn_ord.
  move=> H.
  apply/IHn.
  have := ltn_ord i.
  by rewrite ltnS leq_eqVlt => /orP [/eqP /esym |].
  rewrite mulNr subr_le0.
  apply/le_trans.
  by apply/ltW/Ht.
  apply/mulr_ge0 => //.
  by apply/ltW.
  rewrite ltNge negbK in Ht.
  case: n IHn => [IHn|].
  rewrite /total_conc.
  rewrite big_ord1 /= (tnth_nth 0) /= mulr0 addr0 /maxr.
  case:ifP => // H.
  apply/andP.
  split.
  apply/conc_non_neg => //.
  by apply/non_neg.
  apply/le_trans; last first.
  apply/safe.
  by apply/HC.
  rewrite -(add0r (Concentration _ _)).
  apply/lerD.
  by move/andP: HC => [].
  apply/root_is_max => //.
  by apply/non_neg.
  apply/andP.
  split => //.
  by apply/ltW.
  move=> n IHn.
  case: (boolP (t < (ttd *+ n.+1))) => Ht_ttd.
  rewrite /total_conc big_ord_recr /=.
  rewrite (_ : maxr 0%R _ = 0).
  rewrite addr0.
  apply/andP.
  split.
  apply/sumr_ge0 => i _.
  rewrite /maxr.
  case: ifP => //.
  by apply/ltW.
  apply/le_trans; last first.
  move: (IHn n (ltnSn n) t) => /andP [_].
  apply.
  rewrite /total_conc.
  apply/ler_sum => i _ /=.
  rewrite le_eqVlt.
  apply/orP.
  left.
  apply/eqP.
  apply/f_equal2 => //.
  apply/f_equal2 => //.
  by rewrite !(tnth_nth 0) /= nth_rcons size_tuple ltn_ord.
  rewrite /maxr.
  case:ifP => //.
  rewrite ltNge => /negP H.
  exfalso.
  apply/H.
  apply/conc_non_pos.
  rewrite (tnth_nth 0) /= nth_rcons size_tuple ltnn eqxx.
  by apply/non_neg/IHn/ltnSn.
  rewrite mulNr subr_le0.
  apply/ltW.
  by rewrite mulr_natr.
  rewrite ltNge negbK -mulr_natr in Ht_ttd.
  rewrite unfold_n_dose_once /=.
  apply/andP.
  split.
  apply/addr_ge0 => //.
  rewrite /total_conc.
  apply/sumr_ge0 => i _ /=.
  rewrite /maxr.
  case: ifP => //.
  by apply/ltW.
  rewrite /maxr.
  case: ifP => //.
  by apply/ltW.
  rewrite /maxr.
  case: ifP => //; last first.
  move=> _.
  rewrite addr0.
  by move: (IHn n (ltnSn n) t) => /andP [_].
  move=> H.
  apply/le_trans; last first.
  apply/safe.
  apply/(IHn n (ltnSn n) (ttd * n.+1%:R)).
  apply/lerD; last by apply/root_is_max/non_neg/IHn/ltnSn.
  apply (ler0_derive1_nincry (a := ttd * n.+1%:R)) => //.
  move => x Hx.
  apply/derivable1_diffP.
  apply/total_conc_differentiable => //.
  move=> m Hm.
  apply/eqP.
  case: (ltgtP x (ttd * m%:R)) => //=.
  move=> H'.
  exfalso.
  move: Hx.
  rewrite in_itv => /= /andP [Hx _].
  move:Hx.
  rewrite ltNge => /negP.
  apply.
  rewrite H'.
  apply/ler_pM => //.
  by apply/ltW.
  rewrite ler_nat.
  apply/ltnW.
  by apply/Hm.
  by apply/doses_pos.
  move=> x Hx.
  rewrite total_conc_diff_correct /total_conc_diff.
  apply/sumr_le0 => i _.
  case:ifP => // H'.
  rewrite -derivative_correct.
  apply: deriv_is_non_pos.
  apply/dose_pos=> //.
  by apply/IHn.
  move: Hx.
  rewrite !in_itv /= => /andP [Hx _].
  apply/andP.
  split=> //.
  rewrite -subr_gt0.
  rewrite (_ : x - _ - _ = x - (ttd * i%:R + dCdt_root)); last by lra.
  rewrite subr_gt0.
  apply/lt_trans; last by apply/Hx.
  rewrite (_ : ttd * n.+1%:R = ttd * n%:R + ttd); last by lra.
  rewrite addrC (addrC _ ttd).
  apply/ltr_leD => //.
  apply/ler_pM => //.
  by apply/ltW.
  rewrite ler_nat.
  by rewrite -ltnS ltn_ord.
  by apply/doses_pos.
  move=> m Hm.
  apply/eqP.
  case: (ltgtP x (ttd * m%:R)) => //=.
  move=> H'.
  exfalso.
  move: Hx.
  rewrite in_itv => /= /andP [Hx _].
  move:Hx.
  rewrite ltNge => /negP.
  apply.
  rewrite H'.
  apply/ler_pM => //.
  by apply/ltW.
  rewrite ler_nat.
  apply/ltnW.
  by apply/Hm.
  by apply/continuous_subspaceT/total_conc_cont.
Qed.

End Theory.

Section Application.
Local Open Scope R_scope.

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
  {| C := tnth t 0%R
  ; T := tnth t 1%R
  ; wbc := tnth t 2%R
  ; age := tnth t 3%R
  ; weight := tnth t 4%R
  ; sex := tnth t 5%R
  |}.


Definition network (temp wbc age weight sex C : R)
  := ((pk (ntensor_of_tuple (state_to_tuple
     {| C := C
     ; T := temp
     ; wbc := wbc
     ; age := age
     ; weight := weight
     ; sex := sex
     |})))^^=0%R).

Lemma state_to_tupleK : cancel state_to_tuple tuple_to_state.
Proof. by case. Qed.

Lemma tuple_to_stateK : cancel tuple_to_state state_to_tuple.
Proof.
  move=> t;
  apply/eq_from_tnth;
  case.
  by repeat case => [//= ? | //=];
  rewrite /state_to_tuple /= !(tnth_nth 0%R).
Qed.

Definition update_state (s : state) : state :=
  {| C := C s
  ; T := T s
  ; wbc := wbc s
  ; age := age s
  ; weight := weight s
  ; sex := sex s
  |}.

Lemma RlnE (x : R) : 0 < x -> Rpower.ln x = ln x.
Proof.
rewrite /ln /Rpower.ln /= /Rln /=.
case(Rlt_dec 0 x) => // Hx.
have H := ln_exists x Hx.
have : ln_exists x Hx = H.
  apply: eq_sig.
    case: H => y Hy.
    case: (ln_exists x Hx) => y0 Hy0 /=.
    apply:expR_inj.
    rewrite -!RexpE.
    by rewrite -Hy0 -Hy.
  case: H.
  case: (ln_exists x Hx) => [y1 p1] y2 p2 /= Heq.
  by subst y2.
move=> -> _ /=.
move: H => [y Hy].
rewrite Hy RexpE.
apply: expR_inj.
rewrite (xget_unique point (x := y)) => //= y0 /eqP Hy0.
by apply: expR_inj.
Qed.

Lemma const_t_ltP {d : Order.disp_t} {R : porderType d} (t u : R) :
  (t < u :> R)%O <-> (const_t t < const_t u :> 'T_(nil, nil))%O.
Proof.
split; by rewrite -tensor_nil_ltP !const_tK.
Qed.

Axiom vcl_fix : forall s' : state,
    ((tnth (state_to_tuple s') conc +
    ((pk (ntensor_of_tuple (state_to_tuple s')))^^=0 * Ka.[::] /
     (Vd.[::] * Ka.[::] - Ke.[::]) * Ke_under.[::] -
     Ka_over.[::])%R)%E) =
    ((tnth (state_to_tuple s') conc +
    ((pk (ntensor_of_tuple (state_to_tuple s')))^^=0 * Ka.[::] /
     (Vd.[::] * (Ka.[::] - Ke.[::])) * (Ke_under.[::] -
Ka_over.[::]))%R)%E).

Axiom vcl_fix' : forall s' : state,
    ((tnth (state_to_tuple s') conc +
    ((pk (ntensor_of_tuple (state_to_tuple s')))^^=0 * Ka.[::] /
     (Vd.[::] * Ka.[::] - Ke.[::]) * Ke_over.[::] -
     Ka_under.[::])%R)%E) =
    ((tnth (state_to_tuple s') conc +
    ((pk (ntensor_of_tuple (state_to_tuple s')))^^=0 * Ka.[::] /
     (Vd.[::] * (Ka.[::] - Ke.[::])) * (Ke_over.[::] -
     Ka_under.[::]))%R)%E).

Lemma temp {R : realType} (x y : R) (Hxy : x != y) (Hx : (0 < x)%R) (Hy : (0 < y)%R) :
  (0 <= ln (x / y) / (x - y))%R.
Proof.
  case: (ltgtP x y) => H.
  rewrite -(opprK (ln _)) -lnV.
  rewrite invf_div.
  (* Unset Printing Notations. *)
  rewrite mulNr -mulrN -invrN.
  apply divr_ge0.
  apply/ln_ge0.
  apply/ltW.
  rewrite ltr_pdivlMr => //.
  by rewrite mul1r.
  rewrite opprB subr_ge0.
  by apply/ltW.
  rewrite posrE.
  rewrite ltr_pdivlMr => //.
  by rewrite mul0r.
  apply divr_ge0.
  apply/ln_ge0.
  apply/ltW.
  rewrite ltr_pdivlMr => //.
  by rewrite mul1r.
  rewrite subr_ge0.
  by apply/ltW.
  by move/eqP: Hxy.
Qed.

Theorem pk_safe (n : nat) (t : R) (s : state) :
  safeInput (ntensor_of_tuple (state_to_tuple s)) ->
  (0 <= total_conc Vd.[::] Ke.[::] Ka.[::] ttd.[::] (@n_doses R Vd.[::] Ke.[::] Ka.[::] ttd.[::]
  (network s.(T) s.(wbc) s.(age) s.(weight) s.(sex)) (C s) n) t <= C_safe.[::])%R.
Proof.
move=> Hi.
apply/doses_safe => //=.
by rewrite const_t_ltP const_tK Vd_pos.
by rewrite const_t_ltP const_tK Ke_pos.
by rewrite const_t_ltP const_tK Ka_pos.
by rewrite const_t_ltP const_tK ttd_pos.
by rewrite const_t_ltP const_tK C_safe_pos.
apply/eqP => H.
have := Ke_n_Ka => /eqP.
apply.
move/eqP: H.
rewrite subr_eq0 -tensor_nil_eqP.
by move=> /eqP.
rewrite /dCdt_root.
rewrite RlnE.
rewrite /dCdt_root /Ke /Ka !const_tK.
apply/RltP.
rewrite -!RmultE -!RoppE -!RinvE -RplusE.
interval.
apply/Rlt_mult_inv_pos;
apply/RltP;
rewrite const_t_ltP const_tK.
by apply/Ka_pos.
by apply/Ke_pos.
move=> C HC.
rewrite /network /normpk.
set s' :=
  {|
C := C; T := T s; wbc := wbc s; age := age s; weight := weight s; sex := sex s
  |}.
have Hi' : safeInput (ntensor_of_tuple (state_to_tuple s')).
rewrite /safeInput.
split.
rewrite -!tensor_nil_leP !const_tK /ntensor_of_tuple /= nstackE const_tK.
rewrite /conc /state_to_tuple tnth0 /s' /=.
apply/andP.
move: HC.
by rewrite const_tK.
move: Hi => [_].
by rewrite -!tensor_nil_leP !ntensor_of_tupleE.
have := (safe _ Hi').
rewrite /safeOutput.
case: ifP => Ke_n_Ka;
rewrite -tensor_nil_leP !tensor_nilD;
rewrite tensor_nilN !tensor_nilM tensor_nilV tensor_nilD tensor_nilM tensor_nilN;
rewrite /normpk !ntensor_of_tupleE.
rewrite vcl_fix.
move=> H.
rewrite (_ : C = tnth (state_to_tuple s') conc) => //=.
apply/le_trans; last first.
by apply/H.
apply/lerD => //.
rewrite /Concentration /dCdt_root /=.
apply/ler_nmul_pos.
apply/mulr_ge0_le0.
apply/mulr_ge0.
have := nonNeg _ Hi'.
by rewrite /nonNegOutput /normpk -tensor_nil_leP !const_tK.
apply/ltW.
have := Ka_pos.
by rewrite -tensor_nil_ltP !const_tK.
rewrite invr_le0.
apply/mulr_ge0_le0.
have := Vd_pos.
rewrite -tensor_nil_ltP !const_tK.
by apply/ltW.
rewrite subr_le0.
apply/ltW.
move: Ke_n_Ka.
by rewrite tensor_nil_ltP.
apply/lerD.
apply/RleP.
rewrite -!RinvE -!RplusE -!RoppE -!RmultE -RexpE RlnE.
rewrite !const_tK.
interval.
apply/Rlt_mult_inv_pos;
apply/RltP;
rewrite const_t_ltP const_tK.
by apply/Ka_pos.
by apply/Ke_pos.
rewrite -subr_ge0 addrC opprK subr_ge0.
apply/RleP.
rewrite -!RinvE -RplusE -!RoppE -!RmultE -RexpE RlnE.
rewrite !const_tK.
interval.
apply/Rlt_mult_inv_pos;
apply/RltP;
rewrite const_t_ltP const_tK.
by apply/Ka_pos.
by apply/Ke_pos.
move: Ke_n_Ka => /negP.
rewrite -tensor_nil_ltP ltNge => /negP.
rewrite negbK [in (_ <= _)%R]le_eqVlt => /orP [// /eqP /esym | ].
have /eqP := Spec.Ke_n_Ka.
by rewrite tensor_nil_eqP.

move=> Ke_n_Ka.
rewrite vcl_fix'.
move=> H.
rewrite (_ : C = tnth (state_to_tuple s') conc) => //=.
apply/le_trans; last first.
by apply/H.
apply/lerD => //.
rewrite /Concentration /dCdt_root /=.
apply/ler_pM.
apply/mulr_ge0.
apply/mulr_ge0.
have:= nonNeg _ Hi'.
rewrite /nonNegOutput.
by rewrite -tensor_nil_leP !const_tK.
apply/ltW.
have := Ka_pos.
by rewrite -tensor_nil_ltP !const_tK.
rewrite invr_ge0.
apply/mulr_ge0.
apply/ltW.
have := Vd_pos.
by rewrite -tensor_nil_ltP !const_tK.
rewrite subr_ge0.
by apply/ltW.
rewrite subr_ge0 ler_expR -subr_ge0 addrC !mulNr opprK subr_ge0.
apply/ler_pM.
apply/ltW.
have:= Ke_pos.
by rewrite -tensor_nil_ltP !const_tK.
apply/mulr_ge0.
apply/ln_ge0.
rewrite ler_pdivlMr.
rewrite mul1r.
by apply/ltW.
move: Ke_pos.
by rewrite -tensor_nil_ltP !const_tK.
rewrite invr_ge0.
rewrite subr_ge0.
by apply/ltW.
by apply/ltW.
apply/ler_pM => //.
apply/ln_ge0.
rewrite ler_pdivlMr.
rewrite mul1r.
by apply/ltW.
have := Ke_pos.
by rewrite -tensor_nil_ltP !const_tK.
rewrite invr_ge0 subr_ge0.
by apply/ltW.
apply/ler_pM => //.
apply/mulr_ge0.
have := nonNeg _ Hi'.
rewrite /nonNegOutput.
by rewrite -tensor_nil_leP !const_tK /normpk.
have := Ka_pos.
rewrite -tensor_nil_ltP !const_tK.
by apply/ltW.
rewrite invr_ge0.
apply/mulr_ge0.
have := Vd_pos.
rewrite -tensor_nil_ltP !const_tK.
by apply/ltW.
rewrite subr_ge0.
by apply/ltW.
apply/lerD.
apply/RleP.
rewrite -RexpE -!RoppE -!RmultE -!RinvE RlnE.
rewrite -!RplusE !const_tK.
interval.
apply/Rlt_mult_inv_pos;
apply/RltP;
rewrite const_t_ltP const_tK.
by apply/Ka_pos.
by apply/Ke_pos.
rewrite -subr_ge0 addrC opprK subr_ge0.
apply/RleP.
rewrite -RexpE -!RoppE -!RmultE -!RinvE RlnE.
rewrite -!RplusE !const_tK.
interval.
apply/Rlt_mult_inv_pos;
apply/RltP;
rewrite const_t_ltP const_tK.
by apply/Ka_pos.
by apply/Ke_pos.
move=> C HC.
set s' :=
  {|
C := C; T := T s; wbc := wbc s; age := age s; weight := weight s; sex := sex s
  |}.
suff : safeInput (ntensor_of_tuple (state_to_tuple s')).
move=> /nonNeg.
by rewrite /nonNegOutput -tensor_nil_leP /normpk const_tK.
rewrite /safeInput.
split.
rewrite -!tensor_nil_leP !const_tK /ntensor_of_tuple /= nstackE const_tK.
rewrite /conc /state_to_tuple tnth0 /s' /=.
apply/andP.
move: HC.
by rewrite const_tK.
move: Hi => [_].
by rewrite -!tensor_nil_leP !ntensor_of_tupleE.
move: Hi => [H _].
move: H.
by rewrite -!tensor_nil_leP !const_tK ntensor_of_tupleE => /andP.
Qed.
