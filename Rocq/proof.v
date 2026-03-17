From Coq Require Lra.
Tactic Notation "std_lra" := Lra.lra.
From Stdlib Require Import Reals.
From mathcomp Require Import all_boot all_order all_algebra all_reals ring lra Rstruct Rstruct_topology.
From mathcomp Require Import all_classical all_analysis.
From Interval Require Import Tactic.
Require Import vehicle.tensor.
From HB Require Import structures.
Import Num.Theory GRing.Theory Order.POrderTheory.
Import numFieldNormedType.Exports.

Open Scope order_scope.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Spec.


Section Helpers.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Lemma min_fun_to_max (T : Type) (T' : numDomainType) (f g : T -> T') :
  (f \min g) = (f + g) - (f \max g).
Proof.
  apply/funext=> x /=; by rewrite Num.Theory.minr_to_max. Qed.

Lemma max_fun_to_min (T : Type) (T' : numDomainType) (f g : T -> T') :
  (f \max g) = (f + g) - (f \min g).
Proof.
  apply/funext => x /=; by rewrite Num.Theory.maxr_to_min. Qed.

Lemma fun_maxC d (T : Type) (T' : orderType d) (f g : T -> T') :
  f \max g = g \max f.
Proof. by apply/funext => z/=; rewrite Order.TotalTheory.maxC. Qed.

Lemma fun_minC d (T : Type) (T' : orderType d) (f g : T -> T') :
  f \min g = g \min f.
Proof. by apply/funext => z/=; rewrite Order.TotalTheory.minC. Qed.

Context {R : numFieldType} {V W : normedModType R}.

Lemma derive0 (f : V -> W) (x : V) : 'D_0 f x = 0.
Proof.
  apply/lim_near_cst => //=.
  near=> h.
  by rewrite scaler0 add0r subrr scaler0.
  Unshelve.
  end_near.
Qed.

End Helpers.

Section Derive_max.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Context {K : realType} {V W : normedModType K}.
Implicit Types f g : V -> K^o.
Implicit Type x : V.

Fact der_max f g x v :
  f x <> g x -> derivable f x v -> derivable g x v ->
  {for x, continuous f} -> {for x, continuous g} ->
  (fun h => h^-1 *: (((f \max g) \o shift x) (h *: v) - (f \max g) x)) @
    0^' --> if f x < g x then 'D_v g x else 'D_v f x.
Proof.
wlog: f g x / f x < g x.
  move=> wlg fx_neq_gx.
  move: (fx_neq_gx) => /eqP.
  rewrite neq_lt => /orP[fg|gf].
    move: fg fx_neq_gx.
    by apply:wlg.
  move=> df dg cf cg.
  move: dg df cg cf.
  rewrite fun_maxC ltNge if_neg le_eqVlt.
  move: fx_neq_gx => /nesym/[dup] fx_neq_gx /eqP/negPf -> /=.
  by apply:(wlg g f).
move=> fx_lt_gx fg_neq df dg cf cg.
case: ifPn => fg /=.
  rewrite /Num.max fg => t Ht.
  apply:(@near_eq_cvg _ _ _ _ (fun h => h^-1 *: (g (h *: v + x) - g x))).
    near=> h.
    rewrite ifT // -subr_lt0 (_ : f _ - _ = ((f - g) \o shift x) (h *: v)) //.
    near: h.
    have Hf : forall f : V -> K^o,
    continuous_at x f -> f (shift x (x0 *: v)) @[x0 --> nbhs 0^'] --> f x.
      move=> f' cf'.
      apply:cvg_comp; last by apply:cf'.
      rewrite -[in nbhs x](add0r x).
      apply:cvgD; last by apply:cvg_cst.
      rewrite -(scale0r v).
      apply:cvgZ; last by apply:cvg_cst.
      by apply:nbhs_dnbhs.
    apply/cvgr_lt; last by move: fg; rewrite -subr_lt0; apply.
    by apply:cvgB; apply:Hf.
  by apply:dg.
exfalso.
by apply: (negP fg).
Unshelve.
end_near.
Qed.

Lemma derivable_max f g x v :
  f x <> g x -> derivable f x v -> derivable g x v ->
  {for x, continuous f} -> {for x, continuous g} ->
  derivable (f \max g) x v.
Proof.
move=> fx_gx df dg cf cg; apply/cvg_ex.
exists(if f x < g x then 'D_v g x else 'D_v f x).
exact: der_max.
Qed.

Lemma derive_maxl f g x v : f x > g x ->
  {for x, continuous f} -> {for x, continuous g} ->
  'D_v (f \max g) x = 'D_v f x.
Proof.
case: (boolP (v == 0)) => [/eqP -> //= gx_fx cf cg | v0].
  by rewrite !derive0.
move=> fg cf cg; apply: near_eq_derive => //.
near do rewrite /Order.max_fun /Num.max ifN// -leNgt -subr_le0.
by move: fg; rewrite -subr_lt0; apply: cvgr_le; exact: cvgB.
Unshelve. all: by end_near. Qed.

Lemma derive_maxr f g x v : f x < g x ->
  {for x, continuous f} -> {for x, continuous g} ->
  'D_v (f \max g) x = 'D_v g x.
Proof. by move=> fg cf cg; rewrite fun_maxC derive_maxl. Qed.

End Derive_max.

Section Theory.

Context {R : realType}.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Variables (Vd Ke Ka ttd C_safe Ka_under Ka_over Ke_under Ke_over : R).

Hypothesis Vd_pos : Vd > 0.
Hypothesis Ke_pos : Ke > 0.
Hypothesis Ka_pos : Ka > 0.
Hypothesis ttd_pos : ttd > 0.
Hypothesis C_safe_pos : C_safe > 0.
Hypothesis Ke_n_Ka : Ka - Ke != 0.

Definition dCdt_root : R :=
  (ln (Ka/Ke)) / (Ka - Ke).

Hypothesis ttd_dCdt_root : dCdt_root <= ttd.

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
rewrite derive1E deriveZ //= deriveB //= -derive1E derive1_comp //= !derive1E.
rewrite deriveZ //= derive_id -!derive1E derive1_comp //= !derive1E deriveZ;
rewrite //= derive_id (congr1 (fun f => f (-Ke * t)) (derive_expR R)).
rewrite (congr1 (fun f => f (-Ka * t)) (derive_expR R)) scalerBr !scalerA.
rewrite !scaler1 /dCdt.
ring.
Qed.

Lemma root_correct (D t : R) :
  D != 0 -> dCdt D t = 0 <-> t = dCdt_root.
Proof.
move=> H.
split.
  rewrite/dCdt /dCdt_root mulrBr=> /subr0_eq /mulrI => H0.
  apply/(mulfI Ke_n_Ka).
  rewrite mulrA (mulrC (Ka - Ke) (ln _)) -mulrA mulrV;
  last by apply/unitrPr;
  exists ((Ka - Ke)^-1);
  apply/mulfV/Ke_n_Ka.
  apply/expR_inj.
  rewrite mulr1 lnK;
  last by apply Num.Internals.pos_divr_closed;
  rewrite ?Ka_pos ?Ke_pos.
  rewrite mulrBl exp.expRB -expRN.
  apply/(@mulfI _ Ke);
  first by apply/lt0r_neq0/Ke_pos.
  rewrite !mulrA (mulrC Ke Ka) -!mulrA mulrV; last first.
    rewrite unitrE mulfV //.
    by apply/lt0r_neq0.
  rewrite mulr1 mulrA.
  apply/(@mulfI _ (expR (Ka * t))^-1);
  first by apply/lt0r_neq0; rewrite invr_gt0; apply/expR_gt0.
  rewrite !mulrA (mulrC (expR _)^-1 Ke) -(mulrA Ke _ _) mulVr.
    rewrite mulrC mulr1 /= -expRN -mulNr mulrC (mulrC (expR _) Ka) -mulNr.
    apply/esym/H0.
    rewrite unitrE mulfV; first by apply/eqP => //.
    rewrite mulrI_eq0 ?invr_eq0 ?mulf_neq0 //.
      by apply/lt0r_neq0.
    by apply/GRing.lregM; apply/mulrI; rewrite unitrE mulfV // lt0r_neq0.
  by rewrite unitrE mulfV // lt0r_neq0 // expR_gt0.
move=> H0.
rewrite H0 /dCdt /dCdt_root.
rewrite [X in _ * X](_ : _ = 0) ?mulr0 //.
apply/eqP.
rewrite subr_eq0.
apply/eqP/ln_inj;
  last first.
  - rewrite !lnM //= ?posrE ?Ka_pos ?expR_gt0 ?invr_gt0 ?Ke_pos //.
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

Lemma ler_pmul_pos (a b c : R) : 0 <= a -> b <= c -> a * b <= a * c.
Proof.
rewrite le_eqVlt => /orP [/eqP <- | ].
  by rewrite !mul0r.
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
apply/continuousM; first by apply/cst_continuous.
apply/continuousB/continuous_comp/continuous_expR/scaler_continuous.
by apply/continuous_comp/continuous_expR/scaler_continuous.
Qed.

Lemma deriv_is_pos (D t : R) (HD : 0 < D) (Ht : t \in `]-oo, dCdt_root[%R) :
  (0 <= (Concentration D)^`() t).
Proof.
rewrite derivative_correct /dCdt.
case: (ltgtP t 0) => Ht0.
- case: (ltgtP Ke Ka) => HKeKa.
  + rewrite pmulr_rge0.
      rewrite subr_ge0.
      apply/ler_pM; [by apply/ltW/Ke_pos | by apply/expR_ge0 | by apply/ltW | ].
      rewrite ler_expR -subr_le0 addrC !mulNr opprK subr_le0 mulrC (mulrC Ke).
      rewrite ler_nM2l //.
      by apply/ltW.
    by apply divr_gt0; rewrite pmulr_lgt0 ?subr_gt0.
  + rewrite nmulr_rge0 ?subr_le0.
      apply/ler_pM; [by apply/ltW/Ka_pos | by apply/expR_ge0 | by apply/ltW | ].
      rewrite ler_expR -subr_le0 addrC !mulNr opprK subr_le0 mulrC (mulrC Ka).
      rewrite ler_nM2l //.
      by apply/ltW.
    rewrite nmulr_llt0; first by rewrite pmulr_lgt0 ?Ka_pos.
    by rewrite invr_lt0 nmulr_llt0; [apply/Vd_pos | rewrite subr_lt0].
  + exfalso.
    move/eqP: Ke_n_Ka.
    lra.
  (* 0 < t *)
- case: (ltgtP Ke Ka) => HKeKa.
  + rewrite pmulr_rge0.
      rewrite subr_ge0.
      rewrite -ler_ln ?lnM ?posrE ?pmulr_rgt0 ?expR_gt0 //;
      rewrite ?Ke_pos ?Ka_pos //.
      rewrite !expRK -subr_le0 !mulNr.
      rewrite opprB [X in _ + X]addrC addrA [X in X + _]addrAC -ln_div;
      rewrite ?Ka_pos ?Ke_pos //.
      rewrite -mulNr -addrA -mulrDl [X in X * t]addrC -opprB mulNr subr_le0.
      (* rewrite -ler_expR lnK ?posrE ?divr_gt0 ?Ka_pos ?Ke_pos // mulrDl. *)
      (* rewrite expRD. *)
      rewrite -(@ler_pM2l _ ((Ka - Ke)^-1)); last by rewrite invr_gt0; lra.
      rewrite (mulrC (Ke - Ka) t) mulrA (mulrC _ t) -mulrA.
      rewrite -[Ka - Ke]opprB invrN [X in t * X]mulNr mulVf; last lra.
      rewrite -subr_ge0 addrC mulNr opprK mulrN mulr1 subr_ge0 mulrC.
      apply/ltW.
      move: Ht.
      rewrite in_itv //= /dCdt_root.
      by rewrite -divrNN opprB -lnV ?invf_div ?posrE ?divr_gt0 ?Ka_pos ?Ke_pos.
    rewrite pmulr_rgt0.
    rewrite invr_gt0 pmulr_rgt0 ?Vd_pos //; first lra.
    by rewrite pmulr_rgt0 ?Ka_pos.
  + rewrite nmulr_rge0.
      rewrite subr_le0.
      rewrite -ler_ln ?lnM ?posrE ?pmulr_rgt0 ?expR_gt0 ?Ka_pos ?Ke_pos // !expRK.
      rewrite -subr_le0 !mulNr.
      rewrite opprB [X in _ + X]addrC addrA [X in X + _]addrAC -ln_div;
      rewrite ?Ka_pos ?Ke_pos //.
      rewrite -mulNr -addrA -mulrDl [X in X * t]addrC -opprB mulNr subr_le0.
      rewrite -(@ler_nM2l _ ((Ka - Ke)^-1));
      last by rewrite invr_lt0; lra.
      rewrite mulrA (mulrC _ t) mulVf // mulr1 mulrC.
      apply/ltW.
      move: Ht.
      by rewrite in_itv //= /dCdt_root.
    rewrite pmulr_rlt0; last by apply/mulr_gt0.
    by rewrite invr_lt0 pmulr_rlt0 ?Vd_pos // ?pmulr_rgt0 ?Ka_pos; first lra.
  + move: Ke_n_Ka.
    lra.
  (* t = 0 *)
- rewrite Ht0 !mulr0 expR0 !mulr1.
  case: (ltgtP Ke Ka) => HKeKa.
  + rewrite pmulr_rge0.
      by apply/ltW; rewrite subr_gt0.
    rewrite pmulr_rgt0.
      rewrite invr_gt0 pmulr_rgt0 ?Vd_pos // subr_gt0.
      lra.
    by rewrite pmulr_rgt0 ?Ka_pos.
  + rewrite nmulr_rge0.
      by apply/ltW; rewrite subr_lt0.
    rewrite pmulr_rlt0.
      by rewrite invr_lt0 pmulr_rlt0 ?Vd_pos // subr_lt0.
    by rewrite pmulr_rgt0 ?Ka_pos.
  + exfalso.
    move/eqP: Ke_n_Ka.
    lra.
Qed.

Lemma conc_D0 : Concentration 0 = 0.
Proof.
apply funext => t.
by rewrite /Concentration !mul0r.
Qed.

Lemma conc_neq0 (D t : R) : D <> 0 -> t <> 0 -> Concentration D t <> 0.
Proof.
move=> HD Ht.
rewrite /Concentration.
apply/eqP/mulf_neq0; last first.
  rewrite subr_eq0.
  apply/eqP => /expR_inj/eqP/negP.
  apply.
  apply/negP.
  rewrite -subr_eq0 addrC !mulNr opprK subr_eq0.
  apply/eqP => /mulIf.
  move/eqP: Ht => H /(_ H) /eqP.
  rewrite -subr_eq0 => H'.
  move/eqP: Ke_n_Ka.
  apply.
  by apply/eqP/H'.
apply/mulf_neq0.
by apply/mulf_neq0; [apply/eqP | apply/lt0r_neq0].
by apply/invr_neq0/mulf_neq0/Ke_n_Ka/lt0r_neq0.
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
- rewrite pmulr_rle0.
    rewrite subr_le0.
    rewrite -ler_ln ?lnM ?posrE ?pmulr_rgt0 ?expR_gt0 ?Ka_pos ?Ke_pos // !expRK.
    rewrite -subr_le0 !mulNr opprB [Ke * t - _]addrC addrA [in (_ - _ - _)]addrC.
    rewrite addrA [(- _) + _]addrC -ln_div ?posrE ?Ka_pos ?Ke_pos // -mulNr.
    rewrite -addrA -mulrDl [(-Ka) + _]addrC -[((_ - _) * _)]opprK subr_le0 -mulNr.
    rewrite opprB -(@ler_pM2l _ ((Ka - Ke)^-1));
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
- rewrite nmulr_rle0.
    rewrite subr_ge0.
    rewrite -ler_ln ?lnM ?posrE ?pmulr_rgt0 ?expR_gt0 ?Ka_pos ?Ke_pos // !expRK.
    rewrite -subr_le0 !mulNr opprB [Ka * t - _]addrC addrA [in (_ - _ - _)]addrC.
    rewrite addrA [(- _) + _]addrC -ln_div ?posrE ?Ka_pos ?Ke_pos // -mulNr.
    rewrite -addrA -mulrDl [(-Ke) + _]addrC -[((_ - _) * _)]opprK subr_le0 -mulNr.
    rewrite opprB -(@ler_pM2l _ ((Ke - Ka)^-1));
    last by rewrite invr_gt0; lra.
    rewrite mulrA (mulrC _ t) mulVf.
      rewrite mulr1 mulrC -divrNN opprB -lnV ?invf_div ?posrE ?divr_gt0 ?Ka_pos //.
      apply/ltW.
      move: Ht.
      by rewrite in_itv //= /dCdt_root => /andP [].
    lra.
  rewrite pmulr_rlt0.
    rewrite invr_lt0 pmulr_rlt0 ?Vd_pos //.
    lra.
  by rewrite pmulr_rgt0 ?Ka_pos.
- exfalso.
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

Lemma conc_non_neg (D t : R) : 0 <= D -> 0 <= t -> 0 <= Concentration D t.
Proof.
rewrite le_eqVlt => /orP [/eqP <- _| HD ]; first by rewrite conc_D0.
rewrite le_eqVlt => /orP [/eqP <- | Ht]; first by rewrite conc_t0.
by apply/ltW/conc_pos.
Qed.

Lemma conc_non_pos (D t : R) : 0 <= D -> t <= 0 -> Concentration D t <= 0.
Proof.
rewrite le_eqVlt => /orP [/eqP <- _| HD ]; first by rewrite conc_D0.
rewrite le_eqVlt => /orP [/eqP -> | Ht]; first by rewrite conc_t0.
by apply/ltW/conc_neg.
Qed.

Lemma root_is_max (D t : R) (HD : 0 <= D) :
  Concentration D t <= Concentration D dCdt_root.
Proof.
move: HD.
rewrite le_eqVlt => /orP [/eqP <- | HD]; first by rewrite conc_D0.
case: (ltgtP t dCdt_root) => [ | | -> //] Htr.
  apply/(ger0_derive1_ndecrNy) => //.
  - move=> x Hx.
    by apply deriv_is_pos.
  - apply/derivable_within_continuous => /= t' _.
    rewrite derivable1_diffP.
    by apply conc_diff.
  - by apply/ltW.
apply/(ler0_derive1_nincry) => //.
- move=> x Hx.
  by apply deriv_is_non_pos => //; apply/ltW.
- apply/derivable_within_continuous => /= t' _.
  rewrite derivable1_diffP.
  by apply conc_diff.
- by apply/ltW.
Qed.

Definition total_conc {n} (Ds : n.-tuple R)
  := \sum_(i < n) ((cst 0) \max (Concentration (tnth Ds i)) \o (center (ttd * i%:R))).

Definition total_conc_diff n (Ds : n.-tuple R) (t : R)
  := \sum_(i < n) (fun x : R => if 0 < Concentration (tnth Ds i) x then (dCdt (tnth Ds i) x) else 0) (t - ttd * i%:R).

Lemma continuous_shift (f : R -> R) (k : R) (H : continuous f) : continuous (f \o (shift k)).
Proof.
move=> x.
apply: continuous_comp;
last by apply H.
apply/continuousD;
last by apply:(near_cst_continuous k);
near=> t.
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

Lemma total_conc_cont {n} (Ds : n.-tuple R) :
  continuous (total_conc Ds).
Proof.
rewrite /total_conc -sum_apply.
apply/continuous_big.
  apply/tvs.standard_add_continuous.
move=> i _.
by apply/continuous_shift/max_fun_continuous/conc_cont/cst_continuous.
Qed.

Lemma max_eq (f g : R -> R) : f =1 g -> f \max g = f.
Proof.
move=> fg.
apply funext=> x.
by rewrite /Order.max_fun /maxr fg ifN ?ltxx.
Qed.

Lemma total_conc_derivable n (t : R) (Ds : n.-tuple R) (i : 'I_n)
  (HC : 0 <> Concentration (tnth Ds i) (center (ttd * i%:R) t)) :
  derivable ((cst 0 \max Concentration (tnth Ds i)) \o center (ttd * i%:R)) t 1.
Proof.
  apply/derivable_max.
  - rewrite /=.
    by apply/HC.
  - by apply/derivable_cst.
  - by apply/derivable1_diffP/differentiable_comp/conc_diff/differentiableD.
  - by apply/cst_continuous.
  - by apply/continuous_shift/conc_cont.
Qed.

Lemma total_conc_diff_correct n (t : R) (Ds : n.-tuple R) (HDs : all (>= 0) Ds) (Ht : forall m : nat, (m < n)%O -> t <> ttd * m%:R) :
  (total_conc Ds)^`() t = total_conc_diff Ds t.
Proof.
rewrite derive1E /total_conc derive_sum; last first.
  move=> i.
  case: (eqVneq (tnth Ds i) 0) => [-> | HD]; first by rewrite conc_D0 max_eq.
  apply/total_conc_derivable.
  apply/nesym/conc_neq0; first by apply/eqP.
  apply/eqP.
  rewrite subr_eq0.
  by apply/eqP/Ht/ltn_ord.
rewrite /total_conc_diff.
apply/eq_bigr => i _.
case: (eqVneq (tnth Ds i) 0) => [-> | HD].
by rewrite max_eq conc_D0 ?derive_cst ?ltxx.
case (ltgtP 0 (Concentration (tnth Ds i) (t - ttd * i %:R))) => H.
- rewrite H -derive1E derive1_comp //; last first.
  apply/derivable_max/conc_cont/cst_continuous/derivable1_diffP/conc_diff/derivable_cst.
  by apply/nesym/eqP/lt0r_neq0.
  rewrite !derive1E /= deriveD // derive_id derive_cst addr0 mulr1 -derive1E.
  rewrite derive1E derive_maxr //=.
  + by rewrite -derive1E derivative_correct.
  + by apply/cst_continuous.
  + by apply/conc_cont.
  rewrite ifN ?ltNge ?negbK; last by apply/ltW.
  rewrite derive_maxl //.
  + by rewrite derive_cst.
  + by apply/cst_continuous.
  + by apply/continuous_comp/conc_cont/continuousD/cst_continuous.
- contra: H => _.
  apply/eqP/nesym/conc_neq0; first by apply/eqP.
  apply/eqP.
  rewrite subr_eq0.
  by apply/eqP/Ht/ltn_ord.
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
  total_conc (n_doses initial n.+1) t = total_conc (n_doses initial n) t + maxr 0 (Concentration (network (total_conc (n_doses initial n) ((ttd * n.+1%:R)%R))) (t - ttd * n.+1%:R%R)).
Proof.
rewrite /total_conc big_ord_recr /total_conc /=.
rewrite (tnth_nth (network initial)) /= nth_rcons ifF ?ifT ?size_tuple ?ltnn // -!sum_apply.
congr (_ + _).
  apply/eq_bigr=> i _.
  apply/f_equal2/f_equal2 => //.
  by rewrite !(tnth_nth 0) nth_rcons /= size_tuple ifT.
rewrite /=.
apply/f_equal2/f_equal2 => //.
apply/f_equal.
by rewrite /total_conc -sum_apply /= -(mulr_natr ttd).
Qed.

Lemma total_conc_non_neg {n : nat} (initial t : R) (Hi : 0 <= initial) (Ht : 0 <= t) :
  all [pred x | 0 <= x] (n_doses initial n) -> 0 <= (total_conc (n_doses initial n) t).
Proof.
rewrite /total_conc -!sum_apply => H.
apply/sumr_ge0 => i _.
rewrite /= /maxr.
case: ifP => //.
apply/ltW.
Qed.

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
case => [/= _ _ | m Hm H]; first by apply/non_neg.
rewrite nth_rcons size_tuple /= ltnn eqxx.
apply/non_neg.
fold n_doses.
move: H => /=.
congr (0 <= _ <= C_safe).
  rewrite /total_conc -!sum_apply big_ord_recr /= max_l ?addr0.
    apply/eq_bigr => i _.
    apply/f_equal2/f_equal2 => //.
    by rewrite !(tnth_nth 0) nth_rcons size_tuple /= ltn_ord.
  by rewrite -[ttd *+ m.+1]mulr_natr -mulrBr subrr mulr0 conc_t0 /maxr.
rewrite /total_conc -!sum_apply big_ord_recr /= max_l ?addr0.
  apply/eq_bigr => i _.
  apply/f_equal2/f_equal2 => //.
  by rewrite !(tnth_nth 0) nth_rcons size_tuple /= ltn_ord.
by rewrite -[ttd *+ m.+1]mulr_natr -mulrBr subrr mulr0 conc_t0.
Qed.

Lemma doses_pos (n : nat) (initial : R) (HC : 0 <= initial <= C_safe) :
    (forall m : nat,
    (m < n.+1)%N -> forall t : R, 0 <= total_conc (n_doses initial m) t <= C_safe) ->
    all (>= 0) (n_doses initial n).
Proof.
elim: n.
  move=> _.
  apply/andP.
  by split => //; apply/non_neg.
move=> n IHn H.
apply/allP => /= x.
rewrite /= mem_rcons in_cons => /orP [/eqP -> |].
  by apply/non_neg/(H n _ (ttd *+ n.+1))/ltn_trans/ltnSn.
apply/allP/IHn.
move=> m Hm t'.
apply/H.
by apply/ltn_trans/ltnSn/Hm.
Qed.

Theorem doses_safe (n : nat) (initial t : R) (HC : 0 <= initial <= C_safe) :
  0 <= total_conc (n_doses initial n) t <= C_safe.
Proof.
have root_non_neg : (0 <= dCdt_root).
  rewrite /dCdt_root.
  case: (ltgtP Ke Ka) => Ke_Ka.
  - apply/divr_ge0.
      apply/ln_ge0.
      by rewrite ler_pdivlMr ?mul1r //; apply/ltW.
    rewrite subr_ge0.
    by apply/ltW.
  - rewrite -divrNN.
    apply/divr_ge0.
      rewrite -lnV; last by rewrite ?posrE ?divr_gt0 ?Ka_pos ?Ke_pos.
      rewrite invf_div lnM ?posrE ?Ke_pos ?invr_gt0 ?Ka_pos //.
      rewrite lnV ?subr_ge0 ?ler_ln ?posrE ?Ke_pos ?Ka_pos //.
      by apply/ltW.
    rewrite opprB subr_ge0.
    by apply/ltW.
  - contra: Ke_n_Ka => _; lra.
elim/ltn_ind: n t.
case => [_| n IHn] t;
rewrite /total_conc.
  apply/andP.
  split.
  rewrite -!sum_apply.
    apply/sumr_ge0 => /= i _.
    rewrite /maxr.
    case: ifP => //.
    by apply/ltW.
  rewrite big_ord1 /= /maxr.
  case: ifP => _.
    rewrite (tnth_nth 0) /= mulr0 subr0 -[Concentration _ _]add0r.
    apply/le_trans/safe/HC.
    apply/lerD; first by move/andP:HC => [].
    by apply/root_is_max/non_neg/HC.
  by apply/le_trans/(snd (andP HC))/(fst (andP (HC))).
case: (lerP t (ttd *+ n.+1)) => t_ttd.
  rewrite -!sum_apply big_ord_recr /= max_l.
    rewrite addr0.
    rewrite (eq_bigr (fun i => ((cst 0 \max Concentration (tnth (n_doses initial n) i)) \o center (ttd * i%:R)) t)).
      move: (IHn n (ltnSn n) t).
      rewrite /total_conc -sum_apply.
      by apply.
    move=> i _.
    by rewrite !(tnth_nth 0) nth_rcons size_tuple /= ltn_ord.
  apply/conc_non_pos.
    rewrite (tnth_nth 0) nth_rcons size_tuple ltnn eq_refl.
    by apply/non_neg/IHn.
  by rewrite subr_le0 mulr_natr.
apply/andP.
split.
  rewrite -sum_apply.
  apply/sumr_ge0 => /= i _.
  rewrite /maxr.
  by case: ifP => //; apply/ltW.
rewrite big_ord_recr /=.
apply/le_trans/(@safe (total_conc (n_doses initial n) (ttd *+ n.+1)))/IHn/ltnSn.
apply/lerD.
  rewrite /total_conc -!sum_apply.
  apply/ler_sum => /= i _.
  rewrite !(tnth_nth 0) nth_rcons size_tuple /= ltn_ord.
  rewrite /maxr.
  case: ifP; last first.
    move=> H.
    case: (eqVneq 0 ((n_doses initial n)`_i)) => [<- | HD].
      by rewrite conc_D0 /= ltxx.
    contra: H => _.
    apply/conc_pos.
      rewrite lt_neqAle HD /=.
      apply/(allP (doses_pos HC IHn))/mem_nth.
      by rewrite size_tuple ltn_ord.
    rewrite subr_gt0.
    apply/lt_trans/t_ttd.
    by rewrite mulr_natr ltr_pMn2l.
  case:ifP => H H'.
    apply/ler0_derive1_nincry.
    - move=> x itv_x.
      by apply/derivable1_diffP/conc_diff.
    - move=> x itv_x.
      apply/deriv_is_non_pos/itv_x/(allP (doses_pos HC IHn))/mem_nth.
      by rewrite size_tuple.
    - by apply/continuous_subspaceT/conc_cont.
    - rewrite -[ttd *+ _]mulr_natr -mulrBr  -[dCdt_root]mulr1.
      apply/ler_pM => //.
      rewrite -subr_ge0.
      rewrite -addrA -opprD subr_ge0.
      by rewrite (_ : _ + 1%R = i%:R + (1 : nat)%:R) // -natrD ler_nat addn1 ltn_ord.
    - by apply/lerB => //; apply/ltW.
  case:(eqVneq 0 (n_doses initial n)`_i) => [<- | HD].
    by rewrite conc_D0.
  contra: H => _.
  apply/conc_pos.
    rewrite lt_neqAle HD /=.
    apply/(allP (doses_pos HC IHn))/mem_nth.
    by rewrite size_tuple.
  by rewrite subr_gt0 mulr_natr ltr_pMn2l.
rewrite (tnth_nth 0) nth_rcons size_tuple ltnn eq_refl /maxr.
rewrite /= /maxr.
case:ifP => _.
  by apply/root_is_max/non_neg/IHn/ltnSn.
by apply/conc_non_neg/root_non_neg/non_neg/IHn/ltnSn.
Qed.

End Theory.

Section Application.

Notation R := Rdefinitions.R.

Local Open Scope R_scope.

  (** State of patient **)
Record state := State
         { C : R
         ; T : R
         ; wbc : R
         ; age : R
         ; weight : R}.

  (** Shows [tuple]'s and [state]'s are isomorphic. **)

Definition state_to_tuple (s : state) : 5.-tuple R :=
  [tuple C s; T s; wbc s; age s; weight s].

Definition tuple_to_state (t : 5.-tuple R) : state :=
  {| C := tnth t 0%R
  ; T := tnth t 1%R
  ; wbc := tnth t 2%R
  ; age := tnth t 3%R
  ; weight := tnth t 4%R
  |}.

Definition network (temp wbc age weight C : R)
  := ((pk (ntensor_of_tuple (state_to_tuple
     {| C := C
     ; T := temp
     ; wbc := wbc
     ; age := age
     ; weight := weight
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

Lemma const_t_leP {d : Order.disp_t} {R : porderType d} (t u : R) :
  (t <= u :> R)%O <-> (const_t t <= const_t u :> 'T_(nil, nil))%O.
Proof.
split; by rewrite -tensor_nil_leP !const_tK.
Qed.

(* Lemma const_t_eqP {d : Order.disp_t} {R : porderType d} (t u : R) : *)
(*   (t = u :> *)

Axiom vcl_fix : forall s' : state, (((normpk (ntensor_of_tuple (state_to_tuple s')))^^0 * Ka / (Vd * Ka - Ke) *
                    Ke_under - Ka_over) =
                 ((normpk (ntensor_of_tuple (state_to_tuple s')))^^0 * Ka / (Vd * (Ka - Ke)) *
                    ((Ke_under - Ka_over))))%R.

Axiom vcl_fix' : forall s' : state, (((normpk (ntensor_of_tuple (state_to_tuple s')))^^0 * Ka / (Vd * Ka - Ke) *
                    Ke_over - Ka_under) =
                 ((normpk (ntensor_of_tuple (state_to_tuple s')))^^0 * Ka / (Vd * (Ka - Ke)) *
                    ((Ke_over- Ka_under))))%R.

Definition error (x : R) := if (x < eps.[::])%R then 0%R else x.

Definition safeOutput (x : state) :=
  C x + Concentration Vd.[::] Ke.[::] Ka.[::] (error (normpk (ntensor_of_tuple (state_to_tuple x)))^^=0%R) (dCdt_root Ke.[::] Ka.[::]) <= C_safe.[::].

Lemma safe x : safeInput x -> safeOutput (tuple_to_state (tuple_of_ntensor x)).
Proof.
move=> safeInp.
move: (safeInp).
rewrite /safeInput => [[/andP Hc] [/andP Ht] [/andP HW] [/andP Ha] /andP Hw].
set s := tuple_to_state (tuple_of_ntensor x).
have Hsx : x = ntensor_of_tuple (state_to_tuple s).
  by rewrite /s tuple_to_stateK tuple_of_ntensorK.
case: (boolP ((C s) < (C_safe.[::] * (99/100)%coqR))%R)=>Hc'.
  have /safeFar : safeFarInput x.
    rewrite /safeFarInput.
    split.
      split.
        by move: Hc => /andP[c _].
      apply/ltW.
      rewrite -tensor_nil_ltP tensor_nilM [(const_t (_ / _)%coqR).[::]]const_tK.
      by rewrite Hsx ntensor_of_tupleE (tnth_nth 0).
    split.
      by apply/andP.
    split.
      by apply/andP.
    split.
      by apply/andP.
    by apply/andP.
  rewrite /safeFarOutput.
  case: ifP => Ke_Ka /ltW H.
    apply/RleP/le_trans; last first.
      rewrite -tensor_nil_leP in H.
      by apply: H.
    rewrite Hsx vcl_fix -!Hsx tensor_nilD.
    apply/lerD.
      by rewrite Hsx ntensor_of_tupleE (tnth_nth 0).
    rewrite /safeOutput /Concentration.
    rewrite !tensor_nilM tensor_nilV tensor_nilM !tensor_nilD !tensor_nilN.
    rewrite /error.
    case:ifP => He.
      rewrite -lerN2 -!mulNr -lerN2 -!mulrN.
      apply/ler_pM.
      - by rewrite oppr0 !mul0r.
      - rewrite opprB subr_ge0 ler_expR -subr_ge0 addrC !mulNr opprK subr_ge0.
        apply/ler_pM => //.
        + apply/ltW/const_t_ltP.
          by rewrite tensor_nilK Ka_pos.
        + rewrite /dCdt_root.
          apply/mulr_le0.
            apply/ln_le0.
            rewrite ler_pdivrMr ?mul1r ?tensor_nil_leP.
              by apply/ltW.
            by rewrite const_t_ltP tensor_nilK Ke_pos.
          rewrite invr_le0 subr_le0 tensor_nil_leP.
          by apply/ltW.
        + by apply/ltW/tensor_nil_ltP.
      - rewrite !mulNr -!mulrN.
        apply/ler_pM=> //.
        + by rewrite mul0r.
        + rewrite -oppr0 lerN2 invr_le0.
          apply/mulr_ge0_le0.
            apply/ltW.
            by rewrite const_t_ltP tensor_nilK Vd_pos.
          rewrite subr_le0 tensor_nil_leP.
          by apply/ltW.
        + apply/ler_pM => //.
            rewrite const_t_leP tensor_nilK.
            by apply/ltW/Ka_pos.
          rewrite const_t_leP tensor_nilK.
          by apply/ltW/nonNeg.
      - rewrite lerN2 /dCdt_root -!RlnE.
          rewrite -!RexpE -!RmultE -!RoppE -!RinvE -!RplusE !const_tK.
          apply/RleP.
          interval.
        apply/RltP.
        apply/divr_gt0.
          by rewrite const_t_ltP tensor_nilK Ka_pos.
        by rewrite const_t_ltP tensor_nilK Ke_pos.
    apply/ler_nmul_pos.
      apply/mulr_ge0_le0.
        apply/mulr_ge0.
          apply/ltW.
          rewrite const_t_ltP tensor_nilK.
          by apply/nonNeg.
        apply/ltW.
        rewrite const_t_ltP const_tK.
        by apply/Ka_pos.
      rewrite invr_le0.
      apply/mulr_ge0_le0.
        apply/ltW.
        by rewrite const_t_ltP tensor_nilK Vd_pos.
      rewrite subr_le0.
      by apply/ltW/tensor_nil_ltP.
    apply/lerD.
      rewrite !const_tK /dCdt_root -RexpE -RlnE -!RmultE -!RinvE.
        rewrite -!RoppE -!RplusE.
        apply/RleP.
        interval.
      interval.
    rewrite !const_tK /dCdt_root -RexpE -RlnE -!RmultE -!RinvE.
      rewrite -!RoppE -!RplusE.
      apply/RleP.
      interval.
    interval.
  rewrite /safeOutput /Concentration.
  apply/RleP/le_trans; last first.
    rewrite -tensor_nil_leP in H.
    by apply: H.
  rewrite Hsx vcl_fix' -!Hsx tensor_nilD.
  apply/lerD.
    by rewrite Hsx ntensor_of_tupleE (tnth_nth 0).
  rewrite !tensor_nilM tensor_nilV tensor_nilM !tensor_nilD !tensor_nilN.
  rewrite /error.
  case: ifP => He.
    apply/ler_pM.
    - by rewrite !mul0r.
    - rewrite subr_ge0 ler_expR -subr_ge0 addrC !mulNr opprK subr_ge0 //.
      apply/ler_pM => //.
      + apply/ltW/const_t_ltP.
        by rewrite tensor_nilK Ke_pos.
      + rewrite /dCdt_root.
        apply/divr_ge0.
          apply/ln_ge0.
          rewrite ler_pdivlMr.
            rewrite mul1r const_t_leP !tensor_nilK.
            move/negP: Ke_Ka.
            rewrite -tensor_nil_ltP ltNge => /negP /negPn.
            by rewrite -tensor_nil_leP.
          by rewrite const_t_ltP tensor_nilK Ke_pos.
        rewrite subr_ge0.
        move/negP: Ke_Ka.
        by rewrite -tensor_nil_ltP ltNge => /negP /negPn.
      + move/negP: Ke_Ka.
        by rewrite -tensor_nil_ltP ltNge => /negP /negPn.
    - apply/ler_pM => //.
      + by rewrite mul0r.
      + rewrite invr_ge0.
        apply/mulr_ge0.
          apply/ltW/const_t_ltP.
          by rewrite tensor_nilK Vd_pos.
        rewrite subr_ge0.
        rewrite -[(_ <= _)%R]negbK -ltNge.
        by apply/negP/tensor_nil_ltP/negP/negPf.
      + apply/ler_pM => //.
          apply/ltW/const_t_ltP.
          by rewrite tensor_nilK Ka_pos.
        apply/ltW/const_t_ltP.
        rewrite tensor_nilK.
        by apply/nonNeg.
    - apply/lerD.
        rewrite /dCdt_root -RlnE.
          rewrite -!RexpE -!RmultE -!RoppE !const_tK -RplusE -!RinvE.
          apply/RleP.
          interval.
        apply/RltP.
        by apply/divr_gt0;
        rewrite const_t_ltP tensor_nilK ?Ka_pos ?Ke_pos.
      rewrite -subr_ge0 addrC !mulNr opprK subr_ge0.
      rewrite /dCdt_root -RlnE.
        rewrite -!RexpE -!RmultE -!RoppE !const_tK -RplusE -!RinvE.
        apply/RleP.
        interval.
      apply/RltP.
      by apply/divr_gt0;
      rewrite const_t_ltP tensor_nilK ?Ka_pos ?Ke_pos.
  apply/ler_pmul_pos.
    apply/mulr_ge0.
      apply/mulr_ge0.
        rewrite const_t_leP tensor_nilK.
        by apply/ltW/nonNeg.
      apply/ltW.
      by rewrite const_t_ltP tensor_nilK Ka_pos.
    rewrite invr_ge0.
    apply/mulr_ge0.
      apply/ltW.
      by rewrite const_t_ltP tensor_nilK Vd_pos.
    rewrite subr_ge0 tensor_nil_leP.
    have : ~~ (Ka < Ke)%R by apply/negPf.
    move=> /negP.
    rewrite -tensor_nil_ltP.
    rewrite ltNge => /negP /negPn.
    by rewrite tensor_nil_leP.
  apply/lerD.
    rewrite /dCdt_root -RlnE.
      rewrite -RexpE /dCdt_root !const_tK.
      rewrite -!RmultE -!RoppE -!RinvE -!RplusE.
      apply/RleP.
      interval.
    apply/RltP.
    apply/divr_gt0;
    rewrite const_t_ltP const_tK.
      by apply/Ka_pos.
    by apply/Ke_pos.
  rewrite /dCdt_root -RlnE.
    rewrite -RexpE /dCdt_root !const_tK.
    rewrite -!RmultE -!RoppE -!RinvE -!RplusE.
    apply/RleP.
    interval.
  apply/RltP.
  apply/divr_gt0;
  rewrite const_t_ltP const_tK.
    by apply/Ka_pos.
  by apply/Ke_pos.
rewrite /safeOutput -Hsx.
suff -> : (error (normpk x)^^=0%R) = 0%R.
  rewrite conc_D0 -(addr0 (C_safe.[::])).
  apply/RleP/lerD => //.
  move/andP: Hc => [_ /tensor_nil_leP].
  by rewrite Hsx ntensor_of_tupleE (tnth_nth 0).
rewrite /error ifT //.
rewrite tensor_nil_ltP.
apply/safeNear.
rewrite /safeNearInput.
split.
  split.
    rewrite -tensor_nil_leP -[(_ <= _)%R]negbK -ltNge tensor_nilM.
    rewrite Hsx ntensor_of_tupleE (tnth_nth 0%R).
    by rewrite [X in (_ * X)%R]const_tK.
  by move/andP: Hc => [].
split.
  by apply/andP.
split.
  by apply/andP.
split.
  by apply/andP.
by apply/andP.
Qed.

Theorem pk_safe (n : nat) (t : R) (s : state) :
  safeInput (ntensor_of_tuple (state_to_tuple s)) ->
  (0 <= total_conc Vd.[::] Ke.[::] Ka.[::] ttd.[::] (@n_doses R Vd.[::] Ke.[::] Ka.[::] ttd.[::]
  (error \o (network s.(T) s.(wbc) s.(age) s.(weight))) (C s) n) t <= C_safe.[::])%R.
Proof.
move=> Hi.
apply/doses_safe => //=.
- by rewrite const_t_ltP const_tK Vd_pos.
- by rewrite const_t_ltP const_tK Ke_pos.
- by rewrite const_t_ltP const_tK Ka_pos.
- by rewrite const_t_ltP const_tK ttd_pos.
- rewrite subr_eq0.
  by apply/eqP/tensor_nil_eqP/eqP/Ke_n_Ka.
- rewrite /dCdt_root -RlnE.
    rewrite /Ke /Ka !const_tK.
    apply/RleP.
    rewrite -!RmultE -!RoppE -!RinvE -RplusE.
    interval.
  apply/Rlt_mult_inv_pos;
  apply/RltP;
  rewrite const_t_ltP const_tK.
    by apply/Ka_pos.
  by apply/Ke_pos.
- move=> C HC.
  set s' :=
  {|
C := C; T := T s; wbc := wbc s; age := age s; weight := weight s
  |}.
  suff /safe: safeInput (ntensor_of_tuple (state_to_tuple s')).
    rewrite /safeOutput ntensor_of_tupleK state_to_tupleK.
    by rewrite /s' /Application.C /network /normpk //= => /RleP.
  rewrite /safeInput.
  split.
    rewrite -!tensor_nil_leP !const_tK /ntensor_of_tuple /= nstackE const_tK.
    rewrite /conc /state_to_tuple tnth0 /s' /=.
    apply/andP.
    move: HC.
    by rewrite const_tK.
  move: Hi => [_].
  by rewrite -!tensor_nil_leP /s' !ntensor_of_tupleE !(tnth_nth 0) /=.
- move=> C HC.
  set s' :=
  {|
C := C; T := T s; wbc := wbc s; age := age s; weight := weight s;
  |}.
  suff /nonNeg: safeInput (ntensor_of_tuple (state_to_tuple s')).
    rewrite /nonNegOutput /error => /ltW.
    case:ifP => H //.
    by rewrite -tensor_nil_leP /normpk const_tK.
  rewrite /safeInput.
  split.
    rewrite -!tensor_nil_leP !const_tK /ntensor_of_tuple /= nstackE const_tK.
    rewrite /conc /state_to_tuple tnth0 /s' /=.
    apply/andP.
    move: HC.
    by rewrite const_tK.
  move: Hi => [_].
  by rewrite -!tensor_nil_leP !ntensor_of_tupleE.
- move: Hi => [H _].
  move: H.
  by rewrite -!tensor_nil_leP !const_tK ntensor_of_tupleE => /andP.
Qed.
