From mathcomp Require Import all_boot all_order all_algebra all_classical all_analysis all_reals ring lra.
(* From vehicle Require Import tensor. *)
From HB Require Import structures.
Import Num.Theory GRing.Theory Order.POrderTheory.
Import numFieldNormedType.Exports.
(* Import numFieldTopology.Exports. *)

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

Definition conc_f (D : R) : R -> R :=
  cst ((D * Ka) / (Vd * (Ka - Ke))) \* ((expR \o *%R (- Ke)) - (expR \o *%R (- Ka))).

Lemma conc_equiv (D : R) : Concentration D = conc_f D.
Proof.
  apply/funext => t.
  by rewrite /Concentration /conc_f /=.
Qed.

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
  rewrite !unitfE => //.
  apply/andP.
  by split;
  [ | apply/lt0r_neq0].
  by apply lt0r_neq0.
Qed.

Lemma mulr0I {a b : R} : a \is a GRing.unit -> a * b = 0 <-> b = 0.
Proof.
  move=> H.
  split => H0.
  apply/(mulrI H).
  by rewrite mulr0.
  by rewrite H0 mulr0.
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
  rewrite mulrBl exp.expRB -expRN.
  apply/(@mulfI _ Ke);
  first by apply/lt0r_neq0.
  rewrite !mulrA (mulrC Ke Ka) -!mulrA (mulrV unitr_Ke) mulr1 mulrA.
  apply/(@mulfI _ (expR (Ka * t))^-1);
  first by apply/lt0r_neq0; rewrite invr_gt0; apply/expR_gt0.
  by rewrite !mulrA (mulrC (expR _)^-1 Ke) -(mulrA Ke _ _) (mulVr (unitr_n0expR _)) mulrC mulr1 /= -expRN -mulNr mulrC (mulrC (expR _) Ka) -mulNr.
  move=> H0.
  rewrite H0 /dCdt /dCdt_root (mulr0I (left_is_unit H)).
  apply/eqP.
  rewrite subr_eq0.
  apply/eqP/ln_inj;
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

Lemma ler_nmul_pos (a b c : R) : a < 0 -> c <= b -> a * b <= a * c.
Proof.
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
  apply/ler_pM; [by apply/ltW | by apply/expR_ge0 | by apply/ltW | ].
  rewrite ler_expR -subr_le0 addrC !mulNr opprK subr_le0 mulrC (mulrC Ke) ler_nM2l //.
  by apply/ltW.
  by apply divr_gt0; [by rewrite pmulr_lgt0 | by rewrite pmulr_lgt0 ?subr_gt0].
  rewrite nmulr_rge0 ?subr_le0.
  apply/ler_pM; [by apply/ltW | by apply/expR_ge0 | by apply/ltW | ].
  rewrite ler_expR -subr_le0 addrC !mulNr opprK subr_le0 mulrC (mulrC Ka) ler_nM2l //.
  by apply/ltW.
  by rewrite nmulr_llt0; [rewrite pmulr_lgt0 //= |rewrite invr_lt0 nmulr_llt0 //= subr_lt0].
  exfalso.
  move/eqP: Ke_n_Ka.
  lra.
  (* 0 < t *)
  case: (ltgtP Ke Ka) => HKeKa.
  rewrite pmulr_rge0.
  rewrite subr_ge0.
  rewrite -ler_ln ?lnM ?posrE ?pmulr_rgt0 ?expR_gt0 // !expRK -subr_le0 !mulNr.
  rewrite (_ : (ln Ke - Ke * t - (ln Ka - Ka * t)) = (- (ln Ka - ln Ke) + Ka * t - Ke * t)); last lra.
  rewrite -ln_div // -mulNr -addrA -mulrDl addrC subr_le0.
  rewrite -(@ler_pM2l _ ((Ka - Ke)^-1));
  last by rewrite invr_gt0; lra.
  rewrite (mulrC (Ka - Ke) t) mulrA (mulrC _ t) -mulrA mulVf.
  rewrite mulr1 mulrC.
  apply/ltW.
  move: Ht.
  by rewrite in_itv //= /dCdt_root.
  lra.
  rewrite pmulr_rgt0.
  rewrite invr_gt0 pmulr_rgt0 //.
  lra.
  by rewrite pmulr_rgt0.
  rewrite nmulr_rge0.
  rewrite subr_le0.
  rewrite -ler_ln ?lnM ?posrE ?pmulr_rgt0 ?expR_gt0 // !expRK -subr_le0 !mulNr.
  rewrite (_ : (ln Ka - Ka * t - (ln Ke - Ke * t)) = ((ln Ka - ln Ke) - (Ka * t - Ke * t))); last lra.
  rewrite -ln_div // -mulNr -mulrDl subr_le0.
  rewrite -(@ler_nM2l _ ((Ka - Ke)^-1));
  last by rewrite invr_lt0; lra.
  rewrite mulrA (mulrC _ t) mulVf.
  rewrite mulr1 mulrC.
  apply/ltW.
  move: Ht.
  by rewrite in_itv //= /dCdt_root.
  lra.
  rewrite pmulr_rlt0.
  rewrite invr_lt0 pmulr_rlt0 //.
  lra.
  by rewrite pmulr_rgt0.
  exfalso.
  move/eqP: Ke_n_Ka.
  lra.
  (* t = 0 *)
  rewrite Ht0 !mulr0 exp.expR0 !mulr1.
  case: (ltgtP Ke Ka) => HKeKa.
  rewrite pmulr_rge0.
  by apply/ltW; rewrite subr_gt0.
  by rewrite pmulr_rgt0;[ rewrite invr_gt0 pmulr_rgt0 // subr_gt0 | rewrite pmulr_rgt0].
  rewrite nmulr_rge0.
  by apply/ltW; rewrite subr_lt0.
  by rewrite pmulr_rlt0;[ rewrite invr_lt0 pmulr_rlt0 // subr_lt0 | rewrite pmulr_rgt0].
  exfalso.
  move/eqP: Ke_n_Ka.
  lra.
Qed.

Lemma deriv_is_neg (D t : R) (HD : 0 < D) (Ht : t \in `]dCdt_root, +oo[%R) :
 ((Concentration D)^`() t <= 0).
Proof.
  rewrite derivative_correct /dCdt.
  case: (ltgtP Ke Ka) => HKeKa.
  rewrite pmulr_rle0.
  rewrite subr_le0.
  rewrite -ler_ln ?lnM ?posrE ?pmulr_rgt0 ?expR_gt0 // !expRK -subr_le0 !mulNr.
  rewrite (_ : (ln Ka - Ka * t - (ln Ke - Ke * t)) = ((ln Ka - ln Ke) - (Ka * t - Ke * t))); last lra.
  rewrite -ln_div // -mulNr -mulrDl subr_le0.
  rewrite -(@ler_pM2l _ ((Ka - Ke)^-1));
  last by rewrite invr_gt0; lra.
  rewrite (mulrC (Ka - Ke) t) mulrA (mulrC _ t) -mulrA mulVf.
  rewrite mulr1 mulrC.
  apply/ltW.
  move: Ht.
  by rewrite in_itv //= /dCdt_root => /andP [].
  lra.
  rewrite pmulr_rgt0.
  rewrite invr_gt0 pmulr_rgt0 //.
  lra.
  by rewrite pmulr_rgt0.
  rewrite nmulr_rle0.
  rewrite subr_ge0.
  rewrite -ler_ln ?lnM ?posrE ?pmulr_rgt0 ?expR_gt0 // !expRK -subr_le0 !mulNr.
  rewrite (_ : (ln Ke - Ke * t - (ln Ka - Ka * t)) = (-(ln Ka - ln Ke) + (Ka * t - Ke * t))); last lra.
  rewrite -ln_div // -mulNr -mulrDl addrC subr_le0.
  rewrite -(@ler_nM2l _ ((Ka - Ke)^-1));
  last by rewrite invr_lt0; lra.
  rewrite mulrA (mulrC _ t) mulVf.
  rewrite mulr1 mulrC.
  apply/ltW.
  move: Ht.
  by rewrite in_itv //= /dCdt_root => /andP [].
  lra.
  rewrite pmulr_rlt0.
  rewrite invr_lt0 pmulr_rlt0 //.
  lra.
  by rewrite pmulr_rgt0.
  exfalso.
  move/eqP: Ke_n_Ka.
  lra.
Qed.

Lemma conc_D0 : Concentration 0 = 0.
Proof.
  apply funext => t.
  by rewrite /Concentration !mul0r.
Qed.

Lemma root_is_max (D t : R) (HD : 0 <= D) (Ht : 0 <= t) :
  Concentration D t <= Concentration D dCdt_root.
Proof.
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
  by apply deriv_is_neg.
  apply/derivable_within_continuous => /= t' _.
  rewrite derivable1_diffP.
  by apply conc_diff.
  by apply/ltW.
Qed.

(** Time to dose **)
Variables ttd : R.

Hypothesis ttd_pos : ttd > 0.

Hypothesis ttd_dCdt_root : dCdt_root < ttd.

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
Lemma continuous_sum {n} (f : 'I_n -> R -> R) : (forall i : 'I_n, continuous (f i)) -> continuous (fun t => \sum_(i < n) f i t).
Proof.
  rewrite /=.
  rewrite sum_apply.
  move: n f.
  elim => [f H x | n IHf f H x].
  rewrite big_ord0.
  by apply/cst_continuous.
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
  by apply differentiable_cst.
  rewrite big_ord_recr /= -derivable1_diffP.
  apply derivableD;
  rewrite derivable1_diffP; [by apply/IHf | by apply/ H].
Qed.

Lemma derive_sum {n} (f : 'I_n -> R -> R) (t : R) :
  (forall i : 'I_n, differentiable (f i) t) -> 'D_1 (fun t => \sum_(i < n) f i t) t = \sum_(i < n) ('D_1 (f i) t).
Proof.
  rewrite /= sum_apply.
  move: n f.
  elim => [f H | n IHf f H].
  by rewrite !big_ord0 derive_cst.
  rewrite !big_ord_recr /= deriveD;[ by rewrite IHf | rewrite derivable1_diffP | rewrite derivable1_diffP]; [by apply/differentiable_sum | by apply/H].
Qed.

Lemma total_conc_cont {n} (Ds : n.-tuple R) :
  continuous (total_conc Ds).
Proof.
  rewrite /total_conc.
  apply continuous_sum => i.
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

Lemma max_diff_eq (f g : R -> R) (H : f = g) : (f \max g)^`() = f^`().
Proof.
  by rewrite -H max_eq.
Qed.

Lemma differentiable_max_eq (f g : R -> R) (t : R) (H : f =1 g) (Hf :differentiable f t) :
  differentiable (f \max g) t.
Proof.
  rewrite /Order.max_fun.
  suff : (fun x => maxr (f x) (g x)) = f => [-> | ].
  by apply Hf.
  apply funext => x.
  by rewrite H /maxr ifN // ltxx.
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

Lemma total_conc_diff_correct n (t : R) (Ds : n.-tuple R) (HDs : all [pred x | 0 <= x] Ds) (Ht : forall m : nat, m < n -> t <> ttd * m%:R) :
  (total_conc Ds)^`() t = total_conc_diff Ds t.
  rewrite derive1E /total_conc derive_sum.
  rewrite /total_conc_diff.
  apply/eq_bigr => i _.
  case (ltgtP 0 (Concentration (tnth Ds i) (t - ttd * i %:R))) => /eqP /eqP H.
  rewrite H.
  rewrite -derive1E derive1_comp //.
  rewrite derive1_id mulr1 // derive1_comp //.
  rewrite !derive1E /= deriveD // derive_id derive_cst addr0 mulr1 -derive1E.
  by rewrite max_diffr /=; [ rewrite derivative_correct mulNr | rewrite mulNr | apply/cst_continuous | apply/conc_cont].
  rewrite derivable1_diffP.
  apply/differentiable_max; [ apply/eqP; by rewrite eq_sym lt0r_neq0 // mulNr | apply/differentiable_cst | apply/conc_diff].
  rewrite derivable1_diffP.
  apply differentiable_comp => //.
  apply/differentiable_max; [ apply/eqP; by rewrite eq_sym lt0r_neq0 // mulNr | apply/differentiable_cst | apply/conc_diff].
  rewrite ifF.
  rewrite -derive1E derive1_comp //.
  rewrite !derive1E derive_id mulr1 -derive1E derive1_comp //.
  by rewrite !derive1E /= deriveD // derive_id derive_cst addr0 mulr1 -derive1E max_diffl /=;[ by rewrite derive1_cst | by rewrite mulNr | by apply:cst_continuous | by apply conc_cont].
  case: (boolP ((tnth Ds i) == 0)) => [/eqP -> | /eqP HDs_i];
  rewrite derivable1_diffP.
  rewrite conc_D0.
  by apply:differentiable_max_eq.
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
  by rewrite max_diff_eq;[ by rewrite derive1E derive_cst mul0r ifF // -H ltxx | by rewrite HDs_i conc_D0 /=].
  rewrite HDs_i conc_D0 derivable1_diffP.
  by apply differentiable_max_eq.
  rewrite HDs_i conc_D0 derivable1_diffP.
  by apply differentiable_max_eq.
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
  by rewrite mulrI_eq0 => [ /eqP | ];
  [ lra
  | by apply mulfI].
  apply/unitrPr.
  exists (tnth Ds i * Ka / (Vd * (Ka - Ke)))^-1.
  by apply/mulfV/mulf_neq0;
  [ apply/mulf_neq0; [ by apply/eqP | by apply lt0r_neq0] |
  apply/invr_neq0/mulf_neq0; [by apply lt0r_neq0 | by apply Ke_n_Ka]].
  move=> i.
  apply/differentiable_comp.
  by rewrite -derivable1_diffP; apply/derivable_id.
  apply/differentiable_comp => //.
  case: (boolP ((tnth Ds i) == 0)) => /eqP HDs_i.
  rewrite HDs_i conc_D0.
  by apply differentiable_max_eq.
  rewrite max_swap.
  apply/differentiable_max; [ | by apply/conc_diff | by apply/differentiable_cst].
  rewrite /Concentration.
  apply/eqP/mulf_neq0.
  by apply/mulf_neq0;
  [ apply/mulf_neq0; [ by apply/eqP | by apply/lt0r_neq0]
  | apply/invr_neq0/mulf_neq0;[ by apply/lt0r_neq0 | by apply Ke_n_Ka]].
  apply/eqP => /subr0_eq/expR_inj /= /eqP.
  by rewrite -subr_eq0 addrC mulNr opprK -mulrDl mulNr mulrI_eq0  => [/eqP/subr0_eq | ];
  [ by apply/ (Ht i)/ltn_ord
  | by apply mulfI].
Qed.

(* Reduced network because im only reasoning on the concentration atm *)
Parameter network : R -> R.

Axiom safe : forall C : R, 0 <= C + (Concentration (network C) dCdt_root) <= 30.
Axiom non_neg : forall C : R, 0 <= network C.

Lemma conc_t0 (D : R) : Concentration D 0 = 0.
Proof.
  rewrite /Concentration !mulr0 !expR0.
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
  rewrite pmulr_rgt0;
  [ by rewrite invr_gt0 pmulr_rgt0 // subr_gt0
  | by rewrite pmulr_rgt0].
  rewrite nmulr_rlt0.
  rewrite subr_gt0 ltr_expR mulrC (mulrC (-Ke)).
  apply/ltr_nmul_pos => //.
  lra.
  rewrite pmulr_rlt0;
  [ by rewrite invr_lt0 pmulr_rlt0 // subr_lt0
  | by rewrite pmulr_rgt0].
Qed.

Lemma conc_non_neg (D t : R) : 0 <= D -> 0 <= t -> 0 <= Concentration D t.
Proof.
  move=> HD Ht.
  rewrite /Concentration.
  case (boolP (D == 0)) => [/eqP -> | ];
                          first by rewrite !mul0r lexx.
  case (boolP (t == 0)) => [/eqP -> | ].
  by rewrite !mulr0 !expR0 subrr mulr0 lexx.
  move: Ht.
  rewrite le_eqVlt => /orP [/eqP -> /eqP //| Ht _].
  move: HD.
  rewrite le_eqVlt => /orP [/eqP -> /eqP // | HD _].
  case: (ltgtP Ke Ka) => HKeKa.
  rewrite pmulr_rge0.
  rewrite subr_ge0 ler_expR -subr_ge0 addrC mulNr opprK -mulrDl pmulr_rge0;
  [ by apply/ltW
  | by rewrite subr_gt0].
  by rewrite pmulr_rgt0;
  rewrite ?invr_gt0 pmulr_rgt0 // subr_gt0.
  rewrite nmulr_rge0.
  rewrite subr_le0 ler_expR -subr_ge0 addrC mulNr opprK -mulrDl pmulr_rge0;
  [ by apply/ltW
  | by rewrite subr_gt0].
  by rewrite pmulr_rlt0;
  [by rewrite invr_lt0 pmulr_rlt0 // subr_lt0
  | by rewrite pmulr_rgt0].
  move: Ke_n_Ka.
  rewrite HKeKa.
  lra.
Qed.

Lemma conc_pos (D t : R) : 0 < D -> 0 < t -> 0 < Concentration D t.
Proof.
  move=> HD Ht.
  rewrite /Concentration.
  case: (ltgtP Ke Ka) => H.
  rewrite pmulr_rgt0.
  by rewrite subr_gt0 ltr_expR -subr_gt0 addrC mulNr opprK -mulrDl pmulr_rgt0 // subr_gt0.
  by rewrite pmulr_rgt0;
  rewrite ?invr_gt0 pmulr_rgt0 // subr_gt0.
  rewrite nmulr_rgt0.
  by rewrite subr_lt0 ltr_expR -subr_lt0 addrC mulNr opprK -mulrDl nmulr_rlt0 // subr_lt0.
  rewrite pmulr_rlt0;
  [ by rewrite invr_lt0 pmulr_rlt0 // subr_lt0
  | by rewrite pmulr_rgt0].
  move: Ke_n_Ka.
  lra.
Qed.

Lemma total_conc_differentiable {n} (Ds : n.-tuple R) (t : R) (Ht : forall m : nat, m < n -> t <> ttd * m%:R) (HDs : all [pred x | 0 <= x] Ds) : differentiable (total_conc Ds) t.
Proof.
  rewrite /total_conc.
  rewrite (_ : (fun t => _) = \sum_(i < n) ((cst 0 \max Concentration (tnth Ds i)) \o shift (- ttd * i%:R))); last by apply sum_apply.
  apply differentiable_sum => i.
  apply differentiable_comp => //.
  case: (boolP ((tnth Ds i) == 0)) => [/eqP -> | /eqP H'].
  rewrite conc_D0.
  by apply differentiable_max_eq.
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

Fixpoint n_doses (initial : R) (n : nat) : n.+1.-tuple R :=
  match n with
  | 0 => [:: (network initial)]
  | n'.+1 =>
      let Doses := n_doses initial n' in
      rcons Doses (network (total_conc Doses (ttd *+ (n'.+1))))
  end.

Lemma maxr_eq (x y z w : R) : x = y -> z = w -> maxr x z = maxr y w.
Proof.
  move=> Hx Hz.
  rewrite /maxr.
  case (ltgtP x z) => H;
  [ by rewrite H -Hx -Hz H
  | by rewrite ifN ?ifN; lra
  | by rewrite -Hz -Hx H].
Qed.

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

Lemma n_doses_pos (n : nat) (initial : R) : all [pred x | 0 <= x] (n_doses initial n).
Proof.
  apply/allP.
  move: n.
  elim => /= [n | n IHn x] /=.
  rewrite mem_seq1 => /eqP ->.
  by apply/non_neg.
  rewrite mem_rcons in_cons => /orP [/eqP -> | H].
  apply non_neg.
  by apply IHn.
Qed.

Theorem doses_safe (n : nat) (initial t : R) (HC : 0 <= initial) (Ht : 0 <= t) :
  total_conc (n_doses initial n) t <= 30.
Proof.
  move: n.
  elim => [ | n IHn].
  rewrite //= /total_conc big_ord1 /= (tnth_nth 0) /= mulr0 addr0 /maxr.
  case: (ltgtP 0 (Concentration (network initial) t)) => // _.
  have := (safe initial) => /andP [H H'].
  apply/(le_trans _ H').
  rewrite -(addr0 (Concentration (network initial) t)) addrC.
  apply/lerD => //.
  apply root_is_max => //=.
  by apply/non_neg.
  case: (ltgtP t (ttd *+ n.+1)) => Ht_ttd.
  rewrite unfold_n_dose_once /=.
  rewrite /maxr ifN ?addr0 // ltNge negbK le_eqVlt.
  apply/orP.
  case (ltgtP 0 (network (total_conc (n_doses initial n) (ttd * n.+1%:R)))).
  right.
  apply conc_neg => //.
  lra.
  have := (non_neg (total_conc (n_doses initial n) (ttd * n.+1%:R))).
  lra.
  move=> <-.
  left.
  by rewrite conc_D0.
  rewrite unfold_n_dose_once /=.
  set C' := Concentration _ _.
  have : 0 <= C'.
  rewrite /C'.
  apply conc_non_neg;
  [ by apply non_neg
  | lra].
  rewrite le_eqVlt => /orP [/eqP <- //= | ].
  by rewrite /maxr ifF ?ltxx ?addr0.
  rewrite /maxr => ->.
  rewrite /C'.
  have/andP [_] := (safe (total_conc (n_doses initial n) (ttd * n.+1%:R))).
  apply/le_trans/lerD.
  apply (ler0_derive1_nincry (a := ttd *+ n.+1)).
  move=> x.
  rewrite in_itv /= => /andP [Hx _].
  apply/derivable1_diffP/total_conc_differentiable.
  move=> m Hm.
  apply/eqP.
  rewrite neq_lt.
  apply/orP.
  right.
  have : (ttd * m%:R < ttd * n.+1%:R);last lra.
  apply/ltr_pmul_pos => //.
  by rewrite ltr_nat.
  exact: (n_doses_pos n initial).
  move=> x Hx.
  rewrite total_conc_diff_correct /total_conc_diff.
  apply sumr_le0 => i _.
  case: (boolP (tnth (n_doses initial n) i == 0)) => [/eqP -> | /eqP HDs_i].
  by rewrite ifN //= conc_D0 ltxx.
  rewrite ifT.
  rewrite -derivative_correct.
  apply: deriv_is_neg.
  have := n_doses_pos n initial => /allP /= /(_ (tnth (n_doses initial n) i) (mem_tnth i (n_doses initial n))).
  rewrite le_eqVlt => /orP [/eqP | //] .
  lra.
  move: Hx.
  rewrite !in_itv /= => /andP [H _].
  apply/andP.
  split => //.
  rewrite -subr_lt0 addrC opprB addrC addrA subr_lt0.
  move: H.
  apply lt_trans.
  rewrite mulrS.
  apply ltr_leD => //.
  rewrite -(mulr_natr ttd n).
  apply ler_pmul_pos => //.
  rewrite ler_nat -ltnS.
  by apply ltn_ord.
  apply/conc_pos.
  have := n_doses_pos n initial => /allP /= /(_ (tnth (n_doses initial n) i) (mem_tnth i (n_doses initial n))).
  rewrite le_eqVlt => /orP [/eqP | //] .
  lra.
  move: Hx.
  rewrite in_itv /= subr_gt0 => /andP [H _].
  apply/(lt_trans _ H).
  rewrite -(mulr_natr ttd n.+1).
  apply ltr_pmul_pos => //.
  rewrite ltr_nat.
  by apply ltn_ord.
  by apply (n_doses_pos n initial).
  move=> m Hm.
  suff : (ttd * m%:R < x); first lra.
  apply/lt_trans; last first.
  move: Hx.
  rewrite in_itv /= => /andP [H _].
  apply H.
  rewrite -(mulr_natr ttd n.+1).
  apply/ltr_pmul_pos => //.
  by rewrite ltr_nat.
  by apply/continuous_subspaceT/total_conc_cont.
  lra.
  lra.
  apply root_is_max => //.
  apply non_neg.
  lra.
  rewrite unfold_n_dose_once /= Ht_ttd.
  rewrite -(mulr_natr ttd) mulNr subrr conc_t0 /maxr ifF ?ltxx // addr0 mulr_natr.
  apply:(le_trans _ IHn).
  by rewrite Ht_ttd.
Qed.

End Theory.
