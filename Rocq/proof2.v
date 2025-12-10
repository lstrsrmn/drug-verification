From mathcomp Require Import all_ssreflect all_algebra order reals lra seq tuple ssrbool ssrfun order exp constructive_ereal derive sequences eqtype normed_module Rstruct normedtype topology ring.
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

Definition Vd : R := 10.
Definition Ke : R := 3.
Definition Ka : R := 4.

Definition Concentration (D t : R) : R :=
  ((D * Ka) / (Vd * (Ka - Ke))) * (expR ((-Ke) * t) - expR ((-Ka) * t)).

Definition dCdt (D t : R) : R :=
  ((D * Ka / (Vd * (Ka - Ke)))) * (Ka * (expR (-Ka * t)) - Ke * (expR (-Ke * t))).

Definition dCdt_root : R :=
  (ln (Ka/Ke)) / (Ka - Ke).

Lemma conc_diff (D t : R) : differentiable (Concentration D) t.
Proof.
  by apply /differentiableZ /differentiableB;
  apply /differentiable_comp /derivable1_diffP /derivable_expR.
Qed.

Lemma derivative_correct : forall D t : R, (Concentration D)^`() t = dCdt D t.
Proof.
  move=> D t.
  rewrite derive1E.
  rewrite deriveZ => /=;
  last by apply /derivableB;
  by apply /derivable1_diffP /differentiable_comp;[apply/differentiableM /derivable1_diffP /derivable_id /derivable1_diffP /derivable_cst | apply/derivable1_diffP /derivable_expR].
  rewrite deriveB => /=;
  [| apply /derivable1_diffP /differentiable_comp;[apply/differentiableM /derivable1_diffP /derivable_id /derivable1_diffP /derivable_cst | apply/derivable1_diffP /derivable_expR]
  | apply /derivable1_diffP /differentiable_comp;[apply/differentiableM /derivable1_diffP /derivable_id /derivable1_diffP /derivable_cst | apply/derivable1_diffP /derivable_expR]].
  rewrite -derive1E derive1_comp; [| apply: derivableM; [apply/derivable_cst | apply/derivable_id] | apply/derivable_expR].
  rewrite !derive1E deriveZ; last by apply/derivable_id.
  rewrite derive_id -!derive1E derive1_comp;
  [| apply: derivableM; [apply/derivable_cst | apply/derivable_id]
  | apply/derivable_expR].
  rewrite !derive1E deriveZ; last by apply/derivable_id.
  rewrite derive_id (congr1 (fun f => f (-Ke * t)) (derive_expR R)) (congr1 (fun f => f (-Ka * t)) (derive_expR R)).
  rewrite scalerBr !scalerA !scaler1 /dCdt.
  ring.
Qed.

Lemma root_correct (D t : R) :
 D != 0 -> dCdt D t = 0 -> t = dCdt_root.
Proof.
  rewrite/dCdt /dCdt_root mulrBr=> H /subr0_eq /mulrI.
  have : (D * Ka / (Vd * (Ka - Ke))) \is a GRing.unit.
  rewrite unitrM.
  apply/andP.
  split.
  rewrite unitrM.
  apply/andP.
  split.
  apply/unitrP.
  exists D^-1.
  split;
    [apply/mulVf | apply/mulfV]=> //=.
  apply/unitrP.
  exists Ka^-1.
  split;
    [apply/mulVf/eqP | apply/mulfV/eqP]=> //=;
  lra.
  apply/unitrP.
  exists (Vd * (Ka - Ke)).
  split;
    [apply/mulfV/eqP | apply/mulVf/eqP]=> //=;
  lra.
  move=> -> /= /(_ isT) H0.
  have H1: Ka - Ke != 0;
  first lra.
  apply/(mulfI H1).
  rewrite mulrA.
  rewrite (mulrC (Ka - Ke) (ln _)).
  rewrite -mulrA.
  rewrite mulrV.
  rewrite mulr1.
  apply expR_inj.
  rewrite lnK.
  rewrite mulrBl.
  rewrite expRB.
  apply/(@mulfI _ Ke).
  lra.
  rewrite !mulrA.
  rewrite (mulrC Ke Ka).
  rewrite -!mulrA.
  rewrite mulrV.
  rewrite mulr1.
  rewrite mulrA.
  apply/(@mulfI _ (expR (Ke * t))).
  apply/lt0r_neq0.
  apply/expR_gt0.
  rewrite !mulrA.
  rewrite mulrC.
  rewrite !mulrA.
  rewrite mulVr.
  rewrite mul1r.

(* Need to say that for the Concentration function, dCdt is the derivative and dCdt_root is the global maximum *)

Definition next_state : 
