(*Require Import VST.concurrency.conclib. *)
Require Import flows.flows.
Require Import flows.multiset_flows.
From iris_ora Require Export ora.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.

Global Instance Node_EqDecision:  EqDecision Node.
Proof.
  unfold EqDecision, Decision.
  intros.
  decide equality. decide equality.
  apply Val.eq. apply Val.eq. apply Val.eq.
Qed.

Global Instance val_EqDecision:  EqDecision val.
Proof.
  unfold EqDecision, Decision.
  intros.
  apply Val.eq. 
Qed.

Global Instance Node_countable : Countable Node.
Proof. unfold Node. Admitted.

Section flows.
  Context `{flowdom : Type} `{CCM flowdom}.
  Print Node.
  Local Instance flows_order : OraOrder flowintT := fun (a b: flowintT) => a = b \/ b = intUndef.
  
  Print flowintT.
  
  Lemma Increasing_flows : forall a, Increasing a <-> a = ε \/ a = intUndef.
  Proof.
  split; intros Ha.
  - specialize (Ha ε).
    rewrite right_id in Ha.
    inversion Ha; auto.
  - intros ?; destruct Ha.
    + subst a. rewrite left_id; hnf; auto. 
    + hnf. subst a. right.
      by rewrite (intComp_undef_op).
  Qed.

  Definition flows_ora_mixin : DORAMixin flowintT.
  Proof.
    split; try apply _; try done.
    - intros ???.
      rewrite Increasing_flows.
      destruct x; inversion H0; auto.
    - intros ???; inversion H0; hnf; auto.
    - intros ?????; inversion H0; subst; eexists; split; eauto; hnf; [left|right]; auto.
    - intros ?????; inversion H1; subst; auto; hnf; auto. 
    - intros ????; inversion H0; subst; hnf; [left | right]; auto; by pose proof (intComp_undef_op y). 
    - intros ????; inversion H1; subst; [auto | contradiction].
    - intros ???;
      destruct cx; unfold pcore, flowintRAcore; destruct x; intros H0;
      inversion H; subst; try eauto.
      destruct (int f0 ⋅ y); eexists; split; try done; subst; hnf; [left | right]; eauto;
      eexists.
      + rewrite (intComp_undef_op y);
        eexists; split; last first; eauto; hnf; auto.
      + inversion H0; subst. inversion H3.
      + rewrite (intComp_undef_op y).
        eexists; split; eauto; hnf; auto.
  Qed.
  
  Canonical Structure flowsRA := discreteOra flowintT flows_ora_mixin.
  Global Instance flows_ora_discrete : OraDiscrete flowintT.
  Proof.
    apply discrete_ora_discrete.
  Qed.
  
  Canonical Structure flowintUR : uora := Uora flowintT flowint_ucmra_mixin.
End flows.

Section multiset_flow.
Context `{Countable K}. 
  Definition K_multiset := nzmap K nat.
  Global Instance K_multiset_ccm : CCM K_multiset := lift_ccm K nat.
  Global Canonical Structure multiset_flowint_ur : uora := @flowintUR K_multiset _.
End multiset_flow.
