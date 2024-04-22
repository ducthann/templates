Require Import VST.concurrency.conclib.
From iris.algebra Require Import excl auth gmap agree gset.
Require Import flows.inset_flows.
Require Import flows.auth_ext.
Require Import flows.multiset_flows.
Require Import flows.flows.
Require Import iris_ora.algebra.gmap.
Require Import iris_ora.logic.own.
Require Import iris_ora.algebra.ext_order.
Require Import iris_ora.algebra.frac_auth.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import VST.floyd.library.
Require Import VST.atomics.verif_lock_atomic.
Require Import tmpl.puretree.
Require Import tmpl.flows_ora.
Require Import tmpl.giveup_template.
Require Import tmpl.keyset_ra_ora.

Definition Key := Z.

Section Give_Up_Cameras.
  Lemma flwint n (x y : @multiset_flowint_ur Key _ _): ✓{n} y → x ≼ₒ{n} y → x ≼{n} y.
    Proof.
      intros Hv Hxy; destruct y; destruct Hxy; subst; try done.
    Qed.
  Canonical Structure flow_authR := @authR _ flwint.

  (* RA for authoritative flow interfaces over multisets of keys *)
  Class flowintG Σ := FlowintG { flowint_inG :> inG Σ (flow_authR) }.
  Definition flowintΣ : gFunctors := #[GFunctor (flow_authR)].

  Instance subG_flowintΣ {Σ} : subG flowintΣ Σ → flowintG Σ.
  Proof. solve_inG. Qed.

  (* RA for authoritative sets of nodes *)
  
  Canonical Structure gset_authR A `{Countable A} := inclR(iris.algebra.auth.authR(gsetR A)).

  Class nodesetG Σ := NodesetG { nodeset_inG :> inG Σ (gset_authR Node ) }.
  Definition nodesetΣ : gFunctors := #[GFunctor (gset_authR Node )].

  Instance subG_nodesetΣ {Σ} : subG nodesetΣ Σ → nodesetG Σ.
  Proof. solve_inG. Qed.

  Lemma ks A `{Countable A} n  (x y : keysetUR A): ✓{n} y → x ≼ₒ{n} y → x ≼{n} y.
  Proof. intros Hv Hxy; destruct y; destruct Hxy; subst; try done. Qed.
  Canonical Structure keyset_authR A `{Countable A} := @authR _ (ks A).

  Class keysetG Σ := KeysetG { keyset_inG :> inG Σ (keyset_authR Key  ) }.
  Definition keysetΣ : gFunctors := #[GFunctor (keyset_authR Key)].

  Instance subG_keysetΣ {Σ} : subG (@keysetΣ) Σ → (@keysetG) Σ.
  Proof. solve_inG. Qed.
End Give_Up_Cameras.

Definition number2Z (x : number) : Z :=
  match x with
    | Finite_Integer y => y
    | Neg_Infinity => Int.min_signed
    | Pos_Infinity => Int.max_signed
  end.

(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
(* FOUND = F, NOTFOUND = NF, NULLNEXT = NN *)
Inductive enum : Type := F | NF | NN.

Definition enums x : val :=
  match x with
  | F => Vint Int.zero
  | NF => Vint Int.one
  | NN => Vint (Int.repr 2%Z)
  end.

#[global] Instance enum_inhabited : Inhabitant (enum).
Proof.
  unfold Inhabitant; apply F.
Defined.

Definition pointer_of (n : Node) :=  fst n.
Definition lock_of (n : Node) := fst (snd n).
Definition node_of (n : Node) := snd (snd n).
Definition min_of (rg: (number * number)) := fst rg.
Definition max_of (rg: (number * number)) := snd rg.


Section NodeRep.
Context `{!VSTGS unit Σ, !flowintG Σ, !nodesetG Σ, !keysetG Σ }.
Definition inFP (γ_f: gname) (n : Node) : mpred :=
    ∃ (N: gset Node),
      (own (inG0 := nodeset_inG)) γ_f (◯ N : gset_authR _) ∧ ⌜n ∈ N⌝.

Class NodeRep : Type := {
    node : Node → @multiset_flowint_ur Key _ _ → gset Key → mpred;
    (* node_sep_star: ∀ n I_n I_n' C C', node n I_n C ∗ node n I_n' C' -∗ False; *)
    node_rep_R_valid_pointer: forall n I_n C, node n I_n C -∗ valid_pointer (pointer_of n);
    node_rep_R_pointer_null: forall n I_n C, node n I_n C -∗ ⌜is_pointer_or_null (pointer_of n)⌝;
    node_size: nat;
}.

Global Instance inFP_persistent γ_f n: Persistent (inFP γ_f n).
Proof.
  apply bi.exist_persistent.
  intros x.
  apply bi.and_persistent.
  apply own_core_persistent.
  apply (iris.algebra.auth.auth_frag_core_id _ ).
  apply _. apply _.
Qed.

End NodeRep.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


(*

*)
