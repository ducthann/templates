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
Definition Value := val.

Section Give_Up_Cameras.
  Lemma flwint n (x y : @multiset_flowint_ur Key _ _): ✓{n} y → x ≼ₒ{n} y → x ≼{n} y.
  Proof. intros Hv Hxy; destruct y; destruct Hxy; subst; try done. Qed.
  Canonical Structure flow_authR := @authR _ flwint.

  (* RA for authoritative flow interfaces over multisets of keys *)
  Class flowintG Σ := FlowintG { flowint_inG :> inG Σ (flow_authR) }.
  Definition flowintΣ : gFunctors := #[GFunctor (flow_authR)].

  Instance subG_flowintΣ {Σ} : subG flowintΣ Σ → flowintG Σ.
  Proof. solve_inG. Qed.

  (* RA for authoritative sets of nodes *)

  Canonical Structure gmap_authR K A `{Countable K} :=
    inclR(iris.algebra.auth.authR(iris.algebra.gmap.gmapR K A)).

  Locate agree.
  Check iris.algebra.agree.agree.
  Class nodemapG Σ := NodesetG { nodemap_inG :> inG Σ (gmap_authR Node (iris.algebra.agree.agree (prodO val val))) }.
  Definition nodemapΣ : gFunctors := #[GFunctor (gmap_authR Node (iris.algebra.agree.agree (prodO val val)))].

  Locate agree.

  Instance subG_nodemapΣ {Σ} : subG nodemapΣ Σ → nodemapG Σ.
  Proof. solve_inG. Qed.

(*
  
  Canonical Structure gset_authR A `{Countable A} := inclR(iris.algebra.auth.authR(gsetR A)).

  Class nodesetG Σ := NodesetG { nodeset_inG :> inG Σ (gset_authR Node ) }.
  Definition nodesetΣ : gFunctors := #[GFunctor (gset_authR Node )].

  Instance subG_nodesetΣ {Σ} : subG nodesetΣ Σ → nodesetG Σ.
  Proof. solve_inG. Qed.
*)

  (* keymap *)

  Canonical Structure keymap_authR K A `{Countable K} :=
    inclR(iris.algebra.auth.authR(iris.algebra.gmap.gmapR K A)).

  Class keymapG Σ := KeymapG { keymap_inG :>
                                 inG Σ (keymap_authR Key (iris.algebra.excl.exclR (discreteO val)))}.
  Definition keymapΣ : gFunctors :=
    #[GFunctor (keymap_authR Key (iris.algebra.excl.exclR (discreteO val)))].

  Instance subG_keymapΣ {Σ} : subG (@keymapΣ) Σ → (@keymapG) Σ.
  Proof. solve_inG. Qed.
  
  Lemma ks A `{Countable A} n (x y : keysetUR A): ✓{n} y → x ≼ₒ{n} y → x ≼{n} y.
  Proof. intros Hv Hxy; destruct y; destruct Hxy; subst; try done. Qed.
  Canonical Structure keyset_authR A `{Countable A} := @authR _ (ks A).

  Class keysetG Σ := KeysetG { keyset_inG :> inG Σ (keyset_authR Key) }.
  Definition keysetΣ : gFunctors := #[GFunctor (keyset_authR Key)].

  Instance subG_keysetΣ {Σ} : subG (@keysetΣ) Σ → (@keysetG) Σ.
  Proof. solve_inG. Qed.
  

  (*
  Canonical Structure gmap_authR K `{Countable K} A := inclR(iris.algebra.auth.authR(iris.algebra.gmap.gmapR K A )).

  Class nodemapG Σ := NodemapG { nodemap_inG :> inG Σ (gmap_authR Key Node) }.
  Definition nodesetΣ : gFunctors := #[GFunctor (gset_authR Node )].

  Instance subG_nodesetΣ {Σ} : subG nodesetΣ Σ → nodesetG Σ.
  Proof. solve_inG. Qed.
*)
  
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

#[global] Instance enum_inhabited : Inhabitant enum.
Proof. unfold Inhabitant; apply F. Defined.

(* Definition pointer_of (n : Node) :=  fst n.
Definition lock_of (n : Node) := fst (snd n).
Definition node_of (n : Node) := snd (snd n).
*)
Definition min_of (rg: (number * number)) := fst rg.
Definition max_of (rg: (number * number)) := snd rg.

(*Node = val.
gmap Node -> (val, val) 
 *)
Section NodeRep.
Context `{!VSTGS unit Σ, !flowintG Σ, !nodemapG Σ, !keymapG Σ }.

Definition inFP (γ_f: gname) (pn lock: val) (n : Node) : mpred :=
    ∃ (N: gmap Node (val * val)),
      own (inG0 := nodemap_inG) γ_f (◯ (to_agree <$> N) : gmap_authR Node _) ∧
        ⌜N !! n = Some (pn, lock)⌝.

(*
Definition inFP (γ_f: gname) (n : Node) : mpred :=
    ∃ (N: gset Node),
      (own (inG0 := nodeset_inG)) γ_f (◯ N : gset_authR _) ∧ ⌜n ∈ N⌝.
*)

Class NodeRep : Type := {
    node : Node → @multiset_flowint_ur Key _ _ → gmap Key Value -> gmap nat Node -> mpred;
    node_rep_R_valid_pointer: forall n I_n C next, node n I_n C next -∗ valid_pointer n;
    node_rep_R_pointer_null: forall n I_n C next, node n I_n C next -∗ ⌜is_pointer_or_null n⌝;
    node_size: nat;
}.

Global Instance inFP_persistent γ_f pn lock n: Persistent (inFP γ_f pn lock n).
Proof.
  apply bi.exist_persistent.
  intros x.
  apply bi.and_persistent.
  apply own_core_persistent.
  apply (iris.algebra.auth.auth_frag_core_id _ ).
  apply _.
  apply _.
Qed.

End NodeRep.

