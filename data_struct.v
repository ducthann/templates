Require Import VST.concurrency.conclib.
From iris.algebra Require Import excl auth gmap agree gset.
Require Export flows.inset_flows.
Require Import flows.auth_ext.
Require Import flows.multiset_flows.
Require Import flows.flows.
Require Import iris_ora.algebra.gmap.
Require Import iris_ora.logic.own.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles. 
Require Import bst.puretree.
Require Import bst.giveup_template.
Require Import VST.floyd.library.
From iris_ora.algebra Require Import frac_auth.
Require Import bst.flows_ora.
Require Import bst.keyset_ra_ora.

Definition Key := Z.

Section Give_Up_Cameras.
  About multiset_flowint_ur.
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
  (* Definition gset1 := gmap K unit. *)
  Canonical Structure gsetR A `{Countable A} := gmapR A unit.
  Canonical Structure gsetUR A `{Countable A} := gmapUR A unit.
  Lemma gst A `{Countable A} n (x y : gsetUR A): ✓{n} y → x ≼ₒ{n} y → x ≼{n} y.
  Proof.
    intros Hv Hxy.
    rewrite lookup_includedN; intros i.
    specialize (Hv i); specialize (Hxy i); rewrite option_includedN.
    destruct (x !! i) as [a|] eqn: Hx; last by auto.
    rewrite Hx in Hxy |- *.
    destruct (_ !! _) as [b|]; last done;
    right; eexists _, _; split; first done.
    split; first done; auto.
  Qed.
  
  Canonical Structure gset_authR A `{Countable A} := @authR _ (gst A).

  Class nodesetG Σ := NodesetG { nodeset_inG :> inG Σ (gset_authR Node) }.
  Definition nodesetΣ : gFunctors := #[GFunctor (gset_authR Node)].

  Instance subG_nodesetΣ {Σ} : subG nodesetΣ Σ → nodesetG Σ.
  Proof. solve_inG. Qed.

  About keysetUR.
  Lemma ks A `{Countable A} n  (x y : keysetUR A): ✓{n} y → x ≼ₒ{n} y → x ≼{n} y.
  Proof. intros Hv Hxy; destruct y; destruct Hxy; subst; try done. Qed.
  Canonical Structure keyset_authR A `{Countable A} := @authR _ (ks A).

  Class keysetG Σ := KeysetG { keyset_inG :> inG Σ (keyset_authR Key  ) }.
  Definition keysetΣ : gFunctors := #[GFunctor (keyset_authR Key)].

  Instance subG_keysetΣ {Σ} : subG (@keysetΣ) Σ → (@keysetG) Σ.
  Proof. solve_inG. Qed.

  Locate prod.
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


Section NodeRep.
  Context `{!VSTGS unit Σ, !flowintG Σ, !nodesetG Σ, !keysetG Σ }.

  Locate keysetG.
  Definition inFP (γ_f: gname) (n : Node) : mpred :=
    ∃ (N: gmap Node unit),
      (own (inG0 := nodeset_inG)) γ_f (◯ N) ∧ ⌜N !! n = Some tt⌝.

  Locate K.

  Class NodeRep : Type := {
      node : Node → @multiset_flowint_ur Key _ _ → gset Key → mpred;
      node_sep_star: ∀ n I_n I_n' C C', node n I_n C ∗ node n I_n' C' -∗ False;
      node_rep_R_valid_pointer: forall n I_n C, node n I_n C -∗ valid_pointer n;
      node_rep_R_pointer_null: forall n I_n C, node n I_n C -∗ ⌜is_pointer_or_null n⌝;
      node_size: nat;
  }.
   
  Global Instance inFP_persistent γ_f n: Persistent (inFP γ_f n).
  Proof.
    apply bi.exist_persistent.
    intros.
    apply bi.and_persistent; try apply _.
    apply own_core_persistent.
    apply (auth_frag_core_id _ (gst Node)).
    apply _.
  Qed.

  
  (*
  Lemma inFP_equiv γ_f n1 n2:
  inFP γ_f n1 ∗ inFP γ_f n2 -∗ ⌜n1 = n2⌝.
  Proof.
    iIntros "[#H1 #H2]".
    unfold inFP.
    iDestruct "H1" as (N) "(H11 & %H12)".
    iDestruct "H2" as (N1) "(H21 & %H22)".
    iCombine "H11 H21" as "HV".
    rewrite -own_op.
    Search op auth_frag .
    Check frac_auth_agreeI.
    Locate "◯".
    *)
End NodeRep.

Check NodeRep.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


Section give_up.
  Context `{N: NodeRep } `{EqDecision K} `{Countable K}.
  Context `{!VSTGS unit Σ, !flowintG Σ, !nodesetG Σ, !keysetG Σ }.
  
  Definition t_struct_node := Tstruct _node_t noattr.
  Definition t_struct_nodeds := Tstruct _node noattr.
  Definition t_struct_pn := Tstruct _pn noattr.

  (*
    typedef struct node_t {node *t; lock_t lock; int min; int max; } node_t;

    typedef struct node {int key; void *value; void *left, *right;} node;
   

   *)

  Definition node_rep (pn n lock: val) (min max : number) I_n C :=
    ⌜repable_signed (number2Z min) ∧ repable_signed (number2Z max) /\
      is_pointer_or_null n /\ is_pointer_or_null lock⌝ ∧ 
      field_at Ews (t_struct_node) [StructField _t] n pn ∗ (* pn ->n*) 
      field_at Ews (t_struct_node) [StructField _min] (vint (number2Z (min))) pn ∗ (*pn -> min*)
      field_at Ews (t_struct_node) [StructField _max] (vint (number2Z (max))) pn ∗ (*pn -> max*) 
      malloc_token Ews t_struct_node pn ∗
      node n I_n C.
  
  Definition nodePred γ_I γ_k n (In : @multiset_flowint_ur Key _ _ ) Cn  : mpred :=
                    node n In Cn 
                    ∗  own γ_k (◯ flows.keyset_ra.prod (keyset _ _ Key In n, Cn)  : keyset_authR Key)
                    ∗ own γ_I (◯ In) 
                    ∗ ⌜dom In = {[n]}⌝.
  


(** Definitions of cameras used in the template verification *)



#[export] Instance pointer_lock : Ghost := discrete_PCM (val * val * range).
Definition ghost_info : Type := (key * val * (list val))%type.

(* This allows the range to be outdated while the ghost_info may be present or absent. *)
#[export] Instance node_ghost : Ghost := prod_PCM pointer_lock (exclusive_PCM (option ghost_info)).
Notation node_info := (@G node_ghost).

Definition in_tree (g: gname) (g1 : gname) (pn: val) (lock: val):=
      ghost_snap (P := gmap_ghost (K := gname)(A := discrete_PCM (val * val)) )
        ({[g1 := (pn, lock)]}) g.

Lemma in_tree_equiv g g_in p1 p2 lk1 lk2:
  in_tree g g_in p1 lk1 * in_tree g g_in p2 lk2 |-- !!((p1 = p2) /\ (lk1 = lk2)) .
Proof.
  iIntros "H".
  iPoseProof(ghost_snap_join' with "H") as (v') "(%H & _)".
  iPureIntro.
  specialize (H g_in).
  rewrite ! lookup_insert in H.
  inversion H; subst; inversion H3; inversion H0; auto.
Qed.

Lemma in_tree_duplicate g gin pn lock:
  in_tree g gin pn lock |-- in_tree g gin pn lock * in_tree g gin pn lock.
Proof. by rewrite - bi.persistent_sep_dup. Qed.

Section NodeRep.
  Class NodeRep : Type := {
      node_rep_R : val -> option (option ghost_info) -> gname -> mpred;
      node_rep_R_valid_pointer: forall tp g_in g, node_rep_R tp g_in g |-- valid_pointer tp;
      node_rep_R_pointer_null: forall tp g_in g, node_rep_R tp g_in g |-- !! is_pointer_or_null tp;
      node_size: nat;
      node_null: forall g_info, node_rep_R nullval g_info = !!(g_info = Some None) && seplog.emp;
  }.
End NodeRep.
