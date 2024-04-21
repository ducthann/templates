Require Import VST.concurrency.conclib.
From iris.algebra Require Import excl auth gmap agree gset.
Require Export flows.inset_flows.
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

Section give_up.
  Context `{N: NodeRep } `{EqDecision K} `{Countable K}.
  Context `{!VSTGS OK_ty Σ, !cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr),
            !flowintG Σ, !nodesetG Σ, !keysetG Σ, inG Σ (frac_authR (agreeR Node))}.

  Check inG.
  
  Definition t_struct_node := Tstruct _node_t noattr.
  Definition t_struct_nodeds := Tstruct _node noattr.
  Definition t_struct_pn := Tstruct _pn noattr.

  (* struct node_t {node *t; lock_t lock; int min; int max; } node_t;
    struct node {int key; void *value; void *left, *right;} node; *)

  Definition node_rep γ_f γ_k (n : Node) (rg : (number * number))
    (In : @multiset_flowint_ur Key _ _ ) Cn :=
    ⌜repable_signed (number2Z (min_of rg)) ∧ repable_signed (number2Z (max_of rg)) /\
      is_pointer_or_null (node_of n) /\ is_pointer_or_null (lock_of n)⌝ ∧
      field_at Ews (t_struct_node) [StructField _t] (node_of n) (pointer_of n) ∗ (* pn ->n*) 
      field_at Ews (t_struct_node) [StructField _min] (vint (number2Z (min_of rg))) (pointer_of n) ∗ (*pn -> min*)
      field_at Ews (t_struct_node) [StructField _max] (vint (number2Z (max_of rg))) (pointer_of n) ∗ (*pn -> max*) 
      malloc_token Ews t_struct_node (pointer_of n) (* ∗ inFP γ_f n *) ∗
      node n In Cn ∗ own γ_k (◯ prod (keyset _ _ Key In n, Cn): keyset_authR Key) ∗
      own γ_f (◯ In) ∗ ⌜dom In = {[n]}⌝.


  (*
  Definition nodePred γ_I γ_k n (In : @multiset_flowint_ur Key _ _ ) Cn :=
   node n In Cn ∗ own γ_k (◯ prod (keyset _ _ Key In n, Cn): keyset_authR Key) ∗
     own γ_I (◯ In) ∗ ⌜dom In = {[n]}⌝.
 *)
  
  Definition globalGhost
    γ_I γ_f γ_k (r :Node) C (I: @multiset_flowint_ur Key _ _): mpred :=
    own γ_I (● I) ∗ ⌜globalinv _ _ Key r I⌝ ∗
      own γ_k (● prod (KS, C): keyset_authR Key) ∗ own (inG0 := nodeset_inG) γ_f (● (dom I)).

  Lemma node_exist_in_tree γ_f n (I: @multiset_flowint_ur Key _ _):
    inFP γ_f n ∗ own (inG0 := nodeset_inG) γ_f (● (dom I)) ⊢ ⌜n ∈ dom I⌝.
  Proof.
    intros; iIntros "(#Hfp & Hown)".
    unfold inFP.
    iDestruct "Hfp" as (n1) "[Hown1 %H1]".
    iDestruct (own_valid_2  with "Hown Hown1") as %Hown.
    rewrite auth_both_valid_discrete in Hown.
    set_solver.
  Qed.

  Lemma node_conflict_local γ_f γ_k n (rg rg': (number * number)) I_n I_n' C C':
  node_rep γ_f γ_k n rg I_n C ∗ node_rep γ_f γ_k n rg' I_n' C' -∗ False.
  Proof.
    iIntros "(H1 & H2)".
    unfold node_rep.
    iDestruct "H1" as "(((_ & _) & _) & (H1 & _)) ".
    iDestruct "H2" as "(((_ & _) & _) & (H2 & _)) ".
    iPoseProof (field_at_conflict Ews t_struct_node (DOT _t)  with "[$H1 $H2]") as "HF";
      simpl; eauto. done.
  Qed.

  Lemma ghost_snapshot_fp γ_f (Ns: gset Node) n:
    own (inG0 := nodeset_inG) γ_f (● Ns) ∧ ⌜n ∈ Ns⌝ ==∗
         own γ_f (inG0 := nodeset_inG) (● Ns) ∗ inFP γ_f n.
  Proof.
    iIntros "(H1 & %H2)".
    iMod (own_update (i := nodeset_inG) γ_f (● Ns) (● Ns ⋅ ◯ Ns) with "[$]") as "H".
    { apply auth_update_dfrac_alloc. apply _. done. }
    iDestruct "H" as "(Haa & Haf)".
    iModIntro.
    by iFrame.
  Qed.

  Definition ltree (p lock : val) R :=
    ∃ lsh, ⌜field_compatible t_struct_node nil p /\ readable_share lsh⌝ ∧
             (field_at lsh t_struct_node [StructField _lock] lock p ∗ inv_for_lock lock R).


 
  Definition node_lock_inv_pred γ_f γ_g γ_k node rg I_n C :=
    my_half γ_g 1 (to_agree node) ∗ node_rep γ_f γ_k node rg I_n C.
  
  Lemma node_lock_inv_pred_exclusive : forall γ_f γ_g γ_k node rg I_n C,
      exclusive_mpred (node_lock_inv_pred γ_f γ_g γ_k node rg I_n C).
  Proof.
    intros.
    unfold exclusive_mpred, node_lock_inv_pred.
    iIntros "((_ & H) & (_ & H'))".
    iPoseProof (node_conflict_local with "[$H $H']") as "?"; done.
  Qed.

  Definition nodeFull γ_f γ_g γ_k n rg: mpred :=
        ∃ In C, ltree (pointer_of n) (lock_of n) (node_lock_inv_pred γ_f γ_g γ_k n rg In C).

  Check public_half.

  Definition CSSi γ_I γ_f γ_g γ_k r C I rg: mpred :=
                    globalGhost γ_I γ_f γ_k r C I 
                  ∗ ([∗ set] n ∈ (dom I), public_half γ_g (to_agree n) ∗ nodeFull γ_I γ_g γ_k n rg).

  Definition CSS γ_I γ_f γ_g γ_k r C rg : mpred := ∃ I, CSSi γ_I γ_f γ_g γ_k r C I rg.

  Lemma inFP_domm γ_I γ_f γ_g γ_k r C I n rg :
    inFP γ_f n -∗ CSSi γ_I γ_f γ_g γ_k r C I rg -∗ ⌜n ∈ dom I⌝.
  Proof.
    iIntros "#Hfp Hcss".
    iDestruct "Hcss" as "((HI & Hglob & Hks & Hdom) & Hbigstar)".
    iPoseProof (node_exist_in_tree with "[$Hfp Hdom]") as "H"; done.
  Qed.

  Lemma int_domm γ_I γ_f γ_g γ_k r C I n In rg :
    own γ_I (◯ In) -∗ ⌜dom In = {[n]}⌝ -∗ CSSi γ_I γ_f γ_g γ_k r C I rg -∗ ⌜n ∈ dom I⌝.
  Proof.
    iIntros "Hi Dom_In Hcss".
    iDestruct "Dom_In" as %Dom_In.
    iDestruct "Hcss" as "((HI & Hglob & Hks & Hdom) & Hbigstar)".
    Check own_valid_2.
    iDestruct (own_valid_2  with "HI Hi") as %Hown.
    rewrite auth_both_valid_discrete in Hown.
    destruct Hown as [Io I_incl].
    destruct Io as [Io Io1].
    iPureIntro.
    rewrite Io1.
    rewrite intComp_dom. set_solver.
    rewrite <- Io1; auto.
  Qed.
  
  
End give_up.

