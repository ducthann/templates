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
Require Import tmpl.giveup_template.
Require Import tmpl.flows_ora.
Require Import tmpl.keyset_ra_ora.
Require Import tmpl.data_struct.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


Section give_up.
  Context `{N: NodeRep } `{EqDecision K} `{Countable K}.
  Context `{!VSTGS OK_ty Σ, !cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr),
            !flowintG Σ, !nodesetG Σ, !keysetG Σ, inG Σ (frac_authR (agreeR Node))}.
  
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
    iDestruct "Hfp" as (n1) "[Hown1 %H1]".
    iDestruct (own_valid_2 with "Hown Hown1") as %Hown.
    rewrite auth_both_valid_discrete in Hown.
    set_solver.
  Qed.

  Lemma node_conflict_local γ_f γ_k n (rg rg': (number * number)) I_n I_n' C C':
  node_rep γ_f γ_k n rg I_n C ∗ node_rep γ_f γ_k n rg' I_n' C' -∗ False.
  Proof.
    iIntros "((((_ & _) & _) & (H1 & _))  & (((_ & _) & _) & (H2 & _)))".
    iPoseProof (field_at_conflict Ews t_struct_node (DOT _t) with "[$H1 $H2 //]") as "HF"; try done; auto.
  Qed.

  Lemma ghost_snapshot_fp γ_f (Ns: gset Node) n:
    own (inG0 := nodeset_inG) γ_f (● Ns) ∧ ⌜n ∈ Ns⌝ ==∗
         own γ_f (inG0 := nodeset_inG) (● Ns) ∗ inFP γ_f n.
  Proof.
    iIntros "(H1 & %H2)".
    iMod (own_update (i:= nodeset_inG) γ_f (● Ns) (● Ns ⋅ ◯ Ns) with "[$]") as "H".
    { apply auth_update_dfrac_alloc. apply _. auto. }
    iDestruct "H" as "(Haa & Haf)".
    iModIntro.
    by iFrame.
  Qed.

  Definition ltree (p lock : val) R :=
    ∃ lsh, ⌜field_compatible t_struct_node nil p /\ readable_share lsh⌝ ∧
             (field_at lsh t_struct_node [StructField _lock] lock p ∗ inv_for_lock lock R).

  Definition node_lock_inv_pred γ_f γ_g γ_k node rg I_n C :=
    my_half γ_g 1 (to_agree node) ∗ node_rep γ_f γ_k node rg I_n C.
  
  Lemma node_lock_inv_pred_exclusive γ_f γ_g γ_k node rg I_n C:
      exclusive_mpred (node_lock_inv_pred γ_f γ_g γ_k node rg I_n C).
  Proof.
    iIntros "((_ & H) & (_ & H'))".
    iPoseProof (node_conflict_local with "[$H $H']") as "?"; done.
  Qed.

  Definition nodeFull γ_f γ_g γ_k n rg : mpred :=
        ∃ In C, ltree (pointer_of n) (lock_of n) (node_lock_inv_pred γ_f γ_g γ_k n rg In C).

  Definition CSSi γ_I γ_f γ_g γ_k r C I rg: mpred :=
                    globalGhost γ_I γ_f γ_k r C I 
                  ∗ ([∗ set] n ∈ (dom I), public_half γ_g (to_agree n) ∗ nodeFull γ_I γ_g γ_k n rg).

  Definition CSS γ_I γ_f γ_g γ_k r C rg : mpred := ∃ I, CSSi γ_I γ_f γ_g γ_k r C I rg.

  Check CSSi.

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
    iDestruct (own_valid_2  with "HI Hi") as %Hown.
    rewrite auth_both_valid_discrete in Hown.
    destruct Hown as [[Io Io1] I_incl].
    iPureIntro.
    rewrite Io1 intComp_dom; last first; try rewrite <- Io1; auto.
    set_solver.
  Qed.

  (* root is in footprint *)
  Lemma ghost_update_root γ_I γ_f γ_g γ_k r C rg :
    CSS γ_I γ_f γ_g γ_k r C rg ==∗
       CSS γ_I γ_f γ_g γ_k r C rg ∗ inFP γ_f r.
  Proof.
    iIntros "Hcss".
    iDestruct "Hcss" as (I) "((HI & #Hglob & Hks & Hdom) & Hbigstar)".
    iDestruct "Hglob" as %Hglob.
    specialize ((globalinv_root_fp I r) Hglob); intros.
    iMod (ghost_snapshot_fp γ_f (dom I) r with "[$Hdom //]") as "(Hdom & #Hinfp)".
    iIntros "!>".
    iFrame "Hinfp ∗ %".
  Qed.

  Lemma lock_join lsh1 lsh2 pn lock_in :
    ⌜readable_share lsh1 /\ readable_share lsh2⌝ ∧ field_at lsh1 t_struct_node (DOT _lock) lock_in pn ∗ field_at lsh2 t_struct_node (DOT _lock) lock_in pn -∗
        ∃ (lsh : share), ⌜readable_share lsh⌝ ∧ field_at lsh t_struct_node (DOT _lock) lock_in pn.
    Admitted.

  Lemma share_divided lsh pn (lock_in : val):
    ⌜readable_share lsh⌝ ∧ field_at lsh t_struct_node (DOT _lock) lock_in pn -∗
    (∃ lsh, ⌜readable_share lsh⌝ ∧ field_at lsh t_struct_node (DOT _lock) lock_in pn) ∗
    (∃ lsh, ⌜readable_share lsh⌝ ∧ field_at lsh t_struct_node (DOT _lock) lock_in pn).
  Proof.
    iIntros "(% & H1)".
    assert(sepalg.join (fst (slice.cleave lsh)) (snd (slice.cleave lsh)) lsh).
    apply slice.cleave_join.
    iPoseProof(field_at_share_join (fst (slice.cleave lsh)) (snd (slice.cleave lsh)) with "[H1]")
    as "(H11 & H12)"; auto; auto.
    pose proof H1 as H1'.
    apply cleave_readable1 in H1. 
    apply cleave_readable2 in H1'.
    iSplitL "H11"; iExists _; by iFrame.
  Qed.
  
End give_up.

Global Hint Resolve node_lock_inv_pred_exclusive : core.
Lemma key_range (x: Z) a b
  (Hrg: (Int.min_signed ≤ x ≤ Int.max_signed)%Z)
  (Hrgx: (number2Z a < x < number2Z b)%Z) :
  key_in_range x (a, b) = true.
Proof.
  unfold key_in_range; apply andb_true_iff;
    (split; unfold number2Z in Hrgx; destruct a; destruct b; simpl; lia).
Qed.
Global Hint Resolve key_range : core.
