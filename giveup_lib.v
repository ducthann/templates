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

Definition Value := iris.algebra.excl.exclR (discreteO val).

Section give_up.
  Context `{N: NodeRep } `{EqDecision K} `{Countable K}.
   
  Definition prod3O A B C D E := prodO A (prodO B (prodO C (prodO D E))).
  Definition per_node := prod3O val val Node (@multiset_flowint_ur Key _ _) (gmap Key data_struct.Value).
  Context `{!VSTGS unit Σ, !cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr),
            !flowintG Σ, !nodemapG Σ, !keymapG Σ, !keysetG Σ,
        inG Σ (frac_authR (agreeR per_node))}.
  
  Definition t_struct_node := Tstruct _node_t noattr.
  Definition t_struct_nodeds := Tstruct _node noattr.
  Definition t_struct_pn := Tstruct _pn noattr.

  (* struct node_t {node *t; lock_t lock; int min; int max; } node_t;
    struct node {int key; void *value; void *left, *right;} node; *)

  

  Lemma inFP_duplicate γ_f pn lock n:
    inFP γ_f pn lock n -∗ inFP γ_f pn lock n ∗ inFP γ_f pn lock n.
  Proof. by rewrite - bi.persistent_sep_dup; iIntros "?". Qed.

  (* γ_f for N: gset Node)
    γ_I for In (multiset_flowint_ur)
    γ_k for keyset 
   *)
  
  Definition node_rep γ_I γ_k pn lock (n : Node)
    (In : @multiset_flowint_ur Key _ _ ) Cn := ∃ (rg : (number * number)) next,
    ⌜repable_signed (number2Z (min_of rg)) ∧ repable_signed (number2Z (max_of rg)) /\
      is_pointer_or_null n /\ is_pointer_or_null lock ∧
      (∀ k, and (Z.lt (number2Z (min_of rg)) k) (Z.lt k (number2Z (max_of rg))) -> in_inset _ _ _ k In n) ∧ dom In = {[n]} ⌝ ∧
      field_at Ews (t_struct_node) [StructField _t] n pn ∗ (* pn ->n*) 
      field_at Ews (t_struct_node) [StructField _min] (vint (number2Z (min_of rg))) pn ∗ (*pn -> min*)
      field_at Ews (t_struct_node) [StructField _max] (vint (number2Z (max_of rg))) pn ∗ (*pn -> max*)
      
      malloc_token Ews t_struct_node pn (* ∗ inFP γ_f n *) ∗
      node n In Cn next ∗ own γ_k (◯ prod (keyset _ _ Key In n, dom Cn): keyset_authR Key) ∗
      own γ_I (◯ In).


  (*
  Definition nodePred γ_I γ_k n (In : @multiset_flowint_ur Key _ _ ) Cn :=
   node n In Cn ∗ own γ_k (◯ prod (keyset _ _ Key In n, Cn): keyset_authR Key) ∗
     own γ_I (◯ In) ∗ ⌜dom In = {[n]}⌝.
 *)

  Definition own_nodes γ_f (I : @multiset_flowint_ur Key _ _ ) :=
    ∃ N, ⌜dom N = dom I⌝ ∧ own (inG0 := nodemap_inG) γ_f (● N).

  Definition globalGhost
    γ_I γ_f γ_k (r :Node) (C : gmap Key data_struct.Value) (I: @multiset_flowint_ur Key _ _): mpred :=
    own γ_I (● I) ∗ ⌜globalinv _ _ Key r I⌝ ∗
      own γ_k (● prod (KS, dom C): keyset_authR Key) ∗
      own_nodes γ_f I
  (* own (inG0 := nodeset_inG) γ_f (● (dom I)) *).

  Lemma node_exist_in_tree γ_f pn lock n (I: @multiset_flowint_ur Key _ _):
    inFP γ_f pn lock n ∗ own_nodes γ_f I ⊢ ⌜n ∈ dom I⌝.
  Proof.
    intros; iIntros "(#Hfp & Hown)".
    iDestruct "Hfp" as (n1) "[Hown1 %H1]".
    Check own_valid_2.
    unfold own_nodes.
    iDestruct "Hown" as (N0) "(%Hdom & Hown)".
    iDestruct (own_valid_2 γ_f (● N0: gmap_authR _ _) (◯ (to_agree <$> n1)) with "[$] [$]") as "Hown".
    iDestruct "Hown" as %Hown.
    rewrite auth_both_valid_discrete in Hown.
    destruct Hown.
    Search included gmap.
    rewrite lookup_included in H2.
    specialize (H2 n).
    Search lookup fmap.
    rewrite lookup_fmap in H2.
    rewrite H1 in H2.
    iPureIntro.
    simpl in H2.
    Search dom lookup.
    rewrite <- Hdom.
    Search dom lookup.
    unfold dom in *.
    simpl in *.
    hnf in N0.
    rewrite elem_of_dom.
    Search included Some.
    apply Some_included_is_Some in H2.
    auto.
 Qed.

  Lemma in_node_equiv γ_f p1 p2 lk1 lk2 n:
    inFP γ_f p1 lk1 n ∗ inFP γ_f p2 lk2 n -∗ ⌜ p1 = p2 /\ lk1 = lk2 ⌝ .
  Proof.
    iIntros "(H1 & H2)".
    unfold inFP.
    iDestruct "H1" as (N1) "(H1 & %K1)".
    iDestruct "H2" as (N2) "(H2 & %K2)".
    Search op to_agree.
    Check own_valid_2.
    Check own_op.
    iDestruct (own_valid_2 γ_f (◯ (to_agree <$> N1): gmap_authR Node _) (◯ (to_agree <$> N2): gmap_authR Node _) with "[$H1] [$H2]") as "%Hown".
    Search valid auth_frag.
    rewrite auth_frag_op_valid in Hown.
    Search valid gmap.
    eapply lookup_valid_Some in Hown; last first.
    Search lookup op.
    rewrite lookup_op.
    Search lookup fmap.
    rewrite ! lookup_fmap.
    erewrite K1.
    rewrite K2.
    rewrite -  Some_op.
    auto.
    apply to_agree_op_inv_L in Hown.
    iPureIntro.
    inversion Hown; subst.
    auto.
  Qed.
    
  Lemma node_conflict_local γ_I γ_k pn lock n I_n I_n' C C':
  node_rep γ_I γ_k pn lock n I_n C ∗ node_rep γ_I γ_k pn lock n I_n' C' -∗ False.
  Proof.
    iIntros "(H1 & H2)".
    iDestruct "H1" as (rg next) "(_ & (H1 & _))".
    iDestruct "H2" as (rg' next') "(_ & (H2 & _))".
    iPoseProof (field_at_conflict Ews t_struct_node (DOT _t) with "[$H1 $H2 //]") as "HF"; try done; auto.
  Qed.

  Lemma ghost_snapshot_fp γ_f (Ns: gmap Node (val * val)) pn lock n:
    own (inG0 := nodemap_inG) γ_f (● (to_agree <$> Ns)) ∧ ⌜Ns !! n = Some (pn, lock)⌝ ==∗
         own γ_f (inG0 := nodemap_inG) (● (to_agree <$> Ns)) ∗ inFP γ_f pn lock n.
  Proof.
    iIntros "(H1 & %H2)".
    iMod (own_update (i:= nodemap_inG) γ_f (● (to_agree <$> Ns)) (● (to_agree <$> Ns) ⋅ ◯ (to_agree <$> Ns)) with "[$]") as "H".
    { apply auth_update_dfrac_alloc. apply _. auto. }
    iDestruct "H" as "(Haa & Haf)".
    iModIntro.
    unfold inFP.
    by iFrame.
  Qed.

  Definition ltree (p lock : val) R :=
    ∃ lsh, ⌜field_compatible t_struct_node nil p /\ readable_share lsh⌝ ∧
             (field_at lsh t_struct_node [StructField _lock] lock p ∗ inv_for_lock lock R).

  Definition node_lock_inv_pred γ_I γ_k γ_g pn lock (node : Node) (In : @multiset_flowint_ur Key _ _ ) Cn :=
    my_half γ_g 1 (to_agree (pn, (lock, (node, (In, Cn))))) ∗ node_rep γ_I γ_k pn lock node In Cn.
  
  Lemma node_lock_inv_pred_exclusive γ_I γ_k γ_g pn lock node I_n C:
      exclusive_mpred (node_lock_inv_pred γ_I γ_g γ_k pn lock node I_n C).
  Proof.
    iIntros "((_ & H) & (_ & H'))".
    iPoseProof (node_conflict_local with "[$H $H']") as "?"; done.
  Qed.

  (*
  Definition nodeFull γ_I γ_k γ_g pn lock node : mpred :=
        ∃ In C, ltree pn lock (node_lock_inv_pred γ_I γ_k γ_g pn lock node In C).

  
  Definition CSSi γ_I γ_f γ_k γ_g r C I : mpred :=
                    globalGhost γ_I γ_f γ_k r C I 
                  ∗ ([∗ set] n ∈ (dom I), public_half γ_g (to_agree n ∗ nodeFull γ_I γ_k γ_g pn lock n).
 *)

  Definition CSSi γ_I γ_f γ_k γ_g r C I : mpred := globalGhost γ_I γ_f γ_k r C I
                  ∗ ([∗ set] n ∈ (dom I), ∃ pn lock In Cn,
                      public_half γ_g (to_agree (pn, (lock, (n, (In, Cn))))) ∗
                                  inFP γ_f pn lock n ∗
                        ltree pn lock (node_lock_inv_pred γ_I γ_k γ_g pn lock n In Cn)).
                     
  Definition CSS γ_I γ_f γ_k γ_g r C: mpred := ∃ I, CSSi γ_I γ_f γ_k γ_g r C I.

  Lemma inFP_domm γ_I γ_f γ_k γ_g r C I pn lock n :
    inFP γ_f pn lock n -∗ CSSi γ_I γ_f γ_k γ_g r C I -∗ ⌜n ∈ dom I⌝.
  Proof.
    iIntros "#Hfp Hcss".
    iDestruct "Hcss" as "((HI & Hglob & Hks & Hdom) & Hbigstar)".
    iPoseProof (node_exist_in_tree with "[$Hfp Hdom]") as "H"; done.
  Qed.

  Lemma int_domm γ_I γ_f γ_k γ_g r C I n In :
    own γ_I (◯ In) -∗ ⌜dom In = {[n]}⌝ -∗ CSSi γ_I γ_f γ_k γ_g r C I -∗ ⌜n ∈ dom I⌝.
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
  Lemma ghost_update_root γ_I γ_f γ_k γ_g r C :
    CSS γ_I γ_f γ_k γ_g r C ==∗
       ∃ pr lockr,  CSS γ_I γ_f γ_k γ_g r C ∗ inFP γ_f pr lockr r.
  Proof.
    iIntros "Hcss".
    iDestruct "Hcss" as (I) "((HI & #Hglob & Hks & Hdom) & Hbigstar)".
    iDestruct "Hglob" as %Hglob.
    specialize ((globalinv_root_fp I r) Hglob); intros.
    unfold own_nodes.
    rewrite (big_sepS_elem_of_acc _ (dom I) r); last first. auto.
    iDestruct "Hdom" as (N1) "(%Hdom & Hdom1)".
    iDestruct "Hbigstar" as "(Hbigstar & Hb1)".
    iDestruct "Hbigstar" as (pr lockr Inr Cnr) "(K1 & (#K2 & K3))".
    iModIntro.
    iExists _, _. iFrame "K2".
    iAssert ((∃ (pn lock : valC) (In0 : multiset_flowint_ur) (Cn : gmapO Key valC),
                  public_half γ_g (to_agree (pn, (lock, (r, (In0, Cn))))) ∗ 
                  inFP γ_f pn lock r ∗ ltree pn lock (node_lock_inv_pred γ_I γ_k γ_g pn lock r In0 Cn))  )  with "[K1 K3]" as "Hb"; auto.
    {
      iExists _, _, _, _. iFrame. iFrame "K2".
    }
    iSpecialize ("Hb1" with "Hb").
    iFrame.
    iPureIntro. done.
  Qed.

  
  Lemma lock_join lsh1 lsh2 pn lock_in :
    ⌜readable_share lsh1 /\ readable_share lsh2⌝ ∧
      field_at lsh1 t_struct_node (DOT _lock) lock_in pn ∗
        field_at lsh2 t_struct_node (DOT _lock) lock_in pn -∗
        ∃ (lsh : share), ⌜readable_share lsh⌝ ∧ field_at lsh t_struct_node (DOT _lock) lock_in pn.
  Proof.
    iIntros "((%Hrs1 & %Hrs2) & H)".
    iPoseProof (field_at_share_joins lsh1 lsh2 with "[$H]") as "%HJ". done.
    destruct HJ as (lsh & HJ).
    rewrite (field_at_share_join lsh1 lsh2 lsh); auto.
    iExists lsh. iFrame. iPureIntro.
    pose proof (@join_readable1 lsh1 lsh2 lsh). auto.
  Qed.

  Lemma share_divided lsh pn (lock_in : val):
    ⌜readable_share lsh⌝ ∧
      field_at lsh t_struct_node (DOT _lock) lock_in pn -∗
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

  Lemma inv_lock γ_I γ_k γ_g pn lock n In Cn In1 Cn1 In2 Cn2:
  node_lock_inv_pred γ_I γ_k γ_g pn lock n In Cn ∗
    inv_for_lock lock (node_lock_inv_pred γ_I γ_k γ_g pn lock n In1 Cn1) -∗
      node_lock_inv_pred γ_I γ_k γ_g pn lock n In Cn ∗
        inv_for_lock lock (node_lock_inv_pred γ_I γ_k γ_g pn lock n In2 Cn2).
  Proof.
    iIntros "(Hnode & Hinv)".
    iDestruct "Hinv" as (b') "(Hatm & Hnode')".
    destruct b'.
    - iFrame.
    - iDestruct "Hnode" as "(_ & Hnode)".
      iDestruct "Hnode'" as "(_ & Hnode')".
      by iPoseProof (node_conflict_local _ _ pn lock n In In1 Cn Cn1 with "[$Hnode $Hnode']") as "?".
  Qed.
      
  Lemma in_tree_inv' γ_I γ_f γ_k γ_g r (m: gmap Key data_struct.Value) pn lock n In Cn:
    inFP γ_f pn lock n ∗ node_lock_inv_pred γ_I γ_k γ_g pn lock n In Cn ∗ CSS γ_I γ_f γ_k γ_g r m -∗
        (node_lock_inv_pred γ_I γ_k γ_g pn lock n In Cn ∗
             (inv_for_lock lock (node_lock_inv_pred γ_I γ_k γ_g pn lock n In Cn))) ∗
                  (inv_for_lock lock (node_lock_inv_pred γ_I γ_k γ_g pn lock n In Cn) -∗
                         CSS γ_I γ_f γ_k γ_g r m).
  Proof.
    iIntros "(#HinFP & (Hnode & HCSS))".
    iDestruct "HCSS" as (In') "HCSS".
    iPoseProof (inFP_domm γ_I γ_f γ_k γ_g r m In' pn lock n with "[$HinFP] [$HCSS]") as "%".
    unfold CSSi.
    iDestruct "HCSS" as "((Hglob & H3) & H4)".
    rewrite (big_sepS_elem_of_acc _ (dom In') n); last first. auto.
    iDestruct "H4" as "(H41 & H42)".
    iDestruct "H41" as (p1 lk1 In1 Cn1) "(H41 & (#K1 & K2))".
    unfold ltree.
    iDestruct "K2" as (lsh1) "(%K1 & (K2 & K3))".
    iDestruct "Hnode" as "(Hn1 & Hn2)".
    iPoseProof (public_agree with "[$Hn1 $H41]") as "%Hagree".
    apply to_agree_inj, leibniz_equiv in Hagree.
    symmetry in Hagree.
    inversion Hagree; subst.
    iAssert (node_lock_inv_pred γ_I γ_k γ_g pn lock n In Cn) with "[$Hn1 $Hn2]" as "Hnode".
    iSplitL "Hnode K3"; iFrame. 
    iIntros "H".
    iAssert (∃ (pn0 lock0 : valC) (In0 : multiset_flowint_ur) (Cn0 : gmapO Key valC),
             public_half γ_g (to_agree (pn0, (lock0, (n, (In0, Cn0))))) ∗ inFP γ_f pn0 lock0 n ∗
             ∃ lsh : share,
               ⌜field_compatible t_struct_node [] pn0 ∧ readable_share lsh⌝
               ∧ @field_at _ _ _ CompSpecs lsh t_struct_node (DOT _lock) lock0 pn0 ∗
               inv_for_lock lock0 (node_lock_inv_pred γ_I γ_k γ_g pn0 lock0 n In0 Cn0))
        with "[$H41 $K2 $H]" as "H1"; auto.
      iSpecialize ("H42" with "H1").
      iFrame.
  Qed.
  
  Lemma in_node_inv γ_I γ_f γ_k γ_g r (m: gmap Key data_struct.Value) pn lock n:
    inFP γ_f pn lock n ∗ CSS γ_I γ_f γ_k γ_g r m -∗
      (∃ In C, (inv_for_lock lock (node_lock_inv_pred γ_I γ_k γ_g pn lock n In C) ∗
               (inv_for_lock lock (node_lock_inv_pred γ_I γ_k γ_g pn lock n In C)
                -∗ CSS γ_I γ_f γ_k γ_g r m))) ∧                                       
      (∃ R, (ltree pn lock R) ∗
              (ltree pn lock  R -∗ CSS γ_I γ_f γ_k γ_g r m)).

  Proof.
    iIntros "(#H1 & H2)".
    iDestruct "H2" as (I) "H2".
    iPoseProof (inFP_domm γ_I γ_f γ_k γ_g r m I pn lock n with "[$] [$]") as "%".
    iDestruct "H2" as "((H2 & H3) & H4)".
    unfold own_nodes.
    Check big_sepS_elem_of_acc _ (dom I) n.
    rewrite (big_sepS_elem_of_acc _ (dom I) n); last first; auto.
    iDestruct "H4" as "(Hn & Hbigstar)".
    iDestruct "Hn" as (p lk In C) "(Hp & (#Hn1 & Hn))".
    iDestruct "Hn" as (lsh) "(%Hn1 & (Hn2 & Hn3))".
    iPoseProof (in_node_equiv γ_f pn p lock lk n with "[$H1 $Hn1]") as "%K1".
    destruct K1; subst.
    iSplit.
    - iExists _, _.
      iFrame.
      iIntros "H".
      iExists I. iFrame.
      iAssert ((∃ (pn lock : valC) (In0 : multiset_flowint_ur) (Cn : gmapO Key valC),
                  public_half γ_g (to_agree (pn, (lock, (n, (In0, Cn))))) ∗ 
                  inFP γ_f pn lock n ∗ ltree pn lock (node_lock_inv_pred γ_I γ_k γ_g pn lock n In0 Cn))  )  with "[$H $Hn2 $Hp]" as "Hb"; auto.
      by iSpecialize ("Hbigstar" with "[$Hb]").
    - unfold ltree.
      iExists _.
      iSplitL "Hn2 Hn3".
      iExists lsh. iSplit. done. iFrame.
      iIntros "H".
      iDestruct "H" as (lsh1) "H".
      iExists I. iFrame.
      iDestruct "H" as "(%Hm1 & Hm2)".
      iAssert ((∃ (pn lock : valC) (In0 : multiset_flowint_ur) (Cn : gmapO Key valC),
                  public_half γ_g (to_agree (pn, (lock, (n, (In0, Cn))))) ∗ 
                  inFP γ_f pn lock n ∗
                  ∃ lsh0 : share,
                    ⌜field_compatible t_struct_node [] pn ∧ readable_share lsh0⌝
                    ∧ @field_at _ _ _ CompSpecs lsh0 t_struct_node (DOT _lock) lock pn ∗
                    inv_for_lock lock (node_lock_inv_pred γ_I γ_k γ_g pn lock n In0 Cn)))
        with "[$Hp $Hm2]" as "Hb"; auto.
      iSpecialize ("Hbigstar" with "Hb").
      iFrame.
  Qed.
  
  Lemma lock_alloc (B: Type) (b: _ -> B -> mpred) (Q : B → mpred) γ_I γ_f γ_g γ_k r pn lock n:
         atomic_shift (λ C, CSS γ_I γ_f γ_g γ_k r C) ⊤ ∅ b Q ∗ inFP γ_f pn lock n -∗
         |={⊤}=> atomic_shift (λ C, CSS γ_I γ_f γ_g γ_k r C) ⊤ ∅ b Q ∗ inFP γ_f pn lock n ∗
            (∃ lsh : share,
      ⌜readable_share lsh⌝ ∧ field_at lsh t_struct_node (DOT _lock) lock pn).
  Proof.
    iIntros "(AU & #H)".
    iMod "AU" as (m) "[Hm HClose]".
    iPoseProof (in_node_inv γ_I γ_f γ_g γ_k r with "[$H $Hm]") as "InvLock".
    iDestruct "InvLock" as "(_ & InvLock)".
    iDestruct "InvLock" as (R) "[H1 H2]".
    iDestruct "H1" as (lsh) "(%Hfr & (H12 & H13))".
    destruct Hfr as (Hf & Hr).
    iPoseProof (share_divided with "[$H12]") as "H1"; auto.
    iDestruct "H1" as "(H1 & H1')".
    iDestruct "H1" as (lsh1) "(% & H1)".
    iDestruct "H1'" as (lsh2) "(% & H1')".
    iAssert (∃ lsh, ⌜readable_share lsh⌝ ∧ @field_at _ _ _ CompSpecs lsh t_struct_node (DOT _lock) lock pn) with "[$H1]" as "H3". done.
    iAssert (∃ lsh, ⌜readable_share lsh⌝ ∧ @field_at _ _ _ CompSpecs lsh t_struct_node (DOT _lock) lock pn) with "[$H1']" as "H3'". done.
    iFrame. iFrame "H".
    iDestruct "H3" as (lsh') "(% & H3)".
    iAssert (∃ lsh, ⌜field_compatible t_struct_node [] pn ∧ readable_share lsh ⌝ ∧
          (@field_at _ _ _ CompSpecs lsh t_struct_node (DOT _lock) lock pn ∗
           inv_for_lock lock R))  with "[H3 H13]" as "H1".
    { iExists _. iFrame. done. }
    iSpecialize ("H2" with "H1").
    by iSpecialize ("HClose" with "H2").
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
