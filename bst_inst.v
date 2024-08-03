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
Require Import tmpl.bst. (*binary search tree*)
Require Import tmpl.keyset_ra_ora.
Require Import tmpl.puretree.
Require Import tmpl.data_struct.
Require Import tmpl.flows_ora.


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

#[global] Instance gmap_inhabited V : Inhabitant (gmap key V).
Proof. unfold Inhabitant; apply empty. Defined.

#[global] Instance number_inhabited: Inhabitant number.
Proof. unfold Inhabitant; apply Pos_Infinity. Defined.

Section give_up_traverse.
  Context `{N: NodeRep } `{EqDecision K} `{Countable K}.
  Context `{!VSTGS unit Σ, !cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr),
            !flowintG Σ, !nodesetG Σ, !keysetG Σ, !keymapG Σ, inG Σ (frac_authR (agreeR Node))}.

  (* struct node {int key; void *value; struct tree_t *left, *right;} node;*)
  Definition t_struct_tree := Tstruct _node noattr.
  (* Define for dynamic list *)
  Definition struct_dlist := Tstruct _DList noattr.

(* struct tree_t {node *t; lock_t *lock; int min; int max; } tree_t; *)
(* Definition t_struct_tree_t := Tstruct _tree_t noattr. *)

(* node_rep_R r.1.1.1 r.1.2 r.2 g, and r is type of node_info *)

(*
Class NodeRep : Type := {
    node : val → @multiset_flowint_ur Key _ _ → gmap Key Value -> gmap nat Node -> mpred;
    (* node_sep_star: ∀ n I_n I_n' C C', node n I_n C ∗ node n I_n' C' -∗ False; *)
    node_rep_R_valid_pointer: forall n I_n C next, node n I_n C next -∗ valid_pointer n;
    node_rep_R_pointer_null: forall n I_n C next, node n I_n C next -∗ ⌜is_pointer_or_null n⌝;
    node_size: nat;
}.

 *)

Local Instance nzmap_filter: Filter (Z * nat) (@multiset_flows.K_multiset Key Z.eq_dec Z_countable).
Proof.
  intros ???.
  eapply (NZMap (filter P (nzmap_car H2)) _).
  Unshelve.
  unfold bool_decide.
  destruct (nzmap_wf_decision Key (filter P (nzmap_car H2))); try done.
  rewrite /not in n. apply n. clear n.
  rewrite / nzmap_wf /map_Forall.
  intros i x Hf.
  assert (nzmap_wf (nzmap_car H2)) as wfH. { apply nzmap_is_wf. }
  apply map_lookup_filter_Some_1_1 in Hf.
  rewrite /nzmap_wf /map_Forall in wfH.
  eapply wfH; eauto.
Defined.

Lemma nzmap_lookup_filter_Some `{Countable K} `{CCM A}
  (P : Z * nat → Prop) (H7 : ∀ x : Z * nat, Decision (P x)) (m : nzmap Z nat) (i : Z) (x : nat):
  filter P m !! i = Some x <-> m !! i = Some x /\ P (i, x).
Proof.
  rewrite /lookup /nzmap_lookup.
  split; intros; destruct m.
  - rewrite /filter /= in H3. { by apply map_lookup_filter_Some in H3. }
  - by rewrite /filter map_lookup_filter_Some.
Qed.

Lemma nzmap_dom_filter_subseteq (P : Z * nat → Prop) `{!∀ x, Decision (P x)} (m : nzmap Z nat):
  dom (filter P m) ⊆ dom m.
Proof. destruct m. rewrite / filter /nzmap_dom /=. apply dom_filter_subseteq. Qed.


#[local] Obligation Tactic := idtac.

#[local] Program Instance my_specific_tree_rep : NodeRep := {
  node := fun (n : Node) (In : @multiset_flowint_ur Key _ _) (C: gmap Key data_struct.Value)
            (next:  gmap nat val) =>
  if eq_dec n nullval
  then ⌜inf In n = 0%CCM 
         (* (∃ (k : Z), ∀ (k' : Z), (k < k')%Z -> k' ∈ dom (inf In n)) ∧ 
         out_map In = ∅ ∧ C = ∅ /\ dom In = {[ n ]} *)⌝ ∧ emp
  else
  (∃ (x : Z) (v : val) (m1 m2: Node),
      ⌜(Int.min_signed <= x <= Int.max_signed)%Z /\ is_pointer_or_null (next !!! 0) /\
        is_pointer_or_null (next !!! 1) /\ (tc_val (tptr Tvoid) v)
        ∧ C = {[x := v]}
        ∧ (dom (out_map In) = {[ if (eq_dec m1 nullval) then nullval else m1; if (eq_dec m2 nullval) then nullval else m2]}) ∧ dom In = {[ n ]} ∧
        (forall y, in_outset _ _ Key y In m1 <-> (y < x)%Z ∧ in_inset _ _ _ y In n) ∧
        (forall y, in_outset _ _ Key y In m2 <-> (x < y)%Z ∧ in_inset _ _ _ y In n) ∧
        (forall y, in_outsets _ _ Key y In -> in_outset _ _ _ y In m1 ∨ in_outset _ _ _ y In m2)⌝ ∧
       data_at Ews t_struct_tree (Vint (Int.repr x), (v, ((next !!! 0), (next !!! 1)))) n ∗
       malloc_token Ews t_struct_tree n); node_size := 2}.
(* ; node_rep_R_valid_pointer }. *)
Next Obligation.
  intros n In Cn next.
  destruct (EqDec_val n nullval) as [-> | Hn]; auto.
  rewrite if_false; auto.
  iIntros "H". iDestruct "H" as (x v m1 m2) "H". iStopProof. entailer !.
Defined.
Next Obligation.
  intros n In Cn next.
  destruct (EqDec_val n nullval) as [-> | Hn]; auto.
  rewrite if_false; auto.
  iIntros "H". iDestruct "H" as (x v m1 m2) "H". iStopProof. entailer !.
Defined.

(* Spec of findnext function *)
(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
Definition findnext_spec :=
  DECLARE _findNext
  WITH x: Z, p: Node, n: val, n_pt : val, Ip : flowintT,
                Cp : (gmap Key data_struct.Value), nextp : gmap nat Node, sh: share, gv: globals
  PRE [ tptr t_struct_tree, tptr (tptr tvoid), tint ]
          PROP (writable_share sh; (Int.min_signed ≤ x ≤ Int.max_signed)%Z)
          PARAMS (p; n; Vint (Int.repr x)) GLOBALS (gv)
          SEP (node p Ip Cp nextp ∗ ⌜p <> nullval /\ in_inset _ _ Key x Ip p⌝ ∧
               data_at sh (tptr tvoid) n_pt n)
  POST [ tint ]
  ∃ (stt: enum), ∃ (n' next : val), ∃ (m1 m2 : Node), (* list of m for generic *)
         PROP (match stt with
               | F | NF => (n' = p)
               | NN => (n' = next)
               end; (dom (out_map Ip) = {[ if (eq_dec m1 nullval) then nullval else m1; if (eq_dec m2 nullval) then nullval else m2]}))
        LOCAL (temp ret_temp (enums stt))
        SEP (match stt with
               | F | NF => ⌜¬in_outsets _ _ _ x Ip⌝ ∧ data_at sh (tptr tvoid) n_pt n
               | NN => ⌜in_outset _ _ _ x Ip m1 ∨ in_outset _ _ _ x Ip m2⌝ ∧
                        data_at sh (tptr tvoid) next n
             end ∗ node p Ip Cp nextp).

Lemma findNext: semax_body Vprog Gprog f_findNext findnext_spec.
Proof.
  start_function.
  Intros.
  rewrite /node /my_specific_tree_rep if_false; eauto.
  Intros x0 v0 m1 m2.
  forward.
  forward_if. (* if (_x < _y) *)
  - do 3 forward. 
    Exists NN (nextp !!! 0) (nextp !!! 0) m1 m2.
    rewrite /node /my_specific_tree_rep.
    destruct (eq_dec p nullval); auto. { contradiction. }
    Exists x0 v0 m1 m2.
    entailer !.
    left. apply (H11 x); auto. 
  - (* if (_x > _y) *)
    forward_if.
    do 3 forward.
    Exists NN (nextp !!! 1) (nextp !!! 1) m1 m2.
    rewrite /node /my_specific_tree_rep.
    destruct (eq_dec p nullval); auto. { contradiction. }
    Exists x0 v0 m1 m2.
    entailer !.
    right. apply (H12 x); auto.
    (* x = y *)
    forward.
    Exists F p p m1 m2.
    rewrite /node /my_specific_tree_rep.
    destruct (eq_dec p nullval); auto. { contradiction. }
    Exists x0 v0 m1 m2.
    entailer !.
    assert (x = x0). lia. subst x0.
    specialize (H11 x).
    specialize (H12 x).
    specialize (H13 x).
    apply H13 in H8.
    destruct H8.
    { apply H11 in H8. lia. }
    { apply H12 in H8. lia. }
Qed.

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t: type, gv: globals
   PRE [ size_t ]
       PROP (and (Z.le 0 (sizeof t)) (Z.lt (sizeof t) Int.max_unsigned);
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ]
    ∃ p: _,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; malloc_token Ews t p ∗ data_at_ Ews t p).

Fixpoint list_to_gmap_aux (l : list Node) (key : nat) : gmap nat Node :=
  match l with
  | [] => ∅
  | x :: xs => <[key:=x]> (list_to_gmap_aux xs (S key))
  end.

Definition list_to_gmap (l : list Node) : gmap nat Node :=
  list_to_gmap_aux l 0.

(*  Ip : @flowintT _ K_multiset_ccm  _ _ *)

(*  @flows.int (@multiset_flows.K_multiset Key Z.eq_dec Z_countable) K_multiset_ccm _  _
          {|infR := {[ tp := S ]}; outR := <<[ Znth 0 next0 := S ]>> ∅ |} = Ip; *)

Definition flow_int I:= @flows.int (@multiset_flows.K_multiset Key Z.eq_dec Z_countable)
                           K_multiset_ccm _ _ I.

Definition remap_out I I_new new_node:=
  flow_int {| infR := inf_map I; outR := <<[ new_node := inf I_new new_node ]>>∅ |}.

Definition flowint_T := @flowintT (@multiset_flows.K_multiset Key Z.eq_dec Z_countable) _ _ _.

(* Definition  @I_empty (@multiset_flows.K_multiset Key Z.eq_dec Z_countable) _ _ _. *)

Lemma contextualLeq_insert_BST_node_empty (Ip: flowint_T) (new_node: val) m1 ks:
     let I_new := flow_int {| infR := {[new_node := m1]}; outR := ∅ |} in
     Ip = flow_int I_emptyR -> m1 <> 0%CCM ->
    (forall (I0 : flowint_T), ✓ (I0 ⋅ Ip) ∧ (dom I0 ## dom I_new) ∧ 
                         I0 = flow_int {| infR := ks; outR := ∅ |}
            -> contextualLeq _ (I0 ⋅ Ip) ((remap_out I0 I_new new_node) ⋅ I_new)).
Proof.
  intros.
  destruct H3 as (? & ?).
  assert (✓ I_new) as VInew; auto.
  {
    rewrite intValid_unfold.
    do 2 (split; auto).
    rewrite /I_new /out_map /= /dom /=.
    set_solver.
  }
  set I0' := remap_out I0 I_new new_node.
  assert (✓ (I0' ⋅ I_new)) as VI0'new.
  {
    pose proof VInew as VInew'.
    apply intValid_composable.
    do 2 (split ; auto).
    - simpl.
      apply intValid_unfold in VInew.
      destruct VInew as (? & ? & ?).
      rewrite /I_new /= in H6 .
      rewrite nzmap_dom_insert_nonzero. set_solver.
      rewrite /inf /=.
      rewrite lookup_insert. simpl. auto.
    - intros Hin.
      simpl in Hin.
      simpl. admit.
    - repeat (split; auto).
      + rewrite /I0' /I_new /flowint_dom /=. set_solver. 
      + intros i x Hix.
        rewrite /I_new /out /=.
        rewrite nzmap_lookup_empty.
        rewrite ccm_comm ccm_pinv_unit ccm_right_id.
        rewrite /inf. rewrite Hix. auto.
      + intros i x Hix.
        rewrite /I0' /I_new /out /inf /=.
        assert (i = new_node) as ->.
        {
          rewrite /I_new /= in Hix.
          destruct (decide (i = new_node)); auto.
          rewrite lookup_insert_ne in Hix; auto.
          set_solver.
        }
        rewrite nzmap_lookup_total_insert.
        rewrite /inf /=.
        rewrite ccm_pinv_inv ccm_right_id lookup_insert.
        rewrite /I_new /= in Hix.
        rewrite lookup_insert in Hix.
        by injection Hix.
  }
  repeat split; try done.
  - rewrite intComp_dom; auto.
    rewrite intComp_dom; auto.
    rewrite H1 /I0' /I_new /= /flowint_dom /=.
    set_solver.
  - intros x Hx.
    rewrite intComp_dom in Hx; auto.
    rewrite H1 /= /flowint_dom /inf_map /= in Hx.
    assert (x ∈ dom I0). set_solver.
    assert (x ∈ dom I0'). set_solver.
    rewrite intComp_inf_1; auto.
    rewrite intComp_inf_1; auto.
    assert (out Ip x = out I_new x) as ->.
    {
      rewrite H1 /I_new /out /=. auto.
    }
    assert (inf I0 x = inf I0' x) as ->. set_solver.
    auto. 
  - intros x Hx.
    destruct (decide (x ∈ dom (I0 ⋅ Ip))) as [Hout | Hout].
    {
      rewrite intComp_dom in Hout; auto.
      rewrite intComp_dom in Hx; auto.
      assert (x ∈ dom I0). set_solver. set_solver.
    }
    {
      rewrite intComp_unfold_out; auto.
      rewrite intComp_unfold_out; auto.
      rewrite H1 /I0' /I_new /= /out /=.
      assert (x <> new_node).
      { destruct (decide (x = new_node)) as [-> | Hnew]; try done.
        { rewrite intComp_dom in Hx; auto.
          set_solver. 
        }
      }
      rewrite nzmap_lookup_total_insert_ne; auto.
      destruct H4 as (? & ?).
      rewrite H6. simpl. auto.
    }
    Admitted.

Definition insertOp_spec :=
  DECLARE _insertOp
    WITH x: Z, v: val, stt: Z, p: Node, tp: val, l: val, dl: val, Ip: flowintT,
         Cp: (gmap Key data_struct.Value), next0: list Node, next: list Node, sh: share, gv: globals
  PRE [ tptr (tptr t_struct_tree), tint, tptr tvoid, tint, tptr (struct_dlist)]
  PROP (repable_signed x; is_pointer_or_null v;
        is_pointer_or_null (Znth 0 next); is_pointer_or_null (Znth 1 next);
        in_inset _ _ Key x Ip tp; ¬ in_outsets _ _ Key x Ip;
        length next = node_size; tp = nullval)
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt); l)
  GLOBALS (gv)
  SEP (mem_mgr gv;
       node tp Ip Cp (list_to_gmap next0);
       field_at Tsh (struct_dlist) (DOT _list) dl l;
       data_at Ews (tptr t_struct_tree) tp p;
       data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl)
  POST[ tvoid ]
  ∃ (new_node : Node) (I_new: flowintT), (* It is a combination of two new I1 and I2 flows *)
  PROP (new_node <> nullval)
  LOCAL ()
  SEP (mem_mgr gv; node new_node I_new ({[x := v]}) (list_to_gmap next);
       field_at Tsh struct_dlist (DOT _list) dl l;
       data_at Ews (tptr t_struct_tree) new_node p;
       data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl;
     ⌜∀ I0, ✓ (I0 ⋅ Ip) ∧ (dom I0 ## dom I_new) ∧ 
                         I0 = flow_int {| infR := ks; outR := ∅ |}
            -> contextualLeq _ (I0 ⋅ Ip) ((remap_out I0 I_new new_node) ⋅ I_new)⌝).

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; makelock_spec; surely_malloc_spec; insertOp_spec]).

(* Proving insertOp satisfies spec *)
Lemma insertOp: semax_body Vprog Gprog f_insertOp insertOp_spec.
Proof.
  start_function.
  forward_call (t_struct_tree, gv).
  Intros new_node.
  do 4 forward.
  entailer !.
  simpl in H7. by rewrite Zlength_correct H7.
  do 3 forward.
  entailer !.
  simpl in H7. by rewrite Zlength_correct H7.
  do 2 forward.
  Exists new_node.
  assert_PROP (new_node <> nullval) by entailer !.
  rewrite /in_outsets in H6. 
  assert (forall n, ¬in_outset val_EqDecision Node_countable Key x Ip n) as allNot. set_solver.
  clear H6.
  subst tp.
  unfold node at 1. rewrite /my_specific_tree_rep.
  rewrite -> if_true; auto.
  Intros.
  Exists (flow_int {| infR := {[ new_node := inf Ip nullval ]}; outR :=  ∅ |}).
  Exists (flow_int I_emptyR).
  Exists (flow_int I_emptyR).
  entailer !.
  assert_PROP (new_node <> nullval). entailer !.
  unfold node at 1.
  rewrite -> if_false; auto.
  Exists x v nullval nullval.
  entailer !.
  repeat split; try done.
  + admit.
  + admit.
  + set_solver.
  + intros (HLe & Hin).
    rewrite /in_inset /inf /= lookup_insert /= in Hin.
    rewrite /inf in H6.
    rewrite H6 in Hin. set_solver.
  + intros (HLe & Hin).
    rewrite /in_inset /inf /= lookup_insert /= in Hin.
    rewrite /inf in H6. rewrite H6 in Hin. set_solver.
  + intros.
    rewrite /in_outsets in H22.
    destruct H22 as (? & H22).
    rewrite /inf in H6.
    left.
    rewrite /in_outset /= /out /out_map /= in H22.
    rewrite nzmap_lookup_empty in H22. set_solver.
  + assert (Znth 0 next = list_to_gmap next !!! 0). admit.
    assert (Znth 1 next = list_to_gmap next !!! 1). admit.
    rewrite H22. rewrite H23. entailer !.
    iIntros "_". iPureIntro.
    do 2 ( split; auto).
    intros I0 HI0p.
    destruct HI0p as (? & ? & ? & ? & ? & ?).
    eapply  (contextualLeq_insert_BST_node_empty Ip (flow_int I_emptyR) (flow_int I_emptyR) new_node); try done.
    admit.
    apply intComp_valid_proj2 in H25.
    apply intValid_unfold in H25.
    destruct H25 as (? & ? & ?).
    rewrite H6 in H27.
    rewrite /out in H27.
    Search nzmap 0%CCM.
    rewrite <- nzmap_elem_of_dom_total2 in H27.

Admitted.
