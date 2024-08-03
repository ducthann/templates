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
Require Import tmpl.list. (*binary search tree*)
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
  Context `{!cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr),
            !flowintG Σ, !nodesetG Σ, !keysetG Σ, !keymapG Σ, inG Σ (frac_authR (agreeR Node))}.
  

(* struct node {int key; void *value; struct tree_t *left, *right;} node;*)
Definition t_struct_list := Tstruct _node noattr.
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
  unfold not in n.
  apply n. clear n.
  rewrite / nzmap_wf /map_Forall.
  intros i x Hf.
  assert (nzmap_wf (nzmap_car H2)) as wfH. { apply nzmap_is_wf. }
  apply map_lookup_filter_Some_1_1 in Hf.
  rewrite /nzmap_wf /map_Forall in wfH.
  eapply wfH; eauto.
Defined.

Lemma nzmap_lookup_filter_Some `{Countable K} `{CCM A}
  (P : Z * nat → Prop) (H7 : ∀ x : Z * nat, Decision (P x)) 
  (m : nzmap Z nat) (i : Z) (x : nat) :
  filter P m !! i = Some x <-> m !! i = Some x /\ P (i, x).
Proof.
  unfold lookup, nzmap_lookup .
  split.
  - intros.
    destruct m.
    unfold filter in H3.
    simpl in H3.
    apply map_lookup_filter_Some in H3. auto.
  - intros.
    destruct m.
    unfold filter. simpl.
    rewrite map_lookup_filter_Some. auto.
Qed.

Lemma nzmap_dom_filter_subseteq (P : Z * nat → Prop) `{!∀ x, Decision (P x)} (m : nzmap Z nat):
  dom (filter P m) ⊆ dom m.
Proof.
  destruct m.
  unfold filter.
  simpl.
  unfold nzmap_dom. simpl.
  apply dom_filter_subseteq.
Qed.

#[local] Obligation Tactic := idtac.

#[local] Program Instance my_specific_tree_rep : NodeRep := {
  node := fun (n : Node) (In : @multiset_flowint_ur Key _ _) (C: gmap Key data_struct.Value)
            (next:  gmap nat val) =>
  if eq_dec n nullval
  then ⌜∀ y : Key, ¬ in_outsets val_EqDecision Node_countable Key y In ∧
                     ¬ ∃ n1 : Node, n1 ≠ n ∧ in_inset val_EqDecision Node_countable Key y In n1 ∧
                     C = ∅⌝ ∧ emp
  else
  (∃ (x : Z) (v : val) (n' : Node),
      ⌜and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\
       is_pointer_or_null (next !!! 0)  /\
          (tc_val (tptr Tvoid) v) ∧ C = {[x := v]} ∧ dom (out_map In) = {[n']} ∧
        (forall y, in_outset _ _ Key y In n' <-> Z.lt x y ∧ in_inset _ _ Key y In n) ∧
        (forall y, in_outsets _ _ Key y In -> in_outset _ _ Key y In n') ⌝ ∧
       data_at Ews t_struct_list (Vint (Int.repr x), (v, (next !!! 0))) n ∗
       malloc_token Ews t_struct_list n); node_size := 1}.
(* ; node_rep_R_valid_pointer }. *)
Next Obligation.
  intros n In Cn next.
  destruct (EqDec_val n nullval). 
  - simpl. rewrite e. auto.
  - rewrite if_false; auto. iIntros "H".
    iDestruct "H" as (x v) "(%HJ & (H1 & H2))".
    iStopProof. entailer !.
Defined.
Next Obligation.
  intros n In Cn next.
  destruct (EqDec_val n nullval).
  - simpl. rewrite e. auto.
  - rewrite if_false; auto.
    iIntros "H".
    iDestruct "H" as (x v) "(%HJ & (H1 & H2))".
    iStopProof. entailer !.
Defined.

(* Spec of findnext function *)
(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
Definition findnext_spec :=
  DECLARE _findNext
  WITH x: Z, p: Node, n: val, n_pt : val, Ip : flowintT,
                Cp : (gmap Key data_struct.Value), nextp : gmap nat Node, sh: share, gv: globals
  PRE [ tptr t_struct_list, tptr (tptr tvoid), tint ]
          PROP (writable_share sh;
                (Int.min_signed ≤ x ≤ Int.max_signed)%Z
          (*; is_pointer_or_null pa; is_pointer_or_null pb*) )
          PARAMS (p; n; Vint (Int.repr x)) GLOBALS (gv)
          SEP (node p Ip Cp nextp ∗ ⌜p <> nullval /\ in_inset _ _ Key x Ip p⌝ ∧
               (* field_at sh (t_struct_tree) [StructField _t] r.1.1.1 p; *)
               data_at sh (tptr tvoid) n_pt n)
  POST [ tint ]
  ∃ (stt: enum), ∃ (n' next : val), ∃ (nnext : Node),
         PROP (match stt with
               | F | NF => (n' = p)
               | NN => (n' = next)
               end; dom (out_map Ip) = {[nnext]})
        LOCAL (temp ret_temp (enums stt))
        SEP (match stt with
               | F | NF => ⌜¬in_outsets _ _ Key x Ip⌝ ∧ data_at sh (tptr tvoid) n_pt n
               | NN => ⌜in_outset _ _ Key x Ip nnext⌝ ∧ data_at sh (tptr tvoid) next n
             end;
               node p Ip Cp nextp).

Lemma findNext: semax_body Vprog Gprog f_findNext findnext_spec.
Proof.
  start_function.
  Intros.
  unfold node.
  unfold my_specific_tree_rep.
  rewrite -> if_false; eauto.
  Intros x0 v0.
  forward.
  forward_if. (* if (_x < _y) *)
  - forward. forward. forward.
    Exists NN (nextp !!! 0) (nextp !!! 0) n'.
    unfold node, my_specific_tree_rep.
    rewrite -> if_false; auto.
    Exists x0 v0 .
    entailer !.
    specialize (H9 x).
    set_solver.
    Exists n'. entailer !.
  - (* if (_x > _y) *)
    forward_if.
    repeat forward.
    Exists NF p p n'.
    entailer !.
    apply (H10 x), (H9 x) in H7.
    lia.
    rewrite /node /my_specific_tree_rep.
    rewrite -> if_false; auto.
    Exists x0 v0 n'. entailer !.
    (* x = y *)
    forward.
    Exists F p p n'.
    rewrite /node /my_specific_tree_rep.
    rewrite -> if_false; auto.
    Exists x0 v0 n'.
    entailer !.
    assert (x = x0). lia. subst x0.
    apply (H10 x) in H7.
    apply (H9 x) in H7.
    lia.
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
       SEP (mem_mgr gv; malloc_token Ews t p; data_at_ Ews t p).

Fixpoint list_to_gmap_aux (l : list Node) (key : nat) : gmap nat Node :=
  match l with
  | [] => ∅
  | x :: xs => <[key:=x]> (list_to_gmap_aux xs (S key))
  end.

Definition list_to_gmap (l : list Node) : gmap nat Node :=
  list_to_gmap_aux l 0.

(*  Ip : @flowintT _ K_multiset_ccm  _ _ *)

Check contextualLeq _ .
(*  @flows.int (@multiset_flows.K_multiset Key Z.eq_dec Z_countable) K_multiset_ccm _  _
          {|infR := {[ tp := S ]}; outR := <<[ Znth 0 next0 := S ]>> ∅ |} = Ip; *)

Definition flow_int I:= @flows.int (@multiset_flows.K_multiset Key Z.eq_dec Z_countable)
                           K_multiset_ccm _ _ I.

Definition remap_out I tp new_node := flow_int {| infR := inf_map I; outR := <<[ tp := 0%CCM]>> <<[ new_node := out I tp ]>>(out_map I) |}.

Definition insertOp_spec :=
  DECLARE _insertOp
    WITH x: Z, v: val, stt: Z, p: Node, tp: val, l: val, dl: val, Ip: flowintT,
         Cp: (gmap Key data_struct.Value), next0: list Node, next: list Node, sh: share, gv: globals
  PRE [ tptr (tptr t_struct_list), tint, tptr tvoid, tint, tptr (struct_dlist)]
  PROP (repable_signed x; is_pointer_or_null v; length next = node_size;
        in_inset _ _ Key x Ip tp; ¬ in_outsets _ _ Key x Ip;
        is_pointer_or_null (Znth 0 next) (* ; tp = nullval*) )
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt); l)
  GLOBALS (gv)
  SEP (mem_mgr gv;
       node tp Ip Cp (list_to_gmap next0);
       field_at Tsh (struct_dlist) (DOT _list) dl l;
       data_at Ews (tptr t_struct_list) tp p;
       data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl)
  POST[ tvoid ]
  ∃ (new_node : Node) (I_new I1: flowintT),
  PROP (new_node <> nullval)
  LOCAL ()
  SEP (mem_mgr gv; node new_node I_new ({[x := v]}) (list_to_gmap next);
       node tp I1 Cp (list_to_gmap next0);
       field_at Tsh struct_dlist (DOT _list) dl l;
       data_at Ews (tptr t_struct_list) new_node p;
     data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl;
     ⌜∀ I0, contextualLeq _ (I0 ⋅ Ip) ((remap_out Ip tp new_node) ⋅ I1 ⋅ I_new) ∧
                inf ((remap_out Ip tp new_node) ⋅ I1 ⋅ I_new) new_node = 0%CCM⌝).

Search data_at.

(*
Lemma ne_pointer sh p1 p2 t v1 v2:
  writable_share sh -> sh ≠ Share.bot -> (0 < sizeof t)%Z ->
  data_at sh t v1 p1 ∗ data_at sh t v2 p2 -∗ ⌜p1 <> p2⌝.
Proof.
  intros.
  iIntros "(H1 & H2)".
  destruct (decide (p1 = p2)) as [-> | Hp]; try done.
  iDestruct (data_at_conflict with "[$H1 $H2]") as "H"; try done.
Qed.
*)

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec; surely_malloc_spec; insertOp_spec]).

(* Proving insertOp satisfies spec *)
Lemma insertOp: semax_body Vprog Gprog f_insertOp insertOp_spec.
Proof.
  start_function.
  forward_call (t_struct_list, gv).
  unfold node, my_specific_tree_rep.
  Intros new_node.
  destruct (decide (tp = nullval)) as [Heq | Hneq].
  {
    rewrite Heq.
    rewrite -> if_true; auto.
    Intros.
    forward. forward. forward. forward. entailer !. rewrite Zlength_correct.
    simpl in *. rewrite -> H3. lia.
    specialize (H7 x).
    destruct H7.
    
    
  assert (tp <> nullval). admit.
  rewrite -> if_false; auto.
  Intros x0 v0.
  forward. forward. forward. forward.
  rewrite Zlength_correct.
  simpl in *.
  rewrite -> H3.
  entailer !.
  Intros n'.
  forward. forward.
  assert_PROP (new_node <> tp). entailer !.
  unfold in_outsets in H5.
  assert (forall n, ¬ in_outset val_EqDecision Node_countable Key x Ip n) as allNot. set_solver.
  assert (Z.le x x0) as Hle.
  { apply Ztac.elim_concl_le.
    intros Hlt.
    assert (Z.lt x0 x ∧ in_inset val_EqDecision Node_countable Key x Ip tp) as Hcm; auto.
    apply (H13 x) in Hcm. set_solver.
  }
  assert_PROP (new_node <> nullval). entailer !.
  assert (list_to_gmap_aux next 0 !!! 0 = Znth 0 next /\
            list_to_gmap_aux next0 0 !!! 0 = Znth 0 next0) as (Hznth & Hznth0).
  { split; unfold Znth; [destruct next as [| x' xs'] | destruct next0 as [| x' xs']];
      simpl; auto; rewrite lookup_total_insert; auto.
  }
  rewrite /in_outset /out /in_inset in H13.
  rewrite /in_outsets /in_outset /out in H14.
  rewrite /in_outset in allNot.
   
  Exists new_node.
  set m1 := filter (fun '(k, _) => Z.lt x k) (inf Ip tp).
  (* Set Printing Implicit. *)
  Exists (flow_int {| infR := {[ new_node := inf Ip tp ]}; outR := <<[ tp := m1 ]>> ∅ |}).
  Exists (flow_int {| infR := {[ tp := m1 ]}; outR := <<[ n' := out Ip n' ]>> ∅ |}).
  rewrite / node / my_specific_tree_rep.
  rewrite if_false; auto.
  rewrite if_false; auto.
  entailer !.
  Exists x v tp.
  Exists x0 v0 n'.
  entailer !.
  repeat split; try done.
  - rewrite /list_to_gmap Hznth; auto. 
  - rewrite / out_map /inf /=.
    rewrite <- leibniz_equiv_iff.
    rewrite nzmap_dom_insert_nonzero. set_solver.
    rewrite /in_inset in H4.
    apply nzmap_elem_of_dom_total in H4.
    destruct (lookup) eqn: Eqn.
    rewrite /inf Eqn /= in H4.
    rewrite <- nzmap_elem_of_dom_total in H4.
    admit.
    unfold inf in H4. rewrite Eqn in H4. simpl in H4.
    contradiction.
  - rewrite /in_outset /out /out_map //= nzmap_lookup_total_insert in H11.
    rewrite / in_inset in H4.
    apply nzmap_elem_of_dom_total in H11.
    rewrite nzmap_lookup_total_alt in H11.
    rewrite /default /id in H11.
    destruct (lookup) eqn: Eqn.
    apply (nzmap_lookup_filter_Some (λ '(k, _), (x < k)%Z) _ (@inf (@multiset_flows.K_multiset Key Z.eq_dec Z_countable)
            (@multiset_flows.K_multiset_ccm Key Z.eq_dec Z_countable) val_EqDecision Node_countable Ip
            tp)  y n) in Eqn.
    lia.
    contradiction.
  - rewrite /in_outset /out /out_map /= nzmap_lookup_total_insert /inf in H11.
    rewrite /in_inset /inf lookup_insert /=. 
    rewrite /default /id in H11.
    destruct (lookup) eqn: Eqn.
    + assert (dom (filter (λ '(k, _), (x < k)%Z) k) ⊆ dom k). { apply nzmap_dom_filter_subseteq. }
      set_solver.
    + rewrite /in_inset /inf Eqn /default in H4.
      apply nzmap_elem_of_dom_total in H4.
      rewrite nzmap_lookup_empty in H4. contradiction.
  - intros.
    destruct H11.
    rewrite /in_inset /out /out_map /inf lookup_insert /= in H31. 
    rewrite /in_outset /out /out_map nzmap_lookup_total_insert /inf.
    destruct (lookup) eqn: Eqn.
    simpl in H31.
    rewrite /default /id.
    admit.
    set_solver.
  - intros.
    rewrite /in_outsets /in_outset /out /out_map /inf /= in H11. 
    destruct H11 as (n1 & H11).
    rewrite /in_outset /out /out_map nzmap_lookup_total_insert /inf.
    destruct (decide (n1 = tp)).
    { subst. rewrite nzmap_lookup_total_insert in H11. auto. }
    { rewrite nzmap_lookup_total_insert_ne in H11. set_solver. auto. }
  - simpl.
    rewrite <- leibniz_equiv_iff.
    rewrite nzmap_dom_insert_nonzero.
    set_solver.
    rewrite /out.
    apply nzmap_elem_of_dom_total. rewrite H12. set_solver.
  - rewrite /in_outset /out /= nzmap_lookup_total_insert in H11. 
    specialize (H13 y).
    apply H13 in H11. lia.
  - rewrite /in_inset /inf lookup_insert. 
    rewrite /in_outset /out nzmap_lookup_total_insert /= in H11. 
    specialize (H13 y).
    apply H13 in H11.
    destruct H11.
    assert ((x < y)%Z). lia.
    destruct (lookup) eqn: Eqn.
    rewrite /default /id.
    admit.
    rewrite /in_inset in H4.
    rewrite /default /id.
    rewrite /inf in H31. rewrite Eqn /= in H31. set_solver.
  - intros.
    destruct H11.
    rewrite /in_inset /out /out_map /inf /= lookup_insert in H31. 
    rewrite /in_outset /out nzmap_lookup_total_insert /=. 
    apply H14.
    exists n'. apply H13.
    split; try done.
    destruct (lookup) eqn: Eqn.
    unfold inf.
    rewrite Eqn /=.
    assert (dom (filter (λ '(k, _), (x < k)%Z) k) ⊆ dom k). { apply nzmap_dom_filter_subseteq. }
    set_solver.
    apply nzmap_elem_of_dom_total in H31.
    rewrite /in_inset /inf in H4.
    rewrite Eqn in H4.
    unfold default in H4. set_solver.
  - intros.
    rewrite /in_outsets /in_outset /out nzmap_lookup_total_insert /=.
    apply H14.
    rewrite /in_outsets /in_outset /out /= in H11. 
    destruct H11 as (n1 & H11).
    destruct (decide (n1 = n')) as [-> | Hn1n'].
    { rewrite nzmap_lookup_total_insert in H11. by eexists. }
    { rewrite nzmap_lookup_total_insert_ne in H11. by eexists. auto. }
  - rewrite Hznth. entailer !.
    iIntros "_".
    iPureIntro.

    
    set I1 := flows.int
       {|
         infR := {[new_node := inf Ip tp]};
         outR := <<[ tp := filter (λ '(k, _), (x < k)%Z) (inf Ip tp) ]>> ∅
       |}.
    set I2 := flows.int
         {|
           infR := {[tp := filter (λ '(k, _), (x < k)%Z) (inf Ip tp)]};
           outR := <<[ n' := out Ip n' ]>> ∅
         |}.

    Check keyset _ _ Key I1 tp.
    
    
    Admitted.


