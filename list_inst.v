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
  Locate VSTGS0.
  Context `{N: NodeRep } `{EqDecision K} `{Countable K}.
  Locate VSTGS0.
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

#[local] Obligation Tactic := idtac.

#[local] Program Instance my_specific_tree_rep : NodeRep := {
  node := fun (n : Node) (In : @multiset_flowint_ur Key _ _) (C: gmap Key data_struct.Value)
            (next:  gmap nat Node) =>
  if eq_dec n nullval
  then ⌜∀ y : Key, ¬ in_outsets val_EqDecision Node_countable Key y In ∧
                     ¬ ∃ n1 : Node, n1 ≠ n ∧ in_inset val_EqDecision Node_countable Key y In n1 ∧
                     C = ∅⌝ ∧ emp
  else
  (∃ (x : Z) (v : val),
      ⌜and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\
       is_pointer_or_null (next !!! 0)  /\
          (tc_val (tptr Tvoid) v) ∧ C = {[x := v]} ∧
        (forall y, in_outset _ _ _ y In (next !!! 0) <-> Z.lt x y ∧ in_inset _ _ _ y In n) ∧
        (forall y, in_outsets _ _ _ y In -> in_outset _ _ _ y In (next !!! 0)) ⌝ ∧
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
          SEP (node p Ip Cp nextp ∗ ⌜p <> nullval /\ in_inset _ _ _ x Ip p⌝ ∧
               (* field_at sh (t_struct_tree) [StructField _t] r.1.1.1 p; *)
               data_at sh (tptr tvoid) n_pt n)
  POST [ tint ]
  ∃ (stt: enum), ∃ (n' next : Node),
         PROP (match stt with
               | F | NF => (n' = p)
               | NN => (n' = next)
               end)
        LOCAL (temp ret_temp (enums stt))
        SEP (match stt with
               | F | NF => ⌜¬in_outsets _ _ _ x Ip⌝ ∧ data_at sh (tptr tvoid) n_pt n
               | NN => ⌜in_outset _ _ _ x Ip next⌝ ∧ data_at sh (tptr tvoid) next n
             end ∗
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
    Exists NN (nextp !!! 0) (nextp !!! 0).
    unfold node, my_specific_tree_rep.
    rewrite -> if_false; auto.
    Exists x0 v0 .
    entailer !.
    apply (H8 x). split. lia.
    auto.
  - (* if (_x > _y) *)
    forward_if.
    repeat forward.
    Exists NF p p.
    entailer !.
    specialize (H9 x).
    specialize (H9 H7).
    specialize (H8 x).
    apply H8 in H9.
    destruct H9. lia.
    unfold node, my_specific_tree_rep.
    rewrite -> if_false; auto.
    Exists x0 v0.
    entailer !.
    (* x = y *)
    forward.
    Exists F p p.
    unfold node, my_specific_tree_rep.
    rewrite -> if_false; auto.
    Exists x0 v0.
    entailer !.
    assert (x = x0). lia.
    subst x0.
    specialize (H8 x).
    specialize (H9 x).
    apply H9 in H7.
    apply H8 in H7. lia.
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



Definition insertOp_spec :=
  DECLARE _insertOp
    WITH x: Z, v: val, stt: Z, p: Node, tp: val, l: val, dl: val,
                  Ip : @flowintT _ K_multiset_ccm  _ _,
                    Cp : (gmap Key data_struct.Value),
                     (* pnext : gmap nat Node, *)
                      next0: list Node, next: list Node,
                        sh: share, gv: globals
  PRE [ tptr (tptr t_struct_list), tint, tptr tvoid, tint, tptr (struct_dlist)]
  PROP (repable_signed x; is_pointer_or_null v; (*node_size = length ((gmap_to_node_list pnext)); *)
        length next = node_size;
        (* is_pointer_or_null (Znth 0 (gmap_to_node_list pnext)); *)
        is_pointer_or_null (Znth 0 next);
        tp = nullval)
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt); l)
  GLOBALS (gv)
  SEP (mem_mgr gv; node tp Ip Cp (list_to_gmap next0);
       field_at Tsh (struct_dlist) (DOT _list) dl l;
       data_at Ews (tptr t_struct_list) tp p;
                   (* field_at Ews (struct_dlist) [StructField _size] (Vptrofs (Ptrofs.repr 2%Z)) l ∗ *)
                   (* data_at Ews (tarray (tptr tvoid) (Zlength (gmap_to_node_list pnext) )) (gmap_to_node_list pnext) dl *)
       data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl
       )
  POST[ tvoid ]
  ∃ (pnt : Node),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv; node pnt Ip (<[x := v]> Cp) (list_to_gmap next);
       node tp Ip Cp (list_to_gmap next0);
       field_at Tsh struct_dlist (DOT _list) dl l;
       data_at Ews (tptr t_struct_list) pnt p;
       (*data_at Ews (tarray (tptr tvoid) (Zlength (gmap_to_node_list pnext))) (gmap_to_node_list pnext) dl*)
     data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl  

  ).



Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
     surely_malloc_spec; insertOp_spec (* ; traverse_spec; insert_spec; treebox_new_spec*) ]).
(* Proving insertOp satisfies spec *)

Lemma insertOp: semax_body Vprog Gprog f_insertOp insertOp_spec.
Proof.
  start_function.
  forward_call (t_struct_list, gv).
  unfold node, my_specific_tree_rep.
  Intros new_node.
  clear H5.
  assert (tp <> nullval). admit.
  rewrite -> if_false; auto.
  forward.
  forward.
  forward.
  forward.
  entailer !.
  rewrite Zlength_correct.
  simpl in *.
  rewrite -> H3. lia.
  forward.
  forward.
  assert_PROP(new_node ≠ nullval). entailer !.
  Exists new_node.
  unfold node, my_specific_tree_rep.
  rewrite if_false; auto.
  Intros x0 v0.
  assert (list_to_gmap_aux next 0 !!! 0 = Znth 0 next).
  {
    unfold Znth.
    destruct next as [| x' xs'].
    - simpl. auto.
    - rewrite lookup_total_insert. auto.
  }
  rewrite H13.
  entailer !.
  Exists x v.
  rewrite -> if_false; auto.
  Exists x0 v0.
  entailer !.
  entailer !.
  split. admit.
  split.
  intros.
  split.
  - intros.
    split.
    admit.
    
  - 
    intros.
    specialize (H5 y).
    destruct H5.
    unfold in_outsets in H5. set_solver.
  - intros.
    specialize (H5 y).
    destruct H5.
    destruct H19.
    set_solver.
  - intros.
    set_solver.
  Qed.

Lemma insertOp: semax_body Vprog Gprog f_insertOp insertOp_spec.
Proof.
  start_function.
  forward_call (t_struct_list, gv).
  unfold node, my_specific_tree_rep.
  Intros new_node.
  subst.
  rewrite -> if_true; auto.
  forward.
  forward.
  forward.
  forward.
  entailer !.
  rewrite Zlength_correct.
  simpl in *.
  rewrite -> H3. lia.
  forward.
  forward.
  assert_PROP(new_node ≠ nullval). entailer !.
  Exists new_node.
  unfold node, my_specific_tree_rep.
  rewrite if_false; auto.
  entailer !.
  Exists x v.
  assert (list_to_gmap_aux next 0 !!! 0 = Znth 0 next).
  {
    unfold Znth.
    destruct next as [| x' xs'].
    - simpl. auto.
    - rewrite lookup_total_insert. auto.
  }
  rewrite H18.
  entailer !.
  split.
  intros.
  split.
  - intros.
    specialize (H5 y).
    destruct H5.
    unfold in_outsets in H5. set_solver.
  - intros.
    specialize (H5 y).
    destruct H5.
    destruct H19.
    set_solver.
  - intros.
    set_solver.
  Qed.
