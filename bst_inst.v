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

 Check list Node.


  
#[local] Obligation Tactic := idtac.

#[local] Program Instance my_specific_tree_rep : NodeRep := {
  node := fun (n : Node) (In : @multiset_flowint_ur Key _ _) (C: gmap Key data_struct.Value)
            (next:  gmap nat Node) =>
  if eq_dec n nullval
  then ⌜True⌝
  else
  (∃ (x : Z) (v : val) (p1 p2: nat),
      ⌜and (Z.le Int.min_signed x) (Z.le x Int.max_signed) /\
       is_pointer_or_null (next !!! p1) /\ is_pointer_or_null (next !!! p2) /\
          (tc_val (tptr Tvoid) v) ∧
        (forall y, in_outset _ _ _ y In (next !!! p1) <-> Z.lt y x ∧ in_inset _ _ _ y In n) ∧
        (forall y, in_outset _ _ _ y In (next !!! p2) <-> Z.lt x y ∧ in_inset _ _ _ y In n) ∧
        (forall y, in_outsets _ _ _ y In -> in_outset _ _ _ y In (next !!! p1) ∨ in_outset _ _ _ y In (next !!! p2))⌝ ∧
       data_at Ews t_struct_tree (Vint (Int.repr x), (v, ((next !!! p1), (next !!! p2)))) n ∗
       malloc_token Ews t_struct_tree n); node_size := 2}.
(* ; node_rep_R_valid_pointer }. *)
Next Obligation.
  intros n In Cn next. 
  destruct (EqDec_val n nullval). 
  - simpl. rewrite e. auto.
  - rewrite if_false; auto. iIntros "H".
    iDestruct "H" as (x v p1 p2) "(%HJ & (H1 & H2))".
    iStopProof. entailer !.
Defined.
Next Obligation.
  intros n In Cn next.
  destruct (EqDec_val n nullval).
  - simpl. rewrite e. auto.
  - rewrite if_false; auto.
    iIntros "H".
    iDestruct "H" as (x v p1 p2) "(%HJ & (H1 & H2))".
    iStopProof. entailer !.
Defined.

(* Spec of findnext function *)
(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
Definition findnext_spec :=
  DECLARE _findNext
  WITH x: Z, p: Node, n: val, n_pt : val, Ip : flowintT,
                Cp : (gmap Key data_struct.Value), nextp : gmap nat Node, sh: share, gv: globals
  PRE [ tptr t_struct_tree, tptr (tptr tvoid), tint ]
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
  Intros x0 v0 p1 p2.
  forward.
  forward_if. (* if (_x < _y) *)
  - forward. forward. forward.
    Exists NN (nextp !!! p1) (nextp !!! p1) .
    unfold node.
    unfold my_specific_tree_rep.
    rewrite -> if_false; auto.
    Exists x0 v0 p1 p2.
    entailer !.
    apply (H8 x). split. lia.
    auto.
  - (* if (_x > _y) *)
    forward_if.
    repeat forward.
    Exists NN (nextp !!! p2) (nextp !!! p2).
    entailer !.
    apply (H9 x). split. lia. auto. 
    unfold node, my_specific_tree_rep.
    rewrite -> if_false; auto.
    Exists x0 v0 p1 p2.
    entailer !.
    (* x = y *)
    forward.
    Exists F p p.
    unfold node, my_specific_tree_rep.
    rewrite -> if_false; auto.
    Exists x0 v0 p1 p2.
    entailer !.
    assert (x = x0). lia.
    subst x0.
    specialize (H8 x).
    specialize (H9 x).
    specialize (H10 x).
    apply H10 in H18.
    destruct H18.
    apply H8 in H18. lia.
    apply H9 in H18. lia.
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

Definition insertOp_spec :=
  DECLARE _insertOp
    WITH x: Z, stt: Z, v: val, p: val, tp: val, l: val, dl: val, next: list val, r: node_info,
                    g: gname, gv: globals
  PRE [ tptr (tptr t_struct_tree), tint, tptr tvoid, tint, tptr (struct_dlist)]
  PROP (repable_signed x; is_pointer_or_null v; is_pointer_or_null (Znth 0 next);
        is_pointer_or_null (Znth 1 next); key_in_range x r.1.2 = true ;
        length next = node_size)
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt); l)
  GLOBALS (gv)
  SEP (mem_mgr gv; field_at Ews (struct_dlist) [StructField _list] dl l *
                     data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl * 
                     (* (!!(p = r.1.1.1 /\ p = nullval)  && seplog.emp); *)
       data_at Ews (tptr t_struct_tree) tp p)
  POST[ tvoid ]
  ∃ (pnt : val),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv; data_at Ews (tptr t_struct_tree) pnt p;
       node_rep_R pnt r.1.2 (Some (Some (x, v, next))) g;
       field_at Ews struct_dlist (DOT _list) dl l;
       data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl).

Lemma length_equal_2 (x: Z) (v: val) (next : list val):
  length next = 2%nat ->
  Some (Some (x, v, next)) = Some (Some (x, v, [Znth 0 next; Znth 1 next])).
Proof.
  intros H_length.
  destruct next as [|a [|b tl]] eqn:Heq_next; try discriminate.
  inversion H_length; subst.
  unfold Znth; simpl.
  repeat f_equal. 
  by apply nil_length_inv. 
Qed.

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
     surely_malloc_spec; insertOp_spec (* ; traverse_spec; insert_spec; treebox_new_spec*) ]).
(* Proving insertOp satisfies spec *)
Lemma insertOp: semax_body Vprog Gprog f_insertOp insertOp_spec.
Proof.
  start_function.
  forward_call (t_struct_tree, gv).
  Intros new_node.
  forward.
  forward.
  forward.
  forward.
  entailer !.
  simpl in H4.
  by rewrite Zlength_correct H4.
  forward.
  forward.
  forward.
  entailer !.
  simpl in H4.
  by rewrite Zlength_correct H4.
  forward.
  forward.
  Exists new_node.
  assert_PROP (new_node <> nullval) by entailer !.
  unfold node_rep_R.
  unfold my_specific_tree_rep.
  rewrite if_false; auto.
  entailer !.
  Exists x v (Znth 0 next) (Znth 1 next).
  entailer !.
  by apply length_equal_2.
Qed.
