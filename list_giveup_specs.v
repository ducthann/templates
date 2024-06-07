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
Require Import tmpl.list_giveup. (* list_giveup.c *)
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
  Context (Hsize: node_size = 1%nat).
  
Definition struct_dlist := Tstruct _DList noattr.
Definition t_struct_node := Tstruct _node_t noattr.
Definition t_struct_nodeds := Tstruct _node noattr.

Definition fst_list : list (val * val * val * val) -> list val := map (fun '(x, _, _,_) => x).
Definition snd_list : list (val * val * val * val) -> list val := map (fun '(_, x, _,_) => x).
Definition thrd_frth_list: list (val * val * val * val) -> list (val * val) :=
  map (fun '(_, _, x, y) => (x, y)).
Definition fst_snd_list: list (val * val * val * val) -> list (val * val) :=
  map (fun '(x, y, _,_) => (x, y)).
(*getting p that points to min *)
Definition fst_thrd_list: list (val * val * val * val) -> list (val * val) :=
  map (fun '(x, _, y,_) => (x, y)).
(*getting p that points to max *)
Definition fst_frth_list: list (val * val * val * val) -> list (val * val) :=
  map (fun '(x, _, _, y) => (x, y)).

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

Definition insertOp_spec :=
  DECLARE _insertOp
    WITH x: Z, v: val, stt: Z, p: Node, tp: val, l: val, dl: val,
                  Ip : @flowintT _ K_multiset_ccm  _ _,
                    Cp : (gmap Key data_struct.Value),
                     (* pnext : gmap nat Node, *)
                      next: list Node,
                        gv: globals
  PRE [ tptr (tptr t_struct_nodeds), tint, tptr tvoid, tint, tptr (struct_dlist)]
  PROP (repable_signed x; is_pointer_or_null v; (*node_size = length ((gmap_to_node_list pnext)); *)
        length next = node_size;
        (* is_pointer_or_null (Znth 0 (gmap_to_node_list pnext)); *)
        is_pointer_or_null (Znth 0 next);
        tp = nullval)
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt); l)
  GLOBALS (gv)
  SEP (mem_mgr gv; node tp Ip Cp (list_to_gmap next);
       field_at Tsh (struct_dlist) (DOT _list) dl l;
       data_at Ews (tptr t_struct_nodeds) tp p;
                   (* field_at Ews (struct_dlist) [StructField _size] (Vptrofs (Ptrofs.repr 2%Z)) l ∗ *)
                   (* data_at Ews (tarray (tptr tvoid) (Zlength (gmap_to_node_list pnext) )) (gmap_to_node_list pnext) dl *)
       data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl
       )
  POST[ tvoid ]
  ∃ (pnt : Node),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv; node pnt Ip Cp (list_to_gmap next); node tp Ip Cp (list_to_gmap next);
       field_at Tsh struct_dlist (DOT _list) dl l;
       data_at Ews (tptr t_struct_nodeds) pnt p;
       (*data_at Ews (tarray (tptr tvoid) (Zlength (gmap_to_node_list pnext))) (gmap_to_node_list pnext) dl*)
     data_at Ews (tarray (tptr tvoid) (Zlength next)) next dl  

  ).


Definition insertOp_giveup_spec :=
  DECLARE _insertOp_giveup
    WITH x: Z, v: val, stt: Z, p: Node, tp: val, min: Z, max: Z,
                  Ip : @flowintT _ K_multiset_ccm  _ _,
                    Cp : (gmap Key data_struct.Value),
                      next : list Node,
                        sh: share, gv: globals
  PRE [ tptr t_struct_node, tint, tptr tvoid, tint ]
  PROP (repable_signed min; repable_signed max; repable_signed x;
        is_pointer_or_null v; is_pointer_or_null v; is_pointer_or_null tp)
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt))
  GLOBALS (gv)
  SEP (mem_mgr gv;
       match (Int.eq (Int.repr stt) (Int.repr 2%Z)) with
        | true => ⌜tp = nullval⌝ ∧ emp
        | false => ⌜tp <> nullval⌝ ∧ emp 
       end;
       field_at Ews t_struct_node (DOT _t) tp p;
       field_at Ews t_struct_node (DOT _min) (vint min) p;
       field_at Ews t_struct_node (DOT _max) (vint max) p;
       node tp Ip Cp (list_to_gmap next))
  POST[ tvoid ] (* triple (pointer, lock, min, max) *)
  ∃ (pnt : val) (trl : list (val * val * val * val)) (ptl : list val),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv;
       (match (Int.eq (Int.repr stt) (Int.repr 2%Z)) with
        | true => ⌜tp = nullval⌝ ∧ emp
        | _    =>  ⌜tp <> nullval⌝ ∧ emp 
        end)).

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;  
                             insertOp_giveup_spec; insertOp_spec;
                             surely_malloc_spec ]).

Lemma insertOp_bst: semax_body Vprog Gprog f_insertOp_giveup insertOp_giveup_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_call (tarray (tptr tvoid) 1, gv). simpl. computable.
  Intros lst.
  forward.
  forward_call (t_struct_node, gv).
  Intros p1.
  forward.
  forward.
  forward_call (gv).
  Intros lock.
  forward.
  forward.
  forward.
  forward_call release_nonatomic (lock).
  forward_if(PROP ( )
     LOCAL (temp _t'20 (Znth 0 (upd_Znth 0 (default_val (tarray (tptr tvoid) 1)) p1)); 
     temp _t'19 lst; temp _l lock; temp _t'21 lst; temp _t'2 p1; temp _t'1 lst;
     temp _t'22 (Vlong (Int64.repr (Int.signed (Int.repr 1))));
     lvar _dlist (Tstruct _DList noattr) v_dlist; gvars gv; temp _p p; temp _x (vint x); 
     temp _value v; temp _status (vint stt))
     SEP (atomic_int_at Ews (vint 0) lock; mem_mgr gv; malloc_token Ews t_struct_node p1;
     data_at Ews t_struct_node ((default_val t_struct_node).1, (lock, (default_val t_struct_node).2.2))
       p1; malloc_token Ews (tarray (tptr tvoid) 1) lst;
     data_at Ews (tarray (tptr tvoid) 1) (upd_Znth 0 (default_val (tarray (tptr tvoid) 1)) p1) lst;
     data_at Tsh (Tstruct _DList noattr) (lst, Vlong (Int64.repr (Int.signed (Int.repr 1)))) v_dlist;
     if Int.eq (Int.repr stt) (Int.repr 2) then ⌜tp = nullval⌝ ∧ emp else ⌜tp ≠ nullval⌝ ∧ emp;
     field_at Ews t_struct_node (DOT _t) tp p; field_at Ews t_struct_node (DOT _min) (vint min) p;
     field_at Ews t_struct_node (DOT _max) (vint max) p; node tp Ip Cp (list_to_gmap [p1]))).
  - rewrite H7; simpl.
    Intros.
    forward. forward. forward.
    assert_PROP(field_compatible t_struct_node [] p1) by entailer!.
    assert_PROP(field_compatible t_struct_node (DOT _t) p) by entailer !.
    assert (field_address t_struct_node (DOT _t) p  = p) as I.
    rewrite ->  field_compatible_field_address, isptr_offset_val_zero; auto.
    
    (* call insertOp *)
    forward_call(x, v, stt, (field_address t_struct_node [StructField _t] p), tp, v_dlist, lst, Ip, Cp, [p1] , gv).
    {
      subst tp.
      entailer !. simpl.
      rewrite I. rewrite isptr_offset_val_zero.
      replace (vint stt) with (vint 2); f_equal; auto. auto.
    }
    unfold_data_at (data_at _ _ _ v_dlist).
    cancel.
    entailer !.
    assert (list_to_gmap next = list_to_gmap [p1]). admit.
    rewrite H8.
    entailer !.
    Intros pnt.
    admit.


  - rewrite Int.eq_false; auto.
    Intros.
    forward. forward. forward. forward.
    forward. forward. forward. forward.
    forward. forward. forward. forward.
    assert_PROP (field_compatible t_struct_node [] p1) by entailer!.
    (* call insertOp *)
    assert_PROP(field_compatible t_struct_node (DOT _t) p) by entailer !.
    assert (field_address t_struct_node (DOT _t) p  = p) as I.
    rewrite -> field_compatible_field_address, isptr_offset_val_zero; auto.
    (* call insertOp *)
    forward_call(x, v, stt, (field_address t_struct_node [StructField _t] p), nullval, v_dlist, lst, Ip, Cp, [p1] , gv).
    unfold_data_at (data_at _ _ _ v_dlist).
    entailer !.
    change (Vlong (Int64.repr 0)) with nullval.
    assert (list_to_gmap next = list_to_gmap [p1]). admit.
    rewrite H23.
    cancel.
    unfold_data_at (data_at _ _ _ v_dlist).
    
    
    {
      subst tp.
      entailer !. simpl.
      rewrite I. rewrite isptr_offset_val_zero.
      replace (vint stt) with (vint 2); f_equal; auto. auto.
    }

    
    forward. forward. forward. forward. forward. forward. entailer !. list_solve.
    forward. forward. forward. entailer !. list_solve.
    forward.
    rewrite H5.
    entailer !.
    simpl.
    Exists pnt .
    cancel.
    unfold_data_at (data_at _ _ _ v_dlist).
    entailer !.
    rewrite ! node_null.
    entailer !.
  - rewrite Int.eq_false; auto.
    Intros.
    forward. forward. forward. forward.
    forward. forward. forward. forward.
    forward. forward. forward. forward.
    assert_PROP (field_compatible t_struct_node [] p1) by entailer!.
    (* call insertOp *)
    assert_PROP(field_compatible t_struct_node (DOT _t) p) by entailer !.
    assert (field_address t_struct_node (DOT _t) p  = p) as I.
    rewrite -> field_compatible_field_address, isptr_offset_val_zero; auto.
    forward_call(x, stt, v, (field_address t_struct_node [StructField _t] p), v_dlist, lst, [p1] ,
                  g, gv).
    unfold_data_at (data_at _ _ _ v_dlist).
    entailer !.
    change (Vlong (Int64.repr 0)) with nullval.
    cancel. 
    rewrite Int.eq_false; auto.
    Intros pnt.
    Exists pnt.
    entailer !.
    unfold_data_at (data_at _ _ _ v_dlist).
    simpl.
    entailer !.
  - forward.
    assert (field_address t_struct_node (DOT _t) p = p) as I.
    {
      clear -H5.
      rewrite ->  field_compatible_field_address, isptr_offset_val_zero; auto.
      (* isptr p ; field_compatible t_struct_node (DOT _t) p *)
    }
    destruct (Int.eq (Int.repr stt) (Int.repr 2)).
    + subst. 
      Intros pnt.
      assert_PROP (pnt <> nullval). entailer !.
      forward_call (tarray (tptr tvoid) 1 , lst, gv).
      {
        assert_PROP (lst <> nullval) by entailer !.
        rewrite if_false; auto. cancel.
      }
      Exists pnt.
      unfold post_insert_giveup1.
      Exists [(p1, lock, vint x, (vint (Int.max_signed)))] [nullval].
      unfold_data_at (data_at _ _ _ v_dlist).
      entailer.
      simpl.
      unfold_data_at (data_at _ _ _ p1).
      unfold_data_at(data_at_ Tsh (Tstruct _DList noattr) v_dlist).
      entailer !.
    + Intros pnt.
      assert_PROP (pnt <> nullval). entailer !.
      forward_call (tarray (tptr tvoid) 1 , lst, gv).
      {
        assert_PROP (lst <> nullval) by entailer !.
        rewrite if_false; auto. cancel.
      }
      Exists pnt.
      unfold post_insert_giveup2.
      Exists [(p1, lock, vint x, (vint max))] [tp].
      unfold_data_at (data_at _ _ _ v_dlist).
      entailer.
      simpl.
      unfold_data_at (data_at _ _ _ p1).
      unfold_data_at(data_at_ Tsh (Tstruct _DList noattr) v_dlist).
      entailer !.
Qed.

End give_up.

