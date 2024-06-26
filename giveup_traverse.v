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
Require Import tmpl.keyset_ra_ora.
Require Import tmpl.puretree.
Require Import tmpl.data_struct.
Require Import tmpl.giveup_lib.
Require Import tmpl.flows_ora.

(*#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
*)
#[global] Instance gmap_inhabited V : Inhabitant (gmap key V).
Proof. unfold Inhabitant; apply empty. Defined.

#[global] Instance number_inhabited: Inhabitant number.
Proof. unfold Inhabitant; apply Pos_Infinity. Defined.

Section give_up_traverse.
  Context `{N: NodeRep } `{EqDecision K} `{Countable K}.
  Context `{!cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr),
            !flowintG Σ, !nodemapG Σ, !keymapG Σ, !keysetG Σ,
        inG Σ (frac_authR (agreeR per_node))}.



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


(* t_struct_node represents for the generic-struct rather specific-data-structure *)
(* Spec of inrange function *)
(*
(k: K) (In : multiset_flowint_ur K) (C: gset K)
 *)

(*
node_rep γ_f γ_k (n : Node) (rg : (number * number))
    (In : @multiset_flowint_ur Key _ _ ) Cn
 *)

Definition inRange_spec :=
  DECLARE _inRange
    WITH x: Z, pn: val, lock: val, n: Node, min: Z, max : Z,  In : flowintT,
                Cn : (gmap Key data_struct.Value), nextp : gmap nat Node, sh: share, gv: globals
  PRE [ tptr t_struct_node, tint]
          PROP (writable_share sh; repable_signed min; repable_signed max; repable_signed x;
          (∀ k, and (Z.lt min k) (Z.lt k max) -> in_inset _ _ _ k In n))
          PARAMS (pn; Vint (Int.repr x)) GLOBALS (gv)
          SEP (node n In Cn nextp;
              field_at sh (t_struct_node) [StructField _min] (Vint (Int.repr min)) pn;
              field_at sh (t_struct_node) [StructField _max] (Vint (Int.repr max)) pn)
  POST [ tint ]
  ∃ (succ: bool),
         PROP (match succ with
               | true => and (Z.lt min x) (Z.lt x max) ∧ (succ -> in_inset _ _ _ x In n)
               | false => or (Z.le x min) (Z.le max x) /\ (succ -> in_inset _ _ _ x In n)
               end)
        LOCAL (temp ret_temp (Vint (if succ then Int.one else Int.zero)))
        SEP (node n In Cn nextp; 
             field_at sh (t_struct_node) [StructField _min] (Vint (Int.repr min)) pn;
              field_at sh (t_struct_node) [StructField _max] (Vint (Int.repr max)) pn).

(*
Definition post_traverse (b: val) x (g: gname) (e: enum) (p: val) (sh: share) (g_in: gname) (n: node_info):=
  ⌜ key_in_range x (n.1).2 = true ∧
      repable_signed (number2Z (n.1).2.1) /\ repable_signed (number2Z (n.1).2.2) /\
      is_pointer_or_null (((n.1).1).2) /\
      (if Val.eq (enums e) (enums NN)
       then n.2 = Some None /\ ((n.1).1).1 = nullval
                          else ((n.1).1).1 <> nullval)
                        (* (match (pt.1 : enum) with
                         | NN => pt.2.2.2.2.2 = Some None /\ ((((pt.2.2.2).2).1).1).1 = nullval
                         | NF | F =>  ((((pt.2.2.2).2).1).1).1 <> nullval
                        (* | NF => ((((pt.2.2.2).2).1).1).1 <> nullval *)
                          end) *)  ) && seplog.emp * 
  data_at Ews t_struct_pn (p, p) b * in_tree g g_in p ((n.1).1).2 * node_lock_inv_pred g p g_in n.
*)

(* Proving inrange spec *)
Lemma body_inrange: semax_body Vprog Gprog f_inRange inRange_spec.
Proof.
  start_function.
  forward.
  forward_if (PROP ()
              LOCAL (temp _t'1 (if andb (Z.ltb min x) (Z.ltb x max)
                                then Val.of_bool true
                                else Val.of_bool false);
                     temp _t'2 (vint min); gvars gv; temp _p pn; temp _x (vint x))
     SEP (node n In Cn nextp; field_at sh t_struct_node (DOT _min) (vint min) pn;
     field_at sh t_struct_node (DOT _max) (vint max) pn)).
  - repeat forward. entailer !.
     destruct (Z.ltb_spec min x), (Z.ltb_spec x max); try rep_lia.
    + unfold Val.of_bool, Int.lt.
      autorewrite with norm; auto.
    + unfold Val.of_bool, Int.lt.
      apply Z.le_ge in H11.
      destruct (zlt x max); [try easy | auto].
  - forward.
    destruct (Z.ltb_spec min x); try rep_lia.
    entailer !.
  - forward_if. forward.
    + assert (((Z.ltb min x) && (Z.ltb x max))%bool = true) as Hx.
      { destruct((Z.ltb min x) && (Z.ltb x max))%bool; easy. }
      Exists true. entailer !.
      specialize (H4 x).
      apply andb_prop in Hx.
      destruct Hx as (Hx & Hy).
      apply Z.ltb_lt in Hx, Hy.
      assert ((min < x < max)%Z) as Hxy. lia.
      by apply H4 in Hxy.
    + assert (((Z.ltb min x) && (Z.ltb x max))%bool = false) as Hy.
      { destruct ((Z.ltb min x) && (Z.ltb x max))%bool; easy. }
      forward.
      Exists false.
      entailer !.
Qed.
(*
 CSS γ_I γ_f γ_g γ_k r C: mpred := ∃ I, CSSi γ_I γ_f γ_g γ_k r C I.

 *)

Check t_struct_pn.
Check @CSS.

Program Definition traverse_spec :=
  DECLARE _traverse
          ATOMIC TYPE (ConstType
                       (val * val * val * Node * Z  * val * (gmap Key data_struct.Value) * gname * gname * gname * gname * globals))
          OBJ C INVS empty
  WITH b, n, lock, r, x, v, C, γ_I, γ_f, γ_g, γ_k, gv
  PRE [ tptr t_struct_pn, tint]
  PROP (and (Z.le (Int.min_signed) x) (Z.le x (Int.max_signed)); is_pointer_or_null v;
        is_pointer_or_null lock; is_pointer_or_null n)
  PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
  SEP  (mem_mgr gv; 
        inFP γ_f n lock r;
        ∃ (p: val), data_at Ews (t_struct_pn) (p, n) b ) | (CSS γ_I γ_f γ_g γ_k r C)
  POST [ tint ]
  ∃ v : Z,
  PROP ()
  LOCAL (temp ret_temp (vint v))
  SEP (mem_mgr gv (* !!( key_in_range x (((pt.2.2.2).2).1).2 = true ∧
                         repable_signed (number2Z (((pt.2.2.2).2).1).2.1) ∧
                         repable_signed (number2Z (((pt.2.2.2).2).1).2.2) /\
                         is_pointer_or_null ((((pt.2.2.2).2).1).1).2
                       /\ (if Val.eq (enums pt.1) (enums NN) then
                            pt.2.2.2.2.2 = Some None /\ ((((pt.2.2.2).2).1).1).1 = nullval
                          else ((((pt.2.2.2).2).1).1).1 <> nullval)
                        (* (match (pt.1 : enum) with
                         | NN => pt.2.2.2.2.2 = Some None /\ ((((pt.2.2.2).2).1).1).1 = nullval
                         | NF | F =>  ((((pt.2.2.2).2).1).1).1 <> nullval
                        (* | NF => ((((pt.2.2.2).2).1).1).1 <> nullval *)
                          end) *)  ) && seplog.emp; *)
      (*  data_at Ews t_struct_pn (pt.2.1, pt.2.1) b  ;
        in_tree g pt.2.2.2.1 pt.2.1 ((((pt.2.2.2).2).1).1).2  ;
       node_lock_inv_pred g pt.2.1 pt.2.2.2.1 (pt.2.2.2).2 *) )| (CSS γ_I γ_f γ_g γ_k r C).

(*
Program Definition traverse_spec :=
  DECLARE _traverse
          ATOMIC TYPE (rmaps.ConstType
                       (val * val * val * Z  * val * globals * gname * gname))
          OBJ M INVS ∅
  WITH b, n, lock, x, v, gv, g, g_root
  PRE [ tptr t_struct_pn, tint]
  PROP (and (Z.le (Int.min_signed) x) (Z.le x (Int.max_signed)); is_pointer_or_null v)
  PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
  SEP  (mem_mgr gv; 
        in_tree g g_root n lock;
        !!(is_pointer_or_null lock /\ is_pointer_or_null n) && seplog.emp;
        EX (p: val), data_at Ews (t_struct_pn) (p, n) b ) | (CSS g g_root M)
  POST [ tint ]
  EX  pt: enum * (val * (share * (gname * node_info ))) %type,
  PROP ()
  LOCAL (temp ret_temp (enums pt.1))
  SEP (mem_mgr gv; post_traverse b x g pt.1 pt.2.1 pt.2.2.1 pt.2.2.2.1 (pt.2.2.2).2)| (CSS g g_root M).
*)

(*
Lemma node_rep_saturate_local r p g g_current:
  node_rep p g g_current r |-- !! is_pointer_or_null p.
Proof. unfold node_rep; entailer !. Qed.
Local Hint Resolve node_rep_saturate_local: saturate_local.

Lemma node_rep_valid_pointer t g g_current p: node_rep p g g_current t |-- valid_pointer p.
Proof.
  unfold node_rep.
  Intros.
  iIntros "(((((H & ?) & ?) & ?) & ?) & ?)".
  iPoseProof (field_at_valid_ptr0 with "H") as "H"; try auto; simpl; try lia.
  iVST. entailer !.
Qed.
Local Hint Resolve node_rep_valid_pointer : valid_pointer.
*)
(*
(* Spec of findnext function *)
(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
Definition findnext_spec :=
  DECLARE _findNext
  WITH x: Z, p: val, n: val, n_pt : val, r : node_info, g: gname, sh: share, gv: globals
  PRE [ tptr tvoid, tptr (tptr tvoid), tint ]
          PROP (writable_share sh(*; is_pointer_or_null pa; is_pointer_or_null pb*) )
          PARAMS (p; n; Vint (Int.repr x)) GLOBALS (gv)
          SEP ((* data_at sh (t_struct_tree_t) (p, n) b *)
            node_rep_R r.1.1.1 r.1.2 r.2 g ;
               field_at sh (t_struct_node) [StructField _t] r.1.1.1 p;
               data_at sh (tptr t_struct_node) n_pt n)
  POST [ tint ]
  EX (stt: enum), EX (n' next : val),
         PROP (match stt with
               | F | NF => (n' = p)
               | NN => (n' = next)
               end)
        LOCAL (temp ret_temp (enums stt))
        SEP (match stt with
               | F | NF => data_at sh (tptr t_struct_node) n_pt n
               | NN => !!(n' ∈ extract_node_pn r) && data_at sh (tptr t_struct_node) next n
             end *
               node_rep_R r.1.1.1 r.1.2 r.2 g *
               field_at sh (t_struct_node) [StructField _t] r.1.1.1 p).
*)

(* Spec of findnext function *)
(* FOUND = 0, NOTFOUND = 1, NULLNEXT = 2 (NULLNEXT = NULL || NEXT ) *)
(*
Definition findnext_spec :=
  DECLARE _findNext
  WITH x: Z, p: val, n: val, n_pt : val, r: node_info,
                g: gname, sh: share, gv: globals
  PRE [ tptr t_struct_nodeds, tptr (tptr tvoid), tint ]
          PROP (writable_share sh(*; is_pointer_or_null pa; is_pointer_or_null pb*) )
          PARAMS (p; n; Vint (Int.repr x)) GLOBALS (gv)
          SEP (node_rep_R r.1.1.1 r.1.2 r.2 g * (!!(p = r.1.1.1 /\ p <> nullval) && seplog.emp)  *
               (* field_at sh (t_struct_tree) [StructField _t] r.1.1.1 p; *)
               
               data_at sh (tptr t_struct_node) n_pt n)
  POST [ tint ]
  EX (stt: enum), EX (n' next : val),
         PROP (match stt with
               | F | NF => (n' = p)
               | NN => (n' = next)
               end)
        LOCAL (temp ret_temp (enums stt))
        SEP (match stt with
               | F | NF => data_at sh (tptr t_struct_node) n_pt n
               | NN => !!(n' ∈ extract_node_pn r) && data_at sh (tptr t_struct_node) next n
             end *
               node_rep_R r.1.1.1 r.1.2 r.2 g) .
*)


(* traverse invariants *)
Definition traverse_inv (b: val) (pn lock: val) (r: Node) (sh: share) (x : Z) (v: val)  gv
                        (γ_f : gname) AS : environ -> mpred :=
  (∃ (pnN p lockN: val) (n: Node),
            PROP ()
            LOCAL (temp _p pn; temp _status (vint 2); temp _pn__2 b; temp _x (vint x);
                   (* temp _value v; *) gvars gv)
            SEP (data_at sh (t_struct_pn) (p, pnN) b;
                 inFP γ_f pnN lockN n; inFP γ_f pn lock r; AS; mem_mgr gv ∧
                 ⌜is_pointer_or_null lockN⌝))%assert.


(*
node_lock_inv_pred γ_I γ_k γ_g pn lock (node : Node) (In : @multiset_flowint_ur Key _ _ ) Cn


Definition traverse_inv_1 (b p: val) (sh: share) (x : Z) (g_root g_in g: gname) (r: node_info) :=
  data_at sh (t_struct_pn) (p, p) b * in_tree g g_in p r.1.1.2 *
  node_lock_inv_pred γ_I γ_k γ_g pn lock (node : Node) (In : @multiset_flowint_ur Key _ _ ) Cn*
  (!!(key_in_range x r.1.2 = true (* /\ r.2 = Some None *) /\
      repable_signed (number2Z r.1.2.1) ∧
      repable_signed (number2Z r.1.2.2) /\ is_pointer_or_null r.1.1.2) && seplog.emp).

Definition traverse_inv_2 (b p: val) (sh : share) (x : Z) (g_root g_in g: gname) (r: node_info) :=
  data_at sh (t_struct_pn) (p, p) b *
  in_tree g g_in p r.1.1.2 *
  (* node_lock_inv_pred_1 g p g_in r x * *) (* modify it later*)
  (!!(repable_signed (number2Z r.1.2.1) ∧
      repable_signed (number2Z r.1.2.2) /\ is_pointer_or_null r.1.1.2) && seplog.emp).
*)
(*
Definition insertOp_bst_spec :=
  DECLARE _insertOp_bst
    WITH x: Z, stt: Z,  v: val, p: val, tp: val, min: Z, max: Z, gv: globals
  PRE [ tptr t_struct_node, tint, tptr tvoid, tint ]
  PROP (repable_signed min; repable_signed max; repable_signed x;
        is_pointer_or_null v )
  PARAMS (p; Vint (Int.repr x); v; Vint (Int.repr stt))
  GLOBALS (gv)
  SEP (mem_mgr gv;
       field_at Ews t_struct_node (DOT _t) tp p;
       field_at Ews t_struct_node (DOT _min) (vint min) p;
       field_at Ews t_struct_node (DOT _max) (vint max) p)
  POST[ tvoid ]
  EX (pnt : val) (pnl: list val) (lkl: list val),
  PROP (pnt <> nullval)
  LOCAL ()
  SEP (mem_mgr gv;
       (* data_at sh t_struct_pn (p, p) b; *)
       field_at Ews t_struct_node (DOT _t) pnt p;
       malloc_token Ews t_struct_node pnt;
       iter_sepcon (fun pn => malloc_token Ews t_struct_node pn) pnl;
       iter_sepcon (fun lk => atomic_int_at Ews (vint 0) lk) lkl;
(*
       data_at Ews t_struct_tree (vint x, (v, (p1', p2'))) pnt;
       data_at Ews t_struct_tree_t (Vlong (Int64.repr 0), (lock2, (vint x, vint max))) p2';
       data_at Ews t_struct_tree_t (Vlong (Int64.repr 0), (lock1, (vint min, vint x))) p1';
*)
       field_at Ews t_struct_node (DOT _min) (vint min) p;
       field_at Ews t_struct_node (DOT _max) (vint max) p).
*)

Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec (*; findnext_spec *) ; 
                             inRange_spec; traverse_spec; surely_malloc_spec ]).



Lemma node_rep_R_saturate_local: forall  n I_n C next,
  node n I_n C next -∗ ⌜is_pointer_or_null n⌝.
Proof. apply node_rep_R_pointer_null. Qed.
Local Hint Resolve node_rep_R_saturate_local: saturate_local.

Lemma node_rep_R_valid_pointer: forall  n I_n C next,
  node n I_n C next -∗ valid_pointer n.
Proof. apply node_rep_R_valid_pointer. Qed.
Local Hint Resolve node_rep_R_valid_pointer : valid_pointer.

(*
Lemma insertOp_bst: semax_body Vprog Gprog f_insertOp_bst insertOp_bst_spec.
Proof.
  start_function.
  forward_call (t_struct_node, gv).
  Intros p1.
  forward_call (t_struct_node, gv).
  Intros p2.
  forward.
  assert_PROP (field_compatible t_struct_node [] p1) by entailer!.
  assert_PROP (field_compatible t_struct_node [] p2) by entailer!.
  forward. 
  forward_call (gv).
  Intros lock1.
  forward.
  sep_apply atomic_int_isptr.
  Intros.
  forward_call release_nonatomic (lock1).
  forward_call (gv).
  Intros lock2.
  forward.
  Intros.
  forward_call release_nonatomic (lock2).
  (* make lock invariant *)
  Admitted.
*)

(* PROVING traverse spec *)
Lemma traverse: semax_body Vprog Gprog f_traverse traverse_spec.
Proof.
  start_function.
  Intros p.
  forward.
  forward.
  set (AS := atomic_shift _ _ _ _ _ ).
  (* New pt: bool * (val * (share * (gname * node_info))) *)
  Check traverse_inv.
  forward_loop (traverse_inv b n lock r Ews x v gv γ_f AS)
    break: (*consider to remove gsh *)
    (∃ (flag: enum) (q : val) (gsh: share) (g_in: gname),
     PROP() LOCAL(temp _status (enums flag))
     SEP((match flag with
            | F => (* ((traverse_inv_2 b q Ews x g_root g_in g r) *
                      (!!(r.1.1.1 <> nullval) && seplog.emp)) *) ⌜True⌝
            | NF => (* ((traverse_inv_2 b q Ews x g_root g_in g r) *
                      (!!(r.1.1.1 <> nullval) && seplog.emp)) *) ⌜True⌝
            | NN => (* ((traverse_inv_1 b q Ews x g_root g_in g r) *
                      (!!( r.1.1.1 = nullval) && seplog.emp)) *) ⌜True⌝
          end) ∗ Q (1%Z) ∗ mem_mgr gv)).
  - unfold traverse_inv.
    Exists n p lock r.
    rewrite {1} (bi.persistent_sep_dup (inFP γ_f n lock r)).
    entailer !.
  - (*go deeply into loop*) (*pre-condition*)
    unfold traverse_inv.
    Intros pn pp lockN pnN.
    gather_SEP AS (inFP γ_f pn lockN pnN).
    viewshift_SEP 0 (AS ∗ (inFP γ_f pn lockN pnN) ∗
                          (∃ lsh, ⌜readable_share lsh⌝ ∧
                                     field_at lsh t_struct_node (DOT _lock) lockN pn)).
    {
      go_lowerx.
      iIntros "((AU & #H) & _)".
      iApply (lock_alloc with "[$H $AU]").
    }
    Intros lsh.
    forward.
    forward.
    rewrite {1} (bi.persistent_sep_dup (inFP γ_f pn lockN pnN)).
    (* acquire(pn->n->lock); *)
    Check node_lock_inv_pred.
    forward_call acquire_inv_atomic (lockN,
        AS  ∗ (∃ In Cn, node_lock_inv_pred γ_I γ_g γ_k pn lockN pnN In Cn)).
    {
      unfold rev_curry, tcurry; simpl.
      rewrite - assoc assoc; apply bi.sep_mono; [|cancel].
      unfold atomic_shift; iIntros "(AU & #HinFP)"; iAuIntro; unfold atomic_acc; simpl.
      iMod "AU" as (m) "[Hm HClose]".
      iModIntro.
      simpl.
      iPoseProof (in_node_inv  with "[$HinFP $Hm]") as "InvLock".
      iDestruct "InvLock" as "(InvLock & _)".
      iDestruct "InvLock" as (In Cn) "(H1 & H2)".
      iExists (node_lock_inv_pred γ_I γ_g γ_k pn lockN pnN In Cn). iFrame "H1".
      iSplit.
      - iIntros "H1".
        iSpecialize ("H2" with "H1").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2"); auto.
      - iIntros (m') "((H1 & H1') & _)".
        iSpecialize ("H2" with "H1").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2").
        iMod ("HClose").
        iFrame "HClose".
        iModIntro.
        iExists _, _. iFrame.
    }
    Intros IC. simpl.
    forward.
    forward.
    forward.
    unfold node_lock_inv_pred, node_rep.
    Intros rg next.
    destruct IC as (I1 & C1).
    simpl.
    (* inrange function *)
    forward_call(x, pn, lockN, pnN, number2Z (min_of rg), number2Z (max_of rg), I1, C1, next, Ews, gv).
    Intros succ1.
    destruct succ1.
    + forward_if.
      forward.
      forward.
      (*tp = nullval --- pn->p->t == NULL; break*)
      forward_if.
      entailer !.
      Search denote_tc_test_eq .
      
      admit.
      (* push back lock into invariant *)
      gather_SEP AS (inFP γ_f pn lockN pnN) (field_at lsh t_struct_node (DOT _lock) _ _).
      viewshift_SEP 0 (AS ∗ inFP γ_f pn lockN pnN).
      {
        go_lowerx.
        iIntros "((AU & (#HinFP & H1)) & _)".
        iMod "AU" as (m) "[Hm HClose]".
        iPoseProof (in_node_inv with "[$HinFP $Hm]") as "InvLock".
        iDestruct "InvLock" as "(_ & InvLock)".
        simpl.
        iDestruct "InvLock" as (R) "(H1' & H2')".
        unfold ltree.
        iDestruct "H1'" as (lsh1) "(%Hf & (H12 & H13))".
        iAssert(∃ lsh0 : share,
            ⌜field_compatible t_struct_node [] pn ∧ readable_share lsh0⌝
            ∧ @field_at _ _ _ CompSpecs lsh0 t_struct_node (DOT _lock) lockN pn ∗
            inv_for_lock lockN R) with "[H1 H12 H13]" as "H1'".
        {
          destruct Hf as (Hf & Hrs).
          iPoseProof (lock_join with "[$H1 $H12]") as "H1". done.
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _. iFrame. iPureIntro. done.
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod ("HClose"). by iFrame "HinFP".
      }
      Intros.
      forward.
      forward.
      
      


      


            EX lsh0 : share,
           !! (field_compatible t_struct_node [] pn ∧ readable_share lsh0 ) &&
           (@field_at CompSpecs lsh0 t_struct_node (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
        unfold ltree.
        iDestruct "H1'" as (lsh1) "(%H12 & (H12 & H13))".








        

        
      {
        

        
      forward.
      forward.
      iIntros "H".
      Search denote_tc_test_eq .
      unfold VST.veric.expr2.denote_tc_test_eq.
      destruct IC.
      simpl.
      forward.
    + forward_if.
      forward.
      forward.
      
      forward.
      unfold field_at.
      forward.
      (*tp = nullval --- pn->p->t == NULL; break*)
      forward_if.
      (* prove r.1.1.2 = lock_in *)
      gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
      assert_PROP (r.1.1.2 = lock_in) as Hlk.
      { sep_apply in_tree_equiv; entailer !. }
      Intros.
      rewrite Hlk.
      (* push back lock into invariant *)
      gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
      viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
      {
        go_lower.
        iIntros "((AU & #H) & H1)".
        iMod "AU" as (m) "[Hm HClose]".
        iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
        iDestruct "InvLock" as "(_ & InvLock)".
        iDestruct "InvLock" as (R) "[H1' H2']".
        unfold ltree.
        iDestruct "H1'" as (lsh1) "(%H12 & (H12 & H13))".
        iAssert(EX lsh0 : share,
           !! (field_compatible t_struct_node [] pn ∧ readable_share lsh0 ) &&
           (@field_at CompSpecs lsh0 t_struct_node (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
          destruct H12 as (Hf & Hrs).
          iPoseProof (lock_join with "[H1 H12]") as "H1".
          { iSplitL "H1"; iFrame; iPureIntro; auto. }
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _. iFrame; iPureIntro; repeat (split; auto).
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod "HClose". by iFrame.
      }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!(y = (NN, (pn, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (NN, (pn, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        iModIntro. iExists _.
        by iFrame "Hm".
      }
      (*proving it satisfies with the post condition of traverse *)
      Intros y.
      forward.
      forward.
      Exists NN pn Ews g_in r.
      unfold traverse_inv_1.
      unfold node_lock_inv_pred, node_rep.
      entailer !.
      destruct (r.1.2).
      eapply key_range; auto.
      by iIntros "(H & _)". 
      forward.
      assert_PROP(field_compatible t_struct_pn (DOT _n) b). entailer !.
      forward.
      (* findNext *)
      forward_call(x, r.1.1.1, (field_address t_struct_pn [StructField _n] b),
                   pn, r, g, Ews, gv).
      { unfold_data_at (data_at Ews t_struct_pn _ b). cancel. entailer !. }
      {
        Intros succ.
        (* assert_PROP(r.1.1.1 <> nullval) by entailer !. *)
        destruct succ.1.1; last first.
        Intros. 
        * (* NN => succ.1.2 = succ.2  *)
          (* not found and find the next point *)
          forward.
          forward_if.
          easy. (* contradiction *)
          forward_if.
          easy. (* contradiction *)
          forward.
          gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
          assert_PROP (r.1.1.2 = lock_in) as Hlk.
          { sep_apply in_tree_equiv; entailer !. }
          rewrite Hlk.
          Intros.
          forward.
          (* push back lock into invariant *)
          gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
          viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
          { go_lower.
            apply push_lock_back; auto.  }
          (* make in_tree of next node : in_tree g succ.2 pnext lknext *)
          Intros.
          gather_SEP AS (in_tree g g_in pn lock_in) (node_rep_R r.1.1.1 r.1.2 r.2 g)
                        (field_at _ _ _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (malloc_token Ews t_struct_node pn) (my_half g_in Tsh r).
          viewshift_SEP 0 (EX g_in1 lock1, AS * (node_lock_inv_pred g pn g_in r ) *
                                           (in_tree g g_in1 succ.2 lock1)).
          {
            go_lower.
            iIntros "(((((((AU & #H) & HNode) & H2) & H3) & H4) & H5) & H6)".
            iMod "AU" as (m) "[Hm HClose]".
            iPoseProof (ghost_update_step g g_in g_root pn succ.1.2 lock_in m r
                         with "[$H $Hm $HNode $H2 $H3 $H4 $H5 $H6]")
              as (g_in1 lock1) "((Inv & H1) & H2)".
            { rewrite <- Hlk. iFrame "H". done. }
            iExists g_in1, lock1.
            iSpecialize ("HClose" with "H1").
            rewrite H11.
            by iFrame "Inv H2".
          }
          (*Now we have in_tree g succ.2 pnext lknext *)
          Intros gnext lknext.
          (* _release(_t'8);) *)
          forward_call release_inv (lock_in, node_lock_inv_pred g pn g_in r, AS).
          {
            lock_props.
            iIntros "(((((((HAS & H1) & H2) & H3) & H4) & H5) & H6) & H7)".
            iCombine "HAS H1 H3 H2 H4 H5 H6 H7" as "Hnode_inv_pred".
            iVST.
            rewrite <- H11.
            rewrite <- 2sepcon_assoc; rewrite <- 2sepcon_comm.
            apply sepcon_derives; [| cancel_frame].
            unfold atomic_shift;
              iIntros "((AU & H1) & #H2)";

              iAuIntro; unfold atomic_acc; simpl.
            iMod "AU" as (m) "[Hm HClose]".
            iModIntro.
            iExists tt.
            iPoseProof (in_tree_inv' g g_in g_root pn (r.1.1.2) m r
                         with "[H2 H1 $Hm]") as "(HI1 & HI2)".
            { rewrite Hlk. iFrame "H1 H2". }
            iDestruct "HI1" as "(HI1' & HI1)".
            rewrite Hlk.
            iFrame "HI1' HI1".
            iSplit.
            {
              iIntros "(Hnode_Iinv & InvLock)".
              iSpecialize ("HI2" with "InvLock").
              iDestruct "HClose" as "[HClose _]".
              iFrame "Hnode_Iinv".
              iSpecialize ("HClose" with "HI2").
              iFrame.
            }
            iIntros (_) "(H & _)".
            iSpecialize ("HI2" with "H").
            iDestruct "HClose" as "[HClose _]". 
            by iSpecialize ("HClose" with "HI2").
         }
         (* proving |--  traverse_inv *)
         unfold traverse_inv.
         Exists succ.1.2 pn gnext lknext.
         entailer !. admit. (* is_pointer_or_null lknext *)
         unfold_data_at (data_at Ews t_struct_pn _ b).
         cancel. 
       * (* NF case *)
         forward.
         forward_if.
         forward.
         easy.
         forward_if.
         gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
         assert_PROP (r.1.1.2 = lock_in) as Hlk.
         { sep_apply in_tree_equiv; entailer !. }
         Intros.
         rewrite Hlk.
         (* push back lock into invariant *)
         gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
         viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
         {
           go_lower.
           iIntros "((AU & #H) & H1)".
           iMod "AU" as (m) "[Hm HClose]".
           iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
           iDestruct "InvLock" as "(_ & InvLock)".
           iDestruct "InvLock" as (R) "[H1' H2']".
           unfold ltree.
           iDestruct "H1'" as (lsh1) "(%K12 & (H12 & H13))".
           iAssert(EX lsh0 : share,
                      !! (field_compatible t_struct_node [] pn ∧ readable_share lsh0 ) &&
                        (@field_at CompSpecs lsh0 t_struct_node (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
          destruct K12 as (Hf & Hrs).
          iPoseProof (lock_join with "[H1 H12]") as "H1".
          { iSplitL "H1"; iFrame; iPureIntro; auto. }
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _. iFrame; iPureIntro; repeat (split; auto).
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod "HClose". by iFrame.
      }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!(y = (NF, (succ.1.2, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (NF, (succ.1.2, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        iModIntro. iExists _.
        by iFrame "Hm".
      }
      Intros y.
      rewrite <- H11.
      forward.
      forward.
      Exists NF succ.1.2 Ews g_in r.
      unfold traverse_inv_2.
      entailer !.
      unfold_data_at (data_at Ews t_struct_pn _ b).
      cancel.
      admit.
      (* re-modify traverse_inv_2 *)
      (* contradiction *)
      easy.
    * forward.
      forward_if.
      gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
      assert_PROP (r.1.1.2 = lock_in) as Hlk.
      { sep_apply in_tree_equiv; entailer !. }
      Intros.
      rewrite Hlk.
      (* push back lock into invariant *)
      gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
      viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
      {
        go_lower.
        iIntros "((AU & #H) & H1)".
        iMod "AU" as (m) "[Hm HClose]".
        iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
        iDestruct "InvLock" as "(_ & InvLock)".
        iDestruct "InvLock" as (R) "[H1' H2']".
        unfold ltree.
        iDestruct "H1'" as (lsh1) "(%K12 & (H12 & H13))".
        iAssert(EX lsh0 : share,
                      !! (field_compatible t_struct_node [] pn ∧ readable_share lsh0 ) &&
                        (@field_at CompSpecs lsh0 t_struct_node (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
          destruct K12 as (Hf & Hrs).
          iPoseProof (lock_join with "[H1 H12]") as "H1".
          { iSplitL "H1"; iFrame; iPureIntro; auto. }
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _. iFrame; iPureIntro; repeat (split; auto).
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod "HClose". by iFrame.
      }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!(y = (F, (succ.1.2, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (F, (succ.1.2, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        iModIntro. iExists _.
        by iFrame "Hm".
      }
      Intros y.
      rewrite <- H11.
      forward.
      forward.
      Exists F succ.1.2 Ews g_in r.
      unfold traverse_inv_2.
      (* re-modify traverse_inv_2 *)
      admit.
      (* contradiction *)
      easy.
    }
    easy.
  + forward_if.
    easy.
    forward.
    forward.
    gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
    assert_PROP (r.1.1.2 = lock_in) as Hlk.
    { sep_apply in_tree_equiv; entailer !. }
    rewrite Hlk.
    Intros.
      (* push back lock into invariant *)
    gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_node _ _ pn).
    viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
    { go_lower; apply push_lock_back; auto. }
    Intros.
    gather_SEP AS (in_tree g g_in pn lock_in) (node_rep_R r.1.1.1 r.1.2 r.2 g)
                        (field_at _ _ _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (field_at Ews t_struct_node _ _ pn)
                        (malloc_token Ews t_struct_node pn) (my_half g_in Tsh r).
    viewshift_SEP 0 (AS * (node_lock_inv_pred g pn g_in r )).
    {
            go_lower.
            iIntros "(((((((AU & #H) & HNode) & H2) & H3) & H4) & H5) & H6)".
            iFrame.
            rewrite <- Hlk. iFrame "H". done.
    }
    forward_call release_inv (lock_in, node_lock_inv_pred g pn g_in r, AS).
    {
        lock_props.
        iIntros "(((((HAS & H1) & H2) & H3) & H4) & H5)".
        iCombine "HAS H1 H2 H3 H4 H5" as "Hnode_inv_pred".
        iVST.
        rewrite <- 2sepcon_assoc; rewrite <- 2sepcon_comm.
        apply sepcon_derives; [| cancel_frame].
        unfold atomic_shift; iIntros "((AU & H1) & #H2)";

              iAuIntro; unfold atomic_acc; simpl.
        iMod "AU" as (m) "[Hm HClose]".
        iModIntro.
        iExists tt.
        iPoseProof (in_tree_inv' g g_in g_root pn (r.1.1.2) m r
                         with "[H2 H1 $Hm]") as "(HI1 & HI2)".
        { rewrite Hlk. iFrame "H1 H2". }
          iDestruct "HI1" as "(HI1' & HI1)".
          rewrite Hlk.
          iFrame "HI1' HI1".
          iSplit.
          {
            iIntros "(Hnode_Iinv & InvLock)".
            iSpecialize ("HI2" with "InvLock").
            iDestruct "HClose" as "[HClose _]".
            iFrame "Hnode_Iinv".
            iSpecialize ("HClose" with "HI2").
              iFrame.
          }
          iIntros (_) "(H & _)".
          iSpecialize ("HI2" with "H").
          iDestruct "HClose" as "[HClose _]". 
          by iSpecialize ("HClose" with "HI2").
     }
     (* proving |--  traverse_inv *)
       forward.
       unfold traverse_inv.
       Exists n pn g_root lock.
       sep_apply (in_tree_duplicate g g_root n).
       entailer !. 
    - (* semax Delta (PROP ( )  RETURN ( ) SEP ()) (return _flag;) POSTCONDITION *)
       Intros flag.
       Intros pn gsh g_in r.
       unfold traverse_inv_1, traverse_inv_2.
       destruct flag.
       (*
       + simpl.
         autorewrite with norm.
         forward.
         unfold post_traverse.
         Exists (true, (pn, (gsh, (g_in, r)))).
         simpl. entailer !. 
       + forward.
         Exists (false, (pn, (gsh, (g_in, r)))).
         simpl.
         unfold node_lock_inv_pred_1, node_rep_1 at 1, tree_rep_R_1 at 1.
         Intros g1 g2 v1 p1 p2 l1 l2.
         rewrite H7.
         entailer !.
         exists v1, g1, g2; auto.
         unfold node_lock_inv_pred, node_rep, tree_rep_R.
         rewrite -> if_false; auto.
         simpl.
         Exists g1 g2 x v1 p1 p2 l1 l2.
         entailer !. apply derives_refl.
Qed.
*)
Admitted.


End give_up_traverse.
