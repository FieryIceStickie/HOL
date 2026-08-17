(*
  This file defines a type for coinductive choice trees (ctree), as
  described in Chappe et al.'s 2023 paper titled "Choice Trees".

  This implementation differs from the paper by replacing the stepping
  branch node BrS with a Tau node (the paper uses Step . = BrS 1 (λ_ -> .), and we have
  Step = Guard o Tau). Thus, BrD is renamed to Br, and we recover BrS as a Br node where
  every continuation is guarded by a Tau.

    ('a,'v,'e,'r) ctree  =
    |  Ret 'r                --  termination with result 'r
    |  Tau (ctree)           --  a silent action, then continue
    |  Vis 'e ('a -> ctree)  --  visible event 'e with answer 'a, then continue based on answer
    |  Br  ('v -> ctree)     --  branching based on 'v
*)

Theory ctree
Ancestors
  pred_set arithmetic list rich_list option relation sum pair
  combin bisimulation itreeTau quotient prim_rec
Libs
  pred_setLib term_tactic mp_then BasicProvers dep_rewrite quotientLib

Theorem MAX_SUC:
  MAX (SUC n) (SUC m) = SUC (MAX n m)
Proof
  rw[MAX_DEF]
QED

Theorem MAX_SET_IMAGE_SUC:
  FINITE P ∧ P ≠ ∅ ==> MAX_SET (IMAGE SUC P) = SUC (MAX_SET P)
Proof
  Induct_on `FINITE` >> rw[MAX_SET_THM]
  >> Cases_on `P = ∅` >> gvs[MAX_SUC]
QED

Theorem FINITE_UPPER_BOUNDED:
  FINITE P <=> ∃m. ∀n. n ∈ P ==> n ≤ m
Proof
  rw[EQ_IMP_THM]
  >- metis_tac[X_LE_MAX_SET]
  >> first_x_assum mp_tac >> qid_spec_tac `P`
  >> Induct_on `m` >> rw[]
  >> irule SUBSET_FINITE_I
  >- (qexists `{0}` >> rw[SUBSET_DEF])
  >> qexists `(P DIFF {SUC m}) ∪ {SUC m}` >> rw[SUBSET_DEF]
  >> first_x_assum irule >> rw[]
  >> first_x_assum drule >> rw[]
QED

Theorem DIFF_EMPTY_IMP_EQ:
  s DIFF t = ∅ ∧ t DIFF s = ∅ <=> s = t
Proof
  rw[EXTENSION] >> metis_tac[]
QED

Theorem MAX_SET_BIGUNION:
  FINITE Ps ∧ (∀P. P ∈ Ps ==> FINITE P) ∧ (∃P. P ∈ Ps ∧ P ≠ ∅)
    ==> ∃P. P ∈ Ps ∧ MAX_SET P = MAX_SET (BIGUNION Ps) ∧
        ∀P'. P' ∈ Ps ==> MAX_SET P' ≤ MAX_SET P
Proof
  rw[] >> `MAX_SET (BIGUNION Ps) ∈ BIGUNION Ps` by (
    irule MAX_SET_IN_SET
    >> rw[FINITE_BIGUNION, EXTENSION]
    >- metis_tac[]
    >> qexists `P` >> rw[]
    >> gvs[EXTENSION] >> metis_tac[]
  )
  >> gvs[BIGUNION] >> gvs[GSYM BIGUNION]
  >> qexists `s` >> simp[] >> conj_asm1_tac
  >> DEP_REWRITE_TAC[MAX_SET_TEST_IFF] >> rw[]
  >- (rw[EXTENSION] >> metis_tac[]) 
  >- (irule X_LE_MAX_SET >> rw[FINITE_BIGUNION] >> rpt (goal_assum $ dxrule_at Any))
  >> Cases_on `P' = ∅` >> rw[]
  >> irule X_LE_MAX_SET >> rw[FINITE_BIGUNION]
  >> irule_at (Pos hd) MAX_SET_IN_SET >> rw[]
QED

Theorem FINITE_SET_OF_SETS_UPPER_BOUNDED:
  (∀P. P ∈ Ps ==> FINITE P ∧ MAX_SET P ≤ n) ==> FINITE Ps
Proof
  rw[] >> irule SUBSET_FINITE_I
  >> qexists `POW {k | k ≤ n}`
  >> rw[FINITE_UPPER_BOUNDED]
  >- metis_tac[]
  >> rw[SUBSET_DEF, IN_POW]
  >> first_x_assum dxrule >> rw[]
  >> metis_tac[X_LE_MAX_SET, LE_TRANS]
QED

(* Used with irule_at for bisimulation *)
Theorem rel_exact_lemma[local]:
  (λp q. p = u ∧ q = v) u v
Proof
  rw[]
QED

(* -----------------------------------------------------------------------------------
     0. Type Definition
   -----------------------------------------------------------------------------------
   Hol4 currently does not support (co)algebraic datatype definitions, so we build
   the type manually. As a tree, ctrees support a natural encoding via its indexing
   function, one form of which takes a list of edge types and returns SOME node if
   the edges are a valid path from the root of the tree, and NONE otherwise.
   -----------------------------------------------------------------------------------*)

(* --- 0.0 - rep and abs --- *)

Datatype:
  ctree_node = RetN 'r | TauN | VisN 'e | BrN
End

Datatype:
  ctree_edge = tauE | visE 'a | brE 'v
End

Theorem ctree_edge_distinct[local] = TypeBase.distinct_of ``:('a, 'v) ctree_edge``;

Type ctree_rep[pp] = ``:('a, 'v) ctree_edge list -> ('e, 'r) ctree_node option``;

(* itreeTauTheory defines valid paths by extracting elements via x ++ y::ys.
   We differ in that we define valid_paths inductively, but the overall idea is the same. *)
Inductive valid_paths:
[~nil:] valid_paths f []
[~tau:] valid_paths f path ∧ f path = SOME TauN     ==> valid_paths f (SNOC tauE path)
[~vis:] valid_paths f path ∧ f path = SOME (VisN e) ==> valid_paths f (SNOC (visE a) path)
[~br:]  valid_paths f path ∧ f path = SOME BrN      ==> valid_paths f (SNOC (brE v) path)
End

Theorem valid_paths_cons:
  valid_paths f (h::t) <=>
   (case f [] of
    | NONE => F
    | SOME (RetN r) => F
    | SOME TauN     => h = tauE
    | SOME (VisN e) => ∃a. h = visE a
    | SOME BrN      => ∃v. h = brE v) ∧
  valid_paths (λp. f (h::p)) t
Proof
  rw[EQ_IMP_THM] >- (
    pop_assum mp_tac >> Induct_on `t` using SNOC_INDUCT
    >> rw[Once valid_paths_cases]
    >> metis_tac[]
  )
  >- (
    pop_assum mp_tac >> qid_spec_tac `f`
    >> Induct_on `t` using SNOC_INDUCT
    >> rw[valid_paths_nil]
    >> rw[Once valid_paths_cases]
    >> dxrule $ iffLR valid_paths_cases >> rw[]
  )
  >- (
    rpt (FULL_CASE_TAC >> gvs[])
    >> Induct_on `t` using SNOC_INDUCT
    >> rw[] >> rw[Once valid_paths_cases, valid_paths_nil]
    >> dxrule $ iffLR valid_paths_cases >> rw[]
  )
QED

Definition ctree_rep_ok_def:
  ctree_rep_ok f <=> ∀path. path ∉ valid_paths f <=> f path = NONE
End

(* We choose a ret node for simplicity *)
Theorem type_inhabited[local]:
  ∃f. ctree_rep_ok f
Proof
  qexists `λp. if p = [] then SOME (RetN ARB) else NONE`
  >> rw[ctree_rep_ok_def, IN_DEF]
  >> rw[EQ_IMP_THM, valid_paths_nil]
  >> gvs[Once valid_paths_cases]
QED

val ctree_tydef = new_type_definition ("ctree", type_inhabited);
val ctree_repabs = define_new_type_bijections
  { name = "ctree_absrep",
    ABS  = "ctree_abs",
    REP  = "ctree_rep",
    tyax = ctree_tydef};

(* Lemmas for proving reps are valid *)
Theorem ctree_rep_ok_rep[local]:
  ctree_rep_ok (ctree_rep t)
Proof
  metis_tac[ctree_repabs]
QED

Theorem ctree_rep_ok_o[local]:
  (∀x. ctree_rep_ok (f x)) ==> ctree_rep o ctree_abs o f = f
Proof
  metis_tac[ctree_repabs, o_DEF]
QED

Theorem ctree_rep_11[local]:
  ctree_rep t = ctree_rep t' <=> t = t'
Proof
  metis_tac[ctree_repabs]
QED

Theorem ctree_abs_11[local]:
  ctree_abs f = ctree_abs f' ∧ ctree_rep_ok f ∧ ctree_rep_ok f' ==> f = f'
Proof
  metis_tac[ctree_repabs]
QED

(* --- 0.1 - Constructors --- *)

Definition Ret_rep_def:
  Ret_rep r = λpath.
    case path of
    | [] => SOME (RetN r)
    | _  => NONE
End

Definition Tau_rep_def:
  Tau_rep f = λpath.
    case path of
    | [] => SOME TauN
    | tauE::path => f path
    | _ => NONE
End

Definition Vis_rep_def:
  Vis_rep e g = λpath.
    case path of
    | [] => SOME (VisN e)
    | visE a::path => g a path
    | _ => NONE
End

Definition Br_rep_def:
  Br_rep k = λpath.
    case path of
    | [] => SOME BrN
    | brE v::path => k v path
    | _ => NONE
End

val ctree_ctor_rep_def = LIST_CONJ [Ret_rep_def, Tau_rep_def, Vis_rep_def, Br_rep_def];

Theorem ctree_rep_ok_ctor[local]:
  ctree_rep_ok (Ret_rep r) ∧
  (ctree_rep_ok u ==> ctree_rep_ok (Tau_rep u)) ∧
  ((∀a. ctree_rep_ok (g a)) ==> ctree_rep_ok (Vis_rep e g)) ∧
  ((∀v. ctree_rep_ok (k v)) ==> ctree_rep_ok (Br_rep k))
Proof
  rw[ctree_rep_ok_def, ctree_ctor_rep_def]
  >> Cases_on `path` >> rw[]
  >> gvs[IN_DEF, valid_paths_nil]
  >> rw[valid_paths_cons]
  >> CASE_TAC >> metis_tac[]
QED

Theorem ctree_ctor_rep_11[local]:
  (Ret_rep r = Ret_rep r' <=> r = r') ∧
  (Tau_rep u = Tau_rep u' <=> u = u') ∧
  (Vis_rep e g = Vis_rep e' g' <=> e = e' ∧ g = g') ∧
  (Br_rep k = Br_rep k' <=> k = k')
Proof
  rw[ctree_ctor_rep_def, FUN_EQ_THM, EQ_IMP_THM]
  >| map (fn p => first_x_assum $ qspec_then p mp_tac)
     [`[]`, `tauE::x`, `[]`, `visE x::x'`,  `brE x::x'`]
  >> rw[]
QED

Definition Ret_def:
  Ret r = ctree_abs (Ret_rep r)
End

Definition Tau_def:
  Tau u = ctree_abs (Tau_rep (ctree_rep u))
End

Definition Vis_def:
  Vis e g = ctree_abs (Vis_rep e (ctree_rep o g))
End

Definition Br_def:
  Br k = ctree_abs (Br_rep (ctree_rep o k))
End

val ctree_ctor_def = LIST_CONJ [Ret_def, Tau_def, Vis_def, Br_def];

Theorem ctree_rep_ctor[local]:
  ctree_rep (Ret r) = Ret_rep r ∧
  ctree_rep (Tau u) = Tau_rep (ctree_rep u) ∧
  ctree_rep (Vis e g) = Vis_rep e (ctree_rep o g) ∧
  ctree_rep (Br k) = Br_rep (ctree_rep o k)
Proof
  rw[ctree_ctor_def]
  >> DEP_REWRITE_TAC[iffLR $ cj 2 ctree_repabs, ctree_rep_ok_ctor]
  >> rw[ctree_rep_ok_rep]
QED

(* --- 0.2 - Injectivity and Distinctness --- *)

Theorem ctree_11:
  (Ret r = Ret r' <=> r = r') ∧
  (Tau u = Tau u' <=> u = u') ∧
  (Vis e g = Vis e' g' <=> e = e' ∧ g = g') ∧
  (Br k = Br k' <=> k = k')
Proof
  rw[EQ_IMP_THM, ctree_ctor_def]
  >> dxrule ctree_abs_11 >> rw[ctree_ctor_rep_11]
  >> metis_tac[ctree_rep_ok_rep, ctree_rep_ok_ctor, ctree_rep_11, o_DEF]
QED

Theorem ctree_distinct_lemma[local]:
  ALL_DISTINCT [Ret r; Tau u; Vis e g; Br k]
Proof
  rw[ALL_DISTINCT, ctree_ctor_def]
  >> spose_not_then strip_assume_tac
  >> dxrule ctree_abs_11 >> rw[]
  >>~- ([`ctree_rep_ok`], metis_tac[ctree_rep_ok_ctor, ctree_rep_ok_rep, o_DEF])
  >> rw[ctree_ctor_rep_def, FUN_EQ_THM]
  >> qexists `[]` >> rw[]
QED

Theorem ctree_distinct =
  ctree_distinct_lemma |> SIMP_RULE std_ss [ALL_DISTINCT, MEM, GSYM CONJ_ASSOC];

(* --- 0.3 - Cases --- *)

Theorem ctree_rep_cases[local]:
  ∀f. ctree_rep_ok f ==>
    (∃r.   f = Ret_rep r) ∨
    (∃u.   f = Tau_rep u   ∧ ctree_rep_ok u) ∨
    (∃e g. f = Vis_rep e g ∧ ∀a. ctree_rep_ok (g a)) ∨
    (∃k.   f = Br_rep  k   ∧ ∀v. ctree_rep_ok (k v))
Proof
  rw[] >> Cases_on `f []`
  >- metis_tac[ctree_rep_ok_def, valid_paths_nil, IN_DEF]
  >> Cases_on `x`
  >| [disj1_tac >> qexists `r`,
      disj2_tac >> disj1_tac >> qexists `λp. f (tauE::p)`,
      disj2_tac >> disj2_tac >> disj1_tac >> qexistsl [`e`, `λa p. f (visE a::p)`],
      disj2_tac >> disj2_tac >> disj2_tac >> qexists `λv p. f (brE v::p)`]
  >> rw[FUN_EQ_THM, ctree_ctor_rep_def]
  >> rpt CASE_TAC
  >> gvs[ctree_rep_ok_def, IN_DEF] >> rw[]
  >> qmatch_goalsub_abbrev_tac `f (h::t)`
  >> first_x_assum $ qspec_then `h::t` mp_tac
  >> unabbrev_all_tac
  >> rw[valid_paths_cons]
QED

Theorem ctree_cases:
  ∀t. (∃r. t = Ret r) ∨ (∃u. t = Tau u) ∨ (∃e g. t = Vis e g) ∨ (∃k. t = Br k)
Proof
  rw[ctree_ctor_def, GSYM ctree_rep_11]
  >> Cases_on `ctree_rep t` using ctree_rep_cases
  >> gvs[ctree_rep_ok_rep]
  >> metis_tac[ctree_rep_ok_ctor, ctree_rep_ok_o, ctree_repabs]
QED

Definition ctree_CASE_def:
  ctree_CASE t ret tau vis br =
    case ctree_rep t [] of
    | NONE   => ARB (* can't happen *)
    | SOME (RetN r) => ret r
    | SOME TauN     => tau   $ ctree_abs (λp. ctree_rep t (tauE::p))
    | SOME (VisN e) => vis e $ λa. ctree_abs (λp. ctree_rep t (visE a::p))
    | SOME BrN      => br    $ λv. ctree_abs (λp. ctree_rep t (brE v::p))
End

Theorem ctree_CASE:
  ctree_CASE (Ret r) ret tau vis br = ret r ∧
  ctree_CASE (Tau u) ret tau vis br = tau u ∧
  ctree_CASE (Vis e g) ret tau vis br = vis e g ∧
  ctree_CASE (Br k) ret tau vis br = br k
Proof
  rw[ctree_CASE_def, ctree_rep_ctor, ctree_ctor_rep_def]
  >> cong_tac NONE
  >> metis_tac[ctree_repabs]
QED

Theorem ctree_CASE_cong:
  (t = t') ∧
  (∀r. t = Ret r ==> ret r = ret' r) ∧
  (∀u. t = Tau u ==> tau u = tau' u) ∧
  (∀e g. t = Vis e g ==> vis e g = vis' e g) ∧
  (∀k. t = Br k ==> br k = br' k) ==>
  ctree_CASE t ret tau vis br = ctree_CASE t' ret' tau' vis' br'
Proof
  Cases_on `t` using ctree_cases >> rpt (rw[ctree_CASE])
QED

Theorem ctree_CASE_eq:
  ctree_CASE t ret tau vis br = x <=>
    (∃r.   t = Ret r   ∧ ret r   = x) ∨
    (∃u.   t = Tau u   ∧ tau u   = x) ∨
    (∃e g. t = Vis e g ∧ vis e g = x) ∨
    (∃k.   t = Br  k   ∧ br  k   = x)
Proof
  Cases_on `t` using ctree_cases >> rw[ctree_CASE, ctree_11, ctree_distinct]
QED

Theorem ctree_CASE_elim:
  R (ctree_CASE t ret tau vis br) <=>
    (∃r.   t = Ret r   ∧ R (ret r)  ) ∨
    (∃u.   t = Tau u   ∧ R (tau u)  ) ∨
    (∃e g. t = Vis e g ∧ R (vis e g)) ∨
    (∃k.   t = Br  k   ∧ R (br k)   )
Proof
  Cases_on `t` using ctree_cases >> rw[ctree_CASE, ctree_11, ctree_distinct]
QED

Theorem ctree_bisimulation:
  p = q <=> ∃R. R p q ∧
    (∀r t.   R (Ret r) t   ==> t = Ret r) ∧
    (∀u t.   R (Tau u) t   ==> ∃u'. t = Tau u' ∧ R u u') ∧
    (∀e g t. R (Vis e g) t ==> ∃g'. t = Vis e g' ∧ ∀a. R (g a) (g' a)) ∧
    (∀k t.   R (Br k) t    ==> ∃k'. t = Br k' ∧ ∀v. R (k v) (k' v))
Proof
  rw[EQ_IMP_THM]
  >- (qexists `(=)` >> gvs[ctree_11])
  >> irule $ iffLR ctree_rep_11 >> rw[FUN_EQ_THM]
  >> last_x_assum mp_tac >> qid_spec_tac `p` >> qid_spec_tac `q`
  >> Induct_on `x` >> rw[]
  >> Cases_on `p` using ctree_cases
  >> last_x_assum dxrule >> rw[]
  >> rw[ctree_rep_ctor, ctree_ctor_rep_def]
  >> CASE_TAC >> metis_tac[]
QED

Theorem datatype_ctree:
  DATATYPE (ctree
    (Ret : 'r -> ('a, 'v, 'e, 'r) ctree)
    (Tau : ('a, 'v, 'e, 'r) ctree -> ('a, 'v, 'e, 'r) ctree)
    (Vis : 'e -> ('a -> ('a, 'v, 'e, 'r) ctree) -> ('a, 'v, 'e, 'r) ctree)
    (Br  : ('v -> ('a, 'v, 'e, 'r) ctree) -> ('a, 'v, 'e, 'r) ctree)
  )
Proof
  rw[boolTheory.DATATYPE_TAG_THM]
QED

val _ = TypeBase.export [
  TypeBasePure.mk_datatype_info {
      ax = TypeBasePure.ORIG TRUTH,
      induction = TypeBasePure.ORIG ctree_bisimulation,
      case_def = ctree_CASE,
      case_cong = ctree_CASE_cong,
      case_eq = ctree_CASE_eq,
      case_elim = ctree_CASE_elim,
      nchotomy = ctree_cases,
      size = NONE,
      encode = NONE,
      lift = NONE,
      one_one = SOME ctree_11,
      distinct = SOME ctree_distinct,
      fields = [],
      accessors = [],
      updates = [],
      destructors = [],
      recognizers = []
    } ]

Overload "case" = ``ctree_CASE``;

(* Automation for case simps *)
fun ctree_srule rules = SIMP_RULE bool_ss ([ctree_11, ctree_distinct] @ rules);

fun cases_to_simp q thm =
  map
  (fn p => thm |> Q.INST [q |-> p] |> ctree_srule [])
  [`Ret r`, `Tau u`, `Vis e g`, `Br k`]
  |> LIST_CONJ;

(* --- 0.4 - Unfold --- *)

Datatype:
  ctree_next = Ret' 'r
             | Tau' 's
             | Vis' 'e ('a -> 's)
             | Br'  ('b -> 's)
End

Definition ctree_unfold_rep_def:
  ctree_unfold_rep f s path =
    case (path, f s) of
    | ([], Ret' r)   => SOME (RetN r)
    | ([], Tau' u)   => SOME TauN
    | ([], Vis' e g) => SOME (VisN e)
    | ([], Br' k)    => SOME BrN
    | (tauE::p, Tau' u)     => ctree_unfold_rep f u p
    | (visE a::p, Vis' e g) => ctree_unfold_rep f (g a) p
    | (brE v::p, Br' k)     => ctree_unfold_rep f (k v) p
    | _ => NONE
End

Definition ctree_unfold_def:
  ctree_unfold f s = ctree_abs (ctree_unfold_rep f s)
End

Theorem ctree_rep_ok_unfold[local]:
  ctree_rep_ok (ctree_unfold_rep f s)
Proof
  rw[ctree_rep_ok_def]
  >> qid_spec_tac `s` >> Induct_on `path`
  >> gvs[IN_DEF, valid_paths_nil, valid_paths_cons]
  >> rw[Once ctree_unfold_rep_def] >> CASE_TAC
  >> rw[Once ctree_unfold_rep_def, EQ_IMP_THM]
  >> rw[Once ctree_unfold_rep_def]
  >> rpt FULL_CASE_TAC >> gvs[SF ETA_ss]
  >> first_x_assum mp_tac >> rw[Once ctree_unfold_rep_def]
QED

Theorem ctree_unfold_thm:
  ctree_unfold f s =
    case f s of
    | Ret' r   => Ret r
    | Tau' u   => Tau (ctree_unfold f u)
    | Vis' e g => Vis e (ctree_unfold f o g)
    | Br' k    => Br (ctree_unfold f o k)
Proof
  Cases_on `f s`
  >> rw[ctree_unfold_def, ctree_ctor_def] >> cong_tac NONE
  >> rw[FUN_EQ_THM, Once ctree_unfold_rep_def, ctree_ctor_rep_def]
  >> rpt CASE_TAC >> rw[ctree_unfold_def]
  >> metis_tac[ctree_repabs, ctree_rep_ok_unfold]
QED

(* The ∃_. in the ret case is for rewriting the symmetric case; without it,
   Ret r = ctree_unfold f s won't be rewritten. *)
Theorem ctree_unfold_eq[simp]:
  (ctree_unfold f s = Ret r   <=> ∃_. f s = Ret' r) ∧
  (ctree_unfold f s = Tau u   <=> ∃u'. f s = Tau' u' ∧ ctree_unfold f u' = u) ∧
  (ctree_unfold f s = Vis e g <=> ∃g'. f s = Vis' e g' ∧ (λa. ctree_unfold f (g' a)) = g) ∧
  (ctree_unfold f s = Br k    <=> ∃k'. f s = Br' k' ∧ (λv. ctree_unfold f (k' v)) = k)
Proof
  Cases_on `f s` >> rw[] >> rw[Once ctree_unfold_thm, FUN_EQ_THM]
QED

(* --- 0.5 - Index --- *)

Definition ctree_index_def:
  ctree_index path t =
    if ctree_rep t path ≠ NONE
    then SOME (ctree_abs (λp. ctree_rep t (path ++ p)))
    else NONE
End

Theorem ctree_index_nil[simp]:
  ctree_index [] t = SOME t
Proof
  rw[ctree_index_def, ctree_repabs, SF ETA_ss]
  >> Cases_on `t` >> rw[ctree_rep_ctor, ctree_ctor_rep_def]
QED

Theorem ctree_index_cons[simp]:
  ctree_index (h::p)      (Ret r)   = NONE ∧
  ctree_index (tauE::p)   (Tau u)   = ctree_index p u ∧
  ctree_index (visE a::p) (Tau u) = NONE ∧
  ctree_index (brE v::p)  (Tau u)    = NONE ∧
  ctree_index (tauE::p)   (Vis e g)   = NONE ∧
  ctree_index (visE a::p) (Vis e g) = ctree_index p (g a) ∧
  ctree_index (brE v::p)  (Vis e g)    = NONE ∧
  ctree_index (tauE::p)   (Br k)   = NONE ∧
  ctree_index (visE a::p) (Br k) = NONE ∧
  ctree_index (brE v::p)  (Br k)    = ctree_index p (k v)
Proof
  rw[ctree_index_def, ctree_rep_ctor, ctree_ctor_rep_def]
QED

Theorem ctree_index_ret[simp]:
  ctree_index p (Ret r) = SOME t <=> p = [] ∧ t = Ret r
Proof
  Cases_on `p` >> rw[] >> metis_tac[]
QED

Theorem ctree_index_eq_some[simp]:
  (ctree_index (h::p) (Tau u) = SOME t' <=> h = tauE ∧ ctree_index p u = SOME t') ∧
  (ctree_index (h::p) (Vis e g) = SOME t' <=> ∃a. h = visE a ∧ ctree_index p (g a) = SOME t') ∧
  (ctree_index (h::p) (Br k) = SOME t' <=> ∃v. h = brE v ∧ ctree_index p (k v) = SOME t')
Proof
  Cases_on `h` >> rw[]
QED

Theorem ctree_index_rules = LIST_CONJ [ctree_index_nil, ctree_index_cons];

Theorem ctree_index_append:
  ctree_index (p ++ q) = OPTION_MCOMP (ctree_index q) (ctree_index p)
Proof
  rw[FUN_EQ_THM, OPTION_MCOMP_def, OPTION_BIND_eq_case]
  >> qid_spec_tac `x` >> Induct_on `p` >> rw[]
  >> Cases_on `h` >> Cases_on `x` >> rw[]
QED

Theorem ctree_index_append_eq:
  ctree_index (p ++ q) t = SOME t' <=> ∃u.
    ctree_index p t = SOME u ∧ ctree_index q u = SOME t'
Proof
  rw[ctree_index_append, EQ_IMP_THM, OPTION_MCOMP_def]
QED

Theorem ctree_index_snoc_eq:
  ctree_index (SNOC h path) t = SOME t' <=> ∃u.
    ctree_index path t = SOME u ∧ ctree_index [h] u = SOME t'
Proof
  rw[SNOC_APPEND, ctree_index_append_eq]
QED


(* -----------------------------------------------------------------------------------
     1. Equational Theory
   -----------------------------------------------------------------------------------
   This section defines important combinators and constants, and develops their
   equational theory in preparation for reasoning about weak/strong bisimulation.
   Additionally, we develop variants of ctree_bisimulation, which are useful in
   proving equality between complex constructs.
   -----------------------------------------------------------------------------------*)

(* --- 1.0 - Bisimulation variants --- *)

(* Theorems ending in coind are alternate forms of the associated bisimulation theorem,
   meant to be used with ho_match_mp_tac to automatically deduce the relation from the
   structure of the goal. *)
Theorem ctree_bisimulation_coind:
  (∀r t.   R (Ret r) t   ==> t = Ret r) ∧
  (∀u t.   R (Tau u) t   ==> ∃u'. t = Tau u' ∧ R u u') ∧
  (∀e g t. R (Vis e g) t ==> ∃g'. t = Vis e g' ∧ ∀a. R (g a) (g' a)) ∧
  (∀k t.   R (Br k) t    ==> ∃k'. t = Br k' ∧ ∀v. R (k v) (k' v))
  ==> ∀t1 t2. R t1 t2 ==> t1 = t2
Proof
  rw[] >> irule $ iffRL ctree_bisimulation
  >> qexists `R` >> rw[]
QED

(* Takes the reflexive closure of the relation we provide *)
Theorem ctree_strong_bisimulation:
  p = q <=> ∃R. R p q ∧
    (∀r t.   R (Ret r) t   ==> t = Ret r) ∧
    (∀u t.   R (Tau u) t   ==> ∃u'. t = Tau u' ∧ (R u u' ∨ u = u')) ∧
    (∀e g t. R (Vis e g) t ==> ∃g'. t = Vis e g' ∧ ∀a. R (g a) (g' a) ∨ g a = g' a) ∧
    (∀k t.   R (Br k) t    ==> ∃k'. t = Br k' ∧ ∀v. R (k v) (k' v) ∨ k v = k' v)
Proof
  rw[EQ_IMP_THM]
  >- (qexists `(=)` >> rw[])
  >> irule $ iffRL ctree_bisimulation
  >> qexists `RC R` >> rw[RC_DEF]
  >> metis_tac[]
QED

Theorem ctree_strong_bisimulation_coind:
  (∀r t.   R (Ret r) t   ==> t = Ret r) ∧
  (∀u t.   R (Tau u) t   ==> ∃u'. t = Tau u' ∧ (R u u' ∨ u = u')) ∧
  (∀e g t. R (Vis e g) t ==> ∃g'. t = Vis e g' ∧ ∀a. R (g a) (g' a) ∨ g a = g' a) ∧
  (∀k t.   R (Br k) t    ==> ∃k'. t = Br k' ∧ ∀v. R (k v) (k' v) ∨ k v = k' v)
  ==> ∀t1 t2. R t1 t2 ==> t1 = t2
Proof
  rw[] >> irule $ iffRL ctree_strong_bisimulation
  >> qexists `R` >> rw[]
QED

(* --- 1.1 - Combinators/Constants --- *)

Definition Guard_def:
  Guard t = Br (λb. t)
End

Definition BrS_def:
  BrS k = Br (Tau o k)
End

Definition Step_def:
  Step = Guard o Tau
End

Definition Guard'_def:
  Guard' t = Br' (λb. t)
End

Theorem ctree_unfold_guard:
  f s = Guard' s' ==> ctree_unfold f s = Guard (ctree_unfold f s')
Proof
  rw[Guard_def, Guard'_def, Once ctree_unfold_thm, FUN_EQ_THM]
QED

Definition ctree_stuck_def:
  ctree_stuck = ctree_unfold (λ_. Guard' ()) ()
End

Definition ctree_spin_def:
  ctree_spin = ctree_unfold (λ_. Tau' ()) ()
End

Theorem ctree_stuck_thm:
  ctree_stuck = Guard ctree_stuck
Proof
  rw[ctree_stuck_def, Once ctree_unfold_guard]
QED

Theorem ctree_spin_thm:
  ctree_spin = Tau ctree_spin
Proof
  rw[ctree_spin_def, Once ctree_unfold_thm]
QED

(* These two are very useful for iter, so we define them specifically *)
Definition LRet_def:
  LRet s = Ret (INL s)
End

Definition RRet_def:
  RRet r = Ret (INR r)
End

(* We define 9 primitives/constants/combinators:
     Ret, Tau, Vis, Br, Guard, BrS, Step, ctree_stuck, ctree_spin, LRet, RRet
   There are 9C2 + 9 = 45 pairs to develop equations for.
   ctree_11 gives 4
   ctree_distinct gives 6
   ctree_comb_distinct gives 16 + 3 + 2 + 16 + 1 = 38
   ctree_comb_eq gives 4 + 4 + 2 + 1 + 1 + 4 = 16
   The total is then 64, with the remaining two being
     ctree_stuck = ctree_stuck ∧ ctree_spin = ctree_spin
   which are trivial.
*)
Theorem ctree_comb_distinct_lemma[local]:
  DISJOINT {Guard t; BrS k; Step t; ctree_stuck} {Ret r; Tau u; Vis e g; ctree_spin} ∧
  DISJOINT {ctree_spin} {Ret r; Vis e g; Br k} ∧
  DISJOINT {ctree_stuck} {BrS k; Step t}
Proof
  rw[]
  >> rw[Once ctree_stuck_thm, Once ctree_spin_thm]
  >> rw[Guard_def, BrS_def, Step_def]
  >> rw[FUN_EQ_THM, Once ctree_stuck_thm]
  >> rw[Guard_def]
QED

(* This is separate to avoid type issues *)
Theorem ctree_comb_distinct_lemma2[local]:
  DISJOINT {LRet s; RRet r} {Tau u; Vis e g; Br k; Guard t; BrS k; Step t; ctree_stuck; ctree_spin} ∧
  LRet s ≠ RRet r
Proof
  rw[LRet_def, RRet_def]
  >> rw[Once ctree_stuck_thm, Once ctree_spin_thm]
  >> rw[Guard_def, BrS_def, Step_def]
QED

val set_ss = std_ss ++ PRED_SET_ss
Theorem ctree_comb_distinct[simp] =
  LIST_CONJ [ctree_comb_distinct_lemma, ctree_comb_distinct_lemma2]
  |> SIMP_RULE set_ss [GSYM CONJ_ASSOC];

Theorem ctree_comb_eq[simp]:
  (Br k = Guard t        <=> ∃_. k = λv. t) ∧
  (Br k = BrS k'         <=> ∃_. k = λv. Tau (k' v)) ∧
  (Br k = Step t         <=> ∃_. k = λv. Tau t) ∧
  (Br k = ctree_stuck    <=> ∃_. k = λv. ctree_stuck) ∧
  (Guard t = Guard t'    <=> t = t') ∧
  (Guard t = BrS k       <=> ∃u. t = Tau u ∧ k = λv. u) ∧
  (Guard t = Step t'     <=> ∃_. t = Tau t') ∧
  (Guard t = ctree_stuck <=> ∃_. t = ctree_stuck) ∧
  (BrS k = BrS k'        <=> k = k') ∧
  (BrS k = Step t        <=> ∃_. k = λv. t) ∧
  (Step t = Step t'      <=> t = t') ∧
  (Tau u = ctree_spin    <=> ∃_. u = ctree_spin) ∧
  (LRet s = LRet s'      <=> s = s') ∧
  (RRet r = RRet r'      <=> r = r') ∧
  (LRet p = Ret p'       <=> ∃_. p' = INL p) ∧
  (RRet q = Ret q'       <=> ∃_. q' = INR q)
Proof
  rw[]
  >> rw[Once ctree_stuck_thm, Once ctree_spin_thm]
  >> rw[Guard_def, BrS_def, Step_def, LRet_def, RRet_def, FUN_EQ_THM]
  >> metis_tac[ctree_11]
QED

Theorem ctree_guard'_simp_lemma[local]:
  DISJOINT {Guard' t} {Ret' r; Tau' u; Vis' e g} ∧
  (Guard' t = Br' k <=> ∃_. k = λv. t)
Proof
  rw[Guard'_def] >> metis_tac[]
QED

Theorem ctree_guard'_simp[simp] = ctree_guard'_simp_lemma |> SIMP_RULE set_ss [GSYM CONJ_ASSOC];

Theorem ctree_index_combs[simp]:
  ctree_index (tauE::p)   (Guard t) = NONE ∧
  ctree_index (visE a::p) (Guard t) = NONE ∧
  ctree_index (brE v::p)  (Guard t) = ctree_index p t ∧
  ctree_index (tauE::p)   (BrS k)   = NONE ∧
  ctree_index (visE a::p) (BrS k)   = NONE ∧
  ctree_index (brE v::p)  (BrS k)   = ctree_index p (Tau (k v)) ∧
  ctree_index (tauE::p)   (Step t)  = NONE ∧
  ctree_index (visE a::p) (Step t)  = NONE ∧
  ctree_index (brE v::p)  (Step t)  = ctree_index p (Tau t) ∧
  ctree_index (h::p)      (LRet s)  = NONE ∧
  ctree_index (h::p)      (RRet r)  = NONE
Proof
  rw[Guard_def, BrS_def, Step_def, LRet_def, RRet_def]
QED

Theorem ctree_index_stuck_spin:
  (ctree_index p ctree_stuck = if EVERY (λh. ∃v. h = brE v) p then SOME ctree_stuck else NONE) ∧
  ctree_index p ctree_spin = if EVERY (λh. h = tauE) p then SOME ctree_spin else NONE
Proof
  Induct_on `p` >> rw[]
  >> rw[Once ctree_stuck_thm, Once ctree_spin_thm] >> rw[]
  >> Cases_on `h` >> rw[]
QED

Theorem ctree_index_stuck_spin_eq_some[simp]:
  (ctree_index p ctree_stuck = SOME t <=> EVERY (λh. ∃v. h = brE v) p ∧ t = ctree_stuck) ∧
  (ctree_index p ctree_spin = SOME t <=> EVERY (λh. h = tauE) p ∧ t = ctree_spin)
Proof
  rw[ctree_index_stuck_spin]
QED

(* --- 1.2 - Bind --- *)

Definition ctree_push_inj_def:
  ctree_push_inj inj t =
    case t of
    | Ret r   => Ret' r
    | Tau u   => Tau'   (inj u)
    | Vis e g => Vis' e (inj o g)
    | Br  k   => Br'    (inj o k)
End

(* Note: We cannot just do
   | Ret' r => ctree_push_inj INR (k r)
   | t => t
   because this would make the return types of the ctrees
   in INL and INR the same. *)
Definition ctree_bind_fn_def:
  (ctree_bind_fn k (INL u) =
     case ctree_push_inj INL u of
     | Ret' r => ctree_push_inj INR (k r)
     | Tau' u => Tau' u
     | Vis' e g => Vis' e g
     | Br' k => Br' k) ∧
  (ctree_bind_fn k (INR v) = ctree_push_inj INR v)
End

Definition ctree_bind_def:
  ctree_bind t k = ctree_unfold (ctree_bind_fn k) (INL t)
End

Definition ctree_compose_def:
  ctree_compose f g = λx. ctree_bind (f x) g
End

val _ = set_mapped_fixity {
  term_name = "ctree_compose",
  fixity = Infixl 600,
  tok = ">>>"
};

Theorem ctree_compose_thm[simp] = ctree_compose_def |> SIMP_RULE std_ss [FUN_EQ_THM]

Theorem ctree_compose_o[simp]:
  (f o g) >>> h = (f >>> h) o g
Proof
  rw[FUN_EQ_THM]
QED

Theorem ctree_bind_INR_id[local]:
  ctree_unfold (ctree_bind_fn k) (INR t) = t
Proof
  irule $ iffRL ctree_bisimulation
  >> qexists `λu v. ∃t. u = ctree_unfold (ctree_bind_fn k) (INR t) ∧ v = t`
  >> rw[ctree_bind_fn_def, ctree_push_inj_def] >> FULL_CASE_TAC
  >> gvs[]
QED

Theorem ctree_bind_simps[simp]:
  ctree_bind (Ret r)   h = h r ∧
  ctree_bind (Tau u)   h = Tau (ctree_bind u h) ∧
  ctree_bind (Vis e g) h = Vis e (g >>> h) ∧
  ctree_bind (Br k)    h = Br (k >>> h)
Proof
  rw[ctree_compose_def, ctree_bind_def, ctree_bind_fn_def, ctree_push_inj_def]
  >> rw[Once ctree_unfold_thm, ctree_bind_fn_def, ctree_push_inj_def, ctree_compose_def]
  >> FULL_CASE_TAC
  >> rw[FUN_EQ_THM, ctree_bind_INR_id]
QED

Theorem ctree_bind_comb_simps[simp]:
  ctree_bind (Guard t) h = Guard (ctree_bind t h) ∧
  ctree_bind (BrS k) h = BrS (k >>> h) ∧
  ctree_bind (Step t) h = Step (ctree_bind t h) ∧
  ctree_bind ctree_stuck h = ctree_stuck ∧
  ctree_bind ctree_spin h = ctree_spin ∧
  (∀h. ctree_bind (LRet s) h = h (INL s)) ∧
  (∀h. ctree_bind (RRet r) h = h (INR r)) (* We add ∀h. to avoid type issues with the others *)
Proof
  rw[Guard_def, BrS_def, Step_def, LRet_def, RRet_def, FUN_EQ_THM]
  >> qmatch_goalsub_abbrev_tac `ctree_bind t h = t'`
  >> irule $ iffRL ctree_bisimulation
  >> irule_at (Pos hd) rel_exact_lemma >> rw[]
  >> unabbrev_all_tac
  >> gvs[Once ctree_stuck_thm, Once ctree_spin_thm, Guard_def]
QED

Theorem ctree_compose_simps[simp]:
  Tau o f >>> g = Tau o (f >>> g) ∧
  Guard o f >>> g = Guard o (f >>> g) ∧
  Step o f >>> g = Step o (f >>> g)
Proof
  rw[FUN_EQ_THM]
QED

Theorem ctree_bind_right_id[simp]:
  ctree_bind t Ret = t
Proof
  irule $ iffRL ctree_bisimulation
  >> qexists `λp q. p = ctree_bind q Ret` >> rw[]
  >> Cases_on `t` >> gvs[]
QED

Theorem ctree_compose_id[simp]:
  Ret >>> f = f ∧ g >>> Ret = g
Proof
  rw[FUN_EQ_THM]
QED

Theorem ctree_bind_assoc:
  ctree_bind (ctree_bind t h) k = ctree_bind t (h >>> k)
Proof
  irule $ iffRL ctree_strong_bisimulation
  >> qexists `λp q. ∃m.
    p = ctree_bind (ctree_bind m h) k ∧
    q = ctree_bind m (h >>> k)` >> rw[]
  >- metis_tac[]
  >> Cases_on `m` >> gvs[]
  >> metis_tac[]
QED

Theorem ctree_compose_assoc:
  f >>> (g >>> h) = f >>> g >>> h
Proof
  rw[FUN_EQ_THM, ctree_bind_assoc]
QED

Theorem ctree_bind_ret_inv[simp]:
  ctree_bind t k = Ret r <=> ∃r'. t = Ret r' ∧ k r' = Ret r
Proof
  eq_tac >> Cases_on `t` >> rw[]
QED

Theorem ctree_compose_ret_inv:
  f >>> g = Ret <=> ∃f' g'.
    f = Ret o f' ∧
    (∀x. x ∈ IMAGE f' UNIV ==> g x = Ret (g' x)) ∧
    g' o f' = I
Proof
  rw[EQ_IMP_THM, FUN_EQ_THM] >- (
    qexistsl [`λx. case f x of Ret r => r | _ => ARB`,
              `λx. case g x of Ret r => r | _ => ARB`]
    >> rw[] >> rpt CASE_TAC
    >> metis_tac[ctree_distinct, ctree_11]
  ) >> qexists `f' x` >> rw[] >> metis_tac[]
QED

(* Works for any monad, equivalent to the statement that the mapping into the Kleisli category
   is functorial, i.e. respects composition of morphisms *)
Theorem ctree_bind_lift:
  ctree_bind t (Ret o f o g) = ctree_bind (ctree_bind t (Ret o g)) (Ret o f)
Proof
  rw[ctree_bind_assoc] >> cong_tac NONE >> rw[FUN_EQ_THM]
QED

Theorem ctree_compose_lift:
  Ret o f >>> g = g o f
Proof
  rw[FUN_EQ_THM]
QED

Theorem ctree_index_bind_cases:
  ctree_index path (ctree_bind t k) = SOME t' <=>
    (∃u. ctree_index path t = SOME u ∧ (∀r. u ≠ Ret r) ∧ t' = ctree_bind u k) ∨
    (∃p q r. path = p ++ q ∧ ctree_index p t = SOME (Ret r) ∧ ctree_index q (k r) = SOME t')
Proof
  rw[EQ_IMP_THM] >> rpt (pop_assum mp_tac)
  >> rename [`ctree_index path _ = _`]
  >> qid_spec_tac `t`
  >> Induct_on `path` >> rw[]
  >> Cases_on `t` >> gvs[]
  >> (first_x_assum dxrule >> rw[] >- metis_tac[])
  >> disj2_tac
  >> irule_at (Pos hd) $ GSYM (cj 2 APPEND)
  >> rw[]
QED

Theorem ctree_index_bind_rules:
  (ctree_index path t = SOME u ==> ctree_index path (ctree_bind t k) = SOME (ctree_bind u k)) ∧
  (ctree_index p t = SOME (Ret r) ∧ ctree_index q (k r) = SOME t'
    ==> ctree_index (p ++ q) (ctree_bind t k) = SOME t')
Proof
  Cases_on `u` >> rw[]
  >> irule $ iffRL ctree_index_bind_cases >> rw[]
  >- (goal_assum $ dxrule_at Any >> qexists `[]` >> rw[])
  >> metis_tac[]
QED

(* --- 1.3 - Values and retless --- *)

Inductive values:
[~ret:] values (Ret r) r
[~tau:] values u r     ==> values (Tau u) r
[~vis:] values (g a) r ==> values (Vis e g) r
[~br:]  values (k v) r ==> values (Br k) r
End

Theorem values_pcases[local]:
  values (Ret r)   = {r} ∧
  values (Tau u)   = values u ∧
  values (Vis e g) = BIGUNION {values (g a) | a | T} ∧
  values (Br k)    = BIGUNION {values (k v) | v | T}
Proof
  rw[EXTENSION, IN_DEF] >> gvs[Once values_cases] >> metis_tac[]
QED

Theorem values_combs[local]:
  values (Guard t) = values t ∧
  values (BrS k)   = values (Br k) ∧
  values (Step t)  = values t ∧
  values (LRet s)  = {INL s} ∧
  values (RRet r)  = {INR r}
Proof
  rw[Guard_def, BrS_def, Step_def, LRet_def, RRet_def, values_pcases, BIGUNION]
QED

Theorem values_stuck_spin[local]:
  values ctree_stuck = EMPTY ∧
  values ctree_spin  = EMPTY
Proof
  rw[EXTENSION, IN_DEF]
  >> Induct_on `values` >> rw[]
  >> rw[]
  >> metis_tac[]
QED

Theorem values_simps[simp] =
  LIST_CONJ [values_pcases, values_combs, values_stuck_spin]
  |> SIMP_RULE std_ss [GSYM CONJ_ASSOC];

Theorem values_bind_simp[simp]:
  values (ctree_bind p k) r' <=> ∃r. values p r ∧ values (k r) r'
Proof
  eq_tac >- (
    qid_spec_tac `p`
    >> Induct_on `values` >> rw[] >> rw[]
    >> Cases_on `p` >> gvs[]
    >> metis_tac[IN_DEF]
  )
  >> rw[] >> rpt (first_x_assum mp_tac)
  >> Induct_on `values` >> rw[]
  >> metis_tac[IN_DEF]
QED

Theorem values_bind:
  values (ctree_bind p k) = BIGUNION {values (k r) | r ∈ values p}
Proof
  rw[EXTENSION, IN_DEF] >> metis_tac[]
QED

Theorem values_bind_eq[simp]:
  ctree_bind t k = ctree_bind t k' <=> ∀x. x ∈ values t ==> k x = k' x
Proof
  rw[EQ_IMP_THM, IN_DEF]
  >- (rpt (pop_assum mp_tac) >> Induct_on `values` >> rw[FUN_EQ_THM])
  >> irule $ iffRL ctree_strong_bisimulation
  >> qexists `λp q. ∃m. (∀x. values m x ==> k x = k' x) ∧
    p = ctree_bind m k ∧ q = ctree_bind m k'` >> rw[]
  >- metis_tac[] >> gvs[]
  >> Cases_on `m` >> gvs[] >> metis_tac[IN_DEF]
QED

Theorem values_bind_eq_ret:
  (∀x. x ∈ values t ==> k x = Ret x) ==> ctree_bind t k = t
Proof
  rw[] >> `ctree_bind t k = ctree_bind t Ret` suffices_by rw[Excl "values_bind_eq"]
  >> rw[Excl "ctree_bind_right_identity"]
  >> metis_tac[IN_DEF]
QED

Theorem values_index:
  values t = {r | ∃path. ctree_index path t = SOME (Ret r)}
Proof
  rw[FUN_EQ_THM, EQ_IMP_THM]
  >> pop_assum mp_tac
  >- (Induct_on `values` >> rw[] >> metis_tac[ctree_index_rules])
  >> qid_spec_tac `t` >> Induct_on `path` >> rw[]
  >> Cases_on `t` >> Cases_on `h` >> gvs[]
  >> metis_tac[IN_DEF]
QED

Theorem values_index_subset:
  ctree_index path t = SOME t' ==> values t' ⊆ values t
Proof
  rw[values_index, SUBSET_DEF]
  >> qexists `path ++ path'`
  >> rw[ctree_index_append, OPTION_MCOMP_def]
QED

CoInductive retless:
[~tau:] retless u ==> retless (Tau u)
[~vis:] (∀a. retless (g a)) ==> retless (Vis e g)
[~br:] (∀v. retless (k v)) ==> retless (Br k)
End

Theorem not_retless_ret[local]:
  ¬retless (Ret r)
Proof
  spose_not_then strip_assume_tac
  >> gvs[Once retless_cases]
QED

Theorem retless_tauvisbr[local]:
  (retless (Tau u)   <=> retless u) ∧
  (retless (Vis e g) <=> ∀a. retless (g a)) ∧
  (retless (Br k)    <=> ∀v. retless (k v))
Proof
  rw[] >> gvs[Once retless_cases]
QED

Theorem retless_iff_not_values:
  retless p <=> ∀r'. ¬values p r'
Proof
  rw[EQ_IMP_THM] >- (
    first_x_assum mp_tac
    >> Induct_on `values` >> rw[]
    >> metis_tac[not_retless_ret, retless_tauvisbr]
  )
  >> irule retless_coind
  >> qexists `λu. ∀r'. ¬values u r'` >> rw[]
  >> rename[`∀r'. ¬values u r'`] >> Cases_on `u`
  >> gvs[] >> metis_tac[IN_DEF]
QED

Theorem retless_iff_empty:
  retless p <=> values p = EMPTY
Proof
  rw[EXTENSION, IN_DEF, retless_iff_not_values]
QED

Theorem retless_combs[local]:
  (retless (Guard t) <=> retless t) ∧
  (retless (BrS k)   <=> ∀v. retless (k v)) ∧
  (retless (Step t)  <=> retless t) ∧
  retless ctree_stuck ∧
  retless ctree_spin ∧
  ¬retless (LRet s) ∧
  ¬retless (RRet r)
Proof
  rw[Guard_def, BrS_def, Step_def, LRet_def, RRet_def, retless_iff_not_values]
  >> metis_tac[IN_DEF]
QED

Theorem retless_simps[simp] =
  LIST_CONJ (
    not_retless_ret ::
    CONJ_LIST 3 retless_tauvisbr @
    CONJ_LIST 7 retless_combs
  )

Theorem retless_bind:
  retless (ctree_bind p k) <=> ∀r. values p r ==> retless (k r)
Proof
  rw[retless_iff_not_values] >> metis_tac[]
QED

Theorem retless_bind:
  retless (ctree_bind p k) <=> ∀r. values p r ==> retless (k r)
Proof
  rw[retless_iff_not_values] >> metis_tac[]
QED

Theorem retless_thm:
  retless p <=> ∃R. R p ∧ ∀t. R t ==>
    (∃u.   t = Tau u   ∧ R u) ∨
    (∃e g. t = Vis e g ∧ ∀a. R (g a)) ∨
    (∃k.   t = Br k    ∧ ∀v. R (k v))
Proof
  rw[EQ_IMP_THM] >- (
    qexists `retless` >> rw[]
    >> Cases_on `t` >> gvs[]
  )
  >> last_x_assum mp_tac >> qid_spec_tac `p`
  >> ho_match_mp_tac retless_coind >> rw[]
QED

Theorem retless_strong_thm:
  retless p <=> ∃R. R p ∧ ∀t. R t ==>
    (∃u.   t = Tau u   ∧ (R u ∨ retless u)) ∨
    (∃e g. t = Vis e g ∧ ∀a. R (g a) ∨ retless (g a)) ∨
    (∃k.   t = Br k    ∧ ∀v. R (k v) ∨ retless (k v))
Proof
  rw[EQ_IMP_THM] >- (
    qexists `retless` >> rw[]
    >> Cases_on `t` >> gvs[]
  )
  >> rw[retless_thm]
  >> qexists `λt. R t ∨ retless t` >> rw[]
  >> Cases_on `t` >> gvs[]
QED

Theorem retless_strong_coind:
  (∀t. R t ==>
    (∃u.   t = Tau u   ∧ (R u ∨ retless u)) ∨
    (∃e g. t = Vis e g ∧ ∀a. R (g a) ∨ retless (g a)) ∨
    (∃k.   t = Br k    ∧ ∀v. R (k v) ∨ retless (k v)))
  ==> ∀t. R t ==> retless t
Proof
  rw[] >> irule $ iffRL retless_strong_thm
  >> qexists `R` >> rw[]
QED

(* ctree_bisimulation_bind is bisimulation up to bind (allows us to reason about
   big steps rather than having to fall back to reasoning on constructors), with a
   few modifications to make proofs cleaner. In particular, we only care that the
   continuations agree whenever they are used, so we can assume that x is a value
   of the ctree we are binding. Additionally, we have pushed the bind back one level,
   so rather than a case split of four constructors we just reason about one overall
   bind (we regain productivity from the m ≠ Ret r condition, and we add reflexivity
   to recover equality between Rets) *)
Theorem ctree_bisimulation_bind_lemma[local]:
  (∀x. x ∈ values t ==> R (f x) (f' x) ∨ f x = f' x) ==>
    (R (ctree_bind (t: ('a, 'b, 'c, 'd) ctree) f) (ctree_bind t f') ∨
    ∃(m: ('a, 'b, 'c, 'd) ctree) h h'.
      ctree_bind t f = ctree_bind m h ∧ ctree_bind t f' = ctree_bind m h' ∧
      (∀r. m ≠ Ret r) ∧
      (∀x. x ∈ values m ==> R (h x) (h' x) ∨ h x = h' x)
  ) ∨ ∀x. x ∈ values t ==> f x = f' x
Proof
  Cases_on `∃r. t = Ret r` >> rw[] >> gvs[]
  >> disj1_tac >> disj2_tac
  >> qexistsl [`t`, `f`, `f'`] >> rw[]
QED

Theorem ctree_bisimulation_bind:
  p0 = q0 <=> ∃R. R p0 q0 ∧
    ∀p q. R p q ==> p = q ∨
      ∃(m: ('a, 'b, 'c, 'e) ctree) f f'.
        p = ctree_bind m f ∧ q = ctree_bind m f' ∧
        (∀r. m ≠ Ret r) ∧
        (∀x. x ∈ values m ==> R (f x) (f' x) ∨ f x = f' x)
Proof
  rw[EQ_IMP_THM]
  >- (qexists `(=)` >> rw[])
  >> irule $ iffRL ctree_strong_bisimulation
  >> qexists `λp q. R p q ∨ ∃m f f'.
    p = ctree_bind m f ∧ q = ctree_bind m f' ∧
    (∀r. m ≠ Ret r) ∧
    (∀x. x ∈ values m ==> R (f x) (f' x) ∨ f x = f' x)` >> rw[]
  >> first_x_assum dxrule >> gvs[] >> rw[]
  >> Cases_on `m` >> gvs[SF DNF_ss] >> rw[]
  >> irule ctree_bisimulation_bind_lemma >> rw[]
  >> metis_tac[]
QED

Theorem ctree_bisimulation_bind_coind:
  (∀p q. R p q ==> p = q ∨
    ∃(m: ('a, 'b, 'c, 'e) ctree) f f'.
      p = ctree_bind m f ∧ q = ctree_bind m f' ∧
      (∀r. m ≠ Ret r) ∧
      (∀x. x ∈ values m ==> R (f x) (f' x) ∨ f x = f' x))
  ==> ∀p0 q0. R p0 q0 ==> p0 = q0
Proof
  rw[] >> irule $ iffRL ctree_bisimulation_bind
  >> qexists `R` >> rw[]
QED

Theorem retless_bind_thm:
  retless p0 <=> ∃R. R p0 ∧ ∀p. R p ==> retless p ∨ ∃m f.
    p = ctree_bind m f ∧
    (∀r. m ≠ Ret r) ∧
    (∀s. s ∈ values m ==> R (f s) ∨ retless (f s))
Proof
  rw[EQ_IMP_THM]
  >- (qexists `retless` >> rw[])
  >> irule $ iffRL retless_strong_thm
  >> qexists `λt. retless t ∨ ∃m f.
    t = ctree_bind m f ∧
    (∀r. m ≠ Ret r) ∧
    (∀s. s ∈ values m ==> R (f s) ∨ retless (f s))` >> rw[]
  >- (Cases_on `t` >> gvs[])
  >> Cases_on `m` >> rw[]
  >| map Cases_on [`∃r. u = Ret r`, `∃r. g a = Ret r`, `∃r. k v = Ret r`]
  >> rw[] >> gvs[SF DNF_ss] >>~ [`_ = Ret r`]
  >- (first_x_assum $ qspecl_then [`r`, `a`] strip_assume_tac >> gvs[])
  >- (first_x_assum $ qspecl_then [`r`, `v`] strip_assume_tac >> gvs[])
  >> metis_tac[]
QED

Theorem retless_bind_coind:
  (∀p. R p ==> ∃m f.
    p = ctree_bind m f ∧
    (∀r. m ≠ Ret r) ∧
    (∀s. s ∈ values m ==> R (f s) ∨ retless (f s)))
  ==> ∀p0. R p0 ==> retless p0
Proof
  rw[] >> irule $ iffRL retless_bind_thm
  >> qexists `R` >> rw[]
QED

(* --- 1.4 - Iter --- *)

Definition ctree_iter_def:
  ctree_iter body seed = ctree_unfold (λn.
    case n of
    | Ret (INL i) => Guard' (body i)
    | Ret (INR r) => Ret' r
    | Tau u       => Tau' u
    | Vis e g     => Vis' e g
    | Br  k       => Br'  k
  ) (body seed)
End

Definition ctree_iter_fn_def:
  ctree_iter_fn body lr =
    case lr of
    | INL i => Guard (ctree_iter body i)
    | INR r => Ret r
End

Theorem ctree_iter_fn_simp[simp]:
  ctree_iter_fn body (INL i) = Guard (ctree_iter body i) ∧
  ctree_iter_fn body (INR r) = Ret r
Proof
  rw[ctree_iter_fn_def]
QED

Theorem ctree_iter_fn_eq[simp]:
  (ctree_iter_fn body lr = Ret r <=> ∃_. lr = INR r) ∧
  (ctree_iter_fn body lr ≠ Tau u) ∧
  (ctree_iter_fn body lr ≠ Vis e g) ∧
  (ctree_iter_fn body lr = Br k    <=> ∃i. lr = INL i ∧ k = (λv. ctree_iter body i)) ∧
  (ctree_iter_fn body lr = Guard t <=> ∃i. lr = INL i ∧ t = ctree_iter body i)
Proof
  rw[ctree_iter_fn_def]
  >> Cases_on `lr` >> rw[]
  >> metis_tac[]
QED

Theorem ctree_iter_fn_thm:
  ctree_iter body seed = ctree_bind (body seed) (ctree_iter_fn body)
Proof
  rw[ctree_iter_def]
  >> qmatch_goalsub_abbrev_tac `ctree_unfold f _ = ctree_bind _ _`
  >> rw[Once ctree_strong_bisimulation]
  >> qexists `λp q. ∃v. p = ctree_unfold f v ∧ q = ctree_bind v (ctree_iter_fn body)`
  >> rw[] >- metis_tac[] >~ [`Br`]
  >> unabbrev_all_tac >> gvs[AllCaseEqs()]
  >> rw[ctree_iter_def] >> metis_tac[]
QED

(* This is mainly provided for use with the bind theorems, which is why we do not
   rewrite with ctree_bind_assoc. This will loop, so Once needs to be applied when
   rewriting. For most cases, ctree_iter_fn_thm is the desired theorem. *)
Theorem ctree_iter_thm:
  ctree_iter body seed =
  ctree_bind
    (ctree_bind (body seed) (sum_case (Guard o LRet) RRet))
    (sum_case (ctree_iter body) Ret)
Proof
  rw[ctree_iter_fn_thm, ctree_bind_assoc]
  >> Cases_on `x` >> rw[ctree_iter_fn_thm]
QED

Theorem ctree_iter_LRet_lemma[local]:
  ∀p q. (p = ctree_iter LRet s ∧ q = ctree_stuck) ==> p = q
Proof
  ho_match_mp_tac ctree_bisimulation_coind
  >> rw[] >> gvs[Once ctree_iter_fn_thm]
QED

Theorem ctree_iter_LRet[simp] = ctree_iter_LRet_lemma |> SIMP_RULE std_ss [];

Definition iter_vars_def:
  iter_vars body = {y | ∃s. INL y ∈ values (body s)}
End

(* Two ctree_iters are the same if their bodies agree on all iter_vars *)
Theorem ctree_iter_eq:
  ∀(body: 'e -> ('a, 'b, 'c, 'e + 'd) ctree) body'.
  (∀s. s ∈ iter_vars body ∧ s ∈ iter_vars body' ==> body s = body' s) ∧
  seed ∈ iter_vars body ∧ seed ∈ iter_vars body'
    ==> ctree_iter body seed = ctree_iter body' seed
Proof
  rw[] >> (ctree_bisimulation_bind
  |> INST_TYPE [``:'e`` |-> ``:'e + 'd``]
  |> iffRL |> irule >> rw[])
  >> qexists `λp q. ∃s.
    s ∈ iter_vars body ∩ iter_vars body' ∧
    p = ctree_iter body s ∧ q = ctree_iter body' s` >> rw[]
  >- metis_tac[]
  >> Cases_on `∃r. body s = RRet r` >- (
    disj1_tac >> rw[ctree_iter_fn_thm]
    >> Cases_on `x` >> gvs[]
  )
  >> disj2_tac
  >> rw[Once ctree_iter_thm]
  >> irule_at (Pos hd) EQ_REFL
  >> rw[Once ctree_iter_thm, Excl "values_bind_eq"]
  >> irule_at (Pos hd) EQ_REFL
  >> rw[]
  >- (CASE_TAC >> rw[] >> metis_tac[RRet_def])
  >> gvs[values_bind]
  >> rpt FULL_CASE_TAC >> gvs[iter_vars_def]
  >> metis_tac[]
QED

(* Variant of the above for when the starting seed is unique *)
Theorem ctree_iter_eq_initial:
  body seed = body' seed ∧
  (∀s. s ∈ iter_vars body ∩ iter_vars body' ==> body s = body' s)
  ==> ctree_iter body seed = ctree_iter body' seed
Proof
  rw[ctree_iter_fn_thm]
  >> Cases_on `x` >> rw[]
  >> irule ctree_iter_eq
  >> rw[iter_vars_def]
  >> metis_tac[]
QED

(* Alpha equivalence of the iteration variable *)
Theorem ctree_iter_alpha_lemma[local]:
  ∀(body: 'e -> ('a, 'b, 'c, 'e + 'd) ctree).
  iter_vars body ⊆ seeds ∧ INJ f seeds UNIV ==>
  ∀p q. (∃seed.
    seed ∈ seeds ∧
    p = ctree_iter body seed ∧
    q = ctree_iter (Ret o LINV f seeds >>> body >>> Ret o SUM_MAP f I) (f seed)
  ) ==> p = q
Proof
  strip_tac >> strip_tac
  >> (ctree_bisimulation_bind_coind
  |> INST_TYPE [``:'e`` |-> ``:'e + 'd``]
  |> ho_match_mp_tac >> rw[])
  >> qmatch_goalsub_abbrev_tac `ctree_iter body seed = ctree_iter g (f seed)`
  >> Cases_on `∃r. body seed = RRet r` >- (
    disj1_tac >> rw[ctree_iter_fn_thm] >> gvs[SUM_MAP_EQ, RRet_def, Abbr `g`]
    >> metis_tac[LINV_DEF]
  )
  >> disj2_tac
  >> rw[Once ctree_iter_thm]
  >> irule_at (Pos hd) EQ_REFL
  >> qexists `sum_case (ctree_iter g o f) Ret`
  >> rw[] >- (
    rw[Abbr `g`, ctree_iter_fn_thm, ctree_bind_assoc]
    >> DEP_REWRITE_TAC[LINV_DEF]
    >> rw[] >- metis_tac[]
    >> CASE_TAC >> rw[ctree_iter_fn_thm, ctree_bind_assoc]
  )
  >> CASE_TAC >> rw[]
  >- metis_tac[RRet_def]
  >> disj1_tac >> irule_at (Pos last) EQ_REFL
  >> rw[] >> gvs[values_bind]
  >> FULL_CASE_TAC >> gvs[]
  >> irule $ iffLR SUBSET_DEF
  >> goal_assum $ dxrule_at (Pos last)
  >> rw[iter_vars_def] >> metis_tac[]
QED

Theorem ctree_iter_alpha:
  ∀seeds f (body: 'e -> ('a, 'b, 'c, 'e + 'd) ctree) body' seed seed'.
  iter_vars (body: 'e -> ('a, 'b, 'c, 'e + 'd) ctree) ∪ {seed} ⊆ seeds ∧
  INJ f seeds UNIV ∧
  seed' = f seed ∧
  (∀s. s ∈ seeds ==> body' (f s) = ctree_bind (body s) (Ret o SUM_MAP f I))
    ==> ctree_iter body seed = ctree_iter body' seed'
Proof
  rw[] >> irule ctree_iter_alpha_lemma
  >> rpt (goal_assum $ drule_at Any)
  >> rw[] >> irule ctree_iter_eq_initial
  >> rw[ctree_compose_lift] >- (
    gvs[iter_vars_def, values_bind]
    >> Cases_on `r` >> gvs[]
    >> DEP_REWRITE_TAC[LINV_DEF]
    >> `x ∈ seeds` suffices_by metis_tac[]
    >> irule $ iffLR SUBSET_DEF
    >> goal_assum $ dxrule_at (Pos last)
    >> rw[iter_vars_def]
    >> metis_tac[]
  )
  >> DEP_REWRITE_TAC[LINV_DEF]
  >> metis_tac[]
QED

(* For common use cases, it is easier to just prove the bodies are equal at all points *)
Theorem ctree_iter_alpha_univ:
  ∀f. INJ f UNIV UNIV ∧ seed' = f seed ∧
    body' o f = body >>> Ret o SUM_MAP f I
  ==> ctree_iter body seed = ctree_iter body' seed'
Proof
  rw[] >> irule ctree_iter_alpha
  >> qexistsl [`f`, `UNIV`]
  >> rw[] >> gvs[FUN_EQ_THM]
QED

Definition ctree_bimap_def:
  ctree_bimap f g = sum_case (f >>> LRet) (g >>> RRet)
End

Theorem ctree_bimap_thm[simp] =
  ctree_bimap_def |> SIMP_RULE std_ss [FUN_EQ_THM, sum_case_def, ctree_compose_thm]

Theorem ctree_bind_iter_lemma[local]:
  ∀p q. (∃s.
    p = ctree_bind (ctree_iter f s) k ∧
    q = ctree_iter ((f: 's -> ('a, 'b, 'c, 's + 'r) ctree) >>> ctree_bimap Ret k) s
  ) ==> p = q
Proof
  ctree_bisimulation_bind_coind
  |> INST_TYPE [``:'e`` |-> ``:'s + 'r``]
  |> ho_match_mp_tac
  >> rw[ctree_iter_fn_thm, ctree_iter_fn_def, ctree_bind_assoc]
  >> Cases_on `∃r. f s = Ret (INR r)` >> rw[] >> rw[] >- (
    disj1_tac >> rw[ctree_bind_assoc]
    >> irule EQ_SYM >> irule values_bind_eq_ret
    >> rw[]
  )
  >> disj2_tac
  >> qexistsl [
    `ctree_bind (f s) (sum_case (Guard o LRet) RRet)`,
    `sum_case (ctree_iter f >>> k) k`,
    `sum_case (ctree_iter (f >>> ctree_bimap Ret k)) k`
  ]
  >> rw[ctree_bind_assoc]
  >> CASE_TAC >> rw[ctree_bind_assoc]
  >- (irule values_bind_eq_ret >> rw[])
  >> rw[ctree_iter_fn_thm, ctree_bind_assoc]
  >> metis_tac[]
QED

Theorem ctree_bind_iter:
  ctree_bind (ctree_iter f s) k = ctree_iter (f >>> ctree_bimap Ret k) s
Proof
  metis_tac[ctree_bind_iter_lemma]
QED

Theorem ctree_compose_iter:
  ctree_iter f >>> g = ctree_iter (f >>> ctree_bimap Ret g)
Proof
  rw[FUN_EQ_THM, ctree_bind_iter]
QED

(* An alternate form of iteration, the main one when studying traced monoidal categories.
   See itrees paper for more information. *)
Definition ctree_loop_def:
  ctree_loop body seed = ctree_iter (body >>> Ret o SUM_MAP INL I) (INR seed)
End

(* --- 1.5 - Height --- *)

Definition ctree_heights_def:
  ctree_heights t = {LENGTH path | IS_SOME (ctree_index path t)}
End

Theorem ctree_heights_zero[simp]:
  0 ∈ ctree_heights t
Proof
  rw[ctree_heights_def]
QED

Theorem ctree_heights_nonempty[simp]:
  ctree_heights t ≠ ∅
Proof
  rw[EXTENSION] >> irule_at Any ctree_heights_zero
QED

Theorem ctree_heights_closed_below[local]:
  n ≤ m ∧ m ∈ ctree_heights t ==> n ∈ ctree_heights t
Proof
  rw[ctree_heights_def, IS_SOME_EXISTS]
  >> qexists `TAKE n path` >> rw[]
  >> metis_tac[TAKE_DROP, ctree_index_append_eq]
QED

Theorem ctree_heights_cases:
  ∀t.
    (FINITE (ctree_heights t) ∧ ∃n. ctree_heights t = {k | k ≤ n}) ∨
    (INFINITE (ctree_heights t) ∧ ctree_heights t = UNIV)
Proof
  rw[] >> Cases_on `FINITE (ctree_heights t)` >> rw[] >- (
    qexists `MAX_SET (ctree_heights t)`
    >> rw[EXTENSION, EQ_IMP_THM, X_LE_MAX_SET]
    >> irule ctree_heights_closed_below
    >> goal_assum $ dxrule_at (Pos hd)
    >> rw[MAX_SET_IN_SET]
  )
  >> rw[EXTENSION]
  >> dxrule_at Concl $ iffRL FINITE_UPPER_BOUNDED >> rw[NOT_LE]
  >> metis_tac[ctree_heights_closed_below, LT_IMP_LE]
QED

Theorem ctree_heights_ret[local]:
  ctree_heights (Ret r) = {0}
Proof
  rw[ctree_heights_def, EXTENSION, IS_SOME_EXISTS]
QED

Theorem ctree_heights_simps[simp]:
  ctree_heights (Ret r) = {0} ∧
  ctree_heights (Tau u) = {0} ∪ IMAGE SUC (ctree_heights u) ∧
  ctree_heights (Vis e g) = {0} ∪ IMAGE SUC (BIGUNION {ctree_heights (g a) | a | T}) ∧
  ctree_heights (Br k) = {0} ∪ IMAGE SUC (BIGUNION {ctree_heights (k v) | v | T})
Proof
  rw[ctree_heights_ret] >> (
    irule SUBSET_ANTISYM >> rw[SUBSET_DEF, ctree_heights_def, IS_SOME_EXISTS]
    >- (Cases_on `path` >> gvs[SF DNF_ss] >> metis_tac[])
    >> gvs[SPECIFICATION]
  )
  >> qrefine `h::p` >> rw[] >> metis_tac[]
QED

Theorem ctree_heights_combs_simps[simp]:
  ctree_heights (Guard t) = {0} ∪ IMAGE SUC (ctree_heights t) ∧
  ctree_heights (BrS k) = {0; 1} ∪ IMAGE (SUC o SUC) (BIGUNION {ctree_heights (k v) | v | T}) ∧
  ctree_heights (Step t) = {0; 1} ∪ IMAGE (SUC o SUC) (ctree_heights t) ∧
  ctree_heights (LRet s) = {0} ∧
  ctree_heights (RRet r') = {0}
Proof
  rw[Guard_def, BrS_def, Step_def, LRet_def, RRet_def]
  >> `{0; 1} = {0} ∪ {1}` by rw[EXTENSION]
  >> rw[GSYM UNION_ASSOC] >> cong_tac (SOME 1)
  >- (cong_tac (SOME 1) >> rw[EXTENSION] >> metis_tac[])
  >> rw[IMAGE_o]
  >> irule SUBSET_ANTISYM >> rw[SUBSET_DEF]
  >> gvs[SF DNF_ss]
  >> goal_assum $ dxrule_at Any
QED

Theorem ctree_heights_stuck_spin_simps[simp]:
  ctree_heights ctree_stuck = UNIV ∧
  ctree_heights ctree_spin = UNIV
Proof
  rw[ctree_heights_def, EXTENSION, IS_SOME_EXISTS]
  >> Induct_on `x` >> rw[]
  >| map qexists [`brE v::path`, `tauE::path`] >> rw[]
QED

Definition ctree_height_def:
  ctree_height t =
    if FINITE (ctree_heights t)
    then SOME (MAX_SET (ctree_heights t))
    else NONE
End

Theorem ctree_heights_nonempty_lemma:
  {ctree_heights (f x) | x | T} ≠ ∅ ∧
  {ctree_heights (f x) | x | T} ≠ {∅}
Proof
  rw[] >> irule $ CONTRAPOS (iffRL DIFF_EMPTY_IMP_EQ) >> rw[]
  >> rw[FUN_EQ_THM] >> metis_tac[]
QED

Theorem ctree_height_zero[simp]:
  ctree_height t = SOME 0 <=> ∃r. t = Ret r
Proof
  Cases_on `t` >> rw[ctree_height_def, MAX_SET_UNION]
  >> spose_not_then strip_assume_tac
  >> last_x_assum mp_tac
  >> DEP_REWRITE_TAC[MAX_SET_IMAGE_SUC] >> rw[]
  >> rw[ctree_heights_nonempty_lemma]
QED

Theorem ctree_height_ret_tau[simp]:
  ctree_height (Ret r) = SOME 0 ∧
  ctree_height (Tau u) = OPTION_MAP SUC (ctree_height u)
Proof
  rw[ctree_height_def]
  >> DEP_REWRITE_TAC[MAX_SET_UNION, MAX_SET_IMAGE_SUC]
  >> rw[]
QED

Theorem ctree_height_LRRet[simp]:
  ctree_height (LRet s) = SOME 0 ∧ ctree_height (RRet r) = SOME 0
Proof
  rw[LRet_def, RRet_def]
QED

Theorem ctree_height_eq_some[simp]:
  (ctree_height (Tau u) = SOME n <=> ∃m. n = SUC m ∧ ctree_height u = SOME m) ∧
  (ctree_height (Vis e g) = SOME n <=> ∃m. n = SUC m ∧
    (∃a. ctree_height (g a) = SOME m) ∧
    ∀a. ∃j. ctree_height (g a) = SOME j ∧ j ≤ m) ∧
  (ctree_height (Br k) = SOME n <=> ∃m. n = SUC m ∧
    (∃v. ctree_height (k v) = SOME m) ∧
    ∀v. ∃j. ctree_height (k v) = SOME j ∧ j ≤ m)
Proof
  rw[] >- metis_tac[] >> (
    Cases_on `n` >- rw[] >> gvs[SF DNF_ss]
    >> rename[`SOME (SUC n)`] >> eq_tac >- (
      rw[ctree_height_def, SF DNF_ss, MAX_SET_UNION]
      >> first_x_assum mp_tac
      >> DEP_REWRITE_TAC[MAX_SET_IMAGE_SUC] >> rw[ctree_heights_nonempty_lemma]
      >> dxrule MAX_SET_BIGUNION >> rw[SF DNF_ss]
      >> metis_tac[]
    )
    >> strip_tac >> gvs[ctree_height_def]
    >> conj_asm1_tac >> rw[]
    >- (irule FINITE_SET_OF_SETS_UPPER_BOUNDED >> rw[SF DNF_ss] >> metis_tac[])
    >- metis_tac[]
    >> rw[MAX_SET_UNION, MAX_SET_IMAGE_SUC, ctree_heights_nonempty_lemma]
    >> gvs[SF DNF_ss]
    >> DEP_REWRITE_TAC[MAX_SET_TEST_IFF] >> rw[]
    >> rw[ctree_heights_nonempty_lemma, SF DNF_ss]
    >- (irule_at Any MAX_SET_IN_SET >> rw[])
    >> metis_tac[X_LE_MAX_SET, LE_TRANS]
  )
QED

Theorem ctree_height_eq_some_comb[simp]:
  (ctree_height (Guard t) = SOME n <=> ∃m. n = SUC m ∧ ctree_height t = SOME m) ∧
  (ctree_height (BrS k) = SOME n <=> ∃m. n = SUC (SUC m) ∧
    (∃v. ctree_height (k v) = SOME m) ∧
    ∀v. ∃j. ctree_height (k v) = SOME j ∧ j ≤ m) ∧
  (ctree_height (Step t) = SOME n <=> ∃m. n = SUC (SUC m) ∧ ctree_height t = SOME m)
Proof
  rw[Guard_def, Step_def, BrS_def, SF DNF_ss] >> metis_tac[LE_REFL]
QED

Theorem ctree_height_stuck_spin[simp]:
  ctree_height ctree_stuck = NONE ∧ ctree_height ctree_spin = NONE
Proof
  rw[ctree_height_def]
QED

Theorem ctree_height_1:
  ctree_height t = SOME 1 <=>
    (∃r.   t = Tau (Ret r)) ∨
    (∃e f. t = Vis e (Ret o f)) ∨
    (∃f.   t = Br (Ret o f))
Proof
  Cases_on `t` >> rw[EQ_IMP_THM, FUN_EQ_THM] >> metis_tac[]
QED

Theorem not_ret_imp_ctree_bind_height_1:
  (∀r. t ≠ Ret r) ==> ∃(t': ('a, 'b, 'c, 'a + 'b) ctree) k.
    ctree_height t' = SOME 1 ∧
    (∀r. t' ≠ Ret r) ∧ t = ctree_bind t' k
Proof
  Cases_on `t` >> rw[ctree_height_1, SF DNF_ss]
  >- (qexists `λv. u` >> rw[])
  >- (qexistsl [`sum_case g ARB`, `INL`] >> rw[FUN_EQ_THM])
  >> qexistsl [`sum_case ARB k`, `INR`] >> rw[FUN_EQ_THM]
QED


(* -----------------------------------------------------------------------------------
     2. Bisimulation
   -----------------------------------------------------------------------------------
   This section defines the labelled transition system (LTS) associated with ctrees,
   which allows us to define the equivalence sbisim, essentially making branches from
   Br nodes invisible. This makes ctrees nondeterministic, which is the first main
   difference with itrees.
   -----------------------------------------------------------------------------------*)

(* --- 2.0 - ctree_lts --- *)

Datatype:
  ctree_label = val 'r | tau | obs 'e 'a
End

Theorem ctree_label_distinct_11[local] =
  map (fn f => f ``:('a, 'b, 'c) ctree_label``) [TypeBase.distinct_of, TypeBase.one_one_of]
  |> LIST_CONJ
  |> SIMP_RULE std_ss [GSYM CONJ_ASSOC]

Inductive ctree_lts:
[~ret:] ctree_lts (Ret r) (val r) ctree_stuck
[~tau:] ctree_lts (Tau u) tau u
[~vis:] ctree_lts (Vis e g) (obs e a) (g a)
[~br:] ctree_lts (k v) l t ==> ctree_lts (Br k) l t
End

Theorem ctree_lts_simps[simp] = ctree_lts_cases |> Q.SPECL [`p`, `l`, `q`] |> cases_to_simp `p`;

Theorem ctree_lts_comb_simps[simp]:
  (ctree_lts (Guard t) l q <=> ctree_lts t l q) ∧
  (ctree_lts (BrS k) l q <=> l = tau ∧ ∃v. q = k v) ∧
  (ctree_lts (Step t) l q <=> l = tau ∧ q = t) ∧
  (ctree_lts ctree_spin l q <=> l = tau ∧ q = ctree_spin)
Proof
  rw[Guard_def, BrS_def, Step_def, Once ctree_spin_thm]
  >> metis_tac[]
QED

(* Used for metis_tac/resolve_then *)
Theorem ctree_lts_comb_rules:
  ctree_lts (BrS k) tau (k v) ∧
  ctree_lts (Step t) tau t ∧
  ctree_lts ctree_spin tau ctree_spin
Proof
  rw[] >> metis_tac[]
QED

Theorem no_ctree_lts_iff_stuck:
  (∀l t'. ¬ctree_lts t l t') <=> t = ctree_stuck
Proof
  rw[EQ_IMP_THM] >- (
    irule $ iffRL ctree_bisimulation
    >> qexists `λp q. (∀l t'. ¬ctree_lts p l t') ∧ q = ctree_stuck`
    >> rw[]
  )
  >> Induct_on `ctree_lts` >> rw[]
  >> metis_tac[]
QED

Theorem not_ctree_lts_stuck[simp]:
  ¬ctree_lts ctree_stuck l q
Proof
  metis_tac[no_ctree_lts_iff_stuck]
QED

Theorem ctree_lts_val_stuck:
  ctree_lts p (val r) q <=> ctree_lts p (val r) ctree_stuck ∧ q = ctree_stuck
Proof
  eq_tac
  >- (Induct_on `ctree_lts` >> rw[] >> metis_tac[])
  >> rw[]
QED

(* A useful thing to note for when we later prove some theorems for when a branch node
   is sbisim to a Vis node. Basically, any (obs e a) label must come from some Vis node,
   so if (obs e a) is a label then (obs e a') must also be a label for any other a', by
   starting from that same Vis node and taking the a' path. *)
Theorem ctree_lts_obs_carry:
  ctree_lts p (obs e a) p' ==> ∀a'. ∃q'. ctree_lts p (obs e a') q'
Proof
  Induct_on `ctree_lts` >> rw[]
  >> metis_tac[]
QED

Definition invisible_edge_def:
  invisible_edge t = ∃v. t = brE v
End

Theorem invisible_edge_thm[simp]:
  ¬invisible_edge (tauE) ∧ ¬invisible_edge (visE a) ∧ invisible_edge (brE v)
Proof
  rw[invisible_edge_def]
QED

Theorem ctree_lts_index_rules:
  ∀p.
    (∀k. p' ≠ Br k) ∧ EVERY invisible_edge path ∧
    ctree_index path p = SOME p' ∧ ctree_lts p' l q
  ==> ctree_lts p l q
Proof
  Induct_on `path` >> rw[]
  >> Cases_on `h` >> gvs[]
  >> Cases_on `p` >> gvs[]
  >> metis_tac[]
QED

Theorem ctree_lts_index_cases:
  ctree_lts p l q <=> ∃path p'.
    (∀k. p' ≠ Br k) ∧ EVERY invisible_edge path ∧
    ctree_index path p = SOME p' ∧ ctree_lts p' l q
Proof
  reverse (rw[EQ_IMP_THM])
  >- (dxrule_all ctree_lts_index_rules >> rw[])
  >> rpt (pop_assum mp_tac)
  >> Induct_on `ctree_lts` >> rw[] >~ [`ctree_index _ (Br k)`]
  >- (qexists `brE v::path` >> rw[] >> metis_tac[])
  >> qexists `[]` >> rw[]
QED

Theorem ctree_lts_values:
  ctree_lts p l q ==> values q ⊆ values p
Proof
  Induct_on `ctree_lts` >> rw[SUBSET_DEF] >> metis_tac[]
QED

Theorem ctree_lts_values_val:
  ctree_lts p (val r) q ==> r ∈ values p
Proof
  Induct_on `ctree_lts` >> rw[] >> metis_tac[]
QED

Theorem values_lts:
  values p = {r | ∃q. ctree_lts p (val r) q} ∪ BIGUNION {values q | ∃l. ctree_lts p l q}
Proof
  rw[EXTENSION] >> reverse eq_tac
  >- metis_tac[ctree_lts_values, SUBSET_DEF, ctree_lts_values_val]
  >> gvs[IN_DEF] >> Induct_on `values` >> rw[]
  >> metis_tac[]
QED

(* Because ctree_label requires a return type to be specified, when binding across different
   types we want a way to say "these labels are the same".
   When we have ctree_bind t k, I will conventionally use the left argument (l) for the label of
   ctree_bind t k and the right arugment (l') for the label of t. *)
Definition ctree_lts_same_def:
  ctree_lts_same l l' <=> l = tau ∧ l' = tau ∨ ∃e a. l = obs e a ∧ l' = obs e a
End

Theorem ctree_lts_same[simp]:
  ¬ctree_lts_same (val r) l' ∧
  ¬ctree_lts_same l (val r') ∧
  (ctree_lts_same tau l' <=> l' = tau) ∧
  (ctree_lts_same l tau <=> l = tau) ∧
  (ctree_lts_same (obs e a) l' <=> l' = obs e a) ∧
  (ctree_lts_same l (obs e a) <=> l = obs e a)
Proof
  rw[ctree_lts_same_def, EQ_IMP_THM]
QED

Theorem ctree_lts_sym:
  ctree_lts_same l l' ==> ctree_lts_same l' l
Proof
  rw[ctree_lts_same_def] >> metis_tac[]
QED

Theorem ctree_lts_bind_rules:
  (ctree_lts_same l l' ∧ ctree_lts p l' q ==> ctree_lts (ctree_bind p k) l (ctree_bind q k)) ∧
  (ctree_lts p (val r) p' ∧ ctree_lts (k r) l q' ==> ctree_lts (ctree_bind p k) l q')
Proof
  rpt conj_tac
  >> Induct_on `ctree_lts` >> rw[]
  >> metis_tac[]
QED

Theorem ctree_lts_bind_same = cj 1 ctree_lts_bind_rules;

Theorem ctree_lts_bind_ret = cj 2 ctree_lts_bind_rules;

Theorem ctree_lts_bind_cases:
  ctree_lts (ctree_bind t k) l q <=>
    (∃u l'. ctree_lts_same l l' ∧ ctree_lts t l' u ∧ q = ctree_bind u k) ∨
    (∃r. ctree_lts t (val r) ctree_stuck ∧ ctree_lts (k r) l q)
Proof
  reverse eq_tac
  >- (rw[] >> metis_tac[ctree_lts_bind_rules])
  >> qid_spec_tac `t`
  >> Induct_on `ctree_lts` >> rw[] >> rw[]
  >> Cases_on `t` >> gvs[]
  >- goal_assum $ dxrule_at Any
  >> first_x_assum $ resolve_then Any mp_tac EQ_REFL
  >> rw[] >> metis_tac[]
QED

(* --- 2.1 - ctree_sbisim definition --- *)

(* Having defined the lts, we can use the existing theory on bisimulation to define ctree_sbisim.
   It is useful to not have to directly refer to BISIM_REL and BISIM in proofs, so we redefine
   a few theorems specialized for sbisim. *)

Definition ctree_sbisim_def:
  ctree_sbisim = BISIM_REL ctree_lts
End

fun spec_lts thm =
  thm
  |> INST_TYPE [
    alpha |-> ``:('a, 'b, 'c, 'd) ctree``,
    beta |-> ``:('a, 'c, 'd) ctree_label``
  ]
  |> Q.SPEC `ctree_lts`
  |> SIMP_RULE std_ss [GSYM ctree_sbisim_def];

Theorem ctree_sbisim_thm:
  ctree_sbisim p0 q0 <=> ∃R. R p0 q0 ∧
    (∀p q. R p q ⇒
      ∀l. (∀p'. ctree_lts p l p' ⇒ ∃q'. ctree_lts q l q' ∧ R p' q') ∧
           (∀q'. ctree_lts q l q' ⇒ ∃p'. ctree_lts p l p' ∧ R p' q'))
Proof
  rw[ctree_sbisim_def, BISIM_REL_def, BISIM_def]
  >> metis_tac[]
QED

Theorem ctree_sbisim_coind = spec_lts BISIM_REL_coind;

Theorem ctree_sbisim_strong_thm = spec_lts BISIM_REL_strong_thm;

Theorem ctree_sbisim_strong_coind = spec_lts BISIM_REL_strong_coind;

Theorem ctree_sbisim_sym_thm = spec_lts BISIM_REL_sym_thm;

Theorem ctree_sbisim_sym_coind = spec_lts BISIM_REL_sym_coind;

Theorem ctree_sbisim_sym_strong_thm = spec_lts BISIM_REL_sym_strong_thm;

Theorem ctree_sbisim_sym_strong_coind = spec_lts BISIM_REL_sym_strong_coind;

(* It is almost never necessary to expand ctree_sbisim in the assumptions, since doing so
   would be extremely verbose and annoying to work with. These two theorems should be used
   instead, with drule or drule_all (or the x variants), and give you everything you would
   get from expanding directly.
   It can be useful to use resolve_then with the lts rules (like ctree_lts_ret) to
   fill in the lts portion. *)
Theorem ctree_sbisim_lts_rules = spec_lts BISIM_REL_ts
Theorem ctree_sbisim_lts = cj 1 ctree_sbisim_lts_rules;

Theorem ctree_sbisim_lts_right = cj 2 ctree_sbisim_lts_rules;

(* Unwraps a layer of lts, niche usage *)
Theorem ctree_sbisim_iff_lts:
  ctree_sbisim p q <=>
    (∀l p'. ctree_lts p l p' ⇒ ∃q'. ctree_lts q l q' ∧ ctree_sbisim p' q') ∧
    ∀l q'. ctree_lts q l q' ⇒ ∃p'. ctree_lts p l p' ∧ ctree_sbisim p' q'
Proof
  eq_tac
  >- metis_tac[ctree_sbisim_lts_rules]
  >> qid_spec_tac `q` >> qid_spec_tac `p`
  >> ho_match_mp_tac ctree_sbisim_coind
  >> rw[]
  >> metis_tac[ctree_sbisim_lts_rules]
QED

(* --- 2.2 - Basic ctree_sbisim equational theory --- *)

Theorem ctree_sbisim_equiv[simp] = spec_lts BISIM_REL_IS_EQUIV_REL;

Theorem ctree_sbisim_refl_sym_trans[simp] = MATCH_MP (iffLR equivalence_def) ctree_sbisim_equiv;

Theorem ctree_sbisim_equiv_rules = spec_lts BISIM_REL_EQUIV_rules;

Theorem ctree_sbisim_refl[simp] = cj 1 ctree_sbisim_equiv_rules;

Theorem ctree_sbisim_sym = iffLR $ cj 2 ctree_sbisim_equiv_rules;

Theorem ctree_sbisim_trans = cj 3 ctree_sbisim_equiv_rules;

(* ctree_sbisimᵀ = ctree_sbisim *)
Theorem ctree_sbisim_inv[simp] =
  symmetric_inv_identity
  |> INST_TYPE [``:'a`` |-> ``:('a, 'b, 'c, 'd) ctree``]
  |> Q.SPEC `ctree_sbisim`
  |> fn t => MATCH_MP t (cj 2 ctree_sbisim_refl_sym_trans);


(* Used for making symmetric rewrites *)
Theorem ctree_sbisim_sym_eq[local]:
  ctree_sbisim p q <=>
  (∀t. ctree_sbisim p t <=> ctree_sbisim q t) ∧
  (∀t. ctree_sbisim t p <=> ctree_sbisim t q)
Proof
  metis_tac[ctree_sbisim_equiv_rules]
QED

Theorem ctree_sbisim_sym_iff[local]:
  (ctree_sbisim p q <=> P p q) <=>
  (ctree_sbisim p q <=> P p q) ∧
  (ctree_sbisim q p <=> P p q)
Proof
  metis_tac[ctree_sbisim_sym]
QED

val ctree_sbisim_make_sym_eq = SIMP_RULE std_ss [Once ctree_sbisim_sym_eq];
val ctree_sbisim_make_sym_iff = SIMP_RULE std_ss [Once ctree_sbisim_sym_iff];

Theorem ctree_sbisim_ctors[simp]:
  (ctree_sbisim (Ret r) (Ret r') <=> r = r') ∧
  (ctree_sbisim (Tau u) (Tau v) <=> ctree_sbisim u v) ∧
  (ctree_sbisim (Vis e g) (Vis e' g') <=> e = e' ∧ (∀a. ctree_sbisim (g a) (g' a)))
Proof
  rpt conj_tac >> (
    eq_tac >> strip_tac
    >- (dxrule ctree_sbisim_lts >> rw[] >> metis_tac[ctree_label_distinct_11])
    >> irule $ iffRL ctree_sbisim_strong_thm
    >> irule_at (Pos hd) rel_exact_lemma >> rw[]
  )
QED

Theorem ctree_sbisim_br:
  (∀v. ∃v'. ctree_sbisim (k v) (k' v')) ∧
  (∀v'. ∃v. ctree_sbisim (k v) (k' v'))
    ==> ctree_sbisim (Br k) (Br k')
Proof
  rw[] >> irule $ iffRL ctree_sbisim_strong_thm
  >> irule_at (Pos hd) rel_exact_lemma >> rw[]
  >> metis_tac[ctree_sbisim_lts_rules]
QED

Theorem ctree_sbisim_guard:
  ctree_sbisim (Guard t) t
Proof
  rw[Once ctree_sbisim_iff_lts]
  >> goal_assum $ dxrule_at (Pos hd) >> rw[]
QED

Theorem ctree_sbisim_brS[simp]:
  ctree_sbisim (BrS k) (BrS k') <=>
    (∀v. ∃v'. ctree_sbisim (k v) (k' v')) ∧
    (∀v'. ∃v. ctree_sbisim (k v) (k' v'))
Proof
  rw[EQ_IMP_THM]
  >- (dxrule ctree_sbisim_lts >> rw[] >> metis_tac[])
  >- (dxrule ctree_sbisim_lts_right >> rw[] >> metis_tac[])
  >> rw[BrS_def]
  >> irule ctree_sbisim_br
  >> rw[]
QED

Theorem ctree_sbisim_step:
  ctree_sbisim (Step t) (Tau t)
Proof
  rw[Step_def, ctree_sbisim_guard]
QED

Theorem ctree_sbisim_funpow:
  ctree_sbisim (FUNPOW Guard n t) t ∧
  ctree_sbisim (FUNPOW Step n t) (FUNPOW Tau n t)
Proof
  Induct_on `n` >> rw[FUNPOW_SUC]
  >> irule ctree_sbisim_trans
  >| map (irule_at (Pos hd)) [ctree_sbisim_guard, ctree_sbisim_step]
  >> rw[]
QED

Theorem ctree_sbisim_sym_eqs[simp] =
  [ctree_sbisim_guard, ctree_sbisim_step] @ CONJ_LIST 2 ctree_sbisim_funpow
  |> map ctree_sbisim_make_sym_eq
  |> LIST_CONJ
  |> SIMP_RULE std_ss [GSYM CONJ_ASSOC];

Theorem ctree_sbisim_stuck_lemma[local]:
  ctree_sbisim t ctree_stuck <=> t = ctree_stuck
Proof
  rw[GSYM no_ctree_lts_iff_stuck, Once ctree_sbisim_iff_lts]
QED

Theorem ctree_sbisim_stuck[simp] = ctree_sbisim_make_sym_iff ctree_sbisim_stuck_lemma;

Theorem ctree_sbisim_not[simp]:
  (¬ctree_sbisim (Ret r) (Tau u)) ∧
  (¬ctree_sbisim (Tau u) (Ret r)) ∧
  (¬ctree_sbisim (Tau u) (Vis e g)) ∧
  (¬ctree_sbisim (Vis e g) (Ret r)) ∧
  (¬ctree_sbisim (Vis e g) (Tau u))
Proof
  rw[] >> spose_not_then strip_assume_tac
  >> dxrule ctree_sbisim_lts >> rw[]
  >> metis_tac[ctree_label_distinct_11]
QED

Theorem ctree_sbisim_index:
  ∀p q path p' l p''.
  ctree_sbisim p q ∧ ctree_index path p = SOME p'
  ∧ EVERY invisible_edge path ∧ (∀k. p' ≠ Br k) ∧ ctree_lts p' l p''
  ==> ∃path' q' q''.
    EVERY invisible_edge path' ∧
    ctree_index path' q = SOME q' ∧ (∀k. q' ≠ Br k) ∧
    ctree_lts q' l q'' ∧ ctree_sbisim p'' q''
Proof
  rw[] >> dxrule_all ctree_lts_index_rules >> rw[]
  >> dxrule_all ctree_sbisim_lts >> rw[]
  >> dxrule $ iffLR ctree_lts_index_cases >> rw[]
  >> rpt (goal_assum $ dxrule_at Any)
QED

Theorem ctree_path_cases:
  ∀path.
    EVERY invisible_edge path ∨
    ∃xs h ys.path = xs ++ h::ys ∧ EVERY invisible_edge xs ∧ ¬invisible_edge h
Proof
  rw[] >> Cases_on `SPLITP (COMPL invisible_edge) path`
  >> Cases_on `r`
  >| map drule [iffLR SPLITP_NIL_SND_EVERY, SPLITP_IMP]
  >> rw[o_DEF, IN_DEF, SF ETA_ss]
  >> dxrule SPLITP_JOIN >> rw[]
  >> rpt (goal_assum $ dxrule_at Any)
  >> irule_at Any EQ_REFL
QED

Theorem ctree_path_ind:
  ∀P.
    (∀path. EVERY invisible_edge path ==> P path) ∧
    (∀xs h ys. EVERY invisible_edge xs ∧ ¬invisible_edge h ∧ P ys ==> P (xs ++ h::ys))
  ==> ∀path. P path
Proof
  rw[] >> measureInduct_on `LENGTH path` >> rw[]
  >> Cases_on `path` using ctree_path_cases
  >> gvs[]
End

Theorem ctree_sbisim_values_lemma[local]:
  ctree_sbisim p q ==> values p ⊆ values q
Proof
  rw[SUBSET_DEF, values_index] >> rpt (pop_assum mp_tac)
  >> qid_spec_tac `q` >> qid_spec_tac `p`
  >> Induct_on `path` using ctree_path_ind >> rw[] >- (
    dxrule ctree_sbisim_index >> disch_then dxrule >> rw[]
    >> Cases_on `q'` >> gvs[] >> goal_assum $ dxrule_at Any
  )
  >> gvs[ctree_index_append_eq]
  >> Cases_on `u` >> gvs[]
  >> dxrule ctree_sbisim_index >> rpt (disch_then dxrule) >> rw[SF DNF_ss]
  >| [all_tac, first_x_assum $ qspec_then `a` strip_assume_tac]
  >> first_x_assum dxrule_all >> rw[]
  >> Cases_on `q'` >> gvs[]
  >> qrefine `path'' ++ h::path`
  >> rw[ctree_index_append_eq]
  >> goal_assum $ dxrule_at Any
QED

Theorem ctree_sbisim_values:
  ctree_sbisim p q ==> values p = values q
Proof
  rw[] >> irule SUBSET_ANTISYM
  >> metis_tac[ctree_sbisim_sym, ctree_sbisim_values_lemma]
QED

Theorem ctree_sbisim_values_rev:
  ctree_sbisim p q ==> values q = values p
Proof
  metis_tac[ctree_sbisim_values]
QED

Theorem ctree_sbisim_retless:
  ctree_sbisim p q ==> (retless p <=> retless q)
Proof
  rw[retless_iff_empty] >> metis_tac[ctree_sbisim_values]
QED

(* Some inversion formulas for the visible nodes *)

Theorem ctree_sbisim_visible_inv:
  (ctree_sbisim p (Ret r) <=> (∀l q. ctree_lts p l q <=> l = val r ∧ q = ctree_stuck)) ∧
  (ctree_sbisim p (Tau u) <=>
    (∃p'. ctree_lts p tau p' ∧ ctree_sbisim p' u) ∧
    ∀l q. ctree_lts p l q ==> l = tau ∧ ctree_sbisim q u) ∧
  (ctree_sbisim p (Vis e g) <=>
    (∀a. ∃p'. ctree_lts p (obs e a) p' ∧ ctree_sbisim p' (g a)) ∧
    ∀l q. ctree_lts p l q ==> ∃a. l = obs e a ∧ ctree_sbisim q (g a))
Proof
  rw[EQ_IMP_THM]
  >>~- ([`ctree_sbisim _ _ (* g *)`, `_ = _ ∧ _`], rw[Once ctree_sbisim_iff_lts] >> metis_tac[])
  >>~- ([`ctree_lts _ _ _ (* a *)`], dxrule_all ctree_sbisim_lts >> rw[])
  >> dxrule ctree_sbisim_lts_right >> rw[]
QED

(* Vis is separate, as we need to justify that there can only be one vis node up to sbisim
   despite the branching, so proof is more complex. An inversion formula for two branch nodes
   is rather doomed so we don't attempt it. *)
Theorem ctree_sbisim_br_inv_lemma[local]:
  (ctree_sbisim (Br k) (Ret r) <=>
    (∃v. ctree_sbisim (k v) (Ret r)) ∧
    ∀v. ctree_sbisim (k v) (Ret r) ∨ k v = ctree_stuck) ∧
  (ctree_sbisim (Br k) (Tau u) <=>
    (∃v. ctree_sbisim (k v) (Tau u)) ∧
    ∀v. ctree_sbisim (k v) (Tau u) ∨ k v = ctree_stuck)
Proof
  rw[ctree_sbisim_visible_inv] >> metis_tac[no_ctree_lts_iff_stuck]
QED

Theorem ctree_sbisim_br_vis_lemma[local]:
  ctree_sbisim (Br k) (Vis e g) ∧ ctree_lts (k v) l t
    ==> ctree_sbisim (k v) (Vis e g)
Proof
  rw[] >> rw[Once ctree_sbisim_iff_lts]
  >> drule_then strip_assume_tac ctree_lts_br
  >> drule_all ctree_sbisim_lts >> rw[] >> gvs[]
  >> rev_dxrule ctree_lts_obs_carry >> rw[]
  >> first_x_assum $ qspec_then `a` strip_assume_tac
  >> drule_then strip_assume_tac ctree_lts_br
  >> dxrule_all ctree_sbisim_lts >> rw[] >> gvs[]
  >> metis_tac[]
QED

Theorem ctree_sbisim_br_inv_vis[local]:
  ctree_sbisim (Br k) (Vis e g) <=>
    (∃v. ctree_sbisim (k v) (Vis e g)) ∧
    ∀v. ctree_sbisim (k v) (Vis e g) ∨ k v = ctree_stuck
Proof
  rw[EQ_IMP_THM] >- (
    drule_then strip_assume_tac ctree_sbisim_lts_right
    >> first_x_assum $ resolve_then Any mp_tac ctree_lts_vis >> rw[]
    >> first_x_assum $ qspec_then `ARB` mp_tac >> rw[]
    >> dxrule_all ctree_sbisim_br_vis_lemma >> rw[]
    >> goal_assum $ dxrule_at Any
  )
  >- (
    Cases_on `k v = ctree_stuck` >> rw[]
    >> dxrule_at Concl $ iffLR no_ctree_lts_iff_stuck >> rw[]
    >> dxrule_all ctree_sbisim_br_vis_lemma >> rw[]
  )
  >> gvs[ctree_sbisim_visible_inv]
  >> metis_tac[not_ctree_lts_stuck]
QED

Theorem ctree_sbisim_br_inv =
  (CONJ_LIST 2 ctree_sbisim_br_inv_lemma) @ [ctree_sbisim_br_inv_vis]
  |> LIST_CONJ;

Theorem ctree_sbisim_bind_cong:
  ∀p q. (∃t t' k k'.
    ctree_sbisim t t' ∧ (∀v. v ∈ values t ==> ctree_sbisim (k v) (k' v)) ∧
    p = ctree_bind t k ∧ q = ctree_bind t' k')
  ==> ctree_sbisim p q
Proof
  ho_match_mp_tac ctree_sbisim_sym_strong_coind >> rw[]
  >- (gvs[symmetric_def] >> metis_tac[ctree_sbisim_sym, ctree_sbisim_values])
  >> dxrule $ iffLR ctree_lts_bind_cases >> rw[]
  >| [drule ctree_lts_values, drule ctree_lts_values_val] >> rw[]
  >> dxrule_all ctree_sbisim_lts >> rw[]
  >| map (irule_at (Pos hd)) $ CONJ_LIST 2 ctree_lts_bind_rules
  >> rpt (goal_assum $ dxrule_at (Pos hd)) >> rw[]
  >> metis_tac[ctree_sbisim_lts, SUBSET_DEF]
QED

Theorem ctree_sbisim_bind:
  ctree_sbisim t t' ∧ (∀v. v ∈ values t ==> ctree_sbisim (k v) (k' v))
    ==> ctree_sbisim (ctree_bind t k) (ctree_bind t' k')
Proof
  metis_tac[ctree_sbisim_bind_cong]
QED

Theorem ctree_sbisim_bind_t = ctree_sbisim_bind |> Q.INST [`k'` |-> `k`] |> SIMP_RULE std_ss [ctree_sbisim_refl];

Theorem ctree_sbisim_bind_k = ctree_sbisim_bind |> Q.INST [`t'` |-> `t`] |> SIMP_RULE std_ss [ctree_sbisim_refl];

Theorem ctree_sbisim_bind_ret:
  ctree_sbisim t (Ret r) ==> ctree_sbisim (ctree_bind t k) (k r)
Proof
  rw[] >> `ctree_sbisim (ctree_bind t k) (ctree_bind (Ret r) k)` suffices_by rw[]
  >> metis_tac[ctree_sbisim_bind_t]
QED

(* --- 2.3 - ctree_sbisim_bind_thm --- *)

(* Progress is necessary on both sides: if we were to use ``(∀r. m ≠ Ret r ∨ m' ≠ Ret r)``,
   then consider the case ``ctree_sbisim t ctree_stuck``.
   Using the relation ``λp q. p = t ∧ q = ctree_stuck``, we can bind the left side to a Ret node
   and expand a Br node on the right, which puts us back in the (t, ctree_stuck) case, and finishes
   the proof. Since not every ctree is stuck, this is a contradiction. *)
Definition bind_rel_def:
  bind_rel (:'e) R p q <=>
    ctree_sbisim p q ∨ ∃(m: ('a, 'b, 'c, 'e) ctree) m' f f'.
      p = ctree_bind m f ∧ q = ctree_bind m' f' ∧
      ctree_sbisim m m' ∧
      (∀r. m ≠ Ret r ∧ m' ≠ Ret r) ∧
      ∀x. x ∈ values m ==> R (f x) (f' x)
End

Theorem sbisim_rsubset_bind_rel:
  ctree_sbisim ⊆ᵣ (bind_rel (:'e) R)
Proof
  rw[RSUBSET, bind_rel_def]
QED

Theorem rpreserves_symmetric_bind_rel:
  rpreserves symmetric (bind_rel (:'e))
Proof
  rw[rpreserves_def, symmetric_def, bind_rel_def, EQ_IMP_THM]
  >> metis_tac[ctree_sbisim_sym, ctree_sbisim_values]
QED

Theorem rmonotone_bind_rel:
  rmonotone (bind_rel (:'e))
Proof
  rw[rmonotone_def, RSUBSET, bind_rel_def] >> metis_tac[]
QED

Theorem SC_bind_rel:
  SC (bind_rel (:'e) R) ⊆ᵣ bind_rel (:'e) (SC R)
Proof
  irule RMONOTONE_IMP_CLOSURE_RSUBSET
  >> rw[rmonotone_bind_rel]
  >> irule_at (Pos last) rpreserves_symmetric_bind_rel
  >> rw[]
QED

Theorem inv_bind_rel[local]:
  (bind_rel (:'e) R)ᵀ = bind_rel (:'e) Rᵀ
Proof
  rw[FUN_EQ_THM, bind_rel_def]
  >> metis_tac[ctree_sbisim_sym, ctree_sbisim_values]
QED

Theorem bind_rel_productive_left[local]:
  ctree_sbisim p (Ret r) ∧ bind_rel (:'e) R (k r) (k' r)
  ==> bind_rel (:'e) R (ctree_bind (p: ('a, 'b, 'c, 'e) ctree) k) (k' r)
Proof
  rw[bind_rel_def]
  >- metis_tac[ctree_sbisim_trans, ctree_sbisim_bind_ret]
  >> disj2_tac
  >> goal_assum $ dxrule_at (Pos (el 2))
  >> qexistsl [`ctree_bind p (λv. m)`, `f`] >> rw[ctree_bind_assoc]
  >- (rev_dxrule ctree_sbisim_values >> rw[] >> gvs[]) >- (
    irule ctree_sbisim_trans
    >> goal_assum $ dxrule_at (Pos last)
    >> irule ctree_sbisim_trans
    >> irule_at (Pos hd) ctree_sbisim_bind_t
    >> goal_assum $ dxrule_at (Pos hd)
    >> rw[]
  )
  >> gvs[values_bind, SPECIFICATION]
QED

Theorem bind_rel_productive_right[local]:
  ctree_sbisim (Ret r) p' ∧ bind_rel (:'e) R (k r) (k' r)
  ==> bind_rel (:'e) R (k r) (ctree_bind (p': ('a, 'b, 'c, 'e) ctree) k')
Proof
  rw[bind_rel_def]
  >- metis_tac[ctree_sbisim_trans, ctree_sbisim_bind_ret, ctree_sbisim_sym]
  >> disj2_tac
  >> goal_assum $ dxrule_at (Pos hd)
  >> qexistsl [`ctree_bind p' (λv. m')`, `f'`] >> rw[ctree_bind_assoc]
  >- (rev_dxrule ctree_sbisim_values_rev >> rw[] >> gvs[])
  >> irule ctree_sbisim_trans
  >> goal_assum $ dxrule_at (Pos hd)
  >> irule ctree_sbisim_trans
  >> irule_at (Pos last) ctree_sbisim_bind_t
  >> goal_assum $ dxrule_at (Pos hd)
  >> rw[]
QED

Theorem bind_rel_productive[local]:
  R ⊆ᵣ (bind_rel (:'e) R) ∧
  ctree_sbisim (m: ('a, 'b, 'c, 'e) ctree) m' ∧
  (∀x. x ∈ values m ==> R (f x) (f' x))
  ==> bind_rel (:'e) R (ctree_bind m f) (ctree_bind m' f')
Proof
  Cases_on `∀r. m ≠ Ret r ∧ m' ≠ Ret r` >> rw[]
  >- (rw[bind_rel_def] >> metis_tac[])
  >> gvs[]
  >- metis_tac[RSUBSET, bind_rel_productive_right]
  >> drule ctree_sbisim_values >> rw[] >> gvs[]
  >> metis_tac[RSUBSET, bind_rel_productive_left]
QED

Theorem bind_rel_lts[local]:
  R ⊆ᵣ (bind_rel (:'e) R) ∧ bind_rel (:'e) R p q ∧ ctree_lts p l p'
  ==> ∃q'. ctree_lts q l q' ∧ bind_rel (:'e) R p' q'
Proof
  rw[] >> dxrule $ iffLR ctree_lts_index_cases >> rw[]
  >> qpat_x_assum `bind_rel _ R p q` mp_tac
  >> qpat_x_assum `ctree_index _ p = _` mp_tac
  >> qid_spec_tac `q` >> qid_spec_tac `p`
  >> measureInduct_on `LENGTH path` >> rw[]
  >> dxrule $ iffLR bind_rel_def >> rw[]
  >- (dxrule_all ctree_lts_index_rules >> metis_tac[ctree_sbisim_lts, sbisim_rsubset_bind_rel, RSUBSET])
  >> dxrule $ iffLR ctree_index_bind_cases >> rw[] >- (
    dxrule_at (Pos (el 3)) ctree_lts_index_rules >> rw[]
    >> dxrule $ iffLR ctree_lts_bind_cases >> reverse (rw[])
    >- (Cases_on `u` >> gvs[])
    >> `∀k. u ≠ Br k` by (Cases_on `u` >> gvs[])
    >> first_x_assum dxrule_all >> rw[]
    >> drule_all ctree_sbisim_lts >> rw[]
    >> rename[`ctree_sbisim u' v'`]
    >> irule_at (Pos hd) $ cj 1 ctree_lts_bind_rules
    >> rpt (goal_assum $ dxrule_at (Pos hd))
    >> irule bind_rel_productive >> rw[]
    >> metis_tac[ctree_lts_values, ctree_sbisim_values, SUBSET_DEF]
  )
  >> rename[`EVERY _ (pathl ++ pathr)`] >> gvs[]
  >> first_x_assum $ qspec_then `pathr` strip_assume_tac >> gvs[]
  >> `0 < LENGTH pathl` by (Cases_on `pathl` >> gvs[]) >> gvs[]
  >> first_x_assum $ dxrule_then strip_assume_tac
  >> drule values_index_subset >> rw[]
  >> first_x_assum dxrule >> rw[]
  >> dxrule $ iffLR RSUBSET >> disch_then dxrule >> rw[]
  >> first_x_assum dxrule >> rw[]
  >> dxrule_at (Pos (el 3)) ctree_lts_index_rules >> rw[]
  >> dxrule_all ctree_sbisim_lts >> rw[]
  >> irule_at (Pos hd) $ cj 2 ctree_lts_bind_rules
  >> rpt (goal_assum $ dxrule_at (Pos hd))
QED

Theorem ctree_sbisim_bind_lemma[local]:
  symmetric R ∧ R p q ∧ R ⊆ᵣ (bind_rel (:'e) R) ==> ctree_sbisim p q
Proof
  rw[] >> irule $ iffRL ctree_sbisim_sym_thm
  >> qexists `bind_rel (:'e) R`
  >> rw[MATCH_MP (iffLR rpreserves_def) rpreserves_symmetric_bind_rel]
  >> metis_tac[RSUBSET, bind_rel_lts]
QED

Theorem ctree_sbisim_bind_rel_thm:
  ctree_sbisim p0 q0 <=> ∃R. R p0 q0 ∧ R ⊆ᵣ (bind_rel (:'e) (R ∪ᵣ ctree_sbisim))
Proof
  rw[EQ_IMP_THM]
  >- (qexists `ctree_sbisim` >> rw[sbisim_rsubset_bind_rel])
  >> irule ctree_sbisim_bind_lemma
  >> qexists `SC $ bind_rel (:'e) (R RUNION ctree_sbisim)`
  >> rw[SC_SYMMETRIC]
  >- metis_tac[RSUBSET, SC_bind_rel, SC_DEF]
  >> rw[SC_THM, RUNION_RSUBSET, INV_RSUBSET, inv_bind_rel]
  >> irule $ MATCH_MP (iffLR rmonotone_def) rmonotone_bind_rel
  >> rw[RUNION_RSUBSET, RSUBSET_RUNION, SC_THM, sbisim_rsubset_bind_rel,
        INV_RUNION, INV_RSUBSET, INV_RUNION, inv_bind_rel]
QED

Theorem ctree_sbisim_bind_rel_coind:
  R p0 q0 ∧ R ⊆ᵣ (bind_rel (:'e) (R ∪ᵣ ctree_sbisim))
  ==> ∀p q. R p q ==> ctree_sbisim p q
Proof
  rw[] >> irule $ iffRL ctree_sbisim_bind_rel_thm
  >> qexists `R` >> rw[]
QED

Theorem ctree_sbisim_bind_thm:
  ctree_sbisim p0 q0 <=> ∃R. R p0 q0 ∧
    ∀p q. R p q ==> ctree_sbisim p q ∨
      ∃(m: ('a, 'b, 'c, 'e) ctree) m' f f'.
        p = ctree_bind m f ∧ q = ctree_bind m' f' ∧
        ctree_sbisim m m' ∧
        (∀r. m ≠ Ret r ∧ m' ≠ Ret r) ∧
        (∀x. x ∈ values m ==> R (f x) (f' x) ∨ ctree_sbisim (f x) (f' x))
Proof
  rw[EQ_IMP_THM]
  >- (qexists `ctree_sbisim` >> metis_tac[])
  >> irule $ iffRL ctree_sbisim_bind_rel_thm
  >> qexists `R` >> rw[RSUBSET, bind_rel_def, RUNION]
  >> metis_tac[]
QED

Theorem ctree_sbisim_bind_coind:
  (∀p q. R p q ==> ctree_sbisim p q ∨
    ∃(m: ('a, 'b, 'c, 'e) ctree) m' f f'.
      p = ctree_bind m f ∧ q = ctree_bind m' f' ∧
      ctree_sbisim m m' ∧
      (∀r. m ≠ Ret r ∧ m' ≠ Ret r) ∧
      (∀x. x ∈ values m ==> R (f x) (f' x) ∨ ctree_sbisim (f x) (f' x)))
  ==> ∀p q. R p q ==> ctree_sbisim p q
Proof
  rw[] >> irule $ iffRL ctree_sbisim_bind_thm
  >> qexists `R` >> rw[]
QED

Theorem ctree_sbisim_bind_sym_thm:
  ctree_sbisim p0 q0 <=> ∃R. symmetric R ∧ R p0 q0 ∧
    ∀p q. R p q ==> ctree_sbisim p q ∨
      ∃(m: ('a, 'b, 'c, 'e) ctree) m' f f'.
        p = ctree_bind m f ∧ q = ctree_bind m' f' ∧
        ctree_sbisim m m' ∧
        (∀r. m ≠ Ret r) ∧
        (∀x. x ∈ values m ==> R (f x) (f' x) ∨ ctree_sbisim (f x) (f' x))
Proof

  rw[EQ_IMP_THM]
  >- (qexists `ctree_sbisim` >> rw[])
  >> (ctree_sbisim_bind_thm
  |> INST_TYPE [``:'e`` |-> ``:'a + 'b``]
  |> iffRL |> irule)
  >> qexists `R ∪ᵣ bind_rel (:'a + 'b) R` >> reverse (rw[RUNION])
  >- (dxrule $ iffLR bind_rel_def >> metis_tac[])
  >> `R q p` by gvs[symmetric_def]
  >> first_assum dxrule >> first_assum dxrule
  >> rw[] >> rw[ctree_sbisim_sym]
  >> rename1 `ctree_bind n g = ctree_bind m f`
  >> rename1 `ctree_bind n' g' = ctree_bind m' f'`
  >> disj2_tac
  >> rpt (dxrule not_ret_imp_ctree_bind_height_1) >> rw[]
  >> gvs[ctree_bind_assoc]
  >> irule_at (Pos hd) EQ_REFL
  >> irule_at (Pos hd) EQ_SYM >> goal_assum $ dxrule_at (Pos hd)
  >> rw[] >- (
    
  )


QED

(* --- 2.3 - Advanced ctree_sbisim equational theory --- *)

Theorem ctree_sbisim_iter_lemma[local]:
  ∀(p: ('a, 'b, 'c, 'd) ctree) q. (∃(s: 'e).
    p = ctree_iter k s ∧ q = ctree_iter k' s ∧
    (∀s. ctree_sbisim (k s) (k' s))
  ) ==> ctree_sbisim p q
Proof

  (ctree_sbisim_bind_coind
  |> INST_TYPE [``:'e`` |-> ``:'e + 'd``]
  |> ho_match_mp_tac) >> rw[]
  >> Cases_on `∀r. k s ≠ RRet r` >> gvs[] >- (
    disj2_tac >> rw[ctree_iter_thm]
    >> rpt (irule_at (Pos hd) EQ_REFL)
    >> rw[ctree_sbisim_bind_t]
    >> CASE_TAC >> rw[ctree_iter_thm] >> gvs[]
    >> metis_tac[]
  )

QED
