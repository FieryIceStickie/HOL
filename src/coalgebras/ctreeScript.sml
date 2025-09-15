(*
  This file defines a type for coinductive choice trees (ctree), as
  explained in Chappe et al.'s 2023 paper titled "Choice Trees".

  This implementation differs from the paper by replacing the stepping
  branch node BrS with a Tau node (called Step . = BrS 1 (λ_ -> .) in the paper).
  Thus, BrD is renamed to Br, and we recover BrS as a Br node where every continuation
  is guarded by a Tau.

    ('a,'b,'e,'r) ctree  =
    |  Ret 'r                --  termination with result 'r
    |  Tau (ctree)           --  a silent action, then continue
    |  Vis 'e ('a -> ctree)  --  visible event 'e with answer 'a, then continue based on answer
    |  Br  ('b -> ctree)     --  branching based on 'b
*)

Theory ctree
Ancestors
  arithmetic list llist alist option pred_set relation pair
  combin companion fixedPoint set_relation bisimulation
Libs
  term_tactic mp_then BasicProvers dep_rewrite

(* --- Type definition --- *)

Datatype:
  ctree_el = Return 'r | Silence | Event 'e | Branch
End

Type ctree_rep[local] = ``:('a + 'b) option list -> ('e,'r) ctree_el``;
val f = ``(f: ('a,'b,'e,'r) ctree_rep)``

Theorem path_el_cases[local]:
  ∀n. (n = NONE) ∨ (∃a. n = SOME (INL a)) ∨ (∃b. n = SOME (INR b))
Proof
  Cases_on `n` >> rw[]
  >> Cases_on `x` >> rw[]
QED

Definition path_ok_def:
  path_ok path ^f <=>
    ∀xs y ys. path = xs ++ y::ys ==>
      case f xs of
      | Return _ => F                       (* a path cannot continue past a Return *)
      | Silence  => y = NONE                (* Silence consumes no input *)
      | Branch   => ∃b. y = SOME (INR b)    (* Branch should be a branch *)
      | Event e  => ∃a. y = SOME (INL a)    (* the next element must be an input *)
End

Definition ctree_rep_ok_def:
  ctree_rep_ok ^f <=>
    (* every bad path leads to the Silence element *)
    ∀path. ¬path_ok path f ==> f path = Silence
End

Theorem type_inhabited[local]:
  ∃f. ctree_rep_ok ^f
Proof
  qexists_tac `λp. Silence`
  >> fs[ctree_rep_ok_def]
QED

val ctree_tydef = new_type_definition ("ctree", type_inhabited);

val repabs_fns = define_new_type_bijections
  { name = "ctree_absrep",
    ABS  = "ctree_abs",
    REP  = "ctree_rep",
    tyax = ctree_tydef};

(* --- rep and abs theorems --- *)

val ctree_absrep = CONJUNCT1 repabs_fns
val ctree_repabs = CONJUNCT2 repabs_fns

Theorem ctree_repabs_o[local]:
  ∀k. (∀a. ctree_rep_ok $ k a) ==> ctree_rep o ctree_abs o k = k
Proof
  rw[ctree_repabs, FUN_EQ_THM]
QED

Theorem ctree_rep_ok_ctree_rep[local, simp]:
  ∀t. ctree_rep_ok $ ctree_rep t
Proof
  fs [ctree_repabs, ctree_absrep]
QED

Theorem ctree_abs_11[local]:
  ctree_rep_ok r1 ∧ ctree_rep_ok r2 ==>
    (ctree_abs r1 = ctree_abs r2 <=> r1 = r2)
Proof
  metis_tac[ctree_repabs]
QED

Theorem ctree_rep_11[local]:
  (ctree_rep t1 = ctree_rep t2) = (t1 = t2)
Proof
  metis_tac[ctree_absrep]
QED

Theorem ctree_rep_o_11[local]:
  ctree_rep o g = ctree_rep o h <=> g = h
Proof
  rw[FUN_EQ_THM] >> metis_tac[ctree_rep_11]
QED

Theorem ctree_rep_ok_cons[local]:
  ctree_rep_ok f ==> ∀v. ctree_rep_ok $ λpath. f (v::path)
Proof
  rw[ctree_rep_ok_def]
  >> first_x_assum $ qspec_then `v::path` strip_assume_tac
  >> first_x_assum irule
  >> gvs[path_ok_def]
  >> rename[`v::(xs ++ [y] ++ ys)`]
  >> qexistsl[`v::xs`,`y`,`ys`]
  >> rw[]
QED

Theorem path_not_ok_imp_silence[local]:
  (ctree_rep_ok f) ∧
    (¬case f [] of
       Return r => F
     | Silence  => v = NONE
     | Event e  => ∃a. v = SOME (INL a)
     | Branch   => ∃b. v = SOME (INR b))
  ==> f (v::t) = Silence
Proof
  rw[ctree_rep_ok_def, path_ok_def]
  >> first_x_assum $ qspec_then `v::t` strip_assume_tac
  >> first_x_assum irule
  >> qexistsl[`[]`,`v`,`t`] >> rw[]
QED

(* --- Constructors --- *)

Definition Ret_rep_def:
  Ret_rep (x: 'r) =
    λpath. if path = [] then Return x else Silence
End

Definition Ret_def:
  Ret x = ctree_abs (Ret_rep x)
End

Definition Tau_rep_def:
  Tau_rep ^f =
    λpath. case path of
           | NONE::rest => f rest
           | _ => Silence
End

Definition Tau_def:
  Tau t = ctree_abs $ Tau_rep (ctree_rep t)
End

Definition Vis_rep_def:
  Vis_rep e k =
    λpath. case path of
           | [] => Event e
           | SOME (INL a)::rest => k a rest
           | _ => Silence
End

Definition Vis_def:
  Vis e k = ctree_abs $ Vis_rep e (ctree_rep o k)
End

Definition Br_rep_def:
  Br_rep k =
    λpath. case path of
           | [] => Branch
           | SOME (INR b)::rest => k b rest
           | _ => Silence
End

Definition Br_def:
  Br k = ctree_abs $ Br_rep (ctree_rep o k)
End

Theorem All_def[local] = LIST_CONJ [Ret_def, Tau_def, Vis_def, Br_def];

Theorem All_rep_def[local] = LIST_CONJ [Ret_rep_def, Tau_rep_def, Vis_rep_def, Br_rep_def];

(* Lemmas to prove constructors have ok rep *)

Theorem ctree_rep_ok_Ret[local]:
  ∀x. ctree_rep_ok (Ret_rep x)
Proof
  rw[ctree_rep_ok_def, Ret_rep_def]
  >> Cases_on `path = []`
  >> gvs[path_ok_def]
QED

Theorem ctree_rep_ok_Tau[local]:
  ∀f. ctree_rep_ok f ==> ctree_rep_ok (Tau_rep ^f)
Proof
  rw[ctree_rep_ok_def, Tau_rep_def]
  >> Cases_on `∃r. path = NONE::r`
  >> gvs[path_ok_def]
  >- (
    full_case_tac >> gvs[]
    >> rename[`xs ++ [y] ++ ys`]
    >> first_x_assum $ qspec_then `xs ++ [y] ++ ys` mp_tac
    >> metis_tac[]
  )
  >> rpt (case_tac >> fs[])
QED

Theorem ctree_rep_ok_Vis[local]:
  ∀e k. (∀a. ctree_rep_ok (k a)) ==> ctree_rep_ok (Vis_rep e k)
Proof
  rw[ctree_rep_ok_def, Vis_rep_def]
  >> Cases_on `path = [] ∨ ∃x r. path = SOME (INL x)::r`
  >> gvs[path_ok_def]
  >- (
    full_case_tac >> gvs[]
    >> rename[`xs ++ [y] ++ ys`]
    >> first_x_assum $ qspecl_then [`x`,`xs ++ [y] ++ ys`] mp_tac
    >> metis_tac[]
  )
  >> rpt (case_tac >> fs[])
QED

Theorem ctree_rep_ok_Br[local]:
  ∀k. (∀b. ctree_rep_ok (k b)) ==> ctree_rep_ok (Br_rep k)
Proof
  rw[ctree_rep_ok_def, Br_rep_def]
  >> Cases_on `path = [] ∨ ∃x r. path = SOME (INR x)::r`
  >> gvs[path_ok_def]
  >- (
    full_case_tac >> gvs[]
    >> rename[`xs ++ [y] ++ ys`]
    >> first_x_assum $ qspecl_then [`x`,`xs ++ [y] ++ ys`] mp_tac
    >> metis_tac[]
  )
  >> rpt (case_tac >> fs[])
QED

Theorem ctree_rep_ok_All[local] = LIST_CONJ [ctree_rep_ok_Ret, ctree_rep_ok_Tau, ctree_rep_ok_Vis, ctree_rep_ok_Br];

(* Helps metis_tac work *)
Theorem ctree_All_repabs[local]:
  (∀r.   ctree_rep $ ctree_abs (Ret_rep r                ) = Ret_rep r                ) ∧
  (∀u.   ctree_rep $ ctree_abs (Tau_rep   (ctree_rep u)  ) = Tau_rep   (ctree_rep u)  ) ∧
  (∀e g. ctree_rep $ ctree_abs (Vis_rep e (ctree_rep o g)) = Vis_rep e (ctree_rep o g)) ∧
  (∀k.   ctree_rep $ ctree_abs (Br_rep    (ctree_rep o k)) = Br_rep    (ctree_rep o k))
Proof
  rw[]
  >> irule $ iffLR ctree_repabs
  >> rw[ctree_rep_ok_All]
QED

(* Injectivity *)

Theorem All_rep_11[local]:
  (∀x y.     Ret_rep x   = Ret_rep y   <=> x = y) ∧
  (∀u v.     Tau_rep u   = Tau_rep v   <=> u = v) ∧
  (∀x y g k. Vis_rep x g = Vis_rep y k <=> x = y ∧ g = k) ∧
  (∀g k.     Br_rep  g   = Br_rep  k   <=> g = k)
Proof
  rw[All_rep_def, FUN_EQ_THM] >> eq_tac >> rw[]
  >| [
    first_x_assum $ qspec_then `[]` mp_tac,
    rename[`u r = v r`] >> first_x_assum $ qspec_then `NONE::r` mp_tac,
    first_x_assum $ qspec_then `[]` mp_tac,
    rename[`g a r = k a r`] >> first_x_assum $ qspec_then `SOME (INL a)::r` mp_tac,
    rename[`g a r = k a r`] >> first_x_assum $ qspec_then `SOME (INR a)::r` mp_tac
  ] >> rw[]
QED

Theorem Ret_11:
  ∀x y. Ret x = Ret y <=> x = y
Proof
  metis_tac[Ret_def, ctree_All_repabs, ctree_abs_11, ctree_rep_11, All_rep_11]
QED

Theorem Tau_11:
  ∀x y. Tau x = Tau y <=> x = y
Proof
  metis_tac[Tau_def, ctree_All_repabs, ctree_abs_11, ctree_rep_11, All_rep_11]
QED

Theorem Vis_11:
  ∀x y g k. Vis x g = Vis y k <=> x = y ∧ g = k
Proof
  metis_tac[Vis_def, ctree_All_repabs, ctree_abs_11, ctree_rep_o_11, All_rep_11]
QED

Theorem Br_11:
  ∀g k. Br g = Br k <=> g = k
Proof
  metis_tac[Br_def, ctree_All_repabs, ctree_abs_11, ctree_rep_o_11, All_rep_11]
QED

Theorem ctree_11 = LIST_CONJ [Ret_11, Tau_11, Vis_11, Br_11];

(* Distinctness *)

Theorem ctree_distinct_lemma[local]:
  ALL_DISTINCT [Ret x; Tau t; Vis e g; Br k]
Proof
  rw[ALL_DISTINCT, All_def]
  >> qmatch_goalsub_abbrev_tac `ctree_abs v1 = ctree_abs v2`
  >> `v1 ≠ v2` suffices_by (
    `ctree_rep_ok v1 ∧ ctree_rep_ok v2` by (unabbrev_all_tac >> fs[ctree_rep_ok_All])
    >> rw[ctree_abs_11]
  ) >> unabbrev_all_tac
  >> rw[All_rep_def, FUN_EQ_THM]
  >> qexists_tac `[]` >> rw[]
QED

Theorem ctree_distinct =
  ctree_distinct_lemma |> SIMP_RULE std_ss [ALL_DISTINCT, MEM, GSYM CONJ_ASSOC];

(* Cases *)

Theorem ctree_rep_cases[local]:
  ∀f. ctree_rep_ok f ==>
    (∃r  . f = Ret_rep r                           ) ∨
    (∃u  . f = Tau_rep u   ∧     ctree_rep_ok u    ) ∨
    (∃e g. f = Vis_rep e g ∧ ∀a. ctree_rep_ok $ g a) ∨
    (∃k  . f = Br_rep  k   ∧ ∀b. ctree_rep_ok $ k b)
Proof
  rw[Once ctree_rep_ok_def, path_ok_def]
  >> Cases_on `f []`
  >> rw[All_rep_def, FUN_EQ_THM]
  >| [
    disj1_tac
    >> qexists `r` >> Cases_on `x`,
    disj2_tac >> disj1_tac
    >> qexists `λpath. f (NONE::path)`,
    disj2_tac >> disj2_tac >> disj1_tac
    >> qexistsl[`e`,`λa path. f (SOME (INL a)::path)`],
    disj2_tac >> disj2_tac >> disj2_tac
    >> qexists `λb path. f (SOME (INR b)::path)`
  ] >> rw[]
  >> rpt (case_tac >> rw[])
  >> rw[ctree_rep_ok_cons, ctree_rep_ok_def, path_ok_def]
  >> irule path_not_ok_imp_silence >> rw[ctree_rep_ok_def, path_ok_def]
QED

Theorem ctree_cases:
  ∀t.
    (∃r  . t = Ret r  ) ∨
    (∃u  . t = Tau u  ) ∨
    (∃e g. t = Vis e g) ∨
    (∃k  . t = Br  k  )
Proof
  rw[All_def, GSYM ctree_rep_11, ctree_All_repabs]
  >> `ctree_rep_ok $ ctree_rep t` by rw[ctree_rep_ok_ctree_rep]
  >> dxrule ctree_rep_cases >> rw[]
  >| [
    disj1_tac
    >> qexists `r`,
    disj2_tac >> disj1_tac
    >> qexists `ctree_abs u`,
    disj2_tac >> disj2_tac >> disj1_tac
    >> qexistsl [`e`,`ctree_abs o g`],
    disj2_tac >> disj2_tac >> disj2_tac
    >> qexists `ctree_abs o k`
  ] >> metis_tac[ctree_repabs, ctree_repabs_o]
QED

Definition ctree_CASE[nocompute]:
  ctree_CASE (t: ('a,'b,'e,'r) ctree) ret tau vis br =
    case ctree_rep t [] of
    | Return r => ret r
    | Silence  => tau   $     ctree_abs (λpath. ctree_rep t $ NONE::path        )
    | Event e  => vis e $ λa. ctree_abs (λpath. ctree_rep t $ SOME (INL a)::path)
    | Branch   => br    $ λb. ctree_abs (λpath. ctree_rep t $ SOME (INR b)::path)
End

Theorem ctree_CASE[compute, allow_rebind]:
  ctree_CASE (Ret r)   ret tau vis br = ret r   ∧
  ctree_CASE (Tau u)   ret tau vis br = tau u   ∧
  ctree_CASE (Vis e g) ret tau vis br = vis e g ∧
  ctree_CASE (Br  k)   ret tau vis br = br  k
Proof
  rw[ctree_CASE, All_def, ctree_All_repabs]
  >> rw[All_rep_def, SF ETA_ss, ctree_absrep]
QED

Theorem ctree_CASE_eq:
  ctree_CASE t ret tau vis br = v <=>
    (∃r.   t = Ret r   ∧ ret r   = v) ∨
    (∃u.   t = Tau u   ∧ tau u   = v) ∨
    (∃e g. t = Vis e g ∧ vis e g = v) ∨
    (∃k.   t = Br  k   ∧ br  k   = v)
Proof
  qspec_then `t` strip_assume_tac ctree_cases
  >> rw[ctree_CASE, ctree_11, ctree_distinct]
QED

Theorem ctree_CASE_elim:
  ∀f.
  f(ctree_CASE t ret tau vis br) <=>
    (?r.   t = Ret r   ∧ f(ret r  )) ∨
    (?u.   t = Tau u   ∧ f(tau u  )) ∨
    (?e g. t = Vis e g ∧ f(vis e g)) ∨
    (?k.   t = Br  k   ∧ f(br  k  ))
Proof
  qspec_then `t` strip_assume_tac ctree_cases
  >> rw[ctree_CASE, ctree_11, ctree_distinct]
QED

(* ctree unfold *)

Datatype:
  ctree_next = Ret' 'r
             | Tau' 'seed
             | Vis' 'e ('a -> 'seed)
             | Br'  ('b -> 'seed)
End

Definition ctree_unfold_path_def:
  (ctree_unfold_path f seed [] =
     case f seed of
     | Ret' r   => Return r
     | Tau' u   => Silence
     | Vis' e g => Event e
     | Br'  k   => Branch) ∧
  (ctree_unfold_path f seed (NONE::rest) =
     case f seed of
     | Tau' u => ctree_unfold_path f u rest
     | _      => Silence) ∧
  (ctree_unfold_path f seed (SOME (INL a)::rest) =
     case f seed of
     | Vis' e g => ctree_unfold_path f (g a) rest
     | _        => Silence) ∧
  (ctree_unfold_path f seed (SOME (INR b)::rest) =
     case f seed of
     | Br'  k   => ctree_unfold_path f (k b) rest
     | _        => Silence)
End

Definition ctree_unfold:
  ctree_unfold f seed = ctree_abs (ctree_unfold_path f seed)
End

Theorem ctree_unfold_path_repabs[local]:
  ctree_rep (ctree_abs (ctree_unfold_path f s)) = ctree_unfold_path f s
Proof
  fs[GSYM ctree_repabs, ctree_rep_ok_def]
  >> qid_spec_tac `s`
  >> Induct_on `path` >- rw[path_ok_def]
  >> Cases_on `h` using path_el_cases
  >> rw[ctree_unfold_path_def]
  >> case_tac
  >> first_x_assum irule >> gvs[path_ok_def]
  >> Cases_on `xs` >> gvs[ctree_unfold_path_def]
  >> metis_tac[]
QED

Theorem ctree_unfold[allow_rebind]:
  ctree_unfold f seed =
    case f seed of
    | Ret' r   => Ret r
    | Tau' s   => Tau   (ctree_unfold f s)
    | Vis' e g => Vis e (ctree_unfold f o g)
    | Br'  k   => Br    (ctree_unfold f o k)
Proof
  Cases_on `f seed`
  >> rw[ctree_unfold, All_def, GSYM ctree_rep_11]
  >> rw[ctree_unfold_path_repabs, ctree_All_repabs, FUN_EQ_THM]
  >> rename[`ctree_unfold_path f seed path`]
  >> Cases_on `path` >> TRY $ Cases_on `h` using path_el_cases
  >> rw[ctree_unfold_path_def, All_def, All_rep_def, ctree_unfold, ctree_unfold_path_repabs]
QED

(* Equivalences *)

Theorem ctree_rep_simps[simp]:
  ctree_rep (Ret r) [] = Return r ∧
  ctree_rep (Ret r) (NONE::rest) = Silence ∧
  ctree_rep (Ret r) (SOME (INL a)::rest) = Silence ∧
  ctree_rep (Ret r) (SOME (INR b)::rest) = Silence ∧
  ctree_rep (Tau u) [] = Silence ∧
  ctree_rep (Tau u) (NONE::rest) = ctree_rep u rest ∧
  ctree_rep (Tau u) (SOME (INL a)::rest) = Silence ∧
  ctree_rep (Tau u) (SOME (INR b)::rest) = Silence ∧
  ctree_rep (Vis e g) [] = Event e ∧
  ctree_rep (Vis e g) (NONE::rest) = Silence ∧
  ctree_rep (Vis e g) (SOME (INL a)::rest) = ctree_rep (g a) rest ∧
  ctree_rep (Vis e g) (SOME (INR b)::rest) = Silence ∧
  ctree_rep (Br k) [] = Branch ∧
  ctree_rep (Br k) (NONE::rest) = Silence ∧
  ctree_rep (Br k) (SOME (INL a)::rest) = Silence ∧
  ctree_rep (Br k) (SOME (INR b)::rest) = ctree_rep (k b) rest
Proof
  rw[All_def, ctree_All_repabs] >> rw[All_rep_def]
QED

Theorem ctree_bisimulation:
  ∀t1 t2.
    t1 = t2 <=> ∃R. R t1 t2 ∧
      (∀r t. R (Ret r) t ==> t = Ret r) ∧
      (∀u t. R (Tau u) t ==> ∃v. t = Tau v ∧ R u v) ∧
      (∀e g t. R (Vis e g) t ==> ∃h. t = Vis e h ∧ ∀a. R (g a) (h a)) ∧
      (∀k t. R (Br k) t ==> ∃j. t = Br j ∧ ∀b. R (k b) (j b))
Proof
  rw[] >> eq_tac >> rw[]
  >- (qexists `(=)` >> fs[ctree_11])
  >> rw[GSYM ctree_rep_11, FUN_EQ_THM]
  >> last_x_assum mp_tac >> qid_spec_tac `t2` >> qid_spec_tac `t1`
  >> rename[`_ path = _ path`] >> Induct_on `path`
  >> Cases_on `t1` using ctree_cases >> rw[]
  >> last_x_assum $ dxrule_then strip_assume_tac >> rw[]
  >> Cases_on `h` using path_el_cases >> rw[]
QED

Theorem ctree_strong_bisimulation:
  ∀t1 t2.
    t1 = t2 <=> ∃R. R t1 t2 ∧
      (∀r t. R (Ret r) t ==> t = Ret r) ∧
      (∀u t. R (Tau u) t ==> ∃v. t = Tau v ∧ (R u v ∨ u = v)) ∧
      (∀e g t. R (Vis e g) t ==> ∃h. t = Vis e h ∧ ∀a. R (g a) (h a) ∨ g a = h a) ∧
      (∀k t. R (Br k) t ==> ∃j. t = Br j ∧ ∀b. R (k b) (j b) ∨ k b = j b)
Proof
  rw[] >> eq_tac >> rw[]
  >- (qexists `(=)` >> fs[ctree_11])
  >> rw[Once ctree_bisimulation]
  >> qexists `λp q. R p q ∨ p = q`
  >> metis_tac[]
QED

(* Register type *)

Theorem ctree_CASE_cong:
  ∀M M' ret tau vis br ret' tau' vis' br'.
    (M = M') ∧
    (∀r. M' = Ret r ==> ret r = ret' r) ∧
    (∀u. M' = Tau u ==> tau u = tau' u) ∧
    (∀e g. M' = Vis e g ==> vis e g = vis' e g) ∧
    (∀k. M' = Br k ==> br k = br' k) ==>
    ctree_CASE M' ret tau vis br = ctree_CASE M' ret' tau' vis' br'
Proof
  rw[]
  >> qspec_then `M` strip_assume_tac ctree_cases
  >> rw[ctree_CASE]
QED

Theorem datatype_ctree:
  DATATYPE ((ctree
    (Ret : 'r -> ('a, 'b, 'e, 'r) ctree)
    (Tau : ('a, 'b, 'e, 'r) ctree -> ('a, 'b, 'e, 'r) ctree)
    (Vis : 'e -> ('a -> ('a, 'b, 'e, 'r) ctree) -> ('a, 'b, 'e, 'r) ctree)
    (Br  : ('b -> ('a, 'b, 'e, 'r) ctree) -> ('a, 'b, 'e, 'r) ctree)
  ): bool)
Proof
  rw[boolTheory.DATATYPE_TAG_THM]
QED

val _ = TypeBase.export
  [TypeBasePure.mk_datatype_info
    { ax = TypeBasePure.ORIG TRUTH,
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
      recognizers = [] } ]

Overload "case" = ``ctree_CASE``;

(* --- Combinators --- *)
Definition BrS_def:
  BrS t = Br (Tau o t)
End

Definition Guard_def:
  Guard t = Br (λb. t)
End

Definition Guard'_def:
  Guard' t = Br' (λb. t)
End

Theorem ctree_unfold_guard:
  f seed = Guard' s ==> ctree_unfold f seed = Guard $ ctree_unfold f s
Proof
  rw[Guard_def, Guard'_def, Once ctree_unfold, FUN_EQ_THM]
QED

(* Bind *)

Definition ctree_push_inj_def:
  ctree_push_inj inj t =
    case t of
    | Ret r   => Ret' r
    | Tau u   => Tau'   (inj u)
    | Vis e g => Vis' e (inj o g)
    | Br  k   => Br'    (inj o k)
End

Definition ctree_bind_def:
  ctree_bind t k = ctree_unfold (λn.
    case n of
    | INL (Ret r)   => ctree_push_inj INR (k r)
    | INL (Tau u)   => Tau'   (INL u)
    | INL (Vis e g) => Vis' e (INL o g)
    | INL (Br k)    => Br'    (INL o k)
    | INR v => ctree_push_inj INR v
  ) (INL t)
End

Theorem ctree_bind_INR_id[local]:
  ctree_unfold (λn.
    case n of
    | INL (Ret r)   => ctree_push_inj INR (k r)
    | INL (Tau u)   => Tau'   (INL u)
    | INL (Vis e g) => Vis' e (INL o g)
    | INL (Br k)    => Br'    (INL o k)
    | INR v => ctree_push_inj INR v
  ) (INR t) = t
Proof
  qmatch_goalsub_abbrev_tac `ctree_unfold f _ = _`
  >> rw[Once ctree_strong_bisimulation]
  >> qexists `λp q. p = ctree_unfold f (INR q)`
  >> rw[Abbr`f`] >> Cases_on `t`
  >> gvs[Once ctree_unfold, ctree_push_inj_def]
  >> fs[Once ctree_unfold]
QED

Theorem ctree_bind_thm[simp]:
  ctree_bind (Ret r)   h = h r ∧
  ctree_bind (Tau u)   h = Tau (ctree_bind u h) ∧
  ctree_bind (Vis e g) h = Vis e (λa. ctree_bind (g a) h) ∧
  ctree_bind (Br k)    h = Br (λb. ctree_bind (k b) h)
Proof
  rw[ctree_bind_def]
  >- (
    Cases_on `h r`
    >> rw[Once ctree_unfold, Once ctree_push_inj_def, FUN_EQ_THM, ctree_bind_INR_id]
  )
  >> rw[Once ctree_unfold, FUN_EQ_THM]
QED

Theorem ctree_bind_right_identity[simp]:
  ctree_bind t Ret = t
Proof
  rw[Once ctree_bisimulation]
  >> qexists `λp q. p = ctree_bind q Ret` >> rw[]
  >> Cases_on `t` >> gvs[]
QED

Theorem ctree_bind_assoc:
  ctree_bind (ctree_bind t k) k'
  = ctree_bind t (λx. ctree_bind (k x) k')
Proof
  rw[Once ctree_strong_bisimulation]
  >> qexists `λp q. ∃v.
    p = ctree_bind (ctree_bind v k) k' ∧
    q = ctree_bind v (λx. ctree_bind (k x) k')
  ` >> rw[]
  >- metis_tac[]
  >> Cases_on `v` >> gvs[]
  >> metis_tac[]
QED

(* Iter *)

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

Theorem ctree_iter_thm:
  ctree_iter body seed = ctree_bind (body seed) (λlr.
    case lr of
    | INL i => Guard (ctree_iter body i)
    | INR r => Ret r
  )
Proof
  rw[ctree_iter_def]
  >> qmatch_goalsub_abbrev_tac `ctree_unfold f _ = ctree_bind _ f'`
  >> rw[Once ctree_strong_bisimulation]
  >> qexists `λp q. ∃v. p = ctree_unfold f v ∧ q = ctree_bind v f'`
  >> unabbrev_all_tac >> rw[]
  >- metis_tac[]
  >> first_x_assum $ strip_assume_tac o ONCE_REWRITE_RULE[ctree_unfold]
  >> gvs[AllCaseEqs(), Guard_def, Guard'_def]
  >> metis_tac[]
QED

(* Loop *)

Definition ctree_loop_def:
  ctree_loop body seed = ctree_iter (λa.
    ctree_bind (body a) (λcb.
      case cb of
      | INL c => Ret (INL (INL c))
      | INR b => Ret (INR b)
    )
  ) (INR seed)
End

(* Stuck *)

Definition ctree_stuck_def:
  ctree_stuck = ctree_unfold (λ_. Guard' ()) ()
End

Theorem ctree_stuck_thm:
  ctree_stuck = Guard ctree_stuck
Proof
  rw[ctree_stuck_def, Once ctree_unfold_guard]
QED

(* Bisimulations -- sbisim and wbisim
Consider the natural LTS over ctrees, where every node is a state with transitions
Ret r   --- val r --> ∅
Tau u   ---   τ   --> u
Vis e g ---obs e a--> g a
Br  k   --- ch b  --> k b
∅ denotes a stuck state.
Then:
(=) is bisimulation over this LTS
sbisim is bisimulation over this LTS up to finite numbers of ch b transitions
wbisim is bisimulation over this LTS up to finite numbers of ch b and τ transitions

It is possible to define an alternate LTS by omitting ch b transitions from the start; this
is the approach the paper takes, and we do the same.
*)

(* strip_ch t t' means t' is reachable from t via a finite number of ch b nodes
and t' has no more ch b transitions (i.e. t' is not a branch node) *)
Inductive strip_ch:
[~ret:] strip_ch (Ret r) (Ret r)
[~tau:] strip_ch (Tau u) (Tau u)
[~vis:] strip_ch (Vis e g) (Vis e g)
[~br:] strip_ch (k b) t' ==> strip_ch (Br k) t'
End

Theorem strip_ch_diff[simp]:
  ¬strip_ch t (Br k) ∧
  ¬strip_ch (Ret r) (Tau u)   ∧
  ¬strip_ch (Ret r) (Vis e g) ∧
  ¬strip_ch (Tau u) (Ret r)   ∧
  ¬strip_ch (Tau u) (Vis e g) ∧
  ¬strip_ch (Vis e g) (Ret r) ∧
  ¬strip_ch (Vis e g) (Tau u)
Proof
  rw[] >> Induct_on `strip_ch` >> rw[]
QED

Theorem strip_ch_same[simp]:
  (strip_ch (Ret r) (Ret r') <=> r = r') ∧
  (strip_ch (Tau u) (Tau u') <=> u = u') ∧
  (strip_ch (Vis e g) (Vis e' g') <=> e = e' ∧ g = g')
Proof
  rw[] >> eq_tac >> rw[Once strip_ch_cases]
QED

Theorem strip_ch_guard[simp]:
  strip_ch (Guard t) t' <=> strip_ch t t'
Proof
  rw[] >> rw[Guard_def, Once strip_ch_cases]
QED

Theorem not_strip_ch_stuck[simp]:
  ¬strip_ch ctree_stuck t
Proof
  Induct_on `strip_ch` >> rw[]
  >> rw[Once ctree_stuck_thm, Guard_def, FUN_EQ_THM]
  >> metis_tac[]
QED

Theorem not_strip_ch_self_iff_stuck:
  (∀t'. ¬strip_ch t t') ==> t = ctree_stuck
Proof
  rw[Once ctree_bisimulation]
  >> qexists `λp q. (∀v. ¬strip_ch p v) ∧ q = ctree_stuck`
  >> rw[] >~ [`Br`]
  >- (
    qexists `λb. ctree_stuck`
    >> rw[GSYM Guard_def, ctree_stuck_thm]
    >> metis_tac[strip_ch_rules]
  ) >> metis_tac[strip_ch_same]
QED

(* LTS definition *)
Datatype:
  ctree_label = val 'r | tau | obs 'e 'a
End

Inductive ctree_lts:
[~ret:] ctree_lts (Ret r) (val r) ctree_stuck
[~tau:] ctree_lts (Tau u) (tau) u
[~vis:] ctree_lts (Vis e g) (obs e a) (g a)
[~br:] ctree_lts (k v) l t ==> ctree_lts (Br k) l t
End

Theorem ctree_lts_resp_strip_ch[local]:
  strip_ch p p' ∧ ctree_lts p' l q ==> ctree_lts p l q
Proof
  Cases_on `∃k. p = Br k` >- (
    gvs[] >> qid_spec_tac `k`
    >> Induct_on `strip_ch`
    >> rw[] >> gvs[]
    >> Cases_on `k b` >> Cases_on `p'`
    >> gvs[Once ctree_lts_cases]
    >> metis_tac[ctree_lts_rules]
  )
  >> Cases_on `p` >> Cases_on `p'` >> gvs[]
QED

Theorem strip_ch_imp_ctree_lts:
  (∀p r.     strip_ch p (Ret r)   ==> ctree_lts p (val r) ctree_stuck) ∧
  (∀p u.     strip_ch p (Tau u)   ==> ctree_lts p (tau) u            ) ∧
  (∀p e g a. strip_ch p (Vis e g) ==> ctree_lts p (obs e a) (g a)    )
Proof
  metis_tac[ctree_lts_rules, ctree_lts_resp_strip_ch]
QED

Theorem not_ctree_lts_stuck:
  ¬ctree_lts ctree_stuck l q
Proof
  Induct_on `ctree_lts`
  >> rw[] >~ [`Br`]
  >- (rw[Once ctree_stuck_thm, Guard_def, FUN_EQ_THM] >> metis_tac[])
  >> gvs[Once ctree_stuck_thm, Guard_def]
QED

Definition ctree_sbisim_def:
  ctree_sbisim = BISIM_REL ctree_lts
End

(* Equational theory *)

Theorem ctree_sbisim_refl:
  ctree_sbisim t t
Proof
  rw[ctree_sbisim_def, BISIM_REL_def]
  >> qexists `(=)`
  >> rw[BISIM_ID]
QED

Theorem ctree_sbisim_sym:
  ctree_sbisim t t' ==> ctree_sbisim t' t
Proof
  rw[ctree_sbisim_def, BISIM_REL_def]
  >> qexists `inv R`
  >> rw[BISIM_INV]
QED

Theorem ctree_sbisim_trans:
  ctree_sbisim u v ∧ ctree_sbisim v w ==> ctree_sbisim u w
Proof
  rw[ctree_sbisim_def, BISIM_REL_def]
  >> qexists `R' O R`
  >> metis_tac[BISIM_O, O_DEF]
QED

Theorem ctree_sbisim_ret:
  ctree_sbisim (Ret r) (Ret r') <=> r = r'
Proof
  eq_tac >> rw[ctree_sbisim_refl]
  >> gvs[ctree_sbisim_def, BISIM_REL_def, BISIM_def]
  >> first_x_assum $ dxrule_then strip_assume_tac
  >> `∃p'. ctree_lts (Ret r) (val r') p'` by metis_tac[ctree_lts_rules]
  >> rfs[Once ctree_lts_cases]
QED

Theorem ctree_sbisim_tau:
  ctree_sbisim (Tau u) (Tau v) <=> ctree_sbisim u v
Proof
  eq_tac >> rw[ctree_sbisim_def, BISIM_REL_def, BISIM_def] >| [
    (* ==> *)
    qexists `R`
    >> `∃p'. ctree_lts (Tau u) tau p' ∧ R p' v` by metis_tac[ctree_lts_rules]
    >> rfs[Once ctree_lts_cases]
    >> metis_tac[],
    (* <== *)
    qexists `λp q. p = Tau u ∧ q = Tau v ∨ R p q` >> rw[] >| [
      rfs[Once ctree_lts_cases] >> rw[],
      rfs[Once ctree_lts_cases] >> rw[],
      metis_tac[],
      metis_tac[]
    ]
  ]
QED

Theorem pred_comm_bisim[local]:
  (∀x. ∃R. BISIM ts R ∧ R (f x) (g x)) ==> (∃R. BISIM ts R ∧ ∀x. R (f x) (g x))
Proof
  rw[] 
  >> qexists `λa b. ∃x R. BISIM ts R ∧ R a b`
  >> rw[] >> rw[BISIM_def]
  >> metis_tac[]
QED

Theorem ctree_sbisim_vis:
  ctree_sbisim (Vis e g) (Vis e' g') <=> e = e' ∧ (∀a. ctree_sbisim (g a) (g' a))
Proof
  eq_tac >~ [`_ ⇒ ctree_sbisim (Vis e g) (Vis e' g')`]
  >> rw[ctree_sbisim_def, BISIM_REL_def]
  (* <== *)
  >- (
    dxrule_then strip_assume_tac pred_comm_bisim
    >> gvs[BISIM_def]
    >> qexists `λp q. p = Vis e g ∧ q = Vis e g' ∨ R p q` >> rw[] >| [
      rfs[Once ctree_lts_cases] >> rw[],
      rfs[Once ctree_lts_cases] >> rw[],
      metis_tac[],
      metis_tac[]
    ]
  )
  (* ==> *)
  >> gvs[BISIM_def]
  >> `∃p'. ctree_lts (Vis e g) (obs e' a) p' ∧ R p' (g' a)` by metis_tac[ctree_lts_rules]
  >> rfs[Once ctree_lts_cases] 
  >> qexists `R` >> metis_tac[]
QED

(* This is not an iff, since the assumption here is less general than required *)
Theorem ctree_sbisim_br:
  (∀b. ∃b'. ctree_sbisim (k b) (k' b')) ∧
  (∀b'. ∃b. ctree_sbisim (k b) (k' b'))
    ==> ctree_sbisim (Br k) (Br k')
Proof
  rw[]
QED


Theorem ctree_sbisim_guard:
  ctree_sbisim (Guard t) t
Proof
  rw[ctree_sbisim_def, BISIM_REL_def, BISIM_def]
  >> qexists `λp q. p = Guard q ∨ p = q` >> rw[]
  >| [
    qexists `p'` >> gvs[Once ctree_lts_cases]
  ]
QED

