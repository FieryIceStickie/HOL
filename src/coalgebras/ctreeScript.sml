(*
  This file defines a type for coinductive choice trees (ctree), as
  explained in Chappe et al.'s 2023 paper titled "Choice Trees".

  This implementation differs from the paper by replacing the stepping
  branch node BrS with a Tau node (the paper uses Step . = BrS 1 (λ_ -> .), and we have
  Step = Guard o Tau).
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
  arithmetic list llist alist option relation pair
  combin companion fixedPoint bisimulation itreeTau
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
  (ctree_rep t1 = ctree_rep t2) <=> (t1 = t2)
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

Theorem ctree_unfold_thm:
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

(* Automation for case simps *)
val ctree_srule = SIMP_RULE bool_ss [ ctree_11, ctree_distinct];

fun cases_to_simp q th = LIST_CONJ [
  th |> Q.INST [q |-> `Ret r`] |> ctree_srule,
  th |> Q.INST [q |-> `Tau u`] |> ctree_srule,
  th |> Q.INST [q |-> `Vis e g`] |> ctree_srule,
  th |> Q.INST [q |-> `Br k`] |> ctree_srule
];

(* --- Combinators --- *)
Definition Guard_def:
  Guard t = Br (λb. t)
End

Theorem Guard_distinct[simp]:
  ¬(Guard t = Ret r) ∧
  ¬(Guard t = Tau u) ∧
  ¬(Guard t = Vis e g)
Proof
  rw[Guard_def]
QED

Definition Guard'_def:
  Guard' t = Br' (λb. t)
End

(* Possibly worth adding these to unfold *)
Definition BrS_def:
  BrS t = Br (Tau o t)
End

Theorem BrS_distinct[simp]:
  ¬(BrS k = Ret r) ∧
  ¬(BrS k = Tau u) ∧
  ¬(BrS k = Vis e g)
Proof
  rw[BrS_def]
QED

Definition Step_def:
  Step t = Guard (Tau t)
End

Theorem Step_distinct[simp]:
  ¬(Step t = Ret r) ∧
  ¬(Step t = Tau u) ∧
  ¬(Step t = Vis e g)
Proof
  rw[Step_def]
QED

Theorem ctree_unfold_guard:
  f seed = Guard' s ==> ctree_unfold f seed = Guard (ctree_unfold f s)
Proof
  rw[Guard_def, Guard'_def, Once ctree_unfold_thm, FUN_EQ_THM]
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
  >> gvs[Once ctree_unfold_thm, ctree_push_inj_def]
  >> fs[Once ctree_unfold_thm]
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
    >> rw[Once ctree_unfold_thm, Once ctree_push_inj_def, FUN_EQ_THM, ctree_bind_INR_id]
  )
  >> rw[Once ctree_unfold_thm, FUN_EQ_THM]
QED

Theorem ctree_bind_guard[simp]:
  ctree_bind (Guard t) h = Guard (ctree_bind t h)
Proof
  rw[Guard_def]
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

Theorem ctree_bind_ret_inv:
  ctree_bind t k = Ret r <=> ∃r'. t = Ret r' ∧ k r' = Ret r
Proof
  eq_tac >> Cases_on `t` >> rw[ctree_bind_thm]
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

Definition ctree_iter_fn_def:
  ctree_iter_fn body lr =
    case lr of
    | INL i => Guard (ctree_iter body i)
    | INR r => Ret r
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
  >> first_x_assum $ strip_assume_tac o ONCE_REWRITE_RULE[ctree_unfold_thm]
  >> gvs[AllCaseEqs(), Guard_def, Guard'_def]
  >> metis_tac[]
QED

Theorem ctree_iter_fn_thm:
  ctree_iter body seed = ctree_bind (body seed) (ctree_iter_fn body)
Proof
  rw[Once ctree_iter_thm]
  >> qmatch_goalsub_abbrev_tac `ctree_bind (body seed) f`
  >> `f = ctree_iter_fn body` by rw[FUN_EQ_THM, ctree_iter_fn_def]
  >> rw[]
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

Theorem ctree_bind_stuck[simp]:
  ctree_bind ctree_stuck k = ctree_stuck
Proof
  rw[Once ctree_strong_bisimulation]
  >> qexists `λp q. p = ctree_bind ctree_stuck k ∧ q = ctree_stuck`
  >> rw[]
  >> rfs[Once ctree_stuck_thm, Guard_def]
QED

(* Bisimulations -- sbisim and wbisim *)

(* strip_ch t t' means t' is one of the nodes "absorbed" by the branch node t
or t is just not a branch node
Of use because it allows us to reason about the missing branch transitions *)
Inductive strip_ch:
[~ret:] strip_ch (Ret r) (Ret r)
[~tau:] strip_ch (Tau u) (Tau u)
[~vis:] strip_ch (Vis e g) (Vis e g)
[~br:] strip_ch (k b) t' ==> strip_ch (Br k) t'
End

Theorem not_strip_ch_br[simp]:
  ¬strip_ch t (Br k)
Proof
  rw[] >> Induct_on `strip_ch` >> rw[]
QED

Theorem strip_ch_same[simp]:
  (strip_ch (Ret r) p <=> p = Ret r) ∧
  (strip_ch (Tau u) p <=> p = Tau u) ∧
  (strip_ch (Vis e g) p <=> p = Vis e g)
Proof
  rw[] >> eq_tac >> rw[Once strip_ch_cases]
QED

Theorem strip_ch_guard[simp]:
  strip_ch (Guard t) t' <=> strip_ch t t'
Proof
  rw[] >> rw[Guard_def, Once strip_ch_cases]
QED

Theorem not_strip_ch_stuck:
  (∀t'. ¬strip_ch t t') <=> t = ctree_stuck
Proof
  eq_tac >| [
    rw[Once ctree_bisimulation]
    >> qexists `λp q. (∀v. ¬strip_ch p v) ∧ q = ctree_stuck`
    >> rw[] >~ [`Br`]
    >- (
      qexists `λb. ctree_stuck`
      >> rw[GSYM Guard_def, ctree_stuck_thm]
      >> metis_tac[strip_ch_rules]
    ) >> metis_tac[strip_ch_same],
    Induct_on `strip_ch` >> rw[]
    >> rw[Once ctree_stuck_thm, Guard_def, FUN_EQ_THM]
    >> metis_tac[]
  ]
QED

(* LTS definition *)
Datatype:
  ctree_label = val 'r | tau | obs 'e 'a
End

Theorem ctree_label_distinct = TypeBase.distinct_of ``:('a, 'b, 'r) ctree_label``;

Inductive ctree_lts:
[~ret:] ctree_lts (Ret r) (val r) ctree_stuck
[~tau:] ctree_lts (Tau u) tau u
[~vis:] ctree_lts (Vis e g) (obs e a) (g a)
[~br:] ctree_lts (k v) l t ==> ctree_lts (Br k) l t
End

(* Redefine to pass into cases_to_simp *)
Theorem ctree_lts_pcases:
  ctree_lts p l q <=>
  (∃r. p = Ret r ∧ l = val r ∧ q = ctree_stuck) ∨
  (p = Tau q ∧ l = tau) ∨
  (∃a e g. p = Vis e g ∧ l = obs e a ∧ q = g a) ∨
  (∃k v. p = Br k ∧ ctree_lts (k v) l q)
Proof
  rw[Once ctree_lts_cases]
QED

Theorem ctree_lts_pcases_simp[simp] = cases_to_simp `p` ctree_lts_pcases;

Theorem ctree_lts_guard:
  ctree_lts (Guard t) = ctree_lts t
Proof
  rw[FUN_EQ_THM, EQ_IMP_THM, Guard_def, ctree_lts_rules]
  >> metis_tac[]
QED

Theorem ctree_lts_brS:
  ∀k b. ctree_lts (BrS k) tau (k b)
Proof
  rw[BrS_def] >> metis_tac[]
QED

Theorem ctree_lts_tau_brS:
  ∀k v l p. ctree_lts (Tau (k v)) l p ==> ctree_lts (BrS k) l p
Proof
  rw[BrS_def] >> metis_tac[]
QED

Theorem ctree_lts_step:
  ∀t. ctree_lts (Step t) tau t
Proof
  rw[Step_def, ctree_lts_guard, ctree_lts_tau]
QED

(* For bind, note the different val r types *)
Definition ctree_lts_same_def:
  ctree_lts_same l l' <=> l = tau ∧ l' = tau ∨ ∃e a. l = obs e a ∧ l' = obs e a
End

Theorem ctree_lts_same_sym:
  ctree_lts_same l l' ==> ctree_lts_same l' l
Proof
  rw[ctree_lts_same_def]
QED

Definition ctree_sbisim_def:
  ctree_sbisim = BISIM_REL ctree_lts
End


(* For when you need to expand sbisim but don't want to expand everything *)
Theorem ctree_sbisim_lts:
  ctree_sbisim p q ∧ ctree_lts p l p' ==> ∃q'. ctree_lts q l q' ∧ ctree_sbisim p' q'
Proof
  rw[ctree_sbisim_def, BISIM_REL_def, BISIM_def]
  >> metis_tac[]
QED

Theorem not_ctree_lts_stuck:
  (∀l t'. ¬ctree_lts t l t') <=> t = ctree_stuck
Proof
  eq_tac >- (
    rw[Once ctree_bisimulation]
    >> qexists `λp q. (∀l t'. ¬ctree_lts p l t') ∧ q = ctree_stuck`
    >> rw[] >~ [`Br`]
    >- (
      qexists `λb. ctree_stuck`
      >> rw[GSYM Guard_def, ctree_stuck_thm]
      >> metis_tac[ctree_lts_rules]
    ) 
    >> metis_tac[ctree_lts_rules]
  )
  >> Induct_on `ctree_lts` >> rw[]
  >> rw[Once ctree_stuck_thm, Guard_def, FUN_EQ_THM]
  >> metis_tac[]
QED


(*
The following theorems refer to this setup
    ------l-------
   /              \
  p --> p' ---l--> p''

  q --> q' ---l--> q''
   \              /
    ------l-------
where --> is strip_tau
(p, q), (p', q'), (p'', q'') are all bisimilar.
*)

(* p --> p' ---l--> p'' <=> p ---l--> p'' *)
Theorem ch_l_iff_l[local]:
  (∃p'. strip_ch p p' ∧ ctree_lts p' l p'') <=> ctree_lts p l p''
Proof
  eq_tac
  >- (Induct_on `strip_ch` >> rw[] >> metis_tac[ctree_lts_rules])
  >>Cases_on `p = ctree_stuck`
  >- metis_tac[not_ctree_lts_stuck]
  >> drule_at Concl $ iffLR not_strip_ch_stuck
  >> first_x_assum mp_tac >> qid_spec_tac `p`
  >> Induct_on `ctree_lts` >> rw[] >~ [`Br`]
  >- metis_tac[strip_ch_rules, not_strip_ch_stuck, not_ctree_lts_stuck]
  >> metis_tac[strip_ch_same, ctree_lts_rules]
QED

(* p --> p' ==> p ---l--> p'' ∧ p' ---l--> p'' *)
Theorem ch_imp_l[local]:
  strip_ch p p' ==> ∃l p''. ctree_lts p l p'' ∧ ctree_lts p' l p''
Proof
  Cases_on `p' = ctree_stuck` >- gvs[Once ctree_stuck_thm, Guard_def]
  >> dxrule_at Concl $ iffLR not_ctree_lts_stuck
  >> metis_tac[ch_l_iff_l]
QED

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

Theorem ctree_sbisim_eq:
  ctree_sbisim p q <=> ctree_sbisim p = ctree_sbisim q
Proof
  rw[EQ_IMP_THM, FUN_EQ_THM]
  >> metis_tac[ctree_sbisim_refl, ctree_sbisim_sym, ctree_sbisim_trans]
QED

Theorem ctree_sbisim_stuck_uniq_0[local]:
  ctree_sbisim t ctree_stuck ==> t = ctree_stuck
Proof
  spose_not_then strip_assume_tac
  >> gvs[GSYM not_ctree_lts_stuck, ctree_sbisim_def, BISIM_REL_def, BISIM_def]
  >> metis_tac[not_ctree_lts_stuck]
QED

Theorem ctree_sbisim_stuck_uniq:
  (ctree_sbisim t ctree_stuck <=> t = ctree_stuck) ∧
  (ctree_sbisim ctree_stuck t <=> t = ctree_stuck)
Proof
  metis_tac[ctree_sbisim_refl, ctree_sbisim_sym, ctree_sbisim_stuck_uniq_0]
QED

Theorem ctree_sbisim_ret[simp]:
  ctree_sbisim (Ret r) (Ret r') <=> r = r'
Proof
  rw[EQ_IMP_THM, ctree_sbisim_refl]
  >> qspec_then `r` strip_assume_tac ctree_lts_ret
  >> dxrule_all ctree_sbisim_lts
  >> rw[]
QED

Theorem ctree_sbisim_tau[simp]:
  ctree_sbisim (Tau u) (Tau v) <=> ctree_sbisim u v
Proof
  rw[EQ_IMP_THM] >- (
    qspec_then `u` strip_assume_tac ctree_lts_tau
    >> dxrule_all ctree_sbisim_lts
    >> rw[Once ctree_lts_cases]
  )
  >> rw[ctree_sbisim_def, Once BISIM_REL_strong_thm]
  >> qexists `λp q. p = Tau u ∧ q = Tau v`
  >> rw[GSYM ctree_sbisim_def]
QED

Theorem ctree_sbisim_vis:
  ctree_sbisim (Vis e g) (Vis e' g') <=> e = e' ∧ (∀a. ctree_sbisim (g a) (g' a))
Proof
  eq_tac >> strip_tac >- (
    `∀a. e = e' ∧ ctree_sbisim (g a) (g' a)` suffices_by rw[]
    >> strip_tac
    >> qspecl_then [`a`, `e`, `g`] strip_assume_tac ctree_lts_vis
    >> dxrule_all ctree_sbisim_lts
    >> rw[Once ctree_lts_cases]
  )
  >> rw[ctree_sbisim_def, Once BISIM_REL_strong_thm]
  >> qexists `λp q. p = Vis e g ∧ q = Vis e g'`
  >> rw[GSYM ctree_sbisim_def]
  >> gvs[Once ctree_lts_cases]
  >> metis_tac[ctree_lts_rules]
QED

Theorem ctree_sbisim_br:
  (∀b. ∃b'. ctree_sbisim (k b) (k' b')) ∧
  (∀b'. ∃b. ctree_sbisim (k b) (k' b'))
    ==> ctree_sbisim (Br k) (Br k')
Proof
  strip_tac >> rw[ctree_sbisim_def, Once BISIM_REL_strong_thm]
  >> qexists `λp q. p = Br k ∧ q = Br k'`
  >> rw[GSYM ctree_sbisim_def]
  >> gvs[Once ctree_lts_cases]
  >> metis_tac[ctree_lts_rules, ctree_sbisim_lts, ctree_sbisim_sym]
QED

Theorem ctree_sbisim_guard:
  ctree_sbisim (Guard t) t
Proof
  rw[ctree_sbisim_def, Once BISIM_REL_strong_thm]
  >> qexists `λp q. p = Guard q` >> rw[GSYM ctree_sbisim_def]
  >> metis_tac[ctree_lts_guard, ctree_sbisim_refl]
QED

Theorem ctree_sbisim_guard_eq = ctree_sbisim_guard |> SIMP_RULE std_ss [ctree_sbisim_eq];

Theorem ctree_sbisim_strip_ch:
  (∀p'. strip_ch p p' ==> ∃q'. strip_ch q q' ∧ ctree_sbisim p' q') ∧
  (∀q'. strip_ch q q' ==> ∃p'. strip_ch p p' ∧ ctree_sbisim p' q')
    ==> ctree_sbisim p q
Proof
  rw[] >> rw[ctree_sbisim_def, Once BISIM_REL_strong_thm]
  >> qexists `λu v. p = u ∧ q = v` >> rw[GSYM ctree_sbisim_def]
  >> metis_tac[ch_l_iff_l, ctree_sbisim_lts, ctree_sbisim_sym]
QED

Theorem ctree_sbisim_brS:
  (∀b. ∃b'. ctree_sbisim (k b) (k' b')) ∧
  (∀b'. ∃b. ctree_sbisim (k b) (k' b'))
    ==> ctree_sbisim (Br k) (Br k')
Proof
  metis_tac[ctree_sbisim_br, ctree_sbisim_tau]
QED

Theorem ctree_sbisim_step:
  ctree_sbisim (Step t) (Tau t)
Proof
  rw[Step_def, ctree_sbisim_guard_eq, ctree_sbisim_refl]
QED

Theorem ctree_sbisim_step_eq = ctree_sbisim_step |> SIMP_RULE std_ss [ctree_sbisim_eq];

Theorem ctree_sbisim_not_0[local]:
  (¬ctree_sbisim (Ret r) (Tau u)) ∧
  (¬ctree_sbisim (Ret r) (Vis e g)) ∧
  (¬ctree_sbisim (Tau u) (Vis e g))
Proof
  rw[] >> spose_not_then strip_assume_tac >| [
    qspec_then `r` strip_assume_tac ctree_lts_ret,
    qspec_then `r` strip_assume_tac ctree_lts_ret,
    qspec_then `u` strip_assume_tac ctree_lts_tau
  ]
  >> dxrule_all ctree_sbisim_lts
  >> rw[Once ctree_lts_cases]
QED

Theorem ctree_sbisim_not[simp]:
  (¬ctree_sbisim (Ret r) (Tau u)) ∧
  (¬ctree_sbisim (Ret r) (Vis e g)) ∧
  (¬ctree_sbisim (Tau u) (Ret r)) ∧
  (¬ctree_sbisim (Tau u) (Vis e g)) ∧
  (¬ctree_sbisim (Vis e g) (Ret r)) ∧
  (¬ctree_sbisim (Vis e g) (Tau u))
Proof
  metis_tac[ctree_sbisim_not_0, ctree_sbisim_sym]
QED

(* Experimental, possibly not very useful *)
Theorem ctree_sbisim_sym_strong_guard_thm:
  ctree_sbisim t t' <=> ∃R. symmetric R ∧ R t t' ∧ ∀p q. R p q ==>
    (∀l p'. ctree_lts p l p' ==> ∃q'. ctree_lts q l q' ∧ (R p' q' ∨ ctree_sbisim p' q')) ∨
    (∃u. p = Guard u ∧ R u q)
Proof
  rw[EQ_IMP_THM] >- (
    rfs[ctree_sbisim_def] >> rw[GSYM ctree_sbisim_def]
    >> dxrule_then strip_assume_tac $ iffLR BISIM_REL_sym_strong_thm
    >> gvs[GSYM ctree_sbisim_def]
    >> metis_tac[]
  )
  >> rw[ctree_sbisim_def, Once BISIM_REL_sym_strong_thm]
  >> qexists `R` >> simp[GSYM ctree_sbisim_def]
  >> Induct_on `ctree_lts` >> rw[] >~ [`Br`]
  >> first_x_assum $ dxrule_then strip_assume_tac
  >- metis_tac[ctree_lts_rules, ctree_sbisim_refl]
  >- (dxrule_then strip_assume_tac ctree_lts_br >> gvs[ctree_lts_guard] >> gvs[Guard_def])
  >> gvs[ctree_lts_guard]
  >> metis_tac[ctree_lts_guard, ctree_lts_rules, ctree_sbisim_refl, Guard_def]
QED

(* Common case *)
Theorem ctree_sbisim_lts_ret:
  ctree_sbisim p q ∧ ctree_lts p (val r) ctree_stuck ==> ctree_lts q (val r) ctree_stuck
Proof
  metis_tac[ctree_sbisim_lts, ctree_sbisim_stuck_uniq]
QED

Theorem ctree_sbisim_br_ret:
  ctree_sbisim (Br k) (Ret r) ==> ctree_sbisim (k b) (Ret r) ∨ k b = ctree_stuck
Proof
  Cases_on `k b = ctree_stuck` >- rw[]
  >> dxrule_at Concl $ iffLR not_ctree_lts_stuck >> rw[]
  >> rename[`ctree_lts (k b) l t`]
  >> disj1_tac
  >> rw[] >> irule ctree_sbisim_strip_ch >> rw[]
  >- (
    drule_then strip_assume_tac strip_ch_br
    >> dxrule_then strip_assume_tac ch_imp_l
    >> dxrule_all ctree_sbisim_lts >> rw[]
    >> Cases_on `p'`
    >> gvs[Once ctree_lts_cases]
    >> rfs[Once ctree_lts_cases]
    >> rw[ctree_sbisim_refl]
  )
  >> qexists `Ret r` >> rw[ctree_sbisim_refl]
  >> drule_then strip_assume_tac ctree_lts_br
  >> dxrule_all ctree_sbisim_lts >> rw[]
  >> qpat_x_assum `ctree_lts (Ret _) _ _` mp_tac
  >> rw[Once ctree_lts_cases]
  >> gvs[ctree_sbisim_stuck_uniq]
  >> dxrule_then strip_assume_tac $ iffRL ch_l_iff_l
  >> gvs[Once ctree_lts_cases]
QED

Theorem ctree_lts_bind_cases:
  ∀p. ctree_lts (ctree_bind p k) l p'' ==> ∃l'.
    (∃p'. ctree_lts_same l l' ∧ ctree_lts p l' p' ∧ p'' = ctree_bind p' k) ∨
    (∃r. ctree_lts p (val r) ctree_stuck ∧ ctree_lts (k r) l p'')
Proof
  Induct_on `ctree_lts` >> rw[]
  >> Cases_on `p` >> gvs[]
  >> metis_tac[ctree_bind_stuck, ctree_lts_rules, ctree_lts_same_def]
QED

Theorem ctree_lts_bind_ret[local]:
  ctree_lts p (val r) ctree_stuck ∧ ctree_lts (k r) l p' ==> ctree_lts (ctree_bind p k) l p'
Proof
  Induct_on `ctree_lts` >> rw[]
  >> first_x_assum $ dxrule_then strip_assume_tac
  >> qmatch_goalsub_abbrev_tac `ctree_lts (Br c) l p'`
  >> metis_tac[ctree_lts_rules]
QED

Theorem ctree_lts_bind_tau_vis[local]:
  ∀k. ctree_lts p l' p' ∧ ctree_lts_same l l' ==> ctree_lts (ctree_bind p k) l (ctree_bind p' k)
Proof
  Induct_on `ctree_lts` >> rw[ctree_lts_same_def, ctree_lts_rules]
  >> qmatch_goalsub_abbrev_tac `ctree_lts (Br c) l q`
  >> metis_tac[ctree_lts_rules]
QED

Theorem ctree_lts_bind_rules = LIST_CONJ [ctree_lts_bind_ret, ctree_lts_bind_tau_vis];

Theorem ctree_sbisim_bind_t[local]:
  ctree_sbisim t t' ==> ctree_sbisim (ctree_bind t k) (ctree_bind t' k)
Proof
  rw[] >> rw[ctree_sbisim_def, Once BISIM_REL_sym_strong_thm]
  >> qexists `λp q. ∃u v. p = ctree_bind u k ∧ q = ctree_bind v k ∧ ctree_sbisim u v`
  >> rw[GSYM ctree_sbisim_def]
  >- (gvs[symmetric_def] >> metis_tac[ctree_sbisim_sym])
  >- metis_tac[]
  >> dxrule_then strip_assume_tac ctree_lts_bind_cases
  >> metis_tac[
    ctree_sbisim_lts, ctree_lts_bind_rules,
    ctree_sbisim_refl, ctree_sbisim_lts_ret
  ]
QED

Theorem ctree_sbisim_bind_k[local]:
  (∀r. ctree_sbisim (k r) (k' r)) ==> ctree_sbisim (ctree_bind t k) (ctree_bind t k')
Proof
  rw[] >> rw[ctree_sbisim_def, Once BISIM_REL_strong_thm]
  >> qexists `λp q. ∃u. p = ctree_bind u k ∧ q = ctree_bind u k'`
  >> rw[GSYM ctree_sbisim_def]
  >- metis_tac[]
  >> dxrule_then strip_assume_tac ctree_lts_bind_cases
  >> metis_tac[
    ctree_sbisim_lts, ctree_lts_bind_rules,
    ctree_sbisim_refl, ctree_sbisim_sym
  ]
QED

Theorem ctree_sbisim_bind:
  ctree_sbisim t t' ∧ (∀r. ctree_sbisim (k r) (k' r))
    ==> ctree_sbisim (ctree_bind t k) (ctree_bind t' k')
Proof
  metis_tac[ctree_sbisim_bind_t, ctree_sbisim_bind_k, ctree_sbisim_trans]
QED

Inductive iter_chain:
[~retl:]
  ctree_lts u (val (INL s)) ctree_stuck ∧
  iter_chain k tl (k s) l u'
  ==> iter_chain k (s::tl) u l u'
[~retr:]
  ctree_lts u (val (INR r)) ctree_stuck
  ==> iter_chain k [] u (val (INR r)) ctree_stuck
[~tau:]
  ctree_lts u (tau: ('a, 'b, 'c + 'd) ctree_label) u'
  ==> iter_chain k [] u (tau: ('a, 'b, 'c + 'd) ctree_label) u'
[~vis:]
  ctree_lts u (obs e a) u'
  ==> iter_chain k [] u (obs e a) u'
End

Theorem ctree_lts_imp_iter_chain:
  (∀l p'. ctree_lts p l p' ==> ctree_lts q l p') ∧ iter_chain k seeds p l p'
    ==> iter_chain k seeds q l p'
Proof
  Induct_on `iter_chain` >> rw[iter_chain_rules]
QED

Theorem ctree_lts_iter_fn_cases:
  ∀u. ctree_lts (ctree_bind u (ctree_iter_fn k)) l p ==> ∃seeds.
    (∃r. iter_chain k seeds u (val (INR r)) ctree_stuck ∧ l = val r ∧ p = ctree_stuck) ∨
    (∃l' u'. iter_chain k seeds u l' u' ∧ ctree_lts_same l l' ∧ p = ctree_bind u' (ctree_iter_fn k))
Proof
  Induct_on `ctree_lts` >> rw[] >~ [`Br`] >- (
    Cases_on `u` >> gvs[ctree_iter_fn_def, AllCaseEqs(), Guard_def] >- (
      (* retl *)
      first_x_assum $ qspec_then `k i` strip_assume_tac
      >> gvs[ctree_iter_fn_thm]
      >> qexists `i::seeds`
      >> metis_tac[iter_chain_cases, ctree_lts_rules]
    ) (* br *)
    >> first_x_assum $ qspec_then `k'' v` strip_assume_tac >> gvs[]
    >> metis_tac[ctree_lts_rules, ctree_lts_imp_iter_chain]
  )
  >> Cases_on `u` >> gvs[ctree_iter_fn_def, AllCaseEqs()]
  >> metis_tac[iter_chain_rules, ctree_lts_rules, ctree_lts_same_def]
QED

Theorem ctree_lts_iter_fn_retr[local]:
  iter_chain k seeds u (val (INR r)) ctree_stuck
    ==> ctree_lts (ctree_bind u (ctree_iter_fn k)) (val r) ctree_stuck
Proof
  Induct_on `iter_chain` >> rw[]
  >> irule ctree_lts_bind_ret
  >| [qexists `INL s`, qexists `INR r`]
  >> rw[ctree_iter_fn_def, ctree_lts_guard, ctree_iter_fn_thm, ctree_lts_rules]
QED

Theorem ctree_lts_iter_fn_tau_vis[local]:
  iter_chain k seeds u l' u' ∧ ctree_lts_same l l'
    ==> ctree_lts (ctree_bind u (ctree_iter_fn k)) l (ctree_bind u' (ctree_iter_fn k))
Proof
  Induct_on `iter_chain` >> rw[] >- (
    first_x_assum $ drule_then strip_assume_tac
    >> dxrule_then strip_assume_tac ctree_lts_bind_ret
    >> gvs[ctree_iter_fn_def, ctree_lts_guard, ctree_iter_fn_thm]
  )
  >> metis_tac[ctree_lts_same_def, ctree_lts_bind_tau_vis]
QED

Theorem ctree_lts_iter_fn_rules = LIST_CONJ [ctree_lts_iter_fn_retr, ctree_lts_iter_fn_tau_vis];

Theorem ctree_sbisim_iter_chain:
  ∀v. (∀s. ctree_sbisim (k s) (k' s)) ∧ ctree_sbisim u v ∧ iter_chain k seeds u l p
  ==> ∃q. iter_chain k' seeds v l q ∧ ctree_sbisim p q
Proof
  Induct_on `iter_chain` >> rw[]
  >- metis_tac[iter_chain_cases, ctree_sbisim_lts_ret]
  >> metis_tac[ctree_sbisim_lts, iter_chain_rules, ctree_sbisim_stuck_uniq]
QED

Theorem ctree_sbisim_iter:
  (∀s. ctree_sbisim (k s) (k' s)) ==> ctree_sbisim (ctree_iter k s) (ctree_iter k' s)
Proof
  rw[] >> rw[ctree_sbisim_def, Once BISIM_REL_sym_strong_thm]
  >> qexists `λp q. ∃k k' u v. (∀s. ctree_sbisim (k s) (k' s)) ∧
    p = ctree_bind u (ctree_iter_fn k) ∧
    q = ctree_bind v (ctree_iter_fn k') ∧
    ctree_sbisim u v`
  >> rw[GSYM ctree_sbisim_def]
  >- (gvs[symmetric_def] >> metis_tac[ctree_sbisim_sym])
  >- metis_tac[ctree_iter_fn_thm]
  >> dxrule_then strip_assume_tac ctree_lts_iter_fn_cases
  >> metis_tac[ctree_sbisim_iter_chain, ctree_sbisim_stuck_uniq, ctree_lts_iter_fn_rules]
QED

Theorem ctree_sbisim_loop:
  (∀s. ctree_sbisim (k s) (k' s)) ==> ctree_sbisim (ctree_loop k s) (ctree_loop k' s)
Proof
  rw[ctree_loop_def] >> irule ctree_sbisim_iter
  >> metis_tac[ctree_sbisim_bind, ctree_sbisim_refl]
QED

(* wbisim *)

Theorem ETS_CASES[local]:
  ETS ts tau p p' <=> p = p' ∨ ∃u. ts p tau u ∧ ETS ts tau u p'
Proof
  rw[ETS_def, Once RTC_CASES1]
QED

Theorem ETS_INDUCT[local, rule_induction]:
  ∀ts tau P. (∀p. P p p) ∧ (
    (∀p p' q. ts p tau p' ∧ P p' q ⇒ P p q) ∨
    (∀p q' q. P p q' ∧ ts q' tau q ⇒ P p q)
  ) ⇒ ∀p0 q0. ETS ts tau p0 q0 ⇒ P p0 q0
Proof
  rw[] >| [irule RTC_INDUCT, irule RTC_INDUCT_RIGHT1] >> rw[]
  >> qexists `λx y. ts x tau' y`
  >> metis_tac[ETS_def]
QED

Theorem WTS_INDUCT[local]:
  ∀ts tau P.
    (∀p l q. l ≠ tau ∧ ts p l q ⇒ P p l q) ∧
    (∀p p' l q. ts p tau p' ∧ P p' l q ⇒ P p l q) ∧
    (∀p l q' q. P p l q' ∧ ts q' tau q ⇒ P p l q)
  ⇒ ∀p0 l0 q0. l0 ≠ tau ∧ WTS ts tau p0 l0 q0 ⇒ P p0 l0 q0
Proof
  rw[WTS_def]
  >> qhdtm_x_assum `ETS` mp_tac
  >> qpat_x_assum `ts _ _ _` mp_tac
  >> Induct_on `ETS` >> reverse (rw[])
  >- metis_tac[]
  >> qhdtm_x_assum `ETS` mp_tac
  >> qpat_x_assum `ts _ _ _` mp_tac
  >> Induct_on `ETS` >> rw[]
  >> metis_tac[]
QED

Inductive ctree_wlts:
[~lts:] ctree_lts p l q ∧ l ≠ tau ==> ctree_wlts p l q
[~tauL:] ctree_lts p tau p' ∧ ctree_wlts p' l q ==> ctree_wlts p l q
[~tauR:] ctree_wlts p l q' ∧ ctree_lts q' tau q ==> ctree_wlts p l q
End

Theorem ctree_wlts_wts_equiv:
  ctree_wlts p l q <=> l ≠ tau ∧ WTS ctree_lts tau p l q
Proof
  eq_tac >- (
    Induct_on `ctree_wlts` >> rw[]
    >> metis_tac[TS_IMP_WTS, TS_IMP_ETS, ETS_REFL, ETS_WTS_ETS]
  )
  >> match_mp_tac WTS_INDUCT
  >> metis_tac[ctree_wlts_rules]
QED

Theorem ctree_wlts_not_tau[simp]:
  ctree_wlts p l q ==> l ≠ tau
Proof
  metis_tac[ctree_wlts_wts_equiv]
QED

Theorem ctree_wlts_val_stuck:
  ctree_wlts p (val r) p' ==> p' = ctree_stuck
Proof
  Induct_on `ctree_wlts` >> rw[]
  >- (first_x_assum mp_tac >> Induct_on `ctree_lts` >> rw[])
  >> metis_tac[not_ctree_lts_stuck]
QED

Inductive ctree_elts:
[~refl:] ctree_elts p p
[~tau:] ctree_lts p tau p' ∧ ctree_elts p' q ==> ctree_elts p q
End

Theorem ctree_elts_trans:
  ctree_elts p p' ∧ ctree_elts p' p'' ==> ctree_elts p p''
Proof
  Induct_on `ctree_elts` >> metis_tac[ctree_elts_rules]
QED

Theorem ctree_elts_ets_equiv:
  ctree_elts p q <=> ETS ctree_lts tau p q
Proof
  eq_tac
  >- (Induct_on `ctree_elts` >> metis_tac[ETS_REFL, TS_IMP_ETS, ETS_TRANS])
  >> Induct_on `ETS`
  >> metis_tac[ctree_elts_rules]
QED

Theorem ctree_elts_tauR[local]:
  ctree_elts p q' ∧ ctree_lts q' tau q ⇒ ctree_elts p q
Proof
  Induct_on `ctree_elts` >> metis_tac[ctree_elts_rules]
QED

Theorem ctree_elts_rules_sym:
  (∀p. ctree_elts p p) ∧
  (∀p p' q. ctree_lts p tau p' ∧ ctree_elts p' q ⇒ ctree_elts p q) ∧
  (∀p q' q. ctree_elts p q' ∧ ctree_lts q' tau q ⇒ ctree_elts p q)
Proof
  metis_tac[ctree_elts_rules, ctree_elts_tauR]
QED

Theorem ctree_elts_cases_right:
  ctree_elts p q <=> p = q ∨ ∃q'. ctree_elts p q' ∧ ctree_lts q' tau q
Proof
  eq_tac
  >- (Induct_on `ctree_elts` >> metis_tac[ctree_elts_rules])
  >> metis_tac[ctree_elts_rules_sym]
QED

Theorem ctree_elts_lts_elts:
  ctree_wlts p l q <=> l ≠ tau ∧ ∃p' q'. ctree_elts p p' ∧ ctree_lts p' l q' ∧ ctree_elts q' q
Proof
  eq_tac
  >- (Induct_on `ctree_wlts` >> metis_tac[ctree_elts_rules_sym])
  >> rw[ctree_wlts_wts_equiv, ctree_elts_ets_equiv]
  >> metis_tac[TS_IMP_WTS, ETS_WTS_ETS]
QED

Theorem ctree_elts_wlts_elts:
  ctree_elts p p' ∧ ctree_wlts p' l q' ∧ ctree_elts q' q ==> ctree_wlts p l q
Proof
  metis_tac[ctree_elts_trans, ctree_elts_lts_elts]
QED

Theorem ctree_wlts_prules:
  (∀r. ctree_wlts (Ret r) (val r) ctree_stuck) ∧
  (∀u l p. ctree_wlts u l p ==> ctree_wlts (Tau u) l p) ∧
  (∀a e g. ctree_wlts (Vis e g) (obs e a) (g a)) ∧
  (∀k v l p. ctree_wlts (k v) l p ==> ctree_wlts (Br k) l p)
Proof
  rw[] >~ [`Br`] >- (
    first_x_assum mp_tac >> Induct_on `ctree_wlts`
    >> metis_tac[ctree_lts_rules, ctree_wlts_rules]
  )
  >> metis_tac[ctree_lts_rules, ctree_wlts_rules, ctree_label_distinct]
QED

Theorem ctree_wlts_pcases:
  ctree_wlts p l q <=>
  (∃r.     p = Ret r   ∧ l = val r ∧ q = ctree_stuck) ∨
  (∃u.     p = Tau u   ∧ ctree_wlts u l q) ∨
  (∃a e g. p = Vis e g ∧ l = obs e a ∧ ctree_elts (g a) q) ∨
  (∃k v.   p = Br k    ∧ ctree_wlts (k v) l q)
Proof
  eq_tac >- (
    Induct_on `ctree_wlts` >> rw[]
    >>~- ([`ctree_lts ctree_stuck tau q`], metis_tac[not_ctree_lts_stuck])
    >> gvs[Once ctree_lts_cases]
    >> metis_tac[ctree_wlts_rules, ctree_elts_rules_sym, ctree_lts_rules]
  )
  >> rw[]
  >- (irule ctree_wlts_lts >> rw[ctree_lts_ret])
  >- metis_tac[ctree_wlts_rules, ctree_lts_tau]
  >- (rw[ctree_elts_lts_elts] >> metis_tac[ctree_elts_refl, ctree_lts_vis])
  >> first_x_assum mp_tac >> Induct_on `ctree_wlts`
  >> metis_tac[ctree_lts_rules, ctree_wlts_rules]
QED

Theorem ctree_elts_prules:
  (∀p. ctree_elts p p) ∧
  (∀u. ctree_elts (Tau u) u) ∧
  (∀k v p. ctree_elts (k v) p ==> p = k v ∨ ctree_elts (Br k) p)
Proof
  rw[] >~ [`Br`] >- (
    first_x_assum mp_tac >> Induct_on `ctree_elts`
    >> metis_tac[ctree_lts_rules, ctree_elts_rules, ctree_elts_trans]
  )
  >> metis_tac[ctree_lts_rules, ctree_elts_rules]
QED

Theorem ctree_elts_pcases:
  ctree_elts p q <=>
  (∃r.     p = Ret r   ∧ q = Ret r) ∨
  (∃u.     p = Tau u   ∧ (p = q ∨ ctree_elts u q)) ∨
  (∃a e g. p = Vis e g ∧ q = Vis e g) ∨
  (∃k v.   p = Br k    ∧ (p = q ∨ ∃q' v. ctree_lts (k v) tau q' ∧ ctree_elts q' q))
Proof
  eq_tac >- (
    Induct_on `ctree_elts` >> rw[ctree_cases]
    >> rev_drule_then strip_assume_tac $ iffLR ctree_lts_cases
    >> gvs[]
    >> metis_tac[ctree_elts_rules, ctree_lts_rules]
  )
  >> rw[]
  >> metis_tac[ctree_lts_rules, ctree_elts_rules]
QED

Theorem ctree_elts_pcases_simp[simp] = cases_to_simp `p` ctree_elts_pcases;

Theorem ctree_elts_brS:
  ctree_elts (BrS k) (k b)
Proof
  rw[BrS_def, Once ctree_elts_pcases]
  >> disj2_tac >> qexistsl [`k b`, `b`]
  >> rw[ctree_lts_tau, ctree_elts_refl]
QED

Definition ctree_wbisim_def:
  ctree_wbisim = WBISIM_REL ctree_lts tau
End

Theorem ctree_wlts_tau:
  ctree_wlts (Tau u) = ctree_wlts u
Proof
  rw[FUN_EQ_THM, EQ_IMP_THM]
  >- gvs[Once ctree_wlts_pcases]
  >> metis_tac[ctree_lts_rules, ctree_wlts_rules]
QED

Theorem ctree_wlts_guard:
  ctree_wlts (Guard t) = ctree_wlts t
Proof
  rw[FUN_EQ_THM, EQ_IMP_THM]
  >- gvs[Once ctree_wlts_pcases, Guard_def]
  >> dxrule_then strip_assume_tac $ iffLR ctree_elts_lts_elts
  >> rev_dxrule_then strip_assume_tac $ iffLR ctree_elts_cases
  >> metis_tac[ctree_lts_guard, ctree_elts_rules, ctree_elts_lts_elts]
QED

Theorem ctree_wlts_brS:
  ctree_wlts (k v) l p ==> ctree_wlts (BrS k) l p
Proof
  rw[BrS_def]
  >> irule $ cj 4 ctree_wlts_prules
  >> qexists `v`
  >> rw[ctree_wlts_tau]
QED

Theorem ctree_wlts_step:
  ctree_wlts (Step t) = ctree_wlts t
Proof
  rw[Step_def, ctree_wlts_guard, ctree_wlts_tau]
QED

Theorem ctree_wbisim_lts:
  ctree_wbisim p q ∧ ctree_lts p l p' ∧ l ≠ tau ==> ∃q'. ctree_wlts q l q' ∧ ctree_wbisim p' q'
Proof
  rw[ctree_wbisim_def, WBISIM_REL_def]
  >> `∃q'. ctree_wlts q l q' ∧ R p' q'` suffices_by metis_tac[]
  >> gvs[WBISIM_def]
  >> metis_tac[ctree_wlts_wts_equiv]
QED

Theorem ctree_wbisim_lts_tau:
  ctree_wbisim p q ∧ ctree_lts p tau p' ==> ∃q'. ctree_elts q q' ∧ ctree_wbisim p' q'
Proof
  rw[ctree_wbisim_def, WBISIM_REL_def]
  >> `∃q'. ctree_elts q q' ∧ R p' q'` suffices_by metis_tac[]
  >> gvs[WBISIM_def]
  >> metis_tac[ctree_elts_ets_equiv]
QED

Theorem ctree_wbisim_elts:
  ctree_wbisim p q ∧ ctree_elts p p' ==> ∃q'. ctree_elts q q' ∧ ctree_wbisim p' q'
Proof
  qid_spec_tac `q`
  >> Induct_on `ctree_elts` >> rw[]
  >> metis_tac[ctree_elts_rules, ctree_wbisim_lts_tau, ctree_elts_trans]
QED

Theorem ctree_wbisim_wlts:
  ctree_wbisim p q ∧ ctree_wlts p l p' ==> ∃q'. ctree_wlts q l q' ∧ ctree_wbisim p' q'
Proof
  rw[ctree_elts_lts_elts]
  >> dxrule_all ctree_wbisim_elts >> rw[]
  >> dxrule_all ctree_wbisim_lts >> rw[]
  >> dxrule_all ctree_wbisim_elts >> rw[]
  >> metis_tac[ctree_elts_lts_elts, ctree_elts_trans]
QED

Theorem ctree_wbisim_lts_ret:
  ctree_wbisim p q ∧ ctree_lts p (val r) ctree_stuck ==> ctree_wlts q (val r) ctree_stuck
Proof
  rw[] >> dxrule_then strip_assume_tac ctree_wbisim_lts
  >> first_x_assum $ qspecl_then [`ctree_stuck`, `val r`] strip_assume_tac
  >> gvs[]
  >> metis_tac[ctree_wlts_val_stuck]
QED

Theorem ctree_wbisim_wlts_ret:
  ctree_wbisim p q ∧ ctree_wlts p (val r) ctree_stuck ==> ctree_wlts q (val r) ctree_stuck
Proof
  Induct_on `ctree_wlts` >> rw[]
  >- metis_tac[ctree_wbisim_lts_ret]
  >> metis_tac[ctree_wlts_tauL, ctree_wbisim_wlts, ctree_wlts_val_stuck]
QED

(* Equivalence proofs *)

Theorem ctree_wbisim_refl:
  ctree_wbisim t t
Proof
  rw[ctree_wbisim_def, WBISIM_REL_def]
  >> qexists `(=)`
  >> rw[WBISIM_ID]
QED

Theorem ctree_wbisim_sym:
  ctree_wbisim t t' ==> ctree_wbisim t' t
Proof
  rw[ctree_wbisim_def, WBISIM_REL_def]
  >> qexists `inv R`
  >> rw[WBISIM_INV]
QED

Theorem ctree_wbisim_trans:
  ctree_wbisim u v ∧ ctree_wbisim v w ==> ctree_wbisim u w
Proof
  rw[ctree_wbisim_def, WBISIM_REL_def]
  >> qexists `R' O R`
  >> metis_tac[WBISIM_O, O_DEF]
QED

Theorem ctree_wbisim_eq:
  ctree_wbisim p q <=> ctree_wbisim p = ctree_wbisim q
Proof
  rw[EQ_IMP_THM, FUN_EQ_THM]
  >> metis_tac[ctree_wbisim_refl, ctree_wbisim_sym, ctree_wbisim_trans]
QED

(* wbisim theorems *)

Theorem ctree_wbisim_thm:
  ctree_wbisim p0 q0 <=> ∃R. R p0 q0 ∧
  (∀p q. R p q ⇒
    (∀l p'. l ≠ tau ∧ ctree_lts p l p' ==> ∃q'. ctree_wlts q l q' ∧ R p' q') ∧
    (∀l q'. l ≠ tau ∧ ctree_lts q l q' ==> ∃p'. ctree_wlts p l p' ∧ R p' q') ∧
    (∀p'. ctree_lts p tau p' ==> ∃q'. ctree_elts q q' ∧ R p' q') ∧
    (∀q'. ctree_lts q tau q' ==> ∃p'. ctree_elts p p' ∧ R p' q'))
Proof
  rw[ctree_wbisim_def, WBISIM_REL_def, WBISIM_def, EQ_IMP_THM]
  >> qexists `R`
  >> metis_tac[ctree_wlts_wts_equiv, ctree_elts_ets_equiv]
QED

Theorem ctree_wbisim_strong_thm:
  ctree_wbisim p0 q0 <=> ∃R. R p0 q0 ∧
  (∀p q. R p q ⇒
    (∀l p'. l ≠ tau ∧ ctree_lts p l p' ==> ∃q'. ctree_wlts q l q' ∧ (R p' q' ∨ ctree_wbisim p' q')) ∧
    (∀l q'. l ≠ tau ∧ ctree_lts q l q' ==> ∃p'. ctree_wlts p l p' ∧ (R p' q' ∨ ctree_wbisim p' q')) ∧
    (∀p'. ctree_lts p tau p' ==> ∃q'. ctree_elts q q' ∧ (R p' q' ∨ ctree_wbisim p' q')) ∧
    (∀q'. ctree_lts q tau q' ==> ∃p'. ctree_elts p p' ∧ (R p' q' ∨ ctree_wbisim p' q')))
Proof
  rw[EQ_IMP_THM, Once ctree_wbisim_thm]
  >- (qexists `R` >> metis_tac[])
  >> rw[Once ctree_wbisim_thm]
  >> qexists `λp q. R p q ∨ ctree_wbisim p q`
  >> metis_tac[ctree_wbisim_lts, ctree_wbisim_lts_tau, ctree_wbisim_sym]
QED

Theorem ctree_wbisim_sym_thm:
  ctree_wbisim p0 q0 <=> ∃R. symmetric R ∧ R p0 q0 ∧
  (∀p q. R p q ⇒
    (∀l p'. l ≠ tau ∧ ctree_lts p l p' ==> ∃q'. ctree_wlts q l q' ∧ R p' q') ∧
    (∀p'. ctree_lts p tau p' ==> ∃q'. ctree_elts q q' ∧ R p' q'))
Proof
  rw[EQ_IMP_THM, Once ctree_wbisim_thm] >- (
    qexists `λp q. R p q ∨ R q p`
    >> rw[symmetric_def]
    >> metis_tac[]
  )
  >> rw[Once ctree_wbisim_thm]
  >> qexists `R` >> rw[]
  >> gvs[symmetric_def]
  >> metis_tac[]
QED

Theorem ctree_wbisim_sym_strong_thm:
  ctree_wbisim p0 q0 <=> ∃R. symmetric R ∧ R p0 q0 ∧
  (∀p q. R p q ⇒
    (∀l p'. l ≠ tau ∧ ctree_lts p l p' ==> ∃q'. ctree_wlts q l q' ∧ (R p' q' ∨ ctree_wbisim p' q')) ∧
    (∀p'. ctree_lts p tau p' ==> ∃q'. ctree_elts q q' ∧ (R p' q' ∨ ctree_wbisim p' q')))
Proof
  rw[EQ_IMP_THM, Once ctree_wbisim_sym_thm]
  >- (qexists `R` >> metis_tac[])
  >> rw[Once ctree_wbisim_sym_thm]
  >> qexists `λp q. R p q ∨ ctree_wbisim p q` >> rw[]
  >- (gvs[symmetric_def] >> metis_tac[ctree_wbisim_sym])
  >> metis_tac[ctree_wbisim_lts, ctree_wbisim_lts_tau, ctree_wbisim_sym]
QED

(* Equational theory *)

Theorem ctree_sbisim_imp_wbisim:
  ctree_sbisim p q ==> ctree_wbisim p q
Proof
  rw[ctree_sbisim_def, ctree_wbisim_def, BISIM_REL_IMP_WBISIM_REL]
QED

Theorem ctree_wbisim_ret:
  ctree_wbisim (Ret r) (Ret r') <=> r = r'
Proof
  rw[EQ_IMP_THM, ctree_wbisim_refl]
  >> qspec_then `r` strip_assume_tac ctree_lts_ret
  >> dxrule_all ctree_wbisim_lts_ret >> rw[]
  >> gvs[Once ctree_wlts_pcases]
QED

Theorem ctree_wbisim_tau:
  ctree_wbisim (Tau u) u
Proof
  rw[Once ctree_wbisim_strong_thm]
  >> qexists `λp q. p = Tau q` >> rw[]
  >- gvs[Once ctree_lts_cases]
  >- metis_tac[ctree_wlts_lts, ctree_wbisim_refl, ctree_wlts_tau]
  >- (gvs[Once ctree_lts_cases] >> metis_tac[ctree_wbisim_refl, ctree_elts_refl])
  >> metis_tac[ctree_elts_rules, ctree_lts_rules, ctree_wbisim_refl]
QED

Theorem ctree_wbisim_tau_eq = ctree_wbisim_tau |> SIMP_RULE std_ss [ctree_wbisim_eq];

Theorem ctree_wbisim_vis_e[local]:
  ctree_wbisim (Vis e g) (Vis e' g') ==> e = e'
Proof
  rw[]
  >> qspecl_then [`a`, `e`, `g`] strip_assume_tac ctree_lts_vis
  >> dxrule_then strip_assume_tac ctree_wbisim_lts
  >> first_x_assum $ dxrule_then strip_assume_tac
  >> gvs[Once ctree_wlts_pcases]
QED

Theorem ctree_wbisim_vis:
  ctree_wbisim (Vis e g) (Vis e' g') <=> e = e' ∧ ∀a. ctree_wbisim (g a) (g' a)
Proof
  rw[EQ_IMP_THM] >- metis_tac[ctree_wbisim_vis_e] >- (
    drule_then strip_assume_tac ctree_wbisim_vis_e >> rw[]
    >> rename[`ctree_wbisim (Vis e' h) (Vis e' h')`]
    >> irule $ iffRL ctree_wbisim_sym_strong_thm
    >> qexists `λp q. ∃e g g'. p = g a ∧ q = g' a ∧ ctree_wbisim (Vis e g) (Vis e g')`
    >> rw[]
    >- (gvs[symmetric_def] >> metis_tac[ctree_wbisim_sym])
    >- metis_tac[]
    >> qspecl_then [`a`, `e`, `g`] strip_assume_tac ctree_lts_vis
    >> dxrule_then strip_assume_tac ctree_wbisim_lts
    >> first_x_assum $ dxrule_then strip_assume_tac
    >> gvs[]
    >> dxrule_then strip_assume_tac $ iffLR ctree_wlts_pcases >> rw[]
    >- (drule_all ctree_wbisim_lts >> metis_tac[ctree_elts_wlts_elts, ctree_elts_refl])
    >> metis_tac[ctree_wbisim_lts_tau, ctree_elts_trans]
  )
  >> irule $ iffRL ctree_wbisim_strong_thm
  >> qexists `λp q. p = Vis e g ∧ q = Vis e g'`
  >> rw[] >> gvs[Once ctree_lts_cases]
  >> metis_tac[ctree_lts_rules, ctree_wlts_cases, ctree_wbisim_sym, ctree_label_distinct]
QED

Theorem ctree_wbisim_brS:
  (∀b. ∃b'. ctree_wbisim (k b) (k' b')) ∧
  (∀b'. ∃b. ctree_wbisim (k b) (k' b'))
    ==> ctree_wbisim (BrS k) (BrS k')
Proof
  rw[BrS_def]
  >> irule $ iffRL ctree_wbisim_strong_thm
  >> qexists `λp q. p = BrS k ∧ q = BrS k'`
  >> rw[BrS_def] >> gvs[Ntimes ctree_lts_cases 2]
  >> rw[GSYM BrS_def]
  >> metis_tac[ctree_elts_brS]
QED

Theorem ctree_wbisim_not_0[local]:
  ¬ctree_wbisim (Ret r) (Vis e g)
Proof
  spose_not_then strip_assume_tac
  >> drule_then strip_assume_tac ctree_wbisim_lts
  >> qspec_then `r` strip_assume_tac ctree_lts_ret
  >> first_x_assum $ dxrule_then strip_assume_tac
  >> gvs[Once ctree_wlts_pcases]
QED

Theorem ctree_wbisim_not[simp]:
  (¬ctree_wbisim (Ret r) (Vis e g)) ∧
  (¬ctree_wbisim (Vis e g) (Ret r))
Proof
  metis_tac[ctree_wbisim_not_0, ctree_wbisim_sym]
QED

Definition itc_def:
  itc (t: ('a, 'b, 'c) itree) = ctree_unfold (λit.
    case it of
    | Ret r   => Ret' r
    | Tau u   => Tau' u
    | Vis e g => Vis' e g
  ) t
End

Theorem itc_thm:
  (itc (Ret r) = Ret r) ∧
  (itc (Tau u) = Tau (itc u)) ∧
  (itc (Vis e g) = Vis e (itc o g))
Proof
  rw[itc_def]
  >> rw[Once ctree_unfold_thm]
  >> rw[FUN_EQ_THM, GSYM itc_def]
QED

Theorem itc_cases:
  ∀t t'. itc t = t' <=>
  (∃r.     t = Ret r   ∧ Ret r           = t') ∨
  (∃u.     t = Tau u   ∧ Tau   (itc u)   = t') ∨
  (∃a e g. t = Vis e g ∧ Vis e (itc o g) = t')
Proof
  rw[EQ_IMP_THM]
  >- (Cases_on `t` >> rw[Ntimes itc_thm 3])
  >> rw[Ntimes itc_thm 3]
QED

Theorem itc_not_br[simp]:
  ∀k. itc t ≠ Br k
Proof
  rw[Once itc_cases]
QED

Theorem itc_11:
  itc p = itc q <=> p = q
Proof
  rw[EQ_IMP_THM]
  >> rw[Once itree_strong_bisimulation]
  >> qexists `λu v. itc u = itc v` >> rw[]
  >> qpat_x_assum `itc p = itc q` kall_tac
  >> Cases_on `t` >> gvs[FUN_EQ_THM, itc_thm]
  >> metis_tac[]
QED

Theorem strip_tau_itc_lts[local]:
  (strip_tau p (Ret r) ==> ctree_wlts (itc p) (val r) ctree_stuck) ∧
  (strip_tau p (Vis e g) ==> ctree_wlts (itc p) (obs e a) (itc (g a)))
Proof
  strip_tac >> Induct_on `strip_tau` >> rw[]
  >> gvs[Once itc_thm, ctree_wlts_tau, ctree_wlts_prules, o_DEF]
QED

Theorem itree_wbisim_imp_ctree_wbisim_itc[local]:
  itree_wbisim p q ==> ctree_wbisim (itc p) (itc q)
Proof
  rw[Once ctree_wbisim_sym_strong_thm]
  >> rename[`itree_wbisim t t'`]
  >> qexists `λu v. ∃p q. u = itc p ∧ v = itc q ∧ itree_wbisim p q`
  >> rw[]
  >- (gvs[symmetric_def] >> metis_tac[itree_wbisim_sym])
  >- metis_tac[]
  >> qpat_x_assum `itree_wbisim t t'` kall_tac
  >> dxrule_then strip_assume_tac $ iffLR ctree_lts_cases
  >> gvs[Once itc_cases]
  >> dxrule_then strip_assume_tac $ iffLR itree_wbisim_cases
  >> gvs[] >~ [`itree_wbisim t t'`] >- (
    qexists `itc t'`
    >> rw[itc_thm, ctree_elts_prules]
    >> disj1_tac >> qexistsl [`Tau t`, `t'`]
    >> rw[itc_thm, itree_wbisim_tau]
  )
  >> metis_tac[
    strip_tau_itc_lts, ctree_wbisim_refl,
    itree_wbisim_rules, ctree_elts_refl
  ]
QED

Theorem ctree_lts_itc_cases[local]:
  ∀p l q. ctree_lts (itc p) l q <=>
  (∃r.     p = Ret r   ∧ l = val r   ∧ q = ctree_stuck) ∨
  (∃u.     p = Tau u   ∧ l = tau     ∧ q = itc u) ∨
  (∃a e g. p = Vis e g ∧ l = obs e a ∧ q = itc (g a))
Proof
  rw[EQ_IMP_THM]
  >> gvs[Once ctree_lts_cases]
  >> gvs[Once itc_cases]
QED

Theorem ctree_wlts_itc_cases[local]:
  ∀p l q. ctree_wlts (itc p) l q <=>
  (∃r.     strip_tau p (Ret r) ∧ l = val r   ∧ q = ctree_stuck) ∨
  (∃a e g. strip_tau p (Vis e g) ∧ l = obs e a ∧ q = itc (g a))
Proof
  rw[EQ_IMP_THM] >- (
    first_x_assum mp_tac
    >> Induct_on `ctree_wlts` >> rw[]
    >>~- ([`ctree_lts ctree_stuck tau q`], metis_tac[not_ctree_lts_stuck])
    >> dxrule_then strip_assume_tac $ iffLR ctree_lts_itc_cases
    >> rw[]
  )
  >> metis_tac[strip_tau_itc_lts]
QED

Theorem ctree_wbisim_itc_imp_itree_wbisim[local]:
  ∀p q. ctree_wbisim (itc p) (itc q) ==> itree_wbisim p q
Proof
  ho_match_mp_tac itree_wbisim_strong_coind >> rw[]
  >> Cases_on `p` >> gvs[itc_thm, ctree_wbisim_tau_eq]

  rename[`Ret r`]
  >> qspec_then `r` strip_assume_tac ctree_lts_ret
  >> dxrule_then strip_assume_tac ctree_wbisim_lts
  >> first_x_assum $ resolve_then Any strip_assume_tac ctree_lts_ret
  >> gvs[]
  >> first_x_assum $ dxrule_then strip_assume_tac


QED

Theorem itree_wbisim_iff_ctree_wbisim_itc:
  itree_wbisim p q <=> ctree_wbisim (itc p) (itc q)
Proof
  metis_tac[itree_wbisim_imp_ctree_wbisim_itc, ctree_wbisim_itc_imp_itree_wbisim]
QED


(* Examples *)

(* An interesting example of a stuck ctree *)
Theorem ctree_iter_stuck[local]:
  ctree_iter (λx. Ret $ INL (x+1)) 0 = ctree_stuck
Proof
  rw[Once ctree_strong_bisimulation]
  >> qexists `λp q. ∃n. p = ctree_iter (λx. Ret $ INL (x+1)) n ∧ q = ctree_stuck`
  >> rw[]
  >- metis_tac[]
  >> gvs[Once ctree_iter_thm, Guard_def]
  >> rw[Once ctree_stuck_thm, Guard_def]
  >> metis_tac[]
QED

(* Example of ctree_iter *)
Definition ctree_collatz_tree[local]:
  collatz_tree = Br (λb.
    ctree_iter (λn.
      ctree_bind (Ret (if EVEN n then n DIV 2 else 3 * n + 1)) (λm.
        if m = b then Ret (INR b) else Ret (INL m)
  )) b)
End

Theorem collatz_124[local]:
  ctree_lts collatz_tree (val 1) ctree_stuck ∧
  ctree_lts collatz_tree (val 2) ctree_stuck ∧
  ctree_lts collatz_tree (val 4) ctree_stuck
Proof
  rw[] >> qmatch_goalsub_abbrev_tac `val n`
  >> rw[ctree_collatz_tree] >> irule ctree_lts_br
  >> qexists `n` >> rw[Abbr `n`]
  >> rw[ctree_iter_fn_thm, ctree_iter_fn_def, ctree_lts_guard, ctree_lts_rules]
QED

(* Counterexample to converse of ctree_sbisim_strip_ch *)
Definition BrVis1[local]:
  brvis1 = Br (λb. Vis 7 (λa. Ret (if b then a else ¬a)))
End

Definition BrVis2[local]:
  (brvis2: (bool, bool, num, bool) ctree) = Br (λb. Vis 7 (λa. Ret b))
End

Theorem BrVis1_lts[local]:
  ctree_lts brvis1 l p <=> ∃a b. l = obs 7 a ∧ p = Ret b
Proof
  eq_tac >> rw[BrVis1, Once ctree_lts_cases]
  >- (Cases_on `v` >> rfs[Once ctree_lts_cases])
  >> qexists `a = b`
  >> qspecl_then [
    `a`,`7`, `λa'. (Ret (if a = b then a' else ¬a'): (bool, bool, num, bool) ctree)`
  ] strip_assume_tac $ cj 3 ctree_lts_rules
  >> `(if a = b then b else ¬a) = b` by metis_tac[]
  >> gvs[]
QED

Theorem BrVis2_lts[local]:
  ctree_lts brvis2 l p <=> ∃a b. l = obs 7 a ∧ p = Ret b
Proof
  eq_tac >> rw[BrVis2, Once ctree_lts_cases]
  >- (Cases_on `v` >> rfs[Once ctree_lts_cases])
  >> qexists `b`
  >> qabbrev_tac `(g: bool -> (bool, bool, num, bool) ctree) = λa. Ret b`
  >> metis_tac[ctree_lts_rules]
QED

Theorem ctree_lts_brvis12[local]:
  ctree_lts brvis1 l q <=> ctree_lts brvis2 l q
Proof
  rw[BrVis1_lts, BrVis2_lts]
QED

Theorem brvis_sbisim[local]:
  ctree_sbisim brvis1 brvis2
Proof
  rw[ctree_sbisim_def, BISIM_REL_def, BISIM_def]
  >> qexists `λp q. p = brvis1 ∧ q = brvis2 ∨ p = q`
  >> rw[] >> metis_tac[ctree_lts_brvis12]
QED

(* Counterexample to ctree_wbisim_br *)

Definition btk_def[local]:
  btk = (Ret: bool -> (bool, bool, bool, bool) ctree)
End

Definition btk'_def[local]:
  btk' = Tau o btk
End

Theorem not_ctree_wbisim_brtau_k[local]:
  (∀b. ∃b'. ctree_wbisim (btk b) (btk' b')) ∧
  (∀b'. ∃b. ctree_wbisim (btk b) (btk' b')) ∧
  ¬ctree_wbisim (Br btk') (Br btk)
Proof
  rw[btk_def, btk'_def]
  >- metis_tac[ctree_wbisim_tau, ctree_wbisim_sym]
  >- metis_tac[ctree_wbisim_tau, ctree_wbisim_sym]
  >> spose_not_then strip_assume_tac
  >> `ctree_lts (Br (Tau o Ret)) tau (Ret F: (bool, bool, bool, bool) ctree)` by metis_tac[ctree_lts_rules, o_DEF]
  >> dxrule_all ctree_wbisim_lts_tau >> rw[]
  >> spose_not_then strip_assume_tac
  >> dxrule_then strip_assume_tac $ iffLR ctree_elts_cases
  >- (
    gvs[]
    >> `ctree_lts (Br Ret) (val T) (ctree_stuck: (bool, bool, bool, bool) ctree)` by metis_tac[ctree_lts_rules]
    >> dxrule_then strip_assume_tac ctree_wbisim_sym
    >> dxrule_then strip_assume_tac ctree_wbisim_lts
    >> first_x_assum $ dxrule_then strip_assume_tac
    >> gvs[Once ctree_wlts_pcases]
  )
  >> gvs[Ntimes ctree_lts_cases 2]
QED



