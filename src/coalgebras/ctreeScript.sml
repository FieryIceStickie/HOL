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
  combin companion fixedPoint set_relation
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

Theorem datatype_itree:
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


