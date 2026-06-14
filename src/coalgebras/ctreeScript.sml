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
  pred_set arithmetic list option relation
  combin bisimulation itreeTau
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

Theorem ctree_unfold_eq[local]:
  (ctree_unfold f s = Ret r   <=> f s = Ret' r) ∧
  (ctree_unfold f s = Tau u   <=> ∃u'. f s = Tau' u' ∧ ctree_unfold f u' = u) ∧
  (ctree_unfold f s = Vis e g <=> ∃g'. f s = Vis' e g' ∧ (λa. ctree_unfold f (g' a)) = g) ∧
  (ctree_unfold f s = Br k    <=> ∃k'. f s = Br' k' ∧ (λv. ctree_unfold f (k' v)) = k)
Proof
  Cases_on `f s` >> rw[] >> gvs[Once ctree_unfold_thm, ctree_11, ctree_distinct, FUN_EQ_THM]
QED

Theorem ctree_unfold_sym_eq[simp]:
  (ctree_unfold f s = Ret r   <=> f s = Ret' r) ∧
  (ctree_unfold f s = Tau u   <=> ∃u'. f s = Tau' u' ∧ ctree_unfold f u' = u) ∧
  (ctree_unfold f s = Vis e g <=> ∃g'. f s = Vis' e g' ∧ (λa. ctree_unfold f (g' a)) = g) ∧
  (ctree_unfold f s = Br k    <=> ∃k'. f s = Br' k' ∧ (λv. ctree_unfold f (k' v)) = k) ∧
  (Ret r   = ctree_unfold f s <=> f s = Ret' r) ∧
  (Tau u   = ctree_unfold f s <=> ∃u'. f s = Tau' u' ∧ ctree_unfold f u' = u) ∧
  (Vis e g = ctree_unfold f s <=> ∃g'. f s = Vis' e g' ∧ (λa. ctree_unfold f (g' a)) = g) ∧
  (Br k    = ctree_unfold f s <=> ∃k'. f s = Br' k' ∧ (λv. ctree_unfold f (k' v)) = k)
Proof
  rw[ctree_unfold_eq] >> metis_tac[ctree_unfold_eq]
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

Theorem ctree_strong_coind:
  (∀r t. R (Ret r) t ==> t = Ret r) ∧
  (∀u t. R (Tau u) t ==> ∃v. t = Tau v ∧ (R u v ∨ u = v)) ∧
  (∀e g t. R (Vis e g) t ==> ∃h. t = Vis e h ∧ ∀a. R (g a) (h a) ∨ g a = h a) ∧
  (∀k t. R (Br k) t ==> ∃j. t = Br j ∧ ∀b. R (k b) (j b) ∨ k b = j b)
    ==> ∀t1 t2. R t1 t2 ==> t1 = t2
Proof
  rw[] >> rw[Once ctree_strong_bisimulation]
  >> qexists `R` >> rw[]
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
val ctree_srule = SIMP_RULE bool_ss [ctree_11, ctree_distinct];

fun cases_to_simp q thm = LIST_CONJ [
  thm |> Q.INST [q |-> `Ret r`] |> ctree_srule,
  thm |> Q.INST [q |-> `Tau u`] |> ctree_srule,
  thm |> Q.INST [q |-> `Vis e g`] |> ctree_srule,
  thm |> Q.INST [q |-> `Br k`] |> ctree_srule
];

(* --- Combinators --- *)
Definition Guard_def:
  Guard t = Br (λb. t)
End

Definition Guard'_def:
  Guard' t = Br' (λb. t)
End

(* Unfold doesn't support multi ctor combinators *)
Definition BrS_def:
  BrS k = Br (Tau o k)
End

Definition Step_def:
  Step = Guard o Tau
End

Theorem ctree_unfold_guard:
  f seed = Guard' s ==> ctree_unfold f seed = Guard (ctree_unfold f s)
Proof
  rw[Guard_def, Guard'_def, Once ctree_unfold_thm, FUN_EQ_THM]
QED

(* Stuck & Spin *)
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

Theorem ctree_tau_not_stuck[local]:
  Tau u ≠ ctree_stuck
Proof
  rw[Once ctree_stuck_thm, Guard_def]
QED

Theorem ctree_comb_distinct_lemma[local]:
  ALL_DISTINCT [Ret r; Tau u; Vis e g; Guard t] ∧
  ALL_DISTINCT [Ret r; Tau u; Vis e g; BrS k] ∧
  ALL_DISTINCT [Ret r; Tau u; Vis e g; Step t] ∧
  ALL_DISTINCT [Ret r; Tau u; Vis e g; ctree_stuck] ∧
  ALL_DISTINCT [Ret r; ctree_spin; Vis e g; Br k] ∧
  ctree_stuck ≠ ctree_spin ∧
  ctree_stuck ≠ BrS k ∧
  ctree_stuck ≠ Step t ∧
  ctree_spin ≠ Guard t ∧
  ctree_spin ≠ BrS k ∧
  ctree_spin ≠ Step t
Proof
  rw[ALL_DISTINCT]
  >> rw[Once ctree_stuck_thm, Once ctree_spin_thm]
  >> rw[Guard_def, BrS_def, Step_def, FUN_EQ_THM]
  >> metis_tac[ctree_tau_not_stuck]
QED

Theorem ctree_comb_distinct[simp] = ctree_comb_distinct_lemma
  |> SIMP_RULE std_ss [ALL_DISTINCT, MEM, GSYM CONJ_ASSOC, ctree_distinct];

Theorem ctree_comb_eq[simp]:
  (Br k = Guard t     <=> k = λv. t) ∧
  (Br k = BrS k'      <=> k = λv. Tau (k' v)) ∧
  (Br k = Step t      <=> k = λv. Tau t) ∧
  (Guard t = Br k     <=> k = λv. t) ∧
  (Guard t = Guard t' <=> t = t') ∧
  (Guard t = BrS k    <=> ∃u. t = Tau u ∧ k = λv. u) ∧
  (Guard t = Step t'  <=> t = Tau t') ∧
  (BrS k = Br k'      <=> k' = λv. Tau (k v)) ∧
  (BrS k = Guard t    <=> ∃u. t = Tau u ∧ k = λv. u) ∧
  (BrS k = BrS k'     <=> k = k') ∧
  (BrS k = Step t     <=> k = λv. t) ∧
  (Step t = Br k      <=> k = λv. Tau t) ∧
  (Step t = Guard t'  <=> t' = Tau t) ∧
  (Step t = BrS k     <=> k = λv. t) ∧
  (Step t = Step t'   <=> t = t') ∧
  (Br k = ctree_stuck    <=> k = λv. ctree_stuck) ∧
  (Guard t = ctree_stuck <=> t = ctree_stuck) ∧
  (Tau u = ctree_spin <=> u = ctree_spin)
Proof
  rw[]
  >> rw[Once ctree_stuck_thm, Once ctree_spin_thm]
  >> rw[Guard_def, BrS_def, Step_def, FUN_EQ_THM, EQ_IMP_THM]
  >> Cases_on `t`
  >> gvs[]
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
  >> gvs[ctree_push_inj_def]
QED

Theorem ctree_bind_thm[simp]:
  ctree_bind (Ret r)   h = h r ∧
  ctree_bind (Tau u)   h = Tau (ctree_bind u h) ∧
  ctree_bind (Vis e g) h = Vis e (λa. ctree_bind (g a) h) ∧
  ctree_bind (Br k)    h = Br (λv. ctree_bind (k v) h)
Proof
  rw[ctree_bind_def]
  >> Cases_on `h r`
  >> rw[Once ctree_push_inj_def, ctree_bind_INR_id]
  >> rw[FUN_EQ_THM]
QED

Theorem ctree_bind_comb[simp]:
  ctree_bind (Guard t) h = Guard (ctree_bind t h) ∧
  ctree_bind (BrS k) h = BrS (λv. ctree_bind (k v) h) ∧
  ctree_bind (Step t) h = Step (ctree_bind t h)
Proof
  rw[Guard_def, BrS_def, Step_def, FUN_EQ_THM]
QED

Theorem ctree_bind_stuck[simp]:
  ctree_bind ctree_stuck k = ctree_stuck
Proof
  rw[Once ctree_strong_bisimulation]
  >> qexists `λp q. p = ctree_bind ctree_stuck k ∧ q = ctree_stuck`
  >> rw[]
  >> gvs[Once ctree_stuck_thm]
  >> qexists `λv. ctree_stuck`
  >> rw[]
QED

Theorem ctree_bind_spin[simp]:
  ctree_bind ctree_spin k = ctree_spin
Proof
  rw[Once ctree_strong_bisimulation]
  >> qexists `λp q. p = ctree_bind ctree_spin k ∧ q = ctree_spin`
  >> rw[]
  >> gvs[Once ctree_spin_thm]
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

Theorem ctree_iter_fn_simp[simp]:
  ctree_iter_fn body (INL i) = Guard (ctree_iter body i) ∧
  ctree_iter_fn body (INR r) = Ret r
Proof
  rw[ctree_iter_fn_def]
QED

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
  >> rw[]
  >- metis_tac[]
  >> first_x_assum $ strip_assume_tac o ONCE_REWRITE_RULE[ctree_unfold_thm]
  >> unabbrev_all_tac
  >> gvs[AllCaseEqs(), Guard_def, Guard'_def]
  >> metis_tac[]
QED

Theorem ctree_iter_fn_thm:
  ctree_iter body seed = ctree_bind (body seed) (ctree_iter_fn body)
Proof
  `ctree_iter_fn body = λlr. ctree_iter_fn body lr` by metis_tac[]
  >> gvs[ctree_iter_fn_def]
  >> metis_tac[ctree_iter_thm]
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

(* Bisimulations -- sbisim and wbisim *)

(* strip_ch t t' means t' is one of the nodes "absorbed" by the branch node t
   or t is just not a branch node
   Niche usage *)
Inductive strip_ch:
[~ret:] strip_ch (Ret r) (Ret r)
[~tau:] strip_ch (Tau u) (Tau u)
[~vis:] strip_ch (Vis e g) (Vis e g)
[~br:] strip_ch (k v) t' ==> strip_ch (Br k) t'
End

Theorem strip_ch_pcases_simp[simp]:
  (strip_ch (Ret r) q <=> q = Ret r) ∧
  (strip_ch (Tau u) q <=> q = Tau u) ∧
  (strip_ch (Vis e g) q <=> q = Vis e g) ∧
  (strip_ch (Br k) q <=> ∃v. strip_ch (k v) q)
Proof
  rw[] >> rw[Once strip_ch_cases]
QED

Theorem not_strip_ch_br[simp]:
  ¬strip_ch t (Br k)
Proof
  rw[] >> Induct_on `strip_ch` >> rw[]
QED

Theorem strip_ch_combs[simp]:
  (strip_ch (Guard t) q <=> strip_ch t q) ∧
  (strip_ch (BrS k) q <=> ∃u v. q = Tau u ∧ k v = u)∧
  (strip_ch (Step t) q <=> q = Tau t) ∧
  (strip_ch ctree_spin q <=> q = ctree_spin)
Proof
  rw[Guard_def, BrS_def, Step_def, Once ctree_spin_thm]
  >> rw[GSYM ctree_spin_thm]
QED

Theorem not_strip_ch_stuck:
  (∀t'. ¬strip_ch t t') <=> t = ctree_stuck
Proof
  eq_tac >- (
    rw[Once ctree_bisimulation]
    >> qexists `λp q. (∀v. ¬strip_ch p v) ∧ q = ctree_stuck`
    >> rw[]
    >> qexists `λv. ctree_stuck` >> rw[]
  )
  >> Induct_on `strip_ch` >> rw[]
  >> metis_tac[]
QED

Theorem not_strip_ch_stuck_simp[simp]:
  ¬strip_ch ctree_stuck q
Proof
  metis_tac[not_strip_ch_stuck]
QED

(* LTS definition *)
Datatype:
  ctree_label = val 'r | tau | obs 'e 'a
End

Theorem ctree_label_distinct[local] = TypeBase.distinct_of ``:('a, 'b, 'r) ctree_label``;

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

Theorem ctree_lts_val_stuck:
  ctree_lts p (val r) q <=> ctree_lts p (val r) ctree_stuck ∧ q = ctree_stuck
Proof
  eq_tac
  >- (Induct_on `ctree_lts` >> rw[] >> metis_tac[])
  >> rw[]
QED

Theorem ctree_lts_combs[simp]:
  (ctree_lts (Guard t) l q <=> ctree_lts t l q) ∧
  (ctree_lts (BrS k) l q <=> l = tau ∧ ∃v. q = k v) ∧
  (ctree_lts (Step t) l q <=> l = tau ∧ q = t) ∧
  (ctree_lts ctree_spin l q <=> l = tau ∧ q = ctree_spin)
Proof
  rw[Guard_def, BrS_def, Step_def, Once ctree_spin_thm]
  >> metis_tac[]
QED

(* Used for metis_tac/resolve_then *)
Theorem ctree_lts_brS:
  ctree_lts (BrS k) tau (k v)
Proof
  rw[] >> metis_tac[]
QED

Theorem ctree_lts_step:
  ctree_lts (Step t) tau t
Proof
  rw[]
QED

Theorem ctree_lts_spin:
  ctree_lts ctree_spin tau ctree_spin
Proof
  rw[]
QED

Theorem ctree_lts_funpow[simp]:
  ctree_lts (FUNPOW Guard n p) l q <=> ctree_lts p l q
Proof
  Induct_on `n` >> rw[FUNPOW_SUC]
QED

Theorem not_ctree_lts_stuck:
  (∀l t'. ¬ctree_lts t l t') <=> t = ctree_stuck
Proof
  eq_tac >- (
    rw[Once ctree_bisimulation]
    >> qexists `λp q. (∀l t'. ¬ctree_lts p l t') ∧ q = ctree_stuck`
    >> rw[]
    >> qexists `λv. ctree_stuck` >> rw[]
  )
  >> Induct_on `ctree_lts` >> rw[]
  >> metis_tac[]
QED

Theorem ctree_lts_stuck[simp]:
  ¬ctree_lts ctree_stuck l q
Proof
  metis_tac[not_ctree_lts_stuck]
QED

Theorem ctree_lts_obs_carry:
  ctree_lts p (obs e a) p' ==> ∀a'. ∃q'. ctree_lts p (obs e a') q'
Proof
  Induct_on `ctree_lts` >> rw[]
  >> metis_tac[]
QED

Definition ctree_sbisim_def:
  ctree_sbisim = BISIM_REL ctree_lts
End

fun ctree_sbisim_thm_conv thm =
  thm
  |> INST_TYPE [
    alpha |-> ``:('a, 'b, 'c, 'd) ctree``,
    beta |-> ``:('a, 'c, 'd) ctree_label``
  ]
  |> Q.INST [`ts` |-> `ctree_lts`]
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

(* Useful theorem when the bisimulation candidate is obvious *)
Theorem ctree_sbisim_coind =
  BISIM_REL_coind
  |> INST_TYPE [
    alpha |-> ``:('a, 'b, 'c, 'd) ctree``,
    beta |-> ``:('a, 'c, 'd) ctree_label``
  ]
  |> Q.SPEC `ctree_lts`
  |> SIMP_RULE std_ss [GSYM ctree_sbisim_def];

Theorem ctree_sbisim_strong_thm     = ctree_sbisim_thm_conv BISIM_REL_strong_thm;

Theorem ctree_sbisim_sym_thm        = ctree_sbisim_thm_conv BISIM_REL_sym_thm;

Theorem ctree_sbisim_sym_strong_thm = ctree_sbisim_thm_conv BISIM_REL_sym_strong_thm;

(* For when you need to expand sbisim but don't want to expand everything *)
Theorem ctree_sbisim_lts:
  ctree_sbisim p q ∧ ctree_lts p l p' ==> ∃q'. ctree_lts q l q' ∧ ctree_sbisim p' q'
Proof
  rw[ctree_sbisim_thm] >> metis_tac[]
QED

Theorem ctree_sbisim_lts_right:
  ctree_sbisim p q ∧ ctree_lts q l q' ==> ∃p'. ctree_lts p l p' ∧ ctree_sbisim p' q'
Proof
  rw[ctree_sbisim_thm] >> metis_tac[]
QED

Theorem ctree_sbisim_iff_lts:
  ctree_sbisim p q <=>
    (∀l p'. ctree_lts p l p' ⇒ ∃q'. ctree_lts q l q' ∧ ctree_sbisim p' q') ∧
    ∀l q'. ctree_lts q l q' ⇒ ∃p'. ctree_lts p l p' ∧ ctree_sbisim p' q'
Proof
  eq_tac
  >- metis_tac[ctree_sbisim_lts, ctree_sbisim_lts_right]
  >> qid_spec_tac `q` >> qid_spec_tac `p`
  >> ho_match_mp_tac ctree_sbisim_coind
  >> rw[]
  >> metis_tac[ctree_sbisim_lts, ctree_sbisim_lts_right]
QED

(* For bind, note the different val r types *)
Definition ctree_lts_same_def:
  ctree_lts_same l l' <=> l = tau ∧ l' = tau ∨ ∃e a. l = obs e a ∧ l' = obs e a
End

Theorem ctree_lts_same_pcases[simp]:
  (ctree_lts_same tau q       <=> q = tau) ∧
  (ctree_lts_same (obs e a) q <=> q = obs e a) ∧
  (¬ctree_lts_same (val r) q)
Proof
  rw[ctree_lts_same_def]
QED

Theorem ctree_lts_same_cases:
  ∀l. (∃r. l = val r) ∨ ∃l'. ctree_lts_same l l'
Proof
  Cases_on `l` >> rw[]
QED

Theorem ctree_lts_same_sym:
  ctree_lts_same l l' <=> ctree_lts_same l' l
Proof
  rw[EQ_IMP_THM, ctree_lts_same_def]
QED

Theorem ctree_lts_same_qcases[simp] =
  ctree_lts_same_pcases
  |> CONJ_LIST 3
  |> map (SIMP_RULE std_ss [Once ctree_lts_same_sym])
  |> LIST_CONJ;

(*
The following theorems refer to this setup
    ------l-------
   /              \
  p --> p' ---l--> p''

  q --> q' ---l--> q''
   \              /
    ------l-------
where --> is strip_ch
(p, q), (p', q'), (p'', q'') are all bisimilar.
*)

(* p --> p' ---l--> p'' <=> p ---l--> p'' *)
Theorem strip_ch_lts:
  (∃p'. strip_ch p p' ∧ ctree_lts p' l p'') <=> ctree_lts p l p''
Proof
  eq_tac
  >- (Induct_on `strip_ch` >> rw[] >> metis_tac[ctree_lts_rules])
  >> Cases_on `p = ctree_stuck`
  >- metis_tac[not_ctree_lts_stuck]
  >> drule_at Concl $ iffLR not_strip_ch_stuck
  >> first_x_assum mp_tac >> qid_spec_tac `p`
  >> Induct_on `ctree_lts` >> rw[]
  >> metis_tac[not_strip_ch_stuck, not_ctree_lts_stuck]
QED

(* p --> p' ==> p ---l--> p'' ∧ p' ---l--> p'' *)
Theorem strip_ch_imp_l:
  strip_ch p p' ==> ∃l p''. ctree_lts p l p'' ∧ ctree_lts p' l p''
Proof
  Cases_on `p' = ctree_stuck` >- gvs[Once ctree_stuck_thm, Guard_def]
  >> dxrule_at Concl $ iffLR not_ctree_lts_stuck
  >> metis_tac[strip_ch_lts]
QED

(* Equational theory *)

Theorem ctree_sbisim_refl[simp]:
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

(* Automation theorems for simp *)
Theorem ctree_sbisim_sym_eq[local]:
  ctree_sbisim p q <=>
  (∀t. ctree_sbisim p t <=> ctree_sbisim q t) ∧
  (∀t. ctree_sbisim t p <=> ctree_sbisim t q)
Proof
  metis_tac[ctree_sbisim_refl, ctree_sbisim_sym, ctree_sbisim_trans]
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

Theorem ctree_sbisim_ret[simp]:
  ctree_sbisim (Ret r) (Ret r') <=> r = r'
Proof
  rw[EQ_IMP_THM, ctree_sbisim_refl]
  >> dxrule_then strip_assume_tac ctree_sbisim_lts
  >> first_x_assum $ resolve_then Any strip_assume_tac ctree_lts_ret
  >> gvs[]
QED

Theorem ctree_sbisim_tau[simp]:
  ctree_sbisim (Tau u) (Tau v) <=> ctree_sbisim u v
Proof
  rw[EQ_IMP_THM] >- (
    dxrule_then strip_assume_tac ctree_sbisim_lts
    >> first_x_assum $ resolve_then Any strip_assume_tac ctree_lts_tau
    >> gvs[]
  )
  >> rw[Once ctree_sbisim_strong_thm]
  >> qexists `λp q. p = Tau u ∧ q = Tau v`
  >> rw[]
QED

Theorem ctree_sbisim_vis[simp]:
  ctree_sbisim (Vis e g) (Vis e' g') <=> e = e' ∧ (∀a. ctree_sbisim (g a) (g' a))
Proof
  eq_tac >> strip_tac >- (
    dxrule_then strip_assume_tac ctree_sbisim_lts
    >> first_x_assum $ resolve_then Any strip_assume_tac ctree_lts_vis
    >> gvs[]
  )
  >> rw[Once ctree_sbisim_strong_thm]
  >> qexists `λp q. p = Vis e g ∧ q = Vis e g'`
  >> rw[]
QED

Theorem ctree_sbisim_br:
  (∀b. ∃b'. ctree_sbisim (k b) (k' b')) ∧
  (∀b'. ∃b. ctree_sbisim (k b) (k' b'))
    ==> ctree_sbisim (Br k) (Br k')
Proof
  strip_tac >> rw[Once ctree_sbisim_strong_thm]
  >> qexists `λp q. p = Br k ∧ q = Br k'` >> rw[]
  >> metis_tac[ctree_sbisim_lts, ctree_sbisim_sym]
QED

Theorem ctree_sbisim_strip_ch:
  (∀p'. strip_ch p p' ==> ∃q'. strip_ch q q' ∧ ctree_sbisim p' q') ∧
  (∀q'. strip_ch q q' ==> ∃p'. strip_ch p p' ∧ ctree_sbisim p' q')
    ==> ctree_sbisim p q
Proof
  strip_tac >> rw[Once ctree_sbisim_strong_thm]
  >> qexists `λu v. p = u ∧ q = v` >> rw[]
  >> metis_tac[strip_ch_lts, ctree_sbisim_lts, ctree_sbisim_sym]
QED

Theorem ctree_sbisim_guard:
  ctree_sbisim (Guard t) t
Proof
  rw[Once ctree_sbisim_strong_thm]
  >> qexists `λp q. p = Guard q` >> rw[]
  >> metis_tac[ctree_sbisim_refl]
QED

Theorem ctree_sbisim_guard_funpow:
  ctree_sbisim (FUNPOW Guard n t) t
Proof
  Induct_on `n` >> rw[FUNPOW_SUC]
  >> metis_tac[ctree_sbisim_trans, ctree_sbisim_guard]
QED

Theorem ctree_sbisim_brS[simp]:
  ctree_sbisim (BrS k) (BrS k') <=>
    (∀b. ∃b'. ctree_sbisim (k b) (k' b')) ∧
    (∀b'. ∃b. ctree_sbisim (k b) (k' b'))
Proof
  eq_tac >> strip_tac >- (
    rw[] >| [all_tac, dxrule_then strip_assume_tac ctree_sbisim_sym]
    >> dxrule_then strip_assume_tac ctree_sbisim_lts
    >> first_x_assum $ resolve_then Any strip_assume_tac ctree_lts_brS
    >> gvs[] >> metis_tac[ctree_sbisim_sym]
  )
  >> rw[BrS_def]
  >> irule ctree_sbisim_br
  >> rw[]
QED

Theorem ctree_sbisim_step:
  ctree_sbisim (Step t) (Tau t)
Proof
  rw[Step_def, ctree_sbisim_guard]
QED

Theorem ctree_sbisim_step_funpow:
  ctree_sbisim (FUNPOW Step n p) (FUNPOW Tau n p)
Proof
  Induct_on `n` >> rw[FUNPOW_SUC]
  >> metis_tac[ctree_sbisim_trans, ctree_sbisim_step, ctree_sbisim_tau]
QED

Theorem ctree_sbisim_sym_eqs[simp] = LIST_CONJ (
  [ctree_sbisim_guard, ctree_sbisim_guard_funpow, ctree_sbisim_step, ctree_sbisim_step_funpow]
  |> map ctree_sbisim_make_sym_eq
);

Theorem ctree_sbisim_stuck_lemma[local]:
  ctree_sbisim t ctree_stuck <=> t = ctree_stuck
Proof
  rw[EQ_IMP_THM] >> rw[GSYM not_ctree_lts_stuck]
  >> spose_not_then strip_assume_tac
  >> dxrule_all ctree_sbisim_lts
  >> rw[]
QED

Theorem ctree_sbisim_stuck_sym_eq[simp] = ctree_sbisim_make_sym_iff ctree_sbisim_stuck_lemma;

(* Common case, useful for metis_tac since normal ctree_sbisim_lts with simpset can ifer *)
Theorem ctree_sbisim_lts_ret:
  ctree_sbisim p q ∧ ctree_lts p (val r) ctree_stuck ==> ctree_lts q (val r) ctree_stuck
Proof
  metis_tac[ctree_sbisim_lts, ctree_sbisim_stuck_sym_eq]
QED

Theorem ctree_sbisim_not[simp]:
  (¬ctree_sbisim (Ret r) (Tau u)) ∧
  (¬ctree_sbisim (Ret r) (Vis e g)) ∧
  (¬ctree_sbisim (Tau u) (Ret r)) ∧
  (¬ctree_sbisim (Tau u) (Vis e g)) ∧
  (¬ctree_sbisim (Vis e g) (Ret r)) ∧
  (¬ctree_sbisim (Vis e g) (Tau u))
Proof
  rw[] >> spose_not_then strip_assume_tac
  >> dxrule_then strip_assume_tac ctree_sbisim_lts
  >> gvs[]
  >> metis_tac[ctree_label_distinct]
QED

(* Experimental, possibly not very useful *)
Theorem ctree_sbisim_sym_strong_guard_thm:
  ctree_sbisim t t' <=> ∃R. symmetric R ∧ R t t' ∧ ∀p q. R p q ==>
    (∀l p'. ctree_lts p l p' ==> ∃q'. ctree_lts q l q' ∧ (R p' q' ∨ ctree_sbisim p' q')) ∨
    (∃u. p = Guard u ∧ R u q)
Proof
  rw[EQ_IMP_THM]
  >- metis_tac[ctree_sbisim_sym_strong_thm]
  >> rw[Once ctree_sbisim_sym_strong_thm]
  >> qexists `R` >> simp[]
  >> Induct_on `ctree_lts` >> rw[]
  >> first_x_assum dxrule >> rw[]
  >> metis_tac[]
QED

(* Not added to simpset since one should Cases_on `p` and use the other simp rules *)
(* Mainly useful as a lemma to prove below, though there could be other uses *)
Theorem ctree_sbisim_pcases_ret:
  ctree_sbisim p (Ret r) <=> (∀l q. ctree_lts p l q <=> l = val r ∧ q = ctree_stuck)
Proof
  rw[EQ_IMP_THM]
  >- (dxrule_all ctree_sbisim_lts >> rw[])
  >- (dxrule_all ctree_sbisim_lts >> rw[])
  >- (dxrule ctree_sbisim_lts_right >> rw[])
  >> rw[Once ctree_sbisim_strong_thm]
  >> qexists `λx y. x = p ∧ y = Ret r` >> rw[]
  >> metis_tac[]
QED

Theorem ctree_sbisim_pcases_tau:
  ctree_sbisim p (Tau u) <=>
    (∃p'. ctree_lts p tau p' ∧ ctree_sbisim p' u) ∧
    ∀l q. ctree_lts p l q ==> l = tau ∧ ctree_sbisim q u
Proof
  rw[EQ_IMP_THM]
  >- (dxrule ctree_sbisim_lts_right >> rw[])
  >- (dxrule_all ctree_sbisim_lts >> rw[])
  >- (dxrule_all ctree_sbisim_lts >> rw[])
  >> rw[Once ctree_sbisim_strong_thm]
  >> qexists `λx y. x = p ∧ y = Tau u` >> rw[]
  >> metis_tac[]
QED

Theorem ctree_sbisim_pcases_vis:
  ctree_sbisim p (Vis e g) <=>
    (∀a. ∃p'. ctree_lts p (obs e a) p' ∧ ctree_sbisim p' (g a)) ∧
    ∀l q. ctree_lts p l q ==> ∃a. l = obs e a ∧ ctree_sbisim q (g a)
Proof
  rw[EQ_IMP_THM]
  >- (dxrule ctree_sbisim_lts_right >> rw[])
  >- (dxrule_all ctree_sbisim_lts >> rw[])
  >> rw[Once ctree_sbisim_strong_thm]
  >> qexists `λx y. x = p ∧ y = Vis e g` >> rw[]
  >> metis_tac[]
QED

Theorem ctree_sbisim_pcases = LIST_CONJ [ctree_sbisim_pcases_ret, ctree_sbisim_pcases_tau, ctree_sbisim_pcases_vis];

Theorem ctree_sbisim_br_pcases_lemma[local]:
  (ctree_sbisim (Br k) (Ret r) <=>
    (∃v. ctree_lts (k v) (val r) ctree_stuck) ∧
    ∀b. ctree_sbisim (k b) (Ret r) ∨ k b = ctree_stuck) ∧
  (ctree_sbisim (Br k) (Tau u) <=>
    (∃v p'. ctree_lts (k v) tau p' ∧ ctree_sbisim p' u) ∧
    ∀b. ctree_sbisim (k b) (Tau u) ∨ k b = ctree_stuck)
Proof
  rw[ctree_sbisim_pcases] >> metis_tac[not_ctree_lts_stuck]
QED

Theorem ctree_sbisim_br_vis_carry[local]:
  ctree_sbisim (Br k) (Vis e g) ∧ ctree_lts (k v) (obs e a) p' ==> ∀a'.
    ∃q'. ctree_lts (k v) (obs e a') q' ∧ ctree_sbisim q' (g a')
Proof
  rw[]
  >> dxrule_then strip_assume_tac ctree_lts_obs_carry
  >> first_x_assum $ qspec_then `a'` strip_assume_tac
  >> qexists `q'` >> rw[]
  >> dxrule_then strip_assume_tac ctree_lts_br
  >> dxrule_all ctree_sbisim_lts >> rw[]
QED

(* Vis is separate, as we need to justify that there can only be one vis node up to sbisim
   despite the branching it can do, so proof is more complex *)
Theorem ctree_sbisim_br_vis_lemma[local]:
  ctree_sbisim (Br k) (Vis e g) <=>
    (∃v. ∀a. ∃p'. ctree_lts (k v) (obs e a) p' ∧ ctree_sbisim p' (g a)) ∧
    ∀b. ctree_sbisim (k b) (Vis e g) ∨ k b = ctree_stuck
Proof
  irule EQ_SYM >> rw[EQ_IMP_THM]
  >- (gvs[ctree_sbisim_pcases_vis] >> metis_tac[not_ctree_lts_stuck])
  >- (
    drule_then strip_assume_tac ctree_sbisim_lts_right
    >> first_x_assum $ resolve_then Any strip_assume_tac ctree_lts_vis
    >> first_assum $ qspec_then `a` strip_assume_tac
    >> gvs[]
    >> metis_tac[ctree_sbisim_br_vis_carry]
  )
  >> Cases_on `k b = ctree_stuck` >> rw[]
  >> rw[Once ctree_sbisim_strong_thm]
  >> qexists `λp q. p = k b ∧ q = Vis e g` >> rw[]
  >- (dxrule ctree_sbisim_lts >> rw[] >> metis_tac[])
  >> dxrule_at Concl $ iffLR not_ctree_lts_stuck >> rw[]
  >> drule_then strip_assume_tac ctree_lts_br
  >> drule_all ctree_sbisim_lts >> rw[]
  >> metis_tac[ctree_sbisim_br_vis_carry]
QED

Theorem ctree_sbisim_br_pcases[simp] = LIST_CONJ (
  CONJ_LIST 2 ctree_sbisim_br_pcases_lemma @ [ctree_sbisim_br_vis_lemma]
  |> map ctree_sbisim_make_sym_iff
);

Theorem ctree_lts_bind_ret:
  ctree_lts p (val r) ctree_stuck ∧ ctree_lts (k r) l p' ==> ctree_lts (ctree_bind p k) l p'
Proof
  Induct_on `ctree_lts` >> rw[]
  >> metis_tac[]
QED

Theorem ctree_lts_bind_tau_vis:
  ∀k. ctree_lts p l' p' ∧ ctree_lts_same l l' ==> ctree_lts (ctree_bind p k) l (ctree_bind p' k)
Proof
  Induct_on `ctree_lts` >> rw[]
  >> metis_tac[]
QED

Theorem ctree_lts_bind_rules = LIST_CONJ [ctree_lts_bind_ret, ctree_lts_bind_tau_vis];

Theorem ctree_lts_bind_cases:
  ctree_lts (ctree_bind p k) l p'' <=>
    (∃l' p'. ctree_lts_same l l' ∧ ctree_lts p l' p' ∧ p'' = ctree_bind p' k) ∨
    (∃r. ctree_lts p (val r) ctree_stuck ∧ ctree_lts (k r) l p'')
Proof
  eq_tac >- (
    qid_spec_tac `p`
    >> Induct_on `ctree_lts` >> rw[]
    >> Cases_on `p` >> gvs[]
    >> metis_tac[]
  ) >> metis_tac[ctree_lts_bind_rules]
QED

Theorem ctree_sbisim_bind_t[local]:
  ctree_sbisim t t' ==> ctree_sbisim (ctree_bind t k) (ctree_bind t' k)
Proof
  rw[] >> rw[Once ctree_sbisim_sym_strong_thm]
  >> qexists `λp q. ∃u v. p = ctree_bind u k ∧ q = ctree_bind v k ∧ ctree_sbisim u v`
  >> rw[]
  >- (gvs[symmetric_def] >> metis_tac[ctree_sbisim_sym])
  >- metis_tac[]
  >> dxrule_then strip_assume_tac $ iffLR ctree_lts_bind_cases
  >> gvs[]
  >> metis_tac[
    ctree_sbisim_lts, ctree_lts_bind_rules,
    ctree_sbisim_refl, ctree_sbisim_lts_ret
  ]
QED

Theorem ctree_sbisim_bind_k[local]:
  (∀r. ctree_sbisim (k r) (k' r)) ==> ctree_sbisim (ctree_bind t k) (ctree_bind t k')
Proof
  rw[] >> rw[Once ctree_sbisim_strong_thm]
  >> qexists `λp q. ∃u. p = ctree_bind u k ∧ q = ctree_bind u k'`
  >> rw[]
  >- metis_tac[]
  >> dxrule_then strip_assume_tac $ iffLR ctree_lts_bind_cases
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

Theorem ctree_lts_iter_retl:
  ctree_lts (k s) (val (INL s')) ctree_stuck ∧
  ctree_lts (ctree_iter k s') l p'
  ==> ctree_lts (ctree_iter k s) l p'
Proof
  rw[] >> rw[Once ctree_iter_thm]
  >> irule ctree_lts_bind_ret
  >> qexists `INL s'` >> rw[]
QED

Theorem ctree_lts_iter_retr:
  ctree_lts (k s) (val (INR r)) ctree_stuck
  ==> ctree_lts (ctree_iter k s) (val r) ctree_stuck
Proof
  rw[Once ctree_iter_thm]
  >> irule ctree_lts_bind_ret
  >> qexists `INR r` >> rw[]
QED

Theorem ctree_lts_iter_tau_vis:
  ctree_lts (k s) l' u' ∧ ctree_lts_same l l'
  ==> ctree_lts (ctree_iter k s) l (ctree_bind u' (ctree_iter_fn k))
Proof
  rw[ctree_iter_fn_thm]
  >> irule ctree_lts_bind_tau_vis
  >> metis_tac[]
QED

Theorem ctree_lts_iter_rules = LIST_CONJ
  [ctree_lts_iter_retl, ctree_lts_iter_retr, ctree_lts_iter_tau_vis];

Theorem ctree_lts_iter_cases:
  ctree_lts (ctree_iter k s) l p' <=>
    (∃s'. ctree_lts (k s) (val (INL s')) ctree_stuck ∧ ctree_lts (ctree_iter k s') l p') ∨
    (∃r. ctree_lts (k s) (val (INR r)) ctree_stuck ∧ l = val r ∧ p' = ctree_stuck) ∨
    (∃l' u'. ctree_lts (k s) l' u' ∧ ctree_lts_same l l' ∧ p' = ctree_bind u' (ctree_iter_fn k))
Proof
  rw[EQ_IMP_THM] >- (
    gvs[Once ctree_iter_fn_thm, Once ctree_lts_bind_cases]
    >- metis_tac[]
    >> Cases_on `r` >> gvs[]
    >> metis_tac[]
  ) >> metis_tac[ctree_lts_iter_rules]
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

Theorem iter_chain_simp[simp]:
  (iter_chain k [] p l p' <=> (∀s. l ≠ val (INL s)) ∧ ctree_lts p l p') ∧
  (iter_chain k (s::tl) p l p' <=>
    ctree_lts p (val (INL s)) ctree_stuck ∧ iter_chain k tl (k s) l p')
Proof
  rw[] >> rw[Once iter_chain_cases]
  >> Cases_on `l` >> rw[EQ_IMP_THM]
  >- metis_tac[]
  >> Cases_on `r` >> rw[]
  >> metis_tac[ctree_lts_val_stuck]
QED

Theorem ctree_lts_imp_iter_chain:
  (∀l p'. ctree_lts p l p' ==> ctree_lts q l p') ∧ iter_chain k seeds p l p'
    ==> iter_chain k seeds q l p'
Proof
  Induct_on `iter_chain` >> rw[iter_chain_rules]
QED

Theorem ctree_lts_iter_fn_retr:
  iter_chain k seeds u (val (INR r)) ctree_stuck
    ==> ctree_lts (ctree_bind u (ctree_iter_fn k)) (val r) ctree_stuck
Proof
  Induct_on `iter_chain` >> rw[]
  >> irule ctree_lts_bind_ret
  >| [qexists `INL s`, qexists `INR r`]
  >> rw[ctree_iter_fn_thm]
QED

Theorem ctree_lts_iter_fn_tau_vis:
  iter_chain k seeds u l' u' ∧ ctree_lts_same l l'
    ==> ctree_lts (ctree_bind u (ctree_iter_fn k)) l (ctree_bind u' (ctree_iter_fn k))
Proof
  Induct_on `iter_chain` >> rw[] >- (
    first_x_assum $ drule_then strip_assume_tac
    >> dxrule_then strip_assume_tac ctree_lts_bind_ret
    >> gvs[ctree_iter_fn_thm]
  )
  >> metis_tac[ctree_lts_same_def, ctree_lts_bind_tau_vis]
QED

Theorem ctree_lts_iter_fn_rules = LIST_CONJ [ctree_lts_iter_fn_retr, ctree_lts_iter_fn_tau_vis];

Theorem ctree_lts_iter_fn_cases:
  ctree_lts (ctree_bind u (ctree_iter_fn k)) l p <=> ∃seeds.
    (∃r. iter_chain k seeds u (val (INR r)) ctree_stuck ∧ l = val r ∧ p = ctree_stuck) ∨
    (∃l' u'. iter_chain k seeds u l' u' ∧ ctree_lts_same l l' ∧ p = ctree_bind u' (ctree_iter_fn k))
Proof
  eq_tac >- (
    qid_spec_tac `u`
    >> Induct_on `ctree_lts` >> rw[] >~ [`Br`]
    >> Cases_on `u` >> gvs[ctree_iter_fn_def, AllCaseEqs()]
    >- (
      (* retl *)
      first_x_assum $ qspec_then `k i` strip_assume_tac
      >> gvs[ctree_iter_fn_thm]
      >> qexists `i::seeds` >> gvs[]
      >> metis_tac[iter_chain_cases]
    ) >- (
      first_x_assum $ qspec_then `k'' v` strip_assume_tac >> gvs[]
      >> metis_tac[ctree_lts_br, ctree_lts_imp_iter_chain]
    )
    >> metis_tac[iter_chain_rules, ctree_lts_rules]
  )
  >> metis_tac[ctree_lts_iter_fn_rules]
QED

Theorem ctree_sbisim_iter_chain:
  ∀v. (∀s. ctree_sbisim (k s) (k' s)) ∧ ctree_sbisim u v ∧ iter_chain k seeds u l p
  ==> ∃q. iter_chain k' seeds v l q ∧ ctree_sbisim p q
Proof
  Induct_on `iter_chain` >> rw[]
  >- metis_tac[iter_chain_cases, ctree_sbisim_lts_ret]
  >> metis_tac[ctree_sbisim_lts, iter_chain_rules, ctree_sbisim_stuck_sym_eq]
QED

Theorem ctree_sbisim_iter:
  (∀s. ctree_sbisim (k s) (k' s)) ==> ctree_sbisim (ctree_iter k s) (ctree_iter k' s)
Proof
  rw[] >> rw[Once ctree_sbisim_sym_strong_thm]
  >> qexists `λp q. ∃k k' u v. (∀s. ctree_sbisim (k s) (k' s)) ∧
    p = ctree_bind u (ctree_iter_fn k) ∧
    q = ctree_bind v (ctree_iter_fn k') ∧
    ctree_sbisim u v`
  >> rw[]
  >- (gvs[symmetric_def] >> metis_tac[ctree_sbisim_sym])
  >- metis_tac[ctree_iter_fn_thm]
  >> dxrule_then strip_assume_tac $ iffLR ctree_lts_iter_fn_cases
  >> gvs[Once ctree_lts_val_stuck]
  >> metis_tac[ctree_sbisim_iter_chain, ctree_sbisim_stuck_sym_eq, ctree_lts_iter_fn_rules]
QED

Theorem ctree_sbisim_loop:
  (∀s. ctree_sbisim (k s) (k' s)) ==> ctree_sbisim (ctree_loop k s) (ctree_loop k' s)
Proof
  rw[ctree_loop_def] >> irule ctree_sbisim_iter
  >> metis_tac[ctree_sbisim_bind, ctree_sbisim_refl]
QED

(* wbisim *)


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

Theorem ctree_elts_refl_simp[simp] = ctree_elts_refl;

Theorem ctree_elts_pcases:
  ctree_elts p q <=>
  (∃r.     p = Ret r   ∧ q = Ret r) ∨
  (∃u.     p = Tau u   ∧ (p = q ∨ ctree_elts u q)) ∨
  (∃a e g. p = Vis e g ∧ q = Vis e g) ∨
  (∃k v.   p = Br k    ∧ (p = q ∨ ∃q' v. ctree_lts (k v) tau q' ∧ ctree_elts q' q))
Proof
  eq_tac >- (
    Induct_on `ctree_elts` >> rw[ctree_cases]
    >> Cases_on `p`
    >> gvs[ctree_elts_rules]
    >> metis_tac[ctree_elts_rules, ctree_lts_rules]
  )
  >> rw[]
  >> metis_tac[ctree_lts_rules, ctree_elts_rules]
QED

Theorem ctree_elts_pcases_simp[simp] = cases_to_simp `p` ctree_elts_pcases;

Theorem ctree_elts_stuck_spin_lemma[local]:
  (ctree_elts ctree_stuck q ==> q = ctree_stuck) ∧
  (ctree_elts ctree_spin q ==> q = ctree_spin)
Proof
  strip_tac >> Induct_on `ctree_elts` >> gvs[]
QED

Theorem ctree_elts_combs[simp]:
  (ctree_elts (Guard t) q   <=> q = Guard t ∨ ∃q'. ctree_lts t tau q' ∧ ctree_elts q' q) ∧
  (ctree_elts (BrS k) q     <=> q = BrS k ∨ ∃v. ctree_elts (k v) q) ∧
  (ctree_elts (Step t) q    <=> q = Step t ∨ ctree_elts t q) ∧
  (ctree_elts ctree_stuck q <=> q = ctree_stuck) ∧
  (ctree_elts ctree_spin q  <=> q = ctree_spin)
Proof
  rw[Guard_def, BrS_def, Step_def]
  >> metis_tac[ctree_elts_stuck_spin_lemma, ctree_elts_refl]
QED

Theorem ctree_elts_funpow[simp]:
  ctree_elts (FUNPOW Tau n p) p ∧
  ctree_elts (FUNPOW Step n p) p
Proof
  Induct_on `n` >> rw[FUNPOW_SUC]
QED

Inductive ctree_wlts:
[~lts:] ctree_lts p l q ∧ l ≠ tau ==> ctree_wlts p l q
[~tauL:] ctree_lts p tau p' ∧ ctree_wlts p' l q ==> ctree_wlts p l q
[~tauR:] ctree_wlts p l q' ∧ ctree_lts q' tau q ==> ctree_wlts p l q
End

Theorem ctree_wlts_not_tau[simp]:
  ¬ctree_wlts p tau q
Proof
  Induct_on `ctree_wlts` >> rw[]
QED

Theorem ctree_elts_wlts_elts:
  ctree_elts p p' ∧ ctree_wlts p' l q' ∧ ctree_elts q' q ==> ctree_wlts p l q
Proof
  Induct_on `ctree_elts` >> rw[]
  >> rpt (pop_assum mp_tac)
  >> Induct_on `ctree_elts` >> rw[]
  >> metis_tac[ctree_wlts_rules]
QED

Theorem ctree_elts_lts_elts:
  ctree_wlts p l q <=> l ≠ tau ∧ ∃p' q'. ctree_elts p p' ∧ ctree_lts p' l q' ∧ ctree_elts q' q
Proof
  eq_tac
  >- (Induct_on `ctree_wlts` >> metis_tac[ctree_elts_rules_sym])
  >> metis_tac[ctree_elts_wlts_elts, ctree_wlts_lts]
QED

Theorem ctree_wlts_wts_equiv:
  ctree_wlts p l q <=> l ≠ tau ∧ WTS ctree_lts tau p l q
Proof
  rw[WTS_def, GSYM ctree_elts_ets_equiv, ctree_elts_lts_elts]
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

Theorem ctree_wlts_pcases_simp[simp] = cases_to_simp `p` ctree_wlts_pcases;

Theorem ctree_wlts_val_stuck:
  ctree_wlts p (val r) q <=> ctree_wlts p (val r) ctree_stuck ∧ q = ctree_stuck
Proof
  rw[ctree_elts_lts_elts, EQ_IMP_THM, Once ctree_lts_val_stuck]
  >> metis_tac[ctree_elts_refl]
QED

Theorem ctree_wlts_combs[simp]:
  (ctree_wlts (Guard t) l q   <=> ctree_wlts t l q) ∧
  (ctree_wlts (BrS k) l q     <=> ∃v. ctree_wlts (k v) l q) ∧
  (ctree_wlts (Step t) l q    <=> ctree_wlts t l q) ∧
  (¬ctree_wlts ctree_stuck l q) ∧
  (¬ctree_wlts ctree_spin l q)
Proof
  rw[Guard_def, BrS_def, Step_def]
  >> gvs[ctree_elts_lts_elts]
QED

Theorem ctree_wlts_funpow[simp]:
  (ctree_wlts (FUNPOW Tau n p) l q <=> ctree_wlts p l q) ∧
  (ctree_wlts (FUNPOW Guard n p) l q <=> ctree_wlts p l q) ∧
  (ctree_wlts (FUNPOW Step n p) l q <=> ctree_wlts p l q)
Proof
  Induct_on `n` >> rw[FUNPOW_SUC]
QED

Definition ctree_wbisim_def:
  ctree_wbisim = WBISIM_REL ctree_lts tau
End

Theorem ctree_wbisim_refl[simp]:
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

Theorem ctree_wbisim_sym_eq:
  ctree_wbisim p q <=>
  (∀t. ctree_wbisim p t <=> ctree_wbisim q t) ∧
  (∀t. ctree_wbisim t p <=> ctree_wbisim t q)
Proof
  rw[EQ_IMP_THM, FUN_EQ_THM]
  >> metis_tac[ctree_wbisim_refl, ctree_wbisim_sym, ctree_wbisim_trans]
QED

Theorem ctree_wbisim_lts:
  ctree_wbisim p q ∧ ctree_lts p l p' ∧ l ≠ tau ==> ∃q'. ctree_wlts q l q' ∧ ctree_wbisim p' q'
Proof
  rw[ctree_wbisim_def, WBISIM_REL_def]
  >> `∃q'. ctree_wlts q l q' ∧ R p' q'` suffices_by metis_tac[]
  >> gvs[WBISIM_def]
  >> metis_tac[ctree_wlts_wts_equiv]
QED

Theorem ctree_wbisim_lts_right:
  ctree_wbisim p q ∧ ctree_lts q l q' ∧ l ≠ tau ==> ∃p'. ctree_wlts p l p' ∧ ctree_wbisim p' q'
Proof
  metis_tac[ctree_wbisim_lts, ctree_wbisim_sym]
QED

Theorem ctree_wbisim_lts_tau:
  ctree_wbisim p q ∧ ctree_lts p tau p' ==> ∃q'. ctree_elts q q' ∧ ctree_wbisim p' q'
Proof
  rw[ctree_wbisim_def, WBISIM_REL_def]
  >> `∃q'. ctree_elts q q' ∧ R p' q'` suffices_by metis_tac[]
  >> gvs[WBISIM_def]
  >> metis_tac[ctree_elts_ets_equiv]
QED

Theorem ctree_wbisim_lts_tau_right:
  ctree_wbisim p q ∧ ctree_lts q tau q' ==> ∃p'. ctree_elts p p' ∧ ctree_wbisim p' q'
Proof
  metis_tac[ctree_wbisim_lts_tau, ctree_wbisim_sym]
QED

Theorem ctree_wbisim_elts:
  ctree_wbisim p q ∧ ctree_elts p p' ==> ∃q'. ctree_elts q q' ∧ ctree_wbisim p' q'
Proof
  qid_spec_tac `q`
  >> Induct_on `ctree_elts` >> rw[]
  >> metis_tac[ctree_elts_rules, ctree_wbisim_lts_tau, ctree_elts_trans]
QED

Theorem ctree_wbisim_elts_right:
  ctree_wbisim p q ∧ ctree_elts q q' ==> ∃p'. ctree_elts p p' ∧ ctree_wbisim p' q'
Proof
  metis_tac[ctree_wbisim_elts, ctree_wbisim_sym]
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

Theorem ctree_wbisim_wlts_right:
  ctree_wbisim p q ∧ ctree_wlts q l q' ==> ∃p'. ctree_wlts p l p' ∧ ctree_wbisim p' q'
Proof
  metis_tac[ctree_wbisim_wlts, ctree_wbisim_sym]
QED

Theorem ctree_wbisim_lts_ret:
  ctree_wbisim p q ∧ ctree_lts p (val r) ctree_stuck ==> ctree_wlts q (val r) ctree_stuck
Proof
  rw[] >> dxrule_then strip_assume_tac ctree_wbisim_lts
  >> first_x_assum $ dxrule_then strip_assume_tac
  >> gvs[Once ctree_wlts_val_stuck]
QED

Theorem ctree_wbisim_wlts_ret:
  ctree_wbisim p q ∧ ctree_wlts p (val r) ctree_stuck ==> ctree_wlts q (val r) ctree_stuck
Proof
  rw[] >> dxrule_all ctree_wbisim_wlts >> rw[]
  >> gvs[Once ctree_wlts_val_stuck]
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

Theorem ctree_wbisim_coind:
  ∀R. (∀p q. R p q ⇒
    (∀l p'. l ≠ tau ∧ ctree_lts p l p' ==> ∃q'. ctree_wlts q l q' ∧ R p' q') ∧
    (∀l q'. l ≠ tau ∧ ctree_lts q l q' ==> ∃p'. ctree_wlts p l p' ∧ R p' q') ∧
    (∀p'. ctree_lts p tau p' ==> ∃q'. ctree_elts q q' ∧ R p' q') ∧
    (∀q'. ctree_lts q tau q' ==> ∃p'. ctree_elts p p' ∧ R p' q')
  ) ⇒ ∀p q. R p q ⇒ ctree_wbisim p q
Proof
  rw[ctree_wbisim_thm]
  >> qexists `R`
  >> metis_tac[]
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

Theorem ctree_wbisim_imp_lts[local]:
  ctree_wbisim p q ==>
    (∀l p'. l ≠ tau ∧ ctree_lts p l p' ==> ∃q'. ctree_wlts q l q' ∧ ctree_wbisim p' q') ∧
    (∀l q'. l ≠ tau ∧ ctree_lts q l q' ==> ∃p'. ctree_wlts p l p' ∧ ctree_wbisim p' q') ∧
    (∀p'. ctree_lts p tau p' ==> ∃q'. ctree_elts q q' ∧ ctree_wbisim p' q') ∧
    (∀q'. ctree_lts q tau q' ==> ∃p'. ctree_elts p p' ∧ ctree_wbisim p' q')
Proof
  metis_tac[ctree_wbisim_lts, ctree_wbisim_lts_tau, ctree_wbisim_sym]
QED

Theorem ctree_wbisim_iff_lts:
  ctree_wbisim p q <=>
    (∀l p'. l ≠ tau ∧ ctree_lts p l p' ==> ∃q'. ctree_wlts q l q' ∧ ctree_wbisim p' q') ∧
    (∀l q'. l ≠ tau ∧ ctree_lts q l q' ==> ∃p'. ctree_wlts p l p' ∧ ctree_wbisim p' q') ∧
    (∀p'. ctree_lts p tau p' ==> ∃q'. ctree_elts q q' ∧ ctree_wbisim p' q') ∧
    (∀q'. ctree_lts q tau q' ==> ∃p'. ctree_elts p p' ∧ ctree_wbisim p' q')
Proof
  eq_tac
  >- (strip_tac >> irule ctree_wbisim_imp_lts >> rw[])
  >> qid_spec_tac `q` >> qid_spec_tac `p`
  >> ho_match_mp_tac ctree_wbisim_coind >> rw[]
  >> first_x_assum $ dxrule_all >> rw[]
  >| [qexists `q'`, qexists `p'`, qexists `q'`, qexists `p'`]
  >> (conj_tac >- rw[] >> irule ctree_wbisim_imp_lts >> rw[])
QED

(* Equational theory *)

Theorem ctree_sbisim_imp_wbisim:
  ctree_sbisim p q ==> ctree_wbisim p q
Proof
  rw[ctree_sbisim_def, ctree_wbisim_def, BISIM_REL_IMP_WBISIM_REL]
QED

Theorem ctree_wbisim_ret[simp]:
  ctree_wbisim (Ret r) (Ret r') <=> r = r'
Proof
  rw[EQ_IMP_THM]
  >> dxrule_then strip_assume_tac ctree_wbisim_lts
  >> gvs[]
QED

Theorem ctree_wbisim_tau:
  ctree_wbisim (Tau u) u
Proof
  rw[Once ctree_wbisim_strong_thm]
  >> qexists `λp q. p = Tau q` >> rw[]
  >> metis_tac[ctree_wlts_lts, ctree_elts_rules, ctree_wbisim_refl]
QED

Theorem ctree_wbisim_tau_funpow:
  ctree_wbisim (FUNPOW Tau n u) u
Proof
  Induct_on `n` >> rw[FUNPOW_SUC]
  >> metis_tac[ctree_wbisim_trans, ctree_wbisim_tau]
QED

Theorem ctree_wbisim_vis_e[local]:
  ctree_wbisim (Vis e g) (Vis e' g') ==> e = e'
Proof
  rw[]
  >> dxrule_then strip_assume_tac ctree_wbisim_lts
  >> first_x_assum $ resolve_then Any strip_assume_tac ctree_lts_vis
  >> gvs[]
  >> metis_tac[]
QED

Theorem ctree_wbisim_vis[simp]:
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
    >> qpat_x_assum `ctree_wbisim (Vis e' h) _` kall_tac
    >> dxrule_then strip_assume_tac ctree_wbisim_lts
    >> first_x_assum $ resolve_then Any strip_assume_tac ctree_lts_vis
    >> first_x_assum $ qspec_then `a` strip_assume_tac
    >> gvs[]
    >- (drule_all ctree_wbisim_lts >> metis_tac[ctree_elts_wlts_elts, ctree_elts_refl])
    >> metis_tac[ctree_wbisim_lts_tau, ctree_elts_trans]
  )
  >> irule $ iffRL ctree_wbisim_strong_thm
  >> qexists `λp q. p = Vis e g ∧ q = Vis e g'`
  >> rw[]
  >> metis_tac[ctree_elts_rules, ctree_wbisim_sym]
QED

Theorem ctree_wbisim_brS:
  (∀b. ∃b'. ctree_wbisim (k b) (k' b')) ∧
  (∀b'. ∃b. ctree_wbisim (k b) (k' b'))
    ==> ctree_wbisim (BrS k) (BrS k')
Proof
  rw[]
  >> irule $ iffRL ctree_wbisim_strong_thm
  >> qexists `λp q. p = BrS k ∧ q = BrS k'`
  >> rw[]
  >> metis_tac[ctree_elts_refl, ctree_wbisim_refl]
QED

Theorem ctree_wbisim_guard:
  ctree_wbisim (Guard t) t
Proof
  irule ctree_sbisim_imp_wbisim >> rw[]
QED

Theorem ctree_wbisim_guard_funpow:
  ctree_wbisim (FUNPOW Guard n t) t
Proof
  irule ctree_sbisim_imp_wbisim >> rw[]
QED

Theorem ctree_wbisim_step:
  ctree_wbisim (Step t) t
Proof
  rw[Step_def]
  >> metis_tac[ctree_wbisim_trans, ctree_wbisim_guard, ctree_wbisim_tau]
QED

Theorem ctree_wbisim_step_funpow:
  ctree_wbisim (FUNPOW Step n t) t
Proof
  Induct_on `n` >> rw[FUNPOW_SUC]
  >> metis_tac[ctree_wbisim_trans, ctree_wbisim_step]
QED

Theorem ctree_wbisim_sym_eqs[simp] = LIST_CONJ (
  [ctree_wbisim_tau, ctree_wbisim_tau_funpow,
   ctree_wbisim_guard, ctree_wbisim_guard_funpow,
   ctree_wbisim_step, ctree_wbisim_step_funpow]
  |> map (SIMP_RULE std_ss [Once ctree_wbisim_sym_eq])
)

Theorem ctree_wbisim_stuck_spin[local]:
  ctree_wbisim ctree_stuck ctree_spin
Proof
  irule $ iffRL ctree_wbisim_thm
  >> qexists `λp q. p = ctree_stuck ∧ q = ctree_spin`
  >> rw[]
QED

Theorem ctree_wbisim_stuck_spin_sym_eq[simp]:
  ctree_wbisim ctree_stuck ctree_spin ∧
  ctree_wbisim ctree_spin ctree_stuck
Proof
  metis_tac[ctree_wbisim_sym, ctree_wbisim_stuck_spin]
QED

Theorem ctree_wbisim_not[simp]:
  (¬ctree_wbisim (Ret r) (Vis e g)) ∧
  (¬ctree_wbisim (Vis e g) (Ret r))
Proof
  rw[] >> spose_not_then strip_assume_tac
  >> dxrule_then strip_assume_tac ctree_wbisim_lts
  >> gvs[]
  >> metis_tac[ctree_label_distinct]
QED

Theorem ctree_wlts_bind_vis:
  ctree_wlts p (obs e a) p' ==> ctree_wlts (ctree_bind p k) (obs e a) (ctree_bind p' k)
Proof
  Induct_on `ctree_wlts` >> rw[]
  >> metis_tac[
    ctree_wlts_rules, ctree_lts_bind_tau_vis,
    ctree_lts_same_pcases, ctree_label_distinct
  ]
QED

Theorem ctree_wlts_bind_ret:
  ctree_wlts p (val r) ctree_stuck ∧ ctree_wlts (k r) l p' ⇒
    ctree_wlts (ctree_bind p k) l p'
Proof
  Induct_on `ctree_wlts` >> rw[] >> rpt (first_x_assum mp_tac)
  >> Induct_on `ctree_wlts` >> rw[]
  >> metis_tac[
    ctree_wlts_rules, ctree_lts_bind_rules,
    ctree_lts_same_pcases, ctree_label_distinct, ctree_wlts_val_stuck
  ]
QED

Theorem ctree_elts_bind:
  ctree_elts p p' ==> ctree_elts (ctree_bind p k) (ctree_bind p' k)
Proof
  Induct_on `ctree_elts` >> rw[]
  >> metis_tac[
    ctree_elts_tau, ctree_lts_bind_tau_vis,
    ctree_lts_same_pcases, ctree_label_distinct
  ]
QED

Theorem ctree_elts_bind_ret:
  ctree_wlts p (val r) ctree_stuck ∧ ctree_lts (k r) tau p' ⇒
    ctree_elts (ctree_bind p k) p'
Proof
  Induct_on `ctree_wlts` >> rw[]
  >> metis_tac[
    ctree_elts_rules, ctree_lts_bind_ret,
    ctree_elts_bind, ctree_elts_trans, ctree_wlts_val_stuck
  ]
QED

Theorem ctree_wbisim_bind_t:
  ctree_wbisim t t' ==> ctree_wbisim (ctree_bind t k) (ctree_bind t' k)
Proof
  rw[] >> rw[Once ctree_wbisim_sym_strong_thm]
  >> qexists `λp q. ∃u v. p = ctree_bind u k ∧ q = ctree_bind v k ∧ ctree_wbisim u v`
  >> rw[]
  >- (gvs[symmetric_def] >> metis_tac[ctree_wbisim_sym])
  >- metis_tac[]
  >> qpat_x_assum `ctree_wbisim t t'` kall_tac
  >> dxrule_then strip_assume_tac $ iffLR ctree_lts_bind_cases
  >> gvs[]
  >- (
    Cases_on `l` >> gvs[]
    >> metis_tac[ctree_wbisim_lts, ctree_wlts_lts, ctree_wlts_bind_vis, ctree_label_distinct]
  )
  >- metis_tac[ctree_wbisim_lts_ret, ctree_wlts_lts, ctree_wlts_bind_ret, ctree_label_distinct, ctree_wbisim_refl]
  >- metis_tac[ctree_wbisim_lts_tau, ctree_elts_bind, ctree_label_distinct]
  >> metis_tac[ctree_wbisim_lts_ret, ctree_elts_bind_ret, ctree_label_distinct, ctree_wbisim_refl]
QED

Theorem ctree_wbisim_bind_k[local]:
  (∀r. ctree_wbisim (k r) (k' r)) ==> ctree_wbisim (ctree_bind t (Tau o k)) (ctree_bind t (Tau o k'))
Proof
  rename[`∀r. ctree_wbisim (c r) (c' r)`] >> rw[]
  >> rw[Once ctree_wbisim_sym_strong_thm]
  >> qexists `λp q. ∃u k k'. (∀r. ctree_wbisim (k r) (k' r)) ∧
    p = ctree_bind u (Tau o k) ∧ q = ctree_bind u (Tau o k')`
  >> rw[]
  >- (gvs[symmetric_def] >> metis_tac[ctree_wbisim_sym])
  >- metis_tac[]
  >> qpat_x_assum `∀r. ctree_wbisim (c r) (c' r)` kall_tac
  >> dxrule_then strip_assume_tac $ iffLR ctree_lts_bind_cases
  >> gvs[]
  >- metis_tac[ctree_lts_bind_tau_vis, ctree_wlts_lts]
  >- metis_tac[ctree_elts_bind, ctree_elts_rules]
  >> dxrule_then strip_assume_tac ctree_lts_bind_ret
  >> first_x_assum $ qspecl_then [`k' r`, `tau`, `Tau o k'`] strip_assume_tac
  >> gvs[]
  >> metis_tac[ctree_elts_rules]
QED

Theorem ctree_wbisim_bind:
  ctree_wbisim t t' ∧ (∀r. ctree_wbisim (k r) (k' r))
    ==> ctree_wbisim (ctree_bind t (Tau o k)) (ctree_bind t' (Tau o k'))
Proof
  metis_tac[ctree_wbisim_bind_k, ctree_wbisim_bind_t, ctree_wbisim_trans]
QED

(* Useful for iter *)
Definition LRet_def:
  LRet s = Ret (INL s)
End

Definition RRet_def:
  RRet r = Ret (INR r)
End

Theorem LRRet_11[simp]:
  (LRet s = LRet s' <=> s = s') ∧
  (RRet r = RRet r' <=> r = r')
Proof
  rw[LRet_def, RRet_def]
QED

Theorem ctree_lts_LRRet_pcases[simp]:
  (ctree_lts (LRet s) l p <=> l = val (INL s) ∧ p = ctree_stuck) ∧
  (ctree_lts (RRet r) l p <=> l = val (INR r) ∧ p = ctree_stuck)
Proof
  rw[LRet_def, RRet_def]
QED

Theorem ctree_sbisim_LRRet[simp]:
  ¬ctree_sbisim (LRet s) (RRet r) ∧
  ¬ctree_sbisim (RRet s) (LRet r) ∧
  (ctree_sbisim (LRet s) (LRet s') <=> s = s') ∧
  (ctree_sbisim (RRet r) (RRet r') <=> r = r')
Proof
  rw[LRet_def, RRet_def]
QED

Theorem ctree_wbisim_LRRet[simp]:
  ¬ctree_wbisim (LRet s) (RRet r) ∧
  ¬ctree_wbisim (RRet s) (LRet r) ∧
  (ctree_wbisim (LRet s) (LRet s') <=> s = s') ∧
  (ctree_wbisim (RRet r) (RRet r') <=> r = r')
Proof
  rw[LRet_def, RRet_def]
QED

Theorem ctree_bind_LRRet[simp]:
  ctree_bind (LRet s) k = k (INL s) ∧
  ctree_bind (RRet r) k = k (INR r)
Proof
  rw[LRet_def, RRet_def]
QED

Definition itc_def:
  itc (t: ('a, 'b, 'c) itree) = ctree_unfold (λit.
    case it of
    | Ret r   => Ret' r
    | Tau u   => Tau' u
    | Vis e g => Vis' e g
  ) t
End

Theorem itc_thm[simp]:
  itc (Ret r) = Ret r ∧
  itc (Tau u) = Tau (itc u) ∧
  itc (Vis e g) = Vis e (itc o g)
Proof
  rw[itc_def, FUN_EQ_THM] >> metis_tac[]
QED

Theorem itc_cases:
  ∀t t'. itc t = t' <=>
  (∃r.     t = Ret r   ∧ Ret r           = t') ∨
  (∃u.     t = Tau u   ∧ Tau   (itc u)   = t') ∨
  (∃a e g. t = Vis e g ∧ Vis e (itc o g) = t')
Proof
  rw[EQ_IMP_THM] >> gvs[]
  >> Cases_on `t` >> gvs[]
QED

Theorem itc_pcases[simp]:
  (Ret r    = itc t <=> t = Ret r) ∧
  (Tau u'   = itc t <=> ∃u. u' = itc u ∧ t = Tau u) ∧
  (Vis e g' = itc t <=> ∃g. g' = itc o g ∧ t = Vis e g) ∧
  (Br k     ≠ itc t)
Proof
  rw[itc_cases] >> metis_tac[]
QED

Theorem itc_spin[simp]:
  itc spin = ctree_spin
Proof
  irule $ iffRL ctree_bisimulation
  >> qexists `λp q. p = itc spin ∧ q = ctree_spin`
  >> rw[] >> gvs[Once spin]
QED

Theorem itc_funpow[simp]:
  itc (FUNPOW Tau n p) = FUNPOW Tau n (itc p)
Proof
  Induct_on `n` >> rw[FUNPOW_SUC]
QED

Theorem itc_11[simp]:
  itc p = itc q <=> p = q
Proof
  rw[EQ_IMP_THM]
  >> rw[Once itree_strong_bisimulation]
  >> qexists `λu v. itc u = itc v` >> rw[]
  >> qpat_x_assum `itc p = itc q` kall_tac
  >> gvs[FUN_EQ_THM]
QED

Theorem ctree_lts_itc_cases:
  ∀p l q. ctree_lts (itc p) l q <=>
  (∃r.     p = Ret r   ∧ l = val r   ∧ q = ctree_stuck) ∨
  (∃u.     p = Tau u   ∧ l = tau     ∧ q = itc u) ∨
  (∃a e g. p = Vis e g ∧ l = obs e a ∧ q = itc (g a))
Proof
  rw[EQ_IMP_THM] >> gvs[Once ctree_lts_cases, Once itc_cases]
QED

Theorem ctree_wlts_itc_cases:
  ctree_wlts (itc p) l q' <=>
  (∃r.     strip_tau p (Ret r)   ∧ l = val r   ∧ q' = ctree_stuck) ∨
  (∃a e g. strip_tau p (Vis e g) ∧ l = obs e a ∧
       ∃q. q' = itc q ∧ ∃n. g a = FUNPOW Tau n q)
Proof
  eq_tac >- (
    qid_spec_tac `p`
    >> Induct_on `ctree_wlts` >> rw[FUN_EQ_THM]
    >> gvs[ctree_lts_itc_cases]
    >> metis_tac[FUNPOW_0, FUNPOW]
  )
  >> rw[]
  >> last_x_assum mp_tac >> Induct_on `strip_tau`
  >> gvs[]
QED

Theorem strip_tau_itc_vis:
  strip_tau p (Vis e g) ==> ctree_wlts (itc p) (obs e a) (itc (g a))
Proof
  Induct_on `strip_tau` >> rw[]
QED

Theorem itree_wbisim_imp_ctree_wbisim_itc[local]:
  itree_wbisim p q ==> ctree_wbisim (itc p) (itc q)
Proof
  rw[Once ctree_wbisim_sym_strong_thm]
  >> rename[`itree_wbisim t t'`]
  >> qexists `λu v. ∃p q. u = itc p ∧ v = itc q ∧ itree_wbisim p q`
  >> rw[]
  >- (gvs[symmetric_def] >> metis_tac[itree_wbisim_sym])
  >> qpat_x_assum `itree_wbisim t t'` kall_tac
  >> dxrule_then strip_assume_tac $ iffLR ctree_lts_itc_cases
  >> dxrule_then strip_assume_tac $ iffLR itree_wbisim_cases
  >> gvs[]
  >> metis_tac[
    ctree_wlts_itc_cases, ctree_wbisim_refl,
    itree_wbisim_rules, ctree_elts_refl, strip_tau_itc_vis
  ]
QED

Theorem ctree_wbisim_itc_ret[local]:
  ctree_wbisim (Ret r) (itc q) ==> strip_tau q (Ret r)
Proof
  rw[]
  >> dxrule_then strip_assume_tac ctree_wbisim_lts
  >> first_x_assum $ resolve_then Any strip_assume_tac ctree_lts_ret
  >> gvs[]
  >> dxrule_then strip_assume_tac $ iffLR ctree_wlts_itc_cases
  >> gvs[]
QED

Theorem ctree_wbisim_itc_vis[local]:
  ctree_wbisim (Vis e (itc o g)) (itc q: ('a, 'b, 'c, 'd) ctree) ==> ∃g'.
    strip_tau q (Vis e g') ∧ ∀a.
      ctree_wbisim (itc (g a)) (itc (g' a): ('a, 'b, 'c, 'd) ctree)
Proof
  rw[]
  >> dxrule_then strip_assume_tac ctree_wbisim_lts
  >> first_x_assum $ resolve_then Any strip_assume_tac ctree_lts_vis
  >> gvs[]
  >> first_assum $ qspec_then `a` strip_assume_tac
  >> drule_then strip_assume_tac $ iffLR ctree_wlts_itc_cases
  >> gvs[] >> qexists `g'` >> rw[]
  >> first_x_assum $ qspec_then `a'` strip_assume_tac
  >> dxrule_then strip_assume_tac $ iffLR ctree_wlts_itc_cases
  >> gvs[]
  >> dxrule_all strip_tau_inj >> rw[] >> gvs[]
QED

Theorem ctree_wbisim_itc_imp_itree_wbisim[local]:
  ∀p q. ctree_wbisim (itc p) (itc q) ==> itree_wbisim p q
Proof
  ho_match_mp_tac itree_wbisim_strong_coind >> rw[]
  >> Cases_on `p` >> Cases_on `q` >> gvs[]
  >> metis_tac[ctree_wbisim_itc_ret, ctree_wbisim_itc_vis, ctree_wbisim_sym]
QED

Theorem ctree_wbisim_itc_iff_itree_wbisim[simp]:
  ctree_wbisim (itc p) (itc q) <=> itree_wbisim p q
Proof
  metis_tac[itree_wbisim_imp_ctree_wbisim_itc, ctree_wbisim_itc_imp_itree_wbisim]
QED

Theorem itc_bind[simp]:
  itc (itree_bind t k) = ctree_bind (itc t) (itc o k)
Proof
  rw[Once ctree_strong_bisimulation]
  >> qexists `λx y. ∃p h. x = itc (itree_bind p h) ∧ y = ctree_bind (itc p) (itc o h)`
  >> rw[]
  >- metis_tac[]
  >> Cases_on `p` >> gvs[]
  >> metis_tac[]
QED

Datatype:
  ACtree = ARet 'r | ATau 'u | AVis 'e 'g
End

Definition ctree_head_def:
  ctree_head p = ctree_unfold (λs.
    case s of
    | Ret r   => Ret' (ARet r)
    | Tau u   => Ret' (ATau u)
    | Vis e g => Ret' (AVis e g)
    | Br  k   => Br' (λb. (k b))
  ) p
End

Theorem ctree_head_pcases[simp]:
  (ctree_head (Ret r) = Ret (ARet r)) ∧
  (ctree_head (Tau u) = Ret (ATau u)) ∧
  (ctree_head (Vis e g) = Ret (AVis e g)) ∧
  (ctree_head (Br k) = Br (λv. ctree_head (k v)))
Proof
  rw[ctree_head_def]
  >> rw[Once ctree_unfold_thm, o_DEF]
QED

Theorem ctree_head_combs[simp]:
  (ctree_head (Guard t) = Guard (ctree_head t)) ∧
  (ctree_head (Step t) = Guard (Ret (ATau t))) ∧
  (ctree_head (BrS k) = Br (λv. Ret (ATau (k v)))) ∧
  (ctree_head ctree_spin = Ret (ATau ctree_spin))
Proof
  rw[Guard_def, Step_def, BrS_def, Once ctree_spin_thm]
QED

Theorem ctree_head_stuck[simp]:
  ctree_head ctree_stuck = ctree_stuck
Proof
  rw[Once ctree_bisimulation]
  >> qexists `λp q. p = ctree_head ctree_stuck ∧ q = ctree_stuck`
  >> rw[] 
  >> gvs[Once ctree_stuck_thm]
  >> qexists `λv. ctree_stuck` >> rw[]
QED

Theorem ctree_head_label[simp]:
  ¬(ctree_lts (ctree_head p) tau q) ∧
  ¬(ctree_lts (ctree_head p) (obs e a) q)
Proof
  rw[] >> irule IMP_F
  >> qid_spec_tac `p`
  >> Induct_on `ctree_lts`
  >> (
    rw[] >> Cases_on `p` 
    >> gvs[] >> metis_tac[]
  )
QED

Theorem ctree_head_strip_ch:
  (ctree_lts (ctree_head p) (val (ARet r)) ctree_stuck <=> strip_ch p (Ret r)) ∧
  (ctree_lts (ctree_head p) (val (ATau u)) ctree_stuck <=> strip_ch p (Tau u)) ∧
  (ctree_lts (ctree_head p) (val (AVis e g)) ctree_stuck <=> strip_ch p (Vis e g))
Proof
  rw[] >> (
    eq_tac >> qid_spec_tac `p` >- (
      Induct_on `ctree_lts` >> rw[]
      >> Cases_on `p` >> gvs[] >> metis_tac[]
    )
    >> Induct_on `strip_ch` >> rw[] 
    >> metis_tac[]
  )
QED

Inductive is_val:
[~ret:] is_val (Ret r) r
[~tau:] is_val u r     ==> is_val (Tau u) r
[~vis:] is_val (g a) r ==> is_val (Vis e g) r
[~br:]  is_val (k v) r ==> is_val (Br k) r
End

Theorem is_val_pcases[simp]:
  (is_val (Ret r) r'   <=> r = r') ∧
  (is_val (Tau u) r'   <=> is_val u r') ∧
  (is_val (Vis e g) r' <=> ∃a. is_val (g a) r') ∧
  (is_val (Br k) r'    <=> ∃v. is_val (k v) r')
Proof
  rw[] >> gvs[Once is_val_cases]
QED

Theorem is_val_combs[simp]:
  (is_val (Guard t) r' <=> is_val t r') ∧
  (is_val (BrS k) r'   <=> ∃v. is_val (k v) r') ∧
  (is_val (Step t) r'  <=> is_val t r')
Proof
  rw[Guard_def, BrS_def, Step_def]
QED

Theorem is_val_stuck_spin[simp]:
  ¬is_val ctree_stuck r' ∧
  ¬is_val ctree_spin r'
Proof
  conj_tac
  >> Induct_on `is_val` >> rw[]
  >> metis_tac[]
QED

Theorem is_val_bind[simp]:
  is_val (ctree_bind p k) r' <=> ∃r. is_val p r ∧ is_val (k r) r'
Proof
  eq_tac >- (
    qid_spec_tac `p`
    >> Induct_on `is_val` >> rw[]
    >> Cases_on `p` >> gvs[]
    >> metis_tac[]
  )
  >> rw[] >> rpt (first_x_assum mp_tac)
  >> Induct_on `is_val` >> rw[]
  >> metis_tac[]
QED

Inductive is_val_chain:
[~nil:]  is_val (k s) (INR r) ==> is_val_chain k s [] r
[~cons:] is_val (k s) (INL s') ∧ is_val_chain k s' tl r
           ==> is_val_chain k s (s'::tl) r
End

Theorem is_val_chain_simp[simp]:
  (is_val_chain k s [] r <=> is_val (k s) (INR r)) ∧
  (is_val_chain k s (s'::tl) r <=> is_val (k s) (INL s') ∧ is_val_chain k s' tl r)
Proof
  rw[] >> rw[Once is_val_chain_cases]
QED

Theorem is_val_iter_rules:
  (is_val (k s) (INR r) ==> is_val (ctree_iter k s) r) ∧
  (is_val (k s) (INL s') ∧ is_val (ctree_iter k s') r ==> is_val (ctree_iter k s) r)
Proof
  rw[]
  >> rw[ctree_iter_fn_thm]
  >> rw[ctree_iter_fn_def]
  >| [qexists `INR r`, qexists `INL s'`]
  >> rw[]
QED

Theorem is_val_iter_fn:
  is_val (ctree_bind u (ctree_iter_fn k)) r <=>
    is_val u (INR r) ∨
    ∃s seeds. is_val u (INL s) ∧ is_val_chain k s seeds r
Proof
  eq_tac >- (
    qid_spec_tac `u`
    >> Induct_on `is_val` >> rw[] >~ [`Br`] 
    >> Cases_on `u` >> gvs[ctree_iter_fn_def, AllCaseEqs()]
    >- (
      first_x_assum $ qspec_then `k i` strip_assume_tac
      >> gvs[ctree_iter_fn_thm]
      >- (qexists `[]` >> gvs[])
      >> qexists `s::seeds` >> gvs[]
    )
    >> metis_tac[]
  )
  >> rw[] >| [qexists `INR r`, qexists `INL s`]
  >> gvs[ctree_iter_fn_def]
  >> rpt (first_x_assum mp_tac) 
  >> qid_spec_tac `s` >> qid_spec_tac `u`
  >> Induct_on `seeds` >> rw[]
  >> metis_tac[is_val_iter_rules]
QED

Theorem is_val_iter[simp]:
  is_val (ctree_iter k s) r <=> ∃seeds. is_val_chain k s seeds r
Proof
  rw[EQ_IMP_THM, ctree_iter_fn_thm, is_val_iter_fn]
  >> metis_tac[is_val_chain_cases]
QED

CoInductive retless:
[~tau:] retless u ==> retless (Tau u)
[~vis:] (∀a. retless (g a)) ==> retless (Vis e g)
[~br:] (∀v. retless (k v)) ==> retless (Br k)
End

Theorem not_retless_ret[simp]:
  ¬retless (Ret r)
Proof
  spose_not_then strip_assume_tac
  >> gvs[Once retless_cases]
QED

Theorem retless_pcases[simp]:
  (retless (Tau u)   <=> retless u) ∧
  (retless (Vis e g) <=> ∀a. retless (g a)) ∧
  (retless (Br k)    <=> ∀v. retless (k v))
Proof
  rw[] >> gvs[Once retless_cases]
QED

Theorem retless_iff_not_is_val:
  retless p <=> ∀r'. ¬is_val p r'
Proof
  rw[EQ_IMP_THM] >- (
    first_x_assum mp_tac
    >> Induct_on `is_val` >> rw[]
    >> metis_tac[]
  )
  >> irule retless_coind
  >> qexists `λu. ∀r'. ¬is_val u r'` >> rw[]
  >> rename[`∀r'. ¬is_val u r'`] >> Cases_on `u`
  >> gvs[]
QED

Theorem retless_combs[simp]:
  (retless (Guard t) <=> retless t) ∧
  (retless (BrS k)   <=> ∀v. retless (k v)) ∧
  (retless (Step t)  <=> retless t) ∧
  retless ctree_stuck ∧
  retless ctree_spin
Proof
  rw[Guard_def, BrS_def, Step_def, retless_iff_not_is_val]
  >> metis_tac[]
QED

Theorem retless_bind:
  retless (ctree_bind p k) <=> ∀r. is_val p r ==> retless (k r)
Proof
  rw[retless_iff_not_is_val] >> metis_tac[]
QED

Theorem retless_iter:
  retless (ctree_iter k s) <=> ∀seeds r. ¬is_val_chain k s seeds r
Proof
  rw[retless_iff_not_is_val] >> metis_tac[]
QED

Theorem retless_iter_once:
  retless (ctree_iter k s) <=> 
    (∀r. ¬is_val (k s) (INR r)) ∧ 
    ∀s'. is_val (k s) (INL s') ==> retless (ctree_iter k s')
Proof
  rw[EQ_IMP_THM, retless_iff_not_is_val]
  >> metis_tac[is_val_chain_cases]
QED

(* Examples *)

(* An interesting example of a stuck ctree *)
Theorem ctree_iter_stuck[local]:
  ctree_iter (λx. Ret $ INL (x+1)) 0 = ctree_stuck
Proof
  rw[Once ctree_bisimulation]
  >> qexists `λp q. ∃n. p = ctree_iter (λx. Ret $ INL (x+1)) n ∧ q = ctree_stuck`
  >> rw[]
  >- metis_tac[]
  >> gvs[Once ctree_iter_thm]
  >> qexists `λv. ctree_stuck`
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
  >> rw[ctree_collatz_tree]
  >> qexists `n` >> rw[Abbr `n`]
  >> rw[ctree_iter_fn_thm]
QED

(* Counterexample to converse of ctree_sbisim_strip_ch *)
Definition BrVis1_def[local]:
  brvis1 = Br (λb. Vis 7 (λa. Ret (if b then a else ¬a)))
End

Definition BrVis2_def[local]:
  (brvis2: (bool, bool, num, bool) ctree) = Br (λb. Vis 7 (λa. Ret b))
End

Theorem BrVis1_lts[local]:
  ctree_lts brvis1 l p <=> ∃a b. l = obs 7 a ∧ p = Ret b
Proof
  rw[EQ_IMP_THM, BrVis1_def] >> metis_tac[]
QED

Theorem BrVis2_lts[local]:
  ctree_lts brvis2 l p <=> ∃a b. l = obs 7 a ∧ p = Ret b
Proof
  rw[EQ_IMP_THM, BrVis2_def] >> metis_tac[]
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
  >> metis_tac[ctree_lts_brvis12]
QED

(* Counterexample to ctree_wbisim_br *)

Definition btk_def[local]:
  (btk: bool -> (bool, bool, bool, bool) ctree) = Tau o Ret
End

Definition btk'_def[local]:
  (btk': bool -> (bool, bool, bool, bool) ctree) = Ret
End

Theorem not_ctree_wbisim_br[local]:
  (∀b. ∃b'. ctree_wbisim (btk b) (btk' b')) ∧
  (∀b'. ∃b. ctree_wbisim (btk b) (btk' b')) ∧
  ¬ctree_wbisim (Br btk) (Br btk')
Proof
  rw[btk_def, btk'_def]
  >> spose_not_then strip_assume_tac
  >> dxrule_then strip_assume_tac ctree_wbisim_lts_tau
  >> gvs[]
  >> first_x_assum $ qspec_then `Ret F` strip_assume_tac
  >> gvs[]
  >> dxrule_then strip_assume_tac ctree_wbisim_sym
  >> dxrule_then strip_assume_tac ctree_wbisim_lts
  >> first_x_assum $ resolve_then Any strip_assume_tac ctree_lts_br
  >> gvs[]
QED

Theorem not_ctree_wbisim_bind_k[local]:
  (∀r. ctree_wbisim (btk r) (btk' r)) ∧
  ¬ctree_wbisim (ctree_bind (Br Ret) btk) (ctree_bind (Br Ret) btk')
Proof
  rw[btk_def, btk'_def]
  >> `¬ctree_wbisim (Br btk) (Br btk')` suffices_by (metis_tac[btk_def, btk'_def])
  >> rw[not_ctree_wbisim_br]
QED
