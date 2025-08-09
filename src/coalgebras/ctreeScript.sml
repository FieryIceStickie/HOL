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

Type ctree_rep[local] = “:('a + 'b) option list -> ('e,'r) ctree_el”;
val f = “(f: ('a,'b,'e,'r) ctree_rep)”

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

(* --- Constructors --- *)

(* Ret *)
Definition Ret_rep_def:
  Ret_rep (x: 'r) =
    λpath. if path = [] then Return x else Silence
End

Definition Ret_def:
  Ret x = ctree_abs (Ret_rep x)
End

Theorem ctree_rep_ok_Ret[local]:
  ∀x. ctree_rep_ok (Ret_rep x)
Proof
  rw[ctree_rep_ok_def, Ret_rep_def]
  >> Cases_on `path = []`
  >> gvs[path_ok_def]
QED

Theorem Ret_rep_11[local]:
  ∀x y. Ret_rep x = Ret_rep y <=> x = y
Proof
  rw[Ret_rep_def, FUN_EQ_THM] >> eq_tac >> rw[]
  >> first_x_assum $ qspec_then `[]` mp_tac
  >> rw[]
QED

Theorem Ret_11:
  ∀x y. Ret x = Ret y <=> x = y
Proof
  metis_tac[Ret_def, ctree_rep_ok_Ret, ctree_abs_11, ctree_rep_11, Ret_rep_11]
QED

(* Tau *)
Definition Tau_rep_def:
  Tau_rep ^f =
    λpath. case path of
           | NONE::rest => f rest
           | _ => Silence
End

Definition Tau_def:
  Tau t = ctree_abs $ Tau_rep (ctree_rep t)
End

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

Theorem Tau_rep_11[local]:
  ∀x y. Tau_rep x = Tau_rep y <=> x = y
Proof
  rw[Tau_rep_def, FUN_EQ_THM] >> eq_tac >> rw[]
  >> rename[`x r = y r`]
  >> first_x_assum $ qspec_then `NONE::r` mp_tac
  >> rw[]
QED

Theorem Tau_11:
  ∀x y. Tau x = Tau y <=> x = y
Proof
  metis_tac[Tau_def, ctree_rep_ok_ctree_rep, ctree_rep_ok_Tau,
            ctree_abs_11, ctree_rep_11, Tau_rep_11]
QED

(* Vis *)
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

Theorem Vis_rep_11[local]:
  ∀x y g k. Vis_rep x g = Vis_rep y k <=> x = y ∧ g = k
Proof
  rw[Vis_rep_def, FUN_EQ_THM] >> eq_tac >> rw[]
  >| [
    first_x_assum $ qspec_then `[]` mp_tac,
    rename[`g a r = k a r`]
    >> first_x_assum $ qspec_then `SOME (INL a)::r` mp_tac
  ] >> rw[]
QED

Theorem Vis_11:
  ∀x y g k. Vis x g = Vis y k <=> x = y ∧ g = k
Proof
  rw[Vis_def] >> eq_tac
  >> qmatch_goalsub_abbrev_tac `ctree_abs v1 = ctree_abs v2`
  >> `ctree_rep_ok v1 ∧ ctree_rep_ok v2` by (unabbrev_all_tac >> fs[ctree_rep_ok_Vis])
  >> unabbrev_all_tac >> rw[]
  >> rev_dxrule_all ctree_abs_11
  >> rw[Vis_rep_11, ctree_rep_ok_ctree_rep, FUN_EQ_THM]
  >> metis_tac[ctree_rep_11]
QED

(* Br *)
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

Theorem Br_rep_11[local]:
  ∀g k. Br_rep g = Br_rep k <=> g = k
Proof
  rw[Br_rep_def, FUN_EQ_THM] >> eq_tac >> rw[]
  >> rename[`g a r = k a r`]
  >> first_x_assum $ qspec_then `SOME (INR a)::r` mp_tac
  >> rw[]
QED

Theorem Br_11:
  ∀g k. Br g = Br k <=> g = k
Proof
  rw[Br_def] >> eq_tac
  >> qmatch_goalsub_abbrev_tac `ctree_abs v1 = ctree_abs v2`
  >> `ctree_rep_ok v1 ∧ ctree_rep_ok v2` by (unabbrev_all_tac >> fs[ctree_rep_ok_Br])
  >> unabbrev_all_tac >> rw[]
  >> rev_dxrule_all ctree_abs_11
  >> rw[Br_rep_11, ctree_rep_ok_ctree_rep, FUN_EQ_THM]
  >> metis_tac[ctree_rep_11]
QED

Theorem ctree_11 = LIST_CONJ [Ret_11, Tau_11, Vis_11, Br_11];

(* A few useful lemmas *)
Theorem ctree_rep_ok_All[local] =
  LIST_CONJ [ctree_rep_ok_Ret, ctree_rep_ok_Tau, ctree_rep_ok_Vis, ctree_rep_ok_Br];

Theorem All_def[local] = LIST_CONJ [Ret_def, Tau_def, Vis_def, Br_def];

Theorem All_rep_def[local] = LIST_CONJ [Ret_rep_def, Tau_rep_def, Vis_rep_def, Br_rep_def];

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

Theorem ctree_rep_cases[local]:
  ctree_rep_ok f ==>
      (∃r  . f = Ret_rep r                           )
    ∨ (∃u  . f = Tau_rep u   ∧     ctree_rep_ok u    )
    ∨ (∃e g. f = Vis_rep e g ∧ ∀a. ctree_rep_ok $ g a)
    ∨ (∃k  . f = Br_rep  k   ∧ ∀b. ctree_rep_ok $ k b)
Proof
  rw[Once ctree_rep_ok_def, path_ok_def]
  >> Cases_on `f []`
  >> rw[All_rep_def, FUN_EQ_THM]
  >| [
    (* Return *)
    disj1_tac >> qexists `r` >> Cases_on `x`,
    (* Tau *)
    disj2_tac >> disj1_tac
    >> qexists `λpath. f (NONE::path)`,
    (* Vis *)
    disj2_tac >> disj2_tac >> disj1_tac
    >> qexistsl[`e`,`λa path. f (SOME (INL a)::path)`],
    (* Br *)
    disj2_tac >> disj2_tac >> disj2_tac
    >> qexists `λb path. f (SOME (INR b)::path)`
  ] >> rw[]
  >> rpt (case_tac >> rw[])
  >> rw[ctree_rep_ok_cons, ctree_rep_ok_def, path_ok_def]
  >> irule path_not_ok_imp_silence >> rw[ctree_rep_ok_def, path_ok_def]
QED
