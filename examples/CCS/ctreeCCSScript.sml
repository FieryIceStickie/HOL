Theory ctreeCCS
Ancestors
  arithmetic list option relation combin bisimulation 
  ctree CCS
Libs
  term_tactic mp_then BasicProvers dep_rewrite

Type ccs_ctree_base[pp] = ``:(unit, bool option, 'a Label, 'r) ctree``
Type ccs_ctree_label_base[pp] = ``:(unit, 'a Label, 'b) ctree_label``

Type ccs_ctree[pp] = ``:('a, string) ccs_ctree_base``
Type ccs_ctree_label[pp] = ``:('a, string) ccs_ctree_label_base``

Theorem ccs_branch_cases:
  ∀v. v = SOME F ∨ v = SOME T ∨ v = NONE 
Proof
  Cases_on `v` >> rw[]
QED

Definition LRet_def:
  LRet r = Ret (INL r)
End

Definition RRet_def:
  RRet r = Ret (INR r)
End

Definition ctree_nil_def:
  ctree_nil = (ctree_stuck: 'a ccs_ctree)
End

Theorem ctree_nil_lts[simp]:
  ¬ctree_lts ctree_nil l p
Proof
  rw[ctree_nil_def]
QED

Definition ctree_sum_def:
  ctree_sum (p: 'a ccs_ctree) q = Br (λv. 
    case v of
    | SOME F => p
    | SOME T => q
    | NONE => ctree_stuck
  )
End

Theorem ctree_sum_lts_cases:
  ctree_lts (ctree_sum p q) l t <=> ctree_lts p l t ∨ ctree_lts q l t
Proof
  rw[EQ_IMP_THM, ctree_sum_def]
  >- (Cases_on `v` using ccs_branch_cases >> gvs[])
  >| [qexists `SOME F`, qexists `SOME T`]
  >> rw[]
QED

Definition actL_def:
  actL p' q =
    case p' of
    | ATau u   => Tau (LRet (u, q))
    | AVis e g => Vis e (λa. LRet (g a, q))
    | _ => ctree_stuck
End

Definition actR_def:
  actR p q' =
    case q' of
    | ATau u   => Tau (LRet (p, u))
    | AVis e g => Vis e (λa. LRet (p, g a))
    | _ => ctree_stuck
End

Definition actLR_def:
  actLR p' q' =
    case (p', q') of
    | (AVis e g, AVis e' g') => if e = COMPL_LAB e' 
                                then Tau (LRet (g (), g' ()))
                                else ctree_stuck
    | _ => ctree_stuck
End

Definition ctree_par_fn_def:
  ctree_par_fn (p, q) = Br (λv. 
    case v of
    | SOME F => ctree_bind (ctree_head p) (λp'. actL p' q)
    | SOME T => ctree_bind (ctree_head q) (λq'. actR p q')
    | NONE => ctree_bind (ctree_head p) (λp'. 
              ctree_bind (ctree_head q) (λq'. actLR p' q'))
  )
End

Definition ctree_par_def:
  ctree_par (p: 'a ccs_ctree) (q: 'a ccs_ctree) = ctree_iter ctree_par_fn (p, q)
End

Definition colab_def:
  colab l l' <=> ∃n. l = obs n () ∧ l' = obs (COMPL_LAB n) ()
End

Theorem colab_sym:
  colab l l' ==> colab l' l
Proof
  rw[colab_def, COMPL_COMPL_LAB]
QED

Theorem ctree_par_lts_rules:
  (ctree_lts p l p' ==> ctree_lts (ctree_par p q) l (ctree_par p' q)) ∧
  (ctree_lts q l q' ==> ctree_lts (ctree_par p q) l (ctree_par p q')) ∧
  (ctree_lts p l p' ∧ ctree_lts q l' q' ∧ colab l l'
    ==> ctree_lts (ctree_par p q) tau (ctree_par p' q'))
Proof
  rw[] >> rw[ctree_par_def, Once ctree_iter_fn_thm, ctree_par_fn_def]
  >| [qexists `SOME F`, qexists `SOME T`, qexists `NONE`] >> rw[]
  >> irule ctree_lts_iter_tau_vis
QED

Theorem ctree_par_lts:

  ctree_lts (ctree_par p q) l t <=>
    (∃p'. ctree_lts p l p' ∧ t = ctree_par p' q) ∨
    (∃q'. ctree_lts q l q' ∧ t = ctree_par p q') ∨
    (l = tau ∧ ∃n p' q'. 
      ctree_lts p (obs n ()) p' ∧ 
      ctree_lts q (obs (COMPL_LAB n) ()) q' ∧
      t = ctree_par p' q')

Proof
  rw[EQ_IMP_THM] >- (
    gvs[Once ctree_par_def, Once ctree_iter_fn_thm]
    >> dxrule_then strip_assume_tac $ iffLR ctree_lts_iter_fn_cases
    >> gvs[]

  )
QED
    

Definition ctree_restr_def:
  (ctree_restr: 'a -> 'a ccs_ctree -> 'a ccs_ctree) c =
    ctree_unfold (λt.
      case t of
      | Ret r   => Ret' r
      | Tau u   => Tau' u
      | Br k    => Br' k
      | Vis e g => (
        if e = name c ∨ e = coname c
        then Br' (λv. ctree_stuck)
        else Vis' e g
      )
    )
End

Definition ctree_rec_def:
  ctree_rec x (p: 'a ccs_ctree) =
    ctree_iter (λs. 
      ctree_bind p (λv. Ret (
        if v = x
        then INL p
        else INR v)))
End



  

Definition ccs_label_same:
  ccs_label_same (l: 'a ccs_ctree_label) (l': 'a Action) <=>
    (∃n. l = obs n () ∧ l' = label n) ∨
    (l = tau ∧ l' = tau)
End

Definition interp_ccs:
  (interp_ccs: 'a CCS -> 'a ccs_ctree) =
    ctree_iter (λs.
      case s of
      | var a     => RRet a
      | l..p      => IVis l (λa. LRet p)
      | p + q     => ccs_sum p q
      | p || q    => Ret (INR "")
      | restr c p => Ret (INR "")
      | rec x p   => Ret (INR "")
    )
End
