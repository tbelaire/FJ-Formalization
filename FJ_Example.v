
(***************************************************************************
 * Cast-Free Featherweight Java
 *
 * Bruno De Fraine, with help from Erik Ernst and Mario Sudholt, Summer 2008
 ***************************************************************************)

Require Import AdditionalTactics.
Require Import Metatheory.
Require Import FJ_Definitions.
Require Import FJ_Facts.
Require Import FJ_Properties.

(* The classic Pair example from the FJ paper *)

Variable A : cname.
Variable B : cname.
Hypothesis A_fresh: Object <> A.
Hypothesis B_fresh: Object <> B /\ A <> B.

Variable Pair : cname.
Hypothesis Pair_fresh : Object <> Pair /\ A <> Pair /\ B <> Pair.

Lemma A_fresh_not: ~(Object = A).
Proof.
exact A_fresh.
Qed.

Lemma B_fresh_not: ~(Object = B \/ A = B).
Proof.
destruct B_fresh.
tauto.
Qed.

Lemma Pair_fresh_not: ~(Object = Pair \/ A = Pair \/ B = Pair).
Proof.
destruct Pair_fresh.
destruct H0.
tauto.
Qed.

Hint Local Resolve A_fresh_not B_fresh_not Pair_fresh_not.

Variable fst : fname.
Variable snd : fname.
Hypothesis fst_neq_snd : fst <> snd.
Variable setfst : mname.
Variable newfst : var.
Hypothesis newfst_neq_this : this <> newfst.

Definition pair_flds : flds := (fst,Object) :: (snd,Object) :: nil.

Definition pair (a: exp) (b: exp) := e_new Pair (a :: b :: nil).

Definition setfst_env : env := (newfst,Object) :: nil.
Definition setfst_body : exp := pair (e_var newfst) (e_field (e_var this) snd).
Definition pair_mths : mths := (setfst,(Pair,setfst_env,setfst_body)) :: nil.

Hypothesis ct_fix: CT =
    (A,(Object,nil,nil)) ::
    (B,(Object,nil,nil)) ::
    (Pair,(Object,pair_flds,pair_mths)) :: nil.

Module ExNoObj: NoObj.

Lemma ct_noobj: Object \notin dom CT.
Proof.
rewrite ct_fix.
simpl. intuition auto.
Qed.

End ExNoObj.

Lemma ct_a: binds A (Object,nil,nil) CT.
Proof.
rewrite ct_fix in |- *. auto using binds_first, binds_other.
Qed.

Lemma ct_b: binds B (Object,nil,nil) CT.
Proof.
rewrite ct_fix in |- *. auto using binds_first, binds_other.
Qed.

Lemma ct_pair: binds Pair (Object,pair_flds,pair_mths) CT.
Proof.
rewrite ct_fix in |- *. auto 7 using binds_first, binds_other.
Qed.

Hint Local Resolve ct_a ct_b ct_pair fst_neq_snd newfst_neq_this.

Hint Unfold no_binds.

Lemma ex_ok_setfst_env : ok ((this,Pair)::setfst_env).
Proof.
pose newfst_neq_this.
unfold setfst_env in |- *.
auto using nobinds_nil, nobinds_cons.
Qed.

Lemma pair_pair_flds : fields Pair pair_flds.
Proof.
change pair_flds with (nil ++ pair_flds) in |- *; eauto.
Qed.

Hint Local Resolve ex_ok_setfst_env pair_pair_flds.

Module Import Facts1 := NoObjFacts ExNoObj.

Lemma ex_ok_setfst: ok_meth Pair Object setfst Pair setfst_env setfst_body.
Proof.
split.
Case "left"; unfold can_override. intros. contradiction (obj_nomeths _ _ H).
Case "right".
assert (binds snd Object pair_flds).
unfold pair_flds. eauto using binds_first, binds_other.
assert (typing ((this, Pair) :: setfst_env) (e_var newfst) Object).
unfold setfst_env. eauto using binds_first, binds_other.
assert (wide_typings ((this, Pair) :: setfst_env) ((e_var newfst)::(e_field (e_var this) snd)::nil) (imgs pair_flds)).
unfold pair_flds. simpl. eauto 10 using binds_first.
unfold setfst_body; unfold pair; eauto.
Qed.

Lemma ex_ok_pair: ok_class Pair Object pair_flds pair_mths.
Proof.
split.
(*EDIT1 BEGIN*)
(*intros; rewrite (obj_nofields _ H); unfold pair_flds. simpl. auto using nobinds_nil, nobinds_cons.*)
exists nil; split. apply fields_obj. unfold pair_flds. simpl. auto using nobinds_nil, nobinds_cons.
(*EDIT1 END*)
unfold pair_mths in |- *.
split.
auto.
assert (ok_meth' Pair Object setfst (Pair, setfst_env, setfst_body)).
unfold ok_meth'. apply ex_ok_setfst.
auto.
Qed.

Module ExOkTable: OkTable.

Lemma ok_ct: ok_ctable CT.
Proof.
rewrite ct_fix in |- *.
unfold ok_ctable in |- *.
split.
auto 8 using nobinds_nil, nobinds_cons.
apply fa_cons.
apply fa_cons.
apply fa_cons.
apply fa_nil.
unfold ok_class' in |- *; apply ex_ok_pair.
unfold ok_class' in |- *; apply ok_class_empty.
unfold ok_class' in |- *; apply ok_class_empty.
Qed.

End ExOkTable.

Module ExHyps: Hyps.

Definition ct_noobj := ExNoObj.ct_noobj.
Definition ok_ct := ExOkTable.ok_ct.

End ExHyps.

Module Import Props1 := Properties ExHyps.

(* new Pair(a, b).snd -> b *)
Lemma ex_step_field: forall a b, eval (e_field (pair a b) snd) b.
Proof.
intros.
unfold pair in |- *.
eapply eval_field.
apply pair_pair_flds.
unfold pair_flds in |- *; simpl.
apply z_cons.
apply z_cons.
apply z_nil.
eauto using binds_first, binds_other.
Qed.

Lemma ex_type_field:
typing nil (e_field (pair (e_new A nil) (e_new B nil)) snd) Object.
Proof.
eapply t_field.
unfold pair; eapply t_new.
eauto.
unfold pair_flds; simpl.
eapply wts_cons.
eapply wts_cons.
eauto.
eapply wt_sub.
eapply t_new.
eauto.
simpl; eauto.
eauto.
eapply wt_sub.
eapply t_new.
eauto.
simpl; eauto.
eauto.
red.
econstructor.
eauto.
unfold pair_flds.
eauto using binds_other, binds_first.
Qed.

Lemma ex_subst_body: forall a b c,
    subst_exp ((this,pair a b)::(newfst,c)::nil) setfst_body =
    pair c (e_field (pair a b) snd).
Proof.
intros.
simpl in |- *.
rewrite eq_atom_true in |- *.
rewrite eq_atom_false in |- *.
rewrite eq_atom_true in |- *.
reflexivity.
auto.
Qed.

(* new Pair(a, b).setfst(c) -> new Pair(c, b) *)
Lemma ex_step_meth: forall a b c,
    eval (e_meth (pair a b) setfst (c::nil)) (pair c (e_field (pair a b) snd)).
Proof.
intros.
rewrite <- ex_subst_body in |- *.
unfold pair in |- *.
eapply eval_meth.
eapply method_this.
apply ct_pair.
unfold pair_mths in |- *.
eapply binds_first.
unfold setfst_env in |- *; simpl.
apply z_cons.
apply z_nil.
Qed.
