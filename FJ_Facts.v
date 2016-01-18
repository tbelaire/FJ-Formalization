
(***************************************************************************
 * Cast-Free Featherweight Java
 *
 * Bruno De Fraine, with help from Erik Ernst and Mario Sudholt, Summer 2008
 ***************************************************************************)

Require Import AdditionalTactics.
Require Import Metatheory.
Require Import FJ_Definitions.

(** * Auxiliary facts *)

(** ** Mutual induction schemes *)

(* See section 10.3 of the refman *)

Scheme typing_typings_ind := Minimality for typing Sort Prop
with wide_typing_typings_ind := Minimality for wide_typing Sort Prop
with wide_typings_typings_ind := Minimality for wide_typings Sort Prop.

Combined Scheme typings_mutind from typing_typings_ind, wide_typing_typings_ind, wide_typings_typings_ind.

(** ** Inversions to retrieve information from typings *)

Fact typings_implies_ok_env:
    (forall E e t, typing E e t -> ok E) /\
    (forall E e t, wide_typing E e t -> ok E) /\
    (forall E es env, wide_typings E es env -> ok E).
Proof.
  apply typings_mutind; intros; trivial.
Qed.

Definition typing_implies_ok_env := proj1 typings_implies_ok_env.
Definition wide_typing_implies_ok_env := proj1 (proj2 typings_implies_ok_env).
Definition wide_typings_implies_ok_env := proj2 (proj2 typings_implies_ok_env).

Hint Immediate typing_implies_ok_env wide_typing_implies_ok_env wide_typings_implies_ok_env.

Fact ok_class_meth: forall C D fs ms m t E e,
    ok_class C D fs ms ->
    binds m (t,E,e) ms ->
    ok_meth C D m t E e.
Proof.
  intros.
  destruct H as (_, (_, H)).
  fold (ok_meth' C D m (t, E, e)).
  eapply fa_binds_elim; eassumption.
Qed.

Fact ok_ctable_class: forall ct C D fs ms,
    ok_ctable ct ->
    binds C (D,fs,ms) ct ->
    ok_class C D fs ms.
Proof.
  intros.
  destruct H as (_, H).
  fold (ok_class' C (D, fs, ms)).
  eapply fa_binds_elim; eassumption.
Qed.

(** ** Correspondence between keys and images of the same environment *)

Fact wide_typings_implies_zip: forall E0 E ds,
    wide_typings E0 ds (imgs E) ->
    exists Eds, env_zip E ds Eds.
Proof.
  intros. generalize dependent ds.
  induction E; intros; inversion H; subst.
  Case "el_nil". eauto.
  Case "el_cons".
    destruct IHE with (1:=H4).
    destruct a. eauto.
Qed.

Fact binds_zip: forall E0 E ds Eds v t,
    wide_typings E0 ds (imgs E) ->
    env_zip E ds Eds ->
    binds v t E ->
    (exists2 e, binds v e Eds & wide_typing E0 e t).
Proof.
  intros E0 E ds Eds v t. revert ds Eds.
  induction E; intros; [ | destruct a as (a0,t0)]; inversion H1.
  Case "cons".
    inversion H0. subst. inversion H. subst.
    destruct (v == a0).
    SCase "v = a0". subst injections. eauto using binds_first.
    SCase "v <> a0".
      destruct IHE with (1:=H7) (2:=H8) (3:=H3).
      eauto using binds_other.
Qed.

(** ** Properties that follow from the [ct_noobj] hypothesis *)

Module Type NoObj.
    Parameter ct_noobj: Object \notin dom CT.
End NoObj.

Module NoObjFacts (Import H: NoObj).

    Fact obj_nofields : forall flds, fields Object flds -> flds = nil.
    Proof.
      intros.
      inversion_clear H; subst.
        reflexivity.
        contradiction by (apply ct_noobj). eapply binds_In; eassumption.
    Qed.

    Fact obj_nomeths : forall m mdecl, ~method Object m mdecl.
    Proof.
      unfold not; intros.
      inversion_clear H; subst; apply ct_noobj; eapply binds_In; eassumption.
    Qed.

    Fact ok_class_empty: forall C, ok_class C Object nil nil.
    Proof.
      intros.
      unfold ok_class; split.
        (*EDIT1 BEGIN*)
        (*intros fs H.
        rewrite obj_nofields with (1:=H).*)
        exists nil; split.
        apply fields_obj.
        (*EDIT1 END*)
        simpl. auto.
        auto.
    Qed.

    Fact fields_fun: forall t fs fs',
        fields t fs -> fields t fs' -> fs = fs'.
    Proof.
      intros t fs fs' H H'. revert fs' H'.
      induction H; intros; inversion H'; subst;
        try solve [ contradiction by (apply ct_noobj); eapply binds_In; eassumption ].
      Case "fields_obj". reflexivity.
      Case "fields_other".
        assert ((D, fs, ms) = (D0, fs0, ms0)) by (eapply binds_fun; eassumption).
        subst injections.
        replace fs'1 with fs'; auto.
    Qed.

End NoObjFacts.

(** * Other properties and generalized typing rules *)

(** The generalized typing rules recreate the ordinary term typing rules, but
    require a [wide_typing] in place of a [typing] in the conditions. They
    usually follow from the property that subtyping preserves methods,
    fields,... *)

Fact method_fun: forall t m mdecl mdecl',
    method t m mdecl -> method t m mdecl' -> mdecl = mdecl'.
Proof.
  intros t m mdecl mdecl' H H'.
  induction H; destruct H'; assert ((D, fs, ms) = (D0, fs0, ms0))
    by (eapply binds_fun; eassumption); subst injections.
  Case "method_this-method_this". eapply binds_fun; eassumption.
  Case "method_this-method_other". contradiction by (eauto using binds_nobinds).
  Case "method_other-method_this". contradiction by (eauto using binds_nobinds).
  Case "method_other-method_ohter". eauto.
Qed.

(** ** Subtyping preserves fields *)

Fact sub_fields: forall u v fsv,
    sub u v -> fields v fsv -> exists fs, fields u (fsv ++ fs).
Proof.
  intros u v fsv H Hv. revert fsv Hv.
  induction H; intros.
  Case "sub_refl".
    exists (nil : flds). rewrite <- app_nil_end. assumption.
  Case "sub_trans".
    destruct IHsub2 with (1:=Hv) as (fsu, IH2).
    destruct IHsub1 with (1:=IH2) as (fst, IH1).
    rewrite app_ass in IH1.
    eauto.
  Case "sub_extends".
    destructs H. eauto.
Qed.

Fact sub_field: forall u v f t,
    sub u v -> field v f t -> field u f t.
Proof.
  unfold field. intros.
  destruct H0 as (fs, H0, H1).
  destruct sub_fields with (1:=H) (2:=H0) as (fs0, HH).
  eauto using binds_head.
Qed.

(** ** First two generalized typing rules *)

Lemma gt_field: forall E e0 f t t0,
    wide_typing E e0 t0 ->
    field t0 f t ->
    typing E (e_field e0 f) t.
Proof.
destruct 1; eauto using sub_field.
Qed.

Hint Resolve gt_field.

Lemma gt_sub : forall E e t t',
    wide_typing E e t ->
    sub t t' ->
    wide_typing E e t'.
Proof.
destruct 1; eauto.
Qed.

(* To avoid needless search, only hint gt_sub when the sub relation is already in
 * context; similar in spirit to "Hint Immediate gt_sub." but a little more powerful *)
Hint Extern 1 (wide_typing ?E ?e ?t) =>
match goal with
| H: sub ?t0 t |- _ => refine (gt_sub E e t0 t _ H)
end.

(** ** Properties that follow from [ok_ct] assumption *)

Module Type OkTable.
    Parameter ok_ct: ok_ctable CT.
End OkTable.

Module OkTableFacts (Import H: OkTable).

    Definition ok_ct_class C D fs ms := ok_ctable_class _ C D fs ms ok_ct.
    Definition ok_ct_meth C D fs ms m t E e H :=
        ok_class_meth C D fs ms m t E e (ok_ct_class _ _ _ _ H).

    Hint Resolve ok_ct_class ok_ct_meth.

    (** ** Method body conforms to method type *)

    Fact method_implies_typing: forall t m t0 E e,
        method t m (t0,E,e) ->
        exists2 t', sub t t' & wide_typing ((this,t')::E) e t0.
    Proof.
      intros. remember (t0, E, e) as mdecl.
      induction H; subst.
      Case "method_this". eauto via (ok_meth C D m t0 E e).
      Case "method_other". destruct IHmethod; [reflexivity | eauto 7].
    Qed.

    (** ** Subtyping preserves method types *)

    Fact sub_mtype: forall u t m t0 ts te,
        sub u t -> method t m (t0,ts,te) ->
        exists2 us, imgs ts = imgs us &
          (*EDIT2 BEGIN*)
          (*exists2 t0', sub t0' t0 &
            exists ue, method u m (t0',us,ue).*)
          exists ue, method u m (t0,us,ue).
          (*EDIT2 END*)
    Proof.
      intros u t m t0 ts te H. revert m t0 ts te.
      induction H; intros.
      Case "sub_refl". eauto.
      Case "sub_trans".
        (*EDIT2 BEGIN*)
        (*destruct IHsub2 with (1:=H1) as (us2, IH2a, (t02, IH2c, (ue2, IH2b))).
        destruct IHsub1 with (1:=IH2b) as (us1, IH1a, (t01, IH1c, (ue1, IH1b))).*)
        destruct IHsub2 with (1:=H1) as (us2, IH2a, (ue2, IH2b)).
        destruct IHsub1 with (1:=IH2b) as (us1, IH1a, (ue1, IH1b)).
        (*EDIT2 END*)
        exists us1; [ eauto using trans_eq | eauto ].
      Case "sub_extends".
        destruct H as (fs,(ms,H)).
        case_eq (get m ms); [ intros ((t1,us),ue) Hb | intro Hb ].
        SCase "binds m ms (t1,us,ue)".
          assert (Hok: ok_meth C D m t1 us ue) by eauto.
          destruct Hok as (Hoverride,_). destruct Hoverride with (1:=H0).
          (*EDIT2 BEGIN*)
          subst.
          (*EDIT2 END*)
          eauto.
        SCase "no_binds m ms". eauto.
    Qed.

    (** ** One more generalized typing rule *)

    Lemma gt_meth : forall E E0 e0 b t0 t m es,
        wide_typing E e0 t0 ->
        method t0 m (t, E0, b) ->
        wide_typings E es (imgs E0) ->
        wide_typing E (e_meth e0 m es) t.
    Proof.
      intros. destruct H.
      (*EDIT2 BEGIN*)
      (*destruct sub_mtype with (1:=H2) (2:=H0) as (us,Hu,(t0',Hs,(ue,Hm))).*)
      destruct sub_mtype with (1:=H2) (2:=H0) as (us,Hu,(ue,Hm)).
      (*EDIT2 END*)
      rewrite Hu in H1.
      eauto.
    Qed.

    Hint Resolve gt_meth.

End OkTableFacts.

