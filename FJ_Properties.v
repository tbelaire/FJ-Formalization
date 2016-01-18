
(***************************************************************************
 * Cast-Free Featherweight Java
 *
 * Bruno De Fraine, with help from Erik Ernst and Mario Sudholt, Summer 2008
 ***************************************************************************)

Require Import AdditionalTactics.
Require Import Metatheory.
Require Import FJ_Definitions.
Require Import FJ_Facts.

(** * The weakening lemma (optional) *)

Lemma weakening':
    (forall EE e t, typing EE e t ->
      forall E F G, EE=F++G -> ok (F++E++G) -> typing (F++E++G) e t) /\
    (forall EE e t, wide_typing EE e t ->
      forall E F G, EE=F++G -> ok (F++E++G) -> wide_typing (F++E++G) e t) /\
    (forall EE es env, wide_typings EE es env ->
      forall E F G, EE=F++G -> ok (F++E++G) -> wide_typings (F++E++G) es env).
Proof.
  (* Prove property at once for typing, wide_typing and wide_typings using
     mutual inducion. *)
  apply typings_mutind; intros; subst; eauto using binds_weaken.
Qed.

Lemma weakening: forall E F G e t,
    ok (F++E++G) ->
    typing (F++G) e t ->
    typing (F++E++G) e t.
Proof.
  intros.
  destruct weakening' as (Hweak, _).
  eapply Hweak; trivial; assumption.
Qed.

(** * Requirements for preservation *)

(** ** Preservation over [exps_context] and [exp_context] *)

Fact preservation_over_esc: forall EE E ts e e',
    exps_context EE ->
    (forall t, typing E e t -> wide_typing E e' t) ->
    wide_typings E (EE e) ts ->
    wide_typings E (EE e') ts.
Proof.
  intros. generalize dependent ts.
  induction H; intros; inversion H1; subst.
  Case "esc_head". destruct H6. eauto.
  Case "esc_tail". eauto.
Qed.

Module Properties (H: Hyps).

    (** Import previous conclusions for either of the hypotheses *)

    Module Import Facts1 := NoObjFacts H.
    Module Import Facts2 := OkTableFacts H.

    Fact preservation_over_ec: forall EE E e e' t,
        exp_context EE ->
        (forall t0, typing E e t0 -> wide_typing E e' t0) ->
        typing E (EE e) t ->
        wide_typing E (EE e') t.
    Proof.
      intros.
      destruct H; inversion H1; subst; eauto using preservation_over_esc.
    Qed.

    (** ** Term substitutivity lemma *)

    Lemma term_substitutivity': forall E E0 ds Eds,
        wide_typings E0 ds (imgs E) ->
        env_zip E ds Eds ->
        (forall EE e t, typing EE e t ->
           EE = E -> wide_typing E0 (subst_exp Eds e) t) /\
        (forall EE e t, wide_typing EE e t ->
           EE = E -> wide_typing E0 (subst_exp Eds e) t) /\
        (forall EE es ts, wide_typings EE es ts ->
           EE = E -> wide_typings E0 (List.map (subst_exp Eds) es) ts).
    Proof.
      (* Prove property at once for typing, wide_typing and wide_typings using
         mutual inducion. *)
      intros E E0 ds Eds Hb Hz.
      apply typings_mutind; intros; subst; simpl; eauto.
      Case "t_var".
        destruct binds_zip with (1:=Hb) (2:=Hz) (3:=H0) as (e, H1a, H1b).
        rewrite H1a. exact H1b.
    Qed.

    Lemma term_substitutivity: forall E E0 e t ds Eds,
        wide_typing E e t ->
        wide_typings E0 ds (imgs E) ->
        env_zip E ds Eds ->
        wide_typing E0 (subst_exp Eds e) t.
    Proof.
      intros.
      destruct term_substitutivity' with (1:=H0) (2:=H1) as (_, (Hsub, _)).
      eapply Hsub; trivial; assumption.
    Qed.

    (** * Preservation property *)

    Theorem preservation: forall E e e' t,
        typing E e t ->
        eval e e' ->
        wide_typing E e' t.
    Proof.
      intros. generalize dependent t.
      induction H0; intros.
      Case "eval_field".
        inversion H2. inversion H6. subst.
        destruct H8 as (fs1, H8a, H8b).
        assert (fs0 = fs1) by (eapply fields_fun; eassumption). subst.
        assert (fs1 = fs) by (eapply fields_fun; eassumption). subst.
        destruct binds_zip with (1:=H14) (2:=H0) (3:=H8b) as (e0, Hb1, Hb2).
        assert (e0 = e) by (eapply binds_fun; eassumption). subst.
        exact Hb2.
      Case "eval_meth".
        inversion H1. inversion H6. subst.
        assert ((t, E0, e) = (t0, E2, b)) by (eapply method_fun; eauto).
        subst injections.
        destruct method_implies_typing with (1:=H8) as (t',H8a,H8b).
        eapply term_substitutivity; (try simpl; eauto).
      Case "eval_context".
        eapply preservation_over_ec; eassumption.
    Qed.

    (** * Progress property *)

    Theorem progress':
        (forall E e t, typing E e t ->
           E = nil -> value e \/ exists e', eval e e') /\
        (forall E e t, wide_typing E e t ->
           E = nil -> value e \/ exists e', eval e e') /\
        (forall E ds env, wide_typings E ds env ->
           E = nil -> (forall v, In v ds -> value v) \/
             exists2 EE, exps_context EE &
               (exists2 e0, (EE e0) = ds & (exists e0', eval e0 e0'))).
    Proof.
      (* Prove property at once for typing, wide_typing and wide_typings using
         mutual inducion. *)
      apply typings_mutind; intros; subst E; specialize trivial.
      Case "t_var". contradiction (binds_nil H0).
      Case "t_field".
        destruct H0 as [H0 | (e',H0)]; [ | right; eauto ].
        destruct H0. inversion H. subst.
        destruct wide_typings_implies_zip with (1:=H7) as (Eds, Hzip).
        destruct H1 as (fs0, H1a, H1b).
        assert (fs0 = fs) by (eapply fields_fun; eassumption). subst.
        destruct binds_zip with (1:=H7) (2:=Hzip) (3:=H1b).
        eauto.
      Case "t_meth".
        destruct H0 as [H0 | (es',H0)]; [ | right; eauto ].
        destruct H0. inversion H. subst.
        destruct wide_typings_implies_zip with (1:=H2) as (Eds,Hzip).
        eauto.
      Case "t_new".
        destruct H1 as [H1 | (EE,H1a,(e0,H1b,(e0',H1c)))]; [ auto | ].
        subst es. eauto.
      Case "wt_sub". auto.
      Case "wts_nil". left. intros. contradiction H0.
      Case "wts_cons".
        destruct H0 as [H0 | (EE,H0a,(e0,H0b,H0c))].
        SCase "values es".
          destruct H2 as [H2 | (e',H2)].
          SSCase "value e".
            left. intros.
            destruct in_inv with (1:=H3); [ subst | ]; auto.
          SSCase "e progress".
            right. exists (fun e1 => e1::es); eauto.
        SCase "es progress".
          subst es. right. exists (fun e1 => e::(EE e1)); eauto.
    Qed.

    Theorem progress: forall e t,
        typing nil e t ->
        value e \/ (exists e', eval e e').
    Proof.
      intros.
      destruct (progress') as (Hpro,_).
      apply Hpro with (1:=H). reflexivity.
    Qed.

End Properties.

(** * Epilogue *)

(** Check that these properties indeed prove safety *)

Module SafetyProof : Safety := Properties.

