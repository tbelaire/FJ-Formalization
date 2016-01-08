
(***************************************************************************
 * Cast-Free Featherweight Java
 *
 * Bruno De Fraine, with help from Erik Ernst and Mario Sudholt, Summer 2008
 ***************************************************************************)

(** printing \in %\ensuremath{\in}% *)
(** printing \notin %\ensuremath{\notin}% *)
(** printing == %\ensuremath{\doteq}% *)

(** This library provides a number of auxiliary constructs (and their
    properties) for the study of programming languages in Coq. The definition
    of these constructs is mostly straightforward. *)

Require Import AdditionalTactics.
Require Export Atom.
Require Export List.

Set Implicit Arguments.

(** * Atoms *)

Notation "x == y" := (eq_atom_dec x y) (at level 67).

Fact eq_atom_true: forall (A : Type) a (c d : A),
    (if a == a then c else d) = c.
Proof.
  intros.
  destruct (a == a).
    reflexivity.
    destruct n. reflexivity.
Qed.

Fact eq_atom_false: forall (A : Type) a b (c d : A),
    a <> b -> (if a == b then c else d) = d.
Proof.
  intros.
  destruct (a == b); [ subst; destruct H | ]; reflexivity.
Qed.

Definition In_atom_list_dec := In_dec eq_atom_dec.

(** * Environments *)

(** An environment maps atoms to some value of an variable type [A]. We model
    an environment as a list of pairs: [list (atom * A)]. *)

Notation "x \in E" := (In x E) (at level 69).
Notation "x \notin E" := (~ In x E) (at level 69).

Section Environment.

    Variable A: Type.

    (** The function [get x E] retrieves the first binding of [x] in
        environment [E]. *)

    Fixpoint get (x: atom) (E: list (atom * A)) : option A :=
        match E with
        | nil => None
        | (y,v)::E => if x == y then Some v else get x E
        end.

    (** [binds x v E] holds when [x] is bound to [v] in [E].  [no_binds x E]
        holds when there is no binding for [x] in [E].  *)

    Definition binds x v E : Prop :=
        get x E = Some v.

    Definition no_binds x E : Prop :=
        get x E = None.

    Fact binds_first: forall x (a : A) E, binds x a ((x,a)::E).
    Proof.
      intros.
      unfold binds. simpl.
      apply eq_atom_true.
    Qed.

    Fact binds_other: forall x y (a b : A) E,
        binds y b E -> x <> y -> binds y b ((x,a)::E).
    Proof.
      intros.
      unfold binds in *. simpl.
      rewrite eq_atom_false with (1:=sym_not_eq H0).
      assumption.
    Qed.

    Fact binds_nil: forall x (a : A), ~binds x a nil.
    Proof.
      unfold binds. simpl. intros. discriminate.
    Qed.

    Fact binds_fun: forall E x (a b : A),
        binds x a E -> binds x b E -> a = b.
    Proof.
      unfold binds. intros E x a b H H'.
      rewrite H' in H. injection H.
      auto.
    Qed.

    Fact binds_elim_eq: forall x (a b : A) E,
        binds x a ((x,b)::E) -> a = b.
    Proof.
      intros x a b E.
      unfold binds. simpl.
      rewrite eq_atom_true.
      injection 1. auto.
    Qed.

    Fact binds_elim_neq: forall x y (a b : A) E,
        x <> y -> binds x a ((y,b)::E) -> binds x a E.
    Proof.
      intros x y a b E H.
      unfold binds. simpl.
      rewrite eq_atom_false; trivial.
    Qed.

    Fact binds_head : forall x a E F,
        binds x a F -> binds x a (F ++ E).
    Proof.
      intros x a E F.
      unfold binds.
      induction F as [|(y,b)]; simpl; intros H.
      Case "nil". discriminate.
      Case "cons". destruct (x == y); auto.
    Qed.

    Fact binds_nobinds : forall x a E,
        binds x a E -> no_binds x E -> False.
    Proof.
      unfold binds. unfold no_binds. intros.
      rewrite H in H0. discriminate.
    Qed.

    Fact nobinds_nil: forall x, no_binds x nil.
    Proof.
      intros.
      unfold no_binds. reflexivity.
    Qed.

    Fact nobinds_cons: forall x y b E,
        no_binds x E ->
        x <> y ->
        no_binds x ((y,b)::E).
    Proof.
      unfold no_binds. intros.
      simpl.
      rewrite eq_atom_false with (1:=H0).
      assumption.
    Qed.

    Fact nobinds_app: forall x E1 E2,
       no_binds x E1 ->
       no_binds x E2 ->
       no_binds x (E1++E2).
    Proof.
      unfold no_binds. intros.
      induction E1 as [|(y,v)]; simpl.
      Case "nil". assumption.
      Case "cons". destruct (x==y).
        SCase "x=y".
          subst. rewrite binds_first in H. discriminate H.
        SCase "x<>y".
          simpl in H. rewrite eq_atom_false with (1:=n) in H.
          auto.
    Qed.

    (** The functions [keys E] and [dom E] retrieve the atoms that are bound in
        the environment [E]. *)

    Definition keys (E: list (atom * A)) : list atom :=
        List.map (fun p => match p with (x,_) => x end) E.
    
    Definition dom := keys.

    Fact dom_binds: forall (E : list (atom * A)) (x : atom),
        x \in dom E -> exists v:A, binds x v E.
    Proof.
      intros.
      induction E as [| (u, v) E]; simpl in H.
      Case "nil". contradiction.
      Case "cons".
        unfold binds in *. simpl in *.
        destruct (x == u); [ eauto | apply IHE ].
        destruct H; [ symmetry in H; contradiction | apply H ].
    Qed.

    Fact binds_In : forall a x E,
        binds x a E -> x \in dom E.
    Proof.
      intros.
      induction E as [| (u, v) E].
      Case "nil". contradiction (binds_nil H).
      Case "cons".
        unfold binds in *. simpl in *.
        destruct (x == u); auto.
    Qed.

    Fact dom_binds_neg: forall (E : list (atom * A)) (x : atom),
        x \notin dom E -> get x E = None.
    Proof.
      intros.
      induction E as [| (u, v) E].
      Case "nil". reflexivity.
      Case "cons".
        simpl in *.
        destruct (x == u); [ contradiction H | apply IHE ]; auto.
    Qed.

    (** The function [imgs E] retrieves the values in [E]. [map f E] applies
        [f] to the values in [E]. *)

    Definition imgs (E: list (atom * A)) : list A :=
        List.map (fun p => match p with (_,v) => v end) E.

    Definition map (B: Type) (f: A -> B) (E: list (atom * A)) : list (atom * B) :=
        List.map (fun p => match p with (x,v) => (x, f v) end) E.

    (** [ok E] holds when the environment [E] contains no duplicate bindings. *)

    Inductive ok: list (atom * A) -> Prop :=
    | ok_nil: ok nil
    | ok_cons: forall E x v, ok E -> no_binds x E -> ok ((x,v)::E).

    Fact binds_concat_ok : forall x a E F,
      binds x a E -> ok (F ++ E) -> binds x a (F ++ E).
    Proof.
      intros x a E F.
      induction F as [|(y,b)]; simpl; intros H Ok.
      Case "nil". assumption.
      Case "cons".
        inversion Ok. subst.
        destruct (y == x).
        SCase "x=y".
          subst.
          contradiction binds_nobinds with (a:=a) (2:=H4).
          eauto.
        SCase "x<>y".
          apply binds_other; [ auto | assumption ].
    Qed.

    Fact binds_weaken : forall x a E F G,
      binds x a (G ++ E) ->
      ok (G ++ F ++ E) ->
      binds x a (G ++ F ++ E).
    Proof.
      induction G as [|(y,b)]; simpl; intros H Ok.
      Case "nil". apply binds_concat_ok; assumption.
      Case "cons".
        inversion Ok. subst.
        destruct (y == x).
        SCase "x=y".
          subst.
          rewrite binds_elim_eq with (1:=H).
          apply binds_first.
        SCase "x<>y".
          apply binds_other with (2:=n).
          apply IHG; [ eauto using binds_elim_neq | assumption ].
    Qed.

   (** [forall_env P E] holds when proposition [P x v] holds for all bindings
       [(x, v)] in environment [E]. *)

    Variable P: atom -> A -> Prop.

    Inductive forall_env : list (atom * A) -> Prop :=
    | fa_nil: forall_env nil
    | fa_cons: forall E x v, forall_env E -> P x v -> forall_env ((x,v)::E).

    Hint Constructors forall_env.

    Fact fa_single: forall x a, P x a -> forall_env ((x,a)::nil).
    Proof.
      auto.
    Qed.

    Fact fa_app: forall E F,
        forall_env E -> forall_env F -> forall_env (E++F).
    Proof.
      intros; induction H; simpl; auto.
    Qed.

    Fact fa_weaken: forall E F G,
        forall_env (E++F++G) -> forall_env (E++G).
    Proof.
      intros; induction E as [| (y,a)]; simpl.
      Case "nil".
        induction F as [| (y,a)].
        SCase "nil". trivial.
        SCase "cons". apply IHF. inversion H. subst. assumption.
      Case "cons". inversion H. subst. auto.
    Qed.

    Fact fa_binds_elim: forall x a E,
        binds x a E -> forall_env E -> P x a.
    Proof.
      intros; induction H0.
      Case "fa_nil". contradiction (binds_nil H).
      Case "fa_cons". destruct (x == x0).
        SCase "x = x0". subst. rewrite (binds_elim_eq H). assumption.
        SCase "x <> x0". eauto using binds_elim_neq.
    Qed.

End Environment.

Unset Implicit Arguments.
Hint Constructors ok.
Hint Constructors forall_env.
Implicit Arguments fa_nil [A].

Set Implicit Arguments.

(** [env_zip aenv bs benv] will match up environment [aenv] with the value list
    [bs] to produce the environment [benv]. *)

Inductive env_zip (A: Type) (B: Type) : list (atom * A) -> list B -> list (atom * B) -> Prop :=
| z_nil : env_zip nil nil nil
| z_cons : forall x a b aenv bs benv,
    env_zip aenv bs benv ->
    env_zip ((x,a)::aenv) (b::bs) ((x,b)::benv).

Hint Constructors env_zip.

Unset Implicit Arguments.

