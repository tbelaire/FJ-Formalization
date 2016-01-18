
Require Export String.
Open Scope string_scope.

(* *********************************************************************** *)
(** * Delineating cases in proofs *)

(** This section was taken from the POPLmark Wiki
    ( http://alliance.seas.upenn.edu/~plclub/cgi-bin/poplmark/ ). *)

(** ** Tactic definitions *)

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name
  | fail 1 "because we are working on a different case." ].

Ltac Case name := Case_aux case name.
Ltac SCase name := Case_aux subcase name.
Ltac SSCase name := Case_aux subsubcase name.

(** * Do some automatic destructions *)

(* http://logical.saclay.inria.fr/cocorico/decompose%20records%20%28tactic%29 *)

Tactic Notation "decompose" "records" :=
repeat (match goal with
| H: _ |- _ => progress (decompose record H); clear H
end).

Tactic Notation "subst" "injections" :=
repeat (progress (match goal with
| H: _ = _ |- _ => injection H; clear H; intros; subst
end)).

Tactic Notation "destructs" hyp(H) := try red in H; decompose record H.

Tactic Notation "forward" hyp(H) "by" tactic(t) :=
    lapply H; [ clear H; intro H | t ].

Tactic Notation "forward" hyp(H) := forward H by idtac.

Tactic Notation "contradiction" "by" tactic(t) :=
  assert False; [ t | contradiction ].

Tactic Notation "auto" "via" constr(e) :=
    let H := fresh in (assert (H: e) by auto; try red in H; try decompose record H; auto).

Tactic Notation "eauto" "via" constr(e) :=
    let H := fresh in (assert (H: e) by eauto; try red in H; try decompose record H; eauto).

Tactic Notation "specialize" "trivial" :=
repeat match goal with
| H: ?H0 -> _ |- _ =>
  let HT := fresh in
  (assert (HT: H0) by trivial;
  specialize (H HT);
  clear HT)
end.

Tactic Notation "fold_simpl" constr(t) :=
    let et := (eval simpl in t) in change et with t.

