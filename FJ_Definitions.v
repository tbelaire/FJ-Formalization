
(***************************************************************************
 * Cast-Free Featherweight Java
 *
 * Bruno De Fraine, with help from Erik Ernst and Mario Sudholt, Summer 2008
 ***************************************************************************)

(** printing \in %\ensuremath{\in}% *)
(** printing \notin %\ensuremath{\notin}% *)
(** printing == %\ensuremath{\doteq}% *)

(** This library contains the actual Featherweight Java language definition.
    The definition is divided up between syntax, auxiliaries, evaluation and
    typing. *)

Require Import Metatheory.
Require Import CpdtTactics.

(** * Syntax *)

(** ** Lexical categories *)

(** Names of variables, fields, methods and classes are atoms (their equality
    is decidable). *)

Definition var := atom.
Definition fname := atom.
Definition mname := atom.
Definition cname := atom.

(** The names [this] and [Object] are predefined. We simply assume that these
    names exist. *)

Parameter this : var.
Parameter Object : cname.

(** ** Type and term expressions *)

(** Class names are the only form of types. **)

Definition typ := cname.

(** The expression forms are variable reference, field get, method invocation
    and object creation. *)

(* (Expr) but missing cast.  The rest of (C-Decl), (K-Decl), (M-Decl) syntax are
   not included.
   We do have a class table CT, constructed without syntax ahead of time. *)


Inductive exp_ : bool -> Set :=
| e_var {b} : var -> exp_ b
| e_field {b} : exp_ b -> fname -> exp_ b
| e_meth {b} : exp_ b -> mname -> list (exp_ b) -> exp_ b
| e_new {b} : cname -> list (exp_ b) -> exp_ b
| e_cast {b} : cname -> exp_ b -> exp_ b
| e_lib : exp_ true.

(** ** Environments and class tables *)

(** An [env] declares a number of variables and their types. A [benv] binds
    variables to expressions. *)
Definition exp_a := exp_ false.
Definition exp_l := exp_ true.

Fixpoint embed_exp {b} (e : exp_ b) : exp_l :=
    match e with
    | @e_var _ v => e_var v
    | @e_field _ o f => e_field (embed_exp o) f
    | @e_meth _ o m args =>
            e_meth (embed_exp o) m (List.map embed_exp args)
    | @e_new _ C args => e_new C (List.map embed_exp args)
    | @e_cast _ C e => e_cast C (embed_exp e)
    | e_lib => e_lib
    end.

Module Type GenericOverExprSig.
Parameter exp : Set.
End GenericOverExprSig.

Module ExprWithoutLib <: GenericOverExprSig.
Definition exp := exp_a.
End ExprWithoutLib.

Module ExprWithLib <: GenericOverExprSig.
Definition exp := exp_l.
End ExprWithLib.

(* Definition exp := exp_ with_lib. *)
Module Export GenericOverExpr (ModuleThatDefinesExp: GenericOverExprSig).
Import ModuleThatDefinesExp.
Open Scope list_scope.


Definition env := (list (var * typ)).
Definition benv := (list (var * exp)).

(** [flds] and [mths] map the names of fields and methods to their
    definitions. *)

Definition flds := (list (fname * typ)).
Definition mths := (list (mname * (typ * env * exp))).

(** [ctable] maps the names of classes to their definitions. A class definition
    consists of a parent class and a number of fields and methods. *)

Definition ctable := (list (cname * (cname * flds * mths))).

(** The way this is going to work is we have everything generic over CT,
 *  but with a _ suffix, and the a wrapper definition that uses CT without the suffix.
 *  When this section ends, we'll add a global parameter for a fixed CT,
 *  and define all the wrappers.
 *)




(** * Typing *)

(** ** Well-formed types *)

(** [ok_type_ t] holds when [t] is a well-formed type. *)

Inductive ok_type_ (CT:ctable) : typ -> Prop :=
| ok_obj: @ok_type_ CT Object
| ok_in_ct: forall C, C \in dom CT -> @ok_type_ CT C.

Hint Constructors ok_type_.

(** [directed_ct CT] holds when the ctable only has references to already
  * existing classes for inheritance *)

Inductive directed_ct : ctable -> Prop :=
| directed_ct_nil : directed_ct nil
| directed_ct_cons :
        forall (C D : cname) (fs : flds) (ms: mths) (ct : ctable),
        directed_ct ct ->
        C \notin (keys ct) -> (* No duplicate bindings *)
        ok_type_ ct D ->    (* No forward references *)
        directed_ct ((C, (D, fs, ms)) :: ct).

Hint Constructors directed_ct.

(** [extends C D] holds if [C] is a direct subclass of [D]. *)

Definition extends_ (CT:ctable) (C D : cname) : Prop :=
    exists fs, exists ms, binds C (D,fs,ms) CT.
Hint Unfold extends_.

(** [sub s u] holds if [s] is a subtype of [u]. The subtype relation is the
    reflexive, transitive closure of the direct subclass relation. *)

(* (S-Ref) (S-Trans) (S-Sub) are defined here. *)

Inductive sub_ (CT:ctable) : typ -> typ -> Prop :=
| sub_refl : forall t, ok_type_ CT t -> sub_ CT t t
| sub_trans : forall t1 t2 t3,
        sub_ CT t1 t2 -> sub_ CT t2 t3 -> sub_ CT t1 t3
| sub_extends : forall C D, @extends_ CT C D -> sub_ CT C D.


(* Strict subset *)
(* This is phrased as being indexed on CT instead of parameterized
due to an problem arising when we want to prove things about some C subset of D,
in ((C, (D, fs, ms)) :: CT).

Previously it was paramaterized:

    Inductive ssub_ (CT: ctable): typ -> typ -> Prop :=
    | ssub_trans : forall t1 t2 t3,
            ssub_ CT t1 t2 ->
            ssub_ CT t2 t3 ->
            ssub_ CT t1 t3
    | ssub_extends : forall t1 t2, @extends_ CT t1 t2 -> ssub_ CT t1 t2.

Which gave rise to this induction scheme:

    Theorem ssub__ind_parametric :
    forall (CT : ctable) (P : typ -> typ -> Prop),
    (forall t1 t2 t3 : typ,
        ssub_ CT t1 t2 -> P t1 t2 ->
        ssub_ CT t2 t3 -> P t2 t3 ->
        P t1 t3) ->
    (forall t1 t2 : cname, extends_ CT t1 t2 -> P t1 t2) ->
    forall C D : typ, ssub_ CT C D -> P C D.

Key part: forall C D, ssub_ CT C D -> P C D.
trying to write

    forall C D, ssub_ ((C, (D, fs, ms)) :: CT) C D -> P C D

is impossible, as the bindings for C and D will be fresh, and you'd get

    forall C' D', ssub_ ((C, (D, fs, ms)) :: CT) C' D' -> P C' D'

which obviously is less helpful.

However, most proofs do not rely on this generality, and in fact,
it's not helpful, as you need to do the convoy pattern or inversions
more frequently when using the new induction scheme.

Helpfully, we can still do induction using the old scheme.
`no_ssub_with_empty_table` is a very good example of this.


*)
Inductive ssub_p (CT:ctable) : typ -> typ -> Prop :=
| ssub_p_trans : forall t1 t2 t3,
        ssub_p CT t1 t2 -> ssub_p CT t2 t3 -> ssub_p CT t1 t3
| ssub_p_extends : forall C D, extends_ CT C D -> ssub_p CT C D.

Inductive ssub_ : ctable -> typ -> typ -> Prop :=
| ssub_trans : forall CT t1 t2 t3,
        ssub_ CT t1 t2 ->
        ssub_ CT t2 t3 ->
        ssub_ CT t1 t3
| ssub_extends : forall CT t1 t2, @extends_ CT t1 t2 -> ssub_ CT t1 t2.

Hint Constructors sub_ ssub_.


Ltac unfold_extends H := destruct H as [?fs [?ms ?H_binds]].
Hint Extern 1 => match goal with
    [ H: extends_ _ _ _ |- _] => unfold_extends H
end.
Ltac solve_binds_nil :=
    match goal with
    | [H: (binds ?C ?x ?nil) |- _] => exfalso; apply binds_nil2 in H; assumption
    end.
Hint Extern 1 False => solve_binds_nil.

(* This gives reasonable names to things. *)
Ltac unfold_directed H_directed:=
    inversion H_directed
    as [ | ?C ?D ?fs ?ms ?CT ?H_dir ?H_notin ?H_ok ]; subst.
(* This will cause it to run unconditionally on all autos... *)
(* Hint Extern 3 => unfold_directed. *)

Ltac unfold_ok_type H_ok_type:=
    inversion H_ok_type.



(* Always break down directed_ct (x :: xs) into some information about x
* and directed_ct xs.
*)
Hint Extern 1 (directed_ct ?x) =>
    match goal with
    | [ H: directed_ct (?x :: ?xs) |- _ ] => inversion H; subst
    end.

Lemma weaken_no_obj : forall CT (A B : cname) (fs : flds) (ms : mths),
    Object \notin dom ((A, (B, fs, ms)) :: CT) ->
    Object \notin dom CT.
Proof.
    crush.
Qed.
Hint Resolve weaken_no_obj.

Lemma weaken_ok_type CT C A B fs ms
    (H_neq : A <> C)
    (H_ok : @ok_type_ ((A, (B, fs, ms)) :: CT) C)
    :
    @ok_type_ CT C.
Proof.
    intros.
    destruct H_ok as [|C]; crush.
Qed.  Hint Resolve weaken_ok_type.

Lemma strengthen_ok_type CT C A B fs ms
    (H_ok: ok_type_ CT C)
    : ok_type_ ((A, (B, fs, ms)):: CT) C.
Proof.
    destruct H_ok; constructor; crush.
Qed. Hint Resolve strengthen_ok_type.

Lemma ok_type_nil : forall C,
    ok_type_ nil C ->
    C = Object.
Proof.
    intros.
    inversion H.
    - reflexivity.
    - exfalso.
    crush.
Defined.

Lemma weaken_directed_ct : forall x v ct,
    directed_ct ((x, v) :: ct) ->
    directed_ct ct.
Proof.
    intros.
    auto.
Qed.

Hint Resolve weaken_directed_ct.

Lemma directed_binds_unique : forall CT C D fs ms,
    Object \notin dom CT ->
    directed_ct CT ->
    binds C (D, fs, ms) CT ->
    C <> D.
Proof.
    intros CT0 C D fs ms H_object H_dir H_binds.
    unfold not.
    intros.
    subst.
    induction H_dir.
    apply binds_nil in H_binds; assumption.
    destruct (C == D).
    - subst.
    destruct H0.
    + apply binds_elim_eq in H_binds.
    inversion H_binds.
    subst.
    unfold not in H_object.
    apply H_object.
    unfold In.
    simpl.
    auto.
    +
    apply binds_elim_eq in H_binds.
    inversion H_binds.
    subst.
    contradiction.
    - (* Induction C <> D *)
    apply IHH_dir.
    crush.
    eapply binds_elim_neq with (y:= C).
    auto.
    exact H_binds.
Qed.

Hint Resolve directed_binds_unique.

Lemma directed_binds : forall C D fs ms CT,
    directed_ct CT ->
    binds C (D, fs, ms) CT ->
    ok_type_ CT D.
Proof.
    intros.
    induction H.
    apply binds_nil in H0.
    auto.

    destruct (C0 == C).
    - (* == *)
    subst.
    apply binds_elim_eq in H0.
    assert (D0 = D).
        inversion H0.
        reflexivity.
    subst.
    destruct H2.
    + apply ok_obj.
    + apply ok_in_ct.
    apply in_cons.
    auto.
    - (* <> *)
    apply strengthen_ok_type.
    apply IHdirected_ct.
    eapply binds_elim_neq with (y:=C0).
    auto.
    exact H0.
Qed.

Hint Resolve directed_binds.

(** ** Subtyping *)




Lemma ssub__ind_parametric : 
  forall (CT : ctable) (P : typ -> typ -> Prop),
 (forall t1 t2 t3 : typ,
ssub_ CT t1 t2 -> P t1 t2 -> ssub_ CT t2 t3 -> P t2 t3 -> P t1 t3) ->
 (forall t1 t2 : cname, extends_ CT t1 t2 -> P t1 t2) ->
forall C D : typ, ssub_ CT C D -> P C D.
Proof.
    intros CT P P_trans P_extends.
    intros C D H_sub.
    induction H_sub.
    -
    apply P_trans with (t2:=t2).
    auto.
    apply IHH_sub1.
    intros t4 t5 t6 H_sub45 P45 H_sub56 P56.
    apply P_trans with (t2:=t5); auto.
    exact P_extends.
    auto.

    apply IHH_sub2.
    intros t4 t5 t6 H_sub45 P45 H_sub56 P56.
    apply P_trans with (t2:=t5); auto.
    exact P_extends.
    -
    apply P_extends.
    unfold_extends H.
    unfold extends_.
    exists fs, ms.
    exact H_binds.
Qed.

(* Here's the current one for comparison
ssub__ind
     : forall P : ctable -> typ -> typ -> Prop,
       (forall (CT : ctable) (t1 t2 t3 : typ),
        ssub_ CT t1 t2 ->
        P CT t1 t2 -> ssub_ CT t2 t3 -> P CT t2 t3 -> P CT t1 t3) ->
       (forall (CT : ctable) (t1 t2 : cname), extends_ CT t1 t2 -> P CT t1 t2) ->
       forall (c : ctable) (t t0 : typ), ssub_ c t t0 -> P c t t0
       *)

Lemma ssub_to_sub (CT: ctable): forall A B,
    ssub_ CT A B ->
    sub_ CT A B.
Proof.
    intros.
    induction H.
    apply sub_trans with (t2:=t2); auto.
    apply sub_extends; auto.
Qed.

Lemma sub_to_ssub_or_eq CT A B
    (H_sub: sub_ CT A B):
    ssub_ CT A B \/ A = B.
Proof.
    induction H_sub.
    - right. reflexivity.
    - destruct IHH_sub1.
    destruct IHH_sub2.
    + left. apply ssub_trans with (t2 := t2); auto.
    + subst. auto.
    + subst. auto.
    - left. apply ssub_extends. assumption.
Qed.


    (*
    induction H_sub.
    -
    intros.
    apply sub_refl.
    -
    intros.
    apply sub_trans with (t2 := t2).
    crush.
    destruct (A == t2).
    + subst.
    exfalso.

    crush.
Abort. *)

Lemma no_self_inheritance : forall CT : ctable,
    directed_ct CT ->
    Object \notin dom CT ->
    forall C : cname,
    ~ exists fs ms, binds C (C,fs,ms) CT.
Proof.
    intros CT H ct_noobj C.
    unfold not.
    intros.
    destruct H0 as [fs].
    destruct H0 as [ms].
    induction H.
    - (* ct_directed_nil.*)
    unfold binds in H0.
    absurd (None = Some (C, fs, ms)); discriminate.


    - (* ct_directed_cons *)
    destruct (C == C0) as [H3 | Hneq].

    + (* C == C0 *)
    symmetry in H3; subst.
    unfold binds in H0.
    simpl in H0.
    rewrite eq_atom_true in H0.
    inversion H0.
    subst.
    destruct H2.
    * (* D = Object. *)
    subst.
    rewrite dom_distribute_cons in ct_noobj.
    apply not_in_split in ct_noobj.
    subst.
    absurd (Object = Object); auto.
    apply ct_noobj.
    * (* D \in key ct. *)
    crush.
    + (* C <> C0 *)
    inversion H0.
    rewrite dom_distribute_cons in ct_noobj.
    apply not_in_split in ct_noobj.
    apply IHdirected_ct.  apply ct_noobj.
    assert ((if C == C0 then
             Some (D, fs0, ms0)
             else Metatheory.get C ct) = Metatheory.get C ct).
    exact (eq_atom_false _ _ Hneq).
    rewrite H3 in H4.
    apply H4.
Qed.

Lemma distinct_parent : forall CT C D fs ms,
    directed_ct CT ->
    Object \notin dom CT ->
    binds C (D,fs,ms) CT ->
    C <> D.
Proof.
    intros CT C D fs ms H_directed H_noobj H_binds.
    unfold not.
    intros H_eq.
    subst.
    absurd ( (exists (fs : flds) (ms : mths), binds D (D, fs, ms) CT)).
    + refine (no_self_inheritance CT H_directed H_noobj _ ).
    + exists fs; exists ms. auto.
Qed.

Hint Resolve distinct_parent.


Lemma directed_is_ok : forall ct,
    directed_ct ct -> ok ct.
Proof.
    intros.
    induction H.
    auto.
    pose (dom_binds_neg ct C H0) as H3.
    apply ok_cons.
    assumption.
    unfold no_binds.
    assumption.
Qed.

Hint Resolve directed_is_ok.


(* Rest of the Lineage facts *)

Lemma directed_ok : forall CT C D fs ms,
    directed_ct CT ->
    binds C (D, fs, ms) CT ->
    @ok_type_ CT D.
Proof.
    intros.
    induction CT.
    - (* nil *)
    unfold binds in H0.
    unfold get in H0.
    discriminate.
    - (* cons *)
    destruct a as [E [[F fs'] ms']].
    destruct (E == C) as [| H_neq].
    + (* = *)
    subst.
    inversion H.
    subst.
    assert (D = F).
        unfold binds in H0.
        unfold get in H0.
        rewrite eq_atom_true in H0.
        inversion H0.
        reflexivity.
    symmetry in H1.
    subst.
    destruct H8.
    * (* Object *)
    subst.
    apply ok_obj.
    * (* D \in keys *)
    apply ok_in_ct.
    unfold dom.
    apply in_cons.
    assumption.

    + (* <> *)
    apply strengthen_ok_type.
    apply IHCT.
    * (* directed_ct CT *)
    exact (weaken_directed_ct _ _ _ H).
    * (* binds C (D, fs, ms) CT *)
    eapply binds_elim_neq with (y:= E).
    auto.
    exact H0.
Qed.

Hint Resolve directed_ok.

Lemma directed_sub_ok : forall CT C D,
    directed_ct CT ->
    ok_type_ CT C ->
    @sub_ CT C D ->
    ok_type_ CT D.
Proof.
    intros CT C D H_dir H_ok H_sub.
    induction H_sub.
    - crush.
    - crush.
    - eauto. (* unfold_extends.
    eauto. *)
Qed.

(* End simple facts about our predicates. *)

(** * The grand induction theorem *)
Lemma ClassTable_rect_base_case
(    P : cname -> Type)
(H_directed_ct : directed_ct nil)
(H_noobj : Object \notin @dom cname nil)
(H_Obj : P Object)
(H_Ind : forall (C D : cname) (fs : flds) (ms : mths),
        ok_type_ nil D -> binds C (D, fs, ms) nil -> P D -> P C)
:
forall C : cname, ok_type_ nil C -> P C.
Proof.
    intros C H_ok.
    assert (C = Object) by apply (ok_type_nil C H_ok).
    rewrite H.
    exact H_Obj.
Defined.

Lemma ok_head_parent
(E : cname)
(C : cname)
(fs : flds)
(ms : mths)
(CT' : list (cname * (cname * flds * mths)))
(H_dir : directed_ct ((C, (E, fs, ms)) :: CT'))
(H_noobj : Object \notin dom ((C, (E, fs, ms)) :: CT'))
(H_ok : ok_type_ ((C, (E, fs, ms)) :: CT') C)
:
ok_type_ ((C, (E, fs, ms)) :: CT') E.
Proof.
    unfold_directed H_dir.
    destruct H_ok0.
    - (* is object *)
    subst.
    apply ok_obj.
    - (* in keys *)
    apply ok_in_ct.
    unfold dom.
    unfold keys.
    simpl.
    crush.
Defined.

Lemma ClassTable_rect_reduce_H_Ind
(P : cname -> Type)
(C : cname)
(E : cname)
(fs : flds)
(ms : mths)
(CT' : list (cname * (cname * flds * mths)))
(H_directed_ct : directed_ct ((C, (E, fs, ms)) :: CT'))
(H_Ind : forall (C0 D0 : cname) (fs0 : flds) (ms0 : mths),
        ok_type_ ((C, (E, fs, ms)) :: CT') D0 ->
        binds C0 (D0, fs0, ms0) ((C, (E, fs, ms)) :: CT') -> P D0 -> P C0)
:
forall (C0 D0 : cname) (fs0 : flds) (ms0 : mths),
ok_type_ CT' D0 -> binds C0 (D0, fs0, ms0) CT' -> P D0 -> P C0.
Proof.
        intros C0 D0 fs' ms' H_ok' H_binds H_D0.
        assert (H_ok_D0: ok_type_ ((C, (E, fs, ms)) :: CT') D0) by  auto.
        refine (H_Ind C0 D0 fs' ms' H_ok_D0 _ H_D0).
        (* binds C0 (D0, fs', ms') _ *)
        destruct (C0 == C).
        + (* eq *)
        subst.
        (* Contradiction , we've bound D twice, with D0 and E *)
        exfalso.
        inversion H_directed_ct.
        subst.
        apply binds_In in H_binds.
        contradiction.
        + (* neq *)
        refine (binds_other _ _ _); auto.
Defined.

Lemma ClassTable_rect_inductive_step
(P : cname -> Type)
(D : cname)
(E : cname)
(fs : flds)
(ms : mths)
(CT' : list (cname * (cname * flds * mths)))
(H_directed_ct : directed_ct ((D, (E, fs, ms)) :: CT'))
(H_noobj : Object \notin dom ((D, (E, fs, ms)) :: CT'))
(H_Obj : P Object)
(H_Ind : forall (C D0 : cname) (fs0 : flds) (ms0 : mths),
        ok_type_ ((D, (E, fs, ms)) :: CT') D0 ->
        binds C (D0, fs0, ms0) ((D, (E, fs, ms)) :: CT') -> P D0 -> P C)
(IHCT' : directed_ct CT' ->
        Object \notin dom CT' ->
        (forall (C D0 : cname) (fs0 : flds) (ms0 : mths),
         ok_type_ CT' D0 -> binds C (D0, fs0, ms0) CT' -> P D0 -> P C) ->
        forall C : cname, ok_type_ CT' C -> P C)
    : forall C : cname, ok_type_ ((D, (E, fs, ms)) :: CT') C -> P C.
Proof.
    intros C H_ok.
    destruct (D == C).
    + (* eq Going to use H_Ind *)
    subst.
    (* Plan: use H_Ind to solve,
        as we can show P E by IHCT *)

    assert (H_ok_E : ok_type_ ((C, (E, fs, ms)) :: CT') E) by
    exact (ok_head_parent _ _ _ _ _ H_directed_ct H_noobj H_ok).
    refine (H_Ind C E fs ms H_ok_E (binds_first C _ _ ) _).
    * (* Show (P E) by IHCT' *) {
        eapply IHCT'.
        - exact (weaken_directed_ct _ _ _ H_directed_ct).
        - (* object \notin dom CT *)
        exact (weaken_no_obj _ _ _ _ _ H_noobj).
        - (* smaller H_Ind *)
        apply (ClassTable_rect_reduce_H_Ind P C E fs ms _ H_directed_ct H_Ind).
        - (* ok_type E *)
        abstract exact (weaken_ok_type _ E C _ _ _
            (distinct_parent _ C E fs ms H_directed_ct H_noobj
                (binds_first _ _ _))
            H_ok_E).
    }

    + (* neq  Going to use IHCT' as we've got a smaller CT now. *)
    apply IHCT'.
    * exact (weaken_directed_ct _ _ _ H_directed_ct).
    * (* Obj \notin CT *)
    exact (weaken_no_obj _ _ _ _ _ H_noobj).
    * (* Use H_Ind *)
    apply (ClassTable_rect_reduce_H_Ind P D E fs ms _ H_directed_ct H_Ind).
    * (* Last argument of IHCT' *)
    exact (weaken_ok_type _ _ _ _ _ _ n H_ok).
Defined.

(* Rules for induciton principles *)
(* 
   forall CT ,                          (induction parameters)
   forall P: cname -> Type, (predicates)
   branch1, branch2, ... , branchr,                    (branches of the principle)
   forall (x1:Ti_1) (x2:Ti_2) ... (xni:Ti_ni),         (induction arguments)
   (HI: I prm1..prmp x1...xni)                         (optional main ind)
   *)
(** ClassTable_rect
* The idea behind this theorem is for a fixed class table CT,
* if we have a property `P : cname -> Prop` we wish to show,
* then it suffices to show (P Object) and (P D -> P C) when C
* inherits from D.
* There are a few additional hypothesis required, such as CT being directed,
* and not including Object, as well as all the classes involved being
* ok_type, that is either Object, or in CT.
*
* This theorem isn't actually an induction scheme, as defined
* by coq, as P does not take CT as an argument.  However, so long as you
* are not proving things about some C and (C, (D, fs,ms)) :: CT,
* where you would need to pick the class table after you pick C,
* this theorem works quite well.
*
* It requires a manual use of `refine`, and usually specifying P exactly,
* unfortunately.
*
*)
(* I don't think it's possible to prove a more general theorem.
If we had `filter_to_lineage C CT`, which removed from CT
all the pairs that didn't start with C or an ancestor of C,
and we tried to prove

forall (P: ctable -> typ -> Prop)

forall CT,   P (filter_to_lineage CT Object) Object ->
forall CT C, P (filter_to_lineage C CT) C ->
forall CT C,
directed_ct CT ->
Object \notin CT ->
ok_type_ CT C ->
P CT C.

It wouldn't hold up, as  TODO ?
*)



Theorem ClassTable_rect (CT: ctable)
    (P: cname -> Type)
    (H_dir: directed_ct CT)
    (H_noobj: Object \notin dom CT)
    (H_obj: P Object)
    (H_ind: (forall (C D : cname) fs ms,
      ok_type_ CT D ->
      binds C (D, fs, ms) CT ->
      P D -> P C))
    : forall C: cname,
     (ok_type_ CT C) ->
    P C.
Proof.
    induction CT as [| [D [[E fs] ms]] CT'].
    - (* nil *)
    intros.
    apply ClassTable_rect_base_case; auto.
    - (* cons *)
    apply ClassTable_rect_inductive_step; auto.
Defined.

(* Specialized to Prop *)
Theorem ClassTable_ind (CT: ctable)
    (P: cname -> Prop)
    (H_dir: directed_ct CT)
    (H_noobj: Object \notin dom CT)
    (H_obj: P Object)
    (H_ind: (forall (C D : cname) fs ms,
      ok_type_ CT D ->
      binds C (D, fs, ms) CT ->
      P D -> P C))
    : forall C: cname,
     (ok_type_ CT C) ->
    P C.
Proof.
    apply ClassTable_rect; auto.
Qed.
(** Here is an excellent example of how ClassTable_ind can be used to simplify
* a proof:
* This proof stats that every class is a subclass of object, which is 'trivial',
* yet is only easy to prove using ClassTable_ind.
*)
Lemma object_sub_top : forall CT C,
    Object \notin dom CT ->
    directed_ct CT ->
    ok_type_ CT C ->
    sub_ CT C Object.
Proof.
    intros CT C H_noobj H_dir H_ok.

    refine((ClassTable_rect CT
        (* P *) (fun C:cname => sub_ CT C Object)
        H_dir  H_noobj  _(*PO*) _(*PInd*))
    C H_ok).
    - (* sub_ CT Object Object *)
    apply sub_refl.
    constructor.
    - (* ok_type_ CT D -> binds C (D, fs, ms) -> sub_ CT D Object -> sub_ CT C Object *)

    (* refine doesn't clear away hypothesis like induction does, so we must
     * do it ourselves. *)
    clear C H_ok.
    intros C D fs ms H_ok H_binds H_sub.
    apply sub_trans with (t2 := D).
    + (* sub_ CT C D *)
    apply sub_extends.
    unfold extends_.
    exists fs.
    exists ms.
    exact H_binds.
    + (* sub_ CT D Object *)
    exact H_sub.
Qed.
Hint Resolve object_sub_top.

Lemma object_sub_top_hard_way CT C
    (H_noobj: Object \notin dom CT)
    (H_dir: directed_ct CT)
    (H_ok_C: ok_type_ CT C)
    : sub_ CT C Object.
Proof.
    (* If we just do an induction on CT... *)
    (* We need the induction principle to hold no matter what class we are talking about. *)
    generalize C, H_ok_C; clear C H_ok_C.
    induction CT.
    - (* sub_ nil C Object *)
    intros C H_ok_C.
    inversion H_ok_C; auto.
    - (* sub_ ((A, (B, fs, ms)) :: CT) C Object *)
    (* Here we don't really know anything, we have to do cases on what
    * A and B are to try and figure out what case we are in. *)
    intros C H_ok_C.
    destruct a as [A [[B fs] ms]].
    unfold_directed H_dir.
    destruct (A == C).
    + { (* Then we know that sub_ CT B Object, and use transitivity *)
    subst.
    apply sub_trans with (t2 := B).
    - (* sub C B *)
    apply sub_extends.
    unfold extends_.
    exists fs, ms.
    auto.
    - (* sub_ ((C, (B, fs, ms))::CT) B Object *)
    (* An application of the induction hypothesis get us this: *)
    assert (H_sub: sub_ CT B Object). {
        apply IHCT; crush.
    }
    (* Here, we run into a problem, as we need to show that
    adding an extra pair to the front of CT doesn't invalidate
    sub, but that's actually a nontrivial theorem below that depends
    on the current fact.
    We are forced to abort.*)
Abort.
(* And that's why ClassTable_ind is useful. *)

(* Unfortunately, it is less useful for computation than I hoped.
I would have liked to show the pair of theorems about how it reduces,
so if we have some `H : forall C, ok_type_ CT C -> P C`  we proved with an application of
ClassTable_rect CT .. P_Obj P_Ind,
and we apply it `H Object _`, we should get exactly P_Obj,
and if we apply it to `H C _`, when we have `H_binds: binds C (D, fs, ms) CT`,
and some `P_D : P D`
then we should get (P_Ind C D ...  P_D).

This would be really useful, as we could define method resolution using ClassTable_rect
instead of helper functions, and P_Obj and P_Ind are really simple.

when looking up a method named M

    P_Obj := None (* as Object has no methods *)
    P_Ind C D fs ms ... P_D :=
        match lookup M ms with
        | Some (m_body) => Some (m_body) (* we overrode the method in C *)
        | None => P_D (* We did not, so look it up in D *)
        end.

If we could write the method we find in terms of a chain of applications of
P_Ind capped off by a P_Obj, it would simple to prove things based on induction.

Alas, it does not seem tractable to prove both of those reduction rules,
as they require simplifying the body of ClassTable_rect Defined above,
which expands to over 3000 lines.  That's actually the reason it was
split into so many lemmas, in an attempt to manage the size of the goal.

It was possible to prove the case for Object, but the proof is commented
out as it takes a while to step past it.

*)



(* Attempt to show usful Set level facts about ClassTable *)
(*
Require Import Coq.Logic.JMeq.
Require Import Program.


Lemma ClassTable_obj_inv (CT : ctable)
    (H_dir : directed_ct CT)
    (H_noobj : Object \notin dom CT)
    (P : cname -> Type)
    (P_Obj : P Object)
    (P_Ind : forall (C D : cname) fs ms,
      ok_type_ CT D ->
      binds C (D, fs, ms) CT ->
      P D -> P C)
    (H_ok : ok_type_ CT Object) :
    (@ClassTable_rect CT P H_dir H_noobj P_Obj P_Ind Object H_ok) =
    P_Obj.
Proof.
    induction CT.
    - unfold ClassTable_rect.
    simpl.
    unfold eq_rect_r.
    unfold eq_rect.
    unfold eq_sym.
    dependent destruction H_ok; crush.
    - (* Inductive *)
    destruct a as [A [[B fs] ms]].
    unfold ClassTable_rect.
    unfold ClassTable_rect_inductive_step.
    simpl.
    destruct (A == Object) as [H_eq | H_neq].
    +
    exfalso.
    rewrite H_eq in H_noobj.
    crush.
    +
    apply IHCT.
Qed.
Lemma weaken_P_Ind (CT : ctable)
    (A B : cname) fs' ms'
    (H_dir : directed_ct ((A, (B, fs', ms')) :: CT))
    (H_noobj : Object \notin dom ((A, (B, fs', ms')) :: CT))
    (P : cname -> Type)
    (P_Ind : forall (C D : cname) fs ms,
      ok_type_ ((A, (B, fs', ms')) :: CT) D ->
      binds C (D, fs, ms) ((A, (B, fs', ms')) :: CT) ->
      P D -> P C)
    :
    forall (C D : cname) fs' ms',
    ok_type_ (CT) D ->
    binds C (D, fs', ms') CT ->
    P D -> P C.
Proof.
Abort.


Lemma ClassTable_ind_inv_different (CT : ctable)
    (A B : cname) fs' ms'
    (H_dir : directed_ct ((A, (B, fs', ms')) :: CT))
    (H_noobj : Object \notin dom ((A, (B, fs', ms')) :: CT))
    (P : cname -> Type)
    (P_Obj : P Object)
    (P_Ind : forall (C D : cname) fs ms,
      ok_type_ ((A, (B, fs', ms')) :: CT) D ->
      binds C (D, fs, ms) ((A, (B, fs', ms')) :: CT) ->
      P D -> P C)
    (C D : cname) fs ms
    (H_neq : C <> A)
    (H_ok_C : ok_type_ ((A, (B, fs', ms')) :: CT) C)
    (H_ok_D : ok_type_ ((A, (B, fs', ms')) :: CT) D)
    (H_binds :  binds C (D, fs, ms) ((A, (B, fs', ms')) :: CT))
    :
    (@ClassTable_rect ((A, (B, fs', ms')) :: CT) P H_dir H_noobj P_Obj P_Ind C H_ok_C)
    =
    (@ClassTable_rect CT P
    (weaken_directed_ct _ _ _ H_dir)
    (weaken_no_obj _ _ _ _ _ H_noobj)
    P_Obj
    (weaken_P_Ind CT A B fs' ms' H_dir H_noobj P P_Ind)
    C
    (weaken_ok_type _ _ _ _ (symmetry_neq H_neq) H_ok_C)).
Proof.
    unfold ClassTable_rect at 1.
    simpl.
    unfold ClassTable_rect_inductive_step at 1.
    simpl.
    destruct (A == C).
    - exfalso;  symmetry in e; auto.
    -
    unfold ClassTable_rect at 1.
    simpl.
Abort.


(* TODO
* This isn't working because we get a really large goal statement.
*)
Lemma ClassTable_ind_inv (CT : ctable)
    (H_dir : directed_ct CT)
    (H_noobj : Object \notin dom CT)
    (P : cname -> Type)
    (P_Obj : P Object)
    (P_Ind : forall (C D : cname) fs ms,
      ok_type_ CT D ->
      binds C (D, fs, ms) CT ->
      P D -> P C)
    (C D : cname) fs ms
    (H_ok_D : ok_type_ CT D)
    (H_ok_C : ok_type_ CT C)
    (H_binds :  binds C (D, fs, ms) CT)
    :
    (@ClassTable_rect CT P H_dir H_noobj P_Obj P_Ind C H_ok_C)
    =
    P_Ind C D fs ms H_ok_D H_binds
    (* P D = *) (@ClassTable_rect
        CT P H_dir H_noobj P_Obj P_Ind D H_ok_D).
Proof.
    induction CT.
    -
    solve_binds_nil.
    -
    destruct a as [A [[B fs'] ms']].
    unfold ClassTable_rect at 1.
    simpl.
    unfold ClassTable_rect_inductive_step at 1.
    simpl.
    (* TODO *)
    destruct (A == C).
    + unfold eq_rect_r at 1.
    unfold eq_rect at 1.
    unfold eq_sym at 1.
    dependent destruction e.
    {
    unfold ok_head_parent.
    dependent destruction H_dir.
    simpl.
    dependent destruction o.
    -
    simpl.
    destruct (A == D).
Abort.
(*
    -
    dependent destruction e.
    dependent destruction H_dir.
    simpl.
    dependent destruction o.
    simpl.
    unfold eq_ind_r.
    unfold eq_ind.
    unfold eq_rect.
    unfold eq_sym.
    exfalso.
    apply binds_elim_eq in H_binds.
    inversion H_binds.
    subst.
    crush.
    - (* A <> D *)

    (*refine (distinct_parent _ A A fs ms H_directed_ct _ _).*)
Abort.
*)

*)

(* Proved as an example above. 
Lemma object_sub_top : forall CT C,
    Object \notin dom CT ->
    directed_ct CT ->
    ok_type_ CT C ->
    sub_ CT C Object.
Proof.
    intros CT C H_noobj H_dir H_ok.
    induction CT using ClassTable_rect.

    refine((ClassTable_rect CT 
        (fun C:cname => sub_ CT C Object)
        H_dir  H_noobj  _(*PO*) _(*PInd*))
    C H_ok).
    -
    apply sub_refl.
    constructor.
    -

    clear C H_ok.
    intros C D fs ms H_ok H_binds H_sub.
    apply sub_trans with (t2 := D).
    +
    apply sub_extends.
    unfold extends_.
    exists fs.
    exists ms.
    exact H_binds.
    +
    exact H_sub.
Qed.
Hint Resolve object_sub_top.
*)

Lemma object_ssub_top' : forall CT C,
    Object \notin dom CT ->
    directed_ct CT ->
    ok_type_ CT C ->
    C = Object \/ ssub_ CT C Object.
Proof.
    intros CT C H_noobj H_dir H_ok.

    refine((ClassTable_rect CT
        (fun C:cname => C = Object \/ ssub_ CT C Object)
        H_dir  H_noobj  _(*PO*) _(*PInd*))
    C H_ok).

    intros.
    left; auto.

    clear C H_ok.
    intros C D fs ms H_ok H_binds H_sub.
    destruct H_sub.
    -
    subst.
    right.
    apply ssub_extends.
    unfold extends_.
    exists fs.
    exists ms.
    exact H_binds.
    -
    right.

    apply ssub_trans with (t2 := D).
    +
    apply ssub_extends.
    unfold extends_.
    exists fs; exists ms.
    exact H_binds.
    +
    exact H.
Qed.

Hint Resolve object_ssub_top'.

Lemma object_ssub_top : forall CT C,
    Object \notin dom CT ->
    directed_ct CT ->
    ok_type_ CT C ->
    C <> Object ->
    ssub_ CT C Object.
Proof.
    intros.
    assert (H_top : C = Object \/ ssub_ CT C Object) by auto.
    destruct H_top.
    exfalso. auto.
    auto.
Qed.
Hint Resolve object_ssub_top.

Lemma ssub_ok_1 : forall CT C D,
    ssub_ CT C D -> ok_type_ CT C.
Proof.
    intros.
    induction H.
    -
    apply IHssub_1.
    -
    unfold_extends H.
    constructor.
    apply binds_In with (a:= (t2, fs, ms)).
    exact H_binds.
Qed.  Hint Resolve ssub_ok_1.

Lemma ssub_ok_2 : forall CT C D,
    directed_ct CT ->
    ssub_ CT C D -> ok_type_ CT D.
Proof.
    intros CT C D H_dir H_sub.
    induction H_sub.
    crush.

    unfold_extends H.
    eapply directed_binds.
    exact H_dir.
    exact H_binds.
Qed.
Hint Resolve ssub_ok_2.

Lemma sub_ok_1 : forall CT C D,
    sub_ CT C D -> ok_type_ CT C.
Proof.
    intros.
    induction H.
    -
    assumption.
    -
    apply IHsub_1.
    -
    unfold_extends H.
    constructor.
    apply binds_In with (a:= (D, fs, ms)).
    exact H_binds.
Qed.  Hint Resolve sub_ok_1.

Lemma sub_ok_2 : forall CT C D,
    directed_ct CT ->
    sub_ CT C D -> ok_type_ CT D.
Proof.
    intros CT C D H_dir H_sub.
    induction H_sub.
    -
    assumption.
    -
    crush.
    -

    unfold_extends H.
    eapply directed_binds.
    exact H_dir.
    exact H_binds.
Qed.
Hint Resolve sub_ok_2.


Lemma binds_parent_ok: forall CT A B C D fs ms fs' ms',
    directed_ct ((A, (B, fs', ms')) :: CT) ->
    binds C (D, fs, ms) ((A, (B, fs', ms')) :: CT) ->
    ok_type_ CT D.
Proof.
    intros CT A B C D fs ms fs' ms'.
    intros H_dir H_binds.
    unfold_directed H_dir.
    destruct (C == A).
    -
    subst.
    apply binds_elim_eq in H_binds.
    inversion H_binds.
    auto.
    -
    apply binds_elim_neq in H_binds; eauto.
Qed. Hint Resolve binds_parent_ok.


Lemma not_your_father (CT:ctable) : forall A B C D fs ms,
    directed_ct ((A, (B, fs, ms)) :: CT) ->
    Object \notin dom ((A, (B, fs, ms)) :: CT) ->
    ssub_ ((A, (B, fs, ms)) :: CT) C D ->
    A <> D.
Proof.
    intros A B C D fs ms H_dir H_noobj H_sub.
    unfold not.
    induction H_sub using ssub__ind_parametric.
    auto.
    unfold_extends H.
    unfold_directed H_dir.
    destruct (t1 == A).
    -
    intros H_eq.
    symmetry in H_eq.
    subst.
    refine (_ (no_self_inheritance ((A, (B, fs, ms)) :: CT)
        H_dir H_noobj A)).

    unfold not.
    intros H.
    apply H.
    exists fs0; exists ms0.
    exact (H_binds).
    -
    intros H_eq.
    symmetry in H_eq.
    subst.

    apply binds_elim_neq in H_binds; auto.
    apply directed_ok in H_binds; auto.
    destruct H_binds; crush.
Qed. Hint Resolve not_your_father.

(* This is signifigently easier with the parametric induction scheme,
as the index based one "forgets" that CT is nil, making it impossible.
I think you could do it by writing the proof longhand and using
the convoy pattern, but it's much more work *)
Lemma no_ssub_with_empty_table C D :
    ssub_ nil C D ->
    False.
Proof.
    intros H_sub.
    induction H_sub using ssub__ind_parametric; auto.
Qed.
Hint Resolve no_ssub_with_empty_table.


Lemma weaken_ssub (CT:ctable) C D A B fs ms
    (H_dir: directed_ct ((A, (B, fs, ms))::CT))
    (* ok_type_ CT C -> *)
    (H_noobj: Object \notin dom ((A, (B, fs, ms)) :: CT))
    (* ok_type_ CT D -> *)
    (H_neq: A <> C)
    (H_sub: ssub_ ((A, (B, fs, ms)) :: CT) C D)
    : ssub_ CT C D.
Proof.
    pattern C, D, H_dir, H_noobj, H_neq.
    induction H_sub using ssub__ind_parametric.
    - apply ssub_trans with (t2:=t2).
    +
    crush.
    +
    unfold_directed H_dir.
    assert (H_neq2 : A <> t2).
    refine (not_your_father CT A B t1 t2 fs ms H_dir H_noobj H_sub1 ).
    auto.
    -
    unfold_extends H.
    apply binds_elim_neq in H_binds; auto.
    constructor.
    unfold extends_.
    exists fs0; exists ms0.
    exact (H_binds).
Qed. Hint Resolve weaken_ssub.

Lemma ssub_anti_reflexive CT C
    (H_noobj: Object \notin dom CT)
    (H_dir: directed_ct CT)
    : ssub_ CT C C -> False.
Proof.
    intros H_sub.
    induction CT.
    -
    induction H_sub using ssub__ind_parametric; auto.
    -
    destruct a as [A [[B fs] ms]].
    unfold_directed H_dir.
    assert (H_neq: A <> C) by
    exact (not_your_father CT A B C C fs ms H_dir H_noobj H_sub).
    +
    apply IHCT. crush. auto.
    refine (weaken_ssub CT C C A B fs ms H_dir H_noobj H_neq H_sub).
Qed. Hint Resolve ssub_anti_reflexive.

Lemma anti_symmetric_ssub (CT: ctable) C D :
    directed_ct CT ->
    Object \notin dom CT ->
    ssub_ CT C D ->
    ssub_ CT D C ->
    False.
Proof.
    intros H_dir H_noobj H_CD H_DC.
    induction CT.
    eauto.
    destruct a as [A [[B fs] ms]].
    unfold_directed H_dir.
    apply IHCT.
    auto.
    eauto.

    assert (H_neq_AC: A <> C) by
    exact (not_your_father CT A B D C fs ms H_dir H_noobj H_DC).
    apply (weaken_ssub CT C D A B fs ms H_dir H_noobj H_neq_AC H_CD).
    assert (H_neq_AD: A <> D) by
    exact (not_your_father CT A B C D fs ms H_dir H_noobj H_CD).
    apply (weaken_ssub CT D C A B fs ms H_dir H_noobj H_neq_AD H_DC).

Qed.
Hint Resolve anti_symmetric_ssub.

Lemma object_ssub_not_bot CT C
    (H_noobj: Object \notin dom CT)
    (H_dir: directed_ct CT)
    (H_sub: ssub_ CT Object C)
    : False.
Proof.
    assert (H_ok: ok_type_ CT C).
    apply ssub_ok_2 with (C:= Object); auto.
    induction H_sub;  eauto.
Qed.
Hint Resolve object_ssub_not_bot.

Lemma ssub_child_in_table CT C D
    (H_dir: directed_ct CT)
    (H_noobj: Object \notin dom CT)
    (H_sub : ssub_ CT C D)
    : C \in dom CT.
Proof.
    assert (H_ok: ok_type_ CT C).
    apply ssub_ok_1 with (D := D);
    assumption.

    destruct H_ok.
    exfalso.
    apply object_ssub_not_bot with (CT := CT) (C:= D); auto.
    assumption.
Qed. Hint Resolve ssub_child_in_table.

Lemma object_subclasses_self_only CT C
    (H_noobj: Object \notin dom CT)
    (H_dir: directed_ct CT)
    (H_ok: ok_type_ CT C)
    (H_sub: sub_ CT Object C)
    : Object = C.
Proof.
    assert (H: ssub_ CT Object C \/ Object = C).
    apply sub_to_ssub_or_eq; auto.
    destruct H.
    - exfalso.  refine (object_ssub_not_bot CT C _ _ H); auto.
    - auto.
Qed.  Hint Rewrite object_subclasses_self_only.

Lemma sub_nil_is_object C D
    (H_dir: directed_ct nil)
    (H_sub: sub_ nil C D)
    : C = Object /\ D = Object.
Proof.
    induction H_sub.
    -
    destruct H.
    auto.
    crush.
    -
    crush.
    -
    unfold_extends H.
    crush.
Qed. Hint Resolve sub_nil_is_object.

Lemma weaken_sub (CT:ctable) C D A B fs ms
    (H_dir: directed_ct ((A, (B, fs, ms))::CT))
    (* ok_type_ CT C -> *)
    (H_noobj: Object \notin dom ((A, (B, fs, ms)) :: CT))
    (* ok_type_ CT D -> *)
    (H_neq: A <> C)
    (H_sub: sub_ ((A, (B, fs, ms)) :: CT) C D)
    : sub_ CT C D.
Proof.
    induction H_sub.
    -
    constructor.
    apply weaken_ok_type with (A:=A) (B:=B) (fs:=fs) (ms:=ms).
    assumption.
    assumption.
    - apply sub_trans with (t2:=t2).
    +
    crush.
    +
    unfold_directed H_dir.
    assert (H_ssub1_or_eq: ssub_ ((A, (B, fs, ms)) :: CT) t1 t2 \/ t1 = t2) by
    apply (sub_to_ssub_or_eq _ t1 t2 H_sub1).
    assert (H_ssub2_or_eq: ssub_ ((A, (B, fs, ms)) :: CT) t2 t3 \/ t2 = t3) by
    apply (sub_to_ssub_or_eq _ t2 t3 H_sub2).
    {
    destruct H_ssub1_or_eq as [H_ssub1 | H_eq].
    -
    destruct H_ssub2_or_eq as [H_ssub2 | H_eq].
    +
    assert (H_neq2: A <> t2) by
    refine (not_your_father CT A B t1 t2 fs ms H_dir H_noobj H_ssub1 ).
    assert (ssub_ CT t2 t3) by
    refine (weaken_ssub CT t2 t3 A B fs ms H_dir H_noobj H_neq2 H_ssub2).
    apply ssub_to_sub; assumption.
    +
    subst.
    apply sub_refl.
    apply ssub_ok_2 with (C:=t1); auto.
    apply (weaken_ssub _ _ _ A B fs ms); auto.
    -
    subst.
    auto.
    }
    -
    unfold_extends H.
    apply binds_elim_neq in H_binds; auto.
    constructor.
    unfold extends_.
    exists fs0; exists ms0.
    exact (H_binds).
Qed. Hint Resolve weaken_sub.

(* A particular subcase of strengthening ssub *)
Lemma strengthen_ssub_case
    (CT : list (cname * (cname * flds * mths)))
    (A : cname)
    (B : cname)
    (C : typ)
    (D : typ)
    (F : cname)
    (ms : mths)
    (fs : flds)
    (fs2 : flds)
    (ms2 : mths)
    (H_dir0 : directed_ct ((C, (F, fs2, ms2)) :: CT))
    (H_noobj0 : Object \notin dom ((C, (F, fs2, ms2)) :: CT))
    (H_neq_C : A <> C)
    (H_notin : A \notin keys ((C, (F, fs2, ms2)) :: CT))
    (H_sub : ssub_ ((C, (F, fs2, ms2)) :: CT) C D)
    :
    ssub_ ((A, (B, fs, ms)) :: (C, (F, fs2, ms2)) :: CT) C D.
Proof.
    refine ((ssub__ind
    (* P *) (fun CT X Y => 
    directed_ct CT ->
    Object \notin dom CT ->
    A <> X ->
    A \notin keys CT ->
    ssub_ ((A, (B, fs, ms))::CT) X Y)
    (* H_Trans *) _
    (* H_Extend *) _)
    (* CT *) ((C, (F, fs2, ms2)) :: CT)
    C D H_sub
    H_dir0
    H_noobj0
    H_neq_C
    H_notin
    ).
    - (* trans *)
    clear.
    intros CT C t2 D.
    intros H_sub_1 IH_1 H_sub_2 IH_2.
    intros H_dir0 H_noobj0.
    intros H_neqAC .
    intros H_A_notin.

    destruct (A == t2) as [H_eq_At2|H_neq_t2].
    + (* A = t2 *)
    rewrite <- H_eq_At2 in * |- *; clear H_eq_At2.
    clear IH_1 IH_2.
    assert (H: A \in keys CT) by
    refine (ssub_child_in_table CT A D H_dir0 H_noobj0 H_sub_2).
    contradiction H.
    + (* A <> t2 *)
    assert (C <> t2). {
        destruct (C == t2) as [H_eq_Ct2 | H_neq_Ct2].
        - (* eq *)
        rewrite <- H_eq_Ct2 in H_sub_1.
        exfalso.
        refine (ssub_anti_reflexive CT C H_noobj0 H_dir0 H_sub_1).
        - (* neq *) exact H_neq_Ct2.
    }
    assert (H_ok_t2: ok_type_ CT t2) by
    exact (ssub_ok_1 CT t2 D H_sub_2).
    apply ssub_trans with (t2:=t2).
    apply IH_1; assumption.
    apply IH_2; assumption.
    - (* extends *)
    clear.
    intros CT C D H_extends.
    intros H_dir0 H_noobj0.
    intros H_neqAC .
    intros H_A_notin.

    unfold_extends H_extends.
    apply ssub_extends.
    unfold extends_.
    exists fs0, ms0.
    apply (binds_other _ H_binds H_neqAC).
Qed.

Lemma strengthen_ssub (CT:ctable) C D A B ms fs
    (H_dir: directed_ct ((A, (B, fs, ms)) :: CT))
    (H_ok_C_s: ok_type_ ((A, (B, fs, ms)) :: CT) C)
    (H_noobj: Object \notin dom ((A, (B, fs, ms)) :: CT))
    (H_neq: A <> C)
    (H_sub: ssub_ CT C D)
    (H_ok_D: ok_type_ CT D)
    : ssub_ ((A, (B, fs, ms)) :: CT) C D.
Proof.
    assert (H_ok_C: ok_type_ CT C) by
        refine (weaken_ok_type CT C _ _ _ _ H_neq H_ok_C_s).
    induction CT.

    -
    exfalso.
    exact (no_ssub_with_empty_table C D H_sub).
    -
    {
    destruct a as [E [[F fs2] ms2]].
    unfold_directed H_dir.
    unfold_directed H_dir0.
    destruct (E == B) as [ | H_neq_B].
    + (* E = B Case *)
    subst.
    clear IHCT. (* it doesn't apply as B is not okay in CT. *)
    move H_dir0 before H_dir.
    move H_dir1 after H_dir0.
    move H_noobj before  fs.
    move H_ok_C before H_ok0.
    move H_ok_D before H_ok_C.
    move H_ok before H_ok_D.
    rename H_ok into H_ok_B.
    move H_ok_C before H_ok_D.
    move H_ok_C_s after H_ok_C.

    {
        induction H_sub using ssub__ind_parametric.
        move t1 before fs.
        move t2 before t1.
        move t3 before t2.
        - (* trans *)
        destruct (A == t2).
        + subst. (* This is a contradiciton as t2 \notin B :: dom CT,
        but ssub_ B:: CT t2 t3 *)
        assert (t2 \in dom ((B, (F, fs2, ms2)) :: CT)).
            apply ssub_child_in_table with (D:= t3); crush.
        contradiction H_notin.
        + (* we can now do the transitivity case *)


        {
            apply ssub_trans with (t2:=t2).

            -
            apply IHH_sub1; try assumption.
            apply ssub_ok_1 with (D := t3); assumption.
            -
            assert (H_ok_t2_s: ok_type_ ((B, (F, fs2, ms2)) :: CT) t2).
            apply ssub_ok_2 with (C:= t1) (D := t2); assumption.
            apply IHH_sub2; try assumption.
            apply strengthen_ok_type; assumption.
        }
        - (* extends case *)
        unfold_extends H.
        apply ssub_extends.
        unfold extends_.
        exists fs0, ms0.
        auto.

    }
    + (* E <> B case *)
    (* Going to be able to use IHCT  *)
    move H_neq_B before H_neq.
    rename H_neq into H_neq_C.
    move H_dir0 before H_dir.
    move H_dir1 before H_dir0.
    move H_ok_C_s after H_ok_C.
    rename H_ok0 into H_ok_F_w.
    move H_ok_F_w before H_ok_C_s.
    rename H_ok into H_ok_B.
    move H_ok_B before H_ok_C.

    assert (H_neq_D: A <> D).  {
        destruct H_ok_D as [| D H_in_D]; crush.
    }
    move H_neq_D before H_neq_C.
    assert (H_ok_B_w: ok_type_ CT B) by
        refine (weaken_ok_type CT B E F fs2 ms2 H_neq_B H_ok_B).
    move H_ok_B_w after H_ok_F_w.

    assert (H_noobj0: Object \notin dom ((E, (F, fs2, ms2)) :: CT)) by crush.
    move H_noobj0 before H_noobj.
    assert (H_noobj1: Object \notin dom CT) by crush.
    move H_noobj1 before H_noobj0.

    assert (H_neq_ED: E <> D) by
        refine (not_your_father CT E F C D fs2 ms2
        H_dir0 H_noobj0 H_sub).
    move H_neq_ED before H_neq_B.

    (* Is C = E and D = F? *)
    {
        destruct (C == E) as [H_eq | H_neq_CE].
        -
        rewrite <- H_eq in * |- *; clear H_eq.
        clear IHCT. (* Not goin to use it *)
        apply strengthen_ssub_case; assumption.
        - (* C <> E *)
        move H_neq_CE after H_neq_ED.


        assert (H_neq_EC: E <> C) by auto.
        assert (H_notin1: A \notin keys CT) by crush.
        assert(H_sub_w: ssub_ CT C D). {
            apply weaken_ssub with (A:=E) (B:=F) (fs:=fs2) (ms:=ms2); auto.
        } move H_sub_w before H_sub.
        clear IHCT.
        (* Trans should fall easily enough, then extends should not be too bad. *)
        {
            refine ((ssub__ind
            (* P *) (fun CT X Y => forall
            (H_dir: directed_ct CT)
            (H_noobj: Object \notin dom CT)
            (H_neq1: A <> X)
            (H_neq2: E <> X)
            (H_notin1: A \notin keys CT)
            (H_notin2: E \notin keys CT ),
            ssub_ ((A, (B, fs, ms))::(E, (F, fs2, ms2))::CT) X Y)
            (* H_Trans *) _
            (* H_Extend *) _)
            (* CT *) CT
            C D H_sub_w
            _ _ _ _ _ _); try assumption.
            - (* trans *)
            clear dependent CT.
            clear dependent C.
            clear dependent D.

            intros CT t1 t2 t3.
            intros H_sub_1 IHH_sub_1 H_sub_2 IHH_sub_2.
            intros.
            apply ssub_trans with (t2:=t2).
            +
            auto.
            + (* Need t2 <> A, t2 <> E *)

            assert (t2 \in keys CT). {
                apply ssub_child_in_table with (D := t3); assumption.
            }
            assert (A <> t2). {
                destruct (A == t2).
                subst.
                contradiction.
                auto.
            }
            assert (E <> t2). {
                destruct (E == t2).
                subst.
                contradiction.
                auto.
            }
            auto.
            - (* extends *)
            clear dependent CT;
            clear dependent C;
            clear dependent D.
            intros CT C D H_extends.
            intros.

            unfold_extends H_extends.
            apply ssub_extends.
            unfold extends_.
            exists fs0, ms0.
            auto.
        }
    }
    }
Qed. Hint Resolve strengthen_ssub.

Lemma strengthen_sub (CT:ctable) : forall C D A B ms fs,
    directed_ct ((A, (B, fs, ms)) :: CT) ->
    ok_type_ ((A, (B, fs, ms)) :: CT) C ->
    Object \notin dom ((A, (B, fs, ms)) :: CT) ->
    A <> C ->
    sub_ CT C D ->
    ok_type_ CT D ->
    sub_ ((A, (B, fs, ms)) :: CT) C D.
Proof.
    intros C D A B ms fs H_dir H_ok_C H_noobj H_neq H_sub H_ok_D.
    assert (H_ok_C_weak: ok_type_ CT C) by
        refine (weaken_ok_type CT C _ _ _ _ H_neq H_ok_C).
    induction CT.

    -
    assert (H : C = Object /\ D = Object) by auto.
    destruct H; subst.
    apply sub_refl.
    auto.

    -
    destruct a as [E [[F fs2] ms2]].
    unfold_directed H_dir.
    unfold_directed H_dir0.
    destruct (E == B) as [ | H_neqB].
    +
    subst.
    clear IHCT. (* it doesn't apply as B is not okay in CT. *)
    move H_dir0 before H_dir.
    move H_dir1 after H_dir0.
    move H_noobj before  fs.
    move H_ok_C before H_ok0.
    move H_ok_D before H_ok_C.
    move H_ok before H_ok_D.
    rename H_ok into H_ok_B.
    move H_ok_C_weak before H_ok_D.

    {
    induction H_sub.
    -
    auto.
    - (* trans *)
    destruct (A == t2).
    + (* This is a contradiciton as t2 \notin B :: dom CT,
    but sub_ B:: CT t2 t3 *)

    subst.
    assert (H_ssub_1: ssub_ ((B, (F, fs2, ms2)) :: CT) t1 t2).
    +

    apply sub_trans with (t2:=t2).
    +

    +
    apply IHH_sub1; try assumption.
    apply sub_ok_1 with (D := t3); assumption.
    +
    apply IHH_sub2; try assumption.
    {
    - subst.
    -
    }


    
    }


    +
    {
    assert (H_sub2 :  sub_ ((A, (B, fs, ms)) :: CT) C D).
    apply IHCT.
    constructor.
    auto.
    crush.
    {
    - subst. apply (weaken_ok_type CT B B F fs2 ms2).
    -
    }admit.
    eapply weaken_ok_type. exact H_neqB. exact H_ok.
    assert (H_neqC: E <> C). admit.
    apply strengthen_ok_type.
    apply weaken_ok_type with (A:= E) (B:=F) (fs:=fs2) (ms:=ms2).
    auto.
    auto.
    crush.
    apply (weaken_sub CT C D A B fs ms).
    constructor.
    auto.
    crush.
    eapply weaken_ok_type. 
    assert (H_neqB: E <> B). admit.
    exact H_neqB.
    exact H_ok.
    crush.
    auto.


Qed.


(*
    refine((ClassTable_rect CT
        (fun D:cname => sub_ ((A, (B, fs, ms)) :: CT) C D)
        H_dir0  _  _(*PO*) _(*PInd*))
    D H_ok_D).
    - (* Object \notin dom CT *)
    crush.
    - (* sub_ (A, (B, fs ms)) ::CT  C Object *)
    auto.
    -
    clear D H_sub H_ok_D.
    intros C' D fs' ms' H_ok_D H_binds H_subCD.
    (* H_subCD must in fact be a transitive case.
    * If it were a extends case,
    * we would have binds C (D,..) and binds C' (D, ...)
    *)
    induction H_subCD as [ CD |  |  ].
    - (* C = D case *)


Qed.
*)
    


(* TODO Restructure below this point still *)

(** We assume a fixed class table [CT]. *)
Parameter CT_A : ctable.
Parameter CT_L : ctable.

Definition CT := CT_A ++ CT_L.

Definition CT_L' := CT_L.

Definition CT' := CT_A ++ CT_L'.

(* TODO is it a good idea to have this as global hypotheis? *)
Hypothesis CT_is_directed : directed_ct CT.
Hypothesis CT_L_is_directed : directed_ct CT_L.
Hypothesis CT_nocontains_obj : Object \notin dom CT.

(* Definitions which just assume CT. *)
Definition ok_type := ok_type_ CT.
Hint Unfold ok_type.
Definition extends := extends_ CT.
Hint Unfold extends.
Definition sub     := @sub_ CT.
Hint Unfold sub.

(** * Auxiliaries *)

(** ** Field and method lookup *)

(** [field C f t] holds if a field named [f] with type [t] is defined for class
    [C] in the class hierarchy. *)

(* (F-Object) and (Fields) defined. *)

Inductive fields : cname -> flds -> Prop :=
| fields_obj : fields Object nil
| fields_other : forall C D fs fs' ms,
    binds C (D,fs,ms) CT ->
    fields D fs' ->
    fields C (fs'++fs).

Hint Constructors fields.

Definition field (C : cname) (f : fname) (t : typ) : Prop :=
    exists2 fs, fields C fs & binds f t fs.

Hint Unfold field.

(** [method C m mdecl] holds if a method named [m] with declaration [mdecl] is
    defined for class [C] in the class hierarchy. *)

Inductive method : cname -> mname -> typ * env * exp -> Prop :=
| method_this : forall C D fs ms m mdecl,
    binds C (D,fs,ms) CT ->
    binds m mdecl ms ->
    method C m mdecl
| method_super : forall C D fs ms m mdecl,
    binds C (D,fs,ms) CT ->
    no_binds m ms ->
    method D m mdecl ->
    method C m mdecl.

Hint Constructors method.

(*
Notation ctable := (list (cname * (cname * flds * mths))).
Notation flds := (list (fname * typ)).
Notation mths := (list (mname * (typ * env * exp))).
Notation env := (list (var * typ)).
*)



(* Need to generate a lineage list, of all the parents as well as the current class.. *)

Fixpoint lineage (CT: ctable) (* (H: directed_ct CT) *) (C: cname) {struct CT} : list cname :=
    match CT with
    | nil => C :: nil
    | ((C', (D, _, _)) :: CT') =>
            if C == C' then
            C :: lineage CT' D
            else
            lineage CT' C
    end.

Example lineage_test : forall A B C : cname,
    lineage ((A, (B, nil, nil)) ::
             (B, (C, nil, nil)) ::
             (C, (Object, nil, nil)) :: nil ) A = A :: B :: C :: Object :: nil.
Proof.
    intros.
    unfold lineage.
    rewrite eq_atom_true.
    rewrite eq_atom_true.
    rewrite eq_atom_true.
    reflexivity.
Qed.

Lemma extend_lineage (CT': ctable) : forall A B fs ms C D,
    C <> A ->
    D \in lineage CT' C ->
    D \in lineage ((A, (B, fs, ms))::CT') C .
Proof.
    intros.
    unfold lineage.
    fold lineage.
    rewrite eq_atom_false.
    assumption.
    assumption.
Qed.

Hint Immediate extend_lineage.

Fixpoint method_lookup_helper (CT: ctable) (m:mname) (ancestors: list cname) :=
    match ancestors with
    | nil => None
    | C :: Cs => match Metatheory.get C CT with
        | None => (* impossible *) None
        | Some (_, _, ms) => match Metatheory.get m ms with
            | None => method_lookup_helper CT m Cs
            | Some (v) => Some (C, v)
            end
        end
    end.

Definition mtype_lookup {CT : ctable} {H: directed_ct CT}  (m:mname) (C:cname) :
    option (list typ * typ) :=
    match method_lookup_helper CT m (lineage CT C) with
    | None => None
    | Some (C, (R, env, _)) => Some ((List.map (snd (A:=mname) (B:=typ)) env), R)
    end.

Definition mbody_lookup {CT : ctable} {H: directed_ct CT} (m:mname) (C:cname) :
    option (env * exp) :=
    match method_lookup_helper CT m (lineage CT C) with
    | None => None
    | Some (C, (R, env, body)) => Some (env, body)
    end.

Definition mresolve (CT : ctable) {H: directed_ct CT} (m:mname) (C:cname) :
    option (cname) :=
    match method_lookup_helper CT m (lineage CT C) with
    | None => None
    | Some (C, _) => Some C
    end.


Definition mresolve2 (CT: ctable) (m: mname)
    {H_dir: directed_ct CT}
    {H_noobj: Object \notin dom CT}
    : forall C: cname, ok_type_ CT C -> option (cname) :=
    @ClassTable_rect CT (fun (C: cname) => option (cname))
    H_dir H_noobj
    (* P Obj *) ((fun _: cname => @None cname) Object)
    (* P ind *) (fun (C D: cname) fs ms H_ok H_binds P_D =>
        match get m ms with
        | None => P_D
        | Some _ => Some C
    end).


(* mresolve3 CT C m D means that when starting with child class C,
* and looking for a method D, we find the method on class D. *)
Inductive mresolve3 : ctable -> cname -> mname -> cname -> Prop :=
| MResolve_Head_Direct : forall CT m C D (ms: mths) fs,
        m \in dom ms ->
        mresolve3 ((C, (D, fs, ms)) :: CT) C m C
| MResolve_Head_Inherit : forall CT m C D E (ms: mths) fs,
        m \notin dom ms ->
        mresolve3 CT D m E ->
        mresolve3 ((C, (D, fs, ms)) :: CT) C m E
| MResolve_Tail : forall CT m A B C D (ms: mths) fs,
        C <> A ->
        mresolve3 CT C m D ->
        mresolve3 ((A, (B, fs, ms)) :: CT) C m D.
        


Definition declares_m (C:cname) (m:mname) : Prop :=
    (exists D fs ms, binds C (D, ms, fs) CT /\ m \in dom ms).

(* TODO parameterize over CT and CT'? *)
Definition declares_f (C:cname) (f:fname) : Prop :=
    (exists D fs ms, binds C (D, ms, fs) CT /\ f \in dom fs).

Fixpoint constructor_helper (CT: ctable) (ancestors: list cname) :=
    match ancestors with
    | nil => nil
    | C :: Cs => match Metatheory.get C CT with
        | None => (* impossible *) nil
        | Some (_, fs, _) => 
                (constructor_helper CT Cs) ++ fs
        end
    end.

Definition constructor (C:cname) : list (fname * typ) :=
    constructor_helper CT (lineage CT C).


(*
Module Example_lookup.
    Variable A B C D : cname.
    Variable foo : mname.
(*
Notation ctable := (list (cname * (cname * flds * mths))).
Notation flds := (list (fname * typ)).
Notation mths := (list (mname * (typ * env * exp))).
Notation env := (list (var * typ)).
*)
    Definition CT : ctable := (
        (A, (B, nil, nil)) ::
        (B, (C, nil, (foo, (C,nil,(e_new C nil)))::nil)) ::
        (C, (Object, nil, nil)) ::
        nil ).

    Lemma dir_CT : directed_ct CT.
    Proof.
        unfold CT.
        apply directed_ct_cons.
        apply directed_ct_cons.
        apply directed_ct_cons.
        apply directed_ct_nil.
        auto.
        right.
        auto.
        simpl.
        admit.  (* A B C D, Distinct *)
        left.
        simpl.
        left; reflexivity.
        simpl.
        admit.  (* A B C D, Distinct *)
        simpl.
        left.
        left.
        reflexivity.
    Qed.




    Example m_type_lookup :
            mtype_lookup (CT:=CT) (H:=dir_CT) foo A = Some (nil, C).
    Proof.
        unfold mtype_lookup.
        simpl.
        rewrite eq_atom_true.
        rewrite eq_atom_true.
        rewrite eq_atom_true.
        unfold method_lookup_helper.
        simpl.
        rewrite eq_atom_true.
        rewrite eq_atom_true.
        rewrite eq_atom_true.
        rewrite eq_atom_false.
        rewrite eq_atom_false.
        rewrite eq_atom_false.
        rewrite eq_atom_false.
        rewrite eq_atom_false.
        rewrite eq_atom_false.
        simpl.
        rewrite eq_atom_true.
        simpl.
        reflexivity.
        admit.
        admit.
        admit.
        admit.
        admit.
        admit.
    Qed.
End Example_lookup.
*)

Lemma lineage_object : forall CT,
    Object \notin dom CT ->
    Object :: nil = lineage CT Object.
Proof.
    intros CT'.
    induction CT'.
    - crush.
    - intros.
    destruct a as [A [[B fs] ms]].
    crush.
Qed.

Hint Resolve lineage_object.



Lemma self_lineage1 : forall CT C,
    ok_type_ CT C ->
    directed_ct CT ->
    Object \notin dom CT ->
    hd_error (lineage CT C) = Some (C).
Proof.
    clear.
    intros CT C H_ok H_dir H_noobj.
    induction CT.
    - crush.
    -
    destruct a as [A [[B fs] ms]].
    destruct (A == C).
    + (* Found it *)
    subst.
    unfold lineage.
    fold lineage.
    rewrite eq_atom_true.
    crush.
    + (* IH time *)
    unfold lineage.
    fold lineage.
    rewrite eq_atom_false.
    { apply IHCT.
    - eapply weaken_ok_type.
    exact n.
    exact H_ok.
    - eapply weaken_directed_ct.
    exact H_dir.
    - crush.
    }
    crush.
Qed.


Lemma self_lineage : forall CT C,
    directed_ct CT ->
    ok_type_ CT C ->
    C \in lineage CT C.
Proof.
    clear.
    intros.
    induction CT0.
    crush.
    destruct a as [A [[B fs] ms]].
    unfold lineage.
    fold lineage.
    destruct (A == C).
    - subst.
    rewrite eq_atom_true.
    crush.

    -
    rewrite eq_atom_false.
    apply IHCT0.
    + eapply weaken_directed_ct. apply H.
    +
    inversion H0.
    * apply ok_obj.
    *
    subst.
    crush.
    + crush.
Qed.

Hint Resolve self_lineage.

Lemma list_map_head : forall A xs ys,
    xs = ys ->
    @hd_error A xs = hd_error ys.
Proof.
    intros.
    congruence.
Qed.

Lemma lineage_injective : forall CT C D,
    Object \notin dom CT ->
    directed_ct CT ->
    ok_type_ CT C ->
    ok_type_ CT D ->
    lineage CT C = lineage CT D ->
    C = D.
Proof.
    clear.
    intros CT' C D H_noobj H_dir H_ok_C H_ok_D H_eq.
    induction CT'.
    -
    apply ok_type_nil in H_ok_C.
    apply ok_type_nil in H_ok_D.
    crush.
    - (* inductive case *)
    destruct a as [A [[B fs] ms]].
    (* Two cases, either A = C = D or A <> C, A <> D *)
    destruct (A == C).
    + subst.
    (* Either it's easy, or false *)
    destruct (D == C).
    * crush.
    * (* Have to show inconsitency *)
    unfold lineage in H_eq.
    fold lineage in H_eq.
    rewrite eq_atom_true in H_eq.
    rewrite eq_atom_false in H_eq.
    {
    apply list_map_head in H_eq.
    rewrite self_lineage1 in H_eq.
    - simpl in H_eq.
    unfold value in H_eq.
    inversion H_eq.
    reflexivity.
    -
    eapply weaken_ok_type with (C:= D) (D := C).
    auto.
    exact H_ok_D.
    -
    eapply weaken_directed_ct.
    exact H_dir.
    - (* no_obj *)
    crush.
    }
    crush.
    + {
    destruct (A == D).
    -
    subst.
    unfold lineage in H_eq.
    fold lineage in H_eq.
    rewrite eq_atom_true in H_eq.
    rewrite eq_atom_false in H_eq.
    {
    apply list_map_head in H_eq.
    rewrite self_lineage1 in H_eq.
    - simpl in H_eq.
    unfold value in H_eq.
    inversion H_eq.
    symmetry in H0.
    contradiction.
    -
    eapply weaken_ok_type with (C:= C) (D := D).
    auto.
    exact H_ok_C.
    -
    eapply weaken_directed_ct.
    exact H_dir.
    - (* no_obj *)
    crush.
    }
    crush.
    -
    apply IHCT'.
    + (* no_obj *)
    crush.
    + (* directed *)
    eapply weaken_directed_ct.
    exact H_dir.
    + (* OK C *)
    eapply weaken_ok_type.
    exact n.
    exact H_ok_C.
    + (* OK D *)
    eapply weaken_ok_type.
    exact n0.
    exact H_ok_D.
    + (* Both <> A *)
    {
    unfold lineage in H_eq.
    fold lineage in H_eq.
    rewrite eq_atom_false in H_eq.
    rewrite eq_atom_false in H_eq.
    assumption.
    auto.
    auto.
    }
    }
Qed.

Lemma extends_lineage1 : forall CT C D,
    directed_ct CT ->
    Object \notin dom CT ->
    ok_type_ CT C ->
    ok_type_ CT D ->
    @extends_ CT C D ->
    C :: lineage CT D = lineage CT C.
Proof.
    intros CT0 C D H_dir H_noobj H_ok_C H_ok_D H_extends.
    induction CT0.
    +
    unfold lineage.
    destruct H_extends as [fs [ms H_binds]].
    exfalso.
    eapply binds_nil2.
    apply H_binds.
    +
    destruct a as [A [[B fs] ms]].
    (* Peel off A from CT in lineage (A _) :: CT D *)
    {
    unfold lineage at 1.
    fold lineage.
    destruct (A == D).
    + (* A = D is nonsense, *)
    subst.
    exfalso.
    inversion H_dir.
    subst.
    destruct H_extends as [fs' [ms' H_binds]].
    assert (H_neq : C <> D) by
        exact (directed_binds_unique ((D, (B, fs, ms)) :: CT0) C D
        fs' ms' H_noobj H_dir H_binds ).
    assert (binds C (D, fs', ms') CT0) by
        exact (binds_elim_neq H_neq H_binds).
    assert (H_ok_D2 : ok_type_ CT0 D) by
        exact (directed_binds C D fs' ms' CT0 H2 H).
    (* We have D ok in CT0 but also not in CT0 *)
    inversion H_ok_D2.
    * symmetry in H0. subst.
    simpl in H_noobj.  crush.
    * subst.  crush.
    + (* A <> D, peel it off *)
    rewrite eq_atom_false.



    (* Now peel off the extra from lineage C *)
    unfold lineage at 2.
    fold lineage.
    destruct (A == C).
    - subst.
    rewrite eq_atom_true.
    destruct H_extends as [fs' [ms' H_binds]].

    inversion H_binds.
    rewrite eq_atom_true in H0.
    inversion H0.
    subst.
    crush.
    -
    rewrite eq_atom_false.
    {
    apply IHCT0.
    - exact (weaken_directed_ct _ _ _ H_dir).
    - crush.
    - exact (weaken_ok_type _ _ _ _ n0 H_ok_C).
    - exact (weaken_ok_type _ _ _ _ n H_ok_D).
    -
    destruct H_extends as [fs' [ms' H_binds]].
    apply binds_elim_neq in H_binds.
    exists fs'.
    exists ms'.
    assumption.
    crush.
    }
    crush.
    - crush.
    }
Qed.

Lemma extends_lineage : forall CT C D,
    directed_ct CT ->
    @extends_ CT C D ->
    D \in lineage CT C.
Proof.
    intros.
    induction CT0.
    +
    unfold lineage.
    destruct H0 as [fs [ms H0]].
    exfalso.
    eapply binds_nil2.
    apply H0.
    +
    destruct a as [A [[B fs] ms]].
    unfold lineage.
    fold lineage.
    destruct (A == C).
    - subst.
    rewrite eq_atom_true.
    destruct H0 as [fs' [ms' H0]].

    inversion H0.
    rewrite eq_atom_true in H2.
    inversion H2.
    subst.
    unfold In.
    fold In.
    right.
    apply self_lineage.
    exact (weaken_directed_ct _ _ _ H).
    inversion H.
    subst.
    assumption.
    -
    rewrite eq_atom_false.
    apply IHCT0.
    crush.
    unfold extends_ in H0.
    destruct H0 as [fs' [ms' H_binds]].
    apply binds_elim_neq in H_binds.
    unfold extends_.
    exists fs'.
    exists ms'.
    assumption.
    crush.
    crush.
Qed.

Lemma lineage_composition: forall CT C D,
    directed_ct CT ->
    ok_type_ CT C ->
    ok_type_ CT D ->
    @sub_ CT C D ->
    exists xs,
    (xs ++ lineage CT D) = lineage CT C.
Abort.

Lemma extends_lineage_containment: forall CT C D,
    directed_ct CT ->
    Object \notin dom CT ->
    ok_type_ CT C ->
    ok_type_ CT D ->
    @extends_ CT C D ->
    forall E,
    E \in lineage CT D ->
    E \in lineage CT C.
Proof.
    clear.
    intros CT' C D H_dir H_noobj H_ok_C H_ok_D H_extends.
    induction CT'.
    -
    inversion H_ok_C.
    inversion H_ok_D.
    subst.
    crush.
    crush.
    crush.
    -
    destruct a as [A [[B fs] ms]].
    {
    destruct (A == C). destruct (A == D).
    - (* Both equal *)
    unfold lineage;  fold lineage.
    subst.
    crush.
    - (* A = C, A <> D *)
    unfold lineage;  fold lineage.
    subst.
    rewrite eq_atom_true.
    rewrite eq_atom_false; auto.
    intros E H.
    assert (H_binds : binds C (B, fs, ms) ((C, (B, fs, ms)) :: CT'0)) by
        apply binds_first.
    destruct H_extends as [fs' [ms' H_binds_D]].
    assert (H_eq : (B, fs, ms) = (D, fs', ms')) by
        apply (binds_fun H_binds H_binds_D).
    inversion H_eq.
    subst.
    crush.
    -
    subst.
    intros E H.
    rewrite <- extends_lineage1 with (D := D); crush.
    }
Qed.

Hint Resolve extends_lineage_containment.

Lemma subs_lineage_containment: forall CT C D,
    directed_ct CT ->
    Object \notin dom CT ->
    ok_type_ CT C ->
    ok_type_ CT D ->
    @sub_ CT C D ->
    forall E,
    E \in lineage CT D ->
    E \in lineage CT C.
Proof.
    clear.
    intros CT' C D H_dir H_noobj H_ok_C H_ok_D H_sub.
    induction H_sub.
    - (* sub_refl *)
    crush.
    - (* sub_trans *)
    intros E H_in.
    assert (ok_type_ CT' t2) by
        exact (directed_sub_ok CT' t1 t2 H_dir H_ok_C H_sub1).
    crush.
    - (* sub_extends *)
    intros.
    apply extends_lineage_containment with (D:= D); crush.
Qed.






Lemma lineage_subs: forall CT C D,
    directed_ct CT ->
    Object \notin dom CT ->
    ok_type_ CT C ->
    ok_type_ CT D ->
    D \in lineage CT C ->
    @sub_ CT C D.
Proof.
    intros CT' C D H_dir H_noobj H_ok_C H_ok_D H_lineage.
    induction CT'.
    { crush. }
    destruct a as [A [[B fs] ms]].
    destruct (A == C).
    -
    subst.
    simpl in H_lineage; rewrite eq_atom_true in H_lineage.
    inversion H_dir.
    subst.
    crush.
Abort.


(** ** Term expression typing *)

(** [typing E e t] holds when expression [e] has type [t] in environment [E].
    [wide_typing E e t] holds when [e] has a subtype of [t]. *)

Inductive typing : env -> exp -> typ -> Set :=
| t_var : forall v t E,
    ok E ->
    binds v t E ->
    typing E (e_var v) t
| t_field : forall E e0 t0 t f,
    typing E e0 t0 ->
    field t0 f t ->
    typing E (e_field e0 f) t
| t_meth : forall E E0 e0 b t0 t m es,
    typing E e0 t0 ->
    method t0 m (t,E0,b) ->
    wide_typings E es (imgs E0) ->
    typing E (e_meth e0 m es) t
| t_new : forall E C fs es,
    fields C fs ->
    wide_typings E es (imgs fs) ->
    typing E (e_new C es) C
(* Could use wide_typing in upcast, but not downcast or stupidcast.
   I kept the symmetry instead. *)
| t_upcast : forall E e0 C D,
    typing E e0 D ->
    sub D C ->
    typing E (e_cast C e0) C
| t_downcast : forall E e0 C D,
    typing E e0 D ->
    sub C D ->
    C <> D ->
    typing E (e_cast C e0) C
(* Stupid warning *)
| t_stupidcast : forall E e0 C D,
    typing E e0 D ->
    (~ sub C D) ->
    (~ sub D C) ->
    typing E (e_cast C e0) C

with wide_typing : env -> exp -> typ -> Set :=
| wt_sub : forall E e t t',
    typing E e t -> sub t t' -> wide_typing E e t'

with wide_typings : env -> list exp -> list typ -> Set :=
| wts_nil : forall E,
    ok E ->
    wide_typings E nil nil
| wts_cons : forall E E0 es e t,
    wide_typings E es E0 ->
    wide_typing E e t ->
    wide_typings E (e::es) (t::E0).

Hint Constructors typing wide_typing wide_typings.

Fixpoint has_downcast (E':env) (e':exp) (t':typ) (type : typing E' e' t') : bool := (match type with
| t_var _ _ _ _ _ =>
        true
| t_field E e0 t0 t f H_typing H_field =>
        has_downcast E e0 t0 H_typing
| t_meth E E0 e0 b t0 t m es H_typing H_method H_wts =>
        andb (has_downcast E e0 t0 H_typing)
             (wide_typings_has_downcast E es (imgs E0) H_wts)
| t_new E C fs es H_fields H_wts =>
        wide_typings_has_downcast E es (imgs fs) H_wts
| t_upcast E e0 C D H_typing H_sub =>
        has_downcast E e0 D H_typing
| t_downcast _ _ _ _ _ _ _ =>
        false
| t_stupidcast _ _ _ _ _ _ _ =>
        false
end)
with wide_typing_has_downcast E e t (type: wide_typing E e t) : bool
:= match type with
| wt_sub E e t t' H_typing H_sub =>
        has_downcast E e t H_typing
end
with wide_typings_has_downcast E es ts (type: wide_typings E es ts) : bool
:= match type with
| wts_nil E H_ok =>
        true
| wts_cons E E0 es e t H_wts H_wt =>
        andb (wide_typing_has_downcast E e t H_wt)
        (wide_typings_has_downcast E es E0 H_wts)
end.

(* REL operator *)

Section REL.
(* Variables (CT_A : ctable) (CT_L : ctable). *)

(* This has to be exp_ true, as they show up on the right side of REL *)
Variable LPT : list (exp_ true).

Inductive REL : (exp_ false) -> (exp_ true) -> Prop :=
| rel_field : forall (e : exp_ false) (e' : exp_ true) f,
    REL e e' ->
    REL (e_field e f) (e_field e' f)
| rel_lib_field : forall (e : exp_ false) f,
    REL e e_lib ->
    
    (* TODO (declaring_class f) \in CT_L -> *)
    REL (e_field e f) e_lib
| rel_new : forall C
        (es : list(exp_ false))
        (e's : list(exp_ true)),
    Forall2 REL es e's ->
    C \in dom CT' ->
    REL (e_new C es) (e_new C e's)
| rel_new_obj :
    REL (e_new Object nil) (e_new Object nil)
| rel_lib_new : forall (C : cname)
        (es : list(exp_ false)),
    Forall (fun e => REL e e_lib) es ->
    C \in (dom CT_L) ->
    REL (e_new C es) e_lib
| rel_invk : forall m e es e' e's,
    REL e e' ->
    Forall2 REL es e's ->
    REL (e_meth e m es) (e_meth e' m e's)
| rel_lib_invk : forall m e es,
    REL e e_lib ->
    Forall (fun e => REL e e_lib) es ->
    (* TODO  clean this up. *)
    (exists C D fs (ms : mths),
        binds C (D, fs, ms) CT_L /\ m \in (dom ms)) ->
    REL (e_meth e m es) e_lib
| rel_cast : forall C e e',
    REL e e' ->
    REL (e_cast C e) (e_cast C e')
| rel_lib_cast : forall C e,
    REL e e_lib ->
    REL (e_cast C e) (e_lib)
| rel_ltp : forall e e',
    REL e e' ->
    e' \in LPT ->
    REL e e_lib.

End REL.



(** ** Declaration typing *)

(** [ok_meth C D m t E e] holds when [(t, E, e)] is a valid method declaration
    for method [m] in class [C] with parent [D]. *)

Definition can_override (D: cname) (m: mname) (t: typ) (E: env) : Prop :=
    (*EDIT2 BEGIN*)
    (*forall t' E' e, method D m (t',E',e) -> sub t t' /\ imgs E = imgs E'.*)
    forall t' E' e, method D m (t',E',e) -> t = t' /\ imgs E = imgs E'.
    (*EDIT2 END*)

Hint Unfold can_override.

Definition ok_meth (C D: cname) (m: mname) (t: typ) (E: env) (e: exp) : Prop :=
    can_override D m t E /\ (exists wt, wt = wide_typing ((this,C)::E) e t).

Hint Unfold ok_meth.

(** [ok_class C D fs ms] holds when it is valid to define class [C] with parent
    [D], fields [fs] and methods [ms]. *)

Definition ok_meth' (C D: cname) (m : mname) (v : typ * env * exp) : Prop :=
    match v with (t,E,e) => ok_meth C D m t E e end.

Definition ok_class (C: cname) (D: cname) (fs: flds) (ms: mths) : Prop :=
    (*EDIT1 BEGIN*)
    (*(forall fs', fields D fs' -> ok (fs' ++ fs)) /\*)
    (exists fs', fields D fs' /\ ok (fs' ++ fs)) /\
    (*EDIT1 END*)
    ok ms /\
    forall_env (ok_meth' C D) ms.

Hint Unfold ok_class.

(** [ok_ctable ct] holds when [ct] is a well-formed class table. *)

Definition ok_class' (C: cname) (v : cname * flds * mths) : Prop :=
    match v with (D,flds,mths) => ok_class C D flds mths end.

Definition ok_ctable ct := ok ct /\ forall_env ok_class' ct.

Hint Unfold ok_ctable.

(** ** Term substitution *)

(** [subst_exp E e] returns the term expression [e] where any occurrances of
    bound variables have been replaced by their bindings in environment [E]. *)
Fixpoint subst_exp {b:bool} (E : (list (var * exp_ b))) (e : exp_ b) {struct e} : exp_ b :=
    match e in exp_ b return list (var * exp_ b) -> exp_ b with
    | e_var _ v => fun E =>
        match Metatheory.get v E with
        | Some e' => e'
        | None => e_var v
        end
    | e_field _ e0 f => fun E => e_field (subst_exp E e0) f
    | e_meth _ e0 m es => fun E => e_meth (subst_exp E e0) m (List.map (subst_exp E) es)
    | e_new _ C es => fun E => e_new C (List.map (subst_exp E) es)
    | e_cast _ C e => fun E => e_cast C (subst_exp E e)
    | e_lib => fun E => e_lib
    end E.

(** * Evaluation *)

(** ** Evaluation contexts *)

(** We model evaluation contexts as functions of type [exp -> exp].
    [exp_context EE] holds if [EE] is an evaluation context. Basically, any
    subexpression of an expression is an evaluation context. **)

Inductive exps_context : (exp -> list exp) -> Prop :=
| esc_head : forall es,
    exps_context (fun e => e::es)
| esc_tail : forall e EE,
    exps_context EE ->
    exps_context (fun e0 => e::(EE e0)).

Inductive exp_context : (exp -> exp) -> Prop :=
| ec_field_arg0 : forall f,
    exp_context (fun e0 => e_field e0 f)
| ec_meth_arg0 : forall m es,
    exp_context (fun e0 => e_meth e0 m es)
| ec_meth_args : forall m e0 EE,
    exps_context EE ->
    exp_context (fun e => e_meth e0 m (EE e))
| ec_new_args : forall C EE,
    exps_context EE ->
    exp_context (fun e => e_new C (EE e))
| ec_cast_arg0 : forall C,
    exp_context (fun e0 => e_cast C e0).

Hint Constructors exp_context exps_context.

(** ** Evaluation *)

(** [eval e e'] holds when term expression [e] reduces to [e'] in one step. *)

Inductive eval : exp -> exp -> Prop :=
| eval_field : forall C fs es f e fes,
    fields C fs ->
    env_zip fs es fes ->
    binds f e fes ->
    eval (e_field (e_new C es) f) e
| eval_meth : forall C m t E e es ves es0,
    method C m (t,E,e) ->
    env_zip E es ves ->
    eval (e_meth (e_new C es0) m es) (subst_exp ((this,(e_new C es0))::ves) e)
| eval_cast : forall C D fs,
    sub C D ->
    eval (e_cast D (e_new C fs)) (e_new C fs)
| eval_context : forall EE e e',
    eval e e' ->
    exp_context EE ->
    eval (EE e) (EE e').

Hint Constructors eval.
(* Help Coq to eapply eval_context rule ("Meta cannot occur in evar body") *)
Hint Extern 2 (eval (e_field _ ?f) _) => eapply (eval_context (fun e0 => e_field e0 f)).
Hint Extern 2 (eval (e_meth _ ?m ?es) _) => eapply (eval_context (fun e0 => e_meth e0 m es)).
Hint Extern 2 (eval (e_meth ?e0 ?m (?EE _)) _) => eapply (eval_context (fun e => e_meth e0 m (EE e))).
Hint Extern 2 (eval (e_new ?C (?EE _)) _) => eapply (eval_context (fun e => e_new C (EE e))).

(** * Properties *)

(** We conclude the definition of the calculus with a definition of the safety
    properties that are proven in the other parts of the development. *)

(** [value e] holds when the term expression [e] represents a value. Values are
    terms that consist only of [e_new] expressions. *)

Inductive value : exp -> Prop :=
| value_new : forall cn es,
    (forall e, In e es -> value e) -> value (e_new cn es).

Hint Constructors value.

Definition libify {A} : list A -> list exp_l := (List.map (fun _ => e_lib)).

Reserved Notation "A ->> B" (no associativity, at level 50).

Inductive Ave_Reduce : (exp_l * list exp_l) -> (exp_l * list exp_l) -> Prop :=
| ra_fj :  forall e e' (LPT : list exp_l),
     eval e e' ->
     (embed_exp e, LPT) ->> (embed_exp e', LPT)
| ra_field : forall C d f LPT,
    C \in dom CT_L' ->
    declares_f C f ->
    (d, LPT) ->> (d, (e_field e_lib f) :: LPT)
| ra_new : forall C d LPT,
    C \in dom CT_L' ->
    (d, LPT) ->> (d, (e_new C (libify (constructor C))) :: LPT)
| ra_invk : forall C m t e env d LPT,
    C \in dom CT_L' ->
    (* TODO Duplicate hyps ? *)
    declares_m C m ->
    method C m (t, env, e) ->
    (d, LPT) ->> (d, (e_meth e_lib m (libify env) :: LPT))
| ra_cast : forall C LPT,
    (e_cast C e_lib, LPT) ->> (e_lib, LPT)
| ra_lib_invk : forall C m es ds LPT,

    (* TODO mresolve ...? *)
    (e_meth (e_new C es) m ds, LPT) ->> (e_lib, (e_new C es) :: ds ++ LPT)
| ra_return : forall e LPT,
    e \in LPT ->
    (e_lib, LPT) ->> (e, LPT)
| ra_sub : forall d e e' LPT LPT',
    e \in LPT ->
    (e, LPT) ->> (e', LPT') ->
    (d, LPT) ->> (d, e' :: LPT ++ LPT')
| rac_field : forall f e e' LPT LPT',
    (e, LPT) ->> (e', LPT') ->
    (e_field e f, LPT) ->> (e_field e' f, LPT ++ LPT')
| rac_invk_recv : forall m e e' es LPT LPT',
    (e, LPT) ->> (e', LPT') ->
    (e_meth e m es, LPT) ->> (e_meth e' m es, LPT ++ LPT')
| rac_invk_arg : forall m e elo ei ei' ehi LPT LPT',
    (ei, LPT) ->> (ei', LPT') ->
    (e_meth e m (elo ++ ei  :: ehi), LPT) ->>
    (e_meth e m (elo ++ ei' :: ehi), LPT ++ LPT')
| rac_new_arg : forall C elo ei ei' ehi LPT LPT',
    (ei, LPT) ->> (ei', LPT') ->
    (e_new C (elo ++ ei  :: ehi), LPT) ->>
    (e_new C (elo ++ ei' :: ehi), LPT ++ LPT')
| rac_cast : forall C e e' LPT LPT',
    (e, LPT) ->> (e', LPT') ->
    (e_cast C e, LPT) ->> (e_cast C e', LPT ++ LPT')
    where "A ->> B" := (Ave_Reduce A B).





(* Proof of Averroes things *)

Lemma ancestor_in_CT_A : forall A C,
    A \in lineage CT C ->
    A \in dom CT_A ->
    C \in dom CT_A.
Proof.
    intros A C H H_CT_A.
    assert (H_ok : ok CT). apply directed_is_ok; assumption.
    unfold CT in *|- *.

    assert (H_A_not_CT_L : A \notin dom CT_L).
        unfold not.
        intros H_CT_L.
        apply dom_binds in H_CT_A.
        apply dom_binds in H_CT_L.
        induction H_CT_A as [x H_binds_CT_A].
        induction H_CT_L as [y H_binds_CT_L].
        absurd (A = A).
        exact (ok_disjoint_app H_binds_CT_A H_binds_CT_L H_ok).
        reflexivity.

    induction CT_A.
    unfold dom in H_CT_A.
    unfold keys in H_CT_A.
    simpl in H_CT_A.
    exfalso; assumption.
    destruct a as [B p].
    destruct (B == C).
    subst.



Abort.
Lemma mresolve_cases : forall CT m C C' D,
    forall (H_directed_ct : directed_ct CT),
    extends_ CT C D ->

    @mresolve CT H_directed_ct m C = Some C' ->
      C = C' \/ @mresolve CT H_directed_ct m D = Some C'.
Proof.
    clear.
    intros.
    unfold extends_ in H.
    destruct H as [fs [ms H_binds]].
    
Abort.

Definition length_of_class_chain : forall CT C
    (H_dir : directed_ct CT)
    (H_noobj : Object \notin dom CT)
    (H_ok :  ok_type_ CT C), nat.
Proof.
    clear.
    intros.
    generalize C H_ok.
    clear C H_ok.
    refine(
    @ClassTable_rect CT0 (fun (C: cname) => nat)
    H_dir H_noobj
    (* P Obj *) ((fun _: cname => 0) Object)
    (* P ind *) (fun (C D: cname) fs ms H_ok H_binds P_D => 1 + P_D)
    ).
Defined.

Lemma zero_ancestors_object : forall CT
    (H_dir : directed_ct CT)
    (H_noobj : Object \notin dom CT),
    length_of_class_chain CT Object
    H_dir H_noobj (ok_obj CT) = 0.
Proof.
    intros.
    unfold length_of_class_chain.
    apply (ClassTable_obj_inv
    CT0
    H_dir
    H_noobj
    (fun _ : cname  => nat)
    0
    (fun (C D : cname) (fs : flds) (ms : mths) (_ : ok_type_ CT0 D)
     (_ : binds C (D, fs, ms) CT0) (P_D : nat) => 1 + P_D)
    (ok_obj CT0)).
Qed.


Lemma mresolve2_Object_None : forall CT m
    (H_dir : directed_ct CT)
    (H_noobj : Object \notin dom CT),
    @mresolve2 CT m H_dir H_noobj Object (ok_obj CT) = None.
Proof.
    clear.
    intros.
    unfold mresolve2.
    apply (ClassTable_obj_inv
    CT0
    H_dir
    H_noobj
    (fun _ : cname  => option cname)
    None
    (fun (C D : cname) (fs : flds) (ms : mths) (_ : ok_type_ CT0 D)
    (_ : binds C (D, fs, ms) CT0) (P_D : option cname) =>
    match get m ms with
    | Some _ => Some C
    | None => P_D
    end)
    (ok_obj CT0)).
Qed.

Lemma mresolve3_result_in_CT : forall CT (m:mname) C D,
    directed_ct CT ->
    mresolve3 CT C m D ->
    D \in dom CT.
Proof.
    clear.
    intros CT m C D H_dir.
    generalize C.  clear C.
    induction CT.
    -
    intros C H_mres.
    exfalso.
    inversion H_mres.
    -
    intros C H_mres.
    destruct a as [A [[B fs] ms]].
    assert (H_dir' : directed_ct CT0) by
        exact (weaken_directed_ct _ _ _ H_dir).
    {
    inversion H_mres.
    - subst. crush.
    - subst.
    rename H8 into H_mres'.
    simpl.
    right.
    exact (IHCT H_dir' B H_mres').
    -
    subst.
    rename H8 into H_mres'.
    simpl.
    right.
    exact (IHCT H_dir' C H_mres').
    }
Qed.


Lemma mresolve3_subclass : forall CT (m:mname) C D,
    (* directed_ct CT -> *)
    mresolve3 CT C m D ->
    sub_ CT C D.
Proof.
    clear.
    intros CT m C D.
    generalize C; clear C.
    induction CT.
    -
    intros.
    inversion H.
    -
    {
    intros C H_mres.
    inversion H_mres.
    -
    subst.
    crush.
    - subst.
    apply (sub_trans _ C D0 D).
    apply sub_extends.
    +
    unfold extends_.
    exists fs.
    exists ms.
    auto.
    +
    assert ((sub_ CT0) D0 D) by auto.

| sub_trans : forall t1 t2 t3, sub_ CT t1 t2 -> sub_ CT t2 t3 -> sub_ CT t1 t3






Lemma mresolve3_in_CT_A : forall CT_A CT_L (m:mname) C D,
    directed_ct (CT_A ++ CT_L) ->
    mresolve3 (CT_A ++ CT_L) C m D ->
    D \in dom CT_A ->
    C \in dom CT_A.
Proof.
    clear.
    intros CT_A CT_L.
    intros m C D H_dir H_mres H_D_in.
    induction CT_A.
    - exfalso.
    crush.
    -
    destruct a as [A [[B fs] ms]].
    assert (H_dir': directed_ct (CT_A0 ++ CT_L)) by
        exact (weaken_directed_ct _ _ _ H_dir).
    inversion H_mres.
    + crush.
    + crush.
    + subst.
    rename H8 into H_mres'.
    simpl.
    right.
    assert (IH: D \in dom CT_A0 -> C \in dom CT_A0) by auto .
    clear IHCT_A.
    apply IH.
    app
    {
    destruct (D == A).
    -
    subst.
    
    refine (mresolve3_result_in_CT _ _ _ _ _ _).
    exfalso.
    (* Contradiction as CT_A0 no longer contains A,
    * and CT_L doesn't contain A, so we'll never resolve m to A. *)
    

    (* This is false because in order for
Qed.



Lemma mresolve_in_CT_A (C : cname) : forall (m:mname) C'
    (H_ok : ok_type_ CT C),
    @mresolve2 CT m CT_is_directed CT_nocontains_obj
                  C H_ok
                  = Some C' ->
    C' \in dom CT_A ->
    C \in dom CT_A.
Proof.
    eapply (@ClassTable_rect CT
    (fun D:cname =>
     forall (m : mname) (C' : cname) H_ok',
        mresolve2 CT m D H_ok' = Some C' ->
        C' \in dom CT_A ->
        D \in dom CT_A
)).
    - exact CT_is_directed.
    - (* Object \notin dom CT *)
    exact CT_nocontains_obj.
    - (* mresolve to Object is absurd *)
    intros.
    unfold mresolve2 in H.
    admit.
    - (* Inductive case *)
    intros.
    clear C.
    rename C0 into C.
    (* mresolve m C = Some C' ->
    *  C = C' /\  ... 
    * \/ mresolve m D = Some C'





















End GenericOverLib.

(** The following module defines the hypotheses of the safety argument. We
    assume that [Object] is not defined in the class table [CT] and that class
    table [CT] is well-formed. *)

Module Type Hyps.
    Parameter with_lib : bool.
    Parameter ct_noobj: Object \notin dom (CT with_lib).
    Parameter ok_ct: ok_ctable with_lib (CT with_lib).
End Hyps.

(** Safety of the language may be demonstrated through an implementation of the
    following module type: given the above hypotheses, it provides the
    properties of preservation and progress. *)

Module Type Safety (H: Hyps).
    Parameter preservation: forall E e e' t,
        typing E e t ->
        eval e e' ->
        wide_typing E e' t.

    Parameter progress: forall e t,
        typing nil e t ->
        value e \/ (exists e', eval e e').
End Safety.
*)
