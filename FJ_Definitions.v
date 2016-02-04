
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

Section GenericOverLib.
Variable with_lib : bool.

Definition exp := exp_ with_lib.

Definition env := (list (var * typ)).
Definition benv := (list (var * exp)).

(** [flds] and [mths] map the names of fields and methods to their
    definitions. *)

Definition flds := (list (fname * typ)).
Definition mths := (list (mname * (typ * env * exp))).

(** [ctable] maps the names of classes to their definitions. A class definition
    consists of a parent class and a number of fields and methods. *)

Definition ctable := (list (cname * (cname * flds * mths))).

(** We assume a fixed class table [CT]. *)

Parameter CT_A : ctable.
Parameter CT_L : ctable.

Definition CT := CT_A ++ CT_L.


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

Inductive directed_ct : ctable -> Prop :=
| directed_ct_nil : directed_ct nil
| directed_ct_cons :
        forall (C D : cname) (fs : flds) (ms: mths) (ct : ctable),
        directed_ct ct ->
        C \notin (keys ct) -> (* No duplicate bindings *)
        (D \in (keys ct) \/ D = Object) ->    (* No forward references *)
        directed_ct ((C, (D, fs, ms)) :: ct).

Hint Constructors directed_ct.


Lemma weaken_directed_ct : forall x v ct,
    directed_ct ((x, v) :: ct) ->
    directed_ct ct.
Proof.
    intros.
    inversion H.
    assumption.
Qed.

Example no_self_inheritance : forall CT : ctable,
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
    destruct H2.
    * (* D \in key ct. *)
    rewrite H4 in H2.
    contradiction.
    * (* D = Object. *)
    subst.
    rewrite dom_distribute_cons in ct_noobj.
    apply not_in_split in ct_noobj.
    subst.
    absurd (Object = Object); auto.
    apply ct_noobj.

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

Example lineage_test : forall A B C D : cname,
    lineage ((A, (B, nil, nil)) ::
             (B, (C, nil, nil)) ::
             (C, (D, nil, nil)) :: nil ) A = A :: B :: C :: D :: nil.
Proof.
    intros.
    simpl.
    rewrite eq_atom_true.
    rewrite eq_atom_true.
    rewrite eq_atom_true.
    reflexivity.
Qed.

Fixpoint method_lookup_helper (CT: ctable) (m:mname) (ancestors: list cname) :=
    match ancestors with
    | nil => None
    | C :: Cs => match Metatheory.get C CT with
        | None => (* impossible *) None
        | Some (_, _, ms) => match Metatheory.get m ms with
            | None => method_lookup_helper CT m Cs
            | Some (v) => Some (v)
            end
        end
    end.

Definition mtype_lookup {CT : ctable} {H: directed_ct CT}  (m:mname) (C:cname) :
    option (list typ * typ) :=
    match method_lookup_helper CT m (lineage CT C) with
    | None => None
    | Some (R, env, _) => Some ((List.map (snd (A:=mname) (B:=typ)) env), R)
    end.

Definition mbody_lookup {CT : ctable} {H: directed_ct CT} (m:mname) (C:cname) :
    option (env * exp) :=
    match method_lookup_helper CT m (lineage CT C) with
    | None => None
    | Some (R, env, body) => Some (env, body)
    end.

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


(** * Typing *)

(** ** Well-formed types *)

(** [ok_type t] holds when [t] is a well-formed type. *)

Inductive ok_type : typ -> Prop :=
| ok_obj: ok_type Object
| ok_in_ct: forall t, t \in dom CT -> ok_type t.

Hint Constructors ok_type.

(** ** Subtyping *)

(** [extends C D] holds if [C] is a direct subclass of [D]. *)

Definition extends (C D : cname) : Prop :=
    exists fs, exists ms, binds C (D,fs,ms) CT.

Hint Unfold extends.

(** [sub s u] holds if [s] is a subtype of [u]. The subtype relation is the
    reflexive, transitive closure of the direct subclass relation. *)

(* (S-Ref) (S-Trans) (S-Sub) are defined here. *)

Inductive sub : typ -> typ -> Prop :=
| sub_refl : forall t, sub t t
| sub_trans : forall t1 t2 t3, sub t1 t2 -> sub t2 t3 -> sub t1 t3
| sub_extends : forall C D, extends C D -> sub C D.

Hint Constructors sub.

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

(* TODO Libify *)
Definition CT' := CT_A ++ CT_L.
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
    | e_field _ e0 f => fun _ => e_field (subst_exp E e0) f
    | e_meth _ e0 m es => fun _ => e_meth (subst_exp E e0) m (List.map (subst_exp E) es)
    | e_new _ C es => fun _ => e_new C (List.map (subst_exp E) es)
    | e_cast _ C e => fun _ => e_cast C (subst_exp E e)
    | e_lib => fun _ => e_lib
    end.

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
End GenericOverLib.

(** The following module defines the hypotheses of the safety argument. We
    assume that [Object] is not defined in the class table [CT] and that class
    table [CT] is well-formed. *)

Module Type Hyps.
    Parameter ct_noobj: Object \notin dom CT.
    Parameter ok_ct: ok_ctable CT.
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
