
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
    | e_var _ v => e_var v
    | e_field _ o f => e_field (embed_exp o) f
    | e_meth _ o m args =>
            e_meth (embed_exp o) m (List.map embed_exp args)
    | e_new _ C args => e_new C (List.map embed_exp args)
    | e_cast _ C e => e_cast C (embed_exp e)
    | e_lib => e_lib
    end.

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

(** The way this is going to work is we have everything generic over CT,
 *  but with a _ suffix, and the a wrapper definition that uses CT without the suffix.
 *  When this section ends, we'll add a global parameter for a fixed CT,
 *  and define all the wrappers.
 *)

(** * The grand induction theorem *)

(** * Typing *)

(** ** Well-formed types *)

(** [ok_type_ t] holds when [t] is a well-formed type. *)

Inductive ok_type_ (CT:ctable) : typ -> Prop :=
| ok_obj: @ok_type_ CT Object
| ok_in_ct: forall C, C \in dom CT -> @ok_type_ CT C.

Hint Constructors ok_type_.

Lemma ok_subtable : forall CT C D p,
    D <> C ->
    @ok_type_ ((D, p) :: CT) C ->
    @ok_type_ CT C.
Proof.
    intros.
    destruct H0 as [|C]; crush.
Qed.

Hint Resolve ok_subtable.

Lemma ok_supertable : forall CT C D p,
    @ok_type_ CT C ->
    @ok_type_ ((D, p) :: CT) C.
Proof.
    intros.
    destruct H.
    - apply ok_obj.
    - apply ok_in_ct.
    crush.
Qed.
Hint Resolve ok_supertable.

Lemma ok_type_nil : forall C,
    ok_type_ nil C ->
    C = Object.
Proof.
    intros.
    inversion H.
    - reflexivity.
    - exfalso.
    crush.
Qed.

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

(* Always break down directed_ct (x :: xs) into some information about x
* and directed_ct xs.
*)
Hint Extern 1 (directed_ct ?x) =>
    match goal with
    | [ H: directed_ct (?x :: ?xs) |- _ ] => inversion H; subst
    end.

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
    apply ok_supertable.
    apply IHdirected_ct.
    eapply binds_elim_neq with (y:=C0).
    auto.
    exact H0.
Qed.

Hint Resolve directed_binds.

(** ** Subtyping *)

(** [extends C D] holds if [C] is a direct subclass of [D]. *)

Definition extends_ (CT:ctable) (C D : cname) : Prop :=
    exists fs, exists ms, binds C (D,fs,ms) CT.

Hint Unfold extends_.
Ltac unfold_extends :=
    match goal with
    | [ H: (extends_ ?CT ?C ?D) |- _] => destruct H as [?fs [?ms ?H_binds]]
    end.
Hint Extern 1 (extends_ _ _ _) => unfold_extends.
Ltac solve_binds_nil := 
    match goal with
    | [H: (binds ?C ?x ?nil) |- _] => exfalso; apply binds_nil2 in H; assumption
    end.
Hint Extern 1 (get _ nil = Some _) => solve_binds_nil.
Hint Extern 1 (binds _ _ _) => solve_binds_nil.



(** [sub s u] holds if [s] is a subtype of [u]. The subtype relation is the
    reflexive, transitive closure of the direct subclass relation. *)

(* (S-Ref) (S-Trans) (S-Sub) are defined here. *)

Inductive sub_ (CT:ctable) : typ -> typ -> Prop :=
| sub_refl : forall t, sub_ CT t t
| sub_trans : forall t1 t2 t3, sub_ CT t1 t2 -> sub_ CT t2 t3 -> sub_ CT t1 t3
| sub_extends : forall C D, @extends_ CT C D -> sub_ CT C D.

Hint Constructors sub_.

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
    apply ok_supertable.
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
    - assumption.
    - crush.
    - destruct H as [fs [ms H_binds]].
    eapply directed_ok.
    assumption.
    exact H_binds.
Qed.

Lemma ok_nil_object : forall C,
    ok_type_ nil C -> C = Object.
Proof.
    intros.
    destruct H.
    reflexivity.
    crush.
Qed.

Theorem ClassTable_rect {CT :ctable } : forall P : cname -> Type,
    directed_ct CT ->
    Object \notin dom CT ->
    P Object ->
    (forall (C D : cname) fs ms,
      ok_type_ CT D ->
      binds C (D, fs, ms) CT ->
      P D -> P C) ->
    (forall C: cname, ok_type_ CT C -> P C).
Proof.
    intros P H_directed_ct H_noobj H_Obj H_Ind C H_ok.
    generalize H_ok. clear H_ok.
    generalize C. clear C.
    induction CT as [| [D [[E fs] ms]] CT'].
    - (* nil *)
    intros C H_ok.
    assert (C = Object). apply ok_nil_object. assumption.
    subst.
    assumption.
    - (* cons *)
    intros C H_ok.
    destruct (D == C).
    + (* eq Going to use H_Ind *)
    subst.
    (* Plan: use H_Ind to solve, 
        as we can show P E by IHCT *)

    refine (H_Ind C E _ _ _ _ _).
    * (* E is OK because of directed_ct. *) {
    inversion H_directed_ct.
    subst.
    destruct H6.
    - (* is object *)
    subst.
    apply ok_obj.
    - (* in keys *)
    apply ok_in_ct.
    unfold dom.
    unfold keys.
    simpl.
    crush.
    }
    * (* weaken extends *) {
    unfold binds.
    simpl.
    rewrite eq_atom_true.
    reflexivity.
    }
    * (* Show (P E) by IHCT' *) {
        eapply IHCT'.
        - exact (weaken_directed_ct _ _ _ H_directed_ct).
        - (* object \notin dom CT *) {
        unfold not.
        intro H_Obj_In.
        unfold In in H_noobj.
        simpl in H_noobj.
        auto.
        }
        - (* smaller H_Ind *) {
        intros C0 D0 fs' ms' H_ok' H_binds H_D0.
        apply H_Ind with (D := D0) (fs0 := fs') (ms0 := ms').
        + (* ok_type D0 *)
        destruct H_ok'.
        * apply ok_obj.
        * apply ok_in_ct.
        apply in_cons.
        auto.
        + (* binds C0 (D0, fs', ms' _ *)
        destruct (C0 == C).
        (* eq *)
        subst.
        (* Contradiction , we've bound D twice, with D0 and E *)
        exfalso.
        inversion H_directed_ct.
        subst.
        apply binds_In in H_binds.
        contradiction.
        (* neq *)
        refine (binds_other _ _ _).
        auto.
        unfold not.
        intro.
        symmetry in H.
        contradiction H.
        +
        assumption.
        }
        - (* ok_type E *) {
        refine (_ (directed_ok _ C E fs ms H_directed_ct _)).
        + (* ok_type chaining *)
        assert (H_neq : E <> C). {
            refine (symmetry_neq
                (distinct_parent _ C E fs ms H_directed_ct _ _)).
            (* Object \notin CT *)
            assumption.
            (* binds *)
            apply binds_first.
        }
        intro H_ok_E.
        (* ok *)
        eapply ok_subtable.
        exact (symmetry_neq H_neq).
        exact H_ok_E.
        + (* binds *)
        apply binds_first.
        }
    }
    + (* neq  Going to use IHCT' as we've got a smaller CT now. *)
    apply IHCT'.
    * exact (weaken_directed_ct _ _ _ H_directed_ct).
    * (* Obj \notin CT *) crush.

    * (* Use H_Ind *)
    intros C0 D0 fs' ms' H_ok' H_binds H_D0.
    eapply H_Ind with (D0 := D0) (fs0 := fs') (ms0 := ms').
    destruct H_ok'.
    apply ok_obj.
    apply ok_in_ct.
    apply in_cons.
    auto.

    destruct (C0 == D).
    (* eq *)
    subst.
    (* Contradiction , we've bound D twice, with D0 and E *)
    exfalso.
    inversion H_directed_ct.
    subst.
    apply binds_In in H_binds.
    contradiction.
    (* neq *)
    refine (binds_other _ H_binds _).
    auto.

    assumption.
    * (* Last argument of IHCT' *)
    exact (ok_subtable _ _ _ _ n H_ok).
Defined.

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
    - eapply ok_subtable.
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
    eapply ok_subtable with (C:= D) (D := C).
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
    eapply ok_subtable with (C:= C) (D := D).
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
    eapply ok_subtable.
    exact n.
    exact H_ok_C.
    + (* OK D *)
    eapply ok_subtable.
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
    - exact (ok_subtable _ _ _ _ n0 H_ok_C).
    - exact (ok_subtable _ _ _ _ n H_ok_D).
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

Lemma mresolve2_Object_None : forall CT m
    (H_dir : directed_ct CT)
    (H_noobj : Object \notin dom CT),
    @mresolve2 CT m H_dir H_noobj Object (ok_obj CT) = None.
Proof.
    clear.
    intros.

    unfold mresolve2.
    unfold ClassTable_rect.
    (* What have I done .... *)
    simpl.
Abort.

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
