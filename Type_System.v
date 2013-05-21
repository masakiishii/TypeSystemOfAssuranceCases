Require Export SfLib.

Inductive T : Type :=
 | T_Bool : T
 | T_Env : T.

Inductive term : Type :=
 | term_Valid_Claim   : term
 | term_Invalid_Claim : term
 | term_Evidence      : term
 | term_Undeveloped   : term
 | term_Condition     : term -> term
 | term_Intersection  : term -> term -> term
 | term_Supported     : term -> term
 | term_Strategy      : term -> term
 | term_Alternative   : term -> term -> term
 | term_Function      : id -> T -> term -> term.

Tactic Notation "term_cases" tactic(first) ident(c) :=
 first;
 [Case_aux c "term_Valid_Claim"
 |Case_aux c "term_Invalid_Calim"
 |Case_aux c "term_Evidence"
 |Case_aux c "term_Undeveloped"
 |Case_aux c "term_Condition"
 |Case_aux c "term_Intersection"
 |Case_aux c "term_Supported"
 |Case_aux c "term_Strategy"
 |Case_aux c "term_Alternative"
 |Case_aux c "term_Function" ].


Inductive bool_value : term -> Prop :=
 | true : bool_value term_Valid_Claim
 | false : bool_value term_Invalid_Claim
 | v_fun : forall x T t, bool_value (term_Function x T t).

Hint Constructors bool_value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive reduction : term -> term -> Prop :=
 | E_TRE : term_Evidence ==> term_Valid_Claim
 | E_FLS : term_Undeveloped ==> term_Invalid_Claim
 | E_IFT : (term_Condition term_Valid_Claim) ==> term_Evidence
 | E_IFF : (term_Condition term_Invalid_Claim) ==> term_Invalid_Claim
 | E_INTT : forall t, (term_Intersection term_Valid_Claim t) ==> t
 | E_INTF : forall t, (term_Intersection term_Invalid_Claim t) ==> term_Invalid_Claim
 | E_STRT : (term_Strategy term_Valid_Claim) ==> term_Valid_Claim
 | E_STRF : (term_Strategy term_Invalid_Claim) ==> term_Invalid_Claim
 | E_STR : forall t t', t ==> t' -> (term_Strategy t) ==> term_Supported t'
 | E_GOLT : (term_Supported term_Valid_Claim) ==> term_Valid_Claim
 | E_GOLF : (term_Supported term_Invalid_Claim) ==> term_Invalid_Claim
 | E_GOL : forall t t', t ==> t' -> (term_Supported t) ==> t'
 | E_IF : forall t t', t ==> t' -> (term_Condition t) ==> term_Condition t'
 | E_INS : forall t1 t1' t2, t1 ==> t1' -> (term_Intersection t1 t2) ==> term_Intersection t1' t2
 | E_SPT : forall t, term_Alternative term_Valid_Claim t ==> term_Valid_Claim
 | E_SPF : forall t, term_Alternative term_Invalid_Claim t ==> term_Supported t
 | E_SPE : forall t1 t1' t2, t1 ==> t1' -> (term_Alternative t1 t2) ==> term_Alternative t1' t2

where "t1 '==>' t2" := (reduction t1 t2).

(* | E_SPE2 : forall t1 t2' t2, t2 ==> t2' -> (term_Alternative t1 t2) ==> term_Alternative t1 t2'*)

Tactic Notation "reduction_cases" tactic(first) ident(c) :=
 first;
 [ Case_aux c "E_TRE"
 | Case_aux c "E_FLS"
 | Case_aux c "E_IFT"
 | Case_aux c "E_IFF"
 | Case_aux c "E_INTT"
 | Case_aux c "E_INTF"
 | Case_aux c "E_STR"
 | Case_aux c "E_STRT"
 | Case_aux c "E_STRF"
 | Case_aux c "E_GOLT"
 | Case_aux c "E_GOLF"
 | Case_aux c "E_GOL"
 | Case_aux c "E_IF"
 | Case_aux c "E_INS"
 | Case_aux c "E_SPT"
 | Case_aux c "E_SPF"
 | Case_aux c "E_SPE"].



Hint Constructors reduction.


Inductive has_Type : term -> T -> Prop :=
 | T_TRE : has_Type term_Valid_Claim T_Bool
 | T_FLS : has_Type term_Invalid_Claim T_Bool
 | T_EVI : has_Type term_Evidence T_Bool
 | T_UND : has_Type term_Undeveloped T_Bool
 | T_CON : forall t, has_Type term_Evidence T_Bool ->
                     has_Type t T_Bool ->
                     has_Type (term_Condition t) T_Bool
 | T_INS : forall t1 t2 Ty, has_Type t1 Ty ->
                            has_Type t2 Ty ->
                            has_Type (term_Intersection t1 t2) Ty
 | T_SUP : forall t Ty, has_Type t Ty ->
                        has_Type (term_Supported t) Ty
 | T_STR : forall t Ty, has_Type t Ty ->
                        has_Type (term_Strategy t) Ty
 | T_SPE : forall t1 t2 Ty, has_Type t1 Ty ->
                            has_Type t2 Ty ->
                            has_Type (term_Alternative t1 t2) Ty.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
 first;
 [ Case_aux c "T_TRE"
 | Case_aux c "T_FLS"
 | Case_aux c "T_EVI"
 | Case_aux c "T_UND"
 | Case_aux c "T_CON"
 | Case_aux c "T_INS"
 | Case_aux c "T_SUP"
 | Case_aux c "T_STR"
 | Case_aux c "T_SPE"].


Hint Constructors has_Type.


(* ------<<< Theorem progress >>>------ *)

Theorem progress : forall t Ty, has_Type t Ty -> bool_value t \/ exists t', t ==> t'.
Proof with auto.
intros.
has_type_cases (induction H) Case...
Case "T_EVI".
right.
exists term_Valid_Claim.
apply E_TRE.

Case "T_UND".
right.
exists term_Invalid_Claim.
apply E_FLS.

Case "T_CON".
right.
(*destruct IHhas_Type1.*)
destruct IHhas_Type2.
destruct H1.
exists term_Evidence.
apply E_IFT.
exists term_Invalid_Claim.
apply E_IFF.


destruct H1.
exists (term_Condition x).
apply E_IF.
auto.

Case "T_INS".
right.
destruct IHhas_Type1.
destruct H1.
SCase "T_INTT".
exists t2.
auto.

SCase "T_INTF".
exists term_Invalid_Claim.
auto.

destruct H1.
exists (term_Intersection x t2).
auto.

Case "T_SUP".
right.
destruct IHhas_Type.
destruct H0.

exists term_Valid_Claim.
auto.

exists term_Invalid_Claim.
auto.

destruct H0.
exists x.
auto.

Case "T_STR".
right.
destruct IHhas_Type.
destruct H0.
exists term_Valid_Claim.
auto.

exists term_Invalid_Claim.
auto.

inversion H0.
exists (term_Supported x).
auto.

Case "T_SPE".
right.
destruct IHhas_Type1.
destruct H1.
exists term_Valid_Claim.
auto.

exists (term_Supported t2).
auto.

inversion H1.
exists (term_Alternative x t2).
auto.

Qed.

Check progress.
