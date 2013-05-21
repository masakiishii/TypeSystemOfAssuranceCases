Require Export SfLib.

Inductive T : Type :=
 | T_Bool : T
 | T_Env : T
 | T_Fun : T -> T -> T.


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
 | term_Var           : id -> term
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
 |Case_aux c "term_Var"
 |Case_aux c "term_Function" ].


Inductive bool_value : term -> Prop :=
 | b_true : bool_value term_Valid_Claim
 | b_false : bool_value term_Invalid_Claim.

Hint Constructors bool_value.

Fixpoint subst (s:term) (x:id) (t:term) : term :=
 match t with
  | term_Valid_Claim => term_Valid_Claim
  | term_Invalid_Claim => term_Invalid_Claim
  | term_Evidence => term_Evidence
  | term_Undeveloped => term_Undeveloped
  | term_Condition t => term_Condition t
  | term_Intersection t1 t2 => term_Intersection t1 t2
  | term_Supported t => term_Supported t
  | term_Strategy t => term_Strategy t
  | term_Alternative t1 t2 => term_Alternative t1 t2
  | term_Var x => term_Var x
  | term_Function x' Ty t1 => term_Function x' Ty (subst s x t1)
 end.


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
 | E_FUN : forall t t' x x' Ty, t ==> t' -> (term_Function x' Ty (term_Var x)) ==> t'

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
 | Case_aux c "E_SPE"
 | Case_aux c "E_FUN"].



Hint Constructors reduction.

(* Define Gamma Environment *)
Definition context := partial_map T.

Module Context.

Definition partial_map (A:Type) := id -> option A.
Definition empty {A:Type} : partial_map A := (fun _ => None).
Definition extend {A:Type}  (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if beq_id x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
   (extend ctxt x T) x = Some T.
Proof.
intros.
unfold extend.
rewrite <- beq_id_refl.
auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
 beq_id x2 x1 = false ->
      (extend ctxt x2 T) x1 = ctxt x1.
Proof.
intros.
unfold extend.
rewrite H.
auto.
Qed.

End Context.


Inductive has_Type : context -> term -> T -> Prop :=
 | T_TRE : has_Type empty term_Valid_Claim T_Bool
 | T_FLS : has_Type empty term_Invalid_Claim T_Bool
 | T_EVI : has_Type empty term_Evidence T_Bool
 | T_UND : has_Type empty term_Undeveloped T_Bool
 | T_CON : forall t, has_Type empty term_Evidence T_Bool ->
                     has_Type empty t T_Bool ->
                     has_Type empty (term_Condition t) T_Bool
 | T_INS : forall t1 t2 Ty, has_Type empty t1 Ty ->
                            has_Type empty t2 Ty ->
                            has_Type empty (term_Intersection t1 t2) Ty
 | T_SUP : forall t Ty, has_Type empty t Ty ->
                        has_Type empty (term_Supported t) Ty
 | T_STR : forall t Ty, has_Type empty t Ty ->
                        has_Type empty (term_Strategy t) Ty
 | T_SPE : forall t1 t2 Ty, has_Type empty t1 Ty ->
                            has_Type empty t2 Ty ->
                            has_Type empty (term_Alternative t1 t2) Ty
 | T_VAR : forall Gamma x Ty, Gamma x = Some Ty ->
                              has_Type Gamma (term_Var x) Ty
 | T_FUN : forall Gamma x T11 T12 t12,
             has_Type (extend Gamma x T11) t12 T12 ->
             has_Type Gamma (term_Function x T11 t12) (T_Fun T11 T12).


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
 | Case_aux c "T_SPE"
 | Case_aux c "T_VAR"
 | Case_aux c "T_FUN"].


Hint Constructors has_Type.

(* ----- <<< Define Closed Variable >>>------*)
Inductive appears_free_in : id -> term -> Prop :=
 | afi_Var : forall x, appears_free_in x (term_Var x)
 | afi_Function : forall x y T11 t12, y <> x ->
                                      appears_free_in x t12 ->
                                      appears_free_in x (term_Function y T11 t12).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
 first;
 [Case_aux c "afi_Var"
 |Case_aux c "afi_Function"]. 

Hint Constructors appears_free_in.

Definition closed (t:term) := forall x, ~ appears_free_in x t.

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
