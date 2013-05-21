Require Export preservation.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ (exists t', R t t').

Notation reduction_normal_form := (normal_form reduction).

Definition stuck (t:term) : Prop :=
  reduction_normal_form t /\ ~ bool_value t.

Hint Unfold stuck.


Check refl_step_closure.
Check relation.
Check reduction.

Definition reductionmany := (refl_step_closure reduction).
Notation "t1 '==>*' t2" := (reductionmany t1 t2) (at level 40).


Corollary soundness_type_system : forall t t' Ty,
                                    has_Type t Ty ->
                                    t ==>* t' ->
                                    ~ (stuck t').

Proof.
intros t t' T HT P.
induction P; intros [R S].
destruct (progress x T HT); auto.
apply IHP.
apply (preservation x y T HT H).
unfold stuck.
split.
auto.
auto.
Qed.

