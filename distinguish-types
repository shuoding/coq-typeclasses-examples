Inductive T1 := | v1a | v1b.
Inductive T2 := | v2a | v2b | v2c.

Definition P (T : Set) : Prop :=
  exists (v1 v2 v3 : T), v1 <> v2 /\ v1 <> v3 /\ v2 <> v3.

Goal T1 <> T2.
Proof.
  unfold "<>".
  intros H.
  assert (H1 : ~ (P T1)). {
    unfold P. unfold not. intros H0.
    destruct H0 as [v1 [v2 [v3 [X [Y Z]]]]].
    destruct v1; destruct v2; destruct v3; congruence.
  }
  assert (H2 : P T2). {
    unfold P. exists v2a. exists v2b. exists v2c.
    split; try split; unfold "<>"; intros; discriminate.
  }
  rewrite -> H in H1. auto.
Qed.
