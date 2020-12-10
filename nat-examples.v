Goal forall (a b c : nat), a = b -> b = c -> a = c.
Proof.
  intros.
  rewrite -> H.
  auto.
Qed.

Goal exists n : nat, forall m : nat, exists q : nat, m = n * q.
Proof.
  exists 1.
  intros.
  exists m.
  simpl.
  rewrite <- plus_n_O.
  reflexivity.
Qed.

Goal forall (P : nat -> Prop),
     (forall (a b : nat), P a -> P b -> P (a + b)) ->
     (P 0) ->
     (P 1) ->
     (forall n : nat, P n).
Proof.
  induction n.
  - apply H0.
  - apply H with (a := 1).
    + apply H1.
    + apply IHn.
Qed.