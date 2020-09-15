From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
Import ListNotations.

Fixpoint filter_le (pivot : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xl => if x <=? pivot
               then x :: filter_le pivot xl
               else filter_le pivot xl
  end.

Fixpoint filter_gt (pivot : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xl => if x <=? pivot
               then filter_gt pivot xl
               else x :: filter_gt pivot xl
  end.

Fixpoint quicksort_core (length_upper_bound : nat)
                        (l : list nat)
                        : list nat :=
  match length_upper_bound with
  | O => []
  | S lub => match l with
             | [] => []
             | x :: xl => quicksort_core lub (filter_le x xl) ++
                          [x] ++
                          quicksort_core lub (filter_gt x xl)
             end
  end.

Definition quicksort (l : list nat) : list nat :=
  quicksort_core (length l) l.

Example qs_test_1 : quicksort [5;3;4;2;6;1] = [1;2;3;4;5;6].
Proof. reflexivity. Qed.

Example qs_test_2 : quicksort [] = [].
Proof. reflexivity. Qed.

Example qs_test_3 : quicksort [1;1;1;1;1] = [1;1;1;1;1].
Proof. reflexivity. Qed.