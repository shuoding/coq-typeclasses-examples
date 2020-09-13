From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
Import ListNotations.

Class Monoid (A : Type) : Type := {
  m_id : A;
  m_op : A -> A -> A;
  m_id_left : forall (a : A), m_op m_id a = a;
  m_id_right : forall (a : A), m_op a m_id = a;
  m_op_assoc : forall (a b c : A), m_op a (m_op b c) = m_op (m_op a b) c
}.

Fixpoint m_op_list {A : Type} `{Monoid A} (l : list A) : A :=
  match l with
  | [] => m_id
  | x :: xl => m_op x (m_op_list xl)
  end.

Instance nat_plus_monoid : Monoid nat := {
  m_id := 0;
  m_op := fun a b => a + b;
  m_id_left := Nat.add_0_l;
  m_id_right := Nat.add_0_r;
  m_op_assoc := Nat.add_assoc
}.

Instance list_app_monoid (A : Type) : Monoid (list A) := {
  m_id := [];
  m_op := @List.app A;
  m_id_left := @List.app_nil_l A;
  m_id_right := @List.app_nil_r A;
  m_op_assoc := @List.app_assoc A
}.

Example nat_list_ex : m_op_list [1;2;3] = 6.
Proof. reflexivity. Qed.

Example nat_list_list_ex : m_op_list [[1;2];[3]] = [1;2;3].
Proof. reflexivity. Qed.