Definition even (n : nat) := exists k, n = k + k.
Definition odd (n : nat) := exists k, n = S (k + k).

Axiom double_negation : forall P, P = ~~P.

Lemma contrapositive : forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
Proof. intuition. Qed.

Lemma plus_n_0 : forall n, n + 0 = n.
Proof.
  intros n.
  induction n as [|n' IHn]. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma plus_n_Sm : forall n m, n + S m = S n + m.
Proof.
  intros n m.
  induction n as [|n' IHn]. reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma plus_commutative : forall n m, n + m = m + n.
Proof.
  intros n m.
  induction n as [|n' IHn]. rewrite plus_n_0. reflexivity.
  rewrite plus_n_Sm. simpl. rewrite IHn. reflexivity.
Qed.

Lemma plus_associative : forall n m o, (n + m) + o = n + (m + o).
Proof.
  intros n m o.
  induction n as [|n' IHn]. reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma plus_result_0 : forall n m, n + m = 0 <-> n = 0 /\ m = 0.
Proof.
  intros n m.
  split.
  - intros H.
    destruct n as [|n'] eqn : En.
    + destruct m as [|m'] eqn : Em.
      * split. reflexivity. reflexivity.
      * discriminate H.
    + discriminate H.
  - intros [Hl Hr].
    rewrite Hl, Hr.
    reflexivity.
Qed.

Lemma mult_n_0 : forall n, n * 0 = 0.
Proof.
  intros n.
  induction n as [|n' IHn]. reflexivity.
  simpl. apply IHn.
Qed.

Lemma mult_1_n : forall n, 1 * n = n.
Proof. intros n. simpl. rewrite plus_n_0. reflexivity. Qed.

Lemma mult_n_1 : forall n, n * 1 = n.
Proof.
  intros n.
  induction n as [|n' IHn]. reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma mult_n_Sm : forall n m, n * S m = n + n * m.
Proof.
  intros n m.
  induction n as [|n' IHn]. reflexivity.
  simpl. rewrite IHn.
  rewrite <- (plus_associative m n' _).
  rewrite (plus_commutative m n').
  rewrite (plus_associative n' m _).
  reflexivity.
Qed.

Lemma mult_commutative : forall n m, n * m = m * n.
Proof.
  intros n m.
  induction n as [|n' IHn]. rewrite mult_n_0. reflexivity.
  simpl. rewrite mult_n_Sm. rewrite IHn. reflexivity.
Qed.

Lemma mult_left_distributive : forall n m o, n * (m + o) = n * m + n * o.
Proof.
  intros n m o.
  induction n. reflexivity.
  simpl. rewrite IHn.
  rewrite (plus_associative m (n * m) _).
  rewrite <- (plus_associative (n * m) o (n * o)).
  rewrite (plus_commutative (n * m) o).
  rewrite (plus_associative o (n * m) _).
  rewrite (plus_associative m o _).
  reflexivity.
Qed.

Lemma mult_right_distributive : forall n m o, (n + m) * o = n * o + m * o.
Proof.
  intros n m o.
  induction o as [|o' IHo].
  - rewrite mult_n_0.
    rewrite (mult_n_0 n).
    rewrite (mult_n_0 m).
    reflexivity.
  - rewrite mult_n_Sm.
    rewrite (mult_n_Sm n).
    rewrite (mult_n_Sm m).
    rewrite IHo.
    rewrite (plus_associative n (n * o') _).
    rewrite <- (plus_associative (n * o') m _).
    rewrite (plus_commutative (n * o') m).
    rewrite (plus_associative m (n * o')).
    rewrite (plus_associative n m _).
    reflexivity.
Qed.

Lemma mult_associative : forall n m o, (n * m) * o = n * (m * o).
Proof.
  intros n m o.
  induction n. reflexivity.
  simpl. rewrite <- IHn. apply mult_right_distributive.
Qed.

Lemma mult_result_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros n m.
  split.
  - intros H.
    destruct n as [|n'] eqn : En.
    + left. reflexivity.
    + right. destruct m as [|m'] eqn : Em.
      * reflexivity.
      * simpl in H.
        discriminate H.
  - intros [Hl | Hr].
    + rewrite Hl. reflexivity.
    + rewrite Hr. apply mult_n_0.
Qed.

Lemma even_n__even_SSn : forall n, even n -> even (S (S n)).
Proof.
  intros n H.
  induction H.
  exists (S x).
  simpl.
  rewrite plus_n_Sm.
  rewrite H.
  reflexivity.
Qed.

Lemma odd_n__odd_SSn : forall n, odd n -> odd (S (S n)).
Proof.
  intros n H.
  induction H.
  exists (S x).
  simpl.
  rewrite plus_n_Sm.
  rewrite H.
  reflexivity.
Qed.

Lemma even_SSn__even_n : forall n, even (S (S n)) -> even n.
Proof.
  intros n H.
  induction H.
  assert(H' : exists k, x = S k). {
    induction x as [|x' IHx].
    - discriminate H.
    - exists x'. reflexivity.
  }
  destruct H' as [k H'].
  exists k.
  rewrite H' in H.
  rewrite plus_n_Sm in H.
  simpl in H.
  inversion H.
  reflexivity.
Qed.

Lemma odd_SSn__odd_n : forall n, odd (S (S n)) -> odd n.
Proof.
  intros n H.
  inversion H.
  assert(H' : exists k, x = S k). {
    induction x as [|x' IHx].
    - discriminate H0.
    - exists x'. reflexivity.
  }
  destruct H' as [k H'].
  exists k.
  rewrite H' in H0.
  rewrite plus_n_Sm in H0.
  simpl in H0.
  inversion H0.
  reflexivity.
Qed.

Lemma even_n__not_odd_n : forall n, even n -> ~odd n.
Proof.
  intros n [k H]. generalize dependent n.
  induction k as [|k' IHk].
  - intros n H.
    rewrite H.
    intros [x H'].
    inversion H'.
  - intros n H.
    rewrite H.
    rewrite plus_n_Sm.
    simpl.
    assert(H'' : forall a, ~odd (S (S a)) <-> ~odd a). {
      intros a. split.
      - intros H'' H'''.
        apply odd_n__odd_SSn in H'''.
        apply H'' in H'''.
        apply H'''.
      - intros H'' H'''.
        apply odd_SSn__odd_n in H'''.
        apply H'' in H'''.
        apply H'''.
    }
    apply H''.
    apply IHk.
    reflexivity.
Qed.

Lemma odd_n__not_even_n : forall n, odd n -> ~even n.
Proof.
  intros n [k H]. generalize dependent n.
  induction k as [| k' IHk].
  - intros n H.
    rewrite H.
    intros [x H'].
    destruct x. inversion H'.
    rewrite plus_n_Sm in H'. inversion H'.
  - intros n H.
    rewrite H.
    rewrite plus_n_Sm.
    simpl.
    assert(H'' : forall a, ~even (S (S a)) <-> ~even a). {
      intros a. split.
      - intros H'' H'''.
        apply even_n__even_SSn in H'''.
        apply H'' in H'''.
        apply H'''.
      - intros H'' H'''.
        apply even_SSn__even_n in H'''.
        apply H'' in H'''.
        apply H'''.
    }
    apply H''.
    apply IHk.
    reflexivity.
Qed.

Lemma even_n__odd_Sn : forall n, even n -> odd (S n).
Proof.
  intros n [k H].
  exists k.
  rewrite H.
  reflexivity.
Qed.

Lemma odd_n__even_Sn : forall n, odd n -> even (S n).
Proof.
  intros n [k H].
  exists (S k).
  rewrite H, plus_n_Sm.
  reflexivity.
Qed.

Lemma odd_n__not_odd_Sn : forall n, odd n -> ~odd (S n).
Proof.
  intros n H.
  apply odd_n__even_Sn in H.
  apply even_n__not_odd_n in H.
  apply H.
Qed.

Lemma even_n__not_odd_Sn : forall n, even n -> ~even (S n).
Proof.
  intros n H.
  apply even_n__odd_Sn in H.
  apply odd_n__not_even_n in H.
  apply H.
Qed.

Lemma even_Sn__odd_n : forall n, even (S n) -> odd n.
Proof.
  intros n [[|k] H].
  - discriminate H.
  - exists k.
    rewrite plus_n_Sm in H.
    inversion H.
    reflexivity.
Qed.

Lemma odd_Sn__even_n : forall n, odd (S n) -> even n.
Proof.
  intros n [[|k] H].
  - inversion H.
    exists 0.
    reflexivity.
  - exists (S k).
    inversion H.
    reflexivity.
Qed.

Lemma even_Sn__not_even_n : forall n, even (S n) -> ~even n.
Proof.
  intros n H.
  apply even_Sn__odd_n in H.
  apply odd_n__not_even_n in H.
  apply H.
Qed.

Lemma odd_Sn__not_odd_n : forall n, odd (S n) -> ~odd n.
Proof.
  intros n H.
  apply odd_Sn__even_n in H.
  apply even_n__not_odd_n in H.
  apply H.
Qed.

Lemma not_odd_n__odd_Sn : forall n, ~odd n -> odd (S n).
Proof.
  intros n.
  induction n as [|n' IHn].
  - exists 0. reflexivity.
  - intros H. apply odd_n__odd_SSn.
    apply contrapositive in IHn.
    rewrite <- double_negation in IHn.
    apply IHn.
    apply H.
Qed.

Lemma not_even_n__even_Sn : forall n, ~even n -> even (S n).
Proof.
  intros n H.
  induction n as [|n' IHn].
  - assert(H' : even 0). exists 0. reflexivity.
    apply H in H'.
    destruct H'.
  - apply even_n__even_SSn.
    apply contrapositive in IHn.
    rewrite <- double_negation in IHn.
    apply IHn.
    apply H.
Qed.