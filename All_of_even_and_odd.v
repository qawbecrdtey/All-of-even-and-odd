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

Inductive even : nat->Prop :=
  | ev_0 : even 0
  | ev_SS n (H : even n) : even (S (S n))
.
Inductive odd : nat->Prop :=
  | odd_1 : odd 1
  | odd_SS n (H : odd n) : odd (S (S n))
.

Lemma even_n__even_SSn : forall n, even n -> even (S (S n)).
Proof.
  intros n H.
  apply ev_SS.
  apply H.
Qed.

Lemma odd_n__odd_SSn : forall n, odd n -> odd (S (S n)).
Proof.
  intros n H.
  apply odd_SS.
  apply H.
Qed.

Lemma even_n__not_odd_n : forall n, even n -> ~odd n.
Proof.
  intros n H.
  induction H.
  - intros H'. inversion H'.
  - intros H'. inversion H'.
    apply IHeven in H1.
    apply H1.
Qed.

Lemma odd_n__not_even_n : forall n, odd n -> ~even n.
Proof.
  intros n H.
  induction H.
  - intros H'. inversion H'.
  - intros H'. inversion H'.
    apply IHodd in H1.
    apply H1.
Qed.

Lemma even_n__odd_Sn : forall n, even n -> odd (S n).
Proof.
  intros n H.
  induction H.
  - apply odd_1.
  - apply odd_SS. apply IHeven.
Qed.

Lemma odd_n__even_Sn : forall n, odd n -> even (S n).
Proof.
  intros n H.
  induction H.
  - apply ev_SS. apply ev_0.
  - apply ev_SS. apply IHodd.
Qed.

Lemma odd_n__not_odd_Sn : forall n, odd n -> ~odd (S n).
Proof.
  intros n H.
  apply even_n__not_odd_n.
  apply odd_n__even_Sn.
  apply H.
Qed.

Lemma even_n__not_even_Sn : forall n, even n -> ~even (S n).
Proof.
  intros n H.
  apply odd_n__not_even_n.
  apply even_n__odd_Sn.
  apply H.
Qed.

Lemma even_Sn__odd_n : forall n, even (S n) -> odd n.
Proof.
  intros n H.
  inversion H.
  apply even_n__odd_Sn.
  rewrite <- H0 in H.
  inversion H.
  apply H3.
Qed.

Lemma odd_Sn__even_n : forall n, odd (S n) -> even n.
Proof.
  intros n H.
  inversion H. apply ev_0.
  apply odd_n__even_Sn.
  rewrite <- H0 in H.
  inversion H.
  apply H3.
Qed.

Lemma even_Sn__not_even_n : forall n, even (S n) -> ~even n.
Proof.
  intros n H.
  apply even_Sn__odd_n in H.
  apply odd_n__not_even_n in H.
  apply H.
Qed.

Lemma odd_Sn__not_even_n : forall n, odd (S n) -> ~odd n.
Proof.
  intros n H.
  apply odd_Sn__even_n in H.
  apply even_n__not_odd_n in H.
  apply H.
Qed.

Lemma not_odd_n__odd_Sn : forall n, ~odd n -> odd (S n).
Proof.
  intros n H.
  induction n as [|n' IHn].
  - apply odd_1.
  - apply odd_SS.
    apply contrapositive in IHn.
    + rewrite <- double_negation in IHn.
      apply IHn.
    + intros H'.
      apply H in H'.
      apply H'.
Qed.

Lemma not_even_n__even_Sn : forall n, ~even n -> even (S n).
Proof.
  intros n H.
  induction n as [|n' IHn].
  - assert(H' : even 0). apply ev_0.
    apply H in H'.
    destruct H'.
  - apply ev_SS.
    apply contrapositive in IHn.
    + rewrite <-double_negation in IHn.
      apply IHn.
    + intros H'.
      apply H in H'.
      apply H'.
Qed.

Lemma not_odd_n__even_n : forall n, ~odd n -> even n.
Proof.
  intros n H.
  apply odd_Sn__even_n.
  apply not_odd_n__odd_Sn.
  apply H.
Qed.

Lemma not_even_n__odd_n : forall n, ~even n -> odd n.
Proof.
  intros n H.
  apply even_Sn__odd_n.
  apply not_even_n__even_Sn.
  apply H.
Qed.

Lemma not_odd_Sn__odd_n : forall n, ~odd (S n) -> odd n.
Proof.
  intros n H.
  apply not_odd_n__even_n in H.
  apply even_Sn__odd_n.
  apply H.
Qed.

Lemma not_even_Sn__even_n : forall n, ~even (S n) -> even n.
Proof.
  intros n H.
  apply not_even_n__odd_n in H.
  apply odd_Sn__even_n.
  apply H.
Qed.

Lemma nat_odd_or_even : forall n, even n \/ odd n.
Proof.
  intros n.
  induction n as [|n' [IHl | IHr]].
  - left. apply ev_0.
  - right. apply even_n__odd_Sn. apply IHl.
  - left. apply odd_n__even_Sn. apply IHr.
Qed.

Lemma odd_n__even_n__false : forall n, odd n /\ even n -> False.
Proof.
  intros n [Hl Hr].
  apply even_n__not_odd_n in Hl.
  - apply Hl.
  - apply Hr.
Qed.

Lemma even_n__even_m__even_plus_n_m : forall n m, even n /\ even m -> even (n + m).
Proof.
  intros n m [Hl Hr].
  induction Hl.
  - apply Hr.
  - simpl. apply ev_SS.
    apply IHHl.
Qed.

Lemma even_plus_n_m__even_n__even_m : forall n m, even (n + m) /\ even n -> even m.
Proof.
  intros n m [Hl Hr].
  induction Hr.
  - apply Hl.
  - apply IHHr.
    inversion Hl.
    apply H0.
Qed.

Lemma even_plus_n_m__even_m__even_n : forall n m, even (n + m) /\ even m -> even n.
Proof.
  intros n m [Hl Hr].
  induction Hr.
  - rewrite plus_n_0 in Hl.
    apply Hl.
  - apply IHHr.
    rewrite plus_n_Sm in Hl.
    rewrite plus_n_Sm in Hl.
    inversion Hl.
    apply H0.
Qed.

Lemma odd_n__odd_m__even_plus_n_m : forall n m, odd n /\ odd m -> even (n + m).
Proof.
  intros n m [Hl Hr].
  induction Hl.
  - apply odd_n__even_Sn.
    apply Hr.
  - simpl.
    apply ev_SS.
    apply IHHl.
Qed.

Lemma even_plus_n_m__odd_n__odd_m : forall n m, even (n + m) /\ odd n -> odd m.
Proof.
  intros n m [Hl Hr].
  induction Hr.
  - apply even_Sn__odd_n.
    apply Hl.
  - apply IHHr.
    inversion Hl.
    apply H0.
Qed.

Lemma even_plus_n_m__odd_m__odd_n : forall n m, even (n + m) /\ odd m -> odd n.
Proof.
  intros n m [Hl Hr].
  induction Hr.
  - apply even_Sn__odd_n.
    rewrite plus_commutative in Hl.
    apply Hl.
  - apply IHHr.
    rewrite plus_commutative in Hl.
    inversion Hl.
    rewrite plus_commutative.
    apply H0.
Qed.

Lemma even_n__odd_m__odd_plus_n_m : forall n m, even n /\ odd m -> odd (n + m).
Proof.
  intros n m [Hl Hr].
  induction Hl.
  - apply Hr.
  - simpl. apply odd_SS.
    apply IHHl.
Qed.

Lemma odd_plus_n_m__even_n__odd_m : forall n m, odd (n + m) /\ even n -> odd m.
Proof.
  intros n m [Hl Hr].
  induction Hr.
  - apply Hl.
  - apply IHHr.
    inversion Hl.
    apply H0.
Qed.

Lemma odd_plus_n__odd_m__even_n : forall n m, odd (n + m) /\ odd m -> even n.
Proof.
  intros n m [Hl Hr].
  induction Hr.
  - rewrite plus_commutative in Hl.
    apply odd_Sn__even_n in Hl.
    apply Hl.
  - apply IHHr.
    rewrite plus_commutative in Hl.
    inversion Hl.
    rewrite plus_commutative.
    apply H0.
Qed.

Lemma odd_n__even_m__odd_plus_n_m : forall n m, odd n /\ even m -> odd (n + m).
Proof.
  intros n m [Hl Hr].
  induction Hl.
  - apply even_n__odd_Sn.
    apply Hr.
  - simpl. apply odd_SS.
    apply IHHl.
Qed.

Lemma odd_plus_n_m__odd_n__even_m : forall n m, odd (n + m) /\ odd n -> even m.
Proof.
  intros n m [Hl Hr].
  induction Hr.
  - apply odd_Sn__even_n.
    apply Hl.
  - apply IHHr.
    inversion Hl.
    apply H0.
Qed.

Lemma odd_plus_n_m__even_m__odd_n : forall n m, odd (n + m) /\ even m -> odd n.
Proof.
  intros n m [Hl Hr].
  induction Hr.
  - rewrite plus_n_0 in Hl.
    apply Hl.
  - apply IHHr.
    rewrite plus_commutative in Hl.
    inversion Hl.
    rewrite plus_commutative.
    apply H0.
Qed.

Lemma even_plus_n_n : forall n, even (n + n).
Proof.
  intros n.
  induction n as [|n' IHn].
  - apply ev_0.
  - rewrite plus_n_Sm.
    simpl. apply ev_SS.
    apply IHn.
Qed.

Lemma even_plus_n_m_iff_even_n__even_m_or_odd_n__odd_m :
  forall n m, even (n + m) <-> (even n /\ even m) \/ (odd n /\ odd m)
.
Proof.
  intros n m.
  split.
  - generalize dependent m.
    induction n as [|n' IHn].
    + intros m H.
      left. split. apply ev_0. apply H.
    + intros m H.
      destruct (IHn (S m)) as [[Hll Hlr] | [Hrl Hrr]].
      * rewrite plus_n_Sm. apply H.
      * right. split.
          apply even_n__odd_Sn. apply Hll.
          apply even_Sn__odd_n. apply Hlr.
      * left. split.
        apply odd_n__even_Sn. apply Hrl.
        apply odd_Sn__even_n. apply Hrr.
  - intros [[Hll Hlr] | [Hrl Hrr]].
    + apply even_n__even_m__even_plus_n_m.
      split. apply Hll. apply Hlr.
    + apply odd_n__odd_m__even_plus_n_m.
      split. apply Hrl. apply Hrr.
Qed.

Lemma odd_plus_n_m_iff_even_n__odd_m_or_odd_n__even_m :
  forall n m, odd (n + m) <-> (even n /\ odd m) \/ (odd n /\ even m)
.
Proof.
  intros n m.
  split.
  - generalize dependent m.
    induction n as [|n' IHn].
    + intros m H.
      left. split. apply ev_0. apply H.
    + intros m H.
      destruct (IHn (S m)) as [[Hll Hlr] | [Hrl Hrr]].
      * rewrite plus_n_Sm. apply H.
      * right. split.
          apply even_n__odd_Sn. apply Hll.
          apply odd_Sn__even_n. apply Hlr.
      * left. split.
          apply odd_n__even_Sn. apply Hrl.
          apply even_Sn__odd_n. apply Hrr.
  - intros [[Hll Hlr] | [Hrl Hrr]].
    + apply even_n__odd_m__odd_plus_n_m.
      split. apply Hll. apply Hlr.
    + apply odd_n__even_m__odd_plus_n_m.
      split. apply Hrl. apply Hrr.
Qed.

Lemma even_nSn : forall n, even (n * S n).
Proof.
  intros n. 
  induction n as [|n' IHn].
  - apply ev_0.
  - simpl.
    apply ev_SS.
    rewrite mult_n_Sm.
    rewrite <- (plus_associative n' n' _).
    apply even_n__even_m__even_plus_n_m.
    split. apply even_plus_n_n. apply IHn.
Qed.

Lemma even_n__even_nm : forall n m, even n -> even (n * m).
Proof.
  intros n m H.
  induction H.
  - apply ev_0.
  - simpl.
    rewrite <- plus_associative.
    apply even_n__even_m__even_plus_n_m.
    split.
    + apply even_plus_n_n.
    + apply IHeven.
Qed.

Lemma even_m__even_nm : forall n m, even m -> even (n * m).
Proof.
  intros n m H.
  rewrite mult_commutative.
  apply even_n__even_nm.
  apply H.
Qed.

Lemma even_nm__odd_n__even_m : forall n m, even (n * m) /\ odd n -> even m.
Proof.
  intros n m [Hl Hr].
  induction Hr.
  - rewrite mult_1_n in Hl.
    apply Hl.
  - apply IHHr.
    simpl in Hl.
    destruct m as [|m'] eqn : Em.
    + rewrite mult_n_0.
      apply ev_0.
    + simpl in Hl.
      rewrite plus_n_Sm in Hl.
      simpl in Hl.
      inversion Hl.
      rewrite <- plus_associative in H0.
      apply (even_plus_n_m_iff_even_n__even_m_or_odd_n__odd_m (m' + m') _) in H0.
      destruct H0 as [[Hll Hlr] | [Hrl Hrr]].
      * apply Hlr.
      * apply not_odd_n__even_n.
        intros H'.
        apply odd_n__not_even_n in Hrl.
        apply Hrl.
        apply even_plus_n_n.
Qed.

Lemma even_nm__odd_m__even_n : forall n m, even (n * m) /\ odd m -> even n.
Proof.
  intros n m.
  rewrite mult_commutative.
  apply even_nm__odd_n__even_m.
Qed.

Lemma even_nm_iff_even_n_or_even_m : forall n m, even (n * m) <-> even n \/ even m.
Proof.
  intros n m.
  split.
  - generalize dependent m.
    induction n as [|n' IHn].
    + intros m H. left. apply ev_0.
    + intros m H.
      destruct (IHn (S n')).
      * apply even_nSn.
      * right. apply (even_nm__odd_n__even_m (S n') m).
          split. apply H. apply even_n__odd_Sn. apply H0.
      * left. apply H0.
  - intros [Hl | Hr].
    + apply even_n__even_nm. apply Hl.
    + apply even_m__even_nm. apply Hr.
Qed.

Lemma odd_n__odd_m__odd_nm : forall n m, odd n /\ odd m -> odd (n * m).
Proof.
  intros n m [Hl Hr].
  induction Hl.
  - rewrite mult_1_n. apply Hr.
  - simpl.
    apply odd_n__even_m__odd_plus_n_m.
    split. apply Hr.
    apply odd_n__odd_m__even_plus_n_m.
    split. apply Hr. apply IHHl.
Qed.

Lemma odd_nm_iff_odd_n__odd_m : forall n m, odd (n * m) <-> odd n /\ odd m.
Proof.
  intros n m.
  split.
  - intros H.
    induction n as [|n' IHn].
    + inversion H.
    + simpl in H.
      apply odd_plus_n_m_iff_even_n__odd_m_or_odd_n__even_m in H.
      destruct H as [[Hll Hlr] | [Hrl Hrr]].
      * apply IHn in Hlr.
        destruct Hlr as [Hlrl Hlrr].
        apply even_n__not_odd_n in Hll.
        apply Hll in Hlrr.
        destruct Hlrr.
      * apply even_nm_iff_even_n_or_even_m in Hrr.
        destruct Hrr as [Hrrl | Hrrr].
          split. apply even_n__odd_Sn. apply Hrrl. apply Hrl.
          apply odd_n__not_even_n in Hrl. apply Hrl in Hrrr. destruct Hrrr.
  - apply odd_n__odd_m__odd_nm.
Qed.

Fixpoint power(n k : nat) : nat :=
  match k with
    | 0     => 1
    | S k'  => n * power n k'
  end
.

Lemma power_n_1 : forall n, power n 1 = n.
Proof. apply mult_n_1. Qed.

Lemma even_power_iff_even : forall n k, even (power n (S k)) <-> even n.
Proof.
  intros n k.
  split.
  - induction k as [|k' IHk].
    + rewrite power_n_1.
      intros H. apply H.
    + intros H. simpl in H.
      simpl in IHk.
      apply even_nm_iff_even_n_or_even_m in H.
      destruct H as [Hl | Hr].
      * apply Hl.
      * apply IHk in Hr. apply Hr.
  - intros H. simpl.
    apply even_n__even_nm. apply H.
Qed.

Lemma odd_power_iff_odd : forall n k, odd(power n (S k)) <-> odd n.
Proof.
  intros n k.
  split.
  - induction k as [|k' IHk].
    + simpl. rewrite mult_n_1.
      intros H. apply H.
    + intros H. simpl in H.
      apply odd_nm_iff_odd_n__odd_m in H.
      destruct H as [Hl Hr].
      apply Hl.
  - intros H. simpl.
    induction k as [|k' IHk].
    + rewrite mult_n_1. apply H.
    + apply odd_nm_iff_odd_n__odd_m.
      split. apply H. apply IHk.
Qed.