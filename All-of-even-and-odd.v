Axiom double_negation : forall P, P = ~~P.

Lemma contrapositive : forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
Proof. intuition. Qed.

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
  - Search even.
    apply contrapositive in H.
Qed.