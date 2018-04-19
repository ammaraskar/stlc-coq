Require Import STLC.
Require Import TypeChecker.
Require Import Structures.Equalities.

Lemma someIsNeverNone: forall (t_option: option STLCType) (t: STLCType),
    t_option = Some t
    -> t_option <> None.
Proof.
  intros. congruence. 
Qed.

Lemma notNoneImpliesSome: forall (t_option: option STLCType),
    t_option <> None
    -> exists t, t_option = Some t.
Proof.
  intros. 
  destruct t_option.
  - exists s. reflexivity.
  - contradiction.
Qed.

(*Lemma eqb_neq: forall (n m: nat),
    n <> m
    -> PeanoNat.Nat.eqb n m = false.
Proof.
  induction n.
  - intros. unfold PeanoNat.Nat.eqb. destruct m.
    + contradiction.
    + reflexivity.
  - intros. destruct m.
    + reflexivity.
    + eauto.
Qed.*)

Lemma addingSameElementToMaps: forall (m m': M.t STLCType) (key n: nat) (val: STLCType),
    M.Equal m m'
    -> M.Equal (M.add n val m) (M.add n val m').
Proof.
  intros. unfold M.Equal.
  intros.
  rewrite F.add_o. rewrite F.add_o.
  destruct F.eq_dec. reflexivity.
  unfold M.Equal in H. specialize (H y). assumption.
Qed.

Lemma sameEnvSameType: forall (e: STLCExpr) (T: STLCType) (env env': M.t STLCType),
    M.Equal env env'
    -> type_of e env = Some T
    -> type_of e env' = Some T.
Proof.
  induction e; eauto.
  - intros. symmetry in H0. assert (H' := H0). apply inversion_2' in H0. destruct H0.
    apply inversion_2 with (R2 := x) in H'.
    apply IHe with (env' := (M.add n s env')) in H0.
    simpl. rewrite H0. rewrite H'. reflexivity.
    apply addingSameElementToMaps.
    assumption.
    assumption.
    symmetry. assumption.
  - intros. symmetry in H0. assert (H' := H0). apply inversion_6 in H0. destruct H0.
    destruct H1. rewrite H2 in H1. symmetry in H1.
    apply IHe1 with (env' := env') in H0.
    apply IHe2 with (env' := env') in H2.
    apply IHe3 with (env' := env') in H1.
    simpl. rewrite H0. rewrite H2. rewrite H1. rewrite same_types_are_equal. reflexivity.
    * assumption.
    * assumption.
    * assumption.
  - intros. simpl. simpl in H0. unfold M.Equal in H. specialize (H n).
    rewrite <- H. assumption.
  - intros. symmetry in H0. assert (H' := H0). apply inversion_3 in H0.
    destruct H0. destruct H0. destruct H0. destruct H1.
    apply IHe1 with (env' := env') in H1. apply IHe2 with (env' := env') in H2.
    simpl. rewrite H1. rewrite H2. rewrite H0. rewrite same_types_are_equal. reflexivity.
    * assumption.
    * assumption.
Qed.

Lemma permutation: forall (env: M.t STLCType) (key key': nat) (val val': STLCType),
    key <> key'
    -> M.Equal (M.add key val (M.add key' val' env))
               (M.add key' val' (M.add key val env)).
Proof.
  intros.
  unfold M.Equal. intros.
  rewrite F.add_o. rewrite F.add_o. rewrite F.add_o. rewrite F.add_o.
  unfold F.eq_dec.
  destruct (PeanoNat.Nat.eq_dec key y).
  - destruct (PeanoNat.Nat.eq_dec key' y).
    * rewrite e0 in H. rewrite e in H. contradiction.
    * reflexivity.
  - destruct (PeanoNat.Nat.eq_dec key' y).
    * reflexivity.
    * reflexivity.
Qed.

Lemma keyOverwrite: forall (env: M.t STLCType) (e: STLCExpr) (key key': nat) (val val': STLCType),
    key = key'
    -> M.Equal (M.add key val (M.add key' val' env))
               (M.add key val env).
Proof.
  intros.
  unfold M.Equal. intros.
  rewrite H.
  rewrite F.add_o. rewrite F.add_o. rewrite F.add_o. unfold F.eq_dec.
  destruct (PeanoNat.Nat.eq_dec key' y).
  - reflexivity.
  - reflexivity.
Qed.

(* If two maps have the same mapping for a key. And we add the exact same mapping into
   both lists. Then find will still return the same result *)
Lemma addingSameElementToList: forall (m m': M.t STLCType) (key n: nat) (val: STLCType),
    M.find key m = M.find key m'
    -> M.find key (M.add n val m) = M.find key (M.add n val m').
Proof.
  intros.
  rewrite F.add_o. rewrite F.add_o.
  destruct F.eq_dec. reflexivity. assumption.
Qed.