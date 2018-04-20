Require Import STLC.
Require Import TypeChecker.
Require Import AdditionalFacts.
Require Import EqNat.

Fixpoint substitute (var: nat) (e body: STLCExpr) :=
  match body with
  | Lambda t lVar lBody =>
      if beq_nat lVar var then
        Lambda t lVar lBody
      else
        Lambda t lVar (substitute var e lBody)
  | If c tBranch eBranch =>
      If (substitute var e c) (substitute var e tBranch) (substitute var e eBranch)
  | Var otherV =>
      if beq_nat otherV var then
        e
      else
        Var otherV
  | App e1 e2 => App (substitute var e e1) (substitute var e e2)
  | v => v
  end
.

Fixpoint evalStep (e: STLCExpr) : (option STLCExpr) :=
  match e with
  | If cond tBranch eBranch =>
    match cond with
    | True => Some tBranch
    | False => Some eBranch
    | c => match evalStep c with
            | Some c' => Some (If c' tBranch eBranch)
            | None => None
          end
    end
  | App e1 e2 =>
    match e1 with
      | Lambda _ var body => Some (substitute var e2 body)
      | e => match evalStep e1 with
            | Some e' => Some (App e' e2)
            | None => None
            end
    end
  | _ => None
  end
.

Fixpoint eval (n: nat) (e: STLCExpr) : option STLCExpr :=
  if isValue e then Some e else
    match n with
    | O => None
    | S n => match evalStep e with
            | Some e' => eval n e'
            | None => None
            end
    end
.

Definition halts (e: STLCExpr) :=
  exists n e', eval n e = Some e'.

(* TAPL page 105-106 *)
Theorem progress: forall (e: STLCExpr) (T: STLCType),
    type_of e (M.empty STLCType) = Some T
    -> isValue e = true \/ exists e', evalStep e = Some e'.
Proof.
  intros e.
  induction e.
  - left. reflexivity.
  - left. reflexivity.
  - left. reflexivity.
  - right. symmetry in H. apply inversion_6 in H.
    destruct H. destruct H0. rewrite <- H0 in IHe3.
    clear H0. assert (H0 := H1). assert (H' := H).
    * apply IHe1 in H. apply IHe3 in H0. apply IHe2 in H1.
      destruct H.
      + apply cannonical_form1 in H'. destruct H'.
          simpl. rewrite H2. exists e2. reflexivity.
          simpl. rewrite H2. exists e3. reflexivity.
          assumption.
      + simpl. destruct e1; eauto;
        destruct H; rewrite H; exists (If x e2 e3); reflexivity.
  - right. inversion H.
  - right. symmetry in H. apply inversion_3 in H. inversion H. inversion H0.
    destruct H1. destruct H2. assert (H2' := H2). apply IHe1 in H2. apply IHe2 in H3.
    destruct H2.
    * rewrite H1 in H2'. apply canonical_form2 in H2'. destruct H2'. destruct H4.
      simpl. rewrite H4. exists (substitute x1 e2 x2).
      + reflexivity.
      + assumption.
    * rewrite H1 in H2'. destruct H2. simpl. rewrite H2. destruct e1; eauto.
Qed.

Fixpoint free_in (e: STLCExpr) (x: nat) : bool :=
  match e with
  | Lambda _ var body =>
    if beq_nat x var then
      false
    else
      free_in body x 
  | App e1 e2 =>
    (free_in e1 x) || (free_in e2 x)
  | If cond t e =>
    (free_in cond x) || (free_in t x) || (free_in e x)
  | Var v =>
    if (beq_nat v x) then
      true
    else
      false
  | _ => false
  end
.

Lemma freeInEnv: forall (e: STLCExpr) (x: nat) (T: STLCType) (env: M.t STLCType),
    free_in e x = true
    -> type_of e env = Some T
    -> exists T', M.find x env = Some T'.
Proof.
  induction e.
  - intros. compute in H. discriminate.
  - intros. compute in H. discriminate.
  - intros. unfold free_in in H. simpl. fold free_in in H.
    symmetry in H0. apply inversion_2' in H0. destruct H0.
    destruct (PeanoNat.Nat.eq_dec) with (n := x) (m := n).
    + assert (e' := e0). apply PeanoNat.Nat.eqb_eq in e0. rewrite e0 in H.
      discriminate.
    + assert (n' := n0). apply PeanoNat.Nat.eqb_neq in n'. rewrite n' in H.
      unfold free_in in IHe. apply IHe with (env := (M.add n s env)) (T := x0) in H.
      destruct H. apply not_eq_sym in n0.
      apply F.add_neq_in_iff with (elt := STLCType) (m := env) (e := s) in n0.
      apply someIsNeverNone in H. apply F.in_find_iff in H.
      apply n0 in H. apply F.in_find_iff in H. 
      apply notNoneImpliesSome in H.
      * assumption.
      * assumption.
  - intros. unfold free_in in H.  simpl. fold free_in in H.
    symmetry in H0. apply inversion_6 in H0. destruct H0. destruct H1.
    apply Bool.orb_true_iff in H. destruct H.
    + apply Bool.orb_true_iff in H. destruct H.
      * eapply IHe1 in H; eauto.
      * eapply IHe2 in H2; eauto.
    + rewrite H2 in H1. symmetry in H1. eapply IHe3 in H1; eauto.
  - intros. unfold free_in in H. 
    destruct (PeanoNat.Nat.eq_dec) with (n := n) (m := x). 
    + assert (e' := e). apply PeanoNat.Nat.eqb_eq in e. rewrite e in H.
      simpl in H0.  rewrite e' in H0. exists T. assumption.
    + apply PeanoNat.Nat.eqb_neq in n0. rewrite n0 in H. discriminate.
  - intros. unfold free_in in H. simpl. fold free_in in H.
    symmetry in H0. apply inversion_3 in H0. destruct H0. destruct H0. destruct H0.
    destruct H1. apply Bool.orb_true_iff in H. destruct H.
    + unfold free_in in IHe1. eapply IHe1 in H; eauto.
    + unfold free_in in IHe2. eapply IHe2 in H; eauto.
Qed.

Lemma closedTermHasNoFreeVars: forall (e: STLCExpr) (t: STLCType),
    type_of e (M.empty STLCType) = Some t
    -> (forall (x: nat), free_in e x = false).
Proof.
  intros.
  case_eq (free_in e x).
  - intros. eapply freeInEnv in H0; eauto. destruct H0. compute in H0. discriminate.
  - intros. reflexivity.
Qed.


Lemma contextInvariance: forall (e: STLCExpr) (T: STLCType) (env env': M.t STLCType),
    type_of e env = Some T
    -> (forall (x: nat), free_in e x = true -> M.find x env = M.find x env')
    -> type_of e env' = Some T.
Proof.
  induction e; eauto.
  - intros. symmetry in H. assert (H' := H). 
    apply inversion_2' in H. destruct H.
    apply inversion_2 with (R2 := x) in H'.
    simpl. apply IHe with (env' := (M.add n s env')) in H.
    rewrite H. rewrite H'.
    * reflexivity.
    * intros. unfold free_in in H0. fold free_in in H0. specialize (H0 x0).
      destruct (PeanoNat.Nat.eq_dec) with (n := x0) (m := n).
      + symmetry in e0. assert (e' := e0). assert (e'' := e0).
        apply PeanoNat.Nat.eqb_eq in e'. rewrite <- e' in H0.
        apply F.add_eq_o with (elt := STLCType) (m := env) (e := s) in e0.
        apply F.add_eq_o with (elt := STLCType) (m := env') (e := s) in e''.
        congruence.
      + intros. apply PeanoNat.Nat.eqb_neq in n0. rewrite n0 in H0.
        apply H0 in H1. apply addingSameElementToList with (n := n) (val := s) in H1.
        assumption.
    * symmetry. assumption.
  - intros. symmetry in H. assert (H' := H).
    apply inversion_6 in H. destruct H. destruct H1. rewrite H2 in H1. symmetry in H1.
    unfold free_in in H0. simpl in H0. fold free_in in H0.
    apply IHe1 with (env' := env') in H. simpl.
    rewrite H.
    apply IHe2 with (env' := env') in H2. simpl.
    rewrite H2.
    apply IHe3 with (env' := env') in H1. simpl.
    rewrite H1.
    rewrite same_types_are_equal. reflexivity.
    * intros. specialize (H0 x). rewrite H3 in H0. rewrite Bool.orb_true_r in H0. auto.
    * intros. specialize (H0 x). rewrite H3 in H0. rewrite Bool.orb_true_r in H0. auto.
    * intros. specialize (H0 x). rewrite H3 in H0. rewrite Bool.orb_true_l in H0. auto.
  - intros. assert (H' := H).
    apply inversion_1 in H. specialize (H0 n).
    case_eq (free_in (Var n) n).
    * intros. apply H0 in H1. simpl. congruence.
    * intros. simpl in H1. cut (n = n).
      + intros. apply PeanoNat.Nat.eqb_eq in H2. rewrite H2 in H1. discriminate.
      + reflexivity.
  - intros. symmetry in H. assert (H' := H).
    apply inversion_3 in H. destruct H. destruct H. destruct H. destruct H1.
    unfold free_in in H0. simpl in H0. fold free_in in H0.
    apply IHe1 with (env' := env') in H1. simpl.
    rewrite H1.
    apply IHe2 with (env' := env') in H2. simpl.
    rewrite H2. rewrite H. rewrite same_types_are_equal. reflexivity.
    * intros. specialize (H0 x1). rewrite H3 in H0. rewrite Bool.orb_true_r in H0. auto.
    * intros. specialize (H0 x1). rewrite H3 in H0. rewrite Bool.orb_true_l in H0. auto.
Qed.

Lemma closedTermTypableInEveryEnv: forall (e: STLCExpr) (t: STLCType) (env: M.t STLCType),
    type_of e (M.empty STLCType) = Some t
    -> type_of e env = Some t.
Proof.
  intros. assert (H' := H).
  apply contextInvariance with (env' := env) in H'.
  + assumption.
  + intros. apply closedTermHasNoFreeVars with (x := x) in H. 
    rewrite H0 in H. discriminate.
Qed.

(* TAPL page 106 - 107 *)
Theorem preservationSubstitution: forall (t: STLCExpr) (env: M.t STLCType) (S: STLCType) (s: STLCExpr) (T: STLCType) (x: nat),
    type_of t (M.add x S env) = Some T
    -> type_of s (M.empty STLCType) = Some S
    -> type_of (substitute x s t) env = Some T.
Proof.
  induction t.
  * intros. simpl. simpl in H0. assumption.
  * intros. simpl. simpl in H0. assumption.
  * intros.
    unfold substitute. destruct (PeanoNat.Nat.eq_dec) with (n := n) (m := x).
    - assert (e' := e). apply PeanoNat.Nat.eqb_eq in e. rewrite e.
      assert (H' := H). symmetry in H. apply inversion_2' in H. destruct H.
      apply keyOverwrite with (env := env) (val := s) (val' := S) in e'.
      apply sameEnvSameType with (e := t) (T := x0) in e'.
      simpl. rewrite e'.
      symmetry in H'. apply inversion_2 with (R2 := x0) (R := T) in H'.
      rewrite H'. reflexivity.
      + rewrite <- e' in H. rewrite e' in H. auto.
      + assumption.
      + assumption.
    - assert (n' := n0). apply PeanoNat.Nat.eqb_neq in n'. rewrite n'. fold substitute.
      assert (H' := H). symmetry in H. apply inversion_2' in H. destruct H.
      symmetry in H'. apply inversion_2 with (R2 := x0) (T1 := s) (x := n) (R := T) in H'.
      simpl.
      apply permutation with (env := env) (val := s) (val' := S) in n0.
      apply sameEnvSameType with (e := t) (T := x0) in n0.
      specialize (IHt (M.add n s env) S s0 x0 x). apply IHt in n0.
      rewrite n0. rewrite H'. reflexivity.
      + assumption.
      + assumption.
      + symmetry. assumption.
  * intros. simpl. symmetry in H. apply inversion_6 in H. destruct H. destruct H1.
    specialize (IHt1 env S s Bool x). assert (H2' := H2).
    specialize (IHt2 env S s T x). specialize (IHt3 env S s T x). rewrite <- H1 in IHt3.
    apply IHt1 in H. apply IHt2 in H2. apply IHt3 in H2'.
    rewrite H. rewrite H2. rewrite H2'. rewrite same_types_are_equal.
    + reflexivity.
    + assumption.
    + assumption.
    + assumption.
  * intros. simpl in H. simpl. assert (H' := H). apply someIsNeverNone in H'.
    rewrite <- F.in_find_iff in H'.
    destruct (PeanoNat.Nat.eq_dec) with (n := n) (m := x).
    - assert (e' := e). apply PeanoNat.Nat.eqb_eq in e. rewrite e.
      rewrite F.add_o in H. rewrite e' in H. destruct F.eq_dec in H.
      + apply closedTermTypableInEveryEnv with (env := env) in H0. congruence.
      + contradiction.
    - assert (n' := n0). apply PeanoNat.Nat.eqb_neq in n0. rewrite n0.
      rewrite F.add_o in H. destruct F.eq_dec in H.
      + rewrite e in n'. contradiction.
      + simpl. rewrite H. reflexivity.
  * intros. symmetry in H. apply inversion_3 in H.
    destruct H. destruct H. destruct H. destruct H1.
    apply IHt1 with (T := x0) (s := s) (x := x) in H1.
    apply IHt2 with (T := x1) (s := s) (x := x) in H2.
    simpl. rewrite H1. rewrite H2. rewrite H. rewrite same_types_are_equal.
    reflexivity.
    + assumption.
    + assumption.
Qed.

(* TAPL page 107 *)
Theorem preservation: forall (t t': STLCExpr) (T: STLCType),
    type_of t (M.empty STLCType) = Some T
    -> evalStep t = Some t'
    -> type_of t' (M.empty STLCType) = Some T.
Proof.
  induction t.
  - intros. simpl in H0. discriminate.
  - intros. simpl in H0. discriminate.
  - intros. simpl in H0. discriminate.
  - intros. symmetry in H. apply inversion_6 in H. destruct H. destruct H1.
    simpl in H0. destruct t1; try (simpl in H0; discriminate); try congruence.
    * destruct evalStep.
      + inversion H0. simpl. specialize (IHt1 s Bool). apply IHt1 in H.
        rewrite H. rewrite H2. rewrite <- H1. rewrite H2. rewrite same_types_are_equal.
        reflexivity. reflexivity.
      + discriminate.
    * destruct evalStep.
      + inversion H0. simpl. specialize (IHt1 s Bool). apply IHt1 in H.
        rewrite H. rewrite H2. rewrite <- H1. rewrite H2. rewrite same_types_are_equal.
        reflexivity. reflexivity.
      + discriminate.
  - intros. simpl in H0. discriminate.
  - intros. simpl in H0. symmetry in H. apply inversion_3 in H.
    destruct H. destruct H. destruct H. destruct H1.
    destruct t1; try (simpl in H0; discriminate); try congruence.
    * inversion H0. apply preservationSubstitution with (S := x0). 
      + assert (H1' := H1). symmetry in H1. apply inversion_2' in H1. destruct H1.
        symmetry in H1'. apply inversion_2 with (R2 := x1) in H1'. congruence.
        rewrite H1. reflexivity.
      + assumption.
    * destruct evalStep. inversion H0. simpl. specialize (IHt1 s x). apply IHt1 in H1.
      + rewrite H1. rewrite H2. rewrite H. rewrite same_types_are_equal. reflexivity.
      + reflexivity.
      + discriminate.
    * destruct evalStep. inversion H0. simpl. specialize (IHt1 s x). apply IHt1 in H1.
      + rewrite H1. rewrite H2. rewrite H. rewrite same_types_are_equal. reflexivity.
      + reflexivity.
      + discriminate.
Qed.

Theorem moreComputationSameResult: forall (n n': nat) (e e': STLCExpr),
  eval n e = Some e'
  -> n' >= n
  -> eval n' e = Some e'.
Proof.
  induction n.
  - intros. simpl in H. destruct n'.
    + simpl. destruct (isValue e). assumption. discriminate.
    + simpl. destruct (isValue e). assumption. discriminate.
  - intros. simpl in H. destruct n'.
    + simpl. destruct (isValue e).
      * assumption. 
      * unfold ge in H0. apply max_l in H0. simpl in H0. discriminate.
    + simpl. destruct (isValue e).
      * assumption.
      *  unfold ge in H0. apply le_pred in H0. simpl in H0.
         destruct (evalStep e).
         apply IHn with (n' := n') in H. assumption. assumption. discriminate.
Qed.

Theorem evalPreservesHalting: forall (t t': STLCExpr),
    halts t
    -> evalStep t = Some t'
    -> halts t'.
Proof.
  intros.
  unfold halts in H. destruct H. destruct H.
  unfold halts. exists (x - 1), x0.
  induction x.
  - simpl in H. simpl. destruct t; discriminate.
  - simpl in H. destruct t; try (discriminate).
    + rewrite H0 in H. simpl in H. simpl. rewrite PeanoNat.Nat.sub_0_r. assumption.
    + rewrite H0 in H. simpl in H. simpl. rewrite PeanoNat.Nat.sub_0_r. assumption.
Qed.

Theorem evalPreservesHalting': forall (t t': STLCExpr),
    halts t'
    -> evalStep t = Some t'
    -> halts t.
Proof.
  intros.
  unfold halts in H. destruct H. destruct H.
  unfold halts. exists (1 + x), x0. simpl.
  destruct t; try (discriminate).
  - rewrite H0. simpl. assumption.
  - rewrite H0. simpl. assumption.
Qed.

Fixpoint reducibilitySet (T: STLCType) (t: STLCExpr) : Prop :=
  match T with
  | Bool =>
      type_of t (M.empty STLCType) = Some Bool /\
      halts t
  | Arrow T1 T2 =>
      type_of t (M.empty STLCType) = Some (Arrow T1 T2) /\
      halts t /\
      (forall s, reducibilitySet T1 s -> reducibilitySet T2 (App t s))
  end
.

Lemma reducibilitySetInclusionHalts: forall (T: STLCType) (t: STLCExpr),
    reducibilitySet T t
    -> halts t.
Proof.
  intros.
  destruct T.
  - simpl in H. destruct H. destruct H0. assumption.
  - simpl in H. destruct H. assumption.
Qed.

Lemma reducibilityInversion: forall (T: STLCType) (t: STLCExpr),
    reducibilitySet T t
    -> type_of t (M.empty STLCType) = Some T.
Proof.
  destruct T.
  - intros. simpl in H. destruct H. assumption.
  - intros. simpl in H. destruct H. assumption.
Qed.

Lemma steppingPreservesReducibility: forall (T: STLCType) (t t': STLCExpr),
    type_of t (M.empty STLCType) = Some T /\ evalStep t = Some t'
    -> (reducibilitySet T t <-> reducibilitySet T t').
Proof.
  induction T.
  - intros. destruct H. split.
    + intros. simpl in H1. destruct H1. destruct H2.
      simpl. apply preservation with (t' := t') in H.
      split. assumption.
      split. apply evalPreservesHalting in H0. assumption.
      assumption.
      intros. apply H3 in H4.
      specialize (IHT2 (App t s) (App t' s)). assert (H' := H4).
      apply reducibilityInversion in H4. cut (evalStep (App t s) = Some (App t' s)).
      intros.
      cut (type_of (App t s) (M.empty STLCType) = Some T2 /\ evalStep (App t s) = Some (App t' s)).
      intros. apply IHT2 in H6. apply H6 in H'. assumption.
      split. assumption. assumption.
      simpl. destruct t; try (simpl in H0; discriminate).
      * rewrite H0. reflexivity.
      * rewrite H0. reflexivity.
      * assumption.
    + intros. simpl in H1. destruct H1. destruct H2.
      simpl.
      split. assumption.
      split. apply evalPreservesHalting' with (t := t) in H2. assumption.
      assumption.
      intros. apply H3 in H4.
      specialize (IHT2 (App t s) (App t' s)). assert (H' := H4).
      apply reducibilityInversion in H4. cut (evalStep (App t s) = Some (App t' s)).
      intros.
      cut (type_of (App t s) (M.empty STLCType) = Some T2 /\ evalStep (App t s) = Some (App t' s)).
      intros. apply IHT2 in H6. apply H6 in H'. assumption.
      split. simpl. rewrite H. symmetry in H4. apply inversion_3 in H4.
      destruct H4. destruct H4. destruct H4. destruct H6. rewrite H7. rewrite H6 in H1.
      inversion H1. rewrite H9 in H4. apply equality_implies_types_equal in H4.
      simpl in H4. apply Bool.andb_true_iff in H4. destruct H4. rewrite H4. reflexivity.
      assumption.
      simpl. destruct t; try (simpl in H0; discriminate); try (rewrite H0; reflexivity).
  - intros. destruct H. split.
    + intros. simpl in H1. simpl. apply preservation with (t' := t') in H.
      split. assumption. apply evalPreservesHalting in H0.
      * assumption.
      * destruct H1. assumption.
      * assumption.
    + intros. simpl in H1. simpl. split. assumption.
      apply evalPreservesHalting' in H0. assumption.
      destruct H1. assumption.
Qed.