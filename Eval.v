Require Import STLC.
Require Import TypeChecker.
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

Lemma someIsNeverNone: forall (t_option: option STLCType) (t: STLCType),
    t_option = Some t
    -> t_option <> None.
Proof.
  intros. congruence. 
Qed.

Lemma eqb_neq: forall (n m: nat),
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
Qed.

Lemma permutation: forall (e: STLCExpr) (env: M.t STLCType) (key key': nat) (val val': STLCType),
    key <> key'
    -> type_of e (M.add key val (M.add key' val' env))
       = type_of e (M.add key' val' (M.add key val env)).
Proof.
  intros.
Admitted.

Lemma keyOverwrite: forall (e: STLCExpr) (env: M.t STLCType) (key key': nat) (val val': STLCType),
    key = key'
    -> M.add key val (M.add key' val' env) = M.add key val env.
Proof.
Admitted.

(* TAPL page 106 - 107 *)
Theorem preservationSubstitution: forall (t: STLCExpr) (env: M.t STLCType) (S: STLCType) (s: STLCExpr) (T: STLCType) (x: nat),
    type_of t (M.add x S env) = Some T
    -> type_of s env = Some S
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
      rewrite e' in H. simpl. rewrite H.
      symmetry in H'. apply inversion_2 with (R2 := x0) (R := T) in H'.
      rewrite H'. reflexivity.
      + rewrite <- e' in H. auto.
      + assumption.
    - assert (n' := n0). apply eqb_neq in n'. rewrite n'. fold substitute.
      assert (H' := H). symmetry in H. apply inversion_2' in H. destruct H.
      symmetry in H'. apply inversion_2 with (R2 := x0) (T1 := s) (x := n) (R := T) in H'.
      simpl.
      apply permutation with (env := env) (e := t) (val := s) (val' := S) in n0.
      rewrite n0 in H.
      specialize (IHt (M.add n s env) S s0 x0 x). apply IHt in H.
      rewrite H. rewrite H'. reflexivity.
      + admit.
      + symmetry in H. assumption.
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
      + congruence.
      + contradiction.
    - assert (n' := n0). apply eqb_neq in n0. rewrite n0.
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
Admitted.

(* TAPL page 107 *)
Theorem preservation: forall (env: M.t STLCType) (t t': STLCExpr) (T: STLCType),
    type_of t env = Some T
    -> evalStep t = Some t'
    -> type_of t' env = Some T.
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
      + congruence.
    * destruct evalStep. inversion H0. simpl. specialize (IHt1 s x). apply IHt1 in H1.
      + rewrite H1. rewrite H2. rewrite H. rewrite same_types_are_equal. reflexivity.
      + reflexivity.
      + discriminate.
    * destruct evalStep. inversion H0. simpl. specialize (IHt1 s x). apply IHt1 in H1.
      + rewrite H1. rewrite H2. rewrite H. rewrite same_types_are_equal. reflexivity.
      + reflexivity.
      + discriminate.
Qed.