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
      | _ => None
    end
  | _ => None
  end
.

(* TAPL page 105-106 *)
Theorem wellTypedProgress: forall (e: STLCExpr) (T: STLCType),
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
    * rewrite H1 in H2'. destruct H2.
Qed.