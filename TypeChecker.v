Require Import
  STLC
  Coq.Structures.OrderedTypeEx
  Coq.FSets.FMapFacts
  FSets.FMapList.

Fixpoint types_equal(t1 t2: STLCType) : bool :=
  match t1, t2 with
  | Bool, Bool => true
  | (Arrow t1_arg t1_ret), (Arrow t2_arg t2_ret) =>
      (types_equal t1_arg t2_arg) && (types_equal t1_ret t2_ret)
  | _, _ => false
  end
.

Lemma same_types_are_equal: forall (t: STLCType),
  types_equal t t = true.
Proof.
  intros.
  induction t.
  - simpl.
    rewrite -> IHt1. rewrite -> IHt2.
    reflexivity.
  - reflexivity.
Qed.

Module Import M := FMapList.Make(Nat_as_OT).
Module P := WProperties_fun Nat_as_OT M.
Module F := P.F.

Fixpoint type_of (e: STLCExpr) (env: M.t STLCType) : (option STLCType) :=
  match e with
  | True => value Bool
  | False => value Bool
  | Lambda type var body => 
    match type_of body (M.add var type env) with
    | Some r_type => Some (Arrow type r_type)
    | None => None
    end
  | App e1 e2 =>
    match (type_of e1 env), (type_of e2 env) with
    | (Some f_type), (Some arg_type) =>
      match f_type with
      | Arrow arg r_type => 
        if types_equal arg arg_type then
          Some r_type
        else
          None
      | _ => None
      end
    | _, _ => None
    end
  | If cond t e =>
    match (type_of cond env), (type_of t env), (type_of e env) with
    | (Some Bool), (Some then_type), (Some else_type) =>
      if types_equal then_type else_type then
        Some then_type
      else
        None
    | _, _, _ => None
    end
  | Var v =>
    M.find v env
  end
.

(* TAPL Page 104 *)
Lemma inversion_1 : forall (env: M.t STLCType) (x: nat) (R: STLCType),
  type_of (Var x) env = Some R 
  -> M.find x env = Some R.
Proof.
  intros.
  rewrite <- H.
  simpl. reflexivity.
Qed.

Lemma inversion_2: forall (env: M.t STLCType) (x: nat) 
                          (T1: STLCType) (R: STLCType) (R2: STLCType)
                          (body: STLCExpr),
  Some R = type_of (Lambda T1 x body) env
  -> Some R2 = type_of body (M.add x T1 env)
  -> R = Arrow T1 R2.
Proof.
  intros.
  inversion H.
  rewrite <- H0 in H2.
  inversion H2.
  reflexivity.
Qed.

Lemma inversion_3: forall (env: M.t STLCType) (R arg_type: STLCType)
                          (f arg: STLCExpr),
  Some (Arrow arg_type R) = type_of f env
  -> Some arg_type = type_of arg env
  -> type_of (App f arg) env = Some R.
Proof.
  intros.
  simpl.
  rewrite <- H. rewrite <- H0.
  rewrite -> same_types_are_equal.
  reflexivity.
Qed.

Lemma inversion_4: forall (env: M.t STLCType) (R: STLCType),
  Some R = type_of (True) env
  -> R = Bool.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Lemma inversion_5: forall (env: M.t STLCType) (R: STLCType),
  Some R = type_of (False) env
  -> R = Bool.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Lemma inversion_6': forall (env: M.t STLCType) (R: STLCType)
                          (cond t e: STLCExpr),
  Some R = type_of (If cond t e) env
  -> type_of cond env = Some Bool.
Proof.
  intros.
  simpl in H.
  destruct (type_of cond env).
  destruct s.
  - discriminate.
  - reflexivity.
  - discriminate.
Qed.

Corollary type_versus_arrow : forall (T t2: STLCType),
    types_equal T (Arrow T t2) = false.
Proof.
  intros T.
  induction T.
  - simpl. intros t2.
    rewrite IHT1. reflexivity.
  - simpl. reflexivity.
Qed.

Fact excercise_9_3_2: forall (R: STLCType),
  type_of (App (Var 1) (Var 1)) (M.add 1 R (M.empty STLCType)) = None.
Proof.
  intros.
  induction R.
    - simpl. rewrite type_versus_arrow. reflexivity.
    - simpl. reflexivity.
Qed.


Fact excercise_9_3_2_alt: forall (env: M.t STLCType),
  type_of (App (Var 1) (Var 1)) env = None.
Proof.
  intros.
  induction env using P.map_induction_bis.
    - unfold M.Equal in H.
      simpl. rewrite <- H. simpl in IHenv1. assumption.
    - simpl. reflexivity.
    - induction e.
      * simpl. destruct find.
        + destruct s.
            rewrite type_versus_arrow. reflexivity.
            reflexivity.
      + reflexivity.
      * simpl. destruct find.
        + destruct s.
            rewrite type_versus_arrow. reflexivity.
            reflexivity.
        + reflexivity.
Qed.

Definition isValue (E: STLCExpr) : bool :=
  match E with
  | True => true
  | False => true
  | (Lambda _ _ _) => true
  | _ => false
  end
.

Theorem cannonical_form1: forall (e: STLCExpr) (env: M.t STLCType),
    isValue e = true
    -> type_of e env = Some Bool
    -> e = True \/ e = False.
 Proof.
   intros.
   destruct e.
   - left. reflexivity.
   - right. reflexivity.
   - inversion H0.
     destruct (type_of e (add n s env)); left; discriminate.
   - inversion H.
   - inversion H.
   - inversion H.
Qed.

 Theorem canonical_form2: forall (e: STLCExpr) (env: M.t STLCType)
                            (T1 T2: STLCType),
     isValue e = true
     -> type_of e env = Some (Arrow T1 T2)
     -> exists var body, e = Lambda T1 var body.
 Proof.
   intros.
   destruct e.
   - inversion H0.
   - inversion H0.
   - inversion H0. destruct type_of in H2.
     * inversion H2. exists n, e. reflexivity.
     * inversion H2.
   - inversion H.
   - inversion H.
   - inversion H.
Qed.
