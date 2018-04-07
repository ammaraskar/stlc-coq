Inductive STLCType : Type :=
  | Arrow: STLCType -> STLCType -> STLCType
  | Bool : STLCType.

Inductive STLCExpr : Type :=
  | True:   STLCExpr
  | False:  STLCExpr
  | Lambda: STLCType -> nat -> STLCExpr -> STLCExpr
  | If    : STLCExpr -> STLCExpr -> STLCExpr -> STLCExpr
  | Var   : nat -> STLCExpr
  | App   : STLCExpr -> STLCExpr -> STLCExpr.


Definition isValue (E: STLCExpr) : bool :=
  match E with
  | True => true
  | False => true
  | (Lambda _ _ _) => true
  | _ => false
  end
.