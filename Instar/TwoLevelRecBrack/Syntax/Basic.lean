import Mathlib.Data.Nat.Basic
namespace Bracket

inductive BinOp : Type where
  | add
  | mul
  | sub

@[simp]
def eval : BinOp → ℕ → ℕ → ℕ
  | .add => Nat.add
  | .mul => Nat.mul
  | .sub => Nat.sub

inductive Expr : Type where
  | bvar (i : ℕ)
  | fvar (x : ℕ)
  | lam (e : Expr)
  | app (f : Expr) (arg : Expr)
  | lit (n : ℕ)
  | binary (op : BinOp) (l : Expr) (r : Expr)
  | run (e : Expr)
  | fix (e : Expr)
  | ifz (c : Expr) (l : Expr) (r : Expr)
  | bracket (e : Expr)
  | escape (e : Expr)

end Bracket
