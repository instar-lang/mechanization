import Mathlib.Data.Nat.Basic

namespace Rec

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
  | app₁ (f : Expr) (arg : Expr)
  | app₂ (f : Expr) (arg : Expr)
  | lit (n : ℕ)
  | binary₁ (op : BinOp) (l : Expr) (r : Expr)
  | binary₂ (op : BinOp) (l : Expr) (r : Expr)
  | lift (e : Expr)
  | run (e : Expr)
  | code (e : Expr)
  | reflect (e : Expr)
  | lam𝕔 (e : Expr)
  | lets (b : Expr) (e : Expr)
  | lets𝕔 (b : Expr) (e : Expr)
  | fix₁ (e : Expr)
  | fix₂ (e : Expr)
  | ifz₁ (c : Expr) (l : Expr) (r : Expr)
  | ifz₂ (c : Expr) (l : Expr) (r : Expr)

end Rec
