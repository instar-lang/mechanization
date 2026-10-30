import Instar.TwoLevelRecBrack.Syntax.Basic

namespace Bracket

@[simp]
def opening (i : ℕ) (v : Expr) : Expr → Expr
  | .bvar j => if j = i then v else .bvar j
  | .fvar x => .fvar x
  | .lam e => .lam (opening (i + 1) v e)
  | .app f arg => .app (opening i v f) (opening i v arg)
  | .lit n => .lit n
  | .binary op l r => .binary op (opening i v l) (opening i v r)
  | .run e => .run (opening i v e)
  | .fix e => .fix (opening i v e)
  | .ifz c l r => .ifz (opening i v c) (opening i v l) (opening i v r)
  | .bracket e => .bracket (opening i v e)
  | .escape e => .escape (opening i v e)

notation:max "{" i " ↦ " x "}" e => opening i (Expr.fvar x) e

@[simp]
def closing (i : ℕ) (x : ℕ) : Expr → Expr
  | .bvar j => .bvar j
  | .fvar y => if x == y then .bvar i else .fvar y
  | .lam e => .lam (closing (i + 1) x e)
  | .app f arg => .app (closing i x f) (closing i x arg)
  | .lit n => .lit n
  | .binary op l r => .binary op (closing i x l) (closing i x r)
  | .run e => .run (closing i x e)
  | .fix e => .fix (closing i x e)
  | .ifz c l r => .ifz (closing i x c) (closing i x l) (closing i x r)
  | .bracket e => .bracket (closing i x e)
  | .escape e => .escape (closing i x e)

notation:max "{" i " ↤ " x "}" e => closing i x e

@[simp]
def subst (x : ℕ) (v : Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => if x = y then v else .fvar y
  | .lam e => .lam (subst x v e)
  | .app f arg => .app (subst x v f) (subst x v arg)
  | .lit n => .lit n
  | .binary op l r => .binary op (subst x v l) (subst x v r)
  | .run e => .run (subst x v e)
  | .fix e => .fix (subst x v e)
  | .ifz c l r => .ifz (subst x v c) (subst x v l) (subst x v r)
  | .bracket e => .bracket (subst x v e)
  | .escape e => .escape (subst x v e)

@[simp]
def shiftl (x : ℕ) (n : ℕ) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => if x ≤ y then .fvar (y + n) else .fvar y
  | .lam e => .lam (shiftl x n e)
  | .app f arg => .app (shiftl x n f) (shiftl x n arg)
  | .lit n => .lit n
  | .binary op l r => .binary op (shiftl x n l) (shiftl x n r)
  | .run e => .run (shiftl x n e)
  | .fix e => .fix (shiftl x n e)
  | .ifz c l r => .ifz (shiftl x n c) (shiftl x n l) (shiftl x n r)
  | .bracket e => .bracket (shiftl x n e)
  | .escape e => .escape (shiftl x n e)

@[simp]
def shiftr (x : ℕ) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => if x < y then .fvar (y - 1) else .fvar y
  | .lam e => .lam (shiftr x e)
  | .app f arg => .app (shiftr x f) (shiftr x arg)
  | .lit n => .lit n
  | .binary op l r => .binary op (shiftr x l) (shiftr x r)
  | .run e => .run (shiftr x e)
  | .fix e => .fix (shiftr x e)
  | .ifz c l r => .ifz (shiftr x c) (shiftr x l) (shiftr x r)
  | .bracket e => .bracket (shiftr x e)
  | .escape e => .escape (shiftr x e)

@[simp]
def erase : Expr → Expr
  | .bvar i => .bvar i
  | .fvar y => .fvar y
  | .lam e => .lam (erase e)
  | .app f arg => .app (erase f) (erase arg)
  | .lit n => .lit n
  | .binary op l r => .binary op (erase l) (erase r)
  | .run e => erase e
  | .fix e => .fix (erase e)
  | .ifz c l r => .ifz (erase c) (erase l) (erase r)
  | .bracket e => erase e
  | .escape e => erase e

notation:max "‖" e "‖" => erase e

end Bracket
