import Instar.TwoLevelRecBrack.Syntax.Transform

namespace Bracket
@[simp]
def grounded : Expr → Prop
  | .bvar _ => True
  | .fvar _ => True
  | .lam e => grounded e
  | .app f arg => grounded f ∧ grounded arg
  | .binary _ l r => grounded l ∧ grounded r
  | .lit _ => True
  | .run _ => False
  | .fix e => grounded e
  | .ifz c l r => grounded c ∧ grounded l ∧ grounded r
  | .bracket _ => False
  | .escape _ => False

lemma grounded.under_erase : ∀ e, grounded ‖e‖ :=
  by
  intros e
  induction e with
  | bvar| fvar| lit => simp
  | lam _ IH
  | run _ IH
  | fix _ IH =>
    simp [IH]
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    simp [IH₀, IH₁, IH₂]
  | bracket _ => simp; assumption
  | escape _ => simp; assumption

lemma erasable.run : ∀ e₀ e₁, ‖e₀‖ ≠ Expr.run e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH

lemma erasable.bracket : ∀ e₀ e₁, ‖e₀‖ ≠ Expr.bracket e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH

lemma erasable.escape : ∀ e₀ e₁, ‖e₀‖ ≠ Expr.escape e₁ :=
  by
  intros e₀ e₁
  induction e₀ <;> simp
  all_goals next IH => apply IH


lemma grounded_iff_erase_identity : ∀ e, grounded e ↔ ‖e‖ = e :=
  by
  intros e
  induction e with
  | bvar| fvar| lit => simp
  | run _ => simp; apply erasable.run
  | bracket _ => simp; apply erasable.bracket
  | escape _ => simp; apply erasable.escape
  | lam _ IH
  | fix _ IH => simp; apply IH
  | app _ _ IH₁ IH₂
  | binary _ _ _ IH₁ IH₂ => simp [IH₁, IH₂]
  | ifz _ _ _ IH₁ IH₂ IH₃ => simp [IH₁, IH₂, IH₃]

lemma grounded.under_opening : ∀ e i x, grounded e ↔ grounded ({i ↦ x} e) :=
  by
  intros e i x
  induction e generalizing i with
  | fvar | lit| run| bracket| escape => simp
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]
    . simp [if_neg HEq]
  | lam _ IH
  | fix _ IH =>
    simp; rw [IH]
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    simp; rw [IH₀, IH₁]
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    simp; rw [IH₀, IH₁, IH₂]

end Bracket
