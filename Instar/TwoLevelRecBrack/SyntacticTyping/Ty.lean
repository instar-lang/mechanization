import Instar.TwoLevelRecBrack.SyntacticTyping.Effect
namespace Bracket

inductive Ty : Type where
  | nat
  | code (τ : Ty)
  | arrow (τ𝕒 : Ty) (τ𝕓 : Ty) (φ : Effect)

@[simp]
def erase_ty : Ty → Ty
  | .nat           => .nat
  | .arrow τ𝕒 τ𝕓 _ => .arrow (erase_ty τ𝕒) (erase_ty τ𝕓) ⊥
  | .code τ        => erase_ty τ

inductive Stage : Type where
  | static
  | dynamic

notation:max "𝟙" => Stage.static
notation:max "𝟚" => Stage.dynamic

@[simp]
def wbt : Stage → Ty → Prop
  | 𝟙, .nat           => True
  | 𝟙, .arrow τ𝕒 τ𝕓 _ => wbt 𝟙 τ𝕒 ∧ wbt 𝟙 τ𝕓
  | 𝟙, .code τ        => wbt 𝟚 τ
  | 𝟚, .nat           => True
  | 𝟚, .arrow τ𝕒 τ𝕓 φ => φ = ⊥ ∧ wbt 𝟚 τ𝕒 ∧ wbt 𝟚 τ𝕓
  | 𝟚, .code _        => False

lemma wbt.escape : ∀ τ, wbt 𝟚 τ → wbt 𝟙 τ :=
  by
  intros τ Hwbt
  induction τ
  case nat => simp
  case arrow IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hwbt.right.left
    apply IH₁; apply Hwbt.right.right
  case code => nomatch Hwbt

lemma grounded_ty.under_erase : ∀ τ, wbt 𝟚 (erase_ty τ) :=
  by
  intros τ
  induction τ
  case nat => simp
  case arrow IH₀ IH₁ =>
    constructor; rfl
    constructor; apply IH₀; apply IH₁
  case code IH => simp; exact IH

lemma erasable.code : ∀ τ₀ τ₁, erase_ty τ₀ ≠ .code τ₁ :=
  by
  intros τ₀ τ₁
  induction τ₀ <;> simp
  all_goals next IH => apply IH

lemma grounded_ty_iff_erase_identity : ∀ τ, wbt 𝟚 τ ↔ erase_ty τ = τ :=
  by
  intros τ
  induction τ
  case nat => simp
  case arrow IH𝕒 IH𝕓 =>
    simp [IH𝕒, IH𝕓]
    constructor
    . intros H; simp [H]
    . intros H; simp [H]
  case code IH => simp; apply erasable.code

end Bracket
