import Instar.TwoLevelRec.SyntacticTyping.Defs
import Instar.TwoLevelRecBrack.SyntacticTyping.Defs

namespace Bracket

@[simp]
def elab_op : Bracket.BinOp → Rec.BinOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul

@[simp]
def elab_eff : Bracket.Effect → Rec.Effect
  | ⊤ => ⊤
  | ⊥ => ⊥

@[simp]
lemma elab_eff_union (φ₁ φ₂ : Bracket.Effect) :
    elab_eff (φ₁ ∪ φ₂) = elab_eff φ₁ ∪ elab_eff φ₂ :=
  by
  cases φ₁ <;> cases φ₂ <;> rfl

@[simp]
def elab_type : Bracket.Ty → Rec.Ty
  | .nat => .nat
  | .arrow τ₀ τ₁ φ => .arrow (elab_type τ₀) (elab_type τ₁) (elab_eff φ)
  | .code τ => .fragment (elab_type τ)

/-- Top-level type elaboration: only the outermost `code` becomes `rep`.
Nested code remains `fragment`, matching `elab_type`. -/
@[simp]
def elab_type_reification : Bracket.Ty → Rec.Ty
  | .code τ => .rep (elab_type τ)
  | τ => elab_type τ

lemma elab_type.wbt₂ : ∀ τ,
    Bracket.wbt Bracket.Stage.dynamic τ →
    Rec.wbt Rec.Stage.dynamic (elab_type τ) :=
  by
  intro τ Hwbt
  induction τ with
  | nat => simp
  | arrow τ𝕒 τ𝕓 φ IH𝕒 IH𝕓 =>
      obtain ⟨Hφ, H𝕒, H𝕓⟩ := Hwbt
      subst Hφ
      constructor
      · rfl
      · constructor
        · exact IH𝕒 H𝕒
        · exact IH𝕓 H𝕓
  | code τ IH => nomatch Hwbt

lemma elab_type.wbt₁ : ∀ τ,
    Bracket.wbt Bracket.Stage.static τ →
    Rec.wbt Rec.Stage.static (elab_type τ) :=
  by
  intro τ Hwbt
  induction τ with
  | nat => simp
  | arrow τ𝕒 τ𝕓 φ IH𝕒 IH𝕓 =>
      obtain ⟨H𝕒, H𝕓⟩ := Hwbt
      constructor
      · exact IH𝕒 H𝕒
      · exact IH𝕓 H𝕓
  | code τ IH =>
      simp at Hwbt ⊢
      exact elab_type.wbt₂ τ Hwbt

end Bracket
