import Instar.TwoLevelRecBrack.Elab.Ty

namespace Bracket

/-- Target environments live entirely at stage 1. A source stage-2
binder becomes a static fragment binder in the target. -/
def elab_env : Bracket.TEnv → Rec.TEnv
  | [] => []
  | (τ, Bracket.Stage.static) :: Γ =>
      (elab_type τ, Rec.Stage.static) :: elab_env Γ
  | (τ, Bracket.Stage.dynamic) :: Γ =>
      (.fragment (elab_type τ), Rec.Stage.static) :: elab_env Γ

lemma elab_env.length : ∀ Γ, Γ.length = (elab_env Γ).length :=
  by
  intro Γ
  induction Γ
  case nil => rfl
  case cons head tails IH =>
    have ⟨τ, 𝕊⟩ := head
    cases 𝕊 <;> simp [elab_env, IH]

lemma elab_env.binds : ∀ Γ x τ 𝕊,
    Bracket.binds x (τ, 𝕊) Γ →
    Rec.binds x
      (match 𝕊 with
       | Bracket.Stage.static => (elab_type τ, Rec.Stage.static)
       | Bracket.Stage.dynamic => (.fragment (elab_type τ), Rec.Stage.static))
      (elab_env Γ) :=
  by
  intro Γ
  induction Γ
  case nil =>
    intro x τ 𝕊 Hbinds
    nomatch Hbinds
  case cons head tails IH =>
    intro x τ 𝕊 Hbinds
    have ⟨τ₀, 𝕊₀⟩ := head
    by_cases HEq : tails.length = x
    · simp [HEq] at Hbinds
      cases Hbinds
      subst τ₀
      subst 𝕊₀
      have Hpos : (elab_env tails).length = x := by
        rw [← elab_env.length]
        exact HEq
      unfold elab_env
      cases 𝕊 <;> simp [Rec.getr, Hpos]
    · simp [HEq] at Hbinds
      have Hneg : ¬(elab_env tails).length = x := by
        rw [← elab_env.length]
        exact HEq
      unfold elab_env
      cases 𝕊₀
      · cases 𝕊 <;> simp [Rec.getr, Hneg]
        · exact IH x τ Bracket.Stage.static Hbinds
        · exact IH x τ Bracket.Stage.dynamic Hbinds
      · cases 𝕊 <;> simp [Rec.getr, Hneg]
        · exact IH x τ Bracket.Stage.static Hbinds
        · exact IH x τ Bracket.Stage.dynamic Hbinds

lemma elab_env.binds_static (Γ : Bracket.TEnv) (x : ℕ) (τ : Bracket.Ty)
    (Hbinds : Bracket.binds x (τ, Bracket.Stage.static) Γ) :
    Rec.binds x (elab_type τ, Rec.Stage.static) (elab_env Γ) :=
  by
  exact elab_env.binds Γ x τ Bracket.Stage.static Hbinds

lemma elab_env.binds_dynamic (Γ : Bracket.TEnv) (x : ℕ) (τ : Bracket.Ty)
    (Hbinds : Bracket.binds x (τ, Bracket.Stage.dynamic) Γ) :
    Rec.binds x ((.fragment (elab_type τ)), Rec.Stage.static) (elab_env Γ) :=
  by
  exact elab_env.binds Γ x τ Bracket.Stage.dynamic Hbinds

end Bracket
