import Instar.TwoLevelRecBrack.Elab.Env
import Instar.TwoLevelRecBrack.Elab.Ty

namespace Bracket

/-- Elaboration is type-erased: elaborated terms never mention types, so the
source environment is tracked only by the *stages* of its bindings. -/
inductive elaboration : StEnv → Stage → Expr → Rec.Expr → Prop where
  | fvar₁ : ∀ Γ x,
    binds x (𝟙 : Stage) Γ →
    elaboration Γ 𝟙 (.fvar x) (.fvar x)
  | fvar₂ : ∀ Γ x,
    binds x (𝟚 : Stage) Γ →
    elaboration Γ 𝟚 (.fvar x) (.fvar x)
  | csp : ∀ Γ x,
    binds x (𝟙 : Stage) Γ →
    elaboration Γ 𝟚 (.fvar x) (.lift (.fvar x))
  | lit₁ : ∀ Γ n,
    elaboration Γ 𝟙 (.lit n) (.lit n)
  | lit₂ : ∀ Γ n,
    elaboration Γ 𝟚 (.lit n) (.lift (.lit n))
  | binary₁ : ∀ Γ op l₀ r₀ l₁ r₁,
    elaboration Γ 𝟙 l₀ l₁ →
    elaboration Γ 𝟙 r₀ r₁ →
    elaboration Γ 𝟙 (.binary op l₀ r₀) (.binary₁ (elab_op op) l₁ r₁)
  | binary₂ : ∀ Γ op l₀ r₀ l₁ r₁,
    elaboration Γ 𝟚 l₀ l₁ →
    elaboration Γ 𝟚 r₀ r₁ →
    elaboration Γ 𝟚 (.binary op l₀ r₀) (.binary₂ (elab_op op) l₁ r₁)
  | ifz₁ : ∀ Γ c₀ l₀ r₀ c₁ l₁ r₁,
    elaboration Γ 𝟙 c₀ c₁ →
    elaboration Γ 𝟙 l₀ l₁ →
    elaboration Γ 𝟙 r₀ r₁ →
    elaboration Γ 𝟙 (.ifz c₀ l₀ r₀) (.ifz₁ c₁ l₁ r₁)
  | ifz₂ : ∀ Γ c₀ l₀ r₀ c₁ l₁ r₁,
    elaboration Γ 𝟚 c₀ c₁ →
    elaboration Γ 𝟚 l₀ l₁ →
    elaboration Γ 𝟚 r₀ r₁ →
    elaboration Γ 𝟚 (.ifz c₀ l₀ r₀) (.ifz₂ c₁ l₁ r₁)
  | lam₁ : ∀ Γ e₀ e₁,
    elaboration (𝟙 :: Γ) 𝟙 ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) →
    Rec.closed_at e₁ Γ.length →
    elaboration Γ 𝟙 (.lam e₀) (.lam e₁)
  | lam₂ : ∀ Γ e₀ e₁,
    elaboration (𝟚 :: Γ) 𝟚 ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) →
    Rec.closed_at e₁ Γ.length →
    elaboration Γ 𝟚 (.lam e₀) (.lift (.lam e₁))
  | app₁ : ∀ Γ f₀ arg₀ f₁ arg₁,
    elaboration Γ 𝟙 f₀ f₁ →
    elaboration Γ 𝟙 arg₀ arg₁ →
    elaboration Γ 𝟙 (.app f₀ arg₀) (.app₁ f₁ arg₁)
  | app₂ : ∀ Γ f₀ arg₀ f₁ arg₁,
    elaboration Γ 𝟚 f₀ f₁ →
    elaboration Γ 𝟚 arg₀ arg₁ →
    elaboration Γ 𝟚 (.app f₀ arg₀) (.app₂ f₁ arg₁)
  | fix₁ : ∀ Γ f₀ f₁,
    elaboration Γ 𝟙 f₀ f₁ →
    elaboration Γ 𝟙 (.fix f₀) (.fix₁ f₁)
  | fix₂ : ∀ Γ f₀ f₁,
    elaboration Γ 𝟚 f₀ f₁ →
    elaboration Γ 𝟚 (.fix f₀) (.fix₂ f₁)
  | bracket : ∀ Γ e₀ e₁,
    elaboration Γ 𝟚 e₀ e₁ →
    elaboration Γ 𝟙 (.bracket e₀) e₁
  | escape : ∀ Γ e₀ e₁,
    elaboration Γ 𝟙 e₀ e₁ →
    elaboration Γ 𝟚 (.escape e₀) e₁
  | run : ∀ Γ e₀ e₁,
    elaboration Γ 𝟙 e₀ e₁ →
    elaboration Γ 𝟙 (.run e₀) (.run e₁)

abbrev elaboration_reification := elaboration [] 𝟙

lemma elaboration.fv_subset : ∀ Γ 𝕊 e₀ e₁,
    elaboration Γ 𝕊 e₀ e₁ →
    Rec.fv e₁ ⊆ Bracket.fv e₀ :=
  by
  intros Γ 𝕊 e₀ e₁ HElab
  induction HElab with
  | fvar₁ Γ x _ | fvar₂ Γ x _ | csp Γ x _ => simp
  | lit₁ Γ n | lit₂ Γ n => simp
  | binary₁ Γ op l₀ r₀ l₁ r₁ _ _ IHl IHr
  | binary₂ Γ op l₀ r₀ l₁ r₁ _ _ IHl IHr
  | app₁ Γ f₀ arg₀ f₁ arg₁ _ _ IHl IHr
  | app₂ Γ f₀ arg₀ f₁ arg₁ _ _ IHl IHr =>
    simp only [Rec.fv, Bracket.fv]
    apply Set.union_subset
    · exact Set.Subset.trans IHl Set.subset_union_left
    · exact Set.Subset.trans IHr Set.subset_union_right
  | ifz₁ Γ c₀ l₀ r₀ c₁ l₁ r₁ _ _ _ IHc IHl IHr
  | ifz₂ Γ c₀ l₀ r₀ c₁ l₁ r₁ _ _ _ IHc IHl IHr =>
    simp only [Rec.fv, Bracket.fv]
    apply Set.union_subset
    · apply Set.union_subset
      · exact Set.Subset.trans IHc (Set.Subset.trans Set.subset_union_left Set.subset_union_left)
      · exact Set.Subset.trans IHl (Set.Subset.trans Set.subset_union_right Set.subset_union_left)
    · exact Set.Subset.trans IHr Set.subset_union_right
  | lam₁ Γ e₀ e₁ _ Hclosed₁ IH
  | lam₂ Γ e₀ e₁ _ Hclosed₁ IH =>
    simp only [Rec.fv, Bracket.fv]
    intro x Hx
    have Hne : x ≠ Γ.length :=
      by
      intro HEq
      exact Rec.closed_impl_not_in_fv Γ.length x e₁ Hclosed₁ (le_of_eq HEq.symm) Hx
    have Hnv : x ∉ Rec.fv (.fvar Γ.length) := by simp [Hne]
    have Hmem : x ∈ Bracket.fv ({0 ↦ Γ.length} e₀) :=
      IH (Rec.mem_fv.under_opening x (.fvar Γ.length) 0 e₁ Hx Hnv)
    have Hunion := Bracket.fv.under_opening 0 (.fvar Γ.length) e₀ Hmem
    simp only [Bracket.fv, Set.mem_singleton_iff, Set.mem_union] at Hunion
    cases Hunion
    case inl HEq => exact absurd HEq Hne
    case inr Hin => exact Hin
  | fix₁ Γ f₀ f₁ _ IH
  | fix₂ Γ f₀ f₁ _ IH
  | bracket Γ e₀ e₁ _ IH
  | escape Γ e₀ e₁ _ IH
  | run Γ e₀ e₁ _ IH =>
    simp only [Rec.fv, Bracket.fv]
    exact IH

lemma elaboration.closed : ∀ Γ 𝕊 e₀ e₁,
    elaboration Γ 𝕊 e₀ e₁ →
    Bracket.closed e₀ →
    Rec.closed e₁ :=
  by
  intros Γ 𝕊 e₀ e₁ HElab Hclosed
  rw [Rec.closed_iff_fv_empty]
  have Hsub := elaboration.fv_subset Γ 𝕊 e₀ e₁ HElab
  rw [Bracket.closed_iff_fv_empty] at Hclosed
  rw [Hclosed] at Hsub
  exact Set.Subset.antisymm Hsub (Set.empty_subset _)

/- Elaboration preserves the well-typed-ness of expressions.
  The correspondence between what an expression is typed as before and
  after it is elaborated is trivial for typing judgements at 𝟙 (outside
  of quotes).
  By contrast, source expressions typed at 𝟚 (that is, within quotes) as `τ`
  are elaborated to some combinaton of lifts and/or stage-𝟚 primitives
  in the target language, and so instead will be typed as
  `fragment (elab τ)` therein.

  e.g. `elab ∅ ⟪1 + 1⟫ = (lift 1) +₂ (lift 1)`

  Also note that the typing judgement in the conclusion of this theorem is strictly
  at 𝟙: this is because the elaboration's use of 𝕊 differs from the typing judgements'.
  The typing judgements use 𝕊 as a restriction on the code they will type,
  whereas the elaboration uses 𝕊 to determine whether or not to add lifts/use
  stage-𝟚 primitives.

  e.g. `∅ ⊢₂ 1 : nat`, this is true in both languages.
    However, consider `elab₂ 1`, which for example might have come from
    `elab₁ ⟪1⟫`, reduces to `lift 1`, which is NOT of type nat.

  It is true that expressions of the surface language without any staging constructs
  are syntatically identical to their target counterparts; elaboration does not
  modify these expressions at all.
  *However*, it is not true that the elaboration of code found in quotes will
  be well-typed at stage 2, even if it is elaborated as if it were unquoted, i.e.

  `∅ ⊢₁ ⟪e⟫ : ⟪τ⟫` implies that `∅ ⊢₁ elab₁ e : elab τ`

  because `e` may contain splices.
  -/
lemma elaboration.typing_aux : ∀ Γ 𝕊 e₀ e₁ τ φ,
    Bracket.typing Γ 𝕊 e₀ τ φ →
    elaboration Γ.unzip.snd 𝕊 e₀ e₁ →
    Rec.typing (elab_env Γ) Rec.Stage.static e₁
      (match 𝕊 with
       | Bracket.Stage.static => elab_type τ
       | Bracket.Stage.dynamic => .fragment (elab_type τ))
      (elab_eff φ) :=
  by
  intros Γ 𝕊 e₀ e₁ τ φ Hτ HElab
  revert e₁
  induction Hτ <;> intro e₁ HElab
  case fvar Γ 𝕊 x τ Hbinds Hwbt =>
    cases 𝕊
    · cases HElab with
      | fvar₁ _ =>
        apply Rec.typing.fvar
        · exact elab_env.binds_static Γ x τ Hbinds
        · exact elab_type.wbt₁ τ Hwbt
    · cases HElab with
      | fvar₂ _ =>
        apply Rec.typing.fvar
        · exact elab_env.binds_dynamic Γ x τ Hbinds
        · change Rec.wbt Rec.Stage.dynamic (elab_type τ)
          exact elab_type.wbt₂ τ Hwbt
      | csp _ _ Hcsp =>
        exfalso
        have Hbind := Bracket.binds.unique
          (Bracket.binds.impl_stenv_binds _ x τ 𝟚 Hbinds) Hcsp
        simp at Hbind
  case csp_nat x Hbinds =>
    cases HElab with
    | csp =>
      apply Rec.typing.lift_lit
      apply Rec.typing.fvar
      · exact elab_env.binds_static _ x .nat Hbinds
      · simp
    | fvar₂ _ _ Hvar =>
      exfalso
      have Hbind := Bracket.binds.unique
        (Bracket.binds.impl_stenv_binds _ x .nat 𝟙 Hbinds) Hvar
      simp at Hbind
  case csp_lam x τ𝕒 τ𝕓 φ Hbinds Hwbt =>
    simp only [wbt] at Hwbt
    cases HElab with
    | csp =>
      apply Rec.typing.lift_lam
      apply Rec.typing.fvar
      · exact elab_env.binds_static _ x _ Hbinds
      · exact ⟨elab_type.wbt₂ _ Hwbt.left, elab_type.wbt₂ _ Hwbt.right⟩
    | fvar₂ _ _ Hvar =>
      exfalso
      have Hbind := Bracket.binds.unique
        (Bracket.binds.impl_stenv_binds _ x _ 𝟙 Hbinds) Hvar
      simp at Hbind
  case lit₁ n =>
    cases HElab with
    | lit₁ =>
      apply Rec.typing.lit
  case lit₂ n =>
    cases HElab with
    | lit₂ =>
      apply Rec.typing.lift_lit
      apply Rec.typing.lit
  case binary₁ op l r φ₁ φ₂ _ _ IHl IHr =>
    cases HElab with
    | binary₁ _ _ =>
      simp only [elab_eff_union]
      apply Rec.typing.binary₁
      · exact IHl _ (by assumption)
      · exact IHr _ (by assumption)
  case binary₂ op l r φ₁ φ₂ _ _ IHl IHr =>
    cases HElab with
    | binary₂ _ _ =>
      apply Rec.typing.binary₂
      · exact IHl _ (by assumption)
      · exact IHr _ (by assumption)
  case ifz₁ c l r τ φ₁ φ₂ φ₃ _ _ _ IHc IHl IHr =>
    cases HElab with
    | ifz₁ _ _ _ =>
      simp only [elab_eff_union]
      apply Rec.typing.ifz₁
      · exact IHc _ (by assumption)
      · exact IHl _ (by assumption)
      · exact IHr _ (by assumption)
  case ifz₂ c l r τ φ₁ φ₂ φ₃ _ _ _ IHc IHl IHr =>
    cases HElab with
    | ifz₂ _ _ _ =>
      apply Rec.typing.ifz₂
      · exact IHc _ (by assumption)
      · apply Rec.typing_reification.reify
        exact IHl _ (by assumption)
      · apply Rec.typing_reification.reify
        exact IHr _ (by assumption)
  case app₁ f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂ _ _ IHf IHarg =>
    cases HElab with
    | app₁ _ _ =>
      simp only [elab_eff_union]
      apply Rec.typing.app₁
      · exact IHf _ (by assumption)
      · exact IHarg _ (by assumption)
  case app₂ f arg τ𝕒 τ𝕓 φ₁ φ₂ _ _ IHf IHarg =>
    cases HElab with
    | app₂ _ _ =>
      apply Rec.typing.app₂
      · exact IHf _ (by assumption)
      · exact IHarg _ (by assumption)
  case lam₁ Γ e τ𝕒 τ𝕓 φ _ Hwbt _ IHbody =>
    cases HElab with
    | lam₁ _ _ e₁ HElab Hclosed₁ =>
      have Hlen : Γ.unzip.snd.length = Γ.length := by simp
      rw [Hlen] at HElab Hclosed₁
      apply Rec.typing.lam
      · rw [← elab_env.length]
        exact IHbody _ HElab
      · exact elab_type.wbt₁ τ𝕒 Hwbt
      · rw [← elab_env.length]
        exact Hclosed₁
  case lam₂ Γ e τ𝕒 τ𝕓 φ _ Hwbt _ IHbody =>
    cases HElab with
    | lam₂ _ _ e₁ HElab Hclosed₁ =>
      have Hlen : Γ.unzip.snd.length = Γ.length := by simp
      rw [Hlen] at HElab Hclosed₁
      apply Rec.typing.lift_lam (φ₀ := elab_eff φ)
      apply Rec.typing.lam
      · rw [← elab_env.length]
        exact IHbody _ HElab
      · exact elab_type.wbt₂ τ𝕒 Hwbt
      · rw [← elab_env.length]
        exact Hclosed₁
  case fix₁ f τ𝕒 τ𝕓 φ₀ φ₁ φ₂ Hφ _ IHf =>
    cases HElab with
    | fix₁ _ =>
      apply Rec.typing.fix₁ (φ₀ := elab_eff φ₀) (φ₁ := elab_eff φ₁) (φ₂ := elab_eff φ₂)
      · rw [← elab_eff_union]
        exact congrArg elab_eff Hφ
      · exact IHf _ (by assumption)
  case fix₂ f τ𝕒 τ𝕓 φ _ IHf =>
    cases HElab with
    | fix₂ _ =>
      apply Rec.typing.fix₂
      exact IHf _ (by assumption)
  case bracket e τ φ _ IHsub =>
    cases HElab with
    | bracket _ =>
      exact IHsub _ (by assumption)
  case escape e τ φ _ IHsub =>
    cases HElab with
    | escape _ =>
      exact IHsub _ (by assumption)
  case run e τ φ _ Hclosed IHsub =>
    cases HElab with
    | run _ =>
      apply Rec.typing.run
      · apply Rec.typing_reification.reify
        exact IHsub _ (by assumption)
      · exact elaboration.closed _ _ _ _ (by assumption) Hclosed

lemma elaboration.typing_static : ∀ e₀ e₁ τ φ,
    Bracket.typing ⦰ 𝟙 e₀ τ φ →
    elaboration_reification e₀ e₁ →
    Rec.typing ⦰ Rec.Stage.static e₁ (elab_type τ) (elab_eff φ) :=
  by
  intros e₀ e₁ τ φ Hτ HElab
  exact elaboration.typing_aux ⦰ Bracket.Stage.static e₀ e₁ τ φ Hτ HElab

lemma elaboration.typing_dynamic : ∀ e₀ e₁ τ φ,
    Bracket.typing ⦰ 𝟚 e₀ τ φ →
    elaboration [] 𝟚 e₀ e₁ →
    Rec.typing ⦰ Rec.Stage.static e₁ (.fragment (elab_type τ)) (elab_eff φ) :=
  by
  intros e₀ e₁ τ φ Hτ HElab
  exact elaboration.typing_aux ⦰ Bracket.Stage.dynamic e₀ e₁ τ φ Hτ HElab

lemma elaboration.typing_reification : ∀ e₀ e₁ τ φ,
    Bracket.typing_reification ⦰ e₀ τ φ →
    elaboration_reification e₀ e₁ →
    Rec.typing_reification ⦰ e₁ (elab_type_reification τ) (elab_eff φ) :=
  by
  intros e₀ e₁ τ φ Hτ HElab
  cases Hτ
  case pure Hτ =>
    cases τ
    case code =>
        apply Rec.typing_reification.reify
        simpa [elab_type_reification] using elaboration.typing_static _ _ _ _ Hτ HElab
    all_goals
      apply Rec.typing_reification.pure
      apply elaboration.typing_static _ _ _ _ Hτ HElab
  case reify Hτ =>
    apply Rec.typing_reification.reify
    simpa [elab_type_reification] using elaboration.typing_static _ _ _ _ Hτ HElab

end Bracket
