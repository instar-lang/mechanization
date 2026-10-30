import Instar.TwoLevelRecBrack.Elab.Env
import Instar.TwoLevelRecBrack.Elab.Ty
import Instar.TwoLevelRecBrack.Elab.Relation

namespace Bracket

/-
   Γ  ⊢ˢ  e  :  τ  | φ
  ————————————————————
  |Γ| ⊢¹ |e| : |τ| | ⊥
-/
lemma bracket_erasure_typing : ∀ Γ 𝕊 e τ φ,
    typing Γ 𝕊 e τ φ →
    typing (erase_env Γ) 𝟙 ‖e‖ (erase_ty τ) ⊥ :=
  by
  intros Γ 𝕊 e τ φ Hτ
  induction Hτ with
  | fvar Γ 𝕊 x τ Hbinds _ =>
    apply typing.fvar
    · exact erase_env.binds x τ 𝕊 Γ Hbinds
    · apply wbt.escape
      apply grounded_ty.under_erase
  | csp_nat Γ x Hbinds =>
    apply typing.fvar
    · exact erase_env.binds x .nat 𝟙 Γ Hbinds
    · apply wbt.escape
      apply grounded_ty.under_erase
  | csp_lam Γ x τ𝕒 τ𝕓 φ Hbinds _ =>
    apply typing.fvar
    · exact erase_env.binds x (.arrow (.code τ𝕒) (.code τ𝕓) φ) 𝟙 Γ Hbinds
    · apply wbt.escape
      apply grounded_ty.under_erase
  | lit₁ Γ n | lit₂ Γ n =>
    simp only [erase, erase_ty]
    apply typing.lit₁
  | binary₁ Γ op l r φ₁ φ₂ _ _ IHl IHr | binary₂ Γ op l r φ₁ φ₂ _ _ IHl IHr =>
    simp only [erase, erase_ty]
    exact typing.binary₁ (erase_env Γ) op ‖l‖ ‖r‖ ⊥ ⊥ IHl IHr
  | ifz₁ Γ c l r τ φ₁ φ₂ φ₃ _ _ _ IHc IHl IHr
  | ifz₂ Γ c l r τ φ₁ φ₂ φ₃ _ _ _ IHc IHl IHr =>
    simp only [erase]
    exact typing.ifz₁ (erase_env Γ) ‖c‖ ‖l‖ ‖r‖ (erase_ty τ) ⊥ ⊥ ⊥ IHc IHl IHr
  | lam₁ Γ e τ𝕒 τ𝕓 φ _ _ Hclosed IH | lam₂ Γ e τ𝕒 τ𝕓 φ _ _ Hclosed IH =>
    simp only [erase, erase_ty, erasure_opening_commute] at IH ⊢
    apply typing.lam₁
    · rw [← erase_env.length]
      exact IH
    · apply wbt.escape
      apply grounded_ty.under_erase
    · rw [← erase_env.length, ← closed.under_erase]
      exact Hclosed
  | app₁ Γ f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂ _ _ IHf IHarg
  | app₂ Γ f arg τ𝕒 τ𝕓 φ₁ φ₂ _ _ IHf IHarg =>
    simp only [erase]
    exact typing.app₁ (erase_env Γ) ‖f‖ ‖arg‖ (erase_ty τ𝕒) (erase_ty τ𝕓) ⊥ ⊥ ⊥ IHf IHarg
  | fix₁ Γ f τ𝕒 τ𝕓 φ₀ φ₁ φ₂ _ _ IHf | fix₂ Γ f τ𝕒 τ𝕓 φ _ IHf =>
    simp only [erase, erase_ty]
    apply typing.fix₁ _ _ _ _ ⊥ ⊥ _ (by simp)
    exact IHf
  | bracket Γ e τ φ _ IH | escape Γ e τ φ _ IH | run Γ e τ φ _ _ IH =>
    simp only [erase, erase_ty]
    exact IH

/-
   Γ  ⊢  e  :  τ  | φ
  ————————————————————
  |Γ| ⊢ |e| : |τ| | ⊥
-/
lemma bracket_erasure_typing_reification : ∀ Γ e τ φ,
    typing_reification Γ e τ φ →
    typing_reification (erase_env Γ) ‖e‖ (erase_ty τ) ⊥ :=
  by
  intro Γ e τ φ H
  cases H
  case pure Hty | reify Hty =>
    apply typing_reification.pure
    apply bracket_erasure_typing _ _ _ _ _ Hty

lemma bracket_rec_erasure_equivalent : ∀ Γ 𝕊 e t,
    elaboration Γ 𝕊 e t →
    elaboration (erase_stenv Γ) 𝟙 ‖e‖ ‖t‖ :=
  by
  intros Γ 𝕊 e t HElab
  induction HElab with
  | fvar₁ Γ x Hbinds | fvar₂ Γ x Hbinds | csp Γ x Hbinds =>
    apply elaboration.fvar₁
    exact erased_stenv_binds_static x Γ _ Hbinds
  | lit₁ Γ n | lit₂ Γ n =>
    simp only [erase]
    apply elaboration.lit₁
  | binary₁ Γ op l₀ r₀ l₁ r₁ _ _ IHl IHr
  | binary₂ Γ op l₀ r₀ l₁ r₁ _ _ IHl IHr =>
    simp only [erase]
    apply elaboration.binary₁
    · exact IHl
    · exact IHr
  | app₁ Γ f₀ arg₀ f₁ arg₁ _ _ IHl IHr
  | app₂ Γ f₀ arg₀ f₁ arg₁ _ _ IHl IHr =>
    simp only [erase]
    apply elaboration.app₁
    · exact IHl
    · exact IHr
  | ifz₁ Γ c₀ l₀ r₀ c₁ l₁ r₁ _ _ _ IHc IHl IHr
  | ifz₂ Γ c₀ l₀ r₀ c₁ l₁ r₁ _ _ _ IHc IHl IHr =>
    simp only [erase]
    apply elaboration.ifz₁
    · exact IHc
    · exact IHl
    · exact IHr
  | lam₁ Γ e₀ e₁ _ Hclosed IH | lam₂ Γ e₀ e₁ _ Hclosed IH =>
    simp only [erase]
    apply elaboration.lam₁
    · have Hlen : List.length (erase_stenv Γ) = Γ.length := by simp [erase_stenv]
      rw [erasure_opening_commute, Rec.erasure_opening_commute] at IH
      rw [Hlen]
      exact IH
    · have Hlen : List.length (erase_stenv Γ) = Γ.length := by simp [erase_stenv]
      rw [Hlen, ← Rec.closed.under_erase]
      exact Hclosed
  | fix₁ Γ f₀ f₁ _ IH | fix₂ Γ f₀ f₁ _ IH =>
    simp only [erase]
    apply elaboration.fix₁
    exact IH
  | bracket Γ e₀ e₁ _ IH | escape Γ e₀ e₁ _ IH | run Γ e₀ e₁ _ IH =>
    simp only [erase]
    exact IH

/-
  Roughly speaking, elaboration "commutes" with erasure,
  in the sense of the following abuse of notation:
  |elab Γ e| = elab |Γ| |e|
-/
lemma elab_erasure_comm : ∀ Γ 𝕊 e t₀ t₁,
    elaboration Γ 𝕊 e t₀ →
    elaboration (erase_stenv Γ) 𝟙 ‖e‖ t₁ →
    ‖t₀‖ = t₁ :=
  by
  intros Γ 𝕊 e t₀ t₁ HElab
  induction HElab generalizing t₁ with
  | fvar₁ | fvar₂ | csp | lit₁ | lit₂ =>
    intros H
    cases H
    rfl
  | binary₁ Γ op l₀ r₀ l₁ r₁ _ _ IHl IHr
  | binary₂ Γ op l₀ r₀ l₁ r₁ _ _ IHl IHr =>
    intros H
    cases H with
    | binary₁ _ _ _ _ _ _ Hl Hr =>
      have Hl₁ := IHl _ Hl
      have Hr₁ := IHr _ Hr
      simp only [Rec.erase, Hl₁, Hr₁]
  | app₁ Γ f₀ arg₀ f₁ arg₁ _ _ IHl IHr
  | app₂ Γ f₀ arg₀ f₁ arg₁ _ _ IHl IHr =>
    intros H
    cases H with
    | app₁ _ _ _ _ _ Hl Hr =>
      have Hl₁ := IHl _ Hl
      have Hr₁ := IHr _ Hr
      simp only [Rec.erase, Hl₁, Hr₁]
  | ifz₁ Γ c₀ l₀ r₀ c₁ l₁ r₁ _ _ _ IHc IHl IHr
  | ifz₂ Γ c₀ l₀ r₀ c₁ l₁ r₁ _ _ _ IHc IHl IHr =>
    intros H
    cases H with
    | ifz₁ _ _ _ _ _ _ _ Hc Hl Hr =>
      have Hc₁ := IHc _ Hc
      have Hl₁ := IHl _ Hl
      have Hr₁ := IHr _ Hr
      simp only [Rec.erase, Hc₁, Hl₁, Hr₁]
  | lam₁ Γ e₀ e₁ _ Hclosed IH | lam₂ Γ e₀ e₁ _ Hclosed IH =>
    intros H
    cases H with
    | lam₁ _ _ t₁body Hbody Hclosed₂ =>
      simp at Hbody Hclosed Hclosed₂ ⊢
      simp only [erase_stenv] at IH
      rw [← erasure_opening_commute] at Hbody
      have Hbody₁ := IH _ Hbody
      rw [Rec.erasure_opening_commute] at Hbody₁
      have Hcl₁ := (Rec.closed.under_erase _ _).mp Hclosed
      rw [← Rec.identity.closing_opening 0 _ _ Hcl₁,
        ← Rec.identity.closing_opening 0 _ _ Hclosed₂, Hbody₁]
  | fix₁ Γ f₀ f₁ _ IH | fix₂ Γ f₀ f₁ _ IH =>
    intros H
    cases H with
    | fix₁ _ _ _ Hf =>
      have Hf₁ := IH _ Hf
      simp only [Rec.erase, Hf₁]
  | bracket Γ e₀ e₁ _ IH | escape Γ e₀ e₁ _ IH | run Γ e₀ e₁ _ IH =>
    intros H
    exact IH _ H

end Bracket
