import Instar.TwoLevelRecBrack.Elab.Env
import Instar.TwoLevelRecBrack.Elab.Ty
import Instar.TwoLevelRecBrack.Elab.Relation
import Instar.TwoLevelRecBrack.Elab.Erasure
import Instar.TwoLevelRec.SemanticsPreservation.Defs

namespace Bracket

lemma semantics_preservation_aux : ∀ e t₀ t₁ τ φ,
    typing_reification ⦰ e (.code τ) φ →
    elaboration_reification e t₀ →
    Rec.stepn t₀ (.code t₁) →
    Rec.ctx_equiv ⦰ ‖t₀‖ t₁ (elab_type τ) :=
  by
  intros e t₀ t₁ τ φ Hτ₀ HElab Hstepn
  have Hτ₁ := elaboration.typing_reification _ _ _ _ Hτ₀ HElab
  simp only [elab_type_reification] at Hτ₁
  have ⟨_, Hτ₂, _⟩ := Rec.preservation.stepn _ _ _ _ Hstepn Hτ₁
  have Hvalue : Rec.value (.code t₁) :=
    Rec.value.code _ (by apply Rec.typing_reification.regular _ _ _ _ Hτ₂)
  have ⟨t₂, HEq, Hctx⟩ := Rec.semantics_preservation.stepn.rep _ _ _ _ Hstepn Hvalue Hτ₁
  cases HEq
  exact Hctx

/--
  Elaboration preserves the contextual equivalence between reified programs,
  their unstaged (erased) counterparts, and the code they generate.
  If we allow ourselves to speak of the results of elaboration directly, this
  theorem can be read something like:

  ∅ ⊢ e : ⟪τ⟫ | φ
  elab ∅  e  ⇝* ⟪t₁⟫
  elab ∅ |e|  =   t₂
  ———————————————————
  ∅ ⊧ t₁ ≈𝑐𝑡𝑥 t₂ : elab τ
-/
lemma semantics_preservation : ∀ e t₀ t₁ t₂ τ φ,
    typing_reification ⦰ e (.code τ) φ →
    elaboration_reification e t₀ →
    elaboration_reification ‖e‖ t₁ →
    Rec.stepn t₀ (.code t₂) →
    Rec.ctx_equiv ⦰ t₁ t₂ (elab_type τ) :=
  by
  intros e t₀ t₁ t₂ τ φ Hτ HElab₀ HElab₁ Hstepn
  have Hcomm := elab_erasure_comm _ _ _ _ _ HElab₀ HElab₁
  rw [← Hcomm]
  exact semantics_preservation_aux _ _ _ _ _ Hτ HElab₀ Hstepn

end Bracket
