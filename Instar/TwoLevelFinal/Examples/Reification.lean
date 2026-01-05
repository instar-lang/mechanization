import Instar.TwoLevelFinal.Examples.Notation

namespace Reification

-- reify under B context
-- let x =
--    letc x0 = eff in
--    code x0
-- in e
example : ∀ b e τ φ, ¬typing_reification ⦰ (.lets (.lets𝕔 b (.code (.bvar 0))) e) τ φ :=
  by
  intros _ _ _ _ Hτ
  cases Hτ
  case pure Hτ =>
    generalize HEqφ : ⊥ = φ
    rw [HEqφ] at Hτ
    cases Hτ
    case lets Hcode _ _ => cases Hcode; contradiction
  case reify Hτ =>
    cases Hτ
    case lets Hcode _ _ => cases Hcode; contradiction

-- result of reification under B context
-- let x = code (
--    let x0 = eff in
--    x0
-- )
-- in e
example : ∀ b e τ φ, ¬typing_reification ⦰ (.lets (.code (.lets b (.bvar 0))) e) τ φ :=
  by
  intros _ _ _ _ Hτ
  cases Hτ
  case pure Hτ =>
    generalize HEqφ : ⊥ = φ
    rw [HEqφ] at Hτ
    cases Hτ
    case lets Hcode _ _ => cases Hcode; contradiction
  case reify Hτ =>
    cases Hτ
    case lets Hcode _ _ => cases Hcode; contradiction

-- E context must has
-- E : (Γ ⊢ fragment τ) => (Γ ⊢ rep τ)
-- let x = reflect e
-- in 1
example : ∀ e τ φ, ¬typing_reification ⦰ (.lets (.reflect e) (.lit 1)) τ φ :=
  by
  intros _ _ _ Hτ
  cases Hτ
  case pure Hτ =>
    generalize HEqφ : ⊥ = φ
    rw [HEqφ] at Hτ
    cases Hτ
    case lets Hreflect _ _ =>
      cases Hreflect
      simp at HEqφ
  case reify Hτ =>
    cases Hτ
    contradiction

end Reification
