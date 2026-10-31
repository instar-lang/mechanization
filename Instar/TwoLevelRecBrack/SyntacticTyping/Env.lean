import Instar.TwoLevelRecBrack.SyntacticTyping.Ty
import Instar.TwoLevelRecBrack.Utils.Defs
namespace Bracket

abbrev TEnv := List (Ty × Stage)

notation:max "⦰" => ([] : TEnv)

abbrev StEnv := List Stage

@[simp]
def erase_env : TEnv → TEnv
  | ⦰ => ⦰
  | (τ, _) :: Γ => (erase_ty τ, 𝟙) :: erase_env Γ

lemma erase_env.length : ∀ Γ, Γ.length = (erase_env Γ).length :=
  by
  intros Γ
  induction Γ
  case nil => rfl
  case cons IH => simp; apply IH

lemma erase_env.binds : ∀ x τ 𝕊 Γ, binds x (τ, 𝕊) Γ → binds x (erase_ty τ, 𝟙) (erase_env Γ) :=
  by
  intros x τ 𝕊 Γ Hbinds
  induction Γ
  case nil => nomatch Hbinds
  case cons tails IH =>
    by_cases HEq : tails.length = x
    . simp [if_pos HEq] at Hbinds
      simp [← erase_env.length, if_pos HEq, Hbinds]
    . simp [if_neg HEq] at Hbinds
      simp [← erase_env.length, if_neg HEq]
      apply IH; apply Hbinds

@[simp]
def escape_env : TEnv → TEnv
  | ⦰ => ⦰
  | (τ, _) :: tails => (τ, 𝟙) :: escape_env tails

lemma escape_env.length : ∀ Γ, Γ.length = (escape_env Γ).length :=
  by
  intro Γ
  induction Γ with
  | nil => simp
  | cons head _ IH =>
    have ⟨τ, 𝕊⟩ := head
    cases 𝕊 <;> (simp; apply IH)

@[simp]
def erase_stenv : Bracket.StEnv → Bracket.StEnv := List.map (fun _ => 𝟙)

lemma erased_stenv_binds_static : ∀ x Γ 𝕊, binds x 𝕊 Γ → binds x 𝟙 (erase_stenv Γ) :=
  by
  intro x Γ
  induction Γ generalizing x
  case nil => simp
  case cons IH =>
    intro 𝕊 Hbinds
    simp at *
    intro _
    split_ifs at Hbinds
    apply IH _ _ Hbinds

lemma erase_env_erase_stenv_comm : ∀ Γ, (erase_env Γ).unzip.snd = erase_stenv Γ.unzip.snd :=
  by
  intro Γ
  induction Γ
  case nil => simp
  case cons IH => simp at *; exact IH

lemma escape_env.binds : ∀ Γ x τ 𝕊, binds x (τ, 𝕊) Γ → binds x (τ, 𝟙) (escape_env Γ) :=
  by
  intros Γ x τ 𝕊
  induction Γ with
  | nil => simp
  | cons head tails IH =>
    have ⟨τ, 𝕊⟩ := head
    by_cases HEq : tails.length = x
    . simp [if_pos HEq, ← escape_env.length]
      intros; assumption
    . simp [if_neg HEq, ← escape_env.length]
      apply IH

lemma binds.impl_stenv_binds :
  ∀ (Γ : TEnv) i τ 𝕊,
    binds i (τ, 𝕊) Γ → binds i 𝕊 Γ.unzip.snd :=
  by
  intro Γ
  induction Γ <;> intro i τ 𝕊
  case nil => simp
  case cons x xs IH =>
    simp at *
    split_ifs
    . cases x; simp
    . apply IH

end Bracket
