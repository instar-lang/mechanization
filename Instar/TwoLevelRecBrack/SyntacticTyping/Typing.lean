import Instar.TwoLevelRecBrack.Syntax.Defs
import Instar.TwoLevelRecBrack.Utils.Defs
import Instar.TwoLevelRecBrack.SyntacticTyping.Env
import Instar.TwoLevelRecBrack.SyntacticTyping.Ty

namespace Bracket

/-!
  A stage-indexed source typing judgment whose effects are meant to be the
  same as the effects of the elaborated two-level term.

  The static rules compute the usual effects. The dynamic rules mirror the
  target fragment builders: dynamic code generation is effectful (`⊤`),
  while a dynamic variable bound at stage 2 is pure. `bracket` and `escape`
  are effect-transparent: they merely switch the stage.
-/
inductive typing : TEnv → Stage → Expr → Ty → Effect → Prop where
  | fvar : ∀ Γ 𝕊 x τ,
    binds x (τ, 𝕊) Γ →
    wbt 𝕊 τ →
    typing Γ 𝕊 (.fvar x) τ ⊥
  | csp_nat : ∀ Γ x,
    binds x (.nat, 𝟙) Γ →
    typing Γ 𝟚 (.fvar x) .nat ⊤
  | csp_lam : ∀ Γ x τ𝕒 τ𝕓 φ,
    binds x (.arrow (.code τ𝕒) (.code τ𝕓) φ, 𝟙) Γ →
    wbt 𝟙 (.arrow (.code τ𝕒) (.code τ𝕓) φ) →
    typing Γ 𝟚 (.fvar x) (.arrow τ𝕒 τ𝕓 ⊥) ⊤
  | lit₁ : ∀ Γ n,
    typing Γ 𝟙 (.lit n) .nat ⊥
  | lit₂ : ∀ Γ n,
    typing Γ 𝟚 (.lit n) .nat ⊤
  | binary₁ : ∀ Γ op l r φ₁ φ₂,
    typing Γ 𝟙 l .nat φ₁ →
    typing Γ 𝟙 r .nat φ₂ →
    typing Γ 𝟙 (.binary op l r) .nat (φ₁ ∪ φ₂)
  | binary₂ : ∀ Γ op l r φ₁ φ₂,
    typing Γ 𝟚 l .nat φ₁ →
    typing Γ 𝟚 r .nat φ₂ →
    typing Γ 𝟚 (.binary op l r) .nat ⊤
  | ifz₁ : ∀ Γ c l r τ φ₁ φ₂ φ₃,
    typing Γ 𝟙 c .nat φ₁ →
    typing Γ 𝟙 l τ φ₂ →
    typing Γ 𝟙 r τ φ₃ →
    typing Γ 𝟙 (.ifz c l r) τ (φ₁ ∪ φ₂ ∪ φ₃)
  | ifz₂ : ∀ Γ c l r τ φ₁ φ₂ φ₃,
    typing Γ 𝟚 c .nat φ₁ →
    typing Γ 𝟚 l τ φ₂ →
    typing Γ 𝟚 r τ φ₃ →
    typing Γ 𝟚 (.ifz c l r) τ ⊤
  | lam₁ : ∀ Γ e τ𝕒 τ𝕓 φ,
    typing ((τ𝕒, 𝟙) :: Γ) 𝟙 ({0 ↦ Γ.length} e) τ𝕓 φ →
    wbt 𝟙 τ𝕒 →
    closed_at e Γ.length →
    typing Γ 𝟙 (.lam e) (.arrow τ𝕒 τ𝕓 φ) ⊥
  | lam₂ : ∀ Γ e τ𝕒 τ𝕓 φ,
    typing ((τ𝕒, 𝟚) :: Γ) 𝟚 ({0 ↦ Γ.length} e) τ𝕓 φ →
    wbt 𝟚 τ𝕒 →
    closed_at e Γ.length →
    typing Γ 𝟚 (.lam e) (.arrow τ𝕒 τ𝕓 ⊥) ⊤
  | app₁ : ∀ Γ f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
    typing Γ 𝟙 f (.arrow τ𝕒 τ𝕓 φ₀) φ₁ →
    typing Γ 𝟙 arg τ𝕒 φ₂ →
    typing Γ 𝟙 (.app f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂)
  | app₂ : ∀ Γ f arg τ𝕒 τ𝕓 φ₁ φ₂,
    typing Γ 𝟚 f (.arrow τ𝕒 τ𝕓 ⊥) φ₁ →
    typing Γ 𝟚 arg τ𝕒 φ₂ →
    typing Γ 𝟚 (.app f arg) τ𝕓 ⊤
  | fix₁ : ∀ Γ f τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
    φ₀ = φ₀ ∪ φ₁ →
    typing Γ 𝟙 f (.arrow (.arrow τ𝕒 τ𝕓 φ₀) (.arrow τ𝕒 τ𝕓 φ₀) φ₁) φ₂ →
    typing Γ 𝟙 (.fix f) (.arrow τ𝕒 τ𝕓 φ₀) φ₂
  | fix₂ : ∀ Γ f τ𝕒 τ𝕓 φ,
    typing Γ 𝟚 f (.arrow (.arrow τ𝕒 τ𝕓 ⊥) (.arrow τ𝕒 τ𝕓 ⊥) ⊥) φ →
    typing Γ 𝟚 (.fix f) (.arrow τ𝕒 τ𝕓 ⊥) ⊤
  | bracket : ∀ Γ e τ φ,
    typing Γ 𝟚 e τ φ →
    typing Γ 𝟙 (.bracket e) (.code τ) φ
  | escape : ∀ Γ e τ φ,
    typing Γ 𝟙 e (.code τ) φ →
    typing Γ 𝟚 (.escape e) τ φ
  | run : ∀ Γ e τ φ,
    typing Γ 𝟙 e (.code τ) φ →
    closed e →
    typing Γ 𝟙 (.run e) τ ⊥

/-
  Top-level typing judgement to ensure if an expression is code-generating (φ ≠ ⊥),
  then it will be of code type, thus allowing the core calculus to let-insert
  into produced values
-/
inductive typing_reification : TEnv → Expr → Ty → Effect → Prop
  | pure : ∀ Γ e τ, typing Γ 𝟙 e τ ⊥ → typing_reification Γ e τ ⊥
  | reify : ∀ Γ e τ φ, typing Γ 𝟙 e (.code τ) φ → typing_reification Γ e (.code τ) φ

lemma typing.regular : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → lc e :=
  by
  intros Γ 𝕊 e τ φ Hτ
  induction Hτ <;> try simp
  case lam₁ IH | lam₂ IH => rw [← lc.under_opening]; exact IH
  all_goals tauto

lemma typing.closed_at_env : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → closed_at e Γ.length :=
  by
  intros Γ 𝕊 e τ φ Hτ
  induction Hτ <;> try simp
  case fvar Hbinds _ | csp_nat Hbinds | csp_lam Hbinds _ =>
    rw [getr_exists_iff_index_lt_length]
    exact ⟨_, Hbinds⟩
  case run Hclosed => exact Hclosed
  all_goals tauto

lemma typing.wf : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → wf_at e Γ.length :=
  by
  intros Γ 𝕊 e τ φ Hτ
  constructor
  · apply typing.regular; exact Hτ
  · apply typing.closed_at_env; exact Hτ

lemma typing_reification.regular : ∀ Γ e τ φ, typing_reification Γ e τ φ → lc e :=
  by
  intros Γ e τ φ Hτ
  cases Hτ <;> (apply typing.regular; assumption)

lemma typing_reification.closed_at_env : ∀ Γ e τ φ, typing_reification Γ e τ φ → closed_at e Γ.length :=
  by
  intros Γ e τ φ Hτ
  cases Hτ <;> (apply typing.closed_at_env; assumption)

lemma typing_reification.wf : ∀ Γ e τ φ, typing_reification Γ e τ φ → wf_at e Γ.length :=
  by
  intros Γ e τ φ Hτ
  constructor
  · apply typing_reification.regular; exact Hτ
  · apply typing_reification.closed_at_env; exact Hτ

lemma typing.wbt : ∀ Γ 𝕊 e τ φ, typing Γ 𝕊 e τ φ → wbt 𝕊 τ :=
  by
  intros Γ 𝕊 e τ φ Hτ
  induction Hτ <;> try assumption
  case csp_nat => simp
  case csp_lam Hwbt => exact ⟨rfl, Hwbt⟩
  case lit₁ => simp
  case lit₂ => simp
  case lam₁ => simp_all
  case lam₂ => simp_all
  case app₁ IHf _ => exact IHf.right
  case app₂ IHf _ => exact IHf.right.right
  case fix₁ IHf => exact IHf.left
  case fix₂ IHf => exact IHf.right.left
  case run IH => exact Bracket.wbt.escape _ IH

end Bracket
