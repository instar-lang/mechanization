import Instar.TwoLevelRecBrack.Elab.Relation

namespace Bracket

/-!
The `lam` case recurses on `{0 ↦ Γ.length} e`, which is not a subterm of
`.lam e`, so structural recursion fails. `sizeOf` cannot be the measure either,
since `sizeOf (.bvar 0) = 1` but `sizeOf (.fvar n) = n + 1`; the constructor
count below, which `opening` preserves, can. -/

@[simp]
def Expr.size : Expr → ℕ
  | .bvar _ => 1
  | .fvar _ => 1
  | .lit _ => 1
  | .lam e => e.size + 1
  | .app f arg => f.size + arg.size + 1
  | .binary _ l r => l.size + r.size + 1
  | .run e => e.size + 1
  | .fix e => e.size + 1
  | .ifz c l r => c.size + l.size + r.size + 1
  | .bracket e => e.size + 1
  | .escape e => e.size + 1

lemma Expr.size_opening : ∀ e i n, (opening i (.fvar n) e).size = e.size :=
  by
  intros e i n
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i <;> simp [opening, HEq]
  | fvar z
  | lit z => simp
  | lam _ IH
  | run _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    simp [IH]
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    simp [IH₀, IH₁, IH₂]

/-- Total, option-valued elaboration. It mirrors the `elaboration` relation
where `none` stands for "no derivation". -/
def elab_expr : StEnv → Stage → Expr → Option Rec.Expr
  | _, _, .bvar _ => none
  | Γ, 𝕊, .fvar x =>
    match getr x Γ with
    | some 𝟙 =>
      match 𝕊 with
      | 𝟙 => some (.fvar x)
      | 𝟚 => some (.lift (.fvar x))
    | some 𝟚 =>
      match 𝕊 with
      | 𝟚 => some (.fvar x)
      | 𝟙 => none
    | none => none
  | _, 𝟙, .lit n => some (.lit n)
  | _, 𝟚, .lit n => some (.lift (.lit n))
  | Γ, 𝕊, .binary op l₀ r₀ => do
    let l₁ ← elab_expr Γ 𝕊 l₀
    let r₁ ← elab_expr Γ 𝕊 r₀
    match 𝕊 with
    | 𝟙 => return .binary₁ (elab_op op) l₁ r₁
    | 𝟚 => return .binary₂ (elab_op op) l₁ r₁
  | Γ, 𝕊, .app f₀ arg₀ => do
    let f₁ ← elab_expr Γ 𝕊 f₀
    let arg₁ ← elab_expr Γ 𝕊 arg₀
    match 𝕊 with
    | 𝟙 => return .app₁ f₁ arg₁
    | 𝟚 => return .app₂ f₁ arg₁
  | Γ, 𝕊, .ifz c₀ l₀ r₀ => do
    let c₁ ← elab_expr Γ 𝕊 c₀
    let l₁ ← elab_expr Γ 𝕊 l₀
    let r₁ ← elab_expr Γ 𝕊 r₀
    match 𝕊 with
    | 𝟙 => return .ifz₁ c₁ l₁ r₁
    | 𝟚 => return .ifz₂ c₁ l₁ r₁
  | Γ, 𝕊, .fix f₀ => do
    let f₁ ← elab_expr Γ 𝕊 f₀
    match 𝕊 with
    | 𝟙 => return .fix₁ f₁
    | 𝟚 => return .fix₂ f₁
  | Γ, 𝕊, .lam e₀ => do
    let e₁ ← elab_expr (𝕊 :: Γ) 𝕊 ({0 ↦ Γ.length} e₀)
    match 𝕊 with
    | 𝟙 => return .lam ({0 ↤ Γ.length} e₁)
    | 𝟚 => return .lift (.lam ({0 ↤ Γ.length} e₁))
  | Γ, 𝟙, .bracket e => elab_expr Γ 𝟚 e
  | _, 𝟚, .bracket _ => none
  | Γ, 𝟚, .escape e => elab_expr Γ 𝟙 e
  | _, 𝟙, .escape _ => none
  | Γ, 𝟙, .run e₀ => do
    let e₁ ← elab_expr Γ 𝟙 e₀
    return .run e₁
  | _, 𝟚, .run _ => none
  termination_by _ _ e => e.size
  decreasing_by all_goals (simp [Expr.size_opening] <;> omega)

abbrev elab_expr_reification (e₀ : Expr) : Option Rec.Expr := elab_expr [] 𝟙 e₀

/-- The shared part of the `lam` case, for both stages: opening undoes closing on
the elaborated body, and the closed body is again well formed under `.lam`. -/
lemma elab_expr.lam_body (Γ : StEnv) (𝕊 : Stage) (e₀ : Expr) (t : Rec.Expr)
    (Hrel : elaboration (𝕊 :: Γ) 𝕊 ({0 ↦ Γ.length} e₀) t)
    (Hlc : Rec.lc t)
    (Hclo : Rec.closed_at t (Γ.length + 1)) :
    elaboration (𝕊 :: Γ) 𝕊 ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} ({0 ↤ Γ.length} t)) ∧
      Rec.lc_at ({0 ↤ Γ.length} t) 1 ∧
      Rec.closed_at ({0 ↤ Γ.length} t) Γ.length :=
  ⟨by
    rw [Rec.identity.opening_closing 0 t Γ.length Hlc]
    exact Hrel,
  Rec.lc.under_closing t Γ.length 1 0 Nat.one_pos (Rec.lc.inc t 0 1 Hlc (Nat.zero_le 1)),
  (Rec.closed.under_closing t Γ.length 0).mp Hclo⟩

lemma elab_expr.elaboration_aux : ∀ Γ 𝕊 e₀ e₁,
    elab_expr Γ 𝕊 e₀ = some e₁ →
    elaboration Γ 𝕊 e₀ e₁ ∧ Rec.wf_at e₁ Γ.length
  | _, _, .bvar _, _, HElab => by
    simp [elab_expr] at HElab
  | Γ, 𝟙, .fvar x, e₁, HElab => by
    cases Hgetr : getr x Γ with
    | none => simp [elab_expr, Hgetr] at HElab
    | some 𝕊₀ =>
      cases 𝕊₀
      case static =>
        simp [elab_expr, Hgetr] at HElab
        cases HElab
        exact ⟨elaboration.fvar₁ Γ x Hgetr, by simp [Rec.wf_at, binds.lt_length Hgetr]⟩
      case dynamic => simp [elab_expr, Hgetr] at HElab
  | Γ, 𝟚, .fvar x, e₁, HElab => by
    cases Hgetr : getr x Γ with
    | none => simp [elab_expr, Hgetr] at HElab
    | some 𝕊₀ =>
      cases 𝕊₀
      case static =>
        simp [elab_expr, Hgetr] at HElab
        cases HElab
        exact ⟨elaboration.csp Γ x Hgetr, by simp [Rec.wf_at, binds.lt_length Hgetr]⟩
      case dynamic =>
        simp [elab_expr, Hgetr] at HElab
        cases HElab
        exact ⟨elaboration.fvar₂ Γ x Hgetr, by simp [Rec.wf_at, binds.lt_length Hgetr]⟩
  | Γ, 𝟙, .lit n, e₁, HElab => by
    simp [elab_expr] at HElab
    cases HElab
    exact ⟨elaboration.lit₁ Γ n, by simp [Rec.wf_at]⟩
  | Γ, 𝟚, .lit n, e₁, HElab => by
    simp [elab_expr] at HElab
    cases HElab
    exact ⟨elaboration.lit₂ Γ n, by simp [Rec.wf_at]⟩
  | Γ, 𝟙, .binary op l₀ r₀, e₁, HElab => by
    simp only [elab_expr, Bind.bind, Option.bind_eq_some_iff] at HElab
    have ⟨l₁, Hl, r₁, Hr, HEq⟩ := HElab
    cases HEq
    have ⟨Hrel, Hlc, Hclo⟩ := elab_expr.elaboration_aux Γ 𝟙 l₀ l₁ Hl
    have ⟨Hrel₀, Hlc₀, Hclo₀⟩ := elab_expr.elaboration_aux Γ 𝟙 r₀ r₁ Hr
    exact ⟨elaboration.binary₁ Γ op l₀ r₀ l₁ r₁ Hrel Hrel₀,
      ⟨⟨Hlc, Hlc₀⟩, Hclo, Hclo₀⟩⟩
  | Γ, 𝟚, .binary op l₀ r₀, e₁, HElab => by
    simp only [elab_expr, Bind.bind, Option.bind_eq_some_iff] at HElab
    have ⟨l₁, Hl, r₁, Hr, HEq⟩ := HElab
    cases HEq
    have ⟨Hrel, Hlc, Hclo⟩ := elab_expr.elaboration_aux Γ 𝟚 l₀ l₁ Hl
    have ⟨Hrel₀, Hlc₀, Hclo₀⟩ := elab_expr.elaboration_aux Γ 𝟚 r₀ r₁ Hr
    exact ⟨elaboration.binary₂ Γ op l₀ r₀ l₁ r₁ Hrel Hrel₀,
      ⟨⟨Hlc, Hlc₀⟩, Hclo, Hclo₀⟩⟩
  | Γ, 𝟙, .app f₀ arg₀, e₁, HElab => by
    simp only [elab_expr, Bind.bind, Option.bind_eq_some_iff] at HElab
    have ⟨f₁, Hf, arg₁, Harg, HEq⟩ := HElab
    cases HEq
    have ⟨Hrel, Hlc, Hclo⟩ := elab_expr.elaboration_aux Γ 𝟙 f₀ f₁ Hf
    have ⟨Hrel₀, Hlc₀, Hclo₀⟩ := elab_expr.elaboration_aux Γ 𝟙 arg₀ arg₁ Harg
    exact ⟨elaboration.app₁ Γ f₀ arg₀ f₁ arg₁ Hrel Hrel₀,
      ⟨⟨Hlc, Hlc₀⟩, Hclo, Hclo₀⟩⟩
  | Γ, 𝟚, .app f₀ arg₀, e₁, HElab => by
    simp only [elab_expr, Bind.bind, Option.bind_eq_some_iff] at HElab
    have ⟨f₁, Hf, arg₁, Harg, HEq⟩ := HElab
    cases HEq
    have ⟨Hrel, Hlc, Hclo⟩ := elab_expr.elaboration_aux Γ 𝟚 f₀ f₁ Hf
    have ⟨Hrel₀, Hlc₀, Hclo₀⟩ := elab_expr.elaboration_aux Γ 𝟚 arg₀ arg₁ Harg
    exact ⟨elaboration.app₂ Γ f₀ arg₀ f₁ arg₁ Hrel Hrel₀,
      ⟨⟨Hlc, Hlc₀⟩, Hclo, Hclo₀⟩⟩
  | Γ, 𝟙, .ifz c₀ l₀ r₀, e₁, HElab => by
    simp only [elab_expr, Bind.bind, Option.bind_eq_some_iff] at HElab
    have ⟨c₁, Hc, l₁, Hl, r₁, Hr, HEq⟩ := HElab
    cases HEq
    have ⟨Hrel, Hlc, Hclo⟩ := elab_expr.elaboration_aux Γ 𝟙 c₀ c₁ Hc
    have ⟨Hrel₀, Hlc₀, Hclo₀⟩ := elab_expr.elaboration_aux Γ 𝟙 l₀ l₁ Hl
    have ⟨Hrel₁, Hlc₁, Hclo₁⟩ := elab_expr.elaboration_aux Γ 𝟙 r₀ r₁ Hr
    exact ⟨elaboration.ifz₁ Γ c₀ l₀ r₀ c₁ l₁ r₁ Hrel Hrel₀ Hrel₁,
      ⟨⟨Hlc, Hlc₀, Hlc₁⟩, Hclo, Hclo₀, Hclo₁⟩⟩
  | Γ, 𝟚, .ifz c₀ l₀ r₀, e₁, HElab => by
    simp only [elab_expr, Bind.bind, Option.bind_eq_some_iff] at HElab
    have ⟨c₁, Hc, l₁, Hl, r₁, Hr, HEq⟩ := HElab
    cases HEq
    have ⟨Hrel, Hlc, Hclo⟩ := elab_expr.elaboration_aux Γ 𝟚 c₀ c₁ Hc
    have ⟨Hrel₀, Hlc₀, Hclo₀⟩ := elab_expr.elaboration_aux Γ 𝟚 l₀ l₁ Hl
    have ⟨Hrel₁, Hlc₁, Hclo₁⟩ := elab_expr.elaboration_aux Γ 𝟚 r₀ r₁ Hr
    exact ⟨elaboration.ifz₂ Γ c₀ l₀ r₀ c₁ l₁ r₁ Hrel Hrel₀ Hrel₁,
      ⟨⟨Hlc, Hlc₀, Hlc₁⟩, Hclo, Hclo₀, Hclo₁⟩⟩
  | Γ, 𝟙, .fix f₀, e₁, HElab => by
    simp only [elab_expr, Bind.bind, Option.bind_eq_some_iff] at HElab
    have ⟨f₁, Hf, HEq⟩ := HElab
    cases HEq
    have ⟨Hrel, Hlc, Hclo⟩ := elab_expr.elaboration_aux Γ 𝟙 f₀ f₁ Hf
    exact ⟨elaboration.fix₁ Γ f₀ f₁ Hrel, Hlc, Hclo⟩
  | Γ, 𝟚, .fix f₀, e₁, HElab => by
    simp only [elab_expr, Bind.bind, Option.bind_eq_some_iff] at HElab
    have ⟨f₁, Hf, HEq⟩ := HElab
    cases HEq
    have ⟨Hrel, Hlc, Hclo⟩ := elab_expr.elaboration_aux Γ 𝟚 f₀ f₁ Hf
    exact ⟨elaboration.fix₂ Γ f₀ f₁ Hrel, Hlc, Hclo⟩
  | Γ, 𝟙, .lam e₀, e₁, HElab => by
    simp only [elab_expr, Bind.bind, Option.bind_eq_some_iff] at HElab
    have ⟨t, Ht, HEq⟩ := HElab
    cases HEq
    have ⟨Hrel, Hlc, Hclo⟩ := elab_expr.elaboration_aux (𝟙 :: Γ) 𝟙 ({0 ↦ Γ.length} e₀) t Ht
    have ⟨Hbody, Hlc₁, Hclosed⟩ := elab_expr.lam_body Γ 𝟙 e₀ t Hrel Hlc Hclo
    exact ⟨elaboration.lam₁ Γ e₀ ({0 ↤ Γ.length} t) Hbody Hclosed, Hlc₁, Hclosed⟩
  | Γ, 𝟚, .lam e₀, e₁, HElab => by
    simp only [elab_expr, Bind.bind, Option.bind_eq_some_iff] at HElab
    have ⟨t, Ht, HEq⟩ := HElab
    cases HEq
    have ⟨Hrel, Hlc, Hclo⟩ := elab_expr.elaboration_aux (𝟚 :: Γ) 𝟚 ({0 ↦ Γ.length} e₀) t Ht
    have ⟨Hbody, Hlc₁, Hclosed⟩ := elab_expr.lam_body Γ 𝟚 e₀ t Hrel Hlc Hclo
    exact ⟨elaboration.lam₂ Γ e₀ ({0 ↤ Γ.length} t) Hbody Hclosed, Hlc₁, Hclosed⟩
  | Γ, 𝟙, .bracket e₀, e₁, HElab => by
    simp only [elab_expr] at HElab
    have ⟨Hrel, Hwf⟩ := elab_expr.elaboration_aux Γ 𝟚 e₀ e₁ HElab
    exact ⟨elaboration.bracket Γ e₀ e₁ Hrel, Hwf⟩
  | Γ, 𝟚, .bracket _, _, HElab => by
    simp [elab_expr] at HElab
  | Γ, 𝟚, .escape e₀, e₁, HElab => by
    simp only [elab_expr] at HElab
    have ⟨Hrel, Hwf⟩ := elab_expr.elaboration_aux Γ 𝟙 e₀ e₁ HElab
    exact ⟨elaboration.escape Γ e₀ e₁ Hrel, Hwf⟩
  | Γ, 𝟙, .escape _, _, HElab => by
    simp [elab_expr] at HElab
  | Γ, 𝟙, .run e₀, e₁, HElab => by
    simp only [elab_expr, Bind.bind, Option.bind_eq_some_iff] at HElab
    have ⟨t, Ht, HEq⟩ := HElab
    cases HEq
    have ⟨Hrel, Hlc, Hclo⟩ := elab_expr.elaboration_aux Γ 𝟙 e₀ t Ht
    exact ⟨elaboration.run Γ e₀ t Hrel, Hlc, Hclo⟩
  | Γ, 𝟚, .run _, _, HElab => by
    simp [elab_expr] at HElab
  termination_by _ _ e₀ _ _ => e₀.size
  decreasing_by all_goals (simp [Expr.size_opening] <;> omega)

lemma elab_expr.elaboration : ∀ Γ 𝕊 e₀ e₁,
    elab_expr Γ 𝕊 e₀ = some e₁ →
    elaboration Γ 𝕊 e₀ e₁ :=
  by
  intro Γ 𝕊 e₀ e₁ HElab
  apply (elab_expr.elaboration_aux Γ 𝕊 e₀ e₁ HElab).1

lemma elab_expr.some_of_typing : ∀ Γ 𝕊 e₀ τ φ,
    typing Γ 𝕊 e₀ τ φ →
    ∃ e₁, elab_expr Γ.unzip.snd 𝕊 e₀ = some e₁ :=
  by
  intros Γ 𝕊 e₀ τ φ Hτ
  induction Hτ with
  | fvar Γ 𝕊 x τ Hbinds Hwbt =>
    have Hgetr : getr x Γ.unzip.snd = some 𝕊 := binds.impl_stenv_binds Γ x τ 𝕊 Hbinds
    cases 𝕊
    case static => exact ⟨.fvar x, by simp only [elab_expr, Hgetr]⟩
    case dynamic => exact ⟨.fvar x, by simp only [elab_expr, Hgetr]⟩
  | csp_nat Γ x Hbinds | csp_lam Γ x _ _ _ Hbinds _ =>
    have Hgetr : getr x Γ.unzip.snd = some (𝟙 : Stage) :=
      binds.impl_stenv_binds Γ x _ (𝟙 : Stage) Hbinds
    exact ⟨.lift (.fvar x), by simp only [elab_expr, Hgetr]⟩
  | lit₁ Γ n => exact ⟨.lit n, by simp only [elab_expr]⟩
  | lit₂ Γ n => exact ⟨.lift (.lit n), by simp only [elab_expr]⟩
  | binary₁ Γ op l r φ₁ φ₂ _ _ IHl IHr =>
    have ⟨l₁, Hl⟩ := IHl
    have ⟨r₁, Hr⟩ := IHr
    exact ⟨.binary₁ (elab_op op) l₁ r₁, by simp only [elab_expr, Bind.bind, Option.bind, Option.pure_def, Hl, Hr]⟩
  | binary₂ Γ op l r φ₁ φ₂ _ _ IHl IHr =>
    have ⟨l₁, Hl⟩ := IHl
    have ⟨r₁, Hr⟩ := IHr
    exact ⟨.binary₂ (elab_op op) l₁ r₁, by simp only [elab_expr, Bind.bind, Option.bind, Option.pure_def, Hl, Hr]⟩
  | ifz₁ Γ c l r τ φ₁ φ₂ φ₃ _ _ _ IHc IHl IHr =>
    have ⟨c₁, Hc⟩ := IHc
    have ⟨l₁, Hl⟩ := IHl
    have ⟨r₁, Hr⟩ := IHr
    exact ⟨.ifz₁ c₁ l₁ r₁, by simp only [elab_expr, Bind.bind, Option.bind, Option.pure_def, Hc, Hl, Hr]⟩
  | ifz₂ Γ c l r τ φ₁ φ₂ φ₃ _ _ _ IHc IHl IHr =>
    have ⟨c₁, Hc⟩ := IHc
    have ⟨l₁, Hl⟩ := IHl
    have ⟨r₁, Hr⟩ := IHr
    exact ⟨.ifz₂ c₁ l₁ r₁, by simp only [elab_expr, Bind.bind, Option.bind, Option.pure_def, Hc, Hl, Hr]⟩
  | lam₁ Γ e τ𝕒 τ𝕓 φ _ Hwbt Hclosed IH =>
    have ⟨t, Ht⟩ := IH
    have Hunzip : ((τ𝕒, (𝟙 : Stage)) :: Γ).unzip.snd = (𝟙 : Stage) :: Γ.unzip.snd := by simp
    have Hlen : Γ.length = Γ.unzip.snd.length := by simp
    have Ht₁ : elab_expr ((𝟙 : Stage) :: Γ.unzip.snd) (𝟙 : Stage) ({0 ↦ Γ.unzip.snd.length} e) = some t := by
      rw [← Hunzip, ← Hlen]
      exact Ht
    exact ⟨.lam ({0 ↤ Γ.unzip.snd.length} t), by simp only [elab_expr, Bind.bind, Option.bind, Option.pure_def, Ht₁]⟩
  | lam₂ Γ e τ𝕒 τ𝕓 φ _ Hwbt Hclosed IH =>
    have ⟨t, Ht⟩ := IH
    have Hunzip : ((τ𝕒, (𝟚 : Stage)) :: Γ).unzip.snd = (𝟚 : Stage) :: Γ.unzip.snd := by simp
    have Hlen : Γ.length = Γ.unzip.snd.length := by simp
    have Ht₁ : elab_expr ((𝟚 : Stage) :: Γ.unzip.snd) (𝟚 : Stage) ({0 ↦ Γ.unzip.snd.length} e) = some t := by
      rw [← Hunzip, ← Hlen]
      exact Ht
    exact ⟨.lift (.lam ({0 ↤ Γ.unzip.snd.length} t)), by simp only [elab_expr, Bind.bind, Option.bind, Option.pure_def, Ht₁]⟩
  | app₁ Γ f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂ _ _ IHf IHarg =>
    have ⟨f₁, Hf⟩ := IHf
    have ⟨arg₁, Harg⟩ := IHarg
    exact ⟨.app₁ f₁ arg₁, by simp only [elab_expr, Bind.bind, Option.bind, Option.pure_def, Hf, Harg]⟩
  | app₂ Γ f arg τ𝕒 τ𝕓 φ₁ φ₂ _ _ IHf IHarg =>
    have ⟨f₁, Hf⟩ := IHf
    have ⟨arg₁, Harg⟩ := IHarg
    exact ⟨.app₂ f₁ arg₁, by simp only [elab_expr, Bind.bind, Option.bind, Option.pure_def, Hf, Harg]⟩
  | fix₁ Γ f τ𝕒 τ𝕓 φ₀ φ₁ φ₂ _ _ IHf =>
    have ⟨f₁, Hf⟩ := IHf
    exact ⟨.fix₁ f₁, by simp only [elab_expr, Bind.bind, Option.bind, Option.pure_def, Hf]⟩
  | fix₂ Γ f τ𝕒 τ𝕓 φ _ IHf =>
    have ⟨f₁, Hf⟩ := IHf
    exact ⟨.fix₂ f₁, by simp only [elab_expr, Bind.bind, Option.bind, Option.pure_def, Hf]⟩
  | bracket Γ e τ φ _ IH =>
    have ⟨t, Ht⟩ := IH
    exact ⟨t, by simp only [elab_expr, Ht]⟩
  | escape Γ e τ φ _ IH =>
    have ⟨t, Ht⟩ := IH
    exact ⟨t, by simp only [elab_expr, Ht]⟩
  | run Γ e τ φ _ Hclosed IH =>
    have ⟨t, Ht⟩ := IH
    exact ⟨.run t, by simp only [elab_expr, Bind.bind, Option.bind, Option.pure_def, Ht]⟩

lemma elab_expr.some_of_typing_reification : ∀ e₀ τ φ,
    Bracket.typing_reification ⦰ e₀ τ φ →
    ∃ e₁, elab_expr_reification e₀ = some e₁ :=
  by
  intros e₀ τ φ Hτ
  have Hunzip : (⦰ : TEnv).unzip.snd = [] := rfl
  cases Hτ with
  | pure τ Hty =>
    have ⟨e₁, HElab⟩ := elab_expr.some_of_typing ⦰ 𝟙 e₀ τ ⊥ Hty
    rw [Hunzip] at HElab
    exact ⟨e₁, HElab⟩
  | reify τ _ Hty =>
    have ⟨e₁, HElab⟩ := elab_expr.some_of_typing ⦰ 𝟙 e₀ (.code τ) φ Hty
    rw [Hunzip] at HElab
    exact ⟨e₁, HElab⟩

lemma elab_expr.typing_reification : ∀ e₀ τ φ,
    Bracket.typing_reification ⦰ e₀ τ φ →
    ∃ e₁, elab_expr_reification e₀ = some e₁ ∧
      Rec.typing_reification ⦰ e₁ (elab_type_reification τ) (elab_eff φ) :=
  by
  intros e₀ τ φ Hτ
  have ⟨e₁, HElab⟩ := elab_expr.some_of_typing_reification e₀ τ φ Hτ
  exact ⟨e₁, HElab, elaboration.typing_reification e₀ e₁ τ φ Hτ
    (elab_expr.elaboration [] 𝟙 e₀ e₁ HElab)⟩

end Bracket
