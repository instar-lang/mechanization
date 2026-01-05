import Mathlib.Data.Set.Insert
import Instar.TwoLevelRec.Syntax.Transform

@[simp]
def fv : Expr → Set ℕ
  | .bvar _ => ∅
  | .fvar x => { x }
  | .lam e => fv e
  | .lift e => fv e
  | .app₁ f arg => fv f ∪ fv arg
  | .app₂ f arg => fv f ∪ fv arg
  | .lit _ => ∅
  | .binary₁ _ l r => fv l ∪ fv r
  | .binary₂ _ l r => fv l ∪ fv r
  | .run e => fv e
  | .code e => fv e
  | .reflect e => fv e
  | .lam𝕔 e => fv e
  | .lets b e => fv b ∪ fv e
  | .lets𝕔 b e => fv b ∪ fv e
  | .fix₁ e => fv e
  | .fix₂ e => fv e
  | .ifz₁ c l r => fv c ∪ fv l ∪ fv r
  | .ifz₂ c l r => fv c ∪ fv l ∪ fv r

lemma fv.under_opening : ∀ i v e, fv (opening i v e) ⊆ fv v ∪ fv e :=
  by
  intros i v e
  induction e generalizing i with
  | bvar j =>
    simp; by_cases HEq : j = i
    . rw [if_pos HEq]
    . rw [if_neg HEq]; simp
  | fvar z => simp
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; constructor
    . apply Set.Subset.trans; apply IH₀
      apply Set.union_subset_union; rfl; simp
    . apply Set.Subset.trans; apply IH₁
      apply Set.union_subset_union; rfl; simp
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor; constructor
    . apply Set.Subset.trans; apply IH₀
      apply Set.union_subset_union; rfl
      apply Set.subset_union_of_subset_left; simp
    . apply Set.Subset.trans; apply IH₁
      apply Set.union_subset_union; rfl
      apply Set.subset_union_of_subset_left; simp
    . apply Set.Subset.trans; apply IH₂
      apply Set.union_subset_union; rfl
      apply Set.subset_union_of_subset_right; rfl

lemma fv.under_closing : ∀ i x e, fv (closing i x e) = fv e \ { x } :=
  by
  intros i x e
  induction e generalizing i with
  | bvar => simp
  | fvar y =>
    by_cases HEq : x = y
    . simp [if_pos HEq]
      simp [HEq]
    . simp [if_neg HEq]
      rw [Set.diff_singleton_eq_self]
      simp; apply HEq
  | lit => simp
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]
    rw [Set.union_diff_distrib]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp [IH₀, IH₁, IH₂]
    rw [Set.union_diff_distrib]
    rw [Set.union_diff_distrib]

lemma fv.under_codify : ∀ e i, fv e = fv (codify i e) :=
  by
  intros e i
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]
    . simp [if_neg HEq]
  | fvar => rfl
  | lit => rfl
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | fix₁ _ IH
  | fix₂ _ IH => apply IH
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp; rw [IH₀, IH₁]
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp; rw [IH₀, IH₁, IH₂]

lemma not_in_fv.under_opening :
  ∀ x y i e,
    x ∉ fv e →
    x ≠ y →
    x ∉ fv ({i ↦ y} e) :=
  by
  intros x y i e HNotIn HNe HIn
  apply HNotIn
  have H : fv ({i ↦ y} e) ⊆ { y } ∪ fv e := by apply fv.under_opening
  rw [Set.subset_def] at H
  cases (H x HIn)
  case inl => simp at *; omega
  case inr => assumption

lemma not_in_fv.under_subst :
  ∀ x e v,
    x ∉ fv v →
    x ∉ fv (subst x v e) :=
  by
  intros x e v HNotIn HIn
  apply HNotIn
  induction e with
  | bvar j => nomatch HIn
  | fvar y =>
    by_cases HEq : x = y
    . simp [if_pos HEq] at HIn
      apply HIn
    . simp [if_neg HEq] at HIn
      contradiction
  | lit => nomatch HIn
  | lam _ IH
  | lift _ IH
  | lam𝕔 _ IH
  | code _ IH
  | reflect _ IH
  | run _ IH
  | fix₁ _ IH
  | fix₂ _ IH =>
    apply IH; apply HIn
  | app₁ _ _ IH₀ IH₁
  | app₂ _ _ IH₀ IH₁
  | binary₁ _ _ _ IH₀ IH₁
  | binary₂ _ _ _ IH₀ IH₁
  | lets _ _ IH₀ IH₁
  | lets𝕔 _ _ IH₀ IH₁ =>
    simp at HIn
    cases HIn
    case inl HIn =>
      apply IH₀; apply HIn
    case inr HIn =>
      apply IH₁; apply HIn
  | ifz₁ _ _ _ IH₀ IH₁ IH₂
  | ifz₂ _ _ _ IH₀ IH₁ IH₂ =>
    simp at HIn
    cases HIn
    case inl HIn =>
      cases HIn
      case inl HIn =>
        apply IH₀; apply HIn
      case inr HIn =>
        apply IH₁; apply HIn
    case inr HIn =>
      apply IH₂; apply HIn
