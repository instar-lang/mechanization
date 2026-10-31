import Instar.TwoLevelRecBrack.Syntax.Transform
import Instar.TwoLevelRecBrack.Syntax.Fv

namespace Bracket

-- closedness condition for free variables
@[simp]
def closed_at (e : Expr) (x : ℕ) : Prop :=
  match e with
  | .bvar _ => true
  | .fvar y => y < x
  | .lam e => closed_at e x
  | .app f arg => closed_at f x ∧ closed_at arg x
  | .binary _ l r => closed_at l x ∧ closed_at r x
  | .lit _ => true
  | .run e => closed_at e x
  | .fix e => closed_at e x
  | .ifz c l r => closed_at c x ∧ closed_at l x ∧ closed_at r x
  | .bracket e => closed_at e x
  | .escape e => closed_at e x

@[simp]
def closed e := closed_at e 0

-- closedness condition for bound variables
@[simp]
def lc_at (e : Expr) (i : ℕ) : Prop :=
  match e with
  | .bvar j => j < i
  | .fvar _ => true
  | .lam e => lc_at e (i + 1)
  | .app f arg => lc_at f i ∧ lc_at arg i
  | .binary _ l r => lc_at l i ∧ lc_at r i
  | .lit _ => true
  | .run e => lc_at e i
  | .fix e => lc_at e i
  | .ifz c l r => lc_at c i ∧ lc_at l i ∧ lc_at r i
  | .bracket e => lc_at e i
  | .escape e => lc_at e i

@[simp]
def lc e := lc_at e 0

@[simp]
def wf_at (e : Expr) (x : ℕ) : Prop := lc e ∧ closed_at e x

@[simp]
def wf (e : Expr) : Prop := wf_at e 0

lemma closed.inc : ∀ x y e, closed_at e x → x ≤ y → closed_at e y :=
  by
  intros x y e Hclosed Hxy
  induction e with
  | bvar | lit => simp
  | fvar => simp at *; omega
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lam _ IH
  | run _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    apply IH; apply Hclosed
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    simp; constructor
    apply IH₀; apply Hclosed.left; constructor
    apply IH₁; apply Hclosed.right.left
    apply IH₂; apply Hclosed.right.right

lemma closed.dec.not_in_fv : ∀ e x, closed_at e (x + 1) → x ∉ fv e → closed_at e x :=
  by
  intros e x Hclosed HFv
  induction e with
  | bvar | lit => simp
  | fvar y => simp at *; omega
  | lam _ IH
  | run _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    apply IH; apply Hclosed; apply HFv
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    simp at HFv; constructor
    apply IH₀; apply Hclosed.left; apply HFv.left
    apply IH₁; apply Hclosed.right; apply HFv.right
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    simp at HFv; constructor
    apply IH₀; apply Hclosed.left; apply HFv.left.left; constructor
    apply IH₁; apply Hclosed.right.left; apply HFv.left.right
    apply IH₂; apply Hclosed.right.right; apply HFv.right

lemma closed.dec.under_subst : ∀ x e v, closed_at v x → closed_at e (x + 1) → closed_at (subst x v e) x :=
  by
  intros x e v Hv He
  induction e with
  | bvar => apply He
  | fvar z =>
    by_cases HEq : x = z
    . simp [if_pos HEq]; apply Hv
    . simp [if_neg HEq]; simp at He; omega
  | lit => simp
  | lam _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    apply IH; apply He
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply He.left
    apply IH₁; apply He.right
  | run _ IH =>
    simp; apply IH; apply He
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    apply IH₀; apply He.left; constructor
    apply IH₁; apply He.right.left
    apply IH₂; apply He.right.right

lemma closed.under_closing : ∀ e x i, closed_at e (x + 1) ↔ closed_at ({i ↤ x} e) x :=
  by
  intros e x i
  induction e generalizing i with
  | bvar | lit => simp
  | fvar y =>
    by_cases HEq : x = y
    . simp [HEq]
    . simp [if_neg HEq]; omega
  | lam _ IH
  | run _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    apply IH
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    constructor
    . intro Hclosed; constructor
      apply (IH₀ _).mp; apply Hclosed.left
      apply (IH₁ _).mp; apply Hclosed.right
    . intro Hclosed; constructor
      apply (IH₀ _).mpr; apply Hclosed.left
      apply (IH₁ _).mpr; apply Hclosed.right
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    . intro Hclosed; constructor
      apply (IH₀ _).mp; apply Hclosed.left; constructor
      apply (IH₁ _).mp; apply Hclosed.right.left
      apply (IH₂ _).mp; apply Hclosed.right.right
    . intro Hclosed; constructor
      apply (IH₀ _).mpr; apply Hclosed.left; constructor
      apply (IH₁ _).mpr; apply Hclosed.right.left
      apply (IH₂ _).mpr; apply Hclosed.right.right

lemma closed.under_opening : ∀ e x i, closed_at e x → closed_at ({i ↦ x} e) (x + 1) :=
  by
  intros e x i
  induction e generalizing i with
  | fvar y => simp; omega
  | bvar j =>
    by_cases HEq : j = i
    . rw [HEq]; simp
    . simp; rw [if_neg HEq]; simp
  | lit => simp
  | lam _ IH
  | run _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    apply IH
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    intro Hclosed; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    intro Hclosed; constructor
    apply IH₀; apply Hclosed.left; constructor
    apply IH₁; apply Hclosed.right.left
    apply IH₂; apply Hclosed.right.right

lemma closed.under_shiftl : ∀ x y e n, closed_at e x → closed_at (shiftl y n e) (x + n) :=
  by
  intros x y e n Hclosed
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases HLe : y ≤ z
    . simp [if_pos HLe]; apply Hclosed
    . simp [if_neg HLe]; simp at Hclosed; omega
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => simp
  | lam _ IH
  | run _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    apply IH; apply Hclosed
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    apply IH₀; apply Hclosed.left; constructor
    apply IH₁; apply Hclosed.right.left
    apply IH₂; apply Hclosed.right.right

lemma closed.under_subst : ∀ x e v y, closed_at v y → closed_at e y → closed_at (subst x v e) y :=
  by
  intros x e v y Hv He
  induction e generalizing y with
  | bvar => apply He
  | fvar z =>
    by_cases HEq : x = z
    . simp [if_pos HEq]; apply Hv
    . simp [if_neg HEq]; apply He
  | lit => simp
  | lam _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    apply IH; apply Hv; apply He
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hv; apply He.left
    apply IH₁; apply Hv; apply He.right
  | run _ IH =>
    simp; apply IH; apply Hv; apply He
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    apply IH₀; apply Hv; apply He.left; constructor
    apply IH₁; apply Hv; apply He.right.left
    apply IH₂; apply Hv; apply He.right.right

lemma closed.under_shiftr : ∀ x e, closed_at e x → closed_at (shiftr x e) x :=
  by
  intros x e Hclosed
  induction e with
  | bvar j => simp
  | fvar z =>
    by_cases Hxz : x < z
    . simp [if_pos Hxz]; simp at Hclosed; omega
    . simp [if_neg Hxz]; simp at Hclosed; omega
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    simp; constructor
    apply IH₀; apply Hclosed.left
    apply IH₁; apply Hclosed.right
  | lit => simp
  | lam _ IH
  | run _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    apply IH; apply Hclosed
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    apply IH₀; apply Hclosed.left; constructor
    apply IH₁; apply Hclosed.right.left
    apply IH₂; apply Hclosed.right.right

lemma closed.dec.under_shiftr :
  ∀ x y e, closed_at e (x + y + 1) → y ∉ fv e → closed_at (shiftr y e) (x + y) :=
  by
  intros x y e Hclosed HFv
  cases x
  case zero =>
    simp at *
    apply closed.under_shiftr
    apply closed.dec.not_in_fv
    apply Hclosed; apply HFv
  case succ x =>
    induction e with
    | bvar | lit => simp
    | fvar z =>
      by_cases HEq : y < z
      . simp [if_pos HEq]; simp at Hclosed; omega
      . simp [if_neg HEq]; simp at Hclosed; omega
    | lam _ IH
    | run _ IH
    | fix _ IH
    | bracket _ IH
    | escape _ IH =>
      apply IH; apply HFv; apply Hclosed
    | app _ _ IH₀ IH₁
    | binary _ _ _ IH₀ IH₁ =>
      simp at HFv; constructor
      apply IH₀; apply HFv.left; apply Hclosed.left
      apply IH₁; apply HFv.right; apply Hclosed.right
    | ifz _ _ _ IH₀ IH₁ IH₂ =>
      simp at HFv; constructor
      apply IH₀; apply HFv.left.left; apply Hclosed.left; constructor
      apply IH₁; apply HFv.left.right; apply Hclosed.right.left
      apply IH₂; apply HFv.right; apply Hclosed.right.right

lemma closed.under_erase : ∀ e x, closed_at e x ↔ closed_at ‖e‖ x :=
  by
  intros e x
  induction e with
  | fvar | lit | bvar => simp
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

lemma closed_impl_not_in_fv :
  ∀ x y e,
    closed_at e x →
    y ≥ x →
    y ∉ fv e :=
  by
  intros x y e Hclosed HGe HIn
  induction e with
  | bvar | lit => nomatch HIn
  | fvar => simp at *; omega
  | lam _ IH
  | run _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    apply IH; apply Hclosed; apply HIn
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    cases HIn
    case inl H₀ =>
      apply IH₀; apply Hclosed.left; apply H₀
    case inr H₁ =>
      apply IH₁; apply Hclosed.right; apply H₁
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    cases HIn
    case inl HIn =>
      cases HIn
      case inl H₀ =>
        apply IH₀; apply Hclosed.left; apply H₀
      case inr H₁ =>
        apply IH₁; apply Hclosed.right.left; apply H₁
    case inr H₂ =>
      apply IH₂; apply Hclosed.right.right; apply H₂

lemma closed_iff_fv_empty : ∀ e, closed e ↔ fv e = ∅ :=
  by
  intro e
  induction e with
  | bvar => simp
  | fvar => simp
  | lit => simp
  | lam _ IH
  | run _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    apply IH
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    constructor
    . intro HFv; simp at HFv
      simp; constructor
      apply IH₀.mp; apply HFv.left
      apply IH₁.mp; apply HFv.right
    . intro Hclosed; simp at Hclosed
      simp; constructor
      apply IH₀.mpr; apply Hclosed.left
      apply IH₁.mpr; apply Hclosed.right
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    . intro HFv; simp at HFv
      simp; constructor; constructor
      apply IH₀.mp; apply HFv.left
      apply IH₁.mp; apply HFv.right.left
      apply IH₂.mp; apply HFv.right.right
    . intro Hclosed; simp at Hclosed
      simp; constructor
      apply IH₀.mpr; apply Hclosed.left.left; constructor
      apply IH₁.mpr; apply Hclosed.left.right
      apply IH₂.mpr; apply Hclosed.right

lemma lc.inc: ∀ e i j, lc_at e i → i ≤ j → lc_at e j :=
  by
  intros e i j Hclosed HLe
  induction e generalizing i j with
  | bvar => simp at *; omega
  | fvar | lit => simp
  | lam _ IH
  | run _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    apply IH; apply Hclosed; omega
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hclosed.left; omega
    apply IH₁; apply Hclosed.right; omega
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    apply IH₀; apply Hclosed.left; omega; constructor
    apply IH₁; apply Hclosed.right.left; omega
    apply IH₂; apply Hclosed.right.right; omega

lemma lc.under_opening : ∀ i x e, lc_at ({i ↦ x} e) i ↔ lc_at e (i + 1) :=
  by
  intros i x e
  induction e generalizing i with
  | bvar j =>
    by_cases HEq : j = i
    . simp [if_pos HEq]; omega
    . simp [if_neg HEq]; omega
  | fvar => simp
  | lit => simp
  | lam _ IH
  | run _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    apply IH
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    constructor
    . intro Hlc; constructor
      apply (IH₀ _).mp; apply Hlc.left
      apply (IH₁ _).mp; apply Hlc.right
    . intro Hlc; constructor
      apply (IH₀ _).mpr; apply Hlc.left
      apply (IH₁ _).mpr; apply Hlc.right
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    . intro Hlc; constructor
      apply (IH₀ _).mp; apply Hlc.left; constructor
      apply (IH₁ _).mp; apply Hlc.right.left
      apply (IH₂ _).mp; apply Hlc.right.right
    . intro Hlc; constructor
      apply (IH₀ _).mpr; apply Hlc.left; constructor
      apply (IH₁ _).mpr; apply Hlc.right.left
      apply (IH₂ _).mpr; apply Hlc.right.right

lemma lc.under_closing : ∀ e x i j, j < i → lc_at e i → lc_at ({j ↤ x} e) i :=
  by
  intros e x i j Hlt
  induction e generalizing i j with
  | bvar | lit => simp
  | fvar y =>
    by_cases HEq : x = y
    . rw [HEq]; simp; omega
    . simp; rw [if_neg HEq]; simp
  | lam _ IH
  | run _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    apply IH; omega
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    intro Hlc; constructor
    apply IH₀; omega; apply Hlc.left
    apply IH₁; omega; apply Hlc.right
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    intro Hlc; constructor
    apply IH₀; omega; apply Hlc.left; constructor
    apply IH₁; omega; apply Hlc.right.left
    apply IH₂; omega; apply Hlc.right.right

lemma lc.under_subst : ∀ x e v i, lc_at v i → lc_at e i → lc_at (subst x v e) i :=
  by
  intros x e v i Hv He
  induction e generalizing i with
  | bvar => apply He
  | fvar y =>
    by_cases HEq : x = y
    . simp [if_pos HEq]; apply Hv
    . simp [if_neg HEq]
  | lit => simp
  | lam _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    apply IH; apply lc.inc
    apply Hv; omega; apply He
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply Hv; apply He.left
    apply IH₁; apply Hv; apply He.right
  | run _ IH =>
    apply IH; apply Hv; apply He
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    constructor
    apply IH₀; apply Hv; apply He.left; constructor
    apply IH₁; apply Hv; apply He.right.left
    apply IH₂; apply Hv; apply He.right.right

lemma lc.under_erase : ∀ e i, lc_at e i ↔ lc_at ‖e‖ i :=
  by
  intros e i
  induction e generalizing i with
  | fvar | lit | bvar => simp
  | run _ IH
  | lam _ IH
  | fix _ IH
  | bracket _ IH
  | escape _ IH =>
    simp [IH]
  | app _ _ IH₀ IH₁
  | binary _ _ _ IH₀ IH₁ =>
    simp [IH₀, IH₁]
  | ifz _ _ _ IH₀ IH₁ IH₂ =>
    simp [IH₀, IH₁, IH₂]

@[simp]
lemma erasure_opening_commute : ∀ (e : Bracket.Expr) i x, ‖{i ↦ x} e‖ = {i ↦ x} ‖e‖ :=
  by
  intro e
  induction e <;> intro i x <;> simp_all
  case bvar => split_ifs <;> simp

end Bracket
