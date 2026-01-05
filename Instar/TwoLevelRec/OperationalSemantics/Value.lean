import Instar.TwoLevelRec.Syntax.Defs

inductive value : Expr → Prop where
  | lam : ∀ e, lc (.lam e) → value (.lam e)
  | lit : ∀ n, value (.lit n)
  | code : ∀ e, lc e → value (.code e)

lemma lc.value : ∀ e, value e → lc e := by
  intro e Hvalue
  cases Hvalue with
  | lam _ Hclosed => apply Hclosed
  | lit => simp
  | code _ Hclosed => apply Hclosed

instance lc_at.decidable (e : Expr) (i : Nat) : Decidable (lc_at e i) :=
  match e with
  | .bvar j => if h : j < i then isTrue h else isFalse h
  | .fvar _ => isTrue (by simp)
  | .lam e => lc_at.decidable e (i + 1)
  | .lift e => lc_at.decidable e i
  | .app₁ f arg =>
    match lc_at.decidable f i, lc_at.decidable arg i with
    | isTrue Hf, isTrue Harg => isTrue ⟨Hf, Harg⟩
    | isFalse Hf, _ => isFalse (λ H => Hf H.left)
    | _, isFalse Harg => isFalse (λ H => Harg H.right)
  | .app₂ f arg =>
    match lc_at.decidable f i, lc_at.decidable arg i with
    | isTrue Hf, isTrue Harg => isTrue ⟨Hf, Harg⟩
    | isFalse Hf, _ => isFalse (λ H => Hf H.left)
    | _, isFalse Harg => isFalse (λ H => Harg H.right)
  | .lit _ => isTrue (by simp)
  | .binary₁ _ l r =>
    match lc_at.decidable l i, lc_at.decidable r i with
    | isTrue Hl, isTrue Hr => isTrue ⟨Hl, Hr⟩
    | isFalse Hr, _ => isFalse (λ H => Hr H.left)
    | _, isFalse Hr => isFalse (λ H => Hr H.right)
  | .binary₂ _ l r =>
    match lc_at.decidable l i, lc_at.decidable r i with
    | isTrue Hl, isTrue Hr => isTrue ⟨Hl, Hr⟩
    | isFalse Hr, _ => isFalse (λ H => Hr H.left)
    | _, isFalse Hr => isFalse (λ H => Hr H.right)
  | .run e => lc_at.decidable e i
  | .code e => lc_at.decidable e i
  | .reflect e => lc_at.decidable e i
  | .lam𝕔 e => lc_at.decidable e (i + 1)
  | .lets b e =>
    match lc_at.decidable b i, lc_at.decidable e (i + 1) with
    | isTrue Hb, isTrue He => isTrue ⟨Hb, He⟩
    | isFalse Hb, _ => isFalse (λ H => Hb H.left)
    | _, isFalse He => isFalse (λ H => He H.right)
  | .lets𝕔 b e =>
    match lc_at.decidable b i, lc_at.decidable e (i + 1) with
    | isTrue Hb, isTrue He => isTrue ⟨Hb, He⟩
    | isFalse Hb, _ => isFalse (λ H => Hb H.left)
    | _, isFalse He => isFalse (λ H => He H.right)
  | .fix₁ e => lc_at.decidable e i
  | .fix₂ e => lc_at.decidable e i
  | .ifz₁ c l r =>
    match lc_at.decidable c i, lc_at.decidable l i, lc_at.decidable r i with
    | isTrue Hc, isTrue Hl, isTrue Hr => isTrue ⟨Hc, Hl, Hr⟩
    | isFalse Hc, _, _ => isFalse (λ H => Hc H.left)
    | _, isFalse Hr, _ => isFalse (λ H => Hr H.right.left)
    | _, _, isFalse Hr => isFalse (λ H => Hr H.right.right)
  | .ifz₂ c l r =>
    match lc_at.decidable c i, lc_at.decidable l i, lc_at.decidable r i with
    | isTrue Hc, isTrue Hl, isTrue Hr => isTrue ⟨Hc, Hl, Hr⟩
    | isFalse Hc, _, _ => isFalse (λ H => Hc H.left)
    | _, isFalse Hr, _ => isFalse (λ H => Hr H.right.left)
    | _, _, isFalse Hr => isFalse (λ H => Hr H.right.right)

instance value.decidable (e : Expr) : Decidable (value e) :=
  match e with
  | .lam e =>
    match lc_at.decidable e 1 with
    | isTrue Hlc => isTrue (by apply value.lam; apply Hlc)
    | isFalse Hlc => isFalse (by intros Hvalue; apply Hlc; apply lc.value _ Hvalue)
  | .lit _ => isTrue (by apply value.lit)
  | .code e =>
    match lc_at.decidable e 0 with
    | isTrue Hlc => isTrue (by apply value.code; apply Hlc)
    | isFalse Hlc => isFalse (by intros Hvalue; apply Hlc; apply lc.value _ Hvalue)
  | .bvar _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .fvar _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .lift _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .app₁ _ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .app₂ _ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .binary₁ _ _ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .binary₂ _ _ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .run _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .reflect _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .lam𝕔 _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .lets _ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .lets𝕔 _ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .fix₁ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .fix₂ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .ifz₁ _ _ _ => isFalse (by intros Hvalue; nomatch Hvalue)
  | .ifz₂ _ _ _ => isFalse (by intros Hvalue; nomatch Hvalue)
