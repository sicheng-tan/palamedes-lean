import Palamedes.Support

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : (l : Tree α) → (x : α) → (r : Tree α) → Tree α

def treeToString [ToString α] : Tree α → String
  | .leaf => "(leaf)"
  | .node l x r => s!"(node {treeToString l} {x} {treeToString r})"

instance [ToString α] : ToString (Tree α) where
  toString := treeToString

inductive TreeF (α β : Type) where
  | leaf : TreeF α β
  | node : (l : β) → (x : α) → (r : β) → TreeF α β

def Tree.accu
    {α β σ : Type}
    (st : α → σ → σ × σ)
    (f : β → α → β → σ → β)
    (z : σ → β)
    (t : Tree α)
    (s : σ) :
    β :=
  match t with
  | .leaf => z s
  | .node l x r =>
    let (sl, sr) := st x s
    f (Tree.accu st f z l sl) x (Tree.accu st f z r sr) s

def Tree.fold
    {α β : Type}
    (f : β → α → β → β)
    (z : β)
    (t : Tree α) :
    β :=
  match t with
  | .leaf => z
  | .node l x r => f (Tree.fold f z l) x (Tree.fold f z r)

@[simp] theorem fold_leaf : Tree.fold f z .leaf = z := rfl
@[simp] theorem fold_node {x} {l r : Tree α} {f : β → α → β → β} {z} :
    Tree.fold f z (.node l x r) = f (Tree.fold f z l) x (Tree.fold f z r) := rfl

def Tree.foldM
    [Monad m]
    {α β : Type}
    (f : β → α → β → m β)
    (z : m β)
    (t : Tree α) :
    m β :=
  match t with
  | .leaf => z
  | .node l x r => do
    f (← Tree.foldM f z l) x (← Tree.foldM f z r)

@[simp] theorem foldM_leaf [Monad m] {f : β → α → β → m β} {z : m β} : Tree.foldM f z .leaf = z := rfl
@[simp] theorem foldM_cons [Monad m] [LawfulMonad m] {x : α} {l r : Tree α} {f : β → α → β → m β} {z : m β} :
    Tree.foldM f z (.node l x r) = l.foldM f z >>= λ vL => r.foldM f z >>= f vL x := by
  simp only [Tree.foldM]

def Tree.accuM
    [Monad m]
    {α β σ : Type}
    (st : α → σ → σ × σ)
    (f : β → α → β → σ → m β)
    (z : σ → m β)
    (t : Tree α)
    (s : σ) :
    m β :=
  match t with
  | .leaf => z s
  | .node l x r => do
    let (sl, sr) := st x s
    f (← Tree.accuM st f z l sl) x (← Tree.accuM st f z r sr) s

theorem fold_accuM
    [Monad m]
    {α β σ : Type}
    {st : α → σ → σ × σ}
    {s : σ}
    {t : Tree α}
    {z : σ → m β}
    {f : β → α → β → σ → m β}
    {f' : (σ → m β) → α → (σ → m β) → σ → m β} :
    f' = (λ bl x br => λ s => do
      let (sl, sr) := st x s
      f (← bl sl) x (← br sr) s) →
    Tree.fold f' z t s = Tree.accuM st f z t s := by
  induction t generalizing s <;> simp_all [Tree.fold, Tree.accuM]

def unfoldTree (n : Nat) (f : β → Gen (TreeF α β)) (b : β) : Gen (Option (Tree α)) :=
  match n with
  | 0 => pure none
  | n + 1 => do
    match (← f b) with
    | .leaf => pure (some .leaf)
    | .node bl x br => do
      let l ← unfoldTree n f bl
      let r ← unfoldTree n f br
      pure (do pure (.node (← l) x (← r)))

@[simp]
def support_unfoldTree (P : β → TreeF α β → Prop) (b : β) (xs : Tree α) : Prop :=
  match xs with
  | .leaf => P b .leaf
  | .node l x r => ∃ bl br,
    P b (.node bl x br) ∧
    support_unfoldTree P bl l ∧
    support_unfoldTree P br r

theorem unfoldTree_monotonic'
    {n : Nat}
    {f : β → Gen (TreeF α β)}
    {b : β} :
    .some v ∈ 〚unfoldTree n f b〛→
    .some v ∈ 〚unfoldTree (n + 1) f b〛:= by
  intro hn
  induction v generalizing n b with
  | leaf =>
    match n with
    | 0 => simp_all [unfoldTree]
    | .succ _ =>
      simp_all [unfoldTree, bind, optBind_bind]
      have ⟨v', hv'1, hv'2⟩ := hn
      exists v'
      match v' with
      | .leaf => simp_all
      | .node _ _ _ =>
        simp_all [bind, optBind_bind]
        have ⟨a, ⟨_, ⟨b, _, _⟩⟩⟩ := hv'2
        match a, b with
        | .some _, .some _ => simp_all
  | node l x r ihl ihr =>
    match n with
    | 0 => simp_all [unfoldTree]
    | .succ n' =>
      simp_all [unfoldTree, bind, optBind_bind]
      have ⟨v', hv'1, hv'2⟩ := hn
      exists v'
      match v' with
      | .node bl y br =>
        simp_all [unfoldTree, bind, optBind_bind]
        have ⟨ll, hll, rr, hrr, h⟩ := hv'2
        clear hv'2
        match ll, rr with
        | .none, _ => simp_all
        | _, .none => simp_all
        | .some ll, some rr =>
          simp_all [unfoldTree, bind, optBind_bind]
          cases h
          replace ihl := ihl hll
          replace ihr := ihr hrr
          clear hll
          clear hrr
          exists (some l)
          apply And.intro
          . aesop
          . aesop

theorem unfoldTree_monotonic
    {n m : Nat}
    {f : β → Gen (TreeF α β)}
    {b : β} :
    n ≤ m →
    .some v ∈ 〚unfoldTree n f b〛→
    .some v ∈ 〚unfoldTree m f b〛:= by
  intro hlt hn
  induction m generalizing n with
  | zero =>
    cases hlt
    simp_all
  | succ m' ih =>
    have : n = m' + 1 ∨ n ≤ m' := by cases hlt <;> simp_all
    match this with
    | .inl h => subst h; simp_all
    | .inr h =>
      have := ih h hn
      apply unfoldTree_monotonic' this

theorem support_unfoldTree_ok :
    support (.indexed (λ n => unfoldTree n f b)) = support_unfoldTree (λ b' => support (f b')) b := by
  funext t
  induction t generalizing b with
  | leaf =>
    simp_all
    apply Iff.intro
    . intro ⟨n, h⟩
      match n with
      | 0 => simp_all [unfoldTree]
      | n + 1 =>
        simp_all [unfoldTree, bind, optBind_bind]
        have ⟨v', hv'1, hv'2⟩ := h
        match v' with
        | .leaf => simp_all
        | .node _ _ _ =>
          simp_all [unfoldTree, bind, optBind_bind]
          have ⟨l'', hl'', r'', hr''⟩ := hv'2
          match l'', r'' with
          | .none, _ => simp_all
          | _, .none => simp_all
          | .some .leaf, .some (.node _ _ _) => simp_all [Option.bind]
          | .some (.node _ _ _), .some .leaf => simp_all [Option.bind]
          | .some (.node _ _ _), .some (.node _ _ _) => simp_all
    . intro h
      exists 1
      simp [unfoldTree, bind, optBind_bind]
      exists .leaf
  | node l x r ih_l ih_r =>
    simp_all
    apply Iff.intro
    . intro ⟨n, h⟩
      match n with
      | 0 => simp_all [unfoldTree]
      | n + 1 =>
        simp_all [unfoldTree, bind, optBind_bind]
        have ⟨v', hv'1, hv'2⟩ := h
        match v' with
        | .leaf => simp_all
        | .node bl'' x br'' =>
          simp_all [unfoldTree, bind, optBind_bind]
          have ⟨l'', hl'', r'', hr'', hv''⟩ := hv'2
          match l'', r'' with
          | .none, _ => simp_all
          | _, .none => simp_all
          | .some l, .some r =>
            simp_all
            obtain ⟨rfl, rfl, rfl⟩ := hv''
            exists bl''
            exists br''
            apply And.intro hv'1
            apply And.intro
            . apply (@ih_l bl'').mp
              exists n
            . apply (@ih_r br'').mp
              exists n
    . intro ⟨bl, br, hx, hl, hr⟩
      have ⟨nl, hl⟩ := ih_l.mpr hl
      have ⟨nr, hr⟩ := ih_r.mpr hr
      exists nl + nr + 1
      simp_all [unfoldTree, bind, optBind_bind]
      exists .node bl x br
      simp_all [unfoldTree, bind, optBind_bind]
      exists some l
      apply And.intro
      . apply @unfoldTree_monotonic _ _ _ nl (nl + nr)
        . simp
        . assumption
      . exists some r
        apply And.intro
        . apply @unfoldTree_monotonic _ _ _ nr (nl + nr)
          . simp
          . assumption
        . simp

theorem TreeF_or
    {α β : Type}
    {P : Prop}
    {Q : β → α → β → Prop}
    {t : TreeF α β} :
    TreeF.rec P Q t ↔ (P ∧ t = .leaf) ∨ (∃ bl x br, t = .node bl x br ∧ Q bl x br) := by
  match t with
  | .leaf => simp
  | .node _ _ _ => aesop

theorem Tree.merge_accuM
    {t : Tree α}
    {st₁ : α → σ₁ → σ₁ × σ₁}
    {st₂ : α → σ₂ → σ₂ × σ₂}
    {f₁ : β₁ → α → β₁ → σ₁ → Option β₁}
    {f₂ : β₂ → α → β₂ → σ₂ → Option β₂}
    {s₁ : σ₁} {s₂ : σ₂}
    {z₁ : σ₁ → Option β₁} {z₂ : σ₂ → Option β₂}
    {b₁ : β₁} {b₂ : β₂}
    :
    (t.accuM st₁ f₁ z₁ s₁ = some b₁ ∧ t.accuM st₂ f₂ z₂ s₂ = some b₂)
    ↔
    (t.accuM
      (λ x (s₁, s₂) => (((st₁ x s₁).1, (st₂ x s₂).1), ((st₁ x s₁).2, (st₂ x s₂).2)))
      (λ (bl₁, bl₂) x (br₁, br₂) (s₁, s₂) => do (← f₁ bl₁ x br₁ s₁, ← f₂ bl₂ x br₂ s₂))
      (λ (s₁, s₂) => do (← z₁ s₁, ← z₂ s₂))
      (s₁, s₂) = some (b₁, b₂)) := by
  induction t generalizing st₁ st₂ f₁ f₂ s₁ s₂ z₁ z₂ b₁ b₂
  case leaf =>
    simp [accuM]
    apply Iff.intro <;> intro H
    . -- (->)
      rw [H.left, H.right]
      simp
    . -- (<-)
      generalize Hx1 : (z₁ s₁) = x1
      generalize Hx2 : (z₂ s₂) = x2
      cases x1 <;> cases x2 <;> simp_all
  case node l x r IHl IHr =>
    apply Iff.intro
    . -- (->)
      intro ⟨ H1, H2 ⟩
      unfold accuM at H1 H2 ⊢
      simp at H1 H2 ⊢
      rw [Option.bind_eq_some] at H1 H2
      replace ⟨ lv₁, ⟨ Hlv₁, H1 ⟩  ⟩ := @H1
      replace ⟨ lv₂, ⟨ Hlv₂, H2 ⟩  ⟩ := @H2
      rw [Option.bind_eq_some] at H1 H2
      replace ⟨ rv₁, ⟨ Hrv₁, H1 ⟩  ⟩ := @H1
      replace ⟨ rv₂, ⟨ Hrv₂, H2 ⟩  ⟩ := @H2
      replace IHl := @IHl st₁ st₂ f₁ f₂ (st₁ x s₁).fst (st₂ x s₂).fst z₁ z₂ lv₁ lv₂
      replace IHr := @IHr st₁ st₂ f₁ f₂ (st₁ x s₁).snd (st₂ x s₂).snd z₁ z₂ rv₁ rv₂
      simp_all
    . -- (<-)
      intro H
      unfold accuM at H ⊢
      simp at H ⊢
      rw [Option.bind_eq_some] at H
      replace ⟨ ⟨ lv₁, lv₂ ⟩ , ⟨ Hlv, H ⟩  ⟩ := @H
      rw [Option.bind_eq_some] at H
      replace ⟨ ⟨ rv₁, rv₂ ⟩ , ⟨ Hrv, H ⟩ ⟩ := @H
      rw [Option.bind_eq_some] at H
      replace ⟨ v₁, ⟨ Hv₁ , H ⟩ ⟩ := @H
      rw [Option.bind_eq_some] at H
      replace ⟨ v₂, ⟨ Hv₂ , H ⟩ ⟩ := @H
      replace IHl := @IHl st₁ st₂ f₁ f₂ (st₁ x s₁).fst (st₂ x s₂).fst z₁ z₂ lv₁ lv₂
      replace IHr := @IHr st₁ st₂ f₁ f₂ (st₁ x s₁).snd (st₂ x s₂).snd z₁ z₂ rv₁ rv₂
      simp_all

theorem Tree.coerce_to_fold
    {t : Tree α}
    {f : Tree α → β} -- function to be coerced
    {z : β}
    {g : β → α → β → β}
    (h1 : f .leaf = z)
    (h2 : ∀ l x r, f (.node l x r) = g (f l) x (f r)) :
    f t = t.fold g z := by
  induction t <;> simp_all

theorem Tree.coerce_to_foldM
    {t : Tree α}
    {f : Tree α → Bool} -- function to be coerced
    {p : α → Bool}
    (h1 : f .leaf = true)
    (h2 : ∀ l x r, f (.node l x r) = (p x && f l && f r)) :
    (f t) = (t.foldM (λ () x () => guard (p x)) () = some ()) := by
  induction t with
  | leaf =>
    simp [h1]
  | node l x r ih =>
    simp [h2]
    match Hl : Tree.foldM (λ () y () => guard (p y)) () l with
    | none => simp_all
    | some vL => match Hr : Tree.foldM (λ () y () => guard (p y)) () r with
      | none => simp_all
      | some vR => simp_all [guard]

theorem Tree.coerce_to_accuM
    {t : Tree α}
    {f : Tree α → σ → Bool}
    {p : α → σ → Bool}
    {st₁ : α → σ → σ}
    {st₂ : α → σ → σ}
    {z : σ → Bool}
    (h₁ : ∀ s, f .leaf s = z s)
    (h₂ : ∀ l x r s, f (.node l x r) s = (p x s && f l (st₁ x s) && f r (st₂ x s))) :
    (f t s) = (t.accuM (λ x s => ⟨st₁ x s, st₂ x s⟩) (λ () x () s => guard (p x s)) (λ s => guard (z s)) s = some ()) := by
  induction t generalizing s with
  | leaf => simp [Tree.accuM, h₁, guard]
  | node l x r ih =>
    simp [Tree.accuM, h₂]
    apply Iff.intro
    . aesop
    . intro h
      simp_all [Option.bind, guard]
      aesop
