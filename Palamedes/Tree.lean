import Palamedes.Free
import Palamedes.Synth
import Palamedes.Support

attribute [-aesop] Subtype
attribute [-simp] Prod.forall

def foldTreeM [Monad m] (f : TreeF α β → m β) : Tree α → m β
  | .leaf => f .leaf
  | .node l x r => do
    f (.node (← foldTreeM f l) x (← foldTreeM f r))

def accTree
    {α γ : Type}
    (st : α → γ → γ × γ)
    (alg : TreeF α β → γ → β)
    (t : Tree α)
    (p : γ) :
    β :=
  alg (match t with
    | .leaf => .leaf
    | .node l x r =>
      let (lp, rp) := st x p
      .node (accTree st alg l lp) x (accTree st alg r rp)) p

instance : Functor (TreeF α) where
  map := λ f t =>
    match t with
    | .leaf => .leaf
    | .node l x r => .node (f l) x (f r)

@[aesop unsafe apply]
abbrev synth_unfoldTree
    {α β : Type}
    {f : TreeF α β → β}
    {b : β}
    (f' : (b : β) → CGen (λ v =>
      TreeF.rec
        (f .leaf = b)
        (λ l x r => f (.node l x r) = b) v)) :
    CGen (λ t => foldTree f t = b) := by
  exists .unfoldTree (λ b => (f' b).val) b
  intro t
  induction t generalizing b with
  | leaf =>
    simp_all [foldTree, (f' b).property .leaf]
  | node l x r ih_l ih_r =>
    simp_all [foldTree, (f' b).property (.node (foldTree f l) x (foldTree f r))]

@[aesop unsafe apply]
abbrev synth_unfoldTreeM
    {α β : Type}
    {f : TreeF α β → Option β}
    {b : β}
    (f' : (b : β) → CGen (λ v =>
      TreeF.rec
        (f .leaf = b)
        (λ l x r => f (.node l x r) = some b) v)) :
    CGen (λ t => foldTreeM f t = some b) := by
  exists .unfoldTree (λ b => (f' b).val) b
  intro t
  induction t generalizing b with
  | leaf =>
    simp_all [foldTreeM, (f' b).property .leaf]
  | node l x r ih_l ih_r =>
    simp_all
    apply Iff.intro
    . rintro ⟨bl, br, hx, hl, hr⟩
      simp_all [foldTreeM, ((f' b).property (.node bl x br)).mp hx]
    . intro h
      simp [foldTreeM] at h
      cases hl' : foldTreeM f l <;> simp_all
      cases hr' : foldTreeM f r <;> simp_all
      case some bl br =>
      simp_all [((f' b).property (.node bl x br)).mpr]

@[aesop unsafe apply]
abbrev synth_Tree.rec
    {α β : Type}
    {P : Prop}
    {Q : β → α → β → Prop}
    (g_leaf : CGen (λ () => P))
    (g_node : CGen (λ (p : β × α × β) => Q p.fst p.snd.fst p.snd.snd)) :
    CGen (TreeF.rec P Q) := by
  exists (pick
    (do let () ← g_leaf.val
        pure .leaf)
    (do let (bl, x, br) ← g_node.val
        pure (.node bl x br)))
  intro v
  simp_all
  match v with
  | .leaf =>
    have := g_leaf.property
    apply Iff.intro
    . rintro ⟨v', hv'⟩
      match v' with
      | 0 => simp_all
      | 1 => simp_all
    . intro h
      exists 0
      simp_all
  | .node bl x br =>
    have hl := g_node.property
    apply Iff.intro
    . rintro ⟨v', hv'⟩
      match v' with
      | 0 => simp_all
      | 1 =>
        simp_all
        aesop
    . intro h
      exists 1
      simp_all
      exists bl
      simp_all

@[aesop unsafe apply]
abbrev synth_cut'
    {P Q : α → Prop}
    {hequiv : ∀ v, P v ↔ Q v}
    (g : CGen P) :
    CGen Q := by
  obtain ⟨val, property⟩ := g
  exists val
  intro v
  simp_all only

@[simp]
theorem support_pick
    {v : α}
    {x y : Gen α} :
    v ∈ 〚pick x y〛 ↔ v ∈ 〚x〛∨ v ∈ 〚y〛:= by
  simp_all
  apply Iff.intro
  . rintro ⟨v', _, hv'⟩
    match v' with
    | 0 => simp_all
    | 1 => simp_all
  . intro h
    match h with
    | .inl h => exists 0
    | .inr h => exists 1

example : CGen (λ (t : Tree Nat) =>
    foldTree (TreeF.rec true (λ bl x br => bl && x == 2 && br)) t = true) := by
  apply synth_unfoldTree
  simp
  intro b
  match b with
  | true =>
    simp
    exists (pick (pure .leaf)
                 (pure (.node true 2 true)))
    intro v
    rw [support_pick]
    cases v <;> aesop
  | false => sorry

def isBST (lo hi : Int) : Tree Int → Bool
  | .leaf => true
  | .node l x r =>
    decide (lo ≤ x ∧ x ≤ hi) &&
    isBST lo (x - 1) l &&
    isBST (x + 1) hi r

def isBST' (lo hi : Int) (t : Tree Int) : Bool :=
  accTree
    (λ x => λ (lo, hi) => ((lo, x - 1), (x + 1, hi)))
    (λ t => match t with
            | .leaf => λ _ => true
            | .node l x r => λ (lo, hi) => l && decide (lo ≤ x ∧ x ≤ hi) && r)
    t
    (lo, hi)

attribute [local simp] isBST isBST' accTree in
theorem isBST_isBST' : isBST lo hi t = isBST' lo hi t := by
  induction t generalizing lo hi with
  | leaf => simp
  | node l x r ih_l ih_r =>
    simp
    rw [ih_l]
    rw [ih_r]
    simp_all
    clear ih_l
    clear ih_r
    by_cases hlt : lo ≤ x ∧ x ≤ hi
    . aesop
    . have : decide (lo ≤ x) = false ∨ decide (x ≤ hi) = false := by
        simp at hlt
        by_cases lo ≤ x
        . simp_all only [forall_const, decide_True, Bool.true_eq_false, decide_False, or_true]
        . simp_all only [false_implies, decide_False, decide_eq_false_iff_not, true_or]
      match this with
      | .inl h => rw [h]; simp
      | .inr h => rw [h]; simp

example {lo hi : Int} : CGen (λ t => isBST lo hi t = true) := by
  apply synth_cut
  case P =>
    exact λ t => isBST' lo hi t = true
  case hequiv =>
    intro v
    rw [isBST_isBST']
  simp only [isBST']
  sorry
