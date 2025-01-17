import Palamedes.Synth
import Mathlib.Tactic.Convert

abbrev synth_pure'
    (h : P = (λ v => v = a))
    : CGen P := by
  exists (pure a)
  rw [h]
  simp

abbrev synth_bind'
    {P : α → Prop}
    {Q : α → β → Prop}
    (h : R = (λ v => ∃ a, P a ∧ Q a v))
    (hb : CGen P)
    (hf : (a : α) → CGen (Q a))
    : CGen R := by
  rw [h]
  apply synth_bind hb hf

abbrev synth_accuTreeM'
    {α β σ : Type}
    {R : Tree α → Prop}
    {st : α → σ → σ × σ}
    {f : β → α → β → σ → Option β}
    {z : σ → Option β}
    {s : σ}
    {b : β}
    (h : R = (λ v => Tree.accuM st f z v s = some b))
    (g : (b : β) → (s : σ) → CGen (TreeF.rec (z s = some b) (λ bl a br => f bl a br s = some b))) :
    CGen R := by
  rw [h]
  apply synth_accuTreeM g

attribute [simp]
  guard
  failure
  ite -- NOTE This may be a problem
  deforest_decidable_bind
  deforest_decidable_eq
  decidable_or
  ListF_or
  TreeF_or
  fold_foldM
  merge_foldM
attribute [-simp]
  Prod.forall
attribute [-aesop]
  Subtype
add_aesop_rules unsafe [
  apply synth_bind,
  apply synth_bind_arb,
  apply synth_or,
  apply synth_pure,
  apply synth_true,
  apply synth_tuple,
  apply synth_unfoldM,
  apply synth_accuM,
  apply synth_accuTreeM,
  apply synth_between,
  (by (conv => congr; intro v; congr; intro x; rw [and_comm]); apply synth_bind),
  apply synth_pure'
]
add_aesop_rules 5% [
  cases Nat,
  cases Bool,
]

def genTwo : CGen (λ v => v = 2) := by
  aesop

def genTwo' : CGen (λ v => 2 = v) := by
  aesop

theorem foldTree_accuTreeM
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
    Tree.accuM st f z t s = Tree.fold f' z t s := by
  induction t generalizing s <;> simp_all [Tree.accuM, Tree.fold]

@[simp]
def isBST (lo hi : Nat) (t : Tree Nat) : Option Unit :=
  Tree.fold (λ fl x fr => λ (p : Nat × Nat) => do
              guard (p.fst ≤ x)
              guard (x ≤ p.snd)
              fl (p.fst, x - 1)
              fr (x + 1, p.snd))
            (λ _ => pure ())
            t
            (lo, hi)
