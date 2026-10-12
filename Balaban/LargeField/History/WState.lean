module

public import Balaban.LargeField.History.K1
import Mathlib.Tactic.Linarith

/-!
# Window states, bookkeeping data and the transitions (T1)–(T7) (Part I, §I.4.3–§I.4.4)

`WState` is the three-way window state `Pre / Pending(q, ν) / Active(q, ν, 𝓜)` (Definition I.4.6),
`Book` the bookkeeping data of a component that the counter reads (state, smallness clock `s`,
spine length, and whether the spine is a point).

The derived data (`Book.q`, `Book.nu`, `Book.M`), the ripeness time `t^*` (`Setting.tStar`), the
bank `U` (`Setting.bank`), the admissibility predicate (B.1) and the transitions are definitions;
`StateRule` and `BookRule` say that the bookkeeping of a component after a step is the one the
rules of Definition I.4.7 and (T1)–(T5) prescribe, with the arbitrary choices of the construction
kept as data.
-/

@[expose] public section

namespace Balaban.LargeField

/-- The window state of a component (Definition I.4.6). -/
inductive WState where
  | pre : WState
  | pending (q ν : ℕ) : WState
  | active (q ν : ℕ) (M : Finset ℕ) : WState

/-- The bookkeeping data of a component read by the counter: window state, smallness clock `s`,
length of the spine, and the flag "the spine is a point". -/
structure Book where
  st : WState
  s : ℕ
  len : ℝ
  pt : Prop

namespace WState

open Classical in
/-- The state after a restart (T2), (T3), (T5): a point spine is a certified entry. -/
noncomputable def restart (μ : ℕ) (pt' : Prop) : WState :=
  if pt' then .active μ 1 ∅ else .pre

end WState

namespace Book

/-- The core scale `q` (for `Pre`, `q := s`). -/
def q (b : Book) : ℕ :=
  match b.st with
  | .pre => b.s
  | .pending q _ => q
  | .active q _ _ => q

/-- The number of pieces `ν` (for `Pre`, `ν := 1`). -/
def nu (b : Book) : ℕ :=
  match b.st with
  | .pre => 1
  | .pending _ ν => ν
  | .active _ ν _ => ν

/-- The merge record `𝓜` (empty for `Pre` and `Pending`). -/
def M (b : Book) : Finset ℕ :=
  match b.st with
  | .active _ _ M => M
  | _ => ∅

/-- The component is in an `Active` state. -/
def IsActive (b : Book) : Prop := ∃ q ν M, b.st = .active q ν M

/-- The component is in a `Pending` state. -/
def IsPending (b : Book) : Prop := ∃ q ν, b.st = .pending q ν

/-- The book of a kept ripe component after `R^{(k)}`: `Active(k, 1, ∅)`, the spine and the
clock `s` are kept. -/
def kept (k : ℕ) (b : Book) : Book := { b with st := .active k 1 ∅ }

end Book

namespace WState

open Classical in
/-- The state after a pure shadow (T1). -/
noncomputable def shadow (μ : ℕ) (pt' : Prop) (b : Book) : WState :=
  match b.st with
  | .pre => if pt' then .active μ 1 ∅ else .pre
  | .pending q ν => if μ < q then .pending q ν else .active q ν ∅
  | .active q ν M => .active q ν M

end WState

namespace Setting

variable (S : Setting)

/-- The ripeness time `t^* = max {q + n_q(q), s + n_2(s)}`. -/
noncomputable def tStar (b : Book) : ℕ := max (b.q + S.nq b.q) (b.s + S.n2 b.s)

/-- The bank `U = ½ ∑_{ξ ∈ 𝓜} τ_ξ`. -/
noncomputable def bank (b : Book) : ℝ := 1 / 2 * ∑ ξ ∈ b.M, S.tau ξ

/-- Admissibility (B.1) of a book at scale `k`. -/
def Admissible (k : ℕ) (b : Book) : Prop :=
  match b.st with
  | .pre => ¬ b.pt
  | .pending q ν => k < q ∧ q ≤ k + S.h k + 1 ∧ 1 ≤ ν ∧ ν ≤ S.numax k
  | .active q ν M => q ≤ k ∧ 1 ≤ ν ∧ ν ≤ S.numax k ∧ ∀ ξ ∈ M, q < ξ ∧ ξ ≤ k

/-- A component of `Z^pre_k` is ripe if it is `Active` and `t^* = k`. -/
def Ripe (k : ℕ) (b : Book) : Prop := b.IsActive ∧ S.tStar b = k

open Classical in
/-- The book of a non-removed component of `Z_k` obtained from its pre-`R` book. -/
noncomputable def postBook (k0 k : ℕ) (b : Book) : Book :=
  if 1 ≤ k ∧ k ≤ k0 ∧ S.Ripe k b then b.kept k else b

/-- The largest core scale `q̃` among the parts of a merge. -/
def t4Q {ι : Type*} (parts : Finset ι) (f : ι → Book) : ℕ := parts.sup (fun i => (f i).q)

/-- The record set `E = ⋃ 𝓜_i ∪ {μ}` of a merge at scale `μ`. -/
def t4E {ι : Type*} (μ : ℕ) (parts : Finset ι) (f : ι → Book) : Finset ℕ :=
  parts.biUnion (fun i => (f i).M) ∪ {μ}

/-- The first candidate ripeness time `t₀ = max {q̃ + n_q(q̃), s' + n_2(s')}`. -/
noncomputable def t4t0 {ι : Type*} (parts : Finset ι) (f : ι → Book) (s' : ℕ) : ℕ :=
  max (t4Q parts f + S.nq (t4Q parts f)) (s' + S.n2 s')

/-- The ripeness time `T = min {t ≥ t₀ : k₁(t) ∉ B(E)}` of (B.3). -/
noncomputable def t4T {ι : Type*} (μ : ℕ) (parts : Finset ι) (f : ι → Book) (s' : ℕ) : ℕ :=
  sInf {t : ℕ | S.t4t0 parts f s' ≤ t ∧ S.k1 t ∉ S.blocked (t4E μ parts f)}

/-- The new core `q' = k₁(T)`. -/
noncomputable def t4q {ι : Type*} (μ : ℕ) (parts : Finset ι) (f : ι → Book) (s' : ℕ) : ℕ :=
  S.k1 (S.t4T μ parts f s')

/-- The state after a merge within the cap (T4), formula (B.3). -/
noncomputable def t4State {ι : Type*} (μ : ℕ) (parts : Finset ι) (f : ι → Book) (s' : ℕ) :
    WState :=
  if S.t4q μ parts f s' ≤ μ then
    .active (S.t4q μ parts f s') (∑ i ∈ parts, (f i).nu)
      ((t4E μ parts f).filter (fun ξ => S.t4q μ parts f s' < ξ))
  else .pending (S.t4q μ parts f s') (∑ i ∈ parts, (f i).nu)

/-- The new window state of a component with old parts `parts` (books `f`) and `r` new cubes,
new point flag `pt'` and new clock `s'`: the rules (T1)–(T5). -/
def StateRule {ι : Type*} (μ : ℕ) (parts : Finset ι) (f : ι → Book) (r : ℕ) (pt' : Prop)
    (s' : ℕ) (st' : WState) : Prop :=
  (1 ≤ r → st' = WState.restart μ pt') ∧
  (r = 0 → ∀ i, parts = {i} → st' = WState.shadow μ pt' (f i)) ∧
  (r = 0 → 2 ≤ parts.card → (∃ i ∈ parts, (f i).st = .pre) → st' = WState.restart μ pt') ∧
  (r = 0 → 2 ≤ parts.card → (∀ i ∈ parts, (f i).st ≠ .pre) →
    ∑ i ∈ parts, (f i).nu ≤ S.numax μ → st' = S.t4State μ parts f s') ∧
  (r = 0 → 2 ≤ parts.card → (∀ i ∈ parts, (f i).st ≠ .pre) →
    S.numax μ < ∑ i ∈ parts, (f i).nu → st' = WState.restart μ pt')

/-- The bookkeeping of a component `Z'` of `Z^pre_μ` with old parts `parts` (post-`R` books `f`)
and `r` new cubes: spine length (4.1), the pure-shadow rule, the clock rule (Definition I.4.7,
item 5), and the window-state rules (T1)–(T5) when `win` (that is, `μ ≤ k₀`) holds. -/
structure BookRule {ι : Type*} (μ : ℕ) (win : Prop) (parts : Finset ι) (f : ι → Book) (r : ℕ)
    (b' : Book) : Prop where
  len_nonneg : 0 ≤ b'.len
  pt_len : b'.pt → b'.len = 0
  /-- (4.1). -/
  len_gen : b'.len ≤ ∑ i ∈ parts, (f i).len / S.L + (((parts.card + r : ℕ) : ℝ) - 1) * S.D μ
  /-- Pure shadow (Definition I.4.7, item 4): a non-point spine keeps `ℓ/L` and `ℓ > L`;
  a point spine stays a point. -/
  shadow : r = 0 → ∀ i, parts = {i} →
    (¬ b'.pt → (S.L : ℝ) < (f i).len) ∧ ((f i).pt → b'.pt)
  /-- Clock of a non-point spine: its projected epoch. -/
  clock_np : ¬ b'.pt → b'.s = μ + max 1 ⌈Real.logb S.L (max b'.len 1)⌉₊
  /-- Clock of a point spine in a pure shadow whose old spine was a point. -/
  clock_pt_shadow : b'.pt → r = 0 → ∀ i, parts = {i} → (f i).pt → b'.s = (f i).s
  /-- Clock of a point spine otherwise. -/
  clock_pt_other : b'.pt → ¬ (r = 0 ∧ ∃ i, parts = {i} ∧ (f i).pt) → b'.s = μ
  state : win → S.StateRule μ parts f r b'.pt b'.s b'.st

end Setting

end Balaban.LargeField
