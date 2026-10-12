module

public import Balaban.LargeField.History.RStep
import Mathlib.Tactic.Linarith

/-!
# The abstract history of the step counter (Part I, §I.5.2)

`CounterHist S k₀ K Cp` is the numerical history on which LF-2 is proved: for each scale `k` a
finite type `Cp k` of components of `Z^pre_k`, their bookkeeping `bk`, the set `rem k` of
components removed by `R^{(k)}`, the successor map and the parts of each component of
`Z^pre_{k+1}`, the number of new cubes, the volume `|Z'|_#`, and the reals `G^pre`, `G`.

The fields are exactly the hypotheses of §I.5.2 in numerical form:
* `book_rule`: the bookkeeping of Definition I.4.7 and (T1)–(T5) (`Setting.BookRule`);
* `vol_bound`: Lemma V with (3.1), i.e. `|Z'|_# ≤ C_V ρ^{d-1}(ℓ + ρ)` (supplied by
  `Counter/Volume` and the spine-consistency lemma in the geometric layer);
* `budget` is (B), `rg_*` is (Rg).
-/

@[expose] public section

namespace Balaban.LargeField

/-- The numerical abstract history of LF-2. -/
structure CounterHist (S : Setting) (k0 K : ℕ) (Cp : ℕ → Type) [∀ k, Fintype (Cp k)]
    [∀ k, DecidableEq (Cp k)] where
  /-- `Z_0 = ∅`. -/
  isEmpty0 : IsEmpty (Cp 0)
  /-- bookkeeping of the components of `Z^pre_k` -/
  bk : ∀ k, Cp k → Book
  /-- components removed by `R^{(k)}` -/
  rem : ∀ k, Finset (Cp k)
  rem_empty : ∀ k, (k = 0 ∨ k0 < k) → rem k = ∅
  rem_ripe : ∀ k, ∀ c ∈ rem k, S.Ripe k (bk k c)
  /-- the component of `Z^pre_{k+1}` containing the old component -/
  succ : ∀ k, Cp k → Cp (k + 1)
  /-- the old parts of a component of `Z^pre_{k+1}` (non-removed components with this successor) -/
  parts : ∀ k, Cp (k + 1) → Finset (Cp k)
  mem_parts : ∀ k (c : Cp k) (Z' : Cp (k + 1)), c ∈ parts k Z' ↔ c ∉ rem k ∧ succ k c = Z'
  /-- the number of new cubes `|𝒩_k ∩ Z|_#` -/
  newc : ∀ k, Cp k → ℕ
  /-- the number of cubes `|Z|_#` -/
  vol : ∀ k, Cp k → ℝ
  /-- `G^pre_k(Z)` -/
  Gp : ∀ k, Cp k → ℝ
  /-- `G_k(Z)` -/
  G : ∀ k, Cp k → ℝ
  /-- every component contains a seed -/
  seed_pos : ∀ k, k < K → ∀ Z' : Cp (k + 1), 1 ≤ (parts k Z').card + newc (k + 1) Z'
  /-- the bookkeeping rules -/
  book_rule : ∀ k, k < K → ∀ Z' : Cp (k + 1),
    S.BookRule (k + 1) (k + 1 ≤ k0) (parts k Z') (fun c => S.postBook k0 k (bk k c))
      (newc (k + 1) Z') (bk (k + 1) Z')
  /-- Lemma V and (3.1) -/
  vol_bound : ∀ k, k < K → ∀ Z' : Cp (k + 1),
    vol (k + 1) Z' ≤ S.CV * (S.rho (k + 1) : ℝ) ^ (S.d - 1) *
      ((bk (k + 1) Z').len + S.rho (k + 1))
  /-- (B) -/
  budget : ∀ k, k < K → ∀ Z' : Cp (k + 1),
    ∑ c ∈ parts k Z', G k c + S.g k * newc (k + 1) Z' - S.cv * S.lam (k + 1) * vol (k + 1) Z' ≤
      Gp (k + 1) Z'
  /-- (Rg), kept ripe components -/
  rg_ripe : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : Cp k, c ∉ rem k → S.Ripe k (bk k c) →
    Gp k c - S.CR * S.lam k ^ (2 * S.d + 1) + S.A3' * S.lam k ^ S.pR ≤ G k c
  /-- (Rg), non-ripe components -/
  rg_nonripe : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : Cp k, c ∉ rem k → ¬ S.Ripe k (bk k c) →
    G k c = Gp k c
  /-- (Rg), `k > k₀` -/
  rg_frozen : ∀ k, k0 < k → ∀ c : Cp k, G k c = Gp k c

namespace CounterHist

variable {S : Setting} {k0 K : ℕ} {Cp : ℕ → Type} [∀ k, Fintype (Cp k)] [∀ k, DecidableEq (Cp k)]
  (H : CounterHist S k0 K Cp)

/-- The post-`R` book of a non-removed component. -/
noncomputable def pbk (k : ℕ) (c : Cp k) : Book := S.postBook k0 k (H.bk k c)

end CounterHist

namespace Setting.Good

variable {S : Setting} (G : S.Good)

include G

/-- One step of the invariant: if the post-`R` books of the parts satisfy the invariant at scale
`k`, the pre-`R` book of the component at scale `k + 1 ≤ k₀` satisfies it. -/
theorem pre_inv_step {k0 K : ℕ} {Cp : ℕ → Type} [∀ k, Fintype (Cp k)] [∀ k, DecidableEq (Cp k)]
    (H : CounterHist S k0 K Cp) {k : ℕ} (hK : k < K) (hk0 : k + 1 ≤ k0) (Z' : Cp (k + 1))
    (h : ∀ i ∈ H.parts k Z', BookInv S k (H.pbk k i) ∧ k < S.tStar (H.pbk k i)) :
    BookInv S (k + 1) (H.bk (k + 1) Z') :=
  (G.step_classify (f := H.pbk k) (fun i hi => (h i hi).1) (fun i hi => (h i hi).2)
    (H.seed_pos k hK Z') (Setting.BookRule.toTrue S (H.book_rule k hK Z') hk0)).1

/-- The numerical invariant at all scales `1 ≤ k ≤ min {k₀, K}`: every component of `Z^pre_k`
satisfies `BookInv k`, every non-removed one satisfies `BookInv k` after `R^{(k)}` with
`k < t^*` (Lemma C4 (a)–(c) and Lemma C (f4), numerically). -/
theorem window_inv {k0 K : ℕ} {Cp : ℕ → Type} [∀ k, Fintype (Cp k)] [∀ k, DecidableEq (Cp k)]
    (H : CounterHist S k0 K Cp) :
    ∀ k, 1 ≤ k → k ≤ k0 → k ≤ K → ∀ c : Cp k, BookInv S k (H.bk k c) ∧
      BookInv S k (H.pbk k c) ∧ k < S.tStar (H.pbk k c) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro hk0 hkK c
    have hinv := G.pre_inv_step H (k := 0) (by omega) (by omega) c (fun i _ =>
      (H.isEmpty0.false i).elim)
    have hr := G.rstep_inv (k0 := k0) (le_refl 1) hk0 hinv
    exact ⟨hinv, hr.1, hr.2.1⟩
  | succ k hk ih =>
    intro hk0 hkK c
    have hinv := G.pre_inv_step H (k := k) (by omega) (by omega) c (fun i hi => by
      have hi' := ((H.mem_parts k i c).mp hi)
      have := ih (by omega) (by omega) i
      exact ⟨this.2.1, this.2.2⟩)
    have hr := G.rstep_inv (k0 := k0) (by omega) hk0 hinv
    exact ⟨hinv, hr.1, hr.2.1⟩

end Setting.Good

end Balaban.LargeField
