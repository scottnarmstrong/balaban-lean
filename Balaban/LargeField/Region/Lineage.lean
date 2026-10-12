module

public import Balaban.LargeField.Region.Generating
public import Balaban.LargeField.Geometry.LocalGlobal
import Mathlib.Tactic.Linarith

/-!
# Neighbourhoods along lineages; box-by-box reduction (Part I, Lemmas I.3.15, I.3.16)

* `thick_nbhd_coarsen`: one step of Lemma I.3.15: if the coarsening of `Y ⊆ 𝕋_j` lies in
  `Y' ⊆ 𝕋_{j+1}` and `⌊R_{j-1}⌋ ≤ ⌊R_j⌋`, the coarsening of `(Y^≈)^{∼m}` lies in
  `(Y'^≈)^{∼⌈m/L⌉}`;
* `thick_lineage_subset`: its iteration along a chain `Y_j, Y_{j+1}, …` (the lineage), for the fine
  sites of the region sequence; `thick_lineage_le_one`: radius `1` if `m ≤ L^t`;
* `coreReduction`: Lemma I.3.16, box-by-box reduction at a core for a set function of range `ϖ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-! ### Lemma I.3.15 -/

section One

variable {d n0 n1 L : ℕ} [NeZero n0] [NeZero n1]

/-- **Lemma I.3.15** (one step): `(Y^≈)^{∼m}` coarsens into `(Y'^≈)^{∼⌈m/L⌉}`. -/
theorem thick_nbhd_coarsen (hn : n0 = L * n1) (hL : 0 < L) {ρ' ρ m : ℕ} (hρ : ρ' ≤ ρ)
    {Y : Set (Torus d n0)} {Y' : Set (Torus d n1)} (hYY : blockMap L n1 '' Y ⊆ Y')
    {y : Torus d n0} (hy : y ∈ nbhd m (thick ρ' Y)) :
    blockMap L n1 y ∈ nbhd ((m + L - 1) / L) (thick ρ Y') := by
  obtain ⟨w, hw, hyw⟩ := mem_nbhd.mp hy
  obtain ⟨y2, hy2, hwy2⟩ := mem_nbhd.mp hw
  refine mem_nbhd.mpr ⟨blockMap L n1 w, mem_nbhd.mpr ⟨blockMap L n1 y2, hYY ⟨y2, hy2, rfl⟩, ?_⟩, ?_⟩
  · refine (supDist_blockMap_le hn w y2).trans ?_
    have : (supDist w y2 + L - 1) / L ≤ ρ' + 1 := by
      apply Nat.div_le_of_le_mul
      have : ρ' ≤ L * ρ' := Nat.le_mul_of_pos_left _ hL
      rw [Nat.mul_succ]
      omega
    omega
  · exact (supDist_blockMap_le hn y w).trans (Nat.div_le_div_right (by omega))

end One

/-- The `t`-fold iterate of `m ↦ ⌈m/L⌉`. -/
def ceilDivIter (L : ℕ) : ℕ → ℕ → ℕ
  | 0, m => m
  | t + 1, m => (ceilDivIter L t m + L - 1) / L

theorem ceilDivIter_le {L : ℕ} (hL : 0 < L) (t : ℕ) :
    ∀ {c m : ℕ}, m ≤ c * L ^ t → ceilDivIter L t m ≤ c := by
  induction t with
  | zero => intro c m h; simpa [ceilDivIter] using h
  | succ t ih =>
    intro c m h
    have h1 : ceilDivIter L t m ≤ c * L := ih (by rw [pow_succ] at h; linarith)
    show (ceilDivIter L t m + L - 1) / L ≤ c
    rw [Nat.div_le_iff_le_mul_add_pred hL]
    have : L * c = c * L := mul_comm _ _
    omega

theorem ceilDivIter_le_one {L : ℕ} (hL : 0 < L) {m : ℕ} (t : ℕ) (h : m ≤ L ^ t) :
    ceilDivIter L t m ≤ 1 :=
  ceilDivIter_le hL t (by simpa using h)

section Chain

variable {d L M : ℕ} [NeZero L] [NeZero M] {nn : ℕ → ℕ} [∀ i, NeZero (nn i)] {R : ℕ → ℝ}

/-- **Lemma I.3.15**: along a chain of sets `Y_i ⊆ 𝕋_i` with `Y_i^↑ ⊆ Y_{i+1}` (`j ≤ i < j + t`) and
`⌊R_{i-1}⌋ ≤ ⌊R_i⌋`, a fine site whose `𝕋_j`-cube is in `(Y_j^≈)^{∼m}` has its `𝕋_{j+t}`-cube in
`(Y_{j+t}^≈)^{∼ ceilDivIter t m}` (`≈` at scale `i` has radius `⌊R_{i-1}⌋`). -/
theorem thick_lineage_subset (hnn : ∀ i, nn i = L * nn (i + 1)) (hL : 0 < L) (hR : ∀ i, ⌊R (i - 1)⌋₊ ≤ ⌊R i⌋₊) {K j t : ℕ}
    (hjt : j + t ≤ K) (Y : ∀ i, Set (Torus d (nn i)))
    (hY : ∀ i, j ≤ i → i < j + t → blockMap L (nn (i + 1)) '' Y i ⊆ Y (i + 1))
    {m : ℕ} {x : Torus d (M * nn K * L ^ K)}
    (hx : cubeMap nn L M K j x ∈ nbhd m (thick ⌊R (j - 1)⌋₊ (Y j))) :
    cubeMap nn L M K (j + t) x ∈
      nbhd (ceilDivIter L t m) (thick ⌊R (j + t - 1)⌋₊ (Y (j + t))) := by
  induction t with
  | zero => simpa [ceilDivIter] using hx
  | succ t ih =>
    have h1 := ih (by omega) (fun i hi hi' => hY i hi (by omega))
    have h2 := thick_nbhd_coarsen (hnn (j + t)) hL (hR (j + t)) (hY (j + t) (by omega) (by omega)) h1
    rw [cubeMap_succ hnn (by omega)] at h2
    exact h2

/-- **Lemma I.3.15**, the radius-one form: if `m ≤ L^t`, the neighbourhood of radius `m` at scale `j`
lies in the `1`-neighbourhood of the thickened ancestor at scale `j + t`. -/
theorem thick_lineage_le_one (hnn : ∀ i, nn i = L * nn (i + 1)) (hL : 0 < L) (hR : ∀ i, ⌊R (i - 1)⌋₊ ≤ ⌊R i⌋₊) {K j t : ℕ}
    (hjt : j + t ≤ K) (Y : ∀ i, Set (Torus d (nn i)))
    (hY : ∀ i, j ≤ i → i < j + t → blockMap L (nn (i + 1)) '' Y i ⊆ Y (i + 1))
    {m : ℕ} (hm : m ≤ L ^ t) {x : Torus d (M * nn K * L ^ K)}
    (hx : cubeMap nn L M K j x ∈ nbhd m (thick ⌊R (j - 1)⌋₊ (Y j))) :
    cubeMap nn L M K (j + t) x ∈ nbhd 1 (thick ⌊R (j + t - 1)⌋₊ (Y (j + t))) :=
  nbhd_mono (ceilDivIter_le_one hL t hm) subset_rfl
    (thick_lineage_subset hnn hL hR hjt Y hY hx)

end Chain

/-! ### Lemma I.3.16 -/

section Core

variable {d n : ℕ} [NeZero n]

/-- A set function of range `ϖ`: `Φ(X) ∩ E` depends only on `X ∩ E^{∼ϖ}`. -/
def HasRange (ϖ : ℕ) (Φ : Set (Torus d n) → Set (Torus d n)) : Prop :=
  ∀ (X X' E : Set (Torus d n)), X ∩ nbhd ϖ E = X' ∩ nbhd ϖ E → Φ X ∩ E = Φ X' ∩ E

/-- **Lemma I.3.16** (box-by-box reduction at the core). `C` a component of the core region `X`
(width `ω = 2 r̂ + L + 11`, `r ≤ r̂`), `U = X^≈`, `W = (Xᶜ)^{≈2}`, `U^C = C^≈`, `W^C = (Cᶜ)^{≈2}`,
`Φ` of range `ϖ`, `2 (m + ϖ) ≤ L + 8`. Then on `(U^C)^{∼m}` the sets `Φ(U^{∼n})` (`n ≤ m`) and
`Φ(W)` coincide with `Φ((U^C)^{∼n})` and `Φ(W^C)`. -/
theorem coreReduction {L r rhat ω m ϖ : ℕ} {X : Finset (Torus d n)} {C : Finset (Torus d n)}
    (hC : C ∈ comps ω X) (hr : r ≤ rhat) (hω : ω = 2 * rhat + L + 11) (hm : 2 * (m + ϖ) ≤ L + 8)
    {Φ : Set (Torus d n) → Set (Torus d n)} (hΦ : HasRange ϖ Φ) :
    (∀ k ≤ m, Φ (nbhd k (thick r (X : Set (Torus d n)))) ∩ nbhd m (thick r (C : Set (Torus d n))) =
      Φ (nbhd k (thick r (C : Set (Torus d n)))) ∩ nbhd m (thick r (C : Set (Torus d n)))) ∧
    Φ (thick2 r (X : Set (Torus d n))ᶜ) ∩ nbhd m (thick r (C : Set (Torus d n))) =
      Φ (thick2 r (C : Set (Torus d n))ᶜ) ∩ nbhd m (thick r (C : Set (Torus d n))) := by
  have h := flow_local_eq_global' hC hr hω hm
  have hE : nbhd ϖ (nbhd m (thick r (C : Set (Torus d n)))) = nbhd (m + ϖ) (thick r (C : Set (Torus d n))) :=
    nbhd_nbhd _ _ _
  refine ⟨fun k hk => hΦ _ _ _ ?_, hΦ _ _ _ ?_⟩
  · rw [hE]; exact h.1 k (by omega)
  · rw [hE]; exact h.2

/-- **Lemma I.3.16**, disjointness: the sets `(U^{C})^{∼(m+ϖ)}` of distinct components are
pairwise disjoint. -/
theorem coreReduction_disjoint {L r rhat ω m ϖ : ℕ} {X C C' : Finset (Torus d n)}
    (hC : C ∈ comps ω X) (hC' : C' ∈ comps ω X) (hne : C ≠ C') (hr : r ≤ rhat)
    (hω : ω = 2 * rhat + L + 11) (hm : 2 * (m + ϖ) ≤ L + 8) :
    Disjoint (nbhd (m + ϖ) (thick r (C : Set (Torus d n))))
      (nbhd (m + ϖ) (thick r (C' : Set (Torus d n)))) :=
  nbhd_thick_disjoint_empty hC hC' hne hr hω hm

end Core

end Balaban.LargeField
