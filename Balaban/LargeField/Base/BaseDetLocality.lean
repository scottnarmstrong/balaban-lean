/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseXLogShiftRows
public import Balaban.Localization.YregBlocks
public import Balaban.Localization.DecCovCutSupport
public import Balaban.Fluctuation.DetCauchyGraph
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Locality of the shifted logarithm for the components of the active region (first step)

For the cover of a level-one generating set and parameters `s`, `s'`, let `Y'` be a union of
nearest-neighbour components of `Yreg s` and of `Yreg s'` on which the cut factors of the cubes
inside `Y'` agree.  Then the rows of `baseCovXLogShift` at the sites of `Y'` agree for `s` and
`s'` (`baseLogShift_rows_of_comp`): the hypotheses of `baseCovXLogShift_rows_exact` hold with
`Sr = Y'` and `Y` the closure `nbrClosure` of `Y'` under lattice neighbours and layer blocks
(`disjI_nbrClosure`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix Balaban Balaban.Multiscale Balaban.Localization

section Closure

variable {d L N₁ m₁ : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {ν : ℝ}

open Classical in
/-- The closure of a set of sites under lattice neighbours and layer blocks (taken from the sites
of `Ω₁` in the set). -/
noncomputable def nbrClosure (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (Sr : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)) :
    Finset (Balaban.Localization.CTorus d L N₁ m₁ 1) :=
  Finset.univ.filter fun x => ∃ p : G.Ω 1, (p : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Sr ∧
    (x = p ∨ (∃ μ : Fin d, x = (p : Balaban.Localization.CTorus d L N₁ m₁ 1) + Pi.single μ 1 ∨
      x = (p : Balaban.Localization.CTorus d L N₁ m₁ 1) - Pi.single μ 1) ∨
      x ∈ G.blk (G.layerIndex (p : Balaban.Localization.CTorus d L N₁ m₁ 1)) p)

theorem mem_nbrClosure_of_nbr {Sr : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)}
    {p q : G.Ω 1} (hp : (p : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Sr)
    (h : (q : Balaban.Localization.CTorus d L N₁ m₁ 1) = p ∨
      (∃ μ : Fin d, (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
          (p : Balaban.Localization.CTorus d L N₁ m₁ 1) + Pi.single μ 1 ∨
        (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
          (p : Balaban.Localization.CTorus d L N₁ m₁ 1) - Pi.single μ 1) ∨
      (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈
        G.blk (G.layerIndex (p : Balaban.Localization.CTorus d L N₁ m₁ 1)) p) :
    (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ nbrClosure G Sr := by
  classical
  unfold nbrClosure
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, p, hp, h⟩

/-- **A thickened cube missing the component misses its closure.**  Let `Y'` be a union of
nearest-neighbour components of `Yreg s`, and `q` an active cube whose thickened cube misses `Y'`.
Then the interaction cube of `q` misses the closure of `Y'` under lattice neighbours and layer
blocks. -/
theorem disjI_nbrClosure (S : DGSetting G a ν) (hconn : HatConn G)
    {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    {Y' : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)}
    (hY : IsNnComp (Yreg G s) Y') {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1}
    (hq : q ∈ cubeIdx G) (hs : sProd G s q ≠ 0) (hD : Disjoint (hatI G q) Y') :
    DisjI G (intBox q) (nbrClosure G Y') := by
  classical
  intro x hxb hxN
  have hxI : (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ hatI G q :=
    Finset.mem_filter.2 ⟨box_subset_hatBox q hxb, x.2⟩
  have hxY : (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Yreg G s :=
    hatI_subset_Yreg_of_active hq hs hxI
  have hnot : (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∉ Y' :=
    fun h => Finset.disjoint_left.1 hD hxI h
  unfold nbrClosure at hxN
  obtain ⟨-, p, hp, hcase⟩ := Finset.mem_filter.1 hxN
  rcases hcase with h | ⟨μ, h | h⟩ | h
  · exact hnot (h ▸ hp)
  · exact hnot (hY.2 p hp x hxY ⟨μ, Or.inl h⟩)
  · refine hnot (hY.2 p hp x hxY ⟨μ, Or.inr ?_⟩)
    rw [h]; abel
  · obtain ⟨h1, h2, hl⟩ := G.layerIndex_spec p.2
    have hn : G.layerIndex (p : Balaban.Localization.CTorus d L N₁ m₁ 1) = 1 := by omega
    rw [hn] at h
    exact hnot (unionOfTopBlocks_of_isNnComp S hconn hY p x (by rw [hn] at hl; exact hl)
      (GeneratingSet.mem_blk.1 h).symm hp)

end Closure

section Rows

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx : ℝ}

/-- **Rows of the shifted logarithm on a component of the active region** (first step).  Let `Y'`
be a union of nearest-neighbour components of `Yreg s` and of `Yreg s'` on which the cut factors
of the cubes inside `Y'` agree.  Then, for every `x ≥ 0`, the rows of the integrand
`(1+x)⁻¹ c(s) - C_x(s)` at the sites of `Y'` agree for `s` and `s'`, and so do those of
`baseCovXLogShift`. -/
theorem baseLogShift_rows_of_comp {κ δ : ℝ} {α : G.Ω 1 → ℂ} (hdg : DGSetting G a ν)
    (hconn : HatConn G) (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hα : AdmPot G α)
    {s s' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {Y' : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)}
    (hY : IsNnComp (Yreg G s) Y') (hY' : IsNnComp (Yreg G s') Y')
    (hagr : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' → sProd G s q = sProd G s' q)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (hφ : IsConstraintField G δ φ)
    (x : G.Ω 1) (hx : (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y') (i : Fin N)
    (z : G.Ω 1 × Fin N) :
    (∀ t : ℝ, 0 ≤ t → baseCovXShiftIntegrand G a aT ν α s φ t (x, i) z =
      baseCovXShiftIntegrand G a aT ν α s' φ t (x, i) z) ∧
    baseCovXLogShift G a aT ν α s φ (x, i) z = baseCovXLogShift G a aT ν α s' φ (x, i) z := by
  classical
  have hsub : ∀ t, t ∈ Y' → ∃ p : G.Ω 1, (p : Balaban.Localization.CTorus d L N₁ m₁ 1) = t :=
    fun t ht => ⟨⟨t, (Finset.mem_filter.1 (hY.1 ht)).2⟩, rfl⟩
  have hSY : Y' ⊆ nbrClosure G Y' := by
    intro t ht
    obtain ⟨p, rfl⟩ := hsub t ht
    exact mem_nbrClosure_of_nbr ht (Or.inl rfl)
  have hmk : ∀ {s₀ : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
      (hY₀ : IsNnComp (Yreg G s₀) Y') (q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1),
      q ∈ cubeIdx G → sProd G s₀ q ≠ 0 →
      SubI G (intBox q) Y' ∨ DisjI G (intBox q) (nbrClosure G Y') := by
    intro s₀ hY₀ q hq h0
    rcases hatDich_of_hatConn hconn hY₀ q hq h0 with h | h
    · refine Or.inl fun t ht => h (Finset.mem_filter.2 ⟨box_subset_hatBox q ht, t.2⟩)
    · exact Or.inr (disjI_nbrClosure hdg hconn hY₀ hq h0 h)
  have hdich : ∀ q ∈ (coverOf G).cubeIdx,
      ((coverOf G).sProd s q ≠ 0 ∨ (coverOf G).sProd s' q ≠ 0) →
      SubI G (intBox q) Y' ∨ DisjI G (intBox q) (nbrClosure G Y') := by
    intro q hq h
    rcases h with h | h
    · exact hmk hY q hq h
    · exact hmk hY' q hq h
  exact baseCovXLogShift_rows_exact S hCx hκ hM hδ hsm hα hs hs' hSY hdich hagr
    (fun p q hp h => mem_nbrClosure_of_nbr hp h) hφ (x, i) z (mem_nbrClosure_of_nbr hx (Or.inl rfl))

/-- **Rows of the shifted logarithm at a site not covered by any active thickened cube.**  If no
active centre of `s` or `s'` has the site `x` in its thickened cube, the rows of `baseCovXLogShift`
at `x` agree for `s` and `s'`. -/
theorem baseLogShift_rows_of_unattached {κ δ : ℝ} {α : G.Ω 1 → ℂ} (hdg : DGSetting G a ν)
    (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hα : AdmPot G α)
    {s s' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (hφ : IsConstraintField G δ φ)
    (x : G.Ω 1)
    (hxs : ∀ q ∈ Zs G s, (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∉ hatBox q)
    (hxs' : ∀ q ∈ Zs G s', (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∉ hatBox q)
    (i : Fin N) (z : G.Ω 1 × Fin N) :
    (∀ t : ℝ, 0 ≤ t → baseCovXShiftIntegrand G a aT ν α s φ t (x, i) z =
      baseCovXShiftIntegrand G a aT ν α s' φ t (x, i) z) ∧
    baseCovXLogShift G a aT ν α s φ (x, i) z = baseCovXLogShift G a aT ν α s' φ (x, i) z := by
  classical
  have hmk : ∀ {s₀ : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
      (hx₀ : ∀ q ∈ Zs G s₀, (x : Balaban.Localization.CTorus d L N₁ m₁ 1) ∉ hatBox q)
      (q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1), q ∈ cubeIdx G → sProd G s₀ q ≠ 0 →
      DisjI G (intBox q) ({(x : Balaban.Localization.CTorus d L N₁ m₁ 1)} :
        Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)) := by
    intro s₀ hx₀ q hq h0 t htb htx
    have : (t : Balaban.Localization.CTorus d L N₁ m₁ 1) = x := Finset.mem_singleton.1 htx
    exact hx₀ q (Finset.mem_filter.2 ⟨hq, h0⟩) (this ▸ box_subset_hatBox q htb)
  have hdich : ∀ q ∈ (coverOf G).cubeIdx,
      ((coverOf G).sProd s q ≠ 0 ∨ (coverOf G).sProd s' q ≠ 0) →
      SubI G (intBox q) (∅ : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)) ∨
        DisjI G (intBox q) ({(x : Balaban.Localization.CTorus d L N₁ m₁ 1)} :
          Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)) := by
    intro q hq h
    rcases h with h | h
    · exact Or.inr (hmk hxs q hq h)
    · exact Or.inr (hmk hxs' q hq h)
  have hagr : ∀ q ∈ (coverOf G).cubeIdx,
      SubI G (intBox q) (∅ : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)) →
      (coverOf G).sProd s q = (coverOf G).sProd s' q := by
    intro q hq hsub
    obtain ⟨t, htb, htΩ⟩ := Balaban.Fluctuation.exists_site_intBox hdg hq
    exact absurd (hsub ⟨t, htΩ⟩ htb) (Finset.notMem_empty _)
  exact baseCovXLogShift_rows_exact S hCx hκ hM hδ hsm hα hs hs' (Finset.empty_subset _) hdich hagr
    (fun p q hp _ => absurd hp (Finset.notMem_empty _)) hφ (x, i) z
    (Finset.mem_singleton_self _)

end Rows

end Balaban.LargeField.Base
