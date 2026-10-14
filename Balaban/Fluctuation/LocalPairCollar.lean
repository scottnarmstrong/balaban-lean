/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairReplacementLocalB

/-!
# The collar of the expansion domain for the local generating set

P3 pp. 78-79 recomputes the term of an expansion domain `Y` on the local generating set
`𝔹_{k+1}(Y)`, built on `Y` itself (P3 (4.44): `Ω'_{k+1} = Y ∩ Ω_{k+1}`, `Ω'_k = Ω'^{~5L}_{k+1} ∪ …`),
and asserts that the term depends on the data only on `Y₁ = X₁ ∪ ⋃ 𝒞 ⊆ Y` (4.42).  In the Lean
construction the cut operators act on interaction cubes `□_z` and thickened cubes `□̂_z` of
half-width up to `4 M₁ L^{k+1}` and on partition functions whose bumps reach `3/2 M₁ L^n`; the
replacement identity `coef_eTermFun_replacement_localB` therefore needs the margin: every site
within sup-distance `2 M₁ L^{k+1}` of the read region `R` lies in the top layer
`Ω_{k+1}(𝔹_{k+1}(·))` of the local generating set.  This margin fails for the generating set built on
the expansion domain itself (near its boundary the local cover has cubes of lower layers), and holds
for the generating set built on the collar

  `Y⁺ = Y ∪ (the 𝒞_{k+1}-cubes within two cubes of Y)`,

written here as the set `Yp` characterized by `hYp`: a site lies in `Yp` iff its `𝒞_{k+1}`-cube
(side `M₁ L^{k+1}`, `M₁ = L^{m₁}`) meets the closed `2 M₁ L^{k+1}`-neighbourhood of `Y`.  No new
definition is introduced.

* `localB_collar_subset`: `Y ⊆ Y⁺`;
* `localB_collar_cubeUnion`, `localB_collar_top`, `localB_collar_gsSpecStrong`: `Y⁺` is a union of
  `𝒞_{k+1}`-cubes, so it is the top layer of `𝔹_{k+1}(Y⁺)` and the specification `GsSpecStrong` of
  `localB` holds for it (the separation index of `localB` is `5 L M₁`, `le_refl`, as for `Y`);
* `localB_collar_margin`: the margin of `coef_eTermFun_replacement_localB` for `𝔹_{k+1}(Y⁺)` from
  `R ⊆ Y`;
* `coef_eTermFun_replacement_localB_collar`: the replacement identity with the restricted datum
  (`coef_eTermFun_replacement_localB_restrict`) on `𝔹_{k+1}(Y⁺)`, the margin replaced by `R ⊆ Y`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.Fluctuation

section Collar

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱl : ℝ}
variable {Y Yp : Set (CTorus d L N₁ m₁ (k + 1))}

omit [NeZero N₁] [NeZero L] in
/-- **The expansion domain lies in its collar**: `Y ⊆ Y⁺`. -/
theorem localB_collar_subset
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁)) :
    Y ⊆ Yp := fun z hz =>
  (hYp z).2 ⟨z, hz, z, rfl, by rw [supDist_self]; exact Nat.zero_le _⟩

omit [NeZero N₁] [NeZero L] in
/-- **The collar is a union of `𝒞_{k+1}`-cubes**: with a site it contains its whole
`𝒞_{k+1}`-cube. -/
theorem localB_collar_cubeUnion
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁)) :
    ∀ x ∈ Yp, ∀ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) → y ∈ Yp := by
  intro x hx y hy
  obtain ⟨x', hx', y', hy', hd⟩ := (hYp x).1 hx
  exact (hYp y).2 ⟨x', hx', y', hy'.trans hy.symm, hd⟩

/-- **The top layer of `𝔹_{k+1}(Y⁺)` is `Y⁺`.** -/
theorem localB_collar_top (hk : k + 1 ≤ k + 1) (hsep : ϱl ≤ minSep L (L ^ m₁))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁)) :
    ((localB (k + 1) hk Yp hsep).Ω (k + 1) : Set (CTorus d L N₁ m₁ (k + 1))) = Yp :=
  localB_Ω_top_eq (localB_collar_cubeUnion hYp)

/-- **The specification of `localB` holds for the collar** (`gsSpecStrong_localB`): `Y⁺` is a
union of `𝒞_{k+1}`-cubes, so `𝔹_{k+1}(Y⁺)` has `Y⁺` as top layer, no layer above `k + 1`, and the
layer indices and blocks of the whole-level set on `Y⁺`. -/
theorem localB_collar_gsSpecStrong (hk : k + 1 ≤ k + 1) (hsep : ϱl ≤ minSep L (L ^ m₁))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁)) :
    GsSpecStrong (k + 1) hk Yp (localB (k + 1) hk Yp hsep) :=
  gsSpecStrong_localB (Nat.le_add_left 1 k) (localB_collar_cubeUnion hYp)

/-- **The margin from `R ⊆ Y`.**  If the read region `R` lies in the expansion domain `Y`, every
site within sup-distance `2 M₁ L^{k+1}` of `R` lies in the top layer of `𝔹_{k+1}(Y⁺)`: its
`𝒞_{k+1}`-cube meets the `2 M₁ L^{k+1}`-neighbourhood of `Y`.  This is the hypothesis `hmar` of
`coef_eTermFun_replacement_localB` for the generating set built on `Y⁺`. -/
theorem localB_collar_margin (hk : k + 1 ≤ k + 1) (hsep : ϱl ≤ minSep L (L ^ m₁))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    {R : Finset (CTorus d L N₁ m₁ (k + 1))} (hRY : ∀ x ∈ R, x ∈ Y) :
    ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ (localB (k + 1) hk Yp hsep).Ω (k + 1) := by
  intro x hx y hxy
  refine (mem_localB_Ω_top y).2 fun y' hy' => ?_
  exact (hYp y').2 ⟨x, hRY x hx, y, hy'.symm, hxy⟩

end Collar

section Assembly

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm ϱ₁ ϱ₂ : ℝ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {ν : ℝ}

/-- **The replacement identity at the local generating set of the collar** (P3 pp. 78-79).  The
case of `coef_eTermFun_replacement_localB_restrict` in which the local generating set is built on
the collar `Y⁺ = Yp` of the expansion domain `Y` (`hYp`): the margin hypothesis is replaced by
`R ⊆ Y` (the read region `R` contains the cubes of `𝒞`, the cubes meeting `X₁` and the data sites of
`𝔹_k(X)`), through `localB_collar_margin`.  The hypotheses left are the constants, the
specifications of the solution maps, the chart of `D` and the fluctuation `ψ'(w)` in the ball. -/
theorem coef_eTermFun_replacement_localB_collar (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ k + 1) (Y Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁))
      (compWeight L a₁) ν)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 ×
        Fin N → ℂ) × ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ :
        (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1
        × Fin N → ℂ)
        (α : (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ), Dec2.IsDecBg (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
          (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (C : Finset (ParIdx
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁))
      {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεb : xiC1 d * eps + (2 * bgK1 d L N + 1) * (xiC1 d * eps) ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    {D : BgData (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) N} (hD : XiCData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
      (compWeight L a₁) ν (k + 1) 1 eps D)
    (ψ' : (ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ → ℂ) → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (hψ : ∀ w ∈ supN C R', ψ' w ∈ FlBall Hm δ₁)
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk), ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (hRk : ∀ x ∈ dataSites Gk, x ∈ R)
    (hRY : ∀ x ∈ R, x ∈ Y) :
    coef (fun w => eTermFun (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) Gk Gj Hm ac Fk E (F₁ (extParams
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
      rawOf D))
        (Sol (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
          flEdat (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk) Hm (F₁ (extParams
            (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
            X₁ w, rawOf D)) D.Ψ (ψ' w))).1 (rawOf D, ψ' w)) C =
      coef (fun w => eTermFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
              (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D)))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D)))
            (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D).Ψ (ψ' w))).1 (rawOf
              (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D), ψ' w)) C :=
  coef_eTermFun_replacement_localB_restrict hG hk1 hk Yp hN hm₁ hM hag hagm hagl hS HB HB' hκ hMc
    hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac Fk E C hR' hRκ heps hsmall hc7 hphi hεb hsmall'
    hc7' hphi' hδ₀e hD ψ' hψ hRC hRX hRk
    (localB_collar_margin hk (le_refl (minSep L (L ^ m₁))) hYp hRY)

end Assembly

end Balaban.Localization
