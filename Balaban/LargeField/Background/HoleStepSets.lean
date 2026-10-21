/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairOp
public import Balaban.LargeField.Region.StepMisses
public import Balaban.Fluctuation.HoleStep
import Mathlib.Tactic.Linarith

/-!
# The generating sets of the step on a region (P5 (2.17))

At the step `k → k + 1` of the region calculus (`RegionStep`, `𝕋_k = Torus d n0`,
`𝕋_{k+1} = Torus d n1`, `n0 = L n1`) the fluctuation integral of P5 (2.16) is expanded around the
composed datum (2.17) of the old operator set `𝔹_k(W_k)` (`p6Hold`, `W_k = (Z_k^c)^{≈2}`) over the
set `(𝔹_k(W_k) ∩ Ω^c_{k+1}) ∪ Λ_{k+1}`: the same layers below `k + 1` and the top layer `Ω_{k+1}`.

* `fineK1_Omega_subset_p6Halo`: the new region lies in the halo `A` of `F♯` (its cubes meet
  `Z_k^c`; P5 (2.3), `RegionStep.blockMap_notMem_Omega`), hence in `W_k` at distance
  `> 5 L M₁ L^k` from `W_k^c` (`p6_halo_subset_W`, `p6_halo_far`);
* `p6Top`: the set of P5 (2.17), `p6Hold.addTop (fine Ω_{k+1})`; `p6Top_Ω_top`, `p6Top_Ω_of_le`,
  `p6Hold_precedes_p6Top`;
* `p6TopC`: the same on the cover torus (`castN`), next to `p6OldC`;
* `p6Top_cubeAligned`, `p6Top_supSep`, `p6TopC_cubeAligned`, `p6TopC_supSep`: the set of (2.17) is
  cube aligned and sup-separated (from those of `F♯`, `p6_fsharp_cubeAligned`, `p6_fsharp_supSep`:
  the layers below the top are those of `F♯` and the top `Ω_{k+1}` lies in the top `A` of `F♯`), the
  hypotheses of the cover estimates of the pair `(coverOf G′, G′)`;
* `holeStepOf`: **the step on a region of a region step** (`Fluctuation.HoleStep`), with the old set
  `p6OldC`, the set `p6TopC`, and the mixed datum `liftMixed` of the old field `ψ_k`, the block
  variable `θ` and the field `h`;
* `cubeOfC`, `locDomC`: the cube of `𝕋_{k+1}` of a site of the cover torus, and the localization
  domain `X₁ = R_{k+1}(□')` of P5 (2.18) of a site: the sites of the cubes of `𝕋_{k+1}` within `ρ`
  cubes of its cube (`mem_locDomC`; it contains the cube, `mem_locDomC_of_cube_eq`);
* `cubeKOfC`, `activeCoreC`: the cube of `𝕋_k` of a site of the cover torus, and the sites of
  `A_X = X ∩ Ω_{k+1}` of a set `X` of cubes of `𝕋_k` (the uncut core of the re-expansion of an old
  boundary term, P6 p. 34; `mem_activeCoreC`);
* `mem_castN_Ω`, `supDist_cast`, `p6TopC_ball`: the sites within `10` top cells of a site of
  `Ω_{k+1}` lie in `Ω₁` of the set of (2.17) (the halo is far from the complement of `W_k`);
* `collarCoreC`: the sites within sup-distance `r` of `A_X` (the uncut core of the re-expansion, with
  the collar of the pair condition `X₀^{∼r₀} ⊂ X₁` of P3 (2.14); `mem_collarCoreC`,
  `activeCoreC_subset_collarCoreC`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Multiscale.GeneratingSet

set_option linter.unusedSectionVars false

variable {d M1 c n1 L k n0 m₁ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} (st : RegionStep d L n0 n1 Rprev Rk)

/-- **The new region lies in the halo of `F♯`**: a fine site of `Ω_{k+1}` has its cube of `𝕋_k`
outside `Z_k` (P5 (2.3), `RegionStep.blockMap_notMem_Omega`), so its cube of `𝕋_{k+1}` meets
`(Z_k^c)^≈`. -/
theorem fineK1_Omega_subset_p6Halo (hn : n0 = L * n1) (ρ' : ℕ) :
    fineK1 M1 c n1 L k st.Omega ⊆ p6Halo M1 c n1 L k ρ' st.Z := by
  intro x hx
  rw [mem_fineK1] at hx
  rw [mem_p6Halo]
  have hu : blockMap (L ^ k * (c * M1)) n0 x ∉ st.Z := fun hZ =>
    st.blockMap_notMem_Omega hZ (by rw [blockMap_k_succ hn x]; exact hx)
  refine subset_nbhd 1 _ ⟨blockMap (L ^ k * (c * M1)) n0 x, subset_nbhd _ _ hu, ?_⟩
  exact blockMap_k_succ hn x

/-- The new region lies in `W_k`. -/
theorem fineK1_Omega_subset_stepW (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 2 * L ≤ ρ' + 2) :
    fineK1 M1 c n1 L k st.Omega ⊆ stepW M1 c n1 L k ρ' st.Z :=
  (fineK1_Omega_subset_p6Halo st hn ρ').trans (p6_halo_subset_W hn hρ st.Z)

/-- **The set of P5 (2.17)**: `(𝔹_k(W_k) ∩ Ω^c_{k+1}) ∪ Λ_{k+1}`, the old operator set `𝔹_k(W_k)`
with the top layer `Ω_{k+1}` (`ρ' = ⌊R_{k-1}⌋ ≥ 3 L`, `c ≥ 5`). -/
noncomputable def p6Top (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c) :
    GeneratingSet d L (M1 * (c * n1)) (k + 1) (minSep L M1) :=
  (p6Hold M1 c n1 L k ρ' st.Z).addTop (fineK1 M1 c n1 L k st.Omega)
    ((isCubeUnion_fineK1 _).isBlockUnion le_rfl)
    (fun _ => by
      rw [p6Hold_Ω_k hn]
      exact fineK1_Omega_subset_stepW st hn (by omega))
    (fun _ x hx y hy => by
      rw [p6Hold_Ω_k hn] at hx
      exact p6_halo_far hn hρ hc st.Z hx (fineK1_Omega_subset_p6Halo st hn ρ' hy))

variable {st}

theorem p6Top_Ω_top (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c) :
    (p6Top st hn hρ hc).Ω (k + 1) = fineK1 M1 c n1 L k st.Omega := by
  unfold p6Top
  rw [GeneratingSet.addTop_Ω]; simp

theorem p6Top_Ω_of_le (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c) {j : ℕ}
    (hj : j ≤ k) : (p6Top st hn hρ hc).Ω j = (p6Hold M1 c n1 L k ρ' st.Z).Ω j := by
  have h : j ≠ k + 1 := by omega
  unfold p6Top
  rw [GeneratingSet.addTop_Ω]; simp [h]

/-- `𝔹_k(W_k) ≺ (𝔹_k(W_k) ∩ Ω^c_{k+1}) ∪ Λ_{k+1}`. -/
theorem p6Hold_precedes_p6Top (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c) :
    Background.Precedes (p6Hold M1 c n1 L k ρ' st.Z) (p6Top st hn hρ hc) := by
  intro i _ hi
  by_cases h : i = k + 1
  · subst h
    rw [p6Hold_Ω_top]
    exact Finset.empty_subset _
  · rw [p6Top_Ω_of_le hn hρ hc (by omega)]

/-- **The set of P5 (2.17) is sup-separated** (`M₁ = L^{m₁}`): its layers below the top are those of
`F♯`, and its top `Ω_{k+1}` lies in the top of `F♯`. -/
theorem p6Top_supSep (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (hM1 : M1 = L ^ m₁) : SupSep (p6Top (M1 := M1) (k := k) st hn hρ hc) m₁ := by
  intro j hj1 hjK x hx y hy
  refine p6_fsharp_supSep (k := k) hn hρ hc st.Z hM1 j hj1 hjK x ?_ y ?_
  · rw [p6Fsharp_Ω_of_le hn hρ hc st.Z (by omega)]
    rwa [p6Top_Ω_of_le hn hρ hc (by omega)] at hx
  · by_cases hj : j + 1 ≤ k
    · rw [p6Fsharp_Ω_of_le hn hρ hc st.Z hj]
      rwa [p6Top_Ω_of_le hn hρ hc hj] at hy
    · have hjk : j + 1 = k + 1 := by omega
      rw [hjk, p6Fsharp_Ω_top]
      rw [hjk, p6Top_Ω_top] at hy
      exact fineK1_Omega_subset_p6Halo st hn ρ' hy

/-- **The set of P5 (2.17) is cube aligned** (`M₁ = L^{m₁}`, `m₁ ≥ 2`): its layers below the top are
those of `F♯`, and its top `Ω_{k+1}` is a union of cubes of `𝕋_{k+1}`. -/
theorem p6Top_cubeAligned (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) : CubeAligned (p6Top (M1 := M1) (k := k) st hn hρ hc) m₁ := by
  have hF := p6_fsharp_cubeAligned (k := k) hn hρ hc st.Z hM1 hm₁
  refine ⟨hm₁, hF.dvd, ?_⟩
  intro j hj1 hjK x x' hcell
  by_cases hj : j = k + 1
  · subst hj
    rw [p6Top_Ω_top, mem_fineK1, mem_fineK1]
    have hdvd : L ^ (k + 1 + m₁) ∣ L ^ (k + 1) * (c * M1) := by
      rw [hM1, show L ^ (k + 1) * (c * L ^ m₁) = L ^ (k + 1 + m₁) * c by rw [pow_add]; ring]
      exact Dvd.intro _ rfl
    rw [blockMap_eq_of_sameCell (m := n1) hcell hdvd]
  · have hjk : j ≤ k := by omega
    rw [p6Top_Ω_of_le hn hρ hc hjk]
    have := hF.union j hj1 hjK x x' hcell
    rwa [p6Fsharp_Ω_of_le hn hρ hc st.Z hjk] at this

variable (st)

/-- The set of P5 (2.17) on the cover torus. -/
noncomputable def p6TopC (hM1 : M1 = L ^ m₁) (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ')
    (hc : 5 ≤ c) : GeneratingSet d L ((c * n1) * L ^ m₁) (k + 1) (minSep L M1) :=
  castN (p6_side hM1) (p6Top st hn hρ hc)

variable {st} in
/-- The set of P5 (2.17) on the cover torus is sup-separated. -/
theorem p6TopC_supSep (hM1 : M1 = L ^ m₁) (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ')
    (hc : 5 ≤ c) : SupSep (p6TopC (k := k) st hM1 hn hρ hc) m₁ :=
  castN_supSep (p6_side hM1) (p6Top_supSep hn hρ hc hM1)

variable {st} in
/-- The set of P5 (2.17) on the cover torus is cube aligned. -/
theorem p6TopC_cubeAligned (hM1 : M1 = L ^ m₁) (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ')
    (hc : 5 ≤ c) (hm₁ : 2 ≤ m₁) : CubeAligned (p6TopC (k := k) st hM1 hn hρ hc) m₁ :=
  castN_cubeAligned (p6_side hM1) (p6Top_cubeAligned hn hρ hc hM1 hm₁)

theorem castN_Ω_subset {N₀ N₀' K' : ℕ} [NeZero N₀] [NeZero N₀'] {ϱ ϱ' : ℝ} (h : N₀ = N₀')
    {G : GeneratingSet d L N₀ K' ϱ} {G' : GeneratingSet d L N₀ K' ϱ'} {i j : ℕ}
    (hs : G.Ω i ⊆ G'.Ω j) : (castN h G).Ω i ⊆ (castN h G').Ω j := by
  subst h; exact hs

theorem castN_Ω_eq_empty {N₀ N₀' K' : ℕ} [NeZero N₀] [NeZero N₀'] {ϱ : ℝ} (h : N₀ = N₀')
    {G : GeneratingSet d L N₀ K' ϱ} {i : ℕ} (he : G.Ω i = ∅) : (castN h G).Ω i = ∅ := by
  subst h; exact he

/-- **The step on a region of a region step** (P5 (2.16)–(2.20)): the old operator set
`𝔹_k(W_k)` (`p6OldC`), the set of (2.17) (`p6TopC`), and the mixed datum `θ̃ = lift_{k,k+1}(ψ_k, θ)`
of the old field `ψ_k` (on the blocks of side `L^k`), the block variable `θ` (on the blocks of side
`L^{k+1}`) and the field `h₀`, on the cover torus; weights `compWeight L a₁`, mass `ν`, coupling
`β`, radius `p₁`, threshold `δ`. -/
noncomputable def holeStepOf (hM1 : M1 = L ^ m₁) (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ')
    (hc : 5 ≤ c) (hk1 : 1 ≤ k) {N : ℕ}
    (ψ : Torus d (((c * n1) * L ^ m₁) * L ^ (k + 1 - k)) → Fin N → ℂ)
    (θ : Torus d (((c * n1) * L ^ m₁) * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) :
    Fluctuation.HoleStep d L (c * n1) m₁ k N (minSep L M1) (minSep L M1) where
  G := p6OldC hM1 ρ' st.Z
  G' := p6TopC st hM1 hn hρ hc
  hpre := castN_precedes (p6_side hM1) (p6Hold_precedes_p6Top hn hρ hc)
  topG := castN_Ω_eq_empty (p6_side hM1) (p6Hold_Ω_top st.Z)
  topIn := castN_Ω_subset (p6_side hM1) (by
    rw [p6Top_Ω_top hn hρ hc, p6Hold_Ω_k hn]
    exact fineK1_Omega_subset_stepW st hn (by omega))
  hk1 := hk1
  D' := liftMixed (p6TopC st hM1 hn hρ hc)
    ((p6TopC st hM1 hn hρ hc).blockUnion (k + 1) (by omega) le_rfl) subset_rfl ψ θ
    (fun i => (h₀ i : ℂ))
  h₀ := h₀
  hh₀ := fun _ hx _ => by rw [liftMixed_h _ _ _ _ _ _ hx]
  a₁ := a₁
  ν := ν
  β := β
  p₁ := p₁
  δ := δ

/-- **The cube of `𝕋_{k+1}` of a site of the cover torus** (`𝕋_{k+1} = Torus d n1`, cubes of side
`c M₁ L^{k+1}`). -/
def cubeOfC (hM1 : M1 = L ^ m₁) (x : Localization.CTorus d L (c * n1) m₁ (k + 1)) : Torus d n1 :=
  blockMap (L ^ (k + 1) * (c * M1)) n1
    ((congrArg (· * L ^ (k + 1)) (p6_side (c := c) (n1 := n1) hM1)).symm ▸ x :
      Torus d (M1 * (c * n1) * L ^ (k + 1)))

open Classical in
/-- **The localization domain `X₁ = R_{k+1}(□')` of P5 (2.18)** of a site of the cover torus: the
sites of the cubes of `𝕋_{k+1}` within `ρ` cubes (`thick ρ`) of the cube `□'` of the site (the pair
`X₀ = □' ⊂ X₁` of the localization extension, P3 (2.14); `ρ = ⌊R_k⌋`). -/
noncomputable def locDomC (hM1 : M1 = L ^ m₁) (ρ : ℕ) (b : Localization.CTorus d L (c * n1) m₁ (k + 1)) :
    Finset (Localization.CTorus d L (c * n1) m₁ (k + 1)) :=
  Finset.univ.filter fun x => cubeOfC hM1 x ∈ thick ρ ({cubeOfC hM1 b} : Set (Torus d n1))

theorem mem_locDomC {hM1 : M1 = L ^ m₁} {ρ : ℕ} {b x : Localization.CTorus d L (c * n1) m₁ (k + 1)} :
    x ∈ locDomC hM1 ρ b ↔ cubeOfC hM1 x ∈ thick ρ ({cubeOfC hM1 b} : Set (Torus d n1)) := by
  classical
  simp [locDomC]

/-- The localization domain of a site contains the sites of its cube. -/
theorem mem_locDomC_of_cube_eq {hM1 : M1 = L ^ m₁} (ρ : ℕ) {b x : Localization.CTorus d L (c * n1) m₁ (k + 1)}
    (h : cubeOfC hM1 x = cubeOfC hM1 b) : x ∈ locDomC hM1 ρ b :=
  mem_locDomC.2 (subset_nbhd _ _ (by rw [h]; rfl))

/-- **The cube of `𝕋_k` of a site of the cover torus** (`𝕋_k = Torus d n0`, cubes of side
`c M₁ L^k`). -/
def cubeKOfC (hM1 : M1 = L ^ m₁) (x : Localization.CTorus d L (c * n1) m₁ (k + 1)) : Torus d n0 :=
  blockMap (L ^ k * (c * M1)) n0
    ((congrArg (· * L ^ (k + 1)) (p6_side (c := c) (n1 := n1) hM1)).symm ▸ x :
      Torus d (M1 * (c * n1) * L ^ (k + 1)))

open Classical in
/-- **The sites of `A_X = X ∩ Ω_{k+1}`** on the cover torus, for a set `X` of cubes of `𝕋_k`: the
sites whose cube of `𝕋_k` lies in `X` and whose cube of `𝕋_{k+1}` lies in `Ω_{k+1}` (the uncut core
of the re-expansion of an old boundary term, P6 p. 34). -/
noncomputable def activeCoreC (hM1 : M1 = L ^ m₁) (X : Finset (Torus d n0)) :
    Finset (Localization.CTorus d L (c * n1) m₁ (k + 1)) :=
  Finset.univ.filter fun x => cubeKOfC (n0 := n0) hM1 x ∈ X ∧ cubeOfC hM1 x ∈ st.Omega

theorem mem_activeCoreC {hM1 : M1 = L ^ m₁} {X : Finset (Torus d n0)}
    {x : Localization.CTorus d L (c * n1) m₁ (k + 1)} :
    x ∈ activeCoreC st hM1 X ↔ cubeKOfC (n0 := n0) hM1 x ∈ X ∧ cubeOfC hM1 x ∈ st.Omega := by
  classical
  simp [activeCoreC]

open Classical in
/-- **The uncut core of the re-expansion of an old boundary term** (P6 p. 34 with the pair
condition `X₀^{∼r₀} ⊂ X₁` of P3 (2.14), the condition that P5 (2.18) uses for `(□′, R_{k+1}(□′))`):
the sites within sup-distance `r` of `A_X = X ∩ Ω_{k+1}` (`activeCoreC`). -/
noncomputable def collarCoreC (hM1 : M1 = L ^ m₁) (r : ℕ) (X : Finset (Torus d n0)) :
    Finset (Localization.CTorus d L (c * n1) m₁ (k + 1)) :=
  Finset.univ.filter fun x => ∃ y ∈ activeCoreC st hM1 X, supDist x y ≤ r

theorem mem_collarCoreC {hM1 : M1 = L ^ m₁} {r : ℕ} {X : Finset (Torus d n0)}
    {x : Localization.CTorus d L (c * n1) m₁ (k + 1)} :
    x ∈ collarCoreC st hM1 r X ↔ ∃ y ∈ activeCoreC st hM1 X, supDist x y ≤ r := by
  classical
  simp [collarCoreC]

/-- `A_X` lies in its collar. -/
theorem activeCoreC_subset_collarCoreC (hM1 : M1 = L ^ m₁) (r : ℕ) (X : Finset (Torus d n0)) :
    activeCoreC (c := c) (k := k) st hM1 X ⊆ collarCoreC (c := c) (k := k) st hM1 r X := by
  intro x hx
  rw [mem_collarCoreC]
  exact ⟨x, hx, by rw [supDist_self]; exact Nat.zero_le _⟩

/-- Membership in a domain of a generating set transported along an equality of the base sides. -/
theorem mem_castN_Ω {N₀ N₀' K' : ℕ} [NeZero N₀] [NeZero N₀'] {ϱ : ℝ} (h : N₀ = N₀')
    (G : GeneratingSet d L N₀ K' ϱ) (j : ℕ) (x : Torus d (N₀' * L ^ K')) :
    x ∈ (castN h G).Ω j ↔ ((congrArg (· * L ^ K') h).symm ▸ x : Torus d (N₀ * L ^ K')) ∈ G.Ω j := by
  subst h; rfl

/-- The sup-distance is preserved by the transport along an equality of sides. -/
theorem supDist_cast {a b : ℕ} (h : a = b) (x y : Torus d a) :
    supDist (h ▸ x : Torus d b) (h ▸ y) = supDist x y := by
  subst h; rfl

/-- **The sites near `Ω_{k+1}` lie in `Ω₁` of the set of (2.17)**: a site within `10` top cells
(`10 M₁ L^{k+1}`) of a site of `Ω_{k+1}` (on the cover torus) lies in `Ω₁(G′)` (`c ≥ 14`,
`⌊R_{k-1}⌋ ≥ 3 L`): `Ω_{k+1}` lies in the halo, which is far from the complement of `W_k = Ω_k`. -/
theorem p6TopC_ball (hM1 : M1 = L ^ m₁) (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ')
    (hc5 : 5 ≤ c) (hc : 14 ≤ c) (hk1 : 1 ≤ k) {x z : Localization.CTorus d L (c * n1) m₁ (k + 1)}
    (hx : cubeOfC hM1 x ∈ st.Omega) (hxz : supDist x z ≤ 10 * L ^ (k + 1 + m₁)) :
    z ∈ (p6TopC (k := k) st hM1 hn hρ hc5).Ω 1 := by
  set e := (congrArg (· * L ^ (k + 1)) (p6_side (c := c) (n1 := n1) hM1)).symm with he
  have hx' : (e ▸ x : Torus d (M1 * (c * n1) * L ^ (k + 1))) ∈ fineK1 M1 c n1 L k st.Omega := by
    rw [mem_fineK1]; exact hx
  have hxh := fineK1_Omega_subset_p6Halo st hn ρ' hx'
  have hz : (e ▸ z : Torus d (M1 * (c * n1) * L ^ (k + 1))) ∈ stepW M1 c n1 L k ρ' st.Z := by
    by_contra hz
    have h := p6_halo_far_sup (M1 := M1) (c := c) hn (by omega) st.Z hz hxh
    have hd : supDist (e ▸ z : Torus d (M1 * (c * n1) * L ^ (k + 1))) (e ▸ x) ≤
        10 * (M1 * L ^ (k + 1)) := by
      rw [supDist_cast, supDist_comm, hM1, ← pow_add, show m₁ + (k + 1) = k + 1 + m₁ by ring]
      exact hxz
    have hP : L ^ k * (c * M1) * (ρ' + 3 - 2 * L) ≥ L ^ k * (c * M1) * (L + 3) :=
      Nat.mul_le_mul_left _ (by omega)
    have hLk : L ^ (k + 1) = L ^ k * L := pow_succ L k
    have hpos : 0 < L ^ k * M1 := Nat.pos_of_ne_zero (by
      have := NeZero.ne L; have := NeZero.ne M1; positivity)
    have h10 : 10 * (M1 * L ^ (k + 1)) < L ^ k * (c * M1) * (L + 2) + 1 := by
      rw [hLk]
      have : 10 * (M1 * (L ^ k * L)) = (L ^ k * M1) * (10 * L) := by ring
      have h2 : L ^ k * (c * M1) * (L + 2) = (L ^ k * M1) * (c * (L + 2)) := by ring
      rw [this, h2]
      have : 10 * L < c * (L + 2) := by nlinarith
      have := Nat.mul_lt_mul_of_pos_left this hpos
      omega
    have h3 : L ^ k * (c * M1) * (L + 3) = L ^ k * (c * M1) * (L + 2) + L ^ k * (c * M1) := by ring
    omega
  rw [p6TopC, mem_castN_Ω, p6Top_Ω_of_le hn hρ hc5 (by omega)]
  have hk : (p6Hold M1 c n1 L k ρ' st.Z).Ω k ⊆ (p6Hold M1 c n1 L k ρ' st.Z).Ω 1 :=
    (p6Hold M1 c n1 L k ρ' st.Z).Ω_antitone le_rfl hk1 (by omega)
  rw [p6Hold_Ω_k hn] at hk
  exact hk hz

end Balaban.LargeField
