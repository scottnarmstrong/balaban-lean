/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldDatumGeo

/-!
# The datum of the local pair from the cube tests of the target H7 domain (target (3) of W1154d)

`inDomainC_holeStepLoc2_of_h7Near`: **the case analysis and proof of `H7MixedDatumLoc2`** for local
sets whose data sites lie over cubes of `Ω^{∼3}_{k+1}`, at a target history `a` whose holes at scale
`k + 1` contain every cube off `Ω_{k+1}` (ruling R17: the pre-`R` records `globalLHPre`; or `globalLH`
without a removal at scale `k + 1`).  Each data site is read by the cube test at its cube of `𝕋_{k+1}`
(`Δ'^c_{k+1}` near a hole, `Δ^c_{k+1}` otherwise); the splits patch by `inDomainC_of_patch_scaled`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background

namespace Balaban.RootFSpine

set_option linter.unusedSectionVars false

section Datum

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **The datum of the local pair of reading HS-2 from the cube tests of the target H7 domain** (the
case analysis of `H7MixedDatumLoc2`, for local sets whose data sites lie over cubes of `Ω^{∼3}_{k+1}`):
the target H7 domain of scale `k + 1` at a history `a` whose top region is `Ω_{k+1}` and whose holes at
scale `k + 1` contain every cube off `Ω_{k+1}` (`hholes`: the pre-`R` records of ruling R17,
`globalLHPre`, or `globalLH` without a removal at `k + 1`), at a set `Y_f` containing the cubes of the data
sites (`CubesOfIn`).  Each data site `x` of `G′_V` is read by the test at its cube `□ = □(x)` of `𝕋_{k+1}`:
`Δ'^c_{k+1}(□)` (the pair `(ψ_k, ψ_{k+1})`, `Ψ̃^c(ε_k, ε_k)`) when `□` is within `3` cubes of a hole,
`Δ^c_{k+1}(□)` (`ψ_{k+1}`, `Ψ̃^c(ε_{k+1}, ε_{k+1})`) otherwise, where `□ ⊂ Ω_{k+1}`; the test reads every
interface partner of `x` (their cubes are within one cube).  The splits patch
(`inDomainC_of_patch_scaled`, `θ = z ψ_{k+1}` on `Ω_{k+1}`, `|z - 1| ≤ η`) into
`Ψ̃^c(3δ₁ + 2ε_k, 3δ₁ + 2ε_k)`, `δ₁ = scaledTol ε_k ε_k η`, under condition (R4) for `h₀` and the mass
condition `hmass` (small mass, or `ν ≤ μ_{k+1}` with `2 ε_k² ≤ δ₁²`). -/
theorem inDomainC_holeStepLoc2_of_h7Near (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (a : LocalHistory S n M K)
    (haΩ : a.Omega k = fineSet (S := S) (n := n) M K (k + 1) (H.step k).Omega)
    (hholes : ∀ Y : Torus S.d (n (k + 1)), Y ∉ (H.step k).Omega →
      CubeSub (S := S) (n := n) M K (k + 1) Y (a.Z (k + 1) \ a.Omega k))
    {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {aw μs ε ε1 νs : ℕ → ℝ}
    {ψ' : MultiFieldC S n M K N} {gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn a (k + 1) hk Yf aw μs ε ε1 νs (fun i => (h₀ i : ℂ)) ψ ψ' gf)
    (hY : CubesOfIn (S := S) (n := n) (M := M) (K := K) (k + 1) Yf
      (fineOfC g hnn hM1 hk '' (dataSites (locG' g hnn hM1 H hk hρ V) :
        Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))))
    (hroom : ∀ x ∈ dataSites (locG' g hnn hM1 H hk hρ V),
      cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ omegaNb a (k + 1) 3 (k + 1))
    {η : ℝ} (hη : 0 ≤ η) (hz : |z - 1| ≤ η) (hε0 : 0 < ε (k + 1)) (hεk : ε (k + 1) ≤ ε k)
    (hR4 : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < scaledTol (ε k) (ε k) η ^ 2)
    (hmass : (0 ≤ ν ∧ ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * (1 + rn h₀) < scaledTol (ε k) (ε k) η ^ 2) ∨
      (0 ≤ ν ∧ ν ≤ μs (k + 1) ∧ 2 * ε k ^ 2 ≤ scaledTol (ε k) (ε k) η ^ 2)) :
    InDomainC (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' ν
      (3 * scaledTol (ε k) (ε k) η + 2 * ε k) (3 * scaledTol (ε k) (ε k) η + 2 * ε k)
      (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D' := by
  classical
  have hc := g.hc
  have hkK : k ≤ K := Nat.le_of_succ_le hk
  set G := locG' g hnn hM1 H hk hρ V with hG
  set δ₁ := scaledTol (ε k) (ε k) η with hδ₁
  have hεk0 : 0 < ε k := hε0.trans_le hεk
  -- the cubes within `3` cubes of a cube away from the holes lie in `Ω_{k+1}`
  have hfarΩ : ∀ Y : Torus S.d (n (k + 1)), Y ∉ omegaCNb a 3 (k + 1) →
      ∀ Y', LargeField.supDist Y Y' ≤ 3 → Y' ∈ (H.step k).Omega := by
    intro Y hY Y' hd
    by_contra hY'
    exact hY (mem_nbhd.2 ⟨Y', hholes Y' hY', hd⟩)
  -- the top set of the mixed tests
  have hOmem : ∀ x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1),
      toCube g hM1 x ∈ omegaLevel (S := S) (n := n) g.M1 g.c (k + 1)
          {y | CubeSub (S := S) (n := n) M K (k + 1) y (a.Omega k)} ↔
        cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ (H.step k).Omega := by
    intro x
    unfold omegaLevel
    rw [mem_cubePre]
    show CubeSub (S := S) (n := n) M K (k + 1) (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x)
      (a.Omega k) ↔ _
    rw [haΩ]
    exact cubeSub_fineSet_iff hnn hk _ _
  -- the datum of the local pair at a data site
  have hdat : ∀ x ∈ dataSites G, ∀ i,
      (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D'.Ψ x i =
        if cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ (H.step k).Omega then
          (z : ℂ) * ψ (k + 1) (coverBlk g hnn hM1 hk (k + 1) le_rfl x) i
        else ψ k (coverBlk g hnn hM1 hk k (Nat.le_succ k) x) i := by
    intro x hx i
    rw [holeStepLoc2_D'_Ψ g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hx]
    unfold mixedLift blockLift
    by_cases hΩ : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ (H.step k).Omega
    · have h1 : x ∈ (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.Ω (k + 1) :=
        (mem_stepG'_top_iff g hnn hM1 H hk hρ x).2 hΩ
      simp only [h1, ↓reduceIte, hΩ]
      rfl
    · have h1 : x ∉ (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.Ω (k + 1) :=
        fun h => hΩ ((mem_stepG'_top_iff g hnn hM1 H hk hρ x).1 h)
      simp only [h1, ↓reduceIte, hΩ]
      rfl
  -- the tests at the cubes of the data sites
  have hsub : ∀ x ∈ dataSites G, CubeSub (S := S) (n := n) M K (k + 1)
      (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x) Yf := by
    intro x hx
    have := hY (fineOfC g hnn hM1 hk x) ⟨x, hx, rfl⟩
    rwa [cubeMap_fineOfC_succ] at this
  have hOmB := omegaLevel_blockUnion (S := S) (n := n) g.M1 g.c (k + 1)
    {y | CubeSub (S := S) (n := n) M K (k + 1) y (a.Omega k)}
  have hm : g.c * n (k + 1) * S.L ^ (k + 1 - (k + 1)) = g.c * n (k + 1) := by simp
  set ψT : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - (k + 1))) → Fin N → ℂ :=
    fun w => ψ (k + 1) (LargeField.torusCast (histScale_eq g.hM hnn le_rfl hk) w) with hψT
  set ψK : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - k)) → Fin N → ℂ :=
    fun w => ψ k (LargeField.torusCast (histScale_eq g.hM hnn (q := k + 1) (Nat.le_succ k) hk) w)
    with hψK
  set hh : Fin N → ℂ := fun i => (h₀ i : ℂ) with hhh
  -- the single test of a cube away from the holes, the mixed test near them
  have hT : ∀ x ∈ dataSites G, cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∉ omegaCNb a 3 (k + 1) →
      InDomainC (genCube (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L) (q := k + 1) g.c (n (k + 1))
        (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x)) (μs (k + 1)) (ε (k + 1)) (ε (k + 1))
        (liftSingle (genCube (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L) (q := k + 1) g.c
          (n (k + 1)) (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x)) ψT hh) :=
    fun x hx hC => (htgt.1 (k + 1) le_rfl _ (hsub x hx) (fun _ _ => by simp [omegaNb]) hC).1
  have hMt : ∀ x ∈ dataSites G, cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ omegaCNb a 3 (k + 1) →
      InDomainC (genCubeMixed hm (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x) (omegaLevel (S := S) (n := n) g.M1 g.c (k + 1) {y | CubeSub (S := S) (n := n) M K (k + 1) y (a.Omega k)}) hOmB) (μs (k + 1))
        (ε k) (ε k) (mixedDataC hh hm (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x) (omegaLevel (S := S) (n := n) g.M1 g.c (k + 1) {y | CubeSub (S := S) (n := n) M K (k + 1) y (a.Omega k)}) hOmB ψK ψT) :=
    fun x hx hC => (htgt.2.1 k le_rfl _ (hsub x hx) (hroom x hx) hC).1
  -- the splits of the charts (a chart is a cube of `𝕋_{k+1}`)
  set T1 := Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))
  let spR : ∀ {Gc : GeneratingSet S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (minSep S.L g.M1)}
      {μc εc : ℝ} {Dc : BgData Gc N}, InDomainC Gc μc εc εc Dc → T1 → Fin N → ℝ :=
    fun h => h.choose
  let spC : ∀ {Gc : GeneratingSet S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (minSep S.L g.M1)}
      {μc εc : ℝ} {Dc : BgData Gc N}, InDomainC Gc μc εc εc Dc → T1 → Fin N → ℂ :=
    fun h => h.choose_spec.choose_spec.choose
  let PT : Torus S.d (n (k + 1)) → Prop := fun Y =>
    InDomainC (genCube (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L) (q := k + 1) g.c (n (k + 1)) Y)
      (μs (k + 1)) (ε (k + 1)) (ε (k + 1))
      (liftSingle (genCube (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L) (q := k + 1) g.c
        (n (k + 1)) Y) ψT hh)
  let PM : Torus S.d (n (k + 1)) → Prop := fun Y =>
    InDomainC (genCubeMixed hm Y (omegaLevel (S := S) (n := n) g.M1 g.c (k + 1) {y | CubeSub (S := S) (n := n) M K (k + 1) y (a.Omega k)}) hOmB) (μs (k + 1)) (ε k) (ε k)
      (mixedDataC hh hm Y (omegaLevel (S := S) (n := n) g.M1 g.c (k + 1) {y | CubeSub (S := S) (n := n) M K (k + 1) y (a.Omega k)}) hOmB ψK ψT)
  let Ψc : Torus S.d (n (k + 1)) → CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1) → Fin N → ℝ :=
    fun Y x => if h : Y ∈ omegaCNb a 3 (k + 1) ∧ PM Y then spR h.2 (toCube g hM1 x)
      else if h : PT Y then spR h (toCube g hM1 x) else 0
  let Ψc' : Torus S.d (n (k + 1)) → CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1) → Fin N → ℂ :=
    fun Y x => if h : Y ∈ omegaCNb a 3 (k + 1) ∧ PM Y then spC h.2 (toCube g hM1 x)
      else if h : PT Y then spC h (toCube g hM1 x) else 0
  let f : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1) → ℝ := fun x =>
    if cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ (H.step k).Omega then z else 1
  -- **the case analysis**: the split of the chart of a data site and its properties at the sites over
  -- cubes within one cube of its cube
  have key : ∀ x ∈ dataSites G,
      ∃ (Gc : GeneratingSet S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (minSep S.L g.M1))
        (Dc : BgData Gc N) (εc : ℝ) (Ψr : T1 → Fin N → ℝ) (hr : Fin N → ℝ) (Ψ' h' : T1 → Fin N → ℂ),
        0 < εc ∧ εc ≤ ε k ∧ InPsiTildeC Gc (μs (k + 1)) εc εc Ψr hr Ψ' h' ∧
        (∀ s ∈ dataSites Gc, ∀ i, Dc.Ψ s i = (Ψr s i : ℂ) + Ψ' s i) ∧
        (∀ s ∈ Gc.Ω 1, ∀ i, Dc.h s i = (hr i : ℂ) + h' s i) ∧
        (∀ s ∈ Gc.Ω 1, ∀ i, Dc.h s i = (h₀ i : ℂ)) ∧
        (∀ y, Ψc (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x) y = Ψr (toCube g hM1 y) ∧
          Ψc' (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x) y = Ψ' (toCube g hM1 y)) ∧
        (∀ x' ∈ dataSites G, LargeField.supDist (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x')
            (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x) ≤ 1 →
          toCube g hM1 x' ∈ Gc.Ω 1 ∧ toCube g hM1 x' ∈ dataSites Gc ∧
          (∀ i, (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D'.Ψ x' i =
            (f x' : ℂ) * Dc.Ψ (toCube g hM1 x') i) ∧
          G.layerIndex x' ≤ Gc.layerIndex (toCube g hM1 x') ∧
          toCube g hM1 x' ∈ Gc.layer (Gc.layerIndex (toCube g hM1 x')) ∧
          (Gc.layerIndex (toCube g hM1 x') = k ∨ Gc.layerIndex (toCube g hM1 x') = k + 1)) := by
    intro x hx
    set Y := cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x with hYdef
    have hnear : ∀ x' : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1),
        LargeField.supDist (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x') Y ≤ 1 →
        blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) (toCube g hM1 x') ∈ nbhd 2 {Y} :=
      fun x' h => mem_nbhd.2 ⟨Y, rfl, by rw [← cubeOfC_eq_toCube]; omega⟩
    by_cases hYC : Y ∈ omegaCNb a 3 (k + 1)
    · -- the mixed test `Δ'^c_{k+1}(□)`
      have hPM : PM Y := hMt x hx hYC
      have hsp := hPM.choose_spec.choose_spec.choose_spec.choose_spec
      refine ⟨_, _, ε k, hPM.choose, hPM.choose_spec.choose, hPM.choose_spec.choose_spec.choose,
        hPM.choose_spec.choose_spec.choose_spec.choose, hεk0, le_rfl, hsp.1, hsp.2.1, hsp.2.2,
        fun s hs i => ?_, fun y => ?_, fun x' hx' hd => ?_⟩
      · unfold mixedDataC; rw [liftMixed_h _ _ _ _ _ _ hs]
      · simp only [Ψc, Ψc', hYC, hPM, and_self, dite_true]
        exact ⟨rfl, rfl⟩
      · obtain ⟨h1, h2, h3, h4⟩ := genCubeMixed_site_spec hm hk1 Y (omegaLevel (S := S) (n := n) g.M1 g.c (k + 1) {y | CubeSub (S := S) (n := n) M K (k + 1) y (a.Omega k)}) hOmB (hnear x' hd)
        have hlG := layerIndex_locG'_le g hnn hM1 H hk hρ V x'
        refine ⟨h1, h2, fun i => ?_, ?_⟩
        · rw [hdat x' hx' i]
          unfold mixedDataC
          rw [liftMixed_Ψ _ _ _ _ _ _ h2]
          unfold mixedLift blockLift
          by_cases hΩ : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x' ∈ (H.step k).Omega
          · have hO : toCube g hM1 x' ∈ (omegaLevel (S := S) (n := n) g.M1 g.c (k + 1) {y | CubeSub (S := S) (n := n) M K (k + 1) y (a.Omega k)}) := (hOmem x').2 hΩ
            simp only [hΩ, hO, ↓reduceIte, f, hψT]
            rw [jBlock_toCube g hnn hM1 hk le_rfl x']
          · have hO : toCube g hM1 x' ∉ (omegaLevel (S := S) (n := n) g.M1 g.c (k + 1) {y | CubeSub (S := S) (n := n) M K (k + 1) y (a.Omega k)}) := fun h => hΩ ((hOmem x').1 h)
            simp only [hΩ, hO, ↓reduceIte, f, hψK, Complex.ofReal_one, one_mul]
            rw [jBlock_toCube g hnn hM1 hk (Nat.le_succ k) x']
        · by_cases hΩ : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x' ∈ (H.step k).Omega
          · obtain ⟨e, hl⟩ := h3 ((hOmem x').2 hΩ)
            rw [e]; exact ⟨hlG.1, hl, Or.inr rfl⟩
          · obtain ⟨e, hl⟩ := h4 (fun h => hΩ ((hOmem x').1 h))
            rw [e]; exact ⟨hlG.2 hΩ, hl, Or.inl rfl⟩
    · -- the single test `Δ^c_{k+1}(□)`
      have hPT : PT Y := hT x hx hYC
      have hsp := hPT.choose_spec.choose_spec.choose_spec.choose_spec
      refine ⟨_, _, ε (k + 1), hPT.choose, hPT.choose_spec.choose, hPT.choose_spec.choose_spec.choose,
        hPT.choose_spec.choose_spec.choose_spec.choose, hε0, hεk, hsp.1, hsp.2.1, hsp.2.2,
        fun s hs i => ?_, fun y => ?_, fun x' hx' hd => ?_⟩
      · rw [liftSingle_h _ _ _ hs]
      · have hn : ¬ (Y ∈ omegaCNb a 3 (k + 1) ∧ PM Y) := fun h => hYC h.1
        simp only [Ψc, Ψc', hYC, hPT, false_and, dite_false, dite_true]
        exact ⟨rfl, rfl⟩
      · obtain ⟨h1, h2, h3, h4⟩ := genCube_site_spec hm (by omega) Y (hnear x' hd)
        have hΩ : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x' ∈ (H.step k).Omega :=
          hfarΩ Y hYC _ (by rw [LargeField.supDist_comm]; omega)
        refine ⟨h1, h2, fun i => ?_, by rw [h3]; exact (layerIndex_locG'_le g hnn hM1 H hk hρ V x').1,
          by rw [h3]; exact h4, Or.inr h3⟩
        rw [hdat x' hx' i, liftSingle_Ψ _ _ _ h2]
        simp only [hΩ, ↓reduceIte, f, hψT]
        rw [jBlock_toCube g hnn hM1 hk le_rfl x']
  -- the patching
  have hL1 : 1 ≤ S.L := Nat.one_le_iff_ne_zero.2 (NeZero.ne S.L)
  refine inDomainC_of_patch_scaled (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D'
    hεk0 hεk0 hη hz f (fun x => by simp only [f]; split_ifs <;> simp) h₀
    (fun x hx i => (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).hh₀ x hx i)
    hR4 (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1) Ψc Ψc'
    (fun j hj1 hjk x hx x' hx' => cubeOfC_eq_of_jBlock g hnn hM1 hk hjk (GeneratingSet.mem_blk.1 hx'))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  -- the layer constancy of the splits on the blocks of `G′_V`
  · intro j hj1 hjk x hx x' hx'
    have hxd : x ∈ dataSites G := (mem_dataSites _).2 (Or.inl (G.layer_subset hj1 hjk hx))
    obtain ⟨Gc, Dc, εc, Ψr, hr, Ψ', h', -, -, hP, -, -, -, hsp, hsite⟩ := key x hxd
    have hcube := cubeOfC_eq_of_jBlock g hnn hM1 hk hjk (GeneratingSet.mem_blk.1 hx')
    obtain ⟨-, -, -, hlG, hlay, hkx⟩ := hsite x hxd (by rw [LargeField.supDist_self]; omega)
    have hjx : G.layerIndex x = j := G.layerIndex_eq hj1 hjk hx
    have hl1 : 1 ≤ Gc.layerIndex (toCube g hM1 x) := by omega
    have hlk : Gc.layerIndex (toCube g hM1 x) ≤ k + 1 := by omega
    have hb := toCube_mem_blk g hM1 (hjx ▸ hlG) hlk hx' Gc
    rw [(hsp x').1, (hsp x).1, (hsp x').2, (hsp x).2]
    exact ⟨hP.layerConst _ hl1 hlk _ hlay _ hb, hP.layerConst' _ hl1 hlk _ hlay _ hb,
      by simp only [f, hcube]⟩
  -- the datum is the scaled value of the split of its chart
  · intro x hx i
    obtain ⟨Gc, Dc, εc, Ψr, hr, Ψ', h', -, -, hP, hΨ, -, -, hsp, hsite⟩ := key x hx
    obtain ⟨-, h2, hdat', -⟩ := hsite x hx (by rw [LargeField.supDist_self]; omega)
    rw [hdat' i, hΨ _ h2 i, (hsp x).1, (hsp x).2]
  -- (R2)
  · intro x hx
    obtain ⟨Gc, Dc, εc, Ψr, hr, Ψ', h', -, hεc, hP, -, -, -, hsp, hsite⟩ := key x hx
    obtain ⟨-, h2, -⟩ := hsite x hx (by rw [LargeField.supDist_self]; omega)
    simp only [(hsp x).1]
    exact (hP.r2 _ h2).trans_le hεc
  -- (R3), in the two mass regimes
  · intro x hx
    obtain ⟨Gc, Dc, εc, Ψr, hr, Ψ', h', hε0', hεc, hP, -, hhr, hh0, hsp, hsite⟩ := key x hx
    obtain ⟨h1, h2, -, hlG, -⟩ := hsite x hx (by rw [LargeField.supDist_self]; omega)
    simp only [(hsp x).1]
    rcases hmass with ⟨hν, hsmall⟩ | ⟨hν, hνμ, h2ε⟩
    · exact r3_of_small_mass hν hL1 (layerIndex_locG'_le g hnn hM1 H hk hρ V x).1 h₀ hsmall _
    · have hh' : ∀ i, h' (toCube g hM1 x) i = ((h₀ i - hr i : ℝ) : ℂ) := fun i => by
        have e1 := hhr _ h1 i
        have e2 := hh0 _ h1 i
        push_cast
        linear_combination e2 - e1
      have h3 := r3_of_large_mass hν hνμ hL1 hlG _ hr h₀ _ hh' (hP.r3 _ h2) (hP.c3b _ h1)
      refine h3.trans_le (le_trans ?_ h2ε)
      have : εc ^ 2 ≤ ε k ^ 2 := pow_le_pow_left₀ hε0'.le hεc 2
      linarith
  -- (C2a)
  · intro x hx
    obtain ⟨Gc, Dc, εc, Ψr, hr, Ψ', h', -, hεc, hP, -, -, -, hsp, hsite⟩ := key x hx
    obtain ⟨-, h2, -⟩ := hsite x hx (by rw [LargeField.supDist_self]; omega)
    rw [show Ψc' (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x) x = Ψ' (toCube g hM1 x) from (hsp x).2]
    have := hP.c2a _ h2
    linarith
  -- (C2b)
  · intro x hx
    obtain ⟨Gc, Dc, εc, Ψr, hr, Ψ', h', -, hεc, hP, -, -, -, hsp, hsite⟩ := key x hx
    obtain ⟨-, h2, -⟩ := hsite x hx (by rw [LargeField.supDist_self]; omega)
    rw [(hsp x).1, (hsp x).2]
    exact (hP.c2b _ h2).trans_le hεc
  -- the interface pairs, read by the test of the chart of the first site
  · intro x x' hp
    obtain ⟨hxd, hx'd, -, hba⟩ := hp
    obtain ⟨Gc, Dc, εc, Ψr, hr, Ψ', h', -, hεc, hP, hΨ, -, -, hsp, hsite⟩ := key x hxd
    have hd : LargeField.supDist (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x')
        (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x) ≤ 1 := by
      rw [LargeField.supDist_comm]; exact cubeOfC_near_of_pair g hnn hM1 H hk hρ V hba
    obtain ⟨h1', h2', hdat', hlG', -, hk'⟩ := hsite x' hx'd hd
    obtain ⟨h1, h2, -, hlG, -, hkx⟩ := hsite x hxd (by rw [LargeField.supDist_self]; omega)
    obtain ⟨y₀, hy₀, y₀', hy₀', hadj⟩ := hba
    have hbs : ∀ s, s ∈ Gc.Ω 1 → blockSet Gc s = Gc.blk (Gc.layerIndex s) s := fun s hs => by
      classical
      unfold blockSet; simp only [hs, ↓reduceIte]
    have hy₀c : toCube g hM1 y₀ ∈ blockSet Gc (toCube g hM1 x) := by
      rw [hbs _ h1]; exact toCube_mem_blk_of_blockSet g hnn hM1 H hk hρ V hy₀ hlG (by omega) Gc
    have hy₀c' : toCube g hM1 y₀' ∈ blockSet Gc (toCube g hM1 x') := by
      rw [hbs _ h1']; exact toCube_mem_blk_of_blockSet g hnn hM1 H hk hρ V hy₀' hlG' (by omega) Gc
    have hadjc := adj_toCube g hM1 hadj
    have hpair : rn (fun i => Ψr (toCube g hM1 x) i - Ψr (toCube g hM1 x') i) < εc ∧
        vn (Ψ' (toCube g hM1 x) - Ψ' (toCube g hM1 x')) < εc := by
      by_cases hlay : Gc.layerIndex (toCube g hM1 x') = Gc.layerIndex (toCube g hM1 x) ∨
          Gc.layerIndex (toCube g hM1 x') + 1 = Gc.layerIndex (toCube g hM1 x)
      · have hI : IsInterfacePair Gc (toCube g hM1 x) (toCube g hM1 x') :=
          ⟨h2, h2', hlay, _, hy₀c, _, hy₀c', hadjc⟩
        exact ⟨hP.r1 _ _ hI, hP.c1 _ _ hI⟩
      · have hlay' : Gc.layerIndex (toCube g hM1 x) + 1 = Gc.layerIndex (toCube g hM1 x') := by omega
        have hI : IsInterfacePair Gc (toCube g hM1 x') (toCube g hM1 x) :=
          ⟨h2', h2, Or.inr hlay', _, hy₀c', _, hy₀c, hadjc.symm⟩
        refine ⟨?_, ?_⟩
        · have e : rn (fun i => Ψr (toCube g hM1 x) i - Ψr (toCube g hM1 x') i) =
              rn (fun i => Ψr (toCube g hM1 x') i - Ψr (toCube g hM1 x) i) := by
            unfold rn; congr 1; exact Finset.sum_congr rfl fun i _ => by ring
          rw [e]; exact hP.r1 _ _ hI
        · rw [vn_sub_comm]; exact hP.c1 _ _ hI
    rw [(hsp x).1, (hsp x').1, (hsp x).2, (hsp x').2]
    refine ⟨hpair.1.trans_le hεc, hpair.2.trans_le hεc, fun i => by rw [hdat' i, hΨ _ h2' i], ?_,
      (hP.r2 _ h2').trans_le hεc⟩
    have := hP.c2a _ h2'
    linarith

end Datum

end Balaban.RootFSpine
