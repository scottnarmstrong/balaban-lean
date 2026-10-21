/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldDatumGeo
public import Balaban.Background.DataPatchChart

/-!
# The datum of the local pair from the cube tests of the target H7 domain (target (3) of W1154d, (3a) of W1154e)

`inDomainC_holeStepLoc2_of_h7`: **the case analysis and proof of `H7MixedDatumLoc2`** for any local set
`V`, at a target history `a` whose holes at scale `k + 1` contain every cube off `Ω_{k+1}` (ruling R17:
the pre-`R` records `globalLHPre`; or `globalLH` without a removal at scale `k + 1`), provided the data
sites of `G′_V` farther than `3` cubes from `Ω_{k+1}` lie over cubes of `𝕋_k` outside the holes of
scale `k` (`hfar`).  Each data site is read by one cube test, its *chart*:

* over a cube `□` of `𝕋_{k+1}` in `Ω^{∼3}_{k+1}`: `Δ'^c_{k+1}(□)` when `□` is within `3` cubes of a hole,
  `Δ^c_{k+1}(□)` otherwise (then `□^{∼3} ⊂ Ω_{k+1}`);
* over a cube of `𝕋_{k+1}` outside `Ω^{∼3}_{k+1}`: `Δ^c_k(□_k)` at its cube `□_k` of `𝕋_k` (a cube set of
  `𝕋_k` on the torus of scale `k`, read through `toCubeK`); the site and its interface partners lie off
  `Ω_{k+1}`, where the datum is `ψ_k`.

The splits of the charts patch by `inDomainC_of_patch_scaled`; the conditions at one chart are
`Background.chartSplit_spec`.
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
case analysis of `H7MixedDatumLoc2`): the target H7 domain of scale `k + 1` at a history `a` whose top
region is `Ω_{k+1}` and whose holes at scale `k + 1` contain every cube off `Ω_{k+1}` (`hholes`: the
pre-`R` records of ruling R17, `globalLHPre`, or `globalLH` without a removal at `k + 1`), at a set `Y_f`
containing the cubes of the data sites (`CubesOfIn`), with the data sites of `G′_V` over cubes of `𝕋_{k+1}`
outside `Ω^{∼3}_{k+1}` lying over cubes of `𝕋_k` outside the holes `(Ω^c_k)^{∼3}` of scale `k` (`hfar`).
Each data site `x` is read by the test of its chart: `Δ'^c_{k+1}(□)` (the pair `(ψ_k, ψ_{k+1})`,
`Ψ̃^c(ε_k, ε_k)`) or `Δ^c_{k+1}(□)` (`ψ_{k+1}`, `Ψ̃^c(ε_{k+1}, ε_{k+1})`) at its cube `□` of `𝕋_{k+1}` when
`□ ∈ Ω^{∼3}_{k+1}` (according as `□` is within `3` cubes of a hole or not), `Δ^c_k(□_k)` (`ψ_k`,
`Ψ̃^c(ε_k, ε_k)`) at its cube `□_k` of `𝕋_k` otherwise; each test reads every interface partner of `x`.
The splits patch (`inDomainC_of_patch_scaled`, `θ = z ψ_{k+1}` on `Ω_{k+1}`, `|z - 1| ≤ η`) into
`Ψ̃^c(3δ₁ + 2ε_k, 3δ₁ + 2ε_k)`, `δ₁ = scaledTol ε_k ε_k η`, under condition (R4) for `h₀` and the mass
condition `hmass` (small mass, or `ν ≤ μ_{k+1}`, `ν ≤ μ_k` with `2 ε_k² ≤ δ₁²`). -/
theorem inDomainC_holeStepLoc2_of_h7 (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
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
    (hfar : ∀ x ∈ dataSites (locG' g hnn hM1 H hk hρ V),
      cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∉ omegaNb a (k + 1) 3 (k + 1) →
        cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x ∉ omegaCNb a 3 k)
    {η : ℝ} (hη : 0 ≤ η) (hz : |z - 1| ≤ η) (hε0 : 0 < ε (k + 1)) (hεk : ε (k + 1) ≤ ε k)
    (hR4 : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < scaledTol (ε k) (ε k) η ^ 2)
    (hmass : (0 ≤ ν ∧ ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * (1 + rn h₀) < scaledTol (ε k) (ε k) η ^ 2) ∨
      (0 ≤ ν ∧ ν ≤ μs (k + 1) ∧ ν ≤ μs k ∧ 2 * ε k ^ 2 ≤ scaledTol (ε k) (ε k) η ^ 2)) :
    InDomainC (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' ν
      (3 * scaledTol (ε k) (ε k) η + 2 * ε k) (3 * scaledTol (ε k) (ε k) η + 2 * ε k)
      (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D' := by
  classical
  have hc := g.hc
  have hkK : k ≤ K := Nat.le_of_succ_le hk
  set G := locG' g hnn hM1 H hk hρ V with hG
  set D' := (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D' with hD'
  have hεk0 : 0 < ε k := hε0.trans_le hεk
  have hL1 : 1 ≤ S.L := Nat.one_le_iff_ne_zero.2 (NeZero.ne S.L)
  -- `Ω^{∼3}_{k+1}` and the cubes away from the holes
  have hΩ3 : ∀ Y Y' : Torus S.d (n (k + 1)), Y' ∈ (H.step k).Omega → LargeField.supDist Y Y' ≤ 3 →
      Y ∈ omegaNb a (k + 1) 3 (k + 1) := by
    intro Y Y' hY' hd
    unfold omegaNb
    simp only [show k + 1 ≠ k + 1 + 1 by omega, ↓reduceIte]
    refine mem_nbhd.2 ⟨Y', ?_, hd⟩
    show CubeSub (S := S) (n := n) M K (k + 1) Y' (a.Omega k)
    rw [haΩ]
    exact (cubeSub_fineSet_iff hnn hk _ _).2 hY'
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
  have hdat : ∀ x ∈ dataSites G, ∀ i, D'.Ψ x i =
        if cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ (H.step k).Omega then
          (z : ℂ) * ψ (k + 1) (coverBlk g hnn hM1 hk (k + 1) le_rfl x) i
        else ψ k (coverBlk g hnn hM1 hk k (Nat.le_succ k) x) i := by
    intro x hx i
    rw [hD', holeStepLoc2_D'_Ψ g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hx]
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
  -- the sites of the cube of `𝕋_k` of a site lie in its cube of `𝕋_{k+1}`
  have hsucc : ∀ (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (x' : Torus S.d (M * n K * S.L ^ K)),
      LargeField.cubeMap n S.L M K k x' = cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x →
      LargeField.cubeMap n S.L M K (k + 1) x' = cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x := by
    intro x x' hx'
    rw [← cubeMap_succ hnn hk x', hx', blockMap_cubeKOfC g hnn hM1 hk x]
  have hOmB := omegaLevel_blockUnion (S := S) (n := n) g.M1 g.c (k + 1)
    {y | CubeSub (S := S) (n := n) M K (k + 1) y (a.Omega k)}
  have hm : g.c * n (k + 1) * S.L ^ (k + 1 - (k + 1)) = g.c * n (k + 1) := by simp
  have hm0 : g.c * n k * S.L ^ (k - k) = g.c * n k := by simp
  set ψT : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - (k + 1))) → Fin N → ℂ :=
    fun w => ψ (k + 1) (LargeField.torusCast (histScale_eq g.hM hnn le_rfl hk) w) with hψT
  set ψK : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - k)) → Fin N → ℂ :=
    fun w => ψ k (LargeField.torusCast (histScale_eq g.hM hnn (q := k + 1) (Nat.le_succ k) hk) w)
    with hψK
  set ψK0 : Torus S.d (g.M1 * (g.c * n k) * S.L ^ (k - k)) → Fin N → ℂ :=
    fun w => ψ k (LargeField.torusCast (histScale_eq g.hM hnn le_rfl hkK) w) with hψK0
  set hh : Fin N → ℂ := fun i => (h₀ i : ℂ) with hhh
  set Om := omegaLevel (S := S) (n := n) g.M1 g.c (k + 1)
    {y | CubeSub (S := S) (n := n) M K (k + 1) y (a.Omega k)} with hOm
  -- the three cube tests
  let PT : Torus S.d (n (k + 1)) → Prop := fun Y =>
    InDomainC (genCube (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L) (q := k + 1) g.c (n (k + 1)) Y)
      (μs (k + 1)) (ε (k + 1)) (ε (k + 1))
      (liftSingle (genCube (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L) (q := k + 1) g.c
        (n (k + 1)) Y) ψT hh)
  let PM : Torus S.d (n (k + 1)) → Prop := fun Y =>
    InDomainC (genCubeMixed hm Y Om hOmB) (μs (k + 1)) (ε k) (ε k) (mixedDataC hh hm Y Om hOmB ψK ψT)
  let PK : Torus S.d (n k) → Prop := fun y =>
    InDomainC (genCube (M1 := g.M1) (N₁ := g.c * n k) (L := S.L) (q := k) g.c (n k) y)
      (μs k) (ε k) (ε k)
      (liftSingle (genCube (M1 := g.M1) (N₁ := g.c * n k) (L := S.L) (q := k) g.c (n k) y) ψK0 hh)
  have hT : ∀ x ∈ dataSites G, cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∉ omegaCNb a 3 (k + 1) →
      PT (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x) :=
    fun x hx hC => (htgt.1 (k + 1) le_rfl _ (hsub x hx) (fun _ _ => by simp [omegaNb]) hC).1
  have hMt : ∀ x ∈ dataSites G, cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ omegaCNb a 3 (k + 1) →
      cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ omegaNb a (k + 1) 3 (k + 1) →
      PM (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x) :=
    fun x hx hC hN => (htgt.2.1 k le_rfl _ (hsub x hx) hN hC).1
  have hKt : ∀ x ∈ dataSites G, cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∉ omegaNb a (k + 1) 3 (k + 1) →
      PK (cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x) := by
    intro x hx hN
    refine (htgt.1 k (Nat.le_succ k) _ (fun x' hx' => hsub x hx x' (hsucc x x' hx'))
      (fun x' hx' => by rw [hsucc x x' hx']; exact hN) (hfar x hx hN)).1
  -- the charts and their splits
  let ch : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1) → Torus S.d (n (k + 1)) ⊕ Torus S.d (n k) :=
    fun x => if cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ omegaNb a (k + 1) 3 (k + 1) then
      Sum.inl (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x)
      else Sum.inr (cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x)
  let Ψc : Torus S.d (n (k + 1)) ⊕ Torus S.d (n k) → CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1) →
      Fin N → ℝ :=
    Sum.elim
      (fun Y x => if h : Y ∈ omegaCNb a 3 (k + 1) ∧ PM Y then h.2.choose (toCube g hM1 x)
        else if h : PT Y then h.choose (toCube g hM1 x) else 0)
      (fun y x => if h : PK y then h.choose (toCubeK g hnn hM1 hk x) else 0)
  let Ψc' : Torus S.d (n (k + 1)) ⊕ Torus S.d (n k) → CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1) →
      Fin N → ℂ :=
    Sum.elim
      (fun Y x => if h : Y ∈ omegaCNb a 3 (k + 1) ∧ PM Y then
          h.2.choose_spec.choose_spec.choose (toCube g hM1 x)
        else if h : PT Y then h.choose_spec.choose_spec.choose (toCube g hM1 x) else 0)
      (fun y x => if h : PK y then h.choose_spec.choose_spec.choose (toCubeK g hnn hM1 hk x) else 0)
  let f : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1) → ℝ := fun x =>
    if cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ (H.step k).Omega then z else 1
  -- **the case analysis**: the chart of a data site and the conditions its split gives
  have key : ∀ x ∈ dataSites G, ∃ (μc : ℝ) (In : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1) → Prop),
      (∀ ν' : ℝ, ν' ≤ μs (k + 1) → ν' ≤ μs k → ν' ≤ μc) ∧
      (∀ x', IsInterfacePair G x x' → In x') ∧
      (∀ j, 1 ≤ j → j ≤ k + 1 → x ∈ G.layer j → ∀ x' ∈ G.blk j x,
        Ψc (ch x) x' = Ψc (ch x) x ∧ Ψc' (ch x) x' = Ψc' (ch x) x) ∧
      (∀ i, D'.Ψ x i = (f x : ℂ) * ((Ψc (ch x) x i : ℂ) + Ψc' (ch x) x i)) ∧
      |∑ i, Ψc (ch x) x i ^ 2 - 1| < ε k ∧
      vn (Ψc' (ch x) x) < ε k + ε k ∧
      ‖∑ i, ((Ψc (ch x) x i : ℂ) + Ψc' (ch x) x i) * ((Ψc (ch x) x i : ℂ) + Ψc' (ch x) x i) -
        ∑ i, (Ψc (ch x) x i : ℂ) * (Ψc (ch x) x i : ℂ)‖ < ε k ∧
      (∀ ν' : ℝ, 0 ≤ ν' → ν' ≤ μc → ν' * ((S.L : ℝ) ^ G.layerIndex x) ^ 2 *
        |1 - (∑ i, Ψc (ch x) x i * h₀ i) / rn (Ψc (ch x) x)| < 2 * ε k ^ 2) ∧
      (∀ x', IsInterfacePair G x x' → In x' →
        rn (fun i => Ψc (ch x) x i - Ψc (ch x) x' i) < ε k ∧ vn (Ψc' (ch x) x - Ψc' (ch x) x') < ε k ∧
        (∀ i, D'.Ψ x' i = (f x' : ℂ) * ((Ψc (ch x) x' i : ℂ) + Ψc' (ch x) x' i)) ∧
        vn (Ψc' (ch x) x') < ε k + ε k ∧ |∑ i, Ψc (ch x) x' i ^ 2 - 1| < ε k) := by
    intro x hx
    set Y := cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x with hYdef
    by_cases hN : Y ∈ omegaNb a (k + 1) 3 (k + 1)
    · -- a chart of `𝕋_{k+1}`: the sites over cubes within one cube of `□`
      have hch : ch x = Sum.inl Y := by simp only [ch, ← hYdef, hN, ↓reduceIte]
      let In : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1) → Prop := fun x' =>
        x' ∈ dataSites G ∧ LargeField.supDist (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x') Y ≤ 1
      have hnear : ∀ x' : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1), In x' →
          blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) (toCube g hM1 x') ∈ nbhd 2 {Y} :=
        fun x' h => mem_nbhd.2 ⟨Y, rfl, by rw [← cubeOfC_eq_toCube]; have := h.2; omega⟩
      have hpIn : ∀ x', IsInterfacePair G x x' → In x' := fun x' hp => ⟨hp.2.1, by
        rw [LargeField.supDist_comm]; exact cubeOfC_near_of_pair g hnn hM1 H hk hρ V hp.2.2.2⟩
      have hIn0 : In x := ⟨hx, by rw [LargeField.supDist_self]; omega⟩
      have hblk1 : ∀ {ϱ' : ℝ} (Gc : GeneratingSet S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) ϱ')
          (x₁ y₁ : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)), y₁ ∈ blockSet G x₁ →
          ∀ l, G.layerIndex x₁ ≤ l → l ≤ k + 1 → toCube g hM1 y₁ ∈ Gc.blk l (toCube g hM1 x₁) :=
        fun Gc _ _ hy l hl hlq => toCube_mem_blk_of_blockSet g hnn hM1 H hk hρ V hy hl hlq Gc
      by_cases hYC : Y ∈ omegaCNb a 3 (k + 1)
      · -- the mixed test `Δ'^c_{k+1}(□)`
        have hPM : PM Y := hMt x hx hYC hN
        have hsp := hPM.choose_spec.choose_spec.choose_spec.choose_spec
        refine ⟨μs (k + 1), In, fun _ h _ => h, hpIn, ?_⟩
        refine chartSplit_spec D' f h₀ hsp.1 le_rfl hsp.2.1
          hsp.2.2 (fun s hs i => by unfold mixedDataC; rw [liftMixed_h _ _ _ _ _ _ hs])
          (toCube g hM1) (fun _ _ h => adj_toCube g hM1 h) (hblk1 _) In ?_ _ _
          (fun y => by constructor <;> simp only [Ψc, Ψc', hch, Sum.elim_inl, hYC, hPM, and_self, dite_true])
          hIn0
        intro x' hx'
        obtain ⟨h1, h2, h3, h4⟩ := genCubeMixed_site_spec hm hk1 Y Om hOmB (hnear x' hx')
        have hlG := layerIndex_locG'_le g hnn hM1 H hk hρ V x'
        refine ⟨h1, fun i => ?_, ?_⟩
        · rw [hdat x' hx'.1 i]
          unfold mixedDataC
          rw [liftMixed_Ψ _ _ _ _ _ _ h2]
          unfold mixedLift blockLift
          by_cases hΩ : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x' ∈ (H.step k).Omega
          · have hO : toCube g hM1 x' ∈ Om := (hOmem x').2 hΩ
            simp only [hΩ, hO, ↓reduceIte, f, hψT]
            rw [jBlock_toCube g hnn hM1 hk le_rfl x']
          · have hO : toCube g hM1 x' ∉ Om := fun h => hΩ ((hOmem x').1 h)
            simp only [hΩ, hO, ↓reduceIte, f, hψK, Complex.ofReal_one, one_mul]
            rw [jBlock_toCube g hnn hM1 hk (Nat.le_succ k) x']
        · by_cases hΩ : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x' ∈ (H.step k).Omega
          · obtain ⟨e, -⟩ := h3 ((hOmem x').2 hΩ)
            rw [e]; exact ⟨hlG.1, by omega⟩
          · obtain ⟨e, -⟩ := h4 (fun h => hΩ ((hOmem x').1 h))
            rw [e]; exact ⟨hlG.2 hΩ, by omega⟩
      · -- the single test `Δ^c_{k+1}(□)`
        have hPT : PT Y := hT x hx hYC
        have hsp := hPT.choose_spec.choose_spec.choose_spec.choose_spec
        have hn : ¬ (Y ∈ omegaCNb a 3 (k + 1) ∧ PM Y) := fun h => hYC h.1
        refine ⟨μs (k + 1), In, fun _ h _ => h, hpIn, ?_⟩
        refine chartSplit_spec D' f h₀ hsp.1 hεk hsp.2.1
          hsp.2.2 (fun s hs i => by rw [liftSingle_h _ _ _ hs])
          (toCube g hM1) (fun _ _ h => adj_toCube g hM1 h) (hblk1 _) In ?_ _ _
          (fun y => by
            constructor <;> simp only [Ψc, Ψc', hch, Sum.elim_inl, hn, hPT, dite_false, dite_true])
          hIn0
        intro x' hx'
        obtain ⟨h1, h2, h3, -⟩ := genCube_site_spec hm (by omega) Y (hnear x' hx')
        have hΩ : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x' ∈ (H.step k).Omega :=
          hfarΩ Y hYC _ (by rw [LargeField.supDist_comm]; have := hx'.2; omega)
        refine ⟨h1, fun i => ?_, by rw [h3]; exact (layerIndex_locG'_le g hnn hM1 H hk hρ V x').1,
          by rw [h3]; omega⟩
        rw [hdat x' hx'.1 i, liftSingle_Ψ _ _ _ h2]
        simp only [hΩ, ↓reduceIte, f, hψT]
        rw [jBlock_toCube g hnn hM1 hk le_rfl x']
    · -- far from `Ω_{k+1}`: the test `Δ^c_k(□_k)` at the cube of `𝕋_k`
      set y := cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x with hydef
      have hch : ch x = Sum.inr y := by simp only [ch, ← hYdef, hN, ↓reduceIte]; rfl
      have hPK : PK y := hKt x hx hN
      have hsp := hPK.choose_spec.choose_spec.choose_spec.choose_spec
      have hxΩ : Y ∉ (H.step k).Omega := fun h => hN (hΩ3 Y Y h (by rw [LargeField.supDist_self]; omega))
      let In : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1) → Prop := fun x' =>
        x' ∈ dataSites G ∧
          LargeField.supDist (cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x') y ≤ 1 ∧
          cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x' ∉ (H.step k).Omega
      have hpIn : ∀ x', IsInterfacePair G x x' → In x' := by
        intro x' hp
        have hd := cubeOfC_near_of_pair g hnn hM1 H hk hρ V hp.2.2.2
        have hx'Ω : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x' ∉ (H.step k).Omega :=
          fun h => hN (hΩ3 Y _ h (hd.trans (by norm_num)))
        refine ⟨hp.2.1, ?_, hx'Ω⟩
        rw [LargeField.supDist_comm]
        exact cubeKOfC_near_of_pair g hnn hM1 H hk hρ V hp.2.2.2
          ((layerIndex_locG'_le g hnn hM1 H hk hρ V x).2 hxΩ)
          ((layerIndex_locG'_le g hnn hM1 H hk hρ V x').2 hx'Ω)
      refine ⟨μs k, In, fun _ _ h => h, hpIn, ?_⟩
      refine chartSplit_spec D' f h₀ hsp.1 le_rfl hsp.2.1
        hsp.2.2 (fun s hs i => by rw [liftSingle_h _ _ _ hs])
        (toCubeK g hnn hM1 hk) (fun _ _ h => adj_toCubeK g hnn hM1 hk h)
        (fun _ _ hy l hl hlq => toCubeK_mem_blk_of_blockSet g hnn hM1 H hk hρ V hy hl hlq _) In ?_ _ _
        (fun y' => by constructor <;> simp only [Ψc, Ψc', hch, Sum.elim_inr, hPK, dite_true])
        ⟨hx, by rw [LargeField.supDist_self]; omega, hxΩ⟩
      intro x' hx'
      have hs : blockMap (S.L ^ k * (g.c * g.M1)) (n k) (toCubeK g hnn hM1 hk x') ∈ nbhd 2 {y} :=
        mem_nbhd.2 ⟨y, rfl, by rw [← cubeKOfC_eq_toCubeK]; have := hx'.2.1; omega⟩
      obtain ⟨h1, h2, h3, -⟩ := genCube_site_spec hm0 hk1 y hs
      refine ⟨h1, fun i => ?_, by rw [h3]; exact (layerIndex_locG'_le g hnn hM1 H hk hρ V x').2 hx'.2.2,
        by rw [h3]; omega⟩
      rw [hdat x' hx'.1 i, liftSingle_Ψ _ _ _ h2]
      simp only [hx'.2.2, ↓reduceIte, f, hψK0, Complex.ofReal_one, one_mul]
      rw [coverBlk_eq_toCubeK g hnn hM1 hk le_rfl x']
  -- the patching
  refine inDomainC_of_patch_scaled D' hεk0 hεk0 hη hz f (fun x => by simp only [f]; split_ifs <;> simp) h₀
    (fun x hx i => (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).hh₀ x hx i)
    hR4 ch Ψc Ψc' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  -- the chart is constant on the blocks of `G′_V`
  · intro j hj1 hjk x hx x' hx'
    have hcube := cubeOfC_eq_of_jBlock g hnn hM1 hk hjk (GeneratingSet.mem_blk.1 hx')
    simp only [ch, hcube]
    split_ifs with hN
    · rfl
    · have hxΩ : cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∉ (H.step k).Omega :=
        fun h => hN (hΩ3 _ _ h (by rw [LargeField.supDist_self]; omega))
      have hjx : G.layerIndex x = j := G.layerIndex_eq hj1 hjk hx
      have hjk' : j ≤ k := hjx ▸ (layerIndex_locG'_le g hnn hM1 H hk hρ V x).2 hxΩ
      rw [cubeKOfC_eq_of_jBlock g hnn hM1 hk hjk' (GeneratingSet.mem_blk.1 hx')]
  -- the layer constancy of the splits on the blocks of `G′_V`
  · intro j hj1 hjk x hx x' hx'
    have hxd : x ∈ dataSites G := (mem_dataSites _).2 (Or.inl (G.layer_subset hj1 hjk hx))
    obtain ⟨-, -, -, -, hlc, -⟩ := key x hxd
    have hcube := cubeOfC_eq_of_jBlock g hnn hM1 hk hjk (GeneratingSet.mem_blk.1 hx')
    exact ⟨(hlc j hj1 hjk hx x' hx').1, (hlc j hj1 hjk hx x' hx').2, by simp only [f, hcube]⟩
  -- the datum is the scaled value of the split of its chart
  · intro x hx i
    obtain ⟨-, -, -, -, -, hsplit, -⟩ := key x hx
    exact hsplit i
  -- (R2)
  · intro x hx
    obtain ⟨-, -, -, -, -, -, hr2, -⟩ := key x hx
    exact hr2
  -- (R3), in the two mass regimes
  · intro x hx
    obtain ⟨μc, -, hμc, -, -, -, -, -, -, hr3, -⟩ := key x hx
    rcases hmass with ⟨hν, hsmall⟩ | ⟨hν, hνμ, hνμk, h2ε⟩
    · exact r3_of_small_mass hν hL1 (layerIndex_locG'_le g hnn hM1 H hk hρ V x).1 h₀ hsmall _
    · exact (hr3 ν hν (hμc ν hνμ hνμk)).trans_le h2ε
  -- (C2a)
  · intro x hx
    obtain ⟨-, -, -, -, -, -, -, hc2a, -⟩ := key x hx
    exact hc2a
  -- (C2b)
  · intro x hx
    obtain ⟨-, -, -, -, -, -, -, -, hc2b, -⟩ := key x hx
    exact hc2b
  -- the interface pairs, read by the test of the chart of the first site
  · intro x x' hp
    obtain ⟨-, In, -, hpIn, -, -, -, -, -, -, hpair⟩ := key x hp.1
    exact hpair x' hp (hpIn x' hp)

end Datum

end Balaban.RootFSpine
