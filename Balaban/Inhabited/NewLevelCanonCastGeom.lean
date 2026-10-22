/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanonCast
public import Balaban.Inhabited.NewLevelCanonGeom

/-!
# `HGeom` for the canonical covers of the settings

`hgeom_of_cast`: the geometry of the canonical covers (`HGeom`) for covers whose generating sets are
the cast local sets of the settings (`CanonCoverCast`).  The margin `Z` is the union of the
`L^{k+1}`-cells of the sites within `L^{k+1}` of the data sites of `Gk`; the region `X₁` contains the
`ℓ¹`-ball of radius `r₀ L^{m₁} L^{k+1}` around the data sites (`BgSetting.hN`), whence
`hreg`; the correspondence of `Gk`, `Gj` on the two tori is `castLocalB_omega_boxMap_all` with
`castNbhd_image`, `kernelSet_boxMap`, `hatFine_boxMap`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Polymer.TwoTorusStep
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField

section CastGeom

variable {d L N₁ N₂ NA NB m₁ k N s : ℕ} [NeZero N₁] [NeZero N₂] [NeZero NA] [NeZero NB] [NeZero L]
  {ϱ ϱ₁ ϱ₁' : ℝ}

/-- The sites of `X̂` lie in the box of radius `R + 2 s_h`. -/
theorem hatSet_inBox {m₀ j R : ℕ} {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : ∀ y ∈ X, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 2 * (R + 2 * ((2 * (L / 2) + 1) * cellSide L m₀ m₁ j)) + 1 <
      (N₁ * L ^ m₁) * L ^ (k + 1)) :
    ∀ z ∈ hatSet m₀ j X, InBox d (R + (2 * (L / 2) + 1) * cellSide L m₀ m₁ j +
      (2 * (L / 2) + 1) * cellSide L m₀ m₁ j) ((N₁ * L ^ m₁) * L ^ (k + 1)) z := by
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hh : L / 2 * cellSide L m₀ m₁ j + cellSide L m₀ m₁ j ≤
      (2 * (L / 2) + 1) * cellSide L m₀ m₁ j := by
    have : L / 2 * cellSide L m₀ m₁ j + cellSide L m₀ m₁ j = (L / 2 + 1) * cellSide L m₀ m₁ j := by
      ring
    rw [this]
    exact Nat.mul_le_mul_right _ (by omega)
  rintro z ⟨y, hy, hz⟩
  exact inBox_of_cubeAt ha0 hh hn (hX y hy) hz

local notation "bmC" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₂ * L ^ m₁) * L ^ (k + 1))
local notation "bmF" => boxMap ((NA * L ^ (m₁ + s)) * L ^ (k + 1)) ((NB * L ^ (m₁ + s)) * L ^ (k + 1))

/-- **The sets of the kernel of `Gk` and of `Gj` lie in the box and correspond; the generating sets
`Gk`, `Gj` of the pair and of its image correspond on the box** (`GSCorr`, and `GSIso` on any region
containing the sites of `Ω₁(Gk)` and their neighbours). -/
theorem pair_gs_corr {m₀ : ℕ} {F : CanonCover d L N₁ m₁ k ϱ ϱ₁} {F' : CanonCover d L N₂ m₁ k ϱ ϱ₁'}
    {hcA : NA * L ^ (m₁ + s) = N₁ * L ^ m₁} {hcB : NB * L ^ (m₁ + s) = N₂ * L ^ m₁}
    (LC : CanonCoverCast m₀ s hcA hcB F F') (hL : 2 ≤ L) (hk1 : 1 ≤ k)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₂) {j : ℕ} {y₀ : CTorus d L N₁ m₁ (k + 1)}
    {X₀ : Set (CTorus d L N₁ m₁ (k + 1))}
    (hadm : (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d m₀ k)
    (hadmB : (j, bmC y₀, bmC '' X₀) ∈ AdmPairs L N₂ m₁ k d m₀ k) {R : ℕ}
    (hpoly : ∀ x ∈ polySet m₀ j y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hX₀ : ∀ x ∈ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hbigA : 2 * (R + 3 * ((2 * (L / 2) + 1) * cellSide L m₀ m₁ j) +
        (5 * L + 1) * (L ^ k * L ^ (m₁ + s)) + 6 * (k + 1) * L ^ ((k + 1) + (m₁ + s)) + 1 +
        (5 * L + 2) * L ^ ((k + 1) + (m₁ + s)) + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 <
      NA * L ^ (m₁ + s) * L ^ (k + 1))
    (hbigB : 2 * (R + 3 * ((2 * (L / 2) + 1) * cellSide L m₀ m₁ j) +
        (5 * L + 1) * (L ^ k * L ^ (m₁ + s)) + 6 * (k + 1) * L ^ ((k + 1) + (m₁ + s)) + 1 +
        (5 * L + 2) * L ^ ((k + 1) + (m₁ + s)) + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 <
      NB * L ^ (m₁ + s) * L ^ (k + 1)) :
    GSCorr (F.GkC j y₀ X₀) (F'.GkC j (bmC y₀) (bmC '' X₀)) bmC
        {z | InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) z} ∧
      GSCorr (F.GjC j y₀ X₀) (F'.GjC j (bmC y₀) (bmC '' X₀)) bmC
        {z | InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) z} ∧
      ∀ (a : ℕ → ℝ) (ν : ℝ) (Rg : Set (CTorus d L N₁ m₁ (k + 1))),
        (∀ x ∈ (F.GkC j y₀ X₀).Ω 1, x ∈ Rg ∧ ∀ μ : Fin d,
          x + Pi.single μ 1 ∈ Rg ∧ x - Pi.single μ 1 ∈ Rg) →
        GSIso a ν (F.GkC j y₀ X₀) (F'.GkC j (bmC y₀) (bmC '' X₀)) bmC Rg := by
  classical
  have hjk : j ≤ k := hadm.2.1
  have hA : NA * L ^ (m₁ + s) * L ^ (k + 1) = N₁ * L ^ m₁ * L ^ (k + 1) := by rw [hcA]
  have hB : NB * L ^ (m₁ + s) * L ^ (k + 1) = N₂ * L ^ m₁ * L ^ (k + 1) := by rw [hcB]
  set P := L ^ ((k + 1) + (m₁ + s)) with hP
  set m' := m₁ + s with hm'
  set sh := (2 * (L / 2) + 1) * cellSide L m₀ m₁ j with hsh
  set sk := L ^ k * L ^ m' with hsk
  set R₁ := R + sh + sh with hR₁
  have hLp : 0 < L := by omega
  -- facts on the powers
  have hskP : sk ≤ P := by
    rw [hsk, hP, ← pow_add]; exact Nat.pow_le_pow_right hLp (by omega)
  have hPpow : ∀ n, n ≤ k + 1 → L ^ n * L ^ m' ≤ P := fun n hn => by
    rw [hP, ← pow_add]; exact Nat.pow_le_pow_right hLp (by omega)
  have hPpow2 : ∀ n, n ≤ k + 1 → L ^ (n + m') ≤ P := fun n hn => by
    rw [hP]; exact Nat.pow_le_pow_right hLp (by omega)
  have hLP : L ^ (k + 1) ≤ P := by
    rw [hP]; exact Nat.pow_le_pow_right hLp (by omega)
  have hmulP : ∀ c : ℕ, c * sk ≤ c * P := fun c => Nat.mul_le_mul_left _ hskP
  have h6 : ∀ n, n ≤ k + 1 → 6 * n * L ^ (n + m') ≤ 6 * (k + 1) * P := fun n hn =>
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hn) (hPpow2 n hn)
  have h5 : ∀ n, n ≤ k + 1 → (5 * L + 2) * (L ^ n * L ^ m') ≤ (5 * L + 2) * P := fun n hn =>
    Nat.mul_le_mul_left _ (hPpow n hn)
  -- the sets lie in the box
  have hhat := hatSet_inBox (m₀ := m₀) (j := j) (X := X₀) hX₀ (by omega)
  have hY : ∀ y ∈ kernelSet (NA := NA) m₀ s j y₀ X₀,
      InBox d R₁ ((NA * L ^ m') * L ^ (k + 1)) y := by
    intro y hy
    have hy' : (torusCast y : CTorus d L N₁ m₁ (k + 1)) ∈ polySet m₀ j y₀ X₀ ∪ hatSet m₀ j X₀ := hy
    refine (inBox_torusCast hA y).1 ?_
    rcases hy' with h | h
    · exact inBox_mono (by omega) (hpoly _ h)
    · exact hhat _ h
  have hYh : ∀ y ∈ hatFine (NA := NA) m₀ s j X₀, InBox d R₁ ((NA * L ^ m') * L ^ (k + 1)) y := by
    intro y hy
    refine (inBox_torusCast hA y).1 ?_
    exact hhat _ hy
  have hy₀ : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y₀ := hX₀ y₀ hadm.2.2.2.2
  have hnh : 2 * (R + 2 * sh) + sh + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by
    have := hbigA; rw [hA] at this; omega
  have hYY := kernelSet_boxMap (NB := NB) (NA := NA) (s := s) hcA hcB hN hN' hjk hL hy₀ hX₀ hnh
  have hmA : 2 * (R₁ + (5 * L + 2) * sk) < NA * L ^ m' * L ^ (k + 1) := by
    have h1 := hmulP (5 * L + 2)
    omega
  have hmB : 2 * (R₁ + (5 * L + 2) * sk) < NB * L ^ m' * L ^ (k + 1) := by
    have h1 := hmulP (5 * L + 2)
    omega
  have hPA : ∀ x ∈ castNbhd (N₁' := NA) (m₁' := m')
      (kernelSet (NA := NA) m₀ s j y₀ X₀), InBox d (R₁ + (5 * L + 1) * sk)
        ((NA * L ^ m') * L ^ (k + 1)) x := by
    rintro x ⟨y', hy', hd⟩
    exact inBox_of_cubeNear (k := k + 1) (n := k) (by omega) (hY y' hy') hmA hd
  have hPPB := castNbhd_image (NB := NB) hY hYY hmA hmB
  have hGkA := LC.hGk j y₀ X₀ hadm
  have hGkB := LC.hGk' j (bmC y₀) (bmC '' X₀) hadmB
  have hGjA := LC.hGj j y₀ X₀ hadm
  have hGjB := LC.hGj' j (bmC y₀) (bmC '' X₀) hadmB
  have hR₁le : R ≤ R₁ := by omega
  -- the margins
  have mk1 : ∀ n, n ≤ k → 2 * (R₁ + (5 * L + 1) * sk + 1 + 6 * k * L ^ (k + m') +
      (5 * L + 2) * (L ^ n * L ^ m')) < NA * L ^ m' * L ^ (k + 1) := fun n hn => by
    have := h6 k (by omega); have := h5 n (by omega); have := hmulP (5 * L + 1); omega
  have mk2 : ∀ n, n ≤ k → 2 * (R₁ + (5 * L + 1) * sk + 1 + 6 * k * L ^ (k + m') +
      (5 * L + 2) * (L ^ n * L ^ m')) < NB * L ^ m' * L ^ (k + 1) := fun n hn => by
    have := h6 k (by omega); have := h5 n (by omega); have := hmulP (5 * L + 1); omega
  have mj1 : ∀ n, n ≤ j → 2 * (R₁ + 1 + 6 * j * L ^ (j + m') +
      (5 * L + 2) * (L ^ n * L ^ m')) < NA * L ^ m' * L ^ (k + 1) := fun n hn => by
    have := h6 j (by omega); have := h5 n (by omega); omega
  have mj2 : ∀ n, n ≤ j → 2 * (R₁ + 1 + 6 * j * L ^ (j + m') +
      (5 * L + 2) * (L ^ n * L ^ m')) < NB * L ^ m' * L ^ (k + 1) := fun n hn => by
    have := h6 j (by omega); have := h5 n (by omega); omega
  have hnk1 : 2 * (R₁ + (5 * L + 1) * sk + 6 * k * L ^ (k + m') + 1) + 3 * L ^ (k + 1) + 5 <
      (N₁ * L ^ m₁) * L ^ (k + 1) := by
    have := h6 k (by omega); have := hmulP (5 * L + 1); rw [← hA]; omega
  have hnk2 : 2 * (R₁ + (5 * L + 1) * sk + 6 * k * L ^ (k + m') + 1) + 3 * L ^ (k + 1) + 5 <
      (N₂ * L ^ m₁) * L ^ (k + 1) := by
    have := h6 k (by omega); have := hmulP (5 * L + 1); rw [← hB]; omega
  have hnk1' : 2 * (R₁ + (5 * L + 1) * sk + 6 * k * L ^ (k + m') + 1 + L ^ (k + 1)) +
      3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1) := by
    have := h6 k (by omega); have := hmulP (5 * L + 1); rw [← hA]; omega
  have hnk2' : 2 * (R₁ + (5 * L + 1) * sk + 6 * k * L ^ (k + m') + 1 + L ^ (k + 1)) +
      3 * L ^ (k + 1) + 5 < (N₂ * L ^ m₁) * L ^ (k + 1) := by
    have := h6 k (by omega); have := hmulP (5 * L + 1); rw [← hB]; omega
  have hnj1 : 2 * (R₁ + 6 * j * L ^ (j + m') + 1) + 3 * L ^ (k + 1) + 5 <
      (N₁ * L ^ m₁) * L ^ (k + 1) := by
    have := h6 j (by omega); rw [← hA]; omega
  have hnj2 : 2 * (R₁ + 6 * j * L ^ (j + m') + 1) + 3 * L ^ (k + 1) + 5 <
      (N₂ * L ^ m₁) * L ^ (k + 1) := by
    have := h6 j (by omega); rw [← hB]; omega
  have hnj1' : 2 * (R₁ + 6 * j * L ^ (j + m') + 1 + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 <
      (N₁ * L ^ m₁) * L ^ (k + 1) := by
    have := h6 j (by omega); rw [← hA]; omega
  have hnj2' : 2 * (R₁ + 6 * j * L ^ (j + m') + 1 + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 <
      (N₂ * L ^ m₁) * L ^ (k + 1) := by
    have := h6 j (by omega); rw [← hB]; omega
  have hHYY := hatFine_boxMap (NB := NB) (NA := NA) (s := s) hcA hcB hN hN' hjk hX₀ hnh
  refine ⟨?_, ?_, ?_⟩
  · rw [hGkA, hGkB]
    refine (gsCorr_castLocalB hcA hcB (Nat.le_succ k) (by omega) hPA hPPB mk1 mk2 hnk1' hnk2').mono ?_
    intro z hz
    exact inBox_mono (by omega) hz
  · rw [hGjA, hGjB, hHYY]
    refine (gsCorr_castLocalB hcA hcB (Nat.le_succ_of_le hjk) (by omega) hYh rfl mj1 mj2 hnj1' hnj2').mono ?_
    intro z hz
    exact inBox_mono (by omega) hz
  · intro a ν Rg hR
    rw [hGkA, hGkB]
    exact gsIso_castLocalB_on hcA hcB (Nat.le_succ k) (by omega) hPA hPPB mk1 mk2 hnk1 hnk2 a ν Rg
      (by rw [← hGkA]; exact hR)


/-- **The margin of a pair**: the union of the `L^{k+1}`-cells of the sites within `L^{k+1}` of the
data sites of `Gk`. -/
def castZ (Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁) : Set (CTorus d L N₁ m₁ (k + 1)) :=
  {y | ∃ x ∈ nearSet (L ^ (k + 1)) (↑(dataSites Gk) : Set (CTorus d L N₁ m₁ (k + 1))),
    SameCell (L ^ (k + 1)) y x}

/-- **The `6 M`-neighbourhood of the margin lies in the region**, from the neighbourhood of radius
`8 M` of the data sites. -/
theorem castZ_margin {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁} (hL : 2 ≤ L)
    {Xr : Set (CTorus d L N₁ m₁ (k + 1))}
    (hreg : ∀ p ∈ dataSites Gk, ∀ v : Fin d → ℤ,
      (∀ μ, |v μ| ≤ ((8 * L ^ ((k + 1) + m₁) : ℕ) : ℤ)) →
      p + (intTorus v : CTorus d L N₁ m₁ (k + 1)) ∈ Xr)
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ castZ Gk) (w : Fin d → ℤ)
    (hw : ∀ μ, |(w μ : ℝ)| < 6 * (L : ℝ) ^ ((k + 1) + m₁)) :
    x + (intTorus w : CTorus d L N₁ m₁ (k + 1)) ∈ Xr := by
  obtain ⟨x', ⟨p, hp, hd⟩, hsc⟩ := hx
  have hLp : 0 < L ^ (k + 1) := pow_pos (by omega) _
  have h1 := supDist_sameCell hLp hsc
  have h2 : supDist x p ≤ 2 * L ^ (k + 1) := (supDist_triangle x x' p).trans (by omega)
  obtain ⟨u, hxu, hu⟩ := exists_int_of_supDist h2
  have e : x + (intTorus w : CTorus d L N₁ m₁ (k + 1)) =
      p + (intTorus (u + w) : CTorus d L N₁ m₁ (k + 1)) := by
    rw [hxu]; funext μ; simp only [Pi.add_apply, intTorus_apply]; push_cast; ring
  rw [e]
  refine hreg p (Finset.mem_coe.1 hp) _ fun μ => ?_
  set M := L ^ ((k + 1) + m₁) with hM
  have hLM : L ^ (k + 1) ≤ M := by
    rw [hM]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hwM : |w μ| ≤ 6 * (M : ℤ) := by
    have := hw μ
    have h3 : |w μ| < (6 * M : ℕ) := by
      have : ((|w μ| : ℤ) : ℝ) < ((6 * M : ℕ) : ℝ) := by
        rw [Int.cast_abs]; push_cast; exact_mod_cast this
      exact_mod_cast this
    push_cast at h3; linarith
  have hu' := hu μ
  have h8 : |(u + w) μ| ≤ |u μ| + |w μ| := by simpa using abs_add_le (u μ) (w μ)
  have hLM' : ((L ^ (k + 1) : ℕ) : ℤ) ≤ M := by exact_mod_cast hLM
  have e1 : ((2 * L ^ (k + 1) : ℕ) : ℤ) = 2 * ((L ^ (k + 1) : ℕ) : ℤ) := by push_cast; ring
  have e2 : ((8 * M : ℕ) : ℤ) = 8 * (M : ℤ) := by push_cast; ring
  rw [e1] at hu'
  rw [e2]
  generalize ((L ^ (k + 1) : ℕ) : ℤ) = a at hu' hLM'
  generalize (M : ℤ) = b at hwM hLM' ⊢
  linarith

/-- **`HGeom` for the canonical covers of the settings.** -/
theorem hgeom_of_cast {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {C' : StepClass d L N₂ m₁ k N ϱ} {F : CanonCover d L N₁ m₁ k ϱ ϱ₁}
    {F' : CanonCover d L N₂ m₁ k ϱ ϱ₁'} {hcA : NA * L ^ (m₁ + s) = N₁ * L ^ m₁}
    {hcB : NB * L ^ (m₁ + s) = N₂ * L ^ m₁} (LC : CanonCoverCast C.m₀ s hcA hcB F F')
    {i₀ i₁ : Fin N} {R : ℕ} (hL : 3 ≤ L) (hk1 : 1 ≤ k)
    (hN : L ^ C.m₀ ∣ N₁) (hN' : L ^ C.m₀ ∣ N₂)
    (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
    (hXLsub : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      polySet C.m₀ j y₀ X₀ ⊆ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hreg : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      ∀ p ∈ dataSites (F.GkC j y₀ X₀), ∀ v : Fin d → ℤ,
        (∀ μ, |v μ| ≤ ((8 * L ^ ((k + 1) + m₁) : ℕ) : ℤ)) →
        p + (intTorus v : CTorus d L N₁ m₁ (k + 1)) ∈
          (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hbigA : 2 * (R + 3 * ((2 * (L / 2) + 1) * cellSide L C.m₀ m₁ k) +
        (5 * L + 1) * (L ^ k * L ^ (m₁ + s)) + 6 * (k + 1) * L ^ ((k + 1) + (m₁ + s)) + 1 +
        (5 * L + 2) * L ^ ((k + 1) + (m₁ + s)) + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 <
      NA * L ^ (m₁ + s) * L ^ (k + 1))
    (hbigB : 2 * (R + 3 * ((2 * (L / 2) + 1) * cellSide L C.m₀ m₁ k) +
        (5 * L + 1) * (L ^ k * L ^ (m₁ + s)) + 6 * (k + 1) * L ^ ((k + 1) + (m₁ + s)) + 1 +
        (5 * L + 2) * L ^ ((k + 1) + (m₁ + s)) + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 <
      NB * L ^ (m₁ + s) * L ^ (k + 1))
    (hcell : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      CellTermsAgree C C' i₀ i₁ j y₀ X₀ (castZ (F.GkC j y₀ X₀))) :
    HGeom S C C' F F' i₀ i₁ R := by
  classical
  have hL2 : 2 ≤ L := by omega
  have hA : NA * L ^ (m₁ + s) * L ^ (k + 1) = N₁ * L ^ m₁ * L ^ (k + 1) := by rw [hcA]
  have hB : NB * L ^ (m₁ + s) * L ^ (k + 1) = N₂ * L ^ m₁ * L ^ (k + 1) := by rw [hcB]
  intro j y₀ X₀ hadm hbox
  have hjk : j ≤ k := hadm.2.1
  have hpoly : ∀ x ∈ polySet C.m₀ j y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun x hx => hbox x (hXLsub j y₀ X₀ hadm hx)
  have hX₀ : ∀ x ∈ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun x hx => hpoly x (Or.inl hx)
  have hshj : (2 * (L / 2) + 1) * cellSide L C.m₀ m₁ j ≤
      (2 * (L / 2) + 1) * cellSide L C.m₀ m₁ k :=
    Nat.mul_le_mul_left _ (cellSide_le_of_le hjk)
  have hLaj : L * cellSide L C.m₀ m₁ j ≤ (2 * (L / 2) + 1) * cellSide L C.m₀ m₁ j :=
    Nat.mul_le_mul_right _ (by omega)
  have hbx : ∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    rintro x (rfl | hx)
    · exact hX₀ _ hadm.2.2.2.2
    · exact hX₀ x hx
  have hadmB := admPairs_image (N₁' := N₂) hN hN' (R := R) (by rw [← hA] at *; omega)
    (by rw [← hB] at *; omega) hadm hbx
  obtain ⟨hc1, hc2, hiso⟩ := pair_gs_corr (NB := NB) (NA := NA) LC hL2 hk1 hN hN' hadm hadmB hpoly
    hX₀ (by omega) (by omega)
  have hGkA := LC.hGk j y₀ X₀ hadm
  have hDp : ∀ x ∈ polySet C.m₀ j y₀ X₀, x ∈ dataSites (F.GkC j y₀ X₀) := by
    intro x hx
    have hxf : (torusCast x : CTorus d L NA (m₁ + s) (k + 1)) ∈
        kernelSet (NA := NA) C.m₀ s j y₀ X₀ := by
      show (torusCast (torusCast x : CTorus d L NA (m₁ + s) (k + 1)) :
        CTorus d L N₁ m₁ (k + 1)) ∈ polySet C.m₀ j y₀ X₀ ∪ hatSet C.m₀ j X₀
      rw [torusCast_torusCast hA.symm]
      exact Or.inl hx
    have := mem_dataSites_kernel (N₀ := N₁ * L ^ m₁) hcA hk1 (hs := LC.hs₁) hxf
    rw [torusCast_torusCast hA.symm] at this
    rw [hGkA]
    exact this
  have hy₀D : y₀ ∈ dataSites (F.GkC j y₀ X₀) := hDp y₀ (Or.inl hadm.2.2.2.2)
  have hZ0 : ∀ p ∈ dataSites (F.GkC j y₀ X₀), p ∈ castZ (F.GkC j y₀ X₀) := fun p hp =>
    ⟨p, ⟨p, Finset.mem_coe.2 hp, by simp [supDist_self]⟩, SameCell.refl _ _⟩
  have h0 : (intTorus (0 : Fin d → ℤ) : CTorus d L N₁ m₁ (k + 1)) = 0 := by
    funext μ; simp [intTorus_apply]
  have hZX : castZ (F.GkC j y₀ X₀) ⊆ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))) :=
    fun x hx => by
      have := castZ_margin hL2 (hreg j y₀ X₀ hadm) hx 0 (fun μ => by simp; positivity)
      rwa [h0, add_zero] at this
  have hnb : ∀ μ : Fin d, y₀ + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1)) ∈
      castZ (F.GkC j y₀ X₀) := fun μ => by
    refine ⟨_, ⟨y₀, Finset.mem_coe.2 hy₀D, (supDist_nsmul_single _ _ μ).trans ?_⟩,
      SameCell.refl _ _⟩
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hblk : ∀ {ϱ' : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ') {n : ℕ}, n ≤ k + 1 →
      ∀ {z y : CTorus d L N₁ m₁ (k + 1)}, z ∈ castZ (F.GkC j y₀ X₀) → y ∈ G.blk n z →
        y ∈ castZ (F.GkC j y₀ X₀) := fun {ϱ'} G {n} hn {z y} hz hy =>
    blk_subset_canonZ (Pt := (↑(dataSites (F.GkC j y₀ X₀)) : Set (CTorus d L N₁ m₁ (k + 1))))
      (r := L ^ (k + 1)) G hn hz hy
  refine ⟨fun μ => hbox _ (hZX (hnb μ)), fun z hz => hpoly z (Or.inr hz),
    castZ (F.GkC j y₀ X₀), fun x hx => hZ0 x (hDp x (Or.inl hx)), hnb, hZX,
    LocalCover.blockMargin_core SpG S.hG' _ (fun x hx w hw => castZ_margin hL2 (hreg j y₀ X₀ hadm) hx w hw),
    hc1.mono (fun z hz => hbox z (hZX hz)), hc2.mono (fun z hz => hbox z (hZX hz)),
    hiso _ _ _ ?_, ?_, ?_, hcell j y₀ X₀ hadm hbox⟩
  · intro x hx
    refine ⟨hZ0 x ((mem_dataSites _).2 (Or.inl hx)), fun μ => ⟨hZ0 _ ?_, hZ0 _ ?_⟩⟩
    · by_cases h : x + Pi.single μ 1 ∈ (F.GkC j y₀ X₀).Ω 1
      · exact (mem_dataSites _).2 (Or.inl h)
      · exact (mem_dataSites _).2 (Or.inr (mem_collar_of_adj _ hx h ⟨μ, Or.inl rfl⟩))
    · by_cases h : x - Pi.single μ 1 ∈ (F.GkC j y₀ X₀).Ω 1
      · exact (mem_dataSites _).2 (Or.inl h)
      · exact (mem_dataSites _).2
          (Or.inr (mem_collar_of_adj _ hx h ⟨μ, Or.inr (sub_add_cancel _ _).symm⟩))
  · intro z hz _
    exact ⟨fun y hy => hblk _ (layerIndex_le_top _ _) hz hy,
      fun y hy => hblk _ (layerIndex_le_top _ _) hz hy,
      fun y hy => hblk _ (layerIndex_le_top _ _) hz hy⟩
  · intro z hz _
    exact ⟨fun y hy => hblk _ (layerIndex_le_top _ _) hz hy,
      fun y hy => hblk _ (layerIndex_le_top _ _) hz hy⟩

end CastGeom

end Balaban.Inhabited
