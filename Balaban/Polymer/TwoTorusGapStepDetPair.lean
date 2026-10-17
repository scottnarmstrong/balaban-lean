/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepDet
public import Balaban.Polymer.TwoTorusGapObsRecentreDet

/-!
# The determinant block sum at the cells of a polymer: the pair theorem (item 24, blocker 7)

`sum_blockU_detActivityBg_cellSites`: the analogue of `evDec_cellSites_blockEnergy` for the sum over
the unit points of a block of the determinant activities at the cubes of the cells of `X`.  The
recentring vector is `exists_recentring_int` for the π'-cube of the root and the sites of the cubes;
the root, the cubes and the margins of `sum_blockU_detActivityBg_recentred` are derived.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.Localization.DetUnitIncidence Balaban.Localization.DecEquiv

section Pair

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱm ϱm' : ℝ} {m₀ : ℕ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl

/-- **The coarse root under the recentring map.**  Let `zv` be a recentring vector with the integer sums
of the centred coordinates of the root site of `zc` at most `r0` and the root site itself within `q`
of the origin.  Then the translated coarse root lies in a coarse box, and the translate by `tB` of the
`bc`-image of `zc` is the `bc`-image of the translate of `zc` by `tA`. -/
theorem rootAct_recentred {rc₀ rc₁ r0 q : ℕ} (zc : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (zv : Fin d → ℤ)
    (hnR : 2 * r0 + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hint : ∀ μ, |(rootSite zc μ).valMinAbs + zv μ| ≤ r0)
    (hxq : ∀ μ, |(rootSite zc μ).valMinAbs| ≤ q)
    (hrc0 : r0 < L ^ (k + 1) * rc₀)
    (hc0 : 2 * rc₀ + 1 < N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
    (hrc1 : q < L ^ (k + 1) * rc₁)
    (hc1 : 2 * rc₁ + 1 < N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
    (hs : 2 * (L ^ (k + 1) * rc₁) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1)) :
    InBox d rc₀ (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
        (rootAct (Equiv.addRight (fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
          zc) ∧
      rootAct (Equiv.addRight (fun μ => ((zv μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))
          (bc zc) =
        bc (rootAct (Equiv.addRight (fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
          zc) := by
  have hz0 : InBox d rc₁ (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) zc := by
    have h := inBox_jBlock (j := k + 1) (k := k + 1) (le_refl _) hrc1 hc1 (rootSite zc)
      (fun μ => hxq μ)
    have e : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (rootSite zc) = zc := blockIndex_rootSite zc
    rwa [e] at h
  have hrs := rootSite_boxMap (N₁ := N₁) (N₁' := N₁') (K := k + 1) (r := L ^ (k + 1) * rc₁) zc hz0
    le_rfl hs
  have hin0 : InBox d r0 ((N₁ * L ^ m₁) * L ^ (k + 1))
      (rootSite zc + fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) :=
    inBox_add_intCast hnR _ zv hint
  refine ⟨?_, ?_⟩
  · exact inBox_jBlock (j := k + 1) (k := k + 1) (le_refl _) hrc0 hc0 _ hin0
  · have hbmadd : bm (rootSite zc +
        fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) =
        bm (rootSite zc) +
          fun μ => ((zv μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))) :=
      boxMap_add_intCast hnR _ zv hint
    show blockIndex (rootSite (bc zc) +
        fun μ => ((zv μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) =
      bc (blockIndex (rootSite zc +
        fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
    rw [hrs, ← hbmadd]
    exact blockIndex_boxMap hrc0 hc0 _ hin0

/-- **The geometry of the recentred root.**  Let `zv` be a recentring vector (a multiple of the cell
side) taking the π'-cube of the root cell of `zc` into the centred box of radius `r0 = Ds + (Ds+1)/4`
as integer sums, the root site lie within `q` of the origin, `Ds + 1 ≥ a_K`, `25 Ds + 25` and
`2 q + 2 r0` below both torus sides and `20 (r0 + 2 L^(k+1)) + 20` below both torus sides.  Then
(with `r = r0 + 2 L^(k+1)`) the translated coarse root lies in a coarse box of radius `rc` with
`L^(k+1) rc + L^(k+1) ≤ r`, the recentred coarse roots correspond, the translated π'-cube lies in the
box of radius `r`, and the margins of `sum_blockU_detActivityBg_twoTorus` hold on both tori. -/
theorem det_root_recentred (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    {Ds q : ℕ} (zc : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (zv : Fin d → ℤ)
    (hDsa : cellSide L m₀ m₁ (k + 1) ≤ Ds + 1)
    (hap : 4 * L ^ (k + 1) ≤ cellSide L m₀ m₁ (k + 1))
    (hn25 : 25 * Ds + 25 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hqn : 2 * q + 2 * (Ds + (Ds + 1) / 4) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hslack : 20 * (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hslack' : 20 * (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hxq : ∀ μ, |(rootSite zc μ).valMinAbs| ≤ q)
    (hint : ∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * cellSide L m₀ m₁ (k + 1)), ∀ μ,
      |(x μ).valMinAbs + zv μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) :
    ∃ rc : ℕ, InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
        (rootAct (Equiv.addRight (fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
          zc) ∧
      L ^ (k + 1) * rc + L ^ (k + 1) ≤ Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1) ∧
      rootAct (Equiv.addRight (fun μ => ((zv μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))
          (bc zc) =
        bc (rootAct (Equiv.addRight (fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
          zc) ∧
      (∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * cellSide L m₀ m₁ (k + 1)),
        InBox d (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
          (x + fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) ∧
      (4 * (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 <
          (N₁ * L ^ m₁) * L ^ (k + 1) ∧
        4 * (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 <
          (N₁' * L ^ m₁) * L ^ (k + 1) ∧
        2 * ((Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) +
          L ^ (k + 1 + m₁)) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1) ∧
        2 * ((Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) +
          L ^ (k + 1 + m₁)) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1) ∧
        2 * ((Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + 2 * (L * cellSide L m₀ m₁ (k + 1))) +
          L * cellSide L m₀ m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1) ∧
        2 * ((Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + 2 * (L * cellSide L m₀ m₁ (k + 1))) +
          L * cellSide L m₀ m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1)) := by
  classical
  have hLpos : 0 < L := by omega
  have hpK : 0 < L ^ (k + 1) := pow_pos hLpos _
  have hapos : 0 < cellSide L m₀ m₁ (k + 1) := cellSide_pos (L := L) m₀ m₁ (k + 1)
  set r0 : ℕ := Ds + (Ds + 1) / 4 with hr0
  set r : ℕ := r0 + 2 * L ^ (k + 1) with hrdef
  have hnR : 2 * r0 + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hnc : N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)) = N₁ * L ^ m₁ := by
    rw [Nat.sub_self, pow_zero, mul_one]
  have hcoarse : ∀ ρ : ℕ, 2 * ρ + 3 * L ^ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1) →
      2 * (ρ / L ^ (k + 1) + 1) + 1 < N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)) := by
    intro ρ hρ
    rw [hnc]
    by_contra h
    push Not at h
    have h1 := Nat.mul_le_mul_right (L ^ (k + 1)) h
    have hu := Nat.div_mul_le_self ρ (L ^ (k + 1))
    have e : (2 * (ρ / L ^ (k + 1) + 1) + 1) * L ^ (k + 1) =
        2 * (ρ / L ^ (k + 1) * L ^ (k + 1)) + 3 * L ^ (k + 1) := by ring
    rw [e] at h1
    omega
  have hxX : rootSite zc ∈ box (rootCube (m₀ := m₀) zc).1 (L * cellSide L m₀ m₁ (k + 1)) :=
    box_mono _ (by nlinarith) (rootSite_mem_box_rootCube (m₀ := m₀) zc)
  have hint0 : ∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * cellSide L m₀ m₁ (k + 1)),
      InBox d r0 ((N₁ * L ^ m₁) * L ^ (k + 1))
        (x + fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) :=
    fun x hx => inBox_add_intCast hnR x zv (hint x hx)
  have hintr : ∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * cellSide L m₀ m₁ (k + 1)),
      InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1))
        (x + fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) :=
    fun x hx => inBox_mono (by omega) (hint0 x hx)
  have hrc0 : r0 < L ^ (k + 1) * (r0 / L ^ (k + 1) + 1) := Nat.lt_mul_div_succ r0 hpK
  have hc0 := hcoarse r0 (by omega)
  have hrc1 : q < L ^ (k + 1) * (q / L ^ (k + 1) + 1) := Nat.lt_mul_div_succ q hpK
  have hc1 := hcoarse q (by omega)
  have hqq := Nat.mul_div_le q (L ^ (k + 1))
  obtain ⟨hzc, hzz⟩ := rootAct_recentred (N₁' := N₁') zc zv hnR
    (fun μ => hint _ hxX μ) (fun μ => hxq μ) hrc0 hc0 hrc1 hc1 (by rw [mul_add]; omega)
  have hw0 := width_le_of_box_subset_inBox (n := (N₁ * L ^ m₁) * L ^ (k + 1)) hd
    (b := (rootCube (m₀ := m₀) zc).1 + fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))
    (s := L * cellSide L m₀ m₁ (k + 1)) (r := r)
    (t := min (L * cellSide L m₀ m₁ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)))
    (min_le_left _ _) (min_le_right _ _)
    (fun x hx => by
      obtain ⟨y, rfl⟩ : ∃ y, x = y + (fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) :=
        ⟨x - fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))), by abel⟩
      exact hintr y ((mem_box_add_iff _ _ y _).1 hx))
  have hw : L * cellSide L m₀ m₁ (k + 1) ≤ 2 * r + 1 := by
    rcases min_choice (L * cellSide L m₀ m₁ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) with h | h
    · rw [h] at hw0; exact hw0
    · rw [h] at hw0; omega
  obtain ⟨-, hn1, hnS, hnH⟩ := gapMargins_of_width (K := k + 1) (R := r) hL hm₀ hm₁ hw
    (by omega : 20 * r + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
  obtain ⟨-, hn1', hnS', hnH'⟩ := gapMargins_of_width (K := k + 1) (R := r) hL hm₀ hm₁ hw
    (by omega : 20 * r + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
  have hu := Nat.mul_div_le r0 (L ^ (k + 1))
  refine ⟨r0 / L ^ (k + 1) + 1, hzc, ?_, hzz, hintr, hn1, hn1', hnS, hnS', hnH, hnH'⟩
  rw [mul_add]
  omega

/-- **The recentred cubes of a set of cells.**  If the box map carries the sites of `Y` onto the sites
of `Y'`, and the translations by `tA`, `tB` commute with it on the sites of `Y` and keep them in the
box of radius `r`, the translate of `Y'` by `tB` is the `cubeMap`-image of the translate of `Y` by
`tA`. -/
theorem cubeAct_recentred_cells {r : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (Y' : Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hbm : bm '' sitesOf Y = sitesOf Y')
    (hadd : ∀ y ∈ sitesOf Y, bm (y + tA) = bm y + tB)
    (hbd : ∀ y ∈ sitesOf Y, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA))
    (hr : 2 * r + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1)) :
    cubeAct (Equiv.addRight tB) Y' =
      (cubeAct (Equiv.addRight tA) Y).image (cubeMap hN hN' le_rfl) := by
  have hσA := genSymm_mem_pavingSymGroup
    (GenSymm.translate (n := k + 1) (m₀ := m₀) tA htA)
  have hσB := genSymm_mem_pavingSymGroup
    (GenSymm.translate (n := k + 1) (m₀ := m₀) tB htB)
  refine eq_of_sitesOf_eq hN' ?_
  rw [sitesOf_cubeAct hN' hσB, sitesOf_image_cubeMap hN hN' le_rfl (r := r) hr _ ?_,
    sitesOf_cubeAct hN hσA, ← hbm, Set.image_image, Set.image_image]
  · exact Set.image_congr (fun y hy => (hadd y hy).symm)
  · rw [sitesOf_cubeAct hN hσA]
    rintro _ ⟨y, hy, rfl⟩
    exact hbd y hy

/-- **The determinant block sum at the cells of a polymer, with the spread bound `Dc` as a
parameter** (`Dc ≤ (Kn - 26) / 25`): the core of `sum_blockU_detActivityBg_cellSites`. -/
theorem sum_blockU_detActivityBg_cellSites_gen (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'}
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) Hm 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) Hm' 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L 1) νS (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L 1) νS (k + 1) 1 eps D')
    {Kn Kn' Ds q : ℕ} [NeZero Kn] [NeZero Kn'] (hK : 26 ≤ Kn) (hKK' : Kn ≤ Kn')
    (hm : (N₁ * L ^ m₁) * L ^ (k + 1) = aK * Kn) (hm' : (N₁' * L ^ m₁) * L ^ (k + 1) = aK * Kn')
    {Dc : ℕ} (hDc : Dc ≤ (Kn - 26) / 25) (hDsdef : Ds = aK * (Dc + 1) - 1)
    {X : Set (Fin d → ℤ)} (hXq : ∀ c ∈ X, ∀ μ, (c μ).natAbs ≤ Kn / 4)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (Y' : Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hY : sitesOf Y = {x | (fun μ => (((((x μ).val / aK : ℕ)) : ZMod Kn)).valMinAbs) ∈ X})
    (hY' : sitesOf Y' = {x' | (fun μ => (((((x' μ).val / aK : ℕ)) : ZMod Kn')).valMinAbs) ∈ X})
    (zc : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hsp : ∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK),
      ∀ y ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK) ∪ sitesOf Y, ∀ μ,
      |(x μ - y μ).valMinAbs| ≤ Ds)
    (hq : ∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK) ∪ sitesOf Y, ∀ μ,
      |(x μ).valMinAbs| ≤ q)
    (hqn : 2 * q + 2 * (Ds + (Ds + 1) / 4) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hslack : 20 * (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hslack' : 20 * (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hraw : ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK) ∪ sitesOf Y, ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      RawBoxAgree {w | InBox d (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1) + 3 * L ^ (k + 1))
          ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
          (rawOf D))
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))
          (rawOf D'))) :
    ∑ y' ∈ (Finset.univ.filter fun u : unitPts (GB) =>
        unitBlock1 (u : UnitTorus d L N₁' m₁ k) = bc zc),
        detActivityBg m₀ (compWeight L 1) 1 νS (rho4 d L N BG κ) D' y' Y' =
      ∑ y ∈ (Finset.univ.filter fun u : unitPts (GA) =>
        unitBlock1 (u : UnitTorus d L N₁ m₁ k) = zc),
        detActivityBg m₀ (compWeight L 1) 1 νS (rho4 d L N BG κ) D y Y := by
  classical
  have : NeZero aK := ⟨(cellSide_pos (L := L) m₀ m₁ (k + 1)).ne'⟩
  have hapos : 0 < aK := cellSide_pos (L := L) m₀ m₁ (k + 1)
  have hLpos : 0 < L := by omega
  have hpK : 0 < L ^ (k + 1) := pow_pos hLpos _
  have hap : 4 * L ^ (k + 1) ≤ aK := by
    have h4 : 4 ≤ L ^ (m₀ + m₁) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ L ^ 2 := Nat.pow_le_pow_left hL 2
        _ ≤ L ^ (m₀ + m₁) := Nat.pow_le_pow_right hLpos (by omega)
    have : aK = L ^ (k + 1) * L ^ (m₀ + m₁) := by
      unfold cellSide; rw [← pow_add]; congr 1; omega
    rw [this]
    nlinarith
  have hbox : ∃ b, box b (L * aK) ⊆ box (rootCube (m₀ := m₀) zc).1 (L * aK) := ⟨_, subset_rfl⟩
  have hDs1 : Ds + 1 ≤ aK * (Dc + 1) := by
    have : 1 ≤ aK * (Dc + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hDsa : aK ≤ Ds + 1 := by
    rw [hDsdef]
    have := Nat.le_mul_of_pos_right aK (show 0 < Dc + 1 by omega)
    omega
  obtain ⟨hn25, hn25', -⟩ := compact_site_margins (K := Kn) (K' := Kn') (cs := aK)
    (Dc := Dc) (Ds := Ds) (q := 0) hK hKK' hapos hDc hDs1 (Nat.zero_le _)
  rw [← hm] at hn25
  rw [← hm'] at hn25'
  obtain ⟨zv, hz, hint⟩ := exists_recentring_int (n := (N₁ * L ^ m₁) * L ^ (k + 1))
    (a := aK) (L := L) (D := Ds) (q := q) hd hapos hL (cellSide_dvd hN le_rfl) hbox
    hsp hn25 hq hqn
  have hxX : rootSite zc ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK) :=
    box_mono _ (by nlinarith) (rootSite_mem_box_rootCube (m₀ := m₀) zc)
  obtain ⟨rc, hzc, hrc, hzz, hroot, hn1, hn1', hnS, hnS', hnH, hnH'⟩ :=
    det_root_recentred (N₁' := N₁') hd hL hm₀ hm₁ zc zv hDsa hap hn25 hqn hslack hslack'
      (fun μ => hq _ (Or.inl hxX) μ) (fun x hx μ => hint x (Or.inl hx) μ)
  have hnR : 2 * (Ds + (Ds + 1) / 4) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hbd : ∀ y ∈ sitesOf Y, InBox d (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1))
      ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) :=
    fun y hy => inBox_mono (by omega) (inBox_add_intCast hnR y zv (hint y (Or.inr hy)))
  have hbm : boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1)) ''
      sitesOf Y = sitesOf Y' := by
    rw [hY, hY']
    exact boxMap_image_cellSites hm hm' hK hKK' X hXq
  have hYc := cubeAct_recentred_cells hN hN' _ _ (fun μ => dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ))
    (fun μ => dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)) Y Y' hbm
    (fun y hy => boxMap_add_intCast hnR y zv (hint y (Or.inr hy))) hbd (by omega)
  exact sum_blockU_detActivityBg_recentred hN2 hk νS β p₁ δ hN hN' hC hC' hδc hcap hsm hmar hαK
    hconn hconn' hD hD' _ _ (fun μ => dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ))
    (fun μ => dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)) zc (bc zc) hzz hzc hrc
    (fun x hx => hroot x (box_mono _ (by nlinarith) hx)) Y Y' hYc hbd hn1 hn1' hnS hnS' hnH hnH'
    (hraw zv hz hint)

/-- **The determinant block sum at the cells of a polymer.**  Let `X` be a set of cells of the
quarter box of the torus with `Kc` cells per side (`26 ≤ Kc ≤ Kc'`) of cyclic spread at most
`(Kc - 26) / 25`, `Y`, `Y'` the cubes of its cells on the two tori, and `zc` a coarse root such that
the π'-cube of its root cell and the sites of `Y` have spread `Ds` (`hsp`) and lie within `q` of the
origin with `2 q + 2 (Ds + (Ds + 1) / 4) < n` (`hq`, `hqn`), with the slack `hslack` (`20 r + 20 < n`
for `r = Ds + (Ds + 1) / 4 + 2 L^(k+1)`).  If the raw data correspond under the recentred map for
every recentring vector (`hraw`), the sum over the unit points of the block `bc zc` of the second
torus of the determinant activities at `Y'` equals the sum over the block `zc` of the first torus at
`Y`. -/
theorem sum_blockU_detActivityBg_cellSites (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'}
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) Hm 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) Hm' 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L 1) νS (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L 1) νS (k + 1) 1 eps D')
    {Kn Kn' Ds q : ℕ} [NeZero Kn] [NeZero Kn'] (hK : 26 ≤ Kn) (hKK' : Kn ≤ Kn')
    (hm : (N₁ * L ^ m₁) * L ^ (k + 1) = aK * Kn) (hm' : (N₁' * L ^ m₁) * L ^ (k + 1) = aK * Kn')
    (hDsdef : Ds = aK * ((Kn - 26) / 25 + 1) - 1)
    {X : Set (Fin d → ℤ)} (hXq : ∀ c ∈ X, ∀ μ, (c μ).natAbs ≤ Kn / 4)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (Y' : Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hY : sitesOf Y = {x | (fun μ => (((((x μ).val / aK : ℕ)) : ZMod Kn)).valMinAbs) ∈ X})
    (hY' : sitesOf Y' = {x' | (fun μ => (((((x' μ).val / aK : ℕ)) : ZMod Kn')).valMinAbs) ∈ X})
    (zc : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hsp : ∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK),
      ∀ y ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK) ∪ sitesOf Y, ∀ μ,
      |(x μ - y μ).valMinAbs| ≤ Ds)
    (hq : ∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK) ∪ sitesOf Y, ∀ μ,
      |(x μ).valMinAbs| ≤ q)
    (hqn : 2 * q + 2 * (Ds + (Ds + 1) / 4) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hslack : 20 * (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hslack' : 20 * (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hraw : ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ box (rootCube (m₀ := m₀) zc).1 (L * aK) ∪ sitesOf Y, ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      RawBoxAgree {w | InBox d (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1) + 3 * L ^ (k + 1))
          ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
          (rawOf D))
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))
          (rawOf D'))) :
    ∑ y' ∈ (Finset.univ.filter fun u : unitPts (GB) =>
        unitBlock1 (u : UnitTorus d L N₁' m₁ k) = bc zc),
        detActivityBg m₀ (compWeight L 1) 1 νS (rho4 d L N BG κ) D' y' Y' =
      ∑ y ∈ (Finset.univ.filter fun u : unitPts (GA) =>
        unitBlock1 (u : UnitTorus d L N₁ m₁ k) = zc),
        detActivityBg m₀ (compWeight L 1) 1 νS (rho4 d L N BG κ) D y Y := by
  exact sum_blockU_detActivityBg_cellSites_gen (Dc := (Kn - 26) / 25) hN2 hk νS β p₁ δ hd hL hm₀ hm₁ hN hN' hC hC' hδc hcap hsm hmar hαK hconn hconn' hD hD' hK hKK' hm hm' le_rfl hDsdef hXq Y Y' hY hY' zc hsp hq hqn hslack hslack' hraw

end Pair

end Balaban.Polymer.TwoTorusStep
