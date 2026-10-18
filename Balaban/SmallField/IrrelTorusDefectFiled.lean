/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectMatch
public import Balaban.SmallField.IrrelTorusDefectSplit
public import Balaban.SmallField.IrrelTorusDefectPartition
public import Balaban.SmallField.IrrelTorusDefectChartCount
public import Balaban.SmallField.IrrelTorusDefectCount

/-!
# The filed torus defect at the origin, exponential form

`norm_filed_origin_le`: the complete finite sum `R_j^T(0) = ∑ᶠ Z ∈ polysAt m₀ j 0, T_Z + Φ_Z`
is bounded by `C E₀ e^{-τ/2}` with `C` independent of the torus, `k`, `j` and the datum, and `τ`
the covering threshold `(N₁ L^{m₁} L^{k-j} - 4 Q - 4)/(4 A) - 1`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ}
  {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

open Classical in
/-- **The filed torus defect at the origin, in the exponential form** (P1 pp. 118–119 (H.6)–(H.7),
pp. 152–153 Prop. 3.10): for a member of the second version, the finite sum over the polymers
through the centre `0` of the terms `T_X + Φ_X` is bounded by `C E₀ e^{-τ/2}`, `τ` the covering
threshold of the torus side. The infinite-volume sum vanishes, the common shapes cancel, and the
two unmatched tails are bounded by the Cauchy form and the polymer counts. The datum enters
through `DataHypAniso` in the conclusion shape of `xiC_dataHypAniso_of_levelGS`. -/
theorem norm_filed_origin_le
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P.m₀ ∣ N₁)
    (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ)
    {σ ε K₂ Λ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (hεΛ : ε ≤ Λ * anisoRadius d L N P j) (hτ : σ ^ 2 * ε ≤ 1 / 4)
    (hdat : ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
      ((fun s => Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)),
          ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) ∈ Dom ∧
        ((fun _ => Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j 0)),
          ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv) ∈ Dom →
      (∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) →
      DataHypAniso Dom (nuIdeal L k (Rg.ν k) j) σ ε K₂
        (fun s => Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        (((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv))
    (hsec : ∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) :
    ‖∑ᶠ Z ∈ polysAt P.m₀ j (0 : CTorus d L N₁ m₁ k),
        (let e : Fld d L N₁ m₁ k N := constFld (Pi.single i₀ 1)
       let blk : Set (CTorus d L N₁ m₁ k) → Finset (CTorus d L N₁ m₁ k) := fun Z' =>
         Finset.univ.filter fun x => Aligned (L ^ j) x ∧ x ∈ Z'
       let u : ℂ := sqrtC (dot (Ψ 0) (Ψ 0))
       let dΨ : Fin d → Fin N → ℂ := fun μ =>
         Ψ (0 + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ 0
       let g : Fin d → Fin d → ℂ := fun μ μ' =>
         dot (dΨ μ) (dΨ μ') - dot (Ψ 0) (dΨ μ) * dot (Ψ 0) (dΨ μ') /
           dot (Ψ 0) (Ψ 0)
       let lift : CTorus d L N₁ m₁ k → Fin d → ℂ := fun z μ =>
         ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - 0) μ : ℤ) : ℂ)
       let a : Set (CTorus d L N₁ m₁ k) → CTorus d L N₁ m₁ k → ℂ := fun Z' x =>
         fderiv ℂ (fun Ψ' => (Tm N₁).E j 0 Z' Ψ' e) e (blockDir L j x i₀)
       (Tm N₁).E j 0 Z e e + (u - 1) * ∑ x ∈ blk Z, a Z x
             + (dot (Ψ 0) ((constFld hv : Fld d L N₁ m₁ k N) 0) / u - 1) *
               fderiv ℂ (fun h' => (Tm N₁).E j 0 Z e h') e e
             - (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' * ∑ x ∈ blk Z, ∑ x' ∈ blk Z,
                 D2 (fun Ψ' => (Tm N₁).E j 0 Z Ψ' e) e (blockDir L j x i₁)
                   (blockDir L j x' i₁) *
                   ((lift x μ - lift x' μ) * (lift x μ' - lift x' μ')))‖ ≤
      2 * (24 * Real.exp 1 *
        (16 * (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 +
          (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 *
            (N * (N * 40 * Λ) ^ 2))) * P.E₀ *
        Real.exp (-((((((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) -
          4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) / (4 * diamA d L P.m₀ m₁) - 1) / 2))) *
        ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
          K0 d L (P.κ - 2))) := by
  have hjk := hn.hjk
  have hj1 := hn.hj1
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hn.hd
  have hcl : SFTermClauses P (xiFieldDom (aIdeal L k (a k)) (Rg.sfBgMass k) (P.eps d L))
      (Tm N₁) := (hF.torus N₁).terms
  have hBg := bgHyp_of_class2 hF.admissible hF.coeff hn.hd hn.hL hn.hϱ
  have hν : 0 < nuIdeal L k (Rg.ν k) j := nuIdeal_pos' (L := L) hF.coeff.nu_pos j
  have hμν := (Rg.sfBgMass_mul_sq hjk).le
  have hνb := hF.coeff.nuIdeal_le_one hF.admissible j
  have hrad := hF.anisoRadiusOK hn.hsmall i₀
  have dat := hdat (Dom := Set.univ) ⟨trivial, trivial⟩ hsec
  have hy : Aligned (L ^ j) (0 : CTorus d L N₁ m₁ k) := fun μ => by simp
  set Lfin := (liftPolys_finite (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j).toFinset
    with hLfin
  have hmemL : ∀ X', X' ∈ Lfin ↔
      X' ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j := fun X' => by
    simp [hLfin]
  let r := anisoRadius d L N P j
  let ψ : Site d → Spin N := fun s => Ψ (0 + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)
  let b : Spin N := ((nuIdeal L k (Rg.ν k) j : ℝ) : ℂ) • hv
  let FF : Finset (Site d) → TermFamily d N := fun X' =>
    ⟨{X'}, fun _ => sizeJ P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'),
      fun S' c => trickFnA i₀ (nuIdeal L k (Rg.ν k) j) r (fun c' : Cfg d N S' =>
        (Tm N₁).E j 0 (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')
          (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - 0))
          (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (Rg.ν k) j) S' c')) c⟩
  let fFin : Finset (Site d) → ℂ := fun X' =>
    Ttw (FF X') i₀ (nuIdeal L k (Rg.ν k) j) X' ψ b +
      Phitw (FF X') i₀ i₁ (nuIdeal L k (Rg.ν k) j) X' ψ
  let Tinf : TermFamily d N := liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀
    (nuIdeal L k (Rg.ν k) j) r
  let fInf : Finset (Site d) → ℂ := fun X' =>
    Ttw Tinf i₀ (nuIdeal L k (Rg.ν k) j) X' ψ b + Phitw Tinf i₀ i₁ (nuIdeal L k (Rg.ν k) j) X' ψ
  have hsplit : ‖∑ X' ∈ Lfin, fFin X'‖ ≤
      2 * (24 * Real.exp 1 *
        (16 * (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 +
          (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 *
            (N * (N * 40 * Λ) ^ 2))) * P.E₀ *
        Real.exp (-((((((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) -
          4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) / (4 * diamA d L P.m₀ m₁) - 1) / 2))) *
        ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
          K0 d L (P.κ - 2))) := by
    obtain ⟨hsum, hzero⟩ := hF.tsum_filed_inf hn hne ψ b
    have hCst0 : 0 ≤ (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 + (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 * (N * (N * 40 * Λ) ^ 2)) := by
      have hΛ : 0 ≤ Λ := by
        have := hrad.1
        by_contra h
        push Not at h
        nlinarith
      have hH : 0 ≤ c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d := by
        have : 0 ≤ c1 d L := by unfold c1; positivity
        positivity
      positivity
    have hmatch : ∀ X ∈ Lfin, X ∈ Tinf.polys → fFin X = fInf X := by
      intro X hX hXp
      exact filed_fin_eq_inf (TmF := Tm) hF.torusIndep hj1 hjk ((hmemL X).1 hX) hXp.2 i₀ i₁
        (nuIdeal L k (Rg.ν k) j) r ψ b
    have hF' : ‖∑ X ∈ Lfin.filter (fun X => X ∉ Tinf.polys), fFin X‖ ≤ (24 * Real.exp 1 * (16 * (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 + (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 * (N * (N * 40 * Λ) ^ 2))) * P.E₀ * Real.exp (-((((((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) - 4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) / (4 * diamA d L P.m₀ m₁) - 1)) / 2)) * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2))) := by
      have hS : ∀ X ∈ Lfin.filter (fun X => X ∉ Tinf.polys),
          X ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j ∧
            ¬ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X := by
        intro X hX
        rw [Finset.mem_filter] at hX
        have hXL := (hmemL X).1 hX.1
        exact ⟨hXL, fun hI => hX.2 ⟨hXL.1, hI⟩⟩
      exact norm_sum_winding_le_of_wt_count (Lfin.filter (fun X => X ∉ Tinf.polys))
        (fun X => sizeJ P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X)) fFin
        hCst0 hF.admissible.E₀_nonneg (fun X _ => treeLenCovOne_nonneg _ _ _)
        (fun X hX => sizeJ_ge_torus_threshold_of_not_infPoly hd hjk hN (hS X hX).1 (hS X hX).2)
        (fun X hX => ⟨0, (hS X hX).1.1⟩)
        (fun X hX => by
          have h := norm_filed_fin_le hcl hBg hν hμν hνb hj1 hjk hN (hS X hX).1 hne hrad dat hσ
            hσ1 hε hεΛ hτ
          refine h.trans (le_of_eq ?_)
          ring)
        (liftPolys_wt_count_subset hjk hN hn.hκ _ (fun X hX => (hS X hX).1))
    have hI : ∀ G : Finset (Finset (Site d)),
        ‖∑ X ∈ G.filter (fun X => X ∈ Tinf.polys ∧ X ∉ Lfin), fInf X‖ ≤ (24 * Real.exp 1 * (16 * (1 + Λ * (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) + Λ ^ 2 + (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (2 * diamA d L P.m₀ m₁) ^ 2 * (N * (N * 40 * Λ) ^ 2))) * P.E₀ * Real.exp (-((((((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) - 4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) / (4 * diamA d L P.m₀ m₁) - 1)) / 2)) * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2))) := by
      intro G
      have hS : ∀ X ∈ G.filter (fun X => X ∈ Tinf.polys ∧ X ∉ Lfin),
          (0 : Site d) ∈ X ∧ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X ∧
            X ∉ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j := by
        intro X hX
        rw [Finset.mem_filter] at hX
        exact ⟨hX.2.1.1, hX.2.1.2, fun h => hX.2.2 ((hmemL X).2 h)⟩
      exact norm_sum_winding_le_of_wt_count (G.filter (fun X => X ∈ Tinf.polys ∧ X ∉ Lfin))
        (fun X => dInf L m₁ k P.m₀ j X) fInf
        hCst0 hF.admissible.E₀_nonneg
        (fun X hX => by
          obtain ⟨n, hn'⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) (hS X hX).2.1
          exact dInf_nonneg hjk hn')
        (fun X hX => dInf_ge_torus_threshold_of_not_liftPolys hd hjk hN (hS X hX).1
          (hS X hX).2.1 (hS X hX).2.2)
        (fun X hX => ⟨0, (hS X hX).1⟩)
        (fun X hX => by
          have h := hF.norm_filed_inf_le hn hne (hS X hX).1 (hS X hX).2.1 dat hσ hσ1 hε hεΛ hτ
          refine h.trans (le_of_eq ?_)
          ring)
        (infPoly_wt_count_subset hjk hn.hκ 0 _ (fun X hX => ⟨(hS X hX).1, (hS X hX).2.1⟩))
    refine (norm_sum_le_of_unmatched Lfin Tinf.polys fFin fInf hmatch hsum hzero hF' hI).trans
      (le_of_eq ?_)
    ring
  rw [finsum_polysAt_zero_eq_sum hjk hN]
  refine le_of_eq_of_le (congrArg norm (Finset.sum_congr rfl fun X' hX' => ?_)) hsplit
  obtain ⟨h0, hnw, hpd⟩ := (Set.Finite.mem_toFinset _).1 hX'
  exact (TPhi_eq_Ttw_add_Phitw (Tm := Tm N₁) (X := Ypoly j X') (S := X') (y := 0) hcl hBg hν
    hμν hνb hj1 hjk hN hy hpd (zero_mem_Ypoly h0) (image_unlift_Ypoly hjk hnw).symm hne hrad Ψ hv).symm

end Balaban.SmallField.Def6v2
