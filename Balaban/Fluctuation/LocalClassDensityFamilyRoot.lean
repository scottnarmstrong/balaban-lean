/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamily
public import Balaban.Fluctuation.GeneralOldCoeffFamily

/-!
# Rooting of the marks of an inherited label (`LocalClassDensityFamilyRoot`)

The marks of (M2) are functions of the configurations of the blocks of index `1` at the level
`k + 1`, attached to labels of `𝒟_{k+1}` (block index `1`) that contain the root cube.  The domains
`Y` of the expansion of an inherited label are domains of `𝒟_{k+1}` for the cover index `C.m₀` of
the class (`isDj_of_polyDom`); they are rooted by the landed bridge construction of the zero class
(`bridge 1 z Y`, `markedIdx`, `bridgeFamily`), after the change of the block index:

* `isDj_of_le_m₀`: a domain of `𝒟_j` for the index `m₀` is a domain of `𝒟_j` for every index
  `m₀' ≤ m₀` (a `π′`-cube of index `m₀` is a union of `π′`-cubes of index `m₀'`).
* `polyDom_isDj_one`: the domains of the expansion of a label are domains of `𝒟_{k+1}` for the block
  index `1` (the hypothesis `hdom` of `markedIdx`, `bridgeFamily`, `rootUnionLabels`).
* `classOldMarkedLocal_rootedMarks_of`: for the given maps of a label and a root `z`, every domain
  `Y` of the expansion either meets the fine block of the root through its nearest neighbours, and
  then its bridge `bridge 1 z Y` is a domain of `𝒟_{k+1}` (index `1`) containing `Y` and the root
  cube, of size at most `d(Y) + c_Br`, on whose blocks the block-level mark of `Y` (block index `1`,
  mask `blockU z`) depends; or it does not, and then the mark derivative of `Y` vanishes (no site of
  `Y` has its unit point in the mask; mark-locality of `classOldMarkedLocal_joint_of`).

With `rootUnionLabels` on the class domains these give the labels of the marks of a class in the
common label system (`commonLabels` with `Lab` the root-union labels of the class domains).
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

section Cells

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

/-- **A domain of `𝒟_j` for the index `m₀` is a domain of `𝒟_j` for every smaller index.**  A
`π′`-cube of index `m₀` (an aligned box of side `L · L^{j + m₀ + m₁}`) containing a site `z`
contains the `π′`-cube of index `m₀' < m₀` through `z` whose base is the cell of side
`L · L^{j + m₀' + m₁}` of `z`. -/
theorem isDj_of_le_m₀ {m₀ m₀' j : ℕ} (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hle : m₀' ≤ m₀)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : IsDj m₀ j X) : IsDj m₀' j X := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact hX
  refine ⟨hX.1, fun z hz => ?_, hX.2.2⟩
  obtain ⟨b, hb, hzb, hbX⟩ := hX.2.1 z hz
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hcs0 : 0 < cellSide L m₀ m₁ j := cellSide_pos (L := L) m₀ m₁ j
  have hA0 : 0 < L * cellSide L m₀' m₁ j := Nat.mul_pos hL0 (cellSide_pos (L := L) m₀' m₁ j)
  have hA : L * cellSide L m₀' m₁ j ∣ cellSide L m₀ m₁ j := by
    unfold cellSide
    rw [← pow_succ']
    exact pow_dvd_pow L (by omega)
  have hcs : cellSide L m₀ m₁ j ∣ (N₁ * L ^ m₁) * L ^ K := cellSide_dvd hN hj
  refine ⟨cbase (L * cellSide L m₀' m₁ j) z,
    aligned_of_dvd (dvd_mul_left _ L) (aligned_cbase z), mem_box_cbase hA0 z, ?_⟩
  have h1 := box_subset_box_cbase_of_dvd (L := 1) hcs0 hA le_rfl
    (aligned_cbase (a := L * cellSide L m₀' m₁ j) z)
  rw [one_mul, one_mul, cbase_cbase_of_dvd hA0 hA] at h1
  exact (h1.trans (cell_subset_cube hcs hcs0 hb hzb)).trans hbX

/-- **The domains of the expansion of a label are domains of `𝒟_{lev}` for the block index `1`.**
`isDj_of_polyDom` gives the cover index `m₀ ≥ 1`; `isDj_of_le_m₀` lowers it to `1`. -/
theorem polyDom_isDj_one {ϱ : ℝ} {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {lev : ℕ}
    (hG' : IsLevel Gp lev) (hlev : lev ≤ K) {X₁f : Finset (CTorus d L N₁ m₁ K)}
    {j m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (h1 : 1 ≤ m₀) {X 𝒦X : Set (CTorus d L N₁ m₁ K)}
    (hS : CovSetup Gp m₀ j X 𝒦X) (hd : 3 ≤ d)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : Y ∈ polyDom Gp X₁f m₀ j 𝒦X) : IsDj 1 lev Y :=
  isDj_of_le_m₀ hN hlev h1 (isDj_of_polyDom hG' hS hd hopt hY)

end Cells

section Rooted

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱm : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The rooted marks of one inherited label.**  For a step `S`, a label `τ = (j, y, X)` of the
class `C` with the hypotheses of `classOldMarkedLocal_blockMarks_of`, given maps, a root `z` and a
clamp radius `0 < ρ ≤ c_ψ`, every domain `Y` of the expansion of the label (`L^{C.m₀} ∣ N₁`, `1 ≤ C.m₀`,
`d ≥ 3`, `L ≥ 2`):

1. if `psiThick Y` meets the fine block of `z`: the bridge `bridge 1 z Y` is a domain of `𝒟_{k+1}`
   for the block index `1`, contains `Y` and the root cube, has size at most `d(Y) + c_Br`, and the
   block-level mark of `Y` (mask `blockU z`, block index `1`) depends only on the blocks inside the
   bridge, at every datum of the chart and every first mark of the disc;
2. otherwise the mark derivative of `Y` vanishes at every point of `Ξ^c × B̂` and every first mark
   of the disc. -/
theorem classOldMarkedLocal_rootedMarks_of {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    {β : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ P.E₀) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (hXp : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hB : BgSetting N S.G' Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N S.G' Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : CovSetup S.G' C.m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' C.m₀ j 𝒦X)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne C.m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L C.m₀ m₁ j) E₀ = treeLenCovOne C.m₀ j X)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2)
    {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData S.G' N,
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ p : Dec2.DecParams (coverOf S.G') × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (hN : L ^ C.m₀ ∣ N₁) (hm1 : 1 ≤ C.m₀) (hd : 3 ≤ d) (hL : 2 ≤ L)
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : Y ∈ polyDom S.G' X₁f C.m₀ j 𝒦X) :
    ((psiThick Y ∩ fineBlock z).Nonempty →
      IsDj 1 (k + 1) (bridge 1 z Y) ∧ Y ⊆ bridge 1 z Y ∧
      rootCube (m₀ := 1) z ∈ blocksOf 1 (k + 1) Set.univ (bridge 1 z Y) ∧
      treeLenCovOne 1 (k + 1) (bridge 1 z Y) ≤ treeLenCovOne 1 (k + 1) Y + cBr d L ∧
      ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        DepOn (blocksOf 1 (k + 1) Set.univ (bridge 1 z Y))
          (fun Φ : ∀ b, (S.blockSplit 1 hp).Ωb b =>
            deriv (fun t : ℂ => evDec X₁f C.m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
              (eTermFun S.G' Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
              (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) (S.blockU z) um t Y
              (Θ, S.hatOf 1 ρ hp Φ)) 0)) ∧
    (psiThick Y ∩ fineBlock z = ∅ →
      ∀ um : ℂ, (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      deriv (fun t : ℂ => evDec X₁f C.m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
        (eTermFun S.G' Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
              (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) (S.blockU z) um t Y u) 0 = 0) := by
  have hYdj : IsDj 1 (k + 1) Y :=
    polyDom_isDj_one S.hG' le_rfl hN hm1 hcov hd hopt hY
  have hN1 : L ^ 1 ∣ N₁ := (pow_dvd_pow L hm1).trans hN
  refine ⟨fun hmeet => ?_, fun hmiss um hum u hu => ?_⟩
  · have hBdj := bridge_isDj hN1 z hYdj
    obtain ⟨hdep, -, -, -⟩ := classOldMarkedLocal_blockMarks_of S hb₁ hbC C hm hcl hβ hE₀ hj1 hjk
      hXp hy hB hF hG cc hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hκP
      hchart hF₁an hF₁ hSolan hSolprop hFkan hFk (S.blockU z) 1 hρ hρc hp
    exact ⟨hBdj, subset_bridge z Y, rootCube_mem_blocksOf_bridge hN1 hL z hYdj hmeet,
      treeLenCovOne_bridge_le hN1 z hYdj, fun Θ hΘ um hum =>
        hdep Y (bridge 1 z Y) (subset_bridge z Y) (cell_subset_of_isDj hN1 hBdj) Θ hΘ um hum⟩
  · obtain ⟨-, -, -, -, e5, -⟩ := classOldMarkedLocal_joint_of hb₁ hbC C hm hcl hβ hE₀ hj1 hjk
      hXp hy hB hF S.hk1 hG S.hG' cc hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1
      hlog hκP hchart hF₁an hF₁ hSolan hSolprop hFkan hFk (S.blockU z)
    have hnot : ∀ y ∈ Y, unitPt S.hG' y ∉ S.blockU z := by
      intro y hy hmem
      have h2 : y ∈ psiThick Y ∩ fineBlock z := ⟨Or.inl hy, S.blockU_supported z hmem y rfl⟩
      rw [hmiss] at h2
      exact h2
    have hopen : IsOpen {t : ℂ | (‖um‖ + ‖t‖) * markedRad d L N k a₁ κ cψ cc < δ₁} :=
      isOpen_lt (by fun_prop) continuous_const
    have hev : (fun t : ℂ => evDec X₁f C.m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
        (eTermFun S.G' Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
              (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) (S.blockU z) um t Y u) =ᶠ[nhds (0 : ℂ)]
        fun _ => evDec X₁f C.m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
          (eTermFun S.G' Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
              (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) (S.blockU z) um 0 Y u := by
      filter_upwards [hopen.mem_nhds hum] with t ht
      exact e5 um t 0 ht hum Y hnot u hu
    rw [hev.deriv_eq]
    simp

end Rooted

end Balaban.Fluctuation
