/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelCoeffBg
public import Balaban.Fluctuation.LocalPairCast
public import Balaban.Fluctuation.LocalSetDetCrossAct
public import Balaban.Inhabited.StepTowerThetaDetG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The coefficient of the new level on a local generating set: the read datum and the determinant
part (`NewLevelCoeffBgCast`)

P3 pp. 78-79: the term of the polymer `Y` is recomputed with `𝔹_{k+1}(Y)`; it is analytic on the
chart `Ξ^c_{k+1}(𝔹_{k+1}(Y); 1, ε′)` (4.46) with the `ε′ ≤ ε_{k+1}` of Lemma 4.2, and it equals the
term of the step because both depend only on the fields restricted to `Y₁`.  The datum of the local
set read from a datum of the step chart of radius `ε` (the canonical transport, `clipRaw`) lies in
the local chart only at the radius `(2 K₁ + 2) C₁ ε` (`castG_canon_gdat_xiCData_of_xiCData`), and in
general not at a radius `(1 + o(1)) ε` (the local chart bounds the jump of the data between
adjacent collar sites of the local set by the radius, while the data of the step chart may jump by
more than `ε` between adjacent blocks of side `L^{k+1}`).  This radius enters only the identities
(the replacement identity and the locality), whose hypotheses are smallness conditions of the
radius against absolute constants (`FlCore`, `decDomMargin`, the coercivity margin), never the room
condition `ε′ + K₂(δ₃ + δ_fl) ≤ ε_k` of Lemma 4.2; the analyticity of the recomputed term is asked on
the local chart of radius `ε_{k+1}` itself.

* `castG_canon_gdat_xiCData_of_xiCData`: the datum read by the canonical transport from a datum of
  the step chart of radius `ε` lies in the chart of the cast local set at every radius
  `ε′ ≥ (2 K₁ + 2) C₁ ε`;
* `canon_gdat_eq_of_mem_one`: the read datum agrees with the datum of the step on `Ω₁` of the local
  set;
* `newLevelDetBg_cross`: the determinant part of the coefficient (`newLevelDetBg`) on the step's
  level set and on a generating set `H'` agree at two data of the charts (same radius) agreeing on a
  region `R` of the top layer of `H'`, for the mask `maskPre` of the mask of the step and a polymer
  whose sites are deep in `R` (`detActivityBg_cross`);
* `newLevelDetBg_castG_canon`: the determinant part of the coefficient of the step at a datum of the
  step chart equals that recomputed on the cast local set at the read datum (the determinant half of
  the replacement identity (A5) of `newLabels_castInputs_of_localFamily`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.LargeField Balaban.Fluctuation Balaban.SmallField.GsSpec Finset

section Read

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {N₁' m₁' : ℕ} [NeZero N₁'] {ϱ : ℝ}

/-- **The radius of the read datum** (P3 (4.44)-(4.47)): for a datum `D` of the chart
`Ξ^c_{k+1}(Gp; 1, ε)` of the step's level set, the datum of the cast local set
`Gb = castG hc (localB (k + 1) … Y' hsep)` read by the canonical transport lies in the chart
`Ξ^c_{k+1}(Gb; 1, ε′)` for every `ε′ ≥ (2 K₁ + 2) C₁ ε` (the data domain `Ψ̃^c(C₁ ε, C₁ ε)` of the
chart, `xiCData_inDomainC`, restricted to `Gb`, and the backgrounds recomputed on `Gb`,
`castG_canon_gdat_xiCData`). -/
theorem castG_canon_gdat_xiCData_of_xiCData {ϱp : ℝ}
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱp} (hG : IsLevel Gp (k + 1))
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hk : k + 1 ≤ k + 1)
    (Y' : Set (CTorus d L N₁' m₁' (k + 1))) (hsep : ϱ ≤ minSep L (L ^ m₁')) {N : ℕ}
    {a₁ ν ε ε' : ℝ} (HBp : BgHyp d L (k + 1) ϱp (compWeight L a₁) ν)
    (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (hε : 0 < ε)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc0 : xiC1 d * ε ≤ bgC0 d L N)
    (hc1 : xiC1 d * ε ≤ bgC1 d L N) (hε' : (2 * bgK1 d L N + 2) * xiC1 d * ε ≤ ε')
    (D : BgData Gp N) (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 ε D) :
    XiCData (castG hc (localB (k + 1) hk Y' hsep)) (compWeight L a₁) ν (k + 1) 1 ε'
      ((BgTransport.canon Gp (castG hc (localB (k + 1) hk Y' hsep)) N).gdat
        (BgTransport.reads_canon hG) D) := by
  have hDom := xiCData_inDomainC HBp hsmall hD
  have hδ0 : 0 < xiC1 d * ε := mul_pos (lt_of_lt_of_le one_pos (one_le_xiC1 d)) hε
  have hμε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * ε) ^ 2 ≤ (xiC1 d * ε) ^ 2 := by
    have := HBp.massLe
    nlinarith [sq_nonneg (xiC1 d * ε)]
  exact castG_canon_gdat_xiCData hG hc hk Y' hsep H HBp.mass hδ0 le_rfl hc0 hc1 hμε
    (by nlinarith) D hDom

/-- **The read datum agrees with the datum of the step on the first domain of `Gb`** (both
fields; `Ω₁(Gb)` lies in the data sites of `Gb`). -/
theorem canon_gdat_eq_of_mem_one {ϱp ϱb : ℝ} {N : ℕ}
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱp}
    {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb} (hG : IsLevel Gp (k + 1))
    (D : BgData Gp N) {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ Gb.Ω 1) :
    D.Ψ x = ((BgTransport.canon Gp Gb N).gdat (BgTransport.reads_canon hG) D).Ψ x ∧
      D.h x = ((BgTransport.canon Gp Gb N).gdat (BgTransport.reads_canon hG) D).h x := by
  rw [BgTransport.canon_gdat_eq_levelRestrict hG]
  exact ⟨(levelRestrict_Ψ hG (Nat.le_add_left 1 k) le_rfl Gb.top D
      ((mem_dataSites _).2 (Or.inl hx))).symm,
    (levelRestrict_h hG (Nat.le_add_left 1 k) le_rfl Gb.top D hx).symm⟩

end Read

section Det

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' ϱm ϱm' : ℝ}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Hm' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm'}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ Kc' Cx' c₂' BG₂' δ₁' c₃ : ℝ}

open Classical in
/-- **The determinant part of the coefficient on the step and on a local generating set agree**
(P3 p. 78 for the determinant): for the step's level set `H`, a generating set `H'` whose top
layer contains a region `R`, data `D`, `D'` of the two charts (same radius) agreeing on `R`, a mask
`Zp` of unit points of `H` whose blocks are unit points of `H'`, and a polymer `T` whose sites have
their `8 M₁ L^{k+1}`-neighbourhood in `R`, `newLevelDetBg H … Zp` at `D` equals
`newLevelDetBg H' … (maskPre hlev H' Zp)` at `D'` (any sources). -/
theorem newLevelDetBg_cross (hlev : IsLevel H (k + 1)) {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hR : ∀ x ∈ R, x ∈ H'.Ω (k + 1))
    (hC : FlCore N H Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N H' Hm' a₁ ν c BG κ eps Kc' Cx' c₂' BG₂' δ₁')
    (hS3 : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c₃ BG)
    (hM3 : c₃ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    {D : BgData H N} {D' : BgData H' N} (hD : XiCData H (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData H' (compWeight L a₁) ν (k + 1) 1 eps D')
    (hdat : ∀ z ∈ R, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z) (hN : L ^ 1 ∣ N₁)
    (Zp : Finset (unitPts H)) (hZp : ∀ y ∈ Zp, (y : UnitTorus d L N₁ m₁ k) ∈ unitPts H')
    (g g' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTdeep : ∀ x ∈ sitesOf T, ∀ z, supDist z x ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R) :
    newLevelDetBg H (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Zp
        (⟨rawOf D, rawOf_mem_rawSub D⟩, g) T =
      newLevelDetBg H' (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (maskPre hlev H' Zp)
        (⟨rawOf D', rawOf_mem_rawSub D'⟩, g') T := by
  rw [newLevelDetBg_rawOf, newLevelDetBg_rawOf]
  refine Finset.sum_bij' (fun y hy => (⟨y.1, hZp y hy⟩ : unitPts H'))
    (fun q _ => (⟨q.1, mem_unitPts_of_isLevel hlev q.1⟩ : unitPts H))
    (fun y hy => ?_) (fun q hq => ?_) (fun y _ => rfl) (fun q _ => rfl) (fun y hy => ?_)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩
  · exact (Finset.mem_filter.1 hq).2
  · exact detActivityBg_cross hlev hR hC hC' hS3 hM3 hk hδc hcap hsm hmar hα hD hD' hdat hN y
      ⟨y.1, hZp y hy⟩ rfl T hTdeep

end Det

section DetCast

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {N₁' m₁' : ℕ} [NeZero N₁'] {ϱ ϱp ϱm ϱm' : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱp}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Hm' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm'}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ Kc' Cx' c₂' BG₂' δ₁' c₃ : ℝ}

open Classical in
/-- **The determinant half of the replacement identity on the cast local set** (P3 p. 79; (A5) of
`newLabels_castInputs_of_localFamily` for the determinant part).  Let `D` be a datum of the step
chart `Ξ^c_{k+1}(Gp; 1, ε)` of the step's level set `Gp`, and `Gb = castG hc (localB (k + 1) … Y'
hsep)` a cast local set whose top layer contains a region `R`.  At the radius `eps ≥ (2K₁+2)C₁ε`
of the read datum (`castG_canon_gdat_xiCData_of_xiCData`), with `FlCore` of both sets at `eps`
(the smallness of `eps` against absolute constants), the determinant part of the coefficient of
the step at `D` equals that recomputed on `Gb` at the datum read by the canonical transport, for
every polymer whose sites are deep in `R` and every mask of the step whose blocks are unit points
of `Gb`. -/
theorem newLevelDetBg_castG_canon (hG : IsLevel Gp (k + 1)) (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    (hk1 : k + 1 ≤ k + 1) (Y' : Set (CTorus d L N₁' m₁' (k + 1))) (hsep : ϱ ≤ minSep L (L ^ m₁'))
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hR : ∀ x ∈ R, x ∈ (castG hc (localB (k + 1) hk1 Y' hsep)).Ω (k + 1))
    (HBp : BgHyp d L (k + 1) ϱp (compWeight L a₁) ν)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (castG hc (localB (k + 1) hk1 Y' hsep)) Hm' a₁ ν c BG κ eps Kc' Cx' c₂' BG₂'
      δ₁')
    (hS3 : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c₃ BG)
    (hM3 : c₃ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    {ε : ℝ} (hε : 0 < ε) (hsmall : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (hc0 : xiC1 d * ε ≤ bgC0 d L N) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    (heps : (2 * bgK1 d L N + 2) * xiC1 d * ε ≤ eps)
    (D : BgData Gp N) (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 ε D)
    (hN : L ^ 1 ∣ N₁) (Zp : Finset (unitPts Gp))
    (hZp : ∀ y ∈ Zp, (y : UnitTorus d L N₁ m₁ k) ∈ unitPts (castG hc (localB (k + 1) hk1 Y' hsep)))
    (g g' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTdeep : ∀ x ∈ sitesOf T, ∀ z, supDist z x ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R) :
    newLevelDetBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Zp
        (⟨rawOf D, rawOf_mem_rawSub D⟩, g) T =
      newLevelDetBg (castG hc (localB (k + 1) hk1 Y' hsep)) (compWeight L a₁) a₁ ν
        (rho4 d L N BG κ) (maskPre hG (castG hc (localB (k + 1) hk1 Y' hsep)) Zp)
        (⟨rawOf ((BgTransport.canon Gp (castG hc (localB (k + 1) hk1 Y' hsep)) N).gdat
          (BgTransport.reads_canon hG) D), rawOf_mem_rawSub _⟩, g') T := by
  have hεe : ε ≤ eps := by
    have h1 : ε ≤ xiC1 d * ε := le_mul_of_one_le_left hε.le (one_le_xiC1 d)
    have h2 : xiC1 d * ε ≤ (2 * bgK1 d L N + 2) * xiC1 d * ε := by
      have := bgK1_pos d L N
      have h0 : 0 ≤ xiC1 d * ε := by have := one_le_xiC1 d; positivity
      nlinarith
    linarith
  refine newLevelDetBg_cross hG hR hC hC' hS3 hM3 hk hδc hcap hsm hmar hα
    (xiCData_mono_radius zero_le_one hεe hD)
    (castG_canon_gdat_xiCData_of_xiCData hG hc hk1 Y' hsep HBp HB hε hsmall hc0 hc1 heps D hD)
    (fun z hz => canon_gdat_eq_of_mem_one hG D
      ((castG hc (localB (k + 1) hk1 Y' hsep)).Ω_antitone le_rfl (Nat.le_add_left 1 k)
        (by omega) (hR z hz)))
    hN Zp hZp g g' T hTdeep

end DetCast

end Balaban.Inhabited
