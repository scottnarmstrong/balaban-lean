/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelLocalClauses
public import Balaban.Inhabited.NewLevelLocalSetFacts
public import Balaban.Inhabited.NewLevelLocalFamilyF
public import Balaban.Inhabited.NewLevelLocalPair
public import Balaban.Inhabited.NewLevelCoeffBgCast
public import Balaban.Inhabited.StepTowerNewLabelsHull
public import Balaban.Fluctuation.LocalSetDetFlCore
public import Balaban.Localization.SharpX0Distance
public import Balaban.Localization.Decoupled2SolveAnalytic
public import Balaban.Localization.Decoupled2Background

/-!
# The clauses (A1)–(A5) of the recomputed family on the cast local set of a polymer

Route R-LOC, L5: the instance of `NewLevelSystem.clauses_of` at the local pair of the polymer `T`,
`Gb = castG hc (𝔹_{k+1}(Yp'))` and `Gd = castG hc (𝔹_k(Ω_k(𝔹_{k+1}(Yp'))))`, for a set `Yp'` whose
cast local set has every site within `2 L^{k+1+m₁'}` of `sitesOf T` in its top layer (`m₁ + 2 ≤ m₁'`;
e.g. the collar of width `2 L^{k+1+m₁'}` of a set `Y ⊇ sitesOf T`, `castLocal_margin`, or the set
`Ŷ` of ruling R13).  The facts of the local pair
(`castG_localB_pair`, `coverBase_of_aligned_supSep`), its fluctuation cores
(`flCore_castG_localB_of`), its decoupling pairs (`Dec2.i4b_analytic`, `Dec2.i4a_analytic`), the
projection onto its data (`exists_rawSub_proj`), the margins of `T` (`castLocal_labelMargin`,
`castLocal_margin`) and the determinant part at the read data (`newLevelDetBg_castG_canon`) are
derived; the step enters through its `FlCore` at the cover constants.

* `flCore_castG_localB_of`: the core of the cast local pair from a core of the step;
* `newLevelDetBg_castLocal_read`: the determinant part at the read data on the cast local set;
* `NewLevelSystem.clauses_castLocal_of`: the clauses (A1)–(A5) of `localFamily_of_coeff` for the
  polymer `T` on its cast local set;
* `NewLevelSystem.localFamily_castLocal_of`: the family `f` and the bounds `b` of the root `z` with
  the forms `hfan`, `hfbd`, `hfloc`, `hfrot`, `hfval` of `newLabels_castInputs_of_localFamily`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec
  Balaban.LargeField Balaban.Polymer Finset MeasureTheory Matrix Balaban.Inhabited.MarkBudgetAudit

section Core

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {N₁' m₁' : ℕ} [NeZero N₁'] {ϱ ϱf : ℝ}

/-- **The fluctuation core of the cast local pair from a core of the step at any cover
constants** and the cover specification `(mixedKc, Cchi)` of the fluctuation pairs of the local
set (`hS2`, `hM2`): `flCore_castG_localB` with the numerical fields of a `FlCore` of a set `Gs`. -/
theorem flCore_castG_localB_of_gen {Gs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {Hf : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱf} {a₁ ν c BG κ eps Kc Cx c₂' c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gs Hf a₁ ν c BG κ eps Kc Cx c₂' BG₂ δ₁)
    (hS2 : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm : m₁ ≤ m₁') (X : Set (CTorus d L N₁' m₁' (k + 1)))
    (hsep : ϱ ≤ minSep L (L ^ m₁')) :
    FlCore N (castG hc (localB (k + 1) (le_refl (k + 1)) X hsep))
      (castG hc (localB k (Nat.le_succ k)
        (↑((localB (k + 1) (le_refl (k + 1)) X hsep).Ω k) : Set (CTorus d L N₁' m₁' (k + 1)))
          hsep))
      a₁ ν c BG κ eps (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂ δ₁ :=
  flCore_castG_localB hC.Sp hc hm X hsep hC.hS hC.HBp hC.hκ hC.hM hC.eps_pos hC.small1 hC.c7le
    hS2 hM2 hC.δ₁_pos hC.δ₁_le hC.B_le hC.B_one hC.phi_lt

/-- **The fluctuation core of the cast local pair from a core of the step with the cover
constants**: `flCore_castG_localB` with the numerical fields of a `FlCore` of a set `Gs` at the
constants `(mixedKc, Cchi)`. -/
theorem flCore_castG_localB_of {Gs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {Hf : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱf} {a₁ ν c BG κ eps c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gs Hf a₁ ν c BG κ eps (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂ δ₁)
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm : m₁ ≤ m₁') (X : Set (CTorus d L N₁' m₁' (k + 1)))
    (hsep : ϱ ≤ minSep L (L ^ m₁')) :
    FlCore N (castG hc (localB (k + 1) (le_refl (k + 1)) X hsep))
      (castG hc (localB k (Nat.le_succ k)
        (↑((localB (k + 1) (le_refl (k + 1)) X hsep).Ω k) : Set (CTorus d L N₁' m₁' (k + 1)))
          hsep))
      a₁ ν c BG κ eps (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂ δ₁ :=
  flCore_castG_localB_of_gen hC hC.hS2 hC.hM2 hc hm X hsep

end Core

section Read

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {N₁' m₁' : ℕ} [NeZero N₁'] {ϱ ϱf ϱm : ℝ}

open Classical in
/-- **The determinant part at the read data on the cast local set of a polymer**: the hypothesis
`hdetT` of `NewLevelSystem.clauses_of` at `Gb = castG hc (𝔹_{k+1}(Yp'))`, for a set `Yp'` whose
cast local set has every site within `2 L^{k+1+m₁'}` of `sitesOf T` in its top layer
(`m₁ + 2 ≤ m₁'`, so that the deep margin
`8 L^{k+1+m₁}` of `newLevelDetBg_castG_canon` lies in the top layer of `Gb`), a mask `Zp` whose
blocks are unit points of `Gb`, and a retraction `π_b` onto the data of `Gb`. -/
theorem newLevelDetBg_castLocal_read {S : StepSetting d L N₁ m₁ k N ϱ} (hS1 : S.a₁ = 1)
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm : m₁ + 2 ≤ m₁') (hsep : ϱ ≤ minSep L (L ^ m₁'))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)}
    {Yp' : Set (CTorus d L N₁' m₁' (k + 1))}
    (hmarg' : ∀ x ∈ sitesOf T, ∀ y : CTorus d L N₁ m₁ (k + 1), supDist x y ≤ 2 * L ^ (k + 1 + m₁') →
      y ∈ (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)).Ω (k + 1))
    {Hf : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱf}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ Kc' Cx' c₂' BG₂' δ₁' c₃ : ℝ}
    (hCs : FlCore N S.G' Hf S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hCz : FlCore N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) Hm S.a₁ S.ν c BG κ eps
        Kc' Cx' c₂' BG₂' δ₁')
    (hS3 : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c₃ BG)
    (hM3 : c₃ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ} (hδc : 0 ≤ δc)
    (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    {t : ℝ} (ht : 0 < t) (hsmall : (4 * d + 6) * ((2 * d + 1) * t) ≤ 1)
    (hc0 : xiC1 d * t ≤ bgC0 d L N) (hc1 : xiC1 d * t ≤ bgC1 d L N)
    (heps : (2 * bgK1 d L N + 2) * xiC1 d * t ≤ eps) (hN1 : L ^ 1 ∣ N₁)
    {Zp : Finset (unitPts S.G')}
    (hZp : ∀ y ∈ Zp, (y : UnitTorus d L N₁ m₁ k) ∈ unitPts
        (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)))
    (πb : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N
        (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)))
    (hπb : ∀ r (h : r ∈ rawSub N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep))), πb
        r = ⟨r, h⟩) :
    ∀ D : BgData S.G' N, XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 t D →
      newLevelDetBg S.G' (compWeight L 1) 1 S.ν (rho4 d L N BG κ) Zp
          (⟨rawOf D, rawOf_mem_rawSub D⟩, 0) T =
        newLevelDetBg (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) (compWeight L 1) 1 S.ν
            (rho4 d L N BG κ)
          (maskPre S.hG' (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) Zp)
              (πb (clipRaw (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep))
              (rawOf D)), 0) T := by
  intro D hD
  have hL : 3 ≤ L := hCs.Sp.hL
  have hk1 := S.hk1
  have h8 : 8 * L ^ (k + 1 + m₁) ≤ 2 * L ^ (k + 1 + m₁') := by
    have h1 : L ^ (k + 1 + m₁) * L ^ 2 ≤ L ^ (k + 1 + m₁') := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 9 ≤ L ^ 2 := by nlinarith
    have h3 : 0 < L ^ (k + 1 + m₁) := pow_pos (by omega) _
    nlinarith
  have hCs1 := hCs
  have hCz1 := hCz
  rw [hS1] at hCs1 hCz1 hD
  have e1 : clipRaw (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) (rawOf D) =
      rawOf ((BgTransport.canon S.G' (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) N).gdat
          (BgTransport.reads_canon S.hG') D) := by
    rw [BgTransport.rawOf_gdat, ← clipRawL_apply]
    rfl
  have hmem : clipRaw (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) (rawOf D) ∈ rawSub N
      (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) := e1 ▸ rawOf_mem_rawSub _
  have hR : ∀ x ∈ Finset.univ.filter
      (· ∈ (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)).Ω (k + 1)), x ∈
      (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)).Ω (k + 1) :=
    fun x hx => (Finset.mem_filter.1 hx).2
  have hdeep : ∀ x ∈ sitesOf T, ∀ y, supDist y x ≤ 8 * L ^ (k + 1 + m₁) →
      y ∈ Finset.univ.filter
          (· ∈ (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)).Ω (k + 1)) := fun x hx y hy =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _,
      hmarg' x hx y ((by rwa [supDist_comm] : supDist x y ≤ 8 * L ^ (k + 1 + m₁)).trans h8)⟩
  rw [newLevelDetBg_castG_canon S.hG' hc le_rfl Yp' hsep hR hCs1.HBp hCz1.HBp hCs1 hCz1 hS3 hM3 hk1
    hδc hcap hsm hmar hα ht hsmall hc0 hc1 heps D hD hN1 Zp hZp 0 0 T hdeep, hπb _ hmem]
  congr 3

end Read

namespace NewLevelSystem

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
  {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
  (NS : NewLevelSystem S C z Jr)

open Classical in
/-- (Core, with the bound of the old terms on their composed charts, `composedChart`.) **The clauses of the recomputed family on the cast local set of a polymer** (route R-LOC, L5):
for the polymer `T` whose root cube is that of `z` and a set `Yp'` whose cast local set has every
site within `2 L^{k+1+m₁'}` of `sitesOf T` in its top layer (`m₁ + 2 ≤ m₁'`), under the hypotheses
of `clauses_of` that do not
concern the local pair, with the step's `FlCore` at the cover constants at the radii `t` and `ε′`
for the constants of the system and of the old terms, there are a retraction `π_b` onto the data
of `Gb = castG hc (𝔹_{k+1}(Yp'))` and a function `c_T` of the parameters of `Gb` (the coefficient
recomputed on `Gb` from the labels inside `T`) with the clauses (A1)–(A5) of
`localFamily_of_coeff`. -/
theorem clauses_castLocal_of_composed (hS1 : S.a₁ = 1)
    (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
    -- the local pair: the cast local set of a set `Yp'` with the margin of `sitesOf T`
    {N₁' m₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm : m₁ + 2 ≤ m₁')
    (hsep : ϱ ≤ minSep L (L ^ m₁'))
    {eps' : ℝ}
    -- the radii
    (hle : t ≤ eps')
    (hεr : (2 * bgK1 d L N + 2) * xiC1 d * t ≤ eps')
    {ε : ℝ}
    (hεt : ε ≤ t)
    {εloc : ℝ}
    (hεloc : εloc ≤ eps')
    {c c₂ : ℝ}
    -- the constants of the system: `FlCore` of the step at the radii `t`, `ε′` (cover constants)
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c NS.BG)
    {ϱf : ℝ} {Hf : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱf}
    {Kc₀ Cx₀ c₂₀ : ℝ}
    (hCs : FlCore N S.G' Hf S.a₁ S.ν c NS.BG NS.κ t Kc₀ Cx₀ c₂₀ NS.BG₂ t)
    (hCs' : FlCore N S.G' Hf S.a₁ S.ν c NS.BG NS.κ eps' Kc₀ Cx₀ c₂₀ NS.BG₂ t)
    (hS2m : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂ NS.BG₂)
    (hM2m : c₂ * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hMXd : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hCx : 0 ≤ Cchi d L)
    (hMXn : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    {δc : ℝ}
    (hδc : 0 ≤ δc)
    (hdm : decDomMargin d L N NS.BG NS.κ (xiC1 d * t) < δc)
    (hα : K4 d L N NS.BG NS.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hdm' : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps') < δc)
    (hα' : K4 d L N NS.BG NS.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4)
    {cψ : ℝ}
    (hcψ : 0 ≤ cψ)
    (hρ₀c : 2 * NS.p₁ ≤ cψ)
    (hρp : S.p₁ ≤ NS.p₁)
    (hRu : corrU * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hBG₂ : 0 ≤ NS.BG₂)
    {κdec κ₀ : ℝ}
    (hκ₀ : 0 ≤ κ₀)
    (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.κ)
    (h1 : 1 ≤ (NS.κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (NS.κ / 2 - 1) / 2)
    {R₁ r : ℝ}
    (hR₁ : 1 < R₁)
    (hr : 0 < r)
    (hrays : (2 * R₁ + r) * NS.p₁ ≤ cψ)
    {R U : ℝ}
    (hR : 0 < R)
    (hRR : (R + R) * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hUR : 2 * U ≤ R)
    (hU : 17 / 16 ≤ U)
    {cL c₂L : ℝ}
    -- the constants of the old terms: `FlCore` of the step at the radii `t`, `ε′`
    (hSL : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) cL NS.O.BG)
    {ϱfL : ℝ} {HfL : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱfL}
    {KcL₀ CxL₀ c₂L₀ : ℝ}
    (hCLs : FlCore N S.G' HfL S.a₁ S.ν cL NS.O.BG NS.O.κ t KcL₀ CxL₀ c₂L₀ NS.O.BG₂ NS.O.δ₁)
    (hCLs' : FlCore N S.G' HfL S.a₁ S.ν cL NS.O.BG NS.O.κ eps' KcL₀ CxL₀ c₂L₀ NS.O.BG₂ NS.O.δ₁)
    (hS2mL : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂L NS.O.BG₂)
    (hM2mL : c₂L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hMXLd : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hMXLn : cstarX d L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    {δcL : ℝ}
    (hdmL : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * t) < δcL)
    (hαL : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hdmL' : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * eps') < δcL)
    (hαL' : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4)
    {cψL : ℝ}
    (hcψL : 0 ≤ cψL)
    (hκκL : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.O.κ)
    (h1L : 1 ≤ (NS.O.κ / 2 - 1) / 2)
    (hlogL : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ NS.O.m₀) ^ d : ℕ) : ℝ)) ≤
      (NS.O.κ / 2 - 1) / 2)
    (hρL : 0 < NS.O.ρ)
    (hρcL : NS.O.ρ ≤ cψL)
    (hρpL : S.p₁ ≤ NS.O.ρ)
    (hRuL : corrU * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) <
      NS.O.δ₁)
    {a : ℝ} (hca : corrU ≤ a)
    (haL : a * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    {t₀ : ℝ}
    (ht₀ : 0 < t₀)
    (hRt : (corrU + t₀) *
      markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    -- the settings of the old terms
    (hNm : L ^ NS.O.m₀ ∣ N₁)
    {XL : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' NS.O.m₀ (NS.O.jL τ) (XL τ) (NS.O.𝒦X τ))
    (hX₁L : ∀ τ, (↑(NS.O.X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
    (hoptL : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) W₀ ∧
        bondCost (scaleW L NS.O.m₀ m₁ (NS.O.jL τ)) E₀ = treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ))
    {Eb : NS.O.ι → ℝ} (hEb : ∀ τ, 0 ≤ Eb τ) {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {r₀ δ₃ δfl δ₃' δfl' ϱs : ℝ} {X₀ : NS.O.ι → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hBo : ∀ τ, BgSetting N S.G' (NS.O.Gk τ) (NS.O.Gj τ) S.a₁ S.ν cL NS.O.BG NS.O.κ r₀ t δ₃
      (X₀ τ) (NS.O.X₁f τ) (NS.O.jL τ))
    {Hs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱs} {Kf Cf c₂f : ℝ}
    (hFLo : ∀ τ, FlSetting N S.G' (NS.O.Gk τ) Hs S.a₁ S.ν NS.O.κ NS.O.BG t δ₃ Kf Cf c₂f
      NS.O.BG₂ NS.O.δ₁ δfl (NS.O.X₁f τ))
    -- the numerical conditions of the settings of the old terms at the gate radius
    (hCN' : ChainNum d L N m₁ NS.O.BG NS.O.κ r₀ eps' δ₃')
    (hFN' : FlNum d L N NS.O.BG NS.O.BG₂ NS.O.κ eps' δ₃' NS.O.δ₁ δfl')
    (hGs : IsLevel Hs k)
    (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1)
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (NS.O.FkL τ) {p | ∃ D : BgData (NS.O.Gk τ) N,
      InUnionDomainC (NS.O.Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hEan : ∀ τ, AnalyticOnNhd ℂ (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
      (XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ composedChart (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖(S.β : ℂ)⁻¹ * NS.O.Eτ τ r‖ ≤
        Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ)))
    (hEr : ∀ τ (Q : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 →
      ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
        (S.β : ℂ)⁻¹ * NS.O.Eτ τ (rotRaw (cmat Q) r) = (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
    -- the bounds of the recomputed activities and marks
    {εH κH κ' : ℝ} (hκH : κH ≤ 2 * κdec - 1)
    {F0 : ({Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) → ℝ}
    (hεz : 8 * (|S.β| * (6 * (1 / 2) * c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t
        (rho4 d L N NS.BG NS.κ)‖ / r ^ 3)) ≤ εH)
    (hεo : ∀ Y ∈ NS.𝒴C, corrU / a * (|S.β| * (∑ τ, if Y ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀
        (NS.O.jL τ) (NS.O.𝒦X τ) then 2 * (Eb τ * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL τ)
          (XL τ) - 2 * κdec * treeLenCov S.G' NS.O.m₀ Y)) else 0)) ≤
      εH * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y))
    (hFb : ∀ i, ‖(S.β : ℂ)‖ * 4 * ‖energyBdScaled d L N (compWeight L S.a₁) k
          (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t (rho4 d L N NS.BG NS.κ)‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) ≤ F0 (Sum.inl i))
    (hFo : ∀ q, |S.β| * (Eb q.1.1 * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL q.1.1)
        (XL q.1.1) - 2 * κdec * treeLenCov S.G' NS.O.m₀ q.1.2) / t₀) ≤
      F0 (Sum.inr q) * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2)))
    (hεpos : 0 < εH)
    (hι : Nonempty ({Y' // Y' ∈ bridgeFamily 1
      (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}))
    (hF0 : ∀ i, 0 < F0 i)
    (hκ' : 0 ≤ κ')
    (hκ : κ' + 3 * NS.Z.κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 +
      rootUnionK d L 1 m₁ NS.Z.κ0) + rootUnionK d L 1 m₁ NS.Z.κ0) ^ 3 * c1 d L *
      Real.exp ((κH - 2 * NS.Z.κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp NS.κ) < 1)
    -- the determinant part on the cast local set
    {c₃ : ℝ} (hS3 : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c₃ NS.BG)
    (hM3 : c₃ * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) (hc0 : xiC1 d * t ≤ bgC0 d L N)
    (hN1 : L ^ 1 ∣ N₁)
    -- the reference configuration and the polymer
    (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (hΦ₀ : ∀ b u, Φ₀ b u = 0)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hzT : rootCube (m₀ := 1) z ∈ T)
    {Yp' : Set (CTorus d L N₁' m₁' (k + 1))}
    (hmarg' : ∀ x ∈ sitesOf T, ∀ y : CTorus d L N₁ m₁ (k + 1), supDist x y ≤ 2 * L ^ (k + 1 + m₁') →
      y ∈ (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)).Ω (k + 1))
    {Ypl : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYpl : thickSet S.G' (sitesOf T) ⊆ Ypl)
    (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ)
    (he : ∀ θ ∈ physV S S.a₁ S.ν t, e θ T = NS.coeff θ T)
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩) :
    ∃ πb : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N
        (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)),
      (∀ r (h : r ∈ rawSub N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep))), πb
          r = ⟨r, h⟩) ∧
      ∃ cT : physParamBg N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) → ℂ, ∃ bT
          : ℝ, 0 ≤ bT ∧
        AnalyticOnNhd ℂ cT
            (physVBg N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) S.a₁ S.ν t) ∧
        (∀ θb ∈ physVBg N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) S.a₁ S.ν t,
            ‖cT θb‖ ≤ bT) ∧
        (∀ θb θb' : physParamBg N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)),
          (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
            XiCRaw (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) (compWeight L S.a₁) S.ν
                (k + 1) 1 εloc →
          (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
            XiCRaw (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) (compWeight L S.a₁) S.ν
                (k + 1) 1 εloc →
          θb.2 = 0 → θb'.2 = 0 →
          (∀ x ∈ Ypl, (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1 x =
              (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1 x ∧
            (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 x =
              (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 x) → cT θb = cT θb') ∧
        (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θb ∈ physVBg N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) S.a₁ S.ν t, ∀ θb'
              ∈ physVBg N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) S.a₁ S.ν t,
          (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) =
            rotRaw (cmat Q) (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) → cT θb' = cT θb) ∧
        (∀ q : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N,
          Def6.XiDom S.G' (compWeight L S.a₁) S.ν (k + 1) ε q.1 q.2 →
          cT (πb (clipRaw (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) q), 0) = e
              (π (clipRaw S.G' q), 0) T) := by
  classical
  have hk1 := S.hk1
  have hd := SpG.hd
  have hL := SpG.hL
  have hN := SpG.big
  have hM := SpG.hM
  have hag := SpG.sep
  have hm₁ : 2 ≤ m₁ := SpG.aligned.two_le
  have hm' : m₁ ≤ m₁' := by omega
  have HB := hCs.HBp
  have hd0 : 0 < d := by omega
  -- the local pair
  obtain ⟨hPd, hdtop, hdk, hHmtop, hrow, hAl, hSS⟩ :=
    castG_localB_pair (a := compWeight L S.a₁) (ν := S.ν) hc hm₁ hm' hk1 hL Yp' hsep
  have Sb := coverBase_of_aligned_supSep hAl hSS hN hM hd hL SpG.mass SpG.massLe SpG.weights hag
  have hCz := flCore_castG_localB_of_gen hCs hS2m hM2m hc hm' Yp' hsep
  have hCz' := flCore_castG_localB_of_gen hCs' hS2m hM2m hc hm' Yp' hsep
  have hCo := flCore_castG_localB_of_gen hCLs hS2mL hM2mL hc hm' Yp' hsep
  have hCo' := flCore_castG_localB_of_gen hCLs' hS2mL hM2mL hc hm' Yp' hsep
  -- the decoupling pairs of the local pair
  have hξ : 0 ≤ xiC1 d := by linarith [one_le_xiC1 d]
  have h0' : 0 ≤ 2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps')) := by
    have := (K4_pos (L := L) (N := N) (κ := NS.κ) hCs.hS.fam.2.1 hd0).le
    have := hCs'.eps_pos; positivity
  have h0L' : 0 ≤ 2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps')) := by
    have := (K4_pos (L := L) (N := N) (κ := NS.O.κ) hCLs.hS.fam.2.1 hd0).le
    have := hCs'.eps_pos; positivity
  obtain ⟨Fz, hFzan, hFz⟩ := Dec2.i4b_analytic (N := N) hS Sb HB hCz.hκ.le hCz.hM
  obtain ⟨Sz, hSzan, hSz⟩ := Dec2.i4a_analytic (N := N) hCz'.hS2.fam hCz'.hS2.an
    hCz'.SM.toCoverBase hCz'.hκ.le hCz'.hM2 false h0' hCz.eps_pos.le hCz'.B_le hCz.δ₁_le
  obtain ⟨FL, hFLan, hFL⟩ := Dec2.i4b_analytic (N := N) hSL Sb HB hCo.hκ.le hCo.hM
  obtain ⟨SL, hSLan, hSLs⟩ := Dec2.i4a_analytic (N := N) hCo'.hS2.fam hCo'.hS2.an
    hCo'.SM.toCoverBase hCo'.hκ.le hCo'.hM2 false h0L' hCo.δ₁_pos.le hCo'.B_le hCo.δ₁_le
  -- the projection onto the data of the local set and the margins of `T`
  obtain ⟨πb, hπb⟩ := exists_rawSub_proj (N := N)
      (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep))
  have hTm : LabelMargin (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) (sitesOf T) :=
    fun x hx y hy => hmarg' x hx y (hy.trans (Nat.mul_le_mul_left 2
      (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega))))
  -- the determinant part at the read data
  have hdetT := newLevelDetBg_castLocal_read hS1 hc hm hsep hmarg' hCs' hCz' hS3 hM3 hδc hMXn hsm
    hdm' hα' hCs.eps_pos hCs.small1 hc0 ((hCs.c7le).trans (c7_le_bgC1 d L N NS.BG NS.κ)) hεr hN1
    (blockU_mem_unitPts_of_margin S z hzT fun x hx => hTm x hx x (by simp [supDist_self])) πb hπb
  obtain ⟨bT, hbT, hA1, hA2, hA3, hA4, hA5⟩ := NS.clauses_of_composed
      (Gl := castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep))
      (Gd := castG hc
      (localB k (Nat.le_succ k)
      (↑((localB (k + 1) (le_refl (k + 1)) Yp' hsep).Ω k) : Set
      (CTorus d L N₁' m₁' (k + 1)))   hsep))
      (fun _ => Fz) (fun _ => Sz) (fun _ => FL) (fun _ => SL) (fun _ => Fz) (fun _ => Sz)
      hS1 SpG HB HB hd hN hm₁ hM hag hag hag hle hεr hεt hεloc hAl hSS hPd hdk hdtop hHmtop
      hrow Sb hS hCz hCz' hMXd hCx hMXn hδc hdm hα hdm' hα' hsm hcψ hρ₀c hρp hRu hBG₂ hκ₀
      hκdec hκκ h1 hlog hR₁ hr hrays hR hRR hUR hU hSL hCo hCo' hMXLd hMXLn hdmL hαL hdmL'
      hαL' hsmL hcψL hκκL h1L hlogL hρL hρcL hρpL hRuL hca haL ht₀ hRt hNm hcovL hX₁L hoptL hEb
      hb₁ hbC hBo hFLo hCN' hFN' hGs hrb hFkan hEan hEbd hEr (fun _ => hFzan)
      (fun _ => hFz) (fun _ => hSzan) (fun _ => hSz) (fun _ => hFzan) (fun _ => hFz)
      (fun _ => hSzan) (fun _ => hSz) (fun _ => hFLan) (fun _ => hFL) (fun _ => hSLan)
      (fun _ => hSLs) hκH hεz hεo hFb hFo hεpos hι hF0 hκ' hκ hε hz Φ₀ hΦ₀ T hTm hYpl e he π hπ πb
      hπb hdetT
  exact ⟨πb, hπb, _, bT, hbT, hA1, hA2, hA3, hA4, hA5⟩


open Classical in
/-- **The clauses of the recomputed family on the cast local set of a polymer** (route R-LOC, L5):
for the polymer `T` whose root cube is that of `z` and a set `Yp'` whose cast local set has every
site within `2 L^{k+1+m₁'}` of `sitesOf T` in its top layer (`m₁ + 2 ≤ m₁'`), under the hypotheses
of `clauses_of` that do not
concern the local pair, with the step's `FlCore` at the cover constants at the radii `t` and `ε′`
for the constants of the system and of the old terms, there are a retraction `π_b` onto the data
of `Gb = castG hc (𝔹_{k+1}(Yp'))` and a function `c_T` of the parameters of `Gb` (the coefficient
recomputed on `Gb` from the labels inside `T`) with the clauses (A1)–(A5) of
`localFamily_of_coeff`. The instance of `clauses_castLocal_of_composed` with the bound on the whole chart. -/
theorem clauses_castLocal_of (hS1 : S.a₁ = 1)
    (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
    -- the local pair: the cast local set of a set `Yp'` with the margin of `sitesOf T`
    {N₁' m₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm : m₁ + 2 ≤ m₁')
    (hsep : ϱ ≤ minSep L (L ^ m₁'))
    {eps' : ℝ}
    -- the radii
    (hle : t ≤ eps')
    (hεr : (2 * bgK1 d L N + 2) * xiC1 d * t ≤ eps')
    {ε : ℝ}
    (hεt : ε ≤ t)
    {εloc : ℝ}
    (hεloc : εloc ≤ eps')
    {c c₂ : ℝ}
    -- the constants of the system: `FlCore` of the step at the radii `t`, `ε′` (cover constants)
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c NS.BG)
    {ϱf : ℝ} {Hf : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱf}
    {Kc₀ Cx₀ c₂₀ : ℝ}
    (hCs : FlCore N S.G' Hf S.a₁ S.ν c NS.BG NS.κ t Kc₀ Cx₀ c₂₀ NS.BG₂ t)
    (hCs' : FlCore N S.G' Hf S.a₁ S.ν c NS.BG NS.κ eps' Kc₀ Cx₀ c₂₀ NS.BG₂ t)
    (hS2m : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂ NS.BG₂)
    (hM2m : c₂ * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hMXd : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hCx : 0 ≤ Cchi d L)
    (hMXn : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    {δc : ℝ}
    (hδc : 0 ≤ δc)
    (hdm : decDomMargin d L N NS.BG NS.κ (xiC1 d * t) < δc)
    (hα : K4 d L N NS.BG NS.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hdm' : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps') < δc)
    (hα' : K4 d L N NS.BG NS.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4)
    {cψ : ℝ}
    (hcψ : 0 ≤ cψ)
    (hρ₀c : 2 * NS.p₁ ≤ cψ)
    (hρp : S.p₁ ≤ NS.p₁)
    (hRu : corrU * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hBG₂ : 0 ≤ NS.BG₂)
    {κdec κ₀ : ℝ}
    (hκ₀ : 0 ≤ κ₀)
    (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.κ)
    (h1 : 1 ≤ (NS.κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (NS.κ / 2 - 1) / 2)
    {R₁ r : ℝ}
    (hR₁ : 1 < R₁)
    (hr : 0 < r)
    (hrays : (2 * R₁ + r) * NS.p₁ ≤ cψ)
    {R U : ℝ}
    (hR : 0 < R)
    (hRR : (R + R) * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hUR : 2 * U ≤ R)
    (hU : 17 / 16 ≤ U)
    {cL c₂L : ℝ}
    -- the constants of the old terms: `FlCore` of the step at the radii `t`, `ε′`
    (hSL : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) cL NS.O.BG)
    {ϱfL : ℝ} {HfL : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱfL}
    {KcL₀ CxL₀ c₂L₀ : ℝ}
    (hCLs : FlCore N S.G' HfL S.a₁ S.ν cL NS.O.BG NS.O.κ t KcL₀ CxL₀ c₂L₀ NS.O.BG₂ NS.O.δ₁)
    (hCLs' : FlCore N S.G' HfL S.a₁ S.ν cL NS.O.BG NS.O.κ eps' KcL₀ CxL₀ c₂L₀ NS.O.BG₂ NS.O.δ₁)
    (hS2mL : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂L NS.O.BG₂)
    (hM2mL : c₂L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hMXLd : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hMXLn : cstarX d L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    {δcL : ℝ}
    (hdmL : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * t) < δcL)
    (hαL : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hdmL' : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * eps') < δcL)
    (hαL' : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4)
    {cψL : ℝ}
    (hcψL : 0 ≤ cψL)
    (hκκL : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.O.κ)
    (h1L : 1 ≤ (NS.O.κ / 2 - 1) / 2)
    (hlogL : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ NS.O.m₀) ^ d : ℕ) : ℝ)) ≤
      (NS.O.κ / 2 - 1) / 2)
    (hρL : 0 < NS.O.ρ)
    (hρcL : NS.O.ρ ≤ cψL)
    (hρpL : S.p₁ ≤ NS.O.ρ)
    (hRuL : corrU * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) <
      NS.O.δ₁)
    {a : ℝ} (hca : corrU ≤ a)
    (haL : a * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    {t₀ : ℝ}
    (ht₀ : 0 < t₀)
    (hRt : (corrU + t₀) *
      markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    -- the settings of the old terms
    (hNm : L ^ NS.O.m₀ ∣ N₁)
    {XL : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' NS.O.m₀ (NS.O.jL τ) (XL τ) (NS.O.𝒦X τ))
    (hX₁L : ∀ τ, (↑(NS.O.X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
    (hoptL : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) W₀ ∧
        bondCost (scaleW L NS.O.m₀ m₁ (NS.O.jL τ)) E₀ = treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ))
    {Eb : NS.O.ι → ℝ} (hEb : ∀ τ, 0 ≤ Eb τ) {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {r₀ δ₃ δfl δ₃' δfl' ϱs : ℝ} {X₀ : NS.O.ι → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hBo : ∀ τ, BgSetting N S.G' (NS.O.Gk τ) (NS.O.Gj τ) S.a₁ S.ν cL NS.O.BG NS.O.κ r₀ t δ₃
      (X₀ τ) (NS.O.X₁f τ) (NS.O.jL τ))
    {Hs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱs} {Kf Cf c₂f : ℝ}
    (hFLo : ∀ τ, FlSetting N S.G' (NS.O.Gk τ) Hs S.a₁ S.ν NS.O.κ NS.O.BG t δ₃ Kf Cf c₂f
      NS.O.BG₂ NS.O.δ₁ δfl (NS.O.X₁f τ))
    -- the numerical conditions of the settings of the old terms at the gate radius
    (hCN' : ChainNum d L N m₁ NS.O.BG NS.O.κ r₀ eps' δ₃')
    (hFN' : FlNum d L N NS.O.BG NS.O.BG₂ NS.O.κ eps' δ₃' NS.O.δ₁ δfl')
    (hGs : IsLevel Hs k)
    (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1)
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (NS.O.FkL τ) {p | ∃ D : BgData (NS.O.Gk τ) N,
      InUnionDomainC (NS.O.Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hEan : ∀ τ, AnalyticOnNhd ℂ (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
      (XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖(S.β : ℂ)⁻¹ * NS.O.Eτ τ r‖ ≤
        Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ)))
    (hEr : ∀ τ (Q : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 →
      ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
        (S.β : ℂ)⁻¹ * NS.O.Eτ τ (rotRaw (cmat Q) r) = (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
    -- the bounds of the recomputed activities and marks
    {εH κH κ' : ℝ} (hκH : κH ≤ 2 * κdec - 1)
    {F0 : ({Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) → ℝ}
    (hεz : 8 * (|S.β| * (6 * (1 / 2) * c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t
        (rho4 d L N NS.BG NS.κ)‖ / r ^ 3)) ≤ εH)
    (hεo : ∀ Y ∈ NS.𝒴C, corrU / a * (|S.β| * (∑ τ, if Y ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀
        (NS.O.jL τ) (NS.O.𝒦X τ) then 2 * (Eb τ * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL τ)
          (XL τ) - 2 * κdec * treeLenCov S.G' NS.O.m₀ Y)) else 0)) ≤
      εH * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y))
    (hFb : ∀ i, ‖(S.β : ℂ)‖ * 4 * ‖energyBdScaled d L N (compWeight L S.a₁) k
          (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t (rho4 d L N NS.BG NS.κ)‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) ≤ F0 (Sum.inl i))
    (hFo : ∀ q, |S.β| * (Eb q.1.1 * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL q.1.1)
        (XL q.1.1) - 2 * κdec * treeLenCov S.G' NS.O.m₀ q.1.2) / t₀) ≤
      F0 (Sum.inr q) * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2)))
    (hεpos : 0 < εH)
    (hι : Nonempty ({Y' // Y' ∈ bridgeFamily 1
      (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}))
    (hF0 : ∀ i, 0 < F0 i)
    (hκ' : 0 ≤ κ')
    (hκ : κ' + 3 * NS.Z.κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 +
      rootUnionK d L 1 m₁ NS.Z.κ0) + rootUnionK d L 1 m₁ NS.Z.κ0) ^ 3 * c1 d L *
      Real.exp ((κH - 2 * NS.Z.κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp NS.κ) < 1)
    -- the determinant part on the cast local set
    {c₃ : ℝ} (hS3 : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c₃ NS.BG)
    (hM3 : c₃ * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) (hc0 : xiC1 d * t ≤ bgC0 d L N)
    (hN1 : L ^ 1 ∣ N₁)
    -- the reference configuration and the polymer
    (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (hΦ₀ : ∀ b u, Φ₀ b u = 0)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hzT : rootCube (m₀ := 1) z ∈ T)
    {Yp' : Set (CTorus d L N₁' m₁' (k + 1))}
    (hmarg' : ∀ x ∈ sitesOf T, ∀ y : CTorus d L N₁ m₁ (k + 1), supDist x y ≤ 2 * L ^ (k + 1 + m₁') →
      y ∈ (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)).Ω (k + 1))
    {Ypl : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYpl : thickSet S.G' (sitesOf T) ⊆ Ypl)
    (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ)
    (he : ∀ θ ∈ physV S S.a₁ S.ν t, e θ T = NS.coeff θ T)
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩) :
    ∃ πb : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N
        (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)),
      (∀ r (h : r ∈ rawSub N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep))), πb
          r = ⟨r, h⟩) ∧
      ∃ cT : physParamBg N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) → ℂ, ∃ bT
          : ℝ, 0 ≤ bT ∧
        AnalyticOnNhd ℂ cT
            (physVBg N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) S.a₁ S.ν t) ∧
        (∀ θb ∈ physVBg N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) S.a₁ S.ν t,
            ‖cT θb‖ ≤ bT) ∧
        (∀ θb θb' : physParamBg N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)),
          (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
            XiCRaw (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) (compWeight L S.a₁) S.ν
                (k + 1) 1 εloc →
          (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
            XiCRaw (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) (compWeight L S.a₁) S.ν
                (k + 1) 1 εloc →
          θb.2 = 0 → θb'.2 = 0 →
          (∀ x ∈ Ypl, (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1 x =
              (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1 x ∧
            (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 x =
              (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 x) → cT θb = cT θb') ∧
        (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θb ∈ physVBg N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) S.a₁ S.ν t, ∀ θb'
              ∈ physVBg N (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) S.a₁ S.ν t,
          (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) =
            rotRaw (cmat Q) (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) → cT θb' = cT θb) ∧
        (∀ q : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N,
          Def6.XiDom S.G' (compWeight L S.a₁) S.ν (k + 1) ε q.1 q.2 →
          cT (πb (clipRaw (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) q), 0) = e
              (π (clipRaw S.G' q), 0) T) :=
  NS.clauses_castLocal_of_composed (hS1 := hS1) (SpG := SpG) (hc := hc) (hm := hm) (hsep := hsep)
    (hle := hle) (hεr := hεr) (hεt := hεt) (hεloc := hεloc) (hS := hS) (hCs := hCs) (hCs' := hCs')
    (hS2m := hS2m) (hM2m := hM2m) (hMXd := hMXd) (hCx := hCx) (hMXn := hMXn) (hδc := hδc)
    (hdm := hdm) (hα := hα) (hdm' := hdm') (hα' := hα') (hsm := hsm) (hcψ := hcψ) (hρ₀c := hρ₀c)
    (hρp := hρp) (hRu := hRu) (hBG₂ := hBG₂) (hκ₀ := hκ₀) (hκdec := hκdec) (hκκ := hκκ) (h1 := h1)
    (hlog := hlog) (hR₁ := hR₁) (hr := hr) (hrays := hrays) (hR := hR) (hRR := hRR) (hUR := hUR)
    (hU := hU) (hSL := hSL) (hCLs := hCLs) (hCLs' := hCLs') (hS2mL := hS2mL) (hM2mL := hM2mL)
    (hMXLd := hMXLd) (hMXLn := hMXLn) (hdmL := hdmL) (hαL := hαL) (hdmL' := hdmL') (hαL' := hαL')
    (hsmL := hsmL) (hcψL := hcψL) (hκκL := hκκL) (h1L := h1L) (hlogL := hlogL) (hρL := hρL)
    (hρcL := hρcL) (hρpL := hρpL) (hRuL := hRuL) (hca := hca) (haL := haL) (ht₀ := ht₀)
    (hRt := hRt) (hNm := hNm) (hcovL := hcovL) (hX₁L := hX₁L) (hoptL := hoptL) (hEb := hEb)
    (hb₁ := hb₁) (hbC := hbC) (hBo := hBo) (hFLo := hFLo) (hCN' := hCN') (hFN' := hFN')
    (hGs := hGs) (hrb := hrb) (hFkan := hFkan) (hEan := hEan) (hEr := hEr) (hκH := hκH)
    (hεz := hεz) (hεo := hεo) (hFb := hFb) (hFo := hFo) (hεpos := hεpos) (hι := hι) (hF0 := hF0)
    (hκ' := hκ') (hκ := hκ) (hε := hε) (hz := hz) (hS3 := hS3) (hM3 := hM3) (hc0 := hc0)
    (hN1 := hN1) (Φ₀ := Φ₀) (hΦ₀ := hΦ₀) (T := T) (hzT := hzT) (hmarg' := hmarg') (hYpl := hYpl)
    (e := e) (he := he) (π := π) (hπ := hπ)
    (hEbd := fun τ r hr => hEbd τ r (composedChart_subset_xiCRaw hr))

open Classical in
/-- (Core, with the bound of the old terms on their composed charts, `composedChart`.) **The family of the new level recomputed on the local generating sets** (route R-LOC, L5; the
forms `hfan`, `hfbd`, `hfloc`, `hfrot`, `hfval` of `newLabels_castInputs_of_localFamily` at the root
`z`).  For the coefficient `e` of the system `NS` on the step chart (`he`), supported on the
polymers rooted at `z` (`hsupp`), sets `Yp Y` whose cast local sets have every site within
`2 L^{k+1+m₁'}` of `sitesOf T` in their top layer for `Y = Y⁺(T)` (`hmarg`; `m₁ + 2 ≤ m₁'`)
and the class radius `ε_{k+1} = P.eps d L (k + 1) ≤ t`, under the hypotheses of
`clauses_castLocal_of` that do not concern the polymer, there are a family `f T` of the pair of
fields and bounds `b T` with (A1)–(A5) on the local generating sets
`castG hc (𝔹_{k+1}(Yp Y⁺(T)))`, `Y⁺(T) = sitesOf (piHull m₀ (thickSet S.G' (sitesOf T)))`. -/
theorem localFamily_castLocal_of_composed (hS1 : S.a₁ = 1)
    (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
    {N₁' m₁' : ℕ}
    [NeZero N₁']
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    (hm : m₁ + 2 ≤ m₁')
    (hsep : ϱ ≤ minSep L (L ^ m₁'))
    {P : Consts} (hNP : L ^ P.m₀ ∣ N₁)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁' m₁' (k + 1)))
    (hmarg : ∀ (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ)), ∀ x ∈ sitesOf T, ∀ y : CTorus d L N₁ m₁ (k + 1),
      supDist x y ≤ 2 * L ^ (k + 1 + m₁') →
      y ∈ (castG hc (localB (k + 1) (le_refl (k + 1))
        (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)).Ω (k + 1))
    {eps' : ℝ}
    (hle : t ≤ eps')
    (hεr : (2 * bgK1 d L N + 2) * xiC1 d * t ≤ eps')
    (hεt : P.eps d L (k + 1) ≤ t)
    {c c₂ : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c NS.BG)
    {ϱf : ℝ}
    {Hf : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱf}
    {Kc₀ Cx₀ c₂₀ : ℝ}
    (hCs : FlCore N S.G' Hf S.a₁ S.ν c NS.BG NS.κ t Kc₀ Cx₀ c₂₀ NS.BG₂ t)
    (hCs' : FlCore N S.G' Hf S.a₁ S.ν c NS.BG NS.κ eps' Kc₀ Cx₀ c₂₀ NS.BG₂ t)
    (hS2m : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂ NS.BG₂)
    (hM2m : c₂ * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hMXd : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hCx : 0 ≤ Cchi d L)
    (hMXn : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    {δc : ℝ}
    (hδc : 0 ≤ δc)
    (hdm : decDomMargin d L N NS.BG NS.κ (xiC1 d * t) < δc)
    (hα : K4 d L N NS.BG NS.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hdm' : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps') < δc)
    (hα' : K4 d L N NS.BG NS.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4)
    {cψ : ℝ}
    (hcψ : 0 ≤ cψ)
    (hρ₀c : 2 * NS.p₁ ≤ cψ)
    (hρp : S.p₁ ≤ NS.p₁)
    (hRu : corrU * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hBG₂ : 0 ≤ NS.BG₂)
    {κdec κ₀ : ℝ}
    (hκ₀ : 0 ≤ κ₀)
    (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.κ)
    (h1 : 1 ≤ (NS.κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (NS.κ / 2 - 1) / 2)
    {R₁ r : ℝ}
    (hR₁ : 1 < R₁)
    (hr : 0 < r)
    (hrays : (2 * R₁ + r) * NS.p₁ ≤ cψ)
    {R U : ℝ}
    (hR : 0 < R)
    (hRR : (R + R) * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hUR : 2 * U ≤ R)
    (hU : 17 / 16 ≤ U)
    {cL c₂L : ℝ}
    (hSL : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) cL NS.O.BG)
    {ϱfL : ℝ}
    {HfL : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱfL}
    {KcL₀ CxL₀ c₂L₀ : ℝ}
    (hCLs : FlCore N S.G' HfL S.a₁ S.ν cL NS.O.BG NS.O.κ t KcL₀ CxL₀ c₂L₀ NS.O.BG₂ NS.O.δ₁)
    (hCLs' : FlCore N S.G' HfL S.a₁ S.ν cL NS.O.BG NS.O.κ eps' KcL₀ CxL₀ c₂L₀ NS.O.BG₂ NS.O.δ₁)
    (hS2mL : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂L NS.O.BG₂)
    (hM2mL : c₂L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hMXLd : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hMXLn : cstarX d L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    {δcL : ℝ}
    (hdmL : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * t) < δcL)
    (hαL : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hdmL' : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * eps') < δcL)
    (hαL' : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4)
    {cψL : ℝ}
    (hcψL : 0 ≤ cψL)
    (hκκL : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.O.κ)
    (h1L : 1 ≤ (NS.O.κ / 2 - 1) / 2)
    (hlogL : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ NS.O.m₀) ^ d : ℕ) : ℝ)) ≤
      (NS.O.κ / 2 - 1) / 2)
    (hρL : 0 < NS.O.ρ)
    (hρcL : NS.O.ρ ≤ cψL)
    (hρpL : S.p₁ ≤ NS.O.ρ)
    (hRuL : corrU * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) <
      NS.O.δ₁)
    {a : ℝ} (hca : corrU ≤ a)
    (haL : a * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    {t₀ : ℝ}
    (ht₀ : 0 < t₀)
    (hRt : (corrU + t₀) *
      markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    (hNm : L ^ NS.O.m₀ ∣ N₁)
    {XL : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' NS.O.m₀ (NS.O.jL τ) (XL τ) (NS.O.𝒦X τ))
    (hX₁L : ∀ τ, (↑(NS.O.X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
    (hoptL : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) W₀ ∧
        bondCost (scaleW L NS.O.m₀ m₁ (NS.O.jL τ)) E₀ = treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ))
    {Eb : NS.O.ι → ℝ} (hEb : ∀ τ, 0 ≤ Eb τ) {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {r₀ δ₃ δfl δ₃' δfl' ϱs : ℝ} {X₀ : NS.O.ι → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hBo : ∀ τ, BgSetting N S.G' (NS.O.Gk τ) (NS.O.Gj τ) S.a₁ S.ν cL NS.O.BG NS.O.κ r₀ t δ₃
      (X₀ τ) (NS.O.X₁f τ) (NS.O.jL τ))
    {Hs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱs} {Kf Cf c₂f : ℝ}
    (hFLo : ∀ τ, FlSetting N S.G' (NS.O.Gk τ) Hs S.a₁ S.ν NS.O.κ NS.O.BG t δ₃ Kf Cf c₂f
      NS.O.BG₂ NS.O.δ₁ δfl (NS.O.X₁f τ))
    -- the numerical conditions of the settings of the old terms at the gate radius
    (hCN' : ChainNum d L N m₁ NS.O.BG NS.O.κ r₀ eps' δ₃')
    (hFN' : FlNum d L N NS.O.BG NS.O.BG₂ NS.O.κ eps' δ₃' NS.O.δ₁ δfl')
    (hGs : IsLevel Hs k)
    (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1)
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (NS.O.FkL τ) {p | ∃ D : BgData (NS.O.Gk τ) N,
      InUnionDomainC (NS.O.Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hEan : ∀ τ, AnalyticOnNhd ℂ (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
      (XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ composedChart (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖(S.β : ℂ)⁻¹ * NS.O.Eτ τ r‖ ≤
        Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ)))
    (hEr : ∀ τ (Q : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 →
      ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
        (S.β : ℂ)⁻¹ * NS.O.Eτ τ (rotRaw (cmat Q) r) = (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
    {εH κH κ' : ℝ} (hκH : κH ≤ 2 * κdec - 1)
    {F0 : ({Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) → ℝ}
    (hεz : 8 * (|S.β| * (6 * (1 / 2) * c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t
        (rho4 d L N NS.BG NS.κ)‖ / r ^ 3)) ≤ εH)
    (hεo : ∀ Y ∈ NS.𝒴C, corrU / a * (|S.β| * (∑ τ, if Y ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀
        (NS.O.jL τ) (NS.O.𝒦X τ) then 2 * (Eb τ * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL τ)
          (XL τ) - 2 * κdec * treeLenCov S.G' NS.O.m₀ Y)) else 0)) ≤
      εH * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y))
    (hFb : ∀ i, ‖(S.β : ℂ)‖ * 4 * ‖energyBdScaled d L N (compWeight L S.a₁) k
          (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t (rho4 d L N NS.BG NS.κ)‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) ≤ F0 (Sum.inl i))
    (hFo : ∀ q, |S.β| * (Eb q.1.1 * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL q.1.1)
        (XL q.1.1) - 2 * κdec * treeLenCov S.G' NS.O.m₀ q.1.2) / t₀) ≤
      F0 (Sum.inr q) * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2)))
    (hεpos : 0 < εH)
    (hι : Nonempty ({Y' // Y' ∈ bridgeFamily 1
      (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}))
    (hF0 : ∀ i, 0 < F0 i)
    (hκ' : 0 ≤ κ')
    (hκ : κ' + 3 * NS.Z.κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 +
      rootUnionK d L 1 m₁ NS.Z.κ0) + rootUnionK d L 1 m₁ NS.Z.κ0) ^ 3 * c1 d L *
      Real.exp ((κH - 2 * NS.Z.κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp NS.κ) < 1)
    {c₃ : ℝ}
    (hS3 : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c₃ NS.BG)
    (hM3 : c₃ * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hc0 : xiC1 d * t ≤ bgC0 d L N)
    (hN1 : L ^ 1 ∣ N₁)
    (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (hΦ₀ : ∀ b u, Φ₀ b u = 0)
    -- the coefficient of the system on the step chart, supported on the rooted polymers
    (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ)
    (he : ∀ θ ∈ physV S S.a₁ S.ν t, ∀ T, e θ T = NS.coeff θ T)
    (hsupp : ∀ θ T, e θ T ≠ 0 → rootCube (m₀ := 1) z ∈ T ∧ IsPolyDom 1 (k + 1) (sitesOf T))
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩) :
    ∃ (f : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N → ℂ)
      (b : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℝ),
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        AnalyticOnNhd ℂ (f T)
          {p | (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
            (castG hc (localB (k + 1) (le_refl (k + 1))
                (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2}) ∧
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        ∀ p : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N,
        (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
        ‖f T p‖ ≤ b T) ∧
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        ∀ p p' : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N,
        (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
          FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
        (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
          FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p'.1 p'.2 →
        (∀ x ∈ sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))), p.1 x = p'.1 x ∧ p.2 x = p'.2 x) →
        f T p = f T p') ∧
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
        ∀ p : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N,
        (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
        f T (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = f T p) ∧
      (∀ T (q : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N),
        Def6.XiDom S.G' S.a S.ν (k + 1) (P.eps d L (k + 1)) q.1 q.2 →
        f T q = e (π (clipRaw S.G' q), 0) T) := by
  classical
  have hYpl : ∀ T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ), thickSet S.G' (sitesOf T) ⊆ sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))) :=
    fun T => subset_sitesOf_piHull hNP _
  have hεloc : (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L (k + 1) ≤ eps' := by
    refine le_trans (mul_le_mul_of_nonneg_left hεt ?_) hεr
    have := one_le_xiC1 d
    have : 0 < bgK1 d L N := bgK1_pos d L N
    positivity
  -- the clauses of the recomputed coefficient, polymer by polymer
  have key : ∀ T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ), ∃ πb : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N
          (castG hc
          (localB (k + 1) (le_refl (k + 1))
          (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)),
      (∀ r (h : r ∈ rawSub N
          (castG hc
          (localB (k + 1) (le_refl (k + 1)) (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))))
          hsep))), πb r = ⟨r, h⟩) ∧
      ∃ cT : physParamBg N
          (castG hc
          (localB (k + 1) (le_refl (k + 1)) (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))))
          hsep)) → ℂ, ∃ bT : ℝ, 0 ≤ bT ∧
      (rootCube (m₀ := 1) z ∈ T →
        AnalyticOnNhd ℂ cT
            (physVBg N
            (castG hc
            (localB (k + 1) (le_refl (k + 1))
            (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) S.a₁ S.ν t) ∧
        (∀ θb ∈ physVBg N
            (castG hc
            (localB (k + 1) (le_refl (k + 1))
            (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) S.a₁ S.ν t,
            ‖cT θb‖ ≤ bT) ∧
        (∀ θb θb' : physParamBg N
            (castG hc
            (localB (k + 1) (le_refl (k + 1))
            (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)),
          (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
            XiCRaw (castG hc
                (localB (k + 1) (le_refl (k + 1))
                (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) (compWeight L S.a₁)
                S.ν (k + 1) 1
              ((2 * bgK1 d L N + 2) * xiC1 d * P.eps d L (k + 1)) →
          (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
            XiCRaw (castG hc
                (localB (k + 1) (le_refl (k + 1))
                (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) (compWeight L S.a₁)
                S.ν (k + 1) 1
              ((2 * bgK1 d L N + 2) * xiC1 d * P.eps d L (k + 1)) →
          θb.2 = 0 → θb'.2 = 0 →
          (∀ x ∈ sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))),
              (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1 x =
              (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1 x ∧
            (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 x =
              (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 x) → cT θb = cT θb') ∧
        (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θb ∈ physVBg N
              (castG hc
              (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) S.a₁ S.ν t, ∀ θb' ∈
              physVBg N
              (castG hc
              (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) S.a₁ S.ν t,
          (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) =
            rotRaw (cmat Q) (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) → cT θb' = cT θb) ∧
        (∀ q : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N,
          Def6.XiDom S.G' (compWeight L S.a₁) S.ν (k + 1) (P.eps d L (k + 1)) q.1 q.2 →
          cT (πb (clipRaw
              (castG hc
              (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) q), 0) = e
              (π (clipRaw S.G' q), 0) T)) := by
    intro T
    by_cases hzT : rootCube (m₀ := 1) z ∈ T
    · obtain ⟨πb, hπb, cT, bT, hbT, h1, h2, h3, h4, h5⟩ :=
        NS.clauses_castLocal_of_composed hS1 SpG hc hm hsep hle hεr hεt hεloc hS hCs hCs' hS2m hM2m hMXd hCx hMXn hδc
            hdm hα hdm' hα' hsm
          hcψ hρ₀c hρp hRu hBG₂ hκ₀ hκdec hκκ h1 hlog hR₁ hr hrays hR hRR hUR hU hSL hCLs hCLs'
          hS2mL hM2mL
          hMXLd hMXLn hdmL hαL hdmL' hαL' hsmL hcψL hκκL h1L hlogL hρL hρcL hρpL hRuL hca haL ht₀ hRt hNm
          hcovL hX₁L hoptL hEb hb₁ hbC hBo hFLo hCN' hFN' hGs hrb hFkan hEan hEbd hEr
          hκH hεz hεo hFb hFo hεpos hι hF0 hκ' hκ hε hz hS3 hM3 hc0 hN1 Φ₀ hΦ₀ T hzT (hmarg T)
          (hYpl T) e (fun θ hθ => he θ hθ T) π hπ
      exact ⟨πb, hπb, cT, bT, hbT, fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · obtain ⟨πb, hπb⟩ := exists_rawSub_proj (N := N)
        (castG hc
        (localB (k + 1) (le_refl (k + 1))
        (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep))
      exact ⟨πb, hπb, fun _ => 0, 0, le_rfl, fun h => absurd h hzT⟩
  choose πb hπb c b hb0 hcl using key
  obtain ⟨f, hf1, hf2, hf3, hf4, hf5⟩ := localFamily_of_coeff (S := S)
    (fun T => castG hc
        (localB (k + 1) (le_refl (k + 1))
        (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep))
    (fun T => sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))
        (fun T => rootCube (m₀ := 1) z ∈ T) πb hπb c hεt
    (fun T hg => (hcl T hg).1) b hb0 (fun T hg => (hcl T hg).2.1) (fun T hg => (hcl T hg).2.2.1)
    (fun T hg => (hcl T hg).2.2.2.1) e π (fun T hg => (hcl T hg).2.2.2.2)
    (fun T hg q _ => by
      by_contra h
      exact hg (hsupp _ T h).1)
  exact ⟨f, b, fun T _ => hf1 T, fun T _ => hf2 T, fun T _ => hf3 T, fun T _ => hf4 T, hf5⟩

open Classical in
/-- **The family of the new level recomputed on the local generating sets** (route R-LOC, L5; the
forms `hfan`, `hfbd`, `hfloc`, `hfrot`, `hfval` of `newLabels_castInputs_of_localFamily` at the root
`z`).  For the coefficient `e` of the system `NS` on the step chart (`he`), supported on the
polymers rooted at `z` (`hsupp`), sets `Yp Y` whose cast local sets have every site within
`2 L^{k+1+m₁'}` of `sitesOf T` in their top layer for `Y = Y⁺(T)` (`hmarg`; `m₁ + 2 ≤ m₁'`)
and the class radius `ε_{k+1} = P.eps d L (k + 1) ≤ t`, under the hypotheses of
`clauses_castLocal_of` that do not concern the polymer, there are a family `f T` of the pair of
fields and bounds `b T` with (A1)–(A5) on the local generating sets
`castG hc (𝔹_{k+1}(Yp Y⁺(T)))`, `Y⁺(T) = sitesOf (piHull m₀ (thickSet S.G' (sitesOf T)))`. The instance of `localFamily_castLocal_of_composed` with the bound on the whole chart. -/
theorem localFamily_castLocal_of (hS1 : S.a₁ = 1)
    (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
    {N₁' m₁' : ℕ}
    [NeZero N₁']
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    (hm : m₁ + 2 ≤ m₁')
    (hsep : ϱ ≤ minSep L (L ^ m₁'))
    {P : Consts} (hNP : L ^ P.m₀ ∣ N₁)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1)) → Set (CTorus d L N₁' m₁' (k + 1)))
    (hmarg : ∀ (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ)), ∀ x ∈ sitesOf T, ∀ y : CTorus d L N₁ m₁ (k + 1),
      supDist x y ≤ 2 * L ^ (k + 1 + m₁') →
      y ∈ (castG hc (localB (k + 1) (le_refl (k + 1))
        (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)).Ω (k + 1))
    {eps' : ℝ}
    (hle : t ≤ eps')
    (hεr : (2 * bgK1 d L N + 2) * xiC1 d * t ≤ eps')
    (hεt : P.eps d L (k + 1) ≤ t)
    {c c₂ : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c NS.BG)
    {ϱf : ℝ}
    {Hf : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱf}
    {Kc₀ Cx₀ c₂₀ : ℝ}
    (hCs : FlCore N S.G' Hf S.a₁ S.ν c NS.BG NS.κ t Kc₀ Cx₀ c₂₀ NS.BG₂ t)
    (hCs' : FlCore N S.G' Hf S.a₁ S.ν c NS.BG NS.κ eps' Kc₀ Cx₀ c₂₀ NS.BG₂ t)
    (hS2m : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂ NS.BG₂)
    (hM2m : c₂ * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hMXd : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hCx : 0 ≤ Cchi d L)
    (hMXn : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    {δc : ℝ}
    (hδc : 0 ≤ δc)
    (hdm : decDomMargin d L N NS.BG NS.κ (xiC1 d * t) < δc)
    (hα : K4 d L N NS.BG NS.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hdm' : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps') < δc)
    (hα' : K4 d L N NS.BG NS.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4)
    {cψ : ℝ}
    (hcψ : 0 ≤ cψ)
    (hρ₀c : 2 * NS.p₁ ≤ cψ)
    (hρp : S.p₁ ≤ NS.p₁)
    (hRu : corrU * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hBG₂ : 0 ≤ NS.BG₂)
    {κdec κ₀ : ℝ}
    (hκ₀ : 0 ≤ κ₀)
    (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.κ)
    (h1 : 1 ≤ (NS.κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (NS.κ / 2 - 1) / 2)
    {R₁ r : ℝ}
    (hR₁ : 1 < R₁)
    (hr : 0 < r)
    (hrays : (2 * R₁ + r) * NS.p₁ ≤ cψ)
    {R U : ℝ}
    (hR : 0 < R)
    (hRR : (R + R) * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hUR : 2 * U ≤ R)
    (hU : 17 / 16 ≤ U)
    {cL c₂L : ℝ}
    (hSL : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) cL NS.O.BG)
    {ϱfL : ℝ}
    {HfL : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱfL}
    {KcL₀ CxL₀ c₂L₀ : ℝ}
    (hCLs : FlCore N S.G' HfL S.a₁ S.ν cL NS.O.BG NS.O.κ t KcL₀ CxL₀ c₂L₀ NS.O.BG₂ NS.O.δ₁)
    (hCLs' : FlCore N S.G' HfL S.a₁ S.ν cL NS.O.BG NS.O.κ eps' KcL₀ CxL₀ c₂L₀ NS.O.BG₂ NS.O.δ₁)
    (hS2mL : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂L NS.O.BG₂)
    (hM2mL : c₂L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hMXLd : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hMXLn : cstarX d L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    {δcL : ℝ}
    (hdmL : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * t) < δcL)
    (hαL : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hdmL' : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * eps') < δcL)
    (hαL' : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4)
    {cψL : ℝ}
    (hcψL : 0 ≤ cψL)
    (hκκL : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.O.κ)
    (h1L : 1 ≤ (NS.O.κ / 2 - 1) / 2)
    (hlogL : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ NS.O.m₀) ^ d : ℕ) : ℝ)) ≤
      (NS.O.κ / 2 - 1) / 2)
    (hρL : 0 < NS.O.ρ)
    (hρcL : NS.O.ρ ≤ cψL)
    (hρpL : S.p₁ ≤ NS.O.ρ)
    (hRuL : corrU * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) <
      NS.O.δ₁)
    {a : ℝ} (hca : corrU ≤ a)
    (haL : a * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    {t₀ : ℝ}
    (ht₀ : 0 < t₀)
    (hRt : (corrU + t₀) *
      markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    (hNm : L ^ NS.O.m₀ ∣ N₁)
    {XL : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' NS.O.m₀ (NS.O.jL τ) (XL τ) (NS.O.𝒦X τ))
    (hX₁L : ∀ τ, (↑(NS.O.X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
    (hoptL : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) W₀ ∧
        bondCost (scaleW L NS.O.m₀ m₁ (NS.O.jL τ)) E₀ = treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ))
    {Eb : NS.O.ι → ℝ} (hEb : ∀ τ, 0 ≤ Eb τ) {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {r₀ δ₃ δfl δ₃' δfl' ϱs : ℝ} {X₀ : NS.O.ι → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hBo : ∀ τ, BgSetting N S.G' (NS.O.Gk τ) (NS.O.Gj τ) S.a₁ S.ν cL NS.O.BG NS.O.κ r₀ t δ₃
      (X₀ τ) (NS.O.X₁f τ) (NS.O.jL τ))
    {Hs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱs} {Kf Cf c₂f : ℝ}
    (hFLo : ∀ τ, FlSetting N S.G' (NS.O.Gk τ) Hs S.a₁ S.ν NS.O.κ NS.O.BG t δ₃ Kf Cf c₂f
      NS.O.BG₂ NS.O.δ₁ δfl (NS.O.X₁f τ))
    -- the numerical conditions of the settings of the old terms at the gate radius
    (hCN' : ChainNum d L N m₁ NS.O.BG NS.O.κ r₀ eps' δ₃')
    (hFN' : FlNum d L N NS.O.BG NS.O.BG₂ NS.O.κ eps' δ₃' NS.O.δ₁ δfl')
    (hGs : IsLevel Hs k)
    (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1)
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (NS.O.FkL τ) {p | ∃ D : BgData (NS.O.Gk τ) N,
      InUnionDomainC (NS.O.Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hEan : ∀ τ, AnalyticOnNhd ℂ (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
      (XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖(S.β : ℂ)⁻¹ * NS.O.Eτ τ r‖ ≤
        Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ)))
    (hEr : ∀ τ (Q : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 →
      ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
        (S.β : ℂ)⁻¹ * NS.O.Eτ τ (rotRaw (cmat Q) r) = (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
    {εH κH κ' : ℝ} (hκH : κH ≤ 2 * κdec - 1)
    {F0 : ({Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) → ℝ}
    (hεz : 8 * (|S.β| * (6 * (1 / 2) * c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t
        (rho4 d L N NS.BG NS.κ)‖ / r ^ 3)) ≤ εH)
    (hεo : ∀ Y ∈ NS.𝒴C, corrU / a * (|S.β| * (∑ τ, if Y ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀
        (NS.O.jL τ) (NS.O.𝒦X τ) then 2 * (Eb τ * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL τ)
          (XL τ) - 2 * κdec * treeLenCov S.G' NS.O.m₀ Y)) else 0)) ≤
      εH * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y))
    (hFb : ∀ i, ‖(S.β : ℂ)‖ * 4 * ‖energyBdScaled d L N (compWeight L S.a₁) k
          (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t (rho4 d L N NS.BG NS.κ)‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) ≤ F0 (Sum.inl i))
    (hFo : ∀ q, |S.β| * (Eb q.1.1 * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL q.1.1)
        (XL q.1.1) - 2 * κdec * treeLenCov S.G' NS.O.m₀ q.1.2) / t₀) ≤
      F0 (Sum.inr q) * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2)))
    (hεpos : 0 < εH)
    (hι : Nonempty ({Y' // Y' ∈ bridgeFamily 1
      (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}))
    (hF0 : ∀ i, 0 < F0 i)
    (hκ' : 0 ≤ κ')
    (hκ : κ' + 3 * NS.Z.κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 +
      rootUnionK d L 1 m₁ NS.Z.κ0) + rootUnionK d L 1 m₁ NS.Z.κ0) ^ 3 * c1 d L *
      Real.exp ((κH - 2 * NS.Z.κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp NS.κ) < 1)
    {c₃ : ℝ}
    (hS3 : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c₃ NS.BG)
    (hM3 : c₃ * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hc0 : xiC1 d * t ≤ bgC0 d L N)
    (hN1 : L ^ 1 ∣ N₁)
    (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (hΦ₀ : ∀ b u, Φ₀ b u = 0)
    -- the coefficient of the system on the step chart, supported on the rooted polymers
    (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ)
    (he : ∀ θ ∈ physV S S.a₁ S.ν t, ∀ T, e θ T = NS.coeff θ T)
    (hsupp : ∀ θ T, e θ T ≠ 0 → rootCube (m₀ := 1) z ∈ T ∧ IsPolyDom 1 (k + 1) (sitesOf T))
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩) :
    ∃ (f : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N → ℂ)
      (b : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℝ),
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        AnalyticOnNhd ℂ (f T)
          {p | (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
            (castG hc (localB (k + 1) (le_refl (k + 1))
                (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2}) ∧
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        ∀ p : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N,
        (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
        ‖f T p‖ ≤ b T) ∧
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        ∀ p p' : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N,
        (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
          FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
        (xiFieldDom S.a S.ν (fun j => (2 * bgK1 d L N + 2) * xiC1 d * P.eps d L j) :
          FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p'.1 p'.2 →
        (∀ x ∈ sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))), p.1 x = p'.1 x ∧ p.2 x = p'.2 x) →
        f T p = f T p') ∧
      (∀ T, IsPolyDom P.m₀ (k + 1) (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T)))) →
        ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
        ∀ p : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N,
        (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
          (castG hc (localB (k + 1) (le_refl (k + 1))
              (Yp (sitesOf (piHull P.m₀ (thickSet S.G' (sitesOf T))))) hsep)) p.1 p.2 →
        f T (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = f T p) ∧
      (∀ T (q : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N),
        Def6.XiDom S.G' S.a S.ν (k + 1) (P.eps d L (k + 1)) q.1 q.2 →
        f T q = e (π (clipRaw S.G' q), 0) T) :=
  NS.localFamily_castLocal_of_composed (hS1 := hS1) (SpG := SpG) (hc := hc) (hm := hm)
    (hsep := hsep) (hNP := hNP) (Yp := Yp) (hmarg := hmarg) (hle := hle) (hεr := hεr) (hεt := hεt)
    (hS := hS) (hCs := hCs) (hCs' := hCs') (hS2m := hS2m) (hM2m := hM2m) (hMXd := hMXd)
    (hCx := hCx) (hMXn := hMXn) (hδc := hδc) (hdm := hdm) (hα := hα) (hdm' := hdm') (hα' := hα')
    (hsm := hsm) (hcψ := hcψ) (hρ₀c := hρ₀c) (hρp := hρp) (hRu := hRu) (hBG₂ := hBG₂) (hκ₀ := hκ₀)
    (hκdec := hκdec) (hκκ := hκκ) (h1 := h1) (hlog := hlog) (hR₁ := hR₁) (hr := hr)
    (hrays := hrays) (hR := hR) (hRR := hRR) (hUR := hUR) (hU := hU) (hSL := hSL) (hCLs := hCLs)
    (hCLs' := hCLs') (hS2mL := hS2mL) (hM2mL := hM2mL) (hMXLd := hMXLd) (hMXLn := hMXLn)
    (hdmL := hdmL) (hαL := hαL) (hdmL' := hdmL') (hαL' := hαL') (hsmL := hsmL) (hcψL := hcψL)
    (hκκL := hκκL) (h1L := h1L) (hlogL := hlogL) (hρL := hρL) (hρcL := hρcL) (hρpL := hρpL)
    (hRuL := hRuL) (hca := hca) (haL := haL) (ht₀ := ht₀) (hRt := hRt) (hNm := hNm)
    (hcovL := hcovL) (hX₁L := hX₁L) (hoptL := hoptL) (hEb := hEb) (hb₁ := hb₁) (hbC := hbC)
    (hBo := hBo) (hFLo := hFLo) (hCN' := hCN') (hFN' := hFN') (hGs := hGs) (hrb := hrb)
    (hFkan := hFkan) (hEan := hEan) (hEr := hEr) (hκH := hκH) (hεz := hεz) (hεo := hεo)
    (hFb := hFb) (hFo := hFo) (hεpos := hεpos) (hι := hι) (hF0 := hF0) (hκ' := hκ') (hκ := hκ)
    (hε := hε) (hz := hz) (hS3 := hS3) (hM3 := hM3) (hc0 := hc0) (hN1 := hN1) (Φ₀ := Φ₀)
    (hΦ₀ := hΦ₀) (e := e) (he := he) (hsupp := hsupp) (π := π) (hπ := hπ)
    (hEbd := fun τ r hr => hEbd τ r (composedChart_subset_xiCRaw hr))

end NewLevelSystem

end Balaban.Inhabited
