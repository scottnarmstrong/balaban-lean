/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairReplacementLocalB
public import Balaban.Localization.DecCovCross
public import Balaban.Localization.LocalHatIntegral
public import Balaban.Fluctuation.HatEngineFan

/-!
# The hat variable at the local generating set

P3 (4.22)-(4.24) and (4.46): the fluctuation variable of a term is `ψ' = β^{-1/2} C^{1/2}(s) ψ`, with
the decoupled square root `C^{1/2}(s)` of the generating set on which the term is computed.  The
ambient term uses the ambient hat lift `hatPsiF` (the square root of the cover of the level set
`𝔹_{k+1}` at the ambient decoupled background and the parameters `σ w = extParams 𝔹_{k+1} X₁ w`);
the term recomputed on `𝔹_{k+1}(Y) = localB (k + 1) … Y` uses the local hat lift: the square root of
the cover of `𝔹_{k+1}(Y)` at the local decoupled background (of the local datum `D'`) and the
transported parameters `τ w`, applied to the restriction of the hat variable `ψ̂` to the unit lattice
of `𝔹_{k+1}(Y)`, extended by zero off its unit blocks.

* `Dec2.hRespects_of_core_near`: the proviso `HRespects` of `decCovSqrt_block_cross` for a set `T`
  containing the `L^{k+1}`-neighbourhood of the core (a non-zero matrix element of `H_{k,x}` joins
  nearest neighbours or two sites of one block of the layer of the row);
* `level_core_mem_of_active`, `localB_core_mem_of_active`: the cores of the active cubes (ambient
  and local) lie in the read region `R`;
* `localHatLift_eq_hatPsiF_localB`: the instance of `Dec2.localLift_eq_liftC_on_component` at
  `(coverOf 𝔹_{k+1}, 𝔹_{k+1})` versus `(coverOf 𝔹_{k+1}(Y), 𝔹_{k+1}(Y))`: at every site within
  `L^{k+1}` of `R` the local hat lift equals the ambient hat lift, under the margin of
  `coef_eTermFun_replacement_localB` (`T` is the union of the `(k+1)`-blocks meeting the
  `L^{k+1}`-neighbourhood of `R`; the backgrounds agree on `T` by `Dec2.decBg_value_cross`);
* `eTermFun_level_hat_congr`: the old term of the ambient pair reads its fluctuation variable only
  within `L^{k+1}` of `R` (`Dec2.decSol_value_cross` for the ambient fluctuation pair with itself).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.Fluctuation Matrix

/-! ### The proviso `HRespects` near the core -/

section Respects

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **The proviso `HRespects` from a neighbourhood of the core.**  If `T` contains every site within
sup-distance `L^{k+1}` of the core `Core(C, s)`, then no non-zero matrix element of the x-shifted
Dirichlet operator of `H` joins a site of the core to a site off `T`: such an element joins nearest
neighbours or two sites of one block of the layer of the row (`xDirichlet_ne_zero_near`), at
sup-distance at most `L^{k+1}`. -/
theorem Dec2.hRespects_of_core_near {C : DecCover d L N₁ m₁ (k + 1)}
    {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (a : ℕ → ℝ) (aT x ν : ℝ) (α : H.Ω 1 → ℂ)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hT : ∀ y' ∈ Dec2.Core C s, ∀ y : CTorus d L N₁ m₁ (k + 1), supDist y' y ≤ L ^ (k + 1) →
      y ∈ T) :
    Dec2.HRespects C H a aT x ν α s T := by
  intro y y' hne hcore
  have hL1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hy' : (y' : CTorus d L N₁ m₁ (k + 1)) ∈ T :=
    hT _ hcore _ (by rw [supDist_self]; exact Nat.zero_le _)
  by_cases hyy : y = y'
  · rw [hyy]
  have hd : supDist (y' : CTorus d L N₁ m₁ (k + 1)) (y : CTorus d L N₁ m₁ (k + 1)) ≤
      L ^ (k + 1) := by
    rcases xDirichlet_ne_zero_near hyy hne with ⟨μ, h | h⟩ | h
    · rw [h, supDist_comm]
      exact (supDist_add_single_le _ μ).trans hL1
    · rw [h]
      exact (supDist_add_single_le _ μ).trans hL1
    · exact (supDist_le_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _) h.symm).trans
        (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L))
          (layerIndex_le_of_Ω_empty H H.top _))
  exact iff_of_true (hT _ hcore _ hd) hy'

end Respects

/-! ### The cores of the active cubes -/

section Cores

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **The core of the ambient cover lies in the read region**: a site of the core of an active
cube of the cover of the level set `𝔹_{k+1}` (parameters `extParams 𝔹_{k+1} X₁ w`, `w` supported
on `𝒞`) lies in `R`. -/
theorem level_core_mem_of_active (hG' : IsLevel Gp (k + 1)) (hm₁ : 2 ≤ m₁)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {C : Finset (ParIdx Gp X₁)}
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    {w : ParIdx Gp X₁ → ℂ} (hw : w ∈ supportedOn C) {y : CTorus d L N₁ m₁ (k + 1)}
    (hy : y ∈ Dec2.Core (coverOf Gp) (Dec2.extS (coverOf Gp) (extParams Gp X₁ w))) : y ∈ R := by
  classical
  simp only [Dec2.Core, Dec2.Zs, Finset.mem_biUnion, Finset.mem_filter] at hy
  obtain ⟨z, ⟨-, hne⟩, hyz⟩ := hy
  exact level_intBox_subset_of_active hG' hm₁ hRC hRX hw hne (coreBox_subset_box hyz)

/-- **The core of the local cover lies in the read region**: with the transported parameters `τ w`
(the ambient parameters at the cubes with base in the top layer of `𝔹_{k+1}(Y)`, `0` at the
others), every active cube of the cover of `𝔹_{k+1}(Y)` is an active ambient cube
(`level_localB_active_cross`), so its core lies in `R`. -/
theorem localB_core_mem_of_active (hG' : IsLevel Gp (k + 1)) (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {C : Finset (ParIdx Gp X₁)}
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    {w : ParIdx Gp X₁ → ℂ} (hw : w ∈ supportedOn C) {y : CTorus d L N₁ m₁ (k + 1)}
    (hy : y ∈ Dec2.Core (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
      (Dec2.extS (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
        (fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
          then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0))) : y ∈ R := by
  classical
  simp only [Dec2.Core, Dec2.Zs, Finset.mem_biUnion, Finset.mem_filter] at hy
  obtain ⟨z, ⟨hz, hne⟩, hyz⟩ := hy
  have hs'0 := localB_tau_off_top hk Y (le_refl (minSep L (L ^ m₁))) (extParams Gp X₁ w)
  obtain ⟨-, heq, -⟩ := level_localB_active_cross (H' := localB (k + 1) hk Y
    (le_refl (minSep L (L ^ m₁)))) hG' hk1 hk Y (le_refl (minSep L (L ^ m₁)))
    (fun x hx => (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω_antitone le_rfl hk1
      (by omega) hx) hs'0
    (localB_hat_of_active (Gp := Gp) hk1 hk Y (le_refl (minSep L (L ^ m₁))) hm₁ hM hs'0)
    (localB_tau_top hG' hk Y (le_refl (minSep L (L ^ m₁))) (extParams Gp X₁ w)) hz hne
  exact level_intBox_subset_of_active hG' hm₁ hRC hRX hw (by rw [heq]; exact hne)
    (coreBox_subset_box hyz)

end Cores

/-! ### The local hat lift equals the ambient hat lift near the read region -/

section HatLift

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {ν : ℝ}

/-- **The local hat lift equals the ambient hat lift near the read region (P3 (4.22)-(4.24) at
`𝔹_{k+1}(Y)`).**  Let `𝔹_{k+1}` be a level set (`k ≥ 1`), `𝔹_{k+1}(Y) = localB (k + 1) … Y`, `R` a
read region with the margin of `coef_eTermFun_replacement_localB` (every site within
`2 M₁ L^{k+1}` of `R` has its `𝒞_{k+1}`-cube in `Y`), and `w` supported on the family `𝒞` with
`|σ w| < e^κ`, `σ w = extParams 𝔹_{k+1} X₁ w`; let `τ w` be the transported parameters.  Let `D` be
a datum of the chart `Ξ^c(𝔹_{k+1}; 1, ε)` and `D'` a datum of `Ξ^c(𝔹_{k+1}(Y); 1, ε')` agreeing with
`D` on the top layer of `𝔹_{k+1}(Y)`, and `F₁`, `F₁'` the decoupled background maps of the two
pairs.  Then at every site `x₀` within `L^{k+1}` of `R` the local hat lift
`cc C'^{1/2}(τ w) ψ̂'` (the square root of the cover of `𝔹_{k+1}(Y)` at the local background, `ψ̂'`
the restriction of `ψ̂` to the unit lattice of `𝔹_{k+1}(Y)`, extended by zero off its unit blocks)
equals the ambient hat lift `hatPsiF` at `σ w`. -/
theorem localHatLift_eq_hatPsiF_localB (hG' : IsLevel Gp (k + 1)) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) {κ : ℝ} (hκ : 0 < κ)
    (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ)
          s D φ α → F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {eps eps' δc : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (heps' : 0 < eps') (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1)
    (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {D' : BgData (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) N}
    (hD'x : XiCData (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
      (k + 1) 1 eps' D')
    (hD' : ∀ x ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1),
      D'.Ψ x = D.Ψ x ∧ D'.h x = D.h x)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {C : Finset (ParIdx Gp X₁)}
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1))
    {w : ParIdx Gp X₁ → ℂ} (hw : w ∈ supportedOn C)
    (hsw : ∀ P, ‖extParams Gp X₁ w P‖ < Real.exp κ) (cc : ℂ) (ψh : unitPts Gp × Fin N → ℂ)
    {x₀ : CTorus d L N₁ m₁ (k + 1)} (hx₀ : ∃ x ∈ R, supDist x x₀ ≤ L ^ (k + 1)) (i : Fin N) :
    (if h : unitBlock x₀ ∈ unitPts (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) then
      (cc • (decCovSqrt (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) a₁ ν
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D')).2
        (Dec2.extS (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
          (fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0))
        (barField (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) D'.Ψ
          (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D')).1)
        (unitQ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
        (unitP (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) *ᵥ
        (fun p => if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0)))
        (⟨unitBlock x₀, h⟩, i)
      else 0) =
    hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp X₁ w) (rawOf D) ψh x₀ i := by
  classical
  obtain ⟨x₁, hx₁R, hx₁⟩ := hx₀
  -- the cover bases, the data domains, the parameters
  obtain ⟨Sb, Sb', -, -⟩ := localB_replacement_coverBases hG' Gp hk Y hN hm₁ hM HB hag hag hagl
  have hd0 : 0 < d := by have := HB.hd; omega
  have hxi := one_le_xiC1 d
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hM2 : 2 ≤ L ^ m₁ := by nlinarith [Nat.one_le_pow 2 L hL1]
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ0' : 0 < xiC1 d * eps' := by positivity
  have hDd : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D := by
    have hc1 : xiC1 d * eps ≤ bgC1 d L N := hc7.trans (c7_le_bgC1 d L N BG κ)
    exact inUnionDomainC_of_inDomainC HB hδ0 (hc1.trans (bgC1_le_bgC0 d L N hd0)) hc7
      (xiCData_inDomainC HB hsmall hD)
  have hDd' : InUnionDomainC (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
      (c7 d L N BG κ) ν D' := by
    have hc1 : xiC1 d * eps' ≤ bgC1 d L N := hc7'.trans (c7_le_bgC1 d L N BG κ)
    exact inUnionDomainC_of_inDomainC HB' hδ0' (hc1.trans (bgC1_le_bgC0 d L N hd0)) hc7'
      (xiCData_inDomainC HB' hsmall' hD'x)
  have hs'0 := localB_tau_off_top hk Y (le_refl (minSep L (L ^ m₁))) (extParams Gp X₁ w)
  have hsτ := localB_tau_top hG' hk Y (le_refl (minSep L (L ^ m₁))) (extParams Gp X₁ w)
  have hhat := localB_hat_of_active (Gp := Gp) hk1 hk Y (le_refl (minSep L (L ^ m₁))) hm₁ hM hs'0
  have hsτn := localB_tau_norm_lt hk Y (le_refl (minSep L (L ^ m₁))) hsw hE1
  -- the backgrounds of the two pairs
  obtain ⟨φ, α, hI, -, -⟩ := coverBg_exists hS Sb HB hκ.le hMc heps hsmall hc7 hsw hD
  have hFe : F₁ (extParams Gp X₁ w, rawOf D) = (φ, α) :=
    hF₁ _ D hsw hDd φ α ⟨hI.small, hI.fixed, hI.field⟩
  obtain ⟨φ', α', hI', -, -⟩ := coverBg_exists hS Sb' HB' hκ.le hMc heps' hsmall' hc7'
    (s := fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
      then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0) hsτn hD'x
  have hFe' : F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω
      (k + 1) then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D') =
      (φ', α') := hF₁' _ D' hsτn hDd' φ' α' ⟨hI'.small, hI'.fixed, hI'.field⟩
  have hdom := decDom_of_coverBg hS Sb HB hκ.le hMc heps hsmall hc7 hphi hsw hD hI hmarD hαD
  have hdom' := decDom_of_coverBg hS Sb' HB' hκ.le hMc heps' hsmall' hc7' hphi' hsτn hD'x hI'
    hmarD' hαD'
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      have : 0 < K4 d L N BG κ := K4_pos hS.fam.2.1 hd0
      unfold decDomMargin; positivity
    linarith
  have SX : Dec2.XCover (coverOf Gp) Gp (compWeight L a₁) a₁ ν (Cchi d L) :=
    ⟨Sb.toCoverGeom, (Sb.weights k hk1 (by omega)).1, (Sb.weights k hk1 (by omega)).2, ha₁, ha₂⟩
  have SX' : Dec2.XCover (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
      (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) a₁ ν (Cchi d L) :=
    ⟨Sb'.toCoverGeom, (Sb'.weights k hk1 (by omega)).1, (Sb'.weights k hk1 (by omega)).2, ha₁, ha₂⟩
  -- the sets `T` (block union) and `Y_b`
  obtain ⟨T, hT⟩ : ∃ T : Finset (CTorus d L N₁ m₁ (k + 1)), ∀ y, y ∈ T ↔ ∃ x ∈ R,
      ∃ z, jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) z =
        jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y ∧ supDist x z ≤ L ^ (k + 1) :=
    ⟨Finset.univ.filter fun y => ∃ x ∈ R, ∃ z, jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) z =
        jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y ∧ supDist x z ≤ L ^ (k + 1),
      fun y => by simp⟩
  obtain ⟨Yb, hYb⟩ : ∃ Yb : Finset (CTorus d L N₁ m₁ (k + 1)), ∀ y, y ∈ Yb ↔ ∃ x ∈ R,
      supDist x y ≤ 3 * L ^ (k + 1) :=
    ⟨Finset.univ.filter fun y => ∃ x ∈ R, supDist x y ≤ 3 * L ^ (k + 1), fun y => by simp⟩
  have hRT1 : ∀ x ∈ R, ∀ y, supDist x y ≤ L ^ (k + 1) → y ∈ T := fun x hx y h =>
    (hT y).2 ⟨x, hx, y, rfl, h⟩
  have hRT : ∀ x ∈ R, x ∈ T := fun x hx =>
    hRT1 x hx x (by rw [supDist_self]; exact Nat.zero_le _)
  have hTR : ∀ y ∈ T, ∃ x ∈ R, supDist x y ≤ 2 * L ^ (k + 1) := by
    intro y hy
    obtain ⟨x, hx, z, hz, hd⟩ := (hT y).1 hy
    have hzy : supDist z y ≤ L ^ (k + 1) :=
      supDist_le_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
        (sameCell_of_jBlock_eq le_rfl hz)
    exact ⟨x, hx, (supDist_triangle x z y).trans (by omega)⟩
  have hTblk : IsBlockUnion L (N₁ * L ^ m₁) (k + 1) (k + 1) T := by
    intro y y' hyy'
    rw [hT, hT]
    constructor
    · rintro ⟨x, hx, z, hz, hd⟩; exact ⟨x, hx, z, hz.trans hyy', hd⟩
    · rintro ⟨x, hx, z, hz, hd⟩; exact ⟨x, hx, z, hz.trans hyy'.symm, hd⟩
  have hTYb : T ⊆ Yb := fun y hy => by
    obtain ⟨x, hx, hd⟩ := hTR y hy
    exact (hYb y).2 ⟨x, hx, by omega⟩
  have h3 : 3 * L ^ (k + 1) ≤ L ^ (k + 1 + m₁) := by
    rw [pow_add L (k + 1) m₁]
    have : 3 ≤ L ^ m₁ := by nlinarith [Nat.one_le_pow 2 L hL1]
    calc 3 * L ^ (k + 1) = L ^ (k + 1) * 3 := by ring
      _ ≤ L ^ (k + 1) * L ^ m₁ := Nat.mul_le_mul_left _ this
  have hYR : ∀ y ∈ Yb, ∃ x ∈ R, supDist x y ≤ L ^ (k + 1 + m₁) := fun y hy => by
    obtain ⟨x, hx, hd⟩ := (hYb y).1 hy
    exact ⟨x, hx, hd.trans h3⟩
  have htop : ∀ y ∈ Yb, y ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) :=
    fun y hy => localB_top_of_mem hk Y _ hmar hYR hy
  have hstb := fun y (hy : y ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)) =>
    level_localB_layer_iff_of_top hG' hk Y (le_refl (minSep L (L ^ m₁))) hy
  have hHb : ∀ x, x ∈ Gp.Ω 1 := fun x => (hG' x).1
  have hH'b : ∀ x ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k,
      x ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 := fun x hx =>
    (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω_antitone le_rfl hk1 (by omega) hx
  have hΩ1 : ∀ y ∈ Yb, y ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 :=
    fun y hy => (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω_antitone le_rfl
      (by omega) (by omega) (htop y hy)
  -- the component hypotheses for `T`
  have hdich : ∀ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (extParams Gp X₁ w)) q ≠ 0 →
        SubI Gp (intBox q) T ∨ DisjI Gp (intBox q) T := fun q _ hne =>
    Or.inl fun x hx => hRT _ (level_intBox_subset_of_active hG' hm₁ hRC hRX hw hne hx)
  have hdich' := level_localB_dich_cross hG' hk1 hk Y _ hHb hH'b hs'0 hhat hsτ hdich
  have hrowb : ∀ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (extParams Gp X₁ w)) q ≠ 0 →
        ∀ x ∈ Yb, x ∈ intBox q → x ∈ T := fun q _ hne x _ hx =>
    hRT _ (level_intBox_subset_of_active hG' hm₁ hRC hRX hw hne hx)
  have hrowb' := level_localB_row_cross hG' hk1 hk Y _ hs'0 hhat hsτ hrowb
  have hin := level_localB_inner_cross hG' hk Y _ hHb (T := T) (fun q hq hne =>
    localB_depth_deep hG' hm₁ hk Y _ hRC hRX hmar hstb hw q
      (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hq).1, fun x hx =>
        level_intBox_subset_of_active hG' hm₁ hRC hRX hw hne hx⟩) hne) hsτ
  have hin' := level_localB_inner_cross' (H := Gp) hG' hk1 hk Y _ hH'b (T := T) hs'0 hhat hsτ
  have hresb : ∀ x ∈ T, x ∈ Gp.Ω 1 → ∀ y ∈ resSites Gp x, y ∈ Gp.Ω 1 ∧ y ∈ Yb := by
    intro x hx _ y hy
    obtain ⟨x', hx', hd⟩ := hTR x hx
    have := supDist_le_of_mem_resSites hy
    exact ⟨hHb y, (hYb y).2 ⟨x', hx', (supDist_triangle x' x y).trans (by omega)⟩⟩
  -- the background comparison on `T`
  obtain ⟨hbα, hbφ⟩ := Dec2.decBg_value_cross hS Sb Sb' HB HB' hκ.le hMc hF₁ hF₁' hsw hsτn hDd
    hDd' hTYb (fun y hy => hstb y (htop y hy)) hdich hdich' hrowb hrowb' hin hin' hresb
    (localB_depth_act hG' hM2 hk Y _ hmar hYR)
    (fun y hy _ z hz => by
      have ht := localB_depth_approxDep (Gp := Gp) hM2 hk Y _ hmar hYR y hy z hz
      exact ⟨(hD' z ht).1.symm, (hD' z ht).2.symm⟩)
  rw [hFe, hFe'] at hbα hbφ
  -- the standing hypotheses of the covariances
  have hXD : ∀ x : ℝ, 0 < x → Dec2.XData (coverOf Gp) Gp (compWeight L a₁) a₁ ν x α κ
      (extS Gp (extParams Gp X₁ w)) (Cchi d L) := fun x hx =>
    xData_cover_of_mem SX (Cchi_nonneg d L) hx.le hκ.le hMX hdom
  have hXD' : ∀ x : ℝ, 0 < x → Dec2.XData
      (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
      (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) a₁ ν x α' κ
      (extS (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))
        (fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
          then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0)) (Cchi d L) :=
    fun x hx => xData_cover_of_mem SX' (Cchi_nonneg d L) hx.le hκ.le hMX hdom'
  have key := Dec2.localLift_eq_liftC_on_component (T := T) (α := α) (α' := α')
    (s := Dec2.extS (coverOf Gp) (extParams Gp X₁ w))
    (s' := Dec2.extS (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
      (fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
        then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0))
    (φ := barField Gp D.Ψ φ)
    (φ' := barField (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) D'.Ψ φ') hG' SX SX'
    (fun v => (hdom.2.2 v).le) (fun v => (hdom'.2.2 v).le)
    (fun y hy => hstb y (htop y (hTYb hy)))
    (fun x hx => (hXD x hx).isUnit_one_sub) (fun x hx => (hXD' x hx).isUnit_one_sub)
    hdich hdich' hin hin'
    (fun x hx hx' hxT => (hbα x hx hx' hxT).symm)
    (fun y hy => by
      have hyb := hTYb hy
      funext j
      simp only [barField]
      rw [dite_eq_left (hΩ1 y hyb), dite_eq_left (hHb y)]
      exact hbφ y (hHb y) (hΩ1 y hyb) hyb j)
    (fun x _ => Dec2.hRespects_of_core_near _ _ _ _ _ fun y' hy' y hd =>
      hRT1 _ (level_core_mem_of_active hG' hm₁ hRC hRX hw hy') y hd)
    (fun x _ => Dec2.hRespects_of_core_near _ _ _ _ _ fun y' hy' y hd =>
      hRT1 _ (localB_core_mem_of_active hG' hk1 hk Y hm₁ hM hRC hRX hw hy') y hd)
    (fun x hx => decM_isUnit_cover (hXD x hx) hdom.2.1.toIsConstraintField hδc hsm)
    (fun x hx => decM_isUnit_cover (hXD' x hx) hdom'.2.1.toIsConstraintField hδc hsm)
    hTblk cc ψh (fun p => if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0)
    (fun b hb hb' _ j => by simp only [dite_eq_left hb])
    (hRT1 _ hx₁R _ hx₁) (hG'.mem_layer x₀) i
  have hFe2 : F₁ (@Prod.mk (DecParams Gp) (RawData d L (N₁ * L ^ m₁) (k + 1) N)
      (extParams Gp X₁ w) (rawOf D)) = (φ, α) := hFe
  rw [hFe']
  unfold hatPsiF hatSqrtF
  rw [hFe2]
  exact key

end HatLift

/-! ### The old term of the ambient pair reads its fluctuation variable near the read region -/

section Reads

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm ϱ₁ ϱ₂ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {a : ℕ → ℝ} {ν : ℝ}

/-- **The old term reads the fluctuation variable only near the read region.**  Let `𝔹_{k+1}` be a
level set, `(coverOf 𝔹_{k+1}, H⁻)` the fluctuation pair with its cover base, `Sol` the decoupled
fluctuation field (mode P), and `R` a read region (the cubes of `𝒞`, the cubes meeting `X₁`, the data
sites of `𝔹_k(X)`).  For `w` supported on `𝒞` with `|σ w| < e^κ` and two fluctuations `ψ₁`, `ψ₂`
with the strict data inequalities that agree within sup-distance `L^{k+1}` of `R`, the old term
`Φ_E(φ, δφ(ψ), (Θ, ψ))` takes the same value at `ψ₁` and `ψ₂`: the fluctuation fields agree on the
`L^{k+1}`-neighbourhood of `R` (`Dec2.decSol_value_cross` for the pair with itself; the residual rows
of `R` and the active interaction cubes stay in it), and the composition reads them there. -/
theorem eTermFun_level_hat_congr (hG' : IsLevel Gp (k + 1)) (hm₁ : 2 ≤ m₁)
    {Kc₂ Cx₂ c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L Kc₂ Cx₂ c₂ BG₂)
    (Sf : Dec2.CoverBase (coverOf Gp) Hm a ν Kc₂ Cx₂) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm a ν p.1) p.2.2.1 p.2.1
          (pertSource Hm a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm a ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm a ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {C : Finset (ParIdx Gp X₁)}
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (hRk : ∀ x ∈ dataSites Gk, x ∈ R)
    {w : ParIdx Gp X₁ → ℂ} (hw : w ∈ supportedOn C)
    (hs : ∀ P, ‖extParams Gp X₁ w P‖ < Real.exp κ)
    (pa : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N)
    {ψ₁ ψ₂ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    (he₁ : StrictDataM Hm N false δ₀ δ₁ (flEdat Gp Hm pa Θ.1 ψ₁))
    (he₂ : StrictDataM Hm N false δ₀ δ₁ (flEdat Gp Hm pa Θ.1 ψ₂))
    (hψ : ∀ x ∈ R, ∀ y, supDist x y ≤ L ^ (k + 1) → ψ₁ y = ψ₂ y) :
    eTermFun Gp Gk Gj Hm ac Fk E pa (Sol (extParams Gp X₁ w, flEdat Gp Hm pa Θ.1 ψ₁)).1
        (Θ, ψ₁) =
      eTermFun Gp Gk Gj Hm ac Fk E pa (Sol (extParams Gp X₁ w, flEdat Gp Hm pa Θ.1 ψ₂)).1
        (Θ, ψ₂) := by
  classical
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀ : Finset (CTorus d L N₁ m₁ (k + 1)), ∀ y, y ∈ Y₀ ↔ ∃ x ∈ R,
      supDist x y ≤ L ^ (k + 1) :=
    ⟨Finset.univ.filter fun y => ∃ x ∈ R, supDist x y ≤ L ^ (k + 1), fun y => by simp⟩
  have hRY₀ : ∀ x ∈ R, x ∈ Y₀ := fun x hx =>
    (hY₀ x).2 ⟨x, hx, by rw [supDist_self]; exact Nat.zero_le _⟩
  obtain ⟨-, hfφ⟩ := Dec2.decSol_value_cross hF₂ Sf Sf hκ hM₂ false h0 h1 hδ₀ hδ₁ hSol hSol hs hs
    he₁ he₂ (Y := Y₀) (T := R) (fun x hx => hRY₀ x hx) (fun _ _ => Iff.rfl)
    (localB_depth_dich hG' hm₁ hRC hRX Hm hw) (localB_depth_dich hG' hm₁ hRC hRX Hm hw)
    (localB_depth_row hG' hm₁ hRC hRX Y₀ hw) (localB_depth_row hG' hm₁ hRC hRX Y₀ hw)
    (fun q hq _ => ⟨hq, rfl, fun _ _ _ _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩)
    (fun q hq hne => ⟨hq, hne⟩)
    (fun x hx _ y hy => ⟨fun _ _ _ => Iff.rfl, fun _ =>
      (hY₀ y).2 ⟨x, hx, supDist_le_of_mem_resSites hy⟩⟩)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun x hx _ y hy => hψ x hx y (supDist_le_of_mem_resSites hy))
    (fun _ _ _ _ _ => rfl)
  have hsvf : ∀ y ∈ Y₀, svec Hm (Sol (extParams Gp X₁ w, flEdat Gp Hm pa Θ.1 ψ₁)).1 y =
      svec Hm (Sol (extParams Gp X₁ w, flEdat Gp Hm pa Θ.1 ψ₂)).1 y := fun y hy =>
    svec_cross Iff.rfl fun h h' i => (hfφ y h h' hy i).symm
  have hLM : ∀ j, j ≤ k + 1 → L ^ j ≤ L ^ (k + 1) := fun j hj =>
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) hj
  rw [eTermFun_congr_raw (Gk := Gk) (Gj := Gj) ac Fk E _ _ (u := (Θ, ψ₁)) (u' := (Θ, ψ₂))
    fun x hx => ⟨rfl, fun _ => rfl,
      hψ x (hRk x hx) x (by rw [supDist_self]; exact Nat.zero_le _)⟩]
  refine (eTermFun_cross ac Fk E (Θ, ψ₂) (fun x _ => ⟨fun _ _ _ => Iff.rfl, fun _ _ => rfl⟩)
    (fun x hx => ⟨fun _ _ _ => Iff.rfl, fun y hy => hsvf y ?_⟩)).symm
  refine (hY₀ y).2 ⟨x, hRk x hx, ?_⟩
  rcases hy with rfl | hy | hy
  · rw [supDist_self]; exact Nat.zero_le _
  · exact (supDist_le_of_mem_blk (layerIndex_le_of_Ω_empty Gk Gk.top x) hy).trans
      (hLM _ (layerIndex_le_of_Ω_empty Gk Gk.top x))
  · exact (supDist_le_of_mem_blk (layerIndex_le_of_Ω_empty Hm Hm.top x) hy).trans
      (hLM _ (layerIndex_le_of_Ω_empty Hm Hm.top x))

end Reads

end Balaban.Localization
