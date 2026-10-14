/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalHatTerm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exact locality of the local terms on the local chart

The term of a polymer `Y` recomputed on a local generating set `𝔹` (P3 (4.46)-(4.47), printed
pp. 78-79; `LocalHatTerm.lean`) is `E_X(Y)(Θ) = ∑_{𝒞 : Y[𝒞] = Y} coef(F(Θ, ·), 𝒞)` with
`F(Θ, w) = ∫_K Φ_E(F₁(σ w, Θ), Sol(σ w, …), (Θ, cc C^{1/2}(σ w) ψ̂)) dγ(ψ̂)`, the decoupled background
`F₁`, the fluctuation field `Sol` and the square root `C^{1/2}` all of the cover of `𝔹`.  It reads the
datum `Θ` on all data sites of `𝔹`.  This file proves that on the chart it depends on `Θ` only
through its values on a set `W` that contains the thickened interaction cube `□̂_z` of every cube
`z` of the cover whose decoupling factor `s_z = ∏_{P ∈ 𝒬(z)} (σ w)_P` does not vanish (P3 (4.47),
"`E(Y)` depends on `Y` only"):

* `inBox_of_supDist_le`: a box enlarged by `t` contains the sup-distance `t`-neighbourhood of each
  of its points;
* `eTermFun_localHat_congr`: **the integrand at one point.**  For two data of the chart agreeing on
  `W`, the composite `Φ_E(F₁(s, Θ), Sol(s, …), (Θ, ψ'(Θ)))` with the local hat lift `ψ'(Θ)` takes the
  same value.  The pair `(coverOf 𝔹, 𝔹)` is compared with itself: the background fields
  (`Dec2.decBg_value_cross`) on the `L^{k+1}`-neighbourhood `T_b` of the active interaction cubes, the
  local hat lifts (`Dec2.localLift_eq_localLift_on_component`) on `T_b`, then the fluctuation field
  and the composition (`eTermFun_replacement_cross_of_agree`).  Every site read lies within
  `5 L^{k+1}` of an active interaction cube, hence in its thickened cube, hence in `W`;
* `evTerm_localHat_congr`: **the term** `E_X(Y)` takes the same value at two data of the chart
  agreeing on `W` (`coef_congr_near`, the integrands agree for every `ψ̂ ∈ K`);
* `evTerm_localHat_clipRaw_congr`: the same on the class domain `Ξ^c_{k+1}(𝔹; 1, ε_{k+1})` through
  the cut-off `clipRaw 𝔹`, for pairs of fields agreeing on `W`.

The hypotheses on the parameter map `σ` (the active thickened cubes lie in `W`; every data site of
the old generating set `𝔹_k(X)` is read inside an active interaction cube) are discharged for the
transported parameters `σ = τ ∘ extParams` at `𝔹 = 𝔹_{k+1}(Y⁺)` and `W = Y` in the instance section.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Finset Matrix MeasureTheory

section Boxes

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

/-- **A box enlarged by `t` contains the `t`-neighbourhood of each of its points** (sup-distance
on the torus). -/
theorem inBox_of_supDist_le {j : ℕ} {y0 x y : CTorus d L N₁ m₁ K} {R : ℝ}
    (h : InBox m₁ j y0 R x) {t : ℕ} (hxy : supDist x y ≤ t) : InBox m₁ j y0 (R + t) y := by
  have hμ : ∀ μ, ∃ u : ℤ, |u| ≤ t ∧ ((u : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) = y μ - x μ :=
    fun μ => (cycNorm_le_iff (y μ - x μ) t).1 (by
      rw [cycNorm_sub_comm]; exact (cycNorm_le_supDist x y μ).trans hxy)
  choose u hu1 hu2 using hμ
  have hy : y = x + (intTorus u : CTorus d L N₁ m₁ K) := by
    funext μ
    simp only [Pi.add_apply, intTorus_apply, hu2 μ]
    ring
  rw [hy]
  exact h.add_int u fun μ => by
    have := hu1 μ
    rw [← Int.cast_abs]
    exact_mod_cast this

end Boxes

section Same

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm ϱ₁ ϱ₂ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {a₁ ν Kc Cx : ℝ}

/-- **Exact locality of the local integrand at one point** (P3 (4.47) on `𝔹`, cover form, one
pair).  Let `(coverOf 𝔹, 𝔹)` and `(coverOf 𝔹, H⁻)` be the background and fluctuation pairs with
their cover bases, `F₁`, `Sol` the decoupled background and fluctuation maps, `s` parameters with
`|s_P| < e^κ`, and `W` a set of sites such that

* (`hact`) the thickened interaction cube `□̂_z` of every cube `z` of the cover with `s_z ≠ 0` lies
  in `W` and in the top layer of `𝔹`;
* (`hcomp`) every data site `x` of `𝔹_k(X)` and the blocks of `x` read by the composition lie in the
  interaction cube of a cube `z` with `s_z ≠ 0`.

Then for two data `D`, `D'` of the chart `Ξ^c(𝔹; 1, ε)` with the same raw values on `W` and every
hat variable `ψ̂` with `|ψ̂| ≤ c_ψ`, the old-term functional `Φ_E` at the decoupled background, the
fluctuation field and `(Θ, ψ'(Θ))`, `ψ'(Θ)` the local hat lift `cc C^{1/2}(s) ψ̂` at the background of
`Θ`, takes the same value at `Θ = D` and `Θ = D'`. -/
theorem eTermFun_localHat_congr (hk1 : 1 ≤ k) (hL2 : 2 ≤ L) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Kc₂ Cx₂ c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L Kc₂ Cx₂ c₂ BG₂)
    (Sf : Dec2.CoverBase (coverOf Gp) Hm (compWeight L a₁) ν Kc₂ Cx₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₁ : ℝ} (hδ₁0 : 0 < δ₁)
    (hB : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤
      deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hPmp : Precedes Hm Gp) (hHm : Hm.Ω (k + 1) = ∅) (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {s : Dec2.DecParams (coverOf Gp)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    {W : Set (CTorus d L N₁ m₁ (k + 1))}
    (hact : ∀ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
        ∀ y, InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y → y ∈ W ∧ y ∈ Gp.Ω (k + 1))
    (hcomp : ∀ x ∈ dataSites Gk, ∃ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 ∧ ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ y ∈ Gk.blk (Gk.layerIndex x) x ∨ y ∈ Gp.blk (Gp.layerIndex x) x ∨
          y ∈ Hm.blk (Hm.layerIndex x) x) → y ∈ intBox q)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    (hDD : ∀ z ∈ W, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    eTermFun Gp Gk Gj Hm ac Fk E (F₁ (s, rawOf D))
        (Sol (s, flEdat Gp Hm (F₁ (s, rawOf D)) (rawOf D).1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (s, rawOf D)).2
                (Dec2.extS (coverOf Gp) s) (barField Gp (rawOf D).1 (F₁ (s, rawOf D)).1)
                (unitQ Gp) (unitP Gp) *ᵥ ψh)) (⟨unitBlock x, h⟩, i)
            else 0))).1
        (rawOf D, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (s, rawOf D)).2
                (Dec2.extS (coverOf Gp) s) (barField Gp (rawOf D).1 (F₁ (s, rawOf D)).1)
                (unitQ Gp) (unitP Gp) *ᵥ ψh)) (⟨unitBlock x, h⟩, i)
            else 0) =
    eTermFun Gp Gk Gj Hm ac Fk E (F₁ (s, rawOf D'))
        (Sol (s, flEdat Gp Hm (F₁ (s, rawOf D')) (rawOf D').1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (s, rawOf D')).2
                (Dec2.extS (coverOf Gp) s) (barField Gp (rawOf D').1 (F₁ (s, rawOf D')).1)
                (unitQ Gp) (unitP Gp) *ᵥ ψh)) (⟨unitBlock x, h⟩, i)
            else 0))).1
        (rawOf D', fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (s, rawOf D')).2
                (Dec2.extS (coverOf Gp) s) (barField Gp (rawOf D').1 (F₁ (s, rawOf D')).1)
                (unitQ Gp) (unitP Gp) *ᵥ ψh)) (⟨unitBlock x, h⟩, i)
            else 0) := by
  classical
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hxi := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hLk : 0 < L ^ (k + 1) := pow_pos (by omega) _
  have hK4 : 0 < K4 d L N BG κ := K4_pos hS.fam.2.1 hd0
  have hUD : ∀ {D₀ : BgData Gp N}, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D₀ →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D₀ := fun hD₀ =>
    inUnionDomainC_of_inDomainC HBp hδ0
      (hc7.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))) hc7
      (xiCData_inDomainC HBp hsmall hD₀)
  have hDd := hUD hD
  have hDd' := hUD hD'
  -- the active cubes are top cubes
  have hq1 : ∀ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 → q.1 = k + 1 := by
    intro q hq hne
    obtain ⟨⟨hq1, hqK⟩, hql, -⟩ := (mem_cubeIdx _).1 hq
    have hc : q.2 ∈ Gp.Ω (k + 1) := (hact q hq hne q.2 (inBox_centre q.1 q.2 (by
      unfold hatRad
      have hB1 : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := one_le_pow₀ (by exact_mod_cast hL1)
      have : (0 : ℝ) ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 := by positivity
      linarith))).2
    exact (mem_layer_iff_of_mem_top hc hq1 hqK).1 hql
  -- the active interaction cubes `T`, their block neighbourhood `T_b` and the read region `Y_b`
  obtain ⟨T, hT⟩ : ∃ T : Finset (CTorus d L N₁ m₁ (k + 1)), ∀ y, y ∈ T ↔
      ∃ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 ∧
        y ∈ intBox q :=
    ⟨Finset.univ.filter fun y => ∃ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 ∧ y ∈ intBox q, fun y => by simp⟩
  have hint : ∀ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 → ∀ x ∈ intBox q, x ∈ T :=
    fun q hq hne x hx => (hT x).2 ⟨q, hq, hne, hx⟩
  have hTnear : ∀ x ∈ T, ∀ z, supDist x z ≤ 5 * L ^ (k + 1) → z ∈ W ∧ z ∈ Gp.Ω (k + 1) := by
    intro x hx z hz
    obtain ⟨q, hq, hne, hxq⟩ := (hT x).1 hx
    have hqk := hq1 q hq hne
    refine hact q hq hne z ((inBox_of_supDist_le (mem_intBox.1 hxq) hz).mono ?_)
    unfold hatRad
    rw [hqk]
    have hL : (2 : ℝ) ≤ L := by exact_mod_cast hL2
    have hp : (0 : ℝ) ≤ (L : ℝ) ^ (k + 1) := by positivity
    have h5 : (5 : ℝ) ≤ 3 * (L : ℝ) ^ 2 := by nlinarith
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right h5 hp]
  obtain ⟨Tb, hTb⟩ : ∃ Tb : Finset (CTorus d L N₁ m₁ (k + 1)), ∀ y, y ∈ Tb ↔ ∃ x ∈ T,
      ∃ z, jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) z =
        jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y ∧ supDist x z ≤ L ^ (k + 1) :=
    ⟨Finset.univ.filter fun y => ∃ x ∈ T, ∃ z, jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) z =
        jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y ∧ supDist x z ≤ L ^ (k + 1),
      fun y => by simp⟩
  obtain ⟨Yb, hYb⟩ : ∃ Yb : Finset (CTorus d L N₁ m₁ (k + 1)), ∀ y, y ∈ Yb ↔ ∃ x ∈ T,
      supDist x y ≤ 3 * L ^ (k + 1) :=
    ⟨Finset.univ.filter fun y => ∃ x ∈ T, supDist x y ≤ 3 * L ^ (k + 1), fun y => by simp⟩
  have hTTb1 : ∀ x ∈ T, ∀ y, supDist x y ≤ L ^ (k + 1) → y ∈ Tb := fun x hx y h =>
    (hTb y).2 ⟨x, hx, y, rfl, h⟩
  have hTTb : ∀ x ∈ T, x ∈ Tb := fun x hx =>
    hTTb1 x hx x (by rw [supDist_self]; exact Nat.zero_le _)
  have hTbT : ∀ y ∈ Tb, ∃ x ∈ T, supDist x y ≤ 2 * L ^ (k + 1) := by
    intro y hy
    obtain ⟨x, hx, z, hz, hd⟩ := (hTb y).1 hy
    have hzy : supDist z y ≤ L ^ (k + 1) :=
      supDist_le_of_sameCell hLk (sameCell_of_jBlock_eq le_rfl hz)
    exact ⟨x, hx, (supDist_triangle x z y).trans (by omega)⟩
  have hTbblk : IsBlockUnion L (N₁ * L ^ m₁) (k + 1) (k + 1) Tb := by
    intro y y' hyy'
    rw [hTb, hTb]
    constructor
    · rintro ⟨x, hx, z, hz, hd⟩; exact ⟨x, hx, z, hz.trans hyy', hd⟩
    · rintro ⟨x, hx, z, hz, hd⟩; exact ⟨x, hx, z, hz.trans hyy'.symm, hd⟩
  have hTbYb : Tb ⊆ Yb := fun y hy => by
    obtain ⟨x, hx, hd⟩ := hTbT y hy
    exact (hYb y).2 ⟨x, hx, by omega⟩
  have hYbW : ∀ y ∈ Yb, y ∈ W ∧ y ∈ Gp.Ω (k + 1) := fun y hy => by
    obtain ⟨x, hx, hd⟩ := (hYb y).1 hy
    exact hTnear x hx y (by omega)
  have hTW : ∀ y ∈ T, y ∈ W := fun y hy => (hYbW y (hTbYb (hTTb y hy))).1
  have hΩ1 : ∀ y ∈ Yb, y ∈ Gp.Ω 1 := fun y hy =>
    Gp.Ω_antitone le_rfl (by omega) (by omega) (hYbW y hy).2
  -- the component hypotheses for the pair with itself
  have hresb : ∀ x ∈ Tb, x ∈ Gp.Ω 1 → ∀ y ∈ resSites Gp x, y ∈ Gp.Ω 1 ∧ y ∈ Yb := by
    intro x hx _ y hy
    obtain ⟨x', hx', hd⟩ := hTbT x hx
    have := supDist_le_of_mem_resSites hy
    have hyb : y ∈ Yb := (hYb y).2 ⟨x', hx', (supDist_triangle x' x y).trans (by omega)⟩
    exact ⟨hΩ1 y hyb, hyb⟩
  have hdatb : ∀ y ∈ Yb, y ∈ Gp.Ω 1 → ∀ z ∈ approxDep Gp y,
      D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z := by
    intro y hy _ z hz
    obtain ⟨x, hx, hd⟩ := (hYb y).1 hy
    have := supDist_le_of_mem_approxDep hz
    exact hDD z (hTnear x hx z ((supDist_triangle x y z).trans (by omega))).1
  -- the background fields agree on `Y_b`, the multipliers on `T_b`
  obtain ⟨hbα, hbφ⟩ := Dec2.decBg_value_cross hS S S HBp HBp hκ.le hM hF₁ hF₁ hs hs hDd hDd'
    hTbYb (fun _ _ _ _ _ => Iff.rfl)
    (fun q hq hne => Or.inl fun x hx => hTTb _ (hint q hq hne _ hx))
    (fun q hq hne => Or.inl fun x hx => hTTb _ (hint q hq hne _ hx))
    (fun q hq hne x _ hx => hTTb _ (hint q hq hne _ hx))
    (fun q hq hne x _ hx => hTTb _ (hint q hq hne _ hx))
    (fun q hq _ => ⟨hq, rfl, fun _ _ _ _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩)
    (fun q hq hne => ⟨hq, hne⟩) hresb (fun _ _ _ _ _ _ _ _ _ _ => Iff.rfl) hdatb
  -- the backgrounds, the covariance data
  obtain ⟨φ, α, hI, -, -⟩ := coverBg_exists hS S HBp hκ.le hM heps hsmall hc7 hs hD
  have hFe : F₁ (s, rawOf D) = (φ, α) := hF₁ s D hs hDd φ α ⟨hI.small, hI.fixed, hI.field⟩
  obtain ⟨φ', α', hI', -, -⟩ := coverBg_exists hS S HBp hκ.le hM heps hsmall hc7 hs hD'
  have hFe' : F₁ (s, rawOf D') = (φ', α') :=
    hF₁ s D' hs hDd' φ' α' ⟨hI'.small, hI'.fixed, hI'.field⟩
  have hdom := decDom_of_coverBg hS S HBp hκ.le hM heps hsmall hc7 hphi hs hD hI hmarD hαD
  have hdom' := decDom_of_coverBg hS S HBp hκ.le hM heps hsmall hc7 hphi hs hD' hI' hmarD hαD
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      unfold decDomMargin; positivity
    linarith
  have SX : Dec2.XCover (coverOf Gp) Gp (compWeight L a₁) a₁ ν Cx :=
    ⟨S.toCoverGeom, (S.weights k hk1 (by omega)).1, (S.weights k hk1 (by omega)).2, ha₁, ha₂⟩
  have hXD : ∀ x : ℝ, 0 < x → Dec2.XData (coverOf Gp) Gp (compWeight L a₁) a₁ ν x α κ
      (extS Gp s) Cx := fun x hx => xData_cover_of_mem SX hCx hx.le hκ.le hMX hdom
  have hXD' : ∀ x : ℝ, 0 < x → Dec2.XData (coverOf Gp) Gp (compWeight L a₁) a₁ ν x α' κ
      (extS Gp s) Cx := fun x hx => xData_cover_of_mem SX hCx hx.le hκ.le hMX hdom'
  rw [hFe, hFe'] at hbα hbφ
  have hHR : ∀ y' ∈ Dec2.Core (coverOf Gp) (Dec2.extS (coverOf Gp) s), ∀ y,
      supDist y' y ≤ L ^ (k + 1) → y ∈ Tb := by
    intro y' hy' y hd
    obtain ⟨z, hz, hy'z⟩ := Finset.mem_biUnion.1 hy'
    obtain ⟨hzc, hzne⟩ := Finset.mem_filter.1 hz
    have hyT : y' ∈ T := hint z hzc hzne y' (mem_intBox.2 ((mem_boxSet.1 hy'z).mono (by
      have : (0 : ℝ) ≤ (L : ℝ) ^ (z.1 + m₁) := by positivity
      linarith)))
    exact hTTb1 y' hyT y hd
  -- the local hat lifts agree on `T_b`
  have hlift : ∀ x₀ ∈ Tb, ∀ i : Fin N,
      (if h : unitBlock x₀ ∈ unitPts Gp then
        (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν α' (Dec2.extS (coverOf Gp) s)
          (barField Gp D'.Ψ φ') (unitQ Gp) (unitP Gp) *ᵥ ψh)) (⟨unitBlock x₀, h⟩, i) else 0) =
      (if h : unitBlock x₀ ∈ unitPts Gp then
        (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν α (Dec2.extS (coverOf Gp) s)
          (barField Gp D.Ψ φ) (unitQ Gp) (unitP Gp) *ᵥ ψh)) (⟨unitBlock x₀, h⟩, i) else 0) := by
    intro x₀ hx₀ i
    by_cases htop : x₀ ∈ Gp.layer (k + 1)
    · exact Dec2.localLift_eq_localLift_on_component (T := Tb) (α := α) (α' := α')
        (s := Dec2.extS (coverOf Gp) s) (s' := Dec2.extS (coverOf Gp) s)
        (φ := barField Gp D.Ψ φ) (φ' := barField Gp D'.Ψ φ') SX SX
        (fun v => (hdom.2.2 v).le) (fun v => (hdom'.2.2 v).le) (fun _ _ _ _ _ => Iff.rfl)
        (fun x hx => (hXD x hx).isUnit_one_sub) (fun x hx => (hXD' x hx).isUnit_one_sub)
        (fun q hq hne => Or.inl fun x hx => hTTb _ (hint q hq hne _ hx))
        (fun q hq hne => Or.inl fun x hx => hTTb _ (hint q hq hne _ hx))
        (fun q hq _ => ⟨hq, rfl, fun _ _ _ _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩)
        (fun q hq hne => ⟨hq, hne⟩)
        (fun x hx hx' hxT => (hbα x hx hx' hxT).symm)
        (fun y hy => by
          have hyb := hTbYb hy
          funext j
          simp only [barField]
          rw [dite_eq_left (hΩ1 y hyb), dite_eq_left (hΩ1 y hyb)]
          exact hbφ y (hΩ1 y hyb) (hΩ1 y hyb) hyb j)
        (fun x _ => Dec2.hRespects_of_core_near _ _ _ _ _ hHR)
        (fun x _ => Dec2.hRespects_of_core_near _ _ _ _ _ hHR)
        (fun x hx => decM_isUnit_cover (hXD x hx) hdom.2.1.toIsConstraintField hδc hsm)
        (fun x hx => decM_isUnit_cover (hXD' x hx) hdom'.2.1.toIsConstraintField hδc hsm)
        hTbblk cc ψh ψh (fun _ _ _ _ _ => rfl) hx₀ htop i
    · have hnot : unitBlock x₀ ∉ unitPts Gp := fun h => by
        obtain ⟨x₁, hx₁, hb⟩ := (mem_unitPts Gp).1 h
        exact htop (layer_of_unitBlock Gp hb hx₁)
      rw [dite_eq_right hnot, dite_eq_right hnot]
  -- the fluctuation, the composition
  set ψ₁ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ :=
    fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts Gp then
        (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (s, rawOf D)).2
          (Dec2.extS (coverOf Gp) s) (barField Gp (rawOf D).1 (F₁ (s, rawOf D)).1)
          (unitQ Gp) (unitP Gp) *ᵥ ψh)) (⟨unitBlock x, h⟩, i)
      else 0 with hψ₁
  set ψ₂ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ :=
    fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts Gp then
        (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (s, rawOf D')).2
          (Dec2.extS (coverOf Gp) s) (barField Gp (rawOf D').1 (F₁ (s, rawOf D')).1)
          (unitQ Gp) (unitP Gp) *ᵥ ψh)) (⟨unitBlock x, h⟩, i)
      else 0 with hψ₂
  have hψ12 : ∀ x ∈ Tb, ψ₁ x = ψ₂ x := fun x hx => funext fun i => by
    rw [hψ₁, hψ₂]
    simp only
    rw [hFe, hFe']
    exact (hlift x hx i).symm
  have hψb := localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂ hS S HBp hκ.le hM hMX hCx hF₁
    heps hsmall hc7 hphi hmarD hαD hsm hs hD cc hcψ hδ₁0 hδ₁c hψh
  have hψb' := localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂ hS S HBp hκ.le hM hMX hCx hF₁
    heps hsmall hc7 hphi hmarD hαD hsm hs hD' cc hcψ hδ₁0 hδ₁c hψh
  have he := strictDataM_flEdat_cover hS S HBp hκ hM heps hsmall hc7 hphi hδ₁0 le_rfl hPmp hF₁
    hSol hs hD hψb.1
  have he' := strictDataM_flEdat_cover hS S HBp hκ hM heps hsmall hc7 hphi hδ₁0 le_rfl hPmp hF₁
    hSol hs hD' hψb'.1
  have hcp : ∀ x ∈ dataSites Gk,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ Gp.layer n ↔ x ∈ Gp.layer n)) ∧
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ y ∈ Gk.blk (Gk.layerIndex x) x ∨ y ∈ Gp.blk (Gp.layerIndex x) x) → y ∈ Yb := by
    intro x hx
    obtain ⟨q, hq, hne, hrd⟩ := hcomp x hx
    refine ⟨fun _ _ _ => Iff.rfl, fun y hy => ?_⟩
    have hyq : y ∈ intBox q := hrd y (by
      rcases hy with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h)))
    exact hTbYb (hTTb y (hint q hq hne y hyq))
  have hcm : ∀ x ∈ dataSites Gk,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ Hm.layer n ↔ x ∈ Hm.layer n)) ∧
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ y ∈ Gk.blk (Gk.layerIndex x) x ∨ y ∈ Hm.blk (Hm.layerIndex x) x) → y ∈ Yb := by
    intro x hx
    obtain ⟨q, hq, hne, hrd⟩ := hcomp x hx
    refine ⟨fun _ _ _ => Iff.rfl, fun y hy => ?_⟩
    have hyq : y ∈ intBox q := hrd y (by
      rcases hy with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h)))
    exact hTbYb (hTTb y (hint q hq hne y hyq))
  have hkT : ∀ x ∈ dataSites Gk, x ∈ T := fun x hx => by
    obtain ⟨q, hq, hne, hrd⟩ := hcomp x hx
    exact hint q hq hne x (hrd x (Or.inl rfl))
  have hdk : ∀ x ∈ dataSites Gk, D.Ψ x = D'.Ψ x ∧ (x ∈ Gk.Ω 1 → D.h x = D'.h x) :=
    fun x hx => ⟨(hDD x (hTW x (hkT x hx))).1, fun _ => (hDD x (hTW x (hkT x hx))).2⟩
  have hresf : ∀ x ∈ T, x ∈ Hm.Ω 1 → ∀ y ∈ resSites Hm x,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ Hm.layer n ↔ y ∈ Hm.layer n)) ∧ (y ∈ Hm.Ω 1 → y ∈ Yb) ∧
        y ∈ Yb := by
    intro x hx _ y hy
    have := supDist_le_of_mem_resSites hy
    have hyb : y ∈ Yb := (hYb y).2 ⟨x, hx, by omega⟩
    exact ⟨fun _ _ _ => Iff.rfl, fun _ => hyb, hyb⟩
  exact (eTermFun_replacement_cross_of_agree hS S S HBp HBp hκ.le hM hF₁ hF₁ hF₂ Sf Sf hM₂
    (by positivity) hδ₁0.le hB hδ₁ hSol hSol ac Fk E hs hs hDd hDd' ψ₁ ψ₂ he he'
    hTbYb (fun _ _ _ _ _ => Iff.rfl)
    (fun q hq hne => Or.inl fun x hx => hTTb _ (hint q hq hne _ hx))
    (fun q hq hne => Or.inl fun x hx => hTTb _ (hint q hq hne _ hx))
    (fun q hq hne x _ hx => hTTb _ (hint q hq hne _ hx))
    (fun q hq hne x _ hx => hTTb _ (hint q hq hne _ hx))
    (fun q hq _ => ⟨hq, rfl, fun _ _ _ _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩)
    (fun q hq hne => ⟨hq, hne⟩) hresb (fun _ _ _ _ _ _ _ _ _ _ => Iff.rfl) hdatb
    (fun y hy => (hDD y (hYbW y hy).1).1)
    (fun x hx => hTbYb (hTTb x hx)) (fun x hx => hTTb x hx) (fun _ _ => Iff.rfl)
    (fun q hq hne => Or.inl fun x hx => hint q hq hne _ hx)
    (fun q hq hne => Or.inl fun x hx => hint q hq hne _ hx)
    (fun q hq hne x _ hx => hint q hq hne _ hx)
    (fun q hq hne x _ hx => hint q hq hne _ hx)
    (fun q hq _ => ⟨hq, rfl, fun _ _ _ _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩)
    (fun q hq hne => ⟨hq, hne⟩) hresf hcp hcm hdk
    (fun x hx _ y hy => hψ12 y (hTTb1 x hx y (supDist_le_of_mem_resSites hy)))
    (fun x hx => hψ12 x (hTTb x (hkT x hx)))).symm

/-- **Exact locality of the local term on the chart** (P3 (4.47): `E(Y)` depends on the datum on
`W` only).  The term of `Y` recomputed on `𝔹`, `∑_{𝒞 ∈ connFams Y} coef(F(Θ, ·), 𝒞)` with the
`ψ̂`-integrated local E-part `F(Θ, w)` at the parameters `σ w`, takes the same value at two raw data
of the chart `Ξ^c(𝔹; 1, ε)` agreeing on `W`, provided that for every connected family `𝒞` with
`Y[𝒞] = Y` and every `w` supported on `𝒞` in the polydisc the hypotheses `hact`, `hcomp` of
`eTermFun_localHat_congr` hold at `σ w`. -/
theorem evTerm_localHat_congr (hk1 : 1 ≤ k) (hL2 : 2 ≤ L) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Kc₂ Cx₂ c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L Kc₂ Cx₂ c₂ BG₂)
    (Sf : Dec2.CoverBase (coverOf Gp) Hm (compWeight L a₁) ν Kc₂ Cx₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₁ : ℝ} (hδ₁0 : 0 < δ₁)
    (hB : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤
      deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hPmp : Precedes Hm Gp) (hHm : Hm.Ω (k + 1) = ∅) (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {ι : Type*} [DecidableEq ι] [Fintype ι] {ϱa : ℝ}
    {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa} {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)}
    {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp)}
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    {W : Set (CTorus d L N₁ m₁ (k + 1))}
    (hact : ∀ C ∈ connFams cI Ga m₀ X₁ Y, ∀ w ∈ supN C (Real.exp κ),
      ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
        ∀ y, InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y → y ∈ W ∧ y ∈ Gp.Ω (k + 1))
    (hcomp : ∀ C ∈ connFams cI Ga m₀ X₁ Y, ∀ w ∈ supN C (Real.exp κ),
      ∀ x ∈ dataSites Gk, ∃ q ∈ (coverOf Gp).cubeIdx,
        (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 ∧ ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ y ∈ Gk.blk (Gk.layerIndex x) x ∨ y ∈ Gp.blk (Gp.layerIndex x) x ∨
            y ∈ Hm.blk (Hm.layerIndex x) x) → y ∈ intBox q)
    {γ : Measure (unitPts Gp × Fin N → ℝ)} {K : Set (unitPts Gp × Fin N → ℝ)}
    (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ)
    {u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
    (hu' : u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
    (huu : ∀ z ∈ W, u.1 z = u'.1 z ∧ u.2 z = u'.2 z) :
    evTerm cI Ga m₀ X₁
        (fun (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ) =>
          ∫ ψ in K,
            eTermFun Gp Gk Gj Hm ac Fk E (F₁ (σ w, Θ))
              (Sol (σ w, flEdat Gp Hm (F₁ (σ w, Θ)) Θ.1
                (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
                  if h : unitBlock x ∈ unitPts Gp then
                    (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                      (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                      (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
                  else 0))).1
              (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
                  if h : unitBlock x ∈ unitPts Gp then
                    (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                      (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                      (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
                  else 0) ∂γ) Y u =
      evTerm cI Ga m₀ X₁
        (fun (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ) =>
          ∫ ψ in K,
            eTermFun Gp Gk Gj Hm ac Fk E (F₁ (σ w, Θ))
              (Sol (σ w, flEdat Gp Hm (F₁ (σ w, Θ)) Θ.1
                (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
                  if h : unitBlock x ∈ unitPts Gp then
                    (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                      (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                      (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
                  else 0))).1
              (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
                  if h : unitBlock x ∈ unitPts Gp then
                    (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                      (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                      (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
                  else 0) ∂γ) Y u' := by
  classical
  obtain ⟨D, hD, rfl⟩ := hu
  obtain ⟨D', hD', rfl⟩ := hu'
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  unfold evTerm
  refine Finset.sum_congr rfl fun C hC => coef_congr_near hE1 fun w hw => ?_
  have hwp : w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ) := fun i => by simpa using hw.2 i
  refine setIntegral_congr_fun hKc.isClosed.measurableSet fun ψ hψ => ?_
  exact eTermFun_localHat_congr hk1 hL2 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7 hphi hmarD
    hαD hsm hF₁ hF₂ Sf hM₂ hδ₁0 hB hδ₁ hSol hPmp hHm ac Fk E cc hcψ hδ₁c (hσκ w hwp)
    (hact C hC w hw) (hcomp C hC w hw) hD hD' huu (fun r => by simpa using hKb ψ hψ r)

/-- **Exact locality of the local term on the class domain.**  `evTerm_localHat_congr` read through
the cut-off `clipRaw 𝔹` on the class domain `Ξ^c_{k+1}(𝔹; 1, ε_{k+1})` (`xiFieldDom`,
`ε_{k+1} ≤ ε`): for two pairs of fields of the domain with the same values on `W` the terms are
equal.  (The class clause `localE` quantifies over all pairs of fields, not only those of the
domain; see the module documentation of `LocalClassLocal`.) -/
theorem evTerm_localHat_clipRaw_congr (hk1 : 1 ≤ k) (hL2 : 2 ≤ L) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Kc₂ Cx₂ c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L Kc₂ Cx₂ c₂ BG₂)
    (Sf : Dec2.CoverBase (coverOf Gp) Hm (compWeight L a₁) ν Kc₂ Cx₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₁ : ℝ} (hδ₁0 : 0 < δ₁)
    (hB : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤
      deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hPmp : Precedes Hm Gp) (hHm : Hm.Ω (k + 1) = ∅) (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {ι : Type*} [DecidableEq ι] [Fintype ι] {ϱa : ℝ}
    {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa} {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)}
    {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp)}
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    {W : Set (CTorus d L N₁ m₁ (k + 1))}
    (hact : ∀ C ∈ connFams cI Ga m₀ X₁ Y, ∀ w ∈ supN C (Real.exp κ),
      ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
        ∀ y, InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y → y ∈ W ∧ y ∈ Gp.Ω (k + 1))
    (hcomp : ∀ C ∈ connFams cI Ga m₀ X₁ Y, ∀ w ∈ supN C (Real.exp κ),
      ∀ x ∈ dataSites Gk, ∃ q ∈ (coverOf Gp).cubeIdx,
        (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 ∧ ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ y ∈ Gk.blk (Gk.layerIndex x) x ∨ y ∈ Gp.blk (Gp.layerIndex x) x ∨
            y ∈ Hm.blk (Hm.layerIndex x) x) → y ∈ intBox q)
    {γ : Measure (unitPts Gp × Fin N → ℝ)} {K : Set (unitPts Gp × Fin N → ℝ)}
    (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ)
    {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps)
    {p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) Gp
      p.1 p.2)
    (hp' : (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) Gp
      p'.1 p'.2)
    (hpp : ∀ z ∈ W, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) :
    evTerm cI Ga m₀ X₁
        (fun (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ) =>
          ∫ ψ in K,
            eTermFun Gp Gk Gj Hm ac Fk E (F₁ (σ w, Θ))
              (Sol (σ w, flEdat Gp Hm (F₁ (σ w, Θ)) Θ.1
                (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
                  if h : unitBlock x ∈ unitPts Gp then
                    (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                      (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                      (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
                  else 0))).1
              (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
                  if h : unitBlock x ∈ unitPts Gp then
                    (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                      (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                      (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
                  else 0) ∂γ) Y (clipRaw Gp p) =
      evTerm cI Ga m₀ X₁
        (fun (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ) =>
          ∫ ψ in K,
            eTermFun Gp Gk Gj Hm ac Fk E (F₁ (σ w, Θ))
              (Sol (σ w, flEdat Gp Hm (F₁ (σ w, Θ)) Θ.1
                (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
                  if h : unitBlock x ∈ unitPts Gp then
                    (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                      (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                      (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
                  else 0))).1
              (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
                  if h : unitBlock x ∈ unitPts Gp then
                    (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                      (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                      (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
                  else 0) ∂γ) Y (clipRaw Gp p') := by
  classical
  refine evTerm_localHat_congr hk1 hL2 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7 hphi hmarD
    hαD hsm hF₁ hF₂ Sf hM₂ hδ₁0 hB hδ₁ hSol hPmp hHm ac Fk E cc hcψ hδ₁c Y hσκ hact hcomp hKc
    hKb (clipRaw_mem_xiCRaw_of_xiDom hεseq hp) (clipRaw_mem_xiCRaw_of_xiDom hεseq hp')
    fun z hz => ⟨funext fun i => ?_, funext fun i => ?_⟩
  · show (if z ∈ dataSites Gp then p.1 z i else 0) = (if z ∈ dataSites Gp then p'.1 z i else 0)
    rw [(hpp z hz).1]
  · show (if z ∈ Gp.Ω 1 then p.2 z i else 0) = (if z ∈ Gp.Ω 1 then p'.2 z i else 0)
    rw [(hpp z hz).2]

end Same

end Balaban.Localization
