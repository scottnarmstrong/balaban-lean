/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Approximate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Analyticity of the approximate field in the data (LEMMA53-astra.md, §4 (A6))

The data enter `approxField` through the pair `p = (Ψ, h)` of raw functions
`Torus → ℂ^N`.  On the set `approxDomain G a ν` of pairs for which every local blend
`w ⬝ w` and every interpolated vector `φ̃ ⬝ φ̃` has positive real part, every coordinate of
`approxField` (`approxField_analytic`) and of the residual (`residualRaw_analytic`) is analytic in
`p`; the complex data of `Lemma 5.3` lie in this set (`data_mem_approxDomain`).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Analytic

variable (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ)

/-- The space of raw data `(Ψ, h)`. -/
abbrev RawData (d L N₀ k N : ℕ) : Type :=
  (Torus d (N₀ * L ^ k) → Fin N → ℂ) × (Torus d (N₀ * L ^ k) → Fin N → ℂ)

open Classical in
/-- The local blend `w_B` at a site (with `ν_B = ν L^{2n}`), and `Ψ_z` at a collar site. -/
noncomputable def locBlend (p : RawData d L N₀ k N) (y : Torus d (N₀ * L ^ k)) : Fin N → ℂ :=
  cBlend (if y ∈ G.Ω 1 then a (G.layerIndex y) else 1)
    (if y ∈ G.Ω 1 then blockMass G ν y else 0) (p.1 y) (if y ∈ G.Ω 1 then p.2 y else 0)

/-- **The domain** of raw data on which the explicit formulas are analytic. -/
def approxDomain : Set (RawData d L N₀ k N) :=
  {p | (∀ y ∈ dataSites G, 0 < (locBlend G a ν p y ⬝ᵥ locBlend G a ν p y).re) ∧
    ∀ x ∈ G.Ω 1, 2 ≤ G.layerIndex x →
      0 < (interp G (locSol G a ν p.1 p.2) x ⬝ᵥ interp G (locSol G a ν p.1 p.2) x).re}

theorem analyticAt_rawΨ (y : Torus d (N₀ * L ^ k)) (i : Fin N) (p : RawData d L N₀ k N) :
    AnalyticAt ℂ (fun q : RawData d L N₀ k N => q.1 y i) p :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Torus d (N₀ * L ^ k) => Fin N → ℂ) y).comp
      (ContinuousLinearMap.fst ℂ _ _))).analyticAt p

theorem analyticAt_rawh (y : Torus d (N₀ * L ^ k)) (i : Fin N) (p : RawData d L N₀ k N) :
    AnalyticAt ℂ (fun q : RawData d L N₀ k N => q.2 y i) p :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Torus d (N₀ * L ^ k) => Fin N → ℂ) y).comp
      (ContinuousLinearMap.snd ℂ _ _))).analyticAt p

theorem analyticAt_locSol {p : RawData d L N₀ k N} (hp : p ∈ approxDomain G a ν)
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) (i : Fin N) :
    AnalyticAt ℂ (fun q : RawData d L N₀ k N => locSol G a ν q.1 q.2 y i) p := by
  classical
  have hpos := hp.1 y hy
  by_cases hy1 : y ∈ G.Ω 1
  · have hmem : (p.1 y, p.2 y) ∈ cDomain (ι := Fin N) (a (G.layerIndex y)) (blockMass G ν y) := by
      simpa [locBlend, hy1, cDomain] using hpos
    have hout := analyticOnNhd_cMinimizer_coord (ι := Fin N) (a (G.layerIndex y))
      (blockMass G ν y) i _ hmem
    have hin : AnalyticAt ℂ (fun q : RawData d L N₀ k N => ((q.1 y, q.2 y) :
        (Fin N → ℂ) × (Fin N → ℂ))) p := by
      refine AnalyticAt.prod ?_ ?_
      · exact (((ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Torus d (N₀ * L ^ k) => Fin N → ℂ) y).comp
            (ContinuousLinearMap.fst ℂ _ _))).analyticAt p
      · exact (((ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Torus d (N₀ * L ^ k) => Fin N → ℂ) y).comp
            (ContinuousLinearMap.snd ℂ _ _))).analyticAt p
    have hout' : AnalyticAt ℂ (fun r : (Fin N → ℂ) × (Fin N → ℂ) =>
        cMinimizer (a (G.layerIndex y)) (blockMass G ν y) r.1 r.2 i)
        ((fun q : RawData d L N₀ k N => ((q.1 y, q.2 y) : (Fin N → ℂ) × (Fin N → ℂ))) p) := hout
    have := AnalyticAt.comp (f := fun q : RawData d L N₀ k N =>
      ((q.1 y, q.2 y) : (Fin N → ℂ) × (Fin N → ℂ))) hout' hin
    simpa [locSol, hy1, Function.comp_def] using this
  · have hmem : (p.1 y, (0 : Fin N → ℂ)) ∈ cDomain (ι := Fin N) (1 : ℝ) (0 : ℝ) := by
      simpa [locBlend, hy1, cDomain] using hpos
    have hout := analyticOnNhd_cMinimizer_coord (ι := Fin N) (1 : ℝ) (0 : ℝ) i _ hmem
    have hin : AnalyticAt ℂ (fun q : RawData d L N₀ k N => ((q.1 y, (0 : Fin N → ℂ)) :
        (Fin N → ℂ) × (Fin N → ℂ))) p := by
      refine AnalyticAt.prod ?_ analyticAt_const
      exact (((ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Torus d (N₀ * L ^ k) => Fin N → ℂ) y).comp
            (ContinuousLinearMap.fst ℂ _ _))).analyticAt p
    have hout' : AnalyticAt ℂ (fun r : (Fin N → ℂ) × (Fin N → ℂ) => cMinimizer (1 : ℝ) (0 : ℝ) r.1 r.2 i)
        ((fun q : RawData d L N₀ k N => ((q.1 y, (0 : Fin N → ℂ)) : (Fin N → ℂ) × (Fin N → ℂ))) p) :=
      hout
    have := AnalyticAt.comp (f := fun q : RawData d L N₀ k N =>
      ((q.1 y, (0 : Fin N → ℂ)) : (Fin N → ℂ) × (Fin N → ℂ))) hout' hin
    simpa [locSol, hy1, Function.comp_def] using this


theorem analyticAt_interp {p : RawData d L N₀ k N} (hp : p ∈ approxDomain G a ν)
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    AnalyticAt ℂ (fun q : RawData d L N₀ k N => interp G (locSol G a ν q.1 q.2) x i) p := by
  simp only [interp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.analyticAt_fun_sum _ fun q hq => analyticAt_const.mul ?_
  obtain ⟨⟨hm1, hmk⟩, hql, -⟩ := (mem_blockIdx G).1 hq
  exact analyticAt_locSol G a ν hp
    ((mem_dataSites G).2 (Or.inl (G.layer_subset hm1 hmk hql))) i

theorem analyticAt_normalize_interp {p : RawData d L N₀ k N} (hp : p ∈ approxDomain G a ν)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hn : 2 ≤ G.layerIndex x) (i : Fin N) :
    AnalyticAt ℂ (fun q : RawData d L N₀ k N =>
      normalize (interp G (locSol G a ν q.1 q.2) x) i) p := by
  have hdot : AnalyticAt ℂ (fun q : RawData d L N₀ k N =>
      interp G (locSol G a ν q.1 q.2) x ⬝ᵥ interp G (locSol G a ν q.1 q.2) x) p := by
    unfold dotProduct
    exact Finset.analyticAt_fun_sum _ fun j _ =>
      (analyticAt_interp G a ν hp x j).mul (analyticAt_interp G a ν hp x j)
  have hre := hp.2 x hx hn
  have hslit : (interp G (locSol G a ν p.1 p.2) x ⬝ᵥ interp G (locSol G a ν p.1 p.2) x) ∈
      Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hre)
  have hsq : AnalyticAt ℂ (fun q : RawData d L N₀ k N =>
      sqrtDot (interp G (locSol G a ν q.1 q.2) x)) p := hdot.cpow analyticAt_const hslit
  have hne : sqrtDot (interp G (locSol G a ν p.1 p.2) x) ≠ 0 := sqrtDot_ne_zero_of_re hre
  simp only [normalize, Pi.smul_apply, smul_eq_mul]
  exact (hsq.inv hne).mul (analyticAt_interp G a ν hp x i)

/-- **Analyticity of the approximate field** in the data. -/
theorem approxField_analytic {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G) (i : Fin N) :
    AnalyticOnNhd ℂ (fun q : RawData d L N₀ k N => approxField G a ν q.1 q.2 x i)
      (approxDomain G a ν) := by
  classical
  intro p hp
  by_cases hx1 : x ∈ G.Ω 1
  · by_cases hl : G.layerIndex x ≤ 1
    · have : (fun q : RawData d L N₀ k N => approxField G a ν q.1 q.2 x i) =
          fun q => locSol G a ν q.1 q.2 x i := by
        funext q; simp [approxField, hx1, hl]
      rw [this]; exact analyticAt_locSol G a ν hp hx i
    · have : (fun q : RawData d L N₀ k N => approxField G a ν q.1 q.2 x i) =
          fun q => normalize (interp G (locSol G a ν q.1 q.2) x) i := by
        funext q; simp [approxField, hx1, hl]
      rw [this]; exact analyticAt_normalize_interp G a ν hp hx1 (by omega) i
  · have hc : x ∈ collar G := ((mem_dataSites G).1 hx).resolve_left hx1
    have : (fun q : RawData d L N₀ k N => approxField G a ν q.1 q.2 x i) =
        fun q => locSol G a ν q.1 q.2 x i := by
      funext q; simp [approxField, hx1, hc]
    rw [this]; exact analyticAt_locSol G a ν hp hx i


theorem analyticAt_ite_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {P : Prop}
    [Decidable P] {f : E → ℂ} {p : E} (hf : P → AnalyticAt ℂ f p) :
    AnalyticAt ℂ (fun q => if P then f q else 0) p := by
  by_cases h : P
  · simpa [h] using hf h
  · simpa [h] using (analyticAt_const : AnalyticAt ℂ (fun _ : E => (0 : ℂ)) p)

/-- The residual written through the raw data (the right-hand side of the formula (10)). -/
noncomputable def residualRaw (Ψ h φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (x : G.Ω 1)
    (i : Fin N) : ℂ :=
  ((a (G.layerIndex x.1) / ((L : ℝ) ^ G.layerIndex x.1) ^ 2 : ℝ) : ℂ) *
        (Ψ x.1 i - ((((((L : ℝ) ^ G.layerIndex x.1) ^ d)⁻¹ : ℝ)) : ℂ) *
          ∑ y ∈ G.blk (G.layerIndex x.1) x.1, φ y i) +
      (ν : ℂ) * (h x.1 i - φ x.1 i) +
      ∑ μ : Fin d, (φ (x.1 + Pi.single μ 1) i + φ (x.1 - Pi.single μ 1) i - 2 * φ x.1 i) +
      ∑ μ : Fin d, ((if x.1 + Pi.single μ 1 ∈ collar G then
          Ψ (x.1 + Pi.single μ 1) i - φ (x.1 + Pi.single μ 1) i else 0) +
        (if x.1 - Pi.single μ 1 ∈ collar G then
          Ψ (x.1 - Pi.single μ 1) i - φ (x.1 - Pi.single μ 1) i else 0))

theorem residual_eq_raw (D : BgData G N) (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (x : G.Ω 1)
    (i : Fin N) : residual G a ν D φ (x, i) = residualRaw G a ν D.Ψ D.h φ x i :=
  residual_apply D φ x i

/-- **Analyticity of the residual** in the data. -/
theorem residualRaw_analytic (x : G.Ω 1) (i : Fin N) :
    AnalyticOnNhd ℂ (fun q : RawData d L N₀ k N =>
      residualRaw G a ν q.1 q.2 (approxField G a ν q.1 q.2) x i) (approxDomain G a ν) := by
  classical
  intro p hp
  have hx := x.2
  obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
  have hxd : x.1 ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
  have hnb : ∀ z, Adj x.1 z → z ∈ dataSites G := fun z hz => by
    by_cases h : z ∈ G.Ω 1
    · exact (mem_dataSites G).2 (Or.inl h)
    · exact (mem_dataSites G).2 (Or.inr (mem_collar_of_adj G hx h hz))
  have hφ : ∀ z ∈ dataSites G, AnalyticAt ℂ
      (fun q : RawData d L N₀ k N => approxField G a ν q.1 q.2 z i) p :=
    fun z hz => approxField_analytic G a ν hz i p hp
  unfold residualRaw
  refine AnalyticAt.add (AnalyticAt.add (AnalyticAt.add ?_ ?_) ?_) ?_
  · refine analyticAt_const.mul ((analyticAt_rawΨ x.1 i p).sub (analyticAt_const.mul ?_))
    refine Finset.analyticAt_fun_sum _ fun y hy => hφ y ?_
    exact (mem_dataSites G).2 (Or.inl (G.layer_subset hn1 hnk
      (mem_layer_of_mem_blk G hn1 hnk hxl hy)))
  · exact analyticAt_const.mul ((analyticAt_rawh x.1 i p).sub (hφ _ hxd))
  · refine Finset.analyticAt_fun_sum _ fun μ _ => ?_
    exact (((hφ _ (hnb _ (adj_add x.1 μ))).add (hφ _ (hnb _ (adj_sub x.1 μ)))).sub
      (analyticAt_const.mul (hφ _ hxd)))
  · refine Finset.analyticAt_fun_sum _ fun μ _ => ?_
    exact (analyticAt_ite_zero fun _ => (analyticAt_rawΨ _ i p).sub (hφ _ (hnb _ (adj_add x.1 μ)))).add
      (analyticAt_ite_zero fun _ => (analyticAt_rawΨ _ i p).sub (hφ _ (hnb _ (adj_sub x.1 μ))))


variable {G a ν}

/-- The complex data of `Lemma 5.3` lie in the domain of analyticity. -/
theorem data_mem_approxDomain {δ ε : ℝ} (S : ApproxSetting d L k ϱ a ν δ ε) {D : BgData G N}
    (W : DataWit G ν δ ε D) (hδ : δ ≤ approxDelta d L) :
    ((D.Ψ, D.h) : RawData d L N₀ k N) ∈ approxDomain G a ν := by
  obtain ⟨hδ1, hs⟩ := approxDelta_le d L hδ
  refine ⟨fun y hy => ?_, fun x hx hn => ?_⟩
  · obtain ⟨-, -, hre, -⟩ := locSol_facts S W hy
    have : (1 / 8 : ℝ) ≤ (locBlend G a ν (D.Ψ, D.h) y ⬝ᵥ locBlend G a ν (D.Ψ, D.h) y).re := by
      unfold locBlend; exact hre
    linarith
  · obtain ⟨hm1, hmk, hxl⟩ := G.layerIndex_spec hx
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    obtain ⟨hdot, -, -, -⟩ := locSol_facts S W hxd
    have hnorm := locSol_norm_le S W hxd
    have h1 := interp_close S W hn hmk hxl
    have hδ0 := S.hδ0
    have hA : cA1 d L * δ ≤ 1 / 100 :=
      (mul_le_mul_of_nonneg_right (cA1_le_cA2 d L) hδ0.le).trans hs
    obtain ⟨-, hz, -, -⟩ := sqrt_facts (ref := locSol G a ν D.Ψ D.h x) hdot hnorm
      (by have := cA1_pos d L; positivity) hA h1
    have h2 : |((interp G (locSol G a ν D.Ψ D.h) x ⬝ᵥ interp G (locSol G a ν D.Ψ D.h) x) - 1).re| ≤
        5 * (cA1 d L * δ) := (Complex.abs_re_le_norm _).trans hz
    have h3 : ((interp G (locSol G a ν D.Ψ D.h) x ⬝ᵥ interp G (locSol G a ν D.Ψ D.h) x) - 1).re =
        (interp G (locSol G a ν D.Ψ D.h) x ⬝ᵥ interp G (locSol G a ν D.Ψ D.h) x).re - 1 := by simp
    rw [h3] at h2
    have := (abs_le.1 h2).1
    show 0 < (interp G (locSol G a ν D.Ψ D.h) x ⬝ᵥ interp G (locSol G a ν D.Ψ D.h) x).re
    linarith

end Analytic

end Balaban.Background
