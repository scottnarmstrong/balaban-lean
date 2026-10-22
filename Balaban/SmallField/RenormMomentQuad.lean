/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormMomentJets
public import Balaban.SmallField.RenormRelevantResponse

/-!
# The second variation of `C₁` along a transverse line at the constant datum

For a whole-lattice level, data `Ψ(s) = e + s ψ'`, `h̃ = e` with `ψ' ⟂ e` layer-constant, and a
background `φ(s)` with `φ(0) = e`, coordinate jets `(e, φ¹, φ²)` and the constraint
`e · φ² = -|φ¹|²` at every site, the function `s ↦ C₁(Ψ(s), φ(s))` has second derivative at `0`
equal to (`secondVar`)

`ξ₃ ⟨X¹, X¹⟩_w + (1+ξ₃) (ζ (2 ⟨ψ', X¹⟩_w + ⟨φ¹, φ¹⟩_w) + ζ² ⟨ψ', ψ'⟩_w) + ξ₃ ⟨∂φ¹, ∂φ¹⟩ + ν ξ₂ ⟨φ¹, φ¹⟩`,

`X¹ = ψ' - Q φ¹`, `⟨·,·⟩_w` the weighted pairing `blockPair`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Flow Finset Matrix

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ} {n : ℕ}

/-- The second variation of `C₁` (see the module docstring). -/
noncomputable def secondVar (G : GeneratingSet d L N₀ K ϱ) (a : ℕ → ℝ) (ν ξ₂ ξ₃ ζ : ℝ)
    (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ) (φ1 : G.Ω 1 × Fin N → ℂ) : ℂ :=
  (ξ₃ : ℂ) * blockPair G a (fun x i => ψ' x i - blockAvg G φ1 x i)
      (fun x i => ψ' x i - blockAvg G φ1 x i) +
    (1 + (ξ₃ : ℂ)) * ((ζ : ℂ) * (2 * blockPair G a ψ' (fun x i => ψ' x i - blockAvg G φ1 x i) +
        blockPair G a (svec G φ1) (svec G φ1)) + (ζ : ℂ) ^ 2 * blockPair G a ψ' ψ') +
    (ξ₃ : ℂ) * bondPair G ψ' φ1 + ((ν * ξ₂ : ℝ) : ℂ) * massPair G (fun _ _ => 0) φ1

theorem blockPair_zero_left (a : ℕ → ℝ) (B : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    blockPair G a (fun _ _ => 0) B = 0 := by simp [blockPair]

theorem blockPair_zero_right (a : ℕ → ℝ) (A : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    blockPair G a A (fun _ _ => 0) = 0 := by simp [blockPair]

theorem blockPair_zero_sub_right (a : ℕ → ℝ) (A f : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    blockPair G a A (fun x i => 0 - f x i) = -blockPair G a A f := by
  unfold blockPair
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem isJet_affine (c b : ℂ) : IsJet (fun s => c + s * b) c b 0 := by
  have := (isJet_const c).add (isJet_id.mul (isJet_const b))
  refine this.of_eq (by simp) (by simp) (by simp)

theorem isJet_secondVar (hG : IsLevel G n) (a : ℕ → ℝ) (ν ξ₂ ξ₃ ζ : ℝ) (e : Fin N → ℂ)
    (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ) (D : ℂ → BgData G N)
    (hΨ : ∀ s, (D s).Ψ = fun x i => e i + s * ψ' x i) (hh : ∀ s, (D s).h = fun _ => e)
    (φ : ℂ → G.Ω 1 × Fin N → ℂ) (φ1 φ2 : G.Ω 1 × Fin N → ℂ)
    (hφ : VJet φ (fun p => e p.2) φ1 φ2)
    (hcon : ∀ x : G.Ω 1, ∑ i, e i * φ2 (x, i) = -∑ i, φ1 (x, i) * φ1 (x, i)) :
    ∃ c0 c1 : ℂ, IsJet (fun s => renormC1 G a ν ξ₂ ξ₃ ζ (D s) (φ s)) c0 c1
      (secondVar G a ν ξ₂ ξ₃ ζ ψ' φ1) := by
  classical
  have hΨj : ∀ x i, IsJet (fun s => (D s).Ψ x i) (e i) (ψ' x i) 0 := fun x i => by
    refine (isJet_affine (e i) (ψ' x i)).of_funext fun s => ?_
    simp only [hΨ]
  have hXj : ∀ x i, IsJet (fun s => (D s).Ψ x i - blockAvg G (φ s) x i) 0
      (ψ' x i - blockAvg G φ1 x i) (0 - blockAvg G φ2 x i) := fun x i => by
    have := (hΨj x i).sub (vjet_blockAvg hφ x i)
    rw [blockAvg_const hG e x i] at this
    exact this.of_eq (sub_self _) rfl rfl
  set X0 : Torus d (N₀ * L ^ K) → Fin N → ℂ := fun _ _ => 0 with hX0
  set X1 : Torus d (N₀ * L ^ K) → Fin N → ℂ := fun x i => ψ' x i - blockAvg G φ1 x i with hX1
  set X2 : Torus d (N₀ * L ^ K) → Fin N → ℂ := fun x i => 0 - blockAvg G φ2 x i with hX2
  set E0 : Torus d (N₀ * L ^ K) → Fin N → ℂ := fun _ i => e i with hE0
  set Z : Torus d (N₀ * L ^ K) → Fin N → ℂ := fun _ _ => 0 with hZ
  have j1 := isJet_blockPair (G := G) a (A := fun s x i => (D s).Ψ x i - blockAvg G (φ s) x i)
    (B := fun s x i => (D s).Ψ x i - blockAvg G (φ s) x i) (A0 := X0) (A1 := X1) (A2 := X2)
    (B0 := X0) (B1 := X1) (B2 := X2) hXj hXj
  have j2 := isJet_blockPair (G := G) a (A := fun s x i => (D s).Ψ x i)
    (B := fun s x i => (D s).Ψ x i - blockAvg G (φ s) x i) (A0 := E0) (A1 := ψ') (A2 := Z)
    (B0 := X0) (B1 := X1) (B2 := X2) hΨj hXj
  have j3 := isJet_blockPair (G := G) a (A := fun s x i => (D s).Ψ x i)
    (B := fun s x i => (D s).Ψ x i) (A0 := E0) (A1 := ψ') (A2 := Z)
    (B0 := E0) (B1 := ψ') (B2 := Z) hΨj hΨj
  have hflat : ∀ x μ i, barField G E0 (fun p : G.Ω 1 × Fin N => e p.2) (x + Pi.single μ 1) i =
      barField G E0 (fun p : G.Ω 1 × Fin N => e p.2) x i := fun x μ i => by
    rw [barField_const hG E0 e, barField_const hG E0 e]
  have j4 := isJet_bondPair (G := G) (Ψ := fun s => (D s).Ψ) (Ψ0 := E0) (Ψ1 := ψ') (Ψ2 := Z)
    hΨj hφ hflat
  have j5 := isJet_massPair (G := G) (fun _ => e) hφ (fun x i => rfl)
  have j5' : IsJet (fun s => massPair G (D s).h (φ s)) 0 0 (2 * massPair G (fun _ _ => 0) φ1) :=
    j5.of_funext fun s => by rw [hh s]
  -- the longitudinal term
  have hlong : blockPair G a E0 (fun x i => blockAvg G φ2 x i) =
      -blockPair G a (svec G φ1) (svec G φ1) := by
    have := sum_blockAvg (G := G) (a := a) (g := fun i _ => e i)
      (fun i x _ y _ => rfl) φ2
    unfold blockPair
    simp only [hE0]
    rw [this]
    rw [← Finset.sum_neg_distrib]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hc := hcon x
    simp only [svec_of_mem]
    have h2 : ∑ i, ((a (G.layerIndex (x : Torus d (N₀ * L ^ K))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2 : ℝ) : ℂ) * e i * φ2 (x, i) =
        ((a (G.layerIndex (x : Torus d (N₀ * L ^ K))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2 : ℝ) : ℂ) * ∑ i, e i * φ2 (x, i) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, hc]; ring
  have F1 := j1.const_mul ((ξ₃ : ℂ) / 2)
  have F2 := ((j2.const_mul (ζ : ℂ)).add (j3.const_mul ((ζ : ℂ) ^ 2 / 2))).const_mul (1 + (ξ₃ : ℂ))
  have F4 := j4.const_mul ((ξ₃ : ℂ) / 2)
  have F5 := j5'.const_mul (((ν * ξ₂ : ℝ) : ℂ) / 2)
  have tot := ((F1.add F2).add F4).add F5
  refine ⟨_, _, (tot.of_funext fun s => rfl).of_eq rfl rfl ?_⟩
  simp only [hX0, hZ, blockPair_zero_left, blockPair_zero_right, hX2, blockPair_zero_sub_right, hlong]
  unfold secondVar
  ring


open Filter Topology in
/-- **The second derivative of `C₁` along a transverse line at the constant datum.** -/
theorem deriv2_renormC1_line {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L K ϱ a ν) (hG : IsLevel G n)
    (eR : Fin N → ℝ) (heR : ∑ i, eR i ^ 2 = 1) (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (hψ' : IsLayerConstant G ψ') (hperp : ∀ x, ∑ i, (eR i : ℂ) * ψ' x i = 0) (ξ₂ ξ₃ ζ : ℝ) :
    deriv (deriv (fun s : ℂ => renormC1 G a ν ξ₂ ξ₃ ζ (lineBg hG (fun i => (eR i : ℂ)) ψ' hψ' s)
        (bgFieldC G a ν (bgC0 d L N) (lineBg hG (fun i => (eR i : ℂ)) ψ' hψ' s)))) 0 =
      secondVar G a ν ξ₂ ξ₃ ζ ψ'
        (liftOp N (greenD G a ν 0) *ᵥ qStar G a ψ') := by
  classical
  set e : Fin N → ℂ := fun i => (eR i : ℂ) with he
  obtain ⟨F, hFan, hFval⟩ := theorem52_analytic (G := G) (a := a) (ν := ν) (N := N) H
  obtain ⟨s₀, hs₀, hdom⟩ := inUnionDomainC_line H hG eR heR ψ' hψ' hperp
  let g : ℂ → RawData d L N₀ K N := fun s => ((fun x i => e i + s * ψ' x i), fun _ => e)
  have hg : ∀ s, g s = ((lineBg hG e ψ' hψ' s).Ψ, (lineBg hG e ψ' hψ' s).h) := fun s => rfl
  have hFg : ∀ s : ℂ, ‖s‖ ≤ s₀ → F (g s) = (bgFieldC G a ν (bgC0 d L N) (lineBg hG e ψ' hψ' s),
      bgMultC G a ν (bgC0 d L N) (lineBg hG e ψ' hψ' s)) := fun s hs => by
    obtain ⟨-, hsm, -⟩ := theorem72 H (hdom s hs)
    rw [hg]; exact hFval _ (hdom s hs) _ _ hsm
  have hEL : ∀ s : ℂ, ‖s‖ ≤ s₀ → IsEL G a ν (lineBg hG e ψ' hψ' s) (F (g s)).1 (F (g s)).2 :=
    fun s hs => by
    obtain ⟨-, hsm, -⟩ := theorem72 H (hdom s hs)
    rw [hFg s hs]; exact hsm.1
  have hnhds : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ ≤ s₀ := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hs₀] with s hs
    simpa using hs
  have hg0 : g 0 ∈ {p | ∃ D : BgData G N,
      InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)} :=
    ⟨lineBg hG e ψ' hψ' 0, hdom 0 (by simpa using hs₀.le), rfl⟩
  have hgan : AnalyticAt ℂ g 0 := by
    refine AnalyticAt.prod (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
      (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => analyticAt_const)
    exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hcomp : AnalyticAt ℂ (fun s => (F (g s)).1) 0 :=
    analyticAt_fst.comp ((hFan (g 0) hg0).comp hgan)
  have hcoord : ∀ q, AnalyticAt ℂ (fun s => (F (g s)).1 q) 0 := fun q =>
    (analyticAt_pi_iff.1 hcomp) q
  set φ0 : G.Ω 1 × Fin N → ℂ := fun q => (F (g 0)).1 q with hφ0
  set φ1 : G.Ω 1 × Fin N → ℂ := fun q => deriv (fun s => (F (g s)).1 q) 0 with hφ1
  set φ2 : G.Ω 1 × Fin N → ℂ := fun q => deriv (deriv (fun s => (F (g s)).1 q)) 0 with hφ2
  have hV : VJet (fun s => (F (g s)).1) φ0 φ1 φ2 := fun q => isJet_of_analyticAt (hcoord q)
  have hd0 : 0 < d := by have := H.hd; omega
  have hc1 : 0 < bgC1 d L N := by
    have h0 := bgC0_pos d L N hd0
    have hK := bgK1_pos d L N
    have hC := lemma53Const_pos d L
    have ha : 0 < approxDelta d L := approxDelta_pos d L
    have hδs := deltaStar_pos d L N hd0
    unfold bgC1; positivity
  have hF0 : F (g 0) = ((fun p : G.Ω 1 × Fin N => e p.2), fun _ => (0 : ℂ)) := by
    rw [hFg 0 (by simpa using hs₀.le), lineBg_zero hG eR ψ' hψ']
    have hb := bgFieldC_const H hG eR heR (δ := min 1 (bgC1 d L N)) (lt_min one_pos hc1)
      (min_le_left _ _) (min_le_right _ _) 0 (by simp; positivity)
      (by simpa using bgC0_pos d L N hd0)
    rw [hb.1, hb.2]
    simp; rfl
  have hφ0e : φ0 = fun p => e p.2 := by
    funext q; simp only [hφ0, hF0]
  have hV' : VJet (fun s => bgFieldC G a ν (bgC0 d L N) (lineBg hG e ψ' hψ' s)) (fun p => e p.2)
      φ1 φ2 := fun q => by
    rw [← hφ0e]
    refine (hV q).congr ?_
    filter_upwards [hnhds] with s hs
    rw [hFg s hs]
  have hcon : ∀ x : G.Ω 1, ∑ i, e i * φ2 (x, i) = -∑ i, φ1 (x, i) * φ1 (x, i) := fun x => by
    have hj := IsJet.sum (Finset.univ : Finset (Fin N)) fun i _ => (hV (x, i)).mul (hV (x, i))
    have hc : IsJet (fun s => ∑ i, (F (g s)).1 (x, i) * (F (g s)).1 (x, i)) 1 0 0 := by
      refine (isJet_const (1 : ℂ)).congr ?_
      filter_upwards [hnhds] with s hs
      exact ((hEL s hs).2 x).symm
    obtain ⟨-, -, h3⟩ := hj.unique hc
    rw [hφ0e] at h3
    have : ∑ i, (φ2 (x, i) * e i + 2 * φ1 (x, i) * φ1 (x, i) + e i * φ2 (x, i)) =
        2 * (∑ i, e i * φ2 (x, i) + ∑ i, φ1 (x, i) * φ1 (x, i)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this] at h3
    have := mul_eq_zero.1 h3
    rcases this with h | h
    · exact absurd h two_ne_zero
    · linear_combination h
  obtain ⟨c0, c1, hjet⟩ := isJet_secondVar hG a ν ξ₂ ξ₃ ζ e ψ' (fun s => lineBg hG e ψ' hψ' s)
    (fun s => rfl) (fun s => rfl)
    (fun s => bgFieldC G a ν (bgC0 d L N) (lineBg hG e ψ' hψ' s)) φ1 φ2 hV' hcon
  rw [hjet.deriv2]
  obtain ⟨φ1', hφ1', hφ1eq⟩ := response_transverse_green H hG eR heR ψ' hψ' hperp
  have : φ1 = φ1' := by
    funext q
    exact (hV' q).hasDerivAt.unique ((hasDerivAt_pi.1 hφ1') q)
  rw [← hφ1eq, ← this]

end Balaban.Fluctuation
