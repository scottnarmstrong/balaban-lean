/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CubeFoldRow
public import Balaban.Multiscale.CutPointwise
public import Balaban.Multiscale.PointwiseGeom
public import Balaban.Multiscale.PointwisePotential

/-!
# The local Poisson bound for the folded cut solution (VMOD-9, (2.2) and (2.3))

* `cutU G cut w x = |w(x)| + ℓ(x) ∑_{μ : (x,μ) ∉ cut} |w(x + e_μ) - w(x)|`, the retained forward
  quantity `U_D` of VMOD-9 (1.2);
* `cubeFold_local_poisson_bound` (2.2): for the folded field `w(z) = ũ(P(z))` of the solution of
  `H_cut(α) u = f`, the lattice Laplacian of `w` on a ball of radius `R` with `d (R + 1) ≤ L^{j-1}`
  around a layer-`j` point `x` of the cube is bounded by `|f̃(P z)| + (3 + Λ₀) L^{-2(j-1)} M`, where
  `M` bounds `U_D` near `x`;
* `cubeFold_local_cutU_eq` (2.3): `U_D(x) = |w(0)| + L^j ∑_μ |w(e_μ) - w(0)|`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Reflection Balaban.LatticeGreen Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The retained forward quantity** `U_D(x) = |w(x)| + ℓ(x) ∑_{(x,μ) ∉ cut} |w(x+e_μ) - w(x)|`. -/
noncomputable def cutU (G : GeneratingSet d L N₀ k ϱ)
    (cut : Finset (Torus d (N₀ * L ^ k) × Fin d)) (w : Torus d (N₀ * L ^ k) → ℂ)
    (x : Torus d (N₀ * L ^ k)) : ℝ :=
  ‖w x‖ + G.spacing x * ∑ μ : Fin d,
    (if (x, μ) ∈ cut then 0 else ‖w (x + Pi.single μ 1) - w x‖)

theorem cutU_nonneg (G : GeneratingSet d L N₀ k ϱ) (cut : Finset (Torus d (N₀ * L ^ k) × Fin d))
    (w : Torus d (N₀ * L ^ k) → ℂ) (x : Torus d (N₀ * L ^ k)) : 0 ≤ cutU G cut w x := by
  have : 0 ≤ G.spacing x := (spacing_pos G).le
  unfold cutU
  have : 0 ≤ ∑ μ : Fin d, (if (x, μ) ∈ cut then (0 : ℝ) else ‖w (x + Pi.single μ 1) - w x‖) :=
    Finset.sum_nonneg fun μ _ => by split_ifs <;> positivity
  positivity

theorem norm_le_cutU (G : GeneratingSet d L N₀ k ϱ) (cut : Finset (Torus d (N₀ * L ^ k) × Fin d))
    (w : Torus d (N₀ * L ^ k) → ℂ) (x : Torus d (N₀ * L ^ k)) : ‖w x‖ ≤ cutU G cut w x := by
  have h := cutU_nonneg G cut w x
  unfold cutU at h ⊢
  have : 0 ≤ G.spacing x * ∑ μ : Fin d,
      (if (x, μ) ∈ cut then (0 : ℝ) else ‖w (x + Pi.single μ 1) - w x‖) := by
    have := (spacing_pos G (x := x)).le
    have : 0 ≤ ∑ μ : Fin d, (if (x, μ) ∈ cut then (0 : ℝ) else ‖w (x + Pi.single μ 1) - w x‖) :=
      Finset.sum_nonneg fun μ _ => by split_ifs <;> positivity
    positivity
  linarith

theorem norm_add_single_le (h : Fin d → ℤ) (μ : Fin d) : ‖h + Pi.single μ 1‖ ≤ ‖h‖ + 1 := by
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  by_cases hi : i = μ
  · subst hi; simp
  · simp [hi]

theorem norm_sub_single_le (h : Fin d → ℤ) (μ : Fin d) : ‖h - Pi.single μ 1‖ ≤ ‖h‖ + 1 := by
  refine (norm_sub_le _ _).trans (add_le_add_right ?_ _)
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  by_cases hi : i = μ
  · subst hi; simp
  · simp [hi]

/-- Membership of the lifted neighbours of a local fold point in `Ω₁`. -/
theorem cubeFold_lift_data (S : ℕ) [NeZero S]
    (c : Fin d → ℕ) (p0 : Torus d (2 * S)) {j : ℕ}
    {x : Torus d (N₀ * L ^ k)}
    (hp0 : foldMap (N₀ * L ^ k) S (2 * S) c p0 = x) {z : Fin d → ℤ}
    (hz : (d : ℝ) * (‖z‖ + 1) ≤ (L : ℝ) ^ (j - 1)) :
    ∃ h : Fin d → ℤ, cubeFoldPt N₀ L k S c p0 z = liftPt x h ∧ (d : ℝ) * ‖h‖ ≤ (L : ℝ) ^ (j - 1) ∧
      ((d : ℝ) * (‖h‖ + 1) ≤ (L : ℝ) ^ (j - 1)) := by
  obtain ⟨h, hh, hP⟩ := cubeFoldPt_disp (N₀ := N₀) (L := L) (k := k) S c p0 z
  rw [cubeFoldPt_zero, hp0] at hP
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨h, hP, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (hh.trans (by linarith)) hd0).trans hz
  · exact (mul_le_mul_of_nonneg_left (by linarith) hd0).trans hz

/-- **VMOD-9 (2.2).** The lattice Laplacian of the folded solution is bounded by the source and by
the retained quantity `U_D` near the centre. -/
theorem cubeFold_local_poisson_bound (G : GeneratingSet d L N₀ k ϱ) (hϱ : 1 ≤ ϱ)
    {a : ℕ → ℝ} {ν Λ₀ : ℝ} (hν : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ Λ₀)
    (ha : IsAdmissibleWeights k a) {α : G.Ω 1 → ℂ}
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (hSℓ : S < N₀ * L ^ k)
    {u f : G.Ω 1 → ℂ}
    (hu : cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α *ᵥ u = f)
    {j : ℕ} (hj2 : 2 ≤ j) (hjk : j ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j)
    (p0 : Torus d (2 * S)) (hp0 : foldMap (N₀ * L ^ k) S (2 * S) c p0 = x)
    {z : Fin d → ℤ} (hz : (d : ℝ) * (‖z‖ + 1) ≤ (L : ℝ) ^ (j - 1)) {M : ℝ} (hM0 : 0 ≤ M)
    (hα : ∀ y, ‖α y‖ ≤ coerciveConst d / (2 * (G.spacing y) ^ 2))
    (hM : ∀ q ∈ G.Ω 1, G.pathDist q x ≤ ENNReal.ofReal (2 * d + 1) →
      cutU G (cubeCut G (cubeSet (N₀ * L ^ k) S c)) (zeroExt (G.Ω 1) u) q ≤ M) :
    ‖negLap (fun w => zeroExt (G.Ω 1) u (cubeFoldPt N₀ L k S c p0 w)) z‖ ≤
      ‖zeroExt (G.Ω 1) f (cubeFoldPt N₀ L k S c p0 z)‖ +
        (3 + Λ₀) * (((L : ℝ) ^ (j - 1)) ^ 2)⁻¹ * M := by
  classical
  have hLpos : (0 : ℝ) < (L : ℝ) ^ (j - 1) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  obtain ⟨h, hP, hdh, hdh1⟩ := cubeFold_lift_data S c p0 hp0 hz
  set p := cubeFoldPt N₀ L k S c p0 z with hpdef
  obtain ⟨hpΩ, hlo, -⟩ := lift_mem_layers G hϱ hj2 hjk hx (z := h) hdh
  rw [← hP] at hpΩ hlo
  obtain ⟨-, hpd⟩ := pathDist_lift_le G hϱ hj2 hjk hx hdh
  rw [← hP] at hpd
  have hpd1 : G.pathDist p x ≤ ENNReal.ofReal 1 := by
    refine hpd.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_one hLpos]
    exact hdh
  -- the collar
  have hcol : ∀ μ : Fin d,
      (p + Pi.single μ 1 ∉ cubeSet (N₀ * L ^ k) S c → p + Pi.single μ 1 ∈ G.Ω 1) ∧
      (p - Pi.single μ 1 ∉ cubeSet (N₀ * L ^ k) S c → p - Pi.single μ 1 ∈ G.Ω 1) := by
    intro μ
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · have := (lift_mem_layers G hϱ hj2 hjk hx (z := h + Pi.single μ 1)
        ((mul_le_mul_of_nonneg_left (norm_add_single_le h μ) (Nat.cast_nonneg d)).trans hdh1)).1
      rwa [liftPt_add_single, ← hP] at this
    · have := (lift_mem_layers G hϱ hj2 hjk hx (z := h - Pi.single μ 1)
        ((mul_le_mul_of_nonneg_left (norm_sub_single_le h μ) (Nat.cast_nonneg d)).trans hdh1)).1
      rwa [liftPt_sub_single, ← hP] at this
  have hrow := cubeFold_local_neumann_row G S c hSℓ p0 z hcol (zeroExt (G.Ω 1) u)
  rw [← hpdef] at hrow
  -- the equation at `p`
  have hS : 0 < S := Nat.pos_of_ne_zero (NeZero.ne S)
  have h2 : 2 ≤ N₀ * L ^ k := by omega
  have heq := cutOperator_eq G hu ⟨p, hpΩ⟩
  unfold cutFullMatrix at heq
  rw [Matrix.map_add (algebraMap ℝ ℂ) (map_add _), Matrix.add_mulVec, Pi.add_apply,
    cutLaplacian_mulVec_complex_row h2] at heq
  have hx' : zeroExt (G.Ω 1) u p = u ⟨p, hpΩ⟩ := zeroExt_mem _ _ ⟨p, hpΩ⟩
  have hfp : zeroExt (G.Ω 1) f p = f ⟨p, hpΩ⟩ := zeroExt_mem _ _ ⟨p, hpΩ⟩
  rw [hrow]
  have hrowEq : ∑ μ : Fin d, ((if (p, μ) ∈ cubeCut G (cubeSet (N₀ * L ^ k) S c) then 0
        else zeroExt (G.Ω 1) u p - zeroExt (G.Ω 1) u (p + Pi.single μ 1)) +
      (if (p - Pi.single μ 1, μ) ∈ cubeCut G (cubeSet (N₀ * L ^ k) S c) then 0
        else zeroExt (G.Ω 1) u p - zeroExt (G.Ω 1) u (p - Pi.single μ 1))) =
      f ⟨p, hpΩ⟩ - ν * u ⟨p, hpΩ⟩ - α ⟨p, hpΩ⟩ * u ⟨p, hpΩ⟩ -
        ((avgMatrix G a).map (algebraMap ℝ ℂ) *ᵥ zeroExt (G.Ω 1) u) p := by
    rw [hx'] at heq ⊢
    linear_combination heq
  rw [hrowEq]
  -- bound the right side
  have hM' : ∀ q, jBlock d L N₀ k (G.layerIndex p) q = jBlock d L N₀ k (G.layerIndex p) p →
      ‖zeroExt (G.Ω 1) u q‖ ≤ M := by
    intro q hq
    obtain ⟨hm1, hmk, hpl⟩ := G.layerIndex_spec hpΩ
    have hql : q ∈ G.layer (G.layerIndex p) := (G.mem_layer_iff hm1 hmk hq).2 hpl
    have hqΩ : q ∈ G.Ω 1 := G.layer_subset hm1 hmk hql
    have h1 := G.pathDist_block_le hm1 hmk hpl hq
    rw [GeneratingSet.pathDist_comm] at h1
    have h2 : G.pathDist q x ≤ ENNReal.ofReal (2 * d + 1) := by
      refine (G.pathDist_triangle q p x).trans ?_
      calc _ ≤ ENNReal.ofReal (2 * d) + ENNReal.ofReal 1 := add_le_add h1 hpd1
        _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) zero_le_one]
    exact (norm_le_cutU G _ _ q).trans (hM q hqΩ h2)
  have hspk : G.spacing p ≤ (L : ℝ) ^ k := spacing_le G hpΩ
  have hsp0 : 0 < G.spacing p := spacing_pos G
  set s := G.spacing p with hs
  have hux : ‖u ⟨p, hpΩ⟩‖ ≤ M := by
    have := hM' p rfl
    rwa [hx'] at this
  have hΛ0 : 0 ≤ Λ₀ := le_trans (by positivity) hν1
  have hν' : ν ≤ Λ₀ * (s ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc ν * s ^ 2 ≤ ν * ((L : ℝ) ^ k) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsp0.le hspk 2) hν
      _ ≤ Λ₀ := hν1
  have hαx : ‖α ⟨p, hpΩ⟩‖ ≤ (s ^ 2)⁻¹ := by
    refine (hα ⟨p, hpΩ⟩).trans ?_
    have h1 : coerciveConst d ≤ 1 / 4 := by
      unfold coerciveConst; linarith [poincareConst_le_half d]
    have : coerciveConst d / (2 * s ^ 2) ≤ (1 / 4) / (2 * s ^ 2) := by
      gcongr
    refine this.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : (s ^ 2)⁻¹ * (2 * s ^ 2) = 2 := by field_simp
    nlinarith [this]
  have hq := avg_row_bound G ha hpΩ (zeroExt (G.Ω 1) u) hM0 hM'
  rw [← hs] at hq
  rw [hfp]
  have hsp_lo : ((s ^ 2)⁻¹) ≤ (((L : ℝ) ^ (j - 1)) ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ hLpos.le hlo 2
  calc _ ≤ ‖f ⟨p, hpΩ⟩‖ + ‖(ν : ℂ) * u ⟨p, hpΩ⟩‖ + ‖α ⟨p, hpΩ⟩ * u ⟨p, hpΩ⟩‖ +
        ‖((avgMatrix G a).map (algebraMap ℝ ℂ) *ᵥ zeroExt (G.Ω 1) u) p‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖f ⟨p, hpΩ⟩‖ + Λ₀ * (s ^ 2)⁻¹ * M + (s ^ 2)⁻¹ * M + 2 * (s ^ 2)⁻¹ * M := by
        gcongr
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hν]
          exact mul_le_mul hν' hux (norm_nonneg _) (by positivity)
        · rw [norm_mul]
          exact mul_le_mul hαx hux (norm_nonneg _) (by positivity)
    _ = ‖f ⟨p, hpΩ⟩‖ + (3 + Λ₀) * (s ^ 2)⁻¹ * M := by ring
    _ ≤ _ := by
        gcongr

/-- **VMOD-9 (2.3).** At the centre `x` of the local fold (with `p₀` in the lower half) the retained
forward quantity is `|w(0)| + L^j ∑_μ |w(e_μ) - w(0)|`. -/
theorem cubeFold_local_cutU_eq (G : GeneratingSet d L N₀ k ϱ) (hϱ : 1 ≤ ϱ)
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (hSℓ : S < N₀ * L ^ k)
    {j : ℕ} (hj2 : 2 ≤ j) (hjk : j ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j)
    (hdj : (d : ℝ) ≤ (L : ℝ) ^ (j - 1)) (p0 : Torus d (2 * S))
    (hp0 : foldMap (N₀ * L ^ k) S (2 * S) c p0 = x) (hlow : ∀ i, (p0 i).val < S)
    (ut : Torus d (N₀ * L ^ k) → ℂ) :
    cutU G (cubeCut G (cubeSet (N₀ * L ^ k) S c)) ut x =
      ‖ut (cubeFoldPt N₀ L k S c p0 0)‖ + (L : ℝ) ^ j * ∑ μ : Fin d,
        ‖ut (cubeFoldPt N₀ L k S c p0 (Pi.single μ 1)) - ut (cubeFoldPt N₀ L k S c p0 0)‖ := by
  classical
  have hx0 : cubeFoldPt N₀ L k S c p0 0 = x := by rw [cubeFoldPt_zero, hp0]
  have hxΛ : x ∈ cubeSet (N₀ * L ^ k) S c := by rw [← hx0]; exact cubeFoldPt_mem S c p0 0
  have hj1 : 1 ≤ j := by omega
  unfold cutU
  rw [G.spacing_eq hj1 hjk hx, hx0]
  congr 2
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [cubeFoldPt_single_up S c p0 hSℓ hlow μ, hx0]
  have hcol : x + Pi.single μ 1 ∉ cubeSet (N₀ * L ^ k) S c → x + Pi.single μ 1 ∈ G.Ω 1 := by
    intro _
    have := (lift_mem_layers G hϱ hj2 hjk hx (z := (Pi.single μ 1 : Fin d → ℤ))
      (by
        have : ‖(Pi.single μ 1 : Fin d → ℤ)‖ ≤ 1 := by
          rw [pi_norm_le_iff_of_nonneg zero_le_one]
          intro i
          by_cases hi : i = μ
          · subst hi; simp
          · simp [hi]
        exact (mul_le_mul_of_nonneg_left this (Nat.cast_nonneg d)).trans (by linarith))).1
    have e := liftPt_add_single x 0 μ
    rw [zero_add, liftPt_zero] at e
    rwa [e] at this
  have hc := mem_cubeCut_up_iff G hxΛ μ hcol
  unfold stepUpT
  by_cases h1 : x + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c
  · have : (x, μ) ∉ cubeCut G (cubeSet (N₀ * L ^ k) S c) := by
      rw [hc]; exact fun h => h h1
    simp [h1, this]
  · have : (x, μ) ∈ cubeCut G (cubeSet (N₀ * L ^ k) S c) := hc.2 h1
    simp [h1, this]

end Balaban.Localization
