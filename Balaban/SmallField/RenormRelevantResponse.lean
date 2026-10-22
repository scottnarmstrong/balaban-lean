/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormRelevantConst
public import Balaban.Background.Theorem52Analytic
public import Balaban.Background.BgFieldTwoTorusEquiv

/-!
# The first-order response of the background at the constant datum

For a whole-lattice level, the datum `Ψ_s = e + s ψ'`, `h̃ = e` with a layer-constant transverse
perturbation `ψ'` (`e · ψ' = 0`) lies in the complex union domain for small `|s|`, and the background
`(bgFieldC, bgMultC)` of `Ψ_s` is differentiable at `s = 0` (`theorem52_analytic`).  Differentiating (EL) at
the constant solution `(e, 0)` gives the first-order response (P4 (5.8), at `λ = ∞`):
`H_0 φ¹ = a Q* ψ'`, `e · φ¹ = 0`, `α¹ = 0`, i.e. `φ¹ = a G Q* ψ'` with `G = (−Δ + aQ*Q + ν)^{-1}`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Matrix

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {n : ℕ}

theorem BgData.ext' {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ) (hh : D.h = D'.h) : D = D' := by
  cases D; cases D'; simp only at hΨ hh; subst hΨ; subst hh; rfl

/-- The line of data `Ψ_s = e + s ψ'`, `h̃ = e`. -/
noncomputable def lineBg (hG : IsLevel G n) (e : Fin N → ℂ) (ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hψ' : IsLayerConstant G ψ') (s : ℂ) : BgData G N where
  Ψ := fun x i => e i + s * ψ' x i
  h := fun _ => e
  Ψ_layerConst := fun m hm1 hmk x hx x' hx' => by
    funext i; simp only [hψ' m hm1 hmk x hx x' hx']
  h_layerConst := fun _ _ _ _ _ _ _ => rfl
  Ψ_zero := fun x hx => absurd (by rw [hG.dataSites_eq]; exact Finset.mem_univ x) hx
  h_zero := fun x hx => absurd (hG x).1 hx

theorem lineBg_zero (hG : IsLevel G n) (eR : Fin N → ℝ) (ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hψ' : IsLayerConstant G ψ') :
    lineBg hG (fun i => (eR i : ℂ)) ψ' hψ' 0 =
      constBg hG ((1 + (0 : ℂ)) • fun i => (eR i : ℂ)) (fun i => (eR i : ℂ)) := by
  refine BgData.ext' ?_ ?_
  · funext x i; simp [lineBg, constBg]
  · rfl

/-- A uniform bound of the (finitely many) vectors `ψ' x`. -/
theorem exists_bound_layer (ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, vn (ψ' x) ≤ C) ∧ ∀ x x', vn (fun i => ψ' x i - ψ' x' i) ≤ C := by
  classical
  refine ⟨2 * ∑ x, vn (ψ' x), mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => vn_nonneg _),
    fun x => ?_, fun x x' => ?_⟩
  · have := Finset.single_le_sum (f := fun x => vn (ψ' x)) (fun y _ => vn_nonneg _) (Finset.mem_univ x)
    have h0 : 0 ≤ ∑ x, vn (ψ' x) := Finset.sum_nonneg fun y _ => vn_nonneg _
    linarith
  · have h1 := Finset.single_le_sum (f := fun x => vn (ψ' x)) (fun y _ => vn_nonneg _) (Finset.mem_univ x)
    have h2 := Finset.single_le_sum (f := fun x => vn (ψ' x)) (fun y _ => vn_nonneg _) (Finset.mem_univ x')
    have h3 : vn (fun i => ψ' x i - ψ' x' i) ≤ vn (ψ' x) + vn (ψ' x') := by
      have := vn_add' (ψ' x) (fun i => -ψ' x' i)
      have h4 : vn (fun i => -ψ' x' i) = vn (ψ' x') := by
        have := vn_smul_complex (-1) (ψ' x')
        simpa using this
      simp only [← sub_eq_add_neg] at this
      linarith
    linarith

/-- **The line of data lies in the complex union domain for small `|s|`.** -/
theorem inUnionDomainC_line {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν) (hG : IsLevel G n)
    (eR : Fin N → ℝ) (heR : ∑ i, eR i ^ 2 = 1) (ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hψ' : IsLayerConstant G ψ') (hperp : ∀ x, ∑ i, (eR i : ℂ) * ψ' x i = 0) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℂ, ‖s‖ ≤ s₀ →
      InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (lineBg hG (fun i => (eR i : ℂ)) ψ' hψ' s) := by
  classical
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨C, hC0, hCx, hCd⟩ := exists_bound_layer ψ'
  have hc1 : 0 < bgC1 d L N := by
    have h0 := bgC0_pos d L N hd0
    have hK := bgK1_pos d L N
    have hC := lemma53Const_pos d L
    have ha : 0 < approxDelta d L := approxDelta_pos d L
    have hδs := deltaStar_pos d L N hd0
    unfold bgC1; positivity
  set δ : ℝ := min 1 (bgC1 d L N) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos hc1
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδc : δ ≤ bgC1 d L N := min_le_right _ _
  refine ⟨δ / (2 * (C + 1)), by positivity, fun s hs => ?_⟩
  have hsC : ‖s‖ * C ≤ δ / 2 := by
    have : ‖s‖ * (2 * (C + 1)) ≤ δ := by
      calc ‖s‖ * (2 * (C + 1)) ≤ δ / (2 * (C + 1)) * (2 * (C + 1)) :=
            mul_le_mul_of_nonneg_right hs (by positivity)
        _ = δ := by field_simp
    nlinarith [norm_nonneg s]
  have hνε : ν * ((L : ℝ) ^ k) ^ 2 * δ ^ 2 ≤ δ ^ 2 := mul_le_of_le_one_left (sq_nonneg _) H.massLe
  have hδ0c : δ ≤ bgC0 d L N := hδc.trans (bgC1_le_bgC0 d L N hd0)
  refine ⟨δ, δ, hδ0, le_rfl, hδ0c, hδc, hνε, fun _ i => eR i, eR, fun x i => s * ψ' x i,
    fun _ _ => 0, ?_, fun x _ i => ?_, fun x _ i => ?_⟩
  · have hP := (inPsiTildeC_constBg (G := G) eR heR (ν := ν) hδ0 hδ1 0 (by simp; positivity))
    refine
      { hP.toInPsiTilde with
        eps_pos := hδ0
        layerConst' := fun m hm1 hmk x hx x' hx' => by
          funext i; simp only [hψ' m hm1 hmk x hx x' hx']
        hLayerConst' := fun _ _ _ _ _ _ _ => rfl
        c1 := fun x x' _ => ?_
        c2a := fun x _ => ?_
        c2b := fun x _ => ?_
        c3a := fun x _ => ?_
        c3b := fun x _ => ?_ }
    · have e : (fun i => s * ψ' x i) - (fun i => s * ψ' x' i) =
          fun i => s * (ψ' x i - ψ' x' i) := by funext i; simp; ring
      rw [e, vn_smul_complex]
      have := hCd x x'
      nlinarith [norm_nonneg s]
    · rw [show (fun i => s * ψ' x i) = fun i => s * ψ' x i from rfl, vn_smul_complex]
      have := hCx x
      nlinarith [norm_nonneg s]
    · have e : ∑ i, ((eR i : ℂ) + s * ψ' x i) * ((eR i : ℂ) + s * ψ' x i) -
          ∑ i, (eR i : ℂ) * (eR i : ℂ) = s ^ 2 * ∑ i, ψ' x i * ψ' x i := by
        have hp := hperp x
        calc _ = ∑ i, (2 * s * ((eR i : ℂ) * ψ' x i) + s ^ 2 * (ψ' x i * ψ' x i)) := by
              rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
          _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp]; ring
      rw [e, norm_mul, norm_pow]
      have h1 : ‖∑ i, ψ' x i * ψ' x i‖ ≤ vn (ψ' x) ^ 2 := by
        rw [vn_sq]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, sq]
      have h2 := hCx x
      have h3 : vn (ψ' x) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (vn_nonneg _) h2 2
      have h4 : ‖s‖ ^ 2 * C ^ 2 ≤ (δ / 2) ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hsC 2
      have h5 : ‖s‖ ^ 2 * ‖∑ i, ψ' x i * ψ' x i‖ ≤ (δ / 2) ^ 2 :=
        (mul_le_mul_of_nonneg_left (h1.trans h3) (by positivity)).trans h4
      nlinarith
    · have h0 : vn ((fun (_ : Torus d (N₀ * L ^ k)) (_ : Fin N) => (0 : ℂ)) x) = 0 := vn_zero
      rw [h0, mul_zero]; positivity
    · simp only [mul_zero, Finset.sum_const_zero, norm_zero]; positivity
  · simp [lineBg]
  · simp [lineBg]

open Filter Topology in
/-- **The first-order response of the background (P4 (5.8) at `λ = ∞`).**  For a whole-lattice level
and a layer-constant transverse perturbation `ψ'` (`e · ψ' = 0`), the background of the data
`(e + s ψ', e)` is differentiable at `s = 0`; its derivative `φ¹` and the derivative `α¹` of the multiplier
satisfy `α¹ = 0`, `H_0 φ¹ = Q* a ψ'` and `e · φ¹ = 0`. -/
theorem response_transverse {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν) (hG : IsLevel G n)
    (eR : Fin N → ℝ) (heR : ∑ i, eR i ^ 2 = 1) (ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hψ' : IsLayerConstant G ψ') (hperp : ∀ x, ∑ i, (eR i : ℂ) * ψ' x i = 0) :
    ∃ (φ1 : G.Ω 1 × Fin N → ℂ) (α1 : G.Ω 1 → ℂ),
      HasDerivAt (fun s : ℂ => bgFieldC G a ν (bgC0 d L N)
        (lineBg hG (fun i => (eR i : ℂ)) ψ' hψ' s)) φ1 0 ∧
      HasDerivAt (fun s : ℂ => bgMultC G a ν (bgC0 d L N)
        (lineBg hG (fun i => (eR i : ℂ)) ψ' hψ' s)) α1 0 ∧ α1 = 0 ∧
      liftOp N (dirichletOperator G a ν 0) *ᵥ φ1 = qStar G a ψ' ∧
      ∀ x : G.Ω 1, ∑ i, (eR i : ℂ) * φ1 (x, i) = 0 := by
  classical
  set e : Fin N → ℂ := fun i => (eR i : ℂ) with he
  have hd0 : 0 < d := by have := H.hd; omega
  have hdot : ∑ i, eR i * eR i = 1 := by simpa [sq] using heR
  have hdotC : ∑ i, e i * e i = 1 := by simp only [he]; exact_mod_cast hdot
  obtain ⟨F, hFan, hFval⟩ := theorem52_analytic (G := G) (a := a) (ν := ν) (N := N) H
  obtain ⟨s₀, hs₀, hdom⟩ := inUnionDomainC_line H hG eR heR ψ' hψ' hperp
  let g : ℂ → RawData d L N₀ k N := fun s => ((fun x i => e i + s * ψ' x i), fun _ => e)
  have hg : ∀ s, g s = ((lineBg hG e ψ' hψ' s).Ψ, (lineBg hG e ψ' hψ' s).h) := fun s => rfl
  -- the background is `F ∘ g` near 0
  have hFg : ∀ s : ℂ, ‖s‖ ≤ s₀ → F (g s) = (bgFieldC G a ν (bgC0 d L N) (lineBg hG e ψ' hψ' s),
      bgMultC G a ν (bgC0 d L N) (lineBg hG e ψ' hψ' s)) := fun s hs => by
    obtain ⟨-, hsm, -⟩ := theorem72 H (hdom s hs)
    rw [hg]; exact hFval _ (hdom s hs) _ _ hsm
  have hEL : ∀ s : ℂ, ‖s‖ ≤ s₀ → IsEL G a ν (lineBg hG e ψ' hψ' s) (F (g s)).1 (F (g s)).2 := fun s hs => by
    obtain ⟨-, hsm, -⟩ := theorem72 H (hdom s hs)
    rw [hFg s hs]; exact hsm.1
  -- the value at `s = 0`
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
  -- differentiability of `F ∘ g` at `0`
  have hg0 : g 0 ∈ {p | ∃ D : BgData G N,
      InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)} :=
    ⟨lineBg hG e ψ' hψ' 0, hdom 0 (by simpa using hs₀.le), rfl⟩
  have hFd : DifferentiableAt ℂ F (g 0) := (hFan (g 0) hg0).differentiableAt
  have hgd : HasDerivAt g ((fun x i => ψ' x i), fun _ _ => (0 : ℂ)) 0 := by
    refine HasDerivAt.prodMk (hasDerivAt_pi.2 fun x => hasDerivAt_pi.2 fun i => ?_)
      (hasDerivAt_pi.2 fun x => hasDerivAt_pi.2 fun i => hasDerivAt_const _ _)
    have := ((hasDerivAt_id (0 : ℂ)).mul_const (ψ' x i)).const_add (e i)
    simpa using this
  have hcomp := hFd.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hgd
  have hφd := (hasFDerivAt_fst (𝕜 := ℂ)).comp_hasDerivAt (0 : ℂ) hcomp
  have hαd := (hasFDerivAt_snd (𝕜 := ℂ)).comp_hasDerivAt (0 : ℂ) hcomp
  set φ1 : G.Ω 1 × Fin N → ℂ := (fderiv ℂ F (g 0) ((fun x i => ψ' x i), fun _ _ => (0 : ℂ))).1 with hφ1
  set α1 : G.Ω 1 → ℂ := (fderiv ℂ F (g 0) ((fun x i => ψ' x i), fun _ _ => (0 : ℂ))).2 with hα1
  have hφ : HasDerivAt (fun s => (F (g s)).1) φ1 0 := hφd
  have hα : HasDerivAt (fun s => (F (g s)).2) α1 0 := hαd
  have hnhds : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ ≤ s₀ := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hs₀] with s hs
    simpa using hs
  -- the constraint
  have hcon : ∀ x : G.Ω 1, ∑ i, e i * φ1 (x, i) = 0 := fun x => by
    have hd : ∀ i, HasDerivAt (fun s => (F (g s)).1 (x, i)) (φ1 (x, i)) 0 := fun i =>
      (hasDerivAt_pi.1 hφ) (x, i)
    have hsq : HasDerivAt (fun s => ∑ i, (F (g s)).1 (x, i) * (F (g s)).1 (x, i))
        (∑ i, (φ1 (x, i) * (F (g 0)).1 (x, i) + (F (g 0)).1 (x, i) * φ1 (x, i))) 0 :=
      HasDerivAt.fun_sum fun i _ => (hd i).mul (hd i)
    have hone : HasDerivAt (fun s => ∑ i, (F (g s)).1 (x, i) * (F (g s)).1 (x, i)) 0 0 := by
      refine (hasDerivAt_const (0 : ℂ) (1 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with s hs
      exact (hEL s hs).2 x
    have := hsq.unique hone
    rw [hF0] at this
    simp only [] at this
    have h2 : (2 : ℂ) * ∑ i, e i * φ1 (x, i) = 0 := by
      rw [← this, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  -- the first-order (EL)
  set A : Matrix (G.Ω 1) (G.Ω 1) ℂ := dirichletOperator G a ν 0 with hA
  set w : ℂ := ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) with hw
  have hφ0 : (F (g 0)).1 = fun p => e p.2 := by rw [hF0]
  have hα0 : (F (g 0)).2 = fun _ => 0 := by rw [hF0]
  have hD : ∀ (x : G.Ω 1) (i : Fin N),
      (∑ y, A x y * φ1 (y, i)) + α1 x * e i = w * ψ' x i := fun x i => by
    have hd : ∀ q, HasDerivAt (fun s => (F (g s)).1 q) (φ1 q) 0 := fun q => (hasDerivAt_pi.1 hφ) q
    have hda : HasDerivAt (fun s => (F (g s)).2 x) (α1 x) 0 := (hasDerivAt_pi.1 hα) x
    have hL : HasDerivAt (fun s => (∑ y, A x y * (F (g s)).1 (y, i)) + (F (g s)).2 x * (F (g s)).1 (x, i))
        ((∑ y, A x y * φ1 (y, i)) + (α1 x * (F (g 0)).1 (x, i) + (F (g 0)).2 x * φ1 (x, i))) 0 :=
      (HasDerivAt.fun_sum fun y _ => (hd (y, i)).const_mul (A x y)).add (hda.mul (hd (x, i)))
    have hR : HasDerivAt (fun s : ℂ => w * (e i + s * ψ' x i) + ν * e i) (w * ψ' x i) 0 := by
      have := (((hasDerivAt_id (0 : ℂ)).mul_const (ψ' x i)).const_add (e i)).const_mul w |>.add_const
        ((ν : ℂ) * e i)
      simpa using this
    have heq : (fun s => (∑ y, A x y * (F (g s)).1 (y, i)) + (F (g s)).2 x * (F (g s)).1 (x, i)) =ᶠ[𝓝 0]
        fun s : ℂ => w * (e i + s * ψ' x i) + ν * e i := by
      filter_upwards [hnhds] with s hs
      have h1 := liftOp_dirichlet_add (G := G) a ν 0 (F (g s)).2 (F (g s)).1 (x, i)
      rw [zero_add] at h1
      have h2 := congrFun (hEL s hs).1 (x, i)
      rw [h1, liftOp_mulVec_apply] at h2
      rw [h2]
      have hlay : G.layerIndex (x : Torus d (N₀ * L ^ k)) = n := (hG x).2
      simp [source, qStar, boundaryTerm, hG.collar_eq, lineBg, hlay, hw]
    have := hL.unique (hR.congr_of_eventuallyEq heq)
    rw [hφ0, hα0] at this
    simpa using this
  have hα1z : α1 = 0 := by
    funext x
    have h1 : ∑ i, e i * (∑ y, A x y * φ1 (y, i)) = 0 := by
      calc _ = ∑ y, A x y * ∑ i, e i * φ1 (y, i) := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := Finset.sum_eq_zero fun y _ => by rw [hcon y, mul_zero]
    have h2 : ∑ i, e i * ((∑ y, A x y * φ1 (y, i)) + α1 x * e i) = w * ∑ i, e i * ψ' x i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hD x i]; ring
    have h3 : ∑ i, e i * ψ' x i = 0 := hperp x
    simp only [mul_add, Finset.sum_add_distrib] at h2
    have h4 : ∑ i, e i * (α1 x * e i) = α1 x := by
      calc _ = α1 x * ∑ i, e i * e i := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        _ = α1 x := by rw [hdotC, mul_one]
    rw [h1, h4, h3] at h2
    simpa using h2
  refine ⟨φ1, α1, ?_, ?_, hα1z, ?_, hcon⟩
  · refine hφ.congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with s hs
    rw [hFg s hs]
  · refine hα.congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with s hs
    rw [hFg s hs]
  · funext ⟨x, i⟩
    rw [liftOp_mulVec_apply]
    have := hD x i
    rw [hα1z] at this
    simpa [qStar, (hG x).2, hw] using this

open Filter Topology in
/-- **The response is `a G Q* ψ'`**: the derivative of the background at the constant datum in the
transverse direction `ψ'` is the image of the source `Q* a ψ'` under the Green function
`G = (−Δ + aQ*Q + ν)^{-1}` (`greenD` at `α = 0`), componentwise. -/
theorem response_transverse_green {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν) (hG : IsLevel G n)
    (eR : Fin N → ℝ) (heR : ∑ i, eR i ^ 2 = 1) (ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hψ' : IsLayerConstant G ψ') (hperp : ∀ x, ∑ i, (eR i : ℂ) * ψ' x i = 0) :
    ∃ φ1 : G.Ω 1 × Fin N → ℂ,
      HasDerivAt (fun s : ℂ => bgFieldC G a ν (bgC0 d L N)
        (lineBg hG (fun i => (eR i : ℂ)) ψ' hψ' s)) φ1 0 ∧
      φ1 = liftOp N (greenD G a ν 0) *ᵥ qStar G a ψ' := by
  obtain ⟨φ1, α1, h1, -, -, hH, -⟩ := response_transverse H hG eR heR ψ' hψ' hperp
  refine ⟨φ1, h1, ?_⟩
  have hd0 : 0 < d := by have := H.hd; omega
  have hU : IsUnit (dirichletOperator G a ν (0 : G.Ω 1 → ℂ)) :=
    (H.green (G := G)).isUnit (α := 0) fun x => by
      simp only [Pi.zero_apply, norm_zero, mul_zero]; exact (gamma1_pos hd0).le
  have := liftOp_inv_mulVec (G := G) (N := N) hU φ1
  rw [hH] at this
  exact this.symm

end Balaban.Fluctuation
