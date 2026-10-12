/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.LayerV2
public import Balaban.Observables.ImprovedConst
public import Balaban.SmallField.Def6v2Inhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-O v2: a member with a nonzero constant-spin response (theorem (b)) -- DRAFT

**Draft, pending Roland's answer to Q13.**  CLASS-RULINGS-2 item 4 ("the P0 vacuity
certificate").

The landed `IsObs` with `LiftCtx` and `β_k ν_k ≤ 1` forces `M^{(j)}(x; e_i, w) = 0` for every
constant complex `w` (`Mobs_const_eq_zero_massFree`): at zero background mass the landed domain
contains the whole complex line of constant fields `h`, and a bounded entire function is constant
(Liouville).  In the second version the backgrounds are complete (Scheme A, W2-RESOLVE §§3-4): the
background mass is positive whenever the physical mass is (`Regime.sfBgMass_pos`), so that branch
does not occur.  The main instance (wide domain) is inhabited by `isObs2_xi_witness`; on the pinned
alternative domain the line is finite, and:

* `pinObs`: the observable terms `M^{(j)}(x, X; Ψ, h) = c_j e^{-κ|X|²} (h(x)·h(x) - 1) h(x)` on the
  whole-torus polymer (the observable layer of the field-dependent member `Def6v2.pinTerms`);
* `isObs2_pinObs`: they satisfy every clause of `IsObs2` on a field domain on which `‖h‖ ≤ 2`
  (the pinned domain with `r_h ≤ 1`), including the axial normalization `M^{(j)}(x; h, h) = 0` and
  the identification (O4) with the generating function of `pinTerms`;
* `pinObs_response_ne_zero`: **the constant-spin response is not zero**:
  `M^{(j)}(x; e, (1+s) e) ≠ 0` for `s > 0`; `pin_const_near`: the constant pairs `(e, c)` with `c`
  close to `e` lie in the pinned domain, at every background mass;
* `pinObs_not_landed`: **these terms are not the observable layer of any member of the landed
  class in the mass-free regime** (they would have to vanish at every constant `h`): the zero of
  `Mobs_const_eq_zero_massFree` is an artifact of the landed domain, not a property of the pinned
  class;
* `obsSourceForm_pinObs`: the source form `ObsSourceForm` of these terms, with the mass-weighted
  derivative constant `C_D = 1/5`;
* `isObs2_pin_witness`, `obs_pinned_response`: the concrete member (`d = L = 3`, `N = 2`).
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
open Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The coefficients of the observable terms: `c^O_j = √β_{j-1} c_j` (so that
`β_{j-1}^{-1/2} M^{(j)} = ℳ^{(j)}`, (2.4)). -/
noncomputable def obsCoef (β cj : ℕ → ℝ) : ℕ → ℝ := fun j => Real.sqrt (β (j - 1)) * cj j

/-- **The observable terms of the field-dependent member**: `μ_j = 0`,
`M^{(j)}(x, X; Ψ, h) = c^O_j e^{-κ|X|²} (h(x)·h(x) - 1) h(x)` on the whole-torus polymer, `R = 0`. -/
noncomputable def pinObs (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁] (κ : ℝ) (cO : ℕ → ℝ) :
    ObsTerms d L N₁ m₁ k N where
  μ := fun _ _ => 0
  M := fun j x X _ h => ((wCoef κ cO j X : ℝ) : ℂ) • mCore (h x)
  R := fun _ _ _ _ _ _ _ => 0

omit [NeZero L] [NeZero N₁] in
theorem wCoef_obsCoef (κ : ℝ) (β cj : ℕ → ℝ) (j : ℕ) (X : Set (CTorus d L N₁ m₁ k)) :
    wCoef κ (obsCoef β cj) j X = Real.sqrt (β (j - 1)) * wCoef κ cj j X := by
  unfold wCoef obsCoef
  split_ifs
  · ring
  · simp

theorem Mobs_pinObs (m₀ : ℕ) (κ : ℝ) (cO : ℕ → ℝ) (j : ℕ) (x : CTorus d L N₁ m₁ k)
    (Ψ h : Fld d L N₁ m₁ k N) :
    Mobs m₀ (pinObs d L N₁ m₁ k N κ cO) j x Ψ h =
      ((wCoef κ cO j (Set.univ : Set (CTorus d L N₁ m₁ k)) : ℝ) : ℂ) • mCore (h x) := by
  unfold Mobs
  rw [finsum_mem_single_supp _ _ Set.univ (fun X hX => by simp [pinObs, wCoef, hX])]
  have hmem : (Set.univ : Set (CTorus d L N₁ m₁ k)) ∈ polysAt m₀ j x :=
    ⟨isPolyDom_univ m₀ j, Set.mem_univ x⟩
  simp only [hmem, ↓reduceIte]
  rfl

theorem Robs_pinObs (m₀ : ℕ) (κ : ℝ) (cO : ℕ → ℝ) (i j : ℕ) (x x' : CTorus d L N₁ m₁ k)
    (Ψ h : Fld d L N₁ m₁ k N) : Robs m₀ (pinObs d L N₁ m₁ k N κ cO) i j x x' Ψ h = 0 := by
  simp [Robs, pinObs]

/-! ### The generating function of the field-dependent member is linear in `g` -/

/-- The linear functional `g ↦ ∑_x ∑_i g_i(x) c_i(x)`. -/
noncomputable def linF (c : Fld d L N₁ m₁ k N) : Fld d L N₁ m₁ k N →L[ℂ] ℂ :=
  ∑ x, ∑ i, c x i • ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ k => Fin N → ℂ) x))

theorem linF_apply (c g : Fld d L N₁ m₁ k N) : linF c g = ∑ x, ∑ i, g x i * c x i := by
  simp [linF, mul_comm]

/-- The coefficient field of the generating function of `pinTerms`:
`φ_k(x) + ∑_j c_j e^{-κ|𝕋|²} m(h)(x)`. -/
noncomputable def genCoef (κ : ℝ) (cj : ℕ → ℝ) (a : ℕ → ℝ) (ν : ℝ)
    (D : BgData (topGS d L N₁ m₁ k ϱ) N) : Fld d L N₁ m₁ k N :=
  fun x i => svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ) a ν D) x i +
    ∑ j ∈ Finset.Icc 1 k, ((wCoef κ cj j (Set.univ : Set (CTorus d L N₁ m₁ k)) : ℝ) : ℂ) *
      mCore ((composedPair a ν j D).2 x) i

theorem Fcomp_pinTerms (m₀ : ℕ) (κ : ℝ) (cj : ℕ → ℝ) (a : ℕ → ℝ) (ν : ℝ)
    (D : BgData (topGS d L N₁ m₁ k ϱ) N) :
    Fcomp m₀ (pinTerms d L N₁ m₁ k N ϱ κ cj) a ν D = ⇑(linF (genCoef κ cj a ν D)) := by
  funext g
  rw [linF_apply]
  unfold Fcomp Floc genCoef
  simp only [Mloc_pinTerms, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]

/-! ### The class clauses -/

theorem matNorm_zero : matNorm (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
  simp [matNorm]

/-- **The observable terms `pinObs` form an observable layer of the second version** on the
field-dependent member `pinTerms`, on every field domain on which `‖h‖ ≤ 2`, for every regime;
`10 √β_{j-1} c_j ≤ β^{-1/2+ρ₁} L^{-jρ₀}`. -/
theorem isObs2_pinObs {P : Consts} {Q : ObsConsts} {Rg : Regime L} {β a : ℕ → ℝ} {cj : ℕ → ℝ}
    {Dom : FieldDom d L N₁ m₁ k N ϱ} (hκ : 0 ≤ P.κ) (hc0 : ∀ j, 0 ≤ cj j) (hβ0 : 0 ≤ β 0)
    (hβ : ∀ j, 1 ≤ j → 0 < β (j - 1))
    (hcO : ∀ j, 10 * obsCoef β cj j ≤
      (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)))
    (hB : ∀ j, cj j ≠ 0 → ∀ G Ψ h, Dom.dom j G Ψ h → ∀ x, vn (h x) ≤ 2) :
    IsObs2 P Q Rg β a Dom (pinTerms d L N₁ m₁ k N ϱ P.κ cj)
      (pinObs d L N₁ m₁ k N P.κ (obsCoef β cj)) (fun _ _ _ _ _ => 0) where
  μ_euc := fun _ _ _ _ _ _ => rfl
  μ_bound := by
    intro j _ _ x
    show |(0 : ℝ)| ≤ _
    rw [abs_zero]
    exact mul_nonneg (Real.rpow_nonneg hβ0 _) (Real.rpow_nonneg (Nat.cast_nonneg L) _)
  analyticM := fun j _ _ x X _ _ p _ => by
    set T : (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N) →L[ℂ] (Fin N → ℂ) :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ k => Fin N → ℂ) x).comp
        (ContinuousLinearMap.snd ℂ _ _) with hT
    have h1 : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => mCore (T p)) p :=
      (mCore_analyticAt (T p)).comp (T.analyticAt p)
    have h0 : AnalyticAt ℂ (fun _ : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
        ((wCoef P.κ (obsCoef β cj) j X : ℝ) : ℂ)) p := analyticAt_const
    exact h0.smul h1
  analyticR := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => analyticOnNhd_const
  rotM := by
    intro j _ _ x X _ _ R hR Ψ h _ _
    show ((wCoef P.κ (obsCoef β cj) j X : ℝ) : ℂ) • mCore (R *ᵥ h x) =
      R *ᵥ (((wCoef P.κ (obsCoef β cj) j X : ℝ) : ℂ) • mCore (h x))
    rw [mCore_rot hR.1, Matrix.mulVec_smul]
  rotR := by
    intro i j _ _ _ x x' X _ _ _ R _ Ψ h _ _
    show (0 : Matrix (Fin N) (Fin N) ℂ) = R * 0 * R.transpose
    simp
  eucM := by
    intro j _ _ x X _ _ r _ Ψ h _ _
    show ((wCoef P.κ (obsCoef β cj) j (r '' X) : ℝ) : ℂ) • mCore (h (r.symm (r x))) =
      ((wCoef P.κ (obsCoef β cj) j X : ℝ) : ℂ) • mCore (h x)
    rw [wCoef_image, Equiv.symm_apply_apply]
  eucR := by intros; rfl
  eucMloc := by
    intro j _ hjk x r _ Ψ h _ _
    rw [Mobs_pinObs, Mobs_pinObs]
    show _ • mCore (h (r.symm (r x))) = _
    rw [Equiv.symm_apply_apply]
  eucRloc := by
    intro i j _ _ hjk x x' r _ Ψ h _ _
    rw [Robs_pinObs, Robs_pinObs]
  localM := by
    intro j x X Ψ Ψ' h h' hloc
    show ((wCoef P.κ (obsCoef β cj) j X : ℝ) : ℂ) • mCore (h x) =
      ((wCoef P.κ (obsCoef β cj) j X : ℝ) : ℂ) • mCore (h' x)
    by_cases hX : X = Set.univ
    · rw [(hloc x (hX ▸ Set.mem_univ x)).2]
    · simp [wCoef, hX]
  localR := by intros; rfl
  realM := by
    intro j _ _ x X _ _ Ψ h _ _ hh i
    show ((((wCoef P.κ (obsCoef β cj) j X : ℝ) : ℂ) • mCore (h x)) i).im = 0
    simp [Complex.mul_im, mCore_im (fun l => hh x l) i]
  realR := by
    intro i j _ _ _ x x' X _ _ _ Ψ h _ _ _ a₁ a₂
    show ((0 : Matrix (Fin N) (Fin N) ℂ) a₁ a₂).im = 0
    simp
  boundM := by
    intro j _ _ x X hX _ Ψ h hd
    have hcO0 : ∀ j, 0 ≤ obsCoef β cj j := fun j =>
      mul_nonneg (Real.sqrt_nonneg _) (hc0 j)
    show vn (((wCoef P.κ (obsCoef β cj) j X : ℝ) : ℂ) • mCore (h x)) ≤ _
    have he := Real.exp_pos (-P.κ * sizeJ P.m₀ j X)
    by_cases hcj : cj j = 0
    · have hw : wCoef P.κ (obsCoef β cj) j X = 0 := by
        unfold wCoef obsCoef; split_ifs <;> simp [hcj]
      rw [hw]
      simp only [Complex.ofReal_zero, zero_smul, vn_zero]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hβ0 _)
        (Real.rpow_nonneg (Nat.cast_nonneg L) _)) he.le
    · rw [vn_smul_c, Complex.norm_real, Real.norm_of_nonneg (wCoef_nonneg hcO0 j X)]
      have h1 := vn_mCore_le (hB j hcj _ Ψ h hd x)
      have h2 := wCoef_le hκ hcO0 (m₀ := P.m₀) hX
      have h4 : wCoef P.κ (obsCoef β cj) j X * vn (mCore (h x)) ≤
          obsCoef β cj j * Real.exp (-P.κ * sizeJ P.m₀ j X) * ((2 ^ 2 + 1) * 2) :=
        mul_le_mul h2 h1 (vn_nonneg _) (mul_nonneg (hcO0 j) he.le)
      nlinarith [mul_le_mul_of_nonneg_right (hcO j) he.le]
  boundR := by
    intro i j _ _ _ x x' X _ _ _ Ψ h _
    show matNorm (0 : Matrix (Fin N) (Fin N) ℂ) ≤ _
    rw [matNorm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hβ0 _)
      (Real.rpow_nonneg (Nat.cast_nonneg L) _)) (Real.exp_pos _).le) (Real.exp_pos _).le
  normM := by
    intro j _ _ x v _ hv
    rw [Mobs_pinObs]
    show _ • mCore (fun i => (v i : ℂ)) = 0
    rw [mCore_unit hv, smul_zero]
  ident := by
    intro Ψ₀ h₀ D _ _ _
    rw [Fcomp_pinTerms]
    refine ⟨fun g _ => (linF _).analyticAt g, fun u => ?_, fun u v => ?_⟩
    · rw [ContinuousLinearMap.fderiv, linF_apply]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
      congr 1
      unfold genCoef Mk2
      have hm : mFactor β (pinObs d L N₁ m₁ k N P.κ (obsCoef β cj)) x = 1 := by
        simp [mFactor, pinObs]
      rw [hm]
      simp only [Complex.ofReal_one, one_mul, Mobs_pinObs, Pi.smul_apply, smul_eq_mul,
        wCoef_obsCoef]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
      have hs : Real.sqrt (β (j - 1)) ≠ 0 := (Real.sqrt_pos.2 (hβ j hj1)).ne'
      push_cast
      have hs' : (Real.sqrt (β (j - 1)) : ℂ) ≠ 0 := by exact_mod_cast hs
      field_simp
    · have hfd : fderiv ℂ ⇑(linF (genCoef P.κ cj (aIdeal L k (a k)) (Rg.sfBgMass k) D)) =
          fun _ => linF (genCoef P.κ cj (aIdeal L k (a k)) (Rg.sfBgMass k) D) :=
        funext fun _ => ContinuousLinearMap.fderiv _
      have hG : ∀ x x' : CTorus d L N₁ m₁ k,
          Gk2 P β a (Rg.sfBgMass k) (pinObs d L N₁ m₁ k N P.κ (obsCoef β cj))
            (fun _ _ _ _ _ => 0) D x x' = 0 := by
        intro x x'
        simp [Gk2, Ck2, Rk2, Robs_pinObs]
      simp [D2, hfd, hG]

/-! ### Theorem (b): the constant-spin response -/

/-- **The constant-spin response of `pinObs` is not zero**: `M^{(j)}(x; e, (1+s) e) ≠ 0` for
`s > 0` and `c^O_j > 0` (the sum over the polymers `X ∋ x`; the whole torus is a polymer). -/
theorem pinObs_response_ne_zero (m₀ : ℕ) {κ : ℝ} {cO : ℕ → ℝ} {j : ℕ} (hc : 0 < cO j)
    (i₀ : Fin N) {s : ℝ} (hs : 0 < s) (x : CTorus d L N₁ m₁ k) :
    Mobs m₀ (pinObs d L N₁ m₁ k N κ cO) j x (constFld (Pi.single i₀ 1))
      (constFld (((1 + s : ℝ) : ℂ) • Pi.single i₀ 1)) ≠ 0 := by
  rw [Mobs_pinObs]
  show ((wCoef κ cO j (Set.univ : Set (CTorus d L N₁ m₁ k)) : ℝ) : ℂ) •
    mCore (((1 + s : ℝ) : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)) ≠ 0
  rw [mCore_smul_single, smul_smul]
  intro h
  have h1 := congrFun h i₀
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.zero_apply] at h1
  have hw : wCoef κ cO j (Set.univ : Set (CTorus d L N₁ m₁ k)) ≠ 0 := by
    simp only [wCoef, ↓reduceIte]; positivity
  have h2 : ((1 + s : ℝ) : ℂ) ^ 2 - 1 ≠ 0 := by
    have : ((1 + s) ^ 2 - 1 : ℝ) ≠ 0 := by nlinarith
    exact_mod_cast this
  have h3 : ((1 + s : ℝ) : ℂ) ≠ 0 := by
    have : (1 + s : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have h4 : ((wCoef κ cO j (Set.univ : Set (CTorus d L N₁ m₁ k)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hw
  exact mul_ne_zero h4 (mul_ne_zero h2 h3) h1

/-- **Constant fields close to `e` are in the pinned domain** (with the constant spin `e`), at
every background mass `μ ≥ 0`: there is `s₀ > 0`, depending on `(d, L, N, ε, μ, j)` only, such that
every constant `h = c` with `|c - e| ≤ s₀` coordinatewise and `‖c - e‖ < r_h` gives a point of
`Pin e r_h` over every level-`j` generating set. -/
theorem pin_const_near {a : ℕ → ℝ} {μ : ℝ} {j : ℕ} (H : BgHyp d L k ϱ a μ) (hjk : j ≤ k)
    {ε rH : ℝ} (hε : 0 < ε) (i₀ : Fin N) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ, (∀ i, j < i → G.Ω i = ∅) →
      ∀ c : Fin N → ℂ, (∀ i, ‖c i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ s₀) →
        vn (fun i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i) < rH →
        Pin (Pi.single i₀ 1) rH G a μ j ε (constFld (Pi.single i₀ 1)) (constFld c) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hK := bgK1_pos d L N
  have hc0 := bgC0_pos d L N hd0
  have hc1 := Balaban.Localization.bgC1_pos' (d := d) (L := L) (N := N) hd0
  set δ := min (min (bgC0 d L N) (bgC1 d L N)) (ε / (2 * bgK1 d L N + 2)) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hc0 hc1) (by positivity)
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos i₀
  have hρ0 : 0 < δ ^ 2 / (2 * N) := by positivity
  have hρ : (N : ℝ) * (δ ^ 2 / (2 * N)) < δ ^ 2 := by
    have e : (N : ℝ) * (δ ^ 2 / (2 * N)) = δ ^ 2 / 2 := by field_simp
    rw [e]; linarith [pow_pos hδ0 2]
  have hε' : (2 * bgK1 d L N + 2) * δ ≤ ε := by
    have h1 : δ ≤ ε / (2 * bgK1 d L N + 2) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity), mul_comm] at h1
  have hm0 : 0 ≤ μ * ((L : ℝ) ^ j) ^ 2 := mul_nonneg H.mass (by positivity)
  have hden : 0 < μ * ((L : ℝ) ^ j) ^ 2 + 1 := by linarith
  refine ⟨δ ^ 2 / (2 * N) / (μ * ((L : ℝ) ^ j) ^ 2 + 1), div_pos hρ0 hden,
    fun G hΩ c hc hpin => ?_⟩
  exact pin_of_close (G := G) (rH := rH) H hΩ hjk i₀ hδ0
    ((min_le_left _ _).trans (min_le_left _ _)) ((min_le_left _ _).trans (min_le_right _ _)) hρ0 hρ
    hε' (constFld (Pi.single i₀ 1)) c
    (fun x i => by simpa [constFld] using hρ0.le) (fun _ _ _ => rfl)
    (fun i => by
      refine (mul_le_mul_of_nonneg_left (hc i) hm0).trans ?_
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith [hρ0, hm0]) hpin

/-- **Theorem (b): the terms `pinObs` are not the observable layer of any member of the landed
class in the mass-free regime.**  If `pinObs` satisfied the landed `IsObs` in a context `LiftCtx`
with `β_k ν_k ≤ 1`, then `Mobs_const_eq_zero_massFree` (Liouville on the unbounded complex `h`-line
of the landed domain) would give `M^{(j)}(x; e, w) = 0` for every constant `w`, contradicting
`pinObs_response_ne_zero`.  The landed zero is a Liouville artifact of the domain; on the pinned
class the response may be nonzero. -/
theorem pinObs_not_landed {P : Consts} {Q : ObsConsts} {β ν a : ℕ → ℝ}
    {Tm : Terms d L N₁ m₁ k N ϱ} {κ : ℝ} {cO : ℕ → ℝ}
    {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
      Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
    {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    {Ek : ℝ} {j : ℕ} {ρ : ℝ} (hO : IsObs P Q β ν a Tm (pinObs d L N₁ m₁ k N κ cO) Gker)
    (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hmf : β k * ν k ≤ 1) (hc : 0 < cO j) (i₀ : Fin N) :
    False :=
  pinObs_response_ne_zero P.m₀ hc i₀ one_pos (0 : CTorus d L N₁ m₁ k)
    (Mobs_const_eq_zero_massFree hO ctx hmf 0 i₀ _)

/-! ### The source form of the observable terms -/

theorem mCore_fderiv_single (i₀ : Fin N) (u : Fin N → ℂ) :
    fderiv ℂ (mCore (N := N)) (Pi.single i₀ 1) u = (2 * u i₀) • (Pi.single i₀ 1 : Fin N → ℂ) := by
  have hq : HasFDerivAt (fun v : Fin N → ℂ => ∑ l, v l * v l)
      (∑ l, ((Pi.single i₀ 1 : Fin N → ℂ) l •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l +
        (Pi.single i₀ 1 : Fin N → ℂ) l •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l))
      (Pi.single i₀ 1) :=
    HasFDerivAt.fun_sum fun l _ =>
      (hasFDerivAt_apply l (Pi.single i₀ 1 : Fin N → ℂ)).mul
        (hasFDerivAt_apply l (Pi.single i₀ 1 : Fin N → ℂ))
  have h := (hq.sub_const 1).smul (hasFDerivAt_id (𝕜 := ℂ) (Pi.single i₀ 1 : Fin N → ℂ))
  have h2 : fderiv ℂ (mCore (N := N)) (Pi.single i₀ 1) = _ := h.fderiv
  rw [h2]
  have h1 : ∑ l, (Pi.single i₀ 1 : Fin N → ℂ) l * (Pi.single i₀ 1 : Fin N → ℂ) l = 1 := by
    simp [Pi.single_apply]
  have hsum : (∑ l, ((Pi.single i₀ 1 : Fin N → ℂ) l •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l +
      (Pi.single i₀ 1 : Fin N → ℂ) l •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l)) u = 2 * u i₀ := by
    rw [_root_.sum_apply, Finset.sum_eq_single i₀]
    · simp [two_mul]
    · intro l _ hl; simp [Pi.single_eq_of_ne hl]
    · simp
  rw [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply, hsum, h1,
    sub_self, zero_smul,
    zero_add]
  rfl

/-- The reparametrized observable source terms `M̃(Ψ, b) = M(Ψ, b/ν_j)`, `R̃ = R(Ψ, b/ν_j)`. -/
noncomputable def obsSourceOf (ν : ℕ → ℝ) (Ot : ObsTerms d L N₁ m₁ k N) :
    ObsSourceTerms d L N₁ m₁ k N where
  M := fun j x X Ψ b => Ot.M j x X Ψ ((nuIdeal L k (ν k) j : ℂ)⁻¹ • b)
  R := fun i j x x' X Ψ b => Ot.R i j x x' X Ψ ((nuIdeal L k (ν k) j : ℂ)⁻¹ • b)

/-- **The source form of the observable terms `pinObs`** (positive masses), with the mass-weighted
derivative constant `C_D = 1/5`: `ν_j |D_b M̃(e, ν_j e)[u]| = 2 c^O_j e^{-κ|X|²} |u_{i₀}|`. -/
theorem obsSourceForm_pinObs {P : Consts} {Q : ObsConsts} {Rg : Regime L} {β a : ℕ → ℝ}
    {cj : ℕ → ℝ} {Dom : FieldDom d L N₁ m₁ k N ϱ} (hκ : 0 ≤ P.κ) (hc0 : ∀ j, 0 ≤ cj j)
    (hβ0 : 0 ≤ β 0) (hβ : ∀ j, 1 ≤ j → 0 < β (j - 1))
    (hcO : ∀ j, 10 * obsCoef β cj j ≤
      (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)))
    (hB : ∀ j, cj j ≠ 0 → ∀ G Ψ h, Dom.dom j G Ψ h → ∀ x, vn (h x) ≤ 2) (hν : 0 < Rg.ν k) (i₀ : Fin N) :
    ObsSourceForm P Q β Rg.ν Dom (pinTerms d L N₁ m₁ k N ϱ P.κ cj)
      (pinObs d L N₁ m₁ k N P.κ (obsCoef β cj))
      (obsSourceOf Rg.ν (pinObs d L N₁ m₁ k N P.κ (obsCoef β cj))) i₀ (1 / 5) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hνj : ∀ j, 0 < nuIdeal L k (Rg.ν k) j := fun j => by unfold nuIdeal; positivity
  have hO := isObs2_pinObs (P := P) (Q := Q) (Rg := Rg) (a := a) (ϱ := ϱ) hκ hc0 hβ0 hβ hcO hB
  have hcO0 : ∀ j, 0 ≤ obsCoef β cj j := fun j => mul_nonneg (Real.sqrt_nonneg _) (hc0 j)
  refine ⟨fun j _ _ x X _ _ Ψ h _ => ?_, fun i j _ _ _ x x' X _ _ _ Ψ h _ => rfl,
    fun j hj1 hjk x X hX hx Ψ b ⟨h, hd, hb⟩ => ?_, fun i j _ _ _ x x' X _ _ _ Ψ b _ => ?_,
    fun j _ _ x X hX _ u => ?_⟩
  · show _ = (pinObs d L N₁ m₁ k N P.κ (obsCoef β cj)).M j x X Ψ
      ((nuIdeal L k (Rg.ν k) j : ℂ)⁻¹ • ((nuIdeal L k (Rg.ν k) j : ℂ) • h))
    rw [inv_smul_smul_fld (hνj j).ne']
  · show vn ((pinObs d L N₁ m₁ k N P.κ (obsCoef β cj)).M j x X Ψ
      ((nuIdeal L k (Rg.ν k) j : ℂ)⁻¹ • b)) ≤ _
    rw [hb, inv_smul_smul_fld (hνj j).ne']
    exact hO.boundM j hj1 hjk x X hX hx Ψ h hd
  · show matNorm (0 : Matrix (Fin N) (Fin N) ℂ) ≤ _
    rw [matNorm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hβ0 _)
      (Real.rpow_nonneg (Nat.cast_nonneg L) _)) (Real.exp_pos _).le) (Real.exp_pos _).le
  · set νj := nuIdeal L k (Rg.ν k) j with hνjdef
    set w := wCoef P.κ (obsCoef β cj) j X with hw
    have hνpos : 0 < νj := hνj j
    have hνne : νj ≠ 0 := hνpos.ne'
    have hνc : (νj : ℂ) ≠ 0 := by exact_mod_cast hνne
    have e : (fun b : Fin N → ℂ =>
        (obsSourceOf Rg.ν (pinObs d L N₁ m₁ k N P.κ (obsCoef β cj))).M j x X
          (constFld (Pi.single i₀ 1)) (constFld b)) =
        fun b => (w : ℂ) • mCore ((νj : ℂ)⁻¹ • b) := rfl
    rw [e]
    have hpt : (νj : ℂ)⁻¹ • ((νj : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)) = Pi.single i₀ 1 := by
      rw [smul_smul, inv_mul_cancel₀ hνc, one_smul]
    have hm : HasFDerivAt (mCore (N := N))
        (fderiv ℂ mCore ((νj : ℂ)⁻¹ • ((νj : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ))))
        ((νj : ℂ)⁻¹ • ((νj : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ))) :=
      (mCore_analyticAt _).differentiableAt.hasFDerivAt
    have hlin : HasFDerivAt (((νj : ℂ)⁻¹) • (id : (Fin N → ℂ) → (Fin N → ℂ)))
        ((νj : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (Fin N → ℂ))
        ((νj : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)) :=
      (hasFDerivAt_id _).const_smul _
    have hF := (hm.comp _ hlin).const_smul (w : ℂ)
    have hF2 : fderiv ℂ (fun b : Fin N → ℂ => (w : ℂ) • mCore ((νj : ℂ)⁻¹ • b))
        ((νj : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)) = _ := hF.fderiv
    rw [hF2, hpt]
    have hval : ((w : ℂ) • (fderiv ℂ (mCore (N := N)) (Pi.single i₀ 1)).comp
        ((νj : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (Fin N → ℂ))) u =
        ((w : ℂ) * (2 * ((νj : ℂ)⁻¹ * u i₀))) • (Pi.single i₀ 1 : Fin N → ℂ) := by
      simp [mCore_fderiv_single, smul_smul]
      ring
    rw [hval, vn_smul_c]
    have hve : vn (Pi.single i₀ 1 : Fin N → ℂ) = 1 := by
      have h1 := Multiscale.vn_sq (Pi.single i₀ 1 : Fin N → ℂ)
      have h2 : ∑ l, ‖(Pi.single i₀ 1 : Fin N → ℂ) l‖ ^ 2 = 1 := by
        rw [Finset.sum_eq_single i₀]
        · simp
        · intro l _ hl; simp [Pi.single_eq_of_ne hl]
        · simp
      rw [h2] at h1
      have h0 := vn_nonneg (Pi.single i₀ 1 : Fin N → ℂ)
      nlinarith
    have hw0 : 0 ≤ w := wCoef_nonneg hcO0 j X
    have hnorm : ‖(w : ℂ) * (2 * ((νj : ℂ)⁻¹ * u i₀))‖ = w * (2 * (νj⁻¹ * ‖u i₀‖)) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hw0, Real.norm_of_nonneg hνpos.le]
      simp
    rw [hnorm, hve, mul_one]
    have hu : ‖u i₀‖ ≤ vn u := norm_le_vn u i₀
    have h2 := wCoef_le hκ hcO0 (m₀ := P.m₀) hX
    have he := Real.exp_pos (-P.κ * sizeJ P.m₀ j X)
    have hcancel : νj * (w * (2 * (νj⁻¹ * ‖u i₀‖))) = 2 * w * ‖u i₀‖ := by
      field_simp
    rw [hcancel]
    have h3 : 2 * w * ‖u i₀‖ ≤ 2 * (obsCoef β cj j * Real.exp (-P.κ * sizeJ P.m₀ j X)) * vn u :=
      mul_le_mul (by linarith) hu (norm_nonneg _)
        (by have := mul_nonneg (hcO0 j) he.le; linarith)
    have h4 := mul_le_mul_of_nonneg_right (hcO j) he.le
    have hv0 := vn_nonneg u
    nlinarith [mul_le_mul_of_nonneg_right h4 hv0]

/-! ### The concrete member -/

/-- The observable constants of the witness: `ρ₀ = 1`, `ρ₁ = 1/2`, `δ₀ = 1`. -/
noncomputable def witQ : ObsConsts := ⟨1, 1 / 2, 1⟩

theorem witQ_admissible : witQ.Admissible 3 where
  ρ₀_pos := by norm_num [witQ]
  ρ₀_le := by norm_num [witQ]
  ρ₁_pos := by norm_num [witQ]
  ρ₁_lt := by norm_num [witQ]
  δ₀_pos := by norm_num [witQ]

theorem witness_obsCoef_le (j : ℕ) :
    10 * obsCoef witnessβ (witCj 3) j ≤
      (witnessβ 0) ^ (-(1 / 2 : ℝ) + witQ.ρ₁) * ((3 : ℕ) : ℝ) ^ (-((j : ℝ) * witQ.ρ₀)) := by
  have hx0 : (0 : ℝ) < ((3 : ℝ) ^ j)⁻¹ := by positivity
  have hx1 : ((3 : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hA : (witnessβ 0) ^ (-(1 / 2 : ℝ) + witQ.ρ₁) * ((3 : ℕ) : ℝ) ^ (-((j : ℝ) * witQ.ρ₀)) =
      ((3 : ℝ) ^ j)⁻¹ := by
    have h1 : witnessβ 0 = 1 := by simp [witnessβ]
    rw [h1, Real.one_rpow, one_mul]
    simp only [witQ, mul_one, Nat.cast_ofNat]
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [hA]
  have hy1 : (1 : ℝ) ≤ (3 : ℝ) ^ (j - 1) := one_le_pow₀ (by norm_num)
  have hs : Real.sqrt (witnessβ (j - 1)) ≤ (3 : ℝ) ^ j := by
    have h2 : Real.sqrt ((3 : ℝ) ^ (j - 1)) ≤ (3 : ℝ) ^ (j - 1) := by
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, by nlinarith⟩
    have h3 : (3 : ℝ) ^ (j - 1) ≤ (3 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) (Nat.sub_le j 1)
    simp only [witnessβ]
    exact h2.trans h3
  have hs0 := Real.sqrt_nonneg (witnessβ (j - 1))
  have hxy : (3 : ℝ) ^ j * ((3 : ℝ) ^ j)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  unfold obsCoef witCj
  have h5 : Real.sqrt (witnessβ (j - 1)) * ((3 : ℝ) ^ j)⁻¹ ≤ 1 := by
    calc Real.sqrt (witnessβ (j - 1)) * ((3 : ℝ) ^ j)⁻¹ ≤ (3 : ℝ) ^ j * ((3 : ℝ) ^ j)⁻¹ :=
          mul_le_mul_of_nonneg_right hs hx0.le
      _ = 1 := hxy
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right h5 hx0.le]

/-- **The main instance (Scheme A) of the observable layer is inhabited at every scale**: on the
wide domain `Ξ^c_j` with complete backgrounds, for the member `isSFFamily2_xi_witness` (zero
terms; `M_k = φ_k`, `G_k = 0`). -/
theorem isObs2_xi_witness (m₁ k k₀ N₁ : ℕ) [NeZero N₁] (ϱ : ℝ) {α₀ : ℝ} (hα : 0 < α₀) :
    IsObs2 (d := 3) (L := 3) (N₁ := N₁) (m₁ := m₁) (k := k) (N := 2) (ϱ := ϱ)
      (witnessConsts α₀) witQ ⟨k₀, witnessν k⟩ witnessβ witnessa
      (xiFieldDom (aIdeal 3 k (witnessa k)) (physMass 3 k (witnessν k k))
        ((witnessConsts α₀).eps 3 3))
      (pinTerms 3 3 N₁ m₁ k 2 ϱ (witnessConsts α₀).κ (fun _ => 0))
      (pinObs 3 3 N₁ m₁ k 2 (witnessConsts α₀).κ (obsCoef witnessβ (fun _ => 0)))
      (fun _ _ _ _ _ => 0) :=
  isObs2_pinObs (witnessConsts_admissible hα).κ_pos.le (fun _ => le_rfl) (by simp [witnessβ])
    (fun j _ => by simp only [witnessβ]; positivity)
    (fun j => by
      have h1 : obsCoef witnessβ (fun _ => 0) j = 0 := by simp [obsCoef]
      rw [h1, mul_zero]
      exact mul_nonneg (Real.rpow_nonneg (by simp [witnessβ]) _)
        (Real.rpow_nonneg (Nat.cast_nonneg 3) _))
    (fun j hj => absurd rfl hj)

/-- **A member of the observable layer of the second version on the pinned domain (alternative
instance), with a nonzero constant-spin response** (`d = L = 3`, `N = 2`, any `m₁`, `k`, `k₀`, pin
radius `r_h ≤ 1`; complete backgrounds; the member `isSFFamily2_pin_witness`). -/
theorem isObs2_pin_witness (m₁ k k₀ N₁ : ℕ) [NeZero N₁] (ϱ : ℝ) {α₀ rH : ℝ} (hα : 0 < α₀)
    (hr1 : rH ≤ 1) :
    IsObs2 (d := 3) (L := 3) (N₁ := N₁) (m₁ := m₁) (k := k) (N := 2) (ϱ := ϱ)
      (witnessConsts α₀) witQ ⟨k₀, witnessν k⟩ witnessβ witnessa
      (pinFieldDom (Pi.single 0 1) rH (aIdeal 3 k (witnessa k))
        (physMass 3 k (witnessν k k)) ((witnessConsts α₀).eps 3 3))
      (pinTerms 3 3 N₁ m₁ k 2 ϱ (witnessConsts α₀).κ (witCj 3))
      (pinObs 3 3 N₁ m₁ k 2 (witnessConsts α₀).κ (obsCoef witnessβ (witCj 3)))
      (fun _ _ _ _ _ => 0) := by
  refine isObs2_pinObs (witnessConsts_admissible hα).κ_pos.le (fun j => (witCj_pos j).le)
    (by simp [witnessβ]) (fun j _ => by simp only [witnessβ]; positivity) witness_obsCoef_le
    (fun j _ G Ψ h hd x => ?_)
  have hp : Pin (Pi.single 0 1) rH G (aIdeal 3 k (witnessa k))
      (physMass 3 k (witnessν k k)) j ((witnessConsts α₀).eps 3 3 j) Ψ h := hd
  linarith [hp.vn_lt x]

/-- **`IsSFObs2` is inhabited**: the member `isSFFamily2_pin_witness` of the small-field class
with its observable layer `isObs2_pin_witness`, on every torus. -/
theorem isSFObs2_pin_witness (m₁ k k₀ N₁ : ℕ) [NeZero N₁] (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ) {α₀ rH : ℝ}
    (hα : 0 < α₀) (hr1 : rH ≤ 1) :
    IsSFObs2 (d := 3) (L := 3) (N₁ := N₁) (m₁ := m₁) (k := k) (N := 2) (ϱ := ϱ)
      (witnessConsts α₀) witQ ⟨k₀, witnessν k⟩ witnessβ witnessa
      (pinFieldDom (Pi.single 0 1) rH (aIdeal 3 k (witnessa k))
        (physMass 3 k (witnessν k k)) ((witnessConsts α₀).eps 3 3))
      (pinTerms 3 3 N₁ m₁ k 2 ϱ (witnessConsts α₀).κ (witCj 3))
      (rho2 (witnessConsts α₀) ⟨k₀, witnessν k⟩ witnessβ witnessa
        (pinTerms 3 3 N₁ m₁ k 2 ϱ (witnessConsts α₀).κ (witCj 3)) 0) 0
      (pinObs 3 3 N₁ m₁ k 2 (witnessConsts α₀).κ (obsCoef witnessβ (witCj 3)))
      (fun _ _ _ _ _ => 0) :=
  ⟨(isSFFamily2_pin_witness m₁ k k₀ ϱ hϱ hα hr1).torus N₁, isObs2_pin_witness m₁ k k₀ N₁ ϱ hα hr1⟩

/-- **`ObsSourceForm` is inhabited**: the source form of the observable terms of the member
`isObs2_pin_witness`, with `C_D = 1/5`. -/
theorem obsSourceForm_pin_witness (m₁ k k₀ N₁ : ℕ) [NeZero N₁] (ϱ : ℝ) {α₀ rH : ℝ} (hα : 0 < α₀)
    (hr1 : rH ≤ 1) :
    ObsSourceForm (d := 3) (L := 3) (N₁ := N₁) (m₁ := m₁) (k := k) (N := 2) (ϱ := ϱ)
      (witnessConsts α₀) witQ witnessβ (witnessν k)
      (pinFieldDom (Pi.single 0 1) rH (aIdeal 3 k (witnessa k))
        (physMass 3 k (witnessν k k)) ((witnessConsts α₀).eps 3 3))
      (pinTerms 3 3 N₁ m₁ k 2 ϱ (witnessConsts α₀).κ (witCj 3))
      (pinObs 3 3 N₁ m₁ k 2 (witnessConsts α₀).κ (obsCoef witnessβ (witCj 3)))
      (obsSourceOf (witnessν k)
        (pinObs 3 3 N₁ m₁ k 2 (witnessConsts α₀).κ (obsCoef witnessβ (witCj 3)))) 0 (1 / 5) := by
  refine obsSourceForm_pinObs (Rg := ⟨k₀, witnessν k⟩) (a := witnessa)
    (witnessConsts_admissible hα).κ_pos.le (fun j => (witCj_pos j).le) (by simp [witnessβ])
    (fun j _ => by simp only [witnessβ]; positivity) witness_obsCoef_le
    (fun j _ G Ψ h hd x => ?_) (witness_coeff (α₀ := α₀) k).nu_pos 0
  have hp : Pin (Pi.single 0 1) rH G (aIdeal 3 k (witnessa k))
      (physMass 3 k (witnessν k k)) j ((witnessConsts α₀).eps 3 3 j) Ψ h := hd
  linarith [hp.vn_lt x]

/-- **Theorem (b), concrete form (complete backgrounds).**  At `d = L = 3`, `N = 2`, every scale
`1 ≤ j ≤ k` and every LF switch index `k₀`: there is `s₀ > 0` such that for `0 < s < s₀` the
constant pair `(ψ, h) = (e₀, (1+s) e₀)` lies in the pinned domain of every level-`j` generating
set, and the member `isObs2_pin_witness` has the nonzero constant-spin response
`M^{(j)}(x; e₀, (1+s) e₀) ≠ 0`. -/
theorem obs_pinned_response (m₁ k k₀ N₁ : ℕ) [NeZero N₁] (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ) {α₀ rH : ℝ}
    (hα : 0 < α₀) (hr : 0 < rH) {j : ℕ} (hjk : j ≤ k) (x : CTorus 3 3 N₁ m₁ k) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      (∀ G : GeneratingSet 3 3 (N₁ * 3 ^ m₁) k ϱ, (∀ i, j < i → G.Ω i = ∅) →
        (pinFieldDom (N := 2) (Pi.single 0 1) rH (aIdeal 3 k (witnessa k))
          (physMass 3 k (witnessν k k)) ((witnessConsts α₀).eps 3 3)).dom j G
          (constFld (Pi.single 0 1)) (constFld (((1 + s : ℝ) : ℂ) • Pi.single 0 1))) ∧
        Mobs (witnessConsts α₀).m₀
          (pinObs 3 3 N₁ m₁ k 2 (witnessConsts α₀).κ (obsCoef witnessβ (witCj 3))) j x
          (constFld (Pi.single 0 1)) (constFld (((1 + s : ℝ) : ℂ) • Pi.single 0 1)) ≠ 0 := by
  have H := bgHyp_of_class2 (ϱ := ϱ) (Rg := ⟨k₀, witnessν k⟩) (witnessConsts_admissible hα)
    (witness_coeff k) le_rfl le_rfl hϱ
  obtain ⟨s₁, hs₁, hnear⟩ := pin_const_near (N₁ := N₁) (m₁ := m₁) (N := 2) (rH := rH) H hjk
    (eps_pos (d := 3) (L := 3) (P := witnessConsts α₀) hα j) 0
  refine ⟨min s₁ rH, lt_min hs₁ hr, fun s hs hss => ⟨fun G hΩ => ?_,
    pinObs_response_ne_zero _ ?_ 0 hs x⟩⟩
  · have e : ∀ i, (((1 + s : ℝ) : ℂ) • (Pi.single 0 1 : Fin 2 → ℂ)) i -
        (Pi.single 0 1 : Fin 2 → ℂ) i = ((s : ℂ) • (Pi.single 0 1 : Fin 2 → ℂ)) i := by
      intro i; simp only [Pi.smul_apply, smul_eq_mul]; push_cast; ring
    have hve : vn (Pi.single 0 1 : Fin 2 → ℂ) = 1 := by
      have h1 := Multiscale.vn_sq (Pi.single 0 1 : Fin 2 → ℂ)
      have h2 : ∑ l, ‖(Pi.single 0 1 : Fin 2 → ℂ) l‖ ^ 2 = 1 := by
        simp [Fin.sum_univ_two]
      rw [h2] at h1
      have h0 := vn_nonneg (Pi.single 0 1 : Fin 2 → ℂ)
      nlinarith
    have key := hnear G hΩ (((1 + s : ℝ) : ℂ) • (Pi.single 0 1 : Fin 2 → ℂ)) (fun i => ?_) ?_
    · exact key
    · rw [e i]
      have h1 : ‖((s : ℂ) • (Pi.single 0 1 : Fin 2 → ℂ)) i‖ ≤ vn ((s : ℂ) • (Pi.single 0 1 : Fin 2 → ℂ)) :=
        norm_le_vn _ i
      rw [vn_smul_c, Complex.norm_real, Real.norm_of_nonneg hs.le, hve, mul_one] at h1
      exact h1.trans (hss.le.trans (min_le_left _ _))
    · have e' : (fun i => (((1 + s : ℝ) : ℂ) • (Pi.single 0 1 : Fin 2 → ℂ)) i -
          (Pi.single 0 1 : Fin 2 → ℂ) i) = (s : ℂ) • (Pi.single 0 1 : Fin 2 → ℂ) := funext e
      rw [e', vn_smul_c, Complex.norm_real, Real.norm_of_nonneg hs.le, hve, mul_one]
      exact hss.trans_le (min_le_right _ _)
  · exact mul_pos (Real.sqrt_pos.2 (by simp only [witnessβ]; positivity)) (witCj_pos j)

end Balaban.Observables
