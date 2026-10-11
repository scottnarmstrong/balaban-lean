/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ConstantConfig
public import Balaban.Symmetry.TotallyReal
public import Balaban.Symmetry.EvenReduction
public import Balaban.Symmetry.Rotation

/-!
# Reduction of `O(N)`-invariant functions of two vectors to three invariants

P1 (3.24)–(3.28): an `O(N)`-invariant function `V(ψ, h)` of two vectors, analytic near
`(e₁, e₁)` (complexified), is an analytic function `f(U, V, W²)` of
`U = |ψ|`, `V = ψ̂ · h`, `W² = |h|² - (ψ̂ · h)²`.
-/

@[expose] public section

open Matrix Metric Set Filter Topology Balaban.Background Balaban.Analysis

namespace Balaban.Symmetry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The triple of invariants `(U, V, W²)` of a pair of complex vectors. -/
noncomputable def invTriple (ψ h : ι → ℂ) : Fin 3 → ℂ := ![invU ψ, invV ψ h, invW2 ψ h]

/-- A real orthogonal matrix acting on a complex vector. -/
def rotC (R : Matrix ι ι ℝ) (x : ι → ℂ) : ι → ℂ := R.map (↑) *ᵥ x

/-- The domain on which the reduction holds: data in `Ω` with `Re ψ² > 0` whose invariants lie in
the polydisc of radii `(δ, δ, δ²)` around `(1, 1, 0)`. -/
def reductionDomain (Ω : Set ((ι → ℂ) × (ι → ℂ))) (δ : ℝ) : Set ((ι → ℂ) × (ι → ℂ)) :=
  {p | p ∈ Ω ∧ 0 < (p.1 ⬝ᵥ p.1).re ∧
    invTriple p.1 p.2 ∈ polydisc (![1, 1, 0] : Fin 3 → ℂ) ![δ, δ, δ ^ 2]}

omit [DecidableEq ι] in
theorem rotC_cplx (R : Matrix ι ι ℝ) (x : ι → ℝ) : rotC R (cplx x) = cplx (R *ᵥ x) := by
  funext k
  simp [rotC, cplx, Matrix.mulVec, dotProduct]

omit [DecidableEq ι] in
theorem analyticAt_dot_fst (p : (ι → ℂ) × (ι → ℂ)) :
    AnalyticAt ℂ (fun q : (ι → ℂ) × (ι → ℂ) => q.1 ⬝ᵥ q.1) p := by
  unfold dotProduct
  exact Finset.analyticAt_fun_sum _ (fun i _ =>
    (analyticAt_coord i p).mul (analyticAt_coord i p))

omit [DecidableEq ι] in
theorem analyticAt_dot_mixed (p : (ι → ℂ) × (ι → ℂ)) :
    AnalyticAt ℂ (fun q : (ι → ℂ) × (ι → ℂ) => q.1 ⬝ᵥ q.2) p := by
  unfold dotProduct
  exact Finset.analyticAt_fun_sum _ (fun i _ =>
    (analyticAt_coord i p).mul (analyticAt_coord' i p))

omit [DecidableEq ι] in
theorem analyticAt_dot_snd (p : (ι → ℂ) × (ι → ℂ)) :
    AnalyticAt ℂ (fun q : (ι → ℂ) × (ι → ℂ) => q.2 ⬝ᵥ q.2) p := by
  unfold dotProduct
  exact Finset.analyticAt_fun_sum _ (fun i _ =>
    (analyticAt_coord' i p).mul (analyticAt_coord' i p))

omit [DecidableEq ι] in
theorem analyticAt_sqrtDot_fst {p : (ι → ℂ) × (ι → ℂ)} (hp : 0 < (p.1 ⬝ᵥ p.1).re) :
    AnalyticAt ℂ (fun q : (ι → ℂ) × (ι → ℂ) => sqrtDot q.1) p :=
  (analyticAt_dot_fst p).cpow analyticAt_const (Complex.mem_slitPlane_iff.mpr (Or.inl hp))

omit [DecidableEq ι] in
theorem analyticAt_invTriple {p : (ι → ℂ) × (ι → ℂ)} (hp : 0 < (p.1 ⬝ᵥ p.1).re) :
    AnalyticAt ℂ (fun q : (ι → ℂ) × (ι → ℂ) => invTriple q.1 q.2) p := by
  have hU := analyticAt_sqrtDot_fst hp
  have hne : sqrtDot p.1 ≠ 0 := sqrtDot_ne_zero_of_re hp
  have hV : AnalyticAt ℂ (fun q : (ι → ℂ) × (ι → ℂ) => invV q.1 q.2) p :=
    (analyticAt_dot_mixed p).div hU hne
  have hW : AnalyticAt ℂ (fun q : (ι → ℂ) × (ι → ℂ) => invW2 q.1 q.2) p :=
    (analyticAt_dot_snd p).sub (hV.pow 2)
  rw [analyticAt_pi_iff]
  intro k
  fin_cases k
  · exact hU
  · exact hV
  · exact hW

/-! ### The slice `(r e_i, c e_i + x e_j)` and the reflection in `e_j` -/

section Slice

variable (i j : ι)

/-- The slice `z ↦ (z₀ e_i, z₁ e_i + z₂ e_j)`. -/
noncomputable def pairOf (z : Fin 3 → ℂ) : (ι → ℂ) × (ι → ℂ) :=
  (z 0 • (Pi.single i 1 : ι → ℂ), z 1 • (Pi.single i 1 : ι → ℂ) + z 2 • (Pi.single j 1 : ι → ℂ))

/-- The reflection `x_j ↦ -x_j`. -/
def reflectMat : Matrix ι ι ℝ := Matrix.diagonal fun k => if k = j then -1 else 1

theorem reflectMat_transpose_mul : (reflectMat j)ᵀ * reflectMat j = 1 := by
  unfold reflectMat
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  by_cases hk : k = j <;> simp [hk]

theorem rotC_reflectMat (x : ι → ℂ) (k : ι) :
    rotC (reflectMat j) x k = (if k = j then -1 else 1) * x k := by
  unfold rotC reflectMat
  rw [Matrix.diagonal_map (by simp), Matrix.mulVec_diagonal]
  by_cases hk : k = j <;> simp [hk]

theorem reflect_pairOf (hij : i ≠ j) (z : Fin 3 → ℂ) :
    (rotC (reflectMat j) (pairOf i j z).1, rotC (reflectMat j) (pairOf i j z).2) =
      pairOf i j (Function.update z 2 (-z 2)) := by
  ext k
  · simp only [pairOf, rotC_reflectMat, Pi.smul_apply, smul_eq_mul]
    by_cases hk : k = j
    · subst hk; simp [hij.symm]
    · simp [hk]
  · simp only [pairOf, rotC_reflectMat, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    by_cases hk : k = j
    · subst hk; simp [hij.symm]
    · simp [hk]

/-- `pairOf` is a continuous linear map. -/
noncomputable def pairOfCLM : (Fin 3 → ℂ) →L[ℂ] (ι → ℂ) × (ι → ℂ) :=
  (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).smulRight
      (Pi.single i 1 : ι → ℂ))).prod
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 1).smulRight
      (Pi.single i 1 : ι → ℂ)) +
     ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 2).smulRight
      (Pi.single j 1 : ι → ℂ)))

omit [Fintype ι] in
theorem pairOfCLM_apply (z : Fin 3 → ℂ) : pairOfCLM i j z = pairOf i j z := rfl

end Slice

/-! ### Identity theorem on pairs of vectors -/

/-- Real points of `X × X`. -/
def IsRealPair (q : (ι → ℂ) × (ι → ℂ)) : Prop :=
  (∀ a, (q.1 a).im = 0) ∧ ∀ a, (q.2 a).im = 0

omit [DecidableEq ι] in
theorem eventually_eq_zero_of_real_pair {P : (ι → ℂ) × (ι → ℂ) → ℂ} {p : (ι → ℂ) × (ι → ℂ)}
    (hp : IsRealPair p) (hP : AnalyticAt ℂ P p)
    (h0 : ∀ᶠ q in 𝓝 p, IsRealPair q → P q = 0) : ∀ᶠ q in 𝓝 p, P q = 0 := by
  classical
  let K : (ι → ℂ) × (ι → ℂ) → (ι ⊕ ι → ℂ) := fun q => Sum.elim q.1 q.2
  let J : (ι ⊕ ι → ℂ) → (ι → ℂ) × (ι → ℂ) := fun z => (fun a => z (Sum.inl a), fun a => z (Sum.inr a))
  have hJK : ∀ q, J (K q) = q := fun q => by simp [J, K]
  have hJc : Continuous J := by fun_prop
  have hKc : Continuous K := by
    refine continuous_pi fun a => ?_
    rcases a with a | a
    · exact (continuous_apply a).comp continuous_fst
    · exact (continuous_apply a).comp continuous_snd
  have hJan : AnalyticAt ℂ J (K p) := by
    refine AnalyticAt.prod ?_ ?_
    · rw [analyticAt_pi_iff]; intro a
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ⊕ ι => ℂ) (Sum.inl a)).analyticAt _
    · rw [analyticAt_pi_iff]; intro a
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ⊕ ι => ℂ) (Sum.inr a)).analyticAt _
  have hKp : J (K p) = p := hJK p
  have hP' : AnalyticAt ℂ (fun z => P (J z)) (K p) := by
    have : AnalyticAt ℂ P (J (K p)) := by rw [hKp]; exact hP
    exact this.comp hJan
  have hreal : ∀ i, (K p i).im = 0 := by
    intro i; rcases i with a | a
    · exact hp.1 a
    · exact hp.2 a
  have h0' : ∀ᶠ z in 𝓝 (K p), (∀ i, (z i).im = 0) → P (J z) = 0 := by
    have ht : Tendsto J (𝓝 (K p)) (𝓝 p) := by
      have := (hJc.continuousAt (x := K p)).tendsto; rwa [hKp] at this
    filter_upwards [ht.eventually h0] with z hz hzr
    exact hz ⟨fun a => hzr (Sum.inl a), fun a => hzr (Sum.inr a)⟩
  have key := Balaban.Symmetry.eventually_eq_zero_of_real hreal hP' h0'
  have hKt : Tendsto K (𝓝 p) (𝓝 (K p)) := hKc.continuousAt
  filter_upwards [hKt.eventually key] with q hq
  simpa [hJK] using hq

omit [DecidableEq ι] in
/-- The invariants of real data are the real quantities of P1 (3.24):
`U = |ψ|`, `V = ψ̂ · h`, `W² = |h|² - (ψ̂ · h)²`. -/
theorem invTriple_cplx (ψ₀ h₀ : ι → ℝ) :
    invTriple (cplx ψ₀) (cplx h₀) =
      ![((Real.sqrt (ψ₀ ⬝ᵥ ψ₀) : ℝ) : ℂ), ((ψ₀ ⬝ᵥ h₀ / Real.sqrt (ψ₀ ⬝ᵥ ψ₀) : ℝ) : ℂ),
        ((h₀ ⬝ᵥ h₀ - (ψ₀ ⬝ᵥ h₀ / Real.sqrt (ψ₀ ⬝ᵥ ψ₀)) ^ 2 : ℝ) : ℂ)] := by
  have hU : invU (cplx ψ₀) = ((Real.sqrt (ψ₀ ⬝ᵥ ψ₀) : ℝ) : ℂ) := by
    unfold invU; rw [sqrtDot_cplx]
  have hV : invV (cplx ψ₀) (cplx h₀) = ((ψ₀ ⬝ᵥ h₀ / Real.sqrt (ψ₀ ⬝ᵥ ψ₀) : ℝ) : ℂ) := by
    unfold invV; rw [sqrtDot_cplx, cplx_dot]; push_cast; rfl
  have hW : invW2 (cplx ψ₀) (cplx h₀) =
      ((h₀ ⬝ᵥ h₀ - (ψ₀ ⬝ᵥ h₀ / Real.sqrt (ψ₀ ⬝ᵥ ψ₀)) ^ 2 : ℝ) : ℂ) := by
    unfold invW2; rw [hV, cplx_dot]; push_cast; rfl
  funext k
  fin_cases k <;> simp [invTriple, hU, hV, hW]

/-! ### Real points: the rotation argument -/

omit [Fintype ι] in
theorem cplx_smul_single (a : ℝ) (i : ι) :
    cplx (a • (Pi.single i 1 : ι → ℝ)) = (a : ℂ) • (Pi.single i 1 : ι → ℂ) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [cplx]
  · simp [cplx, hk]

omit [Fintype ι] [DecidableEq ι] in
theorem cplx_add (x y : ι → ℝ) : cplx (x + y) = cplx x + cplx y := by
  funext k; simp [cplx]

omit [Fintype ι] [DecidableEq ι] in
theorem cplx_re_im {q : ι → ℂ} (hq : ∀ a, (q a).im = 0) : q = cplx (fun a => (q a).re) := by
  funext a; apply Complex.ext <;> simp [cplx, hq a]

theorem single_dot_single_self (i : ι) : (Pi.single i 1 : ι → ℝ) ⬝ᵥ (Pi.single i 1 : ι → ℝ) = 1 := by
  simp [dotProduct, Pi.single_apply]

theorem single_dot_single_ne {i j : ι} (hij : i ≠ j) :
    (Pi.single i 1 : ι → ℝ) ⬝ᵥ (Pi.single j 1 : ι → ℝ) = 0 := by
  simp [dotProduct, Pi.single_apply, hij.symm]

/-- The reduction at a real point: `V(ψ₀, h₀) = f(|ψ₀|, ψ̂₀·h₀, |h₀|² - (ψ̂₀·h₀)²)`. -/
theorem real_point_eq {i j : ι} (hij : i ≠ j) {V : (ι → ℂ) × (ι → ℂ) → ℂ}
    {Ω : Set ((ι → ℂ) × (ι → ℂ))}
    (hinv : ∀ R : Matrix ι ι ℝ, Rᵀ * R = 1 → ∀ p ∈ Ω, V (rotC R p.1, rotC R p.2) = V p)
    {δ : ℝ} (hδ : 0 < δ) {f : (Fin 3 → ℂ) → ℂ}
    (hf : ∀ z : Fin 3 → ℂ, ‖z 0 - 1‖ < δ → ‖z 1 - 1‖ < δ → ‖z 2‖ < δ →
      V (pairOf i j z) = f (Function.update z 2 (z 2 ^ 2)))
    (ψ₀ h₀ : ι → ℝ) (hp : (cplx ψ₀, cplx h₀) ∈ reductionDomain Ω δ) :
    V (cplx ψ₀, cplx h₀) = f (invTriple (cplx ψ₀) (cplx h₀)) := by
  obtain ⟨hpΩ, hre, hpoly⟩ := hp
  have hψψ : 0 < ψ₀ ⬝ᵥ ψ₀ := by
    have : (cplx ψ₀ ⬝ᵥ cplx ψ₀).re = ψ₀ ⬝ᵥ ψ₀ := by rw [cplx_dot]; simp
    simpa [this] using hre
  have hψ : ψ₀ ≠ 0 := by
    intro h0; rw [h0] at hψψ; simp at hψψ
  obtain ⟨M, hM, hMψ, hMh⟩ := exists_rotation hij ψ₀ h₀ hψ
  set r : ℝ := Real.sqrt (ψ₀ ⬝ᵥ ψ₀) with hr
  set c : ℝ := ψ₀ ⬝ᵥ h₀ / r with hc
  set s : ℝ := Real.sqrt (h₀ ⬝ᵥ h₀ - c ^ 2) with hs
  have hr0 : 0 < r := Real.sqrt_pos.mpr hψψ
  -- `|h₀|² = c² + s²`
  have hhh : h₀ ⬝ᵥ h₀ = c ^ 2 + s ^ 2 := by
    have h1 := mulVec_dotProduct_mulVec M hM h₀ h₀
    rw [hMh] at h1
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      single_dot_single_self, single_dot_single_ne hij, single_dot_single_ne hij.symm] at h1
    linarith
  have hs2 : s ^ 2 = h₀ ⬝ᵥ h₀ - c ^ 2 := by linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  -- the rotated point
  have hrot : (rotC M (cplx ψ₀), rotC M (cplx h₀)) = pairOf i j ![(r : ℂ), (c : ℂ), (s : ℂ)] := by
    rw [rotC_cplx, rotC_cplx, hMψ, hMh]
    simp only [pairOf]
    refine Prod.ext ?_ ?_
    · simp [cplx_smul_single]
    · simp [cplx_add, cplx_smul_single]
  -- the invariants
  have hinvT : invTriple (cplx ψ₀) (cplx h₀) =
      Function.update ![(r : ℂ), (c : ℂ), (s : ℂ)] 2 ((s : ℂ) ^ 2) := by
    have hU : invU (cplx ψ₀) = (r : ℂ) := by unfold invU; rw [sqrtDot_cplx]
    have hV : invV (cplx ψ₀) (cplx h₀) = (c : ℂ) := by
      unfold invV; rw [sqrtDot_cplx, cplx_dot, hc]; push_cast; rfl
    have hW : invW2 (cplx ψ₀) (cplx h₀) = (s : ℂ) ^ 2 := by
      unfold invW2; rw [hV, cplx_dot]
      exact_mod_cast hs2.symm
    funext k
    fin_cases k <;> simp [invTriple, hU, hV, hW]
  have hmem := hpoly
  rw [hinvT] at hmem
  have h0 := hmem 0
  have h1 := hmem 1
  have h2 := hmem 2
  simp at h0 h1 h2
  have hsδ : ‖(s : ℂ)‖ < δ := by
    have : ‖(s : ℂ) ^ 2‖ < δ ^ 2 := by simpa using h2
    rw [norm_pow] at this
    exact lt_of_pow_lt_pow_left₀ 2 hδ.le this
  have hV0 := hinv M hM _ hpΩ
  simp only at hV0
  rw [hrot] at hV0
  rw [← hV0, hinvT]
  exact hf ![(r : ℂ), (c : ℂ), (s : ℂ)] (by simpa using h0) (by simpa using h1) (by simpa using hsδ)

/-! ### The reduction theorem -/

omit [DecidableEq ι] in
theorem isOpen_reductionDomain {Ω : Set ((ι → ℂ) × (ι → ℂ))} (hΩ : IsOpen Ω) (δ : ℝ) :
    IsOpen (reductionDomain Ω δ) := by
  have hD : IsOpen {p : (ι → ℂ) × (ι → ℂ) | 0 < (p.1 ⬝ᵥ p.1).re} := by
    have hc : Continuous fun q : (ι → ℂ) × (ι → ℂ) => (q.1 ⬝ᵥ q.1).re :=
      Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun p =>
        (analyticAt_dot_fst p).continuousAt)
    exact isOpen_lt continuous_const hc
  have hcont : ContinuousOn (fun q : (ι → ℂ) × (ι → ℂ) => invTriple q.1 q.2)
      {p : (ι → ℂ) × (ι → ℂ) | 0 < (p.1 ⬝ᵥ p.1).re} := fun p hp =>
    (analyticAt_invTriple hp).continuousAt.continuousWithinAt
  have hpoly : IsOpen (polydisc (![1, 1, 0] : Fin 3 → ℂ) ![δ, δ, δ ^ 2]) :=
    isOpen_polydisc _ _
  have := hcont.isOpen_inter_preimage hD hpoly
  have heq : reductionDomain Ω δ = Ω ∩ ({p : (ι → ℂ) × (ι → ℂ) | 0 < (p.1 ⬝ᵥ p.1).re} ∩
      (fun q : (ι → ℂ) × (ι → ℂ) => invTriple q.1 q.2) ⁻¹'
        (polydisc (![1, 1, 0] : Fin 3 → ℂ) ![δ, δ, δ ^ 2])) := by
    ext p; simp only [reductionDomain, Set.mem_ofPred_eq, mem_inter_iff, mem_preimage]
  rw [heq]
  exact hΩ.inter this

/-- **Reduction of `O(N)`-invariant functions** (P1 (3.24)–(3.28)).

Let `Ω ⊆ ℂ^ι × ℂ^ι` be open, containing `(e_i, e_i)`, and let `V` be analytic on `Ω`, with `Ω`
stable and `V` invariant under real orthogonal matrices (`hinv`) (`ι` has two distinct
indices `i ≠ j`, i.e. `N ≥ 2`).  Then there are `δ > 0` and `f`, analytic on the polydisc of
radii `(δ, δ, δ²)` around `(1, 1, 0)`, such that near every real point `(ψ₀, h₀)` of
`reductionDomain Ω δ` (`ψ₀ ≠ 0`, `Ω`, invariants within the polydisc), `V` coincides with
`f (U, V, W²)` where `(U, V, W²) = invTriple ψ h` are the invariants of P2 (2.6):
`U = √(ψ ⬝ᵥ ψ)`, `V = ψ ⬝ᵥ h / U`, `W² = h ⬝ᵥ h - V²`. -/
theorem exists_invariant_reduction {i j : ι} (hij : i ≠ j) {V : (ι → ℂ) × (ι → ℂ) → ℂ}
    {Ω : Set ((ι → ℂ) × (ι → ℂ))} (hΩ : IsOpen Ω) (hV : AnalyticOnNhd ℂ V Ω)
    (hinv : ∀ R : Matrix ι ι ℝ, Rᵀ * R = 1 → ∀ p ∈ Ω,
      (rotC R p.1, rotC R p.2) ∈ Ω ∧ V (rotC R p.1, rotC R p.2) = V p)
    (hbase : ((Pi.single i 1 : ι → ℂ), (Pi.single i 1 : ι → ℂ)) ∈ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ f : (Fin 3 → ℂ) → ℂ,
      AnalyticOnNhd ℂ f (polydisc (![1, 1, 0] : Fin 3 → ℂ) ![δ, δ, δ ^ 2]) ∧
      ∀ ψ₀ h₀ : ι → ℝ, (cplx ψ₀, cplx h₀) ∈ reductionDomain Ω δ →
        V (cplx ψ₀, cplx h₀) = f (invTriple (cplx ψ₀) (cplx h₀)) ∧
        ∀ᶠ q in 𝓝 (cplx ψ₀, cplx h₀), V q = f (invTriple q.1 q.2) := by
  set z₀ : Fin 3 → ℂ := ![1, 1, 0] with hz₀def
  have hz₀ : z₀ 2 = 0 := by simp [hz₀def]
  set A := pairOfCLM i j with hA
  have hAz₀ : A z₀ = ((Pi.single i 1 : ι → ℂ), (Pi.single i 1 : ι → ℂ)) := by
    rw [hA, pairOfCLM_apply]; simp [pairOf, hz₀def]
  have hG₀ : IsOpen (A ⁻¹' Ω) := hΩ.preimage A.continuous
  have hz₀mem : z₀ ∈ A ⁻¹' Ω := by rw [mem_preimage, hAz₀]; exact hbase
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp hG₀ z₀ hz₀mem
  have hg : AnalyticOnNhd ℂ (fun z => V (A z)) (ball z₀ δ₀) := fun z hz =>
    (hV _ (hball hz)).comp (A.analyticAt z)
  have heven : ∀ z ∈ ball z₀ δ₀, V (A (Function.update z 2 (-z 2))) = V (A z) := by
    intro z hz
    have h1 : A z ∈ Ω := hball hz
    have hS := (hinv (reflectMat j) (reflectMat_transpose_mul j) (A z) h1).2
    rw [hA, pairOfCLM_apply] at *
    rw [← reflect_pairOf i j hij z]
    exact hS
  obtain ⟨δ, hδ, f, hfan, hfeq⟩ := exists_sq_reduction hz₀ hδ₀ hg heven
  refine ⟨δ, hδ, f, hfan, ?_⟩
  intro ψ₀ h₀ hp
  have hfeq' : ∀ z : Fin 3 → ℂ, ‖z 0 - 1‖ < δ → ‖z 1 - 1‖ < δ → ‖z 2‖ < δ →
      V (pairOf i j z) = f (Function.update z 2 (z 2 ^ 2)) := by
    intro z h0 h1 h2
    have := hfeq z (by simpa [hz₀def] using h0) (by simpa [hz₀def] using h1) h2
    simpa [hA, pairOfCLM_apply] using this
  have hinv' : ∀ R : Matrix ι ι ℝ, Rᵀ * R = 1 → ∀ p ∈ Ω,
      V (rotC R p.1, rotC R p.2) = V p := fun R hR p hp => (hinv R hR p hp).2
  have hreal := real_point_eq hij hinv' hδ hfeq' ψ₀ h₀ hp
  refine ⟨hreal, ?_⟩
  -- identity theorem
  set p : (ι → ℂ) × (ι → ℂ) := (cplx ψ₀, cplx h₀) with hpdef
  have hpΩ : p ∈ Ω := hp.1
  have hPan : AnalyticAt ℂ (fun q : (ι → ℂ) × (ι → ℂ) => V q - f (invTriple q.1 q.2)) p := by
    have h1 : AnalyticAt ℂ V p := hV p hpΩ
    have h2 : AnalyticAt ℂ f (invTriple p.1 p.2) := hfan _ hp.2.2
    exact h1.sub (AnalyticAt.comp (f := fun q : (ι → ℂ) × (ι → ℂ) => invTriple q.1 q.2) (x := p) h2
      (analyticAt_invTriple hp.2.1))
  have hpreal : IsRealPair p := ⟨fun a => by simp [hpdef, cplx], fun a => by simp [hpdef, cplx]⟩
  have hnhd : reductionDomain Ω δ ∈ 𝓝 p := (isOpen_reductionDomain hΩ δ).mem_nhds hp
  have h0 : ∀ᶠ q in 𝓝 p, IsRealPair q → V q - f (invTriple q.1 q.2) = 0 := by
    filter_upwards [hnhd] with q hq hqr
    obtain ⟨hq1, hq2⟩ := hqr
    have hq' : q = (cplx (fun a => (q.1 a).re), cplx (fun a => (q.2 a).re)) :=
      Prod.ext (cplx_re_im hq1) (cplx_re_im hq2)
    rw [hq'] at hq ⊢
    have := real_point_eq hij hinv' hδ hfeq' _ _ hq
    simp only at this ⊢
    rw [this]; ring
  have := eventually_eq_zero_of_real_pair hpreal hPan h0
  filter_upwards [this] with q hq
  exact sub_eq_zero.mp hq

/-! ### The standard stable domain -/

/-- The orthogonally stable neighbourhood of the orbit of `(e₁, e₁)`:
`|ψ² - 1|, |ψ·h - 1|, |h² - 1| < ε`. -/
def invariantNeighborhood (ε : ℝ) : Set ((ι → ℂ) × (ι → ℂ)) :=
  {p | ‖p.1 ⬝ᵥ p.1 - 1‖ < ε ∧ ‖p.1 ⬝ᵥ p.2 - 1‖ < ε ∧ ‖p.2 ⬝ᵥ p.2 - 1‖ < ε}

omit [DecidableEq ι] in
theorem isOpen_invariantNeighborhood (ε : ℝ) : IsOpen (invariantNeighborhood (ι := ι) ε) := by
  have c1 : Continuous fun q : (ι → ℂ) × (ι → ℂ) => ‖q.1 ⬝ᵥ q.1 - 1‖ :=
    (continuous_iff_continuousAt.mpr fun p => (analyticAt_dot_fst p).continuousAt).sub
      continuous_const |>.norm
  have c2 : Continuous fun q : (ι → ℂ) × (ι → ℂ) => ‖q.1 ⬝ᵥ q.2 - 1‖ :=
    (continuous_iff_continuousAt.mpr fun p => (analyticAt_dot_mixed p).continuousAt).sub
      continuous_const |>.norm
  have c3 : Continuous fun q : (ι → ℂ) × (ι → ℂ) => ‖q.2 ⬝ᵥ q.2 - 1‖ :=
    (continuous_iff_continuousAt.mpr fun p => (analyticAt_dot_snd p).continuousAt).sub
      continuous_const |>.norm
  exact (isOpen_lt c1 continuous_const).inter
    ((isOpen_lt c2 continuous_const).inter (isOpen_lt c3 continuous_const))

theorem rotC_dot_rotC (R : Matrix ι ι ℝ) (hR : Rᵀ * R = 1) (x y : ι → ℂ) :
    rotC R x ⬝ᵥ rotC R y = x ⬝ᵥ y :=
  cMulVec_dotProduct_mulVec _ (map_ofReal_transpose_mul R hR) x y

theorem rotC_mem_invariantNeighborhood (ε : ℝ) (R : Matrix ι ι ℝ) (hR : Rᵀ * R = 1)
    {p : (ι → ℂ) × (ι → ℂ)} (hp : p ∈ invariantNeighborhood ε) :
    (rotC R p.1, rotC R p.2) ∈ invariantNeighborhood ε := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨?_, ?_, ?_⟩ <;> simpa only [rotC_dot_rotC R hR] using ‹_›

theorem base_mem_invariantNeighborhood {ε : ℝ} (hε : 0 < ε) (i : ι) :
    ((Pi.single i 1 : ι → ℂ), (Pi.single i 1 : ι → ℂ)) ∈ invariantNeighborhood ε := by
  have : (Pi.single i 1 : ι → ℂ) ⬝ᵥ (Pi.single i 1 : ι → ℂ) = 1 := by
    simp [dotProduct, Pi.single_apply]
  refine ⟨?_, ?_, ?_⟩ <;> simpa only [this, sub_self, norm_zero] using hε

/-- The base point `(e_i, e_i)` lies in the reduction domain: its invariants are `(1, 1, 0)`. -/
theorem base_mem_reductionDomain {Ω : Set ((ι → ℂ) × (ι → ℂ))} {δ : ℝ} (hδ : 0 < δ) (i : ι)
    (hΩ : ((Pi.single i 1 : ι → ℂ), (Pi.single i 1 : ι → ℂ)) ∈ Ω) :
    ((Pi.single i 1 : ι → ℂ), (Pi.single i 1 : ι → ℂ)) ∈ reductionDomain Ω δ := by
  have hd : (Pi.single i 1 : ι → ℂ) ⬝ᵥ (Pi.single i 1 : ι → ℂ) = 1 := by
    simp [dotProduct, Pi.single_apply]
  have hsq : sqrtDot (Pi.single i 1 : ι → ℂ) = 1 := by
    have := sqrtDot_sq (Pi.single i 1 : ι → ℂ)
    rw [hd] at this
    have hre := re_sqrtDot_nonneg (Pi.single i 1 : ι → ℂ)
    have h1 : sqrtDot (Pi.single i 1 : ι → ℂ) ^ 2 = 1 ^ 2 := by rw [this, one_pow]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact h
    · rw [h] at hre; simp at hre; linarith
  refine ⟨hΩ, by simp [hd], ?_⟩
  intro k
  fin_cases k
  · simp [invTriple, invU, hsq, hδ]
  · simp [invTriple, invV, hsq, hd, hδ]
  · simp [invTriple, invW2, invV, hsq, hd, hδ]

/-- **Reduction of `O(N)`-invariant functions** on the standard neighbourhood
`invariantNeighborhood ε` of the orbit of `(e₁, e₁)`. -/
theorem exists_invariant_reduction_nhd {i j : ι} (hij : i ≠ j) {ε : ℝ} (hε : 0 < ε)
    {V : (ι → ℂ) × (ι → ℂ) → ℂ} (hV : AnalyticOnNhd ℂ V (invariantNeighborhood ε))
    (hinv : ∀ R : Matrix ι ι ℝ, Rᵀ * R = 1 → ∀ p ∈ invariantNeighborhood ε,
      V (rotC R p.1, rotC R p.2) = V p) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ f : (Fin 3 → ℂ) → ℂ,
      AnalyticOnNhd ℂ f (polydisc (![1, 1, 0] : Fin 3 → ℂ) ![δ, δ, δ ^ 2]) ∧
      ∀ ψ₀ h₀ : ι → ℝ, (cplx ψ₀, cplx h₀) ∈ reductionDomain (invariantNeighborhood ε) δ →
        V (cplx ψ₀, cplx h₀) = f (invTriple (cplx ψ₀) (cplx h₀)) ∧
        ∀ᶠ q in 𝓝 (cplx ψ₀, cplx h₀), V q = f (invTriple q.1 q.2) :=
  exists_invariant_reduction hij (isOpen_invariantNeighborhood ε) hV
    (fun R hR p hp => ⟨rotC_mem_invariantNeighborhood ε R hR hp, hinv R hR p hp⟩)
    (base_mem_invariantNeighborhood hε i)

end Balaban.Symmetry
