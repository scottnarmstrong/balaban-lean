/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.LayerSchur
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Lemma 2.1: structure at the constant configuration (OBSERVABLES.md §2.2)

At `λ = ∞` and the constant configuration `ψ ≡ h`, `|h| = 1`: the Jacobian
`H(x, y) = ∂φ(x; ψ, h)/∂ψ(y)` of the (unit-vector) background field has range `h^⊥`
(sphere constraint) and, by the covariance of the field under the stabilizer `O(N-1)` of `h`, is
`s(x, y)(1 - hhᵀ)`; a covariance commuting with the stabilizer is `c_tr (1 - hhᵀ) + c_lg hhᵀ`; and
the Gaussian kernel `G = H C Hᵀ` is `g (1 - hhᵀ)`: exactly transverse (the longitudinal main term
is `0`).

The background enters through its abstract properties: `φ x ψ h ∈ ℝ^N` for a site `x`, a
configuration `ψ : Y → ℝ^N` and the field `h`; the hypotheses are the four facts about the
background used by the document's proof (`IsBgAt`): it is differentiable at the constant
configuration, equals `h` there, lies on the unit sphere near it, and is `O(N)`-covariant under
the stabilizer of `h`.

* `sphere_range`: the sphere constraint gives `hᵀ H = 0` (item (1));
* `jac_commutes`: covariance gives `S H = H S` for `S` in the stabilizer;
* `jac_scalar` (item (2)): `H(x, y) = s (1 - hhᵀ)`;
* `cov_blocks`: a covariance commuting with the stabilizer is block diagonal in `ℝh ⊕ h^⊥`;
* `gauss_transverse` (item (3)): `G = g (1 - hhᵀ)`, so `hᵀ G = 0` and `G h = 0`;
* `lemma_2_1`: the three items together.

Item (4) of the document (identification of the scalar kernel with `K_{j-1}`) is the dictionary of
`CORRELATIONS.md` §2.1 and is not part of this module.
-/

@[expose] public section

open Matrix Filter Topology

namespace Balaban.Observables

variable {X Y : Type*} [Fintype Y] [DecidableEq Y] {N : ℕ}

/-- The constant configuration `ψ ≡ h`. -/
def constCfg (h : Fin N → ℝ) : Y → Fin N → ℝ := fun _ => h

/-- The Jacobian `H(x, y)_{ik} = ∂φ_i(x; ψ, h)/∂ψ_k(y)` at the constant configuration. -/
noncomputable def bgJac (φ : X → (Y → Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ)) (h : Fin N → ℝ)
    (x : X) (y : Y) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i k =>
    fderiv ℝ (fun ψ => φ x ψ h i) (constCfg h) (Pi.single y (Pi.single k 1))

/-- **The properties of the background used by Lemma 2.1** at the constant configuration `ψ ≡ h`,
`h·h = 1`: differentiability in `ψ`, the value `φ(x; h, h) = h`, the unit sphere constraint near
the constant configuration, and the covariance `φ(x; Sψ, h) = S φ(x; ψ, h)` under the stabilizer
of `h` (`S h = h`), all near the constant configuration. -/
structure IsBgAt (φ : X → (Y → Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ)) (h : Fin N → ℝ) :
    Prop where
  diff : ∀ x, DifferentiableAt ℝ (fun ψ => φ x ψ h) (constCfg h)
  value : ∀ x, φ x (constCfg h) h = h
  sphere : ∀ x, ∀ᶠ ψ in 𝓝 (constCfg (Y := Y) h), φ x ψ h ⬝ᵥ φ x ψ h = 1
  cov : ∀ x, ∀ S ∈ stabilizer h, ∀ᶠ ψ in 𝓝 (constCfg (Y := Y) h),
    φ x (fun y => S *ᵥ ψ y) h = S *ᵥ φ x ψ h

section Jacobian

variable {φ : X → (Y → Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ)} {h : Fin N → ℝ}

omit [Fintype Y] in
theorem single_eq_sum (y : Y) (w : Fin N → ℝ) :
    (Pi.single y w : Y → Fin N → ℝ) = ∑ k, w k • (Pi.single y (Pi.single k 1) : Y → Fin N → ℝ) := by
  ext z j
  by_cases hz : z = y
  · subst hz
    simp [Finset.sum_apply, Pi.single_apply]
  · simp [Finset.sum_apply, Pi.single_eq_of_ne hz]

/-- The derivative of the field in the direction `δ_y w` is `H(x, y) w`. -/
theorem fderiv_single_eq (hb : IsBgAt φ h) (x : X) (y : Y) (w : Fin N → ℝ) :
    fderiv ℝ (fun ψ => φ x ψ h) (constCfg h) (Pi.single y w) = bgJac φ h x y *ᵥ w := by
  have hd : DifferentiableAt ℝ (fun ψ => φ x ψ h) (constCfg h) := hb.diff x
  have hdi : ∀ i, DifferentiableAt ℝ (fun ψ => φ x ψ h i) (constCfg h) := fun i =>
    (differentiableAt_pi (Φ := fun ψ => φ x ψ h)).1 hd i
  ext i
  have hcoord : fderiv ℝ (fun ψ => φ x ψ h) (constCfg h) (Pi.single y w) i =
      fderiv ℝ (fun ψ => φ x ψ h i) (constCfg h) (Pi.single y w) := by
    rw [fderiv_pi (fun i => hdi i)]
    rfl
  rw [hcoord, single_eq_sum, map_sum]
  simp only [map_smul, smul_eq_mul, bgJac, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Item (1), the sphere constraint**: `hᵀ H(x, y) = 0` (the range of `H` is `h^⊥`). -/
theorem sphere_range (hb : IsBgAt φ h) (x : X) (y : Y) :
    h ᵥ* bgJac φ h x y = 0 := by
  have hd := hb.diff x
  have hdi : ∀ i, HasFDerivAt (fun ψ => φ x ψ h i) (fderiv ℝ (fun ψ => φ x ψ h i) (constCfg h))
      (constCfg h) := fun i =>
    ((differentiableAt_pi (Φ := fun ψ => φ x ψ h)).1 hd i).hasFDerivAt
  have hg : HasFDerivAt (fun ψ => ∑ i, φ x ψ h i * φ x ψ h i)
      (∑ i, (φ x (constCfg h) h i • fderiv ℝ (fun ψ => φ x ψ h i) (constCfg h) +
        φ x (constCfg h) h i • fderiv ℝ (fun ψ => φ x ψ h i) (constCfg h))) (constCfg h) :=
    HasFDerivAt.fun_sum fun i _ => (hdi i).mul (hdi i)
  have hconst : HasFDerivAt (fun ψ => ∑ i, φ x ψ h i * φ x ψ h i)
      (0 : (Y → Fin N → ℝ) →L[ℝ] ℝ) (constCfg h) :=
    (hasFDerivAt_const (1 : ℝ) (constCfg h)).congr_of_eventuallyEq
      ((hb.sphere x).mono fun ψ hψ => by simpa [dotProduct] using hψ)
  funext k
  have heq := congrArg (fun A => A (Pi.single y (Pi.single k 1))) (hg.unique hconst)
  simp only [_root_.sum_apply, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul, _root_.zero_apply,
    hb.value x] at heq
  simp only [Matrix.vecMul, dotProduct, bgJac, Matrix.of_apply, Pi.zero_apply]
  have : ∑ i, (h i * fderiv ℝ (fun ψ => φ x ψ h i) (constCfg h) (Pi.single y (Pi.single k 1)) +
      h i * fderiv ℝ (fun ψ => φ x ψ h i) (constCfg h) (Pi.single y (Pi.single k 1))) =
      2 * ∑ i, h i * fderiv ℝ (fun ψ => φ x ψ h i) (constCfg h) (Pi.single y (Pi.single k 1)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this] at heq
  linarith

/-- Multiplication by a matrix as a continuous linear map. -/
noncomputable def mulCLM (S : Matrix (Fin N) (Fin N) ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin S)

/-- Pointwise multiplication `ψ ↦ (S ψ(y))_y` as a continuous linear map. -/
noncomputable def diagCLM (S : Matrix (Fin N) (Fin N) ℝ) :
    (Y → Fin N → ℝ) →L[ℝ] (Y → Fin N → ℝ) :=
  ContinuousLinearMap.pi fun y => (mulCLM S).comp (ContinuousLinearMap.proj y)

@[simp] theorem mulCLM_apply (S : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) :
    mulCLM S v = S *ᵥ v := rfl

omit [Fintype Y] [DecidableEq Y] in
@[simp] theorem diagCLM_apply (S : Matrix (Fin N) (Fin N) ℝ) (ψ : Y → Fin N → ℝ) (y : Y) :
    diagCLM S ψ y = S *ᵥ ψ y := rfl

/-- **Covariance of the Jacobian**: `H(x, y) S = S H(x, y)` for `S` in the stabilizer of `h`
(differentiating `φ(x; Sψ, h) = S φ(x; ψ, h)` at `ψ ≡ h`, which `S` fixes). -/
theorem jac_commutes (hb : IsBgAt φ h) {S : Matrix (Fin N) (Fin N) ℝ} (hS : S ∈ stabilizer h)
    (x : X) (y : Y) : bgJac φ h x y * S = S * bgJac φ h x y := by
  have hd := hb.diff x
  have hSc : diagCLM (Y := Y) S (constCfg h) = constCfg h := by
    ext z j
    simp [constCfg, hS.2]
  have h1 : HasFDerivAt (fun ψ => φ x (diagCLM S ψ) h)
      ((fderiv ℝ (fun ψ => φ x ψ h) (constCfg h)).comp (diagCLM S)) (constCfg h) := by
    have hd' : DifferentiableAt ℝ (fun ψ => φ x ψ h) (diagCLM S (constCfg h)) := by
      rw [hSc]; exact hd
    have := hd'.hasFDerivAt.comp (constCfg h) (diagCLM (Y := Y) S).hasFDerivAt
    rw [hSc] at this
    exact this
  have h2 : HasFDerivAt (fun ψ => S *ᵥ φ x ψ h)
      ((mulCLM S).comp (fderiv ℝ (fun ψ => φ x ψ h) (constCfg h))) (constCfg h) :=
    (mulCLM S).hasFDerivAt.comp (constCfg h) hd.hasFDerivAt
  have h3 : HasFDerivAt (fun ψ => φ x (diagCLM S ψ) h)
      ((mulCLM S).comp (fderiv ℝ (fun ψ => φ x ψ h) (constCfg h))) (constCfg h) :=
    h2.congr_of_eventuallyEq ((hb.cov x S hS).mono fun ψ hψ => hψ)
  have h4 := h1.unique h3
  ext i k
  have h5 := congrArg (fun A => A (Pi.single y (Pi.single k 1) : Y → Fin N → ℝ)) h4
  simp only [ContinuousLinearMap.comp_apply, mulCLM_apply] at h5
  have hSv : diagCLM (Y := Y) S (Pi.single y (Pi.single k 1)) =
      Pi.single y (S *ᵥ Pi.single k 1) := by
    ext z j
    by_cases hz : z = y
    · subst hz; simp
    · simp [Pi.single_eq_of_ne hz]
  rw [hSv, fderiv_single_eq hb, fderiv_single_eq hb] at h5
  have h6 := congrFun h5 i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h6
  simpa [Matrix.mulVec_single_one] using h6

end Jacobian

section Algebra

variable {h : Fin N → ℝ}

/-- The projection onto `ℝ h`. -/
def hProj (h : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ := vecMulVec h h

/-- The projection onto `h^⊥`. -/
def hPerp (h : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ := 1 - vecMulVec h h

theorem hProj_mul_hProj (hh : h ⬝ᵥ h = 1) : hProj h * hProj h = hProj h := by
  simp [hProj, vecMulVec_mul_vecMulVec, hh]

theorem hPerp_mul_hPerp (hh : h ⬝ᵥ h = 1) : hPerp h * hPerp h = hPerp h := by
  have := hProj_mul_hProj hh
  simp only [hPerp, hProj] at *
  calc (1 - vecMulVec h h) * (1 - vecMulVec h h) =
        1 - vecMulVec h h - vecMulVec h h + vecMulVec h h * vecMulVec h h := by noncomm_ring
    _ = 1 - vecMulVec h h := by rw [this]; abel

theorem hPerp_mul_hProj (hh : h ⬝ᵥ h = 1) : hPerp h * hProj h = 0 := by
  have := hProj_mul_hProj hh
  simp only [hPerp, hProj] at *
  rw [sub_mul, Matrix.one_mul, this, sub_self]

theorem hProj_mul_hPerp (hh : h ⬝ᵥ h = 1) : hProj h * hPerp h = 0 := by
  have := hProj_mul_hProj hh
  simp only [hPerp, hProj] at *
  rw [mul_sub, Matrix.mul_one, this, sub_self]

theorem hPerp_transpose : (hPerp h)ᵀ = hPerp h := by
  simp [hPerp, transpose_vecMulVec]

theorem vecMul_hPerp (hh : h ⬝ᵥ h = 1) : h ᵥ* hPerp h = 0 := by
  simp [hPerp, Matrix.vecMul_sub, vecMul_vecMulVec, hh]

theorem hPerp_mulVec (hh : h ⬝ᵥ h = 1) : hPerp h *ᵥ h = 0 := by
  rw [← Matrix.vecMul_transpose, hPerp_transpose, vecMul_hPerp hh]

end Algebra

section Structure

variable {φ : X → (Y → Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ)} {h : Fin N → ℝ}

/-- **Item (2) for the Jacobian**: `H(x, y) = s(x, y) (1 - hhᵀ)`: `H` maps `ℝh` to `0`
(sphere constraint plus covariance) and is a scalar on `h^⊥`. -/
theorem jac_scalar [NeZero N] (hb : IsBgAt φ h) (hh : h ⬝ᵥ h = 1) (x : X) (y : Y) :
    ∃ s : ℝ, bgJac φ h x y = s • hPerp h := by
  obtain ⟨a, b, hab⟩ := commutant_stabilizer hh (fun S hS => (jac_commutes hb hS x y).symm)
  have h0 := sphere_range hb x y
  rw [hab] at h0
  have h1 : a • h = 0 := by
    simpa [Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_sub, vecMul_vecMulVec, hh] using h0
  have h2 : a = 0 := by
    have := congrArg (fun v => v ⬝ᵥ h) h1
    simpa [hh] using this
  exact ⟨b, by rw [hab, h2, zero_smul, zero_add]; rfl⟩

/-- A covariance commuting with the stabilizer is block diagonal in `ℝh ⊕ h^⊥`:
`C = c_tr (1 - hhᵀ) + c_lg hhᵀ`. -/
theorem cov_blocks [NeZero N] (hh : h ⬝ᵥ h = 1) {C : Matrix (Fin N) (Fin N) ℝ}
    (hC : ∀ S ∈ stabilizer h, S * C = C * S) :
    ∃ ctr clg : ℝ, C = ctr • hPerp h + clg • hProj h := by
  obtain ⟨a, b, hab⟩ := commutant_stabilizer hh hC
  exact ⟨b, a, by rw [hab, add_comm]; rfl⟩

omit [DecidableEq Y] in
/-- **Item (3)**: the kernel `G(x, x') = ∑_{y, y'} H(x, y) C(y, y') H(x', y')ᵀ` is transverse:
`G = g (1 - hhᵀ)`, hence `hᵀ G = 0` and `G h = 0`: the longitudinal part vanishes identically. -/
theorem gauss_transverse (hh : h ⬝ᵥ h = 1) {Hm : X → Y → Matrix (Fin N) (Fin N) ℝ}
    {Cm : Y → Y → Matrix (Fin N) (Fin N) ℝ} (hH : ∀ x y, ∃ s : ℝ, Hm x y = s • hPerp h)
    (hC : ∀ y y', ∃ ctr clg : ℝ, Cm y y' = ctr • hPerp h + clg • hProj h) (x x' : X) :
    ∃ g : ℝ, ∑ y, ∑ y', Hm x y * Cm y y' * (Hm x' y')ᵀ = g • hPerp h := by
  choose s hs using hH
  choose ctr clg hc using hC
  refine ⟨∑ y, ∑ y', s x y * ctr y y' * s x' y', ?_⟩
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [hs, hs, hc, Matrix.transpose_smul, hPerp_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add,
    hPerp_mul_hPerp hh, hPerp_mul_hProj hh, smul_zero, add_zero, smul_smul]
  congr 1
  ring

/-- The kernel `G(x, x') = ∑_{y, y'} H(x, y) C(y, y') H(x', y')ᵀ` (`G^{(j)} = H_{j-1} C^{(j-1)}
H_{j-1}^*`, in the plain transpose convention). -/
noncomputable def gaussKernel (Hm : X → Y → Matrix (Fin N) (Fin N) ℝ)
    (Cm : Y → Y → Matrix (Fin N) (Fin N) ℝ) (x x' : X) : Matrix (Fin N) (Fin N) ℝ :=
  ∑ y, ∑ y', Hm x y * Cm y y' * (Hm x' y')ᵀ

omit [DecidableEq Y] in
theorem gaussKernel_transverse (hh : h ⬝ᵥ h = 1) {Hm : X → Y → Matrix (Fin N) (Fin N) ℝ}
    {Cm : Y → Y → Matrix (Fin N) (Fin N) ℝ} (hH : ∀ x y, ∃ s : ℝ, Hm x y = s • hPerp h)
    (hC : ∀ y y', ∃ ctr clg : ℝ, Cm y y' = ctr • hPerp h + clg • hProj h) (x x' : X) :
    (∃ g : ℝ, gaussKernel Hm Cm x x' = g • hPerp h) ∧ h ᵥ* gaussKernel Hm Cm x x' = 0 ∧
      gaussKernel Hm Cm x x' *ᵥ h = 0 := by
  obtain ⟨g, hg⟩ := gauss_transverse hh hH hC x x'
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · show h ᵥ* (∑ y, ∑ y', Hm x y * Cm y y' * (Hm x' y')ᵀ) = 0
    rw [hg, Matrix.vecMul_smul, vecMul_hPerp hh, smul_zero]
  · show (∑ y, ∑ y', Hm x y * Cm y y' * (Hm x' y')ᵀ) *ᵥ h = 0
    rw [hg, Matrix.smul_mulVec, hPerp_mulVec hh, smul_zero]

/-- **Lemma 2.1 (structure at the constant configuration).**  Let `φ` be a unit-vector field with
the properties `IsBgAt` at the constant configuration `ψ ≡ h`, `|h| = 1`, `N ≥ 1`, and let
`C(y, y')` be matrices commuting with the stabilizer of `h` (the covariance of the fluctuation
field).  Then, with `H = bgJac φ h` and `G = H C Hᵀ`:
1. `hᵀ H(x, y) = 0` (the range of `H` is `h^⊥`);
2. `H(x, y) = s (1 - hhᵀ)` and `C(y, y') = c_tr (1 - hhᵀ) + c_lg hhᵀ`;
3. `G(x, x') = g (1 - hhᵀ)`, so `hᵀ G = 0 = G h`: the longitudinal part of `G` vanishes. -/
theorem lemma_2_1 [NeZero N] {φ : X → (Y → Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ)}
    (hb : IsBgAt φ h) (hh : h ⬝ᵥ h = 1) {Cm : Y → Y → Matrix (Fin N) (Fin N) ℝ}
    (hC : ∀ y y', ∀ S ∈ stabilizer h, S * Cm y y' = Cm y y' * S) :
    (∀ x y, h ᵥ* bgJac φ h x y = 0) ∧ (∀ x y, ∃ s : ℝ, bgJac φ h x y = s • hPerp h) ∧
      (∀ y y', ∃ ctr clg : ℝ, Cm y y' = ctr • hPerp h + clg • hProj h) ∧
      ∀ x x', (∃ g : ℝ, gaussKernel (bgJac φ h) Cm x x' = g • hPerp h) ∧
        h ᵥ* gaussKernel (bgJac φ h) Cm x x' = 0 ∧ gaussKernel (bgJac φ h) Cm x x' *ᵥ h = 0 := by
  have h2 : ∀ x y, ∃ s : ℝ, bgJac φ h x y = s • hPerp h := jac_scalar hb hh
  have h3 : ∀ y y', ∃ ctr clg : ℝ, Cm y y' = ctr • hPerp h + clg • hProj h := fun y y' =>
    cov_blocks hh (hC y y')
  exact ⟨sphere_range hb, h2, h3, fun x x' => gaussKernel_transverse hh h2 h3 x x'⟩

end Structure

end Balaban.Observables
