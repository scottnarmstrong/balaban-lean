/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2
public import Balaban.Symmetry.TotallyReal
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Continuation of the real rotation invariance along a path of rotations

The small-field class asks invariance of the terms `ℰ`, `ℳ` under **real** orthogonal matrices
only (P1 (H.4), P4 (H.3)).  The terms are analytic on the field domain.  This file proves the
derived statement used for complex rotations: invariance under real `Q` and analyticity on a set
`D` that contains a path of rotations give invariance along that path.

* `eq_zero_of_real_on_segment`: a function analytic along a segment `[0, w₁]` of `ℂ^ι` which
  vanishes at the real points near `0` vanishes at `w₁` (landed `eventually_eq_zero_of_real` and
  the identity theorem along the segment);
* `eq_of_rotation_family`, `eqVec_of_rotation_family`: for an analytic family `R(w)` of matrices
  with `R(0) = 1`, real orthogonal at real `w`, the terms `ℰ` (resp. `ℳ`) satisfy
  `ℰ(R(w₁) Ψ, R(w₁) h) = ℰ(Ψ, h)` (resp. `ℳ(R(w₁)Ψ, R(w₁)h, R(w₁)g) = R(w₁) ℳ(Ψ, h, g)`) when the
  rotated data `R(w)(Ψ, h)` lie in `D` along the segment;
* `rotExp`: the family `w ↦ exp(A(w))`, `A(w)` the antisymmetric matrix with parameters `w`, which
  is complex orthogonal and real orthogonal at real `w`;
* `rotE_eq_of_exp_path`, `rotM_eq_of_exp_path`: **invariance along `R = Q exp(A)`**,
  `Q` real orthogonal, `A ∈ 𝔰𝔬(N, ℂ)`, whenever `exp(sA)(Ψ, h) ∈ D` for `s ∈ [0, 1]`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Symmetry Balaban.SmallField Balaban.SmallField.Def6 Filter Topology

/-! ### The identity theorem along a segment -/

/-- **A function analytic along `[0, w₁]` which vanishes at the real points near `0` vanishes at
`w₁`.** -/
theorem eq_zero_of_real_on_segment {ι : Type*} [Fintype ι] [DecidableEq ι] {g : (ι → ℂ) → ℂ}
    {w₁ : ι → ℂ} (hg : ∀ w ∈ segment ℝ (0 : ι → ℂ) w₁, AnalyticAt ℂ g w)
    (h0 : ∀ᶠ w in 𝓝 (0 : ι → ℂ), (∀ i, (w i).im = 0) → g w = 0) : g w₁ = 0 := by
  have hz : ∀ i, ((0 : ι → ℂ) i).im = 0 := by simp
  have hev := eventually_eq_zero_of_real hz (hg 0 (left_mem_segment ℝ _ _)) h0
  have han : AnalyticOnNhd ℂ g (segment ℝ (0 : ι → ℂ) w₁) := hg
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_segment 0 w₁).isPreconnected
    (left_mem_segment ℝ _ _) (hev.mono fun _ h => by simpa using h)
  simpa using this (right_mem_segment ℝ _ _)

/-! ### Analytic families of rotations act analytically on fields -/

section Family

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ι : Type*} [Fintype ι]

/-- The entries of the matrix family `R` are analytic functions of the parameter. -/
def AnalyticFam (R : (ι → ℂ) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ i j, AnalyticOnNhd ℂ (fun w => R w i j) Set.univ

theorem AnalyticFam.rotField {R : (ι → ℂ) → Matrix (Fin N) (Fin N) ℂ} (hR : AnalyticFam R)
    (Ψ : Fld d L N₁ m₁ k N) (w : ι → ℂ) :
    AnalyticAt ℂ (fun w => Def6.rotField (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
      (R w) Ψ) w := by
  refine analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_
  simp only [Def6.rotField, Matrix.mulVec, dotProduct]
  exact Finset.analyticAt_fun_sum _ fun l _ => (hR i l w (Set.mem_univ _)).mul analyticAt_const

theorem AnalyticFam.mulVec {R : (ι → ℂ) → Matrix (Fin N) (Fin N) ℂ} (hR : AnalyticFam R)
    (v : Fin N → ℂ) (w : ι → ℂ) (i : Fin N) :
    AnalyticAt ℂ (fun w => (R w).mulVec v i) w := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.analyticAt_fun_sum _ fun l _ => (hR i l w (Set.mem_univ _)).mul analyticAt_const

omit [NeZero L] [NeZero N₁] in
theorem rotField_one (Ψ : Fld d L N₁ m₁ k N) : Def6.rotField (1 : Matrix (Fin N) (Fin N) ℂ) Ψ = Ψ := by
  funext x; simp [Def6.rotField]

/-- **Continuation for the energy terms.**  Let `F` be analytic on a set `D` of pairs of fields,
invariant under every real orthogonal matrix (whenever both `(Ψ, h)` and the rotated pair lie in
`D`).  Let `R(w)` be an analytic family of matrices with `R(0) = 1` which is real orthogonal at real
`w`, and suppose `D` is a neighbourhood of `(Ψ, h)` and contains `R(w)(Ψ, h)` for `w` on the segment
`[0, w₁]`.  Then `F(R(w₁)Ψ, R(w₁)h) = F(Ψ, h)`. -/
theorem eq_of_rotation_family [DecidableEq ι] (F : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (D : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))
    (hF : AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => F p.1 p.2) D)
    (hreal : ∀ Q : Matrix (Fin N) (Fin N) ℂ, IsRot Q → ∀ Ψ h, (Ψ, h) ∈ D →
      (rotField Q Ψ, rotField Q h) ∈ D → F (rotField Q Ψ) (rotField Q h) = F Ψ h)
    (R : (ι → ℂ) → Matrix (Fin N) (Fin N) ℂ) (hR : AnalyticFam R) (hR0 : R 0 = 1)
    (hRr : ∀ w : ι → ℂ, (∀ i, (w i).im = 0) → IsRot (R w))
    {Ψ h : Fld d L N₁ m₁ k N} (hD : D ∈ 𝓝 (Ψ, h)) {w₁ : ι → ℂ}
    (hpath : ∀ w ∈ segment ℝ (0 : ι → ℂ) w₁, (rotField (R w) Ψ, rotField (R w) h) ∈ D) :
    F (rotField (R w₁) Ψ) (rotField (R w₁) h) = F Ψ h := by
  set q : (ι → ℂ) → Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N :=
    fun w => (rotField (R w) Ψ, rotField (R w) h) with hq
  have hqa : ∀ w, AnalyticAt ℂ q w := fun w => (hR.rotField Ψ w).prod (hR.rotField h w)
  have hq0 : q 0 = (Ψ, h) := by simp [hq, hR0, rotField_one]
  have key := eq_zero_of_real_on_segment
    (g := fun w => F (q w).1 (q w).2 - F Ψ h) (w₁ := w₁)
    (fun w hw => ((hF (q w) (hpath w hw)).comp (hqa w)).sub analyticAt_const) (by
      have hev : ∀ᶠ w in 𝓝 (0 : ι → ℂ), q w ∈ D := by
        have := (hqa 0).continuousAt.eventually_mem (hq0 ▸ hD)
        exact this
      filter_upwards [hev] with w hw hwr
      have := hreal (R w) (hRr w hwr) Ψ h (mem_of_mem_nhds hD) hw
      simpa [hq, sub_eq_zero] using this)
  simpa [hq, sub_eq_zero] using key

/-- **Continuation for the source terms** (equivariance): as `eq_of_rotation_family` for
`M(R Ψ, R h, R g) = R M(Ψ, h, g)`. -/
theorem eqVec_of_rotation_family [DecidableEq ι]
    (M : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → Fin N → ℂ)
    (D : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))
    (hM : AnalyticOnNhd ℂ
      (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => M p.1 p.2.1 p.2.2) D)
    (hreal : ∀ Q : Matrix (Fin N) (Fin N) ℂ, IsRot Q → ∀ Ψ h g, (Ψ, h, g) ∈ D →
      (rotField Q Ψ, rotField Q h, rotField Q g) ∈ D →
      M (rotField Q Ψ) (rotField Q h) (rotField Q g) = Q.mulVec (M Ψ h g))
    (R : (ι → ℂ) → Matrix (Fin N) (Fin N) ℂ) (hR : AnalyticFam R) (hR0 : R 0 = 1)
    (hRr : ∀ w : ι → ℂ, (∀ i, (w i).im = 0) → IsRot (R w))
    {Ψ h g : Fld d L N₁ m₁ k N} (hD : D ∈ 𝓝 (Ψ, h, g)) {w₁ : ι → ℂ}
    (hpath : ∀ w ∈ segment ℝ (0 : ι → ℂ) w₁,
      (rotField (R w) Ψ, rotField (R w) h, rotField (R w) g) ∈ D) :
    M (rotField (R w₁) Ψ) (rotField (R w₁) h) (rotField (R w₁) g) = (R w₁).mulVec (M Ψ h g) := by
  set q : (ι → ℂ) → Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N :=
    fun w => (rotField (R w) Ψ, rotField (R w) h, rotField (R w) g) with hq
  have hqa : ∀ w, AnalyticAt ℂ q w := fun w =>
    (hR.rotField Ψ w).prod ((hR.rotField h w).prod (hR.rotField g w))
  have hq0 : q 0 = (Ψ, h, g) := by simp [hq, hR0, rotField_one]
  have hev : ∀ᶠ w in 𝓝 (0 : ι → ℂ), q w ∈ D :=
    (hqa 0).continuousAt.eventually_mem (hq0 ▸ hD)
  funext i
  have key := eq_zero_of_real_on_segment
    (g := fun w => M (q w).1 (q w).2.1 (q w).2.2 i - (R w).mulVec (M Ψ h g) i) (w₁ := w₁)
    (fun w hw => (((analyticAt_pi_iff.1 ((hM (q w) (hpath w hw)).comp (hqa w))) i).sub
      (hR.mulVec _ w i))) (by
      filter_upwards [hev] with w hw hwr
      have := hreal (R w) (hRr w hwr) Ψ h g (mem_of_mem_nhds hD) hw
      simp only [hq]
      rw [this, sub_self])
  simpa [hq, sub_eq_zero] using key

end Family

/-! ### The family `exp(A(w))` -/

section Exp

variable {N : ℕ}

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The antisymmetric matrix with parameters `w`: `A(w)_{ij} = w_{ij} - w_{ji}`. -/
def soParam (w : Fin N × Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => w (i, j) - w (j, i)

/-- The family `w ↦ exp(A(w))`. -/
noncomputable def rotExp (w : Fin N × Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  NormedSpace.exp (soParam w)

theorem soParam_transpose (w : Fin N × Fin N → ℂ) : (soParam w).transpose = -soParam w := by
  ext i j; simp [soParam]

theorem rotExp_zero : rotExp (0 : Fin N × Fin N → ℂ) = 1 := by
  have : soParam (0 : Fin N × Fin N → ℂ) = 0 := by ext i j; simp [soParam]
  simp [rotExp, this]

theorem rotExp_transpose_mul (w : Fin N × Fin N → ℂ) :
    (rotExp w).transpose * rotExp w = 1 := by
  unfold rotExp
  have hc : Commute (-soParam w) (soParam w) := (Commute.refl _).neg_left
  rw [← Matrix.exp_transpose, soParam_transpose, ← Matrix.exp_add_of_commute _ _ hc]
  simp

theorem soParam_conjTranspose_of_real {w : Fin N × Fin N → ℂ} (hw : ∀ i, (w i).im = 0) :
    (soParam w).conjTranspose = -soParam w := by
  ext i j
  have h1 := Complex.conj_eq_iff_im.2 (hw (j, i))
  have h2 := Complex.conj_eq_iff_im.2 (hw (i, j))
  simp [soParam, Matrix.conjTranspose_apply, h1, h2]

/-- `exp(A(w))` is real for real `w`. -/
theorem rotExp_real {w : Fin N × Fin N → ℂ} (hw : ∀ i, (w i).im = 0) (i j : Fin N) :
    (rotExp w i j).im = 0 := by
  have h : (rotExp w).conjTranspose = (rotExp w).transpose := by
    unfold rotExp
    rw [← Matrix.exp_conjTranspose, ← Matrix.exp_transpose, soParam_conjTranspose_of_real hw,
      ← soParam_transpose]
  have := congrFun (congrFun h j) i
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at this
  exact Complex.conj_eq_iff_im.1 this

theorem rotExp_isRot {w : Fin N × Fin N → ℂ} (hw : ∀ i, (w i).im = 0) : IsRot (rotExp w) :=
  ⟨rotExp_transpose_mul w, rotExp_real hw⟩

theorem analyticFam_rotExp : AnalyticFam (rotExp (N := N)) := by
  intro i j w _
  let L : (Fin N × Fin N → ℂ) →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ :=
    { toFun := soParam
      map_add' := fun a b => by ext i j; simp [soParam]; ring
      map_smul' := fun c a => by ext i j; simp [soParam]; ring }
  let Lc := LinearMap.toContinuousLinearMap L
  let E : Matrix (Fin N) (Fin N) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have h1 : AnalyticAt ℂ (fun w => NormedSpace.exp (Lc w)) w :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) (Lc w)).comp (Lc.analyticAt w)
  exact (E.analyticAt _).comp h1

end Exp

/-! ### Invariance along `R = Q exp(A)` -/

section Path

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The parameters of an antisymmetric matrix. -/
noncomputable def soCoord (A : Matrix (Fin N) (Fin N) ℂ) : Fin N × Fin N → ℂ :=
  fun p => A p.1 p.2 / 2

theorem soParam_soCoord {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.transpose = -A) :
    soParam (soCoord A) = A := by
  ext i j
  have : A j i = -A i j := by
    have := congrFun (congrFun hA i) j
    simpa using this
  simp [soParam, soCoord, this]
  ring

theorem soParam_smul (s : ℂ) (w : Fin N × Fin N → ℂ) : soParam (s • w) = s • soParam w := by
  ext i j; simp [soParam]; ring

theorem rotExp_smul_soCoord {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.transpose = -A) (s : ℂ) :
    rotExp (s • soCoord A) = NormedSpace.exp (s • A) := by
  simp [rotExp, soParam_smul, soParam_soCoord hA]

theorem mem_segment_zero {E : Type*} [AddCommGroup E] [Module ℝ E] {w w₁ : E}
    (h : w ∈ segment ℝ (0 : E) w₁) : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ w = s • w₁ := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h
  exact ⟨b, hb, by linarith, by simp⟩

omit [NeZero L] [NeZero N₁] in
theorem rotField_mul (Q M : Matrix (Fin N) (Fin N) ℂ) (Ψ : Fld d L N₁ m₁ k N) :
    Def6.rotField (Q * M) Ψ = Def6.rotField Q (Def6.rotField M Ψ) := by
  funext x; simp [Def6.rotField, Matrix.mulVec_mulVec]

/-- **Invariance of the energy terms along `R = Q exp(A)`.**  Let `F` be analytic on `D`, invariant
under the real orthogonal matrices, `Q` real orthogonal, `A` complex antisymmetric (an element of
`𝔰𝔬(N, ℂ)`), `D` a neighbourhood of `(Ψ, h)`, and `exp(sA)(Ψ, h) ∈ D` for `s ∈ [0, 1]`,
`Q exp(A)(Ψ, h) ∈ D`.  Then `F(Q exp(A) Ψ, Q exp(A) h) = F(Ψ, h)`. -/
theorem rotE_eq_of_exp_path (F : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (D : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))
    (hF : AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => F p.1 p.2) D)
    (hreal : ∀ Q : Matrix (Fin N) (Fin N) ℂ, IsRot Q → ∀ Ψ h, (Ψ, h) ∈ D →
      (Def6.rotField Q Ψ, Def6.rotField Q h) ∈ D →
      F (Def6.rotField Q Ψ) (Def6.rotField Q h) = F Ψ h)
    {Q A : Matrix (Fin N) (Fin N) ℂ} (hQ : IsRot Q) (hA : A.transpose = -A)
    {Ψ h : Fld d L N₁ m₁ k N} (hD : D ∈ 𝓝 (Ψ, h))
    (hpath : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (Def6.rotField (NormedSpace.exp ((s : ℂ) • A)) Ψ,
        Def6.rotField (NormedSpace.exp ((s : ℂ) • A)) h) ∈ D)
    (hend : (Def6.rotField (Q * NormedSpace.exp A) Ψ, Def6.rotField (Q * NormedSpace.exp A) h) ∈
      D) :
    F (Def6.rotField (Q * NormedSpace.exp A) Ψ) (Def6.rotField (Q * NormedSpace.exp A) h) =
      F Ψ h := by
  have h1 := eq_of_rotation_family F D hF hreal rotExp analyticFam_rotExp rotExp_zero
    (fun w hw => rotExp_isRot hw) hD (w₁ := soCoord A) (fun w hw => by
      obtain ⟨s, hs0, hs1, rfl⟩ := mem_segment_zero hw
      have : s • soCoord A = (s : ℂ) • soCoord A := by simp [Complex.coe_smul]
      rw [this, rotExp_smul_soCoord hA]
      exact hpath s hs0 hs1)
  rw [show rotExp (soCoord A) = NormedSpace.exp A by
    simpa using rotExp_smul_soCoord hA 1] at h1
  have hp1 : (Def6.rotField (NormedSpace.exp A) Ψ, Def6.rotField (NormedSpace.exp A) h) ∈ D := by
    simpa using hpath 1 zero_le_one le_rfl
  rw [rotField_mul, rotField_mul] at hend ⊢
  rw [hreal Q hQ _ _ hp1 hend, h1]

/-- **Equivariance of the source terms along `R = Q exp(A)`**: as `rotE_eq_of_exp_path` for
`M(R Ψ, R h, R g) = R M(Ψ, h, g)`. -/
theorem rotM_eq_of_exp_path
    (M : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → Fin N → ℂ)
    (D : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))
    (hM : AnalyticOnNhd ℂ
      (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => M p.1 p.2.1 p.2.2) D)
    (hreal : ∀ Q : Matrix (Fin N) (Fin N) ℂ, IsRot Q → ∀ Ψ h g, (Ψ, h, g) ∈ D →
      (Def6.rotField Q Ψ, Def6.rotField Q h, Def6.rotField Q g) ∈ D →
      M (Def6.rotField Q Ψ) (Def6.rotField Q h) (Def6.rotField Q g) = Q.mulVec (M Ψ h g))
    {Q A : Matrix (Fin N) (Fin N) ℂ} (hQ : IsRot Q) (hA : A.transpose = -A)
    {Ψ h g : Fld d L N₁ m₁ k N} (hD : D ∈ 𝓝 (Ψ, h, g))
    (hpath : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (Def6.rotField (NormedSpace.exp ((s : ℂ) • A)) Ψ,
        Def6.rotField (NormedSpace.exp ((s : ℂ) • A)) h,
        Def6.rotField (NormedSpace.exp ((s : ℂ) • A)) g) ∈ D)
    (hend : (Def6.rotField (Q * NormedSpace.exp A) Ψ, Def6.rotField (Q * NormedSpace.exp A) h,
      Def6.rotField (Q * NormedSpace.exp A) g) ∈ D) :
    M (Def6.rotField (Q * NormedSpace.exp A) Ψ) (Def6.rotField (Q * NormedSpace.exp A) h)
        (Def6.rotField (Q * NormedSpace.exp A) g) =
      (Q * NormedSpace.exp A).mulVec (M Ψ h g) := by
  have h1 := eqVec_of_rotation_family M D hM hreal rotExp analyticFam_rotExp rotExp_zero
    (fun w hw => rotExp_isRot hw) hD (w₁ := soCoord A) (fun w hw => by
      obtain ⟨s, hs0, hs1, rfl⟩ := mem_segment_zero hw
      have : s • soCoord A = (s : ℂ) • soCoord A := by simp [Complex.coe_smul]
      rw [this, rotExp_smul_soCoord hA]
      exact hpath s hs0 hs1)
  rw [show rotExp (soCoord A) = NormedSpace.exp A by
    simpa using rotExp_smul_soCoord hA 1] at h1
  have hp1 : (Def6.rotField (NormedSpace.exp A) Ψ, Def6.rotField (NormedSpace.exp A) h,
      Def6.rotField (NormedSpace.exp A) g) ∈ D := by
    simpa using hpath 1 zero_le_one le_rfl
  rw [rotField_mul, rotField_mul, rotField_mul] at hend ⊢
  rw [hreal Q hQ _ _ _ hp1 hend, h1, Matrix.mulVec_mulVec]

/-- **The complex rotation invariance `CRotE` from the real clause `rotE` and a path.**  If the
domain is open at its points and every pair `(Ψ, h)`, `(RΨ, Rh)` of the domain related by
`R ∈ IsCRot` is joined by a path `exp(sA)(Ψ, h)`, `s ∈ [0, 1]`, in the domain with
`R = Q exp(A)`, `Q` real orthogonal, `A ∈ 𝔰𝔬(N, ℂ)`, then the terms are invariant under `R`.
(That every such pair of the domain `Ξ^c_j` is joined by a path is not proved.) -/
theorem SFTermClauses.cRotE_of_path {P : Consts} {ϱ : ℝ} {Dom : FieldDom d L N₁ m₁ k N ϱ}
    {Tm : Terms d L N₁ m₁ k N ϱ} (hT : SFTermClauses P Dom Tm)
    (hopen : ∀ j G Ψ h, Dom.dom j G Ψ h → {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N |
      Dom.dom j G p.1 p.2} ∈ 𝓝 (Ψ, h))
    (hconn : ∀ j G Ψ h (R : Matrix (Fin N) (Fin N) ℂ), IsCRot R → Dom.dom j G Ψ h →
      Dom.dom j G (Def6.rotField R Ψ) (Def6.rotField R h) →
      ∃ Q A : Matrix (Fin N) (Fin N) ℂ, IsRot Q ∧ A.transpose = -A ∧
        R = Q * NormedSpace.exp A ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
          Dom.dom j G (Def6.rotField (NormedSpace.exp ((s : ℂ) • A)) Ψ)
            (Def6.rotField (NormedSpace.exp ((s : ℂ) • A)) h)) :
    CRotE P Dom Tm := by
  intro j hj1 hjk y X hX hy R hR Ψ h hd hdR
  obtain ⟨Q, A, hQ, hA, rfl, hp⟩ := hconn j (Tm.gs j X) Ψ h R hR hd hdR
  exact rotE_eq_of_exp_path (fun Ψ h => Tm.E j y X Ψ h) {p | Dom.dom j (Tm.gs j X) p.1 p.2}
    (hT.analyticE j hj1 hjk y X hX hy)
    (fun Q hQ Ψ h h1 h2 => hT.rotE j hj1 hjk y X hX hy Q hQ Ψ h h1 h2) hQ hA
    (hopen j _ Ψ h hd) hp hdR

end Path

end Balaban.SmallField.Def6v2
