/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovBound
public import Balaban.Localization.DecoupledIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Continuity in `x` of the decoupled objects (measurability of the `x`-integrands)

For the `x`-integrals of I-4c (ii) the integrands `x ↦ C_x(s)` must be measurable. Every ingredient
is built from the continuous family `x ↦ H_{k,x}` (affine in `s₁(x) = a_k x/(a_k + x)` and
`s₂(x)`), products, sums and inverses of invertible matrices, hence continuous on `x ≥ 0`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix Set Filter Topology

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {α : G.Ω 1 → ℂ} {κ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}

variable (G) in
/-- The part of the averaging form independent of `(s₁, s₂)`. -/
noncomputable def xAvg0 (a : ℕ → ℝ) :
    Matrix (Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) (Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) ℝ :=
  ∑ j ∈ Icc 1 k, (a j / ((L : ℝ) ^ j) ^ 2) • layerBlockMatrix G j j

variable (G) in
/-- The coefficient matrix of `s₁`. -/
noncomputable def xAvg1 :
    Matrix (Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) (Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) ℝ :=
  (1 / ((L : ℝ) ^ k) ^ 2) • (layerBlockMatrix G (k + 1) k - layerBlockMatrix G (k + 1) (k + 1))

variable (G) in
/-- The coefficient matrix of `s₂`. -/
noncomputable def xAvg2 :
    Matrix (Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) (Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) ℝ :=
  (1 / ((L : ℝ) ^ k) ^ 2) • layerBlockMatrix G (k + 1) (k + 1)

theorem xAvgMatrix_affine (a : ℕ → ℝ) (s₁ s₂ : ℝ) :
    xAvgMatrix G a s₁ s₂ = xAvg0 G a + s₁ • xAvg1 G + s₂ • xAvg2 G := by
  unfold xAvgMatrix xAvg0 xAvg1 xAvg2
  module

theorem continuousOn_xS1 {ak : ℝ} (hak : 0 < ak) : ContinuousOn (fun x => xS1 ak x) (Ici 0) := by
  unfold xS1
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
  have : (0 : ℝ) ≤ x := hx
  linarith

theorem continuousOn_xS2 {ak b : ℝ} (hak : 0 < ak) (hb : 0 ≤ b) :
    ContinuousOn (fun x => xS2 ak b x) (Ici 0) := by
  unfold xS2
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
  have : (0 : ℝ) ≤ x := hx
  linarith

theorem continuousOn_restrict_map {T : Type*} [Fintype T] [DecidableEq T] (Λ : Finset T)
    {F : ℝ → Matrix T T ℝ} {S : Set ℝ} (hF : ContinuousOn F S) :
    ContinuousOn (fun x => Green.restrictOp ((F x).map (algebraMap ℝ ℂ)) Λ) S := by
  have hc : Continuous (fun A : Matrix T T ℝ =>
      Green.restrictOp (A.map (algebraMap ℝ ℂ)) Λ) := by
    unfold Green.restrictOp
    exact Continuous.matrix_submatrix (Continuous.matrix_map continuous_id
      (continuous_algebraMap ℝ ℂ)) _ _
  exact hc.comp_continuousOn hF

theorem continuousOn_xAvg_x (hak : 0 < a k) (hb : 0 ≤ aT / (L : ℝ) ^ 2) :
    ContinuousOn (fun x => xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x))
      (Ici 0) := by
  simp only [xAvgMatrix_affine]
  have h1 := continuousOn_xS1 hak
  have h2 := continuousOn_xS2 (b := aT / (L : ℝ) ^ 2) hak hb
  fun_prop

theorem continuousOn_cutXFullMatrix (hak : 0 < a k) (hb : 0 ≤ aT / (L : ℝ) ^ 2)
    (cut : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)) :
    ContinuousOn (fun x => cutXFullMatrix G a aT x ν cut) (Ici 0) := by
  have hA := continuousOn_xAvg_x (G := G) (a := a) (aT := aT) hak hb
  have : (fun x => cutXFullMatrix G a aT x ν cut) =
      fun x => cutLaplacian ν cut + xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) :=
    rfl
  rw [this]
  exact ContinuousOn.add continuousOn_const hA

theorem continuousOn_cutXOperator (hak : 0 < a k) (hb : 0 ≤ aT / (L : ℝ) ^ 2)
    (cut : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)) (α : G.Ω 1 → ℂ) :
    ContinuousOn (fun x => cutXOperator G a aT x ν cut α) (Ici 0) := by
  unfold cutXOperator
  exact (continuousOn_restrict_map _ (continuousOn_cutXFullMatrix hak hb cut)).add continuousOn_const

section LiftCont

theorem contOn_matrix_mul {m n p : Type*} [Fintype n] {S : Set ℝ} {F : ℝ → Matrix m n ℂ}
    {H : ℝ → Matrix n p ℂ} (hF : ContinuousOn F S) (hH : ContinuousOn H S) :
    ContinuousOn (fun x => F x * H x) S := by
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  refine continuousOn_finsetSum _ fun l _ => ?_
  exact (continuousOn_pi.1 (continuousOn_pi.1 hF i) l).mul
    (continuousOn_pi.1 (continuousOn_pi.1 hH l) j)


variable {ι : Type*} [Fintype ι] {S : Set ℝ}

omit [Fintype ι] in
theorem continuousOn_liftOp {F : ℝ → Matrix ι ι ℂ} (hF : ContinuousOn F S) :
    ContinuousOn (fun x => liftOp N (F x)) S := by
  refine continuousOn_pi.2 fun p => continuousOn_pi.2 fun q => ?_
  by_cases hpq : p.2 = q.2
  · simp only [liftOp, hpq, ↓reduceIte]
    exact continuousOn_pi.1 (continuousOn_pi.1 hF p.1) q.1
  · simp only [liftOp, hpq, ↓reduceIte]
    exact continuousOn_const

theorem continuousOn_covA {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b) {κι : Type*} [Fintype κι]
    [DecidableEq κι] (P : Matrix κι κι ℂ) :
    ContinuousOn (fun x => covA c b x P) (Ici 0) := by
  have h1 : ContinuousOn (fun x : ℝ => ((c : ℂ) + x)⁻¹) (Ici 0) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
    have hx' : (0 : ℝ) ≤ x := hx
    have : (c : ℂ) + x = ((c + x : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact_mod_cast (by linarith : (c + x : ℝ) ≠ 0)
  have h2 : ContinuousOn (fun x : ℝ => ((c : ℂ) + x + b)⁻¹) (Ici 0) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
    have hx' : (0 : ℝ) ≤ x := hx
    have : (c : ℂ) + x + b = ((c + x + b : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact_mod_cast (by linarith : (c + x + b : ℝ) ≠ 0)
  unfold covA
  exact (h1.smul continuousOn_const).add (h2.smul continuousOn_const)

end LiftCont

theorem continuousOn_xDirichlet (hak : 0 < a k) (hb : 0 ≤ aT / (L : ℝ) ^ 2)
    (α : G.Ω 1 → ℂ) :
    ContinuousOn (fun x => xDirichletOperator G a aT x ν α) (Ici 0) := by
  have := continuousOn_cutXOperator (G := G) (a := a) (aT := aT) (ν := ν) hak hb ∅ α
  simpa using this

/-! ### Continuity in `x` for the data `Dec2.XData` of the pair `(coverOf G, G)`

The sections `Family`, `DecCont`, `DecCovCont` below are their instances through `XData.toCover`. -/

section FamilyCover

variable {Cx : ℝ} (hfam : ∀ x, 0 ≤ x → Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
include hfam

theorem aux_hak_cover : 0 < a k := by
  have D := hfam 0 le_rfl
  have := D.st.ha k D.st.hk le_rfl
  linarith [this.1]

theorem aux_hb_cover : 0 ≤ aT / (L : ℝ) ^ 2 := by
  have D := hfam 0 le_rfl
  have := D.st.haT1
  positivity

theorem continuousOn_cubeHx_cover (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    ContinuousOn (fun x => cubeHx G a aT x ν α q) (Ici 0) := by
  unfold cubeHx
  exact continuousOn_cutXOperator (aux_hak_cover hfam) (aux_hb_cover hfam) _ α

theorem continuousOn_cubeGx_cover {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G) :
    ContinuousOn (fun x => cubeGx G a aT x ν α q) (Ici 0) := by
  unfold cubeGx
  refine ContinuousOn.mul (contOn_matrix_inv (continuousOn_cubeHx_cover hfam q) fun x hx => ?_)
    continuousOn_const
  have D := hfam x hx
  exact Dec2.cubeHx_isUnit D.st D.pot hx hq

theorem continuousOn_Kzx_cover (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    ContinuousOn (fun x => Kzx G a aT x ν q) (Ici 0) := by
  have h := continuousOn_xDirichlet (G := G) (a := a) (aT := aT) (ν := ν) (aux_hak_cover hfam) (aux_hb_cover hfam) (0 : G.Ω 1 → ℂ)
  unfold Kzx
  exact (continuousOn_const.mul h).sub (h.mul continuousOn_const)

theorem continuousOn_Gstarx_cover :
    ContinuousOn (fun x => Gstarx G a aT x ν α s) (Ici 0) := by
  unfold Gstarx
  refine continuousOn_finsetSum _ fun q hq => ?_
  exact (continuousOn_const (c := sProd G s q)).smul (continuousOn_const.mul (continuousOn_cubeGx_cover hfam hq))

theorem continuousOn_Kcalx_cover :
    ContinuousOn (fun x => Kcalx G a aT x ν α s) (Ici 0) := by
  unfold Kcalx
  refine continuousOn_finsetSum _ fun q hq => ?_
  exact (continuousOn_const (c := sProd G s q)).smul ((continuousOn_Kzx_cover hfam q).mul (continuousOn_cubeGx_cover hfam hq))

theorem continuousOn_Gsx_cover :
    ContinuousOn (fun x => Gsx G a aT x ν α s) (Ici 0) := by
  unfold Gsx
  refine (continuousOn_Gstarx_cover hfam).mul (contOn_matrix_inv (continuousOn_const.sub
    (continuousOn_Kcalx_cover hfam)) fun x hx => ?_)
  exact (hfam x hx).isUnit_one_sub

end FamilyCover

section DecContCover

variable {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {δ : ℝ}
variable {Cx : ℝ} (hfam : ∀ x, 0 ≤ x → Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)

include hfam

theorem continuousOn_commK_cover :
    ContinuousOn (fun x => commK (xDirichletOperator G a aT x ν α) (restrictField G φ))
      (Ici 0) := by
  have h := continuousOn_xDirichlet (G := G) (a := a) (aT := aT) (ν := ν) (aux_hak_cover hfam)
    (aux_hb_cover hfam) α
  unfold commK
  exact (contOn_matrix_mul continuousOn_const (continuousOn_liftOp h)).sub
    (contOn_matrix_mul h continuousOn_const)

theorem continuousOn_decM_cover :
    ContinuousOn (fun x => decM G a aT x ν α s φ) (Ici 0) := by
  unfold decM constraintM
  exact continuousOn_const.sub
    (contOn_matrix_mul (contOn_matrix_mul (continuousOn_commK_cover hfam)
      (continuousOn_liftOp (continuousOn_Gsx_cover hfam))) continuousOn_const)

theorem continuousOn_decN_cover :
    ContinuousOn (fun x => decN G a aT x ν α s φ) (Ici 0) := by
  unfold decN constraintN
  exact continuousOn_const.sub (contOn_matrix_mul (continuousOn_commK_cover hfam)
    (continuousOn_liftOp (continuousOn_Gsx_cover hfam)))

include hφ hδ hsm in
theorem continuousOn_decPi_cover :
    ContinuousOn (fun x => decPi G a aT x ν α s φ) (Ici 0) := by
  unfold decPi
  have hM : ContinuousOn (fun x => (decM G a aT x ν α s φ)⁻¹) (Ici 0) :=
    contOn_matrix_inv (continuousOn_decM_cover hfam) fun x hx => decM_isUnit_cover (hfam x hx) hφ hδ hsm
  exact contOn_matrix_mul (contOn_matrix_mul (contOn_matrix_mul
    (continuousOn_liftOp (continuousOn_Gsx_cover hfam)) continuousOn_const) hM) (continuousOn_decN_cover hfam)

end DecContCover

section DecCovContCover

variable {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ}
  {P : Matrix κι κι ℂ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {δ : ℝ}
variable {Cx : ℝ} (hfam : ∀ x, 0 ≤ x → Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)

include hfam hφ hδ hsm in
theorem continuousOn_decCov_cover :
    ContinuousOn (fun x => decCov G a aT x ν α s φ Q P) (Ici 0) := by
  have hA : ContinuousOn (fun x => covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) (Ici 0) :=
    continuousOn_covA (aux_hak_cover hfam) (aux_hb_cover hfam) _
  have hT : ContinuousOn (fun x => liftOp N (Gsx G a aT x ν α s) - decPi G a aT x ν α s φ)
      (Ici 0) :=
    (continuousOn_liftOp (continuousOn_Gsx_cover hfam)).sub (continuousOn_decPi_cover hfam hφ hδ hsm)
  unfold decCov
  refine hA.add ((continuousOn_const (c := (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ))).smul ?_)
  exact contOn_matrix_mul (contOn_matrix_mul (contOn_matrix_mul (contOn_matrix_mul hA
    continuousOn_const) hT) continuousOn_const) hA

end DecCovContCover

section Family

variable (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α κ s)
include hfam

theorem aux_hak : 0 < a k :=
  aux_hak_cover (fun x hx => (hfam x hx).toCover)

theorem aux_hb : 0 ≤ aT / (L : ℝ) ^ 2 :=
  aux_hb_cover (fun x hx => (hfam x hx).toCover)

theorem continuousOn_cubeHx (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    ContinuousOn (fun x => cubeHx G a aT x ν α q) (Ici 0) :=
  continuousOn_cubeHx_cover (fun x hx => (hfam x hx).toCover) q

theorem continuousOn_cubeGx {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G) :
    ContinuousOn (fun x => cubeGx G a aT x ν α q) (Ici 0) :=
  continuousOn_cubeGx_cover (fun x hx => (hfam x hx).toCover) hq

theorem continuousOn_Kzx (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    ContinuousOn (fun x => Kzx G a aT x ν q) (Ici 0) :=
  continuousOn_Kzx_cover (fun x hx => (hfam x hx).toCover) q

theorem continuousOn_Gstarx :
    ContinuousOn (fun x => Gstarx G a aT x ν α s) (Ici 0) :=
  continuousOn_Gstarx_cover (fun x hx => (hfam x hx).toCover)

theorem continuousOn_Kcalx :
    ContinuousOn (fun x => Kcalx G a aT x ν α s) (Ici 0) :=
  continuousOn_Kcalx_cover (fun x hx => (hfam x hx).toCover)

theorem continuousOn_Gsx :
    ContinuousOn (fun x => Gsx G a aT x ν α s) (Ici 0) :=
  continuousOn_Gsx_cover (fun x hx => (hfam x hx).toCover)

end Family

section DecCont

variable {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {δ : ℝ}
variable (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α κ s)
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)

include hfam

theorem continuousOn_commK :
    ContinuousOn (fun x => commK (xDirichletOperator G a aT x ν α) (restrictField G φ))
      (Ici 0) :=
  continuousOn_commK_cover (fun x hx => (hfam x hx).toCover)

theorem continuousOn_decM :
    ContinuousOn (fun x => decM G a aT x ν α s φ) (Ici 0) :=
  continuousOn_decM_cover (fun x hx => (hfam x hx).toCover)

theorem continuousOn_decN :
    ContinuousOn (fun x => decN G a aT x ν α s φ) (Ici 0) :=
  continuousOn_decN_cover (fun x hx => (hfam x hx).toCover)

include hφ hδ hsm in
theorem continuousOn_decPi :
    ContinuousOn (fun x => decPi G a aT x ν α s φ) (Ici 0) :=
  continuousOn_decPi_cover (fun x hx => (hfam x hx).toCover) hφ hδ hsm

end DecCont

section DecCovCont

variable {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ}
  {P : Matrix κι κι ℂ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {δ : ℝ}
variable (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α κ s)
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)

include hfam hφ hδ hsm in
theorem continuousOn_decCov :
    ContinuousOn (fun x => decCov G a aT x ν α s φ Q P) (Ici 0) :=
  continuousOn_decCov_cover (fun x hx => (hfam x hx).toCover) hφ hδ hsm

end DecCovCont

end Balaban.Localization
