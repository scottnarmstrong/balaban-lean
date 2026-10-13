/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0GoodChart
public import Balaban.LargeField.Base.KF0BoundarySquare
import Mathlib.Tactic.Linarith

/-!
# The completed square on the good region and the shifted form of the sector integral

Fixed bad set `D`, good sites `G = Dᶜ`, bad spins `q`.  The inner good-spin integral of a sector
(`lintegral_goodInner_gaussian`) is a Gaussian integral with the linear boundary term still in the
exponent.  This file moves that term into the Gaussian.

* `goodJ`: the tangent-valued boundary source `J(x) = ∑ (crossing bonds at x) P(h - q_y)`,
  `P` the projection onto `h^⊥`; `goodBdryLin_eq_pairing`: `goodBdryLin = √β ∑_x ⟨J(x), v_x⟩`.
* `goodQuad_completed_square`: `½⟨v,K_G v⟩ + √β⟨J,v⟩ = ½⟨v - m, K_G (v - m)⟩ - (β/2)⟨J,K_G⁻¹J⟩`,
  `m = goodMean = -√β K_G⁻¹ J`.
* `goodReducedConst = goodBdryConst - (β/2)⟨J, K_G⁻¹ J⟩`.
* `lintegral_good_gaussian_shift`: the shifted Gaussian identity.
* `lintegral_goodInner_shifted`: the inner integral of the sector in shifted form; every indicator,
  Jacobian, normal and source term stays inside, and the crossing square is counted once.
* `goodReducedConst_ge`: the Schur bound gives
  `goodReducedConst ≥ (β/2)(1 - θ) S_tan + (β/2) S_norm ≥ 0`.

Everything is for a FIXED bad set.  The linked expansion and the one-scale theorem are NOT proved
here, nor the determinant ratio against the full torus or the sum over sectors with one reference
measure.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Matrix Balaban Balaban.KW

namespace Balaban.LargeField

open SphereChart

open scoped Classical

section Source

variable {d N ℓ : ℕ} [NeZero ℓ] (D : Finset (Torus d ℓ)) {h : EuclideanSpace ℝ (Fin N)}

/-- The tangent part `P(h - q_y)` of `h - q_y`, `P` the projection onto `h^⊥` (`q_y` the bad spin at
`y ∈ D`; the background `h` off `D`). -/
noncomputable def goodTan (hh : ‖h‖ = 1) (q : ↥D → SpinSphere N) (y : Torus d ℓ) : perp h :=
  perpK h hh (h - badExt D h q y)

/-- **The tangent boundary source** `J(x) = ∑_{crossing bonds at x} P(h - q_y)`, `y ∈ D` the other
endpoint.  The bonds at the good site `x` are the `2d` bonds `{x, x ± e_μ}`; a bond to `D` is counted
once (so a neighbour `y` reached by `a` bonds is counted `a` times, as the adjacency multiplicity
`kwAdj x y`, `a = 2` on a torus of side `2`). -/
noncomputable def goodJ (hh : ‖h‖ = 1) (q : ↥D → SpinSphere N) (x : Good D) : perp h :=
  ∑ μ : Fin d, ((if x.1 + Pi.single μ 1 ∈ D then goodTan D hh q (x.1 + Pi.single μ 1) else 0)
    + (if x.1 - Pi.single μ 1 ∈ D then goodTan D hh q (x.1 - Pi.single μ 1) else 0))

/-- The pairing `⟨a, b⟩ = ∑_{x∈G} ⟨a_x, b_x⟩` of tangent fields on the good sites. -/
noncomputable def goodPair (a b : Good D → perp h) : ℝ := ∑ x, inner ℝ (a x) (b x)

/-- Reindexing of the sum over crossing bonds `(x, μ)` of a function of (bad end, good end) as a sum
over the good end. -/
theorem sum_crossing_reindex {M : Type*} [AddCommMonoid M] (μ : Fin d)
    (T : Torus d ℓ → Torus d ℓ → M) (hT : ∀ y z, z ∈ D → T y z = 0) :
    ∑ x : Torus d ℓ, (if IsCrossing D x μ then T (blockEnd D x μ) (goodEnd D x μ) else 0) =
    ∑ z : Torus d ℓ, ((if z - Pi.single μ 1 ∈ D then T (z - Pi.single μ 1) z else 0)
      + (if z + Pi.single μ 1 ∈ D then T (z + Pi.single μ 1) z else 0)) := by
  have hpt : ∀ x : Torus d ℓ, (if IsCrossing D x μ then T (blockEnd D x μ) (goodEnd D x μ) else 0) =
      (if x ∈ D then T x (x + Pi.single μ 1) else 0)
        + (if x + Pi.single μ 1 ∈ D then T (x + Pi.single μ 1) x else 0) := by
    intro x
    by_cases hx : x ∈ D <;> by_cases hy : x + Pi.single μ 1 ∈ D
    · simp [IsCrossing, hx, hy, hT x _ hy, hT _ x hx]
    · simp [IsCrossing, goodEnd, blockEnd, hx, hy]
    · simp [IsCrossing, goodEnd, blockEnd, hx, hy]
    · simp [IsCrossing, hx, hy]
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  have := Equiv.sum_comp (Equiv.addRight (Pi.single μ (1 : ZMod ℓ) : Torus d ℓ))
    (fun z => if z - Pi.single μ 1 ∈ D then T (z - Pi.single μ 1) z else 0)
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at this
  exact this

theorem inner_tan_eq (hh : ‖h‖ = 1) (c : EuclideanSpace ℝ (Fin N)) (u : perp h) :
    inner ℝ ((perpK h hh c : perp h) : EuclideanSpace ℝ (Fin N)) (u : EuclideanSpace ℝ (Fin N)) =
      inner ℝ c (u : EuclideanSpace ℝ (Fin N)) := by
  show inner ℝ (c - inner ℝ h c • h) (u : EuclideanSpace ℝ (Fin N)) = _
  rw [inner_sub_left, inner_smul_left, real_inner_comm, inner_eq_of_mem_perp h u.2]
  simp

/-- **T1.**  The boundary linear term is the pairing of `v` with the tangent source `goodJ`:
`goodBdryLin = √β ∑_{x∈G} ⟨J(x), v_x⟩`. -/
theorem goodBdryLin_eq_pairing (hh : ‖h‖ = 1) (β : ℝ) (q : ↥D → SpinSphere N) (v : Good D → perp h) :
    goodBdryLin D β q v = Real.sqrt β * goodPair D (goodJ D hh q) v := by
  unfold goodBdryLin
  congr 1
  rw [Finset.sum_comm]
  have h1 : ∀ μ : Fin d, ∑ x : Torus d ℓ, (if IsCrossing D x μ then
      inner ℝ (h - badExt D h q (blockEnd D x μ))
        (goodExt D v (goodEnd D x μ) : EuclideanSpace ℝ (Fin N)) else 0) =
      ∑ z : Torus d ℓ, ((if z - Pi.single μ 1 ∈ D then
          inner ℝ (goodTan D hh q (z - Pi.single μ 1) : EuclideanSpace ℝ (Fin N))
            (goodExt D v z : EuclideanSpace ℝ (Fin N)) else 0)
        + (if z + Pi.single μ 1 ∈ D then
          inner ℝ (goodTan D hh q (z + Pi.single μ 1) : EuclideanSpace ℝ (Fin N))
            (goodExt D v z : EuclideanSpace ℝ (Fin N)) else 0)) := by
    intro μ
    rw [sum_crossing_reindex D μ (fun y z => inner ℝ (h - badExt D h q y)
      (goodExt D v z : EuclideanSpace ℝ (Fin N)))
      (fun y z hz => by simp [goodExt_of_mem D v hz])]
    simp only [goodTan, inner_tan_eq hh]
  simp_rw [h1]
  rw [Finset.sum_comm]
  rw [sum_good_eq D]
  · unfold goodPair goodJ
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [goodExt_of_not_mem D v z.2, Submodule.coe_inner]
    rw [Submodule.coe_sum, sum_inner]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Submodule.coe_add, inner_add_left, add_comm]
    congr 1 <;> split_ifs <;> simp
  · intro z hz
    simp [goodExt_of_mem D v hz]

end Source

/-! ### T2: the vector-valued completed square -/

section Shift

variable {d N ℓ : ℕ} [NeZero ℓ] (D : Finset (Torus d ℓ)) {h : EuclideanSpace ℝ (Fin N)}

/-- The `i`-th Euclidean coordinate of a tangent field on the good sites. -/
def goodCoord (v : Good D → perp h) (i : Fin N) : Good D → ℝ :=
  fun x => ((v x : perp h) : EuclideanSpace ℝ (Fin N)) i

theorem goodPair_eq_sum (a b : Good D → perp h) :
    goodPair D a b = ∑ i : Fin N, goodCoord D a i ⬝ᵥ goodCoord D b i := by
  unfold goodPair goodCoord dotProduct
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Submodule.coe_inner, PiLp.inner_apply, mul_comm]

theorem goodQuad_eq_sum (ν : ℝ) (v : Good D → perp h) :
    goodQuad D ν v = ∑ i : Fin N, goodCoord D v i ⬝ᵥ kwOpSub d ℓ ν D *ᵥ goodCoord D v i := rfl

theorem goodCoord_matAct (S : Matrix (Good D) (Good D) ℝ) (ψ : Good D → perp h) (i : Fin N) :
    goodCoord D (matAct S ψ) i = S *ᵥ goodCoord D ψ i :=
  funext fun x => coord_matAct_good D S ψ x i

theorem kwOpSub_symm {ν : ℝ} (hν : 0 < ν) : (kwOpSub d ℓ ν D)ᵀ = kwOpSub d ℓ ν D := by
  have := (kwOpSub_posDef ν D hν).isHermitian
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact this

theorem kwOpSub_det_isUnit {ν : ℝ} (hν : 0 < ν) : IsUnit (kwOpSub d ℓ ν D).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (kwOpSub_posDef ν D hν).isUnit

/-- The mean `m = -√β K_G⁻¹ J` of the shifted Gaussian (in the `√β`-scaled variable `v`). -/
noncomputable def goodMean (β ν : ℝ) (J : Good D → perp h) : Good D → perp h :=
  (-Real.sqrt β) • matAct (kwOpSub d ℓ ν D)⁻¹ J

/-- The reduced boundary constant `goodBdryConst - (β/2) ⟨J, K_G⁻¹ J⟩`. -/
noncomputable def goodReducedConst (hh : ‖h‖ = 1) (β ν : ℝ) (q : ↥D → SpinSphere N) : ℝ :=
  goodBdryConst D h β q - β / 2 *
    goodPair D (goodJ D hh q) (matAct (kwOpSub d ℓ ν D)⁻¹ (goodJ D hh q))

/-- **T2.**  `½⟨v,K_G v⟩ + √β⟨J,v⟩ = ½⟨v - m, K_G (v - m)⟩ - (β/2)⟨J, K_G⁻¹ J⟩`, `m = -√β K_G⁻¹ J`. -/
theorem goodQuad_completed_square {ν β : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β) (J v : Good D → perp h) :
    1 / 2 * goodQuad D ν v + Real.sqrt β * goodPair D J v =
      1 / 2 * goodQuad D ν (v - goodMean D β ν J)
        - β / 2 * goodPair D J (matAct (kwOpSub d ℓ ν D)⁻¹ J) := by
  have hc : ∀ i, goodCoord D (v - goodMean D β ν J) i =
      goodCoord D v i + Real.sqrt β • (kwOpSub d ℓ ν D)⁻¹ *ᵥ goodCoord D J i := by
    intro i
    funext x
    have := congrFun (goodCoord_matAct D (kwOpSub d ℓ ν D)⁻¹ J i) x
    simp only [goodCoord, goodMean, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
      Submodule.coe_sub, Submodule.coe_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at this ⊢
    rw [this]; ring
  rw [goodQuad_eq_sum, goodQuad_eq_sum, goodPair_eq_sum, goodPair_eq_sum]
  simp only [hc, goodCoord_matAct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := completed_square (kwOpSub_symm D hν) (kwOpSub_det_isUnit D hν) (goodCoord D v i)
    (goodCoord D J i) hβ 0
  linarith

end Shift

/-! ### T3: the shifted Gaussian identity -/

section Gauss

variable {d N ℓ : ℕ} [NeZero ℓ] (D : Finset (Torus d ℓ)) {h : EuclideanSpace ℝ (Fin N)}

/-- **T3 (shifted Gaussian identity).**  For every `F ≥ 0` (no measurability is needed),
`∫ F(v) exp(-½⟨v,K_G v⟩ - √β⟨J,v⟩) dv = exp((β/2)⟨J,K_G⁻¹J⟩) · N_G · ∫ F(m + C_G ψ) dγ_G(ψ)`. -/
theorem lintegral_good_gaussian_shift (hh : ‖h‖ = 1) {ν β : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β)
    (J : Good D → perp h) (F : (Good D → perp h) → ENNReal) :
    ∫⁻ v, F v * ENNReal.ofReal (Real.exp (-(1 / 2) * goodQuad D ν v
        - Real.sqrt β * goodPair D J v)) ∂(goodVol D h) =
      ENNReal.ofReal (Real.exp (β / 2 * goodPair D J (matAct (kwOpSub d ℓ ν D)⁻¹ J))) *
        (ENNReal.ofReal (kwGaussNorm d ℓ N ν D) *
          ∫⁻ ψ, F (goodMean D β ν J + matAct (kwSqrt ν D) ψ) ∂(goodGaussian D h)) := by
  set c := β / 2 * goodPair D J (matAct (kwOpSub d ℓ ν D)⁻¹ J) with hc
  set m := goodMean D β ν J with hm
  have h1 : ∀ v, F v * ENNReal.ofReal (Real.exp (-(1 / 2) * goodQuad D ν v
        - Real.sqrt β * goodPair D J v)) =
      ENNReal.ofReal (Real.exp c) * ((fun u => F (u + m) *
        ENNReal.ofReal (Real.exp (-(1 / 2) * goodQuad D ν u))) (v - m)) := by
    intro v
    have e := goodQuad_completed_square D hν hβ J v
    have e2 : -(1 / 2) * goodQuad D ν v - Real.sqrt β * goodPair D J v =
        c + -(1 / 2) * goodQuad D ν (v - m) := by rw [hc]; linarith
    simp only [sub_add_cancel]
    rw [e2, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [lintegral_sub_right_eq_self (μ := goodVol D h)
    (fun u => F (u + m) * ENNReal.ofReal (Real.exp (-(1 / 2) * goodQuad D ν u))) m]
  rw [lintegral_good_gaussian_change D hh hν (fun u => F (u + m))]
  simp_rw [add_comm _ m]

/-- **T3 in Gaussian form.**  `∫ F(C_G ψ) exp(-√β⟨J, C_G ψ⟩) dγ_G = exp((β/2)⟨J,K_G⁻¹J⟩)
∫ F(m + C_G ψ) dγ_G`. -/
theorem lintegral_gaussian_shift (hh : ‖h‖ = 1) {ν β : ℝ} (hν : 0 < ν) (hβ : 0 ≤ β)
    (J : Good D → perp h) (F : (Good D → perp h) → ENNReal) :
    ∫⁻ ψ, F (matAct (kwSqrt ν D) ψ) *
        ENNReal.ofReal (Real.exp (-(Real.sqrt β * goodPair D J (matAct (kwSqrt ν D) ψ))))
        ∂(goodGaussian D h) =
      ENNReal.ofReal (Real.exp (β / 2 * goodPair D J (matAct (kwOpSub d ℓ ν D)⁻¹ J))) *
        ∫⁻ ψ, F (goodMean D β ν J + matAct (kwSqrt ν D) ψ) ∂(goodGaussian D h) := by
  have h1 := lintegral_good_gaussian_change D hh hν (fun v => F v *
    ENNReal.ofReal (Real.exp (-(Real.sqrt β * goodPair D J v))))
  have h2 := lintegral_good_gaussian_shift D hh hν hβ J F
  have h3 : ∀ v, F v * ENNReal.ofReal (Real.exp (-(1 / 2) * goodQuad D ν v
        - Real.sqrt β * goodPair D J v)) =
      F v * ENNReal.ofReal (Real.exp (-(Real.sqrt β * goodPair D J v))) *
        ENNReal.ofReal (Real.exp (-(1 / 2) * goodQuad D ν v)) := by
    intro v
    rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 3; ring
  simp_rw [h3] at h2
  rw [h1] at h2
  have hN : ENNReal.ofReal (kwGaussNorm d ℓ N ν D) ≠ 0 := by
    simpa using kwGaussNorm_pos D hν
  rw [mul_left_comm] at h2
  exact (ENNReal.mul_right_inj hN ENNReal.ofReal_ne_top).1 h2

end Gauss

/-! ### The sector integral in shifted form -/

section Sector

variable {d N ℓ : ℕ} [NeZero ℓ] (D : Finset (Torus d ℓ)) {h : EuclideanSpace ℝ (Fin N)}

/-- The exponent that remains after the Gaussian, the linear boundary term and the boundary
constant have been taken out of `goodChartExponent`: `-(boundary normal + remainder) + sources`. -/
noncomputable def goodShiftedExponent (β ν : ℝ) (g : Torus d ℓ → Fin N → ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (q : ↥D → SpinSphere N) (v : Good D → perp h) : ℝ :=
  -(goodBdryNormal D β q v + goodRemainder D β ν v)
    + (goodSourceConst D g h + (Real.sqrt β)⁻¹ * goodSourceTangent D g v
      + (Real.sqrt β)⁻¹ * goodSourceNormal D g β v)

theorem goodChartExponent_split (hh : ‖h‖ = 1) (β ν : ℝ) (g : Torus d ℓ → Fin N → ℝ)
    (q : ↥D → SpinSphere N) (v : Good D → perp h) :
    goodChartExponent D β ν g h q v =
      -(Real.sqrt β * goodPair D (goodJ D hh q) v) - goodBdryConst D h β q
        + goodShiftedExponent D β ν g h q v := by
  unfold goodChartExponent goodShiftedExponent
  rw [goodBdryLin_eq_pairing D hh]
  ring

/-- **The inner integral of a sector in shifted form** (fixed bad set `D = siteUnion B`).  The
inner good-spin integral of `kf0Sector_iterated` is
`((√β)⁻¹)^{|G|(N-1)} · N_G · exp(-goodReducedConst) · ∫ dγ_G(ψ) J_β · goodWeight · exp(shifted
exponent)` at `v = m + C_G ψ`, `m = -√β K_G⁻¹ J`.  The Jacobian, the cutoffs, the normal and
remainder terms and the sources stay inside, and the crossing square is counted once, in
`goodReducedConst`. -/
theorem lintegral_goodInner_shifted {m : ℕ} [NeZero m] (s : ℕ) (r : ℝ) (B : Finset (Torus d m))
    (hD : D = siteUnion (ℓ := ℓ) s m B) {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) (hh : ‖h‖ = 1)
    (hr : r ≤ 1) (g : Torus d ℓ → Fin N → ℝ) (q : ↥D → SpinSphere N) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (-(β * goodEnergy ν h D
          (glue D q p))
        + sourceOut D g p) *
        goodWeight D h s m r B p) ∂sigmaOut D =
      ENNReal.ofReal (((Real.sqrt β)⁻¹) ^ (Fintype.card (Good D) * (N - 1))) *
        ENNReal.ofReal (kwGaussNorm d ℓ N ν D) *
        ENNReal.ofReal (Real.exp (-goodReducedConst D hh β ν q)) *
        ∫⁻ ψ, ENNReal.ofReal (chartJac β (fun x =>
              (((goodMean D β ν (goodJ D hh q) + matAct (kwSqrt ν D) ψ) x : perp h) :
                EuclideanSpace ℝ (Fin N)))) *
            ENNReal.ofReal (goodWeight D h s m r B
              (chartCfgOn h hh ((Real.sqrt β)⁻¹ •
                (goodMean D β ν (goodJ D hh q) + matAct (kwSqrt ν D) ψ)))) *
            ENNReal.ofReal (Real.exp (goodShiftedExponent D β ν g h q
              (goodMean D β ν (goodJ D hh q) + matAct (kwSqrt ν D) ψ)))
          ∂(goodGaussian D h) := by
  rw [lintegral_goodInner_gaussian D s r B hD hβ hν hh hr g q]
  set J := goodJ D hh q with hJ
  set F : (Good D → perp h) → ENNReal := fun v =>
    ENNReal.ofReal (chartJac β (fun x => ((v x : perp h) : EuclideanSpace ℝ (Fin N)))) *
      ENNReal.ofReal (goodWeight D h s m r B (chartCfgOn h hh ((Real.sqrt β)⁻¹ • v))) *
      ENNReal.ofReal (Real.exp (goodShiftedExponent D β ν g h q v)) with hF
  have h1 : ∀ ψ : Good D → perp h,
      ENNReal.ofReal (chartJac β (fun x =>
              ((matAct (kwSqrt ν D) ψ x : perp h) : EuclideanSpace ℝ (Fin N)))) *
            ENNReal.ofReal (goodWeight D h s m r B
              (chartCfgOn h hh ((Real.sqrt β)⁻¹ • matAct (kwSqrt ν D) ψ))) *
            ENNReal.ofReal (Real.exp (goodChartExponent D β ν g h q (matAct (kwSqrt ν D) ψ))) =
      ENNReal.ofReal (Real.exp (-goodBdryConst D h β q)) *
        (F (matAct (kwSqrt ν D) ψ) * ENNReal.ofReal (Real.exp
          (-(Real.sqrt β * goodPair D J (matAct (kwSqrt ν D) ψ))))) := by
    intro ψ
    rw [goodChartExponent_split D hh]
    have e : -(Real.sqrt β * goodPair D J (matAct (kwSqrt ν D) ψ)) - goodBdryConst D h β q
        + goodShiftedExponent D β ν g h q (matAct (kwSqrt ν D) ψ) =
        (goodShiftedExponent D β ν g h q (matAct (kwSqrt ν D) ψ)
          + -(Real.sqrt β * goodPair D J (matAct (kwSqrt ν D) ψ))) + -goodBdryConst D h β q := by
      ring
    rw [e, Real.exp_add, Real.exp_add,
      ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le),
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    simp only [hF]
    ring
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_gaussian_shift D hh hν hβ.le J F]
  have e3 : ENNReal.ofReal (Real.exp (-goodReducedConst D hh β ν q)) =
      ENNReal.ofReal (Real.exp (-goodBdryConst D h β q)) *
        ENNReal.ofReal (Real.exp (β / 2 * goodPair D J (matAct (kwOpSub d ℓ ν D)⁻¹ J))) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    unfold goodReducedConst
    congr 2
    ring
  rw [e3]
  ring

end Sector

end Balaban.LargeField
