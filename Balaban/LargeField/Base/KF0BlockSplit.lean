/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Model.PartitionFunction
public import Balaban.Model.Symmetry
public import Balaban.Lattice.Blocks

/-!
# Exact block decomposition of the hard-spin partition function (K0.2)-(K0.4)

Source: `notes/phase1/KF0.md`, section "Exact good/bad decomposition and crossing bonds", and
`notes/phase1/LF-BASE-KF0.md` (B.1).  Blocks of side `s` of the torus of side `ℓ = s * m` are
indexed by the torus `Torus d m` via `Balaban.blockMap s m`.  A block `Q` is good for the
configuration `φ` if `‖φ x - h‖ < r` at every site `x` of `Q`, and bad otherwise.

Proved here: the exact sector identity (the product expansion of `1 = χ_Q + (1 - χ_Q)` over the
blocks), the exact splitting of the frozen energy into the part on a set of bad blocks and the
part on the good region with every crossing bond, the expansion of the latter around `h`, and the
raw Peierls inequality for bad blocks.

This is the exact decomposition and the raw Peierls inequality only: no normalized activity
bound, no expansion, no chart, and nothing about Root-F is proved here.

Bond convention (that of the frozen `energy`): the bonds are the pairs `(x, μ)`, `x` a site and
`μ : Fin d`, joining `x` and `x + e_μ`, each counted once in the double sum.  For `ℓ ≥ 3` these
are the nearest-neighbour bonds, each once.  For `ℓ = 2` the bonds `(x, μ)` and
`(x + e_μ, μ)` join the same pair and are both counted, as in the frozen sum; for `ℓ = 1` the
bond joins a site to itself and has zero length.  A bond `(x, μ)` is crossing for a set `D` of
sites when exactly one of `x`, `x + e_μ` lies in `D`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory
open scoped Classical

variable {d N ℓ : ℕ} [NeZero ℓ]

/-- Spin configurations on the torus of side `ℓ`. -/
abbrev Cfg (d N ℓ : ℕ) : Type := Torus d ℓ → SpinSphere N

/-! ### T1: blocks and the site-only test -/

section Blocks

variable (s m : ℕ) [NeZero m]

/-- The block `Q` (a site of the torus of blocks) is good for `φ`: `‖φ x - h‖ < r` at all its
sites. -/
def goodBlock (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (Q : Torus d m) (φ : Cfg d N ℓ) : Prop :=
  ∀ x : Torus d ℓ, blockMap s m x = Q → ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ < r

/-- The test `χ_Q(φ) = 1{∀ x ∈ Q, ‖φ x - h‖ < r}`. -/
noncomputable def chi (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (Q : Torus d m) (φ : Cfg d N ℓ) : ℝ :=
  if goodBlock s m r h Q φ then 1 else 0

/-- The set of bad blocks of `φ`. -/
noncomputable def badSet (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (φ : Cfg d N ℓ) :
    Finset (Torus d m) :=
  Finset.univ.filter fun Q => ¬ goodBlock s m r h Q φ

/-- The sites of the blocks of `B`. -/
noncomputable def siteUnion (B : Finset (Torus d m)) : Finset (Torus d ℓ) :=
  Finset.univ.filter fun x => blockMap s m x ∈ B

/-- The sector weight `∏_{Q∈B}(1 - χ_Q) ∏_{Q∉B} χ_Q`. -/
noncomputable def sectorWeight (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (B : Finset (Torus d m))
    (φ : Cfg d N ℓ) : ℝ :=
  (∏ Q ∈ B, (1 - chi s m r h Q φ)) * ∏ Q ∈ Finset.univ \ B, chi s m r h Q φ

theorem chi_eq_zero_or_one (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (Q : Torus d m)
    (φ : Cfg d N ℓ) : chi s m r h Q φ = 0 ∨ chi s m r h Q φ = 1 := by
  unfold chi; split_ifs <;> simp

theorem chi_nonneg (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (Q : Torus d m) (φ : Cfg d N ℓ) :
    0 ≤ chi s m r h Q φ := by
  rcases chi_eq_zero_or_one (ℓ := ℓ) s m r h Q φ with h | h <;> simp [h]

theorem chi_le_one (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (Q : Torus d m) (φ : Cfg d N ℓ) :
    chi s m r h Q φ ≤ 1 := by
  rcases chi_eq_zero_or_one (ℓ := ℓ) s m r h Q φ with h | h <;> simp [h]

theorem sectorWeight_nonneg (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (B : Finset (Torus d m))
    (φ : Cfg d N ℓ) : 0 ≤ sectorWeight s m r h B φ := by
  unfold sectorWeight
  refine mul_nonneg (Finset.prod_nonneg fun Q _ => ?_) (Finset.prod_nonneg fun Q _ => ?_)
  · linarith [chi_le_one (ℓ := ℓ) s m r h Q φ]
  · exact chi_nonneg (ℓ := ℓ) s m r h Q φ

theorem sectorWeight_le_one (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (B : Finset (Torus d m))
    (φ : Cfg d N ℓ) : sectorWeight s m r h B φ ≤ 1 := by
  unfold sectorWeight
  have h1 : ∏ Q ∈ B, (1 - chi s m r h Q φ) ≤ 1 :=
    Finset.prod_le_one₀ (fun Q _ => by linarith [chi_le_one (ℓ := ℓ) s m r h Q φ])
      fun Q _ => by linarith [chi_nonneg (ℓ := ℓ) s m r h Q φ]
  have h2 : ∏ Q ∈ Finset.univ \ B, chi s m r h Q φ ≤ 1 :=
    Finset.prod_le_one₀ (fun Q _ => chi_nonneg (ℓ := ℓ) s m r h Q φ)
      fun Q _ => chi_le_one (ℓ := ℓ) s m r h Q φ
  have h3 : 0 ≤ ∏ Q ∈ B, (1 - chi s m r h Q φ) :=
    Finset.prod_nonneg fun Q _ => by linarith [chi_le_one (ℓ := ℓ) s m r h Q φ]
  nlinarith [Finset.prod_nonneg (s := Finset.univ \ B) fun Q _ => chi_nonneg (ℓ := ℓ) s m r h Q φ]

theorem measurableSet_goodBlock (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (Q : Torus d m) :
    MeasurableSet {φ : Cfg d N ℓ | goodBlock s m r h Q φ} := by
  have : {φ : Cfg d N ℓ | goodBlock s m r h Q φ} =
      ⋂ x ∈ Finset.univ.filter (fun x : Torus d ℓ => blockMap s m x = Q),
        {φ : Cfg d N ℓ | ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ < r} := by
    ext φ; simp [goodBlock]
  rw [this]
  refine Finset.measurableSet_biInter _ fun x _ => ?_
  have hm : Measurable fun φ : Cfg d N ℓ => ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ :=
    ((measurable_subtype_coe.comp (measurable_pi_apply x)).sub_const h).norm
  exact measurableSet_lt hm measurable_const

theorem measurable_chi (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (Q : Torus d m) :
    Measurable (chi (ℓ := ℓ) (N := N) s m r h Q) :=
  Measurable.ite (measurableSet_goodBlock s m r h Q) measurable_const measurable_const

theorem measurable_sectorWeight (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (B : Finset (Torus d m)) :
    Measurable (sectorWeight (ℓ := ℓ) (N := N) s m r h B) := by
  unfold sectorWeight
  refine (Finset.measurable_prod _ fun Q _ => ?_).mul (Finset.measurable_prod _ fun Q _ => ?_)
  · exact measurable_const.sub (measurable_chi s m r h Q)
  · exact measurable_chi s m r h Q

theorem mem_badSet (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (Q : Torus d m) (φ : Cfg d N ℓ) :
    Q ∈ badSet s m r h φ ↔ ¬ goodBlock s m r h Q φ := by
  simp [badSet]

/-! ### T2: the sector identity -/

/-- Pointwise: the product expansion of `∏_Q (χ_Q + (1 - χ_Q)) = 1`. -/
theorem sum_sectorWeight (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (φ : Cfg d N ℓ) :
    ∑ B : Finset (Torus d m), sectorWeight s m r h B φ = 1 := by
  have h1 := Finset.prod_add (fun Q : Torus d m => 1 - chi s m r h Q φ)
    (fun Q => chi s m r h Q φ) Finset.univ
  simp only [sub_add_cancel, Finset.prod_const_one, Finset.powerset_univ] at h1
  rw [h1]
  rfl

/-- Pointwise: exactly one sector is non-zero, namely the actual bad set. -/
theorem sectorWeight_eq_ite (r : ℝ) (h : EuclideanSpace ℝ (Fin N)) (B : Finset (Torus d m))
    (φ : Cfg d N ℓ) :
    sectorWeight s m r h B φ = if badSet s m r h φ = B then 1 else 0 := by
  unfold sectorWeight
  split_ifs with hB
  · subst hB
    have e1 : ∀ Q ∈ badSet s m r h φ, 1 - chi s m r h Q φ = 1 := by
      intro Q hQ
      have : ¬ goodBlock s m r h Q φ := (mem_badSet s m r h Q φ).1 hQ
      simp [chi, this]
    have e2 : ∀ Q ∈ Finset.univ \ badSet s m r h φ, chi s m r h Q φ = 1 := by
      intro Q hQ
      have : goodBlock s m r h Q φ := by
        by_contra hc
        simp [mem_badSet, hc] at hQ
      simp [chi, this]
    rw [Finset.prod_congr rfl e1, Finset.prod_congr rfl e2]; simp
  · have : ∃ Q, (Q ∈ B ∧ goodBlock s m r h Q φ) ∨ (Q ∉ B ∧ ¬ goodBlock s m r h Q φ) := by
      by_contra hne
      apply hB
      ext Q
      rw [mem_badSet]
      constructor
      · intro hQ
        by_contra hQB
        exact hne ⟨Q, Or.inr ⟨hQB, hQ⟩⟩
      · intro hQB hgood
        exact hne ⟨Q, Or.inl ⟨hQB, hgood⟩⟩
    obtain ⟨Q, ⟨hQ, hg⟩ | ⟨hQ, hg⟩⟩ := this
    · rw [Finset.prod_eq_zero hQ (by simp [chi, hg]), zero_mul]
    · have h0 : ∏ Q ∈ Finset.univ \ B, chi s m r h Q φ = 0 :=
        Finset.prod_eq_zero (i := Q) (by simpa using hQ) (by simp [chi, hg])
      rw [h0, mul_zero]


/-- (K0.2), lintegral form: for measurable `F ≥ 0`,
`∫ F dσ = ∑_B ∫ F ∏_{Q∈B}(1 - χ_Q) ∏_{Q∉B} χ_Q dσ`. -/
theorem lintegral_eq_sum_sector (r : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (F : Cfg d N ℓ → ENNReal) (hF : Measurable F) :
    ∫⁻ φ, F φ ∂aprioriMeasure d N ℓ =
      ∑ B : Finset (Torus d m),
        ∫⁻ φ, F φ * ENNReal.ofReal (sectorWeight s m r h B φ) ∂aprioriMeasure d N ℓ := by
  have hpt : ∀ φ, F φ = ∑ B : Finset (Torus d m), F φ * ENNReal.ofReal (sectorWeight s m r h B φ) := by
    intro φ
    rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg
      (fun B _ => sectorWeight_nonneg s m r h B φ), sum_sectorWeight, ENNReal.ofReal_one, mul_one]
  calc ∫⁻ φ, F φ ∂aprioriMeasure d N ℓ
      = ∫⁻ φ, ∑ B : Finset (Torus d m), F φ * ENNReal.ofReal (sectorWeight s m r h B φ)
          ∂aprioriMeasure d N ℓ := lintegral_congr hpt
    _ = _ := lintegral_finsetSum _ fun B _ =>
        hF.mul (ENNReal.measurable_ofReal.comp (measurable_sectorWeight s m r h B))

/-- (K0.2), Bochner form: for an integrable complex `F`. -/
theorem integral_eq_sum_sector (r : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (F : Cfg d N ℓ → ℂ) (hF : Integrable F (aprioriMeasure d N ℓ)) :
    ∫ φ, F φ ∂aprioriMeasure d N ℓ =
      ∑ B : Finset (Torus d m),
        ∫ φ, F φ * ((sectorWeight s m r h B φ : ℝ) : ℂ) ∂aprioriMeasure d N ℓ := by
  rw [← integral_finsetSum _ fun B _ => ?_]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    simp only
    rw [← Finset.mul_sum, ← Complex.ofReal_sum, sum_sectorWeight]; simp
  · refine hF.mul_bdd (c := 1) ?_ ?_
    · exact (Complex.measurable_ofReal.comp (measurable_sectorWeight s m r h B)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun φ => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sectorWeight_nonneg s m r h B φ)]
      exact sectorWeight_le_one s m r h B φ

/-- The sector integral `Z_B(g) = ∫ e^{-βH₀ + ⟨g,φ⟩} ∏_{Q∈B}(1 - χ_Q) ∏_{Q∉B} χ_Q dσ`. -/
noncomputable def kf0Sector (r : ℝ) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (B : Finset (Torus d m)) (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  sourceIntegral d N ℓ β ν h (fun φ => ((sectorWeight s m r h B φ : ℝ) : ℂ)) g

theorem integrable_sourceIntegrand_of_continuous (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    {c : Cfg d N ℓ → ℂ} (hc : Continuous c) (g : Torus d ℓ → Fin N → ℂ) :
    Integrable (sourceIntegrand d N ℓ β ν h c g) (aprioriMeasure d N ℓ) :=
  integrable_of_continuous
    ((continuous_sourceIntegrand_prod β ν h hc).comp (Continuous.prodMk_right g))

/-- (K0.2): `Z(g) = ∑_B Z_B(g)`. -/
theorem partitionFunction_eq_sum_kf0Sector (r : ℝ) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℂ) :
    partitionFunction d N ℓ β ν h g = ∑ B : Finset (Torus d m), kf0Sector s m r β ν h B g := by
  rw [partitionFunction_eq_sourceIntegral]
  have hint := integrable_sourceIntegrand_of_continuous (d := d) (N := N) (ℓ := ℓ) β ν h
    (c := fun _ => (1 : ℂ)) continuous_const g
  unfold sourceIntegral kf0Sector
  rw [integral_eq_sum_sector s m r h _ hint]
  refine Finset.sum_congr rfl fun B _ => integral_congr_ae
    (Filter.Eventually.of_forall fun φ => ?_)
  simp only [sourceIntegrand]
  ring

end Blocks

end Balaban.LargeField
