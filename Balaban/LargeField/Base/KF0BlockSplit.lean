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

Contents: `goodBlock`, `chi`, `badSet`, `siteUnion`, `sectorWeight` (T1); `lintegral_eq_sum_sector`,
`integral_eq_sum_sector`, `partitionFunction_eq_sum_kf0Sector` (T2); `energy_split`,
`goodEnergy_expand` (T3); `energy_ge_peierls`, `exp_neg_energy_le_peierls`, `peierls_factor_eq`,
`exp_neg_bond_le_one` (T4); `lintegral_split`, `kf0Sector_iterated` (T5, real source, lintegral
form); `measure_badSet_eq_pos`, `kf0_nonvacuity_instance` (T6).

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

/-! ### T3: the exact energy split -/

section Energy

variable (ν : ℝ) (h : EuclideanSpace ℝ (Fin N))

/-- The squared length of the bond `(x, μ)`: `‖φ(x + e_μ) - φ(x)‖²`. -/
noncomputable def bondSq (φ : Cfg d N ℓ) (x : Torus d ℓ) (μ : Fin d) : ℝ :=
  ‖(φ (x + Pi.single μ 1) : EuclideanSpace ℝ (Fin N)) - φ x‖ ^ 2

/-- `H_B`: the mass terms on the sites of `D` and the bonds with both endpoints in `D`. -/
noncomputable def blockEnergy (D : Finset (Torus d ℓ)) (φ : Cfg d N ℓ) : ℝ :=
  (1 / 2) * ∑ x : Torus d ℓ, ∑ μ : Fin d,
      (if x ∈ D ∧ x + Pi.single μ 1 ∈ D then bondSq φ x μ else 0)
    + (ν / 2) * ∑ x : Torus d ℓ, (if x ∈ D then ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 else 0)

/-- `H_G`: the mass terms on the complement of `D`, the bonds inside the complement and every
bond crossing between `D` and its complement (every bond not having both endpoints in `D`). -/
noncomputable def goodEnergy (D : Finset (Torus d ℓ)) (φ : Cfg d N ℓ) : ℝ :=
  (1 / 2) * ∑ x : Torus d ℓ, ∑ μ : Fin d,
      (if x ∈ D ∧ x + Pi.single μ 1 ∈ D then 0 else bondSq φ x μ)
    + (ν / 2) * ∑ x : Torus d ℓ, (if x ∈ D then 0 else ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2)

/-- (K0.2), the energy: `H₀ = H_B + H_G` exactly. -/
theorem energy_split (D : Finset (Torus d ℓ)) (φ : Cfg d N ℓ) :
    energy d N ℓ ν h φ = blockEnergy ν h D φ + goodEnergy ν h D φ := by
  unfold energy blockEnergy goodEnergy
  have h1 : ∑ x : Torus d ℓ, ∑ μ : Fin d, ‖(φ (x + Pi.single μ 1) : EuclideanSpace ℝ (Fin N)) - φ x‖ ^ 2 =
      ∑ x : Torus d ℓ, ∑ μ : Fin d,
        ((if x ∈ D ∧ x + Pi.single μ 1 ∈ D then bondSq φ x μ else 0)
          + (if x ∈ D ∧ x + Pi.single μ 1 ∈ D then 0 else bondSq φ x μ)) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
    split_ifs <;> simp [bondSq]
  have h2 : ∑ x : Torus d ℓ, ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 =
      ∑ x : Torus d ℓ, ((if x ∈ D then ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 else 0)
        + (if x ∈ D then 0 else ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [h1, h2]
  simp only [Finset.sum_add_distrib]
  ring

/-- The endpoint of the bond `(x, μ)` in the complement of `D` (the bond being crossing). -/
def goodEnd (D : Finset (Torus d ℓ)) (x : Torus d ℓ) (μ : Fin d) : Torus d ℓ :=
  if x ∈ D then x + Pi.single μ 1 else x

/-- The endpoint of the bond `(x, μ)` in `D` (the bond being crossing). -/
def blockEnd (D : Finset (Torus d ℓ)) (x : Torus d ℓ) (μ : Fin d) : Torus d ℓ :=
  if x ∈ D then x else x + Pi.single μ 1

/-- The bond `(x, μ)` is crossing for `D`: exactly one endpoint lies in `D`. -/
def IsCrossing (D : Finset (Torus d ℓ)) (x : Torus d ℓ) (μ : Fin d) : Prop :=
  ¬ (x ∈ D ↔ x + Pi.single μ 1 ∈ D)

theorem crossing_expand (u v : EuclideanSpace ℝ (Fin N)) :
    ‖u - v‖ ^ 2 = ‖u - h‖ ^ 2 + 2 * inner ℝ (h - v) (u - h) + ‖h - v‖ ^ 2 := by
  have : u - v = (u - h) + (h - v) := by abel
  rw [this, norm_add_sq_real, real_inner_comm]

/-- (K0.3): the expansion of `H_G` around `h`, with `w = φ - h` on the complement of `D` and the
exterior spins `φ(y)`, `y ∈ D`: the five sums are the internal bonds, the crossing bonds
`½ |w_x|²`, the mass, the linear boundary term `(h - q_y)·w_x` and the constant
`½ |h - q_y|²`. -/
theorem goodEnergy_expand (D : Finset (Torus d ℓ)) (φ : Cfg d N ℓ) :
    goodEnergy ν h D φ =
      (1 / 2) * ∑ x : Torus d ℓ, ∑ μ : Fin d,
        (if x ∉ D ∧ x + Pi.single μ 1 ∉ D then
          ‖((φ (x + Pi.single μ 1) : EuclideanSpace ℝ (Fin N)) - h) - ((φ x : EuclideanSpace ℝ (Fin N)) - h)‖ ^ 2
         else 0)
      + (1 / 2) * ∑ x : Torus d ℓ, ∑ μ : Fin d,
        (if IsCrossing D x μ then ‖(φ (goodEnd D x μ) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 else 0)
      + (ν / 2) * ∑ x : Torus d ℓ,
        (if x ∈ D then 0 else ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2)
      + ∑ x : Torus d ℓ, ∑ μ : Fin d,
        (if IsCrossing D x μ then
          inner ℝ (h - (φ (blockEnd D x μ) : EuclideanSpace ℝ (Fin N)))
            ((φ (goodEnd D x μ) : EuclideanSpace ℝ (Fin N)) - h) else 0)
      + (1 / 2) * ∑ x : Torus d ℓ, ∑ μ : Fin d,
        (if IsCrossing D x μ then
          ‖h - (φ (blockEnd D x μ) : EuclideanSpace ℝ (Fin N))‖ ^ 2 else 0) := by
  unfold goodEnergy
  have key : ∀ (x : Torus d ℓ) (μ : Fin d),
      (if x ∈ D ∧ x + Pi.single μ 1 ∈ D then 0 else bondSq φ x μ) =
        (if x ∉ D ∧ x + Pi.single μ 1 ∉ D then
          ‖((φ (x + Pi.single μ 1) : EuclideanSpace ℝ (Fin N)) - h) - ((φ x : EuclideanSpace ℝ (Fin N)) - h)‖ ^ 2
         else 0)
        + (if IsCrossing D x μ then ‖(φ (goodEnd D x μ) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 else 0)
        + 2 * (if IsCrossing D x μ then
          inner ℝ (h - (φ (blockEnd D x μ) : EuclideanSpace ℝ (Fin N)))
            ((φ (goodEnd D x μ) : EuclideanSpace ℝ (Fin N)) - h) else 0)
        + (if IsCrossing D x μ then
          ‖h - (φ (blockEnd D x μ) : EuclideanSpace ℝ (Fin N))‖ ^ 2 else 0) := by
    intro x μ
    by_cases hx : x ∈ D <;> by_cases hy : x + Pi.single μ 1 ∈ D <;>
      simp [IsCrossing, goodEnd, blockEnd, hx, hy, bondSq]
    all_goals first | exact crossing_expand h _ _ | (rw [norm_sub_rev]; exact crossing_expand h _ _)
  simp only [key, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end Energy

/-! ### T4: the raw Peierls charge -/

section Peierls

variable (s m : ℕ) [NeZero m]

theorem mass_sum_ge_card (r : ℝ) (hr : 0 ≤ r) (h : EuclideanSpace ℝ (Fin N))
    (φ : Cfg d N ℓ) (B : Finset (Torus d m)) (hB : B ⊆ badSet s m r h φ) :
    (B.card : ℝ) * r ^ 2 ≤ ∑ x : Torus d ℓ, ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 := by
  have hx : ∀ Q ∈ B, ∃ x : Torus d ℓ, blockMap s m x = Q ∧
      r ≤ ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ := by
    intro Q hQ
    have := (mem_badSet s m r h Q φ).1 (hB hQ)
    simp only [goodBlock, not_forall, not_lt] at this
    obtain ⟨x, hx1, hx2⟩ := this
    exact ⟨x, hx1, hx2⟩
  choose! xs hxs using hx
  have hinj : Set.InjOn xs (B : Set (Torus d m)) := by
    intro Q hQ Q' hQ' he
    rw [← (hxs Q hQ).1, ← (hxs Q' hQ').1, he]
  calc (B.card : ℝ) * r ^ 2 = ∑ Q ∈ B, r ^ 2 := by simp
    _ ≤ ∑ Q ∈ B, ‖(φ (xs Q) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 :=
        Finset.sum_le_sum fun Q hQ => pow_le_pow_left₀ hr (hxs Q hQ).2 2
    _ = ∑ x ∈ B.image xs, ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 :=
        (Finset.sum_image (f := fun x : Torus d ℓ => ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2) hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)

/-- (K0.4), energy form: on the event that every block of `B` is bad,
`H₀(φ) ≥ (ν r² / 2) · #B`. -/
theorem energy_ge_peierls (r : ℝ) (hr : 0 ≤ r) (ν : ℝ) (hν : 0 ≤ ν)
    (h : EuclideanSpace ℝ (Fin N)) (φ : Cfg d N ℓ) (B : Finset (Torus d m))
    (hB : B ⊆ badSet s m r h φ) :
    ν * r ^ 2 / 2 * B.card ≤ energy d N ℓ ν h φ := by
  have h1 := mass_sum_ge_card s m r hr h φ B hB
  have h2 : 0 ≤ (1 / 2 : ℝ) * ∑ x : Torus d ℓ, ∑ μ : Fin d,
      ‖(φ (x + Pi.single μ 1) : EuclideanSpace ℝ (Fin N)) - φ x‖ ^ 2 :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  unfold energy
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ ν / 2)]

/-- (K0.4): `e^{-β H₀} ≤ e^{-β H₀ / 2} · exp(-β ν r² #B / 4)` on the event that every block of `B`
is bad (`β ≥ 0`). -/
theorem exp_neg_energy_le_peierls (r : ℝ) (hr : 0 ≤ r) (β ν : ℝ) (hβ : 0 ≤ β) (hν : 0 ≤ ν)
    (h : EuclideanSpace ℝ (Fin N)) (φ : Cfg d N ℓ) (B : Finset (Torus d m))
    (hB : B ⊆ badSet s m r h φ) :
    Real.exp (-(β * energy d N ℓ ν h φ)) ≤
      Real.exp (-(β * energy d N ℓ ν h φ / 2)) * Real.exp (-(β * ν * r ^ 2 * B.card / 4)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_left (energy_ge_peierls s m r hr ν hν h φ B hB) hβ
  nlinarith

/-- The specialization `r = r_β / √ν`, `r_β = A log(β a) / √β`: the factor is
`exp(-A² log²(β a) #B / 4)`. -/
theorem peierls_factor_eq (A a β ν : ℝ) (hβ : 0 < β) (hν : 0 < ν) (n : ℕ) :
    Real.exp (-(β * ν * (A * Real.log (β * a) / Real.sqrt β / Real.sqrt ν) ^ 2 * n / 4)) =
      Real.exp (-(A ^ 2 * Real.log (β * a) ^ 2 * n / 4)) := by
  congr 2
  have h1 : Real.sqrt β ^ 2 = β := Real.sq_sqrt hβ.le
  have h2 : Real.sqrt ν ^ 2 = ν := Real.sq_sqrt hν.le
  have h3 : Real.sqrt β ≠ 0 := (Real.sqrt_pos.2 hβ).ne'
  have h4 : Real.sqrt ν ≠ 0 := (Real.sqrt_pos.2 hν).ne'
  field_simp
  rw [h1, h2]
  ring

/-- Each crossing bond factor of the exact decomposition is at most `1`
(`β ≥ 0`, real spins); nothing is discarded in (K0.2). -/
theorem exp_neg_bond_le_one (β : ℝ) (hβ : 0 ≤ β) (u v : EuclideanSpace ℝ (Fin N)) :
    Real.exp (-(β * ‖u - v‖ ^ 2 / 2)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have : 0 ≤ β * ‖u - v‖ ^ 2 / 2 := by positivity
  linarith

end Peierls

/-! ### T5: the iterated (Fubini) form -/

section Fubini

variable (D : Finset (Torus d ℓ))

/-- The configuration with bad spins `q` on `D` and good spins `p` on the complement. -/
def glue (q : ↥D → SpinSphere N) (p : {x : Torus d ℓ // x ∉ D} → SpinSphere N) : Cfg d N ℓ :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Torus d ℓ => SpinSphere N) (· ∈ D)).symm (q, p)

theorem glue_of_mem (q : ↥D → SpinSphere N) (p : {x : Torus d ℓ // x ∉ D} → SpinSphere N)
    (x : Torus d ℓ) (hx : x ∈ D) : glue D q p x = q ⟨x, hx⟩ := by
  simp [glue, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hx]

theorem glue_of_not_mem (q : ↥D → SpinSphere N) (p : {x : Torus d ℓ // x ∉ D} → SpinSphere N)
    (x : Torus d ℓ) (hx : x ∉ D) : glue D q p x = p ⟨x, hx⟩ := by
  simp [glue, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hx]

/-- The product of sphere measures over the sites of `D`. -/
noncomputable abbrev sigmaIn : Measure (↥D → SpinSphere N) :=
  Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere

/-- The product of sphere measures over the sites outside `D`. -/
noncomputable abbrev sigmaOut : Measure ({x : Torus d ℓ // x ∉ D} → SpinSphere N) :=
  Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere

/-- Fubini for the product sphere measure over `D ⊔ Dᶜ`. -/
theorem lintegral_split (f : Cfg d N ℓ → ENNReal) (hf : Measurable f) :
    ∫⁻ φ, f φ ∂aprioriMeasure d N ℓ =
      ∫⁻ q, ∫⁻ p, f (glue D q p) ∂sigmaOut D ∂sigmaIn D := by
  have hmp := measurePreserving_piEquivPiSubtypeProd
    (α := fun _ : Torus d ℓ => SpinSphere N)
    (fun _ : Torus d ℓ => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) (· ∈ D)
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Torus d ℓ => SpinSphere N) (· ∈ D)
  have hg : Measurable fun z => f (e.symm z) := hf.comp e.symm.measurable
  have h1 : ∫⁻ a, f (e.symm (e a)) ∂aprioriMeasure d N ℓ =
      ∫⁻ z, f (e.symm z) ∂((sigmaIn D).prod (sigmaOut D)) := by
    convert hmp.lintegral_comp hg
    unfold aprioriMeasure
    congr
  have h0 : ∫⁻ φ, f φ ∂aprioriMeasure d N ℓ = ∫⁻ a, f (e.symm (e a)) ∂aprioriMeasure d N ℓ := by
    simp
  rw [h0, h1, lintegral_prod _ hg.aemeasurable]
  rfl


/-- The real source term `⟨g, φ⟩ = ∑_x ∑_i g_i(x) φ_i(x)`. -/
noncomputable def realSource (g : Torus d ℓ → Fin N → ℝ) (φ : Cfg d N ℓ) : ℝ :=
  ∑ x : Torus d ℓ, ∑ i : Fin N, g x i * ((φ x : EuclideanSpace ℝ (Fin N)) i)

/-- The source term of the bad spins `q`. -/
noncomputable def sourceIn (g : Torus d ℓ → Fin N → ℝ) (q : ↥D → SpinSphere N) : ℝ :=
  ∑ x : ↥D, ∑ i : Fin N, g x i * ((q x : EuclideanSpace ℝ (Fin N)) i)

/-- The source term of the good spins `p`. -/
noncomputable def sourceOut (g : Torus d ℓ → Fin N → ℝ) (p : {x : Torus d ℓ // x ∉ D} → SpinSphere N) :
    ℝ :=
  ∑ x : {x : Torus d ℓ // x ∉ D}, ∑ i : Fin N, g x i * ((p x : EuclideanSpace ℝ (Fin N)) i)

theorem realSource_glue (g : Torus d ℓ → Fin N → ℝ) (q : ↥D → SpinSphere N)
    (p : {x : Torus d ℓ // x ∉ D} → SpinSphere N) :
    realSource g (glue D q p) = sourceIn D g q + sourceOut D g p := by
  unfold realSource sourceIn sourceOut
  refine (Fintype.sum_subtype_add_sum_subtype (fun x : Torus d ℓ => x ∈ D)
    (fun x => ∑ i : Fin N, g x i * ((glue D q p x : EuclideanSpace ℝ (Fin N)) i))).symm.trans ?_
  congr 1
  · refine Finset.sum_congr (by congr!) fun x _ => Finset.sum_congr rfl fun i _ => ?_
    rw [glue_of_mem D q p x.1 x.2]
  · refine Finset.sum_congr (by congr!) fun x _ => Finset.sum_congr rfl fun i _ => ?_
    rw [glue_of_not_mem D q p x.1 x.2]

theorem sum_ite_mem_eq (F : Torus d ℓ → ℝ) :
    ∑ x : Torus d ℓ, (if x ∈ D then F x else 0) = ∑ x : ↥D, F x := by
  rw [Finset.sum_coe_sort D F, Finset.sum_ite_mem, Finset.univ_inter]

variable (ν : ℝ) (h : EuclideanSpace ℝ (Fin N))

/-- `H_B(q)`, as a function of the bad spins only: the mass on `D` and the bonds with both
endpoints in `D`. -/
noncomputable def blockEnergyIn (q : ↥D → SpinSphere N) : ℝ :=
  (1 / 2) * ∑ x : ↥D, ∑ μ : Fin d,
      (if hy : x.1 + Pi.single μ 1 ∈ D then
        ‖(q ⟨x.1 + Pi.single μ 1, hy⟩ : EuclideanSpace ℝ (Fin N)) - q x‖ ^ 2 else 0)
    + (ν / 2) * ∑ x : ↥D, ‖(q x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2

theorem blockEnergy_glue (q : ↥D → SpinSphere N) (p : {x : Torus d ℓ // x ∉ D} → SpinSphere N) :
    blockEnergy ν h D (glue D q p) = blockEnergyIn D ν h q := by
  unfold blockEnergy blockEnergyIn
  congr 2
  · have : ∀ x : Torus d ℓ, ∑ μ : Fin d,
        (if x ∈ D ∧ x + Pi.single μ 1 ∈ D then bondSq (glue D q p) x μ else 0) =
        if x ∈ D then ∑ μ : Fin d, (if x + Pi.single μ 1 ∈ D then bondSq (glue D q p) x μ else 0)
        else 0 := by
      intro x
      by_cases hx : x ∈ D <;> simp [hx]
    simp_rw [this]
    refine (sum_ite_mem_eq D (fun x => ∑ μ : Fin d,
      (if x + Pi.single μ 1 ∈ D then bondSq (glue D q p) x μ else 0))).trans ?_
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
    by_cases hy : x.1 + Pi.single μ 1 ∈ D
    · simp [hy, bondSq, glue_of_mem D q p _ hy, glue_of_mem D q p x.1 x.2]
    · simp [hy]
  · refine (sum_ite_mem_eq D (fun x => ‖(glue D q p x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2)).trans ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [glue_of_mem D q p x.1 x.2]


variable (s m : ℕ) [NeZero m] (r : ℝ)

/-- The test `χ_Q` read on the bad spins `q` (used for blocks `Q ∈ B`). -/
noncomputable def chiIn (Q : Torus d m) (q : ↥D → SpinSphere N) : ℝ :=
  if ∀ x : ↥D, blockMap s m x.1 = Q → ‖(q x : EuclideanSpace ℝ (Fin N)) - h‖ < r then 1 else 0

/-- The test `χ_Q` read on the good spins `p` (used for blocks `Q ∉ B`). -/
noncomputable def chiOut (Q : Torus d m) (p : {x : Torus d ℓ // x ∉ D} → SpinSphere N) : ℝ :=
  if ∀ x : {x : Torus d ℓ // x ∉ D}, blockMap s m x.1 = Q →
    ‖(p x : EuclideanSpace ℝ (Fin N)) - h‖ < r then 1 else 0

/-- `∏_{Q∈B}(1 - χ_Q(q))`. -/
noncomputable def badWeight (B : Finset (Torus d m)) (q : ↥D → SpinSphere N) : ℝ :=
  ∏ Q ∈ B, (1 - chiIn D h s m r Q q)

/-- `∏_{Q∉B} χ_Q(p)`. -/
noncomputable def goodWeight (B : Finset (Torus d m)) (p : {x : Torus d ℓ // x ∉ D} → SpinSphere N) :
    ℝ :=
  ∏ Q ∈ Finset.univ \ B, chiOut D h s m r Q p

theorem mem_siteUnion (B : Finset (Torus d m)) (x : Torus d ℓ) :
    x ∈ siteUnion (ℓ := ℓ) s m B ↔ blockMap s m x ∈ B := by
  simp [siteUnion]

theorem chi_glue_of_mem (B : Finset (Torus d m)) (q : ↥(siteUnion (ℓ := ℓ) s m B) → SpinSphere N)
    (p : {x : Torus d ℓ // x ∉ siteUnion (ℓ := ℓ) s m B} → SpinSphere N) (Q : Torus d m)
    (hQ : Q ∈ B) :
    chi s m r h Q (glue _ q p) = chiIn _ h s m r Q q := by
  have hiff : goodBlock s m r h Q (glue _ q p) ↔
      ∀ x : ↥(siteUnion (ℓ := ℓ) s m B), blockMap s m x.1 = Q →
        ‖(q x : EuclideanSpace ℝ (Fin N)) - h‖ < r := by
    constructor
    · intro H x hx
      have := H x.1 hx
      rwa [glue_of_mem _ q p x.1 x.2] at this
    · intro H x hx
      have hxD : x ∈ siteUnion (ℓ := ℓ) s m B := (mem_siteUnion s m B x).2 (hx ▸ hQ)
      rw [glue_of_mem _ q p x hxD]
      exact H ⟨x, hxD⟩ hx
  unfold chi chiIn
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; tauto)

theorem chi_glue_of_not_mem (B : Finset (Torus d m))
    (q : ↥(siteUnion (ℓ := ℓ) s m B) → SpinSphere N)
    (p : {x : Torus d ℓ // x ∉ siteUnion (ℓ := ℓ) s m B} → SpinSphere N) (Q : Torus d m)
    (hQ : Q ∉ B) :
    chi s m r h Q (glue _ q p) = chiOut _ h s m r Q p := by
  have hiff : goodBlock s m r h Q (glue _ q p) ↔
      ∀ x : {x : Torus d ℓ // x ∉ siteUnion (ℓ := ℓ) s m B}, blockMap s m x.1 = Q →
        ‖(p x : EuclideanSpace ℝ (Fin N)) - h‖ < r := by
    constructor
    · intro H x hx
      have := H x.1 hx
      rwa [glue_of_not_mem _ q p x.1 x.2] at this
    · intro H x hx
      have hxD : x ∉ siteUnion (ℓ := ℓ) s m B := fun hh => hQ (hx ▸ (mem_siteUnion s m B x).1 hh)
      rw [glue_of_not_mem _ q p x hxD]
      exact H ⟨x, hxD⟩ hx
  unfold chi chiOut
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; tauto)

/-- The sector weight factorizes into a bad part (a function of `q`) and a good part (of `p`). -/
theorem sectorWeight_glue (B : Finset (Torus d m))
    (q : ↥(siteUnion (ℓ := ℓ) s m B) → SpinSphere N)
    (p : {x : Torus d ℓ // x ∉ siteUnion (ℓ := ℓ) s m B} → SpinSphere N) :
    sectorWeight s m r h B (glue _ q p) = badWeight _ h s m r B q * goodWeight _ h s m r B p := by
  unfold sectorWeight badWeight goodWeight
  congr 1
  · exact Finset.prod_congr rfl fun Q hQ => by rw [chi_glue_of_mem h s m r B q p Q hQ]
  · exact Finset.prod_congr rfl fun Q hQ => by
      rw [chi_glue_of_not_mem h s m r B q p Q (Finset.mem_sdiff.1 hQ).2]


theorem chiIn_nonneg_le (Q : Torus d m) (q : ↥D → SpinSphere N) :
    0 ≤ chiIn D h s m r Q q ∧ chiIn D h s m r Q q ≤ 1 := by
  unfold chiIn; split_ifs <;> norm_num

theorem chiOut_nonneg_le (Q : Torus d m) (p : {x : Torus d ℓ // x ∉ D} → SpinSphere N) :
    0 ≤ chiOut D h s m r Q p ∧ chiOut D h s m r Q p ≤ 1 := by
  unfold chiOut; split_ifs <;> norm_num

theorem badWeight_nonneg (B : Finset (Torus d m)) (q : ↥D → SpinSphere N) :
    0 ≤ badWeight D h s m r B q :=
  Finset.prod_nonneg fun Q _ => by linarith [(chiIn_nonneg_le D h s m r Q q).2]

theorem goodWeight_nonneg (B : Finset (Torus d m)) (p : {x : Torus d ℓ // x ∉ D} → SpinSphere N) :
    0 ≤ goodWeight D h s m r B p :=
  Finset.prod_nonneg fun Q _ => (chiOut_nonneg_le D h s m r Q p).1

theorem measurable_realSource (g : Torus d ℓ → Fin N → ℝ) :
    Measurable (realSource (d := d) (N := N) (ℓ := ℓ) g) := by
  refine Continuous.measurable ?_
  unfold realSource
  exact continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_spin_coord x i)

/-- (K0.2), iterated form (lintegral, real source): the sector integral equals
`∫ e^{-βH_B(q) + ⟨g_D,q⟩} ∏_{Q∈B}(1 - χ_Q(q)) · I_G(q, g) dσ^D(q)`, with
`I_G(q,g) = ∫ e^{-βH_G(φ_G | q) + ⟨g_G,φ_G⟩} ∏_{Q∉B} χ_Q(φ_G) dσ^G`, where `H_G(φ_G | q)` is the
good energy of the glued configuration (the mass and internal bonds on `G` and every crossing
bond). -/
theorem kf0Sector_iterated (β ν : ℝ) (g : Torus d ℓ → Fin N → ℝ) (B : Finset (Torus d m)) :
    ∫⁻ φ, ENNReal.ofReal (Real.exp (-(β * energy d N ℓ ν h φ) + realSource g φ) *
        sectorWeight s m r h B φ) ∂aprioriMeasure d N ℓ =
      ∫⁻ q, ENNReal.ofReal (Real.exp (-(β * blockEnergyIn (siteUnion (ℓ := ℓ) s m B) ν h q)
            + sourceIn (siteUnion (ℓ := ℓ) s m B) g q) *
          badWeight (siteUnion (ℓ := ℓ) s m B) h s m r B q) *
        ∫⁻ p, ENNReal.ofReal (Real.exp (-(β * goodEnergy ν h (siteUnion (ℓ := ℓ) s m B)
              (glue (siteUnion (ℓ := ℓ) s m B) q p))
            + sourceOut (siteUnion (ℓ := ℓ) s m B) g p) *
          goodWeight (siteUnion (ℓ := ℓ) s m B) h s m r B p) ∂sigmaOut (siteUnion (ℓ := ℓ) s m B)
        ∂sigmaIn (siteUnion (ℓ := ℓ) s m B) := by
  have hE : Measurable fun φ : Cfg d N ℓ => energy d N ℓ ν h φ :=
    (continuous_energy (d := d) (N := N) (ℓ := ℓ) ν h).measurable
  have hmeas : Measurable fun φ : Cfg d N ℓ => ENNReal.ofReal (Real.exp (-(β * energy d N ℓ ν h φ)
      + realSource g φ) * sectorWeight s m r h B φ) :=
    ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp (((measurable_const.mul hE).neg).add
        (measurable_realSource g))).mul (measurable_sectorWeight s m r h B))
  rw [lintegral_split _ _ hmeas]
  refine lintegral_congr fun q => ?_
  have key : ∀ p, ENNReal.ofReal (Real.exp (-(β * energy d N ℓ ν h (glue (siteUnion s m B) q p))
        + realSource g (glue (siteUnion s m B) q p)) *
        sectorWeight s m r h B (glue (siteUnion s m B) q p)) =
      ENNReal.ofReal (Real.exp (-(β * blockEnergyIn (siteUnion (ℓ := ℓ) s m B) ν h q)
            + sourceIn (siteUnion (ℓ := ℓ) s m B) g q) *
          badWeight (siteUnion (ℓ := ℓ) s m B) h s m r B q) *
        ENNReal.ofReal (Real.exp (-(β * goodEnergy ν h (siteUnion (ℓ := ℓ) s m B)
              (glue (siteUnion (ℓ := ℓ) s m B) q p))
            + sourceOut (siteUnion (ℓ := ℓ) s m B) g p) *
          goodWeight (siteUnion (ℓ := ℓ) s m B) h s m r B p) := by
    intro p
    rw [← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le
      (badWeight_nonneg _ h s m r B q))]
    congr 1
    rw [energy_split ν h (siteUnion s m B), blockEnergy_glue, realSource_glue,
      sectorWeight_glue h s m r B q p]
    have : -(β * (blockEnergyIn (siteUnion (ℓ := ℓ) s m B) ν h q +
          goodEnergy ν h (siteUnion s m B) (glue (siteUnion s m B) q p))) +
        (sourceIn (siteUnion s m B) g q + sourceOut (siteUnion s m B) g p) =
        (-(β * blockEnergyIn (siteUnion (ℓ := ℓ) s m B) ν h q) + sourceIn (siteUnion s m B) g q) +
        (-(β * goodEnergy ν h (siteUnion s m B) (glue (siteUnion s m B) q p)) +
          sourceOut (siteUnion s m B) g p) := by ring
    rw [this, Real.exp_add]
    ring
  simp_rw [key]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Fubini

/-! ### T6: non-vacuity -/

section NonVacuity

variable (s m : ℕ) [NeZero m] (r : ℝ) (h : EuclideanSpace ℝ (Fin N))

theorem measurableSet_badSet_eq (B : Finset (Torus d m)) :
    MeasurableSet {φ : Cfg d N ℓ | badSet s m r h φ = B} := by
  have : {φ : Cfg d N ℓ | badSet s m r h φ = B} = sectorWeight s m r h B ⁻¹' {1} := by
    ext φ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, sectorWeight_eq_ite]
    split_ifs with hB <;> simp [hB]
  rw [this]
  exact measurable_sectorWeight s m r h B (measurableSet_singleton 1)

/-- T2 at `F ≡ 1`: the total mass is the sum over the sets of bad blocks of the measure of the
event "bad set `= B`". -/
theorem apriori_univ_eq_sum_badSet :
    aprioriMeasure d N ℓ Set.univ =
      ∑ B : Finset (Torus d m), aprioriMeasure d N ℓ {φ | badSet s m r h φ = B} := by
  have := lintegral_eq_sum_sector (d := d) (N := N) (ℓ := ℓ) s m r h (fun _ => 1) measurable_const
  simp only [one_mul, lintegral_const, one_mul] at this
  rw [this]
  refine Finset.sum_congr rfl fun B _ => ?_
  have h1 : ∀ φ : Cfg d N ℓ, ENNReal.ofReal (sectorWeight s m r h B φ) =
      Set.indicator {φ | badSet s m r h φ = B} (fun _ => (1 : ENNReal)) φ := by
    intro φ
    rw [sectorWeight_eq_ite]
    by_cases hB : badSet s m r h φ = B <;> simp [hB, Set.indicator]
  simp_rw [h1]
  rw [lintegral_indicator (measurableSet_badSet_eq s m r h B)]
  simp

instance : (aprioriMeasure d N ℓ).IsOpenPosMeasure := by
  unfold aprioriMeasure
  infer_instance

theorem exists_site (hℓ : ℓ = s * m) (Q : Torus d m) : ∃ x : Torus d ℓ, blockMap s m x = Q := by
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · exact absurd (by simpa [h0] using hℓ) (NeZero.ne ℓ)
    · exact h0
  have hc := card_blockFibre (d := d) (ℓ := ℓ) hℓ Q
  have : (blockFibre s m Q : Finset (Torus d ℓ)).Nonempty := by
    rw [← Finset.card_pos, hc]; positivity
  obtain ⟨x, hx⟩ := this
  exact ⟨x, mem_blockFibre.1 hx⟩

/-- Every sector is non-null: for `0 < r ≤ 1`, `‖h‖ = 1`, `s ∣ ℓ`, the event "bad set `= B`"
contains an open non-empty set (spins within `r` of `-h` on the sites of `B`, within `r` of `h`
elsewhere). -/
theorem measure_badSet_eq_pos (hℓ : ℓ = s * m) (hr0 : 0 < r) (hr1 : r ≤ 1) (hh : ‖h‖ = 1)
    (B : Finset (Torus d m)) :
    0 < aprioriMeasure d N ℓ {φ : Cfg d N ℓ | badSet s m r h φ = B} := by
  set D := siteUnion (ℓ := ℓ) s m B
  let c : Torus d ℓ → EuclideanSpace ℝ (Fin N) := fun x => if x ∈ D then -h else h
  have hc : ∀ x, ‖c x‖ = 1 := by
    intro x; simp only [c]; split_ifs <;> simp [hh]
  let U : Set (Cfg d N ℓ) := {φ | ∀ x, ‖(φ x : EuclideanSpace ℝ (Fin N)) - c x‖ < r}
  have hU : IsOpen U := by
    have : U = ⋂ x, {φ : Cfg d N ℓ | ‖(φ x : EuclideanSpace ℝ (Fin N)) - c x‖ < r} := by
      ext φ; simp [U]
    rw [this]
    refine isOpen_iInter_of_finite fun x => isOpen_lt ?_ continuous_const
    exact ((continuous_subtype_val.comp (continuous_apply x)).sub continuous_const).norm
  have hne : U.Nonempty := by
    refine ⟨fun x => ⟨c x, by simp [hc x]⟩, fun x => ?_⟩
    simpa using hr0
  have hsub : U ⊆ {φ : Cfg d N ℓ | badSet s m r h φ = B} := by
    intro φ hφ
    ext Q
    rw [mem_badSet]
    constructor
    · intro hQ
      by_contra hQB
      apply hQ
      intro x hx
      have hxD : x ∉ D := fun hh' => hQB (hx ▸ (mem_siteUnion s m B x).1 hh')
      have := hφ x
      simpa [c, hxD] using this
    · intro hQB hgood
      obtain ⟨x, hx⟩ := exists_site (d := d) (ℓ := ℓ) s m hℓ Q
      have hxD : x ∈ D := (mem_siteUnion s m B x).2 (hx ▸ hQB)
      have h1 := hφ x
      have h2 := hgood x hx
      simp only [c, hxD, ite_true] at h1
      have h3 : ‖(-h) - h‖ ≤ ‖(-h) - (φ x : EuclideanSpace ℝ (Fin N))‖ +
          ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h4 : ‖(-h) - h‖ = 2 := by
        have : (-h) - h = (-2 : ℝ) • h := by module
        rw [this, norm_smul, hh]; norm_num
      have h5 : ‖(-h) - (φ x : EuclideanSpace ℝ (Fin N))‖ = ‖(φ x : EuclideanSpace ℝ (Fin N)) - -h‖ :=
        norm_sub_rev _ _
      have : (φ x : EuclideanSpace ℝ (Fin N)) - -h = (φ x : EuclideanSpace ℝ (Fin N)) + h := by abel
      linarith
  exact lt_of_lt_of_le (hU.measure_pos _ hne) (measure_mono hsub)

/-- Each sector integral (real source, lintegral form) is positive. -/
theorem lintegral_sector_pos (hℓ : ℓ = s * m) (hr0 : 0 < r) (hr1 : r ≤ 1) (hh : ‖h‖ = 1)
    (β ν : ℝ) (g : Torus d ℓ → Fin N → ℝ) (B : Finset (Torus d m)) :
    0 < ∫⁻ φ, ENNReal.ofReal (Real.exp (-(β * energy d N ℓ ν h φ) + realSource g φ) *
        sectorWeight s m r h B φ) ∂aprioriMeasure d N ℓ := by
  have hE : Measurable fun φ : Cfg d N ℓ => energy d N ℓ ν h φ :=
    (continuous_energy (d := d) (N := N) (ℓ := ℓ) ν h).measurable
  have hmeas : Measurable fun φ : Cfg d N ℓ => ENNReal.ofReal (Real.exp (-(β * energy d N ℓ ν h φ)
      + realSource g φ) * sectorWeight s m r h B φ) :=
    ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp (((measurable_const.mul hE).neg).add
        (measurable_realSource g))).mul (measurable_sectorWeight s m r h B))
  rw [lintegral_pos_iff_support hmeas]
  refine lt_of_lt_of_le (measure_badSet_eq_pos s m r h hℓ hr0 hr1 hh B) (measure_mono ?_)
  intro φ hφ
  simp only [Set.mem_ofPred_eq] at hφ
  simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  rw [sectorWeight_eq_ite]
  simp only [hφ, ↓reduceIte, mul_one]
  exact Real.exp_pos _

end NonVacuity

/-- The explicit instance: `d = 3`, `N = 3` (Heisenberg), torus side `ℓ = 4`, blocks of side
`s = 2` (so `m = 2`, eight blocks), `r = 1/4`, `h = e₀`.  Every sector has positive measure
and every sector integral (`β = ν = 1`, zero source) is positive; in particular the sector
`B = ∅` (all blocks good) and the sector of any non-empty set of bad blocks are not null. -/
theorem kf0_nonvacuity_instance :
    (∀ B : Finset (Torus 3 2),
      0 < aprioriMeasure 3 3 4 {φ : Cfg 3 3 4 | badSet 2 2 (1 / 4 : ℝ)
        (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) φ = B}) ∧
    (∀ B : Finset (Torus 3 2),
      0 < ∫⁻ φ, ENNReal.ofReal (Real.exp (-(1 * energy 3 3 4 1
          (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) φ) + realSource (0 : Torus 3 4 → Fin 3 → ℝ) φ) *
        sectorWeight 2 2 (1 / 4 : ℝ) (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) B φ)
          ∂aprioriMeasure 3 3 4) := by
  have hh : ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ))‖ = 1 := by simp
  exact ⟨fun B => measure_badSet_eq_pos (ℓ := 4) 2 2 _ _ rfl (by norm_num) (by norm_num) hh B,
    fun B => lintegral_sector_pos (ℓ := 4) 2 2 _ _ rfl (by norm_num) (by norm_num) hh _ _ _ B⟩

end Balaban.LargeField
