module

public import Balaban.LargeField.Operators.StepData

/-!
# Vacuum bookkeeping for the creating step (R5)

P6 (3.2), P5 (3.18), and LFR (S0) assign the three vacuum constants to the
step which creates a large-field component.  The equations below isolate the
normalization shift and its cancellation with the `EZ` factor of the removed
kernel (P7 (3.7)).  The geometric identification of the sum of the three
regions with the removed volume is kept as an explicit hypothesis where used.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban RegionHistory

variable {S : Setting} {n : ℕ → ℕ} {M K : ℕ}

/-- The three volumes occurring in the creating-step vacuum contribution. -/
noncomputable def stepVacuumVolume (a : LocalHistory S n M K) (k : ℕ) : ℝ :=
  volScale S k ((a.Z (k + 1) \ a.Z k) \ a.Omega k) +
    volScale S k (a.Omega k \ a.OmegaDD k) +
      volScale S k (a.OmegaDD k ∩ a.Z (k + 1))

/-- A common shift of the three creating-step constants changes the boundary exponent by the
shift times exactly the sum of the three region volumes. -/
theorem stepVacuumTerm_shift (a : LocalHistory S n M K) (k : ℕ)
    (Ek Epp Eppp s : ℝ) :
    stepVacuumTerm a k (Ek + s) (Epp + s) (Eppp + s) =
      stepVacuumTerm a k Ek Epp Eppp + s * stepVacuumVolume a k := by
  unfold stepVacuumTerm stepVacuumVolume
  ring

/-- Replacing all three constants by one reference value changes the vacuum term by the
three coefficient differences. -/
theorem stepVacuumTerm_ref_sub (a : LocalHistory S n M K) (k : ℕ)
    (Ek Epp Eppp Eref : ℝ) :
    Eref * stepVacuumVolume a k - stepVacuumTerm a k Ek Epp Eppp =
      stepVacuumTerm a k (Eref - Ek) (Eref - Epp) (Eref - Eppp) := by
  unfold stepVacuumTerm stepVacuumVolume
  ring

/-- The three-volume coefficient estimate, with no assumption about the absolute size of
`Ek`, `Epp`, or `Eppp`. -/
theorem norm_stepVacuumTerm_ref_sub_le (a : LocalHistory S n M K) (k : ℕ)
    (Ek Epp Eppp Eref D : ℝ) (hE : |Eref - Ek| ≤ D)
    (hEpp : |Eref - Epp| ≤ D) (hEppp : |Eref - Eppp| ≤ D) :
    ‖(stepVacuumTerm a k (Eref - Ek) (Eref - Epp) (Eref - Eppp) : ℂ)‖ ≤
      D * stepVacuumVolume a k := by
  let v1 := volScale S k ((a.Z (k + 1) \ a.Z k) \ a.Omega k)
  let v2 := volScale S k (a.Omega k \ a.OmegaDD k)
  let v3 := volScale S k (a.OmegaDD k ∩ a.Z (k + 1))
  have hv1 : 0 ≤ v1 := by unfold v1 volScale; positivity
  have hv2 : 0 ≤ v2 := by unfold v2 volScale; positivity
  have hv3 : 0 ≤ v3 := by unfold v3 volScale; positivity
  have h1 := mul_le_mul_of_nonneg_right hE hv1
  have h2 := mul_le_mul_of_nonneg_right hEpp hv2
  have h3 := mul_le_mul_of_nonneg_right hEppp hv3
  simp only [Complex.norm_real, Real.norm_eq_abs]
  change |(Eref - Ek) * v1 + (Eref - Epp) * v2 + (Eref - Eppp) * v3| ≤
    D * (v1 + v2 + v3)
  have ha := abs_add_le ((Eref - Ek) * v1 + (Eref - Epp) * v2) ((Eref - Eppp) * v3)
  have hb := abs_add_le ((Eref - Ek) * v1) ((Eref - Epp) * v2)
  rw [abs_mul, abs_of_nonneg hv3] at ha
  rw [abs_mul, abs_mul, abs_of_nonneg hv1, abs_of_nonneg hv2] at hb
  linarith

section StepData

variable [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L]

/-- The R5 field removes precisely the vacuum contribution from the actual step exponent. -/
theorem StepData.b_add_vac {R : ℕ → ℝ} {k0 N : ℕ} {geo : Geo S n R M}
    {cs : OpConsts} {κs : ℕ → LocalHistory S n M K → ℝ}
    (SD : StepData k0 geo cs N κs) (k : ℕ) (a : LocalHistory S n M K)
    (o : OutT N R a (k + 1)) (x : NewCfg N a k)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) :
    (SD.ker k a).b o x hv g +
      (stepVacuumTerm a k (SD.vacE k a) (SD.vacEpp k a) (SD.vacEppp k a) : ℂ) =
      SD.b0 k a o x hv g := by
  rw [SD.b_vac]
  ring

/-- The exact normalized per-block bound.  Taking `D = C (log β_k + 1)` and using the
geometric identity `stepVacuumVolume = |Z_{k+1} ∖ Z_k|_k` gives the source's
`O(log β_k + 1)` estimate.  The three difference estimates are explicit premises. -/
theorem StepData.b_ref_bound {R : ℕ → ℝ} {k0 N : ℕ} {geo : Geo S n R M}
    {cs : OpConsts} {κs : ℕ → LocalHistory S n M K → ℝ}
    (SD : StepData k0 geo cs N κs) (H : RegionHistory S n R k0 K)
    (hH : H.Admissible) (k : ℕ) (Z' : H.Comp (k + 1))
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (hg : g ∈ l1Ball (GIdx S n M K N)) (hchi : ChiNewAt geo cs H k Z' o x)
    (Eref D : ℝ)
    (hE : |Eref - SD.vacE k (H.localHistory M K (k + 1) Z')| ≤ D)
    (hEpp : |Eref - SD.vacEpp k (H.localHistory M K (k + 1) Z')| ≤ D)
    (hEppp : |Eref - SD.vacEppp k (H.localHistory M K (k + 1) Z')| ≤ D) :
    ‖(SD.ker k (H.localHistory M K (k + 1) Z')).b o x hv g +
      ((Eref * stepVacuumVolume (H.localHistory M K (k + 1) Z') k : ℝ) : ℂ)‖ ≤
      (cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
        volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
          z ∉ (H.localHistory M K (k + 1) Z').Z k} +
        D * stepVacuumVolume (H.localHistory M K (k + 1) Z') k := by
  let a := H.localHistory M K (k + 1) Z'
  have hid : (SD.ker k a).b o x hv g + ((Eref * stepVacuumVolume a k : ℝ) : ℂ) =
      SD.b0 k a o x hv g +
        (stepVacuumTerm a k (Eref - SD.vacE k a)
          (Eref - SD.vacEpp k a) (Eref - SD.vacEppp k a) : ℂ) := by
    rw [SD.b_vac]
    calc
      _ = SD.b0 k a o x hv g +
          ((Eref * stepVacuumVolume a k -
            stepVacuumTerm a k (SD.vacE k a) (SD.vacEpp k a) (SD.vacEppp k a) : ℝ) : ℂ) := by
              push_cast
              ring
      _ = _ := by rw [stepVacuumTerm_ref_sub]
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add
    (SD.b0_bound H hH k Z' o x hv g hg hchi)
    (norm_stepVacuumTerm_ref_sub_le a k _ _ _ Eref D hE hEpp hEppp))

end StepData

/-- The exponent carried by `removedKernel_K` is `EZ`; after a common shift of the
creating-step constants by `s`, its shift is `s` times the removed volume.  When that volume
equals `stepVacuumVolume`, the sum of the kernel exponent and the boundary exponent is
unchanged.  This is the scalar cancellation used by the removed-kernel weight. -/
theorem stepVacuum_removed_exponent_shift (a : LocalHistory S n M K) (k : ℕ)
    (Ek Epp Eppp s EZ : ℝ) (b0 : ℂ) :
    ((EZ + s * stepVacuumVolume a k : ℝ) : ℂ) +
        (b0 - (stepVacuumTerm a k (Ek + s) (Epp + s) (Eppp + s) : ℂ)) =
      (EZ : ℂ) + (b0 - (stepVacuumTerm a k Ek Epp Eppp : ℂ)) := by
  rw [stepVacuumTerm_shift]
  push_cast
  ring

/-- Exponentiating the previous identity gives the invariance of the combined removed-kernel
weight.  `removedKernel_K` contributes `exp EZ`, and `LFKernel.w` contributes `exp b`. -/
theorem stepVacuum_removed_weight_shift (a : LocalHistory S n M K) (k : ℕ)
    (Ek Epp Eppp s EZ : ℝ) (b0 : ℂ) :
    (Real.exp (EZ + s * stepVacuumVolume a k) : ℂ) *
        Complex.exp (b0 - (stepVacuumTerm a k (Ek + s) (Epp + s) (Eppp + s) : ℂ)) =
      (Real.exp EZ : ℂ) * Complex.exp
        (b0 - (stepVacuumTerm a k Ek Epp Eppp : ℂ)) := by
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  exact stepVacuum_removed_exponent_shift a k Ek Epp Eppp s EZ b0

end Balaban.LargeField
