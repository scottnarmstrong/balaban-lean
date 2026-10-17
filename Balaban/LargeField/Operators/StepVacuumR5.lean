module

public import Balaban.LargeField.Operators.StepData
public import Balaban.Fluctuation.VacuumFlow

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

/-! ### The tie of the vacuum constants to the flow of `E_k`

The fields `vacE`, `vacEpp`, `vacEppp` of `StepData` are data of the step kernel; the clause
`b_vac` has content only if they are the physical constants of the creating step.  The physical
constants are `E_k` (the sequence `sf.E` of the small-field data), `E″_k = E_k + δ″_k` and
`E‴_k = E_k + δ‴_k`, where the offsets `δ″_k = -½ N L^{-d} log (c/2π) + ½ N log β_k` and
`δ‴_k = δ″_k - e(N, p₁) - ½ N log 2π` (P4 (2.1), (2.41), (2.63); `StepSetting.Epp`,
`StepSetting.Eppp`, `StepSetting.eppp_sub_Ek`) do not involve `E_k`.  `VacuumTie` states this
identification on a set `T` of localized histories (those of the creating steps).  A producer of
`StepData` from the flow proves it; the theorems below then show that a shift of the flow
`E_0 ↦ E_0 + c` changes `b_k` exactly by the compensating amount. -/

section Tie

variable [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] {R : ℕ → ℝ} {k0 N : ℕ} {geo : Geo S n R M}
  {cs : OpConsts} {κs : ℕ → LocalHistory S n M K → ℝ}

/-- **The vacuum constants of the step data are the constants of the flow** on the localized
histories `T` of the creating steps: `E_k`, `E″_k = E_k + δ″_k`, `E‴_k = E_k + δ‴_k` with
offsets `δ″`, `δ‴` independent of `E_k`. -/
structure StepData.VacuumTie (SD : StepData k0 geo cs N κs) (T : Set (LocalHistory S n M K))
    (E dpp dppp : ℕ → ℝ) : Prop where
  E_eq : ∀ k a, a ∈ T → SD.vacE k a = E k
  Epp_eq : ∀ k a, a ∈ T → SD.vacEpp k a = E k + dpp k
  Eppp_eq : ∀ k a, a ∈ T → SD.vacEppp k a = E k + dppp k

/-- Inhabitation of `VacuumTie`: step data with zero constants on `T` are tied to the zero
flow. -/
theorem StepData.vacuumTie_zero (SD : StepData k0 geo cs N κs) (T : Set (LocalHistory S n M K))
    (h0 : ∀ k a, a ∈ T → SD.vacE k a = 0 ∧ SD.vacEpp k a = 0 ∧ SD.vacEppp k a = 0) :
    SD.VacuumTie T (fun _ => 0) (fun _ => 0) (fun _ => 0) where
  E_eq k a ha := (h0 k a ha).1
  Epp_eq k a ha := by simpa using (h0 k a ha).2.1
  Eppp_eq k a ha := by simpa using (h0 k a ha).2.2

/-- **Shift of the flow.**  Under the tie, the boundary exponent in the normalization
`E_k + s` (the remainder `b⁰_k` minus the vacuum term with all three constants shifted by `s`)
is `b_k - s V`, `V = stepVacuumVolume`. -/
theorem StepData.VacuumTie.b0_sub_shift {SD : StepData k0 geo cs N κs}
    {T : Set (LocalHistory S n M K)} {E dpp dppp : ℕ → ℝ} (hT : SD.VacuumTie T E dpp dppp)
    {k : ℕ} {a : LocalHistory S n M K} (ha : a ∈ T) (s : ℝ)
    (o : OutT N R a (k + 1)) (x : NewCfg N a k) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) :
    SD.b0 k a o x hv g -
        (stepVacuumTerm a k (E k + s) (E k + dpp k + s) (E k + dppp k + s) : ℂ) =
      (SD.ker k a).b o x hv g - ((s * stepVacuumVolume a k : ℝ) : ℂ) := by
  rw [stepVacuumTerm_shift, SD.b_vac, hT.E_eq k a ha, hT.Epp_eq k a ha, hT.Eppp_eq k a ha]
  push_cast
  ring

/-- **Invariance of the combined exponent under `E_0 ↦ E_0 + c`** (cancellation with the `EZ`
factor of `removedKernel_K`).  The flow is shifted to `E_k + s`; the factor `exp EZ` of the
removed kernel changes to `exp (EZ + s V)`, `V = stepVacuumVolume` the volume of the removed
region, and the boundary exponent of the creating step to `b⁰_k` minus the vacuum term of the
shifted constants.  The weight is unchanged. -/
theorem StepData.VacuumTie.removed_weight_shift {SD : StepData k0 geo cs N κs}
    {T : Set (LocalHistory S n M K)} {E dpp dppp : ℕ → ℝ} (hT : SD.VacuumTie T E dpp dppp)
    {k : ℕ} {a : LocalHistory S n M K} (ha : a ∈ T) (s EZ : ℝ)
    (o : OutT N R a (k + 1)) (x : NewCfg N a k) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) :
    (Real.exp (EZ + s * stepVacuumVolume a k) : ℂ) *
        Complex.exp (SD.b0 k a o x hv g -
          (stepVacuumTerm a k (E k + s) (E k + dpp k + s) (E k + dppp k + s) : ℂ)) =
      (Real.exp EZ : ℂ) * Complex.exp ((SD.ker k a).b o x hv g) := by
  rw [hT.b0_sub_shift ha s o x hv g, Complex.ofReal_exp, ← Complex.exp_add,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The shift produced by the flow.**  If `E'` solves the recursion `E'_{j+1} = q E'_j + g_j`
with the same increments as the flow `E` of the tie, then at every scale `k ≤ K'` the constants
`E'_k` are those of `E_k` shifted by `s = q^k (E'_0 - E_0)` (`VacuumFlow.vacuum_sub_eq`).  The
weight of the normalization `E'` against `exp (EZ + (E'_k - E_k) V)` is unchanged. -/
theorem StepData.VacuumTie.removed_weight_flow {SD : StepData k0 geo cs N κs}
    {T : Set (LocalHistory S n M K)} {E dpp dppp E' : ℕ → ℝ}
    (hT : SD.VacuumTie T E dpp dppp)
    {k : ℕ} {a : LocalHistory S n M K} (ha : a ∈ T) (EZ : ℝ)
    (o : OutT N R a (k + 1)) (x : NewCfg N a k) (hv : EuclideanSpace ℝ (Fin N))
    (gg : GIdx S n M K N → ℂ) :
    (Real.exp (EZ + (E' k - E k) * stepVacuumVolume a k) : ℂ) *
        Complex.exp (SD.b0 k a o x hv gg -
          (stepVacuumTerm a k (E' k) (E' k + dpp k) (E' k + dppp k) : ℂ)) =
      (Real.exp EZ : ℂ) * Complex.exp ((SD.ker k a).b o x hv gg) := by
  have h := hT.removed_weight_shift ha (E' k - E k) EZ o x hv gg
  rwa [show E k + (E' k - E k) = E' k by ring,
    show E k + dpp k + (E' k - E k) = E' k + dpp k by ring,
    show E k + dppp k + (E' k - E k) = E' k + dppp k by ring] at h

/-- **The shift is `q^k (E'_0 - E_0)`** for two solutions of the flow recursion with the same
increments (`VacuumFlow.vacuum_sub_eq`), so `removed_weight_flow` holds with
`E'_k - E_k = q^k (E'_0 - E_0)`. -/
theorem StepData.VacuumTie.shift_eq_pow {E E' g : ℕ → ℝ} {q : ℝ} {K' : ℕ}
    (hE : ∀ j, j < K' → E (j + 1) = q * E j + g j)
    (hE' : ∀ j, j < K' → E' (j + 1) = q * E' j + g j) {k : ℕ} (hk : k ≤ K') :
    E' k - E k = q ^ k * (E' 0 - E 0) :=
  Balaban.Fluctuation.VacuumFlow.vacuum_sub_eq hE hE' k hk

/-- **Per-block bound in the normalization of the backward flow.**  Let `E*` be a solution with
the same increments and `E*_K = 0`; then `s = E_k - E*_k`, the exponent of the creating step in
the normalization `E*` is `b_k + s V`, and, with `|E*_k| ≤ D₀`, `|δ″_k|, |δ‴_k| ≤ D₁`,
`‖b_k + s V‖ ≤ (C_b log β_k + C_b B₀)|Z_{k+1} ∖ Z_k|_{k+1} + (D₀ + D₁) V`
(`V = stepVacuumVolume`).  With `D₀ = C' (log β_k + 1)` from
`VacuumFlow.abs_vacuum_le_of_final_eq_zero` this is the `O(log β_k + 1)` per-block bound. -/
theorem StepData.VacuumTie.b_backward_bound {SD : StepData k0 geo cs N κs}
    {T : Set (LocalHistory S n M K)} {E dpp dppp Es : ℕ → ℝ}
    (hT : SD.VacuumTie T E dpp dppp) (H : RegionHistory S n R k0 K) (hH : H.Admissible)
    (k : ℕ) (Z' : H.Comp (k + 1)) (hmem : H.localHistory M K (k + 1) Z' ∈ T)
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (hg : g ∈ l1Ball (GIdx S n M K N)) (hchi : ChiNewAt geo cs H k Z' o x)
    (D₀ D₁ : ℝ) (hEs : |Es k| ≤ D₀) (hdpp : |dpp k| ≤ D₁) (hdppp : |dppp k| ≤ D₁) :
    ‖(SD.ker k (H.localHistory M K (k + 1) Z')).b o x hv g +
      (((E k - Es k) * stepVacuumVolume (H.localHistory M K (k + 1) Z') k : ℝ) : ℂ)‖ ≤
      (cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
        volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
          z ∉ (H.localHistory M K (k + 1) Z').Z k} +
        (D₀ + D₁) * stepVacuumVolume (H.localHistory M K (k + 1) Z') k := by
  have hD₁ : 0 ≤ D₁ := (abs_nonneg _).trans hdpp
  refine SD.b_ref_bound H hH k Z' o x hv g hg hchi (E k - Es k) (D₀ + D₁) ?_ ?_ ?_
  · rw [hT.E_eq k _ hmem, show E k - Es k - E k = -Es k by ring, abs_neg]
    linarith
  · rw [hT.Epp_eq k _ hmem, show E k - Es k - (E k + dpp k) = -(Es k + dpp k) by ring, abs_neg]
    exact (abs_add_le _ _).trans (by linarith)
  · rw [hT.Eppp_eq k _ hmem, show E k - Es k - (E k + dppp k) = -(Es k + dppp k) by ring,
      abs_neg]
    exact (abs_add_le _ _).trans (by linarith)

end Tie

end Balaban.LargeField
