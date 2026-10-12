module

public import Balaban.LargeField.Operators.CompBound
public import Balaban.LargeField.Budget.Exponents

/-!
# The bound (1.26) for the localized operators (Part II, Lemma II.5.13 along the lineage, (D5))

`locOp_pkgBound`: by induction along the lineage, every localized operator `𝕋_k(Z, 𝔞)` satisfies
the bound (1.26) (`PkgBound`) with the exponent `κ_k(Z, 𝔞)` of Definition II.5.11, provided the
kept operators (S3) satisfy it with their exponents and the step data satisfy (S1)-(S2) with
`κ^{(k)}`.  The premises are those of Lemma II.5.13: (1.26) for the ancestors is the induction
hypothesis, the kept operators are the base of the induction at the kept components, and the
step bound is `StepData.gauss`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section LocOpBound

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)

/-- **(D5) along the lineage** (Lemma II.5.13 by induction on the scale): the localized
operators satisfy the bound (1.26) with the exponents `κ_k(Z, 𝔞)` (`κ`), given that the kept
operators do (S3), that the step data satisfy (S1)-(S2) with `κ^{(k)}` (`StepData.gauss`), and
that `κ_{k+1}(Z') = κ^{(k)}(Z') + ∑_Y κ_k(Y)` at the components that are not kept. -/
theorem locOp_pkgBound (hH : H.Admissible) (lab : ∀ k, H.Comp k → Fin 5)
    (hz : ∀ k, 0 < cs.z (k + 1))
    (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (κ : ∀ k, H.Comp k → ℝ)
    (hkept : ∀ (k : ℕ) (hk : k ≤ K) (Z : H.Comp k), IsKept H k Z →
      PkgBound (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z) (κ k Z))
    (hstep : ∀ (k : ℕ) (Z' : H.Comp (k + 1)), ¬ IsKept H (k + 1) Z' →
      κ (k + 1) Z' = κs k (H.localHistory M K (k + 1) Z') + ∑ Y ∈ H.parts k Z', κ k Y) :
    ∀ (k : ℕ) (hk : k ≤ K) (Z : H.Comp k),
      PkgBound (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z) (κ k Z) := by
  intro k
  induction k with
  | zero => intro hk Z; exact (H.F.isEmpty_comp_zero.false Z).elim
  | succ k ih =>
    intro hk Z'
    by_cases hkp : IsKept H (k + 1) Z'
    · exact hkept (k + 1) hk Z' hkp
    · rw [locOp_level geo cs SD KD hk hkp]
      have h := preOp_pkgBound geo cs SD hH hk Z'
        (fun Y _ => locOp geo cs SD KD hH lab k (by omega) Y) (hz k) (hc k)
        (fun Y => κ k Y.1) (fun Y => ih (by omega) Y.1)
      rw [hstep k Z' hkp, ← Finset.sum_coe_sort]
      exact h

/-- **(D5) with the exponents of Definition II.5.11**: the exponent of the localized operators is
`H.kappa P κK` (`κ^pre_{k+1} = ∑_Y κ_k(Y) + κ^{(k)}`, with `κ^{(k)}` the step exponent of the
budget, `BudgetConsts.kappaStep`), the kept components carrying the exponents `κK` of (S3). -/
theorem locOp_pkgBound_kappa (hH : H.Admissible) (lab : ∀ k, H.Comp k → Fin 5)
    (hz : ∀ k, 0 < cs.z (k + 1))
    (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (P : BudgetConsts) (κK : ∀ k, H.Comp k → ℝ)
    (hκs : ∀ (k : ℕ) (Z' : H.Comp (k + 1)), κs k (H.localHistory M K (k + 1) Z') =
      P.kappaStep S k (Z'.1 ∩ H.newCubes (k + 1)).card (H.outCubes k Z').card)
    (hkept : ∀ (k : ℕ) (hk : k ≤ K) (Z : H.Comp k), IsKept H k Z →
      PkgBound (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z) (κK k Z)) :
    ∀ (k : ℕ) (hk : k ≤ K) (Z : H.Comp k),
      PkgBound (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z) (H.kappa P κK k Z) := by
  refine locOp_pkgBound geo cs SD KD hH lab hz hc (H.kappa P κK) ?_ ?_
  · intro k hk Z hZ
    have h := hkept k hk Z hZ
    cases k with
    | zero => exact (H.F.isEmpty_comp_zero.false Z).elim
    | succ k =>
      have hev : H.IsKeptEvent (k + 1) Z := hZ
      simpa [RegionHistory.kappa, hev] using h
  · intro k Z' hZ'
    have hev : ¬ H.IsKeptEvent (k + 1) Z' := hZ'
    rw [hκs k Z']
    simp only [RegionHistory.kappa, hev, ↓reduceIte, RegionHistory.kappaPre]
    ring

end LocOpBound

end Balaban.LargeField
