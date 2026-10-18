module

public import Balaban.LargeField.Base.BaseMainAction
public import Balaban.LargeField.Base.BaseWitnessGauss
public import Balaban.LargeField.Operators.StepData
public import Balaban.LargeField.Operators.CompBound
public import Balaban.LargeField.Operators.QuietSymm
public import Balaban.LargeField.Base.BaseCarrierData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The physical base carrier and the base kernel (ruling R7)
(BASE-KERNEL §§1-3, §5; LF-RECONSTRUCTION Definition II.7.6, Lemma II.7.7)

BASE-KERNEL §1 factors the base kernel as
`K_0 = ∏_y z_1^N t_0 · ∑_w F^w_0(u) K̃^w_0` (1.1), where `∏ z_1^N t_0` is `gaussProd` and `F^w_0` is
`baseF`.  The remainder `K̃^w_0` is the conditional integral of P5 (2.47) over the spins of the
component after the substitution (2.20) (only the ultralocal Gaussian `ψ'` is integrated; no raw
spin is an argument) and with the complex source `g` kept as an argument.  It contains the cutoff transfer across `∂Ω''_1`,
the base covariance localization and the first small-field expectation (BASE-KERNEL §6, tasks 1-3 =
Proposition II.7.9), which is open.

`BaseSmallFieldInput` is the single structure that packages these open facts.  Its primary datum is
`Kphys`, the complex remainder on the history `H`, the component `Z'`, the complex source on the
physical torus, the witness `w`, the output, the new internal variables and the field `h`
(`notes/phase1/BASECARRIER.md`; the base record is `H.baseRecord`).  The local history is
`H.localHistory 1 1 1 Z'` (`M = K = 1`).  Everything else is a property of `Kphys`.

The source-free real factor `K̃^w_0(0)` (`baseKt0`) is the real part of `Kphys` at source `0`, and
the factorization `K̃^w_0(g) = K̃^w_0(0) e^{b_w(g)}` is a theorem on its nonvanishing domain
(`baseKphys_eq_Kt0_mul_exp`, and after the witness sum `baseKC_eq_baseK0_mul_exp`).  The real
kernel `K_0 = baseK0` and the complex kernel `baseKC` are derived from `Kphys`.

Consequences of the old carrier that are **not** available from this one: a witness-independent
analytic exponent `b_0` (the two-atom example of the W1009 handoff), an `LFKernel` built from the
input (its `b` is total and analytic, `K` is independent of `g`), the indexing by a bare localized
history `a` ((S4) by indexing is now the field `euclid_K` between two histories), and the
`LFKernel`-based `BaseStepData.S2` and `GaussStructure` of the input.  The `∑_{records} ∏ K_0 = ρ_1`
transform relation is not a field (`notes/phase1/BASECARRIER.md`, item T).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal

section Input

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The sum `∑_w F^w_0(u) K̃^w_0` of (1.1), for a remainder family `Kt`; `u_y = z_1 ψ_1(y) -
(Qψ_0)(y)` (`gaussArg`) and `F^w_0 = baseF` with the tolerance `δ_0`. -/
noncomputable def baseSumOf (cs : OpConsts) (a : LocalHistory S n M K)
    (Kt : BaseW a 0 → OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → ℝ)
    (o : OutT N R a (0 + 1)) (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N)) : ℝ :=
  open Classical in
  ∑ w : BaseW a 0, baseF a 0 (cs.delta 0) w (fun y => gaussArg N (cs.z (0 + 1)) o x y.1) *
    Kt w o x hv

/-- The complex sum `∑_w F^w_0(u) K̃^w_0(g)` of (1.1), for a complex remainder family `Kc`. -/
noncomputable def baseSumC (cs : OpConsts) (a : LocalHistory S n M K)
    (Kc : BaseW a 0 → OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → ℂ)
    (o : OutT N R a (0 + 1)) (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N)) : ℂ :=
  open Classical in
  ∑ w : BaseW a 0, ((baseF a 0 (cs.delta 0) w
    (fun y => gaussArg N (cs.z (0 + 1)) o x y.1) : ℝ) : ℂ) * Kc w o x hv

end Input

section Carrier

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} [NeZero S.L] {N : ℕ}

/-- **The physical base carrier** (BASE-KERNEL §§1-3, §5, §6 tasks 1-3 = Proposition II.7.9; P5
(2.20), (2.47); the conditional integral of `notes/phase1/BASECARRIER.md`).

`Kphys H hH Z' g w o x hv` is the remainder `K̃^w_0 e^{b_0}` of (1.1), P5 (2.47), Lemma II.7.7 for the
admissible history `H` and the component `Z'` of `Z^pre_1`: the source kernel of the substitution
(2.20) `ψ_k = ψ^{(k)}(Ω'; θ) + β_k^{-1/2} ψ'`, in which only the ultralocal Gaussian `ψ'` on
`Ω_{k+1} ∩ Ω''^c` is integrated.  It reads the output `o` (`ψ_1`), the new internal variables `x`
(the spins on `Z' ∖ Ω_1`, the fluctuation `ψ'_0` on `Ω ∖ Ω''` and the other new variables), the
field `h` (`hv`) and the source `g` on the physical torus `Torus d (L n_1)`; it reads no raw spin:
the spins outside `Z'` enter the source only through `o`, `h` and `g` (Lemma II.7.7 (b)), and the
spins on `Z' ∖ Ω_1` are held by `x` and not given a second time.  The base record of the history is
`H.baseRecord`; the history enters through the local history `a = H.localHistory 1 1 1 Z'`. -/
structure BaseSmallFieldInput (k0 : ℕ) (geo : Geo S n R 1) (cs : OpConsts) (N : ℕ) where
  /-- the complex remainder `K̃^w_0` -/
  Kphys : ∀ (H : RegionHistory S n R k0 1), H.Admissible → ∀ (Z' : H.Comp 1),
    (Torus S.d (S.L * n 1) → Fin N → ℂ) →
    BaseW (H.localHistory 1 1 1 Z') 0 → OutT N R (H.localHistory 1 1 1 Z') 1 →
    NewCfg N (H.localHistory 1 1 1 Z') 0 → EuclideanSpace ℝ (Fin N) → ℂ
  /-- `K̃^w_0` is Borel in the output and the internal variables (§5) -/
  Kphys_meas : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (g : Torus S.d (S.L * n 1) → Fin N → ℂ)
    (w : BaseW (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)),
    Measurable fun p : OutT N R (H.localHistory 1 1 1 Z') 1 × NewCfg N (H.localHistory 1 1 1 Z') 0 =>
      Kphys H hH Z' g w p.1 p.2 hv
  /-- `K̃^w_0` is independent of `ψ_1` on `Ω^c`: only `A_c(u)` reads it (§5, first paragraph) -/
  Kphys_outside : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (g : Torus S.d (S.L * n 1) → Fin N → ℂ)
    (w : BaseW (H.localHistory 1 1 1 Z') 0) (o o' : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)),
    (∀ y : Vblk R (H.localHistory 1 1 1 Z') (0 + 1),
      y.1 ∉ gaussBlocks (H.localHistory 1 1 1 Z') 0 → o y = o' y) →
      Kphys H hH Z' g w o x hv = Kphys H hH Z' g w o' x hv
  /-- `K̃^w_0` vanishes off `χ^new_0` (§1 last paragraph: `chiNew` supplies the support condition) -/
  Kphys_dom : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (g : Torus S.d (S.L * n 1) → Fin N → ℂ)
    (w : BaseW (H.localHistory 1 1 1 Z') 0) (o : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)),
    ¬ ChiNewAt geo cs H 0 Z' o x → Kphys H hH Z' g w o x hv = 0
  /-- the source-free sector is real and nonnegative (§1 (1.1), §5 "all real factors are
  nonnegative Borel"): the integrand is positive when `g = 0` -/
  Kphys_zero_sector : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
     (w : BaseW (H.localHistory 1 1 1 Z') 0)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)),
    (Kphys H hH Z' 0 w o x hv).im = 0 ∧ 0 ≤ (Kphys H hH Z' 0 w o x hv).re
  /-- the modulus bound relative to the source-free sector (Lemma II.7.7 (b)): on the `ℓ¹` unit
  ball of the source and on `χ^new_0`, `|K̃^w_0(g)| ≤ K̃^w_0(0) e^{‖g|_{Z'}‖_1}`.  The source
  enters `K̃^w_0 e^{b_0}` through the term `⟨g, φ⟩` of `b_0` with unit spins `φ` on `Z'`, so
  `|e^{⟨g,φ⟩}| ≤ e^{‖g|_{Z'}‖_1}` (the proof of (b)); the absolute bound
  `|b_0| ≤ (C_b log β + C_b)|Z'|_1` follows from it where `|Z'|_1 ≥ 1` (no typing constant is
  needed in this form) -/
  Kphys_bound : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (g : GIdx S n 1 1 N → ℂ)
    (w : BaseW (H.localHistory 1 1 1 Z') 0) (o : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)),
    g ∈ l1Ball (GIdx S n 1 1 N) → ChiNewAt geo cs H 0 Z' o x →
    ‖Kphys H hH Z' (baseSource S n N g) w o x hv‖ ≤
      (Kphys H hH Z' 0 w o x hv).re *
        Real.exp (baseSourceNorm H Z' g)
  /-- `K̃^w_0` is analytic in the source on the `ℓ¹` unit ball (§3, joint H7 analyticity) -/
  Kphys_analytic : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
     (w : BaseW (H.localHistory 1 1 1 Z') 0)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)),
    AnalyticOnNhd ℂ (fun g : GIdx S n 1 1 N → ℂ =>
      Kphys H hH Z' (baseSource S n N g) w o x hv) (l1Ball (GIdx S n 1 1 N))
  /-- `K̃^w_0` is real for real sources (§3) -/
  Kphys_real : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (g : GIdx S n 1 1 N → ℂ)
    (w : BaseW (H.localHistory 1 1 1 Z') 0) (o : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)),
    g ∈ l1Ball (GIdx S n 1 1 N) → (∀ i, (g i).im = 0) →
      (Kphys H hH Z' (baseSource S n N g) w o x hv).im = 0
  /-- `K̃^w_0` depends on the source only through its restriction to the sites of `Z'` (Lemma II.7.7
  (b), "`g|_V`"; the source term is counted once on `Z'`, not on the overlapping collars) -/
  Kphys_supp : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
     (g g' : GIdx S n 1 1 N → ℂ)
    (w : BaseW (H.localHistory 1 1 1 Z') 0) (o : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)),
    (∀ i : GIdx S n 1 1 N, i.1 ∈ baseZsites H Z' → g i = g' i) →
      Kphys H hH Z' (baseSource S n N g) w o x hv =
        Kphys H hH Z' (baseSource S n N g') w o x hv
  /-- `O(N)`-covariance of `K̃^w_0`: rotate the source, the output, the internal
  variables and the field (§5 (S5)(i)) -/
  Kphys_rot : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (g : Torus S.d (S.L * n 1) → Fin N → ℂ)
    (w : BaseW (H.localHistory 1 1 1 Z') 0) (ρ : OrthN N)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)),
    Kphys H hH Z' (baseRotSrc ρ g) w (rotOut ρ o) (rotSub ρ x) (ρ hv) =
      Kphys H hH Z' g w o x hv
  /-- Euclidean covariance of the kernel `K_0 = ∏ z_1^N t_0 · ∑_w F^w_0 K̃^w_0` (§5: Lemma I.3.9
  and the local-covariance core equality give (S4)), between the localized histories of two
  components that correspond under a torus symmetry `σ` -/
  euclid_K : ∀ (σ : TorusSym S n 1 1)
    (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (H' : RegionHistory S n R k0 1) (hH' : H'.Admissible) (Z'' : H'.Comp 1)
    (hI : HistImage σ (H.localHistory 1 1 1 Z') (H'.localHistory 1 1 1 Z''))
    (hk : 0 + 1 ≤ 1) (g g' : GIdx S n 1 1 N → ℂ)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (o' : OutT N R (H'.localHistory 1 1 1 Z'') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (x' : NewCfg N (H'.localHistory 1 1 1 Z'') 0)
    (hv : EuclideanSpace ℝ (Fin N)),
    RelOut σ o o' → RelSub hI hk x x' → RelG σ g g' →
      gaussProd N (H'.localHistory 1 1 1 Z'') 0 cs o' x' *
          baseSumC cs (H'.localHistory 1 1 1 Z'')
            (fun w => Kphys H' hH' Z'' (baseSource S n N g') w) o' x' hv =
        gaussProd N (H.localHistory 1 1 1 Z') 0 cs o x *
          baseSumC cs (H.localHistory 1 1 1 Z')
            (fun w => Kphys H hH Z' (baseSource S n N g) w) o x hv

end Carrier

section Derived

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} [NeZero S.L] {N : ℕ}
  {k0 : ℕ} {geo : Geo S n R 1} {cs : OpConsts}
  (inp : BaseSmallFieldInput k0 geo cs N)
  (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)

/-- **The source-free real factor** `K̃^w_0(0)`: the real part of `Kphys` at source `0`. -/
noncomputable def baseKt0 (w : BaseW (H.localHistory 1 1 1 Z') 0)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) : ℝ :=
  (inp.Kphys H hH Z' 0 w o x hv).re

theorem Kphys_zero_eq (w : BaseW (H.localHistory 1 1 1 Z') 0)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) :
    inp.Kphys H hH Z' 0 w o x hv = (baseKt0 inp H hH Z' w o x hv : ℂ) :=
  Complex.ext (by simp [baseKt0]) (by simpa using (inp.Kphys_zero_sector H hH Z' w o x hv).1)

theorem baseKt0_nonneg (w : BaseW (H.localHistory 1 1 1 Z') 0)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) : 0 ≤ baseKt0 inp H hH Z' w o x hv :=
  (inp.Kphys_zero_sector H hH Z' w o x hv).2

theorem measurable_baseKt0 (w : BaseW (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) :
    Measurable fun p : OutT N R (H.localHistory 1 1 1 Z') 1 ×
        NewCfg N (H.localHistory 1 1 1 Z') 0 => baseKt0 inp H hH Z' w p.1 p.2 hv :=
  Complex.measurable_re.comp (inp.Kphys_meas H hH Z' 0 w hv)

theorem baseKt0_outside (w : BaseW (H.localHistory 1 1 1 Z') 0)
    (o o' : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N))
    (h : ∀ y : Vblk R (H.localHistory 1 1 1 Z') (0 + 1),
      y.1 ∉ gaussBlocks (H.localHistory 1 1 1 Z') 0 → o y = o' y) :
    baseKt0 inp H hH Z' w o x hv = baseKt0 inp H hH Z' w o' x hv := by
  unfold baseKt0
  rw [inp.Kphys_outside H hH Z' 0 w o o' x hv h]

theorem baseKt0_dom (w : BaseW (H.localHistory 1 1 1 Z') 0)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) (h : ¬ ChiNewAt geo cs H 0 Z' o x) :
    baseKt0 inp H hH Z' w o x hv = 0 := by
  unfold baseKt0
  rw [inp.Kphys_dom H hH Z' 0 w o x hv h]; rfl

theorem baseKt0_rot (w : BaseW (H.localHistory 1 1 1 Z') 0) (ρ : OrthN N)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) :
    baseKt0 inp H hH Z' w (rotOut ρ o) (rotSub ρ x) (ρ hv) =
      baseKt0 inp H hH Z' w o x hv := by
  unfold baseKt0
  have := inp.Kphys_rot H hH Z' 0 w ρ o x hv
  rw [baseRotSrc_zero] at this
  rw [this]

/-! ### The modulus bound and the factorization on the nonvanishing domain -/

/-- The modulus bound of `Kphys_bound` without the support hypothesis: off `χ^new_0` the value is
`0` (`Kphys_dom`). -/
theorem baseKphys_norm_le (g : GIdx S n 1 1 N → ℂ) (hg : g ∈ l1Ball (GIdx S n 1 1 N))
    (w : BaseW (H.localHistory 1 1 1 Z') 0) (o : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)) :
    ‖inp.Kphys H hH Z' (baseSource S n N g) w o x hv‖ ≤
      baseKt0 inp H hH Z' w o x hv *
        Real.exp (baseSourceNorm H Z' g) := by
  by_cases hc : ChiNewAt geo cs H 0 Z' o x
  · exact inp.Kphys_bound H hH Z' g w o x hv hg hc
  · rw [inp.Kphys_dom H hH Z' _ w o x hv hc, norm_zero,
      baseKt0_dom inp H hH Z' w o x hv hc, zero_mul]

/-- A vanishing source-free sector has vanishing source-dependent sector: the complex-source
integral of a nonnegative integrand supported in a null set is zero. -/
theorem baseKphys_eq_zero_of_baseKt0_eq_zero (g : GIdx S n 1 1 N → ℂ)
    (hg : g ∈ l1Ball (GIdx S n 1 1 N)) (w : BaseW (H.localHistory 1 1 1 Z') 0)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) (h0 : baseKt0 inp H hH Z' w o x hv = 0) :
    inp.Kphys H hH Z' (baseSource S n N g) w o x hv = 0 := by
  have := baseKphys_norm_le inp H hH Z' g hg w o x hv
  rw [h0, zero_mul] at this
  exact norm_le_zero_iff.mp this

/-- **The per-witness complex factorization** `K̃^w_0(g) = K̃^w_0(0) e^{b_w(g)}` on the
nonvanishing domain: where `K̃^w_0(g) ≠ 0` the source-free sector is positive and
`b_w(g) = log (K̃^w_0(g) / K̃^w_0(0))` (a branch of the logarithm). -/
theorem baseKphys_eq_Kt0_mul_exp (g : GIdx S n 1 1 N → ℂ) (hg : g ∈ l1Ball (GIdx S n 1 1 N))
    (w : BaseW (H.localHistory 1 1 1 Z') 0) (o : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N))
    (hne : inp.Kphys H hH Z' (baseSource S n N g) w o x hv ≠ 0) :
    0 < baseKt0 inp H hH Z' w o x hv ∧
      inp.Kphys H hH Z' (baseSource S n N g) w o x hv =
        (baseKt0 inp H hH Z' w o x hv : ℂ) *
          Complex.exp (Complex.log (inp.Kphys H hH Z' (baseSource S n N g) w o x hv /
            (baseKt0 inp H hH Z' w o x hv : ℂ))) := by
  have hpos : 0 < baseKt0 inp H hH Z' w o x hv :=
    lt_of_le_of_ne (baseKt0_nonneg inp H hH Z' w o x hv) fun h =>
      hne (baseKphys_eq_zero_of_baseKt0_eq_zero inp H hH Z' g hg w o x hv h.symm)
  refine ⟨hpos, ?_⟩
  have hc : (baseKt0 inp H hH Z' w o x hv : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [Complex.exp_log (div_ne_zero hne hc), mul_div_cancel₀ _ hc]

end Derived

section SumLemmas

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

theorem baseSumOf_nonneg (cs : OpConsts) (a : LocalHistory S n M K)
    {Kt : BaseW a 0 → OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → ℝ}
    (hKt : ∀ w o x hv, 0 ≤ Kt w o x hv) (o : OutT N R a (0 + 1)) (x : NewCfg N a 0)
    (hv : EuclideanSpace ℝ (Fin N)) : 0 ≤ baseSumOf cs a Kt o x hv := by
  classical
  unfold baseSumOf
  exact Finset.sum_nonneg fun w _ =>
    mul_nonneg (baseF_mem_unit a 0 _ w _).1 (hKt w o x hv)

theorem measurable_baseSumOf (cs : OpConsts) (a : LocalHistory S n M K)
    {Kt : BaseW a 0 → OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → ℝ}
    (hKt : ∀ w hv, Measurable fun p : OutT N R a (0 + 1) × NewCfg N a 0 => Kt w p.1 p.2 hv)
    (hv : EuclideanSpace ℝ (Fin N)) :
    Measurable fun p : OutT N R a (0 + 1) × NewCfg N a 0 => baseSumOf cs a Kt p.1 p.2 hv := by
  classical
  unfold baseSumOf
  refine Finset.measurable_sum _ fun w _ => Measurable.mul ?_ (hKt w hv)
  exact (measurable_baseF a 0 (cs.delta 0) w).comp
    (measurable_pi_iff.mpr fun y => measurable_gaussArg_pair (cs.z (0 + 1)) y.1)

/-- Rotation covariance of the sum, for two families related by the rotation. -/
theorem baseSumOf_rot (cs : OpConsts) (a : LocalHistory S n M K)
    {Kt Kt' : BaseW a 0 → OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → ℝ}
    (ρ : OrthN N)
    (hKt : ∀ w o x hv, Kt' w (rotOut ρ o) (rotSub ρ x) (ρ hv) = Kt w o x hv)
    (o : OutT N R a (0 + 1)) (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N)) :
    baseSumOf cs a Kt' (rotOut ρ o) (rotSub ρ x) (ρ hv) = baseSumOf cs a Kt o x hv := by
  classical
  unfold baseSumOf
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hKt]
  congr 1
  have : (fun y : ↥(gaussBlocks a 0) => gaussArg N (cs.z (0 + 1)) (rotOut ρ o) (rotSub ρ x) y.1) =
      fun y => ρ (gaussArg N (cs.z (0 + 1)) o x y.1) := by
    funext y
    unfold gaussArg
    rw [outField_rot, qCoarseK_rot, ← map_smul, ← map_sub]
  rw [this]
  exact baseF_rot a 0 (cs.delta 0) w ρ _

/-- The complex sum of real families is the cast of the real sum. -/
theorem baseSumC_ofReal (cs : OpConsts) (a : LocalHistory S n M K)
    (Kt : BaseW a 0 → OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → ℝ)
    (o : OutT N R a (0 + 1)) (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N)) :
    baseSumC cs a (fun w o x hv => (Kt w o x hv : ℂ)) o x hv = (baseSumOf cs a Kt o x hv : ℂ) := by
  classical
  unfold baseSumC baseSumOf
  push_cast
  rfl

/-- The modulus of the complex sum is at most the real sum of the bounds. -/
theorem norm_baseSumC_le (cs : OpConsts) (a : LocalHistory S n M K)
    (Kc : BaseW a 0 → OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → ℂ)
    (B : BaseW a 0 → OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → ℝ)
    (o : OutT N R a (0 + 1)) (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N))
    (h : ∀ w, ‖Kc w o x hv‖ ≤ B w o x hv) :
    ‖baseSumC cs a Kc o x hv‖ ≤ baseSumOf cs a B o x hv := by
  classical
  unfold baseSumC baseSumOf
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (baseF_mem_unit a 0 _ w _).1]
  exact mul_le_mul_of_nonneg_left (h w) (baseF_mem_unit a 0 _ w _).1

end SumLemmas

section Kernel

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} [NeZero S.L] {N : ℕ}
  {k0 : ℕ} {geo : Geo S n R 1} {cs : OpConsts}
  (inp : BaseSmallFieldInput k0 geo cs N)
  (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)

/-- **The base kernel** `K_0 = ∏_y z_1^N t_0 · ∑_w F^w_0(u) K̃^w_0(0)` of BASE-KERNEL §1 (1.1), at
the source-free sector, for the component `Z'` of the history `H`. -/
noncomputable def baseK0 (o : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)) : ℝ :=
  gaussProd N (H.localHistory 1 1 1 Z') 0 cs o x *
    baseSumOf cs (H.localHistory 1 1 1 Z') (fun w => baseKt0 inp H hH Z' w) o x hv

/-- **The complex base kernel** `K_0(g) = ∏_y z_1^N t_0 · ∑_w F^w_0(u) K̃^w_0(g)` with the complex
source `g` of the large-field layer. -/
noncomputable def baseKC (g : GIdx S n 1 1 N → ℂ) (o : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)) : ℂ :=
  (gaussProd N (H.localHistory 1 1 1 Z') 0 cs o x : ℂ) *
    baseSumC cs (H.localHistory 1 1 1 Z')
      (fun w => inp.Kphys H hH Z' (baseSource S n N g) w) o x hv

/-- The remainder family of the Gaussian witnesses of (S1) at `k = 0`: `W = {blk, bd}^{P_1 ∩ Z'}`,
`F^w_0 = baseF`, `K̃^w_0` the source-free sector of the input. -/
noncomputable def baseWit (cs : OpConsts) : GaussWit N R (H.localHistory 1 1 1 Z') 0 :=
  open Classical in
  { W := BaseW (H.localHistory 1 1 1 Z') 0
    F := fun w u => baseF (H.localHistory 1 1 1 Z') 0 (cs.delta 0) w u
    Kt := fun w o x hv => baseKt0 inp H hH Z' w o x hv }

theorem baseK0_eq (o : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)) :
    baseK0 inp H hH Z' o x hv = gaussProd N (H.localHistory 1 1 1 Z') 0 cs o x *
      ∑ w, (baseWit inp H hH Z' cs).F w
        (fun y => gaussArg N (cs.z (0 + 1)) o x y.1) * (baseWit inp H hH Z' cs).Kt w o x hv := by
  classical
  rfl

theorem baseK0_nonneg (hz : 0 ≤ cs.z (0 + 1))
    (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) : 0 ≤ baseK0 inp H hH Z' o x hv :=
  mul_nonneg (gaussProd_nonneg N _ 0 cs hz hc o x)
    (baseSumOf_nonneg cs _ (fun w o x hv => baseKt0_nonneg inp H hH Z' w o x hv) o x hv)

theorem measurable_baseK0 (hv : EuclideanSpace ℝ (Fin N)) :
    Measurable fun p : OutT N R (H.localHistory 1 1 1 Z') 1 × NewCfg N (H.localHistory 1 1 1 Z') 0 =>
      baseK0 inp H hH Z' p.1 p.2 hv :=
  (measurable_gaussProd_pair (H.localHistory 1 1 1 Z') 0 cs).mul
    (measurable_baseSumOf cs _ (fun w hv => measurable_baseKt0 inp H hH Z' w hv) hv)

theorem baseK0_rot (ρ : OrthN N) (o : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)) :
    baseK0 inp H hH Z' (rotOut ρ o) (rotSub ρ x) (ρ hv) =
      baseK0 inp H hH Z' o x hv := by
  unfold baseK0
  rw [gaussProd_rot, baseSumOf_rot cs _
    (Kt := fun w => baseKt0 inp H hH Z' w)
    (Kt' := fun w => baseKt0 inp H hH Z' w) ρ
    (fun w o x hv => baseKt0_rot inp H hH Z' w ρ o x hv)]

theorem baseK0_dom (o : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N))
    (hn : ¬ ChiNewAt geo cs H 0 Z' o x) : baseK0 inp H hH Z' o x hv = 0 := by
  classical
  unfold baseK0
  have : baseSumOf cs (H.localHistory 1 1 1 Z') (fun w => baseKt0 inp H hH Z' w) o x hv = 0 := by
    unfold baseSumOf
    exact Finset.sum_eq_zero fun w _ => by
      dsimp only
      rw [baseKt0_dom inp H hH Z' w o x hv hn, mul_zero]
  rw [this, mul_zero]

/-- At source `0` the complex kernel is the real kernel. -/
theorem baseKC_zero (o : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N)) :
    baseKC inp H hH Z' 0 o x hv = (baseK0 inp H hH Z' o x hv : ℂ) := by
  unfold baseKC baseK0
  rw [baseSource_zero]
  have : (fun w => inp.Kphys H hH Z' 0 w) =
      fun w o x hv => (baseKt0 inp H hH Z' w o x hv : ℂ) := by
    funext w o x hv; exact Kphys_zero_eq inp H hH Z' w o x hv
  rw [this, baseSumC_ofReal]; push_cast; rfl

/-- **The modulus bound of the complex kernel**:
`|K_0(g)| ≤ K_0(0) e^{‖g|_{Z'}‖_1}` on the `ℓ¹` unit ball. -/
theorem norm_baseKC_le (g : GIdx S n 1 1 N → ℂ) (hg : g ∈ l1Ball (GIdx S n 1 1 N))
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) :
    ‖baseKC inp H hH Z' g o x hv‖ ≤
      baseK0 inp H hH Z' o x hv *
        Real.exp (baseSourceNorm H Z' g) := by
  classical
  unfold baseKC baseK0
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gaussProd_nonneg N _ 0 cs hz hc o x),
    mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (gaussProd_nonneg N _ 0 cs hz hc o x)
  have hb := norm_baseSumC_le cs (H.localHistory 1 1 1 Z')
    (fun w => inp.Kphys H hH Z' (baseSource S n N g) w)
    (fun w o x hv => baseKt0 inp H hH Z' w o x hv *
      Real.exp (baseSourceNorm H Z' g)) o x hv
    (fun w => baseKphys_norm_le inp H hH Z' g hg w o x hv)
  refine hb.trans (le_of_eq ?_)
  unfold baseSumOf
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- A vanishing source-free kernel has a vanishing complex kernel. -/
theorem baseKC_eq_zero_of_baseK0_eq_zero (g : GIdx S n 1 1 N → ℂ)
    (hg : g ∈ l1Ball (GIdx S n 1 1 N)) (hz : 0 ≤ cs.z (0 + 1))
    (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) (h0 : baseK0 inp H hH Z' o x hv = 0) :
    baseKC inp H hH Z' g o x hv = 0 := by
  have := norm_baseKC_le inp H hH Z' g hg hz hc o x hv
  rw [h0, zero_mul] at this
  exact norm_le_zero_iff.mp this

/-- **The complex factorization of the base kernel** `K_0(g) = K_0(0) e^{b_0(g)}` on the
nonvanishing domain (after the witness sum): where `K_0(g) ≠ 0` the source-free kernel is positive
and `b_0(g) = log (K_0(g) / K_0(0))` (a branch of the logarithm). -/
theorem baseKC_eq_baseK0_mul_exp (g : GIdx S n 1 1 N → ℂ) (hg : g ∈ l1Ball (GIdx S n 1 1 N))
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) (hne : baseKC inp H hH Z' g o x hv ≠ 0) :
    0 < baseK0 inp H hH Z' o x hv ∧
      baseKC inp H hH Z' g o x hv =
        (baseK0 inp H hH Z' o x hv : ℂ) *
          Complex.exp (Complex.log (baseKC inp H hH Z' g o x hv /
            (baseK0 inp H hH Z' o x hv : ℂ))) := by
  have hpos : 0 < baseK0 inp H hH Z' o x hv :=
    lt_of_le_of_ne (baseK0_nonneg inp H hH Z' hz hc o x hv) fun h =>
      hne (baseKC_eq_zero_of_baseK0_eq_zero inp H hH Z' g hg hz hc o x hv h.symm)
  refine ⟨hpos, ?_⟩
  have hc' : (baseK0 inp H hH Z' o x hv : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [Complex.exp_log (div_ne_zero hne hc'), mul_div_cancel₀ _ hc']

theorem baseKC_rot (ρ : OrthN N) (g : GIdx S n 1 1 N → ℂ)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) :
    baseKC inp H hH Z' (rotG ρ g) (rotOut ρ o) (rotSub ρ x) (ρ hv) =
      baseKC inp H hH Z' g o x hv := by
  classical
  unfold baseKC
  rw [gaussProd_rot, ← baseRotSrc_baseSource]
  congr 1
  unfold baseSumC
  refine Finset.sum_congr rfl fun w _ => ?_
  dsimp only
  rw [inp.Kphys_rot H hH Z' (baseSource S n N g) w ρ o x hv]
  congr 2
  have : (fun y : ↥(gaussBlocks (H.localHistory 1 1 1 Z') 0) =>
      gaussArg N (cs.z (0 + 1)) (rotOut ρ o) (rotSub ρ x) y.1) =
      fun y => ρ (gaussArg N (cs.z (0 + 1)) o x y.1) := by
    funext y
    unfold gaussArg
    rw [outField_rot, qCoarseK_rot, ← map_smul, ← map_sub]
  rw [this]
  exact baseF_rot _ 0 (cs.delta 0) w ρ _

end Kernel

/-! ### The Gaussian structure (S1) of the source-free kernel -/

section Gauss

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The Gaussian structure (S1) of version 1.2, i.e. the first five clauses of `GaussStepSpec`
(`0 ≤ F^w ≤ 1`, `F^w` Borel, `K̃^w ≥ 0`, `K̃^w` independent of `ψ_{k+1}` off the Gaussian blocks,
and `K = ∏ z^N t_k · ∑_w F^w K̃^w`), for a real kernel function `Kfn`; the clause (S2) is the
existential tail of `GaussStepSpec`. -/
def GaussStructureFn (cs : OpConsts) (a : LocalHistory S n M K) (k : ℕ)
    (Kfn : OutT N R a (k + 1) → NewCfg N a k → EuclideanSpace ℝ (Fin N) → ℝ)
    (wit : GaussWit N R a k) : Prop :=
  (∀ w u, 0 ≤ wit.F w u ∧ wit.F w u ≤ 1) ∧
  (∀ w, Measurable (wit.F w)) ∧
  (∀ w o x hv, 0 ≤ wit.Kt w o x hv) ∧
  (∀ w o o' x hv, (∀ y : Vblk R a (k + 1), y.1 ∉ gaussBlocks a k → o y = o' y) →
    wit.Kt w o x hv = wit.Kt w o' x hv) ∧
  (∀ o x hv, Kfn o x hv = gaussProd N a k cs o x *
    ∑ w, wit.F w (fun y => gaussArg N (cs.z (k + 1)) o x y.1) * wit.Kt w o x hv)

end Gauss

/-! ### The `k = 0` slice of the step data -/

section StepData

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} [NeZero S.L] {N : ℕ}

/-- The base step data: the `k = 0` slice of `StepData` (Definition II.5.7 (S0), (S1), (S4)),
for every admissible history `H` and component `Z'`.  `K` is the source-free kernel
`K_0`, `KC` the complex kernel with the source of the large-field layer; (S4) is `euclid_K`
between the localized histories of two components.  The one-step bound (S2) and the rotation form
(S5) are separate targets. -/
structure BaseStepData (k0 : ℕ) (geo : Geo S n R 1) (cs : OpConsts) (N : ℕ) where
  /-- the source-free step kernel `K_0(Z', a)` -/
  K : ∀ (H : RegionHistory S n R k0 1), H.Admissible → ∀ (Z' : H.Comp 1),
    OutT N R (H.localHistory 1 1 1 Z') 1 → NewCfg N (H.localHistory 1 1 1 Z') 0 →
    EuclideanSpace ℝ (Fin N) → ℝ
  /-- the complex step kernel at the source `g` -/
  KC : ∀ (H : RegionHistory S n R k0 1), H.Admissible → ∀ (Z' : H.Comp 1),
    (GIdx S n 1 1 N → ℂ) → OutT N R (H.localHistory 1 1 1 Z') 1 →
    NewCfg N (H.localHistory 1 1 1 Z') 0 → EuclideanSpace ℝ (Fin N) → ℂ
  /-- the Gaussian witnesses of (S1) -/
  wit : ∀ (H : RegionHistory S n R k0 1), H.Admissible → ∀ (Z' : H.Comp 1),
    GaussWit N R (H.localHistory 1 1 1 Z') 0
  /-- `K_0 ≥ 0` -/
  K_nonneg : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    o x hv, 0 ≤ K H hH Z' o x hv
  /-- `K_0` is Borel in the output and the internal variables -/
  measurable_K : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    hv,
    Measurable fun p : OutT N R (H.localHistory 1 1 1 Z') 1 × NewCfg N (H.localHistory 1 1 1 Z') 0 =>
      K H hH Z' p.1 p.2 hv
  /-- (S0)/(S1) `O(N)`-covariance of the kernel -/
  rot_K : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (ρ : OrthN N) o x hv,
    K H hH Z' (rotOut ρ o) (rotSub ρ x) (ρ hv) = K H hH Z' o x hv
  /-- (S1) the kernel vanishes off the new part `χ^new_0` of the domain -/
  dom : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    o x hv, ¬ ChiNewAt geo cs H 0 Z' o x → K H hH Z' o x hv = 0
  /-- (S1) the Gaussian structure -/
  gauss1 : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1),
    GaussStructureFn cs (H.localHistory 1 1 1 Z') 0 (K H hH Z') (wit H hH Z')
  /-- the complex kernel at source `0` is the real kernel -/
  KC_zero : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    o x hv, KC H hH Z' 0 o x hv = (K H hH Z' o x hv : ℂ)
  /-- the modulus bound `|K_0(g)| ≤ K_0(0) e^{‖g|_{Z'}‖_1}` on the `ℓ¹` ball -/
  KC_bound : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (g : GIdx S n 1 1 N → ℂ) o x hv, g ∈ l1Ball (GIdx S n 1 1 N) →
    ‖KC H hH Z' g o x hv‖ ≤
      K H hH Z' o x hv * Real.exp (baseSourceNorm H Z' g)
  /-- (S0) the complex kernel is analytic in the source on the `ℓ¹` ball (after the witness sum
  the sum of the analytic functions `K̃^w_0`) -/
  KC_analytic : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    o x hv,
    AnalyticOnNhd ℂ (fun g => KC H hH Z' g o x hv) (l1Ball (GIdx S n 1 1 N))
  /-- the complex kernel is real for real sources -/
  KC_real : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (g : GIdx S n 1 1 N → ℂ) o x hv, g ∈ l1Ball (GIdx S n 1 1 N) →
    (∀ i, (g i).im = 0) → (KC H hH Z' g o x hv).im = 0
  /-- (S0) the complex kernel depends on the source only through `g|_V` -/
  KC_supp : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (g g' : GIdx S n 1 1 N → ℂ) o x hv,
    (∀ i : GIdx S n 1 1 N, i.1 ∈ baseZsites H Z' → g i = g' i) →
      KC H hH Z' g o x hv = KC H hH Z' g' o x hv
  /-- (S0) `O(N)`-covariance of the complex kernel -/
  KC_rot : ∀ (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (ρ : OrthN N) g o x hv,
    KC H hH Z' (rotG ρ g) (rotOut ρ o) (rotSub ρ x) (ρ hv) =
      KC H hH Z' g o x hv
  /-- (S4) Euclidean covariance of the complex kernel (the source is transported) -/
  euclid_KC : ∀ (σ : TorusSym S n 1 1)
    (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (H' : RegionHistory S n R k0 1) (hH' : H'.Admissible) (Z'' : H'.Comp 1)
    (hI : HistImage σ (H.localHistory 1 1 1 Z') (H'.localHistory 1 1 1 Z''))
    (hk : 0 + 1 ≤ 1) (g g' : GIdx S n 1 1 N → ℂ)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (o' : OutT N R (H'.localHistory 1 1 1 Z'') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (x' : NewCfg N (H'.localHistory 1 1 1 Z'') 0)
    (hv : EuclideanSpace ℝ (Fin N)),
    RelOut σ o o' → RelSub hI hk x x' → RelG σ g g' →
      KC H' hH' Z'' g' o' x' hv = KC H hH Z' g o x hv

end StepData

section StepOfInput

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} [NeZero S.L] {N : ℕ}
  {k0 : ℕ} {geo : Geo S n R 1} {cs : OpConsts}

theorem baseKC_analytic (inp : BaseSmallFieldInput k0 geo cs N)
    (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) :
    AnalyticOnNhd ℂ (fun g => baseKC inp H hH Z' g o x hv) (l1Ball (GIdx S n 1 1 N)) := by
  classical
  unfold baseKC baseSumC
  intro g hg
  refine analyticAt_const.fun_mul (Finset.analyticAt_fun_sum _ fun w _ => ?_)
  exact analyticAt_const.fun_mul (inp.Kphys_analytic H hH Z' w o x hv g hg)

theorem baseKC_real (inp : BaseSmallFieldInput k0 geo cs N)
    (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (g : GIdx S n 1 1 N → ℂ) (o : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N))
    (hg : g ∈ l1Ball (GIdx S n 1 1 N)) (hr : ∀ i, (g i).im = 0) :
    (baseKC inp H hH Z' g o x hv).im = 0 := by
  classical
  unfold baseKC baseSumC
  rw [Complex.im_ofReal_mul, Complex.im_sum]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun w _ => ?_)
  rw [Complex.im_ofReal_mul, inp.Kphys_real H hH Z' g w o x hv hg hr, mul_zero]

theorem baseKC_supp (inp : BaseSmallFieldInput k0 geo cs N)
    (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (g g' : GIdx S n 1 1 N → ℂ) (o : OutT N R (H.localHistory 1 1 1 Z') 1)
    (x : NewCfg N (H.localHistory 1 1 1 Z') 0) (hv : EuclideanSpace ℝ (Fin N))
    (h : ∀ i : GIdx S n 1 1 N, i.1 ∈ baseZsites H Z' → g i = g' i) :
    baseKC inp H hH Z' g o x hv = baseKC inp H hH Z' g' o x hv := by
  classical
  unfold baseKC baseSumC
  congr 2
  funext w
  dsimp only
  rw [inp.Kphys_supp H hH Z' g g' w o x hv h]

/-- **The base step data** (BASE-KERNEL §§1-3, §5): (S0), (S1), (S4) at `k = 0`, conditional on the
small-field input. -/
noncomputable def baseStepData_of_input (inp : BaseSmallFieldInput k0 geo cs N)
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) :
    BaseStepData k0 geo cs N where
  K := fun H hH Z' => baseK0 inp H hH Z'
  KC := fun H hH Z' => baseKC inp H hH Z'
  wit := fun H hH Z' => baseWit inp H hH Z' cs
  K_nonneg := fun H hH Z' o x hv => baseK0_nonneg inp H hH Z' hz hc o x hv
  measurable_K := fun H hH Z' hv => measurable_baseK0 inp H hH Z' hv
  rot_K := fun H hH Z' ρ o x hv => baseK0_rot inp H hH Z' ρ o x hv
  dom := fun H hH Z' o x hv hn => baseK0_dom inp H hH Z' o x hv hn
  gauss1 := fun H hH Z' => by
    classical
    exact ⟨fun w u => baseF_mem_unit _ 0 _ w u, fun w => measurable_baseF _ 0 _ w,
      fun w o x hv => baseKt0_nonneg inp H hH Z' w o x hv,
      fun w o o' x hv h => baseKt0_outside inp H hH Z' w o o' x hv h,
      fun o x hv => baseK0_eq inp H hH Z' o x hv⟩
  KC_zero := fun H hH Z' o x hv => baseKC_zero inp H hH Z' o x hv
  KC_bound := fun H hH Z' g o x hv hg => norm_baseKC_le inp H hH Z' g hg hz hc o x hv
  KC_analytic := fun H hH Z' o x hv => baseKC_analytic inp H hH Z' o x hv
  KC_real := fun H hH Z' g o x hv hg hr => baseKC_real inp H hH Z' g o x hv hg hr
  KC_supp := fun H hH Z' g g' o x hv h => baseKC_supp inp H hH Z' g g' o x hv h
  KC_rot := fun H hH Z' ρ g o x hv => baseKC_rot inp H hH Z' ρ g o x hv
  euclid_KC := fun σ H hH Z' H' hH' Z'' hI hk g g' o o' x x' hv ho hx hg => by
    have := inp.euclid_K σ H hH Z' H' hH' Z'' hI hk g g' o o' x x' hv ho hx hg
    unfold baseKC
    exact this

/-! ### Inhabitation -/

/-- The zero `BaseSmallFieldInput`: the remainder `K̃^w_0 ≡ 0` (BASE-KERNEL-4 (3.1)).  It satisfies
every field; it is degenerate (`zero_input_kernel_eq_zero`). -/
noncomputable def zeroBaseSmallFieldInput (geo : Geo S n R 1) (cs : OpConsts) (N k0 : ℕ) :
    BaseSmallFieldInput k0 geo cs N where
  Kphys := fun _ _ _ _ _ _ _ _ => 0
  Kphys_meas := by intros; exact measurable_const
  Kphys_outside := by intros; rfl
  Kphys_dom := by intros; rfl
  Kphys_zero_sector := by intros; exact ⟨rfl, le_rfl⟩
  Kphys_bound := by intros; simp
  Kphys_analytic := by intros; exact analyticOnNhd_const
  Kphys_real := by intros; rfl
  Kphys_supp := by intros; rfl
  Kphys_rot := by intros; rfl
  euclid_K := by
    intro σ H hH Z' H' hH' Z'' hI hk g g' o o' x x' hv ho hx hg
    classical
    simp [baseSumC]

/-- **Inhabitation of `BaseSmallFieldInput`** (rule 10): the zero remainder satisfies every field.
The member is degenerate (`zero_input_kernel_eq_zero`); the physical datum is the conditional
integral of `notes/phase1/BASECARRIER.md`. -/
theorem baseSmallFieldInput_nonempty (geo : Geo S n R 1) (cs : OpConsts) (N k0 : ℕ) :
    Nonempty (BaseSmallFieldInput k0 geo cs N) :=
  ⟨zeroBaseSmallFieldInput geo cs N k0⟩

end StepOfInput

end Balaban.LargeField
