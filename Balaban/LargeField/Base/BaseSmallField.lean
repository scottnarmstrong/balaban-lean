module

public import Balaban.LargeField.Base.BaseMainAction
public import Balaban.LargeField.Base.BaseWitnessGauss
public import Balaban.LargeField.Operators.StepData
public import Balaban.LargeField.Operators.CompBound
public import Balaban.LargeField.Operators.QuietSymm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The base kernel and boundary factor, conditional on the first small-field integral
(BASE-KERNEL §§1-3, §5; LF-RECONSTRUCTION Definition II.7.6, Lemma II.7.7)

BASE-KERNEL §1 factors the base kernel as
`K_0 = ∏_y z_1^N t_0 · ∑_w F^w_0(u) K̃^w_0` (1.1), where `∏ z_1^N t_0` is `gaussProd` and `F^w_0` is
`baseF`.  The remainder `K̃^w_0` and the boundary exponent `b_0` are *not* defined unconditionally:
they contain the cutoff transfer across `∂Ω''_1`, the base covariance localization and the first
small-field expectation (BASE-KERNEL §6, tasks 1-3 = Proposition II.7.9), which is open.

`BaseSmallFieldInput` is the single structure that packages these open facts.  It is a *data* record
(the remainder `Kt` and the exponent `b0`, per localized history `a`, so that (S4) holds by
construction) together with exactly the properties that BASE-KERNEL assigns to Proposition II.7.9.
It is used only as the hypothesis of `*_of_input` declarations.  `baseSmallFieldInput_zero` is its
inhabitation witness (the zero remainder).

* `baseKernel_of_input`, `baseBoundary_of_input`: the base kernel `(K_0, b_0)` as an `LFKernel`;
* `BaseStepData`: the `k = 0` slice of `StepData` ((S0), (S1), (S4) by indexing);
* `baseStepData_of_input`: the base step data;
* `base_not_quiet`: the `quiet` field of `StepData` is vacuous at `k = 0`.
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

variable (K) in
/-- **The open small-field facts of the base step** (BASE-KERNEL §§1-3, §5, §6 tasks 1-3 =
Proposition II.7.9: cutoff transfer, base covariance localization, first small-field expectation).

`Kt a w` is the remainder `K̃^w_0` of (1.1) at the localized history `a` (the history enters only
through `a`: (S4), Lemma I.3.9 and the local-covariance core equality, BASE-KERNEL §5), and `b0 a`
is the boundary exponent `b_0` (§3).  The fields are exactly the properties that §§1, 3, 5 give them
*under* the open obligations. -/
structure BaseSmallFieldInput (k0 : ℕ) (geo : Geo S n R M) (cs : OpConsts) (N : ℕ) where
  /-- the remainder `K̃^w_0` of (1.1): the retained factors, the transferred `B_c^+` cutoffs and the
  first small-field expectation (§1 (1.1), §6 task 1 and task 3) -/
  Kt : ∀ a : LocalHistory S n M K, BaseW a 0 → OutT N R a (0 + 1) → NewCfg N a 0 →
    EuclideanSpace ℝ (Fin N) → ℝ
  /-- the boundary exponent `b_0` (§3 ledger; the rows marked `SF` are Proposition II.7.9) -/
  b0 : ∀ a : LocalHistory S n M K, OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) →
    (GIdx S n M K N → ℂ) → ℂ
  /-- `K̃^w_0 ≥ 0` (§1 (1.1), §5 "all real factors are nonnegative Borel") -/
  Kt_nonneg : ∀ a w o x hv, 0 ≤ Kt a w o x hv
  /-- `K̃^w_0` is Borel in the output and the internal variables (§5) -/
  Kt_meas : ∀ a w hv, Measurable fun p : OutT N R a (0 + 1) × NewCfg N a 0 => Kt a w p.1 p.2 hv
  /-- `K̃^w_0` is independent of `ψ_1` on `Ω^c`: only `A_c(u)` reads it (§5, first paragraph) -/
  Kt_outside : ∀ a w o o' x hv,
    (∀ y : Vblk R a (0 + 1), y.1 ∉ gaussBlocks a 0 → o y = o' y) →
    Kt a w o x hv = Kt a w o' x hv
  /-- `K̃^w_0` vanishes off `χ^new_0` (§1 last paragraph: `chiNew` supplies the support condition) -/
  Kt_dom : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (Z' : H.Comp (0 + 1))
    (w : BaseW (H.localHistory M K (0 + 1) Z') 0) o x hv,
    ¬ ChiNewAt geo cs H 0 Z' o x → Kt (H.localHistory M K (0 + 1) Z') w o x hv = 0
  /-- `O(N)`-covariance of `K̃^w_0` (§5 (S5)(i)) -/
  Kt_rot : ∀ a w (ρ : OrthN N) o x hv,
    Kt a w (rotOut ρ o) (rotSub ρ x) (ρ hv) = Kt a w o x hv
  /-- Euclidean covariance of the kernel `K_0 = ∏ z_1^N t_0 · ∑_w F^w_0 K̃^w_0` (§5: Lemma I.3.9
  and the local-covariance core equality give (S4)) -/
  euclid_K : ∀ (σ : TorusSym S n M K) (a a' : LocalHistory S n M K) (hI : HistImage σ a a')
    (hk : 0 + 1 ≤ K) o o' x x' hv, RelOut σ o o' → RelSub hI hk x x' →
    gaussProd N a' 0 cs o' x' *
        baseSumOf cs a' (fun w => Kt a' w) o' x' hv =
      gaussProd N a 0 cs o x * baseSumOf cs a (fun w => Kt a w) o x hv
  /-- `b_0` is Borel (§3) -/
  b0_meas : ∀ a hv g, Measurable fun p : OutT N R a (0 + 1) × NewCfg N a 0 => b0 a p.1 p.2 hv g
  /-- `b_0` is analytic in `g` on the `ℓ¹` unit ball (§3, joint H7 analyticity) -/
  b0_analytic : ∀ a o x hv, AnalyticOnNhd ℂ (b0 a o x hv) (l1Ball (GIdx S n M K N))
  /-- `b_0` is real for real arguments (§3) -/
  b0_real : ∀ a o x hv g, g ∈ l1Ball (GIdx S n M K N) → (∀ i, (g i).im = 0) →
    (b0 a o x hv g).im = 0
  /-- `b_0` depends on `g` only through `g|_V` (§3 "retained source ... support") -/
  b0_supp : ∀ a o x hv (g g' : GIdx S n M K N → ℂ),
    (∀ i : GIdx S n M K N, i.1 ∈ Vsites R a (0 + 1) → g i = g' i) → b0 a o x hv g = b0 a o x hv g'
  /-- `O(N)`-covariance of `b_0` (§3, §5) -/
  b0_rot : ∀ a (ρ : OrthN N) o x hv g,
    b0 a (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) = b0 a o x hv g
  /-- Euclidean covariance of `b_0` (§3) -/
  euclid_b : ∀ (σ : TorusSym S n M K) (a a' : LocalHistory S n M K) (hI : HistImage σ a a')
    (hk : 0 + 1 ≤ K) o o' x x' hv g g', RelOut σ o o' → RelSub hI hk x x' → RelG σ g g' →
    b0 a' o' x' hv g' = b0 a o x hv g
  /-- the source-independent bound `|b_0| ≤ (C_b log β + C_b B_0) |X|_1` on the localized H7 domain
  (§3, the `SF` row: "requires the uniform analytic estimate") -/
  b0_bound : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (Z' : H.Comp (0 + 1)) o x hv
    (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) → ChiNewAt geo cs H 0 Z' o x →
    ‖b0 (H.localHistory M K (0 + 1) Z') o x hv g‖ ≤
      (cs.Cb * Real.log (cs.beta 0) + cs.Cb * cs.B0) *
        volScale S (0 + 1) {z | z ∈ (H.localHistory M K (0 + 1) Z').Z (0 + 1) ∧
          z ∉ (H.localHistory M K (0 + 1) Z').Z 0}

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

theorem baseSumOf_rot (cs : OpConsts) (a : LocalHistory S n M K)
    {Kt : BaseW a 0 → OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → ℝ}
    (hKt : ∀ w (ρ : OrthN N) o x hv, Kt w (rotOut ρ o) (rotSub ρ x) (ρ hv) = Kt w o x hv)
    (ρ : OrthN N) (o : OutT N R a (0 + 1)) (x : NewCfg N a 0) (hv : EuclideanSpace ℝ (Fin N)) :
    baseSumOf cs a Kt (rotOut ρ o) (rotSub ρ x) (ρ hv) = baseSumOf cs a Kt o x hv := by
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

variable {k0 : ℕ} {geo : Geo S n R M} {cs : OpConsts}

/-- **The base kernel `(K_0, b_0)`** of BASE-KERNEL §§1-3 at the localized history `a`, as a
large-field kernel: `K_0 = ∏_y z_1^N t_0 · ∑_w F^w_0(u) K̃^w_0` (1.1) and the boundary exponent
`b_0`, with `K̃^w_0`, `b_0` taken from the small-field input.  `hz`, `hc` are the signs of the
running constants (`z_1 ≥ 0`, `β_0 a L^{d-2} ≥ 0`). -/
noncomputable def baseKernel_of_input (inp : BaseSmallFieldInput K k0 geo cs N)
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (a : LocalHistory S n M K) :
    LFKernel (OutT N R a (0 + 1)) (NewCfg N a 0) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N) where
  K o x hv := gaussProd N a 0 cs o x * baseSumOf cs a (fun w => inp.Kt a w) o x hv
  b := inp.b0 a
  K_nonneg o x hv := mul_nonneg (gaussProd_nonneg N a 0 cs hz hc o x)
    (baseSumOf_nonneg cs a (fun w o x hv => inp.Kt_nonneg a w o x hv) o x hv)
  measurable_K hv :=
    (measurable_gaussProd_pair a 0 cs).mul
      (measurable_baseSumOf cs a (fun w hv => inp.Kt_meas a w hv) hv)
  measurable_b hv g := inp.b0_meas a hv g
  analytic_b o x hv := inp.b0_analytic a o x hv
  real_b o x hv g := inp.b0_real a o x hv g

/-- **The base boundary exponent `b_0`** (BASE-KERNEL §3). -/
noncomputable def baseBoundary_of_input (inp : BaseSmallFieldInput K k0 geo cs N)
    (a : LocalHistory S n M K) :
    OutT N R a (0 + 1) → NewCfg N a 0 → EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → ℂ :=
  inp.b0 a

/-- The Gaussian witnesses of (S1) at `k = 0`: `W = {blk, bd}^{P_1 ∩ Z'}`, `F^w_0 = baseF`,
`K̃^w_0` from the input. -/
noncomputable def baseWit_of_input (inp : BaseSmallFieldInput K k0 geo cs N)
    (a : LocalHistory S n M K) : GaussWit N R a 0 :=
  open Classical in
  { W := BaseW a 0
    F := fun w u => baseF a 0 (cs.delta 0) w u
    Kt := fun w o x hv => inp.Kt a w o x hv }

theorem baseKernel_K_eq (inp : BaseSmallFieldInput K k0 geo cs N)
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (a : LocalHistory S n M K) (o : OutT N R a (0 + 1)) (x : NewCfg N a 0)
    (hv : EuclideanSpace ℝ (Fin N)) :
    (baseKernel_of_input inp hz hc a).K o x hv = gaussProd N a 0 cs o x *
      ∑ w, (baseWit_of_input inp a).F w
        (fun y => gaussArg N (cs.z (0 + 1)) o x y.1) * (baseWit_of_input inp a).Kt w o x hv := by
  classical
  rfl

/-! ### The first five clauses of `GaussStepSpec`: the Gaussian structure (S1) -/

/-- The Gaussian structure (S1) of version 1.2, i.e. the first five clauses of `GaussStepSpec`
(`0 ≤ F^w ≤ 1`, `F^w` Borel, `K̃^w ≥ 0`, `K̃^w` independent of `ψ_{k+1}` off the Gaussian blocks,
and `K = ∏ z^N t_k · ∑_w F^w K̃^w`); the clause (S2) is the existential tail of `GaussStepSpec`. -/
def GaussStructure (cs : OpConsts) (a : LocalHistory S n M K) (k : ℕ)
    (T : LFKernel (OutT N R a (k + 1)) (NewCfg N a k) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N))
    (wit : GaussWit N R a k) : Prop :=
  (∀ w u, 0 ≤ wit.F w u ∧ wit.F w u ≤ 1) ∧
  (∀ w, Measurable (wit.F w)) ∧
  (∀ w o x hv, 0 ≤ wit.Kt w o x hv) ∧
  (∀ w o o' x hv, (∀ y : Vblk R a (k + 1), y.1 ∉ gaussBlocks a k → o y = o' y) →
    wit.Kt w o x hv = wit.Kt w o' x hv) ∧
  (∀ o x hv, T.K o x hv = gaussProd N a k cs o x *
    ∑ w, wit.F w (fun y => gaussArg N (cs.z (k + 1)) o x y.1) * wit.Kt w o x hv)


theorem baseKernel_gaussStructure_of_input (inp : BaseSmallFieldInput K k0 geo cs N)
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (a : LocalHistory S n M K) :
    GaussStructure cs a 0 (baseKernel_of_input inp hz hc a) (baseWit_of_input inp a) := by
  classical
  refine ⟨fun w u => baseF_mem_unit a 0 _ w u, fun w => measurable_baseF a 0 _ w,
    fun w o x hv => inp.Kt_nonneg a w o x hv, fun w o o' x hv h => inp.Kt_outside a w o o' x hv h,
    fun o x hv => baseKernel_K_eq inp hz hc a o x hv⟩

/-! ### The `k = 0` slice of the step data -/

variable (K) in
/-- The base step data: the `k = 0` slice of `StepData` (Definition II.5.7 (S0), (S1); (S4) holds
because the data are indexed by the localized history `a`).  The one-step bound (S2) is the
separate target `BaseStepData.S2`; (S3) is empty at scale one (`base_not_quiet`, Lemma II.7.2 (c));
(S5) is the separate target `BaseS5`. -/
structure BaseStepData (k0 : ℕ) (geo : Geo S n R M) (cs : OpConsts) (N : ℕ) where
  /-- the step kernel `(K_0, b_0)(Z', a)` -/
  ker : ∀ a : LocalHistory S n M K,
    LFKernel (OutT N R a (0 + 1)) (NewCfg N a 0) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N)
  /-- the Gaussian witnesses of (S1) -/
  wit : ∀ a : LocalHistory S n M K, GaussWit N R a 0
  /-- (S0) `b_0` depends on `g` only through `g|_V` -/
  b_supp : ∀ a o x hv (g g' : GIdx S n M K N → ℂ),
    (∀ i : GIdx S n M K N, i.1 ∈ Vsites R a (0 + 1) → g i = g' i) →
      (ker a).b o x hv g = (ker a).b o x hv g'
  /-- (S0)/(S1) `O(N)`-covariance of the kernel -/
  rot_K : ∀ a (ρ : OrthN N) o x hv,
    (ker a).K (rotOut ρ o) (rotSub ρ x) (ρ hv) = (ker a).K o x hv
  /-- (S0) `O(N)`-covariance of the boundary factor -/
  rot_b : ∀ a (ρ : OrthN N) o x hv g,
    (ker a).b (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) = (ker a).b o x hv g
  /-- (S0)/(S1) Euclidean covariance of the kernel -/
  euclid_K : ∀ (σ : TorusSym S n M K) (a a' : LocalHistory S n M K) (hI : HistImage σ a a')
    (hk : 0 + 1 ≤ K) o o' x x' hv, RelOut σ o o' → RelSub hI hk x x' →
    (ker a').K o' x' hv = (ker a).K o x hv
  /-- (S0) Euclidean covariance of the boundary factor -/
  euclid_b : ∀ (σ : TorusSym S n M K) (a a' : LocalHistory S n M K) (hI : HistImage σ a a')
    (hk : 0 + 1 ≤ K) o o' x x' hv g g', RelOut σ o o' → RelSub hI hk x x' → RelG σ g g' →
      (ker a').b o' x' hv g' = (ker a).b o x hv g
  /-- (S0) the bound on `b_0` on the domain -/
  b_bound : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (Z' : H.Comp (0 + 1)) o x hv
    (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) → ChiNewAt geo cs H 0 Z' o x →
    ‖(ker (H.localHistory M K (0 + 1) Z')).b o x hv g‖ ≤
      (cs.Cb * Real.log (cs.beta 0) + cs.Cb * cs.B0) *
        volScale S (0 + 1) {z | z ∈ (H.localHistory M K (0 + 1) Z').Z (0 + 1) ∧
          z ∉ (H.localHistory M K (0 + 1) Z').Z 0}
  /-- (S1) the kernel vanishes off the new part `χ^new_0` of the domain -/
  dom : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (Z' : H.Comp (0 + 1)) o x hv,
    ¬ ChiNewAt geo cs H 0 Z' o x → (ker (H.localHistory M K (0 + 1) Z')).K o x hv = 0
  /-- (S1) the Gaussian structure -/
  gauss1 : ∀ a, GaussStructure cs a 0 (ker a) (wit a)

/-- **The base step data** (BASE-KERNEL §§1-3, §5): (S0), (S1), (S4) at `k = 0`, conditional on the
small-field input. -/
noncomputable def baseStepData_of_input (inp : BaseSmallFieldInput K k0 geo cs N)
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) :
    BaseStepData K k0 geo cs N where
  ker := baseKernel_of_input inp hz hc
  wit := baseWit_of_input inp
  b_supp := fun a o x hv g g' h => inp.b0_supp a o x hv g g' h
  rot_K := fun a ρ o x hv => by
    show gaussProd N a 0 cs (rotOut ρ o) (rotSub ρ x) *
        baseSumOf cs a (fun w => inp.Kt a w) (rotOut ρ o) (rotSub ρ x) (ρ hv) =
      gaussProd N a 0 cs o x * baseSumOf cs a (fun w => inp.Kt a w) o x hv
    rw [gaussProd_rot, baseSumOf_rot cs a (fun w ρ o x hv => inp.Kt_rot a w ρ o x hv)]
  rot_b := fun a ρ o x hv g => inp.b0_rot a ρ o x hv g
  euclid_K := fun σ a a' hI hk o o' x x' hv ho hx => inp.euclid_K σ a a' hI hk o o' x x' hv ho hx
  euclid_b := fun σ a a' hI hk o o' x x' hv g g' ho hx hg =>
    inp.euclid_b σ a a' hI hk o o' x x' hv g g' ho hx hg
  b_bound := fun H hH Z' o x hv g hg hc' => inp.b0_bound H hH Z' o x hv g hg hc'
  dom := fun H hH Z' o x hv hn => by
    show gaussProd N _ 0 cs o x * baseSumOf cs _ (fun w => inp.Kt _ w) o x hv = 0
    have : baseSumOf cs (H.localHistory M K (0 + 1) Z') (fun w => inp.Kt _ w) o x hv = 0 := by
      classical
      unfold baseSumOf
      exact Finset.sum_eq_zero fun w _ => by
        have h := inp.Kt_dom H hH Z' w o x hv hn
        simp only [h, mul_zero]
    rw [this, mul_zero]
  gauss1 := fun a => baseKernel_gaussStructure_of_input inp hz hc a

/-- **The one-step bound (S2) at `k = 0`** (Lemma II.7.8) with exponent `κ0` for the base step
data: the full `GaussStepSpec` for every admissible region history and component. -/
def BaseStepData.S2 (D : BaseStepData K k0 geo cs N) (κ0 : LocalHistory S n M K → ℝ) : Prop :=
  ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (Z' : H.Comp (0 + 1)),
    GaussStepSpec cs R (H.localHistory M K (0 + 1) Z') 0 (κ0 (H.localHistory M K (0 + 1) Z'))
      (D.ker (H.localHistory M K (0 + 1) Z')) (D.wit (H.localHistory M K (0 + 1) Z'))

/-! ### Inhabitation -/

/-- **Inhabitation of `BaseSmallFieldInput`**: the zero remainder and the zero boundary exponent
satisfy every field, for constants with `0 ≤ C_b`, `0 ≤ B_0`, `1 ≤ β_0` (so that the bound's right
side is non-negative). -/
theorem baseSmallFieldInput_nonempty (geo : Geo S n R M) (cs : OpConsts) (N k0 : ℕ)
    (hCb : 0 ≤ cs.Cb) (hB0 : 0 ≤ cs.B0) (hβ : 1 ≤ cs.beta 0) :
    Nonempty (BaseSmallFieldInput K k0 geo cs N) := by
  have hlog : 0 ≤ Real.log (cs.beta 0) := Real.log_nonneg hβ
  refine ⟨{ Kt := fun _ _ _ _ _ => 0
            b0 := fun _ _ _ _ _ => 0
            Kt_nonneg := ?_
            Kt_meas := ?_
            Kt_outside := ?_
            Kt_dom := ?_
            Kt_rot := ?_
            euclid_K := ?_
            b0_meas := ?_
            b0_analytic := ?_
            b0_real := ?_
            b0_supp := ?_
            b0_rot := ?_
            euclid_b := ?_
            b0_bound := ?_ }⟩
  · intros; exact le_rfl
  · intros; exact measurable_const
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro σ a a' hI hk o o' x x' hv ho hx
    classical
    simp [baseSumOf]
  · intros; exact measurable_const
  · intro a o x hv g _
    exact (analyticAt_const : AnalyticAt ℂ (fun _ : GIdx S n M K N → ℂ => (0 : ℂ)) g)
  · intros; simp
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro H hH Z' o x hv g hg hc
    simp only [norm_zero]
    have : 0 ≤ volScale S (0 + 1) {z | z ∈ (H.localHistory M K (0 + 1) Z').Z (0 + 1) ∧
          z ∉ (H.localHistory M K (0 + 1) Z').Z 0} := by
      unfold volScale; positivity
    positivity

end Input

end Balaban.LargeField
