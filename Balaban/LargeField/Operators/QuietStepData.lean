module

public import Balaban.LargeField.Operators.QuietBound
public import Balaban.LargeField.Operators.QuietSymm
public import Balaban.LargeField.Operators.StepData
public import Balaban.LargeField.Operators.LocOpBound

/-!
# Step data of the quiet steps (Part II, Definition II.5.7 (S0)-(S2), Lemma II.5.14)

`StepData` indexes the step kernel `(K_k, b_k)` by the localized history `a` of a component
(property (S4) of the source: the history enters only through `a`).  The landed quiet kernel
`quietKernel` is indexed by the region history `H` and the component `Z'`.  This file assembles,
from the landed results, the `StepData` fields at the quiet steps:

* `QuietStepInput`: the single structure with the facts that tie the `a`-indexed objects to the
  `H`-indexed quiet kernel (locality (S4) of quietness and of the quiet kernel, the lattice
  covariance between localized histories related by a `HistImage`, the Borel measurability of the
  kernel) and the boundary exponent `b_k` of the source (P6 (3.4)-(3.9)) with its properties (S0);
  `quietStepInput_nonempty` is its inhabitation witness;
* `quietKer`: the large-field kernel of a quiet step (the quiet kernel, `0` off the localized
  histories of quiet steps);
* `quietStepData`: the `StepData` with `ker = quietKer`, whose fields `quiet`, `dom`, `gauss`
  (via `quietKernel_bound`), `rot_K` (via `quietKernel_rot`) are proved from the landed results.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal

section Input

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The localized history `a` is that of a quiet step `k → k + 1` (`1 ≤ k`) of a component of an
admissible region history. -/
def QuietRealized (R : ℕ → ℝ) (k0 : ℕ) (k : ℕ) (a : LocalHistory S n M K) : Prop :=
  ∃ H : RegionHistory S n R k0 K, H.Admissible ∧ ∃ Z' : H.Comp (k + 1), 1 ≤ k ∧ k + 1 ≤ K ∧
    IsQuiet (H.locRH (k + 1) Z') k Z'.1 ∧ H.localHistory M K (k + 1) Z' = a

theorem QuietRealized.le {R : ℕ → ℝ} {k0 k : ℕ} {a : LocalHistory S n M K}
    (h : QuietRealized R k0 k a) : k + 1 ≤ K := by
  obtain ⟨H, -, Z', -, hk, -⟩ := h
  exact hk

variable {k0 : ℕ}

variable (K) in
/-- **The input of the quiet step data.**  `Rq k a` is the quiet kernel without its Gaussian factor
(`quietRest`) as a function of the localized history `a`, and `b k a` the boundary exponent of the
quiet step, with the properties (S0) of Definition II.5.7.

* `not_quiet_zero`: the step `0 → 1` is not quiet (every component of `Z^pre_1` contains a new
  cube; Lemma II.7.2 (c));
* `quiet_local`: quietness of a step is a property of the localized history (S4);
* `Rq_eq`: `Rq` is `quietRest` at the quiet steps (S4 for the quiet kernel, Lemma I.3.9);
* `K_meas`, `b_meas`, `b_analytic`, `b_real`: the kernel is Borel and `b` is analytic and real
  (typing of an `LFKernel`);
* `real_euclid`, `euclid_K`, `euclid_b`: lattice covariance (Lemma II.5.10) between localized
  histories related by a symmetry;
* `b_supp`, `b_rot`, `b_bound`: (S0) for `b`. -/
structure QuietStepInput (k0 : ℕ) (geo : Geo S n R M) (cs : OpConsts) (N : ℕ) where
  not_quiet_zero : ∀ H : RegionHistory S n R k0 K, H.Admissible → ∀ Z' : H.Comp 1, 1 ≤ K →
    ¬ IsQuiet (H.locRH 1 Z') 0 Z'.1
  quiet_local : ∀ (H H' : RegionHistory S n R k0 K), H.Admissible → H'.Admissible →
    ∀ (k : ℕ) (Z' : H.Comp (k + 1)) (Z'' : H'.Comp (k + 1)), 1 ≤ k → k + 1 ≤ K →
    H.localHistory M K (k + 1) Z' = H'.localHistory M K (k + 1) Z'' →
    IsQuiet (H.locRH (k + 1) Z') k Z'.1 → IsQuiet (H'.locRH (k + 1) Z'') k Z''.1
  Rq : ∀ (k : ℕ) (a : LocalHistory S n M K), OutT N R a (k + 1) → NewCfg N a k →
    EuclideanSpace ℝ (Fin N) → ℝ
  Rq_eq : ∀ H : RegionHistory S n R k0 K, H.Admissible → ∀ (k : ℕ) (hk : k + 1 ≤ K),
    1 ≤ k → ∀ Z' : H.Comp (k + 1), IsQuiet (H.locRH (k + 1) Z') k Z'.1 →
    ∀ o x hv, Rq k (H.localHistory M K (k + 1) Z') o x hv =
      quietRest geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
        (locRH_rem (k + 1) Z') o x hv
  K_meas : ∀ (k : ℕ) (a : LocalHistory S n M K) (hv : EuclideanSpace ℝ (Fin N)),
    QuietRealized R k0 k a →
    Measurable fun p : OutT N R a (k + 1) × NewCfg N a k =>
      gaussProd N a k cs p.1 p.2 * Rq k a p.1 p.2 hv
  real_euclid : ∀ (k : ℕ) (σ : TorusSym S n M K) (a a' : LocalHistory S n M K),
    HistImage σ a a' → (QuietRealized R k0 k a ↔ QuietRealized R k0 k a')
  euclid_K : ∀ (k : ℕ) (σ : TorusSym S n M K) (a a' : LocalHistory S n M K)
    (hI : HistImage σ a a') (hk : k + 1 ≤ K) o o' x x' hv, QuietRealized R k0 k a →
    RelOut σ o o' → RelSub hI hk x x' →
    gaussProd N a' k cs o' x' * Rq k a' o' x' hv = gaussProd N a k cs o x * Rq k a o x hv
  b : ∀ (k : ℕ) (a : LocalHistory S n M K), OutT N R a (k + 1) → NewCfg N a k →
    EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → ℂ
  b_meas : ∀ k a hv g, QuietRealized R k0 k a →
    Measurable fun p : OutT N R a (k + 1) × NewCfg N a k => b k a p.1 p.2 hv g
  b_analytic : ∀ k a o x hv, QuietRealized R k0 k a →
    AnalyticOnNhd ℂ (b k a o x hv) (l1Ball (GIdx S n M K N))
  b_real : ∀ k a o x hv g, QuietRealized R k0 k a → g ∈ l1Ball (GIdx S n M K N) →
    (∀ i, (g i).im = 0) → (b k a o x hv g).im = 0
  b_supp : ∀ k a o x hv (g g' : GIdx S n M K N → ℂ), QuietRealized R k0 k a →
    (∀ i : GIdx S n M K N, i.1 ∈ Vsites R a (k + 1) → g i = g' i) →
      b k a o x hv g = b k a o x hv g'
  b_rot : ∀ k a (ρ : OrthN N) o x hv g, QuietRealized R k0 k a →
    b k a (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) = b k a o x hv g
  b_euclid : ∀ (k : ℕ) (σ : TorusSym S n M K) (a a' : LocalHistory S n M K)
    (hI : HistImage σ a a') (hk : k + 1 ≤ K) o o' x x' hv g g', QuietRealized R k0 k a →
    RelOut σ o o' → RelSub hI hk x x' → RelG σ g g' → b k a' o' x' hv g' = b k a o x hv g
  b_bound : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (k : ℕ), k + 1 ≤ K →
    1 ≤ k → ∀ (Z' : H.Comp (k + 1)), IsQuiet (H.locRH (k + 1) Z') k Z'.1 →
    ∀ o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
    ChiNewAt geo cs H k Z' o x →
    ‖b k (H.localHistory M K (k + 1) Z') o x hv g‖ ≤
      (cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
        volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
          z ∉ (H.localHistory M K (k + 1) Z').Z k}

end Input

section Ker

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {k0 : ℕ}

variable {geo : Geo S n R M} {cs : OpConsts}

open Classical in
/-- **The large-field kernel of a quiet step** `(K_k, b_k)(Z', a)`: the quiet kernel
`∏ z^N t_k · K̃` and the boundary exponent of the input at the localized histories `a` of quiet
steps, and `0` at every other `a`. -/
noncomputable def quietKer (inp : QuietStepInput K k0 geo cs N)
    (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hβ : ∀ k, 0 ≤ cs.beta (k + 1)) (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct (k + 1))
    (k : ℕ) (a : LocalHistory S n M K) :
    LFKernel (OutT N R a (k + 1)) (NewCfg N a k) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N) where
  K o x hv := if QuietRealized R k0 k a then gaussProd N a k cs o x * inp.Rq k a o x hv else 0
  b o x hv g := if QuietRealized R k0 k a then inp.b k a o x hv g else 0
  K_nonneg o x hv := by
    by_cases hr : QuietRealized R k0 k a
    · simp only [hr, ↓reduceIte]
      obtain ⟨H, hH, Z', hk1, hk, hq, rfl⟩ := hr
      rw [inp.Rq_eq H hH k hk hk1 Z' hq]
      exact mul_nonneg (gaussProd_nonneg N _ k cs (hz k) (hc k) o x)
        (quietRest_unit geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
          (locRH_rem (k + 1) Z') (hβ k) haw (hμ k) o x hv).1
    · simp only [hr, ↓reduceIte]; exact le_rfl
  measurable_K hv := by
    by_cases hr : QuietRealized R k0 k a
    · simp only [hr, ↓reduceIte]
      exact inp.K_meas k a hv hr
    · simp only [hr, ↓reduceIte]
      exact measurable_const
  measurable_b hv g := by
    by_cases hr : QuietRealized R k0 k a
    · simp only [hr, ↓reduceIte]
      exact inp.b_meas k a hv g hr
    · simp only [hr, ↓reduceIte]
      exact measurable_const
  analytic_b o x hv := by
    by_cases hr : QuietRealized R k0 k a
    · simp only [hr, ↓reduceIte]
      exact inp.b_analytic k a o x hv hr
    · simp only [hr, ↓reduceIte]
      exact analyticOnNhd_const
  real_b o x hv g hg hgr := by
    by_cases hr : QuietRealized R k0 k a
    · simp only [hr, ↓reduceIte]
      exact inp.b_real k a o x hv g hr hg hgr
    · simp only [hr, ↓reduceIte]
      simp

theorem quietKer_K (inp : QuietStepInput K k0 geo cs N)
    (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hβ : ∀ k, 0 ≤ cs.beta (k + 1)) (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct (k + 1))
    (k : ℕ) (a : LocalHistory S n M K) (o : OutT N R a (k + 1)) (x : NewCfg N a k)
    (hv : EuclideanSpace ℝ (Fin N)) :
    (quietKer inp hz hc hβ haw hμ k a).K o x hv =
      open Classical in
      if QuietRealized R k0 k a then gaussProd N a k cs o x * inp.Rq k a o x hv else 0 := rfl

theorem quietKer_b (inp : QuietStepInput K k0 geo cs N)
    (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hβ : ∀ k, 0 ≤ cs.beta (k + 1)) (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct (k + 1))
    (k : ℕ) (a : LocalHistory S n M K) (o : OutT N R a (k + 1)) (x : NewCfg N a k)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) :
    (quietKer inp hz hc hβ haw hμ k a).b o x hv g =
      open Classical in
      if QuietRealized R k0 k a then inp.b k a o x hv g else 0 := rfl

/-- On the localized history of a quiet step, the kernel `quietKer` is the quiet kernel. -/
theorem quietKer_K_quiet (inp : QuietStepInput K k0 geo cs N)
    (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hβ : ∀ k, 0 ≤ cs.beta (k + 1)) (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct (k + 1))
    (H : RegionHistory S n R k0 K) (hH : H.Admissible) (k : ℕ) (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (Z' : H.Comp (k + 1)) (hq : IsQuiet (H.locRH (k + 1) Z') k Z'.1)
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N)) :
    (quietKer inp hz hc hβ haw hμ k (H.localHistory M K (k + 1) Z')).K o x hv =
      quietKernel geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
        (locRH_rem (k + 1) Z') o x hv := by
  classical
  have hr : QuietRealized R k0 k (H.localHistory M K (k + 1) Z') := ⟨H, hH, Z', hk1, hk, hq, rfl⟩
  rw [quietKer_K]
  simp only [hr, ↓reduceIte]
  rw [inp.Rq_eq H hH k hk hk1 Z' hq]
  exact (quietKernel_eq geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
    (locRH_rem (k + 1) Z') o x hv).symm

end Ker

section Gauss

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {k0 : ℕ} {geo : Geo S n R M} {cs : OpConsts}

/-- The step exponent of the quiet steps,
`κ^{(k)} = -(c₁ log β_k + c₂) |Z^c_k ∩ Z'|_{k+1}` (Lemma II.5.14). -/
noncomputable def quietKappaStep (cs : OpConsts) (c1 c2 : ℝ) (k : ℕ) (a : LocalHistory S n M K) :
    ℝ :=
  -(c1 * Real.log (cs.beta k) + c2) * volScale S (k + 1) {z | z ∈ a.Z (k + 1) ∧ z ∉ a.Z k}

/-- The witnesses of the Gaussian structure at a localized history that is not that of a quiet
step: `W = {*}`, `F ≡ 1`, `K̃ = 0`. -/
def zeroWit (N : ℕ) (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ) : GaussWit N R a k where
  W := Unit
  F := fun _ _ => 1
  Kt := fun _ _ _ _ => 0

theorem gaussSpec_zero (cs : OpConsts) (a : LocalHistory S n M K) (k : ℕ) (κ : ℝ)
    (T : LFKernel (OutT N R a (k + 1)) (NewCfg N a k) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N))
    (hK : ∀ o x hv, T.K o x hv = 0) :
    GaussStepSpec cs R a k κ T (zeroWit N R a k) := by
  refine ⟨fun _ _ => ⟨zero_le_one, le_rfl⟩, fun _ => measurable_const, fun _ _ _ _ => le_rfl,
    fun _ _ _ _ _ _ => rfl, fun o x hv => ?_, ?_⟩
  · rw [hK]
    simp [zeroWit]
  · refine ⟨fun _ _ _ _ _ _ => 0, fun _ _ _ _ => measurable_const, ?_, ?_⟩
    · intro w o x hv g hg
      simp [zeroWit]
    · intro par hv g hg
      simp

theorem quietKer_gauss_exists [NeZero N] (inp : QuietStepInput K k0 geo cs N)
    (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hβ : ∀ k, 0 ≤ cs.beta (k + 1)) (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct (k + 1))
    (hN : 2 ≤ N) (c1 c2 : ℝ) (hc1 : cs.Cb ≤ c1) (hc2 : cs.Cb * cs.B0 ≤ c2)
    (hlog : ∀ k, 0 ≤ Real.log (cs.beta k))
    (hcpos : ∀ k, 0 < cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hδ : ∀ k, 0 < cs.delta k) (hδ1 : ∀ k, 3 * S.d * S.L * cs.delta k ≤ 1 / 2)
    (hΛ : ∀ k, 3 * S.d * S.L * cShell N * cs.delta k ≤ 1 / 2)
    (k : ℕ) (a : LocalHistory S n M K) (hr : QuietRealized R k0 k a) :
    ∃ wit : GaussWit N R a k, GaussStepSpec cs R a k (quietKappaStep cs c1 c2 k a)
      (quietKer inp hz hc hβ haw hμ k a) wit := by
  obtain ⟨H, hH, Z', hk1, hk, hq, rfl⟩ := hr
  exact quietKernel_bound geo cs hN hk1 hk Z' hq (quietKer inp hz hc hβ haw hμ k _)
    (fun o x hv => quietKer_K_quiet inp hz hc hβ haw hμ H hH k hk hk1 Z' hq o x hv)
    (fun o x hv g hg hchi => by
      have hr : QuietRealized R k0 k (H.localHistory M K (k + 1) Z') :=
        ⟨H, hH, Z', hk1, hk, hq, rfl⟩
      rw [quietKer_b]
      simp only [hr, ↓reduceIte]
      exact inp.b_bound H hH k hk hk1 Z' hq o x hv g hg hchi)
    c1 c2 hc1 hc2 (hlog k) (hcpos k) (hδ k) (hδ1 k) (hΛ k) (hβ k) haw (hμ k)

open Classical in
/-- The Gaussian witnesses of the quiet steps: those of `quietKernel_bound` at the localized
histories of quiet steps, `zeroWit` elsewhere. -/
noncomputable def quietWit [NeZero N] (inp : QuietStepInput K k0 geo cs N)
    (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hβ : ∀ k, 0 ≤ cs.beta (k + 1)) (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct (k + 1))
    (hN : 2 ≤ N) (c1 c2 : ℝ) (hc1 : cs.Cb ≤ c1) (hc2 : cs.Cb * cs.B0 ≤ c2)
    (hlog : ∀ k, 0 ≤ Real.log (cs.beta k))
    (hcpos : ∀ k, 0 < cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hδ : ∀ k, 0 < cs.delta k) (hδ1 : ∀ k, 3 * S.d * S.L * cs.delta k ≤ 1 / 2)
    (hΛ : ∀ k, 3 * S.d * S.L * cShell N * cs.delta k ≤ 1 / 2)
    (k : ℕ) (a : LocalHistory S n M K) : GaussWit N R a k :=
  if hr : QuietRealized R k0 k a then
    Classical.choose (quietKer_gauss_exists inp hz hc hβ haw hμ hN c1 c2 hc1 hc2 hlog hcpos hδ hδ1
      hΛ k a hr)
  else zeroWit N R a k

end Gauss

section Assemble

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {k0 : ℕ} {geo : Geo S n R M} {cs : OpConsts}

open Classical in
/-- **The step data of the quiet steps** (Definition II.5.7 (S0)-(S2)): the kernel `quietKer`,
the witnesses `quietWit`, the exponent `κ^{(k)} = -(c₁ log β_k + c₂)|Z^c_k ∩ Z'|_{k+1}`.  The
fields `quiet`, `dom`, `gauss` and `rot_K` are proved from `quietKernel`, `quietRest_eq_zero`,
`quietKernel_bound` and `quietKernel_rot`; at the localized histories that are not those of
quiet steps the kernel is `0`. -/
noncomputable def quietStepData [NeZero N] (inp : QuietStepInput K k0 geo cs N)
    (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hβ : ∀ k, 0 ≤ cs.beta (k + 1)) (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct (k + 1))
    (hN : 2 ≤ N) (c1 c2 : ℝ) (hc1 : cs.Cb ≤ c1) (hc2 : cs.Cb * cs.B0 ≤ c2)
    (hlog : ∀ k, 0 ≤ Real.log (cs.beta k))
    (hcpos : ∀ k, 0 < cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hδ : ∀ k, 0 < cs.delta k) (hδ1 : ∀ k, 3 * S.d * S.L * cs.delta k ≤ 1 / 2)
    (hΛ : ∀ k, 3 * S.d * S.L * cShell N * cs.delta k ≤ 1 / 2)
    (hCb : 0 ≤ cs.Cb) (hB0 : 0 ≤ cs.B0) :
    StepData k0 geo cs N (quietKappaStep (K := K) cs c1 c2) where
  ker := quietKer inp hz hc hβ haw hμ
  wit := quietWit inp hz hc hβ haw hμ hN c1 c2 hc1 hc2 hlog hcpos hδ hδ1 hΛ
  b_supp k a o x hv g g' hgg := by
    rw [quietKer_b, quietKer_b]
    by_cases hr : QuietRealized R k0 k a
    · simp only [hr, ↓reduceIte]
      exact inp.b_supp k a o x hv g g' hr hgg
    · simp only [hr, ↓reduceIte]
  rot_K k a ρ o x hv := by
    by_cases hr : QuietRealized R k0 k a
    · obtain ⟨H, hH, Z', hk1, hk, hq, rfl⟩ := hr
      rw [quietKer_K_quiet inp hz hc hβ haw hμ H hH k hk hk1 Z' hq,
        quietKer_K_quiet inp hz hc hβ haw hμ H hH k hk hk1 Z' hq]
      exact quietKernel_rot geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
        (locRH_rem (k + 1) Z') ρ o x hv
    · rw [quietKer_K, quietKer_K]
      simp only [hr, ↓reduceIte]
  rot_b k a ρ o x hv g := by
    rw [quietKer_b, quietKer_b]
    by_cases hr : QuietRealized R k0 k a
    · simp only [hr, ↓reduceIte]
      exact inp.b_rot k a ρ o x hv g hr
    · simp only [hr, ↓reduceIte]
  euclid_K k σ a a' hI hk o o' x x' hv ho hx := by
    rw [quietKer_K, quietKer_K]
    have hiff := inp.real_euclid k σ a a' hI
    by_cases hr : QuietRealized R k0 k a
    · have hr' := hiff.1 hr
      simp only [hr, hr', ↓reduceIte]
      exact inp.euclid_K k σ a a' hI hk o o' x x' hv hr ho hx
    · have hr' : ¬ QuietRealized R k0 k a' := fun h => hr (hiff.2 h)
      simp only [hr, hr', ↓reduceIte]
  euclid_b k σ a a' hI hk o o' x x' hv g g' ho hx hg := by
    rw [quietKer_b, quietKer_b]
    have hiff := inp.real_euclid k σ a a' hI
    by_cases hr : QuietRealized R k0 k a
    · have hr' := hiff.1 hr
      simp only [hr, hr', ↓reduceIte]
      exact inp.b_euclid k σ a a' hI hk o o' x x' hv g g' hr ho hx hg
    · have hr' : ¬ QuietRealized R k0 k a' := fun h => hr (hiff.2 h)
      simp only [hr, hr', ↓reduceIte]
  b_bound H hH k Z' o x hv g hg hchi := by
    rw [quietKer_b]
    by_cases hr : QuietRealized R k0 k (H.localHistory M K (k + 1) Z')
    · obtain ⟨H1, hH1, Z1, hk1, hk, hq1, heq⟩ := hr
      have hq := inp.quiet_local H1 H hH1 hH k Z1 Z' hk1 hk heq hq1
      have hr : QuietRealized R k0 k (H.localHistory M K (k + 1) Z') :=
        ⟨H, hH, Z', hk1, hk, hq, rfl⟩
      simp only [hr, ↓reduceIte]
      exact inp.b_bound H hH k hk hk1 Z' hq o x hv g hg hchi
    · simp only [hr, ↓reduceIte, norm_zero]
      have hvol : 0 ≤ volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
          z ∉ (H.localHistory M K (k + 1) Z').Z k} := by
        unfold volScale; positivity
      exact mul_nonneg (add_nonneg (mul_nonneg hCb (hlog k)) (mul_nonneg hCb hB0)) hvol
  quiet H hH k hk Z' hq o x hv := by
    cases k with
    | zero => exact absurd hq (inp.not_quiet_zero H hH Z' hk)
    | succ k' =>
      exact quietKer_K_quiet inp hz hc hβ haw hμ H hH (k' + 1) hk (by omega) Z' hq o x hv
  dom H hH k Z' o x hv hchi := by
    rw [quietKer_K]
    by_cases hr : QuietRealized R k0 k (H.localHistory M K (k + 1) Z')
    · obtain ⟨H1, hH1, Z1, hk1, hk, hq1, heq⟩ := hr
      have hq := inp.quiet_local H1 H hH1 hH k Z1 Z' hk1 hk heq hq1
      have hr : QuietRealized R k0 k (H.localHistory M K (k + 1) Z') :=
        ⟨H, hH, Z', hk1, hk, hq, rfl⟩
      simp only [hr, ↓reduceIte]
      rw [inp.Rq_eq H hH k hk hk1 Z' hq]
      rw [quietRest_eq_zero geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
        (locRH_rem (k + 1) Z') o x hv hchi, mul_zero]
    · simp only [hr, ↓reduceIte]
  gauss H hH k Z' := by
    by_cases hr : QuietRealized R k0 k (H.localHistory M K (k + 1) Z')
    · have h := Classical.choose_spec (quietKer_gauss_exists inp hz hc hβ haw hμ hN c1 c2 hc1 hc2
        hlog hcpos hδ hδ1 hΛ k _ hr)
      unfold quietWit
      simp only [hr, ↓reduceDIte]
      exact h
    · unfold quietWit
      simp only [hr, ↓reduceDIte]
      refine gaussSpec_zero cs _ k _ _ fun o x hv => ?_
      rw [quietKer_K]
      simp only [hr, ↓reduceIte]

end Assemble

section Compose

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {k0 : ℕ} {geo : Geo S n R M} {cs : OpConsts}

open Classical in
/-- The exponents of the localized operators along the lineage when every step is given by the
step exponents `κs` (Definition II.5.11): `κ_{k+1}(Z') = κ^{(k)}(Z') + ∑_{Y ∈ Anc_k(Z')} κ_k(Y)`
at the components that are not kept, `κK` at the kept ones. -/
noncomputable def lineageKappa (H : RegionHistory S n R k0 K) (M : ℕ) [NeZero M]
    (κs : ℕ → LocalHistory S n M K → ℝ) (κK : ∀ k, H.Comp k → ℝ) : ∀ k, H.Comp k → ℝ
  | 0, _ => 0
  | k + 1, Z' =>
      if H.IsKeptEvent (k + 1) Z' then κK (k + 1) Z'
      else κs k (H.localHistory M K (k + 1) Z') + ∑ Y ∈ H.parts k Z', lineageKappa H M κs κK k Y

/-- **The bound (1.26) for the localized operators built from the quiet step data** (Lemma II.5.13
composed along the lineage, with the one-step bound `quietKernel_bound` of Lemma II.5.14): for an
admissible region history `H`, the localized operator `𝕋_k(Z, 𝔞)` of every component satisfies
(1.26) with the exponent `lineageKappa`, `κ_{k+1}(Z') = -(c₁ log β_k + c₂)|Z^c_k ∩ Z'|_{k+1} +
∑_Y κ_k(Y)`, provided the kept operators (S3) satisfy (1.26) with their exponents `κK`.  At a
component whose step is not quiet the step kernel is `0`. -/
theorem quiet_locOp_pkgBound [NeZero N] (inp : QuietStepInput K k0 geo cs N)
    (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hβ : ∀ k, 0 ≤ cs.beta (k + 1)) (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct (k + 1))
    (hN : 2 ≤ N) (c1 c2 : ℝ) (hc1 : cs.Cb ≤ c1) (hc2 : cs.Cb * cs.B0 ≤ c2)
    (hlog : ∀ k, 0 ≤ Real.log (cs.beta k))
    (hcpos : ∀ k, 0 < cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hδ : ∀ k, 0 < cs.delta k) (hδ1 : ∀ k, 3 * S.d * S.L * cs.delta k ≤ 1 / 2)
    (hΛ : ∀ k, 3 * S.d * S.L * cShell N * cs.delta k ≤ 1 / 2)
    (hCb : 0 ≤ cs.Cb) (hB0 : 0 ≤ cs.B0)
    {κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
    (KD : KeptData k0 geo cs N κ' lamHat) {H : RegionHistory S n R k0 K} (hH : H.Admissible)
    (lab : ∀ k, H.Comp k → Fin 5) (hzpos : ∀ k, 0 < cs.z (k + 1)) (κK : ∀ k, H.Comp k → ℝ)
    (hkept : ∀ (k : ℕ) (hk : k ≤ K) (Z : H.Comp k), IsKept H k Z →
      PkgBound (H.localHistory M K k Z) k
        (locOp geo cs (quietStepData inp hz hc hβ haw hμ hN c1 c2 hc1 hc2 hlog hcpos hδ hδ1 hΛ
          hCb hB0) KD hH lab k hk Z) (κK k Z)) :
    ∀ (k : ℕ) (hk : k ≤ K) (Z : H.Comp k),
      PkgBound (H.localHistory M K k Z) k
        (locOp geo cs (quietStepData inp hz hc hβ haw hμ hN c1 c2 hc1 hc2 hlog hcpos hδ hδ1 hΛ
          hCb hB0) KD hH lab k hk Z)
        (lineageKappa H M (quietKappaStep (K := K) cs c1 c2) κK k Z) := by
  refine locOp_pkgBound geo cs _ KD hH lab hzpos (fun k => (hcpos k).le) _ ?_ ?_
  · intro k hk Z hZ
    have h := hkept k hk Z hZ
    cases k with
    | zero => exact (H.F.isEmpty_comp_zero.false Z).elim
    | succ k =>
      have hev : H.IsKeptEvent (k + 1) Z := hZ
      simpa [lineageKappa, hev] using h
  · intro k Z' hZ'
    have hev : ¬ H.IsKeptEvent (k + 1) Z' := hZ'
    simp [lineageKappa, hev]

end Compose

section Inhabited

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {k0 : ℕ}

/-- **Inhabitation of `QuietStepInput`**: for histories with a single scale record (`K = 0`, so
that no step `k → k + 1` fits, `k + 1 ≤ K`) the input exists, with the zero remainder and the zero
boundary exponent.  The input carries content only for `K ≥ 2` (quiet steps need `1 ≤ k`,
`k + 1 ≤ K`), where it is the locality (S4) of the quiet kernel, a source fact of Lemma I.3.9. -/
theorem quietStepInput_nonempty (geo : Geo S n R M) (cs : OpConsts) (N k0 : ℕ) (hK : K = 0) :
    Nonempty (QuietStepInput K k0 geo cs N) := by
  refine ⟨{
    not_quiet_zero := fun _ _ _ h => by omega
    quiet_local := fun _ _ _ _ _ _ _ _ hk => by omega
    Rq := fun _ _ _ _ _ => 0
    Rq_eq := fun _ _ _ hk => by omega
    K_meas := fun _ _ _ hr => by have := QuietRealized.le hr; omega
    real_euclid := fun _ _ a a' _ => by
      constructor <;> intro hr <;> have := QuietRealized.le hr <;> omega
    euclid_K := fun _ _ _ _ _ hk => by omega
    b := fun _ _ _ _ _ _ => 0
    b_meas := fun _ _ _ _ _ => measurable_const
    b_analytic := fun _ _ _ _ _ _ => analyticOnNhd_const
    b_real := fun _ _ _ _ _ _ _ _ _ => by simp
    b_supp := fun _ _ _ _ _ _ _ _ _ => rfl
    b_rot := fun _ _ _ _ _ _ _ _ => rfl
    b_euclid := fun _ _ _ _ _ hk => by omega
    b_bound := fun _ _ _ hk => by omega }⟩

end Inhabited

end Balaban.LargeField
