module

public import Balaban.LargeField.Operators.QuietLocalRest
public import Balaban.LargeField.Operators.QuietStepData

/-!
# The reduced input of the quiet step data

`QuietStepInput` (W110) carries the locality and covariance facts that tie the `a`-indexed
remainder to the `H`-indexed quiet kernel.  Here they are proved from the landed Lemma I.3.9
(the localized history of `Z'` is generated from its own seed data) and the lattice covariance of
the quiet kernel:

* `quietRq`: the remainder as a function of the localized history `a` (the remainder of any
  realizing `(H, Z')`);
* `quietRq_eq` (`Rq_eq`), `isQuiet_of_hist` (`quiet_local`), `not_isQuiet_zero`
  (`not_quiet_zero`), and `euclid_K` (`quietKernel_of_histImage`, using only
  the localized histories);
* `QuietStepInput'`: the remaining fields: `real_euclid` (the localized histories of quiet steps are
  closed under lattice symmetries) and the boundary exponent `b`;
* `QuietStepInput'.toInput`, `quietStepData'`, `quiet_locOp_pkgBound'`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal

section Rq

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {k0 : ℕ}

/-- A realization of a quiet localized history. -/
theorem QuietRealized.nonempty {k : ℕ} {a : LocalHistory S n M K} (h : QuietRealized R k0 k a) :
    Nonempty {p : (H : RegionHistory S n R k0 K) × H.Comp (k + 1) //
      p.1.Admissible ∧ 1 ≤ k ∧ k + 1 ≤ K ∧ IsQuiet (p.1.locRH (k + 1) p.2) k p.2.1 ∧
        p.1.localHistory M K (k + 1) p.2 = a} := by
  obtain ⟨H, hH, Z', h1, h2, h3, h4⟩ := h
  exact ⟨⟨⟨H, Z'⟩, hH, h1, h2, h3, h4⟩⟩

open Classical in
/-- **The remainder of the quiet kernel as a function of the localized history** `a`: the quiet
remainder `quietRest` of a realization `(H, Z')` of `a` (transported to `a`), `0` if `a` is not
the localized history of a quiet step. -/
noncomputable def quietRq (geo : Geo S n R M) (cs : OpConsts) (k0 : ℕ) (k : ℕ)
    (a : LocalHistory S n M K) (o : OutT N R a (k + 1)) (x : NewCfg N a k)
    (hv : EuclideanSpace ℝ (Fin N)) : ℝ :=
  if h : QuietRealized R k0 k a then
    quietRest geo ((Classical.choice h.nonempty).1.1.locRH (k + 1) (Classical.choice h.nonempty).1.2)
      k (Classical.choice h.nonempty).1.2.1
      (locComp_mem _ (Classical.choice h.nonempty).2.2.2.1 _)
      (Classical.choice h.nonempty).2.2.2.1 cs (locRH_rem _ _)
      (transOut (Classical.choice h.nonempty).2.2.2.2.2.symm o)
      (transNew (Classical.choice h.nonempty).2.2.2.2.2.symm x) hv
  else 0

/-- `Rq_eq`: at a quiet step of an admissible history, `quietRq` is `quietRest`. -/
theorem quietRq_eq (geo : Geo S n R M) (cs : OpConsts) (H : RegionHistory S n R k0 K)
    (hH : H.Admissible) (k : ℕ) (hk : k + 1 ≤ K) (hk1 : 1 ≤ k) (Z' : H.Comp (k + 1))
    (hq : IsQuiet (H.locRH (k + 1) Z') k Z'.1)
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N)) :
    quietRq geo cs k0 k (H.localHistory M K (k + 1) Z') o x hv =
      quietRest geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs (locRH_rem _ _)
        o x hv := by
  classical
  have hr : QuietRealized R k0 k (H.localHistory M K (k + 1) Z') := ⟨H, hH, Z', hk1, hk, hq, rfl⟩
  unfold quietRq
  simp only [hr, ↓reduceDIte]
  exact quietRest_eq_of_hist geo cs hk Z' _ (Classical.choice hr.nonempty).2.2.2.2.2 o x hv

end Rq

section Input

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {k0 : ℕ}

variable (K) in
/-- **The reduced input of the quiet step data.**  The fields of `QuietStepInput` that are not
consequences of the landed results:

* `real_euclid`: the localized histories of quiet steps are closed under symmetries (the image
  history of a region history under a symmetry is again admissible);
* `b`, `b_*`: the boundary exponent of the quiet step with its properties (S0). -/
structure QuietStepInput' (k0 : ℕ) (geo : Geo S n R M) (cs : OpConsts) (N : ℕ) where
  real_euclid : ∀ (k : ℕ) (σ : LatTorusSym S n M K) (a a' : LocalHistory S n M K),
    HistImage σ.toTorusSym a a' → (QuietRealized R k0 k a ↔ QuietRealized R k0 k a')
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
  b_euclid : ∀ (k : ℕ) (σ : LatTorusSym S n M K) (a a' : LocalHistory S n M K)
    (hI : HistImage σ.toTorusSym a a') (hk : k + 1 ≤ K) o o' x x' hv g g', QuietRealized R k0 k a →
    RelOut σ.toTorusSym o o' → RelSub hI hk x x' → RelG σ.toTorusSym g g' → b k a' o' x' hv g' = b k a o x hv g
  b_bound : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (k : ℕ), k + 1 ≤ K →
    1 ≤ k → ∀ (Z' : H.Comp (k + 1)), IsQuiet (H.locRH (k + 1) Z') k Z'.1 →
    ∀ o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
    ChiNewAt geo cs H k Z' o x →
    ‖b k (H.localHistory M K (k + 1) Z') o x hv g‖ ≤
      (cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
        volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
          z ∉ (H.localHistory M K (k + 1) Z').Z k}

variable {geo : Geo S n R M} {cs : OpConsts}

/-- **`QuietStepInput'` gives `QuietStepInput`**: `not_quiet_zero`, `quiet_local`, `Rq_eq` and the
lattice part of `euclid_K` are proved (Lemma I.3.9 (d), `quietKernel_of_histImage`). -/
noncomputable def QuietStepInput'.toInput (inp : QuietStepInput' K k0 geo cs N) :
    QuietStepInput K k0 geo cs N where
  not_quiet_zero := fun H _ Z' hK => not_isQuiet_zero H hK Z'
  quiet_local := fun H H2 _ _ k Z' Z'' _ hk heq hq => isQuiet_of_hist hk Z' Z'' heq hq
  Rq := fun k a o x hv => quietRq geo cs k0 k a o x hv
  Rq_eq := fun H hH k hk hk1 Z' hq o x hv => quietRq_eq geo cs H hH k hk hk1 Z' hq o x hv
  real_euclid := inp.real_euclid
  euclid_K := fun k σ a a' hI hk o o' x x' hv hr ho hx => by
    have hr' := (inp.real_euclid k σ a a' hI).1 hr
    obtain ⟨H, hH, Z', hk1, hkK, hq, rfl⟩ := hr
    obtain ⟨H2, hH2, Z2, hk1', hkK', hq2, rfl⟩ := hr'
    show gaussProd N _ k cs o' x' * quietRq geo cs k0 k _ o' x' hv =
      gaussProd N _ k cs o x * quietRq geo cs k0 k _ o x hv
    rw [quietRq_eq geo cs H hH k hkK hk1 Z' hq, quietRq_eq geo cs H2 hH2 k hkK' hk1' Z2 hq2]
    have h := quietKernel_of_histImage σ geo cs hk Z' Z2 hI ho hx.2 hv
    exact ((quietKernel_eq geo (H2.locRH (k + 1) Z2) k Z2.1 (locComp_mem H2 hk Z2) hk cs
      (locRH_rem _ _) o' x' hv).symm.trans h).trans
      (quietKernel_eq geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
        (locRH_rem _ _) o x hv)
  b := inp.b
  b_meas := inp.b_meas
  b_analytic := inp.b_analytic
  b_real := inp.b_real
  b_supp := inp.b_supp
  b_rot := inp.b_rot
  b_euclid := inp.b_euclid
  b_bound := inp.b_bound

/-- **Inhabitation of `QuietStepInput'`** for histories with no quiet step (`K ≤ 1`: a quiet step
`k → k + 1` needs `1 ≤ k` and `k + 1 ≤ K`), with the zero boundary exponent. -/
theorem quietStepInput'_nonempty (geo : Geo S n R M) (cs : OpConsts) (N k0 : ℕ) (hK : K ≤ 1) :
    Nonempty (QuietStepInput' K k0 geo cs N) := by
  refine ⟨{
    real_euclid := fun _ _ a a' _ => by
      constructor <;> intro hr <;> obtain ⟨H, -, Z', h1, h2, -⟩ := hr <;> omega
    b := fun _ _ _ _ _ _ => 0
    b_meas := fun _ _ _ _ _ => measurable_const
    b_analytic := fun _ _ _ _ _ _ => analyticOnNhd_const
    b_real := fun _ _ _ _ _ _ _ _ _ => by simp
    b_supp := fun _ _ _ _ _ _ _ _ _ => rfl
    b_rot := fun _ _ _ _ _ _ _ _ => rfl
    b_euclid := fun _ _ _ _ _ _ _ _ _ _ _ _ _ hr => by
      obtain ⟨H, -, Z', h1, h2, -⟩ := hr; omega
    b_bound := fun _ _ _ hk h1 => by omega }⟩

end Input

section Assemble

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {k0 : ℕ} {geo : Geo S n R M} {cs : OpConsts}

/-- **The step data of the quiet steps** from the reduced input. -/
noncomputable def quietStepData' [NeZero N] (inp : QuietStepInput' K k0 geo cs N)
    (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hβ : ∀ k, 0 ≤ cs.beta (k + 1)) (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct (k + 1))
    (hbg : ∀ q, BgHyp S.d S.L q (minSep S.L geo.M1) cs.aw (cs.mu q))
    (hN : 2 ≤ N) (c1 c2 : ℝ) (hc1 : cs.Cb ≤ c1) (hc2 : cs.Cb * cs.B0 ≤ c2)
    (hlog : ∀ k, 0 ≤ Real.log (cs.beta k))
    (hcpos : ∀ k, 0 < cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hδ : ∀ k, 0 < cs.delta k) (hδ1 : ∀ k, 3 * S.d * S.L * cs.delta k ≤ 1 / 2)
    (hΛ : ∀ k, 3 * S.d * S.L * cShell N * cs.delta k ≤ 1 / 2)
    (hCb : 0 ≤ cs.Cb) (hB0 : 0 ≤ cs.B0) :
    StepData k0 geo cs N (quietKappaStep (K := K) cs c1 c2) :=
  quietStepData inp.toInput hz hc hβ haw hμ hbg hN c1 c2 hc1 hc2 hlog hcpos hδ hδ1 hΛ hCb hB0

/-- **The bound (1.26) for the localized operators built from the quiet step data**, from the
reduced input (`quiet_locOp_pkgBound`). -/
theorem quiet_locOp_pkgBound' [NeZero N] (inp : QuietStepInput' K k0 geo cs N)
    (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hβ : ∀ k, 0 ≤ cs.beta (k + 1)) (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct (k + 1))
    (hbg : ∀ q, BgHyp S.d S.L q (minSep S.L geo.M1) cs.aw (cs.mu q))
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
        (locOp geo cs (quietStepData' inp hz hc hβ haw hμ hbg hN c1 c2 hc1 hc2 hlog hcpos hδ hδ1 hΛ
          hCb hB0) KD hH lab k hk Z) (κK k Z)) :
    ∀ (k : ℕ) (hk : k ≤ K) (Z : H.Comp k),
      PkgBound (H.localHistory M K k Z) k
        (locOp geo cs (quietStepData' inp hz hc hβ haw hμ hbg hN c1 c2 hc1 hc2 hlog hcpos hδ hδ1 hΛ
          hCb hB0) KD hH lab k hk Z)
        (lineageKappa H M (quietKappaStep (K := K) cs c1 c2) κK k Z) :=
  quiet_locOp_pkgBound inp.toInput hz hc hβ haw hμ hbg hN c1 c2 hc1 hc2 hlog hcpos hδ hδ1 hΛ hCb hB0
    KD hH lab hzpos κK hkept

end Assemble

end Balaban.LargeField
