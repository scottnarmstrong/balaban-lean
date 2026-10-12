module

public import Balaban.Background.Def5Response
public import Balaban.SmallField.TaylorCauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma 2.3 (d): Cauchy estimates for the background field along a line of data

The Taylor/Cauchy toolkit (`SmallField/TaylorCauchy`) on the unit-scale line (`E = ℂ`),
applied to vector-valued functions tested against linear functionals:

* `cauchy_line`: for `f` analytic on `|t| < R` (`R ≥ 2`), `|f| ≤ M`, `f 0 = 0`:
  `|f'(0)| ≤ M/R`, `|f(1) - f'(0)| ≤ 2M/R²`;
* `cauchy_functional`: the same for `λ ∘ Φ`, `Φ : ℂ → (ι → ℂ)`;
* `supBounds_cauchy`, `small_cauchy`: the bounds `SupBounds` (`‖·‖_*`) and `Small` (`|·|₂`) are
  families of such functionals, so they pass to the derivative and to the second-order remainder.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Metric Set Filter Topology Balaban.SmallField

/-- **Cauchy estimates on the unit-scale line** (the toolkit of `TaylorCauchy` for `E = ℂ`): for a
scalar function analytic on the disc of radius `R ≥ 2`, bounded by `M`, with `f 0 = 0`:
`|f'(0)| ≤ M / R` and `|f 1 - f'(0)| ≤ 2 M / R²`. -/
theorem cauchy_line {f : ℂ → ℂ} {R M : ℝ} (hR : 2 ≤ R) (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hM : ∀ t ∈ ball (0 : ℂ) R, ‖f t‖ ≤ M) (h0 : f 0 = 0) :
    ‖deriv f 0‖ ≤ M / R ∧ ‖f 1 - deriv f 0‖ ≤ 2 * M / R ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hd : fderiv ℂ f 0 1 = deriv f 0 := by
    exact fderiv_apply_one_eq_deriv
  constructor
  · have := norm_fderiv_apply_le hR0 hf hM (1 : ℂ)
    rw [hd] at this
    simpa using this
  · have h1 := taylor_first (c := (0 : ℂ)) (z := (1 : ℂ)) hR0 hf hM (by simpa using (by linarith : (1 : ℝ) ≤ R / 2))
    rw [hd, h0] at h1
    simp only [zero_add, sub_zero, norm_one] at h1
    calc ‖f 1 - deriv f 0‖ ≤ 2 * M * (1 / R) ^ 2 := h1
      _ = 2 * M / R ^ 2 := by field_simp

section Vec

variable {ι : Type*} [Fintype ι]

/-- **Cauchy estimates for a vector-valued function of `t`, tested against a linear functional.**
Let `Φ : ℂ → (ι → ℂ)` be analytic on the disc of radius `R ≥ 2`, `Φ 0 = 0`, with derivative `Φd` at
`0`.  If `|λ(Φ t)| ≤ M` on the disc then `|λ Φd| ≤ M/R` and `|λ(Φ 1 - Φd)| ≤ 2M/R²`. -/
theorem cauchy_functional {Φ : ℂ → ι → ℂ} {Φd : ι → ℂ} {R M : ℝ} (hR : 2 ≤ R)
    (hΦ : AnalyticOnNhd ℂ Φ (ball 0 R)) (h0 : Φ 0 = 0) (hd : HasDerivAt Φ Φd 0)
    (Lf : (ι → ℂ) →ₗ[ℂ] ℂ) (hB : ∀ t ∈ ball (0 : ℂ) R, ‖Lf (Φ t)‖ ≤ M) :
    ‖Lf Φd‖ ≤ M / R ∧ ‖Lf (Φ 1 - Φd)‖ ≤ 2 * M / R ^ 2 := by
  have hR0 : 0 < R := by linarith
  let Lc : (ι → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap Lf
  have hLc : ∀ u, Lc u = Lf u := fun u => rfl
  have hf : AnalyticOnNhd ℂ (fun t => Lc (Φ t)) (ball 0 R) :=
    fun t ht => (Lc.analyticAt _).comp (hΦ t ht)
  have hder : HasDerivAt (fun t => Lc (Φ t)) (Lc Φd) 0 := Lc.hasFDerivAt.comp_hasDerivAt 0 hd
  have h1 := cauchy_line hR (f := fun t => Lc (Φ t)) hf (fun t ht => by simpa [hLc] using hB t ht)
    (by simp [h0])
  rw [hder.deriv] at h1
  simp only [hLc, map_sub] at h1 ⊢
  exact h1

end Vec

section SupFuns

open Balaban.Multiscale Balaban.Background

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ K ϱ)

/-- The extension-to-the-torus evaluation `u ↦ svec G u y i` as a linear functional. -/
noncomputable def evF (y : Torus d (N₀ * L ^ K)) (i : Fin N) :
    (G.Ω 1 × Fin N → ℂ) →ₗ[ℂ] ℂ where
  toFun u := svec G u y i
  map_add' u v := svec_add (G := G) u v y i
  map_smul' c u := by
    simp only [svec, zeroExt, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp

theorem evF_apply (y : Torus d (N₀ * L ^ K)) (i : Fin N) (u : G.Ω 1 × Fin N → ℂ) :
    evF G y i u = svec G u y i := rfl

/-- The linear functionals whose bounds make up `SupBounds`. -/
def supFuns : Set ((G.Ω 1 × Fin N → ℂ) →ₗ[ℂ] ℂ) :=
  {Lf | ∃ y i, Lf = evF G y i} ∪
  {Lf | ∃ x ∈ G.Ω 1, ∃ (μ : Fin d) (i : Fin N), Lf = (G.spacing x : ℂ) •
      (evF G (x + Pi.single μ 1) i - evF G x i)} ∪
  {Lf | ∃ x ∈ G.Ω 1, ∃ (μ : Fin d) (i : Fin N), Lf = (G.spacing x : ℂ) •
      (evF G (x - Pi.single μ 1) i - evF G x i)} ∪
  {Lf | ∃ x ∈ G.Ω 1, ∃ i : Fin N, Lf = ((G.spacing x) ^ 2 : ℂ) •
      ∑ μ : Fin d, (2 • evF G x i - evF G (x + Pi.single μ 1) i - evF G (x - Pi.single μ 1) i)}

theorem supBounds_iff (u : G.Ω 1 × Fin N → ℂ) (V : ℝ) :
    SupBounds G u V ↔ ∀ Lf ∈ supFuns G, ‖Lf u‖ ≤ V := by
  have hsp : ∀ x : Torus d (N₀ * L ^ K), ‖(G.spacing x : ℂ)‖ = G.spacing x := fun x => by
    rw [Complex.norm_real, Real.norm_of_nonneg (by unfold GeneratingSet.spacing; positivity)]
  constructor
  · intro h Lf hLf
    rcases hLf with ((⟨y, i, rfl⟩ | ⟨x, hx, μ, i, rfl⟩) | ⟨x, hx, μ, i, rfl⟩) | ⟨x, hx, i, rfl⟩
    · exact h.val y i
    · simp only [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul, norm_mul, hsp]
      exact h.fwd x hx μ i
    · simp only [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul, norm_mul, hsp]
      exact h.bwd x hx μ i
    · have := h.lap x hx i
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply, smul_eq_mul,
        norm_mul, norm_pow, hsp]
      convert this using 3
      refine Finset.sum_congr rfl fun μ _ => ?_
      simp [evF]
  · intro h
    refine ⟨fun y i => ?_, fun x hx μ i => ?_, fun x hx μ i => ?_, fun x hx i => ?_⟩
    · exact h (evF G y i) (Or.inl (Or.inl (Or.inl ⟨y, i, rfl⟩)))
    · have := h _ (Or.inl (Or.inl (Or.inr ⟨x, hx, μ, i, rfl⟩)))
      simpa only [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul, norm_mul, hsp,
        evF_apply] using this
    · have := h _ (Or.inl (Or.inr ⟨x, hx, μ, i, rfl⟩))
      simpa only [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul, norm_mul, hsp,
        evF_apply] using this
    · have := h _ (Or.inr ⟨x, hx, i, rfl⟩)
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply, smul_eq_mul,
        norm_mul, norm_pow, hsp] at this
      convert this using 3
      refine Finset.sum_congr rfl fun μ _ => ?_
      simp [evF]

/-- Cauchy estimates for a family with `SupBounds` on the disc. -/
theorem supBounds_cauchy {Φ : ℂ → G.Ω 1 × Fin N → ℂ} {Φd : G.Ω 1 × Fin N → ℂ} {R M : ℝ}
    (hR : 2 ≤ R) (hΦ : AnalyticOnNhd ℂ Φ (ball 0 R)) (h0 : Φ 0 = 0) (hd : HasDerivAt Φ Φd 0)
    (hB : ∀ t ∈ ball (0 : ℂ) R, SupBounds G (Φ t) M) :
    SupBounds G Φd (M / R) ∧ SupBounds G (Φ 1 - Φd) (2 * M / R ^ 2) := by
  have key : ∀ Lf ∈ supFuns G, ‖Lf Φd‖ ≤ M / R ∧ ‖Lf (Φ 1 - Φd)‖ ≤ 2 * M / R ^ 2 :=
    fun Lf hLf => cauchy_functional hR hΦ h0 hd Lf (fun t ht => (supBounds_iff G _ M).1 (hB t ht) Lf hLf)
  exact ⟨(supBounds_iff G _ _).2 fun Lf hLf => (key Lf hLf).1,
    (supBounds_iff G _ _).2 fun Lf hLf => (key Lf hLf).2⟩

/-- The linear functionals whose bounds make up `Small`. -/
def smallFuns : Set ((G.Ω 1 → ℂ) →ₗ[ℂ] ℂ) :=
  {Lf | ∃ x : G.Ω 1, Lf = ((G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 : ℝ) : ℂ) •
    (LinearMap.proj x : (G.Ω 1 → ℂ) →ₗ[ℂ] ℂ)}

theorem small_iff (α : G.Ω 1 → ℂ) (V : ℝ) :
    Small G α V ↔ ∀ Lf ∈ smallFuns G, ‖Lf α‖ ≤ V := by
  have hsp : ∀ x : Torus d (N₀ * L ^ K), ‖((G.spacing x ^ 2 : ℝ) : ℂ)‖ = G.spacing x ^ 2 := fun x => by
    rw [Complex.norm_real, Real.norm_of_nonneg (by unfold GeneratingSet.spacing; positivity)]
  constructor
  · rintro h Lf ⟨x, rfl⟩
    simp only [LinearMap.smul_apply, LinearMap.coe_proj, Function.eval, smul_eq_mul, norm_mul, hsp]
    exact h x
  · intro h x
    have := h _ ⟨x, rfl⟩
    simpa only [LinearMap.smul_apply, LinearMap.coe_proj, Function.eval, smul_eq_mul, norm_mul,
      hsp] using this

theorem small_cauchy {Φ : ℂ → G.Ω 1 → ℂ} {Φd : G.Ω 1 → ℂ} {R M : ℝ}
    (hR : 2 ≤ R) (hΦ : AnalyticOnNhd ℂ Φ (ball 0 R)) (h0 : Φ 0 = 0) (hd : HasDerivAt Φ Φd 0)
    (hB : ∀ t ∈ ball (0 : ℂ) R, Small G (Φ t) M) :
    Small G Φd (M / R) ∧ Small G (Φ 1 - Φd) (2 * M / R ^ 2) := by
  have key : ∀ Lf ∈ smallFuns G, ‖Lf Φd‖ ≤ M / R ∧ ‖Lf (Φ 1 - Φd)‖ ≤ 2 * M / R ^ 2 :=
    fun Lf hLf => cauchy_functional hR hΦ h0 hd Lf (fun t ht => (small_iff G _ M).1 (hB t ht) Lf hLf)
  exact ⟨(small_iff G _ _).2 fun Lf hLf => (key Lf hLf).1,
    (small_iff G _ _).2 fun Lf hLf => (key Lf hLf).2⟩

end SupFuns

end Balaban.Fluctuation
