/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.MatrixInfty
public import Balaban.Flow.RunningCoefficients

/-!
# The renormalization-group equations at `λ = ∞`: Theorem 3.2 and Lemma 3.3

`notes/phase1/SMALLFIELD.md` §3.4-§3.5 (I-7; review S-05, S-10), an *editable abstract lemma*:
the data bounds (B1) are explicit hypotheses on the functions `c, f` (the analyticity and the
bounds `hc, hf, hcb, hfb, hcond` of the landed theorem), and the inequality (5.29) is the
hypothesis `hη`.

* `rg_step_infty` (**Theorem 3.2 (a)**): one step; existence, uniqueness, analyticity in the
  data, reality for real data, and `|ξ⁰| ≤ C_ξ β⁻¹ q^{k+1}`, `C_ξ = 168 B/α₀²`
  (`q = L^{-2γ}`, so `q^{k+1} = L^{-2γ(k+1)}`);
* `norm_xi_le_of_step` (**Theorem 3.2 (b)**): the inductive bound `|ξ^{(k)}| ≤ (c₈/4) q^{k+1}`,
  `c₈ = 4 C_ξ/β`, from the step bound at each `k`, which may use the bounds at all `j < k`;
* `rg_flow_infty` (**Theorem 3.2 (c)**): `γ_∞`, `δ_∞`, `|γ_∞ - 1| ≤ 2 C_ξ q β⁻¹/(1-q)`,
  `|δ_∞ - 1| ≤ 3 c₈ q/(2(1-q))` (this needs `3 c₈ q ≤ 2(1-q)`, slightly more than the `c₈ q ≤ 1-q`
  of `exists_gamma_infty`; review S-10), and the `β_j⁻¹` asymptotics;
* `delta_infty_bound`: the `δ_∞` bound (missing from the landed lemmas);
* `tendsto_fixedPoint`, `tendsto_rg_solution` (**Lemma 3.3 applied**): continuity of the
  solution in a parameter given uniform convergence of the data.
-/

@[expose] public section

open Metric Set Filter Topology

namespace Balaban.Flow

/-- The constant `C_ξ = 168 B/α₀²` of (3.2), `B = B₆ K₅`. -/
noncomputable def rgCxi (B α₀ : ℝ) : ℝ := 168 * B / α₀ ^ 2

section Step

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- **Theorem 3.2 (a)** (one step at `λ = ∞`).  The hypotheses are those of
`exists_rg_solution_triangular_param` (analyticity and bounds of the data, i.e. (B1), and
(5.27)), together with (5.29) in the form `η ≤ B (2/α₀²) β⁻¹ q^{k+1}`.  Conclusion: the solution
`ξ⁰` exists, is unique in the polydisc of radius `rgRadius (42 κ) c₁₀`, is analytic in the data,
satisfies `|ξ⁰|_∞ ≤ C_ξ β⁻¹ q^{k+1}` (3.2), and is real at every data point fixed by the
conjugation `σ` when the data have the conjugation symmetry. -/
theorem rg_step_infty {A : G → Matrix (Fin 3) (Fin 3) ℂ} {ε : ℝ}
    {P : Set G} (hP : IsOpen P) (hAan : ∀ i j, AnalyticOnNhd ℂ (fun p => A p i j) P)
    (hA : ∀ p ∈ P, TriangularBounds (A p) ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {c f : (Fin 3 → ℂ) × G → (Fin 3 → ℂ)}
    {κ η c₁₀ : ℝ} (hκ : 0 < κ) (hη : 0 ≤ η) (hc₁₀ : 0 < c₁₀)
    (hcond : 16 * (42 * η) * max (2 * (42 * κ)) (1 / c₁₀) ≤ 1)
    (hc : AnalyticOnNhd ℂ c (closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P))
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P))
    (hcb : ∀ p ∈ P, ∀ ε' : ℝ, 0 ≤ ε' → ε' ≤ c₁₀ → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ ε' →
      ‖c (ξ, p)‖ ≤ κ * ε' ^ 2)
    (hfb : ∀ p ∈ P, ∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ c₁₀ → ‖f (ξ, p)‖ ≤ η)
    {B α₀ β q : ℝ} {k : ℕ}
    (hηbd : η ≤ B * (2 / α₀ ^ 2 * (β⁻¹ * q ^ (k + 1))))
    {σ : G → G} (hσP : ∀ p ∈ P, σ p ∈ P)
    (hAσ : ∀ p ∈ P, A (σ p) = (A p).map (starRingEnd ℂ))
    (hcσ : ∀ p ∈ P, ∀ ξ, c (conjVec ξ, σ p) = conjVec (c (ξ, p)))
    (hfσ : ∀ p ∈ P, ∀ ξ, f (conjVec ξ, σ p) = conjVec (f (ξ, p))) :
    ∃ ξs : G → (Fin 3 → ℂ),
      (∀ p ∈ P, ‖ξs p‖ ≤ rgRadius (42 * κ) c₁₀ ∧
        (A p).mulVec (ξs p) + c (ξs p, p) = f (ξs p, p) ∧
        (∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ rgRadius (42 * κ) c₁₀ →
          (A p).mulVec ξ + c (ξ, p) = f (ξ, p) → ξ = ξs p) ∧
        ‖ξs p‖ ≤ rgCxi B α₀ * (β⁻¹ * q ^ (k + 1)) ∧
        (σ p = p → ∀ i, (ξs p i).im = 0)) ∧
      AnalyticOnNhd ℂ ξs P := by
  obtain ⟨ξs, hξs, hanal⟩ := exists_rg_solution_triangular_param hP hAan hA hε0 hε1 hκ hη hc₁₀
    hcond hc hf hcb hfb
  refine ⟨ξs, fun p hp => ?_, hanal⟩
  obtain ⟨h1, h2, h3, h4⟩ := hξs p hp
  refine ⟨h1, h2, h3, ?_, fun hfix i => ?_⟩
  · calc ‖ξs p‖ ≤ 84 * η := h4
      _ ≤ 84 * (B * (2 / α₀ ^ 2 * (β⁻¹ * q ^ (k + 1)))) := by linarith
      _ = rgCxi B α₀ * (β⁻¹ * q ^ (k + 1)) := by unfold rgCxi; ring
  · exact rg_solution_real_of_fixed hσP hAσ hcσ hfσ
      (fun p hp => ⟨(hξs p hp).1, (hξs p hp).2.1, (hξs p hp).2.2.1⟩) hp hfix i

end Step

section Induction

/-- **Theorem 3.2 (b)**: the inductive bound.  If, for every `k`, the bounds
`|ξ^{(j)}| ≤ (c₈/4) q^{j+1}` for `j < k` imply `|ξ^{(k)}| ≤ C β⁻¹ q^{k+1}` (this is
`rg_step_infty`, whose input (5.29) uses (H.6) at step `k`, i.e. the bounds for `j < k`), then
`|ξ^{(k)}| ≤ (c₈/4) q^{k+1}` for all `k`, `c₈ = 4 C/β`. -/
theorem norm_xi_le_of_step {ξ : ℕ → Fin 3 → ℂ} {q C β : ℝ}
    (hstep : ∀ k, (∀ j < k, ‖ξ j‖ ≤ (4 * C / β) / 4 * q ^ (j + 1)) →
      ‖ξ k‖ ≤ C * (β⁻¹ * q ^ (k + 1))) (k : ℕ) :
    ‖ξ k‖ ≤ (4 * C / β) / 4 * q ^ (k + 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    refine (hstep k fun j hj => ih j hj).trans (le_of_eq ?_)
    ring

end Induction

section Limits

variable {ξ : ℕ → Fin 3 → ℂ} {q c₈ : ℝ}

/-- The `δ_∞` bound (review S-10): `|δ_∞ - 1| ≤ 3 c₈ q/(2(1-q))`, provided
`3 c₈ q ≤ 2 (1 - q)`. -/
theorem delta_infty_bound (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : 3 * c₈ * q ≤ 2 * (1 - q))
    (hξ : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * q ^ (k + 1)) :
    ∃ δ : ℂ, Tendsto (deltaSeq ξ) atTop (𝓝 δ) ∧ ‖δ - 1‖ ≤ 3 * (c₈ * q / (2 * (1 - q))) := by
  have hq : 0 < 1 - q := by linarith
  have hs1 : c₈ * q ≤ 1 - q := by nlinarith [mul_nonneg hc hq0]
  obtain ⟨γ, δ, hTγ, hTδ, hγ1, -, hγne, -⟩ := exists_gamma_infty hq0 hq1 hc hs1 hξ
  set c := c₈ * q / 4 with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hcs : c ≤ (1 - q) / 4 := by rw [hcdef]; linarith
  have hξ' : ∀ k, ‖ξ k 1‖ ≤ c * q ^ k := fun k =>
    ((norm_comp_le hξ k 1)).trans (le_of_eq (by rw [hcdef, pow_succ]; ring))
  obtain ⟨γ', hT', h1', -⟩ := Balaban.Analysis.exists_tendsto_prod_inv_one_add
    (ξ := fun k => ξ k 1) hq0 hq1 hc0 hξ' hcs
  have hTγ' : Tendsto (fun k => ∏ j ∈ Finset.range k, (1 + ξ j 1)⁻¹) atTop (𝓝 γ') :=
    (tendsto_add_atTop_iff_nat 1).mp hT'
  have e2c : 2 * c / (1 - q) = c₈ * q / (2 * (1 - q)) := by rw [hcdef]; field_simp; ring
  have hγ'1 : ‖γ' - 1‖ ≤ c₈ * q / (2 * (1 - q)) := by rw [← e2c]; exact h1'
  have hTδ' : Tendsto (deltaSeq ξ) atTop (𝓝 (γ⁻¹ * γ')) := by
    have := (hTγ.inv₀ hγne).mul hTγ'
    refine this.congr fun k => ?_
    rw [deltaSeq_eq]
  have hδ : δ = γ⁻¹ * γ' := tendsto_nhds_unique hTδ hTδ'
  refine ⟨δ, hTδ, ?_⟩
  set t := c₈ * q / (2 * (1 - q)) with ht
  have ht3 : t ≤ 1 / 3 := by
    rw [ht, div_le_iff₀ (by positivity)]; linarith
  have ht0 : 0 ≤ t := by positivity
  have hγlo : 2 / 3 ≤ ‖γ‖ := by
    have := norm_sub_norm_le (1 : ℂ) γ
    rw [norm_sub_rev] at this
    simp only [norm_one] at this
    linarith
  have hinv : ‖γ⁻¹‖ ≤ 3 / 2 := by
    rw [norm_inv]
    calc (‖γ‖)⁻¹ ≤ (2 / 3)⁻¹ := inv_anti₀ (by norm_num) hγlo
      _ = 3 / 2 := by norm_num
  have e : δ - 1 = γ⁻¹ * (γ' - γ) := by rw [hδ]; field_simp
  have hd : ‖γ' - γ‖ ≤ 2 * t := by
    have : γ' - γ = (γ' - 1) - (γ - 1) := by ring
    rw [this]
    exact (norm_sub_le _ _).trans (by linarith)
  rw [e, norm_mul]
  calc ‖γ⁻¹‖ * ‖γ' - γ‖ ≤ 3 / 2 * (2 * t) :=
        mul_le_mul hinv hd (norm_nonneg _) (by norm_num)
    _ = 3 * t := by ring

/-- **Theorem 3.2 (c)**: the limits and the rate.  With `c₈ = 4 C/β`, `q = L^{-2γ}`: `γ_∞`,
`δ_∞` exist, `|γ_∞ - 1| ≤ 2 C q β⁻¹/(1-q)`, `|δ_∞ - 1| ≤ 3 c₈ q/(2(1-q)) = 6 C q β⁻¹/(1-q)`, and
`β_j⁻¹ = (β γ_∞)⁻¹ L^{-j(d-2)} + O(β⁻²) L^{-j(d-2)} q^j` (P9 (4.18)). -/
theorem rg_flow_infty {L : ℝ} (hL : 0 < L) (d : ℕ) {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 < β)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hβs : 6 * C * q ≤ β * (1 - q))
    (hξ : ∀ k, ‖ξ k‖ ≤ (4 * C / β) / 4 * q ^ (k + 1)) :
    ∃ γ δ : ℂ, Tendsto (gammaSeq ξ) atTop (𝓝 γ) ∧ Tendsto (deltaSeq ξ) atTop (𝓝 δ) ∧
      ‖γ - 1‖ ≤ 2 * C * q / (1 - q) * β⁻¹ ∧ ‖δ - 1‖ ≤ 6 * C * q / (1 - q) * β⁻¹ ∧
      ∀ (j : ℕ),
        ‖(betaSeq L d ξ (β : ℂ) j)⁻¹ - ((β : ℂ) * γ)⁻¹ * ((L : ℂ) ^ (j * (d - 2)))⁻¹‖ ≤
          Real.exp 2 * (2 * C * q / (1 - q) * β⁻¹) * ‖(β : ℂ)⁻¹‖ *
            ((L ^ (j * (d - 2)))⁻¹ * q ^ j) := by
  have hq : 0 < 1 - q := by linarith
  have hc : 0 ≤ 4 * C / β := by positivity
  have hs : 3 * (4 * C / β) * q ≤ 2 * (1 - q) := by
    have : 3 * (4 * C / β) * q = 12 * C * q / β := by ring
    rw [this, div_le_iff₀ hβ]; nlinarith
  have hs1 : (4 * C / β) * q ≤ 1 - q := by
    nlinarith [mul_nonneg hc hq0]
  have e1 : (4 * C / β) * q / (2 * (1 - q)) = 2 * C * q / (1 - q) * β⁻¹ := by
    field_simp
    ring
  obtain ⟨δ, hTδ, hδ⟩ := delta_infty_bound hq0 hq1 hc hs hξ
  obtain ⟨γ, hTγ, hγ, hasy⟩ := exists_inv_betaSeq_asymptotics hL d hq0 hq1 hc hs1 hξ
  refine ⟨γ, δ, hTγ, hTδ, hγ.trans (le_of_eq e1), ?_, fun j => ?_⟩
  · refine hδ.trans (le_of_eq ?_)
    rw [e1]; ring
  · have := hasy (β : ℂ) j
    rwa [e1] at this

end Limits

section Stability

variable {E : Type*} [NormedAddCommGroup E]

/-- **Lemma 3.3 applied (abstract form).**  Let `Φ₀` be a `1/2`-contraction on `S` with fixed
point `ξ₀ ∈ S`, and `Φ n` maps whose fixed points `ξ n ∈ S` and which converge to `Φ₀` uniformly
on `S` along the filter `l`.  Then `ξ n → ξ₀` along `l`. -/
theorem tendsto_fixedPoint {ι : Type*} {l : Filter ι} {S : Set E} {Φ₀ : E → E} {Φ : ι → E → E}
    {ξ : ι → E} {ξ₀ : E}
    (hlip : ∀ x ∈ S, ∀ y ∈ S, ‖Φ₀ x - Φ₀ y‖ ≤ 1 / 2 * ‖x - y‖)
    (hclose : ∀ δ > 0, ∀ᶠ n in l, ∀ x ∈ S, ‖Φ₀ x - Φ n x‖ ≤ δ)
    (hmem : ∀ n, ξ n ∈ S) (hξ₀ : ξ₀ ∈ S) (hfix₀ : Φ₀ ξ₀ = ξ₀) (hfix : ∀ n, Φ n (ξ n) = ξ n) :
    Tendsto ξ l (𝓝 ξ₀) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hclose (ε / 4) (by positivity)] with n hn
  have := fixedPoint_dist_le hlip hn hξ₀ (hmem n) hfix₀ (hfix n)
  rw [dist_eq_norm, norm_sub_rev]
  linarith

end Stability

section Continuity

theorem triInv_sub (A : Matrix (Fin 3) (Fin 3) ℂ) (u v : Fin 3 → ℂ) :
    triInv A (u - v) = triInv A u - triInv A v := by
  ext i
  fin_cases i <;> simp [triInv] <;> ring

theorem TriangularBounds.triInv_fixed {A : Matrix (Fin 3) (Fin 3) ℂ} {ε : ℝ}
    (hA : TriangularBounds A ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {c f ξ : Fin 3 → ℂ}
    (h : A.mulVec ξ + c = f) : triInv A (f - c) = ξ := by
  have : f - c = A.mulVec ξ := by rw [← h]; abel
  rw [this, hA.triInv_mulVec hε0 hε1]

/-- **Lemma 3.3 applied to the triangular system.**  Let `ξ n` solve
`A n ξ + c n (ξ) = f n (ξ)` and `ξ₀` solve the limit system `A₀ ξ + c₀ (ξ) = f₀ (ξ)` in the
closed ball `S` of radius `r`; suppose the limit map `Φ₀ = A₀⁻¹ (f₀ - c₀)` is a `1/2`-contraction
on `S`, the data `g n = f n - c n` converge to `g₀ = f₀ - c₀` uniformly on `S` and are bounded by
`M` there, and `A n⁻¹ → A₀⁻¹` in the sense `‖A₀⁻¹ z - (A n)⁻¹ z‖ ≤ ω n ‖z‖`, `ω n → 0`.  Then
`ξ n → ξ₀`. -/
theorem tendsto_rg_solution {ι : Type*} {l : Filter ι} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {A : ι → Matrix (Fin 3) (Fin 3) ℂ} {A₀ : Matrix (Fin 3) (Fin 3) ℂ}
    (hA : ∀ n, TriangularBounds (A n) ε) (hA₀ : TriangularBounds A₀ ε)
    {c f : ι → (Fin 3 → ℂ) → (Fin 3 → ℂ)} {c₀ f₀ : (Fin 3 → ℂ) → (Fin 3 → ℂ)} {r M : ℝ}
    (hlip : ∀ x ∈ closedBall (0 : Fin 3 → ℂ) r, ∀ y ∈ closedBall (0 : Fin 3 → ℂ) r,
      ‖triInv A₀ (f₀ x - c₀ x) - triInv A₀ (f₀ y - c₀ y)‖ ≤ 1 / 2 * ‖x - y‖)
    (hbd : ∀ n, ∀ x ∈ closedBall (0 : Fin 3 → ℂ) r, ‖f n x - c n x‖ ≤ M)
    (hdata : ∀ δ > 0, ∀ᶠ n in l, ∀ x ∈ closedBall (0 : Fin 3 → ℂ) r,
      ‖(f₀ x - c₀ x) - (f n x - c n x)‖ ≤ δ)
    {ω : ι → ℝ} (hω : Tendsto ω l (𝓝 0))
    (hAconv : ∀ n z, ‖triInv A₀ z - triInv (A n) z‖ ≤ ω n * ‖z‖)
    {ξ : ι → Fin 3 → ℂ} {ξ₀ : Fin 3 → ℂ}
    (hmem : ∀ n, ξ n ∈ closedBall (0 : Fin 3 → ℂ) r)
    (hmem₀ : ξ₀ ∈ closedBall (0 : Fin 3 → ℂ) r)
    (hsol : ∀ n, (A n).mulVec (ξ n) + c n (ξ n) = f n (ξ n))
    (hsol₀ : A₀.mulVec ξ₀ + c₀ ξ₀ = f₀ ξ₀) :
    Tendsto ξ l (𝓝 ξ₀) := by
  refine tendsto_fixedPoint (S := closedBall (0 : Fin 3 → ℂ) r)
    (Φ₀ := fun x => triInv A₀ (f₀ x - c₀ x)) (Φ := fun n x => triInv (A n) (f n x - c n x))
    hlip ?_ hmem hmem₀ (hA₀.triInv_fixed hε0 hε1 hsol₀) fun n => (hA n).triInv_fixed hε0 hε1 (hsol n)
  intro δ hδ
  set K := |M| + 1 with hK
  have hK0 : 0 < K := by positivity
  have hωδ : ∀ᶠ n in l, dist (ω n) 0 < δ / (2 * K) :=
    hω.eventually (Metric.ball_mem_nhds 0 (by positivity))
  filter_upwards [hdata (δ / 84) (by positivity), hωδ] with n hn hωn x hx
  have hωn' : |ω n| ≤ δ / (2 * K) := by
    rw [Real.dist_eq, sub_zero] at hωn; exact hωn.le
  have e : triInv A₀ (f₀ x - c₀ x) - triInv (A n) (f n x - c n x) =
      triInv A₀ ((f₀ x - c₀ x) - (f n x - c n x)) +
        (triInv A₀ (f n x - c n x) - triInv (A n) (f n x - c n x)) := by
    have := triInv_sub A₀ (f₀ x - c₀ x) (f n x - c n x)
    rw [this]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖triInv A₀ ((f₀ x - c₀ x) - (f n x - c n x))‖ ≤ 42 * (δ / 84) :=
    (hA₀.norm_triInv_le hε0 hε1 _).trans (mul_le_mul_of_nonneg_left (hn x hx) (by norm_num))
  have h2 : ‖triInv A₀ (f n x - c n x) - triInv (A n) (f n x - c n x)‖ ≤ δ / 2 := by
    refine (hAconv n _).trans ?_
    calc ω n * ‖f n x - c n x‖ ≤ |ω n| * ‖f n x - c n x‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ ≤ |ω n| * K := mul_le_mul_of_nonneg_left
          ((hbd n x hx).trans (by rw [hK]; linarith [le_abs_self M])) (abs_nonneg _)
      _ ≤ δ / (2 * K) * K := mul_le_mul_of_nonneg_right hωn' hK0.le
      _ = δ / 2 := by field_simp
  linarith

end Continuity

end Balaban.Flow
