/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormExpBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 3.1 (g), (h): the renormalization expansions, conditional on the open inputs

FLUCTUATION.md v2.3 §3.1 Theorem 3.1 (g) (P4 Prop 4.1, P6 Prop 2.3) and (h) (P4 Prop 4.2), proofs in
§3.6.  Whole-lattice case (`Z_k = ∅`); the subdomain clause "terms with `Y ⊂ (Z^c_{k+1})^≈` equal the
whole-lattice terms" (P6 (2.27)–(2.30), the P5 (1.8) restriction) is not treated.

**Open inputs** (FLUCTUATION v2.3 marks (g), (h) conditional on them) are packaged in ONE structure,
`RenormExpInput`, with the FLUCTUATION references in its field docstrings:

* `locC1`, `locC2`, `locDφ` — the decoupling expansions (LOC I-4b for the background `φ_{k+1}(s)`,
  LOC I-4a mode U for `δφ(s)` with the sources of Lemma 3.5 (ii), decoupled with the same `s`, and
  Lemma AE + GM on the cover): **OPEN** because the auxiliary cover and its NC (Lemma 2.8,
  VMOD.md) and the complex-mass decoupled I-4a are not available.  They are stated as a
  *localization principle* (`HasLocPrinciple`): one family of local, jointly analytic terms whose
  bound is `K_loc M e^{-κ d(Y)}` whenever `M` bounds the constituent on an enlarged domain (the
  decoupled data lie in `Ξ^c(1, ε⁺)`), at each fixed `ξ` — this is what AE gives;
* `expE0`, `expM0` — Theorem 3.1 (a), (b) evaluated at `θ = (1 + ζ) ψ` (**OPEN**: I-8 itself,
  conditional on cover/NC and the fluctuation I-5); the new contributions `ℰ''₀`, `ℳ''₀` are not
  defined in Lean, so they enter as data `E0θ`, `M0θ`;
* `expOld`, `expOldM` — the localized expansions of the pre-localized old-term differences
  (`∑_{j ≤ k} [ℰ^{(j)}(ψ^{(j)} + δψ^{(j)}) - ℰ^{(j)}(ψ^{(j)})]` resp. `ℳ^{(j)}`) on the polydisc of
  radius `r₀`, with terms vanishing at `ξ = 0` (**OPEN**: the fluctuation I-5 in its "simple
  variation" (V0 with the source-driven `δφ(s)`, LOC V3) and the resummation of Proposition 3.3);
  these differences enter as data `oldE`, `oldM`.

**Proved here** from these inputs, the landed results and Lemma 3.5 (ii):

* `thm31g_C1_of_input`: `C₁(z)` expands with the bound `K_loc (2d + 14) ε⁺² W(B_z) ε_R` — the
  pointwise bound of `C₁` (`norm_renC1On_le`) on `Ξ^c(1, ε⁺)`;
* `thm31g_C2_of_input`: `C₂(z)` with the bound `K_loc (17/32) N (5 + …)(K₂ B)² W(B_z) ε_R²` — the
  pointwise bound of `C₂` from Lemma 3.5 (ii) (`norm_renC2On_le_renSol`), quadratic in `ξ`;
* `thm31g_Eu_of_input`: `ℰ_u(z) = ℰ''₀(z)(θ) + (old differences)` with the bound
  `B_{E0} + B_old ε_R / r₀` — the factor `ε_R / r₀` is Cauchy's estimate (`IsLocExp.cauchy`);
* `thm31h_of_input`: `ℳ(x)` with the bound `B_{M0} + K_loc K₂ B ε_R + B_{old,M} ε_R / r₀`, the
  middle term from `|δφ(x)| ≤ K₂ B |ξ|_∞` (Lemma 3.5 (ii));
* `an_renC1On`, `an_renC2On`: `C₁(z)`, `C₂(z)` are analytic jointly in `(Ψ, h̃, ξ)`;
* `renormExpInput_witness`, `nonempty_renormExpInput` (hard rule 10): the input is inhabited for
  admissible parameters (the trivial one-polymer cover `𝒴 = {𝕋}`, `K_loc = 1`, zero data).

Units are the fine units of `RenormIdentity.lean`: `W(B) = ∑_{x ∈ B} ℓ(x)^{-2}` converts the
`η`-unit bounds `C₄' ε²_{k+1} ε` of the source; `B = 8 ε⁺` for the complete convention
(`exists_isRenSol`), so `(K₂ B)² ε_R² ∝ ε²_{k+1} ε_R²`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Matrix

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Analytic

variable {G : GeneratingSet d L N₀ k ϱ} {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
  {q : Q}

theorem an_svec (φ : Q → G.Ω 1 × Fin N → ℂ) (hφ : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q => φ q (y, i)) q)
    (y : Torus d (N₀ * L ^ k)) (i : Fin N) : AnalyticAt ℂ (fun q => svec G (φ q) y i) q := by
  unfold svec zeroExt
  by_cases hy : y ∈ G.Ω 1
  · simp only [hy, ↓reduceDIte]; exact hφ _ i
  · simp only [hy, ↓reduceDIte]; exact analyticAt_const

theorem an_blockAvg (φ : Q → G.Ω 1 × Fin N → ℂ)
    (hφ : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q => φ q (y, i)) q) (x : Torus d (N₀ * L ^ k))
    (i : Fin N) : AnalyticAt ℂ (fun q => blockAvg G (φ q) x i) q := by
  unfold blockAvg
  exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun y _ => an_svec φ hφ y i)

theorem an_barField (Ψ : Q → Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : Q → G.Ω 1 × Fin N → ℂ)
    (hΨ : ∀ x i, AnalyticAt ℂ (fun q => Ψ q x i) q)
    (hφ : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q => φ q (y, i)) q) (x : Torus d (N₀ * L ^ k))
    (i : Fin N) : AnalyticAt ℂ (fun q => barField G (Ψ q) (φ q) x i) q := by
  unfold barField
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, ↓reduceDIte]; exact hφ _ i
  · simp only [hx, ↓reduceDIte]; exact hΨ x i

theorem an_bondSite (Ψ : Q → Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : Q → G.Ω 1 × Fin N → ℂ)
    (hΨ : ∀ x i, AnalyticAt ℂ (fun q => Ψ q x i) q)
    (hφ : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q => φ q (y, i)) q) (x : Torus d (N₀ * L ^ k)) :
    AnalyticAt ℂ (fun q => bondSite G (Ψ q) (φ q) x) q := by
  unfold bondSite
  refine Finset.analyticAt_fun_sum _ fun μ _ => ?_
  by_cases hc : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
  · simp only [hc, ↓reduceIte]
    refine Finset.analyticAt_fun_sum _ fun i _ => ?_
    have h := (an_barField Ψ φ hΨ hφ (x + Pi.single μ 1) i).sub (an_barField Ψ φ hΨ hφ x i)
    exact h.mul h
  · simp only [hc, ↓reduceIte]; exact analyticAt_const

variable (a : ℕ → ℝ)

/-- `C₁(B)` is analytic jointly in the data, the background and `ξ`. -/
theorem an_renC1On (ν εζ : ℝ) (B : Finset (Torus d (N₀ * L ^ k)))
    (Ψ h : Q → Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : Q → G.Ω 1 × Fin N → ℂ) (ξ : Q → Fin 3 → ℂ)
    (hΨ : ∀ x i, AnalyticAt ℂ (fun q => Ψ q x i) q) (hh : ∀ x i, AnalyticAt ℂ (fun q => h q x i) q)
    (hφ : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q => φ q (y, i)) q)
    (hξ : ∀ j, AnalyticAt ℂ (fun q => ξ q j) q) :
    AnalyticAt ℂ (fun q => renC1On G a ν εζ B (Ψ q) (h q) (φ q) (ξ q)) q := by
  unfold renC1On
  refine Finset.analyticAt_fun_sum _ fun x _ => ?_
  unfold renC1Site renZeta
  have hz : AnalyticAt ℂ (fun q => (εζ : ℂ) * ξ q 0) q := analyticAt_const.mul (hξ 0)
  have hb := an_bondSite Ψ φ hΨ hφ x
  refine AnalyticAt.add ?_ ((hξ 2).div_const.mul hb)
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, ↓reduceIte]
    have hQ := fun i => (hΨ x i).sub (an_blockAvg φ hφ x i)
    refine AnalyticAt.add (analyticAt_const.mul (AnalyticAt.add ?_ ?_)) ?_
    · exact (hξ 2).div_const.mul (Finset.analyticAt_fun_sum _ fun i _ => (hQ i).mul (hQ i))
    · refine (analyticAt_const.add (hξ 2)).mul (AnalyticAt.add ?_ ?_)
      · exact hz.mul (Finset.analyticAt_fun_sum _ fun i _ => (hΨ x i).mul (hQ i))
      · exact (hz.pow 2).div_const.mul
          (Finset.analyticAt_fun_sum _ fun i _ => (hΨ x i).mul (hΨ x i))
    · have hM := fun i => (an_svec φ hφ x i).sub (hh x i)
      exact (analyticAt_const.mul (hξ 1)).div_const.mul
        (Finset.analyticAt_fun_sum _ fun i _ => (hM i).mul (hM i))
  · simp only [hx, ↓reduceIte]; exact analyticAt_const

/-- `C₂(B)` is analytic jointly in the mass, the multiplier, `δφ` and `ξ`. -/
theorem an_renC2On (B : Finset (Torus d (N₀ * L ^ k))) (ξ : Q → Fin 3 → ℂ) (νu : Q → ℂ)
    (αu : Q → G.Ω 1 → ℂ) (δφ : Q → G.Ω 1 × Fin N → ℂ)
    (hξ : ∀ j, AnalyticAt ℂ (fun q => ξ q j) q) (hν : AnalyticAt ℂ νu q)
    (hα : ∀ y, AnalyticAt ℂ (fun q => αu q y) q)
    (hφ : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q => δφ q (y, i)) q) :
    AnalyticAt ℂ (fun q => renC2On G a B (ξ q) (νu q) (αu q) (δφ q)) q := by
  unfold renC2On
  refine Finset.analyticAt_fun_sum _ fun x _ => ?_
  unfold renC2Site
  refine (analyticAt_const.mul (analyticAt_const.add (hξ 2))).mul
    (Finset.analyticAt_fun_sum _ fun i _ => (hφ x i).mul ?_)
  have hA : ∀ y z : G.Ω 1, AnalyticAt ℂ
      (fun q => dirichletOperator G a 0 (αu q + fun _ => νu q) y z) q := by
    intro y z
    have hαν : AnalyticAt ℂ (fun q => (αu q + fun _ => νu q : G.Ω 1 → ℂ)) q :=
      analyticAt_pi_iff.2 fun w => (hα w).add hν
    exact (analyticAt_dirichletOperator_apply G a 0 _ y z).comp hαν
  have e : ∀ q, (liftOp N (dirichletOperator G a 0 (αu q + fun _ => νu q)) *ᵥ δφ q) (x, i) =
      ∑ y, dirichletOperator G a 0 (αu q + fun _ => νu q) x y * δφ q (y, i) := by
    intro q; rw [liftOp_mulVec]; rfl
  simp_rw [e]
  exact Finset.analyticAt_fun_sum _ fun y _ => (hA x y).mul (hφ y i)

end Analytic

section Principle

variable {G : GeneratingSet d L N₀ k ϱ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (G) in
/-- **The localization principle for one constituent** `f` (LOC I-4a/I-4b decoupling on the cover,
Lemma AE and GM; FLUCTUATION.md §3.6, proof of (g)): one family of terms `f_Y`, `Y ∈ 𝒴`, with
`f = ∑_Y f_Y` on `𝒟 × {|ξ|_∞ < r}`, jointly analytic and local on `Y`, such that at every `ξ`, if
`|f(·, ξ)| ≤ M` on the enlarged domain `𝒟⁺` (where the decoupled data lie), then
`|f_Y(·, ξ)| ≤ K_loc M e^{-κ d(Y)}` on `𝒟`. -/
def HasLocPrinciple (Dom Domp : BgData G N → Prop) (r : ℝ)
    (Ys : Finset (Finset (Torus d (N₀ * L ^ k)))) (dY : Finset (Torus d (N₀ * L ^ k)) → ℝ)
    (κ Kloc : ℝ) (f : BgData G N → (Fin 3 → ℂ) → E) : Prop :=
  ∃ term : Finset (Torus d (N₀ * L ^ k)) → RawData d L N₀ k N × (Fin 3 → ℂ) → E,
    (∀ D : BgData G N, Dom D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r →
      f D ξ = ∑ Y ∈ Ys, term Y ((D.Ψ, D.h), ξ)) ∧
    (∀ Y ∈ Ys, AnalyticOnNhd ℂ (term Y) (expDom G Dom r)) ∧
    (∀ Y ∈ Ys, ∀ q ∈ expDom G Dom r, ∀ q' ∈ expDom G Dom r, q.2 = q'.2 →
      RawAgree Y q.1 q'.1 → term Y q = term Y q') ∧
    (∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r → ∀ M : ℝ, (∀ D : BgData G N, Domp D → ‖f D ξ‖ ≤ M) →
      ∀ Y ∈ Ys, ∀ D : BgData G N, Dom D →
        ‖term Y ((D.Ψ, D.h), ξ)‖ ≤ Kloc * M * Real.exp (-κ * dY Y))

variable {Dom Domp : BgData G N → Prop} {r ρ κ Kloc c : ℝ}
  {Ys : Finset (Finset (Torus d (N₀ * L ^ k)))} {dY : Finset (Torus d (N₀ * L ^ k)) → ℝ}
  {f : BgData G N → (Fin 3 → ℂ) → E}

/-- The localization principle and a pointwise bound `|f(·, ξ)| ≤ c |ξ|_∞^p` on `𝒟⁺` give an
expansion on the polydisc of radius `ρ ≤ r` with the bound `K_loc c ρ^p`. -/
theorem HasLocPrinciple.isLocExp (h : HasLocPrinciple G Dom Domp r Ys dY κ Kloc f)
    (hK : 0 ≤ Kloc) (hc : 0 ≤ c) {p : ℕ}
    (hM : ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r → ∀ D : BgData G N, Domp D → ‖f D ξ‖ ≤ c * ‖ξ‖ ^ p)
    (hρ : ρ ≤ r) : ∃ term, IsLocExp G Dom ρ Ys dY κ (Kloc * c * ρ ^ p) f term := by
  obtain ⟨term, hsum, han, hloc, hbd⟩ := h
  refine ⟨term, fun D hD ξ hξ => hsum D hD ξ (hξ.trans_le hρ),
    fun Y hY => (han Y hY).mono (expDom_mono hρ),
    fun Y hY q hq q' hq' => hloc Y hY q (expDom_mono hρ hq) q' (expDom_mono hρ hq'), ?_⟩
  rintro Y hY q ⟨D, hD, hq1, hq2⟩
  have e : q = ((D.Ψ, D.h), q.2) := Prod.ext hq1 rfl
  rw [e]
  refine (hbd q.2 (hq2.trans_le hρ) _ (hM q.2 (hq2.trans_le hρ)) Y hY D hD).trans ?_
  have hp : ‖q.2‖ ^ p ≤ ρ ^ p := pow_le_pow_left₀ (norm_nonneg _) hq2.le p
  have he := (Real.exp_pos (-κ * dY Y)).le
  calc Kloc * (c * ‖q.2‖ ^ p) * Real.exp (-κ * dY Y)
      ≤ Kloc * (c * ρ ^ p) * Real.exp (-κ * dY Y) := by gcongr
    _ = Kloc * c * ρ ^ p * Real.exp (-κ * dY Y) := by ring

end Principle

section Input

variable (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)

/-- **The open inputs of Theorem 3.1 (g), (h)** (FLUCTUATION.md v2.3 §3.1 status, §3.6 proofs of
(g), (h); §6.5 items 1, 3).  Parameters: the base mass `ν`, the class radius `ε = ε_{k+1}`, the
enlarged radius `ε⁺` of the decoupled data, the polydisc radius `r₀`, the solution map `F` of
Lemma 3.5 (ii), the blocks `B_z` with their localization domains `𝒴_z` and the observable's
domains `𝒴^ℳ_p`, the size `d(Y)`, the rates `κ_a`, `κ_b`, the localization constant `K_loc`, and
the data of the open parts (the new contributions at `θ` and the pre-localized old-term
differences). -/
structure RenormExpInput (ν ε εp r₀ : ℝ)
    (F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    {ι : Type*} (blk : ι → Finset (Torus d (N₀ * L ^ k)))
    (Ys : ι → Finset (Finset (Torus d (N₀ * L ^ k))))
    (YsM : G.Ω 1 × Fin N → Finset (Finset (Torus d (N₀ * L ^ k))))
    (dY : Finset (Torus d (N₀ * L ^ k)) → ℝ) (κa κb Kloc BE0 Bold BM0 BoldM : ℝ)
    (E0θ oldE : ι → BgData G N → (Fin 3 → ℂ) → ℂ)
    (M0θ oldM : G.Ω 1 × Fin N → BgData G N → (Fin 3 → ℂ) → ℂ) : Prop where
  /-- (OPEN: cover/NC, Lemma 2.8, VMOD.md) LOC I-4b decoupling of `φ_{k+1}` and AE for `C₁(z)`
  (FLUCTUATION §3.6, proof of (g), first sentence). -/
  locC1 : ∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) (XiCOneReal G a ν εp) r₀ (Ys z) dY κa Kloc
    (fun D ξ => renC1On G a ν ε (blk z) D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) D) ξ)
  /-- (OPEN: cover/NC and the decoupled I-4a mode U at the complex mass `ν_u`) LOC I-4a for `δφ`
  with the sources of Lemma 3.5 (ii), decoupled with the same `s`, and AE, for `C₂(z)`. -/
  locC2 : ∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) (XiCOneReal G a ν εp) r₀ (Ys z) dY κa Kloc
    (fun D ξ => renC2On G a (blk z) ξ (renMassU ν ξ)
      (bgMultC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1)
  /-- (OPEN: Theorem 3.1 (a), I-8, at `θ = (1 + ζ) ψ` via (Ξ2)) the expansion of `ℰ''₀(z)(θ)`. -/
  expE0 : ∀ z, ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa BE0 (E0θ z) term
  /-- (OPEN: fluctuation I-5 (V0, simple variation) and Proposition 3.3) the expansion of the
  pre-localized old-term differences of (3.10) on the polydisc `r₀`, terms vanishing at `ξ = 0`. -/
  expOld : ∀ z, ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Bold (oldE z) term ∧
    ∀ Y ∈ Ys z, ∀ D : BgData G N, XiCOneReal G a ν ε D → term Y ((D.Ψ, D.h), 0) = 0
  /-- (OPEN: as `locC2`) LOC I-4a and AE for `δφ(x)` in (3.11). -/
  locDφ : ∀ p, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) (XiCOneReal G a ν εp) r₀ (YsM p) dY κb Kloc
    (fun D ξ => (F ((D.Ψ, D.h), ξ)).1 p)
  /-- (OPEN: Theorem 3.1 (b), I-8, at `θ`) the expansion of `β_k^{-1/2} ℳ''₀(x)(θ)`. -/
  expM0 : ∀ p, ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) r₀ (YsM p) dY κb BM0 (M0θ p) term
  /-- (OPEN: as `expOld`) the `ℳ^{(j)}`-differences of (3.11), terms vanishing at `ξ = 0`. -/
  expOldM : ∀ p, ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) r₀ (YsM p) dY κb BoldM (oldM p) term ∧
    ∀ Y ∈ YsM p, ∀ D : BgData G N, XiCOneReal G a ν ε D → term Y ((D.Ψ, D.h), 0) = 0

end Input

section Theorems

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν ε εp r₀ r B : ℝ}
  {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
  {ι : Type*} {blk : ι → Finset (Torus d (N₀ * L ^ k))}
  {Ys : ι → Finset (Finset (Torus d (N₀ * L ^ k)))}
  {YsM : G.Ω 1 × Fin N → Finset (Finset (Torus d (N₀ * L ^ k)))}
  {dY : Finset (Torus d (N₀ * L ^ k)) → ℝ} {κa κb Kloc BE0 Bold BM0 BoldM : ℝ}
  {E0θ oldE : ι → BgData G N → (Fin 3 → ℂ) → ℂ}
  {M0θ oldM : G.Ω 1 × Fin N → BgData G N → (Fin 3 → ℂ) → ℂ}

/-- **Theorem 3.1 (g), `C₁(z)`** (FLUCTUATION.md §3.6; P4 Prop 4.1): for `ξ` in the polydisc
`𝒫_{ε_R}`, `C₁(z)` has an expansion over `Y ∈ 𝒴_z` with terms analytic jointly on
`Ξ^c_{k+1}(1, ε) × 𝒫_{ε_R}`, local, bounded by `K_loc (2d + 14) ε⁺² W(B_z) ε_R e^{-κ_a d(Y)}`. -/
theorem thm31g_C1_of_input (H : BgHyp d L k ϱ a ν) (hε : 0 < ε) (hεp : ε ≤ εp)
    (hsm : (4 * d + 6) * ((2 * d + 1) * εp) ≤ 1) (hc1 : xiC1 d * εp ≤ bgC1 d L N)
    (hr₀ : r₀ ≤ 1 / 16)
    (I : RenormExpInput G a ν ε εp r₀ F blk Ys YsM dY κa κb Kloc BE0 Bold BM0 BoldM E0θ oldE M0θ oldM)
    (hK : 0 ≤ Kloc) {εR : ℝ} (hεR : εR ≤ r₀) (z : ι) :
    ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) εR (Ys z) dY κa
      (Kloc * ((2 * d + 14) * εp ^ 2 * blockWeight G (blk z)) * εR ^ 1)
      (fun D ξ => renC1On G a ν ε (blk z) D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) D) ξ) term := by
  have hεp0 : 0 < εp := hε.trans_le hεp
  have hW : 0 ≤ blockWeight G (blk z) := Finset.sum_nonneg fun x _ => by
    have := spacing_pos G (x := x); positivity
  refine (I.locC1 z).isLocExp hK (by positivity) (fun ξ hξ D hD => ?_) hεR
  have := norm_renC1On_le H hεp0 hsm hc1 hD hε.le hεp (hξ.le.trans hr₀) (blk z)
  calc _ ≤ (2 * d + 14) * εp ^ 2 * ‖ξ‖ * blockWeight G (blk z) := this
    _ = (2 * d + 14) * εp ^ 2 * blockWeight G (blk z) * ‖ξ‖ ^ 1 := by ring

/-- **Theorem 3.1 (g), `C₂(z)`** (FLUCTUATION.md §3.6; P4 Prop 4.1): with the solution map of
Lemma 3.5 (ii) on `Ξ^c(1, ε⁺)` (`‖δφ‖_*, |δα|₂ ≤ K₂ B |ξ|_∞`), `C₂(z)` expands with the bound
`K_loc (17/32) N (5 + K₁ C₁ ε⁺ + K₂ B r)(K₂ B)² W(B_z) ε_R² e^{-κ_a d(Y)}` — quadratic in the
polydisc radius. -/
theorem thm31g_C2_of_input (H : BgHyp d L k ϱ a ν) (hεp0 : 0 < εp)
    (hsm : (4 * d + 6) * ((2 * d + 1) * εp) ≤ 1) (hc1 : xiC1 d * εp ≤ bgC1 d L N)
    (hF : IsRenSol G a ν ε εp r B F) (hB0 : 0 ≤ B) (hr : r ≤ 1 / 16) (hr₀ : r₀ ≤ r)
    (I : RenormExpInput G a ν ε εp r₀ F blk Ys YsM dY κa κb Kloc BE0 Bold BM0 BoldM E0θ oldE M0θ oldM)
    (hK : 0 ≤ Kloc) {εR : ℝ} (hεR0 : 0 ≤ εR) (hεR : εR ≤ r₀) (z : ι) :
    ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) εR (Ys z) dY κa
      (Kloc * (17 / 32 * (N * ((5 + bgK1 d L N * (xiC1 d * εp) + cK2 d L N * B * r) *
        (cK2 d L N * B) ^ 2)) * blockWeight G (blk z)) * εR ^ 2)
      (fun D ξ => renC2On G a (blk z) ξ (renMassU ν ξ)
        (bgMultC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term := by
  have hW : 0 ≤ blockWeight G (blk z) := Finset.sum_nonneg fun x _ => by
    have := spacing_pos G (x := x); positivity
  have hK2 := cK2_pos d L N
  have hK1 := bgK1_pos d L N
  have hX := one_le_xiC1 d
  refine (I.locC2 z).isLocExp hK ?_ (fun ξ hξ D hD => ?_) hεR
  · have hr0 : 0 ≤ r := hεR0.trans (hεR.trans hr₀)
    positivity
  · have := norm_renC2On_le_renSol H hεp0 hsm hc1 hF hB0 hr hD.xiCOne (hξ.trans_le hr₀) (blk z)
    calc _ ≤ _ := this
      _ = 17 / 32 * (N * ((5 + bgK1 d L N * (xiC1 d * εp) + cK2 d L N * B * r) *
            (cK2 d L N * B) ^ 2)) * blockWeight G (blk z) * ‖ξ‖ ^ 2 := by ring

/-- **Theorem 3.1 (g), `ℰ_u(z)`** (FLUCTUATION.md §3.6, (3.10); P4 Prop 4.1): the sum of the
new contribution at `θ` and the old-term differences expands with the bound
`B_{E0} + B_old ε_R / r₀` — the factor `ε_R / r₀` is Cauchy's estimate on the terms of the
old-term differences, which vanish at `ξ = 0` (FLUCTUATION: "the `τ`-derivative is bounded by
Cauchy on `|τ| = c_r/ε`"; with `B_{E0} = (N L^d B_𝕃 + 1) K₀` from (a) and `B_old = C₅ E₀ r₀`
this is `(N L^d B_𝕃 + 1 + C₅ E₀ ε_R) K₀`). -/
theorem thm31g_Eu_of_input
    (I : RenormExpInput G a ν ε εp r₀ F blk Ys YsM dY κa κb Kloc BE0 Bold BM0 BoldM E0θ oldE M0θ oldM)
    (hr₀ : 0 < r₀) {εR : ℝ} (hεR : εR ≤ r₀) (z : ι) :
    ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) εR (Ys z) dY κa (BE0 + Bold * (εR / r₀))
      (fun D ξ => E0θ z D ξ + oldE z D ξ) term := by
  obtain ⟨t1, h1⟩ := I.expE0 z
  obtain ⟨t2, h2, h20⟩ := I.expOld z
  exact ⟨_, (h1.mono_radius hεR).add (h2.cauchy hr₀ hεR h20)⟩

/-- **Theorem 3.1 (h)** (FLUCTUATION.md §3.6, (3.11); P4 Prop 4.2): `ℳ(x) = β_k^{-1/2} ℳ''₀(θ)(x) +
δφ(x) + (ℳ^{(j)}-differences)` expands with the bound `B_{M0} + K_loc K₂ B ε_R + B_{old,M} ε_R / r₀`.
With `B_{M0} = ½ β^{-1/4} ξ_{k+1}^{(d-2)/2+γ-α₁}` from (b), `B = 8 ε⁺`,
`ε_{k+1} = α₀ ξ_{k+1}^{(d-2)/2+γ-α₁} L^{(k+1)(2γ-α₁)}`, this is the (H.7) bound with `c₉` replaced
by `½ β^{-1/4} + C₆ ε_R L^{(k+1)(2γ-α₁)}`. -/
theorem thm31h_of_input (hF : IsRenSol G a ν ε εp r B F) (hr₀r : r₀ ≤ r)
    (I : RenormExpInput G a ν ε εp r₀ F blk Ys YsM dY κa κb Kloc BE0 Bold BM0 BoldM E0θ oldE M0θ oldM)
    (hK : 0 ≤ Kloc) (hB0 : 0 ≤ B) (hr₀ : 0 < r₀) {εR : ℝ} (hεR : εR ≤ r₀) (p : G.Ω 1 × Fin N) :
    ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) εR (YsM p) dY κb
      (BM0 + Kloc * (cK2 d L N * B) * εR ^ 1 + BoldM * (εR / r₀))
      (fun D ξ => M0θ p D ξ + (F ((D.Ψ, D.h), ξ)).1 p + oldM p D ξ) term := by
  obtain ⟨t1, h1⟩ := I.expM0 p
  obtain ⟨t3, h3, h30⟩ := I.expOldM p
  have hK2 := cK2_pos d L N
  obtain ⟨t2, h2⟩ := (I.locDφ p).isLocExp (c := cK2 d L N * B) (p := 1) hK (by positivity)
    (fun ξ hξ D hD => by
      have hs := (hF.sup D hD.xiCOne ξ (hξ.trans_le hr₀r)).val (p.1 : Torus d (N₀ * L ^ k)) p.2
      rw [svec_of_mem] at hs
      calc ‖(F ((D.Ψ, D.h), ξ)).1 p‖ ≤ cK2 d L N * (B * ‖ξ‖) := hs
        _ = cK2 d L N * B * ‖ξ‖ ^ 1 := by ring) hεR
  exact ⟨_, ((h1.mono_radius hεR).add h2).add (h3.cauchy hr₀ hεR h30)⟩

end Theorems

section Witness

variable {G : GeneratingSet d L N₀ k ϱ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The localization principle with the single polymer `𝕋` (finite volume, `K_loc = 1`, `d = 0`)
for any function with an analytic raw form. -/
theorem hasLocPrinciple_single {Dom : BgData G N → Prop} {r κ : ℝ}
    {f : BgData G N → (Fin 3 → ℂ) → E} (g : RawData d L N₀ k N × (Fin 3 → ℂ) → E)
    (hfg : ∀ D : BgData G N, Dom D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r → f D ξ = g ((D.Ψ, D.h), ξ))
    (hg : AnalyticOnNhd ℂ g (expDom G Dom r)) :
    HasLocPrinciple G Dom Dom r {Finset.univ} (fun _ => 0) κ 1 f := by
  refine ⟨fun _ => g, fun D hD ξ hξ => by rw [Finset.sum_singleton]; exact hfg D hD ξ hξ,
    fun Y _ => hg, fun Y hY q _ q' _ h2 hag => ?_, fun ξ hξ M hM Y _ D hD => ?_⟩
  · rw [Finset.mem_singleton] at hY
    subst hY
    have h1 : q.1 = q'.1 := Prod.ext (funext fun x => (hag x (Finset.mem_univ x)).1)
      (funext fun x => (hag x (Finset.mem_univ x)).2)
    have e : q = q' := Prod.ext h1 h2
    rw [e]
  · show ‖g ((D.Ψ, D.h), ξ)‖ ≤ 1 * M * Real.exp (-κ * 0)
    rw [← hfg D hD ξ hξ]
    simpa using hM D hD

/-- The zero expansion over the single polymer `𝕋`. -/
theorem isLocExp_zero {Dom : BgData G N → Prop} {r κ : ℝ} :
    IsLocExp G Dom r {Finset.univ} (fun _ => 0) κ 0 (fun _ _ => (0 : E)) (fun _ _ => 0) where
  sum_eq D _ ξ _ := by simp
  analytic Y _ := analyticOnNhd_const
  local_ Y _ q _ q' _ _ _ := rfl
  bound Y _ q _ := by simp

variable (a : ℕ → ℝ)

/-- **Inhabitation of `RenormExpInput`** (hard rule 10) for admissible parameters: the one-polymer
cover `𝒴 = {𝕋}` with `d = 0`, `K_loc = 1`, `ε⁺ = ε`, zero data for the new contributions and the
old-term differences; the localization principles hold with the raw analytic forms of `C₁(z)`,
`C₂(z)`, `δφ(x)` (`an_renC1On`, `an_renC2On`, the analyticity of the Lemma 3.5 map). -/
theorem renormExpInput_witness {ν ε r B r₀ : ℝ} (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hF : IsRenSol G a ν ε ε r B F) (hr₀ : r₀ ≤ r) (hr16 : r₀ ≤ 1 / 16) {ι : Type*}
    (blk : ι → Finset (Torus d (N₀ * L ^ k))) (κa κb : ℝ) :
    RenormExpInput G a ν ε ε r₀ F blk (fun _ => {Finset.univ}) (fun _ => {Finset.univ})
      (fun _ => 0) κa κb 1 0 0 0 0 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
      (fun _ _ _ => 0) := by
  obtain ⟨Fbg, hFan, hFeq⟩ := theorem72_analytic (G := G) (a := a) (ν := ν) (N := N) H
  have hU : ∀ D : BgData G N, XiCOneReal G a ν ε D →
      InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D := fun D hD =>
    (hD.xiCOne.bg H hsm hε hc1).1
  -- analyticity of the background map and of the Lemma 3.5 map at the points of the domain
  have hFa : ∀ q ∈ expDom G (XiCOneReal G a ν ε) r₀,
      AnalyticAt ℂ (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => Fbg q'.1) q := by
    rintro q ⟨D, hD, hq1, -⟩
    exact (hFan _ ⟨D, hU D hD, hq1⟩).comp (aa_fst' q)
  have hFs : ∀ q ∈ expDom G (XiCOneReal G a ν ε) r₀, AnalyticAt ℂ F q := by
    rintro q ⟨D, hD, hq1, hq2⟩
    exact hF.analytic q ⟨D, hD.xiCOne, hq1, hq2.trans_le hr₀⟩
  have hξ : ∀ (q : RawData d L N₀ k N × (Fin 3 → ℂ)) (j : Fin 3),
      AnalyticAt ℂ (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => q'.2 j) q := fun q j => by
    fun_prop
  refine ⟨fun z => ?_, fun z => ?_, fun z => ⟨_, isLocExp_zero⟩,
    fun z => ⟨_, isLocExp_zero, fun _ _ _ _ => rfl⟩, fun p => ?_, fun p => ⟨_, isLocExp_zero⟩,
    fun p => ⟨_, isLocExp_zero, fun _ _ _ _ => rfl⟩⟩
  · -- `C₁(z)`
    refine hasLocPrinciple_single
      (fun q => renC1On G a ν ε (blk z) q.1.1 q.1.2 (Fbg q.1).1 q.2)
      (fun D hD ξ _ => by simp only [hFeq D (hU D hD)]) fun q hq => ?_
    have hφ : ∀ (y : G.Ω 1) (i : Fin N), AnalyticAt ℂ
        (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => (Fbg q'.1).1 (y, i)) q :=
      fun y i => (aa_eval' (y, i) _).comp ((aa_fst' _).comp (hFa q hq))
    have hΨ : ∀ (x : Torus d (N₀ * L ^ k)) (i : Fin N),
        AnalyticAt ℂ (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => q'.1.1 x i) q :=
      fun x i => by fun_prop
    have hh : ∀ (x : Torus d (N₀ * L ^ k)) (i : Fin N),
        AnalyticAt ℂ (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => q'.1.2 x i) q :=
      fun x i => by fun_prop
    have key := an_renC1On (G := G) (q := q) a ν ε (blk z)
      (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => q'.1.1)
      (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => q'.1.2)
      (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => (Fbg q'.1).1)
      (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => q'.2) hΨ hh hφ (hξ q)
    exact key
  · -- `C₂(z)`
    refine hasLocPrinciple_single
      (fun q => renC2On G a (blk z) q.2 (renMassU ν q.2) ((Fbg q.1).2 + (F q).2) (F q).1)
      (fun D hD ξ _ => by simp only [hFeq D (hU D hD)]) fun q hq => ?_
    obtain ⟨D, hD, hq1, hq2⟩ := hq
    have hne : 1 + q.2 2 ≠ 0 := one_add_ne_zero_of_norm (by linarith) 2
    have hm : AnalyticAt ℂ (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => renMassU ν q'.2) q := by
      unfold renMassU
      exact (analyticAt_const.mul (analyticAt_const.add (hξ q 1))).div
        (analyticAt_const.add (hξ q 2)) hne
    have hq : q ∈ expDom G (XiCOneReal G a ν ε) r₀ := ⟨D, hD, hq1, hq2⟩
    have hα : ∀ y : G.Ω 1, AnalyticAt ℂ
        (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => ((Fbg q'.1).2 + (F q').2) y) q := fun y =>
      ((aa_eval' y _).comp ((aa_snd' _).comp (hFa q hq))).add
        ((aa_eval' y _).comp ((aa_snd' _).comp (hFs q hq)))
    have hφ : ∀ (y : G.Ω 1) (i : Fin N), AnalyticAt ℂ
        (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => (F q').1 (y, i)) q :=
      fun y i => (aa_eval' (y, i) _).comp ((aa_fst' _).comp (hFs q hq))
    exact an_renC2On a (blk z) (fun q' => q'.2) (fun q' => renMassU ν q'.2)
      (fun q' => (Fbg q'.1).2 + (F q').2) (fun q' => (F q').1) (hξ q) hm hα hφ
  · -- `δφ(x)`
    refine hasLocPrinciple_single (fun q => (F q).1 p) (fun D _ ξ _ => rfl) fun q hq => ?_
    exact (aa_eval' p _).comp ((aa_fst' _).comp (hFs q hq))

/-- **`RenormExpInput` is inhabited for admissible parameters** (hard rule 10): for every generating
set and mass with the hypotheses of Theorem 5.2, every family of blocks and every pair of rates,
there are `ε, r₀ > 0`, a solution map `F` of Lemma 3.5 (ii), and inputs with these parameters. -/
theorem nonempty_renormExpInput {ν : ℝ} (H : BgHyp d L k ϱ a ν) {ι : Type*}
    (blk : ι → Finset (Torus d (N₀ * L ^ k))) (κa κb : ℝ) :
    ∃ ε r₀ : ℝ, 0 < ε ∧ 0 < r₀ ∧ ∃ F, IsRenSol (N := N) G a ν ε ε r₀ (8 * ε) F ∧
      RenormExpInput G a ν ε ε r₀ F blk (fun _ => {Finset.univ}) (fun _ => {Finset.univ})
        (fun _ => 0) κa κb 1 0 0 0 0 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun _ _ _ => 0) := by
  obtain ⟨ε, r, hε, hr, hr16, hsm, hc1, F, hF⟩ := exists_isRenSol_params (N := N) (G := G) H
  exact ⟨ε, r, hε, hr, F, hF, renormExpInput_witness a H hε hsm hc1 hF le_rfl hr16 blk κa κb⟩

end Witness

end Balaban.Fluctuation
