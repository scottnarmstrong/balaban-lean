/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Analysis.CutExpansion
public import Balaban.Localization.DecoupledCovAnalyticFull
public import Balaban.Localization.DecoupledCovPrincipal
public import Balaban.Fluctuation.StepComplexOut
public import Balaban.Inhabited.LocalizationSettings
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The rooted determinant on the cut chart, at fixed fields (ROOTDET §1, §2, §4 package 1)

The normalization factor of the fluctuation step contributes `-(1/2) ∑_{y ∈ B} tr 𝕃(y,y)` for a
block `B`, `𝕃` the matrix logarithm.  A localized expansion starts from the *decoupled* logarithm
`decLog`, which depends on the cut parameters `s : cubeIdx G' → ℂ` and is jointly analytic on
`DecDom`.  At fixed fields `(φ, α)` this file proves:

* `rootTrace`: the rooted trace `-(1/2) ∑_{y ∈ B} ∑_i 𝕃(s)_{(y,i),(y,i)}`; `analyticOnNhd_rootTrace`
  (joint analyticity on `DecDom`) and `norm_rootTrace_le` (the bound
  `(1/2) N |B| covBLog`, `covBLog = covBLog d L a_k (a₁ / L²) κ`);
* `rootTrace_one_eq_sum_mixDiff`: the value at `s = 1` is `∑_{J ⊆ cubeIdx} Δ_J`, `Δ_J = mixDiff J`
  the `J`-th mixed difference between the cut values `0` and `1` (`Balaban/Analysis/CutExpansion`);
* `norm_mixDiff_rootTrace_le`: `‖Δ_J‖ ≤ (1/2) N |B| covBLog · (2 / e^κ)^{|J|}` (Schwarz lemma
  on each cut disc of radius `R = e^κ`; constant `2 / R`).  The factor `q = 2 / e^κ` is `< 1`
  exactly when `e^κ > 2`;
* `rootTrace_one_eq_logAC`, `sum_rootTrace_one_eq_halfLogDetCC`: at `s = 1` and the step
  background the rooted trace is `-(1/2)` times the block trace of `S.logAC`, and the blocks add
  up to `halfLogDetCC`;
* `rootDet_hypotheses_nonempty`: the hypotheses are satisfiable with `e^κ > 2`.

## What this file does not do

* **DET-CHART** (ROOTDET §1) is not built: a cut-dependent background family `(φ_s, α_s)` of the
  datum on the step chart, analytic in the datum, with `(φ_1, α_1) = (svec bgFieldC, bgMultC)`.
  Here `(φ, α)` are held fixed, so `s ↦ rootTrace` is a cut family at one background only.  The
  landed candidate is `Localization/Decoupled2Background.lean`, `i4b_analytic`.
* The bound on `Δ_J` has no support information.  The vanishing of `Δ_J` for `J` not connected to
  the root (DET-CUT-FACTOR) and the count of `J` per cube set (DET-HULL-COUNT) are separate
  packages.
* `Δ_J` is the integral-free (difference) form of `∫_{[0,1]^J} ∂_J F (s_J, 0)`; no `DetExpansionC`
  is constructed.

## Dependence on `κ`

`covBLog d L a_k b κ = max |log a_k| |log (a_k + b)| + covB4 d L a_k κ / a_k`, so the bound grows
with `κ` through `covB4` (`covB4 = √(covBsq)`), while the geometric factor `2 / e^κ` decreases.
The hypothesis `cstarX d L · exp (N0 d L · κ) ≤ L^{m₁}` bounds `κ` above for fixed `m₁`
(`κ ≤ (m₁ log L - log cstarX) / N0`), with `N0 = 3 (8L)^d`; and `δ² smallConstX d L κ ≤ 1/4` shrinks
the allowed `δ` as `κ` grows.  So `e^κ > 2` needs `m₁` large; see `rootDet_hypotheses_nonempty`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Finset Matrix

section Trace

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι]

/-- **The rooted trace** `-(1/2) ∑_{y ∈ B} ∑_i 𝕃(s)_{(y,i),(y,i)}` of the decoupled logarithm
`𝕃(s) = decLog …(extS G s)…` over a set `B` of sites (the block of the root), at the cut
parameters `s`, the field `φ` and the potential `α`. -/
noncomputable def rootTrace (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ)
    (aT ν : ℝ) (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) (B : Finset κι)
    (s : DecParams G) (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (α : G.Ω 1 → ℂ) : ℂ :=
  -(1 / 2 : ℂ) * ∑ y ∈ B, ∑ i : Fin N, decLog G a aT ν α (extS G s) φ Q P (y, i) (y, i)

variable {a : ℕ → ℝ} {aT ν : ℝ} {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

/-- An entry of a matrix whose operator `ℓ²`-bound is `c ≥ 0` is bounded by `c`. -/
theorem norm_entry_le_of_sqNorm {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ f : ι → ℂ, Green.sqNorm (M *ᵥ f) ≤ c ^ 2 * Green.sqNorm f)
    (p q : ι) : ‖M p q‖ ≤ c := by
  have h1 := h (Pi.single q 1)
  have hs : Green.sqNorm (Pi.single q (1 : ℂ) : ι → ℂ) = 1 := by
    unfold Green.sqNorm
    rw [Finset.sum_eq_single q]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hcol : (M *ᵥ (Pi.single q (1 : ℂ) : ι → ℂ)) p = M p q := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h2 : ‖M p q‖ ^ 2 ≤ Green.sqNorm (M *ᵥ (Pi.single q (1 : ℂ) : ι → ℂ)) := by
    unfold Green.sqNorm
    rw [← hcol]
    exact Finset.single_le_sum (f := fun i => ‖(M *ᵥ (Pi.single q (1 : ℂ) : ι → ℂ)) i‖ ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ p)
  rw [hs, mul_one] at h1
  exact le_of_sq_le_sq (h2.trans h1) hc |>.trans_eq rfl

/-- **(D1) analyticity of the rooted trace**: jointly analytic in `(s, φ, α)` on `DecDom`. -/
theorem analyticOnNhd_rootTrace (S : XSetting G a aT ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hU : IsUnitLattice G Q P) (B : Finset κι) :
    AnalyticOnNhd ℂ (fun e : DecData G N => rootTrace G a aT ν Q P B e.1 e.2.1 e.2.2)
      (DecDom G N κ δ) := by
  unfold rootTrace
  refine fun e he => analyticAt_const.mul ?_
  refine Finset.analyticAt_fun_sum _ fun y _ => Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact analyticOnNhd_decLog_entry (N := N) S hκ hM hδ hsm hU (y, i) (y, i) e he

/-- **(D3) the uniform bound of the rooted trace** on `DecDom`:
`‖rootTrace‖ ≤ (1/2) N |B| covBLog d L a_k (a₁/L²) κ`. -/
theorem norm_rootTrace_le (S : XSetting G a aT ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hU : IsUnitLattice G Q P) (B : Finset κι)
    {e : DecData G N} (he : e ∈ DecDom G N κ δ) :
    ‖rootTrace G a aT ν Q P B e.1 e.2.1 e.2.2‖ ≤
      (1 / 2 : ℝ) * N * B.card * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ := by
  have H := covStanding_of_mem S hκ hM hδ hsm hU he
  have hc : 0 ≤ covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ := by
    unfold covBLog
    have := covB4_nonneg d L (a k) κ
    have := H.hak
    positivity
  have hent : ∀ y i, ‖decLog G a aT ν e.2.2 (extS G e.1) e.2.1 Q P (y, i) (y, i)‖ ≤
      covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ := fun y i =>
    norm_entry_le_of_sqNorm hc (fun f => decLog_bound H f) (y, i) (y, i)
  unfold rootTrace
  rw [norm_mul]
  have hhalf : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [hhalf]
  have hsum : ‖∑ y ∈ B, ∑ i : Fin N, decLog G a aT ν e.2.2 (extS G e.1) e.2.1 Q P (y, i) (y, i)‖
      ≤ B.card * (N * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ y ∈ B, ‖∑ i : Fin N, decLog G a aT ν e.2.2 (extS G e.1) e.2.1 Q P (y, i) (y, i)‖
        ≤ ∑ _y ∈ B, (N * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ) := by
          refine Finset.sum_le_sum fun y _ => (norm_sum_le _ _).trans ?_
          calc ∑ i : Fin N, ‖decLog G a aT ν e.2.2 (extS G e.1) e.2.1 Q P (y, i) (y, i)‖
              ≤ ∑ _i : Fin N, covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ :=
                Finset.sum_le_sum fun i _ => hent y i
            _ = N * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ := by simp
      _ = B.card * (N * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ) := by simp
  calc (1 / 2 : ℝ) * ‖∑ y ∈ B, ∑ i : Fin N, decLog G a aT ν e.2.2 (extS G e.1) e.2.1 Q P (y, i) (y, i)‖
      ≤ (1 / 2 : ℝ) * (B.card * (N * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

/-- **(D4)–(D5) at fixed fields**: for admissible fixed fields `(φ, α)` (strict constraint field
and strict potential bound) and `R = e^κ > 1`, the value at `s = 1` of the rooted trace is the sum
over subsets `J` of cut parameters of the mixed differences `Δ_J`, each bounded by
`(1/2) N |B| covBLog · (2 / e^κ)^{|J|}`.  The factor `2 / e^κ` is `< 1` exactly when `e^κ > 2`. -/
theorem rootTrace_cut_expansion (S : XSetting G a aT ν) {κ : ℝ} (hκ : 0 < κ)
    (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hU : IsUnitLattice G Q P) (B : Finset κι)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hφ : IsConstraintFieldStrict G δ φ)
    {α : G.Ω 1 → ℂ}
    (hα : ∀ w, ‖α w‖ < coerciveConst d / (2 * (G.spacing (w : CTorus d L N₁ m₁ (k + 1))) ^ 2)) :
    rootTrace G a aT ν Q P B (fun _ => 1) φ α =
        ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset,
          mixDiff J (fun s => rootTrace G a aT ν Q P B s φ α) ∧
      ∀ J : Finset (cubeIdx G),
        ‖mixDiff J (fun s => rootTrace G a aT ν Q P B s φ α)‖ ≤
          (1 / 2 : ℝ) * N * B.card * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ *
            (2 / Real.exp κ) ^ J.card := by
  classical
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hmem : ∀ s ∈ cutPolydisc (cubeIdx G) (Real.exp κ), ((s, (φ, α)) : DecData G N) ∈
      DecDom G N κ δ := fun s hs => ⟨hs, hφ, hα⟩
  refine ⟨sum_mixDiff (fun s => rootTrace G a aT ν Q P B s φ α), fun J => ?_⟩
  refine norm_mixDiff_le hR J ?_ ?_
  · intro s hs
    have h := analyticOnNhd_rootTrace (N := N) S hκ.le hM hδ hsm hU B
      ((s, (φ, α)) : DecData G N) (hmem s hs)
    have hc : AnalyticAt ℂ (fun s : DecParams G => ((s, (φ, α)) : DecData G N)) s :=
      AnalyticAt.prod analyticAt_id analyticAt_const
    exact (AnalyticAt.comp (g := fun e : DecData G N => rootTrace G a aT ν Q P B e.1 e.2.1 e.2.2)
      (f := fun s : DecParams G => ((s, (φ, α)) : DecData G N)) h hc).differentiableAt.differentiableWithinAt
  · intro s hs
    exact norm_rootTrace_le (N := N) S hκ.le hM hδ hsm hU B (e := ((s, (φ, α)) : DecData G N)) (hmem s hs)

end Trace

/-! ### The endpoint `s = 1` -/

section Endpoint

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **The endpoint `s = 1` is the landed `logAC`**: with the step background
`φ = svec (bgFieldC)`, `α = bgMultC` (the arguments of `StepSetting.logAC`), the rooted trace at
`s = 1` over the block of `z` is `-(1/2)` times the block trace of `S.logAC`. -/
theorem rootTrace_one_eq_logAC (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    rootTrace S.G' S.a S.a₁ S.ν (unitQ S.G') (unitP S.G') (S.blockU z) (fun _ => 1)
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))
        (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') =
      -(1 / 2 : ℂ) * ∑ y ∈ S.blockU z, ∑ i : Fin N, S.logAC (y, i) (y, i) := by
  unfold rootTrace StepSetting.logAC
  rw [Balaban.Localization.extS_one]

/-- The blocks add up: the rooted traces at `s = 1` over the blocks of all `z` sum to
`halfLogDetCC`. -/
theorem sum_rootTrace_one_eq_halfLogDetCC :
    ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      rootTrace S.G' S.a S.a₁ S.ν (unitQ S.G') (unitP S.G') (S.blockU z) (fun _ => 1)
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))
        (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') = S.halfLogDetCC := by
  simp_rw [rootTrace_one_eq_logAC S]
  exact S.sum_trace_E0locC

end Endpoint

/-! ### Non-vacuity -/

section Inhabited

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- For every generating set with `d > 0`, every `N > 0` and `δ > 0`, `κ`, the point
`(s, φ, α) = (0, e₀, 0)` (constant field `e₀`, zero potential, all cuts `0`) lies in `DecDom`. -/
theorem zero_mem_decDom (hd : 0 < d) (hN : 0 < N) (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (κ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (((fun _ => 0 : DecParams G)),
      ((fun _ i => if i = (⟨0, hN⟩ : Fin N) then 1 else 0 :
        CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ), (0 : G.Ω 1 → ℂ))) ∈ DecDom G N κ δ := by
  refine ⟨fun P => by simpa using Real.exp_pos _, ⟨?_, ?_, ?_, ?_⟩, fun w => ?_⟩
  · intro x hx μ
    have hs := spacing_pos G (x := x)
    refine ⟨?_, ?_⟩ <;> simp [vn] <;> positivity
  · intro x hx
    have hs := spacing_pos G (x := x)
    have h0 : (fun i : Fin N => ∑ μ : Fin d,
        ((if i = (⟨0, hN⟩ : Fin N) then (1 : ℂ) else 0) + (if i = (⟨0, hN⟩ : Fin N) then 1 else 0) -
          2 * (if i = (⟨0, hN⟩ : Fin N) then 1 else 0))) = fun _ => 0 := by
      funext i; simp only [sub_eq_zero.mpr (by ring : _ + _ = (2 : ℂ) * _), Finset.sum_const_zero]
    simp only [h0]
    simp [vn]
    rw [show (WithLp.toLp 2 (fun _ : Fin N => (0 : ℂ))) = 0 from rfl, norm_zero]
    positivity
  · intro x hx
    have : vn (fun i : Fin N => if i = (⟨0, hN⟩ : Fin N) then (1 : ℂ) else 0) = 1 := by
      simp [vn, EuclideanSpace.norm_eq, apply_ite norm, Finset.sum_ite_eq']
    simp only [this]; norm_num
  · intro x hx
    simpa using hδ
  · have hs := spacing_pos G (x := (w : CTorus d L N₁ m₁ (k + 1)))
    have := coerciveConst_pos hd
    simp only [Pi.zero_apply, norm_zero]
    positivity

open Balaban.Inhabited Balaban.Localization.I5Inhabited

/-- **The hypotheses of `rootTrace_cut_expansion` are satisfiable with `e^κ > 2`**, at the
positive scale of `Balaban/Inhabited/LocalizationSettings` (`d = L = 3`, `N = 3`, `N₁ = 6`,
`k = 1`, `a = compWeight 3 1`, `ν = 0`, `G = GP m₁ (rhoSep m₁)`): `κ = log 3`, `m₁ = m₀ + N0 3 3`
where `cstarX 3 3 ≤ 3^{m₀}` (`exists_m₁`), `δ = 1 / (2 (smallConstX + 1))`, the constant field
`φ = e₀`, `α = 0`, and the cut point `s = 0`.  Then the geometric factor is `2/3 < 1`. -/
theorem rootDet_hypotheses_nonempty :
    ∃ (m₁ : ℕ) (ϱ : ℝ) (G : GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) ϱ) (κ δ : ℝ)
      (φ : CTorus 3 3 6 m₁ (1 + 1) → Fin 3 → ℂ) (α : G.Ω 1 → ℂ),
      XSetting G (compWeight 3 1) 1 0 ∧ 0 ≤ κ ∧ 2 < Real.exp κ ∧
      cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ ∧ 0 < δ ∧
      δ ^ 2 * smallConstX 3 3 κ ≤ 1 / 4 ∧ IsUnitLattice G (unitQ G) (unitP G) ∧
      (((fun _ => 0 : DecParams G)), (φ, α)) ∈ DecDom G 3 κ δ := by
  obtain ⟨m₀, h4, hc⟩ := exists_m₁_cstar
  have hS : 0 < smallConstX 3 3 (Real.log 3) := smallConstX_pos 3 3 _
  generalize hSd : smallConstX 3 3 (Real.log 3) = S at hS
  have hδ0 : 0 < 1 / (2 * (S + 1)) := by positivity
  refine ⟨m₀ + N0 3 3, rhoSep (m₀ + N0 3 3), GP (m₀ + N0 3 3) (rhoSep (m₀ + N0 3 3)),
    Real.log 3, 1 / (2 * (S + 1)), _, 0, xSetting_pos (by omega),
    Real.log_nonneg (by norm_num), ?_, ?_, hδ0, ?_,
    (isUnitLatticeB_unit (G := GP (m₀ + N0 3 3) (rhoSep (m₀ + N0 3 3)))).toIsUnitLattice,
    zero_mem_decDom (by norm_num) (by norm_num : 0 < 3) _ _ hδ0⟩
  · rw [Real.exp_log (by norm_num)]; norm_num
  · rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    calc cstarX 3 3 * (3 : ℝ) ^ N0 3 3 ≤ (3 : ℝ) ^ m₀ * (3 : ℝ) ^ N0 3 3 :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = ((3 : ℕ) : ℝ) ^ (m₀ + N0 3 3) := by push_cast; rw [pow_add]
  · generalize hδ : 1 / (2 * (S + 1)) = δ at hδ0
    have h1 : 2 * δ * (S + 1) = 1 := by rw [← hδ]; field_simp
    have h2 : S ≤ (S + 1) ^ 2 := by nlinarith
    have h3 : δ ^ 2 * S ≤ δ ^ 2 * (S + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    nlinarith

end Inhabited

end Balaban.Fluctuation
