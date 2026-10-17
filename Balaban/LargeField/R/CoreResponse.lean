/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.FarDecayUncond
public import Balaban.LargeField.R.PsiZeroData
public import Balaban.LargeField.R.PsiZeroTube
public import Balaban.LargeField.LF1.Struct
import Balaban.LargeField.Base.BaseBackgroundIdent
import Balaban.LargeField.R.PsiZeroAnalyticLocal
import Balaban.Multiscale.PathMetricBounds
import Balaban.Localization.DecoupledBounds
import Balaban.Background.CompositionEstimates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The core-to-action response of the massless background: one-site bounds (Q13-SHARED (2.4))

For a generating set `G` at level `k` and a real block field `ψ_k` on the `k`-blocks, `φ⁰(ψ_k) = bgField G a 0
(dataR G ψ_k)` is the massless Def-5 background of the lifted data.  A change of `ψ_k` on a set `Z_f` of
`k`-blocks changes the lifted data on the fine sites of these blocks only, and Lemma 4.1
(`lemma41_domain_uncond`, from the weighted Proposition 5.1 `weightedProp51S_exists`) bounds the response:

* `coreResponse_farBounds`: for `ψ, ψ'` in the tubes `Ψ̃(𝔹; τ)`, `Ψ̃(𝔹; τ')` (`K₁ τ ≤ min(δ_*, δ_w)`) that agree off
  `Z_f` and differ by at most `t ≤ min(δ_*, δ_w)` on each block of `Z_f`, the differences of the backgrounds and of
  the multipliers satisfy `FarBounds` with rate `γ_w = gammaW d` and constant `K_w C_F t`:
  `|δφ(x)|, ℓ(x)|∂δφ(x)|, ℓ(x)²|Δδφ(x)|, ℓ(x)²|δα(x)| ≤ K_w C_F t e^{-γ_w d(x, W)}`, `W` the fine sites of `Z_f`
  (`d` the multiscale path distance to the `Ω₁`-shadow of `W`);
* `coreResponse_deriv_le` (deliverable (1)): the one-site derivative
  `J_{x i, z j} = ∂ φ⁰(ψ_k)(x, i) / ∂ ψ_k(z)_j` (the real derivative along `ψ_k + t e_{z j}`, written with `deriv`)
  satisfies `|J_{x i, z j}| ≤ K_w C_F e^{-γ_w d(x, W_z)}`, `W_z` the fine sites of the block `z`;
* `decay_shadow_fib_le`, `coreResponse_deriv_le_pathDist`: if the block `z` lies in the top layer `Ω_k` of `G`
  (`OverTop G {z}`), the decay from the shadow of `W_z` is at most `e^{γ(2d+1)}` times the decay from any site `y`
  of the block: `|J_{x i, z j}| ≤ K_w C_F e^{γ_w (2d+1)} e^{-γ_w d(x, y)}`.

The constants `K_w, δ_w > 0` depend only on `(d, L, N)`; `C_F = cF d L = 3 + 2 d L²`, `γ_w = agmonRate d / 8`.
The generating set lives on a torus of side `N₁ L^{m₁} L^k` (the carrier of Lemma 4.1).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization Filter Topology

section Decay

/-- **Comparison of decay factors**: if `D' ≤ D + c` then `e^{-γ D} ≤ e^{γ c} e^{-γ D'}` (`decay γ ⊤ = 0`). -/
theorem decay_le_exp_mul_decay {γ c : ℝ} (hγ : 0 ≤ γ) (hc : 0 ≤ c) {D D' : ENNReal}
    (h : D' ≤ D + ENNReal.ofReal c) : decay γ D ≤ Real.exp (γ * c) * decay γ D' := by
  by_cases hD : D = ⊤
  · rw [hD, decay_top]
    exact mul_nonneg (Real.exp_pos _).le (decay_nonneg _ _)
  · have hD' : D' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hD, ENNReal.ofReal_ne_top⟩) h
    rw [decay_of_ne_top hD, decay_of_ne_top hD', ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : D'.toReal ≤ D.toReal + c := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hD, ENNReal.ofReal_ne_top⟩) h
      rwa [ENNReal.toReal_add hD ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc] at this
    nlinarith

end Decay

section Response

variable {d L N : ℕ} [NeZero L]

/-- **The response of the massless background to a change of the block field on a set of blocks**, for constants
`(K_w, δ_w)` of the weighted Proposition 5.1 (`WeightedProp51S`, inhabited by `weightedProp51S_exists`): for `ψ, ψ'`
in `Ψ̃(𝔹; τ)`, `Ψ̃(𝔹; τ')` (`τ, τ' ≤ c₁`, `K₁ τ ≤ min(δ_*, δ_w)`) that agree off the set `Z_f` of `k`-blocks and
differ by at most `t ≤ min(δ_*, δ_w)` on each block of `Z_f`, the background and multiplier differences satisfy
`FarBounds` with rate `γ_w` and constant `K_w C_F t` from the `Ω₁`-shadow of the fine sites of `Z_f`. -/
theorem coreResponse_farBounds_of_weighted {Kw δw : ℝ} (hWP : WeightedProp51S d L N Kw δw) (hd0 : 0 < d)
    {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ}
    (H : BgHyp d L k ϱ a 0) (hOp : Dec2.OpSetting G a 0) {τ τ' : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ bgC1 d L N)
    (hτs : bgK1 d L N * τ ≤ min (deltaStar d L N) δw) (hτ' : 0 < τ') (hτ1' : τ' ≤ bgC1 d L N)
    {ψ ψ' : BlockField d L (N₁ * L ^ m₁) k N} (ht : TubeOn G Set.univ τ ψ) (ht' : TubeOn G Set.univ τ' ψ')
    (Zf : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))) (hoff : ∀ z ∉ Zf, ψ' z = ψ z) {t : ℝ}
    (ht0 : 0 ≤ t) (hts : t ≤ min (deltaStar d L N) δw) (hdiff : ∀ z ∈ Zf, rn (fun i => ψ' z i - ψ z i) ≤ t) :
    FarBounds G (shadow G (Zf.biUnion (fib d L (N₁ * L ^ m₁) k k))) (gammaW d) (Kw * (cF d L * t))
      (bgField G a 0 (dataR G ψ') - bgField G a 0 (dataR G ψ))
      (bgMult G a 0 (dataR G ψ') - bgMult G a 0 (dataR G ψ)) := by
  have hc10 := bgC1_le_bgC0 d L N hd0
  have hD : InDomainC G 0 τ τ (dataR G ψ) := Base.inDomainC_of_inDomainR hτ (inDomainR_of_tube G hτ ht)
  have hD' : InDomainC G 0 τ' τ' (dataR G ψ') :=
    Base.inDomainC_of_inDomainR hτ' (inDomainR_of_tube G hτ' ht')
  set W := Zf.biUnion (fib d L (N₁ * L ^ m₁) k k) with hW
  have hmemW : ∀ x, x ∈ W ↔ jBlock d L (N₁ * L ^ m₁) k k x ∈ Zf := by
    intro x
    rw [hW, Finset.mem_biUnion]
    constructor
    · rintro ⟨z, hz, hx⟩
      rw [mem_fib] at hx
      rw [← hx] at hz
      exact hz
    · intro hx
      exact ⟨_, hx, mem_fib.2 rfl⟩
  set δΨ : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ := fun x i => (dataR G ψ').Ψ x i - (dataR G ψ).Ψ x i with hδΨ
  have hsupp : ∀ y ∉ W, δΨ y = 0 := by
    intro y hy
    funext i
    simp only [hδΨ, Pi.zero_apply]
    by_cases hyd : y ∈ dataSites G
    · rw [dataR_Ψ G ψ' hyd i, dataR_Ψ G ψ hyd i]
      have hz : jBlock d L (N₁ * L ^ m₁) k k y ∉ Zf := fun h => hy ((hmemW y).2 h)
      simp [liftR, hoff _ hz]
    · rw [(dataR G ψ').Ψ_zero y hyd, (dataR G ψ).Ψ_zero y hyd]
      simp
  have hΨ : ∀ x i, (dataR G ψ').Ψ x i = (dataR G ψ).Ψ x i + δΨ x i := fun x i => by
    simp [hδΨ]
  have hh : ∀ x i, (dataR G ψ').h x i = (dataR G ψ).h x i := by
    intro x i
    by_cases hx : x ∈ G.Ω 1
    · rw [dataR_h G ψ' hx i, dataR_h G ψ hx i]
    · rw [(dataR G ψ').h_zero x hx, (dataR G ψ).h_zero x hx]
  have hdΨ : ∀ x ∈ dataSites G, vn (δΨ x) ≤ t := by
    intro x hx
    have e : δΨ x = fun i => ((ψ' (jBlock d L (N₁ * L ^ m₁) k k x) i -
        ψ (jBlock d L (N₁ * L ^ m₁) k k x) i : ℝ) : ℂ) := by
      funext i
      simp only [hδΨ]
      rw [dataR_Ψ G ψ' hx i, dataR_Ψ G ψ hx i]
      simp [liftR]
    rw [e, vn_ofReal]
    by_cases hz : jBlock d L (N₁ * L ^ m₁) k k x ∈ Zf
    · exact hdiff _ hz
    · have e2 : (fun i => ψ' (jBlock d L (N₁ * L ^ m₁) k k x) i - ψ (jBlock d L (N₁ * L ^ m₁) k k x) i) =
          fun _ => 0 := by
        funext i
        rw [hoff _ hz, sub_self]
      rw [e2]
      simpa [rn] using ht0
  have hν : ∀ ε δ : ℝ, (0 : ℝ) * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2 := fun ε δ => by
    rw [zero_mul, zero_mul]; positivity
  have hF := lemma41_domain_S hWP hd0 H hOp hτ le_rfl (hτ1.trans hc10) hτ1 (hν τ τ) hD hτ' le_rfl (hτ1'.trans hc10) hτ1'
    (hν τ' τ') hD' (hτs.trans (min_le_left _ _)) (hτs.trans (min_le_right _ _)) W hsupp hΨ hh ht0
    (hts.trans (min_le_left _ _)) (hts.trans (min_le_right _ _)) hdΨ
  obtain ⟨e1, e2⟩ := theorem72_real H (inUnionDomainR_of_tube G hτ hτ1 ht)
  obtain ⟨e1', e2'⟩ := theorem72_real H (inUnionDomainR_of_tube G hτ' hτ1' ht')
  rw [e1, e2, e1', e2'] at hF
  exact hF

/-- **The response of the massless background to a change of the block field on a set of blocks** (Lemma 4.1
for the lifted data `dataR`): `coreResponse_farBounds_of_weighted` with the constants `K_w, δ_w > 0` of
`weightedProp51S_exists`, depending only on `(d, L, N)`. -/
theorem coreResponse_farBounds (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ},
        BgHyp d L k ϱ a 0 → Dec2.OpSetting G a 0 →
        ∀ {τ τ' : ℝ}, 0 < τ → τ ≤ bgC1 d L N → bgK1 d L N * τ ≤ min (deltaStar d L N) δw →
        0 < τ' → τ' ≤ bgC1 d L N →
        ∀ {ψ ψ' : BlockField d L (N₁ * L ^ m₁) k N}, TubeOn G Set.univ τ ψ → TubeOn G Set.univ τ' ψ' →
        ∀ (Zf : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))), (∀ z ∉ Zf, ψ' z = ψ z) →
        ∀ {t : ℝ}, 0 ≤ t → t ≤ min (deltaStar d L N) δw →
        (∀ z ∈ Zf, rn (fun i => ψ' z i - ψ z i) ≤ t) →
        FarBounds G (shadow G (Zf.biUnion (fib d L (N₁ * L ^ m₁) k k))) (gammaW d) (Kw * (cF d L * t))
          (bgField G a 0 (dataR G ψ') - bgField G a 0 (dataR G ψ))
          (bgMult G a 0 (dataR G ψ') - bgMult G a 0 (dataR G ψ)) := by
  obtain ⟨Kw, δw, hK, hδw, hW⟩ := weightedProp51S_exists N hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₁ m₁ k _ ϱ G a H hOp τ τ' hτ hτ1 hτs hτ' hτ1' ψ ψ' ht ht' Zf hoff t ht0 hts hdiff
  exact coreResponse_farBounds_of_weighted hW (by omega) H hOp hτ hτ1 hτs hτ' hτ1' ht ht' Zf hoff ht0 hts hdiff

/-- **The one-site derivative of the massless background** (deliverable (1) of the core-to-action response):
`J_{x i, z j} = ∂ φ⁰(ψ_k)(x, i) / ∂ ψ_k(z)_j`, the derivative at `t = 0` of `t ↦ φ⁰(ψ_k + t e_{z j})(x, i)`
(`e_{z j} = Pi.single z (Pi.single j 1)`), satisfies `|J_{x i, z j}| ≤ K_w C_F e^{-γ_w d(x, W_z)}` for `ψ_k` in the
tube `Ψ̃(𝔹; τ)`, `K₁ τ ≤ min(δ_*, δ_w)`, `W_z` the fine sites of the block `z`.  (`deriv` is `0` where the
function is not differentiable, so the bound is unconditional.) -/
theorem coreResponse_deriv_le (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ},
        BgHyp d L k ϱ a 0 → Dec2.OpSetting G a 0 →
        ∀ {τ : ℝ}, 0 < τ → τ ≤ bgC1 d L N → bgK1 d L N * τ ≤ min (deltaStar d L N) δw →
        ∀ {ψ : BlockField d L (N₁ * L ^ m₁) k N}, TubeOn G Set.univ τ ψ →
        ∀ (z : Torus d (N₁ * L ^ m₁ * L ^ (k - k))) (j : Fin N) (x : G.Ω 1) (i : Fin N),
        ‖deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ + t •
          (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0‖ ≤
          Kw * cF d L * decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) := by
  obtain ⟨Kw, δw, hK, hδw, hresp⟩ := coreResponse_farBounds (N := N) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₁ m₁ k _ ϱ G a H hOp τ hτ hτ1 hτs ψ ht z j x i
  have hd0 : 0 < d := by omega
  set e : BlockField d L (N₁ * L ^ m₁) k N := Pi.single z (Pi.single j (1 : ℝ)) with he
  set m : ℝ := min (deltaStar d L N) δw with hm
  have hm0 : 0 < m := lt_min (deltaStar_pos d L N hd0) hδw
  have hcont : Tendsto (fun t : ℝ => ψ + t • e) (𝓝 0) (𝓝 ψ) := by
    have hc : Continuous fun t : ℝ => ψ + t • e := continuous_const.add (continuous_id.smul continuous_const)
    exact hc.tendsto' 0 ψ (by simp)
  have ev1 : ∀ᶠ t : ℝ in 𝓝 0, TubeOn G Set.univ τ (ψ + t • e) := hcont.eventually (eventually_tubeOn G ht)
  have ev2 : ∀ᶠ t : ℝ in 𝓝 0, |t| ≤ m := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hm0] with t ht
    simpa [Real.dist_eq] using ht
  set C := Kw * cF d L * decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) with hC
  have hC0 : 0 ≤ C := mul_nonneg (mul_nonneg hK.le (cF_pos d L).le) (decay_nonneg _ _)
  refine norm_deriv_le_of_lip' hC0 ?_
  filter_upwards [ev1, ev2] with t ht1 ht2
  have hoff : ∀ z' ∉ ({z} : Finset _), (ψ + t • e) z' = ψ z' := by
    intro z' hz'
    have hne : z' ≠ z := fun h => hz' (Finset.mem_singleton.2 h)
    funext i'
    simp [he, hne]
  have hdiff : ∀ z' ∈ ({z} : Finset _), rn (fun i' => (ψ + t • e) z' i' - ψ z' i') ≤ |t| := by
    intro z' hz'
    rw [Finset.mem_singleton.1 hz']
    have e2 : (fun i' => (ψ + t • e) z i' - ψ z i') = fun i' => t * (Pi.single j (1 : ℝ) : Fin N → ℝ) i' := by
      funext i'
      simp [he]
    rw [e2]
    unfold rn
    have hs : ∑ i', (t * (Pi.single j (1 : ℝ) : Fin N → ℝ) i') ^ 2 = t ^ 2 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    rw [hs, Real.sqrt_sq_eq_abs]
  have hF := hresp H hOp hτ hτ1 hτs hτ hτ1 ht ht1 {z} hoff (abs_nonneg t) ht2 hdiff
  have hval := hF.val x i
  rw [Finset.singleton_biUnion] at hval
  simp only [zero_smul, add_zero, sub_zero, Real.norm_eq_abs]
  simp only [Pi.sub_apply] at hval
  calc ‖bgField G a 0 (dataR G (ψ + t • e)) (x, i) - bgField G a 0 (dataR G ψ) (x, i)‖
      ≤ Kw * (cF d L * |t|) *
        decay (gammaW d) (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) := hval
    _ = C * |t| := by rw [hC]; ring

/-- **Decay from the shadow of a top-layer block**: if the `k`-block `z` lies in `Ω_k` (`OverTop G {z}`) and `y` is
a fine site of `z`, then `e^{-γ d(x, W_z)} ≤ e^{γ(2d+1)} e^{-γ d(x, y)}` (`W_z` the fine sites of `z`, `d(x, W_z)` the
path distance to its `Ω₁`-shadow; two sites of the block are at path distance `≤ 2d`, a shadow site is one bond
away from the block). -/
theorem decay_shadow_fib_le {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}
    (hk : 1 ≤ k) {γ : ℝ} (hγ : 0 ≤ γ) {z : Torus d (N₁ * L ^ m₁ * L ^ (k - k))}
    (hz : OverTop G ({z} : Set (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))))
    {y : Torus d (N₁ * L ^ m₁ * L ^ k)} (hy : y ∈ fib d L (N₁ * L ^ m₁) k k z) (x : Torus d (N₁ * L ^ m₁ * L ^ k)) :
    decay γ (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) ≤
      Real.exp (γ * (2 * d + 1)) * decay γ (G.pathDist x y) := by
  classical
  have hlayer : ∀ w ∈ fib d L (N₁ * L ^ m₁) k k z, w ∈ G.layer k := by
    intro w hw
    have hwk : w ∈ G.Ω k := hz w (by rw [mem_fib] at hw; exact hw)
    refine G.mem_layer.2 ⟨hwk, ?_⟩
    rw [G.top]
    simp
  have hyl := hlayer y hy
  have hblk : ∀ w ∈ fib d L (N₁ * L ^ m₁) k k z, G.pathDist w y ≤ ENNReal.ofReal (2 * d) := by
    intro w hw
    refine G.pathDist_block_le hk le_rfl (hlayer w hw) ?_
    rw [mem_fib] at hw hy
    exact hy.trans hw.symm
  have hΩ1 : ∀ w ∈ fib d L (N₁ * L ^ m₁) k k z, w ∈ G.Ω 1 := fun w hw =>
    G.layer_subset hk le_rfl (hlayer w hw)
  have hsh : ∀ w ∈ shadow G (fib d L (N₁ * L ^ m₁) k k z),
      G.pathDist w y ≤ ENNReal.ofReal (2 * d + 1) := by
    intro w hw
    simp only [shadow, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨hwΩ, hw | ⟨w', hw', hadj⟩⟩ := hw
    · exact (hblk w hw).trans (ENNReal.ofReal_le_ofReal (by linarith))
    · calc G.pathDist w y ≤ G.pathDist w w' + G.pathDist w' y := G.pathDist_triangle w w' y
        _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (2 * d) :=
            add_le_add (pathDist_adj_le_one hwΩ (hΩ1 w' hw') hadj) (hblk w' hw')
        _ = ENNReal.ofReal (2 * d + 1) := by
            rw [← ENNReal.ofReal_add zero_le_one (by positivity)]; ring_nf
  refine decay_le_exp_mul_decay hγ (by positivity) ?_
  unfold siteSetDist
  rw [ENNReal.iInf_add]
  refine le_iInf fun w => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hw => ?_
  exact (G.pathDist_triangle x w y).trans (add_le_add le_rfl (hsh w hw))

/-- **The one-site derivative from a site of a top-layer block**: `|J_{x i, z j}| ≤ K_w C_F e^{γ_w(2d+1)}
e^{-γ_w d(x, y)}` for every fine site `y` of the block `z ⊆ Ω_k`. -/
theorem coreResponse_deriv_le_pathDist (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ},
        BgHyp d L k ϱ a 0 → Dec2.OpSetting G a 0 → 1 ≤ k →
        ∀ {τ : ℝ}, 0 < τ → τ ≤ bgC1 d L N → bgK1 d L N * τ ≤ min (deltaStar d L N) δw →
        ∀ {ψ : BlockField d L (N₁ * L ^ m₁) k N}, TubeOn G Set.univ τ ψ →
        ∀ (z : Torus d (N₁ * L ^ m₁ * L ^ (k - k))), OverTop G ({z} : Set _) →
        ∀ {y : Torus d (N₁ * L ^ m₁ * L ^ k)}, y ∈ fib d L (N₁ * L ^ m₁) k k z →
        ∀ (j : Fin N) (x : G.Ω 1) (i : Fin N),
        ‖deriv (fun t : ℝ => bgField G a 0 (dataR G (ψ + t •
          (Pi.single z (Pi.single j (1 : ℝ)) : BlockField d L (N₁ * L ^ m₁) k N))) (x, i)) 0‖ ≤
          Kw * cF d L * Real.exp (gammaW d * (2 * d + 1)) * decay (gammaW d) (G.pathDist x y) := by
  obtain ⟨Kw, δw, hK, hδw, hJ⟩ := coreResponse_deriv_le (N := N) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₁ m₁ k _ ϱ G a H hOp hk τ hτ hτ1 hτs ψ ht z hz y hy j x i
  have hγ : 0 ≤ gammaW d := gammaW_nonneg (by omega)
  have h1 := hJ H hOp hτ hτ1 hτs ht z j x i
  have h2 := decay_shadow_fib_le hk hγ hz hy (x : Torus d (N₁ * L ^ m₁ * L ^ k))
  have hc : 0 ≤ Kw * cF d L := mul_nonneg hK.le (cF_pos d L).le
  calc _ ≤ _ := h1
    _ ≤ Kw * cF d L * (Real.exp (gammaW d * (2 * d + 1)) * decay (gammaW d) (G.pathDist x y)) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ = _ := by ring

end Response

end Balaban.LargeField
