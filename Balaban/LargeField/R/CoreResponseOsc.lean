/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoreResponseSum
public import Balaban.LargeField.R.RhoZeroRestricted
import Balaban.SmallField.FinalCutoff
import Balaban.Fluctuation.CubeActionBound
import Balaban.LargeField.R.DenominatorTube
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The oscillation condition of the restricted denominator (LF4R-PLAN §5, `hosc`)

`denominatorRestricted_bounds_of_osc` (`RhoZeroRestricted.lean`) bounds `Ẽ₀^Z` under the oscillation bound
`|β₀ (A_{Ω₁} - A_Z)(ψ_k(u)) - β₀ (A_{Ω₁} - A_Z)(ψ⁰_k)| ≤ E` on the cutoff ball, `A_{Ω₁} = effAction` (the massless
action on all of `Ω₁(𝔹_k(U_k))`) and `A_Z = actionZ` (the action restricted to the region `Z_r` of the component,
half-bond weights on `∂Z_r`, with its `ν`-term).  Here this bound is proved for the geometry of a removed component:
the core `Z₀` (a set `Z_f` of `k`-blocks of the top layer) lies in `Z_r`, and every site of `Ω₁` read by the action
outside `Z_r` (a site outside `Z_r` or next to one) is at path distance at least `R` from the shadow of the fine sites
of `Z₀`.

* `effAction_sub_actionZ`: `A_{Ω₁} - A_Z` is the block action at the sites of `Ω₁ ∖ Z_r`, plus the bond action with
  the weights `1_{touch Ω₁} - starWeight` (`0` on the bonds inside `Z_r`, `1/2` on `st(Z_r)`, `1` outside), minus
  the `ν`-term of `Z_r`;
* `effAction_sub_actionZ_osc_le_of_weighted` (from `effAction_sub_actionZ_osc_le_of_far`): for two fields of the tubes `Ψ̃(𝔹; τ)`, `Ψ̃(𝔹; τ')` that agree off `Z_f` and differ
  by at most `t` on its blocks, `|β₀ ΔA(ψ') - β₀ ΔA(ψ)| ≤ E`,
  `E = β_k (d+1) N (2 K₁τ B' + B'²) e^{-γ_w R/2} |Z_f| S_{γ_w/2} + β₀ ν L^{kd} (N/2)(4B + B²) |Z_f| S_{γ_w}`,
  `B = K_w C_F t`, `B' = B e^{2dγ_w}`, `S_γ = e^{γ(2d+1)} C(d, L, γ)`: the response `δφ` of the background decays
  from `Z₀` (Lemma 4.1), the action outside `Z_r` only sees `δφ` at distance `≥ R`, and the `ν`-term is summed with
  the counting lemma;
* `hosc_of_margin_of_weighted`: the oscillation hypothesis of `denominatorRestricted_bounds_of_osc` for the restricted density
  (`ψ = ψ⁰_k`, `ψ' = ψ_k(u)` on the cutoff ball, `t = C₆ β_k^{-1/2} p₀`, `τ = K₆ δ`);
* `denominatorRestricted_bounds_of_margin_of_weighted`: Lemma III.8.2 for the restricted density, `|Ẽ₀^Z - Ẽ₀| ≤ E` and
  `|Ẽ₀^Z| ≤ C_Ẽ D₀^d + E`, with the geometric margin in place of the oscillation hypothesis.

With `t = C₆ β_k^{-1/2} p₀`: `β_k B² = (K_w C_F C₆ p₀)²` and `β_k B ≍ β_k^{1/2} p₀`, so the first term of `E` is
`O(|Z₀| (β_k^{1/2} p₀ K₆ δ + p₀²) e^{-γ_w R/2})`: it is bounded uniformly in `β_k` once `R ≥ (1/γ_w) log β_k + C`.
The `ν`-term has no decay (the restricted action carries the mass term on all of `Z_r`); it vanishes at `ν = 0`
(the massless reference of the Q13 ruling).

The counting at the rate `γ_w/2` needs the separation `2 d log L ≤ (γ_w/4)(ϱ - 1)` (a hypothesis; `Dec2.OpSetting`
gives the rate `γ_w`).  The generating set lives on a torus of side `N₁ L^{m₁} L^k` (the carrier of Lemma 4.1).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization ActionConv

section Identity

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

theorem dataRH_h_of_mem (ψ : BlockField d L N₀ k N) (h : Fin N → ℝ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (i : Fin N) : (dataRH G ψ h).h x i = (h i : ℂ) := by
  simp [dataRH, liftSingle_h G _ _ hx]

/-- A sum over the sites of a subset `S ⊆ Ω₁` as a sum over `Ω₁`. -/
theorem sum_sites_eq_sum_Ω {S : Finset (Torus d (N₀ * L ^ k))} (hS : S ⊆ G.Ω 1)
    (f : Torus d (N₀ * L ^ k) → ℝ) :
    ∑ x ∈ S, f x = ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ S then f x else 0) := by
  classical
  rw [Finset.sum_coe_sort (G.Ω 1) (fun x => if x ∈ S then f x else 0), ← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun hx => ⟨hS hx, hx⟩, fun hx => hx.2⟩

/-- **`A_{Ω₁} - A_Z`**: the massless action on `Ω₁` minus the restricted action of the region `Z_r` (both at the
massless background `φ` of the lifted field) is the block action at the sites of `Ω₁ ∖ Z_r`, plus the bond action
with the weights `1_{x ∈ Ω₁ ∨ x + e_μ ∈ Ω₁} - starWeight_{Z_r}(x, μ)`, minus the `ν`-term of `Z_r`. -/
theorem effAction_sub_actionZ (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ) (ψ : BlockField d L N₀ k N) :
    effAction G a ψ - actionZ G a Zr ν h ψ =
      (1 / 2) * ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ k)) ∈ Zr.sites then 0 else
        (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) / ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
          ∑ i, ‖(dataR G ψ).Ψ x i - blockAvg G (bgField G a 0 (dataR G ψ)) x i‖ ^ 2) +
      (1 / 2) * ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
        ((if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then 1 else 0) - Zr.starWeight x μ) *
          ∑ i, ‖barField G (dataR G ψ).Ψ (bgField G a 0 (dataR G ψ)) (x + Pi.single μ 1) i -
            barField G (dataR G ψ).Ψ (bgField G a 0 (dataR G ψ)) x i‖ ^ 2 -
      ν / 2 * ∑ x ∈ Zr.sites, ∑ i, ‖svec G (bgField G a 0 (dataR G ψ)) x i - (h i : ℂ)‖ ^ 2 := by
  classical
  set φ := bgField G a 0 (dataR G ψ) with hφ
  rw [actionZ_eq]
  unfold effAction action actionRegionR
  rw [dataRH_Ψ, ← hφ]
  have hν : ∑ x ∈ Zr.sites, ∑ i, ‖svec G φ x i - (dataRH G ψ h).h x i‖ ^ 2 =
      ∑ x ∈ Zr.sites, ∑ i, ‖svec G φ x i - (h i : ℂ)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
    rw [dataRH_h_of_mem ψ h (Zr.sub_Ω hx) i]
  rw [hν, sum_sites_eq_sum_Ω Zr.sub_Ω]
  have hblk : ∀ x : G.Ω 1,
      (if (x : Torus d (N₀ * L ^ k)) ∈ Zr.sites then 0 else
        (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) / ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
          ∑ i, ‖(dataR G ψ).Ψ x i - blockAvg G φ x i‖ ^ 2) =
      (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) / ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
          ∑ i, ‖(dataR G ψ).Ψ x i - blockAvg G φ x i‖ ^ 2 -
      (if (x : Torus d (N₀ * L ^ k)) ∈ Zr.sites then
        (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) / ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
          ∑ i, ‖(dataR G ψ).Ψ x i - blockAvg G φ x i‖ ^ 2 else 0) := by
    intro x
    split_ifs <;> ring
  have hbond : ∀ (x : Torus d (N₀ * L ^ k)) (μ : Fin d),
      ((if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then 1 else 0) - Zr.starWeight x μ) *
          ∑ i, ‖barField G (dataR G ψ).Ψ φ (x + Pi.single μ 1) i - barField G (dataR G ψ).Ψ φ x i‖ ^ 2 =
        (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
          ∑ i, ‖barField G (dataR G ψ).Ψ φ (x + Pi.single μ 1) i - barField G (dataR G ψ).Ψ φ x i‖ ^ 2 else 0) -
        Zr.starWeight x μ *
          ∑ i, ‖barField G (dataR G ψ).Ψ φ (x + Pi.single μ 1) i - barField G (dataR G ψ).Ψ φ x i‖ ^ 2 := by
    intro x μ
    split_ifs <;> ring
  simp only [hblk, hbond, Finset.sum_sub_distrib]
  ring

end Identity

section Helpers

/-- `|‖a + b‖² - ‖a‖²| ≤ ‖b‖ (2‖a‖ + ‖b‖)` for complex numbers. -/
theorem abs_norm_add_sq_sub_le (a b : ℂ) : |‖a + b‖ ^ 2 - ‖a‖ ^ 2| ≤ ‖b‖ * (2 * ‖a‖ + ‖b‖) := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h2 : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
    have := norm_add_le (a + b) (-b)
    simpa using this
  have h3 : |‖a + b‖ - ‖a‖| ≤ ‖b‖ := abs_le.2 ⟨by linarith, by linarith⟩
  have e : ‖a + b‖ ^ 2 - ‖a‖ ^ 2 = (‖a + b‖ - ‖a‖) * (‖a + b‖ + ‖a‖) := by ring
  rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖a + b‖ + ‖a‖)]
  exact mul_le_mul h3 (by linarith) (by positivity) (norm_nonneg b)

variable {d L : ℕ} [NeZero L] {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}

/-- **Decay from the shadow of a union of blocks**: `e^{-γ d(x, ∪_z W_z)} ≤ ∑_z e^{-γ d(x, W_z)}`. -/
theorem decay_shadow_biUnion_le {γ : ℝ} (hγ : 0 ≤ γ) (Zf : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k - k))))
    (x : Torus d (N₁ * L ^ m₁ * L ^ k)) :
    decay γ (siteSetDist G (shadow G (Zf.biUnion (fib d L (N₁ * L ^ m₁) k k))) x) ≤
      ∑ z ∈ Zf, decay γ (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) := by
  classical
  rcases Zf.eq_empty_or_nonempty with hZ | hZ
  · subst hZ
    have : siteSetDist G (shadow G ((∅ : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))).biUnion
        (fib d L (N₁ * L ^ m₁) k k))) x = ⊤ := by
      unfold siteSetDist
      simp [shadow]
    rw [this, decay_top]
    simp
  obtain ⟨z₀, hz₀, hmin⟩ := Zf.exists_min_image
    (fun z => siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) hZ
  have hge : siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z₀)) x ≤
      siteSetDist G (shadow G (Zf.biUnion (fib d L (N₁ * L ^ m₁) k k))) x := by
    unfold siteSetDist
    refine le_iInf₂ fun w hw => ?_
    simp only [shadow, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨hwΩ, hw⟩ := hw
    have hz : ∃ z ∈ Zf, w ∈ shadow G (fib d L (N₁ * L ^ m₁) k k z) := by
      rcases hw with hw | ⟨w', hw', hadj⟩
      · obtain ⟨z, hz, hwz⟩ := Finset.mem_biUnion.1 hw
        exact ⟨z, hz, by simp [shadow, hwΩ, hwz]⟩
      · obtain ⟨z, hz, hwz⟩ := Finset.mem_biUnion.1 hw'
        exact ⟨z, hz, by simp only [shadow, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hwΩ, Or.inr ⟨w', hwz, hadj⟩⟩⟩
    obtain ⟨z, hz, hwz⟩ := hz
    calc siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z₀)) x
        ≤ siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x := hmin z hz
      _ ≤ G.pathDist x w := iInf₂_le w hwz
  calc _ ≤ decay γ (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z₀)) x) := decay_anti_dist hγ hge
    _ ≤ _ := Finset.single_le_sum (f := fun z => decay γ (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x))
        (fun z _ => decay_nonneg _ _) hz₀

/-- **Counting from a union of top-layer blocks**: `∑_{x ∈ Ω₁} ℓ(x)^{-d} e^{-γ d(x, ∪_z W_z)} ≤ |Z_f| e^{γ(2d+1)} C(d,L,γ)`. -/
theorem sum_siteWeight_decay_shadow_biUnion_le (hk : 1 ≤ k) (hϱ : 1 < ϱ) {γ : ℝ} (hγ : 0 < γ)
    (hcond : 2 * d * Real.log L ≤ γ / 2 * (ϱ - 1)) (Zf : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k - k))))
    (hZ : ∀ z ∈ Zf, OverTop G ({z} : Set (Torus d (N₁ * L ^ m₁ * L ^ (k - k))))) :
    ∑ x : G.Ω 1, siteWeight G x *
        decay γ (siteSetDist G (shadow G (Zf.biUnion (fib d L (N₁ * L ^ m₁) k k))) x) ≤
      Zf.card * (Real.exp (γ * (2 * d + 1)) * countConst d L γ) := by
  calc ∑ x : G.Ω 1, siteWeight G x *
        decay γ (siteSetDist G (shadow G (Zf.biUnion (fib d L (N₁ * L ^ m₁) k k))) x)
      ≤ ∑ x : G.Ω 1, ∑ z ∈ Zf, siteWeight G x *
          decay γ (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (decay_shadow_biUnion_le hγ.le Zf _) (siteWeight_nonneg G _)
    _ = ∑ z ∈ Zf, ∑ x : G.Ω 1, siteWeight G x *
          decay γ (siteSetDist G (shadow G (fib d L (N₁ * L ^ m₁) k k z)) x) := Finset.sum_comm
    _ ≤ ∑ _z ∈ Zf, Real.exp (γ * (2 * d + 1)) * countConst d L γ :=
        Finset.sum_le_sum fun z hz => sum_siteWeight_decay_shadow_fib_le hk hϱ hγ hcond (hZ z hz)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end Helpers

section Osc

variable {d L N : ℕ} [NeZero L] {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ}

open Classical in
/-- **The oscillation of `A_{Ω₁} - A_Z` from the far-decay of the background response** (conditional on the bounds
(4.1) of the response, `FarBounds` with rate `γ` and constant `B`).  For `ψ ∈ Ψ̃(𝔹; τ)` and `ψ'` that agrees with `ψ`
off the blocks `Z_f` (whose fine sites lie in `Z_r`):
`|ΔA(ψ') - ΔA(ψ)| ≤ ∑_{x ∈ Ω₁ read outside Z_r} (d+1) N (2 K₁τ B' + B'²) ℓ(x)^{-2} e^{-γ d(x, W)}
  + (ν/2) N (4B + B²) ∑_{x ∈ Ω₁} e^{-γ d(x, W)}`, `B' = B e^{2dγ}`, `W` the fine sites of `Z_f`
(the sites read outside `Z_r`: outside `Z_r` or next to a site outside `Z_r`). -/
theorem effAction_sub_actionZ_osc_le_of_far (H : BgHyp d L k ϱ a 0) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ bgC1 d L N) {ψ ψ' : BlockField d L (N₁ * L ^ m₁) k N} (ht : TubeOn G Set.univ τ ψ)
    (Zf : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))) (hoff : ∀ z ∉ Zf, ψ' z = ψ z)
    (Zr : Region G) (hZr : ∀ x, jBlock d L (N₁ * L ^ m₁) k k x ∈ Zf → x ∈ Zr.sites)
    {γ B : ℝ} (hγ : 0 ≤ γ) (hB : 0 ≤ B)
    (hF : FarBounds G (shadow G (Zf.biUnion (fib d L (N₁ * L ^ m₁) k k))) γ B
      (bgField G a 0 (dataR G ψ') - bgField G a 0 (dataR G ψ))
      (bgMult G a 0 (dataR G ψ') - bgMult G a 0 (dataR G ψ)))
    {ν : ℝ} (hν : 0 ≤ ν) (h : Fin N → ℝ) (hh1 : ∀ i, |h i| ≤ 1) :
    |(effAction G a ψ' - actionZ G a Zr ν h ψ') - (effAction G a ψ - actionZ G a Zr ν h ψ)| ≤
      ∑ x : G.Ω 1, (if ((x : Torus d (N₁ * L ^ m₁ * L ^ k)) ∉ Zr.sites ∨ ∃ μ : Fin d,
          (x : Torus d (N₁ * L ^ m₁ * L ^ k)) + Pi.single μ 1 ∉ Zr.sites ∨
            (x : Torus d (N₁ * L ^ m₁ * L ^ k)) - Pi.single μ 1 ∉ Zr.sites) then
        (d + 1) * N * (2 * (bgK1 d L N * τ) * (B * Real.exp (2 * d * γ)) + (B * Real.exp (2 * d * γ)) ^ 2) /
          G.spacing x ^ 2 * decay γ (siteSetDist G (shadow G (Zf.biUnion (fib d L (N₁ * L ^ m₁) k k))) x)
        else 0) +
      ν / 2 * N * (4 * B + B ^ 2) *
        ∑ x : G.Ω 1, decay γ (siteSetDist G (shadow G (Zf.biUnion (fib d L (N₁ * L ^ m₁) k k))) x) := by
  classical
  rw [effAction_sub_actionZ Zr ν h ψ', effAction_sub_actionZ Zr ν h ψ]
  set W := Zf.biUnion (fib d L (N₁ * L ^ m₁) k k) with hW
  set φ := bgField G a 0 (dataR G ψ) with hφ
  set φ' := bgField G a 0 (dataR G ψ') with hφ'
  set τf := φ' - φ with hτf
  set Ψ := (dataR G ψ).Ψ with hΨdef
  set Ψ' := (dataR G ψ').Ψ with hΨ'def
  set e : Torus d (N₁ * L ^ m₁ * L ^ k) → ℝ := fun x => decay γ (siteSetDist G (shadow G W) x) with he
  set c := bgK1 d L N * τ with hc
  set B' := B * Real.exp (2 * d * γ) with hB'
  set Out : Torus d (N₁ * L ^ m₁ * L ^ k) → Prop := fun y => y ∉ Zr.sites ∨ ∃ μ : Fin d,
    y + Pi.single μ 1 ∉ Zr.sites ∨ y - Pi.single μ 1 ∉ Zr.sites with hOut
  have hd0 : 0 < d := by have := H.hd; omega
  have hR := inUnionDomainR_of_tube G hτ hτ1 ht
  obtain ⟨-, hunit, -, -, hbb⟩ := theorem71 H hR
  have hBB := hbb τ hτ hτ1 (inDomainR_of_tube G hτ ht)
  have hc0 : 0 ≤ c := mul_nonneg (bgK1_pos d L N).le hτ.le
  have hB'0 : 0 ≤ B' := mul_nonneg hB (Real.exp_pos _).le
  have hBB' : B ≤ B' := le_mul_of_one_le_right hB (Real.one_le_exp (by positivity))
  have he0 : ∀ x, 0 ≤ e x := fun x => decay_nonneg _ _
  have he1 : ∀ x, e x ≤ 1 := fun x => decay_le_one hγ _
  have hsp : ∀ x, 0 < G.spacing x := fun x => spacing_pos G
  have hΨeq : ∀ y, y ∉ Zr.sites → Ψ' y = Ψ y := by
    intro y hy
    by_cases hyd : y ∈ dataSites G
    · funext i
      simp only [hΨ'def, hΨdef]
      rw [dataR_Ψ G ψ' hyd i, dataR_Ψ G ψ hyd i]
      have hz : jBlock d L (N₁ * L ^ m₁) k k y ∉ Zf := fun hz => hy (hZr y hz)
      simp [liftR, hoff _ hz]
    · simp only [hΨ'def, hΨdef]
      rw [(dataR G ψ').Ψ_zero y hyd, (dataR G ψ).Ψ_zero y hyd]
  have hbar : ∀ y i, barField G Ψ' φ' y i = barField G Ψ φ y i + svec G τf y i := by
    intro y i
    by_cases hy : y ∈ G.Ω 1
    · rw [svec_of_mem G τf ⟨y, hy⟩ i]
      simp [barField, hy, hτf]
    · rw [svec_of_not_mem G τf hy i, add_zero]
      have hyZ : y ∉ Zr.sites := fun h => hy (Zr.sub_Ω h)
      simp [barField, hy, hΨeq y hyZ]
  have hQ : ∀ x i, blockAvg G φ' x i = blockAvg G φ x i + blockAvg G τf x i := by
    intro x i
    have : φ' = φ + τf := by simp [hτf]
    rw [this, blockAvg_add]
  have hA : ∀ x : G.Ω 1, ∀ i, ‖Ψ x i - blockAvg G φ x i‖ ≤ c := by
    intro x i
    obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec x.2
    have h1 := FinalCutoff.blockAvg_sub_const_le φ (Ψ x) x.2 (r := c) (fun y hy hyb => by
      have hl := (dataR G ψ).Ψ_layerConst _ hn1 hnk x hxl y hyb
      have := hBB.val ⟨y, hy⟩
      simp only [hΨdef] at hl ⊢
      rw [← hl]
      exact this)
    calc ‖Ψ x i - blockAvg G φ x i‖ = ‖blockAvg G φ x i - Ψ x i‖ := norm_sub_rev _ _
      _ ≤ vn (fun i => blockAvg G φ x i - Ψ x i) := norm_le_vn (fun i => blockAvg G φ x i - Ψ x i) i
      _ ≤ c := h1
  have hT : ∀ x : G.Ω 1, ∀ i, ‖blockAvg G τf x i‖ ≤ B' * e x := by
    intro x i
    obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec x.2
    refine blockAvg_norm_le τf x.2 (fun y hy hyΩ j => ?_) i
    have h1 := hF.val ⟨y, hyΩ⟩ j
    have hpd : G.pathDist x y ≤ ENNReal.ofReal (2 * d) :=
      G.pathDist_block_le hn1 hnk hxl (GeneratingSet.mem_blk.1 hy)
    have h2 : siteSetDist G (shadow G W) x ≤ siteSetDist G (shadow G W) y + ENNReal.ofReal (2 * d) := by
      calc siteSetDist G (shadow G W) x ≤ G.pathDist x y + siteSetDist G (shadow G W) y :=
            setDist_triangle (G := G) (shadow G W) (x : Torus d (N₁ * L ^ m₁ * L ^ k)) y
        _ ≤ ENNReal.ofReal (2 * d) + siteSetDist G (shadow G W) y := add_le_add hpd le_rfl
        _ = _ := add_comm _ _
    have h3 := decay_le_exp_mul_decay hγ (by positivity) h2
    calc ‖τf (⟨y, hyΩ⟩, j)‖ ≤ B * decay γ (siteSetDist G (shadow G W) y) := h1
      _ ≤ B * (Real.exp (γ * (2 * d)) * e x) := mul_le_mul_of_nonneg_left h3 hB
      _ = B' * e x := by rw [hB']; ring_nf
  set K' := 2 * c * B' + B' ^ 2 with hK'
  have hK'0 : 0 ≤ K' := by positivity
  -- the per-site block bound
  set F0 : G.Ω 1 → ℝ := fun x => if Out x then N * K' / G.spacing x ^ 2 * e x else 0 with hF0
  have hF00 : ∀ x, 0 ≤ F0 x := fun x => by
    simp only [hF0]; split_ifs
    · exact mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hK'0) (sq_nonneg _)) (he0 _)
    · exact le_rfl
  have hsq : ∀ (u v : ℝ), 0 ≤ u → 0 ≤ v → v ≤ 1 → u * v * (2 * c + u * v) ≤ (2 * c * u + u ^ 2) * v := by
    intro u v hu hv hv1
    have : u * v * (u * v) ≤ u ^ 2 * v := by
      have h1 : u * v * (u * v) = u ^ 2 * v * v := by ring
      rw [h1]
      exact mul_le_of_le_one_right (by positivity) hv1
    nlinarith
  have hPx : ∀ x : G.Ω 1,
      |(if (x : Torus d (N₁ * L ^ m₁ * L ^ k)) ∈ Zr.sites then 0 else
          (a (G.layerIndex (x : Torus d (N₁ * L ^ m₁ * L ^ k))) /
            ((L : ℝ) ^ G.layerIndex (x : Torus d (N₁ * L ^ m₁ * L ^ k))) ^ 2) *
          ∑ i, ‖Ψ' x i - blockAvg G φ' x i‖ ^ 2) -
        (if (x : Torus d (N₁ * L ^ m₁ * L ^ k)) ∈ Zr.sites then 0 else
          (a (G.layerIndex (x : Torus d (N₁ * L ^ m₁ * L ^ k))) /
            ((L : ℝ) ^ G.layerIndex (x : Torus d (N₁ * L ^ m₁ * L ^ k))) ^ 2) *
          ∑ i, ‖Ψ x i - blockAvg G φ x i‖ ^ 2)| ≤ 2 * F0 x := by
    intro x
    by_cases hx : (x : Torus d (N₁ * L ^ m₁ * L ^ k)) ∈ Zr.sites
    · simp only [hx, ↓reduceIte, sub_self, abs_zero]
      exact mul_nonneg zero_le_two (hF00 x)
    · have hOx : Out x := Or.inl hx
      have hF0x : F0 x = N * K' / G.spacing x ^ 2 * e x := by simp only [hF0, hOx, ↓reduceIte]
      rw [hF0x]
      simp only [hx, ↓reduceIte]
      obtain ⟨hn1, hnk, -⟩ := G.layerIndex_spec x.2
      have hwt := H.weights _ hn1 hnk
      set ℓ := G.spacing x with hℓ
      have hℓ0 : 0 < ℓ := hsp x
      have hcx0 : 0 ≤ a (G.layerIndex (x : Torus d (N₁ * L ^ m₁ * L ^ k))) /
          ((L : ℝ) ^ G.layerIndex (x : Torus d (N₁ * L ^ m₁ * L ^ k))) ^ 2 :=
        div_nonneg (by linarith [hwt.1]) (sq_nonneg _)
      have hcx : a (G.layerIndex (x : Torus d (N₁ * L ^ m₁ * L ^ k))) /
          ((L : ℝ) ^ G.layerIndex (x : Torus d (N₁ * L ^ m₁ * L ^ k))) ^ 2 ≤ 2 / ℓ ^ 2 :=
        div_le_div_of_nonneg_right hwt.2 (sq_nonneg _)
      have hΨx : Ψ' x = Ψ x := hΨeq x hx
      have hS : |∑ i, ‖Ψ' x i - blockAvg G φ' x i‖ ^ 2 - ∑ i, ‖Ψ x i - blockAvg G φ x i‖ ^ 2| ≤
          N * (B' * e x * (2 * c + B' * e x)) := by
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i, |‖Ψ' x i - blockAvg G φ' x i‖ ^ 2 - ‖Ψ x i - blockAvg G φ x i‖ ^ 2|
            ≤ ∑ _i : Fin N, B' * e x * (2 * c + B' * e x) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have e1 : Ψ' x i - blockAvg G φ' x i = (Ψ x i - blockAvg G φ x i) + -blockAvg G τf x i := by
                rw [hΨx, hQ]; ring
              rw [e1]
              refine (abs_norm_add_sq_sub_le _ _).trans ?_
              rw [norm_neg]
              exact mul_le_mul (hT x i) (by linarith [hA x i, hT x i]) (by positivity)
                (mul_nonneg hB'0 (he0 x))
          _ = N * (B' * e x * (2 * c + B' * e x)) := by simp
      rw [← mul_sub, abs_mul, abs_of_nonneg hcx0]
      calc _ ≤ 2 / ℓ ^ 2 * (N * (B' * e x * (2 * c + B' * e x))) :=
            mul_le_mul hcx hS (abs_nonneg _) (by positivity)
        _ ≤ 2 / ℓ ^ 2 * (N * (K' * e x)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) (by positivity)
            rw [hK']
            exact hsq B' (e x) hB'0 (he0 x) (he1 x)
        _ = 2 * (N * K' / ℓ ^ 2 * e x) := by ring
  -- the per-bond bound
  set g : Torus d (N₁ * L ^ m₁ * L ^ k) → ℝ := fun p => if hp : p ∈ G.Ω 1 then F0 ⟨p, hp⟩ else 0 with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => by
    simp only [hg]; split_ifs with hp
    · exact hF00 _
    · exact le_rfl
  have hbond : ∀ (p : Torus d (N₁ * L ^ m₁ * L ^ k)) (hp : p ∈ G.Ω 1), Out p → ∀ (gv sv : Fin N → ℂ),
      (∀ i, ‖gv i‖ ≤ c / G.spacing p) → (∀ i, ‖sv i‖ ≤ B * e p / G.spacing p) →
      |∑ i, (‖gv i + sv i‖ ^ 2 - ‖gv i‖ ^ 2)| ≤ g p := by
    intro p hp hOp gv sv hgv hsv
    have hgp : g p = N * K' / G.spacing p ^ 2 * e p := by
      simp only [hg, hp, ↓reduceDIte, hF0]
      have : Out (⟨p, hp⟩ : G.Ω 1) := hOp
      simp only [this, ↓reduceIte]
    rw [hgp]
    have hℓ0 : 0 < G.spacing p := hsp p
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |‖gv i + sv i‖ ^ 2 - ‖gv i‖ ^ 2|
        ≤ ∑ _i : Fin N, B * e p / G.spacing p * (2 * (c / G.spacing p) + B * e p / G.spacing p) := by
          refine Finset.sum_le_sum fun i _ => (abs_norm_add_sq_sub_le _ _).trans ?_
          exact mul_le_mul (hsv i) (by linarith [hgv i, hsv i]) (by positivity)
            (div_nonneg (mul_nonneg hB (he0 p)) hℓ0.le)
      _ = N * ((B * e p * (2 * c + B * e p)) / G.spacing p ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      _ ≤ N * ((K' * e p) / G.spacing p ^ 2) := by
          refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ (sq_nonneg _)) (Nat.cast_nonneg _)
          refine (hsq B (e p) hB (he0 p) (he1 p)).trans (mul_le_mul_of_nonneg_right ?_ (he0 p))
          rw [hK']
          nlinarith [mul_le_mul_of_nonneg_left hBB' hc0, mul_le_mul hBB' hBB' hB hB'0]
      _ = N * K' / G.spacing p ^ 2 * e p := by ring
  have hQx : ∀ (x : Torus d (N₁ * L ^ m₁ * L ^ k)) (μ : Fin d),
      |((if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then 1 else 0) - Zr.starWeight x μ) *
          ∑ i, ‖barField G Ψ' φ' (x + Pi.single μ 1) i - barField G Ψ' φ' x i‖ ^ 2 -
        ((if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then 1 else 0) - Zr.starWeight x μ) *
          ∑ i, ‖barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i‖ ^ 2| ≤
        g x + g (x + Pi.single μ 1) := by
    intro x μ
    set gv : Fin N → ℂ := fun i => barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i with hgv
    set sv : Fin N → ℂ := fun i => svec G τf (x + Pi.single μ 1) i - svec G τf x i with hsv
    have hS : ∑ i, ‖barField G Ψ' φ' (x + Pi.single μ 1) i - barField G Ψ' φ' x i‖ ^ 2 -
        ∑ i, ‖barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i‖ ^ 2 =
        ∑ i, (‖gv i + sv i‖ ^ 2 - ‖gv i‖ ^ 2) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e1 : barField G Ψ' φ' (x + Pi.single μ 1) i - barField G Ψ' φ' x i = gv i + sv i := by
        rw [hbar, hbar]
        simp only [hgv, hsv]
        ring
      rw [e1]
    rw [← mul_sub, abs_mul, hS]
    have hg2 := add_nonneg (hg0 x) (hg0 (x + Pi.single μ 1))
    have hwt1 : |(if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then (1 : ℝ) else 0) - Zr.starWeight x μ| ≤ 1 := by
      simp only [Region.starWeight]
      split_ifs <;> norm_num
    by_cases hboth : x ∈ Zr.sites ∧ x + Pi.single μ 1 ∈ Zr.sites
    · have h0 : (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then (1 : ℝ) else 0) - Zr.starWeight x μ = 0 := by
        have ht : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 := Or.inl (Zr.sub_Ω hboth.1)
        simp only [Region.starWeight, ht, hboth.1, hboth.2, ↓reduceIte]
        norm_num
      rw [h0, abs_zero, zero_mul]
      exact hg2
    by_cases hx : x ∈ G.Ω 1
    · have hOx : Out x := by
        by_cases hxZ : x ∈ Zr.sites
        · exact Or.inr ⟨μ, Or.inl fun h => hboth ⟨hxZ, h⟩⟩
        · exact Or.inl hxZ
      have hℓ0 := hsp x
      have hb := hbond x hx hOx gv sv (fun i => ?_) (fun i => ?_)
      · calc _ ≤ 1 * g x := mul_le_mul hwt1 hb (abs_nonneg _) zero_le_one
          _ ≤ _ := by linarith [hg0 (x + Pi.single μ 1)]
      · exact (norm_le_vn gv i).trans ((hBB.grad ⟨x, hx⟩ μ).1)
      · have h1 := hF.fwd x hx μ i
        rw [le_div_iff₀ hℓ0]
        simp only [hsv]
        linarith
    by_cases hy : x + Pi.single μ 1 ∈ G.Ω 1
    · have hxZ : x ∉ Zr.sites := fun h => hx (Zr.sub_Ω h)
      have hOy : Out (x + Pi.single μ 1) :=
        Or.inr ⟨μ, Or.inr (by rw [add_sub_cancel_right]; exact hxZ)⟩
      have hℓ0 := hsp (x + Pi.single μ 1)
      have hb := hbond (x + Pi.single μ 1) hy hOy gv sv (fun i => ?_) (fun i => ?_)
      · calc _ ≤ 1 * g (x + Pi.single μ 1) := mul_le_mul hwt1 hb (abs_nonneg _) zero_le_one
          _ ≤ _ := by linarith [hg0 x]
      · have h1 := (hBB.grad ⟨x + Pi.single μ 1, hy⟩ μ).2
        simp only [add_sub_cancel_right] at h1
        have h2 := norm_le_vn (fun i => barField G Ψ φ x i - barField G Ψ φ (x + Pi.single μ 1) i) i
        simp only [hgv]
        rw [norm_sub_rev]
        exact h2.trans h1
      · have h1 := hF.bwd (x + Pi.single μ 1) hy μ i
        simp only [add_sub_cancel_right] at h1
        rw [le_div_iff₀ hℓ0]
        simp only [hsv]
        rw [norm_sub_rev]
        linarith
    · have hxZ : x ∉ Zr.sites := fun h => hx (Zr.sub_Ω h)
      have hyZ : x + Pi.single μ 1 ∉ Zr.sites := fun h => hy (Zr.sub_Ω h)
      have hnt : ¬ (x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1) := fun h => h.elim hx hy
      have h0 : (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then (1 : ℝ) else 0) - Zr.starWeight x μ = 0 := by
        simp only [Region.starWeight, hnt, hxZ, hyZ, ↓reduceIte]
        norm_num
      rw [h0, abs_zero, zero_mul]
      exact hg2
  -- the `ν`-term
  have hVx : ∀ x ∈ Zr.sites, |∑ i, ‖svec G φ' x i - (h i : ℂ)‖ ^ 2 - ∑ i, ‖svec G φ x i - (h i : ℂ)‖ ^ 2| ≤
      N * (4 * B + B ^ 2) * e x := by
    intro x hx
    have hxΩ := Zr.sub_Ω hx
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hφ1 : ∀ i, ‖φ (⟨x, hxΩ⟩, i)‖ ≤ 1 := by
      intro i
      have hs := (hunit ⟨x, hxΩ⟩).2
      have h1 : ‖φ (⟨x, hxΩ⟩, i)‖ ^ 2 ≤ 1 := by
        rw [← hs]
        exact Finset.single_le_sum (f := fun i => ‖φ (⟨x, hxΩ⟩, i)‖ ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ i)
      nlinarith [norm_nonneg (φ (⟨x, hxΩ⟩, i))]
    calc ∑ i, |‖svec G φ' x i - (h i : ℂ)‖ ^ 2 - ‖svec G φ x i - (h i : ℂ)‖ ^ 2|
        ≤ ∑ _i : Fin N, B * e x * (2 * 2 + B * e x) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have e1 : svec G φ' x i - (h i : ℂ) = (svec G φ x i - (h i : ℂ)) + τf (⟨x, hxΩ⟩, i) := by
            rw [svec_of_mem G φ' ⟨x, hxΩ⟩ i, svec_of_mem G φ ⟨x, hxΩ⟩ i]
            simp only [hτf, Pi.sub_apply]
            ring
          rw [e1]
          refine (abs_norm_add_sq_sub_le _ _).trans ?_
          have ha : ‖svec G φ x i - (h i : ℂ)‖ ≤ 2 := by
            rw [svec_of_mem G φ ⟨x, hxΩ⟩ i]
            refine (norm_sub_le _ _).trans ?_
            rw [Complex.norm_real, Real.norm_eq_abs]
            linarith [hφ1 i, hh1 i]
          have ht' : ‖τf (⟨x, hxΩ⟩, i)‖ ≤ B * e x := hF.val ⟨x, hxΩ⟩ i
          exact mul_le_mul ht' (by linarith) (by positivity) (mul_nonneg hB (he0 x))
      _ = N * (B * e x * (4 + B * e x)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ N * (4 * B + B ^ 2) * e x := by
          have h1 : B * e x * (B * e x) ≤ B ^ 2 * e x := by
            have : B * e x * (B * e x) = B ^ 2 * e x * e x := by ring
            rw [this]
            exact mul_le_of_le_one_right (mul_nonneg (sq_nonneg B) (he0 x)) (he1 x)
          have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
          nlinarith [mul_le_mul_of_nonneg_left h1 hN]
  -- assembly
  have hsumg : ∑ x : Torus d (N₁ * L ^ m₁ * L ^ k), g x = ∑ x : G.Ω 1, F0 x := by
    rw [← Finset.sum_subset (Finset.subset_univ (G.Ω 1)) (fun x _ hx => by simp only [hg, hx, ↓reduceDIte])]
    rw [← Finset.sum_coe_sort (G.Ω 1) g]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hg, x.2, ↓reduceDIte]
  have hTP : |(1 / 2) * ∑ x : G.Ω 1, (if (x : Torus d (N₁ * L ^ m₁ * L ^ k)) ∈ Zr.sites then 0 else
          (a (G.layerIndex (x : Torus d (N₁ * L ^ m₁ * L ^ k))) /
            ((L : ℝ) ^ G.layerIndex (x : Torus d (N₁ * L ^ m₁ * L ^ k))) ^ 2) *
          ∑ i, ‖Ψ' x i - blockAvg G φ' x i‖ ^ 2) -
      (1 / 2) * ∑ x : G.Ω 1, (if (x : Torus d (N₁ * L ^ m₁ * L ^ k)) ∈ Zr.sites then 0 else
          (a (G.layerIndex (x : Torus d (N₁ * L ^ m₁ * L ^ k))) /
            ((L : ℝ) ^ G.layerIndex (x : Torus d (N₁ * L ^ m₁ * L ^ k))) ^ 2) *
          ∑ i, ‖Ψ x i - blockAvg G φ x i‖ ^ 2)| ≤ ∑ x : G.Ω 1, F0 x := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc _ ≤ (1 / 2) * ∑ x : G.Ω 1, 2 * F0 x :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => hPx x))
            (by norm_num)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hTQ : |(1 / 2) * ∑ x : Torus d (N₁ * L ^ m₁ * L ^ k), ∑ μ : Fin d,
        ((if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then 1 else 0) - Zr.starWeight x μ) *
          ∑ i, ‖barField G Ψ' φ' (x + Pi.single μ 1) i - barField G Ψ' φ' x i‖ ^ 2 -
      (1 / 2) * ∑ x : Torus d (N₁ * L ^ m₁ * L ^ k), ∑ μ : Fin d,
        ((if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then 1 else 0) - Zr.starWeight x μ) *
          ∑ i, ‖barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i‖ ^ 2| ≤
      d * ∑ x : G.Ω 1, F0 x := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hshift : ∀ μ : Fin d, ∑ x : Torus d (N₁ * L ^ m₁ * L ^ k), g (x + Pi.single μ 1) =
        ∑ x : Torus d (N₁ * L ^ m₁ * L ^ k), g x := fun μ =>
      Fintype.sum_equiv (Equiv.addRight (Pi.single μ 1)) _ _ (fun x => rfl)
    calc _ ≤ (1 / 2) * ∑ x : Torus d (N₁ * L ^ m₁ * L ^ k), ∑ μ : Fin d, (g x + g (x + Pi.single μ 1)) := by
          refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun x _ => ?_)) (by norm_num)
          rw [← Finset.sum_sub_distrib]
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ _ => hQx x μ)
      _ = (1 / 2) * ∑ μ : Fin d, (∑ x : Torus d (N₁ * L ^ m₁ * L ^ k), g x +
            ∑ x : Torus d (N₁ * L ^ m₁ * L ^ k), g (x + Pi.single μ 1)) := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_add_distrib]
      _ = d * ∑ x : G.Ω 1, F0 x := by
          simp only [hshift, hsumg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hTV : |ν / 2 * ∑ x ∈ Zr.sites, ∑ i, ‖svec G φ' x i - (h i : ℂ)‖ ^ 2 -
      ν / 2 * ∑ x ∈ Zr.sites, ∑ i, ‖svec G φ x i - (h i : ℂ)‖ ^ 2| ≤
      ν / 2 * N * (4 * B + B ^ 2) * ∑ x : G.Ω 1, e x := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ν / 2)]
    have hsub : ∑ x ∈ Zr.sites, e x ≤ ∑ x : G.Ω 1, e x := by
      rw [sum_sites_eq_sum_Ω Zr.sub_Ω e]
      refine Finset.sum_le_sum fun x _ => ?_
      split_ifs
      · exact le_rfl
      · exact he0 x
    calc _ ≤ ν / 2 * ∑ x ∈ Zr.sites, N * (4 * B + B ^ 2) * e x :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun x hx => hVx x hx)) (by positivity)
      _ = ν / 2 * (N * (4 * B + B ^ 2)) * ∑ x ∈ Zr.sites, e x := by rw [← Finset.mul_sum]; ring
      _ ≤ ν / 2 * (N * (4 * B + B ^ 2)) * ∑ x : G.Ω 1, e x :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
      _ = _ := by ring
  have hfin : ∑ x : G.Ω 1, (if Out x then
        (d + 1) * N * (2 * c * B' + B' ^ 2) / G.spacing x ^ 2 * e x else 0) = (d + 1) * ∑ x : G.Ω 1, F0 x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hF0, hK']
    split_ifs <;> ring
  rw [hfin]
  obtain ⟨h1a, h1b⟩ := abs_le.1 hTP
  obtain ⟨h2a, h2b⟩ := abs_le.1 hTQ
  obtain ⟨h3a, h3b⟩ := abs_le.1 hTV
  rw [abs_le]
  constructor <;> linarith

/-- `ℓ(x)^{-2} ≤ L^{k(d-2)} ℓ(x)^{-d}` on `Ω₁` (`d ≥ 2`): `β₀ ℓ(x)^{-2} ≤ β_k ℓ(x)^{-d}`. -/
theorem inv_spacing_sq_le_siteWeight (hd2 : 2 ≤ d) (x : G.Ω 1) :
    (G.spacing x ^ 2)⁻¹ ≤ (L : ℝ) ^ (k * (d - 2)) * siteWeight G x := by
  obtain ⟨-, hxk, -⟩ := G.layerIndex_spec x.2
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  set ℓ := G.spacing x with hℓ
  have hℓdef : ℓ = (L : ℝ) ^ G.layerIndex (x : Torus d (N₁ * L ^ m₁ * L ^ k)) := rfl
  have hℓ1 : 1 ≤ ℓ := by rw [hℓdef]; exact one_le_pow₀ hL
  have hℓ0 : 0 < ℓ := by linarith
  have hℓk : ℓ ≤ (L : ℝ) ^ k := by rw [hℓdef]; exact pow_le_pow_right₀ hL hxk
  have hsw : siteWeight G x = (ℓ ^ d)⁻¹ := by
    unfold siteWeight; rw [← hℓdef, inv_pow]
  rw [hsw]
  have hd' : d = (d - 2) + 2 := by omega
  have hpow : ℓ ^ d = ℓ ^ (d - 2) * ℓ ^ 2 := by rw [← pow_add, ← hd']
  have hk2 : ℓ ^ (d - 2) ≤ (L : ℝ) ^ (k * (d - 2)) := by
    rw [pow_mul]; exact pow_le_pow_left₀ hℓ0.le hℓk _
  have hp0 : 0 < ℓ ^ (d - 2) := by positivity
  rw [hpow, mul_inv, ← mul_assoc]
  calc (ℓ ^ 2)⁻¹ = ℓ ^ (d - 2) * (ℓ ^ (d - 2))⁻¹ * (ℓ ^ 2)⁻¹ := by
        rw [mul_inv_cancel₀ hp0.ne', one_mul]
    _ ≤ (L : ℝ) ^ (k * (d - 2)) * (ℓ ^ (d - 2))⁻¹ * (ℓ ^ 2)⁻¹ := by
        gcongr

/-- **The oscillation of `β₀ (A_{Ω₁} - A_Z)` under a change of the field on a set of top-layer blocks**, for constants
`(K_w, δ_w)` of the weighted Proposition 5.1 (`weightedProp51S_exists`).  Let `ψ ∈ Ψ̃(𝔹; τ)` (`K₁ τ ≤ min(δ_*, δ_w)`),
`ψ' ∈ Ψ̃(𝔹; τ')` agree off the set `Z_f` of top-layer blocks and differ by at most `t ≤ min(δ_*, δ_w)` on its blocks;
let the fine sites of `Z_f` lie in the region `Z_r`, and let every site of `Ω₁` read by the action outside `Z_r` be at
path distance at least `R` from the shadow of these fine sites.  Then
`|β₀ ΔA(ψ') - β₀ ΔA(ψ)| ≤ β_k (d+1) N (2 K₁τ B' + B'²) e^{-γ_w R/2} |Z_f| S_{γ_w/2} + β₀ ν L^{kd} (N/2)(4B + B²) |Z_f| S_{γ_w}`
with `B = K_w C_F t`, `B' = B e^{2dγ_w}`, `S_γ = e^{γ(2d+1)} C(d, L, γ)` (`|h| ≤ 1` componentwise). -/
theorem effAction_sub_actionZ_osc_le_of_weighted {Kw δw : ℝ} (hWP : WeightedProp51S d L N Kw δw)
    (hKw : 0 ≤ Kw) (H : BgHyp d L k ϱ a 0) (hOp : Dec2.OpSetting G a 0) (hk : 1 ≤ k)
    (hsep2 : 2 * d * Real.log L ≤ gammaW d / 4 * (ϱ - 1)) {τ τ' : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ bgC1 d L N)
    (hτs : bgK1 d L N * τ ≤ min (deltaStar d L N) δw) (hτ' : 0 < τ') (hτ1' : τ' ≤ bgC1 d L N)
    {ψ ψ' : BlockField d L (N₁ * L ^ m₁) k N} (ht : TubeOn G Set.univ τ ψ) (ht' : TubeOn G Set.univ τ' ψ')
    (Zf : Finset (Torus d (N₁ * L ^ m₁ * L ^ (k - k))))
    (hZ : ∀ z ∈ Zf, OverTop G ({z} : Set (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))))
    (hoff : ∀ z ∉ Zf, ψ' z = ψ z) {t : ℝ} (ht0 : 0 ≤ t) (hts : t ≤ min (deltaStar d L N) δw)
    (hdiff : ∀ z ∈ Zf, rn (fun i => ψ' z i - ψ z i) ≤ t)
    (Zr : Region G) (hZr : ∀ x, jBlock d L (N₁ * L ^ m₁) k k x ∈ Zf → x ∈ Zr.sites) {R : ℝ}
    (hmargin : ∀ y ∈ G.Ω 1, (y ∉ Zr.sites ∨ ∃ μ : Fin d, y + Pi.single μ 1 ∉ Zr.sites ∨
        y - Pi.single μ 1 ∉ Zr.sites) →
      ENNReal.ofReal R ≤ siteSetDist G (shadow G (Zf.biUnion (fib d L (N₁ * L ^ m₁) k k))) y)
    {ν : ℝ} (hν : 0 ≤ ν) (h : Fin N → ℝ) (hh1 : ∀ i, |h i| ≤ 1) {β0 : ℝ} (hβ0 : 0 ≤ β0) :
    |β0 * (effAction G a ψ' - actionZ G a Zr ν h ψ') - β0 * (effAction G a ψ - actionZ G a Zr ν h ψ)| ≤
      betaK d L k β0 * ((d + 1) * N * (2 * (bgK1 d L N * τ) * (Kw * (cF d L * t) * Real.exp (2 * d * gammaW d)) +
          (Kw * (cF d L * t) * Real.exp (2 * d * gammaW d)) ^ 2)) * Real.exp (-(gammaW d / 2 * R)) *
        (Zf.card * (Real.exp (gammaW d / 2 * (2 * d + 1)) * countConst d L (gammaW d / 2))) +
      β0 * ν * ((L : ℝ) ^ k) ^ d * (N / 2 * (4 * (Kw * (cF d L * t)) + (Kw * (cF d L * t)) ^ 2)) *
        (Zf.card * (Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d))) := by
  classical
  have hd3 : 3 ≤ d := H.hd
  have hd0 : 0 < d := by omega
  have hγ0 : 0 ≤ gammaW d := gammaW_nonneg hd0
  have hγ : 0 < gammaW d := by unfold gammaW; have := agmonRate_pos (d := d) hd0; positivity
  have hB : 0 ≤ Kw * (cF d L * t) := mul_nonneg hKw (mul_nonneg (cF_pos d L).le ht0)
  have hF := coreResponse_farBounds_of_weighted hWP hd0 H hOp hτ hτ1 hτs hτ' hτ1' ht ht' Zf hoff ht0 hts hdiff
  have hosc := effAction_sub_actionZ_osc_le_of_far H hτ hτ1 ht Zf hoff Zr hZr hγ0 hB hF hν h hh1
  obtain ⟨hϱ, hcond⟩ := opSetting_counting hOp
  have hcond2 : 2 * d * Real.log L ≤ gammaW d / 2 / 2 * (ϱ - 1) := by
    have e : gammaW d / 2 / 2 = gammaW d / 4 := by ring
    rw [e]; exact hsep2
  set W := Zf.biUnion (fib d L (N₁ * L ^ m₁) k k) with hW
  set B := Kw * (cF d L * t) with hBdef
  set K' := 2 * (bgK1 d L N * τ) * (B * Real.exp (2 * d * gammaW d)) + (B * Real.exp (2 * d * gammaW d)) ^ 2
    with hK'
  have hK'0 : 0 ≤ K' := by
    have := (bgK1_pos d L N).le
    positivity
  rw [← mul_sub, abs_mul, abs_of_nonneg hβ0]
  refine (mul_le_mul_of_nonneg_left hosc hβ0).trans ?_
  rw [mul_add]
  have hS2 := sum_siteWeight_decay_shadow_biUnion_le (G := G) hk hϱ (by positivity : 0 < gammaW d / 2) hcond2
    Zf hZ
  have hS1 := sum_siteWeight_decay_shadow_biUnion_le (G := G) hk hϱ hγ hcond Zf hZ
  rw [← hW] at hS1 hS2
  refine add_le_add ?_ ?_
  · rw [Finset.mul_sum]
    set c1 := betaK d L k β0 * ((d + 1) * N * K') * Real.exp (-(gammaW d / 2 * R)) with hc1
    have hc10 : 0 ≤ c1 := by
      have : 0 ≤ betaK d L k β0 := by unfold betaK; positivity
      positivity
    calc ∑ x : G.Ω 1, β0 * (if ((x : Torus d (N₁ * L ^ m₁ * L ^ k)) ∉ Zr.sites ∨ ∃ μ : Fin d,
            (x : Torus d (N₁ * L ^ m₁ * L ^ k)) + Pi.single μ 1 ∉ Zr.sites ∨
              (x : Torus d (N₁ * L ^ m₁ * L ^ k)) - Pi.single μ 1 ∉ Zr.sites) then
          (d + 1) * N * K' / G.spacing x ^ 2 * decay (gammaW d) (siteSetDist G (shadow G W) x) else 0)
        ≤ ∑ x : G.Ω 1, c1 * (siteWeight G x * decay (gammaW d / 2) (siteSetDist G (shadow G W) x)) := by
          refine Finset.sum_le_sum fun x _ => ?_
          split_ifs with hOx
          · have hm := hmargin x x.2 hOx
            have hdec : decay (gammaW d) (siteSetDist G (shadow G W) x) ≤
                Real.exp (-(gammaW d / 2 * R)) * decay (gammaW d / 2) (siteSetDist G (shadow G W) x) := by
              have e : decay (gammaW d) (siteSetDist G (shadow G W) x) =
                  decay (gammaW d / 2) (siteSetDist G (shadow G W) x) *
                    decay (gammaW d / 2) (siteSetDist G (shadow G W) x) := by
                rw [← Localization.decay_split]; ring_nf
              rw [e]
              exact mul_le_mul_of_nonneg_right (decay_le_exp_dist (by positivity) hm) (decay_nonneg _ _)
            have hsw := inv_spacing_sq_le_siteWeight (G := G) (by omega) x
            have hβk : betaK d L k β0 = β0 * (L : ℝ) ^ (k * (d - 2)) := rfl
            have hsp := spacing_pos G (x := (x : Torus d (N₁ * L ^ m₁ * L ^ k)))
            calc β0 * ((d + 1) * N * K' / G.spacing x ^ 2 * decay (gammaW d) (siteSetDist G (shadow G W) x))
                = (d + 1) * N * K' * (β0 * (G.spacing x ^ 2)⁻¹) *
                    decay (gammaW d) (siteSetDist G (shadow G W) x) := by ring
              _ ≤ (d + 1) * N * K' * (β0 * ((L : ℝ) ^ (k * (d - 2)) * siteWeight G x)) *
                    (Real.exp (-(gammaW d / 2 * R)) * decay (gammaW d / 2) (siteSetDist G (shadow G W) x)) := by
                  refine mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsw hβ0)
                    (by positivity)) hdec (decay_nonneg _ _) ?_
                  have := siteWeight_nonneg G (x : Torus d (N₁ * L ^ m₁ * L ^ k))
                  positivity
              _ = c1 * (siteWeight G x * decay (gammaW d / 2) (siteSetDist G (shadow G W) x)) := by
                  rw [hc1, hβk]; ring
          · rw [mul_zero]
            exact mul_nonneg hc10 (mul_nonneg (siteWeight_nonneg G _) (decay_nonneg _ _))
      _ = c1 * ∑ x : G.Ω 1, siteWeight G x * decay (gammaW d / 2) (siteSetDist G (shadow G W) x) := by
          rw [Finset.mul_sum]
      _ ≤ c1 * (Zf.card * (Real.exp (gammaW d / 2 * (2 * d + 1)) * countConst d L (gammaW d / 2))) :=
          mul_le_mul_of_nonneg_left hS2 hc10
      _ = _ := by rw [hc1]
  · have hsum : ∑ x : G.Ω 1, decay (gammaW d) (siteSetDist G (shadow G W) x) ≤
        ((L : ℝ) ^ k) ^ d * ∑ x : G.Ω 1, siteWeight G x * decay (gammaW d) (siteSetDist G (shadow G W) x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      have h1 := inv_pow_le_siteWeight (G := G) x
      have hp : (0 : ℝ) < ((L : ℝ) ^ k) ^ d := by
        have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
        positivity
      have h2 : 1 ≤ ((L : ℝ) ^ k) ^ d * siteWeight G x := by
        rw [inv_le_iff_one_le_mul₀ hp] at h1
        linarith [mul_comm (siteWeight G x) (((L : ℝ) ^ k) ^ d)]
      calc decay (gammaW d) (siteSetDist G (shadow G W) x)
          = 1 * decay (gammaW d) (siteSetDist G (shadow G W) x) := (one_mul _).symm
        _ ≤ ((L : ℝ) ^ k) ^ d * siteWeight G x * decay (gammaW d) (siteSetDist G (shadow G W) x) :=
            mul_le_mul_of_nonneg_right h2 (decay_nonneg _ _)
        _ = _ := by ring
    have hc2 : 0 ≤ β0 * (ν / 2 * N * (4 * B + B ^ 2)) := by positivity
    calc β0 * (ν / 2 * N * (4 * B + B ^ 2) * ∑ x : G.Ω 1, decay (gammaW d) (siteSetDist G (shadow G W) x))
        = β0 * (ν / 2 * N * (4 * B + B ^ 2)) *
            ∑ x : G.Ω 1, decay (gammaW d) (siteSetDist G (shadow G W) x) := by ring
      _ ≤ β0 * (ν / 2 * N * (4 * B + B ^ 2)) * (((L : ℝ) ^ k) ^ d *
            (Zf.card * (Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d)))) := by
          refine mul_le_mul_of_nonneg_left (hsum.trans ?_) hc2
          exact mul_le_mul_of_nonneg_left hS1 (by positivity)
      _ = _ := by ring

end Osc

section Source

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ)
  (a : ℕ → ℝ) [NeZero N] {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₁ * L ^ m₁ * L ^ (k - k)))
  (w : Fin d → ℕ) (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₁ * L ^ m₁ * L ^ (k - k))
  {X : Set (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L (N₁ * L ^ m₁) k k x ∈ X) (H : BgHyp d L k ϱ a 0)

local notation "Kz" => psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H
local notation "Zb" => boxFinset (L := L) (N₀ := N₁ * L ^ m₁) (k := k) b0 w

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **The oscillation hypothesis `hosc` of `denominatorRestricted_bounds_of_osc` for a removed component**: the core
`Z₀ = box b₀ w` (top-layer blocks, `hΩ`) has its fine sites in `Z_r`, and the sites of `Ω₁` read by the action outside
`Z_r` are at path distance `≥ R` from the shadow of these fine sites.  Then on the cutoff ball (`ψ_k(u)`, `u` within
`ρ = C₆ β_k^{-1/2} p₀` of `ψ⁰_k`) the oscillation of `β₀ (A_{Ω₁} - A_Z)` about `ψ⁰_k` is at most
`E = β_k (d+1) N (2 K₁ K₆δ B' + B'²) e^{-γ_w R/2} |Z₀| S_{γ_w/2} + β₀ ν L^{kd} (N/2)(4B + B²) |Z₀| S_{γ_w}`,
`B = K_w C_F ρ`, `B' = B e^{2dγ_w}`.  Smallness: `K₁ K₆ δ, ρ ≤ min(δ_*, δ_w)`; separation for the rate `γ_w/2`. -/
theorem hosc_of_margin_of_weighted {Kw δw : ℝ} (hWP : WeightedProp51S d L N Kw δw) (hKw : 0 ≤ Kw)
    (hOp : Dec2.OpSetting G a 0) (hsep2 : 2 * d * Real.log L ≤ gammaW d / 4 * (ϱ - 1)) {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)
    {ψk : BlockField d L (N₁ * L ^ m₁) k N} (hψk : TubeOn G (X \ box b0 w) δ ψk) (Zr : Region G) {ν : ℝ}
    (hν : 0 ≤ ν) (h : Fin N → ℝ) (hh1 : ∀ i, |h i| ≤ 1) {β0 p0 R : ℝ} (hβ0 : 0 < β0)
    (hp0 : 1 ≤ cSix d D Kz * p0)
    (hrad : Kz * δ + 5 * zeroRadius (cSix d D Kz) (betaK d L k β0) p0 ≤ etaDen d L N D)
    (hsmall : bgK1 d L N * (Kz * δ) ≤ min (deltaStar d L N) δw)
    (hρs : zeroRadius (cSix d D Kz) (betaK d L k β0) p0 ≤ min (deltaStar d L N) δw)
    (hZr : ∀ x, jBlock d L (N₁ * L ^ m₁) k k x ∈ box b0 w → x ∈ Zr.sites)
    (hmargin : ∀ y ∈ G.Ω 1, (y ∉ Zr.sites ∨ ∃ μ : Fin d, y + Pi.single μ 1 ∉ Zr.sites ∨
        y - Pi.single μ 1 ∉ Zr.sites) →
      ENNReal.ofReal R ≤ siteSetDist G (shadow G ((Zb).biUnion (fib d L (N₁ * L ^ m₁) k k))) y) :
    ∀ u : SuppSpace (Zb) N,
      ZeroCutoff (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)
        (zeroRadius (cSix d D Kz) (betaK d L k β0) p0) u →
      |β0 * (effAction G a (mergeField (Zb) ψk u) - actionZ G a Zr ν h (mergeField (Zb) ψk u)) -
        β0 * (effAction G a (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk) -
          actionZ G a Zr ν h (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk))| ≤
        betaK d L k β0 * ((d + 1) * N * (2 * (bgK1 d L N * (Kz * δ)) *
            (Kw * (cF d L * zeroRadius (cSix d D Kz) (betaK d L k β0) p0) * Real.exp (2 * d * gammaW d)) +
            (Kw * (cF d L * zeroRadius (cSix d D Kz) (betaK d L k β0) p0) * Real.exp (2 * d * gammaW d)) ^ 2)) *
          Real.exp (-(gammaW d / 2 * R)) *
          ((Zb).card * (Real.exp (gammaW d / 2 * (2 * d + 1)) * countConst d L (gammaW d / 2))) +
        β0 * ν * ((L : ℝ) ^ k) ^ d * (N / 2 * (4 * (Kw * (cF d L * zeroRadius (cSix d D Kz) (betaK d L k β0) p0)) +
            (Kw * (cF d L * zeroRadius (cSix d D Kz) (betaK d L k β0) p0)) ^ 2)) *
          ((Zb).card * (Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d))) := by
  intro u hu
  set K := Kz with hKdef
  have hK : 0 < K := psiZeroK_pos N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H
  have hd0 : 0 < d := by omega
  have hD1 : 1 ≤ D := (hw1 ⟨0, hd0⟩).trans (hwD _)
  have hβk : 0 < betaK d L k β0 := by
    unfold betaK
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hC6 : 0 < cSix d D K := cSix_pos hd0 hD1 hK.le
  set ρ := zeroRadius (cSix d D K) (betaK d L k β0) p0 with hρdef
  have hρpos : 0 < ρ := zeroRadius_pos hC6 hβk hp0
  have hη1 : etaDen d L N D ≤ bgC1 d L N := min_le_left _ _
  have hη0 : etaDen d L N D ≤ bgC0 d L N := hη1.trans (bgC1_le_bgC0 d L N hd0)
  have hη16 : etaDen d L N D ≤ 1 := hη0.trans ((bgC0_le d L N).trans (by norm_num))
  have hKδ : 0 < K * δ := mul_pos hK hδ
  have hKδ1 : K * δ ≤ 1 := by linarith
  have hρ1 : ρ ≤ 1 := by linarith
  obtain ⟨hsol, -⟩ := psiZero_spec N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk
  set ψ0 := psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk with hψ0
  have ht0 : TubeOn G Set.univ (K * δ) ψ0 := tubeOn_univ_of_data G hdata hsol.1
  have hclose : ∀ z, rn (fun i => mergeField (Zb) ψk u z i - ψ0 z i) ≤ ρ := by
    intro z
    by_cases hz : z ∈ Zb
    · have h1 : (fun i => mergeField (Zb) ψk u z i - ψ0 z i) = fun i => u (⟨z, hz⟩, i) - ψ0 z i := by
        funext i; rw [mergeField_of_mem hz i]
      rw [h1]; exact (hu ⟨z, hz⟩).le
    · have h1 : (fun i => mergeField (Zb) ψk u z i - ψ0 z i) = fun _ => 0 := by
        funext i
        rw [mergeField_of_not_mem hz, hsol.2.1 z (fun h => hz (mem_boxFinset.2 h))]
        simp
      rw [h1]
      simp [rn, hρpos.le]
  have ht' : TubeOn G Set.univ (K * δ + 5 * ρ) (mergeField (Zb) ψk u) :=
    tubeOn_perturb G hKδ1 hρpos.le hρ1 ht0 hclose
  have hZ : ∀ z ∈ Zb, OverTop G ({z} : Set (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))) := by
    intro z hz x hx
    refine hΩ x (Or.inl ?_)
    rw [Set.mem_singleton_iff.1 hx]
    exact mem_boxFinset.1 hz
  have hoff : ∀ z ∉ Zb, mergeField (Zb) ψk u z = ψ0 z := by
    intro z hz
    rw [mergeField_of_not_mem hz, hsol.2.1 z (fun h => hz (mem_boxFinset.2 h))]
  have hdiff : ∀ z ∈ Zb, rn (fun i => mergeField (Zb) ψk u z i - ψ0 z i) ≤ ρ := fun z _ => hclose z
  exact effAction_sub_actionZ_osc_le_of_weighted hWP hKw H hOp hk hsep2 hKδ (by linarith) hsmall
    (by positivity) (by linarith) ht0 ht' (Zb) hZ hoff hρpos.le hρs hdiff Zr
    (fun x hx => hZr x (mem_boxFinset.1 hx)) hmargin hν h hh1 hβ0.le

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **Lemma III.8.2 for the restricted density with the geometric margin** (`denominatorRestricted_bounds_of_osc`
with `hosc_of_margin_of_weighted`): `|Ẽ₀^Z - Ẽ₀| ≤ E` and `|Ẽ₀^Z| ≤ C_Ẽ D₀^d + E`, `E` as in
`hosc_of_margin_of_weighted`. -/
theorem denominatorRestricted_bounds_of_margin_of_weighted {Kw δw : ℝ} (hWP : WeightedProp51S d L N Kw δw)
    (hKw : 0 ≤ Kw) (hOp : Dec2.OpSetting G a 0) (hsep2 : 2 * d * Real.log L ≤ gammaW d / 4 * (ϱ - 1)) {δ : ℝ}
    (hδ : 0 < δ) (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)
    {ψk : BlockField d L (N₁ * L ^ m₁) k N} (hψk : TubeOn G (X \ box b0 w) δ ψk) (Zr : Region G) {ν : ℝ}
    (hν : 0 ≤ ν) (h : Fin N → ℝ) (hh1 : ∀ i, |h i| ≤ 1) {β0 p0 R : ℝ} (ha : ∀ j, 0 ≤ a j) (hβ0 : 0 < β0)
    (hp0 : 1 ≤ cSix d D Kz * p0)
    (hrad : Kz * δ + 5 * zeroRadius (cSix d D Kz) (betaK d L k β0) p0 ≤ etaDen d L N D)
    (hsmall : bgK1 d L N * (Kz * δ) ≤ min (deltaStar d L N) δw)
    (hρs : zeroRadius (cSix d D Kz) (betaK d L k β0) p0 ≤ min (deltaStar d L N) δw)
    (hZr : ∀ x, jBlock d L (N₁ * L ^ m₁) k k x ∈ box b0 w → x ∈ Zr.sites)
    (hmargin : ∀ y ∈ G.Ω 1, (y ∉ Zr.sites ∨ ∃ μ : Fin d, y + Pi.single μ 1 ∉ Zr.sites ∨
        y - Pi.single μ 1 ∉ Zr.sites) →
      ENNReal.ofReal R ≤ siteSetDist G (shadow G ((Zb).biUnion (fib d L (N₁ * L ^ m₁) k k))) y) :
    |tildeE0Restricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0 -
        tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk (betaK d L k β0) p0| ≤
      betaK d L k β0 * ((d + 1) * N * (2 * (bgK1 d L N * (Kz * δ)) *
          (Kw * (cF d L * zeroRadius (cSix d D Kz) (betaK d L k β0) p0) * Real.exp (2 * d * gammaW d)) +
          (Kw * (cF d L * zeroRadius (cSix d D Kz) (betaK d L k β0) p0) * Real.exp (2 * d * gammaW d)) ^ 2)) *
        Real.exp (-(gammaW d / 2 * R)) *
        ((Zb).card * (Real.exp (gammaW d / 2 * (2 * d + 1)) * countConst d L (gammaW d / 2))) +
      β0 * ν * ((L : ℝ) ^ k) ^ d * (N / 2 * (4 * (Kw * (cF d L * zeroRadius (cSix d D Kz) (betaK d L k β0) p0)) +
          (Kw * (cF d L * zeroRadius (cSix d D Kz) (betaK d L k β0) p0)) ^ 2)) *
        ((Zb).card * (Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d))) ∧
    |tildeE0Restricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr ν h β0 p0| ≤
      cTildeE N d D * (D : ℝ) ^ d +
      (betaK d L k β0 * ((d + 1) * N * (2 * (bgK1 d L N * (Kz * δ)) *
          (Kw * (cF d L * zeroRadius (cSix d D Kz) (betaK d L k β0) p0) * Real.exp (2 * d * gammaW d)) +
          (Kw * (cF d L * zeroRadius (cSix d D Kz) (betaK d L k β0) p0) * Real.exp (2 * d * gammaW d)) ^ 2)) *
        Real.exp (-(gammaW d / 2 * R)) *
        ((Zb).card * (Real.exp (gammaW d / 2 * (2 * d + 1)) * countConst d L (gammaW d / 2))) +
      β0 * ν * ((L : ℝ) ^ k) ^ d * (N / 2 * (4 * (Kw * (cF d L * zeroRadius (cSix d D Kz) (betaK d L k β0) p0)) +
          (Kw * (cF d L * zeroRadius (cSix d D Kz) (betaK d L k β0) p0)) ^ 2)) *
        ((Zb).card * (Real.exp (gammaW d * (2 * d + 1)) * countConst d L (gammaW d)))) :=
  denominatorRestricted_bounds_of_osc G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk Zr h ha hν hβ0 hp0
    hrad (hosc_of_margin_of_weighted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hWP hKw hOp hsep2 hδ hδc hψk Zr
      hν h hh1 hβ0 hp0 hrad hsmall hρs hZr hmargin)

end Source

end Balaban.LargeField
