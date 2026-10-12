/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.DenominatorHess
public import Balaban.LargeField.R.DenominatorTaylor
public import Balaban.LargeField.R.DenominatorGauss
public import Balaban.LargeField.R.DenominatorTube
public import Balaban.LargeField.R.RhoZero
public import Balaban.LargeField.R.PsiZeroAnalyticLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The squeeze of the normalized action about `ψ⁰_k` (Lemma III.8.2, the expansion (3.3))

Under the geometry of Lemma III.3.3 and the smallness `K₆ δ + 5 ρ ≤ etaDen` (`ρ` the radius of the cutoff `χ_{Z₀}`),
the variational function `effOn` of (2.34) is `C²` at every point `ψ⁰ + y` of the polydisc `|y(z)| < ρ`, has vanishing
derivative at `ψ⁰` (a local minimum of the open tube), and its Hessian lies in
`[hessConst, 2 L^{k(d-2)}]` there; hence `effOn(ψ⁰) + (c/2)‖y‖² ≤ effOn(ψ⁰ + y) ≤ effOn(ψ⁰) + L^{k(d-2)}‖y‖²`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField
open Balaban Balaban.Multiscale Balaban.Background MeasureTheory Filter Topology

section Den

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
  [NeZero N]

variable {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)

local notation "Zb" => boxFinset (L := L) (N₀ := N₀) (k := k) b0 w

/-- The tube radius on which the denominator estimates are valid. -/
noncomputable def etaDen (d L N D : ℕ) [NeZero L] : ℝ := min (bgC1 d L N) (etaHess d L N D)

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- The pointwise squeeze of the normalized action about the critical point. -/
theorem effAction_squeeze {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) {ρ : ℝ} (hρ : 0 < ρ)
    (hrad : psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ + 5 * ρ ≤ etaDen d L N D) :
    let ψ0 := psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk
    let u0 := restrictSupp Zb ψ0
    fderiv ℝ (effOn G a Zb ψk) u0 = 0 ∧
    (∀ y ∈ siteBall (Z := ↥Zb) (N := N) ρ,
      ContDiffAt ℝ 2 (effOn G a Zb ψk) (u0 + y)) ∧
    (∀ y ∈ siteBall (Z := ↥Zb) (N := N) ρ,
      effOn G a Zb ψk u0 + hessConst d L k D / 2 * ‖y‖ ^ 2 ≤ effOn G a Zb ψk (u0 + y) ∧
      effOn G a Zb ψk (u0 + y) ≤
        effOn G a Zb ψk u0 + (L : ℝ) ^ (k * (d - 2)) * ‖y‖ ^ 2) := by
  intro ψ0 u0
  have hρ0 : 0 ≤ ρ := hρ.le
  obtain ⟨hsol, -⟩ := psiZero_spec N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk
  set K := psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H with hKdef
  have hK : 0 < K := psiZeroK_pos N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H
  have hKδ : 0 < K * δ := mul_pos hK hδ
  have hd0 : 0 < d := by omega
  set η := etaDen d L N D with hηdef
  have hη1 : η ≤ bgC1 d L N := min_le_left _ _
  have hηh : η ≤ etaHess d L N D := min_le_right _ _
  have hη0 : η ≤ bgC0 d L N := hη1.trans (bgC1_le_bgC0 d L N hd0)
  have hηpos : 0 < η := by linarith
  have hη16 : η ≤ 1 := hη0.trans ((bgC0_le d L N).trans (by norm_num))
  have hag : ∀ z, z ∉ box b0 w → ψ0 z = ψk z := hsol.2.1
  have hmerge0 : mergeField Zb ψk u0 = ψ0 :=
    mergeField_restrict (fun z hz => hag z (fun h => hz (mem_boxFinset.2 h)))
  have ht0 : TubeOn G Set.univ (K * δ) ψ0 := tubeOn_univ_of_data G hdata hsol.1
  have hρ1 : ρ ≤ 1 := by linarith
  have hKδ1 : K * δ ≤ 1 := by linarith
  have hmem : ∀ y ∈ siteBall (Z := ↥Zb) (N := N) ρ, TubeOn G Set.univ η (mergeField Zb ψk (u0 + y)) := by
    intro y hy
    refine tubeOn_mono G hrad (tubeOn_perturb G hKδ1 hρ0 hρ1 ht0 ?_)
    intro z
    by_cases hz : z ∈ Zb
    · have h1 : (fun i => mergeField Zb ψk (u0 + y) z i - ψ0 z i) = fun i => y (⟨z, hz⟩, i) := by
        funext i
        rw [mergeField_of_mem hz i]
        simp [u0, restrictSupp]
      rw [h1]
      unfold rn
      exact Real.sqrt_le_iff.2 ⟨hρ0, (hy ⟨z, hz⟩).le⟩
    · have h1 : (fun i => mergeField Zb ψk (u0 + y) z i - ψ0 z i) = fun _ => 0 := by
        funext i
        rw [mergeField_of_not_mem hz, hag z (fun h => hz (mem_boxFinset.2 h))]
        simp
      rw [h1]
      simp [rn, hρ0]
  have hu0 : TubeOn G Set.univ η (mergeField Zb ψk u0) := by
    simpa using hmem 0 (by intro z; simpa using pow_pos hρ 2)
  have hdiff : DifferentiableAt ℝ (effOn G a Zb ψk) u0 :=
    ((contDiffAt_effOn G Zb H hηpos hη0 hη1 ψk hu0 (n := 2)).differentiableAt (by norm_num))
  have hcrit : fderiv ℝ (effOn G a Zb ψk) u0 = 0 := by
    have hmin : IsLocalMin (effOn G a Zb ψk) u0 := by
      have hcont : Continuous (mergeField Zb ψk : SuppSpace Zb N → BlockField d L N₀ k N) :=
        (contDiff_mergeField (n := 0) ψk).continuous
      have hev : ∀ᶠ u in 𝓝 u0, TubeOn G X (K * δ) (mergeField Zb ψk u) := by
        have := eventually_tubeOn G (hmerge0 ▸ hsol.1 : TubeOn G X (K * δ) (mergeField Zb ψk u0))
        exact (hcont.tendsto u0).eventually this
      filter_upwards [hev] with u hu
      have h1 := hsol.2.2 (mergeField Zb ψk u) hu (fun z hz => mergeField_of_not_mem
        (fun h => hz (mem_boxFinset.1 h)))
      have h2 : effOn G a Zb ψk u0 = effAction G a ψ0 := by
        show effAction G a (mergeField Zb ψk u0) = _
        rw [hmerge0]
      rw [h2]
      exact h1
    exact hmin.fderiv_eq_zero
  have hF : ∀ y ∈ siteBall (Z := ↥Zb) (N := N) ρ, ContDiffAt ℝ 2 (effOn G a Zb ψk) (u0 + y) := fun y hy =>
    contDiffAt_effOn G Zb H hηpos hη0 hη1 ψk (hmem y hy)
  have hΩZ : OverTop G (Zb : Set (Torus d (N₀ * L ^ (k - k)))) := fun x hx =>
    hΩ x (Or.inl (mem_boxFinset.1 (Finset.mem_coe.1 hx)))
  have hlow : ∀ y ∈ siteBall (Z := ↥Zb) (N := N) ρ, ∀ v : SuppSpace Zb N,
      hessConst d L k D * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (effOn G a Zb ψk)) (u0 + y) v v := by
    intro y hy v
    have := psiZero_hess_of_geometry H hk b0 w hw1 hwD hm hΩ hηpos hη0 hη1 hηh (hmem y hy) v
    rw [effOn_merge, restrict_mergeField] at this
    exact this
  have hup : ∀ y ∈ siteBall (Z := ↥Zb) (N := N) ρ, ∀ v : SuppSpace Zb N,
      fderiv ℝ (fderiv ℝ (effOn G a Zb ψk)) (u0 + y) v v ≤ 2 * (L : ℝ) ^ (k * (d - 2)) * ‖v‖ ^ 2 := by
    intro y hy v
    have := effOn_hess_le H hk hd hηpos hη0 hη1 hΩZ (hmem y hy) v
    rw [effOn_merge, restrict_mergeField] at this
    exact this
  refine ⟨hcrit, hF, fun y hy => ?_⟩
  have hT := taylor_two_sided (y := u0 + y) (hy := by show u0 + y - u0 ∈ siteBall (Z := ↥Zb) (N := N) ρ; rwa [add_sub_cancel_left]) (F := effOn G a Zb ψk) (x0 := u0) (c := hessConst d L k D)
    (C := 2 * (L : ℝ) ^ (k * (d - 2))) (S := {x : SuppSpace Zb N | x - u0 ∈ siteBall (Z := ↥Zb) (N := N) ρ})
    (fun y hy t ht => by
      show (u0 + t • (y - u0)) - u0 ∈ siteBall (Z := ↥Zb) (N := N) ρ
      rw [add_sub_cancel_left]
      exact star_siteBall hy ht.1 ht.2)
    (fun x hx => by
      have := hF (x - u0) hx
      rwa [add_sub_cancel] at this)
    hcrit
    (fun x hx v => by
      have := hlow (x - u0) hx v
      rwa [add_sub_cancel] at this)
    (fun x hx v => by
      have := hup (x - u0) hx v
      rwa [add_sub_cancel] at this)
  have := hT
  rw [add_sub_cancel_left] at this
  refine ⟨by linarith [this.1], ?_⟩
  linarith [this.2]
end Den

end Balaban.LargeField
