/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CancelIdentity
public import Balaban.LargeField.R.DenominatorSqueeze
public import Balaban.LargeField.R.PsiZeroHessInput
public import Balaban.LargeField.R.PsiZeroHessLine
public import Balaban.LargeField.R.PsiZeroHessRef
public import Balaban.LargeField.R.PsiZeroAnalyticAction
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The first variation at `ψ⁰_k` (P7 (2.52); LF-RECONSTRUCTION Lemmas III.3.3 and III.6.3, first step)

Convention: the massless reference of P7 (mass `0` in `BgHyp`).

* `firstVar_basis`: the first variation `firstVar` of the effective action at a real block field `ψ` in the
  direction of the basis perturbation at `(z₀, i₀)`, `z₀` a block of `Z`, is
  `(a_k / L^{2k}) · L^{kd} · Re r(z₀, i₀)`, `r = ψ - Q_k φ_k(ψ)` the residual of Definition III.6.1.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.ActionConv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.LargeField Finset

section Basic

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

/-- The data `lift_k ψ̃⁰_k` with a real constant `h` is real. -/
theorem psiZeroData_isReal (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) :
    (psiZeroData G ψ0 h).IsReal := by
  intro x i
  constructor
  · by_cases hx : x ∈ dataSites G
    · simp [psiZeroData, liftSingle_Ψ G _ _ hx]
    · simp [(psiZeroData G ψ0 h).Ψ_zero x hx]
  · by_cases hx : x ∈ G.Ω 1
    · simp [psiZeroData, liftSingle_h G _ _ hx]
    · simp [(psiZeroData G ψ0 h).h_zero x hx]

/-- `psiZeroData` and `dataR` have the same field `Ψ` (they differ only in the constant `h`). -/
theorem psiZeroData_Ψ_eq_dataR (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (ψ : BlockField d L N₀ k N) (hψ : ∀ z i, ψ0 ⟨k, z⟩ i = ψ z i) :
    (psiZeroData G ψ0 h).Ψ = (dataR G ψ).Ψ := by
  funext x
  by_cases hx : x ∈ dataSites G
  · funext i
    simp [psiZeroData, dataR, dataC, liftSingle_Ψ G _ _ hx, hψ]
  · rw [(psiZeroData G ψ0 h).Ψ_zero x hx, (dataR G ψ).Ψ_zero x hx]

/-- At mass `0` the background field only depends on the field `Ψ` of (real) data. -/
theorem bgField_congr_Ψ {D D' : BgData G N} (hD : D.IsReal) (hD' : D'.IsReal) (hΨ : D.Ψ = D'.Ψ) :
    bgField G a 0 D = bgField G a 0 D' := by
  have hact : ∀ φ, action G a 0 D φ = action G a 0 D' φ := by
    intro φ; simp [action, hΨ]
  have hiff : ∀ φ, IsMinimizer G a 0 D φ ↔ IsMinimizer G a 0 D' φ := by
    intro φ
    unfold IsMinimizer
    simp only [hact, hD, hD', true_and]
  have e : IsMinimizer G a 0 D = IsMinimizer G a 0 D' := funext fun φ => propext (hiff φ)
  classical
  have key : ∀ P Q : (↥(G.Ω 1) × Fin N → ℂ) → Prop, P = Q →
      (if H : ∃! φ, P φ then H.exists.choose else (0 : ↥(G.Ω 1) × Fin N → ℂ)) =
        if H : ∃! φ, Q φ then H.exists.choose else 0 := by
    rintro P Q rfl; rfl
  exact key _ _ e

variable (G a) in
/-- The residual `r = ψ - Q_k φ_k(ψ)` of Definition III.6.1 for a real block field `ψ`. -/
noncomputable def resField (ψ : BlockField d L N₀ k N) (z : Torus d (N₀ * L ^ (k - k))) (i : Fin N) : ℂ :=
  (ψ z i : ℂ) - kAvg (fun y j => svec G (bgField G a 0 (dataR G ψ)) y j) z i

theorem rBlk_eq_resField (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (ψ : BlockField d L N₀ k N) (hψ : ∀ z i, ψ0 ⟨k, z⟩ i = ψ z i) (hR : (dataR G ψ).IsReal)
    (z : Torus d (N₀ * L ^ (k - k))) (i : Fin N) :
    rBlk G a ψ0 h z i = resField G a ψ z i := by
  unfold rBlk resField phiZero
  rw [bgField_congr_Ψ (psiZeroData_isReal ψ0 h) hR (psiZeroData_Ψ_eq_dataR ψ0 h ψ hψ), hψ z i]

theorem sub_blockAvg_eq_resField (ψ : BlockField d L N₀ k N) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (hp : G.layerIndex x = k) (i : Fin N) :
    (dataR G ψ).Ψ x i - blockAvg G (bgField G a 0 (dataR G ψ)) x i =
      resField G a ψ (jBlock d L N₀ k k x) i := by
  have hd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
  unfold resField kAvg blockAvg
  rw [dataR_Ψ G ψ hd i, hp, blk_eq_fib]
  unfold blockVol liftR
  push_cast
  rfl

theorem resField_im (ψ : BlockField d L N₀ k N)
    (hφ : ∀ p, (bgField G a 0 (dataR G ψ) p).im = 0) (z : Torus d (N₀ * L ^ (k - k))) (i : Fin N) :
    (resField G a ψ z i).im = 0 := by
  have hs : ∀ y j, (svec G (bgField G a 0 (dataR G ψ)) y j).im = 0 := by
    intro y j
    by_cases hy : y ∈ G.Ω 1
    · rw [svec_of_mem G _ ⟨y, hy⟩ j]; exact hφ _
    · rw [svec_of_not_mem G _ hy j]; simp
  simp [resField, kAvg, Complex.mul_im, Complex.im_sum, hs]

end Basic

section FirstVar

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}
  {Z : Finset (Torus d (N₀ * L ^ (k - k)))}

/-- **The first variation of the effective action along a perturbation supported over `Z`**: for a block
field `ψ` and `v` supported in `Z` (a set of blocks lying over `Ω_k`), the real part of `firstVar` is
`(a_k / L^{2k}) · L^{kd} · ∑_{z, i} ṽ(z, i) Re r(z, i)`, `r = resField` (`blockVol d L k = L^{kd}`). -/
theorem firstVar_re (hk : 1 ≤ k) (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k)))))
    (v : SuppSpace Z N) (ψ : BlockField d L N₀ k N) :
    (firstVar a (dataR G ψ) (topTangent G v) (bgField G a 0 (dataR G ψ))).re =
      a k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k *
        ∑ z ∈ Z, ∑ i, extSupp Z v z i * (resField G a ψ z i).re := by
  classical
  set H : Torus d (N₀ * L ^ (k - k)) → ℝ := fun z =>
    a k / ((L : ℝ) ^ k) ^ 2 * ∑ i, extSupp Z v z i * (resField G a ψ z i).re with hH
  have hterm : ∀ x : Torus d (N₀ * L ^ k), x ∈ G.Ω 1 →
      (((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
        ∑ i, (topTangent G v).Ψ x i *
          ((dataR G ψ).Ψ x i - blockAvg G (bgField G a 0 (dataR G ψ)) x i)).re =
        if jBlock d L N₀ k k x ∈ Z then H (jBlock d L N₀ k k x) else 0 := by
    intro x hx
    have hds : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    by_cases hz : jBlock d L N₀ k k x ∈ Z
    · obtain ⟨-, hlay, -⟩ := (topLift_block_count hΩ hk hz).2 x rfl
      have e1 : ∀ i, (topTangent G v).Ψ x i *
          ((dataR G ψ).Ψ x i - blockAvg G (bgField G a 0 (dataR G ψ)) x i) =
          ((extSupp Z v (jBlock d L N₀ k k x) i : ℝ) : ℂ) *
            resField G a ψ (jBlock d L N₀ k k x) i := fun i => by
        rw [topTangent_Ψ v hds i, sub_blockAvg_eq_resField ψ hx hlay i]
      simp only [e1]
      rw [hlay]
      simp only [hz, ↓reduceIte]
      rw [Complex.re_ofReal_mul, Complex.re_sum]
      simp only [Complex.re_ofReal_mul]
      rfl
    · have e0 : ∀ i, (topTangent G v).Ψ x i = 0 := fun i => by
        rw [topTangent_Ψ v hds i]; simp [extSupp, hz]
      simp [e0, hz]
  have hsub : ∀ x : Torus d (N₀ * L ^ k), x ∉ G.Ω 1 →
      (if jBlock d L N₀ k k x ∈ Z then H (jBlock d L N₀ k k x) else 0) = 0 := by
    intro x hx
    by_cases hz : jBlock d L N₀ k k x ∈ Z
    · exact absurd (G.Ω_antitone le_rfl hk (by omega) (hΩ x hz)) hx
    · simp [hz]
  unfold firstVar
  rw [Complex.re_sum]
  calc _ = ∑ x : G.Ω 1, (if jBlock d L N₀ k k (x : Torus d (N₀ * L ^ k)) ∈ Z then
          H (jBlock d L N₀ k k (x : Torus d (N₀ * L ^ k))) else 0) :=
        Finset.sum_congr rfl fun x _ => hterm x x.2
    _ = ∑ x ∈ G.Ω 1, (if jBlock d L N₀ k k x ∈ Z then H (jBlock d L N₀ k k x) else 0) :=
        Finset.sum_coe_sort (G.Ω 1) (fun x => if jBlock d L N₀ k k x ∈ Z then
          H (jBlock d L N₀ k k x) else 0)
    _ = ∑ x : Torus d (N₀ * L ^ k), (if jBlock d L N₀ k k x ∈ Z then H (jBlock d L N₀ k k x) else 0) :=
        Finset.sum_subset (Finset.subset_univ _) fun x _ hx => hsub x hx
    _ = ((L : ℝ) ^ k) ^ d * ∑ z ∈ Z, H z := sum_fiber_top hk hΩ H
    _ = _ := by
        simp only [hH, ← Finset.mul_sum]
        unfold blockVol
        ring

/-- **T1 (`firstVar_basis`)**: the first variation in the direction of the basis perturbation at
`(z₀, i₀)`, `z₀ ∈ Z`, is `(a_k / L^{2k}) · L^{kd} · Re r(z₀, i₀)` (the constant is
`a k / (L ^ k) ^ 2 * blockVol d L k`, `blockVol d L k = (L ^ k) ^ d`; the effective action here is the
unnormalized `effAction`, so no further factor enters). -/
theorem firstVar_basis (hk : 1 ≤ k) (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k)))))
    (ψ : BlockField d L N₀ k N) {z0 : Torus d (N₀ * L ^ (k - k))} (hz0 : z0 ∈ Z) (i0 : Fin N) :
    (firstVar a (dataR G ψ)
        (topTangent G (EuclideanSpace.single (⟨z0, hz0⟩, i0) (1 : ℝ) : SuppSpace Z N))
        (bgField G a 0 (dataR G ψ))).re =
      a k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k * (resField G a ψ z0 i0).re := by
  classical
  rw [firstVar_re hk hΩ]
  congr 1
  have hext : ∀ z i, extSupp Z (EuclideanSpace.single (⟨z0, hz0⟩, i0) (1 : ℝ) : SuppSpace Z N) z i =
      if z = z0 ∧ i = i0 then 1 else 0 := by
    intro z i
    by_cases hz : z ∈ Z
    · simp [extSupp, hz, Prod.ext_iff, Subtype.ext_iff]
    · have hn : ¬ (z = z0 ∧ i = i0) := fun h => hz (h.1 ▸ hz0)
      simp [extSupp, hz, hn]
  simp only [hext]
  simp [ite_and, hz0]

end FirstVar

section Stationary

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] [NeZero N] {ϱ' : ℝ} (G' : GeneratingSet d L N₀ k ϱ')
  (a : ℕ → ℝ)

variable {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G' (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G', jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ' a 0)

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **P7 (2.52), stationarity of `ψ⁰_k` (Lemma III.3.3 and the first step of Lemma III.6.3)**: the residual
`r = ψ⁰_k - Q_k φ⁰_k` of Definition III.6.1 vanishes on every block of `Z₀ = box b₀ w`.

Massless reference (`BgHyp … 0`).  `ψ0` is the block field `ψ̃⁰_k` of Lemma III.3.3 (`psiZero`, hypothesis `hψ0`),
`h` the constant of the datum `psiZeroData` (it drops out at mass `0`, `bgField_congr_Ψ`).  The smallness is the
one of `effAction_squeeze`, `K₆ δ < etaDen`.  Proof: `effAction_squeeze` (vanishing derivative of the effective
action at the interior minimizer `ψ⁰_k`), `psiZero_derivs_core` (the derivative is `Re firstVar`),
`firstVar_basis` (it is `(a_k / L^{2k}) L^{kd} Re r(z₀, i₀)`) and the realness of the background
(`bgField_im`), so `Im r = 0`. -/
theorem rBlk_psiZero_eq_zero {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψin : BlockField d L N₀ k N}
    (hψin : TubeOn G' (X \ box b0 w) δ ψin)
    (hKδ : psiZeroK N G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ < etaDen d L N D)
    (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (hψ0 : ∀ z i, ψ0 ⟨k, z⟩ i = psiZero N G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψin z i)
    {z : Torus d (N₀ * L ^ (k - k))} (hz : z ∈ box b0 w) (i : Fin N) :
    rBlk G' a ψ0 h z i = 0 := by
  set ψ := psiZero N G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψin with hψdef
  set K := psiZeroK N G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H with hK
  set Zb := boxFinset (L := L) (N₀ := N₀) (k := k) b0 w with hZb
  have hKpos : 0 < K := psiZeroK_pos N G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H
  obtain ⟨hsol, -⟩ := psiZero_spec N G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψin
  have ht : TubeOn G' Set.univ (K * δ) ψ := tubeOn_univ_of_data G' hdata hsol.1
  have hKδ0 : 0 < K * δ := mul_pos hKpos hδ
  have hd0 : 0 < d := by omega
  have hη1 : K * δ ≤ bgC1 d L N := hKδ.le.trans (min_le_left _ _)
  have hηh : K * δ ≤ etaHess d L N D := hKδ.le.trans (min_le_right _ _)
  have hη0 : K * δ ≤ bgC0 d L N := hη1.trans (bgC1_le_bgC0 d L N hd0)
  obtain ⟨hcrit, -, -⟩ := effAction_squeeze G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψin
    (ρ := (etaDen d L N D - K * δ) / 5) (by linarith) (by linarith)
  have hmerge : mergeField Zb ψin (restrictSupp Zb ψ) = ψ :=
    mergeField_restrict (fun z hz => hsol.2.1 z (fun h => hz (mem_boxFinset.2 h)))
  have heff : effOn G' a Zb ψ = effOn G' a Zb ψin := by
    have := effOn_merge G' a Zb ψin (restrictSupp Zb ψ)
    rwa [hmerge] at this
  have hΩZ : OverTop G' (Zb : Set (Torus d (N₀ * L ^ (k - k)))) := fun x hx =>
    hΩ x (Or.inl (mem_boxFinset.1 (Finset.mem_coe.1 hx)))
  have hz' : z ∈ Zb := mem_boxFinset.2 hz
  have hd1 := (psiZero_derivs_core H hk b0 w Zb (coe_boxFinset b0 w) hw1 hwD hm hΩ hKδ0 hη0 hη1 hηh ht
    (EuclideanSpace.single (⟨z, hz'⟩, i) (1 : ℝ))).1
  have h0 : (firstVar a (dataR G' ψ)
      (topTangent G' (EuclideanSpace.single (⟨z, hz'⟩, i) (1 : ℝ) : SuppSpace Zb N))
      (bgField G' a 0 (dataR G' ψ))).re = 0 := by
    rw [← hd1, heff, hcrit]; simp
  rw [firstVar_basis hk hΩZ ψ hz' i] at h0
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have hak : 0 < a k := lt_of_lt_of_le (by norm_num) (H.weights k hk le_rfl).1
  have hc : a k / ((L : ℝ) ^ k) ^ 2 * blockVol d L k ≠ 0 := by
    unfold blockVol; positivity
  have hre : (resField G' a ψ z i).re = 0 := by
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 hc
    · exact h1
  have him := resField_im ψ (bgField_im G' H hKδ0 hη1 ht) z i
  have hR : (dataR G' ψ).IsReal := isReal_of_inDomainR (inDomainR_of_tube G' hKδ0 ht)
  rw [rBlk_eq_resField ψ0 h ψ hψ0 hR z i]
  exact Complex.ext hre him

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **P7 (2.52), site form**: `resZero = 0` at every site of `Ω₁(𝔹_k(U_k))` lying over a block of `Z₀` (such
a site is in `Ω_k`, of layer `k`, by the geometry `OverTop`). -/
theorem resZero_psiZero_eq_zero {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψin : BlockField d L N₀ k N}
    (hψin : TubeOn G' (X \ box b0 w) δ ψin)
    (hKδ : psiZeroK N G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ < etaDen d L N D)
    (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (hψ0 : ∀ z i, ψ0 ⟨k, z⟩ i = psiZero N G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψin z i)
    {x : Torus d (N₀ * L ^ k)} (hx : jBlock d L N₀ k k x ∈ box b0 w) (i : Fin N) :
    resZero G' a ψ0 h x i = 0 := by
  have hxk : x ∈ G'.Ω k := hΩ x (Or.inl hx)
  have hx1 : x ∈ G'.Ω 1 := G'.Ω_antitone le_rfl hk (by omega) hxk
  have hlay : G'.layerIndex x = k :=
    G'.layerIndex_eq hk le_rfl (G'.mem_layer.2 ⟨hxk, by rw [G'.top]; simp⟩)
  rw [resZero_eq_rBlk a ψ0 h hx1 hlay i]
  exact rBlk_psiZero_eq_zero G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψin hKδ ψ0 h hψ0 hx i


include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **P7 (2.52)**: `ψ⁰_{k₁,k} = Q(𝔹_{k₁,k}) φ⁰_k` at every site of `Ω₁(𝔹_{k₁,k})` lying over a block of
`Z₀ = box b₀ w` (LF-RECONSTRUCTION Lemma III.6.3, first step; `psiZeroWin_sub_blockAvg_eq_zero` and the
stationarity `resZero_psiZero_eq_zero`). -/
theorem psiZeroWin_eq_blockAvg_on_Z0 {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} (hprec : Precedes G G')
    {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψin : BlockField d L N₀ k N}
    (hψin : TubeOn G' (X \ box b0 w) δ ψin)
    (hKδ : psiZeroK N G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ < etaDen d L N D)
    (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (hψ0 : ∀ z i, ψ0 ⟨k, z⟩ i = psiZero N G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψin z i)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hxZ : jBlock d L N₀ k k x ∈ box b0 w) (i : Fin N) :
    psiZeroWin G G' a ψ0 h x i = blockAvg G (hprec.restrictφ (phiZero G' a ψ0 h)) x i := by
  have := psiZeroWin_sub_blockAvg_eq_zero hprec a ψ0 h hx
    (fun j => resZero_psiZero_eq_zero G' a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψin hKδ ψ0 h
      hψ0 hxZ j) i
  exact sub_eq_zero.1 this


end Stationary


section Cancellation

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] [NeZero N] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- **Lemma III.6.3 (the fundamental formula; LFR (2.58′); P7 (2.53)-(2.58)), unconditional, real data.**
The identity of `cancellation_identity_of_stationary` with the stationarity premises `hD0r`, `hZk1r` and the
domain premise `hDom` discharged: `hD0r` and `hZk1r` both follow from the stationarity (2.52) of the reference
minimizer `ψ⁰_k` (`rBlk_psiZero_eq_zero`), given that the sites of `D₀` and of `Z_{k₁}` lie over blocks of
`Z₀` (`hD0Z`, `hZk1Z`); `hDom` follows from the tube.  The reference `ψ̃⁰_k = ψ⁰_k` (`hψ0`) is real and the
mass is `0` (the massless reference of P7); this is a statement for real `ψ⁰_k`, not for complex data. -/
theorem cancellation_identity {D' : ℕ} {a₁ : ℝ} (hd : 2 ≤ d) (hk : 1 ≤ k) (ha₁ : 0 < a₁) {β0 ν : ℝ}
    (hβ0 : 0 < β0)
    (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
    (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D') (hm : D' + 2 ≤ N₀ * L ^ (k - k))
    {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G' (box b0 w ∪ shellOut (box b0 w)))
    (hdata : ∀ x ∈ dataSites G', jBlock d L N₀ k k x ∈ X) (H' : BgHyp d L k ϱ' (compWeight L a₁) 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G' (compWeight L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata H')
    {ψin : BlockField d L N₀ k N} (hψin : TubeOn G' (X \ box b0 w) δ ψin)
    (hKδ : psiZeroK N G' (compWeight L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata H' * δ < etaDen d L N D')
    (hprec : Precedes G G') (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (hψ0 : ∀ z i, ψ0 ⟨k, z⟩ i =
      psiZero N G' (compWeight L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata H' hδ hδc hψin z i)
    (Du : BgData G N) {φu : G.Ω 1 × Fin N → ℂ} {αu : G.Ω 1 → ℂ}
    (hDuh : ∀ x i, Du.h x i = (windowData G G' hprec (compWeight L a₁) ψ0 h).h x i)
    (hELu : IsEL G (compWeight L a₁) 0 Du φu αu)
    (D : Region G) (Zr Zk1 : Region G') (D0 Dω : Finset (Torus d (N₀ * L ^ k)))
    (Zb : Finset (Torus d (N₀ * L ^ (k - k))))
    (hD : D.sites = D0 ∪ Dω ∪ Zb.biUnion (fib d L N₀ k k)) (hD0ω : Disjoint D0 Dω)
    (hDr : Disjoint (D0 ∪ Dω) (Zb.biUnion (fib d L N₀ k k)))
    (hZr : Zr.sites = D.sites ∪ Zk1.sites) (hZd : Disjoint D.sites Zk1.sites)
    (hlay' : ∀ x ∈ Zr.sites, G'.layerIndex x = k)
    (hD0Z : ∀ x ∈ D0, jBlock d L N₀ k k x ∈ box b0 w)
    (hZk1Z : ∀ x ∈ Zk1.sites, jBlock d L N₀ k k x ∈ box b0 w)
    (hDω : ∀ x ∈ Dω, G.layerIndex x = k ∧
      ∀ i, dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du x i = 0)
    (hZb : ∀ z ∈ Zb, ∀ x ∈ fib d L N₀ k k z, 1 ≤ G.layerIndex x ∧ G.layerIndex x < k)
    (ψk : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ)
    (hψk : ∀ z ∈ Zb, ∀ i, ψk z i = ((ψ0 ⟨k, z⟩ i : ℝ) : ℂ))
    (ϖ : ℕ → ℝ) (aN : Torus d (N₀ * L ^ (k - k)) → ℝ) (haN : ∀ z ∈ Zb, 0 < aN z) :
    gaussNat G ϖ Du.Ψ (betaK d L k β0) aN ψk Zb + (β0 : ℂ) * actionRegionC D (compWeight L a₁) ν Du φu -
        ((Real.log (constNat N (betaK d L k β0) aN Zb) : ℝ) : ℂ) =
      (β0 : ℂ) * actionRegionC Zr (compWeight L a₁) ν (psiZeroData G' ψ0 h) (phiZero G' (compWeight L a₁) ψ0 h) -
        (β0 : ℂ) * actionRegion0 Zk1 ν (psiZeroData G' ψ0 h) (phiZero G' (compWeight L a₁) ψ0 h) +
        ((betaK d L k β0 : ℝ) * ∑ z ∈ Zb, (1 / 2 : ℂ) * (aN z : ℂ) *
            dotC (kAvg (dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du) z)
              (kAvg (dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du) z) +
          (β0 : ℂ) * (deltaActionC D (compWeight L a₁) ν (windowData G G' hprec (compWeight L a₁) ψ0 h) Du
              (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu
              (hprec.restrictα (alphaZero G' (compWeight L a₁) ψ0 h)) +
            nuTerm D ν (windowData G G' hprec (compWeight L a₁) ψ0 h)
              (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu)) +
        (β0 : ℂ) * stTerm D (windowData G G' hprec (compWeight L a₁) ψ0 h) Du
          (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu -
        ((Real.log (constNat N (betaK d L k β0) (compWeightZ G a₁) Zb) : ℝ) : ℂ) +
        Cnat a₁ hprec ψ0 h Du Zb β0 ϖ aN ψk := by
  have hL : 2 ≤ L := by have := H'.hL; omega
  set ψ := psiZero N G' (compWeight L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata H' hδ hδc hψin with hψdef
  set K := psiZeroK N G' (compWeight L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata H' with hK
  have hKpos : 0 < K := psiZeroK_pos N G' (compWeight L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata H'
  obtain ⟨hsol, -⟩ := psiZero_spec N G' (compWeight L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata H' hδ hδc hψin
  have ht : TubeOn G' Set.univ (K * δ) ψ := tubeOn_univ_of_data G' hdata hsol.1
  have hKδ0 : 0 < K * δ := mul_pos hKpos hδ
  have hη1 : K * δ ≤ bgC1 d L N := hKδ.le.trans (min_le_left _ _)
  have hP := (tubeOn_univ_iff G' hKδ0 ψ).1 ht
  have hP' : InPsiTilde G' 0 (K * δ) (liftR ψ) h :=
    ⟨hP.layerConst, hP.r1, hP.r2, fun x _ => by simpa using pow_pos hKδ0 2, by simpa using pow_pos hKδ0 2⟩
  have hDom : InUnionDomainR G' (bgC1 d L N) 0 (psiZeroData G' ψ0 h) :=
    ⟨K * δ, hKδ0, hη1, liftR ψ, h, hP',
      fun x hx i => by
        rw [congrFun (congrFun (psiZeroData_Ψ_eq_dataR ψ0 h ψ (fun z i => (hψ0 z i))) x) i]
        exact dataR_Ψ G' ψ hx i,
      fun x hx i => by
        simp [psiZeroData, liftSingle_h G' _ _ hx]⟩
  refine cancellation_identity_of_stationary hprec ψ0 h hd hL hk ha₁ hβ0 H' hDom Du hDuh hELu D Zr Zk1 D0 Dω Zb hD
    hD0ω hDr hZr hZd hlay' ?_ ?_ hDω hZb ψk hψk ϖ aN haN
  · intro x hx i
    exact rBlk_psiZero_eq_zero G' (compWeight L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata H' hδ hδc hψin
      hKδ ψ0 h hψ0 (hD0Z x hx) i
  · intro x hx i
    exact rBlk_psiZero_eq_zero G' (compWeight L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata H' hδ hδc hψin
      hKδ ψ0 h hψ0 (hZk1Z x hx) i

end Cancellation

end Balaban.LargeField.ActionConv
