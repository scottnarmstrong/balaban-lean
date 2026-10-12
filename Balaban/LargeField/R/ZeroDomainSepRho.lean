/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ZeroDomainSep
public import Balaban.LargeField.R.RopConcrete
import Mathlib.Tactic.Linarith

/-!
# Independence of the denominators for the components of a history (Lemma III.8.4)

`RopConcrete` takes the geometric premise `hsep` as a hypothesis.  Here the family of ripe components of a history
`H` at scale `k`, with `X c = ripeX H (Zc c)` (the `k`-blocks of the fine set of `U_k^∼`) and `Z₀(Zc c) = box (b0 c)
(w c)`, has `hXreg` (`ripeX_hXreg`, from Lemma III.3.2 (d)) and `hsep` (`zeroDomain_hsep`) proved, and
`rhoZero_indep_other_components`, `integral_rhoZero_indep_other_components` are instantiated.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Balaban Balaban.Multiscale Balaban.Background MeasureTheory

namespace Balaban.LargeField

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ}

include H in
/-- `Z_k` lies in `U_k^∼`: every fine site of `Z_k` has its `π_k`-cube in `bdryUnb`. -/
theorem locFine_cube_mem_bdryUnb (hkK : k ≤ K) (Z : H.Comp k) {x : Torus S.d (S.M * n k * S.L ^ k)}
    (hx : x ∈ H.locFine Z S.M k) : cubeMap n S.L S.M k k x ∈ bdryUnb H Z := by
  have h := (H.mem_locFine_k hkK).1 hx
  exact subset_nbhd 1 _ (subset_nbhd (⌊R (k - 1)⌋₊ + 1) _ h)

include H in
/-- `hXreg`: `Z₀ ∪ shellOut Z₀ ⊆ X(Z)` (Lemma III.3.2 (d)). -/
theorem ripeX_hXreg (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) (hkK : k ≤ K) (hk : 1 ≤ k) (Z : H.Comp k)
    {b0 : Torus S.d (S.M * n k * S.L ^ (k - k))} {w : Fin S.d → ℕ}
    (hbx : ∀ x : Torus S.d (S.M * n k * S.L ^ k), (jBlock S.d S.L (S.M * n k) k k x ∈ box b0 w ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z)) :
    box b0 w ∪ shellOut (box b0 w) ⊆ H.ripeX Z := by
  intro y hy
  obtain ⟨x0, hx0⟩ := Balaban.exists_blockMap_eq (fine_eq_block S.L (S.M * n k) k)
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) k) y
  have hx0' : jBlock S.d S.L (S.M * n k) k k x0 = y := hx0
  have hl := H.mem_locFine_of_mem_box_shell H.F.ok (H.eight_le_L_mul_lateR k) hR hkK hk Z hbx
    (x := x0) (by rw [hx0']; exact hy)
  refine ⟨x0, ?_, hx0'⟩
  have := H.locFine_cube_mem_bdryUnb hkK Z hl
  exact_mod_cast (mem_fineFin).2 this

end RegionHistory

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ}

include H in
/-- `hdata`: the data sites of a generating set whose sites have `π_k`-cube in `U_k^∼` have their `k`-block in `X`. -/
theorem ripeX_hdata (Z : H.Comp k) {ϱ : ℝ} (G : GeneratingSet S.d S.L (S.M * n k) k ϱ)
    (hdU : ∀ x ∈ dataSites G, cubeMap n S.L S.M k k x ∈ bdryUnb H Z) :
    ∀ x ∈ dataSites G, jBlock S.d S.L (S.M * n k) k k x ∈ H.ripeX Z :=
  fun x hx => ⟨x, by exact_mod_cast (mem_fineFin).2 (hdU x hx), rfl⟩

/-- **Lemma III.8.4 (independence), instantiated for the ripe components of a history.**  `Zc` lists distinct
components of `Z_k`, `Z₀(Zc c) = box (b0 c) (w c)`, `X c = ripeX H (Zc c)`; `hsep` and `hXreg` are proved. -/
theorem rhoZero_indep_other_components_ripe (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) (hkK : k ≤ K)
    (N : ℕ) [NeZero N] {ϱ : ℝ} {ι : Type} [Fintype ι] (Zc : ι → H.Comp k) (hZc : Function.Injective Zc)
    (G : ι → GeneratingSet S.d S.L (S.M * n k) k ϱ) (a : ℕ → ℝ) {D : ℕ} (hd : 2 ≤ S.d) (hk : 1 ≤ k)
    (b0 : ι → Torus S.d (S.M * n k * S.L ^ (k - k))) (w : ι → Fin S.d → ℕ)
    (hw1 : ∀ c i, 1 ≤ w c i) (hwD : ∀ c i, w c i ≤ D) (hm : D + 2 ≤ S.M * n k * S.L ^ (k - k))
    (hbx : ∀ c, ∀ x : Torus S.d (S.M * n k * S.L ^ k),
      (jBlock S.d S.L (S.M * n k) k k x ∈ box (b0 c) (w c) ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k (Zc c)))
    (hΩ : ∀ c, OverTop (G c) (box (b0 c) (w c) ∪ shellOut (box (b0 c) (w c))))
    (hdU : ∀ c, ∀ x ∈ dataSites (G c), cubeMap n S.L S.M k k x ∈ bdryUnb H (Zc c))
    (Hbg : BgHyp S.d S.L k ϱ a 0) (δ : ι → ℝ) (hδ : ∀ c, 0 < δ c)
    (hδc : ∀ c, δ c ≤ psiZeroC11 N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm
      (H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (hΩ c) (H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg)
    (c : ι) {ψ ψ' : BlockField S.d S.L (S.M * n k) k N}
    (hψ : FamTube N G b0 w (fun c => H.ripeX (Zc c)) δ c ψ)
    (hψ' : FamTube N G b0 w (fun c => H.ripeX (Zc c)) δ c ψ')
    (h : ∀ z, (∀ c', c' ≠ c → z ∉ box (b0 c') (w c')) → ψ z = ψ' z) (β p0 : ℝ) :
    rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (hΩ c)
      (H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg (hδ c) (hδc c) hψ' β p0 =
    rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (hΩ c)
      (H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg (hδ c) (hδc c) hψ β p0 :=
  rhoZero_indep_other_components N G a hd hk b0 w hw1 hwD hm (fun c => H.ripeX (Zc c))
    (fun c => H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (H.zeroDomain_hsep hkK hk Zc hZc b0 w hbx) hΩ
    (fun c => H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg δ hδ hδc c hψ hψ' h β p0

/-- **Lemma III.8.4, independence of the denominators**, for the ripe components of a history. -/
theorem integral_rhoZero_indep_other_components_ripe (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) (hkK : k ≤ K)
    (N : ℕ) [NeZero N] {ϱ : ℝ} {ι : Type} [Fintype ι] (Zc : ι → H.Comp k) (hZc : Function.Injective Zc)
    (G : ι → GeneratingSet S.d S.L (S.M * n k) k ϱ) (a : ℕ → ℝ) {D : ℕ} (hd : 2 ≤ S.d) (hk : 1 ≤ k)
    (b0 : ι → Torus S.d (S.M * n k * S.L ^ (k - k))) (w : ι → Fin S.d → ℕ)
    (hw1 : ∀ c i, 1 ≤ w c i) (hwD : ∀ c i, w c i ≤ D) (hm : D + 2 ≤ S.M * n k * S.L ^ (k - k))
    (hbx : ∀ c, ∀ x : Torus S.d (S.M * n k * S.L ^ k),
      (jBlock S.d S.L (S.M * n k) k k x ∈ box (b0 c) (w c) ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k (Zc c)))
    (hΩ : ∀ c, OverTop (G c) (box (b0 c) (w c) ∪ shellOut (box (b0 c) (w c))))
    (hdU : ∀ c, ∀ x ∈ dataSites (G c), cubeMap n S.L S.M k k x ∈ bdryUnb H (Zc c))
    (Hbg : BgHyp S.d S.L k ϱ a 0) (δ : ι → ℝ) (hδ : ∀ c, 0 < δ c)
    (hδc : ∀ c, δ c ≤ psiZeroC11 N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm
      (H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (hΩ c) (H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg)
    (c : ι) {ψ ψ' : BlockField S.d S.L (S.M * n k) k N}
    (hψ : FamTube N G b0 w (fun c => H.ripeX (Zc c)) δ c ψ)
    (hψ' : FamTube N G b0 w (fun c => H.ripeX (Zc c)) δ c ψ')
    (h : ∀ z, (∀ c', c' ≠ c → z ∉ box (b0 c') (w c')) → ψ z = ψ' z) (β p0 : ℝ) :
    ∫ u, rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (hΩ c)
      (H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg (hδ c) (hδc c) hψ' β p0 u =
    ∫ u, rhoZero (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (hΩ c)
      (H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg (hδ c) (hδc c) hψ β p0 u := by
  rw [H.rhoZero_indep_other_components_ripe hR hkK N Zc hZc G a hd hk b0 w hw1 hwD hm hbx hΩ hdU Hbg δ hδ hδc c
    hψ hψ' h β p0]

/-- **Lemma III.8.4 (normalization) for the ripe components of a history**, with `hsep` and `hXreg` discharged; the
joint measurability `hmeas` stays (W208's unconditional `R_normalization` is not on `main`). -/
theorem R_normalization_ripe_of_measurable (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) (hkK : k ≤ K)
    (N : ℕ) [NeZero N] {ϱ : ℝ} {ι : Type} [Fintype ι] (Zc : ι → H.Comp k) (hZc : Function.Injective Zc)
    (G : ι → GeneratingSet S.d S.L (S.M * n k) k ϱ) (a : ℕ → ℝ) {D : ℕ} (hd : 2 ≤ S.d) (hk : 1 ≤ k)
    (b0 : ι → Torus S.d (S.M * n k * S.L ^ (k - k))) (w : ι → Fin S.d → ℕ)
    (hw1 : ∀ c i, 1 ≤ w c i) (hwD : ∀ c i, w c i ≤ D) (hm : D + 2 ≤ S.M * n k * S.L ^ (k - k))
    (hbx : ∀ c, ∀ x : Torus S.d (S.M * n k * S.L ^ k),
      (jBlock S.d S.L (S.M * n k) k k x ∈ box (b0 c) (w c) ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k (Zc c)))
    (hΩ : ∀ c, OverTop (G c) (box (b0 c) (w c) ∪ shellOut (box (b0 c) (w c))))
    (hdU : ∀ c, ∀ x ∈ dataSites (G c), cubeMap n S.L S.M k k x ∈ bdryUnb H (Zc c))
    (Hbg : BgHyp S.d S.L k ϱ a 0) (δ : ι → ℝ) (hδ : ∀ c, 0 < δ c)
    (hδc : ∀ c, δ c ≤ psiZeroC11 N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm
      (H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (hΩ c) (H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg)
    (σ : Finset ι) {β p0 : ℝ} (hβ : 0 < β)
    (hp0 : ∀ c ∈ σ, 1 ≤ cSix S.d D
      (psiZeroK N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (H.ripeX_hXreg hR hkK hk (Zc c) (hbx c))
        (hΩ c) (H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg) * p0)
    (hrad : ∀ c ∈ σ, psiZeroK N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm
        (H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (hΩ c) (H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg * δ c +
      5 * zeroRadius (cSix S.d D
        (psiZeroK N (G c) a hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (H.ripeX_hXreg hR hkK hk (Zc c) (hbx c))
          (hΩ c) (H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg)) β p0 ≤ etaDen S.d S.L N D)
    {ρ : BlockField S.d S.L (S.M * n k) k N → ℝ}
    (hρ : Integrable ρ (volume.restrict (famTubeSet N G b0 w (fun c => H.ripeX (Zc c)) δ)))
    (hmeas : ∀ c : σ, Measurable (fun p : SuppSpace (zb b0 w c.1) N ×
        (ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ) =>
      famRho N G a hd hk b0 w hw1 hwD hm (fun c => H.ripeX (Zc c))
        (fun c => H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (H.zeroDomain_hsep hkK hk Zc hZc b0 w hbx) hΩ
        (fun c => H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg δ hδ hδc σ β p0 c.1 p.2 p.1)) :
    Integrable (Rop (famDecomp N G a hd hk b0 w hw1 hwD hm (fun c => H.ripeX (Zc c))
        (fun c => H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (H.zeroDomain_hsep hkK hk Zc hZc b0 w hbx) hΩ
        (fun c => H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg δ hδ hδc σ β p0) ρ)
        (volume.restrict (famTubeSet N G b0 w (fun c => H.ripeX (Zc c)) δ)) ∧
      ∫ ψ, Rop (famDecomp N G a hd hk b0 w hw1 hwD hm (fun c => H.ripeX (Zc c))
        (fun c => H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (H.zeroDomain_hsep hkK hk Zc hZc b0 w hbx) hΩ
        (fun c => H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg δ hδ hδc σ β p0) ρ ψ
          ∂(volume.restrict (famTubeSet N G b0 w (fun c => H.ripeX (Zc c)) δ)) =
        ∫ ψ, ρ ψ ∂(volume.restrict (famTubeSet N G b0 w (fun c => H.ripeX (Zc c)) δ)) :=
  R_normalization_of_measurable N G a hd hk b0 w hw1 hwD hm (fun c => H.ripeX (Zc c))
    (fun c => H.ripeX_hXreg hR hkK hk (Zc c) (hbx c)) (H.zeroDomain_hsep hkK hk Zc hZc b0 w hbx) hΩ
    (fun c => H.ripeX_hdata (Zc c) (G c) (hdU c)) Hbg δ hδ hδc σ hβ hp0 hrad hρ hmeas

end RegionHistory

end Balaban.LargeField
