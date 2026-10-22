/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxCloseCoef
public import Balaban.Green.FinalBoxLocCut
public import Balaban.Green.FinalTaggedWeightedGfin
public import Balaban.Green.FinalTorusCloseUnif
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cut family of the final Hessian on two tori (A6-3 (d), box localization)

Two tori `N ≤ N'`-agnostic (`2 (J + 6) M ≤ N, N'`), the residue lift `f : 𝕋_N → 𝕋_{N'}` and a cell
map `e` that is the identity on the cells of coordinates at most `J + 4` (the window frame of
`final_region_entry_close_unif`). For a family `C` of cells in the window `[4, J]`:

* `chiSum_transport`: the parameter-weighted partition of unity is carried exactly,
  `m(s)(x) = m'(s')(f x)` on the region of `C`, at corresponding parameters;
* `boxCut_close_twoTorus`: the entries of the cut family `boxCut` at corresponding parameters and
  sites of the region differ by at most `P (n_C² + n_C⁴) √ε / √g · (1 + p)`, `ε` the difference of the
  final operators on the region, `g` the final gap, `p` a bound for the entries of the spin projection;
  `P` depends on `d, L, M, κ` only (`final_taggedCfinU_close_weighted`);
* `boxCut_close_twoTorus_margin`: with the uniform closeness of the final operators
  (`final_region_entry_close_unif`), `ε = C₀ e^{-c₀ (min(N, N')/2 - (J + 3) M)}`, so `√ε` decays at the
  rate `c₀/2` per site of margin, i.e. `c₀ M / 2` per macro cell, `c₀ = c₀(d, L)`;
* `spinBoxPatch_image`, `injOn_spinMap`: the regions of `C` and `e C` correspond under `f`.
-/

@[expose] public section

namespace Balaban.Green

open Finset Balaban.Localization Balaban.Analysis Balaban.Polymer

section TwoTorus

variable {d M J N N' L : ℕ} [NeZero N] [NeZero N'] [NeZero L]

omit [NeZero N] [NeZero N'] in
/-- The cell map is injective on the cells of the window. -/
theorem injOn_cellMap_window {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) :
    Set.InjOn e (C : Set (MacIdx d N M)) := by
  intro a ha b hb hab
  funext i
  apply Fin.ext
  have h1 := he a i (by have := (hC a ha i).2; omega)
  have h2 := he b i (by have := (hC b hb i).2; omega)
  have h3 : ((e a i : Fin (macK N' M)) : ℕ) = ((e b i : Fin (macK N' M)) : ℕ) := by rw [hab]
  omega

/-- **The partition of unity at corresponding parameters is carried exactly** on the region. -/
theorem chiSum_transport (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N) (hN' : 2 * (J + 6) * M ≤ N')
    {f : L1Torus d N → L1Torus d N'} (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    {s : MacIdx d N M → ℂ} (hs : s ∈ supportedOn C) {s' : MacIdx d N' M → ℂ}
    (hs' : s' ∈ supportedOn (C.image e)) (hss : ∀ i ∈ C, s' (e i) = s i)
    {x : L1Torus d N} (hx : x ∈ macRegion d N M C) :
    chiSum d N M s x = chiSum d N' M s' (f x) := by
  classical
  have hxm := mid_of_mem_macRegion hM hN hC hx
  unfold chiSum
  rw [← Finset.sum_subset (Finset.subset_univ C) fun z _ hz => by rw [hs z hz, zero_mul],
    ← Finset.sum_subset (Finset.subset_univ (C.image e)) fun z _ hz => by rw [hs' z hz, zero_mul],
    Finset.sum_image (injOn_cellMap_window he hC)]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [hss z hz, macChi_transport hM hN hN' hf hxm he fun i => by
    have := (hC z hz i).2; omega]

/-- The sites of the spin fields over a map of the lattice sites. -/
def spinMap {Nf : ℕ} (f : L1Torus d N → L1Torus d N') :
    L1Torus d N × Fin Nf → L1Torus d N' × Fin Nf := fun p => (f p.1, p.2)

/-- **The regions of `C` and `e C` correspond** under the spin map of the residue lift. -/
theorem spinBoxPatch_image {Nf : ℕ} (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) :
    patchReg (spinBoxPatch d N' M Nf) (C.image e) =
        spinMap (Nf := Nf) f '' patchReg (spinBoxPatch d N M Nf) C ∧
      Set.InjOn (spinMap (Nf := Nf) f) (patchReg (spinBoxPatch d N M Nf) C) := by
  obtain ⟨g, hg⟩ : ∃ g : L1Torus d N' → L1Torus d N, ∀ y μ, g y μ = (((y μ).val : ℕ) : ZMod N) :=
    ⟨fun y μ => (((y μ).val : ℕ) : ZMod N), fun _ _ => rfl⟩
  have hbij := macRegion_bijOn hM hN hN' hf hg he hC
  refine ⟨?_, ?_⟩
  · ext ⟨y, i⟩
    rw [mem_patchReg_spinBoxPatch]
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := hbij.surjOn hy
      exact ⟨(x, i), mem_patchReg_spinBoxPatch.2 hx, by simp [spinMap, hxy]⟩
    · rintro ⟨⟨x, j⟩, hx, hxy⟩
      simp only [spinMap, Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      exact hbij.mapsTo (mem_patchReg_spinBoxPatch.1 hx)
  · rintro ⟨x, i⟩ hx ⟨y, j⟩ hy hxy
    simp only [spinMap, Prod.mk.injEq] at hxy
    have hxy' : x = y :=
      hbij.injOn (mem_patchReg_spinBoxPatch.1 hx) (mem_patchReg_spinBoxPatch.1 hy) hxy.1
    rw [hxy', hxy.2]

/-- **The cut family of the final Hessian on two tori, window frame.** There is `P ≥ 0`, depending on
`d, L, M, κ` only, such that for a family `C` of at most `n_C` cells in the window `[4, J]`, at
corresponding parameters of modulus at most `e^κ` and sites of the region, the entries of the two cut
families differ by at most `P (n_C² + n_C⁴) √ε / √g · (1 + p)`, `ε` the difference of the final operators
on the region. -/
theorem boxCut_close_twoTorus (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (nC : ℕ) {k J N N' : ℕ} [NeZero N] [NeZero N'], 1 ≤ k →
      2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' → ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {ε : ℝ}, (∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
        ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤ ε) →
      ∀ {Nf : ℕ} {h : Fin Nf → ℂ} {p : ℝ}, (∀ i j, ‖spinProj h i j‖ ≤ p) →
      ∀ {s : MacIdx d N M → ℂ}, s ∈ supportedOn C →
      ∀ {s' : MacIdx d N' M → ℂ}, s' ∈ supportedOn (C.image e) →
      (∀ i ∈ C, s' (e i) = s i) → (∀ q, ‖s q‖ ≤ Real.exp κ) →
      ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, ∀ i j : Fin Nf,
      ‖boxCut d L N k M v a h s (x, i) (y, j) - boxCut d L N' k M v a h s' (f x, i) (f y, j)‖ ≤
        P * ((nC : ℝ) ^ 2 + (nC : ℝ) ^ 4) * Real.sqrt ε / Real.sqrt (finalGap d L) * (1 + p) := by
  obtain ⟨P, hP0, hP⟩ := final_taggedCfinU_close_weighted (L := L) hd hM hκ hMB hMκ
  refine ⟨P, hP0, ?_⟩
  intro nC k J N N' _ _ hk hN hN' f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass ε hU Nf h p hp s hs
    s' hs' hss hsκ x hx y hy i j
  have hT := hP nC hk hN hN' hf he hCc hC hv0 hv1 ha1 ha2 hmass hU hs hs' hss hsκ hx hy
  rw [taggedCfinU_finalOp, taggedCfinU_finalOp] at hT
  rw [boxCut_apply, boxCut_apply, chiSum_transport hM hN hN' hf he hC hs hs' hss hx]
  have hfx : (x = y) ↔ (f x = f y) := by
    obtain ⟨g, hg⟩ : ∃ g : L1Torus d N' → L1Torus d N, ∀ y μ, g y μ = (((y μ).val : ℕ) : ZMod N) :=
      ⟨fun y μ => (((y μ).val : ℕ) : ZMod N), fun _ _ => rfl⟩
    have hbij := macRegion_bijOn hM hN hN' hf hg he hC
    exact ⟨fun h => h ▸ rfl, fun h => hbij.injOn hx hy h⟩
  have e1 : ((1 / Real.sqrt a : ℝ) : ℂ) * ((if x = y then chiSum d N' M s' (f x) else 0) *
        spinProj h i j) =
      ((1 / Real.sqrt a : ℝ) : ℂ) * ((if f x = f y then chiSum d N' M s' (f x) else 0) *
        spinProj h i j) := by
    by_cases hxy : x = y
    · subst hxy; simp
    · have hfxy : f x ≠ f y := fun h => hxy (hfx.2 h)
      simp [hxy, hfxy]
  rw [e1, add_sub_add_left_eq_sub, ← sub_mul, norm_mul]
  have hsp : ‖((if i = j then 1 else 0 : ℂ) - spinProj h i j)‖ ≤ 1 + p := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ (hp i j))
    by_cases hij : i = j <;> simp [hij]
  exact mul_le_mul hT hsp (norm_nonneg _) (by positivity)

/-- **The cut family of the final Hessian on two tori, margin form** (window frame). There are `P ≥ 0`
and `C₀, c₀ > 0`, depending on `d, L, M, κ` (`c₀` on `d, L` only), such that the entries of the two cut
families at corresponding parameters and sites of the region of a family of at most `n_C` cells in the
window `[4, J]` differ by at most
`P (n_C² + n_C⁴) √(C₀ e^{-c₀ (min(N, N')/2 - (J + 3) M)}) / √g · (1 + p)`. -/
theorem boxCut_close_twoTorus_margin (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) :
    ∃ P C₀ c₀ : ℝ, 0 ≤ P ∧ 0 < C₀ ∧ 0 < c₀ ∧ ∀ (nC : ℕ) {k J N N' : ℕ} [NeZero N] [NeZero N'],
      1 ≤ k → 2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' → ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {Nf : ℕ} {h : Fin Nf → ℂ} {p : ℝ}, (∀ i j, ‖spinProj h i j‖ ≤ p) →
      ∀ {s : MacIdx d N M → ℂ}, s ∈ supportedOn C →
      ∀ {s' : MacIdx d N' M → ℂ}, s' ∈ supportedOn (C.image e) →
      (∀ i ∈ C, s' (e i) = s i) → (∀ q, ‖s q‖ ≤ Real.exp κ) →
      ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, ∀ i j : Fin Nf,
      ‖boxCut d L N k M v a h s (x, i) (y, j) - boxCut d L N' k M v a h s' (f x, i) (f y, j)‖ ≤
        P * ((nC : ℝ) ^ 2 + (nC : ℝ) ^ 4) *
          Real.sqrt (C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ)))) /
          Real.sqrt (finalGap d L) * (1 + p) := by
  obtain ⟨P, hP0, hP⟩ := boxCut_close_twoTorus (L := L) hd hM hκ hMB hMκ
  obtain ⟨C₀, c₀, hC₀, hc₀, hent⟩ := final_region_entry_close_unif (d := d) (L := L) hd
  refine ⟨P, C₀, c₀, hP0, hC₀, hc₀, ?_⟩
  intro nC k J N N' _ _ hk hN hN' f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass Nf h p hp s hs
    s' hs' hss hsκ x hx y hy i j
  exact hP nC hk hN hN' hf he hCc hC hv0 hv1 ha1 ha2 hmass
    (hent hk hv0 hv1 ha1 ha2 hmass hM hN hN' hf hC) hp hs hs' hss hsκ x hx y hy i j

end TwoTorus

end Balaban.Green
