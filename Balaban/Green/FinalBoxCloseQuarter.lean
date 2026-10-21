/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxCloseCut
public import Balaban.Polymer.TwoTorusQuarterBox
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cut family of the final Hessian on two tori, quarter-box frame (A6-3 (d))

* `chiSum_translate`, `boxCut_translate`: the cut family is covariant under the translation by `p`
  cells (`taggedCfin_translate`, `macChi_translate`);
* `boxCut_close_quarterBox`: for two tori `N ≤ N'` (multiples of `M`), a family `C` of at most `n_C`
  cells within `m` cells of the origin, `4 (m + t) ≤ K = N / M`, `t ≥ 5`, the lift `f` and the cell map
  `e` of the quarter box (as in `finalCoef_close_quarterBox_weighted`), the entries of the two cut
  families at corresponding parameters and sites of the region differ by at most
  `P (n_C² + n_C⁴) √(C₀ e^{-c₀ M (2t - 7)}) / √g · (1 + p)`: the margin `t` (in cells) enters at the rate
  `c₀ M / 2` per cell (after the square root), `c₀ = c₀(d, L)` the decay constant of the final operators.
-/

@[expose] public section

namespace Balaban.Green

open Finset Balaban.Localization Balaban.Analysis Balaban.Polymer

section Translate

variable {d M N L k : ℕ} [NeZero N] [NeZero L] {p : ℕ} {v a : ℝ}

omit [NeZero L] in
theorem chiSum_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (s : MacIdx d N M → ℂ) (x : L1Torus d N) :
    chiSum d N M s (e x) = chiSum d N M (s ∘ σ) x := by
  unfold chiSum
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [macChi_translate hMN σ hσ e he]
  rfl

/-- **The cut family is covariant under the translation by `p` cells.** -/
theorem boxCut_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    {Nf : ℕ} (h : Fin Nf → ℂ) (s : MacIdx d N M → ℂ) (x y : L1Torus d N) (i j : Fin Nf) :
    boxCut d L N k M v a h s (e x, i) (e y, j) = boxCut d L N k M v a h (s ∘ σ) (x, i) (y, j) := by
  have ht := congrFun (congrFun (taggedCfin_translate (L := L) (k := k) hMN σ hσ e he v a s) x) y
  rw [Matrix.submatrix_apply] at ht
  rw [boxCut_apply, boxCut_apply, chiSum_translate hMN σ hσ e he, ht]
  simp only [e.injective.eq_iff]

end Translate

section Quarter

variable {d M L : ℕ} [NeZero L]

/-- **The cut family of the final Hessian on two tori, quarter-box frame.** -/
theorem boxCut_close_quarterBox (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) :
    ∃ P C₀ c₀ : ℝ, 0 ≤ P ∧ 0 < C₀ ∧ 0 < c₀ ∧ ∀ (nC : ℕ) {k N N' : ℕ} [NeZero N] [NeZero N'],
      1 ≤ k → M ∣ N → M ∣ N' → N ≤ N' → ∀ {m t : ℕ}, 5 ≤ t → 4 * (m + t) ≤ macK N M →
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ + ((M * (m + 4) : ℕ) : ZMod N') =
        ((((x μ + ((M * (m + 4) : ℕ) : ZMod N)).val : ℕ)) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, ((z i : ℕ) + (m + 4)) % macK N M ≤ 2 * m + 8 →
        ((e z i : ℕ) + (m + 4)) % macK N' M = ((z i : ℕ) + (m + 4)) % macK N M) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, (z i : ℕ) ≤ m ∨ macK N M - m ≤ (z i : ℕ)) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {Nf : ℕ} {h : Fin Nf → ℂ} {p : ℝ}, (∀ i j, ‖spinProj h i j‖ ≤ p) →
      ∀ {s : MacIdx d N M → ℂ}, s ∈ supportedOn C →
      ∀ {s' : MacIdx d N' M → ℂ}, s' ∈ supportedOn (C.image e) →
      (∀ i ∈ C, s' (e i) = s i) → (∀ q, ‖s q‖ ≤ Real.exp κ) →
      ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, ∀ i j : Fin Nf,
      ‖boxCut d L N k M v a h s (x, i) (y, j) - boxCut d L N' k M v a h s' (f x, i) (f y, j)‖ ≤
        P * ((nC : ℝ) ^ 2 + (nC : ℝ) ^ 4) *
          Real.sqrt (C₀ * Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7)))) /
          Real.sqrt (finalGap d L) * (1 + p) := by
  classical
  obtain ⟨P, C₀, c₀, hP0, hC₀, hc₀, hmain⟩ := boxCut_close_twoTorus_margin (L := L) hd hM hκ hMB hMκ
  refine ⟨P, C₀, c₀, hP0, hC₀, hc₀, ?_⟩
  intro nC k N N' _ _ hk hMN hMN' hNN' m t ht5 hK f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass Nf
    h p hp s hs s' hs' hss hsκ x hx y hy i j
  set q₀ := m + 4 with hq₀
  obtain ⟨σ, hσ⟩ := exists_cellShift (N := N) (M := M) d q₀
  obtain ⟨σ', hσ'⟩ := exists_cellShift (N := N') (M := M) d q₀
  obtain ⟨eN, heN⟩ := exists_translate (d := d) (fun _ => ((M * q₀ : ℕ) : ZMod N))
  obtain ⟨eN', heN'⟩ := exists_translate (d := d) (fun _ => ((M * q₀ : ℕ) : ZMod N'))
  have hKN : macK N M * M = N := by
    rw [macK_eq_div_of_dvd hMN]; exact Nat.div_mul_cancel hMN
  have hJN : 2 * ((2 * m + 4) + 6) * M ≤ N := by
    rw [← hKN]; nlinarith
  have hJN' : 2 * ((2 * m + 4) + 6) * M ≤ N' := hJN.trans hNN'
  set fw : L1Torus d N → L1Torus d N' := fun x μ => (((x μ).val : ℕ) : ZMod N') with hfw
  set ew : MacIdx d N M → MacIdx d N' M := fun z => σ' (e (σ.symm z)) with hew
  have hewin := cellMap_translate (J := 2 * m + 4) σ σ' hσ hσ' (e := e) (fun z i hz => he z i (by
    omega))
  have hCw : ∀ z ∈ C.map σ.toEmbedding, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ 2 * m + 4 := by
    refine window_translate σ hσ fun z hz i => ?_
    have hzK := (z i).isLt
    rcases hC z hz i with h1 | h1
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · have : (z i : ℕ) + q₀ = ((z i : ℕ) + q₀ - macK N M) + macK N M := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  set sw : MacIdx d N M → ℂ := s ∘ σ.symm with hsw
  set s'w : MacIdx d N' M → ℂ := s' ∘ σ'.symm with hs'w
  have hswS : sw ∈ supportedOn (C.map σ.toEmbedding) := fun z hz => by
    refine hs _ fun hc => hz ?_
    exact Finset.mem_map.2 ⟨σ.symm z, hc, by simp⟩
  have hs'wS : s'w ∈ supportedOn ((C.map σ.toEmbedding).image ew) := fun z hz => by
    rw [image_translate σ σ' e C] at hz
    refine hs' _ fun hc => hz ?_
    exact Finset.mem_map.2 ⟨σ'.symm z, hc, by simp⟩
  have hssw : ∀ z ∈ C.map σ.toEmbedding, s'w (ew z) = sw z := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.1 hz
    simp [hsw, hs'w, hew, hss c hc]
  have hswκ : ∀ q, ‖sw q‖ ≤ Real.exp κ := fun q => hsκ _
  have hxw : eN x ∈ macRegion d N M (C.map σ.toEmbedding) :=
    (mem_macRegion_translate hMN σ hσ eN (fun x _ => heN x _) C x).2 hx
  have hyw : eN y ∈ macRegion d N M (C.map σ.toEmbedding) :=
    (mem_macRegion_translate hMN σ hσ eN (fun x _ => heN x _) C y).2 hy
  have hfeq : ∀ z, eN' (f z) = fw (eN z) := fun z => by
    funext μ
    rw [heN', hf]
    simp only [hfw, heN]
  have e1 : boxCut d L N k M v a h s (x, i) (y, j) =
      boxCut d L N k M v a h sw (eN x, i) (eN y, j) := by
    rw [boxCut_translate hMN σ hσ eN (fun x _ => heN x _)]
    congr 1
    funext z; simp [hsw]
  have e2 : boxCut d L N' k M v a h s' (f x, i) (f y, j) =
      boxCut d L N' k M v a h s'w (fw (eN x), i) (fw (eN y), j) := by
    rw [← hfeq, ← hfeq, boxCut_translate hMN' σ' hσ' eN' (fun x _ => heN' x _)]
    congr 1
    funext z; simp [hs'w]
  rw [e1, e2]
  have hb := hmain nC hk hJN hJN' (f := fw) (fun _ _ => rfl) hewin
    (by rw [Finset.card_map]; exact hCc) hCw hv0 hv1 ha1 ha2 hmass hp hswS hs'wS hssw hswκ
    (eN x) hxw (eN y) hyw i j
  refine hb.trans ?_
  have hg : 0 ≤ (Real.sqrt (finalGap d L))⁻¹ := by positivity
  have hmin : min N N' = N := min_eq_left hNN'
  have hexp : Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - ((((2 * m + 4) + 3) * M : ℕ) : ℝ))) ≤
      Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7))) := by
    refine Real.exp_le_exp.2 ?_
    rw [hmin]
    have hNR : (N : ℝ) = (macK N M : ℝ) * M := by exact_mod_cast hKN.symm
    have hKR : 4 * ((m : ℝ) + t) ≤ macK N M := by exact_mod_cast hK
    push_cast
    rw [hNR]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have : (M : ℝ) * (2 * (t : ℝ) - 7) ≤ (macK N M : ℝ) * M / 2 - (2 * m + 4 + 3) * M := by
      nlinarith
    nlinarith
  have hsq := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hexp hC₀.le)
  have hp0' : 0 ≤ 1 + p := by
    rcases isEmpty_or_nonempty (Fin Nf) with hNf | ⟨⟨i0⟩⟩
    · exact (hNf.false i).elim
    · linarith [(norm_nonneg _).trans (hp i0 i0)]
  have hpoly : 0 ≤ P * ((nC : ℝ) ^ 2 + (nC : ℝ) ^ 4) := by positivity
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq hpoly) hg) hp0'

end Quarter

end Balaban.Green
