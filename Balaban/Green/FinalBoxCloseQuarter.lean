/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxCloseCut
public import Balaban.Green.FinalBoxCloseTerm
public import Balaban.Polymer.TwoTorusQuarterBox
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cut family of the final Hessian on two tori, quarter-box frame (A6-3 (d))

* `chiSum_translate`, `boxCut_translate`: the cut family is covariant under the translation by `p`
  cells (`taggedCfin_translate`, `macChi_translate`);
* `quarterBox_regions`: the regions of `C` and `e C` correspond under the lift (injectively), `e` is
  injective on `C`;
* `boxCut_close_read`, `rootedCoef_boxCut_close_quarterBox`: the rooted coefficients of a term of the
  final cut field on two tori, quarter-box frame (`rootedCoef_boxCut_close_of_regions` with the bound of
  `boxCut_close_quarterBox`);
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

omit [NeZero L] in
/-- The cells of the quarter box (within `m` cells of the origin) are in the window `[4, 2m + 4]` after
the cyclic shift by `m + 4` cells, when `4 (m + t) ≤ K`, `t ≥ 5`. -/
theorem window_of_quarter {N : ℕ} [NeZero N] {m t : ℕ} (ht5 : 5 ≤ t) (hK : 4 * (m + t) ≤ macK N M)
    (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + (m + 4)) % macK N M) {C : Finset (MacIdx d N M)}
    (hC : ∀ z ∈ C, ∀ i, (z i : ℕ) ≤ m ∨ macK N M - m ≤ (z i : ℕ)) :
    ∀ z ∈ C.map σ.toEmbedding, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ 2 * m + 4 := by
  refine window_translate σ hσ fun z hz i => ?_
  have hzK := (z i).isLt
  rcases hC z hz i with h1 | h1
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · have : (z i : ℕ) + (m + 4) = ((z i : ℕ) + (m + 4) - macK N M) + macK N M := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega

omit [NeZero L] in
/-- The room of the window on the smaller torus: `2 (2m + 10) M ≤ N` when `4 (m + t) ≤ K`, `t ≥ 5`. -/
theorem room_of_quarter {N : ℕ} [NeZero N] {m t : ℕ} (hMN : M ∣ N) (ht5 : 5 ≤ t)
    (hK : 4 * (m + t) ≤ macK N M) : 2 * ((2 * m + 4) + 6) * M ≤ N := by
  have hKN : macK N M * M = N := by
    rw [macK_eq_div_of_dvd hMN]; exact Nat.div_mul_cancel hMN
  rw [← hKN]; nlinarith

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
  have hJN : 2 * ((2 * m + 4) + 6) * M ≤ N := room_of_quarter hMN ht5 hK
  have hJN' : 2 * ((2 * m + 4) + 6) * M ≤ N' := hJN.trans hNN'
  set fw : L1Torus d N → L1Torus d N' := fun x μ => (((x μ).val : ℕ) : ZMod N') with hfw
  set ew : MacIdx d N M → MacIdx d N' M := fun z => σ' (e (σ.symm z)) with hew
  have hewin := cellMap_translate (J := 2 * m + 4) σ σ' hσ hσ' (e := e) (fun z i hz => he z i (by
    omega))
  have hCw := window_of_quarter ht5 hK σ hσ hC
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

/-- **The regions of `C` and `e C` correspond in the quarter-box frame**: the lift `f` carries the region
of `C` injectively onto the region of `e C`, and `e` is injective on `C`. -/
theorem quarterBox_regions {N N' : ℕ} [NeZero N] [NeZero N'] (hM : 0 < M) (hMN : M ∣ N)
    (hMN' : M ∣ N') (hNN' : N ≤ N') {m t : ℕ} (ht5 : 5 ≤ t) (hK : 4 * (m + t) ≤ macK N M)
    {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ + ((M * (m + 4) : ℕ) : ZMod N') =
      ((((x μ + ((M * (m + 4) : ℕ) : ZMod N)).val : ℕ)) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, ((z i : ℕ) + (m + 4)) % macK N M ≤ 2 * m + 8 →
      ((e z i : ℕ) + (m + 4)) % macK N' M = ((z i : ℕ) + (m + 4)) % macK N M)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, (z i : ℕ) ≤ m ∨ macK N M - m ≤ (z i : ℕ))
    (Nf : ℕ) :
    patchReg (spinBoxPatch d N' M Nf) (C.image e) =
        spinMap (Nf := Nf) f '' patchReg (spinBoxPatch d N M Nf) C ∧
      Set.InjOn (spinMap (Nf := Nf) f) (patchReg (spinBoxPatch d N M Nf) C) ∧
      Set.InjOn e (C : Set (MacIdx d N M)) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_cellShift (N := N) (M := M) d (m + 4)
  obtain ⟨σ', hσ'⟩ := exists_cellShift (N := N') (M := M) d (m + 4)
  obtain ⟨eN, heN⟩ := exists_translate (d := d) (fun _ => ((M * (m + 4) : ℕ) : ZMod N))
  obtain ⟨eN', heN'⟩ := exists_translate (d := d) (fun _ => ((M * (m + 4) : ℕ) : ZMod N'))
  have hJN := room_of_quarter (M := M) hMN ht5 hK
  have hJN' := hJN.trans hNN'
  set fw : L1Torus d N → L1Torus d N' := fun x μ => (((x μ).val : ℕ) : ZMod N') with hfw
  set gw : L1Torus d N' → L1Torus d N := fun y μ => (((y μ).val : ℕ) : ZMod N) with hgw
  set ew : MacIdx d N M → MacIdx d N' M := fun z => σ' (e (σ.symm z)) with hew
  have hewin := cellMap_translate (J := 2 * m + 4) σ σ' hσ hσ' (e := e) (fun z i hz => he z i (by
    omega))
  have hCw := window_of_quarter ht5 hK σ hσ hC
  have hbij := macRegion_bijOn hM hJN hJN' (f := fw) (fun _ _ => rfl) (g := gw) (fun _ _ => rfl)
    hewin hCw
  rw [image_translate σ σ' e C] at hbij
  have hfeq : ∀ z, eN' (f z) = fw (eN z) := fun z => by
    funext μ
    rw [heN', hf]
    simp only [hfw, heN]
  have hreg1 : ∀ x, x ∈ macRegion d N M C ↔ eN x ∈ macRegion d N M (C.map σ.toEmbedding) :=
    fun x => (mem_macRegion_translate hMN σ hσ eN (fun x _ => heN x _) C x).symm
  have hreg2 : ∀ y, y ∈ macRegion d N' M (C.image e) ↔
      eN' y ∈ macRegion d N' M ((C.image e).map σ'.toEmbedding) :=
    fun y => (mem_macRegion_translate hMN' σ' hσ' eN' (fun x _ => heN' x _) (C.image e) y).symm
  have hB : Set.BijOn f (macRegion d N M C) (macRegion d N' M (C.image e)) := by
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
    · rw [hreg2, hfeq]; exact hbij.mapsTo ((hreg1 x).1 hx)
    · have h1 : fw (eN x) = fw (eN y) := by rw [← hfeq, ← hfeq, hxy]
      exact eN.injective (hbij.injOn ((hreg1 x).1 hx) ((hreg1 y).1 hy) h1)
    · obtain ⟨xw, hxw, hfxw⟩ := hbij.surjOn ((hreg2 y).1 hy)
      refine ⟨eN.symm xw, (hreg1 _).2 (by rw [eN.apply_symm_apply]; exact hxw), ?_⟩
      apply eN'.injective
      rw [hfeq, eN.apply_symm_apply, hfxw]
  refine ⟨?_, ?_, ?_⟩
  · ext ⟨y, i⟩
    rw [mem_patchReg_spinBoxPatch]
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := hB.surjOn hy
      exact ⟨(x, i), mem_patchReg_spinBoxPatch.2 hx, by simp [spinMap, hxy]⟩
    · rintro ⟨⟨x, j⟩, hx, hxy⟩
      simp only [spinMap, Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      exact hB.mapsTo (mem_patchReg_spinBoxPatch.1 hx)
  · rintro ⟨x, i⟩ hx ⟨y, j⟩ hy hxy
    simp only [spinMap, Prod.mk.injEq] at hxy
    have hxy' : x = y :=
      hB.injOn (mem_patchReg_spinBoxPatch.1 hx) (mem_patchReg_spinBoxPatch.1 hy) hxy.1
    rw [hxy', hxy.2]
  · intro a ha b hb hab
    have h1 := injOn_cellMap_window hewin hCw (Finset.mem_map_of_mem σ.toEmbedding ha)
      (Finset.mem_map_of_mem σ.toEmbedding hb) (by simp [hab])
    exact σ.injective h1

/-- **The entries of the cut families on the read set**: on the region the closeness is given; at a site
of the read set off the region both entries vanish (the decoupling property), provided the lift of such a
site is off the region of `e C`. -/
theorem boxCut_close_read {k N N' : ℕ} [NeZero N] [NeZero N'] {v a : ℝ} (hd : 0 < d)
    (hk : 1 ≤ k) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {f : L1Torus d N → L1Torus d N'} {e : MacIdx d N M → MacIdx d N' M}
    {C : Finset (MacIdx d N M)} {Nf : ℕ} (h : Fin Nf → ℂ) {S : Set (L1Torus d N × Fin Nf)}
    (hSreg : ∀ q ∈ S, spinMap f q ∈ patchReg (spinBoxPatch d N' M Nf) (C.image e) →
      q ∈ patchReg (spinBoxPatch d N M Nf) C)
    {s : MacIdx d N M → ℂ} (hs : s ∈ polydisc (0 : MacIdx d N M → ℂ) (fun _ => Real.exp κ))
    (hsC : s ∈ supportedOn C) {s' : MacIdx d N' M → ℂ}
    (hs' : s' ∈ polydisc (0 : MacIdx d N' M → ℂ) (fun _ => Real.exp κ))
    (hs'C : s' ∈ supportedOn (C.image e)) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδreg : ∀ q ∈ patchReg (spinBoxPatch d N M Nf) C, ∀ q' ∈ patchReg (spinBoxPatch d N M Nf) C,
      ‖boxCut d L N k M v a h s q q' - boxCut d L N' k M v a h s' (spinMap f q) (spinMap f q')‖ ≤
        δ) :
    ∀ q ∈ S, ∀ q' ∈ patchReg (spinBoxPatch d N M Nf) C,
      ‖boxCut d L N k M v a h s q q' - boxCut d L N' k M v a h s' (spinMap f q) (spinMap f q')‖ ≤
        δ := by
  intro q hq q' hq'
  by_cases hqr : q ∈ patchReg (spinBoxPatch d N M Nf) C
  · exact hδreg q hqr q' hq'
  · have h1 : boxCut d L N k M v a h s q q' = 0 := by
      by_contra hne
      exact hqr ((cutDecoupling_boxCut hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ h).supp C s hs hsC
        q q' hne).1
    have h2 : boxCut d L N' k M v a h s' (spinMap f q) (spinMap f q') = 0 := by
      by_contra hne
      exact hqr (hSreg q hq ((cutDecoupling_boxCut hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ h).supp
        (C.image e) s' hs' hs'C _ _ hne).1)
    rw [h1, h2, sub_self, norm_zero]
    exact hδ0

/-- **The rooted coefficients of a term of the final cut field on two tori, quarter-box frame.** There
are `P ≥ 0`, `C₀, c₀ > 0` (depending on `d, L, M, κ`; `c₀` on `d, L` only) such that, for two tori
`N ≤ N'`, a family `C` of at most `n_C` cells within `m` cells of the origin with margin `t`
(`4 (m + t) ≤ K`, `t ≥ 5`), a term `τ` and a term `τ'` within `η` of `τ` read through the lift `f` on the
read set `S` (whose lift meets the region of `e C` only through the region of `C`), the rooted
coefficients differ by at most `(η + M_τ ε / (r - r₁ - ε)) / (e^κ - 1)^{|C|}`,
`ε = |c| |reg C| δ ρ`, `δ = P (n_C² + n_C⁴) √(C₀ e^{-c₀ M (2t - 7)}) / √g · (1 + p)`. -/
theorem rootedCoef_boxCut_close_quarterBox (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
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
      ∀ {Nf : ℕ} {h : Fin Nf → ℂ} {p : ℝ}, 0 ≤ p → (∀ i j, ‖spinProj h i j‖ ≤ p) →
      ∀ (c : ℂ) (φ₀ : L1Torus d N × Fin Nf → ℂ) (φ₀' : L1Torus d N' × Fin Nf → ℂ)
        {S : Set (L1Torus d N × Fin Nf)},
      (∀ q ∈ S, spinMap f q ∈ patchReg (spinBoxPatch d N' M Nf) (C.image e) →
        q ∈ patchReg (spinBoxPatch d N M Nf) C) →
      (∀ q ∈ S, φ₀ q = φ₀' (spinMap f q)) →
      ∀ {τ : (L1Torus d N × Fin Nf → ℂ) → ℂ} {τ' : (L1Torus d N' × Fin Nf → ℂ) → ℂ} {r Mτ : ℝ},
      AnalyticOnNhd ℂ τ (Metric.ball φ₀ r) → (∀ u ∈ Metric.ball φ₀ r, ‖τ u‖ ≤ Mτ) →
      AnalyticOnNhd ℂ τ' (Metric.ball φ₀' r) → ∀ {η : ℝ},
      (∀ (u' : L1Torus d N' × Fin Nf → ℂ) (u : L1Torus d N × Fin Nf → ℂ),
        (∀ q ∈ S, u q = u' (spinMap f q)) → ‖τ' u' - τ u‖ ≤ η) →
      ∀ {ρ : ℝ}, 0 ≤ ρ → ∀ {w : L1Torus d N × Fin Nf → ℂ}, (∀ q, ‖w q‖ ≤ ρ) →
      ∀ {w' : L1Torus d N' × Fin Nf → ℂ}, (∀ q, ‖w' q‖ ≤ ρ) →
      (∀ q ∈ patchReg (spinBoxPatch d N M Nf) C, w' (spinMap f q) = w q) →
      ∀ {r₁ : ℝ}, ‖c‖ * boxCutConst d L Nf a κ p * ρ < r₁ →
      r₁ + ‖c‖ * ((regFin (spinBoxPatch d N M Nf) C).card : ℝ) *
        (P * ((nC : ℝ) ^ 2 + (nC : ℝ) ^ 4) *
          Real.sqrt (C₀ * Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7)))) /
          Real.sqrt (finalGap d L) * (1 + p)) * ρ < r →
      ‖rootedCoef τ φ₀ (fun s q q' => c * boxCut d L N k M v a h s q q') w C -
          rootedCoef τ' φ₀' (fun s q q' => c * boxCut d L N' k M v a h s q q') w' (C.image e)‖ ≤
        (η + Mτ * (‖c‖ * ((regFin (spinBoxPatch d N M Nf) C).card : ℝ) *
            (P * ((nC : ℝ) ^ 2 + (nC : ℝ) ^ 4) *
              Real.sqrt (C₀ * Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7)))) /
              Real.sqrt (finalGap d L) * (1 + p)) * ρ) /
            (r - r₁ - ‖c‖ * ((regFin (spinBoxPatch d N M Nf) C).card : ℝ) *
              (P * ((nC : ℝ) ^ 2 + (nC : ℝ) ^ 4) *
                Real.sqrt (C₀ * Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7)))) /
                Real.sqrt (finalGap d L) * (1 + p)) * ρ)) /
          (Real.exp κ - 1) ^ C.card := by
  have hκ0 : 0 ≤ κ := by linarith
  obtain ⟨P, C₀, c₀, hP0, hC₀, hc₀, hbox⟩ := boxCut_close_quarterBox (L := L) hd hM hκ0 hMB hMκ
  refine ⟨P, C₀, c₀, hP0, hC₀, hc₀, ?_⟩
  intro nC k N N' _ _ hk hMN hMN' hNN' m t ht5 hK f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass Nf
    h p hp0 hp c φ₀ φ₀' S hSreg hφ τ τ' r Mτ hτan hτb hτ'an η hττ ρ hρ w hw w' hw' hww r₁ hm hr
  obtain ⟨hreg, hinj, heinj⟩ := quarterBox_regions hM hMN hMN' hNN' ht5 hK hf he hC Nf
  set δ := P * ((nC : ℝ) ^ 2 + (nC : ℝ) ^ 4) *
    Real.sqrt (C₀ * Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7)))) /
    Real.sqrt (finalGap d L) * (1 + p) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  refine rootedCoef_boxCut_close_of_regions hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ heinj hreg
    hinj hp0 hp c φ₀ φ₀' hφ hτan hτb hτ'an hττ hρ hw hw' hww hδ0 ?_ hm hr
  intro s hs s' hs' hss
  have hsκ : ∀ q, ‖s q‖ ≤ Real.exp κ := fun q => (hs.2 q).le
  have hspol : s ∈ polydisc (0 : MacIdx d N M → ℂ) (fun _ => Real.exp κ) := fun i => by
    simpa using hs.2 i
  have hs'pol : s' ∈ polydisc (0 : MacIdx d N' M → ℂ) (fun _ => Real.exp κ) := fun j => by
    by_cases hj : j ∈ C.image e
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
      simpa [hss i hi] using hs.2 i
    · simpa [hs' j hj] using Real.exp_pos κ
  refine boxCut_close_read hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ h hSreg hspol hs.1 hs'pol hs'
    hδ0 fun q hq q' hq' => ?_
  obtain ⟨x, i⟩ := q
  obtain ⟨y, j⟩ := q'
  exact hbox nC hk hMN hMN' hNN' ht5 hK hf he hCc hC hv0 hv1 ha1 ha2 hmass hp hs.1 hs' hss hsκ x
    (mem_patchReg_spinBoxPatch.1 hq) y (mem_patchReg_spinBoxPatch.1 hq') i j

end Quarter

end Balaban.Green
