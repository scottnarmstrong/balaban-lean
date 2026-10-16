module

public import Balaban.Polymer.TwoTorusResumRootF

/-!
# The last-scale term as a sum over its fibre (W850, blocker 7)

The last-scale term of a support `X` (a set of cells of the last scale in centred coordinates) is
the sum of the localized coefficients `coef ell C` over the sets `C` of macro cells whose centred
image is `X`.  Centring is injective on cells, so the fibre has at most one element (a fortiori at
most `2 ^ |X|`), and inside the quarter box the cell set of two tori with `K ≤ K'` correspond under
the cell map of `finalCoef_close_quarterBox`.  Hence the closeness of the terms is the closeness of
one coefficient, and has the form of the hypothesis `hcoef` of `rootF_hcoef_limit`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

open Balaban.Green

section Arith

/-- Centred value of a residue in the window around the origin. -/
theorem valMinAbs_window {K m b w : ℕ} [NeZero K] (hK : 2 * m + 9 ≤ K) (hb : b < K)
    (hw : (b + (m + 4)) % K = w) (hw2 : w ≤ 2 * m + 4) :
    ((b : ZMod K)).valMinAbs = (w : ℤ) - (m + 4) := by
  by_cases h : b + (m + 4) < K
  · rw [Nat.mod_eq_of_lt h] at hw
    subst hw
    rw [ZMod.valMinAbs_natCast_of_le_half (by omega)]
    omega
  · have h2 : (b + (m + 4)) % K = b + (m + 4) - K := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h2] at hw
    subst hw
    rw [ZMod.valMinAbs_natCast_of_half_lt (by omega) hb]
    omega

/-- Cells that correspond under the cell map have equal centred coordinates. -/
theorem cen_eq_of_rel {K K' m z e : ℕ} [NeZero K] [NeZero K'] (hK : 2 * m + 9 ≤ K)
    (hK' : 2 * m + 9 ≤ K') (hz : z < K) (he : e < K') (hbox : z ≤ m ∨ K - m ≤ z)
    (hrel : (e + (m + 4)) % K' = (z + (m + 4)) % K) :
    ((e : ZMod K')).valMinAbs = ((z : ZMod K)).valMinAbs := by
  have hw := box_window hz hbox (by omega)
  rw [valMinAbs_window hK' he hrel (by omega), valMinAbs_window hK hz rfl hw.2]

/-- A residue with small centred value lies in the window. -/
theorem box_of_cen {K m z : ℕ} [NeZero K] (hK : 2 * m + 5 ≤ K) (hz : z < K)
    (h : ((z : ZMod K)).valMinAbs.natAbs ≤ m) : z ≤ m ∨ K - m ≤ z := by
  by_cases hh : z ≤ K / 2
  · rw [ZMod.valMinAbs_natCast_of_le_half hh] at h
    left; simpa using h
  · rw [ZMod.valMinAbs_natCast_of_half_lt (by omega) hz] at h
    right; omega

/-- Every centred value of absolute value at most `m` is the centred value of a residue. -/
theorem exists_cell_of_cen {K m : ℕ} [NeZero K] (hK : 2 * m + 1 ≤ K) (c : ℤ)
    (hc : c.natAbs ≤ m) : ∃ a : ℕ, a < K ∧ ((a : ZMod K)).valMinAbs = c := by
  refine ⟨(c : ZMod K).val, ZMod.val_lt _, ?_⟩
  rw [ZMod.natCast_zmod_val]
  refine (ZMod.valMinAbs_spec (c : ZMod K) c).2 ⟨rfl, ?_, ?_⟩ <;> omega

end Arith


section Fibre

variable {d M N₀ : ℕ} [NeZero N₀]

omit [NeZero N₀] in
/-- Centring of the cells of the macro cover is injective. -/
theorem cen_injective (cen : MacIdx d N₀ M → Fin d → ℤ)
    (hcen : ∀ z μ, cen z μ = ((z μ : ℕ) : ZMod (macK N₀ M)).valMinAbs) :
    Function.Injective cen := by
  intro z z' h
  funext μ
  have h1 := congrFun h μ
  rw [hcen, hcen, ZMod.valMinAbs_inj] at h1
  apply Fin.ext
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h1
  rwa [Nat.mod_eq_of_lt (z μ).isLt, Nat.mod_eq_of_lt (z' μ).isLt] at h2

omit [NeZero N₀] in
/-- Two sets of cells with the same centred image are equal. -/
theorem fibre_unique (cen : MacIdx d N₀ M → Fin d → ℤ)
    (hcen : ∀ z μ, cen z μ = ((z μ : ℕ) : ZMod (macK N₀ M)).valMinAbs)
    {X : Finset (Fin d → ℤ)} {C₁ C₂ : Finset (MacIdx d N₀ M)} (h₁ : C₁.image cen = X)
    (h₂ : C₂.image cen = X) : C₁ = C₂ :=
  Finset.image_injective (cen_injective cen hcen) (h₁.trans h₂.symm)

omit [NeZero N₀] in
/-- **The fibre has at most one element, a fortiori at most `2 ^ |X|`.**  The sets `C` of macro
cells whose centred image is `X`. -/
theorem fibre_card_le (cen : MacIdx d N₀ M → Fin d → ℤ)
    (hcen : ∀ z μ, cen z μ = ((z μ : ℕ) : ZMod (macK N₀ M)).valMinAbs)
    (X : Finset (Fin d → ℤ)) :
    ((Finset.univ : Finset (Finset (MacIdx d N₀ M))).filter (fun C => C.image cen = X)).card
      ≤ 2 ^ X.card := by
  refine le_trans ?_ (Nat.one_le_two_pow)
  exact Finset.card_le_one.2 fun C₁ h₁ C₂ h₂ =>
    fibre_unique cen hcen (Finset.mem_filter.1 h₁).2 (Finset.mem_filter.1 h₂).2

end Fibre

section Closeness

variable {d M : ℕ} {ι G : Type*}

/-- **The closeness of the last-scale terms from the closeness of one coefficient (W850).**
Let `T ℓ g X` be the sum of the coefficients `cf ℓ g C` over the sets `C` of macro cells of the
torus `ℓ` (`K ℓ = macK (N ℓ) M` cells per side) whose centred image `cen ℓ C` is `X`.  Suppose the
coefficients of two tori `K ℓ ≤ K ℓ'` are close for supports in the box of radius `m` at the margin
`t ≥ 5`, `4 (m + t) ≤ K ℓ`, in the form of `finalCoef_close_quarterBox` (hypothesis `hC`, for
supports with at most `nC` cells and for the cell map `e` of that theorem).  Then for every `X` in
the quarter box of the torus `ℓ` at margin `τ ℓ X ≥ t₀ ≥ 5`, with at most `nC` cells,
`‖T ℓ g X - T ℓ' g X‖` has the bound of `hcoef` in `rootF_hcoef_limit`. -/
theorem fibre_closeness (N : ι → ℕ) [∀ ℓ, NeZero (N ℓ)] (K : ι → ℕ)
    (hK : ∀ ℓ, K ℓ = macK (N ℓ) M) (hMN : ∀ ℓ, M ∣ N ℓ)
    (cen : ∀ ℓ, MacIdx d (N ℓ) M → Fin d → ℤ)
    (hcen : ∀ ℓ z μ, cen ℓ z μ = ((z μ : ℕ) : ZMod (macK (N ℓ) M)).valMinAbs)
    (cf : ∀ ℓ, G → Finset (MacIdx d (N ℓ) M) → ℂ) (T : ι → G → Finset (Fin d → ℤ) → ℂ)
    (hT : ∀ ℓ g X, T ℓ g X = ∑ C ∈ (Finset.univ : Finset (Finset (MacIdx d (N ℓ) M))).filter
      (fun C => C.image (cen ℓ) = X), cf ℓ g C)
    (Q : ι → Finset (Fin d → ℤ) → Prop)
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (sz : Finset (Fin d → ℤ) → ℕ) (hsz : ∀ X, sz X = X.card)
    (τ : ι → Finset (Fin d → ℤ) → ℕ)
    (hτ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    (D : Set G) {Pc C₀ c₀ κ₁ : ℝ} {t₀ nC : ℕ} (ht₀ : 5 ≤ t₀)
    (ε : ι → G → Finset (Fin d → ℤ) → ℝ)
    (hC : ∀ ℓ ℓ' g, g ∈ D → ∀ {m t : ℕ}, 5 ≤ t → 4 * (m + t) ≤ K ℓ → K ℓ ≤ K ℓ' →
      N ℓ ≤ N ℓ' → ∀ e : MacIdx d (N ℓ) M → MacIdx d (N ℓ') M,
      (∀ z i, ((e z i : ℕ) + (m + 4)) % macK (N ℓ') M = ((z i : ℕ) + (m + 4)) % macK (N ℓ) M) →
      ∀ C : Finset (MacIdx d (N ℓ) M), C.card ≤ nC →
      (∀ z ∈ C, ∀ i, (z i : ℕ) ≤ m ∨ macK (N ℓ) M - m ≤ (z i : ℕ)) →
      ‖cf ℓ g C - cf ℓ' g (C.image e)‖ ≤
        Pc * (C₀ * Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7))) + ε ℓ g (C.image (cen ℓ))) /
          (Real.exp κ₁ - 1) ^ C.card) :
    ∀ ℓ ℓ' X, Q ℓ X → K ℓ ≤ K ℓ' → t₀ ≤ τ ℓ X → X.card ≤ nC → ∀ g ∈ D,
      ‖T ℓ g X - T ℓ' g X‖ ≤
        Pc * (C₀ * Real.exp (-c₀ * ((M : ℝ) * (2 * (τ ℓ X : ℝ) - 7))) + ε ℓ g X) /
          (Real.exp κ₁ - 1) ^ sz X := by
  intro ℓ ℓ' X hQX hKK ht hX g hg
  have hKl := hK ℓ
  have hKl' := hK ℓ'
  have : NeZero (macK (N ℓ) M) := ⟨(macK_pos _ _).ne'⟩
  have : NeZero (macK (N ℓ') M) := ⟨(macK_pos _ _).ne'⟩
  set r := X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs) with hr_def
  have hr : ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ r := fun x hx μ =>
    le_trans (Finset.le_sup (f := fun μ => (x μ).natAbs) (Finset.mem_univ μ))
      (Finset.le_sup (f := fun x : Fin d → ℤ => Finset.univ.sup fun μ => (x μ).natAbs) hx)
  have hrK : r ≤ K ℓ / 4 := Finset.sup_le fun x hx => Finset.sup_le fun μ _ => (hQ ℓ X).1 hQX x hx μ
  have hτℓ := hτ ℓ X
  rw [← hr_def] at hτℓ
  have ht5 : 5 ≤ τ ℓ X := le_trans ht₀ ht
  have hKbig : 2 * r + 9 ≤ macK (N ℓ) M := by omega
  have hKbig' : 2 * r + 9 ≤ macK (N ℓ') M := by omega
  -- existence of a preimage
  have hex : ∀ x : Fin d → ℤ, (∀ μ, (x μ).natAbs ≤ r) → ∃ z : MacIdx d (N ℓ) M, cen ℓ z = x := by
    intro x hx
    choose a ha hv using fun μ => exists_cell_of_cen (K := macK (N ℓ) M) (m := r) (by omega)
      (x μ) (hx μ)
    exact ⟨fun μ => ⟨a μ, ha μ⟩, funext fun μ => by rw [hcen]; exact hv μ⟩
  choose! zf hzf using hex
  set C₀ : Finset (MacIdx d (N ℓ) M) := X.image zf with hC₀
  have hC₀img : C₀.image (cen ℓ) = X := by
    rw [hC₀, Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := X)]
    exact Finset.image_congr fun x hx => hzf x (hr x hx)
  have hcard : C₀.card = X.card := by
    rw [← hC₀img, Finset.card_image_of_injective _ (cen_injective (cen ℓ) (hcen ℓ))]
  have hbox : ∀ z ∈ C₀, ∀ i, (z i : ℕ) ≤ r ∨ macK (N ℓ) M - r ≤ (z i : ℕ) := by
    intro z hz i
    have hzX : cen ℓ z ∈ X := hC₀img ▸ Finset.mem_image_of_mem _ hz
    have := hr _ hzX i
    rw [hcen] at this
    exact box_of_cen (by omega) (z i).isLt this
  obtain ⟨e, he⟩ : ∃ e : MacIdx d (N ℓ) M → MacIdx d (N ℓ') M, ∀ z i,
      ((e z i : ℕ) + (r + 4)) % macK (N ℓ') M = ((z i : ℕ) + (r + 4)) % macK (N ℓ) M :=
    exists_cellMap_box (by omega)
  have hC₀e : (C₀.image e).image (cen ℓ') = X := by
    rw [Finset.image_image, ← hC₀img]
    refine Finset.image_congr fun z hz => ?_
    funext μ
    simp only [Function.comp]
    rw [hcen, hcen]
    exact cen_eq_of_rel hKbig hKbig' (z μ).isLt (e z μ).isLt (hbox z hz μ) (he z μ)
  have hF : (Finset.univ : Finset (Finset (MacIdx d (N ℓ) M))).filter
      (fun C => C.image (cen ℓ) = X) = {C₀} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hC₀img⟩, fun C hC =>
      fibre_unique (cen ℓ) (hcen ℓ) (Finset.mem_filter.1 hC).2 hC₀img⟩
  have hF' : (Finset.univ : Finset (Finset (MacIdx d (N ℓ') M))).filter
      (fun C => C.image (cen ℓ') = X) = {C₀.image e} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hC₀e⟩, fun C hC =>
      fibre_unique (cen ℓ') (hcen ℓ') (Finset.mem_filter.1 hC).2 hC₀e⟩
  have hNN : N ℓ ≤ N ℓ' := by
    obtain ⟨a, ha⟩ := hMN ℓ
    obtain ⟨b, hb⟩ := hMN ℓ'
    have hM : 0 < M := Nat.pos_of_dvd_of_pos ⟨a, ha⟩ (Nat.pos_of_ne_zero (NeZero.ne _))
    have h1 : macK (N ℓ) M = a := by
      rw [macK_eq_div_of_dvd ⟨a, ha⟩, ha, Nat.mul_div_cancel_left _ hM]
    have h2 : macK (N ℓ') M = b := by
      rw [macK_eq_div_of_dvd ⟨b, hb⟩, hb, Nat.mul_div_cancel_left _ hM]
    rw [ha, hb]
    exact Nat.mul_le_mul_left _ (by omega)
  rw [hT, hT, hF, hF', Finset.sum_singleton, Finset.sum_singleton]
  have key := hC ℓ ℓ' g hg (m := r) (t := τ ℓ X) ht5 (by omega) hKK hNN e he C₀
    (by omega) hbox
  rw [hC₀img, hcard] at key
  rw [hsz]
  exact key

end Closeness


end Balaban.Polymer
