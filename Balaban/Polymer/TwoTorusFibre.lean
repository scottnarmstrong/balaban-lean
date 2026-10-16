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

open Balaban.Green Balaban.Localization MeasureTheory Balaban.Analysis

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



section Physical

variable {d M : ℕ} {ι G : Type*}

/-- **The closeness of the last-scale terms from the quarter-box theorem (W850).**
The last-scale term of the support `X` of the torus `ℓ` (`N ℓ = M K ℓ`) is
`T ℓ g X = Σ_{C : C.image (cen ℓ) = X} (coef ellE C - coef ell0 C + coef J C)`, with `ellE`, `ell0`
the logarithms of the perturbed and the unperturbed defect, and `J` the cutoff interaction
`s ↦ ∫_{|ψ| ≤ ρJ} F (Σ_y taggedCfin s · y ψ_y) dγ`.  The physical inputs are exactly the
hypotheses of `finalCoef_close_quarterBox` on each torus (smallness `hW`, analytic logarithms
`han`, `han0`, `hdet`, `hdet0`, analyticity and bounds of `F`, finiteness of the mass of `γ`), the
operator closeness `hEcl` of `E ℓ g` on the support with defect `ε`, the closeness `hFcl` of the
functional `F`, the correspondence `hγ` of the measures, and uniform bounds `Lb`, `mb` on the
Lipschitz constant and the mass.  The conclusion is the closeness `hcoef` of `rootF_hcoef_limit`
(with `Mr = M`, `κ₁ = κ`) for the supports with at most `nC` cells. -/
theorem fibre_hcoef_of_quarterBox {L k : ℕ} [NeZero L] (hd : 0 < d) (hM : 0 < M)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {rE η : ℝ} (hrE : pdEps d L / 4 ≤ rE) (hη0 : 0 ≤ η)
    (hη : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η *
      ballConst d (3 * pdEps d L / 4))) ≤ 1) (nC : ℕ) (hk : 1 ≤ k)
    {v a sc : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (hsc : 0 ≤ sc)
    (N : ι → ℕ) [∀ ℓ, NeZero (N ℓ)] (K : ι → ℕ)
    (hK : ∀ ℓ, K ℓ = macK (N ℓ) M) (hMN : ∀ ℓ, M ∣ N ℓ)
    (cen : ∀ ℓ, MacIdx d (N ℓ) M → Fin d → ℤ)
    (hcen : ∀ ℓ z μ, cen ℓ z μ = ((z μ : ℕ) : ZMod (macK (N ℓ) M)).valMinAbs)
    (D : Set G) (Q : ι → Finset (Fin d → ℤ) → Prop)
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (sz : Finset (Fin d → ℤ) → ℕ) (hsz : ∀ X, sz X = X.card)
    (τ : ι → Finset (Fin d → ℤ) → ℕ)
    (hτ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    {t₀ : ℕ} (ht₀ : 5 ≤ t₀)
    -- the operator `E`, its closeness `ε`, and the logarithms of the defects
    (E : ∀ ℓ, G → Matrix (L1Torus d (N ℓ)) (L1Torus d (N ℓ)) ℂ)
    (hW : ∀ ℓ g, g ∈ D → WSmall rE η (E ℓ g))
    (hW0 : ∀ ℓ, WSmall rE η (0 : Matrix (L1Torus d (N ℓ)) (L1Torus d (N ℓ)) ℂ))
    (ε : ι → G → Finset (Fin d → ℤ) → ℝ) (hε0 : ∀ ℓ g X, 0 ≤ ε ℓ g X)
    (hEcl : ∀ ℓ ℓ' g, g ∈ D → ∀ {m : ℕ} {f : L1Torus d (N ℓ) → L1Torus d (N ℓ')},
      (∀ x μ, f x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ')) =
        ((((x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ))).val : ℕ)) : ZMod (N ℓ'))) →
      ∀ C : Finset (MacIdx d (N ℓ) M), ∀ x ∈ macRegion d (N ℓ) M C, ∀ y ∈ macRegion d (N ℓ) M C,
        ‖E ℓ g x y - E ℓ' g (f x) (f y)‖ ≤ ε ℓ g (C.image (cen ℓ)))
    {ρ : ℝ} (hρ : Real.exp κ < ρ)
    (ellE ell0 : ∀ ℓ, G → (MacIdx d (N ℓ) M → ℂ) → ℂ)
    (han : ∀ ℓ g, g ∈ D → AnalyticOnNhd ℂ (ellE ℓ g) (Metric.ball 0 ρ))
    (han0 : ∀ ℓ g, g ∈ D → AnalyticOnNhd ℂ (ell0 ℓ g) (Metric.ball 0 ρ))
    (hz : ∀ ℓ g, g ∈ D → ellE ℓ g 0 = 0) (hz0 : ∀ ℓ g, g ∈ D → ell0 ℓ g 0 = 0)
    (hdet : ∀ ℓ g, g ∈ D → ∀ s' ∈ Metric.ball (0 : MacIdx d (N ℓ) M → ℂ) ρ,
      (1 - taggedMat Finset.univ (macTags d (N ℓ) M)
        (fun z => boxR (finalOp d L (N ℓ) k v a) (macBoxF d (N ℓ) M z)
            (fun u => ((macChi d (N ℓ) M z u : ℝ) : ℂ)) sc -
          E ℓ g * (Matrix.diagonal (fun u => ((macChi d (N ℓ) M z u : ℝ) : ℂ)) *
            boxG (finalOp d L (N ℓ) k v a) (macBoxF d (N ℓ) M z) sc)) s').det =
        Complex.exp (ellE ℓ g s'))
    (hdet0 : ∀ ℓ g, g ∈ D → ∀ s' ∈ Metric.ball (0 : MacIdx d (N ℓ) M → ℂ) ρ,
      (1 - taggedMat Finset.univ (macTags d (N ℓ) M)
        (fun z => boxR (finalOp d L (N ℓ) k v a) (macBoxF d (N ℓ) M z)
            (fun u => ((macChi d (N ℓ) M z u : ℝ) : ℂ)) sc -
          (0 : Matrix (L1Torus d (N ℓ)) (L1Torus d (N ℓ)) ℂ) *
            (Matrix.diagonal (fun u => ((macChi d (N ℓ) M z u : ℝ) : ℂ)) *
            boxG (finalOp d L (N ℓ) k v a) (macBoxF d (N ℓ) M z) sc)) s').det =
        Complex.exp (ell0 ℓ g s'))
    -- the cutoff interaction
    {ρJ RF Lb mb : ℝ} (hρJ : 0 ≤ ρJ) (hLb : 0 ≤ Lb) (hmb : 0 ≤ mb)
    (γ : ∀ ℓ, Measure (L1Torus d (N ℓ) → ℝ))
    (hγfin : ∀ ℓ, γ ℓ {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ} < ⊤)
    (hγmass : ∀ ℓ, (γ ℓ {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ}).toReal ≤ mb)
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * ρJ < RF)
    (F : ∀ ℓ, G → (L1Torus d (N ℓ) → ℂ) → ℂ) (B' : G → ℝ) (Lip : ι → G → ℝ)
    (hFan : ∀ ℓ g, g ∈ D → AnalyticOnNhd ℂ (F ℓ g) (polydisc (0 : L1Torus d (N ℓ) → ℂ) (fun _ => RF)))
    (hFB : ∀ ℓ g, g ∈ D → ∀ w ∈ polydisc (0 : L1Torus d (N ℓ) → ℂ) (fun _ => RF),
      ‖F ℓ g w‖ ≤ B' g)
    (hFm : ∀ ℓ g, g ∈ D → Measurable (F ℓ g))
    (hLipb : ∀ ℓ g, g ∈ D → Lip ℓ g ≤ Lb)
    (hFcl : ∀ ℓ ℓ' g, g ∈ D → ∀ {m : ℕ} {f : L1Torus d (N ℓ) → L1Torus d (N ℓ')},
      (∀ x μ, f x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ')) =
        ((((x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ))).val : ℕ)) : ZMod (N ℓ'))) →
      ∀ C : Finset (MacIdx d (N ℓ) M), C.card ≤ nC →
      (∀ z ∈ C, ∀ i, (z i : ℕ) ≤ m ∨ macK (N ℓ) M - m ≤ (z i : ℕ)) →
      ∀ {e : MacIdx d (N ℓ) M → MacIdx d (N ℓ') M},
      (∀ z i, ((z i : ℕ) + (m + 4)) % macK (N ℓ) M ≤ 2 * m + 8 →
        ((e z i : ℕ) + (m + 4)) % macK (N ℓ') M = ((z i : ℕ) + (m + 4)) % macK (N ℓ) M) →
      ∀ (w : L1Torus d (N ℓ) → ℂ) (w' : L1Torus d (N ℓ') → ℂ),
        (∀ x, x ∉ macRegion d (N ℓ) M C → w x = 0) →
        (∀ x', x' ∉ macRegion d (N ℓ') M (C.image e) → w' x' = 0) →
        (∀ x, ‖w x‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρJ) →
        (∀ x', ‖w' x'‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρJ) → ∀ η : ℝ, 0 ≤ η →
        (∀ x ∈ macRegion d (N ℓ) M C, ‖w' (f x) - w x‖ ≤ η) →
        ‖F ℓ' g w' - F ℓ g w‖ ≤ Lip ℓ g * η)
    (hγ : ∀ ℓ ℓ', ∀ {m : ℕ} {f : L1Torus d (N ℓ) → L1Torus d (N ℓ')},
      (∀ x μ, f x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ')) =
        ((((x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ))).val : ℕ)) : ZMod (N ℓ'))) →
      ∀ C : Finset (MacIdx d (N ℓ) M), C.card ≤ nC →
      (∀ z ∈ C, ∀ i, (z i : ℕ) ≤ m ∨ macK (N ℓ) M - m ≤ (z i : ℕ)) →
        Measure.map (fun (ψ : L1Torus d (N ℓ) → ℝ) (q : ↥(macRegion d (N ℓ) M C)) => ψ q)
            ((γ ℓ).restrict {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ}) =
          Measure.map (fun (ψ' : L1Torus d (N ℓ') → ℝ) (q : ↥(macRegion d (N ℓ) M C)) => ψ' (f q))
            ((γ ℓ').restrict {ψ' : L1Torus d (N ℓ') → ℝ | ∀ y, |ψ' y| ≤ ρJ}))
    (T : ι → G → Finset (Fin d → ℤ) → ℂ)
    (hT : ∀ ℓ g X, T ℓ g X = ∑ C ∈ (Finset.univ : Finset (Finset (MacIdx d (N ℓ) M))).filter
      (fun C => C.image (cen ℓ) = X),
      (coef (ellE ℓ g) C - coef (ell0 ℓ g) C +
        coef (fun s : MacIdx d (N ℓ) M → ℂ =>
          ∫ ψ in {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ},
            F ℓ g (fun x => ∑ y, taggedCfin d L (N ℓ) k M v a s x y * ((ψ y : ℝ) : ℂ))
              ∂(γ ℓ)) C)) :
    ∃ Pc C₀ c₀ : ℝ, 0 ≤ Pc ∧ 0 < C₀ ∧ 0 < c₀ ∧
    ∀ ℓ ℓ' X, Q ℓ X → K ℓ ≤ K ℓ' → t₀ ≤ τ ℓ X → X.card ≤ nC → ∀ g ∈ D,
      ‖T ℓ g X - T ℓ' g X‖ ≤
        Pc * (C₀ * Real.exp (-c₀ * ((M : ℝ) * (2 * (τ ℓ X : ℝ) - 7))) + ε ℓ g X) /
          (Real.exp κ - 1) ^ sz X := by
  obtain ⟨P, C₁, c₁, hP, hC₁, hc₁, hmain⟩ :=
    finalCoef_close_quarterBox (L := L) hd hM hκ hMB hMκ hrE hη0 hη nC
  set Jc : ℝ := Lb * (((nC * (8 * M + 1) ^ d : ℕ) : ℝ) * ρJ * mb / Real.sqrt (finalGap d L))
    with hJc
  have hJc0 : 0 ≤ Jc := by positivity
  refine ⟨P, (2 + Jc) * C₁, c₁, hP, by positivity, hc₁, ?_⟩
  refine fibre_closeness N K hK hMN cen hcen
    (fun ℓ g C => coef (ellE ℓ g) C - coef (ell0 ℓ g) C +
        coef (fun s : MacIdx d (N ℓ) M → ℂ =>
          ∫ ψ in {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ},
            F ℓ g (fun x => ∑ y, taggedCfin d L (N ℓ) k M v a s x y * ((ψ y : ℝ) : ℂ))
              ∂(γ ℓ)) C) T hT Q hQ sz hsz τ hτ D ht₀ ε ?_
  intro ℓ ℓ' g hg m t ht hbox hKK hNN e he C hCc hCb
  obtain ⟨f, hf⟩ : ∃ f : L1Torus d (N ℓ) → L1Torus d (N ℓ'), ∀ x μ,
      f x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ')) =
        ((((x μ + ((M * (m + 4) : ℕ) : ZMod (N ℓ))).val : ℕ)) : ZMod (N ℓ')) :=
    exists_residueMap_box
  have hMNℓ : M ∣ N ℓ := hMN ℓ
  have hMNℓ' : M ∣ N ℓ' := hMN ℓ'
  have hbox' : 4 * (m + t) ≤ macK (N ℓ) M := by rw [← hK]; exact hbox
  have he' : ∀ z i, ((z i : ℕ) + (m + 4)) % macK (N ℓ) M ≤ 2 * m + 8 →
      ((e z i : ℕ) + (m + 4)) % macK (N ℓ') M = ((z i : ℕ) + (m + 4)) % macK (N ℓ) M :=
    fun z i _ => he z i
  have hden : 0 < (Real.exp κ - 1) ^ C.card := by
    have : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
    exact pow_pos (by linarith) _
  set x : ℝ := Real.exp (-c₁ * ((M : ℝ) * (2 * (t : ℝ) - 7))) with hx
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  obtain ⟨h1, h2⟩ := hmain hk hMNℓ hMNℓ' hNN ht hbox' hf he' hCc hCb hv0 hv1 ha1 ha2 hmass
  -- the logarithm of the perturbed defect
  have b1 := h1 hsc (hW ℓ g hg) (hW ℓ' g hg) (hε0 ℓ g (C.image (cen ℓ)))
    (hEcl ℓ ℓ' g hg hf C) hρ hρ (han ℓ g hg) (han ℓ' g hg) (hz ℓ g hg) (hz ℓ' g hg)
    (hdet ℓ g hg) (hdet ℓ' g hg)
  -- the logarithm of the unperturbed defect
  have b0 := h1 hsc (hW0 ℓ) (hW0 ℓ') le_rfl (εE := 0)
    (fun x _ y _ => by simp) hρ hρ (han0 ℓ g hg) (han0 ℓ' g hg) (hz0 ℓ g hg) (hz0 ℓ' g hg)
    (hdet0 ℓ g hg) (hdet0 ℓ' g hg)
  -- the cutoff interaction
  have bJ := h2 hρJ (hγfin ℓ) (hγfin ℓ') hBR (hFan ℓ g hg) (hFB ℓ g hg) (hFan ℓ' g hg)
    (hFB ℓ' g hg) (hFm ℓ g hg) (hFm ℓ' g hg) (hFcl ℓ ℓ' g hg hf C hCc hCb he')
    (hγ ℓ ℓ' hf C hCc hCb)
  have key : ∀ a a' b b' c c' : ℂ,
      ‖(a - b + c) - (a' - b' + c')‖ ≤ ‖a - a'‖ + ‖b - b'‖ + ‖c - c'‖ := by
    intro a a' b b' c c'
    calc ‖(a - b + c) - (a' - b' + c')‖ = ‖(a - a') - (b - b') + (c - c')‖ := by congr 1; ring
      _ ≤ ‖(a - a') - (b - b')‖ + ‖c - c'‖ := norm_add_le _ _
      _ ≤ ‖a - a'‖ + ‖b - b'‖ + ‖c - c'‖ := by
        gcongr; exact norm_sub_le _ _
  refine (key _ _ _ _ _ _).trans ?_
  have hg0 : 0 < Real.sqrt (finalGap d L) := by
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact Real.sqrt_pos.2 (finalGap_pos (d := d) hL)
  have hPx : 0 ≤ P * (C₁ * x) := mul_nonneg hP (mul_nonneg hC₁.le hx0)
  set A : ℝ := ((nC * (8 * M + 1) ^ d : ℕ) : ℝ) * (P * (C₁ * x) / Real.sqrt (finalGap d L)) * ρJ
    with hA
  have hA0 : 0 ≤ A := by positivity
  have hJ : ‖coef (fun s : MacIdx d (N ℓ) M → ℂ =>
          ∫ ψ in {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ},
            F ℓ g (fun x => ∑ y, taggedCfin d L (N ℓ) k M v a s x y * ((ψ y : ℝ) : ℂ))
              ∂(γ ℓ)) C -
        coef (fun s' : MacIdx d (N ℓ') M → ℂ =>
          ∫ ψ' in {ψ' : L1Torus d (N ℓ') → ℝ | ∀ y, |ψ' y| ≤ ρJ},
            F ℓ' g (fun x => ∑ y, taggedCfin d L (N ℓ') k M v a s' x y * ((ψ' y : ℝ) : ℂ))
              ∂(γ ℓ')) (C.image e)‖ ≤ Jc * (P * (C₁ * x)) / (Real.exp κ - 1) ^ C.card := by
    refine bJ.trans ?_
    refine div_le_div_of_nonneg_right ?_ hden.le
    have hm0 : 0 ≤ (γ ℓ {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ}).toReal :=
      ENNReal.toReal_nonneg
    calc Lip ℓ g * A * (γ ℓ {ψ : L1Torus d (N ℓ) → ℝ | ∀ y, |ψ y| ≤ ρJ}).toReal
        ≤ Lb * A * mb :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hLipb ℓ g hg) hA0) (hγmass ℓ) hm0
            (mul_nonneg hLb hA0)
      _ = Jc * (P * (C₁ * x)) := by rw [hJc, hA]; field_simp
  refine le_trans (add_le_add (add_le_add b1 b0) hJ) (le_of_eq ?_)
  rw [hJc, hx]
  field_simp
  ring

end Physical

end Balaban.Polymer
