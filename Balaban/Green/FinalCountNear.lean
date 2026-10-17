/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLocalBound
public import Balaban.Green.FinalTaggedTorusClose
public import Balaban.Green.FinalCountPolymers
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Near-locality of the coefficient of the cut integral (blocker 5)

`coef_cutoff_eq_zero_of_read` says: if `G` reads the field only on `S` and `S` misses the region
`Y(C)` of `C ≠ ∅`, then the coefficient of the cut integral vanishes.  The quantitative version
replaces "reads only on `S`" by "varies by at most `δ` under changes off `S`" (on the polydisc):

* `norm_coef_cutoff_le_of_near_read`: then `‖coef J_G C‖ ≤ γ(box) δ e^{-(κ-1)|C|}`.
* `norm_coef_cutoff_term_le_near`: the two bounds for one term, by its sup and by its variation.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban.Localization Balaban.Analysis Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation

namespace Balaban.Green

section Near

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ}

open Classical in
/-- **Near-locality of the coefficient.**  Let `f` be analytic and bounded on the polydisc of radius
`Rphys` around `φ₀`, and suppose that it varies by at most `δ` under changes off `S`:
`‖f w - f w'‖ ≤ δ` for `w, w'` in the polydisc that agree on `S`.  If `S` misses the region `Y(C)`
of a nonempty `C`, then `‖coef J_f C‖ ≤ γ(box) δ e^{-(κ-1)|C|}`.  For `δ = 0` this is
`coef_cutoff_eq_zero_of_read`. -/
theorem norm_coef_cutoff_le_of_near_read (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : Measure (L1Torus d N₀ → ℝ)} {ρ Rphys B' δ β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β)
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) < Rphys)
    {f : (L1Torus d N₀ → ℂ) → ℂ} {φ₀ : L1Torus d N₀ → ℂ} {S : Set (L1Torus d N₀)}
    (hf : AnalyticOnNhd ℂ f (polydisc φ₀ (fun _ => Rphys)))
    (hfB : ∀ w ∈ polydisc φ₀ (fun _ => Rphys), ‖f w‖ ≤ B')
    (hnear : ∀ w ∈ polydisc φ₀ (fun _ => Rphys), ∀ w' ∈ polydisc φ₀ (fun _ => Rphys),
      (∀ x ∈ S, w x = w' x) → ‖f w - f w'‖ ≤ δ)
    {C : Finset (MacIdx d N₀ M)} (hC : C.Nonempty) (hS : ∀ x ∈ S, x ∉ macRegion d N₀ M C) :
    ‖coef (fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        f (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C‖ ≤
      (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal * δ * Real.exp (-(κ - 1) * C.card) := by
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
  -- the projection onto the field on `S`
  set π : (L1Torus d N₀ → ℂ) → (L1Torus d N₀ → ℂ) := fun w x => if x ∈ S then w x else φ₀ x
    with hπ
  have hπan : ∀ w, AnalyticAt ℂ π w := fun w => by
    refine analyticAt_pi_iff.2 fun x => ?_
    by_cases hx : x ∈ S
    · simp only [hx, ite_true]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : L1Torus d N₀ => ℂ) x).analyticAt w
    · simp only [hx, ite_false]
      exact analyticAt_const
  have hπmem : ∀ w ∈ polydisc φ₀ (fun _ => Rphys), π w ∈ polydisc φ₀ (fun _ => Rphys) := by
    intro w hw x
    by_cases hx : x ∈ S
    · simpa [hπ, hx] using hw x
    · have h0 : 0 < Rphys := by simpa using hw x |>.trans_le' (norm_nonneg _)
      simpa [hπ, hx] using h0
  have hπS : ∀ w, ∀ x ∈ S, π w x = w x := fun w x hx => by simp [hπ, hx]
  -- the local part `f ∘ π` and the remainder
  have hf' : AnalyticOnNhd ℂ (fun w => f (π w)) (polydisc φ₀ (fun _ => Rphys)) :=
    fun w hw => (hf (π w) (hπmem w hw)).comp (hπan w)
  have hf'B : ∀ w ∈ polydisc φ₀ (fun _ => Rphys), ‖f (π w)‖ ≤ B' :=
    fun w hw => hfB _ (hπmem w hw)
  have hH : AnalyticOnNhd ℂ (fun w => f (π w) - f w) (polydisc φ₀ (fun _ => Rphys)) :=
    hf'.sub hf
  have hHB : ∀ w ∈ polydisc φ₀ (fun _ => Rphys), ‖f (π w) - f w‖ ≤ δ := fun w hw => by
    have := hnear (π w) (hπmem w hw) w hw (fun x hx => hπS w x hx)
    exact this
  have hloc : ∀ w w' : L1Torus d N₀ → ℂ, (∀ x ∈ S, w x = w' x) → f (π w) = f (π w') := by
    intro w w' h
    congr 1
    funext x
    by_cases hx : x ∈ S
    · simp [hπ, hx, h x hx]
    · simp [hπ, hx]
  have h1 := cutoffInteraction_final_phys (N₀ := N₀) (M := M) (k := k) (L := L) (v := v) (a := a)
    hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hβ hγ hBR hf' hf'B
  have h2 := cutoffInteraction_final_phys (N₀ := N₀) (M := M) (k := k) (L := L) (v := v) (a := a)
    hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hβ hγ hBR hH hHB
  have hz := coef_cutoff_eq_zero_of_read (N₀ := N₀) (M := M) (k := k) (L := L) (v := v) (a := a)
    (γ := γ) (ρ := ρ) (β := β) (φ₀ := φ₀) hd hM hloc hC hS
  have hsub : ∀ s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ),
      (∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        f (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) =
      (∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        f (π (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ))) ∂γ) -
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (f (π (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ))) -
          f (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ))) ∂γ := by
    intro s hs
    rw [← integral_sub]
    · simp
    · exact integrable_cutoff_integrand hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hβ hγ hBR
        hf' hf'B hs
    · exact integrable_cutoff_integrand hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hβ hγ hBR
        hH hHB hs
  rw [coef_congr_polydisc hR hsub, coef_sub_open hR h1.1 h2.1, hz, zero_sub, norm_neg]
  calc _ ≤ _ := h2.2.2.2.2.2 C
    _ = _ := by ring

end Near

section Terms

variable {d' L N₁ m₁ kc : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- The sum over the indexed terms `(j, y, X)` as the iterated sum over levels, aligned sites and
polymers through the site. -/
theorem sum_terms_eq {m₀ K : ℕ} (φ : ℕ → CTorus d' L N₁ m₁ kc → Set (CTorus d' L N₁ m₁ kc) → ℝ) :
    ∑ t ∈ (Finset.Icc 1 K).sigma (fun j =>
      ((Finset.univ : Finset (CTorus d' L N₁ m₁ kc)).filter (Aligned (L ^ j))).sigma
        fun y => (Set.toFinite (polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc)
          m₀ j y)).toFinset), φ t.1 t.2.1 t.2.2 =
    ∑ j ∈ Finset.Icc 1 K,
      ∑ y ∈ (Finset.univ : Finset (CTorus d' L N₁ m₁ kc)).filter (Aligned (L ^ j)),
        ∑ᶠ X ∈ polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc) m₀ j y, φ j y X := by
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]

open Classical in
/-- **Terms whose read set reaches a region.**  If every polymer whose read set `S' y X` meets
`Rg` meets `W`, and the polymer count at every site is at most `A E₀`, then the sum of the sups
`E₀ e^{-κ' d_j(X)}` over the polymers (through aligned sites) whose read set meets `Rg` is at most
`A |W| E₀`. -/
theorem sum_hit_le {Q : Type*} {m₀ j : ℕ} {E₀ κ' A : ℝ} (hE₀ : 0 ≤ E₀) (Rg : Set Q)
    (S' : CTorus d' L N₁ m₁ kc → Set (CTorus d' L N₁ m₁ kc) → Set Q)
    (W : Finset (CTorus d' L N₁ m₁ kc))
    (hW : ∀ y X, IsPolyDom m₀ j X → y ∈ X → (∃ x ∈ S' y X, x ∈ Rg) → ∃ w ∈ W, w ∈ X)
    (hcount : ∀ w : CTorus d' L N₁ m₁ kc,
      ∑ y ∈ (Finset.univ : Finset (CTorus d' L N₁ m₁ kc)).filter (Aligned (L ^ j)),
        ∑ᶠ X ∈ polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc) m₀ j y,
          (if w ∈ X then E₀ * Real.exp (-κ' * sizeJ m₀ j X) else 0) ≤ A * E₀) :
    ∑ y ∈ (Finset.univ : Finset (CTorus d' L N₁ m₁ kc)).filter (Aligned (L ^ j)),
      ∑ᶠ X ∈ polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc) m₀ j y,
        (if ∃ x ∈ S' y X, x ∈ Rg then E₀ * Real.exp (-κ' * sizeJ m₀ j X) else 0) ≤
      A * (W.card : ℝ) * E₀ := by
  have hb : ∀ X : Set (CTorus d' L N₁ m₁ kc), 0 ≤ E₀ * Real.exp (-κ' * sizeJ m₀ j X) :=
    fun X => mul_nonneg hE₀ (Real.exp_pos _).le
  have hpt : ∀ y, ∑ᶠ X ∈ polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc) m₀ j y,
      (if ∃ x ∈ S' y X, x ∈ Rg then E₀ * Real.exp (-κ' * sizeJ m₀ j X) else 0) ≤
      ∑ w ∈ W, ∑ᶠ X ∈ polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc) m₀ j y,
        (if w ∈ X then E₀ * Real.exp (-κ' * sizeJ m₀ j X) else 0) := fun y => by
    have hfin := Set.toFinite (polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc) m₀ j y)
    simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun X hX => ?_
    have hX' := hfin.mem_toFinset.1 hX
    have hnn : ∀ w, 0 ≤ (if w ∈ X then E₀ * Real.exp (-κ' * sizeJ m₀ j X) else 0) :=
      fun w => by split_ifs; exacts [hb X, le_rfl]
    split_ifs with hn
    · obtain ⟨w, hwW, hwX⟩ := hW y X hX'.1 hX'.2 hn
      refine le_trans ?_ (Finset.single_le_sum (fun w _ => hnn w) hwW)
      simp [hwX]
    · exact Finset.sum_nonneg fun w _ => hnn w
  calc _ ≤ ∑ y ∈ (Finset.univ : Finset (CTorus d' L N₁ m₁ kc)).filter (Aligned (L ^ j)),
        ∑ w ∈ W, ∑ᶠ X ∈ polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc) m₀ j y,
          (if w ∈ X then E₀ * Real.exp (-κ' * sizeJ m₀ j X) else 0) :=
        Finset.sum_le_sum fun y _ => hpt y
    _ = ∑ w ∈ W, ∑ y ∈ (Finset.univ : Finset (CTorus d' L N₁ m₁ kc)).filter (Aligned (L ^ j)),
        ∑ᶠ X ∈ polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc) m₀ j y,
          (if w ∈ X then E₀ * Real.exp (-κ' * sizeJ m₀ j X) else 0) := Finset.sum_comm
    _ ≤ ∑ _w ∈ W, A * E₀ := Finset.sum_le_sum fun w _ => hcount w
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end Terms

end Balaban.Green
