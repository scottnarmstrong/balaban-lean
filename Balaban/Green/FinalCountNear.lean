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

open Classical in
/-- The terms `(j, y, X)` whose read set meets `Rg`: the sum of their sups is at most
`K A |W| E₀`, by `sum_hit_le` on each level. -/
theorem sum_terms_hit_le {Q : Type*} {m₀ K : ℕ} {E₀ κ' A : ℝ} (hE₀ : 0 ≤ E₀) (Rg : Set Q)
    (S' : ℕ → CTorus d' L N₁ m₁ kc → Set (CTorus d' L N₁ m₁ kc) → Set Q)
    (W : Finset (CTorus d' L N₁ m₁ kc))
    (hW : ∀ j, 1 ≤ j → j ≤ K → ∀ y X, IsPolyDom m₀ j X → y ∈ X →
      (∃ x ∈ S' j y X, x ∈ Rg) → ∃ w ∈ W, w ∈ X)
    (hcount : ∀ j, 1 ≤ j → j ≤ K → ∀ w : CTorus d' L N₁ m₁ kc,
      ∑ y ∈ (Finset.univ : Finset (CTorus d' L N₁ m₁ kc)).filter (Aligned (L ^ j)),
        ∑ᶠ X ∈ polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc) m₀ j y,
          (if w ∈ X then E₀ * Real.exp (-κ' * sizeJ m₀ j X) else 0) ≤ A * E₀) :
    ∑ t ∈ (Finset.Icc 1 K).sigma (fun j =>
      ((Finset.univ : Finset (CTorus d' L N₁ m₁ kc)).filter (Aligned (L ^ j))).sigma
        fun y => (Set.toFinite (polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc)
          m₀ j y)).toFinset),
      (if ∃ x ∈ S' t.1 t.2.1 t.2.2, x ∈ Rg then E₀ * Real.exp (-κ' * sizeJ m₀ t.1 t.2.2)
        else 0) ≤ K * A * (W.card : ℝ) * E₀ := by
  rw [sum_terms_eq (m₀ := m₀) (K := K)
    (fun j y X => if ∃ x ∈ S' j y X, x ∈ Rg then E₀ * Real.exp (-κ' * sizeJ m₀ j X) else 0)]
  calc _ ≤ ∑ j ∈ Finset.Icc 1 K, A * (W.card : ℝ) * E₀ := by
        refine Finset.sum_le_sum fun j hj => ?_
        obtain ⟨h1, hjK⟩ := Finset.mem_Icc.1 hj
        exact sum_hit_le hE₀ Rg (S' j) W (fun y X hX hy hh => hW j h1 hjK y X hX hy hh)
          (fun w => hcount j h1 hjK w)
    _ = _ := by rw [Finset.sum_const, Nat.card_Icc]; simp; ring

open Classical in
/-- `sum_terms_hit_le` for a finite set `T` of terms given by its defining equation, a predicate
`hit` and weights `b` given by their defining equivalences. -/
theorem sum_terms_hit_le' {Q : Type*} {m₀ K : ℕ} {E₀ κ' A : ℝ} (hE₀ : 0 ≤ E₀) (Rg : Set Q)
    (S' : ℕ → CTorus d' L N₁ m₁ kc → Set (CTorus d' L N₁ m₁ kc) → Set Q)
    (W : Finset (CTorus d' L N₁ m₁ kc))
    (hW : ∀ j, 1 ≤ j → j ≤ K → ∀ y X, IsPolyDom m₀ j X → y ∈ X →
      (∃ x ∈ S' j y X, x ∈ Rg) → ∃ w ∈ W, w ∈ X)
    (hcount : ∀ j, 1 ≤ j → j ≤ K → ∀ w : CTorus d' L N₁ m₁ kc,
      ∑ y ∈ (Finset.univ : Finset (CTorus d' L N₁ m₁ kc)).filter (Aligned (L ^ j)),
        ∑ᶠ X ∈ polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc) m₀ j y,
          (if w ∈ X then E₀ * Real.exp (-κ' * sizeJ m₀ j X) else 0) ≤ A * E₀)
    (T : Finset (Σ _ : ℕ, Σ _ : CTorus d' L N₁ m₁ kc, Set (CTorus d' L N₁ m₁ kc)))
    (hT : T = (Finset.Icc 1 K).sigma (fun j =>
      ((Finset.univ : Finset (CTorus d' L N₁ m₁ kc)).filter (Aligned (L ^ j))).sigma
        fun y => (Set.toFinite (polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc)
          m₀ j y)).toFinset))
    (hit : (Σ _ : ℕ, Σ _ : CTorus d' L N₁ m₁ kc, Set (CTorus d' L N₁ m₁ kc)) → Prop)
    (hhit : ∀ t, hit t ↔ ∃ x ∈ S' t.1 t.2.1 t.2.2, x ∈ Rg)
    (b : (Σ _ : ℕ, Σ _ : CTorus d' L N₁ m₁ kc, Set (CTorus d' L N₁ m₁ kc)) → ℝ)
    (hb : ∀ t, b t = E₀ * Real.exp (-κ' * sizeJ m₀ t.1 t.2.2)) :
    ∑ t ∈ T, (if hit t then b t else 0) ≤ K * A * (W.card : ℝ) * E₀ := by
  subst hT
  have := sum_terms_hit_le (d' := d') (L := L) (N₁ := N₁) (m₁ := m₁) (kc := kc) hE₀ Rg S' W hW hcount
  refine le_of_eq_of_le (Finset.sum_congr rfl fun t _ => ?_) this
  rw [hb]
  simp only [hhit]

open Classical in
/-- **Summation by the level of first contact.**  If every term `t` of a finite family has a level
`n ≤ Nm` at which it is hit and `c t ≤ g b_t ω_n`, and the weights `b_t` of the terms hit at level
`n` add up to at most `B n`, then `∑_t c_t ≤ g ∑_{n ≤ Nm} ω_n B_n`. -/
theorem sum_by_level {τ : Type*} (T : Finset τ) (Nm : ℕ) (hit : ℕ → τ → Prop) (c b : τ → ℝ)
    (ω B : ℕ → ℝ) {g : ℝ} (hg : 0 ≤ g) (hb : ∀ t, 0 ≤ b t) (hω : ∀ n, 0 ≤ ω n)
    (hone : ∀ t ∈ T, ∃ n ≤ Nm, hit n t ∧ c t ≤ g * (b t * ω n))
    (hB : ∀ n, ∑ t ∈ T, (if hit n t then b t else 0) ≤ B n) :
    ∑ t ∈ T, c t ≤ g * ∑ n ∈ Finset.range (Nm + 1), ω n * B n := by
  have h1 : ∀ t ∈ T, c t ≤ ∑ n ∈ Finset.range (Nm + 1),
      (if hit n t then g * (b t * ω n) else 0) := by
    intro t ht
    obtain ⟨n, hnN, hn, hle⟩ := hone t ht
    refine hle.trans ?_
    have hnn : ∀ m ∈ Finset.range (Nm + 1), 0 ≤ (if hit m t then g * (b t * ω m) else 0) := by
      intro m _
      by_cases hh : hit m t
      · simp only [hh, ite_true]; exact mul_nonneg hg (mul_nonneg (hb t) (hω m))
      · simp only [hh, ite_false]; exact le_rfl
    refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_range.2 (Nat.lt_succ_of_le hnN)))
    simp only [hn, ite_true]; exact le_rfl
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have : ∑ t ∈ T, (if hit n t then g * (b t * ω n) else 0) =
      g * ω n * ∑ t ∈ T, (if hit n t then b t else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> ring
  rw [this]
  calc _ ≤ g * ω n * B n := mul_le_mul_of_nonneg_left (hB n) (mul_nonneg hg (hω n))
    _ = _ := by ring

end Terms

section Class

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ}

open Classical in
/-- **The volume-uniform bound with a decaying lift.**  Replace the strict locality `hΛloc` of the
lift by its near-locality `hnear`: the term `(j, y, X)` of the interaction, as a function of `w`,
varies by at most `E₀ e^{-κ_P d_j(X)} ε(n)` under changes off the read set `S n j y X` (the read set
at distance level `n`).  Let `N` be a level at which every polymer reaches the region of `C`
(`hreach`) and `W n` a finite set of sites that every polymer reaching the region at level `n`
meets (`hW`).  Then for nonempty `C`,
`‖coef J_{F_K} C‖ ≤ γ(box) e^{-(κ-1)|C|} K A E₀ ∑_{n ≤ N} ω_n |W n|`
with `ω_0 = 1`, `ω_n = ε(n-1)` for `n ≥ 1` and `A = L^{(m₀+m₁) d'} c₁ K₀(d', L, P.κ - 1)`
(`hcount_class`).  The constant involves `N` only through the number of terms of the sum. -/
theorem norm_coef_cutoff_class_le_decay (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : Measure (L1Torus d N₀ → ℝ)} {ρ β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β)
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    {d' : ℕ} {R : ℝ} {N₁ m₁ kc N : ℕ} [NeZero N₁] {ϱ : ℝ}
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) < R)
    {P : Consts} {Dom : FieldDom d' L N₁ m₁ kc N ϱ} {Tm : Terms d' L N₁ m₁ kc N ϱ}
    (hT : SFTermClauses P Dom Tm) {K : ℕ} (hK : K ≤ kc)
    {φ₀ : L1Torus d N₀ → ℂ}
    {Λ : ℕ → (L1Torus d N₀ → ℂ) → Fld d' L N₁ m₁ kc N × Fld d' L N₁ m₁ kc N}
    (hΛ : ∀ j, 1 ≤ j → j ≤ K → AnalyticOnNhd ℂ (Λ j) (polydisc φ₀ (fun _ => R)))
    (hsub : ∀ w ∈ polydisc φ₀ (fun _ => R), ∀ j, 1 ≤ j → j ≤ K →
      ∀ X, IsPolyDom P.m₀ j X → Dom.dom j (Tm.gs j X) (Λ j w).1 (Λ j w).2)
    (S : ℕ → ℕ → CTorus d' L N₁ m₁ kc → Set (CTorus d' L N₁ m₁ kc) → Set (L1Torus d N₀))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n)
    (hnear : ∀ n j y X, 1 ≤ j → j ≤ K → IsPolyDom P.m₀ j X → y ∈ X →
      ∀ w ∈ polydisc φ₀ (fun _ => R), ∀ w' ∈ polydisc φ₀ (fun _ => R),
        (∀ x ∈ S n j y X, w x = w' x) →
        ‖Tm.E j y X (Λ j w).1 (Λ j w).2 - Tm.E j y X (Λ j w').1 (Λ j w').2‖ ≤
          P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) * ε n)
    (hE₀ : 0 ≤ P.E₀) (hN : L ^ P.m₀ ∣ N₁) (hκP : aEnt d' L + 2 ≤ P.κ)
    (C : Finset (MacIdx d N₀ M)) (hC : C.Nonempty) (Nm : ℕ)
    (W : ℕ → Finset (CTorus d' L N₁ m₁ kc))
    (hreach : ∀ j, 1 ≤ j → j ≤ K → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
      ∃ n ≤ Nm, ∃ x ∈ S n j y X, x ∈ macRegion d N₀ M C)
    (hW : ∀ n j, 1 ≤ j → j ≤ K → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
      (∃ x ∈ S n j y X, x ∈ macRegion d N₀ M C) → ∃ w ∈ W n, w ∈ X) :
    ‖coef (fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (fun w : L1Torus d N₀ → ℂ => ∑ j ∈ Finset.Icc 1 K,
            Edens P.m₀ Tm j (Λ j w).1 (Λ j w).2)
          (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C‖ ≤
      (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal * Real.exp (-(κ - 1) * C.card) *
        ((K : ℝ) * ((L : ℝ) ^ ((P.m₀ + m₁) * d') * c1 d' L * K0 d' L (P.κ - 1)) * P.E₀ *
          ∑ n ∈ Finset.range (Nm + 1),
            (if n = 0 then (1 : ℝ) else ε (n - 1)) * ((W n).card : ℝ)) := by
  classical
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
  set A : ℝ := (L : ℝ) ^ ((P.m₀ + m₁) * d') * c1 d' L * K0 d' L (P.κ - 1) with hA
  set g : ℝ := (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal * Real.exp (-(κ - 1) * C.card)
    with hg
  have hg0 : 0 ≤ g := mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  set T : Finset (Σ _ : ℕ, Σ _ : CTorus d' L N₁ m₁ kc, Set (CTorus d' L N₁ m₁ kc)) :=
    (Finset.Icc 1 K).sigma fun j =>
      ((Finset.univ : Finset (CTorus d' L N₁ m₁ kc)).filter (Aligned (L ^ j))).sigma
        fun y => (Set.toFinite (polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc)
          P.m₀ j y)).toFinset with hTdef
  have hmem : ∀ t ∈ T, 1 ≤ t.1 ∧ t.1 ≤ K ∧ IsPolyDom P.m₀ t.1 t.2.2 ∧ t.2.1 ∈ t.2.2 := by
    rintro ⟨j, y, X⟩ ht
    simp only [hTdef, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ,
      true_and, Set.Finite.mem_toFinset] at ht
    exact ⟨ht.1.1, ht.1.2, ht.2.2.1, ht.2.2.2⟩
  have hF : ∀ w : L1Torus d N₀ → ℂ, ∑ j ∈ Finset.Icc 1 K, Edens P.m₀ Tm j (Λ j w).1 (Λ j w).2 =
      ∑ t ∈ T, Tm.E t.1 t.2.1 t.2.2 (Λ t.1 w).1 (Λ t.1 w).2 := fun w => by
    rw [hTdef]
    have := sum_terms_eq (d' := d') (L := L) (N₁ := N₁) (m₁ := m₁) (kc := kc) (m₀ := P.m₀) (K := K)
    unfold Edens Eloc
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
  set f : (Σ _ : ℕ, Σ _ : CTorus d' L N₁ m₁ kc, Set (CTorus d' L N₁ m₁ kc)) →
      (L1Torus d N₀ → ℂ) → ℂ := fun t w => Tm.E t.1 t.2.1 t.2.2 (Λ t.1 w).1 (Λ t.1 w).2 with hf
  set b : (Σ _ : ℕ, Σ _ : CTorus d' L N₁ m₁ kc, Set (CTorus d' L N₁ m₁ kc)) → ℝ :=
    fun t => P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ t.1 t.2.2) with hb
  have hfan : ∀ t ∈ T, AnalyticOnNhd ℂ (f t) (polydisc φ₀ (fun _ => R)) := fun t ht w hw => by
    obtain ⟨h1, hjK, hX, hy⟩ := hmem t ht
    exact (hT.analyticE t.1 h1 (hjK.trans hK) t.2.1 t.2.2 hX hy (Λ t.1 w)
      (hsub w hw t.1 h1 hjK t.2.2 hX)).comp (hΛ t.1 h1 hjK w hw)
  have hfB : ∀ t ∈ T, ∀ w ∈ polydisc φ₀ (fun _ => R), ‖f t w‖ ≤ b t := fun t ht w hw => by
    obtain ⟨h1, hjK, hX, hy⟩ := hmem t ht
    exact hT.boundE t.1 h1 (hjK.trans hK) t.2.1 t.2.2 hX hy _ _ (hsub w hw t.1 h1 hjK t.2.2 hX)
  have hb0 : ∀ t, 0 ≤ b t := fun t => mul_nonneg hE₀ (Real.exp_pos _).le
  -- the coefficient of the sum is the sum of the coefficients
  have hint := fun t (ht : t ∈ T) s (hs : s ∈ polydisc (0 : MacIdx d N₀ M → ℂ)
      (fun _ => Real.exp κ)) =>
    integrable_cutoff_integrand (N₀ := N₀) (M := M) (k := k) (L := L) (v := v) (a := a)
      hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hβ hγ hBR (hfan t ht) (hfB t ht) hs
  have hterm := fun t (ht : t ∈ T) => cutoffInteraction_final_phys (N₀ := N₀) (M := M) (k := k)
    (L := L) (v := v) (a := a) hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hβ hγ hBR
    (hfan t ht) (hfB t ht)
  have hsum : ∀ s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ),
      (∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (∑ t ∈ T, f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ))) ∂γ) =
      ∑ t ∈ T, ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ := fun s hs =>
    integral_finsetSum _ fun t ht => hint t ht s hs
  have hlin := coef_sum_linear hR T (fun _ => (1 : ℂ))
    (fun t s => ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
      f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ)
    (fun t ht => (hterm t ht).1) C
  have hcongr := coef_congr_polydisc hR (f := fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (∑ t ∈ T, f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ))) ∂γ)
    (g := fun s => ∑ t ∈ T, (1 : ℂ) * (∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
      f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ))
    (fun s hs => by simp only [one_mul]; exact hsum s hs) C
  -- the bound of one term
  set hhit : ℕ → (Σ _ : ℕ, Σ _ : CTorus d' L N₁ m₁ kc, Set (CTorus d' L N₁ m₁ kc)) → Prop :=
    fun n t => ∃ x ∈ S n t.1 t.2.1 t.2.2, x ∈ macRegion d N₀ M C with hhitdef
  have hone : ∀ t ∈ T, ∃ n ≤ Nm, hhit n t ∧
      ‖coef (fun s : MacIdx d N₀ M → ℂ =>
        ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
          f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C‖ ≤
        g * (b t * (if n = 0 then (1 : ℝ) else ε (n - 1))) := by
    intro t ht
    obtain ⟨h1, hjK, hX, hy⟩ := hmem t ht
    have hex : ∃ n, hhit n t := by
      obtain ⟨n, -, hn⟩ := hreach t.1 h1 hjK t.2.1 t.2.2 hX hy
      exact ⟨n, hn⟩
    obtain ⟨n, hnN, hn⟩ := hreach t.1 h1 hjK t.2.1 t.2.2 hX hy
    have hn0 := Nat.find_min' hex hn
    refine ⟨Nat.find hex, hn0.trans hnN, Nat.find_spec hex, ?_⟩
    rcases hz : Nat.find hex with _ | m
    · simp only [ite_true, mul_one]
      refine ((hterm t ht).2.2.2.2.2 C).trans (le_of_eq ?_)
      simp only [hg, hb]; ring
    · have hmiss : ∀ x ∈ S m t.1 t.2.1 t.2.2, x ∉ macRegion d N₀ M C := fun x hx hxr =>
        Nat.find_min hex (by omega) ⟨x, hx, hxr⟩
      have := norm_coef_cutoff_le_of_near_read (N₀ := N₀) (M := M) (k := k) (L := L) (v := v)
        (a := a) hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hβ hγ hBR (hfan t ht) (hfB t ht)
        (S := S m t.1 t.2.1 t.2.2) (δ := b t * ε m)
        (fun w hw w' hw' hww => by
          have := hnear m t.1 t.2.1 t.2.2 h1 hjK hX hy w hw w' hw' hww
          simpa only [hf, hb, mul_comm, mul_left_comm, mul_assoc] using this)
        hC hmiss
      simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
      refine this.trans (le_of_eq ?_)
      simp only [hg]; ring
  have hω : ∀ n : ℕ, 0 ≤ (if n = 0 then (1 : ℝ) else ε (n - 1)) := fun n => by
    by_cases h : n = 0
    · simp only [h, ite_true]; exact zero_le_one
    · simp only [h, ite_false]; exact hε _
  have hsum2 : ∀ n, ∑ t ∈ T, (if hhit n t then b t else 0) ≤ K * A * (W n).card * P.E₀ :=
    fun n => by
      convert sum_terms_hit_le' (d' := d') (L := L) (N₁ := N₁) (m₁ := m₁) (kc := kc) hE₀ (macRegion d N₀ M C) (S n) (W n)
        (fun j h1 hjK y X hX hy hh => hW n j h1 hjK y X hX hy hh)
        (fun j h1 hjK w => hcount_class (hjK.trans hK) hN hE₀ hκP w) T hTdef (hhit n)
        (fun t => Iff.rfl) b (fun t => rfl) using 3
  have hfin := sum_by_level T Nm hhit
    (fun t => ‖coef (fun s : MacIdx d N₀ M → ℂ =>
        ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
          f t (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C‖)
    b (fun n => if n = 0 then (1 : ℝ) else ε (n - 1)) (fun n => K * A * (W n).card * P.E₀)
    hg0 hb0 hω hone (fun n => by convert hsum2 n using 3)
  simp only [hF]
  rw [hcongr, hlin]
  refine (norm_sum_le _ _).trans ?_
  simp only [one_mul]
  refine hfin.trans (le_of_eq ?_)
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

end Class

end Balaban.Green
