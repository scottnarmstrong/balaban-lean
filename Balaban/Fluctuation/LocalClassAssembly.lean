/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassCov
public import Balaban.Fluctuation.RootPavingMap

/-!
# The E-part of the local class at the new level: distribution over the sites

The new terms of the local class at the top level `K` are indexed by a polymer `Y ∈ 𝒟_K` and a
site `y`.  For a family `S Y` of polymer terms (in the application, the average over the paving
group of the completed sums over the old labels, `xiFieldDom_avg_completion`), the terms
distributed uniformly over the `L^K`-aligned sites of `Y`,

`E(y, Y) = |Y ∩ Λ_K|⁻¹ S(Y)` for `y ∈ Y`, `0` otherwise,

satisfy:

* `assembly_eucE`: the clause `eucE` (`E(blockBase (r y), r Y)(r Ψ, r h) = E(y, Y)(Ψ, h)` for the
  paving group), for all pairs of fields, from the all-field covariance of `S`; the number of
  aligned sites is invariant (`card_aligned_image_paving`);
* `assembly_local`: the clause `localE` from that of `S`;
* `assembly_norm_le`: `‖E(y, Y)‖ ≤ ‖S(Y)‖` (the clause `boundE` transfers with the same `E₀`);
* `assembly_Edens`: the density `Σ_{y ∈ Λ_K} Σ_{Y ∋ y} E(y, Y) = Σ_{Y ∈ 𝒟_K} S(Y)`;
* `boundE_paving_invariant`: the bound `E₀ e^{-κ d_K(Y)}` of the clause `boundE` is invariant under
  the paving group, so it passes to the group average (`avgTerm_bound`) with the same `E₀`
  (`E₀ ≥ γ(K) ρ_E c₁ (L^K M)^d` of `norm_sum_evTerm_le_boundE` for the sum over the old labels).

The clause `eucEloc` is not termwise (CLASS-RULINGS Q-A): the full level-`K` group does not
preserve the paving; it is not treated here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6 Finset

section Assembly

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

theorem cbase_eq_self_of_aligned {n a : ℕ} [NeZero n] {b : Torus d n} (hb : Aligned a b) :
    cbase a b = b := by
  rw [cbase_eq_sub]
  have : (fun μ => (b μ).val % a) = 0 := funext fun μ => hb μ
  rw [this, natT_zero, sub_zero]

open Classical in
/-- **The number of aligned sites of a polymer is invariant under the paving group.** -/
theorem card_aligned_image_paving (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) :
    ((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
        (fun z => z ∈ r '' Y ∧ Aligned (L ^ K) z)).card =
      ((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
        (fun z => z ∈ Y ∧ Aligned (L ^ K) z)).card := by
  have hY' : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (r '' Y) :=
    (isPolyDom_image_iff hN hr Y).2 hY
  have hri : r⁻¹ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K := inv_mem hr
  have hYY : (⇑(r⁻¹)) '' (r '' Y) = Y := by
    rw [Set.image_image]; simp [Equiv.Perm.inv_def]
  symm
  refine Finset.card_nbij' (fun z => blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r z))
    (fun w => blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r⁻¹ w))
    (fun z hz => ?_) (fun w hw => ?_) (fun z hz => ?_) (fun w hw => ?_)
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
    exact ⟨blockBase_mem_image hr (blockUnion_of_isPolyDom hN hY) hz.1, aligned_cbase _⟩
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
    have h := blockBase_mem_image hri (blockUnion_of_isPolyDom hN hY') hw.1
    rw [hYY] at h
    exact ⟨h, aligned_cbase _⟩
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz
    show blockBase L K (r⁻¹ (blockBase L K (r z))) = z
    rw [blockBase_inv_blockBase hr z]
    exact cbase_eq_self_of_aligned hz.2
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw
    show blockBase L K (r (blockBase L K (r⁻¹ w))) = w
    have := blockBase_inv_blockBase hri w
    rw [inv_inv] at this
    rw [this]
    exact cbase_eq_self_of_aligned hw.2

open Classical in
/-- **The clause `eucE` for the uniformly distributed terms.**  If the polymer terms `S` are
covariant under the paving group for all pairs of fields, the terms
`E(y, Y) = |Y ∩ Λ_K|⁻¹ S(Y)` (`y ∈ Y`) satisfy
`E(blockBase (r y), r Y)(r Ψ, r h) = E(y, Y)(Ψ, h)` for every polymer `Y ∈ 𝒟_K` and `y ∈ Y`. -/
theorem assembly_eucE (hN : L ^ m₀ ∣ N₁)
    (S : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → ℂ)
    (hS : ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K, ∀ Y
      (p : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N),
      S (r '' Y) (actField r p.1, actField r p.2) = S Y p)
    (E : CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N →
      Fld d L N₁ m₁ K N → ℂ)
    (hE : ∀ y Y Ψ h, E y Y Ψ h = if y ∈ Y then
      ((((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
        (fun z => z ∈ Y ∧ Aligned (L ^ K) z)).card : ℕ) : ℂ)⁻¹ * S Y (Ψ, h) else 0)
    {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) {y : CTorus d L N₁ m₁ K}
    (hy : y ∈ Y) (Ψ h : Fld d L N₁ m₁ K N) :
    E (blockBase L K (r y)) (r '' Y) (actField r Ψ) (actField r h) = E y Y Ψ h := by
  have hmem := blockBase_mem_image hr (blockUnion_of_isPolyDom hN hY) hy
  rw [hE, hE]
  simp only [hmem, hy, ↓reduceIte]
  rw [card_aligned_image_paving hN hr hY]
  exact congrArg _ (hS r hr Y (Ψ, h))

open Classical in
/-- **The clause `localE` for the uniformly distributed terms**, from that of `S`. -/
theorem assembly_local
    (S : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → ℂ)
    (hSl : ∀ Y (Ψ Ψ' h h' : Fld d L N₁ m₁ K N), (∀ x ∈ Y, Ψ x = Ψ' x ∧ h x = h' x) →
      S Y (Ψ, h) = S Y (Ψ', h'))
    (E : CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N →
      Fld d L N₁ m₁ K N → ℂ)
    (hE : ∀ y Y Ψ h, E y Y Ψ h = if y ∈ Y then
      ((((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
        (fun z => z ∈ Y ∧ Aligned (L ^ K) z)).card : ℕ) : ℂ)⁻¹ * S Y (Ψ, h) else 0)
    (y : CTorus d L N₁ m₁ K) (Y : Set (CTorus d L N₁ m₁ K)) (Ψ Ψ' h h' : Fld d L N₁ m₁ K N)
    (hY : ∀ x ∈ Y, Ψ x = Ψ' x ∧ h x = h' x) : E y Y Ψ h = E y Y Ψ' h' := by
  rw [hE, hE, hSl Y Ψ Ψ' h h' hY]

open Classical in
/-- **The bound of the uniformly distributed terms**: `‖E(y, Y)‖ ≤ ‖S(Y)‖`. -/
theorem assembly_norm_le
    (S : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → ℂ)
    (E : CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N →
      Fld d L N₁ m₁ K N → ℂ)
    (hE : ∀ y Y Ψ h, E y Y Ψ h = if y ∈ Y then
      ((((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
        (fun z => z ∈ Y ∧ Aligned (L ^ K) z)).card : ℕ) : ℂ)⁻¹ * S Y (Ψ, h) else 0)
    (y : CTorus d L N₁ m₁ K) (Y : Set (CTorus d L N₁ m₁ K)) (Ψ h : Fld d L N₁ m₁ K N) :
    ‖E y Y Ψ h‖ ≤ ‖S Y (Ψ, h)‖ := by
  rw [hE]
  split_ifs
  · rw [norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [norm_inv, Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos ((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
      (fun z => z ∈ Y ∧ Aligned (L ^ K) z)).card with h0 | h0
    · rw [h0]; simp
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast h0)
  · simp

open Classical in
/-- **The density of the uniformly distributed terms**: for terms of the class at the level `K`
given by `E`, `Σ_{y ∈ Λ_K} ℰ^{(K)}(y) = Σ_{Y ∈ 𝒟_K} S(Y)`. -/
theorem assembly_Edens (hN : L ^ m₀ ∣ N₁) {ϱ : ℝ} (Tm : Terms d L N₁ m₁ K N ϱ)
    (S : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → ℂ)
    (hE : ∀ y Y Ψ h, Tm.E K y Y Ψ h = if y ∈ Y then
      ((((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
        (fun z => z ∈ Y ∧ Aligned (L ^ K) z)).card : ℕ) : ℂ)⁻¹ * S Y (Ψ, h) else 0)
    (Ψ h : Fld d L N₁ m₁ K N) :
    Edens m₀ Tm K Ψ h =
      ∑ᶠ Y ∈ {Y : Set (CTorus d L N₁ m₁ K) |
        IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y}, S Y (Ψ, h) := by
  set PP : Set (Set (CTorus d L N₁ m₁ K)) := {Y : Set (CTorus d L N₁ m₁ K) |
    IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y} with hPP
  have hfin : PP.Finite := Set.toFinite _
  set A : Finset (CTorus d L N₁ m₁ K) := (Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
    (Aligned (L ^ K)) with hA
  have hloc : ∀ y, Eloc m₀ Tm K y Ψ h = ∑ Y ∈ hfin.toFinset.filter (fun Y => y ∈ Y),
      Tm.E K y Y Ψ h := by
    intro y
    unfold Eloc
    have hfin' : (polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K y).Finite := Set.toFinite _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin']
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext Y
    simp [polysAt, hPP]
  unfold Edens
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp_rw [hloc]
  rw [← hA]
  rw [Finset.sum_comm' (t' := hfin.toFinset)
    (s' := fun Y => A.filter (fun y => y ∈ Y)) (fun y Y => by
      simp only [Finset.mem_filter]
      tauto)]
  refine Finset.sum_congr rfl fun Y hY => ?_
  have hYp : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y := by
    simpa [hPP] using hY
  have hcard : (A.filter (fun y => y ∈ Y)).card =
      ((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
        (fun z => z ∈ Y ∧ Aligned (L ^ K) z)).card := by
    congr 1
    ext z
    simp [hA, and_comm]
  have hpos : 0 < (A.filter (fun y => y ∈ Y)).card := by
    obtain ⟨x, hx⟩ := hYp.1
    refine Finset.card_pos.2 ⟨blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K x, ?_⟩
    simp only [Finset.mem_filter, hA, Finset.mem_univ, true_and]
    refine ⟨aligned_cbase _, blockUnion_of_isPolyDom hN hYp x hx _ ?_⟩
    exact cbase_eq_self_of_aligned (aligned_cbase _)
  have hterm : ∀ y ∈ A.filter (fun y => y ∈ Y), Tm.E K y Y Ψ h =
      ((((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
        (fun z => z ∈ Y ∧ Aligned (L ^ K) z)).card : ℕ) : ℂ)⁻¹ * S Y (Ψ, h) := by
    intro y hy
    rw [hE]
    simp only [(Finset.mem_filter.1 hy).2, ↓reduceIte]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, ← hcard, nsmul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast hpos.ne'), one_mul]

/-- **The bound of the class is invariant under the paving group**: `E₀ e^{-κ d_K(r Y)} =
E₀ e^{-κ d_K(Y)}` (`sizeJ_image`), so `avgTerm_bound` transfers the clause `boundE` to the group
average with the same `E₀`. -/
theorem boundE_paving_invariant (hN : L ^ m₀ ∣ N₁) (E₀ κ : ℝ) :
    ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K,
      ∀ Y : Set (CTorus d L N₁ m₁ K),
        E₀ * Real.exp (-κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (r '' Y)) =
          E₀ * Real.exp (-κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) := by
  intro r hr Y
  rw [sizeJ_image hN hr Y]

end Assembly

end Balaban.Fluctuation
