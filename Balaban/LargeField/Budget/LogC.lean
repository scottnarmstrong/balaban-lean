module

public import Balaban.LargeField.Budget.Injective

/-!
# The combinatoric factor of a localized history (Part II, Definition II.5.11)

`LocalHistory.logC k a` is `log C_k(Z, 𝔞)` read off the localized history `a = 𝔥_k(Z)`.  Unrolling
`log C_{j+1}(Z') = ∑_Y log C_j(Y) + |Z_j ∩ Z'|_{#j} + (5/4)|Z^c_j ∩ Z'|_{#j}` along the lineage,
`log C_k = ∑_{j<k} (n₁(j) + (5/4) n₂(j))` with `n₁(j) = |Lin_j(Z)|_{#j}` and
`n₁(j) + n₂(j) = |Lin_{j+1}(Z)|_{#j}`.  In terms of the number `N_j` of sites of the record `Z_j`
(`N_j = (L^j M)^d |Lin_j(Z)|`):
`log C_k = ∑_{j<k} (5 N_{j+1} - N_j) / (4 (L^j M)^d)`.

* `logC_succ`: the recursion of Definition II.5.11 for the localized history of a component.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

/-- `log C_k(Z, 𝔞)` read off the localized history `a`:
`∑_{j<k} (5 N_{j+1} - N_j) / (4 (L^j M)^d)`, `N_j` the number of sites of the record `Z_j`. -/
noncomputable def LocalHistory.logC {S : Setting} {n : ℕ → ℕ} {M K : ℕ} (k : ℕ)
    (a : LocalHistory S n M K) : ℝ :=
  ∑ j ∈ Finset.range k, (5 * ((a.Z (j + 1)).ncard : ℝ) - (a.Z j).ncard) /
    (4 * (((S.L ^ j * M) ^ S.d : ℕ) : ℝ))

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0) {M K k : ℕ} [NeZero M]

theorem lin_disjoint (j : ℕ) {c c' : H.Comp k} (hne : c ≠ c') :
    Disjoint (H.lin j k c) (H.lin j k c') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨Y, hd, hxY⟩ := mem_lin.mp hx
  obtain ⟨Y', hd', hxY'⟩ := mem_lin.mp hx'
  have : Y = Y' := Subtype.ext (comp_eq_of_mem Y.2 Y'.2 hxY hxY')
  subst this
  exact hne (hd.unique hd')

theorem card_lin_succ (j : ℕ) (hjk : j ≤ k) (Z' : H.Comp (k + 1)) :
    (H.lin j (k + 1) Z').card = ∑ c ∈ H.parts k Z', (H.lin j k c).card := by
  rw [H.lin_succ_decomp k hjk, Finset.card_biUnion]
  intro c _ c' _ hne
  exact H.lin_disjoint j hne

theorem sum_ncard_Z (hkK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) {j : ℕ} (hj : j ≤ k) :
    (((localHistory H M K (k + 1) Z').Z j).ncard : ℝ) =
      ∑ c ∈ H.parts k Z', (((localHistory H M K k c).Z j).ncard : ℝ) := by
  rw [H.ncard_localHistory_Z Z' hkK (by omega)]
  rw [Finset.sum_congr rfl (fun c _ => by rw [H.ncard_localHistory_Z c (by omega) hj])]
  rw [H.card_lin_succ j hj Z']
  push_cast
  rw [Finset.mul_sum]

/-- **The recursion of Definition II.5.11 for the combinatoric factors** (P6 (3.11)): for a
component `Z'` of `Z^pre_{k+1}`,
`log C_{k+1}(Z') = ∑_Y log C_k(Y) + |Z_k ∩ Z'|_{#k} + (5/4) |Z^c_k ∩ Z'|_{#k}`
(`|Z_k ∩ Z'|_{#k} = |S|`, `|Z^c_k ∩ Z'|_{#k} = L^d |Z'|_# - |S|`). -/
theorem logC_succ (hkK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) :
    (localHistory H M K (k + 1) Z').logC (k + 1) =
      ∑ c ∈ H.parts k Z', (localHistory H M K k c).logC k +
        (5 * ((S.L : ℝ) ^ S.d * Z'.1.card) - (H.oldCubes k Z').card) / 4 := by
  have hLpos : (0 : ℝ) < S.L := by
    have := H.F.ok.two_le_L
    exact_mod_cast (by omega : 0 < S.L)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  unfold LocalHistory.logC
  rw [Finset.sum_range_succ]
  congr 1
  · -- the terms j < k
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j < k := Finset.mem_range.mp hj
    rw [H.sum_ncard_Z hkK Z' hjk.le, H.sum_ncard_Z hkK Z' (show j + 1 ≤ k by omega)]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  · -- the last term
    rw [H.ncard_localHistory_Z Z' hkK le_rfl, H.ncard_localHistory_Z Z' hkK (by omega),
      H.lin_succ_self, lin_self]
    have hc : (0 : ℝ) < (((S.L ^ k * M) ^ S.d : ℕ) : ℝ) := by
      have := H.F.ok.two_le_L
      have : 0 < (S.L ^ k * M) ^ S.d := by
        have := NeZero.pos M
        have : 0 < S.L := by omega
        positivity
      exact_mod_cast this
    have e : (((S.L ^ (k + 1) * M) ^ S.d : ℕ) : ℝ) = (S.L : ℝ) ^ S.d * (((S.L ^ k * M) ^ S.d : ℕ) : ℝ) := by
      push_cast; ring
    push_cast
    push_cast at e
    rw [e]
    field_simp

end RegionHistory

end Balaban.LargeField
