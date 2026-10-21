/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.CorrKappa
public import Balaban.LargeField.Background.TwoTorusRoom
public import Balaban.LargeField.Background.TwoTorusQuietCubes

/-!
# The hypotheses of the comparison of two tori, from the clause of `LFCoherent`

For components `Z₁`, `Z₂` of `Z^pre_{j+1}` of two region histories whose localized histories
correspond (`HistCorr`) and whose sets `V` correspond (`SetCorr`), the lineages and the new cubes
correspond (`linCorr_of_histCorr`), the tori have at least `32` cubes of the scale `j + 1` per
side and the sites of the components have the margin of one cube (`room_margin_of_V`), so that
the comparison of `CorrBook` and `CorrKappa` applies (`corr_of_V`).
-/

@[expose] public section

open Balaban Balaban.LargeField

set_option linter.unusedSectionVars false

namespace Balaban.RootFSpine

theorem SetCorr.union' {d ℓ₁ ℓ₂ : ℕ} {c : Fin d → ℤ} {A₁ B₁ : Set (Torus d ℓ₁)}
    {A₂ B₂ : Set (Torus d ℓ₂)} (hA : SetCorr c A₁ A₂) (hB : SetCorr c B₁ B₂) :
    SetCorr c (A₁ ∪ B₁) (A₂ ∪ B₂) :=
  ⟨fun x hx => hx.elim (hA.1 x) (hB.1 x), fun x hx => hx.elim (hA.2.1 x) (hB.2.1 x),
    fun x₁ x₂ h => by simp only [Set.mem_union]; rw [hA.2.2 x₁ x₂ h, hB.2.2 x₁ x₂ h]⟩

section FromHist

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K}

open RegionHistory

theorem fineSet_lin_inter_new {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k) {j : ℕ} (hj : j < k) :
    fineSet (S := S) (n := n) M K (j + 1) ((H.lin (j + 1) k Z ∩ H.newCubes (j + 1) : Finset _) : Set _) =
      (H.localHistory M K k Z).P j ∪ (H.localHistory M K k Z).Q j ∪ (H.localHistory M K k Z).R j ∪
        (H.localHistory M K k Z).Sset j := by
  obtain ⟨a1, a2, a3, a4⟩ := localHistory_new (H := H) (M := M) Z hkK hj
  rw [a1, a2, a3, a4]
  ext x
  simp only [fineSet, Finset.coe_inter, Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq,
    Finset.mem_coe, RegionHistory.newCubes, mem_finOf]
  simp only [RegionStep.newCubes, Region.newCubes, Set.mem_union]
  tauto


variable {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {H₁ : RegionHistory S n₁ R k0 K}
  {H₂ : RegionHistory S n₂ R k0 K}

/-- **Corresponding localized histories have corresponding lineages and new cubes.** -/
theorem linCorr_of_histCorr {cc : Fin S.d → ℤ} {k : ℕ} (hkK : k ≤ K) {Z₁ : H₁.Comp k}
    {Z₂ : H₂.Comp k}
    (hH : HistCorr cc (H₁.localHistory M K k Z₁) (H₂.localHistory M K k Z₂)) :
    LinCorr M H₁ H₂ cc k Z₁ Z₂ := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have := (hH j).1
    rw [localHistory_Z _ hkK hj, localHistory_Z _ hkK hj] at this
    exact this
  · have h := (hH j)
    unfold FCorr
    rw [fineSet_lin_inter_new hkK Z₁ hj, fineSet_lin_inter_new hkK Z₂ hj]
    exact ((h.2.1.union' h.2.2.1).union' h.2.2.2.1).union' h.2.2.2.2.1


/-- **Room and margin from the containment of `V` in the box.**  If the sites of `V` of the
localized history of a component `Z` of `Z^pre_{j+1}` lie in the box, then the torus has at least
`32` cubes of the scale `j + 1` per side, and the sites of `Z` have the margin of one cube. -/
theorem room_margin_of_V {n : ℕ → ℕ} [∀ k, NeZero (n k)] (H : RegionHistory S n R k0 K)
    {geo : Geo S n R M} {j : ℕ} (hjK : j + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R j⌋₊) (Z : H.Comp (j + 1))
    {ℓ' : ℕ} [NeZero ℓ'] {cc : Fin S.d → ℤ}
    (hV : ∀ x ∈ Vsites R (H.localHistory M K (j + 1) Z) (j + 1),
      InBox (M * n K * S.L ^ K) ℓ' cc (liftNear cc x)) :
    32 ≤ n (j + 1) ∧ Marg (S := S) (n := n) M K cc (M * n K * S.L ^ K) ℓ' (j + 1) Z.1 := by
  have hZc := locComp_mem H (by omega : j + 1 ≤ K) Z
  have hV' : ∀ x ∈ Vsites R (locHist (H.locRH (j + 1) Z) M K (j + 1) Z.1) (j + 1),
      InBox (M * n K * S.L ^ K) ℓ' cc (liftNear cc x) := hV
  have h32 := room_of_V (c := geo.c) (M1 := geo.M1) (H.locRH (j + 1) Z) (fun _ => rfl) hjK
    geo.hM geo.hc hρ Z.1 hZc hV'
  refine ⟨h32, fun x hx => ?_⟩
  have hx' : cubeMap n S.L M K (j + 1) x ∈ (Z.1 : Set (Torus S.d (n (j + 1)))) := hx
  have hnb : cubeMap n S.L M K (j + 1) (zcast (M * n K * S.L ^ K) (liftNear cc x)) ∈
      nbhd 0 (Z.1 : Set (Torus S.d (n (j + 1)))) := by
    rw [zcast_liftNear]
    exact subset_nbhd 0 _ hx'
  have hw := zone_inBox (M := M) (H.locRH (j + 1) Z) (fun _ => rfl) hjK Z.1 hZc hV' (r := 0)
    (by omega) x (by rw [zcast_liftNear] at hnb; exact hnb)
  have := zone_margin (M := M) (H.locRH (j + 1) Z) (fun _ => rfl) hjK Z.1 hZc hV' (r := 0) (m := 1)
    (by omega) (by omega) hw hnb
  simpa using this


theorem three_L_le_floor {n : ℕ → ℕ} [∀ k, NeZero (n k)] (H : RegionHistory S n R k0 K)
    (geo : Geo S n R M) (j : ℕ) : 3 * S.L ≤ ⌊R j⌋₊ := by
  apply Nat.le_floor
  have h1 := geo.hRlow j
  have h2 := H.F.RH.base
  push_cast
  linarith

theorem omega_pos' (S : Setting) (i : ℕ) : 0 < S.omega i := by
  have h : S.L + 11 ≤ S.omega i := by
    rw [Setting.omega_eq_omegaW]; exact le_omegaW _ _ _ _
  omega

/-- **The hypotheses of the comparison of two tori from the clause of `LFCoherent`.** -/
theorem corr_of_V {cc : Fin S.d → ℤ} {j : ℕ} (hjK : j + 1 ≤ K) (geo₁ : Geo S n₁ R M)
    (geo₂ : Geo S n₂ R M) (Z₁ : H₁.Comp (j + 1)) (Z₂ : H₂.Comp (j + 1))
    (hH : HistCorr cc (H₁.localHistory M K (j + 1) Z₁) (H₂.localHistory M K (j + 1) Z₂))
    (hV : SetCorr cc (Vsites R (H₁.localHistory M K (j + 1) Z₁) (j + 1))
      (Vsites R (H₂.localHistory M K (j + 1) Z₂) (j + 1))) :
    CorrEnv S n₁ n₂ M K (j + 1) ∧ LinCorr M H₁ H₂ cc (j + 1) Z₁ Z₂ ∧
      Marg (S := S) (n := n₁) M K cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (j + 1) Z₁.1 ∧
      Marg (S := S) (n := n₂) M K cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (j + 1) Z₂.1 := by
  obtain ⟨r₁, m₁⟩ := room_margin_of_V (geo := geo₁) H₁ hjK (three_L_le_floor H₁ geo₁ j) Z₁
    (ℓ' := M * n₂ K * S.L ^ K) (cc := cc) hV.1
  obtain ⟨r₂, m₂⟩ := room_margin_of_V (geo := geo₂) H₂ hjK (three_L_le_floor H₂ geo₂ j) Z₂
    (ℓ' := M * n₁ K * S.L ^ K) (cc := cc) (fun x hx => (hV.2.1 x hx).symm)
  refine ⟨⟨H₁.F.hnn, H₂.F.hnn, ?_, H₁.F.ok.two_le_L, omega_pos' S, fun i hi => ?_, hjK⟩,
    linCorr_of_histCorr hjK hH, m₁, fun x hx => (m₂ x hx).symm⟩
  · have := geo₁.hM
    have h1 : 1 ≤ geo₁.M1 := Nat.pos_of_ne_zero (NeZero.ne _)
    have := geo₁.hc
    rw [geo₁.hM]; nlinarith
  · exact ⟨le_trans (by omega) (le_trans r₁ (n_ge_of_le H₁.F.hnn hjK hi)),
      le_trans (by omega) (le_trans r₂ (n_ge_of_le H₂.F.hnn hjK hi))⟩

end FromHist

end Balaban.RootFSpine
