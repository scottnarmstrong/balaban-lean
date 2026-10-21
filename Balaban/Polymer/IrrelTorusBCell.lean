/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.IrrelTorusOnBox
public import Balaban.SmallField.IrrelTorusSum

/-!
# The box-renormalized label functional at the cell, on two tori

For the label functional `irrelTorusB` (`irrelTorusOn (relBox m₀)`: the relevant parts are
subtracted from, and filed at the cell `□(y)` for, the polymers within `r_K = ⌊L^{m₀+m₁+K}/8⌋` of the
centre only), the term of the distinguished label `(j, y, □(y))` is the same on two tori:

* `finsum_relBox_boxAgree`: the filed sum `Σ_{Z ∋ y, relBox y Z} (T_Z + Φ_{y,Z})` agrees on the two
  tori; `Z ↦ boxMap '' Z` is a bijection between the selected polymers through `y` and those through
  `boxMap y` (`isPolyDom_image_iff`, `relBox_image_boxMap_iff`), and the relevant parts of
  corresponding polymers agree (`relPartTorus_boxAgree`);
* `irrelTorusB_cell_boxAgree`: **the exact two-torus agreement at the cell**, for fields agreeing
  under `boxMap` on `□(y)` and on the stencil `y + L^j e_μ`, with the margin
  `8 (R + r_K) + 3 L^K + L · cellSide < n` on both tori.  This replaces the cell case
  `CellTermsAgree` of the two-torus comparison, which fails for `irrelTorus` (whose filed sum runs
  over the polymers winding around the torus).
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.RootFSpine Balaban.Multiscale

section Cell

variable {d L N₁ N₂ m₁ K N : ℕ} [NeZero L] [NeZero N₁] [NeZero N₂] {ϱ : ℝ}

set_option hygiene false in
local notation "n₁" => (N₁ * L ^ m₁) * L ^ K
set_option hygiene false in
local notation "n₂" => (N₂ * L ^ m₁) * L ^ K
set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K)
set_option hygiene false in
local notation "bm'" => boxMap ((N₂ * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)

open Classical in
/-- **The filed sum of the selection `relBox` on two tori**: for a centre `y` of the box of radius
`R`, with the margin `8 (R + r_K) + 3 L^K + L · cellSide` on both tori and fields agreeing under
`boxMap` at `y` and on the stencil `y + L^j e_μ`,
`Σ_{Z' ∋ bm y, relBox} (T_{Z'} + Φ_{bm y,Z'}) = Σ_{Z ∋ y, relBox} (T_Z + Φ_{y,Z})`. -/
theorem finsum_relBox_boxAgree {Tm : ∀ (M : ℕ) [NeZero M], Terms d L M m₁ K N ϱ} {m₀ j : ℕ}
    (hj1 : 1 ≤ j) (hjK : j ≤ K) (hT : TorusIndep m₀ Tm)
    (hlocB : ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      (Tm N₂).E j y X Ψ h = (Tm N₂).E j y X Ψ' h')
    (hN₁ : L ^ m₀ ∣ N₁) (hN₂ : L ^ m₀ ∣ N₂) (hM8 : 8 ≤ L ^ (m₀ + m₁)) {R : ℕ}
    (hmar₁ : 8 * (R + L ^ (m₀ + m₁ + K) / 8) + 3 * L ^ K + L * cellSide L m₀ m₁ j < n₁)
    (hmar₂ : 8 * (R + L ^ (m₀ + m₁ + K) / 8) + 3 * L ^ K + L * cellSide L m₀ m₁ j < n₂)
    {y : CTorus d L N₁ m₁ K} (hy : Aligned (L ^ j) y) (hyR : InBox d R n₁ y)
    (hstep : ∀ μ : Fin d, InBox d R n₁ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ K)))
    (i₀ i₁ : Fin N) (Ψ h : Fld d L N₁ m₁ K N) (Ψ' h' : Fld d L N₂ m₁ K N)
    (hy1 : Ψ' (bm y) = Ψ y) (hy2 : h' (bm y) = h y)
    (hΨst : ∀ μ : Fin d, Ψ' (bm (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ K))) =
      Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ K))) :
    ∑ᶠ Z' ∈ polysAt m₀ j (bm y),
        (if relBox m₀ (bm y) Z' then relPartTorus (Tm N₂) i₀ i₁ j (bm y) Ψ' h' Z' else 0) =
      ∑ᶠ Z ∈ polysAt m₀ j y,
        (if relBox m₀ y Z then relPartTorus (Tm N₁) i₀ i₁ j y Ψ h Z else 0) := by
  set R' := R + L ^ (m₀ + m₁ + K) / 8 with hR'
  have hRR' : R ≤ R' := Nat.le_add_right _ _
  have hcs : 0 < L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (NeZero.pos L) (cellSide_pos m₀ m₁ j)
  have hr₁ : 2 * R' + L * cellSide L m₀ m₁ j < n₁ := by omega
  have hr₂ : 2 * R' + L * cellSide L m₀ m₁ j < n₂ := by omega
  have hq₁ : 2 * (2 * R') + 1 < n₁ := by omega
  have hq₂ : 2 * (2 * R') + 1 < n₂ := by omega
  have hb₁ : 2 * R' + 1 < n₁ := by omega
  have hb₂ : 2 * R' + 1 < n₂ := by omega
  have hmar₁' : 8 * R' + 3 * L ^ K < n₁ := by omega
  have hmar₂' : 8 * R' + 3 * L ^ K < n₂ := by omega
  have hyR' : InBox d R' n₁ y := fun μ => (hyR μ).trans (by exact_mod_cast hRR')
  have hyR₂ : InBox d R' n₂ (bm y) := inBox_boxMap hb₂ hyR'
  have hstep' : ∀ μ : Fin d, InBox d R' n₁ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ K)) :=
    fun μ ν => ((hstep μ) ν).trans (by exact_mod_cast hRR')
  -- the selected polymers lie in the enlarged box, on both tori
  have hin₁ : ∀ Z : Set (CTorus d L N₁ m₁ K), relBox m₀ y Z → ∀ z ∈ Z, InBox d R' n₁ z :=
    fun Z hZ => inBox_of_relBox (by omega) hyR hZ
  have hin₂ : ∀ Z' : Set (CTorus d L N₂ m₁ K), relBox m₀ (bm y) Z' → ∀ z ∈ Z', InBox d R' n₂ z :=
    fun Z' hZ' => inBox_of_relBox (by omega) (inBox_boxMap (by omega) hyR) hZ'
  have hfin₁ := Set.toFinite (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ j y)
  have hfin₂ := Set.toFinite (polysAt (d := d) (L := L) (N₁ := N₂) (m₁ := m₁) (k := K) m₀ j (bm y))
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin₁, finsum_mem_eq_finite_toFinset_sum _ hfin₂,
    ← Finset.sum_filter, ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun Z => bm '' Z) (fun Z' => bm' '' Z') ?_ ?_ ?_ ?_ ?_
  · intro Z hZ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hZ ⊢
    obtain ⟨⟨hpd, hyZ⟩, hrel⟩ := hZ
    exact ⟨⟨(isPolyDom_image_iff (N₁' := N₂) (r := R') hN₁ hN₂ hjK hr₁ hr₂ (hin₁ Z hrel)).2 hpd,
      ⟨y, hyZ, rfl⟩⟩, (relBox_image_boxMap_iff hq₁ hq₂ hyR' (hin₁ Z hrel)).2 hrel⟩
  · intro Z' hZ'
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hZ' ⊢
    obtain ⟨⟨hpd, hyZ⟩, hrel⟩ := hZ'
    have hZin : ∀ z ∈ bm' '' Z', InBox d R' n₁ z := by
      rintro _ ⟨z, hz, rfl⟩
      exact inBox_boxMap hb₁ (hin₂ Z' hrel z hz)
    have himg : bm '' (bm' '' Z') = Z' := image_image_boxMap hb₁ (hin₂ Z' hrel)
    refine ⟨⟨(isPolyDom_image_iff (N₁' := N₂) (r := R') hN₁ hN₂ hjK hr₁ hr₂ hZin).1
      (by rw [himg]; exact hpd), ⟨bm y, hyZ, boxMap_boxMap hb₂ hyR'⟩⟩, ?_⟩
    rw [← relBox_image_boxMap_iff hq₁ hq₂ hyR' hZin, himg]
    exact hrel
  · intro Z hZ
    simp only [Finset.mem_filter] at hZ
    exact image_image_boxMap hb₂ (hin₁ Z hZ.2)
  · intro Z' hZ'
    simp only [Finset.mem_filter] at hZ'
    exact image_image_boxMap hb₁ (hin₂ Z' hZ'.2)
  · intro Z hZ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hZ
    obtain ⟨⟨hpd, hyZ⟩, hrel⟩ := hZ
    exact (relPartTorus_boxAgree hj1 hjK hT hlocB hN₁ hN₂ hM8 hmar₁' hmar₂' hy hyZ hpd
      (hin₁ Z hrel) hstep' i₀ i₁ Ψ h Ψ' h' hy1 hy2 hΨst).symm

open Classical in
/-- **The box-renormalized label functional at the cell agrees on two tori** (blocker 7, the cell
case of the two-torus comparison): for a family `Tm` with `TorusIndep`, `L^{m₀} ∣ N₁, N₂`, an aligned
centre `y` whose cell `□(y)` and stencil `y + L^j e_μ` lie in the centred box of radius `R`, the
margin `8 (R + r_K) + 3 L^K + L · cellSide < n` on both tori (`r_K = ⌊L^{m₀+m₁+K}/8⌋`), and fields
agreeing under `boxMap` on `□(y)` and on the stencil,
`ℰ^B_{irrel}(bm y, bm '' □(y); Ψ', h') = ℰ^B_{irrel}(y, □(y); Ψ, h)`. -/
theorem irrelTorusB_cell_boxAgree {Tm : ∀ (M : ℕ) [NeZero M], Terms d L M m₁ K N ϱ} {m₀ j : ℕ}
    (hj1 : 1 ≤ j) (hjK : j ≤ K) (hT : TorusIndep m₀ Tm)
    (hlocB : ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      (Tm N₂).E j y X Ψ h = (Tm N₂).E j y X Ψ' h')
    (hN₁ : L ^ m₀ ∣ N₁) (hN₂ : L ^ m₀ ∣ N₂) (hM8 : 8 ≤ L ^ (m₀ + m₁)) {R : ℕ}
    (hmar₁ : 8 * (R + L ^ (m₀ + m₁ + K) / 8) + 3 * L ^ K + L * cellSide L m₀ m₁ j < n₁)
    (hmar₂ : 8 * (R + L ^ (m₀ + m₁ + K) / 8) + 3 * L ^ K + L * cellSide L m₀ m₁ j < n₂)
    {y : CTorus d L N₁ m₁ K} (hy : Aligned (L ^ j) y)
    (hstep : ∀ μ : Fin d, InBox d R n₁ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ K)))
    (hcell : ∀ z ∈ box (cbase (cellSide L m₀ m₁ j) y -
      natT (fun _ => L / 2 * cellSide L m₀ m₁ j)) (L * cellSide L m₀ m₁ j), InBox d R n₁ z)
    (i₀ i₁ : Fin N) (Ψ h : Fld d L N₁ m₁ K N) (Ψ' h' : Fld d L N₂ m₁ K N)
    (hΨ : ∀ x ∈ box (cbase (cellSide L m₀ m₁ j) y -
      natT (fun _ => L / 2 * cellSide L m₀ m₁ j)) (L * cellSide L m₀ m₁ j), Ψ' (bm x) = Ψ x)
    (hΨst : ∀ μ : Fin d, Ψ' (bm (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ K))) =
      Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ K)))
    (hh : ∀ x ∈ box (cbase (cellSide L m₀ m₁ j) y -
      natT (fun _ => L / 2 * cellSide L m₀ m₁ j)) (L * cellSide L m₀ m₁ j), h' (bm x) = h x) :
    irrelTorusB m₀ (Tm N₂) i₀ i₁ j (bm y) (bm '' box (cbase (cellSide L m₀ m₁ j) y -
      natT (fun _ => L / 2 * cellSide L m₀ m₁ j)) (L * cellSide L m₀ m₁ j)) Ψ' h' =
    irrelTorusB m₀ (Tm N₁) i₀ i₁ j y (box (cbase (cellSide L m₀ m₁ j) y -
      natT (fun _ => L / 2 * cellSide L m₀ m₁ j)) (L * cellSide L m₀ m₁ j)) Ψ h := by
  set C : Set (CTorus d L N₁ m₁ K) := box (cbase (cellSide L m₀ m₁ j) y -
    natT (fun _ => L / 2 * cellSide L m₀ m₁ j)) (L * cellSide L m₀ m₁ j) with hC
  have hcs : 0 < L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (NeZero.pos L) (cellSide_pos m₀ m₁ j)
  have hR₁ : 4 * R < n₁ := by omega
  have hR₂ : 4 * R < n₂ := by omega
  have hm₁ : 2 * R + L * cellSide L m₀ m₁ j < n₁ := by omega
  have hm₂ : 2 * R + 1 < n₂ := by omega
  have hq₁ : 2 * (2 * R) + 1 < n₁ := by omega
  have hq₂ : 2 * (2 * R) + 1 < n₂ := by omega
  have hmar₁' : 8 * R + 3 * L ^ K < n₁ := by omega
  have hmar₂' : 8 * R + 3 * L ^ K < n₂ := by omega
  have hyC : y ∈ C := mem_cubeAt y
  have hCpd : IsPolyDom m₀ j C := isPolyDom_cubeAt hN₁ hjK y
  have hyR : InBox d R n₁ y := hcell y hyC
  have himg : bm '' C = box (cbase (cellSide L m₀ m₁ j) (bm y) -
      natT (fun _ => L / 2 * cellSide L m₀ m₁ j)) (L * cellSide L m₀ m₁ j) :=
    (image_eq_cellBox_iff hjK hN₁ hN₂ (R := R) hm₁ hm₂ hcell hcell).2 rfl
  have hsel : relBox m₀ (bm y) (bm '' C) ↔ relBox m₀ y C :=
    relBox_image_boxMap_iff hq₁ hq₂ hyR hcell
  have hsum := finsum_relBox_boxAgree hj1 hjK hT hlocB hN₁ hN₂ hM8 hmar₁ hmar₂ hy hyR hstep i₀ i₁
    Ψ h Ψ' h' (hΨ y hyC) (hh y hyC) hΨst
  unfold irrelTorusB irrelTorusOn
  rw [ite_eq_left himg, ite_eq_left rfl, hsum,
    E_boxAgree hj1 hjK hT hlocB hN₁ hN₂ hM8 hR₁ hR₂ hy hyC hCpd hcell Ψ h Ψ' h' hΨ hh,
    aTermTorus_boxAgree hj1 hjK hT hlocB hN₁ hN₂ hM8 hmar₁' hmar₂' hy hyC hCpd hcell i₀ Ψ Ψ' hΨ,
    relPartTorus_boxAgree hj1 hjK hT hlocB hN₁ hN₂ hM8 hmar₁' hmar₂' hy hyC hCpd hcell hstep i₀ i₁
      Ψ h Ψ' h' (hΨ y hyC) (hh y hyC) hΨst]
  by_cases hs : relBox m₀ y C
  · simp only [hs, hsel.2 hs, ↓reduceIte]
  · simp only [hs, mt hsel.1 hs, ↓reduceIte]

end Cell

end Balaban.Polymer.TwoTorusStep
