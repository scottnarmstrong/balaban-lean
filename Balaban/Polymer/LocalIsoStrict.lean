/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoBg
public import Balaban.Localization.DecoupledSolveAnalytic
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the data of the decoupled fluctuation problem

For two generating sets carried onto each other by the box map (`OmegaIso G H ρ`), the data
`(φ₀, α₀, δΨ, f₁)` of Proposition 5.1 of the two sets correspond (`EdatCorr`) when the fields
correspond on the box of radius `ρ + 1` and the fields on `Ω₁` correspond under `e`.  The strict
data inequalities of Theorem I-4a (`StrictDataM`) then hold on one torus iff they hold on the
other.

* `OmegaIso.dataSites_iff`, `OmegaIso.inBox_of_mem_dataSites`: the data sites;
* `OmegaIso.zeroExt_eq`, `OmegaIso.negLap_eq`: the zero extension and the Laplacian;
* `EdatCorr`, `OmegaIso.strictDataP_iff`, `OmegaIso.strictDataM_iff`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Matrix

variable {d L N₁ N₁' m₁ K N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ' : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)

namespace OmegaIso

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'}
  {ρ : ℕ}

/-- A data site lies in the box of radius `ρ + 1`. -/
theorem inBox_of_mem_dataSites (hI : OmegaIso G H ρ) {y : CTorus d L N₁ m₁ K}
    (hy : y ∈ dataSites G) : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) y := by
  have h1 := hI.two_lt.1
  rcases (mem_dataSites G).1 hy with h | h
  · exact hI.inBox_succ h
  · obtain ⟨-, x, hx, μ, hxy | hxy⟩ := (mem_collar G).1 h
    · rw [hxy]; exact inBox_add_single (by omega) (hI.boxG x hx) μ
    · have : y = x - Pi.single μ 1 := by rw [hxy]; abel
      rw [this]; exact inBox_sub_single (by omega) (hI.boxG x hx) μ

theorem inBox_of_mem_dataSites' (hI : OmegaIso G H ρ) {y : CTorus d L N₁' m₁ K}
    (hy : y ∈ dataSites H) : InBox d (ρ + 1) ((N₁' * L ^ m₁) * L ^ K) y := by
  have h1 := hI.two_lt.2
  rcases (mem_dataSites H).1 hy with h | h
  · exact inBox_mono (Nat.le_succ ρ) (hI.boxH y h)
  · obtain ⟨-, x, hx, μ, hxy | hxy⟩ := (mem_collar H).1 h
    · rw [hxy]; exact inBox_add_single (by omega) (hI.boxH x hx) μ
    · have : y = x - Pi.single μ 1 := by rw [hxy]; abel
      rw [this]; exact inBox_sub_single (by omega) (hI.boxH x hx) μ

/-- The data sites at corresponding sites of the box of radius `ρ + 1`. -/
theorem dataSites_iff (hI : OmegaIso G H ρ) {z : CTorus d L N₁ m₁ K}
    (hz : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) z) : bm z ∈ dataSites H ↔ z ∈ dataSites G := by
  rw [mem_dataSites, mem_dataSites, hI.mem_iff hz, hI.collar_iff hz]

/-- Every data site of `H` is the image of a data site of `G`. -/
theorem exists_dataSites_of (hI : OmegaIso G H ρ) {y : CTorus d L N₁' m₁ K}
    (hy : y ∈ dataSites H) : ∃ z ∈ dataSites G, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) z ∧
      bm z = y := by
  have hb := hI.inBox_of_mem_dataSites' hy
  have hlt : 2 * (ρ + 1) + 1 < (N₁ * L ^ m₁) * L ^ K := by have := hI.two_lt.1; omega
  have hz : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) (bm' y) := inBox_boxMap hlt hb
  have hback : bm (bm' y) = y := boxMap_boxMap hlt hb
  refine ⟨bm' y, (hI.dataSites_iff hz).1 (by rw [hback]; exact hy), hz, hback⟩

/-- The zero extension of corresponding scalar fields of `Ω₁` at the sites of the box of radius
`ρ + 1`. -/
theorem zeroExt_eq (hI : OmegaIso G H ρ) {u : G.Ω 1 → ℂ} {u' : H.Ω 1 → ℂ}
    (hu : ∀ x, u' (hI.e x) = u x) {z : CTorus d L N₁ m₁ K}
    (hz : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) z) :
    zeroExt (H.Ω 1) u' (bm z) = zeroExt (G.Ω 1) u z := by
  unfold zeroExt
  by_cases h : z ∈ G.Ω 1
  · have h' : bm z ∈ H.Ω 1 := (hI.mem_iff hz).2 h
    simp only [h, h', ↓reduceDIte]
    rw [← hu ⟨z, h⟩]
    rfl
  · have h' : bm z ∉ H.Ω 1 := fun hh => h ((hI.mem_iff hz).1 hh)
    simp only [h, h', ↓reduceDIte]

/-- The lattice Laplacian of corresponding fields at a site of the box of radius `ρ`. -/
theorem negLap_eq (hI : OmegaIso G H ρ) {w : CTorus d L N₁ m₁ K → ℂ}
    {w' : CTorus d L N₁' m₁ K → ℂ} (hw : ∀ z, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) z →
      w' (bm z) = w z) {x : CTorus d L N₁ m₁ K} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    negLap w' (bm x) = negLap w x := by
  unfold negLap
  have h1 := hI.two_lt.1; have h2 := hI.two_lt.2
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← boxMap_add_single (ρ := ρ) (by omega) (by omega) hx μ,
    ← boxMap_sub_single (ρ := ρ) (by omega) (by omega) hx μ,
    hw _ (inBox_mono (Nat.le_succ ρ) hx), hw _ (inBox_add_single (by omega) hx μ),
    hw _ (inBox_sub_single (by omega) hx μ)]

end OmegaIso

/-- **Corresponding data of Proposition 5.1** on two generating sets carried onto each other: the
fields `φ₀`, `δΨ` correspond on the box of radius `ρ + 1`, the multipliers `α₀` and the sources
`f₁` correspond under `e`. -/
structure EdatCorr {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'} {ρ : ℕ} (hI : OmegaIso G H ρ) (p : Edat G N)
    (p' : Edat H N) : Prop where
  φ : FieldCorr (ρ + 1) p.1 p'.1
  α : ∀ x, p'.2.1 (hI.e x) = p.2.1 x
  δΨ : FieldCorr (ρ + 1) p.2.2.1 p'.2.2.1
  f : ∀ x i, p'.2.2.2 (hI.e x, i) = p.2.2.2 (x, i)

/-- `EdatCorr` is inhabited: the zero data correspond. -/
theorem edatCorr_zero {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'} {ρ : ℕ} (hI : OmegaIso G H ρ) :
    EdatCorr (N := N) hI 0 0 :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

namespace OmegaIso

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'}
  {ρ : ℕ}

/-- A statement about all sites of `Ω₁` on the two tori. -/
theorem forall_omega_iff (hI : OmegaIso G H ρ) {P : G.Ω 1 → Prop} {P' : H.Ω 1 → Prop}
    (h : ∀ x, P' (hI.e x) ↔ P x) : (∀ x', P' x') ↔ ∀ x, P x := by
  constructor
  · intro h' x; exact (h x).1 (h' _)
  · intro h' x'
    obtain ⟨x, rfl⟩ := hI.e.surjective x'
    exact (h x).2 (h' x)

/-- **The strict data inequalities (P1)–(P3) at corresponding data.** -/
theorem strictDataP_iff (hI : OmegaIso G H ρ) {p : Edat G N} {p' : Edat H N}
    (hp : EdatCorr hI p p') (δ₀ δ₁ : ℝ) :
    StrictDataP H N δ₀ δ₁ p' ↔ StrictDataP G N δ₀ δ₁ p := by
  have h1 := hI.two_lt.1; have h2 := hI.two_lt.2
  have hsp : ∀ x : G.Ω 1, H.spacing ((hI.e x : H.Ω 1) : CTorus d L N₁' m₁ K) =
      G.spacing (x : CTorus d L N₁ m₁ K) := fun x => hI.spacing_eq x.2
  have hpl : ∀ (x : G.Ω 1) (μ : Fin d), p'.1 (((hI.e x : H.Ω 1) : CTorus d L N₁' m₁ K) +
      Pi.single μ 1) = p.1 ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) := fun x μ => by
    rw [coe_e, ← boxMap_add_single (ρ := ρ) (by omega) (by omega) (hI.boxG x x.2) μ,
      hp.φ _ (hI.nbr_inBox x.2 μ).1]
  have hmi : ∀ (x : G.Ω 1) (μ : Fin d), p'.1 (((hI.e x : H.Ω 1) : CTorus d L N₁' m₁ K) -
      Pi.single μ 1) = p.1 ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) := fun x μ => by
    rw [coe_e, ← boxMap_sub_single (ρ := ρ) (by omega) (by omega) (hI.boxG x x.2) μ,
      hp.φ _ (hI.nbr_inBox x.2 μ).2]
  have hx0 : ∀ x : G.Ω 1, p'.1 ((hI.e x : H.Ω 1) : CTorus d L N₁' m₁ K) = p.1 x := fun x => by
    rw [coe_e, hp.φ _ (hI.inBox_succ x.2)]
  have hds : (∀ x : dataSites H, vn (p'.2.2.1 x) < δ₁) ↔
      ∀ x : dataSites G, vn (p.2.2.1 x) < δ₁ := by
    constructor
    · intro h x
      have hb := hI.inBox_of_mem_dataSites x.2
      have := h ⟨bm (x : CTorus d L N₁ m₁ K), (hI.dataSites_iff hb).2 x.2⟩
      rwa [show p'.2.2.1 (bm (x : CTorus d L N₁ m₁ K)) = p.2.2.1 x from hp.δΨ _ hb] at this
    · intro h y
      obtain ⟨z, hz, hzb, hzy⟩ := hI.exists_dataSites_of y.2
      have := h ⟨z, hz⟩
      show vn (p'.2.2.1 (y : CTorus d L N₁' m₁ K)) < δ₁
      rwa [← hzy, hp.δΨ _ hzb]
  unfold StrictDataP
  refine and_congr (hI.forall_omega_iff fun x => forall_congr' fun μ => ?_) (and_congr
    (hI.forall_omega_iff fun x => ?_) (and_congr (hI.forall_omega_iff fun x => ?_)
      (and_congr (hI.forall_omega_iff fun x => ?_) (and_congr
        (hI.forall_omega_iff fun x => forall_congr' fun i => ?_) hds))))
  · rw [hpl, hmi, hx0, hsp]
  · simp only [hpl, hmi, hx0, hsp]
  · rw [hx0]
  · rw [hsp, hp.α]
  · rw [hsp, hp.f]

/-- **The strict data inequalities of Theorem I-4a in the mode `ιU` at corresponding data.** -/
theorem strictDataM_iff (hI : OmegaIso G H ρ) {p : Edat G N} {p' : Edat H N}
    (hp : EdatCorr hI p p') (ιU : Bool) (δ₀ δ₁ : ℝ) :
    StrictDataM H N ιU δ₀ δ₁ p' ↔ StrictDataM G N ιU δ₀ δ₁ p := by
  have hsp : ∀ x : G.Ω 1, H.spacing ((hI.e x : H.Ω 1) : CTorus d L N₁' m₁ K) =
      G.spacing (x : CTorus d L N₁ m₁ K) := fun x => hI.spacing_eq x.2
  have hφe : ∀ x : G.Ω 1, p'.1 ((hI.e x : H.Ω 1) : CTorus d L N₁' m₁ K) = p.1 x := fun x => by
    rw [coe_e, hp.φ _ (hI.inBox_succ x.2)]
  have hg : ∀ x, gdef H p'.1 (hI.e x) = gdef G p.1 x := gdef_corr hI.e hφe
  have hl : ∀ x : G.Ω 1, negLap (zeroExt (H.Ω 1) (gdef H p'.1))
      ((hI.e x : H.Ω 1) : CTorus d L N₁' m₁ K) =
      negLap (zeroExt (G.Ω 1) (gdef G p.1)) (x : CTorus d L N₁ m₁ K) := fun x => by
    rw [coe_e]
    exact hI.negLap_eq (fun z hz => hI.zeroExt_eq hg hz) (hI.boxG x x.2)
  unfold StrictDataM
  refine and_congr (hI.strictDataP_iff hp δ₀ δ₁) (imp_congr_right fun _ => and_congr
    (hI.forall_omega_iff fun x => ?_) (hI.forall_omega_iff fun x => ?_))
  · rw [hg]
  · rw [hsp, hl]

end OmegaIso

end Balaban.Polymer.LocalIso
