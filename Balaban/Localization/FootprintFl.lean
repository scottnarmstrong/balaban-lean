/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.FootprintMargin
public import Balaban.Localization.RowsBg
public import Balaban.Localization.I5FluctGeom
public import Balaban.Localization.Decoupled2Self

/-!
# Footprint inclusions for the row-local background theorem and for the fluctuation boxes

Continuation of `FootprintMargin.lean` (FOOTPRINT.md, section 1 and section 2, items 3 and 6).

* `rowsDep_subset_component`: at a whole-lattice generating set of level `n`, the raw-data set
  `RowsDep G a ν (S_Y)` read by the row-local background theorem lies in the component `Y`.
  Hence `i4b_local_of_agree_on_component`: the conclusion of `i4b_local_rows` follows from
  agreement of the raw data `Ψ` on `Y` and of `h` on `Y ∩ Ω₁` only (the landed `i4b_local` asks
  agreement on `resDep` of all of `Y`, which leaves `Y`).
* `SYF_subset_SY_level`: the interaction boxes `S_Y^F` of the fluctuation pair
  `(coverOf Gp, Hm)` lie in the boxes `S_Y` of the background `Gp`.  The inclusion of
  `Ω₁(Hm)` in `Ω₁(Gp)` is automatic at full level; the remaining premises are the setting
  `DGSetting Gp a ν` and the connectedness `HatConn Gp` of the thickened boxes.
* `fluct_footprint_subset`: for a centre `x` of `S_Y^F`, the footprint of the residual of `Gp`
  at `x`, and the footprint of the approximate field of `Gp` at every row site of `x` for `Hm`
  (the site, its nearest neighbours, its `k`-block), lie in `Y`.
* `not_exists_box_of_outside_approxDep`: consistency with `exists_outside_approxDep`.  The
  inclusion concerns sites of a box `intBox z` whose thickened box `hatBox z` lies in `Y`; a site
  that reads a block base outside a set `S` lies in no such box.

The fluctuation, square-root and fan row-local theorems and the physical-reads lemma are separate
and not proved here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset Matrix

section Background

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **The raw-data set of the row-local background theorem lies in the component.**  At a
whole-lattice generating set of level `n`, every site of `RowsDep G a ν (S_Y)` lies in `Y`. -/
theorem rowsDep_subset_component {n : ℕ} (hG : IsLevel G n)
    (X₁ : Finset (CTorus d L N₁ m₁ K)) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K))
    (Y : Finset (CTorus d L N₁ m₁ K)) {z : CTorus d L N₁ m₁ K}
    (hz : RowsDep G a ν (SY G X₁ 𝒞 Y) z) : z ∈ Y := by
  have h := footprint_subset_component hG X₁ 𝒞 Y
  rcases hz with ⟨x, hx, hz⟩ | ⟨y, hy | ⟨x, hx, hxy⟩, hz⟩
  · exact h.1 _ hx hz
  · exact h.2 _ hy _ (mem_resSites_self _) hz
  · exact h.2 _ hx _ (mem_resSites_of_entry_ne_zero hxy) hz

/-- **`i4b_local` from raw-data agreement on the component only.**  Same conclusions as
`i4b_local_rows`; the hypothesis is agreement of `Ψ` on `Y` and of `h` on `Y ∩ Ω₁`. -/
theorem i4b_local_of_agree_on_component {c BG : ℝ} (hS : DecSpecs d L c BG)
    (S : DGSetting G a ν) (hconn : HatConn G)
    (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s s' : DecParams G}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D D₂ : BgData G N}
    (hD : InDomainC G ν δ ε D) (hD₂ : InDomainC G ν δ ε D₂)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)} {n : ℕ}
    (hG : IsLevel G n)
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx G, P ∉ parCubes G X₁ → extS G s P = 1 ∧ extS G s' P = 1)
    (hs0 : ∀ P ∈ parCubes G X₁, P ∉ 𝒞 → extS G s P = 0 ∧ extS G s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI G (cubeP P) Y → extS G s P = extS G s' P)
    (hdata : ∀ z ∈ Y, D.Ψ z = D₂.Ψ z ∧ (z ∈ G.Ω 1 → D.h z = D₂.h z))
    {φ φ₂ : G.Ω 1 × Fin N → ℂ} {α α₂ : G.Ω 1 → ℂ}
    (h : IsDecBg G a ν (rho4 d L N BG κ) s D φ α)
    (h₂ : IsDecBg G a ν (rho4 d L N BG κ) s' D₂ φ₂ α₂) :
    (∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y → α x = α₂ x) ∧
    (∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      φ (y, i) - approxField G a ν D.Ψ D.h y i = φ₂ (y, i) - approxField G a ν D₂.Ψ D₂.h y i) ∧
    (∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y →
      (∀ z ∈ approxDep G (y : CTorus d L N₁ m₁ K), RowsDep G a ν (SY G X₁ 𝒞 Y) z) →
      ∀ i : Fin N, φ (y, i) = φ₂ (y, i)) ∧
    (∀ y : G.Ω 1, RowSite G a ν (0 : G.Ω 1 → ℂ) (SY G X₁ 𝒞 Y) y → ∀ i : Fin N,
      φ (y, i) = φ₂ (y, i)) :=
  i4b_local_rows hS S hconn HB hκ hM hs hs' hδ0 hδε hε hδ hνε hD hD₂ hY hs1 hs0 hag
    (fun _ hz => hdata _ (rowsDep_subset_component hG X₁ 𝒞 Y hz)) h h₂

end Background

section Fluct

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a : ℕ → ℝ} {ν : ℝ}

/-- **`S_Y^F ⊆ S_Y`** for the full-level background `Gp`.  The inclusion
`Ω₁(Hm) ⊆ Ω₁(Gp)` holds because `Ω₁(Gp)` is the whole torus; the premises that remain are the
setting `DGSetting Gp a ν` (which gives `CoverLocal (coverOf Gp) Gp`) and `HatConn Gp`. -/
theorem SYF_subset_SY_level {n : ℕ} (hGp : IsLevel Gp n) (S : DGSetting Gp a ν)
    (hconn : HatConn Gp) {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ Dec2.SYF (coverOf Gp) Hm a ν X₁ 𝒞 Y) :
    x ∈ SY Gp X₁ 𝒞 Y :=
  SYF_subset_SY (Dec2.coverLocal_self S) hconn
    (fun b _ => by rw [hGp.Ω_one]; exact Finset.mem_univ _) hY hx

/-- **(FP) for the fluctuation boxes.**  Let `Gp` have level `n = k + 1` and `Hm` level `k`.  For
a site `x` of `S_Y^F`, the footprint `resDep Gp x` of the residual of `Gp` lies in `Y`, and so
does the footprint `approxDep Gp u` of the approximate field at every row site `u` of `Hm` at `x`
(`x`, its nearest neighbours, the sites of its `k`-block). -/
theorem fluct_footprint_subset (hGp : IsLevel Gp (k + 1)) (hHm : IsLevel Hm k)
    (S : DGSetting Gp a ν) (hconn : HatConn Gp)
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ Dec2.SYF (coverOf Gp) Hm a ν X₁ 𝒞 Y) :
    resDep Gp x ⊆ Y ∧ ∀ u ∈ resSites Hm x, approxDep Gp u ⊆ Y := by
  classical
  have hxS := SYF_subset_SY_level (Hm := Hm) hGp S hconn hY hx
  refine ⟨(footprint_subset_component hGp X₁ 𝒞 Y).1 x hxS, fun u hu => ?_⟩
  obtain ⟨z, hzZ, hxz⟩ := Finset.mem_biUnion.1 hxS
  obtain ⟨hz, -, hsub⟩ := Finset.mem_filter.1 hzZ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hle : (L : ℝ) ^ k ≤ (L : ℝ) ^ (k + 1) := pow_le_pow_right₀ hL1 (Nat.le_succ k)
  intro v hv
  have hvh := approxDep_subset_hatBox_of_near hGp hz hxz
    (fun μ => (resSites_coord_bound hHm hu μ).mono hle) hv
  exact hsub ⟨v, by rw [hGp.Ω_one]; exact Finset.mem_univ _⟩ hvh

end Fluct

section Consistency

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- **Consistency with the margin counterexample.**  If a site `x` reads a site `q ∉ S` of the
approximate field (`q ∈ approxDep G x`, as for the sites next to the outer face in
`exists_outside_approxDep`), there is no centre `z` with `x ∈ □_z` and `□̂_z ⊆ S`. -/
theorem not_exists_box_of_outside_approxDep {n : ℕ} (hG : IsLevel G n)
    {S : Set (CTorus d L N₁ m₁ K)} {x q : CTorus d L N₁ m₁ K} (hq : q ∉ S)
    (hqx : q ∈ approxDep G x) :
    ¬ ∃ z ∈ cubeIdx G, x ∈ intBox z ∧ (hatBox z : Set (CTorus d L N₁ m₁ K)) ⊆ S := by
  rintro ⟨z, hz, hxz, hsub⟩
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ n :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  exact hq (hsub (approxDep_subset_hatBox_of_near hG hz hxz
    (fun μ => CoordNear.refl (by linarith) _) hqx))

end Consistency

end Balaban.Localization
