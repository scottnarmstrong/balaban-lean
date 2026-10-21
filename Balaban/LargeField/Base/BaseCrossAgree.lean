/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairLevelInner
public import Balaban.Fluctuation.LocalPairDecBg
public import Balaban.Fluctuation.LocalPairDepth
public import Balaban.Fluctuation.LocalSetDetCrossGeom
public import Balaban.Fluctuation.LocalClassDensityFamilySetPrec
public import Balaban.Polymer.TwoTorusGreenRows
import Mathlib.Tactic.Linarith

/-!
# Agreement of decoupled backgrounds of a level set and of a local generating set near a polymer

For a level set `Gp` and an arbitrary generating set `Gl` at the same top level `K = k + 1`, with
parameters `v`, `v'` of the two covers that agree at the cubes with base in the top layer of `Gl`
and whose active cubes have their interaction cubes inside a set `T`, the decoupled backgrounds of
the two pairs agree: the multipliers on `T` and the fields on a neighbourhood `Y` of `T`
(`decBg_cross_level`).  It is `Dec2.decBg_component_cross` with all its geometric hypotheses derived
from one depth hypothesis: the `8 L^{k+1+m₁}`-neighbourhood of `T` lies in the top layer of `Gl`.
There is no restriction on `k` (the level-`k + 1` statements with `1 ≤ k` use the separation of the
top layer of `Gl` to put interaction cubes inside `Ω_k`; here the active cubes are inside `T`
and `T` is deep).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.Polymer.TwoTorusStep Finset

section CrossBase

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱl : ℝ}
  {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}

theorem crossPow_le {j : ℕ} (hj : j ≤ k + 1) : L ^ (j + m₁) ≤ L ^ (k + 1 + m₁) :=
  Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)

/-- A site of the thickened box `□̂` of a cube of level `j` is within `6 L^{j+m₁}` of its base. -/
theorem supDist_hat_le (hm₁ : 2 ≤ m₁) {j : ℕ} {z y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (h : InBox m₁ j z (hatRad L m₁ j) y) : supDist y z ≤ 6 * L ^ (j + m₁) := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h1 := supDist_le_of_inBox (by unfold hatRad; positivity) h
  have h2 : (L : ℝ) ^ 2 * (L : ℝ) ^ j ≤ (L : ℝ) ^ (j + m₁) := by
    rw [← pow_add, add_comm]
    exact pow_le_pow_right₀ hL (by omega)
  have h3 : (0 : ℝ) ≤ (L : ℝ) ^ (j + m₁) := by positivity
  have h4 : (supDist y z : ℝ) ≤ 6 * (L : ℝ) ^ (j + m₁) := by
    unfold hatRad at h1
    nlinarith
  exact_mod_cast h4

/-- A site of the interaction box of a cube of level `j` is within `3 L^{j+m₁}` of its base. -/
theorem supDist_intBox_le' {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} {x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ intBox q) : supDist x q.2 ≤ 3 * L ^ (q.1 + m₁) := by
  have h1 := supDist_le_of_inBox (by positivity) (mem_intBox.1 hx)
  have h3 : (0 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := by positivity
  have h4 : (supDist x q.2 : ℝ) ≤ 3 * (L : ℝ) ^ (q.1 + m₁) := by linarith
  exact_mod_cast h4

/-- The base of a cube whose cell meets the thickened box of a cube with base in `T` is deep. -/
theorem base_top_of_hat (hm₁ : 2 ≤ m₁) {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    (hdepth : ∀ z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1), (∃ t ∈ T, supDist z t ≤ 8 * L ^ (k + 1 + m₁)) →
      z ∈ Gl.Ω (k + 1))
    {q q' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hq : q.1 ≤ k + 1) (hq' : q'.1 ≤ k + 1)
    (hqT : q.2 ∈ T)
    (h : ∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧ InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) :
    q'.2 ∈ Gl.Ω (k + 1) := by
  obtain ⟨y, hyc, hyb⟩ := h
  refine hdepth _ ⟨q.2, hqT, ?_⟩
  have h1 := supDist_le_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _) hyc
  have h2 := supDist_hat_le hm₁ hyb
  have h3 := supDist_triangle q'.2 y q.2
  have h4 := crossPow_le (L := L) (m₁ := m₁) (k := k) hq
  have h5 := crossPow_le (L := L) (m₁ := m₁) (k := k) hq'
  rw [LargeField.supDist_comm q'.2 y] at h3
  omega

/-- **The cover data at a deep cube agree.**  For a cube `q` of either cover with base in `T`, with
`T` deep in the top layer of `Gl`, the sets `𝒬(q)` of the level set and of `Gl` coincide, the
partition products of parameters that agree on the top layer coincide, and the cut-offs `χ_q`
coincide on the interaction box. -/
theorem cross_cover_agree (hG' : IsLevel Gp (k + 1)) (hm₁ : 2 ≤ m₁)
    {T : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    (hdepth : ∀ z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1),
      (∃ t ∈ T, supDist z t ≤ 8 * L ^ (k + 1 + m₁)) → z ∈ Gl.Ω (k + 1))
    {v : Dec2.DecParams (coverOf Gl)} {v' : Dec2.DecParams (coverOf Gp)}
    (hvv : ∀ P : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1), P.2 ∈ Gl.Ω (k + 1) →
      Dec2.extS (coverOf Gl) v P = Dec2.extS (coverOf Gp) v' P)
    {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ cubeIdx Gp ∨ q ∈ cubeIdx Gl) (hqT : q.2 ∈ T) :
    (coverOf Gp).Qset q = (coverOf Gl).Qset q ∧
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) v') q =
        (coverOf Gl).sProd (Dec2.extS (coverOf Gl) v) q ∧
      ∀ x ∈ intBox q, (coverOf Gp).chi q x = (coverOf Gl).chi q x := by
  have hq1 : q.1 ≤ k + 1 := by
    rcases hq with h | h
    · exact ((mem_cubeIdx _).1 h).1.2
    · exact ((mem_cubeIdx _).1 h).1.2
  have hc1 : ∀ q' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1),
      (q' ∈ cubeIdx Gp ∨ q' ∈ cubeIdx Gl) → q'.1 ≤ k + 1 := by
    intro q' h
    rcases h with h | h
    · exact ((mem_cubeIdx _).1 h).1.2
    · exact ((mem_cubeIdx _).1 h).1.2
  have hQ : (coverOf Gp).Qset q = (coverOf Gl).Qset q :=
    level_qset_eq_of_cover hG' fun q' hc h => base_top_of_hat hm₁ hdepth hq1 (hc1 q' hc) hqT h
  refine ⟨hQ, ?_, fun x hx => ?_⟩
  · unfold DecCover.sProd
    rw [hQ]
    refine Finset.prod_congr rfl fun P hP => (hvv P ?_).symm
    obtain ⟨hPc, hPh⟩ := (DecCover.mem_Qset _).1 hP
    exact base_top_of_hat hm₁ hdepth hq1 (hc1 P (Or.inr hPc)) hqT hPh
  · refine level_chi_eq_of_cover hG' (fun q' hc hb => ?_) q
    refine hdepth _ ⟨q.2, hqT, ?_⟩
    have h1 := supDist_le_of_cubeBump_ne_zero (hc1 q' hc) hb
    have h2 := supDist_intBox_le' hx
    have h3 := supDist_triangle q'.2 x q.2
    have h4 := crossPow_le (L := L) (m₁ := m₁) (k := k) hq1
    rw [LargeField.supDist_comm q'.2 x] at h3
    omega

variable {a : ℕ → ℝ} {ν Kc Cx : ℝ}

/-- **The decoupled backgrounds of a level set and of a local generating set agree near a polymer.**
Let `Gp` be a level set and `Gl` a generating set at the same top level whose top layer contains
the `8 L^{k+1+m₁}`-neighbourhood of a set `T`.  Let `v`, `v'` be parameters of the two covers that
agree at the cubes with base in the top layer of `Gl` and whose active cubes (non-zero partition
product) have their interaction cubes inside `T`.  Let `Y ⊇ T` lie within `2 L^{k+1}` of `T` and
contain the `L^{k+1}`-neighbourhood of `T`, and let the raw data agree on the sites that enter the
approximate field at the sites of `Y`.  Then the multipliers of the two decoupled backgrounds agree
on `T` and the fields on `Y`.  This is `Dec2.decBg_component_cross` for the pairs
`(coverOf Gl, Gl)`, `(coverOf Gp, Gp)`, with every geometric hypothesis derived from the depth
hypothesis; there is no restriction on `k`. -/
theorem decBg_cross_level (hG' : IsLevel Gp (k + 1)) (hm₁ : 2 ≤ m₁)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sl : Dec2.CoverBase (coverOf Gl) Gl a ν Kc Cx) (Sp : Dec2.CoverBase (coverOf Gp) Gp a ν Kc Cx)
    (HBl : BgHyp d L (k + 1) ϱl a ν) (HBp : BgHyp d L (k + 1) ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {v : Dec2.DecParams (coverOf Gl)} {v' : Dec2.DecParams (coverOf Gp)}
    (hv : ∀ P, ‖v P‖ ≤ Real.exp κ) (hv' : ∀ P, ‖v' P‖ ≤ Real.exp κ)
    {δ ε δ' ε' : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hδ0' : 0 < δ') (hδε' : δ' ≤ ε')
    (hε' : ε' ≤ bgC0 d L N) (hδ' : δ' ≤ c7 d L N BG κ)
    (hνε' : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε' ^ 2 ≤ δ' ^ 2)
    {D : BgData Gl N} {D' : BgData Gp N} (hD : InDomainC Gl ν δ ε D)
    (hD' : InDomainC Gp ν δ' ε' D')
    {T Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} (hTY : T ⊆ Y)
    (hdepth : ∀ z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1), (∃ t ∈ T, supDist z t ≤ 8 * L ^ (k + 1 + m₁)) → z ∈ Gl.Ω (k + 1))
    (hYT : ∀ y ∈ Y, ∃ t ∈ T, supDist y t ≤ 2 * L ^ (k + 1))
    (hresY : ∀ x ∈ T, ∀ y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1), supDist x y ≤ L ^ (k + 1) → y ∈ Y)
    (hvv : ∀ P : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1), P.2 ∈ Gl.Ω (k + 1) →
      Dec2.extS (coverOf Gl) v P = Dec2.extS (coverOf Gp) v' P)
    (hactl : ∀ q ∈ (coverOf Gl).cubeIdx, (coverOf Gl).sProd (Dec2.extS _ v) q ≠ 0 →
      ∀ x ∈ intBox q, x ∈ T)
    (hactp : ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS _ v') q ≠ 0 →
      ∀ x ∈ intBox q, x ∈ T)
    (hdat : ∀ y ∈ Y, y ∈ Gl.Ω 1 → ∀ z ∈ approxDep Gl y, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z)
    {φ : Gl.Ω 1 × Fin N → ℂ} {α : Gl.Ω 1 → ℂ} {φ' : Gp.Ω 1 × Fin N → ℂ} {α' : Gp.Ω 1 → ℂ}
    (h : Dec2.IsDecBg (coverOf Gl) Gl a ν (rho4 d L N BG κ) v D φ α)
    (h' : Dec2.IsDecBg (coverOf Gp) Gp a ν (rho4 d L N BG κ) v' D' φ' α') :
    (∀ (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (hx : x ∈ Gl.Ω 1) (hx' : x ∈ Gp.Ω 1), x ∈ T →
      α' ⟨x, hx'⟩ = α ⟨x, hx⟩) ∧
    (∀ (y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ Gl.Ω 1) (hy' : y ∈ Gp.Ω 1), y ∈ Y → ∀ i : Fin N,
      φ' (⟨y, hy'⟩, i) = φ (⟨y, hy⟩, i)) := by
  classical
  have hP0 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hPP := crossPow_le (L := L) (m₁ := m₁) (k := k) (le_refl (k + 1))
  have hLP : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)
  have hYtop : ∀ y ∈ Y, y ∈ Gl.Ω (k + 1) := fun y hy => by
    obtain ⟨t, ht, hd⟩ := hYT y hy
    exact hdepth y ⟨t, ht, by omega⟩
  have hlay : ∀ y ∈ Gl.Ω (k + 1), ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ Gl.layer n ↔ y ∈ Gp.layer n) :=
    fun y hy n hn hnK => (level_layer_iff_of_mem_top hG' hy hn hnK).symm
  have hbaseT : ∀ q ∈ (coverOf Gl).cubeIdx, (coverOf Gl).sProd (Dec2.extS _ v) q ≠ 0 →
      q.2 ∈ T := fun q hq hne => hactl q hq hne _ (Localization.base_mem_intBox q)
  have hbaseT' : ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS _ v') q ≠ 0 →
      q.2 ∈ T := fun q hq hne => hactp q hq hne _ (Localization.base_mem_intBox q)
  have htopT : ∀ y ∈ T, y ∈ Gl.Ω (k + 1) := fun y hy =>
    hdepth y ⟨y, hy, by rw [supDist_self]; exact Nat.zero_le _⟩
  refine Dec2.decBg_component_cross (C := coverOf Gl) (C' := coverOf Gp) (H := Gl) (H' := Gp)
    (s := v) (s' := v') hS Sl Sp HBl HBp hκ hM hv hv' hδ0 hδε hε hδ hνε hδ0' hδε' hε' hδ' hνε' hD hD'
    hTY (fun y hy => hlay y (hYtop y hy))
    (fun q hq hne => Or.inl fun x hx => hactl q hq hne x hx)
    (fun q hq hne => Or.inl fun x hx => hactp q hq hne x hx)
    (fun q hq hne x _ hx => hactl q hq hne x hx) (fun q hq hne x _ hx => hactp q hq hne x hx)
    ?_ ?_ ?_ ?_ hdat h h'
  · intro q hq hne
    obtain ⟨hqc, hsub⟩ := Finset.mem_filter.1 hq
    have hqT := hbaseT q hqc hne
    have hqp : q ∈ (coverOf Gp).cubeIdx :=
      (level_mem_cubeIdx_iff_of_mem_top hG' (htopT _ hqT)).2 hqc
    obtain ⟨-, hs, hchi⟩ := cross_cover_agree hG' hm₁ hdepth hvv (Or.inr hqc) hqT
    refine ⟨Finset.mem_filter.2 ⟨hqp, fun x hx => hactl q hqc hne x hx⟩, hs, ?_, fun x hx => (hchi x hx).symm⟩
    intro x hx y hy n hn hnK
    have hxT := hactl q hqc hne x hx
    refine hlay y (hdepth y ⟨x, hxT, ?_⟩) n hn hnK
    have : supDist y x ≤ 1 := by
      rcases hy with rfl | ⟨μ, rfl | rfl⟩
      · rw [supDist_self]; exact Nat.zero_le _
      · exact supDist_le_one_of_adj ⟨μ, Or.inl rfl⟩
      · exact supDist_le_one_of_adj ⟨μ, Or.inr (by simp)⟩
    omega
  · intro q hq hne
    obtain ⟨hqc, hsub⟩ := Finset.mem_filter.1 hq
    have hqT := hbaseT' q hqc hne
    have hql : q ∈ (coverOf Gl).cubeIdx :=
      (level_mem_cubeIdx_iff_of_mem_top hG' (htopT _ hqT)).1 hqc
    obtain ⟨-, hs, -⟩ := cross_cover_agree hG' hm₁ hdepth hvv (Or.inr hql) hqT
    have hne' : (coverOf Gl).sProd (Dec2.extS _ v) q ≠ 0 := by rw [← hs]; exact hne
    exact ⟨Finset.mem_filter.2 ⟨hql, fun x hx => hactl q hql hne' x hx⟩, hne'⟩
  · intro x hx _ y hy
    have hd := supDist_le_of_mem_resSites hy
    have hyY := hresY x hx y hd
    refine ⟨?_, hyY⟩
    exact Gl.Ω_antitone le_rfl (by omega) (by omega) (hYtop y hyY)
  · intro y hy _ q _ hq2 hb n hn hnK
    refine (hlay q.2 (hdepth q.2 ?_) n hn hnK)
    obtain ⟨t, ht, hd⟩ := hYT y hy
    have h1 := supDist_le_of_bump_ne_zero hb
    have h2 := crossPow_le (L := L) (m₁ := m₁) (k := k) hq2
    have h3 := Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) hq2
    have h4 := supDist_triangle q.2 y t
    rw [LargeField.supDist_comm q.2 y] at h4
    exact ⟨t, ht, by omega⟩

end CrossBase

end Balaban.LargeField.Base
