/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatSetGeom
public import Balaban.Fluctuation.LocalClassDensityIrrelSuppSet
public import Balaban.Inhabited.NewLevelCanonCast

/-!
# The class set lies in the top layer of `Gk` with the collar margin

For the generating sets of the settings, `Gj = castG hc (𝔹_j(X̂))` and
`Gk = castG hc (𝔹_k(castNbhd Y))` with `X̂ ⊆ Y`, every data site of `Gj` (the sites of `Ω₁(Gj)` and of
its collar) lies in the top layer `Ω_k(Gk)` of `Gk`, because the data sites of `𝔹_j(X̂)` are within
`11 L^{m₁'} L^j + 1 ≤ 5 L ⋅ L^{m₁'} L^k` of `X̂` and `castNbhd Y` is the cube-index neighbourhood of `Y`
(`5 L` cubes of side `L^{m₁'} L^k`).  Consequently `Gk.spacing = L^k` there, the scale gap is
`θ = L^{j-k}` (`L^j ≤ θ L^k`) and the collar condition `1 ≤ θ ⋅ spacing` holds
(`scaleGap_top`, `collar_top`: the hypotheses `gap`, `hcol`, `hjθ` of `HypSle` with `θ = L^j / L^k`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.GsSpec Balaban.LargeField Finset

section Top

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ : ℝ}

omit [NeZero N₁] [NeZero L] in
theorem supDist_torusCast_eq {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) (x y : Torus d a) :
    supDist (GsSpec.torusCast x : Torus d b) (GsSpec.torusCast y : Torus d b) = supDist x y := by
  subst h
  have e : ∀ z : Torus d a, (GsSpec.torusCast z : Torus d a) = z := fun z => by
    funext μ; simp [GsSpec.torusCast]
  rw [e, e]

/-- **Sites within `5 L` cube sides have cube indices within `5 L`.** -/
theorem supDist_fineCubeIdx_le_of_supDist {M1 N : ℕ} [NeZero M1] [NeZero N] {q n : ℕ} (hn : n ≤ q)
    {x y : Torus d (M1 * N * L ^ q)} (h : supDist x y ≤ 5 * L * (L ^ n * M1)) :
    supDist (fineCubeIdx M1 N L q n x) (fineCubeIdx M1 N L q n y) ≤ 5 * L := by
  have hP : M1 * N * L ^ q = (L ^ n * M1) * (N * L ^ (q - n)) := fine_eq_cube hn
  have hs : 0 < L ^ n * M1 := Nat.pos_of_ne_zero (by
    have := NeZero.ne L; have := NeZero.ne M1; positivity)
  have := supDist_blockMap_le (d := d) hP x y
  unfold fineCubeIdx
  refine this.trans ?_
  have hlt : (supDist x y + L ^ n * M1 - 1) / (L ^ n * M1) < 5 * L + 1 := by
    rw [Nat.div_lt_iff_lt_mul hs]
    have hsplit : (5 * L + 1) * (L ^ n * M1) = 5 * L * (L ^ n * M1) + L ^ n * M1 := by ring
    generalize L ^ n * M1 = s at hs hsplit h ⊢
    generalize 5 * L * s = t at hsplit h ⊢
    omega
  omega

/-- **The data sites of `𝔹_j(X̂)` (cast) lie in the top layer of `𝔹_k(castNbhd Y)` (cast)** when
`X ⊆ Y` on the finer torus, `j ≤ k` and `L ≥ 3`. -/
theorem dataSites_subset_top {N₁' m₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    (hL : 3 ≤ L) {j : ℕ} (hjk : j ≤ k) {X Y : Set (CTorus d L N₁' m₁' (k + 1))} (hXY : X ⊆ Y)
    {hs₁ : ϱ₁ ≤ minSep L (L ^ m₁')} {hs₂ : ϱ₂ ≤ minSep L (L ^ m₁')} {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ dataSites (castG hc (localB j (Nat.le_succ_of_le hjk) X hs₂))) :
    x ∈ (castG hc (localB k (Nat.le_succ k) (castNbhd (N₁' := N₁') (m₁' := m₁') Y) hs₁)).Ω k := by
  have hL2 : 2 ≤ L := by omega
  obtain ⟨y, hy, hd⟩ := dataSites_castG_range hc (localB j (Nat.le_succ_of_le hjk) X hs₂) X
    (11 * L ^ m₁' * L ^ j + 1)
    (fun x hx => localB_dataSites_range hL2 hx) hx
  have hc' : N₁' * L ^ m₁' * L ^ (k + 1) = N₁ * L ^ m₁ * L ^ (k + 1) := by rw [hc]
  have hxP : (GsSpec.torusCast x : CTorus d L N₁' m₁' (k + 1)) ∈
      castNbhd (N₁' := N₁') (m₁' := m₁') Y := by
    refine ⟨y, hXY hy, ?_⟩
    have hd' : supDist (GsSpec.torusCast x : CTorus d L N₁' m₁' (k + 1)) y ≤
        11 * L ^ m₁' * L ^ j + 1 := by
      have e : (GsSpec.torusCast (GsSpec.torusCast y : Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) :
          Torus d (N₁' * L ^ m₁' * L ^ (k + 1))) = y := by
        exact torusCast_torusCast hc' y
      calc supDist (GsSpec.torusCast x : Torus d (N₁' * L ^ m₁' * L ^ (k + 1))) y
          = supDist (GsSpec.torusCast x : Torus d (N₁' * L ^ m₁' * L ^ (k + 1)))
            (GsSpec.torusCast (GsSpec.torusCast y : Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) :
              Torus d (N₁' * L ^ m₁' * L ^ (k + 1))) := by rw [e]
        _ = supDist x (GsSpec.torusCast y : Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) :=
          supDist_torusCast_eq hc'.symm x _
        _ ≤ _ := hd
    have hLk : L ^ j ≤ L ^ k := Nat.pow_le_pow_right (by omega) hjk
    have hpos : 0 < L ^ k * L ^ m₁' := Nat.pos_of_ne_zero (by
      have := NeZero.ne L; positivity)
    have hbound : 11 * L ^ m₁' * L ^ j + 1 ≤ 5 * L * (L ^ k * L ^ m₁') := by
      have h1 : 11 * L ^ m₁' * L ^ j ≤ 11 * (L ^ k * L ^ m₁') := by nlinarith [Nat.zero_le (L ^ m₁')]
      nlinarith
    exact supDist_fineCubeIdx_le_of_supDist (d := d) (L := L) (M1 := L ^ m₁') (N := N₁')
      (q := k + 1) (n := k) (by omega)
      (x := (GsSpec.torusCast (GsSpec.torusCast x : CTorus d L N₁' m₁' (k + 1)) :
        Torus d (L ^ m₁' * N₁' * L ^ (k + 1))))
      (y := (GsSpec.torusCast y : Torus d (L ^ m₁' * N₁' * L ^ (k + 1))))
      (by
        rw [supDist_torusCast_eq (by ring)]
        exact hd'.trans hbound)
  rw [mem_castG_Ω]
  have htop := localB_Ω_top_eq (hj := Nat.le_succ k) (X := castNbhd (N₁' := N₁') (m₁' := m₁') Y)
    (hsep := hs₁) (fun x hx y hy => castNbhd_saturated x hx y hy)
  have := hxP
  rw [← htop] at this
  exact Finset.mem_coe.1 this

omit [NeZero N₁] [NeZero L] in
theorem layerIndex_le_of_empty {N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ' : ℝ}
    (G : GeneratingSet d L N₀ K ϱ') {j : ℕ} (hG : G.Ω (j + 1) = ∅) {x : Torus d (N₀ * L ^ K)}
    (hx : x ∈ G.Ω 1) : G.layerIndex x ≤ j := by
  obtain ⟨h1, h2, h3⟩ := G.layerIndex_spec hx
  by_contra hlt
  push Not at hlt
  have hmem : x ∈ G.Ω (j + 1) :=
    G.Ω_antitone (by omega) hlt (by omega) (G.mem_layer.1 h3).1
  rw [hG] at hmem
  exact Finset.notMem_empty _ hmem

/-- **The scale gap, the collar condition and `L^j ≤ θ L^k`** for the generating sets of the
settings, with `θ = L^j / L^k` (`θ = L^{j-k}`): the hypotheses `gap`, `hcol`, `hjθ`, `hnj` of `HypSle`
for `G = Gj`, `G' = Gk`. -/
theorem hat_gap {N₁' m₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    (hL : 3 ≤ L) (hk1 : 1 ≤ k) {j : ℕ} (hjk : j ≤ k) {X Y : Set (CTorus d L N₁' m₁' (k + 1))}
    (hXY : X ⊆ Y) {hs₁ : ϱ₁ ≤ minSep L (L ^ m₁')} {hs₂ : ϱ₂ ≤ minSep L (L ^ m₁')}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    (hGj : Gj = castG hc (localB j (Nat.le_succ_of_le hjk) X hs₂))
    (hGk : Gk = castG hc (localB k (Nat.le_succ k) (castNbhd (N₁' := N₁') (m₁' := m₁') Y) hs₁)) :
    (∀ z ∈ dataSites Gj, z ∈ Gk.Ω k ∧ Gk.spacing z = (L : ℝ) ^ k) ∧
      (∀ x ∈ Gj.Ω 1, Gj.layerIndex x ≤ j) ∧
      ScaleGap Gj Gk ((L : ℝ) ^ j / (L : ℝ) ^ k) ∧
      (∀ z ∈ collar Gj, z ∈ Gk.Ω 1 ∧ 1 ≤ ((L : ℝ) ^ j / (L : ℝ) ^ k) * Gk.spacing z) ∧
      (L : ℝ) ^ j ≤ ((L : ℝ) ^ j / (L : ℝ) ^ k) * (L : ℝ) ^ k ∧
      0 < ((L : ℝ) ^ j / (L : ℝ) ^ k) ∧ ((L : ℝ) ^ j / (L : ℝ) ^ k) ≤ 1 := by
  subst hGj hGk
  set Gj := castG hc (localB j (Nat.le_succ_of_le hjk) X hs₂) with hGjd
  set Gk := castG hc (localB k (Nat.le_succ k) (castNbhd (N₁' := N₁') (m₁' := m₁') Y) hs₁)
    with hGkd
  have hLp : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hLk : (0 : ℝ) < (L : ℝ) ^ k := by positivity
  have htop : ∀ z ∈ dataSites Gj, z ∈ Gk.Ω k ∧ Gk.spacing z = (L : ℝ) ^ k := by
    intro z hz
    have hzk := dataSites_subset_top hc hL hjk hXY (hs₁ := hs₁) (hs₂ := hs₂) hz
    refine ⟨hzk, ?_⟩
    have hk1' : z ∈ Gk.layer k := by
      rw [GeneratingSet.mem_layer]
      refine ⟨hzk, ?_⟩
      rw [mem_castG_Ω, localB_Ω_of_gt (by omega)]
      exact Finset.notMem_empty _
    unfold GeneratingSet.spacing
    rw [Gk.layerIndex_eq hk1 (Nat.le_succ k) hk1']
  have hlay : ∀ x ∈ Gj.Ω 1, Gj.layerIndex x ≤ j := fun x hx => by
    refine layerIndex_le_of_empty Gj ?_ hx
    ext z
    simp only [Finset.notMem_empty, iff_false]
    rw [mem_castG_Ω, localB_Ω_of_gt (by omega)]
    exact Finset.notMem_empty _
  have hθ : (L : ℝ) ^ j / (L : ℝ) ^ k * (L : ℝ) ^ k = (L : ℝ) ^ j := by field_simp
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ j := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ L))
  refine ⟨htop, hlay, ?_, ?_, hθ.ge, by positivity, ?_⟩
  · intro x hx
    rw [(htop x ?_).2, hθ]
    · unfold GeneratingSet.spacing
      exact pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ L)) (hlay x hx)
    · exact (mem_dataSites _).2 (Or.inl hx)
  · intro z hz
    have := htop z ((mem_dataSites _).2 (Or.inr hz))
    refine ⟨Gk.Ω_antitone le_rfl hk1 (by omega) this.1, ?_⟩
    rw [this.2, hθ]; exact hLj
  · rw [div_le_one hLk]
    exact pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ L)) hjk

end Top

end Balaban.Inhabited
