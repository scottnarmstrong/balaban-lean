/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Data
public import Balaban.Multiscale.AgmonDecay
public import Balaban.Multiscale.PathMetric

/-!
# The real data domain from local agreement with a family of data

P7 p. 500 after (2.11) and p. 501 after (2.14): the configuration is assumed in the space (1.32) [5]
localized to `W_j ∩ U_{j+1}` for every piece `j`, and the window background is then an analytic
function on the space localized to `W_{k₁} ∩ U_k`.  `inDomainR_of_zones` is the bookkeeping behind
this step: a datum `D_w` on a generating set `G_w` lies in the real domain `Ψ̃(G_w; δ)`
(`InDomainR`) as soon as it is covered by zones `A_i`, on each of which it is identified (through a
bijection `e_i` of the tori that commutes with the lattice steps and carries `n`-blocks to
`n`-blocks) with a datum `D_i` in `Ψ̃(G_i; δ)`: equal `Ω₁` on the zone and its neighbours, equal
layer indices, equal data; every data site lies in a zone, every interface pair (R1) lies in one
zone, the external fields are the same real vector `h`, and (R4) holds for `h` at the level of
`G_w`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Finset

section Zones

variable {d L N₀w kw N : ℕ} [NeZero N₀w] [NeZero L] {ϱw ϱl : ℝ} {ι : Type*}
  {N₀ : ι → ℕ} [∀ i, NeZero (N₀ i)] {kl : ι → ℕ}

omit [NeZero N₀w] [NeZero L] in
/-- Adjacency is carried by a bijection commuting with the lattice steps. -/
theorem adj_map_of_add_single {a b : ℕ} (e : Torus d (N₀w * L ^ kw) ≃ Torus d (a * L ^ b))
    (he : ∀ x (μ : Fin d), e (x + Pi.single μ 1) = e x + Pi.single μ 1)
    {x y : Torus d (N₀w * L ^ kw)} (h : Adj x y) : Adj (e x) (e y) := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inl (by rw [h, he])⟩
  · exact ⟨μ, Or.inr (by rw [h, he])⟩

omit [NeZero N₀w] [NeZero L] in
/-- Adjacency is reflected by a bijection commuting with the lattice steps. -/
theorem adj_of_map_of_add_single {a b : ℕ} (e : Torus d (N₀w * L ^ kw) ≃ Torus d (a * L ^ b))
    (he : ∀ x (μ : Fin d), e (x + Pi.single μ 1) = e x + Pi.single μ 1)
    {x y : Torus d (N₀w * L ^ kw)} (h : Adj (e x) (e y)) : Adj x y := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inl (e.injective (by rw [h, he]))⟩
  · exact ⟨μ, Or.inr (e.injective (by rw [h, he]))⟩

/-- **The real domain from local agreement** (P7 (2.14)-(2.16), the space (1.32) [5] on
`W_{k₁} ∩ U_k` from the spaces on `W_j ∩ U_{j+1}`). -/
theorem inDomainR_of_zones (Gw : GeneratingSet d L N₀w kw ϱw) (Dw : BgData Gw N)
    (Gl : ∀ i, GeneratingSet d L (N₀ i) (kl i) ϱl) (Dl : ∀ i, BgData (Gl i) N)
    (e : ∀ i, Torus d (N₀w * L ^ kw) ≃ Torus d (N₀ i * L ^ kl i))
    (he : ∀ i x (μ : Fin d), e i (x + Pi.single μ 1) = e i x + Pi.single μ 1)
    (hblk : ∀ i n, n ≤ kw → n ≤ kl i → ∀ x y,
      jBlock d L N₀w kw n x = jBlock d L N₀w kw n y →
        jBlock d L (N₀ i) (kl i) n (e i x) = jBlock d L (N₀ i) (kl i) n (e i y))
    (A : ι → Set (Torus d (N₀w * L ^ kw)))
    (hΩ : ∀ i y, y ∈ A i → ∀ y', (y' = y ∨ Adj y y') →
      (y' ∈ Gw.Ω 1 ↔ e i y' ∈ (Gl i).Ω 1))
    (hlay : ∀ i y, y ∈ A i → Gw.layerIndex y = (Gl i).layerIndex (e i y))
    (hΨ : ∀ i y, y ∈ A i → y ∈ dataSites Gw → Dw.Ψ y = (Dl i).Ψ (e i y))
    (hcov : ∀ y ∈ dataSites Gw, ∃ i, y ∈ A i)
    (hpair : ∀ y y', IsInterfacePair Gw y y' → ∃ i, y ∈ A i ∧ y' ∈ A i)
    {ν δ : ℝ} (hdom : ∀ i, InDomainR (Gl i) ν δ (Dl i)) (h : Fin N → ℝ)
    (hh : ∀ y ∈ Gw.Ω 1, ∀ q, Dw.h y q = (h q : ℂ))
    (hhl : ∀ i, ∀ x ∈ (Gl i).Ω 1, ∀ q, (Dl i).h x q = (h q : ℂ))
    (hr4 : ν * ((L : ℝ) ^ kw) ^ 2 * |∑ q, h q ^ 2 - 1| < δ ^ 2) :
    InDomainR Gw ν δ Dw := by
  classical
  choose Ψl hl hP using hdom
  have hdomΨ : ∀ i, ∀ x ∈ dataSites (Gl i), ∀ q, (Dl i).Ψ x q = (Ψl i x q : ℂ) :=
    fun i => (hP i).2.1
  have hdomh : ∀ i, ∀ x ∈ (Gl i).Ω 1, ∀ q, (Dl i).h x q = (hl i q : ℂ) := fun i => (hP i).2.2
  -- data sites on a zone
  have hdata : ∀ i y, y ∈ A i → (y ∈ dataSites Gw ↔ e i y ∈ dataSites (Gl i)) := by
    intro i y hy
    rw [mem_dataSites, mem_dataSites, mem_collar, mem_collar]
    have h0 := hΩ i y hy y (Or.inl rfl)
    constructor
    · rintro (h1 | ⟨h1, x, hx, hxy⟩)
      · exact Or.inl (h0.1 h1)
      · refine Or.inr ⟨fun h2 => h1 (h0.2 h2), e i x, (hΩ i y hy x (Or.inr hxy.symm)).1 hx,
          adj_map_of_add_single (e i) (he i) hxy⟩
    · rintro (h1 | ⟨h1, x', hx', hxy⟩)
      · exact Or.inl (h0.2 h1)
      · have hadj : Adj y ((e i).symm x') :=
          adj_of_map_of_add_single (e i) (he i) (by rw [Equiv.apply_symm_apply]; exact hxy.symm)
        refine Or.inr ⟨fun h2 => h1 (h0.1 h2), (e i).symm x', ?_, hadj.symm⟩
        refine (hΩ i y hy _ (Or.inr hadj)).2 ?_
        rw [Equiv.apply_symm_apply]; exact hx'
  -- the external field of each local datum is `h` where it has a data site
  have hhi : ∀ i y, y ∈ A i → y ∈ dataSites Gw → hl i = h := by
    intro i y hy hyd
    have hd := (hdata i y hy).1 hyd
    obtain ⟨x, hx⟩ : ∃ x, x ∈ (Gl i).Ω 1 := by
      rcases (mem_dataSites _).1 hd with h1 | h1
      · exact ⟨_, h1⟩
      · obtain ⟨-, x, hx, -⟩ := (mem_collar _).1 h1
        exact ⟨x, hx⟩
    funext q
    have h1 := hdomh i x hx q
    rw [hhl i x hx q] at h1
    exact_mod_cast h1.symm
  -- the real field of the window datum
  have hreal : ∀ i y, y ∈ A i → y ∈ dataSites Gw → ∀ q,
      Dw.Ψ y q = (Ψl i (e i y) q : ℂ) := by
    intro i y hy hyd q
    rw [hΨ i y hy hyd, hdomΨ i _ ((hdata i y hy).1 hyd) q]
  refine ⟨fun y q => (Dw.Ψ y q).re, h, ⟨?_, ?_, ?_, ?_, hr4⟩, ?_, hh⟩
  · intro n hn1 hnk x hx x' hx'
    show (fun q => (Dw.Ψ x' q).re) = fun q => (Dw.Ψ x q).re
    rw [Dw.Ψ_layerConst n hn1 hnk x hx x' hx']
  · intro y y' hp
    obtain ⟨i, hy, hy'⟩ := hpair y y' hp
    obtain ⟨hyd, hy'd, hlayer, hba⟩ := hp
    have hre : ∀ z, z ∈ A i → z ∈ dataSites Gw → ∀ q,
        (Dw.Ψ z q).re = Ψl i (e i z) q := fun z hz hzd q => by
      rw [hreal i z hz hzd q]; simp
    simp only [hre y hy hyd, hre y' hy' hy'd]
    refine (hP i).1.r1 (e i y) (e i y') ⟨(hdata i y hy).1 hyd, (hdata i y' hy').1 hy'd, ?_, ?_⟩
    · rw [← hlay i y hy, ← hlay i y' hy']; exact hlayer
    · obtain ⟨z, hz, z', hz', hzz⟩ := hba
      have hmap : ∀ w, w ∈ A i → ∀ u, u ∈ blockSet Gw w → e i u ∈ blockSet (Gl i) (e i w) := by
        intro w hw u hu
        unfold blockSet at hu ⊢
        by_cases hw1 : w ∈ Gw.Ω 1
        · have hw1' := (hΩ i w hw w (Or.inl rfl)).1 hw1
          simp only [hw1, hw1', ite_true] at hu ⊢
          rw [GeneratingSet.mem_blk] at hu ⊢
          rw [← hlay i w hw]
          obtain ⟨-, hk, -⟩ := Gw.layerIndex_spec hw1
          obtain ⟨-, hk', -⟩ := (Gl i).layerIndex_spec hw1'
          rw [← hlay i w hw] at hk'
          exact hblk i _ hk hk' u w hu
        · have hw1' : e i w ∉ (Gl i).Ω 1 := fun h' => hw1 ((hΩ i w hw w (Or.inl rfl)).2 h')
          simp only [hw1, hw1', ite_false, Finset.mem_singleton] at hu ⊢
          rw [hu]
      exact ⟨e i z, hmap y hy z hz, e i z', hmap y' hy' z' hz',
        adj_map_of_add_single (e i) (he i) hzz⟩
  · intro y hyd
    obtain ⟨i, hy⟩ := hcov y hyd
    have : ∀ q, (Dw.Ψ y q).re = Ψl i (e i y) q := fun q => by rw [hreal i y hy hyd q]; simp
    simp only [this]
    exact (hP i).1.r2 _ ((hdata i y hy).1 hyd)
  · intro y hyd
    obtain ⟨i, hy⟩ := hcov y hyd
    have : ∀ q, (Dw.Ψ y q).re = Ψl i (e i y) q := fun q => by rw [hreal i y hy hyd q]; simp
    have hr3 := (hP i).1.r3 _ ((hdata i y hy).1 hyd)
    rw [hhi i y hy hyd, ← hlay i y hy] at hr3
    simp only [this]
    exact hr3
  · intro y hyd q
    obtain ⟨i, hy⟩ := hcov y hyd
    show Dw.Ψ y q = ((Dw.Ψ y q).re : ℂ)
    rw [hreal i y hy hyd q, Complex.ofReal_re]

end Zones

end Balaban.Background
