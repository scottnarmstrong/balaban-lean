/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.DataPatchScaled

/-!
# The split of a cube test read at the sites of a datum

The datum of the local pair of the step on a region (reading HS-2) is patched from the splits of the
cube tests of the target H7 domain (`inDomainC_of_patch_scaled`).  Each test lives on its own generating
set `G_c` (a cube set of `𝕋_{k+1}` or of `𝕋_k`, on its own torus); its split is read at the sites of the
datum through a map `t` of the tori that respects adjacency and the blocks.  This file states, for one
chart, every condition of the patching lemma that the split of the chart gives at a site `x` and at
its interface partners, from the conditions of `Ψ̃^c(G_c; ε_c, ε_c)`.

* `chartSplit_spec`: layer constancy at `x`, the value of the datum, (R2), (C2a), (C2b), condition (R3) in
  the large-mass regime (`r3_of_large_mass`), and the conditions at the interface pairs of `x`, for the
  split `(Ψ, Ψ') ∘ t` of a chart whose sites `In` (containing `x` and its interface partners) lie in
  `Ω₁(G_c)` at a layer at least their own, within one layer of the top of `G_c`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {N : ℕ}

/-- **The conditions of the patching lemma given by the split of one chart.**  A cube test with
generating set `G_c` (top layer `q`) whose datum `D_c` has the split `(Ψ, h, Ψ', h') ∈ Ψ̃^c(G_c; ε_c, ε_c)`,
`ε_c ≤ ε`, with real external field `h₀`, read at the sites of `G` through a map `t` that respects
adjacency and sends the block of `y` of its layer into the block of `t(x)` of every layer `l` with
`l_G(x) ≤ l ≤ q` (`hblk`).  For a site `x` of the chart (`In`: `t(x) ∈ Ω₁(G_c)`, the datum `D` at `x` is
`f(x)` times the datum of the test at `t(x)`, the layer of `t(x)` is at least that of `x` and within one of
`q`), the split `Φ = Ψ ∘ t`, `Φ' = Ψ' ∘ t` gives at `x`: layer constancy, the value `D(x) = f(x)(Φ + Φ')`,
(R2), (C2a), (C2b) at tolerance `ε`, (R3) with `2ε²` for every mass `ν ≤ μ_c` (the mass of the test), and,
at every interface partner `x'` of `x` in the chart, the interface conditions (R1), (C1) and the conditions
of `x'` for the split of `x`. -/
theorem chartSplit_spec (D : BgData G N) (f : Torus d (N₀ * L ^ k) → ℝ) (h₀ : Fin N → ℝ)
    {N₀' q : ℕ} [NeZero N₀'] {ϱ' : ℝ} {Gc : GeneratingSet d L N₀' q ϱ'} {Dc : BgData Gc N}
    {μc εc ε : ℝ} {Ψr : Torus d (N₀' * L ^ q) → Fin N → ℝ} {hr : Fin N → ℝ}
    {Ψ' h' : Torus d (N₀' * L ^ q) → Fin N → ℂ}
    (hP : InPsiTildeC Gc μc εc εc Ψr hr Ψ' h') (hεc : εc ≤ ε)
    (hΨ : ∀ s ∈ dataSites Gc, ∀ i, Dc.Ψ s i = (Ψr s i : ℂ) + Ψ' s i)
    (hhr : ∀ s ∈ Gc.Ω 1, ∀ i, Dc.h s i = (hr i : ℂ) + h' s i)
    (hh0 : ∀ s ∈ Gc.Ω 1, ∀ i, Dc.h s i = (h₀ i : ℂ))
    (t : Torus d (N₀ * L ^ k) → Torus d (N₀' * L ^ q))
    (hadj : ∀ y y', Adj y y' → Adj (t y) (t y'))
    (hblk : ∀ x y, y ∈ blockSet G x → ∀ l, G.layerIndex x ≤ l → l ≤ q → t y ∈ Gc.blk l (t x))
    (In : Torus d (N₀ * L ^ k) → Prop)
    (hIn : ∀ y, In y → t y ∈ Gc.Ω 1 ∧ (∀ i, D.Ψ y i = (f y : ℂ) * Dc.Ψ (t y) i) ∧
      G.layerIndex y ≤ Gc.layerIndex (t y) ∧ q ≤ Gc.layerIndex (t y) + 1)
    (Φ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (Φ' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hΦ : ∀ y, Φ y = Ψr (t y) ∧ Φ' y = Ψ' (t y))
    {x : Torus d (N₀ * L ^ k)} (hx : In x) :
    (∀ j, 1 ≤ j → j ≤ k → x ∈ G.layer j → ∀ x' ∈ G.blk j x, Φ x' = Φ x ∧ Φ' x' = Φ' x) ∧
    (∀ i, D.Ψ x i = (f x : ℂ) * ((Φ x i : ℂ) + Φ' x i)) ∧
    |∑ i, Φ x i ^ 2 - 1| < ε ∧
    vn (Φ' x) < ε + ε ∧
    ‖∑ i, ((Φ x i : ℂ) + Φ' x i) * ((Φ x i : ℂ) + Φ' x i) - ∑ i, (Φ x i : ℂ) * (Φ x i : ℂ)‖ < ε ∧
    (∀ ν : ℝ, 0 ≤ ν → ν ≤ μc →
      ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * |1 - (∑ i, Φ x i * h₀ i) / rn (Φ x)| < 2 * ε ^ 2) ∧
    (∀ x', IsInterfacePair G x x' → In x' →
      rn (fun i => Φ x i - Φ x' i) < ε ∧ vn (Φ' x - Φ' x') < ε ∧
      (∀ i, D.Ψ x' i = (f x' : ℂ) * ((Φ x' i : ℂ) + Φ' x' i)) ∧
      vn (Φ' x') < ε + ε ∧ |∑ i, Φ x' i ^ 2 - 1| < ε) := by
  classical
  have hΦr : Φ = fun y => Ψr (t y) := funext fun y => (hΦ y).1
  have hΦc : Φ' = fun y => Ψ' (t y) := funext fun y => (hΦ y).2
  subst hΦr hΦc
  obtain ⟨h1, hdat, hlG, hq⟩ := hIn x hx
  have h2 : t x ∈ dataSites Gc := (mem_dataSites _).2 (Or.inl h1)
  obtain ⟨hl1, hlq, hlay⟩ := Gc.layerIndex_spec h1
  have hεc0 : 0 < εc := hP.eps_pos
  have hbs : ∀ s, s ∈ Gc.Ω 1 → blockSet Gc s = Gc.blk (Gc.layerIndex s) s := fun s hs => by
    unfold blockSet; simp only [hs, ↓reduceIte]
  refine ⟨fun j hj1 hjk hxj x' hx' => ?_, fun i => by rw [hdat i, hΨ _ h2 i],
    (hP.r2 _ h2).trans_le hεc, by have := hP.c2a _ h2; linarith, (hP.c2b _ h2).trans_le hεc,
    fun ν hν hνμ => ?_, fun x' hp hx' => ?_⟩
  · -- layer constancy
    have hx1 : x ∈ G.Ω 1 := G.Ω_antitone le_rfl hj1 (by omega) (G.mem_layer.1 hxj).1
    have hjx : G.layerIndex x = j := G.layerIndex_eq hj1 hjk hxj
    have hbx : x' ∈ blockSet G x := by
      unfold blockSet; simp only [hx1, ↓reduceIte, hjx]; exact hx'
    have hb := hblk x x' hbx _ hlG hlq
    exact ⟨hP.layerConst _ hl1 hlq _ hlay _ hb, hP.layerConst' _ hl1 hlq _ hlay _ hb⟩
  · -- (R3) in the large-mass regime
    have hh' : ∀ i, h' (t x) i = ((h₀ i - hr i : ℝ) : ℂ) := fun i => by
      have e1 := hhr _ h1 i
      have e2 := hh0 _ h1 i
      push_cast
      linear_combination e2 - e1
    have h3 := r3_of_large_mass hν hνμ (Nat.one_le_iff_ne_zero.2 (NeZero.ne L)) hlG _ hr h₀ _ hh'
      (hP.r3 _ h2) (hP.c3b _ h1)
    have : εc ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hεc0.le hεc 2
    linarith
  · -- the interface pairs
    obtain ⟨h1', hdat', hlG', hq'⟩ := hIn x' hx'
    have h2' : t x' ∈ dataSites Gc := (mem_dataSites _).2 (Or.inl h1')
    obtain ⟨-, hlq', -⟩ := Gc.layerIndex_spec h1'
    obtain ⟨-, -, -, y₀, hy₀, y₀', hy₀', hadj₀⟩ := hp
    have hy₀c : t y₀ ∈ blockSet Gc (t x) := by
      rw [hbs _ h1]; exact hblk x y₀ hy₀ _ hlG hlq
    have hy₀c' : t y₀' ∈ blockSet Gc (t x') := by
      rw [hbs _ h1']; exact hblk x' y₀' hy₀' _ hlG' hlq'
    have hadjc := hadj _ _ hadj₀
    have hpair : rn (fun i => Ψr (t x) i - Ψr (t x') i) < εc ∧ vn (Ψ' (t x) - Ψ' (t x')) < εc := by
      by_cases hlay' : Gc.layerIndex (t x') = Gc.layerIndex (t x) ∨
          Gc.layerIndex (t x') + 1 = Gc.layerIndex (t x)
      · have hI : IsInterfacePair Gc (t x) (t x') := ⟨h2, h2', hlay', _, hy₀c, _, hy₀c', hadjc⟩
        exact ⟨hP.r1 _ _ hI, hP.c1 _ _ hI⟩
      · have hlay'' : Gc.layerIndex (t x) + 1 = Gc.layerIndex (t x') := by omega
        have hI : IsInterfacePair Gc (t x') (t x) :=
          ⟨h2', h2, Or.inr hlay'', _, hy₀c', _, hy₀c, hadjc.symm⟩
        refine ⟨?_, ?_⟩
        · have e : rn (fun i => Ψr (t x) i - Ψr (t x') i) = rn (fun i => Ψr (t x') i - Ψr (t x) i) := by
            unfold rn; congr 1; exact Finset.sum_congr rfl fun i _ => by ring
          rw [e]; exact hP.r1 _ _ hI
        · rw [vn_sub_comm]; exact hP.c1 _ _ hI
    refine ⟨hpair.1.trans_le hεc, hpair.2.trans_le hεc, fun i => by rw [hdat' i, hΨ _ h2' i], ?_,
      (hP.r2 _ h2').trans_le hεc⟩
    have := hP.c2a _ h2'
    linarith

end Balaban.Background
