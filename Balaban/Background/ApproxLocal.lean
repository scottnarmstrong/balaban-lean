/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Interpolation
public import Balaban.Background.LocalSolution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The approximate field: definition and local facts (LEMMA53-astra.md, §4-§6 items 3-4)

* `locSol`: the local solution `φ^B` at a site (`cMinimizer`) of the block through the site, and
  at a collar site `φ^z = Ψ_z / √(Ψ_z ⬝ Ψ_z)`;
* `approxField`: the field `φ₀` of (5);
* `ApproxSetting`, `DataWit`: the standing hypotheses (BACKGROUND.md §1.3) and the decomposition of
  the data `Ψ + Ψ'`, `h + h'` of `InDomainC`;
* `locSol_facts`: `φ^B ⬝ φ^B = 1`, `|φ^B - Ψ_B| ≤ 500 δ`;
* `Ψ_adj_close`: data on adjacent blocks of neighbouring layers differ by at most `2 δ`;
* `locSol_chain`: all blocks active at a site of layer `n ≥ 2` have local solutions within a
  constant multiple of `δ` of the solution at the site (Lemma 5.3a(2), replaced version).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Defs

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The mass `ν L^{2n}` of the block through `y`, `n` the layer index of `y`. -/
noncomputable def blockMass (ν : ℝ) (y : Torus d (N₀ * L ^ k)) : ℝ :=
  ν * ((L : ℝ) ^ G.layerIndex y) ^ 2

open Classical in
/-- The local solution at a site: `φ^B` of the block `B ∋ y` for `y ∈ Ω₁`, and `φ^z` for a collar
site (and `0` elsewhere is never used). -/
noncomputable def locSol (a : ℕ → ℝ) (ν : ℝ) (Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (y : Torus d (N₀ * L ^ k)) : Fin N → ℂ :=
  if y ∈ G.Ω 1 then cMinimizer (a (G.layerIndex y)) (blockMass G ν y) (Ψ y) (h y)
  else cMinimizer 1 0 (Ψ y) 0

open Classical in
/-- **The approximate field** `φ₀` of (5): the local solution on layer one and on the collar, the
normalized interpolation on layers `≥ 2`, and `0` elsewhere. -/
noncomputable def approxField (a : ℕ → ℝ) (ν : ℝ) (Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) : Fin N → ℂ :=
  if x ∈ G.Ω 1 then
    (if G.layerIndex x ≤ 1 then locSol G a ν Ψ h x
     else normalize (interp G (locSol G a ν Ψ h) x))
  else if x ∈ collar G then locSol G a ν Ψ h x else 0

end Defs

section Setting

/-- The standing quantitative hypotheses (BACKGROUND.md §1.3, LEMMA53-astra.md §1). -/
structure ApproxSetting (d L k : ℕ) (ϱ : ℝ) (a : ℕ → ℝ) (ν δ ε : ℝ) : Prop where
  hϱ : (4 * d * L : ℝ) ≤ ϱ
  hd : 1 ≤ d
  hL : 2 ≤ L
  ha : IsAdmissibleWeights k a
  hν0 : 0 ≤ ν
  hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1
  hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2
  hδ0 : 0 < δ
  hδε : δ ≤ ε
  hε : ε ≤ 1 / 16
  hδ : δ ≤ 1 / 1024

/-- The decomposition of the data `D` into the real data `(Ψ, h₀)` of `InPsiTilde` and the complex
perturbations `(Ψ', h')`. -/
structure DataWit (G : GeneratingSet d L N₀ k ϱ) (ν δ ε : ℝ) (D : BgData G N) where
  Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ
  h₀ : Fin N → ℝ
  Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ
  h' : Torus d (N₀ * L ^ k) → Fin N → ℂ
  P : InPsiTildeC G ν δ ε Ψ h₀ Ψ' h'
  hΨ : ∀ x ∈ dataSites G, ∀ i, D.Ψ x i = (Ψ x i : ℂ) + Ψ' x i
  hh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h₀ i : ℂ) + h' x i

theorem DataWit.exists {G : GeneratingSet d L N₀ k ϱ} {ν δ ε : ℝ} {D : BgData G N}
    (h : InDomainC G ν δ ε D) :
    Nonempty (DataWit G ν δ ε D) := by
  obtain ⟨Ψ, h₀, Ψ', h', hP, hΨ, hh⟩ := h
  exact ⟨⟨Ψ, h₀, Ψ', h', hP, hΨ, hh⟩⟩

end Setting

section LocalFacts

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν δ ε : ℝ}
  {D : BgData G N}

theorem blockMass_le (S : ApproxSetting d L k ϱ a ν δ ε) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.Ω 1) :
    0 ≤ blockMass G ν y ∧ blockMass G ν y ≤ 1 := by
  obtain ⟨hm1, hmk, _⟩ := G.layerIndex_spec hy
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast (by have := S.hL; omega : 1 ≤ L)
  have hLm : ((L : ℝ) ^ G.layerIndex y) ^ 2 ≤ ((L : ℝ) ^ k) ^ 2 := by
    have := pow_le_pow_right₀ hL' hmk
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ L) (G.layerIndex y)]
  refine ⟨by unfold blockMass; have := S.hν0; positivity, ?_⟩
  unfold blockMass
  exact (mul_le_mul_of_nonneg_left hLm S.hν0).trans S.hν1

/-- The local solution at a site of `Ω₁ ∪ C`: `φ ⬝ φ = 1`, `|φ - Ψ| ≤ 500 δ`, and the blend has
positive real part (the point lies in the analytic domain). -/
theorem locSol_facts (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) :
    locSol G a ν D.Ψ D.h y ⬝ᵥ locSol G a ν D.Ψ D.h y = 1 ∧
    cNorm (locSol G a ν D.Ψ D.h y - D.Ψ y) ≤ 500 * δ ∧
    (1 / 8 : ℝ) ≤ (cBlend (if y ∈ G.Ω 1 then a (G.layerIndex y) else 1)
      (if y ∈ G.Ω 1 then blockMass G ν y else 0) (D.Ψ y) (if y ∈ G.Ω 1 then D.h y else 0) ⬝ᵥ
      cBlend (if y ∈ G.Ω 1 then a (G.layerIndex y) else 1)
      (if y ∈ G.Ω 1 then blockMass G ν y else 0) (D.Ψ y) (if y ∈ G.Ω 1 then D.h y else 0)).re ∧
    (y ∈ G.Ω 1 → ‖cMultiplier (a (G.layerIndex y)) (blockMass G ν y) (D.Ψ y) (D.h y)‖ ≤ 128 * δ) := by
  classical
  have hδ0 : 0 < δ := lt_of_le_of_lt (abs_nonneg _) (W.P.r2 y hy)
  obtain ⟨hΨn, hΨΨ⟩ := site_Ψ_hyp G W.P S.hδε S.hε hy (D.Ψ y) (W.hΨ y hy)
  by_cases hyΩ : y ∈ G.Ω 1
  · obtain ⟨hm1, hmk, _⟩ := G.layerIndex_spec hyΩ
    have ham := S.ha _ hm1 hmk
    obtain ⟨hB0, hB1⟩ := blockMass_le S hyΩ
    have hL1 : 1 ≤ L := by have := S.hL; omega
    have hH := site_H_hyp G W.P S.hδε S.hε S.hν0 S.hν1 S.hνε hL1 hyΩ (D.Ψ y) (D.h y)
      (W.hΨ y hy) (W.hh y hyΩ)
    have := local_solution (a := a (G.layerIndex y)) (ν := blockMass G ν y) (δ := δ)
      (Ψ := D.Ψ y) (H := D.h y) ham.1 ham.2 hB0 hB1 hδ0.le S.hδ hΨn hΨΨ hH
    simp only [locSol, hyΩ, ite_true]
    exact ⟨this.2.1, this.2.2.1, by simpa [hyΩ] using this.1, fun _ => this.2.2.2⟩
  · have hyC : y ∈ collar G := ((mem_dataSites G).1 hy).resolve_left hyΩ
    have := local_solution (a := 1) (ν := 0) (δ := δ) (Ψ := D.Ψ y) (H := 0) (by norm_num)
      (by norm_num) le_rfl zero_le_one hδ0.le S.hδ hΨn hΨΨ (by simp; linarith)
    simp only [locSol, hyΩ, ite_false]
    exact ⟨this.2.1, this.2.2.1, by simpa [hyΩ] using this.1, fun h => h.elim⟩

theorem locSol_norm_le (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) :
    cNorm (locSol G a ν D.Ψ D.h y) ≤ 2 := by
  obtain ⟨-, h2, -, -⟩ := locSol_facts S W hy
  obtain ⟨hΨn, -⟩ := site_Ψ_hyp G W.P S.hδε S.hε hy (D.Ψ y) (W.hΨ y hy)
  have := cNorm_add_le (locSol G a ν D.Ψ D.h y - D.Ψ y) (D.Ψ y)
  simp at this
  have h3 := S.hδ
  linarith


theorem Ψ_close_of_pair (W : DataWit G ν δ ε D) {y y' : Torus d (N₀ * L ^ k)}
    (hp : IsInterfacePair G y y') : cNorm (D.Ψ y - D.Ψ y') ≤ 2 * δ := by
  have hy : y ∈ dataSites G := hp.1
  have hy' : y' ∈ dataSites G := hp.2.1
  have h1 := W.P.r1 y y' hp
  have h2 := W.P.c1 y y' hp
  have e : D.Ψ y - D.Ψ y' = cplx (fun i => W.Ψ y i - W.Ψ y' i) + (W.Ψ' y - W.Ψ' y') := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, cplx, W.hΨ y hy, W.hΨ y' hy']
    push_cast; ring
  rw [e]
  refine (cNorm_add_le _ _).trans ?_
  rw [cNorm_cplx_eq_rn]
  have : cNorm (W.Ψ' y - W.Ψ' y') < δ := h2
  linarith

theorem Ψ_adj_close (W : DataWit G ν δ ε D) {y y' : Torus d (N₀ * L ^ k)}
    (hy : y ∈ dataSites G) (hy' : y' ∈ dataSites G) (hadj : Adj y y')
    (h1 : G.layerIndex y ≤ G.layerIndex y' + 1) (h2 : G.layerIndex y' ≤ G.layerIndex y + 1) :
    cNorm (D.Ψ y - D.Ψ y') ≤ 2 * δ := by
  have hself : ∀ z : Torus d (N₀ * L ^ k), z ∈ blockSet G z := fun z => by
    unfold blockSet
    split_ifs
    · exact G.mem_blk.2 rfl
    · exact Finset.mem_singleton_self z
  have hba : BlocksAdjacent G y y' := ⟨y, hself y, y', hself y', hadj⟩
  have hba' : BlocksAdjacent G y' y := ⟨y', hself y', y, hself y, hadj.symm⟩
  by_cases hc : G.layerIndex y' = G.layerIndex y ∨ G.layerIndex y' + 1 = G.layerIndex y
  · exact Ψ_close_of_pair W ⟨hy, hy', hc, hba⟩
  · have hc' : G.layerIndex y = G.layerIndex y' ∨ G.layerIndex y + 1 = G.layerIndex y' := by omega
    have := Ψ_close_of_pair W (y := y') (y' := y) ⟨hy', hy, hc', hba'⟩
    have e : cNorm (D.Ψ y - D.Ψ y') = cNorm (D.Ψ y' - D.Ψ y) := vn_sub_comm _ _
    linarith


theorem locSol_adj (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) (hy' : y' ∈ dataSites G)
    (hadj : Adj y y') (h1 : G.layerIndex y ≤ G.layerIndex y' + 1)
    (h2 : G.layerIndex y' ≤ G.layerIndex y + 1) :
    cNorm (locSol G a ν D.Ψ D.h y - locSol G a ν D.Ψ D.h y') ≤ 1002 * δ := by
  obtain ⟨-, f1, -, -⟩ := locSol_facts S W hy
  obtain ⟨-, f2, -, -⟩ := locSol_facts S W hy'
  have f3 := Ψ_adj_close W hy hy' hadj h1 h2
  have e : locSol G a ν D.Ψ D.h y - locSol G a ν D.Ψ D.h y' =
      (locSol G a ν D.Ψ D.h y - D.Ψ y) + (D.Ψ y - D.Ψ y') +
        (D.Ψ y' - locSol G a ν D.Ψ D.h y') := by
    funext i; simp [Pi.sub_apply, Pi.add_apply]
  rw [e]
  have t1 := cNorm_add_le (locSol G a ν D.Ψ D.h y - D.Ψ y) (D.Ψ y - D.Ψ y')
  have t2 := cNorm_add_le (locSol G a ν D.Ψ D.h y - D.Ψ y + (D.Ψ y - D.Ψ y'))
    (D.Ψ y' - locSol G a ν D.Ψ D.h y')
  have e2 : cNorm (D.Ψ y' - locSol G a ν D.Ψ D.h y') =
      cNorm (locSol G a ν D.Ψ D.h y' - D.Ψ y') := vn_sub_comm _ _
  linarith

/-- The data oscillation along the chain from `x` (layer `n ≥ 2`) to a block active at `x`. -/
theorem Ψ_chain (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D) {n : ℕ} (hn2 : 2 ≤ n)
    (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n)
    {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ active G x) :
    cNorm (D.Ψ q.2 - D.Ψ x) ≤ 2 * δ * (d * ((L : ℝ) ^ 2 + 1)) := by
  have hδ0 : 0 ≤ δ := by
    have hx1 : x ∈ dataSites G :=
      (mem_dataSites G).2 (Or.inl (G.layer_subset (by omega) hnk hx))
    exact (lt_of_le_of_lt (abs_nonneg _) (W.P.r2 x hx1)).le
  obtain ⟨hqi, hne⟩ := (mem_active G).1 hq
  obtain ⟨⟨hm1, hmk⟩, hql, hqb⟩ := (mem_blockIdx G).1 hqi
  obtain ⟨hl1, hl2⟩ := active_layer_bounds G S.hϱ S.hd (by have := S.hL; omega) (by omega) hnk hx
    (torusDist_self_le x) hq
  obtain ⟨t, u, ht, hz, hj, hd⟩ := active_lift G hqi hne
  set z : Torus d (N₀ * L ^ k) := intTorus u with hzdef
  have hzΩ : z ∈ G.Ω q.1 := (G.mem_layer.1 hz).1
  have hxΩ : x ∈ G.Ω n := (G.mem_layer.1 hx).1
  let E := EuclideanSpace ℂ (Fin N)
  let f : Torus d (N₀ * L ^ k) → E := fun y => WithLp.toLp 2 (D.Ψ y)
  have hfn : ∀ y y', ‖f y - f y'‖ = cNorm (D.Ψ y - D.Ψ y') := fun y y' => by
    simp only [f, cNorm]; rw [← WithLp.toLp_sub]
  have hΩ1 : ∀ y, y ∈ G.Ω (n - 1) → y ∈ G.Ω 1 :=
    fun y hy => G.Ω_antitone le_rfl (by omega) (by omega) hy
  have hstep : ∀ y y', y ∈ G.Ω (n - 1) → y' ∈ G.Ω (n - 1) → Adj y y' → ‖f y' - f y‖ ≤ 2 * δ := by
    intro y y' hy hy' hadj
    have hy1 := hΩ1 y hy
    have hy1' := hΩ1 y' hy'
    rw [hfn]
    refine Ψ_adj_close W ((mem_dataSites G).2 (Or.inl hy1')) ((mem_dataSites G).2 (Or.inl hy1))
      hadj.symm ?_ ?_
    · exact layerIndex_le_succ_of_adj G S.hϱ S.hd (by have := S.hL; omega) hy1' hy1 hadj.symm
    · exact layerIndex_le_succ_of_adj G S.hϱ S.hd (by have := S.hL; omega) hy1 hy1' hadj
  have hcell : ∀ y y', y ∈ G.Ω (n - 1) → y' ∈ G.Ω (n - 1) →
      jBlock d L N₀ k (n - 1) y = jBlock d L N₀ k (n - 1) y' → f y' = f y := by
    intro y y' hy hy' hc
    have hlay := layerIndex_eq_of_cell_eq G (by omega) (by omega) hy hc
    have hy1 := hΩ1 y hy
    obtain ⟨hm1', hmk', hyl⟩ := G.layerIndex_spec hy1
    have hge := (mem_Ω_iff_le_layerIndex G hy1 (by omega) (by omega)).1 hy
    have hjm := jBlock_mono (by omega : n - 1 ≤ G.layerIndex y) hmk' hc
    have : y' ∈ G.blk (G.layerIndex y) y := G.mem_blk.2 hjm.symm
    simp only [f, D.Ψ_layerConst _ hm1' hmk' y hyl y' this]
  have hmain := chain_to_block G S.hϱ S.hd (by have := S.hL; omega) f (2 * δ) (by linarith)
    hn2 hnk hmk hl2 hl1 hstep hcell hxΩ hzΩ t u (fun μ => by rw [ht μ]) (fun μ => rfl) hd
  have hzblk : z ∈ G.blk q.1 q.2 := G.mem_blk.2 hj
  have : D.Ψ z = D.Ψ q.2 := D.Ψ_layerConst _ hm1 hmk q.2 hql z hzblk
  rw [hfn, this] at hmain
  exact hmain


/-- The closeness constants: `A₁ = 1000 + 2 d (L² + 1)`, `A₂ = A₁ + 1002`. -/
noncomputable def cA1 (d L : ℕ) : ℝ := 1000 + 2 * (d * ((L : ℝ) ^ 2 + 1))
noncomputable def cA2 (d L : ℕ) : ℝ := cA1 d L + 1002

theorem cA1_pos (d L : ℕ) : 0 < cA1 d L := by unfold cA1; positivity

theorem locSol_chain (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D) {n : ℕ}
    (hn2 : 2 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n)
    {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ active G x) :
    cNorm (locSol G a ν D.Ψ D.h q.2 - locSol G a ν D.Ψ D.h x) ≤ cA1 d L * δ := by
  have hx1 : x ∈ dataSites G :=
    (mem_dataSites G).2 (Or.inl (G.layer_subset (by omega) hnk hx))
  obtain ⟨hqi, hne⟩ := (mem_active G).1 hq
  obtain ⟨⟨hm1, hmk⟩, hql, hqb⟩ := (mem_blockIdx G).1 hqi
  have hq1 : q.2 ∈ dataSites G := (mem_dataSites G).2 (Or.inl (G.layer_subset hm1 hmk hql))
  obtain ⟨-, f1, -, -⟩ := locSol_facts S W hq1
  obtain ⟨-, f2, -, -⟩ := locSol_facts S W hx1
  have f3 := Ψ_chain S W hn2 hnk hx hq
  have e : locSol G a ν D.Ψ D.h q.2 - locSol G a ν D.Ψ D.h x =
      (locSol G a ν D.Ψ D.h q.2 - D.Ψ q.2) + (D.Ψ q.2 - D.Ψ x) +
        (D.Ψ x - locSol G a ν D.Ψ D.h x) := by
    funext i; simp [Pi.sub_apply, Pi.add_apply]
  rw [e]
  have t1 := cNorm_add_le (locSol G a ν D.Ψ D.h q.2 - D.Ψ q.2) (D.Ψ q.2 - D.Ψ x)
  have t2 := cNorm_add_le (locSol G a ν D.Ψ D.h q.2 - D.Ψ q.2 + (D.Ψ q.2 - D.Ψ x))
    (D.Ψ x - locSol G a ν D.Ψ D.h x)
  have e2 : cNorm (D.Ψ x - locSol G a ν D.Ψ D.h x) =
      cNorm (locSol G a ν D.Ψ D.h x - D.Ψ x) := vn_sub_comm _ _
  unfold cA1
  nlinarith

/-- All blocks active at `x` or at a neighbour have local solutions within `A₂ δ` of that of
`x` (`n ≥ 3`). -/
theorem locSol_supp_close (S : ApproxSetting d L k ϱ a ν δ ε) (W : DataWit G ν δ ε D) {n : ℕ}
    (hn3 : 3 ≤ n) (hnk : n ≤ k) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer n) (μ : Fin d)
    {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ supp G x μ) :
    cNorm (locSol G a ν D.Ψ D.h q.2 - locSol G a ν D.Ψ D.h x) ≤ cA2 d L * δ := by
  have hL1 : 1 ≤ L := by have := S.hL; omega
  have hδ0 : 0 ≤ δ := by
    have hx1 : x ∈ dataSites G :=
      (mem_dataSites G).2 (Or.inl (G.layer_subset (by omega) hnk hx))
    exact (lt_of_le_of_lt (abs_nonneg _) (W.P.r2 x hx1)).le
  have h1 := cA1_pos d L
  have key : ∀ x', Adj x x' → q ∈ active G x' →
      cNorm (locSol G a ν D.Ψ D.h q.2 - locSol G a ν D.Ψ D.h x) ≤ cA2 d L * δ := by
    intro x' hadj hqa
    obtain ⟨n', h11, h1k, hx'⟩ := exists_layer_adj G S.hϱ S.hd hL1 (by omega) hnk hx hadj
    have hx1 : x ∈ G.Ω 1 := G.layer_subset (by omega) hnk hx
    have hx'1 : x' ∈ G.Ω 1 := G.layer_subset h11 h1k hx'
    have hln' : G.layerIndex x' = n' := G.layerIndex_eq h11 h1k hx'
    have hlx : G.layerIndex x = n := G.layerIndex_eq (by omega) hnk hx
    have hj1 := layerIndex_le_succ_of_adj G S.hϱ S.hd hL1 hx1 hx'1 hadj
    have hj2 := layerIndex_le_succ_of_adj G S.hϱ S.hd hL1 hx'1 hx1 hadj.symm
    have c1 := locSol_chain S W (n := n') (by omega) h1k hx' hqa
    have c2 := locSol_adj S W ((mem_dataSites G).2 (Or.inl hx'1)) ((mem_dataSites G).2 (Or.inl hx1))
      hadj.symm (by omega) (by omega)
    have e : locSol G a ν D.Ψ D.h q.2 - locSol G a ν D.Ψ D.h x =
        (locSol G a ν D.Ψ D.h q.2 - locSol G a ν D.Ψ D.h x') +
          (locSol G a ν D.Ψ D.h x' - locSol G a ν D.Ψ D.h x) := by
      funext i; simp [Pi.sub_apply, Pi.add_apply]
    rw [e]
    have t := cNorm_add_le (locSol G a ν D.Ψ D.h q.2 - locSol G a ν D.Ψ D.h x')
      (locSol G a ν D.Ψ D.h x' - locSol G a ν D.Ψ D.h x)
    unfold cA2
    nlinarith
  simp only [supp, Finset.mem_union] at hq
  rcases hq with (h | h) | h
  · have := locSol_chain S W (by omega) hnk hx h
    have : cA1 d L * δ ≤ cA2 d L * δ := by
      unfold cA2; nlinarith
    linarith
  · exact key _ (adj_add x μ) h
  · exact key _ (adj_sub x μ) h

end LocalFacts

end Balaban.Background
