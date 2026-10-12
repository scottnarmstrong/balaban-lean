/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiProps
public import Balaban.SmallField.XiLevel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (D1-j), complex data: `Ξ^c_j(𝔹; σ, ε) ⊆ Ψ̃^c_{j|k}(𝔹; C₁ σ ε, ε)`

`notes/phase1/MASS-LEVEL.md` §3.  For a generating set with `Ω_{j+1} = ∅` the level-`j` space
`Ξ^c_j` lies in the level-`j` data domain `Ψ̃^c_{j|k}`; the proof is that of `xiC_inPsiTildeC` with
the mass `ν L^{2j}` in the norm clause.

* `Balaban.SmallField.xiC_inPsiTildeCLevel`: the general form (as `xiC_inPsiTildeC`);
* `Balaban.SmallField.xiC_subset_psiTildeCLevel`: **(D1-j)** with `δ = C₁ σ ε`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν σ ε : ℝ}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- The level-`j` form of `xiC_inPsiTildeC`. -/
theorem xiC_inPsiTildeCLevel (H : BgHyp d L k ϱ a ν) {j : ℕ} (hΩ : G.Ω (j + 1) = ∅) (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    (hε1 : ε ≤ 1) (hsmall : (4 * d + 6) * xiEta d σ ε ≤ 1) {δ' ε'' : ℝ}
    (hδ : compC4 d * xiEta d σ ε ≤ δ') (hεε : ε ≤ ε'') (hrat : (σ * ε) ^ 2 / ε ≤ δ' ^ 2 / ε'')
    (hX : XiC G a ν j σ ε Ψ₀ h₀ Ψ'' h'') : InPsiTildeCLevel G ν j δ' ε'' Ψ₀ h₀ Ψ'' h'' := by
  obtain ⟨-, -, Dr, Dc, hXr, hC, hDc, hb⟩ := hX
  have hXr' := hXr
  obtain ⟨hR, hDomR, hbr⟩ := hXr
  have hηpos : 0 < xiEta d σ ε := xiEta_pos hσ hε
  have hση : σ * ε ≤ xiEta d σ ε := le_xiEta hσ hε
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast H.hd
  have hC4 : compC4 d * xiEta d σ ε = (4 * d + 8) * xiEta d σ ε := rfl
  have hδ' : (4 * (d : ℝ) + 8) * xiEta d σ ε ≤ δ' := by rw [← hC4]; exact hδ
  have hε'' : 0 < ε'' := hε.trans_le hεε
  have hA : 0 < σ * ε := mul_pos hσ hε
  have hσ2 : σ ^ 2 * ε ≤ σ * ε := by nlinarith
  obtain ⟨hφre, hunr⟩ := xi_unit H hXr'
  have hunc := xiC_unit H hDc
  have hcl := (xi_fieldBounds H hσ hε hσ1 hXr').close
  have hsr := xi_smooth hσ hε hσ1 hbr
  have hr2 := fun x (hx : x ∈ G.Ω 1) => xi_r2_site_level H hσ hε hσ1 hsmall hXr' hx
  have hreal := (xi_inPsiTildeLevel H hΩ hσ hε hσ1 hsmall hXr').mono (mul_nonneg (by unfold compC4; positivity) hηpos.le) hδ
  refine ⟨hreal, hε'', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- layer constancy of Ψ''
    intro n hn1 hnk x hx x' hx'
    have hxΩ : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
    have hx'l : x' ∈ G.layer n := (G.mem_layer_iff hn1 hnk (GeneratingSet.mem_blk.1 hx')).2 hx
    have hx'Ω : x' ∈ G.Ω 1 := G.layer_subset hn1 hnk hx'l
    funext i
    rw [psi''_eq hR hC ((mem_dataSites G).2 (Or.inl hx'Ω)) i,
      psi''_eq hR hC ((mem_dataSites G).2 (Or.inl hxΩ)) i,
      congrFun (Dc.Ψ_layerConst n hn1 hnk x hx x' hx') i,
      congrFun (Dr.Ψ_layerConst n hn1 hnk x hx x' hx') i]
  · -- layer constancy of h''
    intro n hn1 hnk x hx x' hx'
    have hxΩ : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
    have hx'l : x' ∈ G.layer n := (G.mem_layer_iff hn1 hnk (GeneratingSet.mem_blk.1 hx')).2 hx
    have hx'Ω : x' ∈ G.Ω 1 := G.layer_subset hn1 hnk hx'l
    funext i
    rw [h''_eq hR hC hx'Ω i, h''_eq hR hC hxΩ i,
      congrFun (Dc.h_layerConst n hn1 hnk x hx x' hx') i,
      congrFun (Dr.h_layerConst n hn1 hnk x hx x' hx') i]
  · -- (C1)
    intro x x' hxx'
    have h1 := xiC_c1 hσ hε hσ1 hR hC hb hxx'
    refine h1.trans_lt (lt_of_lt_of_le ?_ hδ')
    unfold xiEta
    nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hA.le]
  · -- (C2a)
    intro x hx
    have h1 := xiC_size hσ hε hσ1 hR hC hb hx
    refine h1.trans_le ?_
    nlinarith
  · -- (C2b)
    intro x hx
    rcases (mem_dataSites G).1 hx with hx1 | hx1
    · have := xiC_c2b_site hσ hε hσ1 hε1 hR hC hb hφre hunr hunc hcl hx1
      refine this.trans_lt (lt_of_lt_of_le ?_ hδ')
      nlinarith
    · have := xiC_c2b_collar hσ hε hσ1 hε1 hR hC hb hφre hunr hunc hsr hx1
      refine this.trans_lt (lt_of_lt_of_le ?_ hδ')
      nlinarith
  · -- (C3a)
    intro x hx
    exact (hb.hAbs x hx).trans_le hrat
  · -- (C3b)
    intro x hx
    refine xiC_c3b hσ hε hσ1 H.mass hb hcl hR ?_ hr2 hsmall hx
    nlinarith


/-- **(D1-j)**: for `Ω_{j+1} = ∅` (the generating set has no active layer above `j`),
`Ξ^c_j(𝔹; σ, ε) ⊆ Ψ̃^c_{j|k}(𝔹; C₁ σ ε, ε)`, for `σ, ε ≤ 1`, `(4d+6)(2d+1) σ ε ≤ 1`
(MASS-LEVEL.md (D1-j); the level-`j` analogue of `xiC_subset_psiTildeC`). -/
theorem xiC_subset_psiTildeCLevel (H : BgHyp d L k ϱ a ν) {j : ℕ} (hΩ : G.Ω (j + 1) = ∅)
    (hσ1 : σ ≤ 1) (hε1 : ε ≤ 1) (hsmall : (4 * d + 6) * ((2 * d + 1) * (σ * ε)) ≤ 1)
    (hX : XiC G a ν j σ ε Ψ₀ h₀ Ψ'' h'') :
    InPsiTildeCLevel G ν j (xiC1 d * (σ * ε)) ε Ψ₀ h₀ Ψ'' h'' := by
  have hσ := hX.1
  have hε := hX.2.1
  have hc1 := one_le_xiC1 d
  refine xiC_inPsiTildeCLevel H hΩ hσ hε hσ1 hε1 hsmall (δ' := xiC1 d * (σ * ε)) (ε'' := ε)
    (by rw [compC4_mul_xiEta]) le_rfl ?_ hX
  have h1 : (σ * ε) ^ 2 / ε ≤ (xiC1 d * (σ * ε)) ^ 2 / ε := by
    refine div_le_div_of_nonneg_right ?_ hε.le
    have := mul_pos hσ hε
    exact pow_le_pow_left₀ this.le (le_mul_of_one_le_left this.le hc1) 2
  exact h1

end Balaban.SmallField
