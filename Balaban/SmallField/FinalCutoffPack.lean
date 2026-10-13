/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.FinalCutoff
public import Balaban.Flow.StopIndex

/-!
# The final cutoff at the stop index, packaged

Algebraic packaging only.  The two landed cutoff lemmas `p4_cutoff_xi` and `p4_cutoff_reg` give,
at the stop index `kStop` with `0 < kStop`, the bound `|ψ_k(x) - h| < (5L+3) ε` on a site `x`
covered by a tested region, the mass factor being converted through `ν_k > (7/8) L⁻²`
(`kStop_spec`, so `1/√ν_k < √(8/7) L`).

* `final_cutoff_at_stop_of_cover`: the bound at one site, under the explicit disjunction "the site
  is covered by a tested region of type `ξ` (`XiBounds`) or of type reg (`BlockClose`,
  `FieldClose`)".
* `final_cutoff_family_of_cover`: the same at every site of a family of blocks, and the inclusion
  of the field into any set of fields that are `r`-close to `h` on the family, when
  `(5L+3) ε ≤ r`.  No final chart with an explicit radius is landed, so the inclusion is stated
  for such a closeness set.
* `final_cutoff_premises_const`: the premises hold for the constant configuration at the landed
  witness of `0 < kStop`.

The physical cover theorem (every integrated block is covered by a tested region, the tests hold
for the final density) and the last-integral bridges are NOT proved here.  Generator-neutral.
-/

@[expose] public section

namespace Balaban.FinalCutoff

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.SmallField
  Balaban.LargeField.StopIndex Balaban.Fluctuation Balaban.SmallField.Def6v2

section Pack

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {β ν₀ a ε₀ : ℝ} {b n : ℕ → ℝ}

/-- **Final cutoff at the stop index, under an explicit cover premise.**  If the site `x` is
covered by a tested region of type `ξ` or of type reg, then `n (kStop) < 1` and
`|ψ_k(x) - c| < (5L+3) ε`. -/
theorem final_cutoff_at_stop_of_cover (h : RunningHyp d L β ν₀ a ε₀ b n) (hpos : 0 < kStop h)
    (hL : 1 ≤ L) {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ} {ε : ℝ} {c : Fin N → ℂ}
    {x : Torus d (N₀ * L ^ k)}
    (hcover :
      (∃ (ν : ℝ) (m : ℕ) (h₀ : Fin N → ℝ) (α : G.Ω 1 → ℂ),
        XiBounds G ν m 1 ε D h₀ φ α ∧ 1 ≤ k ∧ ν * ((L : ℝ) ^ k) ^ 2 = n (kStop h) ∧
          x ∈ G.layer k ∧ ∀ i, (h₀ i : ℂ) = c i) ∨
      (∃ T S : Finset (Torus d (N₀ * L ^ k)),
        BlockClose G D φ T ε ∧ FieldClose G D φ (n (kStop h)) S ε ∧ x ∈ G.Ω 1 ∧ x ∈ T ∧
          (∀ y ∈ G.blk (G.layerIndex x) x, y ∈ S) ∧
          ∀ y ∈ G.blk (G.layerIndex x) x, ∀ i, D.h y i = c i)) :
    n (kStop h) < 1 ∧ vn (fun i => D.Ψ x i - c i) < (5 * L + 3) * ε := by
  rcases hcover with ⟨ν, m, h₀, α, hb, hk, hνk, hx, hc⟩ | ⟨T, S, hT, hS, hx, hxT, hblock, hc⟩
  · have := p4_cutoff_xi h hpos hb hk hL hνk hx
    have e : (fun i => D.Ψ x i - (h₀ i : ℂ)) = fun i => D.Ψ x i - c i := by
      funext i; rw [hc i]
    rw [e] at this
    exact this
  · exact p4_cutoff_reg h hpos hT hS hL hx hxT hblock hc

/-- **Family of blocks.**  If every site of `U` is covered by a tested region (of either type), the
bound `|ψ_k(x) - c| < (5L+3) ε` holds on all of `U`, and, if `(5L+3) ε ≤ r`, the field lies in the
set of fields `r`-close to `c` on `U`. -/
theorem final_cutoff_family_of_cover (h : RunningHyp d L β ν₀ a ε₀ b n) (hpos : 0 < kStop h)
    (hL : 1 ≤ L) {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ} {ε r : ℝ} {c : Fin N → ℂ}
    {U : Set (Torus d (N₀ * L ^ k))}
    (hcover : ∀ x ∈ U,
      (∃ (ν : ℝ) (m : ℕ) (h₀ : Fin N → ℝ) (α : G.Ω 1 → ℂ),
        XiBounds G ν m 1 ε D h₀ φ α ∧ 1 ≤ k ∧ ν * ((L : ℝ) ^ k) ^ 2 = n (kStop h) ∧
          x ∈ G.layer k ∧ ∀ i, (h₀ i : ℂ) = c i) ∨
      (∃ T S : Finset (Torus d (N₀ * L ^ k)),
        BlockClose G D φ T ε ∧ FieldClose G D φ (n (kStop h)) S ε ∧ x ∈ G.Ω 1 ∧ x ∈ T ∧
          (∀ y ∈ G.blk (G.layerIndex x) x, y ∈ S) ∧
          ∀ y ∈ G.blk (G.layerIndex x) x, ∀ i, D.h y i = c i))
    (hr : (5 * L + 3) * ε ≤ r) :
    (∀ x ∈ U, vn (fun i => D.Ψ x i - c i) < (5 * L + 3) * ε) ∧
      U ⊆ {x | vn (fun i => D.Ψ x i - c i) < r} := by
  have key : ∀ x ∈ U, vn (fun i => D.Ψ x i - c i) < (5 * L + 3) * ε :=
    fun x hx => (final_cutoff_at_stop_of_cover h hpos hL (hcover x hx)).2
  exact ⟨key, fun x hx => lt_of_lt_of_le (key x hx) hr⟩

/-- **Non-vacuity.**  At the landed running sequence with `0 < kStop` (`witness_kStop`), the
constant configuration `ψ ≡ e` (`constUnitBg`, `constUnitPhi`) satisfies the reg case of the cover
premise of `final_cutoff_at_stop_of_cover` at every site of `Ω₁`, with `ε = 1`, `c = e`. -/
theorem final_cutoff_premises_const (hd : 2 ≤ d) (hL : 2 ≤ L) (e : Fin N → ℝ)
    (he : ∑ i, e i ^ 2 = 1) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    ∃ (β ν : ℝ) (b n : ℕ → ℝ) (h : RunningHyp d L β ν (5 / 4) 0 b n), 0 < kStop h ∧
      ∃ T S : Finset (Torus d (N₀ * L ^ k)),
        BlockClose G (constUnitBg G e) (constUnitPhi G e) T 1 ∧
        FieldClose G (constUnitBg G e) (constUnitPhi G e) (n (kStop h)) S 1 ∧ x ∈ G.Ω 1 ∧ x ∈ T ∧
          (∀ y ∈ G.blk (G.layerIndex x) x, y ∈ S) ∧
          ∀ y ∈ G.blk (G.layerIndex x) x, ∀ i, (constUnitBg G e).h y i = (e i : ℂ) := by
  obtain ⟨β, ν, b, n, h, -, -, -, hpos, -⟩ := witness_kStop hd hL
  obtain ⟨T, S, hT, hS, hxT, hblock, hc, -⟩ :=
    regIneq_cutoff_const (G := G) e he (n_pos h (kStop h)) hx
  exact ⟨β, ν, b, n, h, hpos, T, S, hT, hS, hx, hxT, hblock, hc⟩

end Pack

end Balaban.FinalCutoff
