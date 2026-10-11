/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Existence
public import Balaban.Background.ApproxAnalytic
public import Balaban.Background.ContractionAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 5.2: existence, bounds, uniqueness, comparison and analyticity (BACKGROUND.md §5.2)

For the standing hypotheses `BgHyp` and constants `c₀ = bgC0`, `c₁ = bgC1`, `K₁ = bgK1` (functions
of `(d, L, N)` only):

* `theorem52_exists` (items 1, 3): for data in `Ψ̃^c(δ, ε)` with `δ ≤ c₁`, `ε ≤ c₀`,
  `ν L^{2k} ε² ≤ δ²`, a small solution exists, satisfies the bounds P2 (1.15) with constant
  `K₁ δ`, and is the only solution of (EL) with `|α|₂ < c₀`;
* `theorem52_compare` (item 3, last line): `|φ^c - φ^r| ≤ ε + K₁ δ` for the complex data and the
  corresponding real data;
* `theorem52_analytic` (item 2): one analytic function of the raw data `(Ψ, h̃)` on all data of
  the union domain `𝒟` that returns the small solution.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Exists

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν δ ε : ℝ} {D : BgData G N}

/-- **Theorem 5.2 (1), (3)** (existence, the bounds P2 (1.15), uniqueness in the class
`|α|₂ < c₀`). -/
theorem theorem52_exists (H : BgHyp d L k ϱ a ν) (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ bgC1 d L N) (hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (hD : InDomainC G ν δ ε D) :
    ∃ (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ),
      IsSmallSolution G a ν (bgC0 d L N) D φ α ∧ BgBounds G D φ α (bgK1 d L N * δ) ∧
      ∀ (φ' : G.Ω 1 × Fin N → ℂ) (α' : G.Ω 1 → ℂ),
        IsSmallSolution G a ν (bgC0 d L N) D φ' α' → φ' = φ ∧ α' = α := by
  obtain ⟨W⟩ := DataWit.exists hD
  obtain ⟨φ, α, h1, h2, -, h4⟩ := bg_core H hδ0 hδε hε hδ hνε W
  exact ⟨φ, α, h1, h2, h4⟩

/-- **Theorem 5.2 (3), last line**: for a decomposition `W` of the complex data and the
corresponding real data `Dr`, the small solutions satisfy `|φ^c - φ^r|₀ ≤ ε + K₁ δ`. -/
theorem theorem52_compare (H : BgHyp d L k ϱ a ν) (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ bgC1 d L N) (hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (W : DataWit G ν δ ε D) (Dr : BgData G N)
    (hΨr : ∀ x ∈ dataSites G, ∀ i, Dr.Ψ x i = (W.Ψ x i : ℂ))
    (hhr : ∀ x ∈ G.Ω 1, ∀ i, Dr.h x i = (W.h₀ i : ℂ))
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hs : IsSmallSolution G a ν (bgC0 d L N) D φ α)
    {φr : G.Ω 1 × Fin N → ℂ} {αr : G.Ω 1 → ℂ}
    (hsr : IsSmallSolution G a ν (bgC0 d L N) Dr φr αr) (x : G.Ω 1) :
    vn (fun i => φ (x, i) - φr (x, i)) ≤ ε + bgK1 d L N * δ := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨hδa, -, hC32, -⟩ := bgC1_facts d L N hd0 hδ
  have S : ApproxSetting d L k ϱ a ν δ ε :=
    H.approxSetting hδ0 hδε (hε.trans (bgC0_le d L N)) (approxDelta_le d L hδa).1 hνε
  have Wr := DataWit.ofReal hδ0 (hδ0.trans_le hδε) W.P.toInPsiTilde Dr hΨr hhr
  obtain ⟨φ1, α1, -, -, hsup1, hu1⟩ := bg_core H hδ0 hδε hε hδ hνε W
  obtain ⟨φ2, α2, -, -, hsup2, hu2⟩ := bg_core H hδ0 hδε hε hδ hνε Wr
  have e1 := (hu1 φ α hs).1
  have e2 := (hu2 φr αr hsr).1
  obtain ⟨-, -, -, -, -, -, hcr, -⟩ := lemma53 S hδa D Dr W hΨr hhr
  have hxd : (x : Torus d (N₀ * L ^ k)) ∈ dataSites G := (mem_dataSites G).2 (Or.inl x.2)
  have hcr' := hcr x hxd
  have hC0 := lemma53Const_pos d L
  have hK2 := cK2_pos d L N
  have hV : 0 ≤ cK2 d L N * (lemma53Const d L * δ) := by positivity
  have hv1 : vn (fun i => φ (x, i) - approxField G a ν D.Ψ D.h x i) ≤
      N * (cK2 d L N * (lemma53Const d L * δ)) := by
    refine vn_le_card_mul hV fun i => ?_
    have := hsup1.val x i
    rw [svec_of_mem G _ x i] at this
    rw [e1]; exact this
  have hv2 : vn (fun i => φr (x, i) - approxField G a ν Dr.Ψ Dr.h x i) ≤
      N * (cK2 d L N * (lemma53Const d L * δ)) := by
    refine vn_le_card_mul hV fun i => ?_
    have := hsup2.val x i
    rw [svec_of_mem G _ x i] at this
    rw [e2]; exact this
  have e : (fun i => φ (x, i) - φr (x, i)) =
      ((approxField G a ν D.Ψ D.h x - approxField G a ν Dr.Ψ Dr.h x) +
        (fun i => φ (x, i) - approxField G a ν D.Ψ D.h x i)) -
        (fun i => φr (x, i) - approxField G a ν Dr.Ψ Dr.h x i) := by
    funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [e]
  have h1 : vn (((approxField G a ν D.Ψ D.h x - approxField G a ν Dr.Ψ Dr.h x) +
        (fun i => φ (x, i) - approxField G a ν D.Ψ D.h x i)) -
        (fun i => φr (x, i) - approxField G a ν Dr.Ψ Dr.h x i)) ≤
      vn ((approxField G a ν D.Ψ D.h x - approxField G a ν Dr.Ψ Dr.h x) +
        (fun i => φ (x, i) - approxField G a ν D.Ψ D.h x i)) +
      vn (fun i => φr (x, i) - approxField G a ν Dr.Ψ Dr.h x i) :=
    cNorm_sub_le _ _
  have h2 := vn_add (approxField G a ν D.Ψ D.h x - approxField G a ν Dr.Ψ Dr.h x)
        (fun i => φ (x, i) - approxField G a ν D.Ψ D.h x i)
  have hK : (1 + 2 * N * cK2 d L N) * (lemma53Const d L * δ) ≤ bgK1 d L N * δ := by
    unfold bgK1
    have : 0 ≤ (L + 2 * d * (L : ℝ) ^ 2 + cK2 d L N) * (lemma53Const d L * δ) := by positivity
    nlinarith
  nlinarith

end Exists

end Balaban.Background
