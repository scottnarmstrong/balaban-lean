/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormExpCauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The renormalization terms `C₁`, `C₂` site by site, and their bounds (FLUCTUATION.md §3.6)

FLUCTUATION.md v2.3 §3.6, proof of Theorem 3.1 (g): "On `Ξ_{k+1}(1, ε_{k+1})` each factor `ψ - Qφ`,
`∂φ`, `√ν (φ - h)` is `O(ε_{k+1})` ..., and `|ζ| ≤ ε_{k+1} ε`, so `|C₁(z, Y)| ≤ C₄' ε_{k+1}² ε ...`;
`C₂(z)`: ... quadratic, hence `C₄' ε_{k+1}² ε²`."  Here, in fine units:

* `renC1Site`, `renC1On`: the site density of `C₁` of Lemma 3.5 (i) with complex `ξ` (block and
  mass terms at `x ∈ Ω₁`, bond terms based at `x`), and its sum over a set `B` of sites (`C₁(z)` for
  `B = B_{k+1}(z)`); `renC1On_univ_ofReal`: over the whole torus and for real `ξ` it is the landed
  `renormC1` of `RenormIdentity.lean`;
* `norm_renC1Site_le`: on the fixed-`h` class domain `XiCOneReal` (the external field is the
  fixed real vector `h₀`, `h'' = 0`), `|C₁(x)| ≤ (2d + 14) ε² |ξ|_∞ / ℓ(x)²`;
* `renC2Site`, `renC2On`: the site density of `C₂ = ½ (1 + ξ₃) ⟨δφ, (H_u + α_u) δφ⟩`
  (`H_u` at the complex mass `ν_u`, the operator of the perturbed system), with
  `renC2On_univ_ofReal`: the landed `renormC2` for real data;
* `norm_renC2Site_le`: `|C₂(x)| ≤ ½ |1 + ξ₃| N (3 + A) V² / ℓ(x)²` when `‖δφ‖_* ≤ V` and
  `ℓ² |α_u + ν_u| ≤ A`; `norm_renC2Site_le_renSol`: with Lemma 3.5 (ii), `V = K₂ B |ξ|_∞`.

**Finding (fixed `h`).**  The `O(ε²)` bound of the mass term `½ ν ξ₂ ‖φ - h‖²` of `C₁` needs the
external field to be the fixed real vector: the landed `Ξ^c` (`XiCBounds.hAbs`) allows a complex
displacement `h''` with only `ν ℓ² |h''| < ε`, for which `ν |h''|²` is not small as `ν → 0`.  This
agrees with FLUCTUATION v2.2 (P5 (1.36)–(1.39): `h` is the fixed physical real unit vector).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Matrix

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Defs

variable (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)

/-- The block weight `a_n L^{-2n}` at a site of layer `n`. -/
noncomputable def blockWt (x : Torus d (N₀ * L ^ k)) : ℝ :=
  a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2

/-- The bond terms of `‖∂φ̄‖²` based at `x` (the bonds `x → x + e_μ` with an endpoint in `Ω₁`). -/
noncomputable def bondSite (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) : ℂ :=
  ∑ μ : Fin d, (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
    ∑ i, (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) *
      (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) else 0)

/-- **The site density of `C₁`** (Lemma 3.5 (i), complex `ξ`, `ζ = ε_ζ ξ₁`): at `x ∈ Ω₁` the block
terms `a_n L^{-2n} [½ ξ₃ |ψ - Qφ|² + (1 + ξ₃)(ζ ψ·(ψ - Qφ) + ½ ζ² ψ·ψ)]` and the mass term
`½ ν ξ₂ (φ - h)·(φ - h)`; at every `x` the bond terms `½ ξ₃ ∑_μ |∂_μ φ̄(x)|²` (bilinear
products). -/
noncomputable def renC1Site (ν εζ : ℝ) (ξ : Fin 3 → ℂ) (Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (φ : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) : ℂ :=
  (if x ∈ G.Ω 1 then
      (blockWt G a x : ℂ) * ((ξ 2 / 2) * ∑ i, (Ψ x i - blockAvg G φ x i) *
          (Ψ x i - blockAvg G φ x i) +
        (1 + ξ 2) * (renZeta εζ ξ * ∑ i, Ψ x i * (Ψ x i - blockAvg G φ x i) +
          (renZeta εζ ξ ^ 2 / 2) * ∑ i, Ψ x i * Ψ x i)) +
      ((ν : ℂ) * ξ 1 / 2) * ∑ i, (svec G φ x i - h x i) * (svec G φ x i - h x i)
    else 0) +
  (ξ 2 / 2) * bondSite G Ψ φ x

/-- `C₁(B)`: the sum of the site density over a set `B` of sites (`C₁(z)` for `B = B_{k+1}(z)`),
for the data `(Ψ, h̃)`. -/
noncomputable def renC1On (ν εζ : ℝ) (B : Finset (Torus d (N₀ * L ^ k)))
    (Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ) (ξ : Fin 3 → ℂ) : ℂ :=
  ∑ x ∈ B, renC1Site G a ν εζ ξ Ψ h φ x

/-- **The site density of `C₂ = ½ (1 + ξ₃) ⟨δφ, (H_u + α_u) δφ⟩`**, with `H_u + α_u` the operator
`H_D^{(0)}(α_u + ν_u)` at the complex mass `ν_u` (the operator of `IsPerturbedM`). -/
noncomputable def renC2Site (ξ : Fin 3 → ℂ) (νu : ℂ) (αu : G.Ω 1 → ℂ) (δφ : G.Ω 1 × Fin N → ℂ)
    (x : G.Ω 1) : ℂ :=
  (1 / 2) * (1 + ξ 2) * ∑ i, δφ (x, i) *
    (liftOp N (dirichletOperator G a 0 (αu + fun _ => νu)) *ᵥ δφ) (x, i)

/-- `C₂(B)`: the sum of the site density over the sites of `Ω₁` in `B`. -/
noncomputable def renC2On (B : Finset (Torus d (N₀ * L ^ k))) (ξ : Fin 3 → ℂ) (νu : ℂ)
    (αu : G.Ω 1 → ℂ) (δφ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x : G.Ω 1 => (x : Torus d (N₀ * L ^ k)) ∈ B),
    renC2Site G a ξ νu αu δφ x

/-- The fixed-`h` class domain: `D` realizes a member `(Ψ₀ + Ψ'', h₀)` of `Ξ^c_k(𝔹; 1, ε)` whose
external field is the real vector `h₀` (no complex displacement of `h`). -/
def XiCOneReal (ν ε : ℝ) (D : BgData G N) : Prop :=
  ∃ (Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (Ψ'' : Torus d (N₀ * L ^ k) → Fin N → ℂ),
    XiC G a ν k 1 ε Ψ₀ h₀ Ψ'' 0 ∧ RealizesC D Ψ₀ h₀ Ψ'' 0

end Defs

section Algebra

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

theorem XiCOneReal.xiCOne {ν ε : ℝ} {D : BgData G N} (h : XiCOneReal G a ν ε D) :
    XiCOne G a ν ε D := by
  obtain ⟨Ψ₀, h₀, Ψ'', hX, hR⟩ := h
  exact ⟨Ψ₀, h₀, Ψ'', 0, hX, hR⟩

theorem spacing_of_not_mem {x : Torus d (N₀ * L ^ k)} (hx : x ∉ G.Ω 1) : G.spacing x = 1 := by
  unfold GeneratingSet.spacing; rw [layerIndex_of_not_mem G hx]; simp

theorem one_le_spacing (x : Torus d (N₀ * L ^ k)) : 1 ≤ G.spacing x := by
  unfold GeneratingSet.spacing
  have : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  exact one_le_pow₀ this

theorem sum_coe_sort_eq_ite (f : Torus d (N₀ * L ^ k) → ℂ) :
    ∑ x : G.Ω 1, f x = ∑ x : Torus d (N₀ * L ^ k), if x ∈ G.Ω 1 then f x else 0 := by
  rw [Finset.sum_coe_sort (G.Ω 1) f, Finset.sum_ite_mem, Finset.univ_inter]

theorem blockPair_eq_sum (u v : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    blockPair G a u v = ∑ x, if x ∈ G.Ω 1 then (blockWt G a x : ℂ) * ∑ i, u x i * v x i else 0 :=
  sum_coe_sort_eq_ite (G := G) (fun x => (blockWt G a x : ℂ) * ∑ i, u x i * v x i)

theorem massPair_eq_sum (h : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ) :
    massPair G h φ = ∑ x, if x ∈ G.Ω 1 then
      ∑ i, (svec G φ x i - h x i) * (svec G φ x i - h x i) else 0 := by
  rw [← sum_coe_sort_eq_ite (G := G)]
  unfold massPair
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [svec_of_mem]

/-- The site density of `C₁` for real `ξ`, in the form of the summands of `renormC1`. -/
theorem renC1Site_ofReal (ν εζ : ℝ) (t : Fin 3 → ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) :
    renC1Site G a ν εζ (fun i => (t i : ℂ)) D.Ψ D.h φ x =
      ((t 2 : ℂ) / 2) * (if x ∈ G.Ω 1 then (blockWt G a x : ℂ) *
          ∑ i, (D.Ψ x i - blockAvg G φ x i) * (D.Ψ x i - blockAvg G φ x i) else 0) +
        (1 + (t 2 : ℂ)) * (((εζ * t 0 : ℝ) : ℂ) * (if x ∈ G.Ω 1 then (blockWt G a x : ℂ) *
            ∑ i, D.Ψ x i * (D.Ψ x i - blockAvg G φ x i) else 0) +
          (((εζ * t 0 : ℝ) : ℂ) ^ 2 / 2) * (if x ∈ G.Ω 1 then (blockWt G a x : ℂ) *
            ∑ i, D.Ψ x i * D.Ψ x i else 0)) +
        ((t 2 : ℂ) / 2) * bondSite G D.Ψ φ x +
        (((ν * t 1 : ℝ) : ℂ) / 2) * (if x ∈ G.Ω 1 then
          ∑ i, (svec G φ x i - D.h x i) * (svec G φ x i - D.h x i) else 0) := by
  unfold renC1Site renZeta
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, ite_true]; push_cast; ring
  · simp only [hx, ite_false]; ring

/-- **Over the whole torus and for real `ξ`, `C₁` is the landed `renormC1`** (Lemma 3.5 (i)). -/
theorem renC1On_univ_ofReal (ν εζ : ℝ) (t : Fin 3 → ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    renC1On G a ν εζ Finset.univ D.Ψ D.h φ (fun i => (t i : ℂ)) =
      renormC1 G a ν (t 1) (t 2) (εζ * t 0) D φ := by
  have e3 : bondPair G D.Ψ φ = ∑ x, bondSite G D.Ψ φ x := rfl
  unfold renormC1 renC1On
  rw [blockPair_eq_sum, blockPair_eq_sum, blockPair_eq_sum, massPair_eq_sum, e3,
    Finset.sum_congr rfl fun x _ => renC1Site_ofReal (G := G) (a := a) ν εζ t D φ x]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **Over `Ω₁` and for real data, `C₂` is the landed `renormC2`** (Lemma 3.5 (i)): the mass
`ν_u` of the operator becomes the constant shift of the multiplier. -/
theorem renC2On_univ_ofReal (νu t₃ : ℝ) (αu : G.Ω 1 → ℂ) (φ φu : G.Ω 1 × Fin N → ℂ) :
    renC2On G a Finset.univ (fun i => if i = 2 then (t₃ : ℂ) else 0) (νu : ℂ) αu (φu - φ) =
      renormC2 G a νu t₃ αu φ φu := by
  unfold renC2On renC2Site renormC2 pair
  have hf : (Finset.univ.filter fun x : G.Ω 1 => (x : Torus d (N₀ * L ^ k)) ∈ Finset.univ) =
      Finset.univ := by ext x; simp
  rw [hf, dirichletOperator_mass_shift G a 0 νu αu, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [sub_zero, ite_true]

end Algebra

section Bounds

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν ε : ℝ}

/-- The factors of `C₁` on the fixed-`h` class domain: `|ψ - Qφ| < 2ε`, `ℓ |∂φ̄| < 2ε`,
`ν ℓ² |φ - h|² ≤ 4ε²`, `|ψ| ≤ 3/2`, for the complex background `φ = bgFieldC`. -/
theorem XiCOneReal.factors (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {D : BgData G N} (hD : XiCOneReal G a ν ε D) :
    (∀ x ∈ G.Ω 1, vn (fun i => D.Ψ x i - blockAvg G (bgFieldC G a ν (bgC0 d L N) D) x i) < 2 * ε) ∧
    (∀ x ∈ G.Ω 1, ∀ μ : Fin d,
      vn (fun i => barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D) (x + Pi.single μ 1) i -
        barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D) x i) < 2 * ε / G.spacing x ∧
      vn (fun i => barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D) (x - Pi.single μ 1) i -
        barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D) x i) < 2 * ε / G.spacing x) ∧
    (∀ x ∈ G.Ω 1, ν * G.spacing x ^ 2 *
      vn (fun i => svec G (bgFieldC G a ν (bgC0 d L N) D) x i - D.h x i) ^ 2 ≤ 4 * ε ^ 2) ∧
    (∀ x ∈ dataSites G, vn (D.Ψ x) ≤ 3 / 2) := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨-, -, -, ⟨W⟩⟩ := hD.xiCOne.bg H hsm hε hc1
  obtain ⟨Ψ₀, h₀, Ψ'', hX, hR⟩ := hD
  obtain ⟨-, -, Dr, Dc, hXr, hC, -, hb⟩ := hX
  obtain rfl : D = Dc := realizesC_unique hR hC
  obtain ⟨hRr, -, hbr⟩ := hXr
  set φc := bgFieldC G a ν (bgC0 d L N) D
  set φr := bgField G a ν Dr
  have hν0 := H.mass
  obtain ⟨hδa, -, -, -⟩ := bgC1_facts d L N hd0 hc1
  have hδ1024 : xiC1 d * ε ≤ 1 / 1024 := (approxDelta_le d L hδa).1
  refine ⟨fun x hx => ?_, fun x hx μ => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · -- the closeness `ψ - Qφ`
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have h1 := hbr.close x hx
    have h2 := hb.close x hx
    have e : (fun i => D.Ψ x i - blockAvg G φc x i) =
        (fun i => Dr.Ψ x i - blockAvg G φr x i) +
          fun i => Ψ'' x i - blockAvg G (φc - φr) x i := by
      funext i
      have hφ : φc = φr + (φc - φr) := by abel
      have hb' := blockAvg_add (G := G) φr (φc - φr) x i
      rw [← hφ] at hb'
      simp only [Pi.add_apply, hR.1 x hxd i, hRr.1 x hxd i, hb']
      ring
    rw [e]
    have := vn_add (fun i => Dr.Ψ x i - blockAvg G φr x i)
      (fun i => Ψ'' x i - blockAvg G (φc - φr) x i)
    simp only [one_pow, one_mul] at h1 h2
    linarith
  · -- the gradients
    obtain ⟨g1, g2⟩ := hbr.grad x hx μ
    obtain ⟨c1, c2⟩ := hb.grad x hx μ
    simp only [one_mul] at g1 g2 c1 c2
    have hsp := spacing_pos G (x := x)
    constructor
    · have e : (fun i => barField G D.Ψ φc (x + Pi.single μ 1) i - barField G D.Ψ φc x i) =
          (fun i => barField G Dr.Ψ φr (x + Pi.single μ 1) i - barField G Dr.Ψ φr x i) +
            fun i => (barField G D.Ψ φc (x + Pi.single μ 1) i -
              barField G Dr.Ψ φr (x + Pi.single μ 1) i) -
              (barField G D.Ψ φc x i - barField G Dr.Ψ φr x i) := by
        funext i; simp only [Pi.add_apply]; ring
      rw [e]
      have := vn_add (fun i => barField G Dr.Ψ φr (x + Pi.single μ 1) i -
          barField G Dr.Ψ φr x i)
        (fun i => (barField G D.Ψ φc (x + Pi.single μ 1) i -
          barField G Dr.Ψ φr (x + Pi.single μ 1) i) -
          (barField G D.Ψ φc x i - barField G Dr.Ψ φr x i))
      have : 2 * ε / G.spacing x = ε / G.spacing x + ε / G.spacing x := by ring
      linarith
    · have e : (fun i => barField G D.Ψ φc (x - Pi.single μ 1) i - barField G D.Ψ φc x i) =
          (fun i => barField G Dr.Ψ φr (x - Pi.single μ 1) i - barField G Dr.Ψ φr x i) +
            fun i => (barField G D.Ψ φc (x - Pi.single μ 1) i -
              barField G Dr.Ψ φr (x - Pi.single μ 1) i) -
              (barField G D.Ψ φc x i - barField G Dr.Ψ φr x i) := by
        funext i; simp only [Pi.add_apply]; ring
      rw [e]
      have := vn_add (fun i => barField G Dr.Ψ φr (x - Pi.single μ 1) i -
          barField G Dr.Ψ φr x i)
        (fun i => (barField G D.Ψ φc (x - Pi.single μ 1) i -
          barField G Dr.Ψ φr (x - Pi.single μ 1) i) -
          (barField G D.Ψ φc x i - barField G Dr.Ψ φr x i))
      have : 2 * ε / G.spacing x = ε / G.spacing x + ε / G.spacing x := by ring
      linarith
  · -- the mass term (fixed real `h₀`)
    have hm := hbr.mass ⟨x, hx⟩
    have hv := hb.val ⟨x, hx⟩
    simp only [one_mul] at hm
    set ℓ := G.spacing x
    have hsp : 0 < ℓ := spacing_pos G
    have hνℓ : ν * ℓ ^ 2 ≤ 1 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsp.le (spacing_le G hx) 2) hν0).trans
        H.massLe
    have hsq : Real.sqrt ν * ℓ ≤ 1 := by
      have : Real.sqrt ν * ℓ = Real.sqrt (ν * ℓ ^ 2) := by
        rw [Real.sqrt_mul hν0, Real.sqrt_sq hsp.le]
      rw [this, Real.sqrt_le_one]
      exact hνℓ
    have e : (fun i => svec G φc x i - D.h x i) =
        (fun i => φr (⟨x, hx⟩, i) - (h₀ i : ℂ)) + fun i => φc (⟨x, hx⟩, i) - φr (⟨x, hx⟩, i) := by
      funext i
      have := hR.2 x hx i
      simp only [Pi.add_apply, this, svec_of_mem G φc ⟨x, hx⟩ i, Pi.zero_apply, add_zero]
      ring
    have htri : vn (fun i => svec G φc x i - D.h x i) ≤
        vn (fun i => φr (⟨x, hx⟩, i) - (h₀ i : ℂ)) +
          vn (fun i => φc (⟨x, hx⟩, i) - φr (⟨x, hx⟩, i)) := by
      rw [e]; exact vn_add _ _
    have hs0 : 0 ≤ Real.sqrt ν * ℓ := by positivity
    have hbnd : Real.sqrt ν * ℓ * vn (fun i => svec G φc x i - D.h x i) ≤ 2 * ε := by
      calc Real.sqrt ν * ℓ * vn (fun i => svec G φc x i - D.h x i)
          ≤ Real.sqrt ν * ℓ * (vn (fun i => φr (⟨x, hx⟩, i) - (h₀ i : ℂ)) +
              vn (fun i => φc (⟨x, hx⟩, i) - φr (⟨x, hx⟩, i))) :=
            mul_le_mul_of_nonneg_left htri hs0
        _ = Real.sqrt ν * ℓ * vn (fun i => φr (⟨x, hx⟩, i) - (h₀ i : ℂ)) +
            Real.sqrt ν * ℓ * vn (fun i => φc (⟨x, hx⟩, i) - φr (⟨x, hx⟩, i)) := by ring
        _ ≤ ε + 1 * ε := add_le_add hm.le (mul_le_mul hsq hv.le (vn_nonneg _) zero_le_one)
        _ = 2 * ε := by ring
    have e2 : ν * ℓ ^ 2 * vn (fun i => svec G φc x i - D.h x i) ^ 2 =
        (Real.sqrt ν * ℓ * vn (fun i => svec G φc x i - D.h x i)) ^ 2 := by
      have := Real.mul_self_sqrt hν0
      have : Real.sqrt ν ^ 2 = ν := by rw [sq]; exact this
      rw [mul_pow, mul_pow, this]
    rw [e2]
    have h0 : 0 ≤ Real.sqrt ν * ℓ * vn (fun i => svec G φc x i - D.h x i) :=
      mul_nonneg hs0 (vn_nonneg _)
    nlinarith
  · -- the size of the data
    have hδ0 : 0 < xiC1 d * ε := by have := one_le_xiC1 d; positivity
    exact (W.vn_le hδ0 hx).trans (by linarith)

/-- The bond terms based at `x` are bounded by `d A² / ℓ(x)²` when `ℓ |∂φ̄| ≤ A` at the points of
`Ω₁` (`ℓ = 1` off `Ω₁`). -/
theorem norm_bondSite_le {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φ : G.Ω 1 × Fin N → ℂ} {A : ℝ}
    (hA : 0 ≤ A)
    (hg : ∀ x ∈ G.Ω 1, ∀ μ : Fin d,
      vn (fun i => barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) ≤ A / G.spacing x ∧
      vn (fun i => barField G Ψ φ (x - Pi.single μ 1) i - barField G Ψ φ x i) ≤ A / G.spacing x)
    (x : Torus d (N₀ * L ^ k)) : ‖bondSite G Ψ φ x‖ ≤ d * A ^ 2 / G.spacing x ^ 2 := by
  unfold bondSite
  have hsp := spacing_pos G (x := x)
  have hterm : ∀ μ : Fin d, ‖(if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
      ∑ i, (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) *
        (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) else 0)‖ ≤
      A ^ 2 / G.spacing x ^ 2 := by
    intro μ
    have hdot : ‖∑ i, (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) *
        (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i)‖ ≤
        vn (fun i => barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) ^ 2 := by
      rw [sq]; exact Balaban.Multiscale.norm_dot_le _ _
    split_ifs with hc
    · by_cases hx : x ∈ G.Ω 1
      · have h1 := (hg x hx μ).1
        refine hdot.trans ?_
        have := pow_le_pow_left₀ (vn_nonneg _) h1 2
        rwa [div_pow] at this
      · have hy : x + Pi.single μ 1 ∈ G.Ω 1 := hc.resolve_left hx
        have h1 := (hg _ hy μ).2
        rw [add_sub_cancel_right] at h1
        have hneg : vn (fun i => barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) =
            vn (fun i => barField G Ψ φ x i - barField G Ψ φ (x + Pi.single μ 1) i) := by
          rw [← vn_neg]; congr 1; funext i; ring
        have hspy := one_le_spacing (G := G) (x + Pi.single μ 1)
        have h2 : vn (fun i => barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) ≤ A := by
          rw [hneg]; exact h1.trans (div_le_self hA hspy)
        rw [spacing_of_not_mem hx, one_pow, div_one]
        exact hdot.trans (pow_le_pow_left₀ (vn_nonneg _) h2 2)
    · simp only [norm_zero]; positivity
  calc ‖∑ μ : Fin d, _‖ ≤ ∑ μ : Fin d, A ^ 2 / G.spacing x ^ 2 :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => hterm μ)
    _ = d * A ^ 2 / G.spacing x ^ 2 := by simp; ring

variable (G) in
/-- The weight `W(B) = ∑_{x ∈ B} ℓ(x)^{-2}` of a set of sites (for a block `B_{k+1}(z)` of the top
layer this is the conversion factor `L^{(k+1)(d-2)}` from `η`-units to fine units). -/
noncomputable def blockWeight (B : Finset (Torus d (N₀ * L ^ k))) : ℝ :=
  ∑ x ∈ B, (G.spacing x ^ 2)⁻¹

/-- **The pointwise bound of `C₁`** (FLUCTUATION.md §3.6, proof of (g)): on the fixed-`h` class
domain `Ξ^c_{k+1}(1, ε)`, with `ζ = ε_ζ ξ₁`, `ε_ζ ≤ ε`, `|ξ|_∞ ≤ 1/16`,
`|C₁(x)| ≤ (2d + 14) ε² |ξ|_∞ / ℓ(x)²`. -/
theorem norm_renC1Site_le (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {D : BgData G N} (hD : XiCOneReal G a ν ε D) {εζ : ℝ} (hεζ0 : 0 ≤ εζ) (hεζ : εζ ≤ ε)
    {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ ≤ 1 / 16) (x : Torus d (N₀ * L ^ k)) :
    ‖renC1Site G a ν εζ ξ D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) D) x‖ ≤
      (2 * d + 14) * ε ^ 2 * ‖ξ‖ / G.spacing x ^ 2 := by
  obtain ⟨hcl, hgr, hms, hvΨ⟩ := hD.factors H hε hsm hc1
  set φc := bgFieldC G a ν (bgC0 d L N) D
  set ℓ := G.spacing x with hℓdef
  have hsp : 0 < ℓ := spacing_pos G
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hξ0 := norm_nonneg ξ
  have hξ1 : ‖ξ 1‖ ≤ ‖ξ‖ := norm_le_pi_norm ξ 1
  have hξ2 : ‖ξ 2‖ ≤ ‖ξ‖ := norm_le_pi_norm ξ 2
  have hz : ‖renZeta εζ ξ‖ ≤ ε * ‖ξ‖ :=
    (norm_renZeta_le hεζ0 ξ).trans (mul_le_mul_of_nonneg_right hεζ hξ0)
  have h1ξ : ‖1 + ξ 2‖ ≤ 17 / 16 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  have hbond := norm_bondSite_le (G := G) (Ψ := D.Ψ) (φ := φc) (A := 2 * ε) (by positivity)
    (fun y hy μ => ⟨(hgr y hy μ).1.le, (hgr y hy μ).2.le⟩) x
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hB : ‖(ξ 2 / 2) * bondSite G D.Ψ φc x‖ ≤ 2 * d * ε ^ 2 * ‖ξ‖ / ℓ ^ 2 := by
    rw [norm_mul, norm_div, Complex.norm_ofNat]
    calc ‖ξ 2‖ / 2 * ‖bondSite G D.Ψ φc x‖ ≤ ‖ξ‖ / 2 * (d * (2 * ε) ^ 2 / ℓ ^ 2) :=
          mul_le_mul (by linarith) hbond (norm_nonneg _) (by positivity)
      _ = 2 * d * ε ^ 2 * ‖ξ‖ / ℓ ^ 2 := by ring
  unfold renC1Site
  split_ifs with hx
  · have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have hP := hvΨ x hxd
    have hC := hcl x hx
    have hM := hms x hx
    obtain ⟨hj1, hjk, -⟩ := G.layerIndex_spec hx
    have hw0 : 0 ≤ blockWt G a x := by
      unfold blockWt; have := (H.weights _ hj1 hjk).1; positivity
    have hw : blockWt G a x ≤ 2 / ℓ ^ 2 := by
      unfold blockWt; rw [hℓdef]; unfold GeneratingSet.spacing
      exact div_le_div_of_nonneg_right (H.weights _ hj1 hjk).2 (by positivity)
    have hv1 := vn_nonneg (fun i => D.Ψ x i - blockAvg G φc x i)
    have hv2 := vn_nonneg (D.Ψ x)
    have d1 : ‖∑ i, (D.Ψ x i - blockAvg G φc x i) * (D.Ψ x i - blockAvg G φc x i)‖ ≤
        4 * ε ^ 2 := (Balaban.Multiscale.norm_dot_le _ _).trans (by nlinarith)
    have d2 : ‖∑ i, D.Ψ x i * (D.Ψ x i - blockAvg G φc x i)‖ ≤ 3 * ε :=
      (Balaban.Multiscale.norm_dot_le _ _).trans (by nlinarith)
    have d3 : ‖∑ i, D.Ψ x i * D.Ψ x i‖ ≤ 9 / 4 :=
      (Balaban.Multiscale.norm_dot_le _ _).trans (by nlinarith)
    have T1 : ‖ξ 2 / 2 * ∑ i, (D.Ψ x i - blockAvg G φc x i) * (D.Ψ x i - blockAvg G φc x i)‖ ≤
        2 * ε ^ 2 * ‖ξ‖ := by
      rw [norm_mul, norm_div, Complex.norm_ofNat]
      calc ‖ξ 2‖ / 2 * _ ≤ ‖ξ‖ / 2 * (4 * ε ^ 2) :=
            mul_le_mul (by linarith) d1 (norm_nonneg _) (by positivity)
        _ = 2 * ε ^ 2 * ‖ξ‖ := by ring
    have hz2 : ‖renZeta εζ ξ ^ 2 / 2‖ ≤ ε ^ 2 * ‖ξ‖ / 32 := by
      rw [norm_div, norm_pow, Complex.norm_ofNat]
      have : ‖renZeta εζ ξ‖ ^ 2 ≤ (ε * ‖ξ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      have : (ε * ‖ξ‖) ^ 2 ≤ ε ^ 2 * ‖ξ‖ / 16 := by
        have := mul_nonneg (mul_nonneg (sq_nonneg ε) hξ0) (sub_nonneg.2 hξ)
        rw [mul_pow]; nlinarith
      linarith
    have T2 : ‖(1 + ξ 2) * (renZeta εζ ξ * ∑ i, D.Ψ x i * (D.Ψ x i - blockAvg G φc x i) +
        (renZeta εζ ξ ^ 2 / 2) * ∑ i, D.Ψ x i * D.Ψ x i)‖ ≤ 4 * ε ^ 2 * ‖ξ‖ := by
      rw [norm_mul]
      have hin : ‖renZeta εζ ξ * ∑ i, D.Ψ x i * (D.Ψ x i - blockAvg G φc x i) +
          (renZeta εζ ξ ^ 2 / 2) * ∑ i, D.Ψ x i * D.Ψ x i‖ ≤
          ε * ‖ξ‖ * (3 * ε) + ε ^ 2 * ‖ξ‖ / 32 * (9 / 4) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul]; exact mul_le_mul hz d2 (norm_nonneg _) (by positivity)
        · rw [norm_mul]; exact mul_le_mul hz2 d3 (norm_nonneg _) (by positivity)
      calc ‖1 + ξ 2‖ * _ ≤ 17 / 16 * (ε * ‖ξ‖ * (3 * ε) + ε ^ 2 * ‖ξ‖ / 32 * (9 / 4)) :=
            mul_le_mul h1ξ hin (norm_nonneg _) (by norm_num)
        _ ≤ 4 * ε ^ 2 * ‖ξ‖ := by
            have := mul_nonneg (sq_nonneg ε) hξ0
            nlinarith
    have T3 : ‖(ν : ℂ) * ξ 1 / 2 * ∑ i, (svec G φc x i - D.h x i) * (svec G φc x i - D.h x i)‖ ≤
        2 * ε ^ 2 * ‖ξ‖ / ℓ ^ 2 := by
      have hν0 := H.mass
      have hd4 := Balaban.Multiscale.norm_dot_le (fun i => svec G φc x i - D.h x i)
        (fun i => svec G φc x i - D.h x i)
      rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hν0,
        Complex.norm_ofNat]
      have hvv := vn_nonneg (fun i => svec G φc x i - D.h x i)
      have hM' : ν * vn (fun i => svec G φc x i - D.h x i) ^ 2 ≤ 4 * ε ^ 2 / ℓ ^ 2 := by
        rw [le_div_iff₀ hℓ2]
        have e : ν * vn (fun i => svec G φc x i - D.h x i) ^ 2 * ℓ ^ 2 =
            ν * ℓ ^ 2 * vn (fun i => svec G φc x i - D.h x i) ^ 2 := by ring
        rw [e]; exact hM
      calc ν * ‖ξ 1‖ / 2 * ‖∑ i, (svec G φc x i - D.h x i) * (svec G φc x i - D.h x i)‖
          ≤ ‖ξ‖ / 2 * (ν * vn (fun i => svec G φc x i - D.h x i) ^ 2) := by
            have h5 : ‖∑ i, (svec G φc x i - D.h x i) * (svec G φc x i - D.h x i)‖ ≤
                vn (fun i => svec G φc x i - D.h x i) ^ 2 := by rw [sq]; exact hd4
            have := mul_le_mul_of_nonneg_left hξ1 hν0
            have h6 : 0 ≤ ν * ‖ξ 1‖ := by positivity
            calc ν * ‖ξ 1‖ / 2 * ‖∑ i, (svec G φc x i - D.h x i) * (svec G φc x i - D.h x i)‖
                ≤ ν * ‖ξ‖ / 2 * vn (fun i => svec G φc x i - D.h x i) ^ 2 :=
                  mul_le_mul (by linarith) h5 (norm_nonneg _) (by positivity)
              _ = ‖ξ‖ / 2 * (ν * vn (fun i => svec G φc x i - D.h x i) ^ 2) := by ring
        _ ≤ ‖ξ‖ / 2 * (4 * ε ^ 2 / ℓ ^ 2) := mul_le_mul_of_nonneg_left hM' (by positivity)
        _ = 2 * ε ^ 2 * ‖ξ‖ / ℓ ^ 2 := by ring
    have hwA : ‖(blockWt G a x : ℂ) * (ξ 2 / 2 * ∑ i, (D.Ψ x i - blockAvg G φc x i) *
        (D.Ψ x i - blockAvg G φc x i) + (1 + ξ 2) * (renZeta εζ ξ * ∑ i, D.Ψ x i *
          (D.Ψ x i - blockAvg G φc x i) + (renZeta εζ ξ ^ 2 / 2) * ∑ i, D.Ψ x i * D.Ψ x i))‖ ≤
        12 * ε ^ 2 * ‖ξ‖ / ℓ ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
      calc blockWt G a x * ‖_‖ ≤ 2 / ℓ ^ 2 * (2 * ε ^ 2 * ‖ξ‖ + 4 * ε ^ 2 * ‖ξ‖) :=
            mul_le_mul hw ((norm_add_le _ _).trans (add_le_add T1 T2)) (norm_nonneg _)
              (by positivity)
        _ = 12 * ε ^ 2 * ‖ξ‖ / ℓ ^ 2 := by ring
    have hsum := add_le_add (add_le_add hwA T3) hB
    have e : 12 * ε ^ 2 * ‖ξ‖ / ℓ ^ 2 + 2 * ε ^ 2 * ‖ξ‖ / ℓ ^ 2 + 2 * d * ε ^ 2 * ‖ξ‖ / ℓ ^ 2 =
        (2 * d + 14) * ε ^ 2 * ‖ξ‖ / ℓ ^ 2 := by ring
    rw [← e]
    exact norm_add₃_le.trans hsum
  · rw [zero_add]
    refine hB.trans ?_
    have : 0 ≤ ε ^ 2 * ‖ξ‖ / ℓ ^ 2 := by positivity
    have e1 : 2 * d * ε ^ 2 * ‖ξ‖ / ℓ ^ 2 = 2 * d * (ε ^ 2 * ‖ξ‖ / ℓ ^ 2) := by ring
    have e2 : (2 * d + 14) * ε ^ 2 * ‖ξ‖ / ℓ ^ 2 = (2 * d + 14) * (ε ^ 2 * ‖ξ‖ / ℓ ^ 2) := by ring
    rw [e1, e2]
    nlinarith

/-- **`C₁(B)`**: `|C₁(B)| ≤ (2d + 14) ε² |ξ|_∞ W(B)`. -/
theorem norm_renC1On_le (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {D : BgData G N} (hD : XiCOneReal G a ν ε D) {εζ : ℝ} (hεζ0 : 0 ≤ εζ) (hεζ : εζ ≤ ε)
    {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ ≤ 1 / 16) (B : Finset (Torus d (N₀ * L ^ k))) :
    ‖renC1On G a ν εζ B D.Ψ D.h (bgFieldC G a ν (bgC0 d L N) D) ξ‖ ≤
      (2 * d + 14) * ε ^ 2 * ‖ξ‖ * blockWeight G B := by
  unfold renC1On blockWeight
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  have := norm_renC1Site_le H hε hsm hc1 hD hεζ0 hεζ hξ x
  rwa [div_eq_mul_inv] at this

/-- **The pointwise bound of `C₂`**: if `‖δφ‖_* ≤ V` and `ℓ² |α_u + ν_u| ≤ A`, then
`|C₂(x)| ≤ ½ |1 + ξ₃| N (3 + A) V² / ℓ(x)²`. -/
theorem norm_renC2Site_le (hw : IsAdmissibleWeights k a) {δφ : G.Ω 1 × Fin N → ℂ} {V A : ℝ}
    (hV : 0 ≤ V) (hA0 : 0 ≤ A) (hS : SupBounds G δφ V) {αu : G.Ω 1 → ℂ} {νu : ℂ}
    (hA : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖αu x + νu‖ ≤ A)
    (ξ : Fin 3 → ℂ) (x : G.Ω 1) :
    ‖renC2Site G a ξ νu αu δφ x‖ ≤
      ‖1 + ξ 2‖ / 2 * (N * ((3 + A) * V ^ 2)) / G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
  set ℓ := G.spacing (x : Torus d (N₀ * L ^ k)) with hℓdef
  have hsp : 0 < ℓ := spacing_pos G
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  obtain ⟨hj1, hjk, -⟩ := G.layerIndex_spec x.2
  have hv : ∀ i, ‖δφ (x, i)‖ ≤ V := fun i => by
    have := hS.val (x : Torus d (N₀ * L ^ k)) i; rwa [svec_of_mem] at this
  have hHv : ∀ i, ‖(liftOp N (dirichletOperator G a 0 (αu + fun _ => νu)) *ᵥ δφ) (x, i)‖ ≤
      (3 + A) * V / ℓ ^ 2 := by
    intro i
    rw [liftOp_mulVec, dirichlet_apply]
    have hlap : ℓ ^ 2 * ‖negLap (zeroExt (G.Ω 1) fun b => δφ (b, i)) (x : Torus d (N₀ * L ^ k))‖
        ≤ V := hS.lap _ x.2 i
    have hbl : ‖blockTerm G a (zeroExt (G.Ω 1) fun b => δφ (b, i)) (x : Torus d (N₀ * L ^ k))‖ ≤
        2 * V / ℓ ^ 2 := by
      refine (blockTerm_norm_le hw x.2 (F := V) fun y => hS.val y i).trans ?_
      rw [hℓdef]; unfold GeneratingSet.spacing
      have h2 := (hw _ hj1 hjk).2
      calc a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
            ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 * V
          ≤ 2 / ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 * V :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h2 (by positivity)) hV
        _ = 2 * V / ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 := by ring
    have hα : ‖(αu + fun _ => νu : G.Ω 1 → ℂ) x * δφ (x, i)‖ ≤ A * V / ℓ ^ 2 := by
      rw [norm_mul, le_div_iff₀ hℓ2]
      have := hA x
      simp only [Pi.add_apply]
      calc ‖αu x + νu‖ * ‖δφ (x, i)‖ * ℓ ^ 2 = (ℓ ^ 2 * ‖αu x + νu‖) * ‖δφ (x, i)‖ := by ring
        _ ≤ A * V := mul_le_mul this (hv i) (norm_nonneg _) hA0
    have hlap' : ‖negLap (zeroExt (G.Ω 1) fun b => δφ (b, i)) (x : Torus d (N₀ * L ^ k))‖ ≤
        V / ℓ ^ 2 := by rw [le_div_iff₀ hℓ2]; linarith
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    calc ‖negLap (zeroExt (G.Ω 1) fun b => δφ (b, i)) (x : Torus d (N₀ * L ^ k)) +
          blockTerm G a (zeroExt (G.Ω 1) fun b => δφ (b, i)) (x : Torus d (N₀ * L ^ k)) +
          (αu + fun _ => νu : G.Ω 1 → ℂ) x * (fun b => δφ (b, i)) x‖
        ≤ V / ℓ ^ 2 + 2 * V / ℓ ^ 2 + A * V / ℓ ^ 2 :=
          (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hlap' hbl)) hα)
      _ = (3 + A) * V / ℓ ^ 2 := by ring
  unfold renC2Site
  rw [norm_mul, norm_mul, norm_div, norm_one, Complex.norm_ofNat]
  have hsum : ‖∑ i, δφ (x, i) * (liftOp N (dirichletOperator G a 0 (αu + fun _ => νu)) *ᵥ δφ)
      (x, i)‖ ≤ N * ((3 + A) * V ^ 2) / ℓ ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖δφ (x, i) * (liftOp N (dirichletOperator G a 0 (αu + fun _ => νu)) *ᵥ δφ) (x, i)‖
        ≤ ∑ _i : Fin N, V * ((3 + A) * V / ℓ ^ 2) := Finset.sum_le_sum fun i _ => by
          rw [norm_mul]; exact mul_le_mul (hv i) (hHv i) (norm_nonneg _) hV
      _ = N * ((3 + A) * V ^ 2) / ℓ ^ 2 := by simp; ring
  calc 1 / 2 * ‖1 + ξ 2‖ * ‖∑ i, δφ (x, i) *
        (liftOp N (dirichletOperator G a 0 (αu + fun _ => νu)) *ᵥ δφ) (x, i)‖
      ≤ 1 / 2 * ‖1 + ξ 2‖ * (N * ((3 + A) * V ^ 2) / ℓ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖1 + ξ 2‖ / 2 * (N * ((3 + A) * V ^ 2)) / ℓ ^ 2 := by ring

/-- A sum over the sites of `Ω₁` in `B` of a nonnegative function of the site is at most the sum
over `B`. -/
theorem sum_filter_coe_le (B : Finset (Torus d (N₀ * L ^ k))) (f : Torus d (N₀ * L ^ k) → ℝ)
    (hf : ∀ y, 0 ≤ f y) :
    ∑ x ∈ Finset.univ.filter (fun x : G.Ω 1 => (x : Torus d (N₀ * L ^ k)) ∈ B),
      f (x : Torus d (N₀ * L ^ k)) ≤ ∑ y ∈ B, f y := by
  have e := Finset.sum_map (Finset.univ.filter (fun x : G.Ω 1 => (x : Torus d (N₀ * L ^ k)) ∈ B))
    (Function.Embedding.subtype (· ∈ G.Ω 1)) f
  simp only [Function.Embedding.coe_subtype] at e
  rw [← e]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun y _ _ => hf y
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
  exact (Finset.mem_filter.1 hx).2

/-- **The bound of `C₂` with Lemma 3.5 (ii)**: for the solution map of `IsRenSol`
(`‖δφ‖_*, |δα|₂ ≤ K₂ B |ξ|_∞`), `α_u = α + δα`, `ν_u = ν (1 + ξ₂)/(1 + ξ₃)`:
`|C₂(x)| ≤ (17/32) N (5 + K₁ C₁ ε + K₂ B r) (K₂ B |ξ|_∞)² / ℓ(x)²`. -/
theorem norm_renC2Site_le_renSol (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {εζ r B : ℝ} {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hF : IsRenSol G a ν εζ ε r B F) (hB0 : 0 ≤ B) (hr : r ≤ 1 / 16) {D : BgData G N}
    (hD : XiCOne G a ν ε D) {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ < r) (x : G.Ω 1) :
    ‖renC2Site G a ξ (renMassU ν ξ) (bgMultC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2)
        (F ((D.Ψ, D.h), ξ)).1 x‖ ≤
      17 / 32 * (N * ((5 + bgK1 d L N * (xiC1 d * ε) + cK2 d L N * B * r) *
        (cK2 d L N * (B * ‖ξ‖)) ^ 2)) / G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
  obtain ⟨-, -, hb, -⟩ := hD.bg H hsm hε hc1
  have hξ0 := norm_nonneg ξ
  have hξ16 : ‖ξ‖ ≤ 1 / 16 := hξ.le.trans hr
  have hK2 := cK2_pos d L N
  have hK1 := bgK1_pos d L N
  have hδ0 : 0 < xiC1 d * ε := by have := one_le_xiC1 d; positivity
  have hν0 := H.mass
  have hr0 : 0 ≤ r := hξ0.trans hξ.le
  set V := cK2 d L N * (B * ‖ξ‖)
  set A := bgK1 d L N * (xiC1 d * ε) + cK2 d L N * B * r + 2
  have hV : 0 ≤ V := by positivity
  have hA0 : 0 ≤ A := by positivity
  have hA : ∀ y : G.Ω 1, G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 *
      ‖(bgMultC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2) y + renMassU ν ξ‖ ≤ A := by
    intro y
    have hsp := spacing_pos G (x := (y : Torus d (N₀ * L ^ k)))
    have hℓ0 : 0 ≤ G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
    have hνℓ : ν * G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 ≤ 1 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsp.le (spacing_le G y.2) 2) hν0).trans
        H.massLe
    have h1 := hb.alpha y
    have h2 := (hF.small D hD ξ hξ) y
    have h3 : ‖renMassU ν ξ‖ ≤ 2 * ν := by
      have := renMassU_sub_norm_le hν0 hξ16
      have e : renMassU ν ξ = (renMassU ν ξ - ν) + (ν : ℂ) := by ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hν0]
      nlinarith
    have hKr : cK2 d L N * (B * ‖ξ‖) ≤ cK2 d L N * B * r := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hξ.le (by positivity)
    simp only [Pi.add_apply]
    calc G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 *
          ‖bgMultC G a ν (bgC0 d L N) D y + (F ((D.Ψ, D.h), ξ)).2 y + renMassU ν ξ‖
        ≤ G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 *
          (‖bgMultC G a ν (bgC0 d L N) D y‖ + ‖(F ((D.Ψ, D.h), ξ)).2 y‖ + ‖renMassU ν ξ‖) :=
          mul_le_mul_of_nonneg_left norm_add₃_le hℓ0
      _ = G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 * ‖bgMultC G a ν (bgC0 d L N) D y‖ +
          G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 * ‖(F ((D.Ψ, D.h), ξ)).2 y‖ +
          G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 * ‖renMassU ν ξ‖ := by ring
      _ ≤ bgK1 d L N * (xiC1 d * ε) + cK2 d L N * B * r + 2 := by
          have h4 : G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 * ‖renMassU ν ξ‖ ≤ 2 := by
            calc G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 * ‖renMassU ν ξ‖
                ≤ G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2 * (2 * ν) :=
                  mul_le_mul_of_nonneg_left h3 hℓ0
              _ = 2 * (ν * G.spacing (y : Torus d (N₀ * L ^ k)) ^ 2) := by ring
              _ ≤ 2 := by linarith
          linarith
  have hmain := norm_renC2Site_le (G := G) H.weights hV hA0 (hF.sup D hD ξ hξ) hA ξ x
  have h1ξ : ‖1 + ξ 2‖ / 2 ≤ 17 / 32 := by
    have := (norm_add_le (1 : ℂ) (ξ 2)).trans (by rw [norm_one]; linarith [norm_le_pi_norm ξ 2] :
      ‖(1 : ℂ)‖ + ‖ξ 2‖ ≤ 17 / 16)
    linarith
  have hsp := spacing_pos G (x := (x : Torus d (N₀ * L ^ k)))
  refine hmain.trans ?_
  have e : 3 + A = 5 + bgK1 d L N * (xiC1 d * ε) + cK2 d L N * B * r := by ring
  rw [e]
  gcongr

/-- **`C₂(B)` with Lemma 3.5 (ii)**:
`|C₂(B)| ≤ (17/32) N (5 + K₁ C₁ ε + K₂ B r) (K₂ B |ξ|_∞)² W(B)`. -/
theorem norm_renC2On_le_renSol (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {εζ r B : ℝ} {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (hF : IsRenSol G a ν εζ ε r B F) (hB0 : 0 ≤ B) (hr : r ≤ 1 / 16) {D : BgData G N}
    (hD : XiCOne G a ν ε D) {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ < r) (Bs : Finset (Torus d (N₀ * L ^ k))) :
    ‖renC2On G a Bs ξ (renMassU ν ξ) (bgMultC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2)
        (F ((D.Ψ, D.h), ξ)).1‖ ≤
      17 / 32 * (N * ((5 + bgK1 d L N * (xiC1 d * ε) + cK2 d L N * B * r) *
        (cK2 d L N * (B * ‖ξ‖)) ^ 2)) * blockWeight G Bs := by
  unfold renC2On blockWeight
  set c := 17 / 32 * (N * ((5 + bgK1 d L N * (xiC1 d * ε) + cK2 d L N * B * r) *
    (cK2 d L N * (B * ‖ξ‖)) ^ 2))
  have hc : 0 ≤ c := by
    have := cK2_pos d L N; have := bgK1_pos d L N; have := one_le_xiC1 d
    have : 0 ≤ r := (norm_nonneg ξ).trans hξ.le
    positivity
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x ∈ Finset.univ.filter (fun x : G.Ω 1 => (x : Torus d (N₀ * L ^ k)) ∈ Bs), ‖_‖
      ≤ ∑ x ∈ Finset.univ.filter (fun x : G.Ω 1 => (x : Torus d (N₀ * L ^ k)) ∈ Bs),
          c * (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2)⁻¹ := Finset.sum_le_sum fun x _ => by
        have := norm_renC2Site_le_renSol H hε hsm hc1 hF hB0 hr hD hξ x
        rwa [div_eq_mul_inv] at this
    _ ≤ ∑ y ∈ Bs, c * (G.spacing y ^ 2)⁻¹ :=
        sum_filter_coe_le Bs (fun y => c * (G.spacing y ^ 2)⁻¹) fun y => by
          have := spacing_pos G (x := y); positivity
    _ = c * ∑ y ∈ Bs, (G.spacing y ^ 2)⁻¹ := by rw [Finset.mul_sum]

end Bounds

end Balaban.Fluctuation
