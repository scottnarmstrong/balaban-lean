/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiPerturb
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (Ξ3): the scaled composition on `Ξ^c`

The scaled composition (R-S) (`Balaban.Background.scaledComposition`) applied to a member of
`Ξ^c_k(𝔹'; 1, ε₀)`: the hypotheses `HypS` of (R-S) on the fields are consequences of the
membership (`xi_fieldBounds`, the complex analogue `xiC_fieldBounds`, `xi_mass_le`), so the composed
data (6.2) lie in the scaled data domain `ScaledPsiC` with `σ = C₀ θ` (`θ = L^{j-k}`).

*Which case is proved.*  The case with the scale gap `ℓ(x) ≤ θ ℓ'(x)` on `Ω₁` and on the collar
(`HypS.gap`, `HypS.hcol`) and `𝔹_j ≺ 𝔹'_k`, in the form of the *restricted pair*
`(reR, dPsi, hRes)` of the real part, the complex displacement and `h''`, with the restriction
`|φ^c - φ^r|₀ ≤ ε` supplied by `Ξ^c` (`XiCBounds.val`).  The membership of the composed datum in
`Ξ^c_j(𝔹; θ, ε₀)` (restriction of the fields, Theorem 7.3) is not proved here.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

omit [NeZero N₀] [NeZero L] in
theorem lap_add_le (A E : Torus d (N₀ * L ^ k) → Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) {r₁ r₂ : ℝ}
    (hA : vn (fun i => ∑ μ : Fin d,
      (A (x + Pi.single μ 1) i + A (x - Pi.single μ 1) i - 2 * A x i)) ≤ r₁)
    (hE : vn (fun i => ∑ μ : Fin d,
      (E (x + Pi.single μ 1) i + E (x - Pi.single μ 1) i - 2 * E x i)) ≤ r₂) :
    vn (fun i => ∑ μ : Fin d, ((A (x + Pi.single μ 1) i + E (x + Pi.single μ 1) i) +
      (A (x - Pi.single μ 1) i + E (x - Pi.single μ 1) i) - 2 * (A x i + E x i))) ≤ r₁ + r₂ := by
  have h := vn_add' (fun i => ∑ μ : Fin d,
      (A (x + Pi.single μ 1) i + A (x - Pi.single μ 1) i - 2 * A x i))
    (fun i => ∑ μ : Fin d, (E (x + Pi.single μ 1) i + E (x - Pi.single μ 1) i - 2 * E x i))
  have e : (fun i => ∑ μ : Fin d, ((A (x + Pi.single μ 1) i + E (x + Pi.single μ 1) i) +
      (A (x - Pi.single μ 1) i + E (x - Pi.single μ 1) i) - 2 * (A x i + E x i))) =
      fun i => (∑ μ : Fin d, (A (x + Pi.single μ 1) i + A (x - Pi.single μ 1) i - 2 * A x i)) +
        ∑ μ : Fin d, (E (x + Pi.single μ 1) i + E (x - Pi.single μ 1) i - 2 * E x i) := by
    funext i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun μ _ => by ring
  rw [e]
  linarith

section Congr

variable {G' : GeneratingSet d L N₀ k ϱ'}

theorem barVec_congr_nbr {Ψ Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φ : G'.Ω 1 × Fin N → ℂ}
    (hag : ∀ x ∈ dataSites G', Ψ' x = Ψ x) {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ G'.Ω 1)
    (hy : Adj x y) : barVec G' Ψ' φ y = barVec G' Ψ φ y := by
  by_cases hy1 : y ∈ G'.Ω 1
  · funext i; simp [barVec, barField, hy1]
  · have hc : y ∈ collar G' := mem_collar_of_adj G' hx hy1 hy
    funext i
    simp only [barVec, barField, hy1, dite_false]
    exact congrFun (hag y ((mem_dataSites G').2 (Or.inr hc))) i

theorem barVec_congr_self {Ψ Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φ : G'.Ω 1 × Fin N → ℂ}
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G'.Ω 1) : barVec G' Ψ' φ x = barVec G' Ψ φ x := by
  funext i; simp [barVec, barField, hx]

/-- `FieldBounds` only depends on the data on `Ω₁ ∪ C(Ω₁)`. -/
theorem fieldBounds_congr {η : ℝ} {Ψ Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φ : G'.Ω 1 × Fin N → ℂ} (h : FieldBounds G' η Ψ φ) (hag : ∀ x ∈ dataSites G', Ψ' x = Ψ x) :
    FieldBounds G' η Ψ' φ where
  close z := by
    have := h.close z
    rwa [hag z ((mem_dataSites G').2 (Or.inl z.2))]
  smooth :=
    { grad := fun x hx μ => by
        have h1 := h.smooth.grad x hx μ
        rw [barVec_congr_nbr hag hx (adj_add x μ), barVec_congr_nbr hag hx (adj_sub x μ),
          barVec_congr_self (Ψ := Ψ) hx]
        exact h1
      lap := fun x hx => by
        have h1 := h.smooth.lap x hx
        have e : ∀ μ, barVec G' Ψ' φ (x + Pi.single μ 1) = barVec G' Ψ φ (x + Pi.single μ 1) :=
          fun μ => barVec_congr_nbr hag hx (adj_add x μ)
        have e2 : ∀ μ, barVec G' Ψ' φ (x - Pi.single μ 1) = barVec G' Ψ φ (x - Pi.single μ 1) :=
          fun μ => barVec_congr_nbr hag hx (adj_sub x μ)
        simp only [e, e2, barVec_congr_self (Ψ := Ψ) hx]
        exact h1 }
  unit := h.unit

end Congr

section Complex

variable {G' : GeneratingSet d L N₀ k ϱ'} {a : ℕ → ℝ} {ν : ℝ}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}

theorem isSmooth_add' {f g : Torus d (N₀ * L ^ k) → Fin N → ℂ} {A B : ℝ}
    (hf : IsSmoothField G' A f) (hg : IsSmoothField G' B g) :
    IsSmoothField G' (A + B) (fun y i => f y i + g y i) where
  grad x hx μ := by
    obtain ⟨f1, f2⟩ := hf.grad x hx μ
    obtain ⟨g1, g2⟩ := hg.grad x hx μ
    have k1 := vn_add_diff (f (x + Pi.single μ 1)) (f x) (g (x + Pi.single μ 1)) (g x)
    have k2 := vn_add_diff (f (x - Pi.single μ 1)) (f x) (g (x - Pi.single μ 1)) (g x)
    have e : (A + B) / G'.spacing x = A / G'.spacing x + B / G'.spacing x := by ring
    rw [e]
    exact ⟨k1.trans (add_le_add f1 g1), k2.trans (add_le_add f2 g2)⟩
  lap x hx := by
    have h := lap_add_le f g x (hf.lap x hx) (hg.lap x hx)
    have e : (A + B) / G'.spacing x ^ 2 = A / G'.spacing x ^ 2 + B / G'.spacing x ^ 2 := by ring
    rw [e]
    exact h

theorem fieldBounds_mono {η η' : ℝ} {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φ : G'.Ω 1 × Fin N → ℂ}
    (h : FieldBounds G' η Ψ φ) (hη : η ≤ η') : FieldBounds G' η' Ψ φ where
  close z := (h.close z).trans hη
  smooth := smooth_mono h.smooth hη
  unit := h.unit

/-- The complex solution of a member of `Ξ^c` satisfies the hypotheses `FieldBounds` of the
composition estimates, with size `2 η`, `η = (2d+1) σ ε`. -/
theorem xiC_fieldBounds (H : BgHyp d L k ϱ' a ν) {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    {Dr Dc : BgData G' N} (hXr : XiAt G' a ν k σ ε Dr Ψ₀ h₀)
    (hC : RealizesC Dc Ψ₀ h₀ Ψ'' h'') (hDcU : InUnionDomainC G' (bgC0 d L N) (bgC1 d L N) ν Dc)
    (hb : XiCBounds G' ν σ ε Dr Dc Ψ'' h'' (bgField G' a ν Dr)
      (bgFieldC G' a ν (bgC0 d L N) Dc) (bgMult G' a ν Dr) (bgMultC G' a ν (bgC0 d L N) Dc)) :
    FieldBounds G' (2 * xiEta d σ ε) (fun x i => (Ψ₀ x i : ℂ) + Ψ'' x i)
      (bgFieldC G' a ν (bgC0 d L N) Dc) := by
  have hXr' := hXr
  obtain ⟨hR, hDomR, hbr⟩ := hXr
  have hηpos := xiEta_pos (d := d) hσ hε
  have hA : 0 ≤ σ * ε := (mul_pos hσ hε).le
  have hsr := xi_smooth hσ hε hσ1 hbr
  have hsd := xiC_smooth hσ hε hσ1 hb
  have hfr := xi_fieldBounds H hσ hε hσ1 hXr'
  have hsum := isSmooth_add' hsr hsd
  have hbc : ∀ z, barVec G' Dc.Ψ (bgFieldC G' a ν (bgC0 d L N) Dc) z =
      barVec G' Dr.Ψ (bgField G' a ν Dr) z + diffBar G' Dc.Ψ Dr.Ψ (bgFieldC G' a ν (bgC0 d L N) Dc)
        (bgField G' a ν Dr) z := by
    intro z; funext i; simp [diffBar]
  have hsm : IsSmoothField G' (2 * xiEta d σ ε) (barVec G' Dc.Ψ (bgFieldC G' a ν (bgC0 d L N) Dc)) := by
    have e : barVec G' Dc.Ψ (bgFieldC G' a ν (bgC0 d L N) Dc) =
        fun y i => barVec G' Dr.Ψ (bgField G' a ν Dr) y i +
          diffBar G' Dc.Ψ Dr.Ψ (bgFieldC G' a ν (bgC0 d L N) Dc) (bgField G' a ν Dr) y i := by
      funext y; exact hbc y
    rw [e]
    refine smooth_mono hsum ?_
    have := le_xiEta (d := d) hσ hε
    linarith
  have hFB : FieldBounds G' (2 * xiEta d σ ε) Dc.Ψ (bgFieldC G' a ν (bgC0 d L N) Dc) :=
    { close := fun z => by
        have hzd : (z : Torus d (N₀ * L ^ k)) ∈ dataSites G' := (mem_dataSites G').2 (Or.inl z.2)
        have h1 := hfr.close z
        have h2 := psi_sub_le (G := G') (f := diffBar G' Dc.Ψ Dr.Ψ (bgFieldC G' a ν (bgC0 d L N) Dc)
          (bgField G' a ν Dr)) (ψ := Ψ'') hA hsd z.2 (xiC_mean hb z.2).le
          (x_mem_blk (G := G') (G'.layerIndex z.1) z.1)
        have e : (fun i => bgFieldC G' a ν (bgC0 d L N) Dc (z, i) - Dc.Ψ z i) =
            (fun i => bgField G' a ν Dr (z, i) - Dr.Ψ z i) -
              (fun i => Ψ'' z i - diffBar G' Dc.Ψ Dr.Ψ (bgFieldC G' a ν (bgC0 d L N) Dc)
                (bgField G' a ν Dr) z i) := by
          funext i
          simp only [Pi.sub_apply]
          rw [diffBar_of_mem z.2, psi''_eq hR hC hzd i]
          ring
        rw [e]
        refine (vn_sub_le_add _ _).trans ?_
        have : σ ^ 2 * ε + 2 * d * (σ * ε) ≤ xiEta d σ ε := by
          unfold xiEta
          have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          nlinarith [mul_pos hσ hε, mul_nonneg this (mul_pos hσ hε).le]
        linarith
      smooth := hsm
      unit := xiC_unit H hDcU }
  refine fieldBounds_congr hFB ?_
  intro x hx
  funext i
  rw [hC.1 x hx i]

end Complex

section Main

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {a : ℕ → ℝ} {ν : ℝ}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- **(Ξ3) = (R-S)** (SMALLFIELD.md §1.7; P3 Lemma 4.1): the scaled composition of a member of
`Ξ^c_k(𝔹'; 1, ε₀)`.  With `η = C₁ ε₀` (`C₁ = (4d+8)(2d+1)`, `(4d+6) η ≤ 1`), `𝔹 ≺ 𝔹'` with the
scale gap `ℓ ≤ θ ℓ'` on `Ω₁` and on the collar, `θ = L^{j-k}`, the composed data (6.2) of the real
part and of the complex displacement (with the fields `φ^r = bgField`, `φ^c = bgFieldC` of the
datum) lie in the scaled data domain `Ψ̃^c(𝔹; σ ε', ε')` of (R-S), `ε' = η`, `σ = C₀ θ`. -/
theorem xiC_scaledComposition (H' : BgHyp d L k ϱ' a ν) {a₁ ε₀ θ : ℝ} {j : ℕ}
    (hprec : Precedes G G') (hL : 2 ≤ L) (ha₁ : 0 < a₁) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hjθ : (L : ℝ) ^ j = θ * (L : ℝ) ^ k) (hnj : ∀ x ∈ G.Ω 1, G.layerIndex x ≤ j)
    (hgap : ScaleGap G G' θ) (hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z)
    (hsmall : (4 * d + 6) * (xiC1 d * ε₀) ≤ 1)
    (hX : XiC G' a ν k 1 ε₀ Ψ₀ h₀ Ψ'' h'') :
    ∃ φr φc : G'.Ω 1 × Fin N → ℂ,
      ScaledPsiC G ν (scaledC0 d * θ) (xiC1 d * ε₀) j (reR G G' a₁ φr Ψ₀) h₀
        (dPsi G G' a₁ φr φc Ψ₀ Ψ'') (hRes G h'') := by
  have hc1 := one_le_xiC1 d
  have hε₀ := hX.2.1
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hC1a : (2 * (d : ℝ) + 1) ≤ xiC1 d := by unfold xiC1; nlinarith
  have hC1b : 2 * (2 * (d : ℝ) + 1) ≤ xiC1 d := by unfold xiC1; nlinarith
  have hsmall' : (4 * d + 6) * ((2 * d + 1) * ε₀) ≤ 1 := by
    refine le_trans ?_ hsmall
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC1a hε₀.le) (by positivity)
  have hP := xiC_one_subset H' hsmall' hX
  obtain ⟨-, -, Dr, Dc, hXr, hC, hDcU, hb⟩ := hX
  have hXr' := hXr
  obtain ⟨hR, hDomR, hbr⟩ := hXr
  set η := xiC1 d * ε₀ with hη
  have hηpos : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    nlinarith [mul_nonneg hd hηpos.le]
  have hEta : xiEta d 1 ε₀ ≤ η := by
    unfold xiEta; rw [hη]; nlinarith [mul_le_mul_of_nonneg_right hC1a hε₀.le]
  have hEta2 : 2 * xiEta d 1 ε₀ ≤ η := by
    unfold xiEta; rw [hη]; nlinarith [mul_le_mul_of_nonneg_right hC1b hε₀.le]
  obtain ⟨hφre, hunr⟩ := xi_unit H' hXr'
  have hfr := fieldBounds_mono (xi_fieldBounds H' one_pos hε₀ le_rfl hXr') hEta
  have hfc := fieldBounds_mono (xiC_fieldBounds H' one_pos hε₀ le_rfl hXr' hC hDcU hb) hEta2
  refine ⟨bgField G' a ν Dr, bgFieldC G' a ν (bgC0 d L N) Dc, ?_⟩
  have HS : HypS G G' a₁ ν η η η θ j Ψ₀ h₀ Ψ'' h'' (bgField G' a ν Dr)
      (bgFieldC G' a ν (bgC0 d L N) Dc) :=
    { prec := hprec, hL := hL, ha₁ := ha₁, hθ0 := hθ0, hθ1 := hθ1, hjθ := hjθ, hnj := hnj,
      gap := hgap, hcol := hcol, hδ := hηpos, hδη := le_rfl, hηε := le_rfl, hε1 := hη1,
      hsmall := hsmall, hν := H'.mass, hνk := H'.massLe, hPC := hP,
      hφr := hφre
      hbr := fieldBounds_congr hfr (fun x hx => by funext i; simp [psiR, hR.1 x hx i]),
      hmass := fun z => by
        have := (hbr.mass z).le
        rw [one_mul] at this
        exact this.trans (by nlinarith),
      hbc := fieldBounds_congr hfc (fun x hx => by funext i; simp [psiC, hC.1 x hx i]),
      hdiff := fun z => (hb.val z).le.trans (by nlinarith) }
  exact scaledComposition HS

end Main

end Balaban.SmallField
