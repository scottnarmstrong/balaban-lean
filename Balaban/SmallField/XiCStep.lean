/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiCScale
public import Balaban.SmallField.XiProps
public import Balaban.Fluctuation.RenormXiC

/-!
# The renormalized datum stays in `Ξ^c` (`RenormThetaDatum` item (ii))

For `Ψ₀ + Ψ''` in `Ξ^c_k(𝔹; 1, ε)` with fixed external field (`h'' = 0`, the class `XiCOneReal`) and
`ξ = (ξ₁, ξ₂, ξ₃)` in the polydisc `‖ξ‖ < r`, the datum `θ_ξ = ((1 + ε ξ₁) Ψ, h)` realizes
`Ψ₀ + (Ψ'' + ζ Ψ)` and lies in `Ξ^c_k(𝔹; 1, ε')` with the radius `ε' = ε + xiLoss …` (`XiC.scale`).  The loss
is `ε ‖ξ‖` times a constant depending on `(d, L, N, K₂)` only (the P4 (4.19) loss); it does not depend on
the scale `k`.  The numerical premise is `2 (C₁ ε + 5 ε ‖ξ‖) ≤ c₁` (the renormalized datum in the domain of
Theorem 5.2).
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Fluctuation

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

/-- The datum with the lifted field multiplied by `1 + ζ`. -/
noncomputable def scaleBgData (D : BgData G N) (ζ : ℂ) : BgData G N where
  Ψ := fun x i => (1 + ζ) * D.Ψ x i
  h := D.h
  Ψ_layerConst := fun n hn1 hnk x hx x' hx' => by
    funext i; simp only [D.Ψ_layerConst n hn1 hnk x hx x' hx']
  h_layerConst := D.h_layerConst
  Ψ_zero := fun x hx => by funext i; simp [D.Ψ_zero x hx]
  h_zero := D.h_zero

/-- The inequalities of `Ξ` are monotone in the radius `ε`. -/
theorem XiBounds.mono_eps {ν σ ε ε' : ℝ} {n : ℕ} {D : BgData G N} {h₀ : Fin N → ℝ}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hσ : 0 ≤ σ) (hε : ε ≤ ε') (hε0 : 0 ≤ ε)
    (h : XiBounds G ν n σ ε D h₀ φ α) : XiBounds G ν n σ ε' D h₀ φ α where
  grad x hx μ := by
    have hℓ : 0 < G.spacing x := spacing_pos G
    have h1 : σ * ε / G.spacing x ≤ σ * ε' / G.spacing x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hε hσ) hℓ.le
    exact ⟨(h.grad x hx μ).1.trans_le h1, (h.grad x hx μ).2.trans_le h1⟩
  lap x hx := by
    have hℓ : 0 < G.spacing x := spacing_pos G
    exact (h.lap x hx).trans_le (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hε (by positivity)) (by positivity))
  mult x := (h.mult x).trans_le (mul_le_mul_of_nonneg_left hε (by positivity))
  close x hx := (h.close x hx).trans_le (mul_le_mul_of_nonneg_left hε (by positivity))
  collarBond z hz z' hz' hadj :=
    (h.collarBond z hz z' hz' hadj).trans_le (mul_le_mul_of_nonneg_left hε hσ)
  mass z := (h.mass z).trans_le (mul_le_mul_of_nonneg_left hε hσ)
  hnorm := (h.hnorm).trans_le (pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_left hε hσ) 2)

/-- Without external displacement the complex domain is monotone in `ε`. -/
theorem InPsiTildeC.mono_eps {ν δ ε ε' : ℝ} {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h : Fin N → ℝ}
    {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hP : InPsiTildeC G ν δ ε Ψ h Ψ' (fun _ _ => 0))
    (hε : ε ≤ ε') (hδ : 0 < δ) : InPsiTildeC G ν δ ε' Ψ h Ψ' (fun _ _ => 0) :=
  { hP with
    eps_pos := lt_of_lt_of_le hP.eps_pos hε
    c2a := fun x hx => (hP.c2a x hx).trans_le (by linarith)
    c3a := fun x hx => by
      have h0 : vn ((fun (_ : Torus d (N₀ * L ^ k)) (_ : Fin N) => (0 : ℂ)) x) = 0 := vn_zero
      rw [h0, mul_zero]; exact div_pos (pow_pos hδ 2) (lt_of_lt_of_le hP.eps_pos hε) }

/-- A datum of the complex domain with `2 δ ≤ c₁` has its background in the uniqueness class of
`IsRenSol.eq_bgC`: `(bgFieldC, bgMultC)` is a small solution with `c₀ = c₆/2`. -/
theorem isSmallSolutionC_of_inDomainC {a : ℕ → ℝ} {ν δ : ℝ} (H : BgHyp d L k ϱ a ν)
    {D : BgData G N} (hD : InDomainC G ν δ δ D) (hδ0 : 0 < δ) (hδc : 2 * δ ≤ bgC1 d L N) :
    IsSmallSolution G a ν (c6 d L N / 2) D (bgFieldC G a ν (bgC0 d L N) D)
      (bgMultC G a ν (bgC0 d L N) D) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hδ1 : δ ≤ bgC1 d L N := by linarith
  have hδ0c : δ ≤ bgC0 d L N := hδ1.trans (bgC1_le_bgC0 d L N hd0)
  have hνε : ν * ((L : ℝ) ^ k) ^ 2 * δ ^ 2 ≤ δ ^ 2 := mul_le_of_le_one_left (sq_nonneg _) H.massLe
  have hU : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D := ⟨δ, δ, hδ0, le_rfl, hδ0c, hδ1, hνε, hD⟩
  obtain ⟨-, hs, hb⟩ := theorem72 H hU
  refine ⟨hs.1, fun x => ?_⟩
  have h1 := (hb δ δ hδ0 le_rfl hδ0c hδ1 hνε hD).alpha x
  have h2 := (bgC1_facts d L N hd0 (δ := 2 * δ) hδc).2.2.2
  have h0 := bgC0_pos d L N hd0
  have h6 := bgC0_le_c6 d L N
  nlinarith [bgK1_pos d L N]

/-- **The loss of the radius** `ε' − ε` (P4 (4.19)): a constant times `ε ‖ξ‖`, with `V = K₂'·8 ε ‖ξ‖`
the bound of the solution map and `ρ = ε ‖ξ‖` the bound of `|ζ|`; the constants depend on `d, L, N` only. -/
noncomputable def xiLoss (d L N : ℕ) [NeZero L] (ε t : ℝ) : ℝ :=
  N * (cK2 d L N * (8 * ε * t)) + 3 * (ε * t) * L +
    N * (cK2 d L N * (8 * ε * t) + 6 * d * (ε * t) * (L : ℝ) ^ 2) + cK2 d L N * (8 * ε * t) +
    N * (3 * (ε * t) + cK2 d L N * (8 * ε * t)) + 2 * ε * (ε * t)

/-- The six inequalities that `XiCBounds.scale` asks of the loss, for `σ = 1`. -/
theorem xiLoss_rooms {N d L V ρ ζn ε : ℝ} (hV : 0 ≤ V) (hρ : 0 ≤ ρ) (hζ : ζn ≤ ρ)
    (hε : 0 ≤ ε) (hN : 0 ≤ N) (hd : 0 ≤ d) (hL : 0 ≤ L) :
    let Δ := N * V + 3 * ρ * L + N * (V + 6 * d * ρ * L ^ 2) + V + N * (3 * ρ + V) + 2 * ε * ρ
    N * V + 3 * ζn * L ≤ 1 * Δ ∧ N * (V + 6 * d * ζn * L ^ 2) ≤ 1 ^ 2 * Δ ∧ V ≤ 1 ^ 2 * Δ ∧
      N * V ≤ Δ ∧ N * (3 * ζn + V) ≤ 1 ^ 2 * Δ ∧ 2 * 1 * ε * ζn ≤ 1 * Δ := by
  intro Δ
  have a1 : 3 * ζn * L ≤ 3 * ρ * L := by nlinarith
  have a2 : N * (V + 6 * d * ζn * L ^ 2) ≤ N * (V + 6 * d * ρ * L ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hN
    have : 6 * d * ζn * L ^ 2 ≤ 6 * d * ρ * L ^ 2 := by
      have : 0 ≤ d * L ^ 2 := by positivity
      nlinarith
    linarith
  have a3 : N * (3 * ζn + V) ≤ N * (3 * ρ + V) :=
    mul_le_mul_of_nonneg_left (by linarith) hN
  have a4 : 2 * 1 * ε * ζn ≤ 2 * ε * ρ := by nlinarith
  have b1 : 0 ≤ N * V := by positivity
  have b2 : 0 ≤ 3 * ρ * L := by positivity
  have b3 : 0 ≤ N * (V + 6 * d * ρ * L ^ 2) := by positivity
  have b5 : 0 ≤ N * (3 * ρ + V) := by positivity
  have b6 : 0 ≤ 2 * ε * ρ := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Δ] <;> nlinarith

theorem xiLoss_nonneg (d L N : ℕ) [NeZero L] {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) : 0 ≤ xiLoss d L N ε t := by
  have := (cK2_pos d L N).le
  unfold xiLoss; positivity

/-- **`Ξ^c` is stable under the renormalization of the datum** (`RenormThetaDatum` item (ii)).  Let
`Ψ₀ + Ψ''` be in `Ξ^c_k(𝔹; 1, ε)` with fixed external field (`h'' = 0`), `F` a solution map (`IsRenSol`)
and `ξ` with `‖ξ‖ < r`, `ξ₂ = ξ₃ = 0` (the datum `θ_ξ` depends on `ξ₁` only).  Then `θ_ξ` realizes
`Ψ₀ + (Ψ'' + ζ(Ψ₀ + Ψ''))`, `ζ = ε ξ₁`, and lies in `Ξ^c_k(𝔹; 1, ε + xiLoss d L N ε ‖ξ‖)`.  The numerical
premise is `2(C₁ ε + 5 ε ‖ξ‖) ≤ c₁` (the renormalized datum in the domain of Theorem 5.2); the loss
`xiLoss` is `O(ε ‖ξ‖)` with a constant depending on `(d, L, N)` only, not on `k`. -/
theorem XiC.scale {a : ℕ → ℝ} {ν ε r : ℝ} {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h₀ : Fin N → ℝ} {Ψ'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    (H : BgHyp d L k ϱ a ν) (hϱ : 1 < ϱ) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    (hF : IsRenSol G a ν ε ε r (8 * ε) F)
    (hX : XiC G a ν k 1 ε Ψ₀ h₀ Ψ'' (fun _ _ => 0)) {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ < r)
    (h1 : ξ 1 = 0) (h2 : ξ 2 = 0)
    (hr : 2 * (xiC1 d * ε + 5 * (ε * ‖ξ‖)) ≤ bgC1 d L N) :
    XiC G a ν k 1 (ε + xiLoss d L N ε ‖ξ‖) Ψ₀ h₀
      (fun x i => Ψ'' x i + renZeta ε ξ * ((Ψ₀ x i : ℂ) + Ψ'' x i)) (fun _ _ => 0) := by
  classical
  have hX0 := hX
  obtain ⟨hσ, hε', Dr, Dc, hDr, hR, hU, hB⟩ := hX
  set ζ : ℂ := renZeta ε ξ with hζdef
  have hd0 : 0 < d := by have := H.hd; omega
  have hρ : ‖ζ‖ ≤ ε * ‖ξ‖ := norm_renZeta_le hε.le ξ
  have hξ0 := norm_nonneg ξ
  have hC1 := one_le_xiC1 d
  set δ₀ := xiC1 d * ε with hδ₀def
  have hδ₀pos : 0 < δ₀ := by positivity
  have hρ0 := norm_nonneg ζ
  have hbc1 := (bgC1_facts d L N hd0 (le_refl (bgC1 d L N))).1
  have happ := (approxDelta_le d L hbc1).1
  have hδn : δ₀ + 5 * ‖ζ‖ ≤ bgC1 d L N / 2 := by nlinarith
  have hδ₀3 : δ₀ ≤ 1 / 16 := by
    have : bgC1 d L N / 2 ≤ 1 / 2048 := by linarith
    nlinarith
  have hζ256 : ‖ζ‖ ≤ 1 / 256 := by nlinarith
  have hPsi := xiC_one_subset H hsm hX0
  have hP1 := hPsi.scale (ζ := ζ) hζ256 hδ₀pos (by linarith) hδ₀3
  have hP2 := InPsiTildeC.mono_eps hP1 (ε' := δ₀ + 5 * ‖ζ‖) (by linarith) (by positivity)
  let Dn : BgData G N := scaleBgData Dc ζ
  have hDnC : InDomainC G ν (δ₀ + 5 * ‖ζ‖) (δ₀ + 5 * ‖ζ‖) Dn := by
    refine ⟨Ψ₀, h₀, _, fun _ _ => 0, hP2, fun x hx i => ?_, fun x hx i => ?_⟩
    · show (1 + ζ) * Dc.Ψ x i = _
      rw [hR.1 x hx i]; ring
    · show Dc.h x i = _
      rw [hR.2 x hx i]
  have hδnpos : 0 < δ₀ + 5 * ‖ζ‖ := by positivity
  have hδn2 : 2 * (δ₀ + 5 * ‖ζ‖) ≤ bgC1 d L N := by linarith
  have hφn := isSmallSolutionC_of_inDomainC H hDnC hδnpos hδn2
  have hDcX : XiCOne G a ν ε Dc := ⟨Ψ₀, h₀, Ψ'', _, hX0, hR⟩
  have heq := hF.eq_bgC H hε hsm hc1 hDcX hξ h1 h2 (Dc := Dn) (fun _ _ => rfl) (fun _ _ => rfl)
    (c₀ := c6 d L N / 2) (by linarith) hφn
  have hsup := hF.sup Dc hDcX ξ hξ
  have hsmall := hF.small Dc hDcX ξ hξ
  rw [heq] at hsup hsmall
  simp only [] at hsup hsmall
  have hVpos : 0 ≤ cK2 d L N * (8 * ε * ‖ξ‖) := by
    have := (cK2_pos d L N).le; positivity
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hvΨ : ∀ x ∈ dataSites G, vn (Dc.Ψ x) ≤ 3 := by
    intro x hx
    have e : Dc.Ψ x = fun i => (Ψ₀ x i : ℂ) + Ψ'' x i := funext fun i => hR.1 x hx i
    rw [e]
    have a1 := vn_add' (fun i => (Ψ₀ x i : ℂ)) (Ψ'' x)
    have a2 : vn (fun i => (Ψ₀ x i : ℂ)) ≤ 2 := by
      rw [vn_ofReal]
      have h2' := hPsi.r2 x hx
      have hsq : rn (Ψ₀ x) ^ 2 = ∑ i, Ψ₀ x i ^ 2 := by
        unfold rn; rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      have hr0 : 0 ≤ rn (Ψ₀ x) := Real.sqrt_nonneg _
      by_contra hc; push Not at hc
      have := abs_lt.mp h2'
      nlinarith
    have a3 := hPsi.c2a x hx
    linarith
  have hcol : ∀ z ∈ collar G, ∀ z' ∈ collar G, Adj z z' →
      vn (fun i => Dc.Ψ z i - Dc.Ψ z' i) ≤ 2 * 1 * ε := by
    intro z hz z' hz' hadj
    have hzd : z ∈ dataSites G := (mem_dataSites G).2 (Or.inr hz)
    have hzd' : z' ∈ dataSites G := (mem_dataSites G).2 (Or.inr hz')
    have e : (fun i => Dc.Ψ z i - Dc.Ψ z' i) =
        fun i => (Dr.Ψ z i - Dr.Ψ z' i) + (Ψ'' z i - Ψ'' z' i) := by
      funext i
      rw [hR.1 z hzd i, hR.1 z' hzd' i, hDr.1.1 z hzd i, hDr.1.1 z' hzd' i]; ring
    rw [e]
    have b1 := hDr.2.2.collarBond z hz z' hz' hadj
    have b2 := hB.collarBond z hz z' hz' hadj
    have b3 := vn_add' (fun i => Dr.Ψ z i - Dr.Ψ z' i) (fun i => Ψ'' z i - Ψ'' z' i)
    linarith
  have hΔ := xiLoss_nonneg d L N hε.le hξ0
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbd : ‖ζ‖ ≤ ε * ‖ξ‖ := hρ
  have hΨ''n : ∀ x ∈ dataSites G, ∀ i, ((Ψ'' x i + ζ * ((Ψ₀ x i : ℂ) + Ψ'' x i))) =
      Ψ'' x i + ζ * Dc.Ψ x i := fun x hx i => by rw [hR.1 x hx i]
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6⟩ := xiLoss_rooms (N := (N : ℝ)) (d := (d : ℝ)) (L := (L : ℝ))
    (V := cK2 d L N * (8 * ε * ‖ξ‖)) (ρ := ε * ‖ξ‖) (ζn := ‖ζ‖) (ε := ε) hVpos
    (by positivity) hbd hε.le hNn (Nat.cast_nonneg d) (by linarith)
  have hΔ' : ε + xiLoss d L N ε ‖ξ‖ - ε = (N : ℝ) * (cK2 d L N * (8 * ε * ‖ξ‖)) +
      3 * (ε * ‖ξ‖) * L + N * (cK2 d L N * (8 * ε * ‖ξ‖) + 6 * d * (ε * ‖ξ‖) * (L : ℝ) ^ 2) +
      cK2 d L N * (8 * ε * ‖ξ‖) + N * (3 * (ε * ‖ξ‖) + cK2 d L N * (8 * ε * ‖ξ‖)) +
      2 * ε * (ε * ‖ξ‖) := by unfold xiLoss; ring
  have hscale := XiCBounds.scale (Dn := Dn) (V := cK2 d L N * (8 * ε * ‖ξ‖))
    (ε' := ε + xiLoss d L N ε ‖ξ‖) (Ψ''n := fun x i => Ψ'' x i + ζ * ((Ψ₀ x i : ℂ) + Ψ'' x i))
    hΨ''n hB hϱ (fun _ _ _ => rfl) hsup hsmall hVpos one_pos hε hvΨ hcol (by linarith) (by rw [hΔ']; exact hr1) (by rw [hΔ']; exact hr2)
    (by rw [hΔ']; exact hr3) (by rw [hΔ']; simpa using hr4) (by rw [hΔ']; exact hr5)
    (by rw [hΔ']; exact hr6)
  refine ⟨one_pos, by linarith, Dr, Dn, ⟨hDr.1, hDr.2.1, ?_⟩, ⟨fun x hx i => ?_, fun x hx i => ?_⟩,
    ⟨δ₀ + 5 * ‖ζ‖, δ₀ + 5 * ‖ζ‖, hδnpos, le_rfl, ?_, ?_, ?_, hDnC⟩, hscale⟩
  · exact hDr.2.2.mono_eps zero_le_one (by linarith) hε.le
  · show (1 + ζ) * Dc.Ψ x i = _
    rw [hR.1 x hx i]; ring
  · show Dc.h x i = _
    rw [hR.2 x hx i]
  · have := bgC1_le_bgC0 d L N hd0; linarith
  · linarith
  · exact mul_le_of_le_one_left (sq_nonneg _) H.massLe

end Balaban.SmallField
