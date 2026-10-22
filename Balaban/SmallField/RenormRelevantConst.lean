/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormExpBounds
public import Balaban.SmallField.RenormRelevantAdd

/-!
# The background of constant data on a whole-lattice level

For a whole-lattice generating set of level `n` (`IsLevel G n`: `Ω₁` is the whole torus, the collar is
empty) and constant data `Ψ ≡ c e`, `h̃ ≡ c' e` along a unit direction `e`, the constant field
`φ ≡ e` solves (EL) with the constant multiplier
`α = a_n L^{-2n} (c − 1) + ν (c' − 1)`.  This is the explicit reference background of the relevant
parts of the renormalization conditions (no Green function is needed).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Matrix

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {n : ℕ}

theorem IsLevel.collar_eq (hG : IsLevel G n) : collar G = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  exact ((mem_collar G).1 hx).1 (hG x).1

theorem IsLevel.dataSites_eq (hG : IsLevel G n) : dataSites G = Finset.univ := by
  ext x
  simp only [Finset.mem_univ, iff_true]
  exact (mem_dataSites G).2 (Or.inl (hG x).1)

/-- The constant datum `(Ψ, h̃) ≡ (ψ, h)` on a whole-lattice level. -/
noncomputable def constBg (hG : IsLevel G n) (ψ h : Fin N → ℂ) : BgData G N where
  Ψ := fun _ => ψ
  h := fun _ => h
  Ψ_layerConst := fun _ _ _ _ _ _ _ => rfl
  h_layerConst := fun _ _ _ _ _ _ _ => rfl
  Ψ_zero := fun x hx => absurd (by rw [hG.dataSites_eq]; exact Finset.mem_univ x) hx
  h_zero := fun x hx => absurd (hG x).1 hx

/-- **The constant background solves (EL)**: `φ ≡ e` with the multiplier
`α ≡ a_n L^{-2n}(c − 1) + ν (c' − 1)`. -/
theorem isEL_const (hG : IsLevel G n) (a : ℕ → ℝ) (ν : ℝ) (e : Fin N → ℂ) (he : ∑ i, e i * e i = 1)
    (c c' : ℂ) :
    IsEL G a ν (constBg hG (c • e) (c' • e)) (fun p => e p.2)
      (fun _ => ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) * (c - 1) + ν * (c' - 1)) := by
  refine ⟨?_, fun x => he⟩
  funext ⟨x, i⟩
  rw [liftOp_mulVec, dirichlet_apply]
  have hz : zeroExt (G.Ω 1) (fun z : G.Ω 1 => e i) = fun _ => e i := by
    funext y; exact zeroExt_mem _ _ ⟨y, (hG y).1⟩
  rw [hz]
  have hx : G.layerIndex (x : Torus d (N₀ * L ^ k)) = n := (hG x).2
  have hcard := card_blk_cast G (G.layerIndex (x : Torus d (N₀ * L ^ k)))
    (G.layerIndex_spec x.2).2.1 x
  have hLd : (0 : ℝ) < ((L : ℝ) ^ n) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hnl : negLap (fun _ : Torus d (N₀ * L ^ k) => e i) x = 0 := by
    simp [negLap]; ring
  have hbt : blockTerm G a (fun _ : Torus d (N₀ * L ^ k) => e i) x =
      ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) * e i := by
    unfold blockTerm
    rw [hx]
    rw [hx] at hcard
    simp only [Finset.sum_const, nsmul_eq_mul]
    have : ((G.blk n x).card : ℂ) = (((L : ℝ) ^ n) ^ d : ℝ) := by exact_mod_cast hcard
    rw [this]
    push_cast
    have hL0 : ((L : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)
    have hLd0 : ((L : ℂ) ^ n) ^ d ≠ 0 := pow_ne_zero _ hL0
    field_simp
  rw [hnl, hbt]
  simp only [source, qStar, boundaryTerm, constBg, hG.collar_eq, Finset.notMem_empty, ↓reduceIte,
    Finset.sum_const_zero, add_zero, hx, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The real centre `(e, e)` with the displacement `t e` lies in `Ψ̃^c(𝔹; δ, δ)` for `‖t‖ ≤ δ/4`,
`0 < δ ≤ 1`. -/
theorem inPsiTildeC_const (eR : Fin N → ℝ) (heR : ∑ i, eR i ^ 2 = 1) {ν δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℂ) (ht : ‖t‖ ≤ δ / 4) :
    InPsiTildeC G ν δ δ (fun _ i => eR i) eR (fun _ i => t * (eR i : ℂ)) (fun _ _ => 0) := by
  have hrn : rn eR = 1 := by unfold rn; rw [heR]; simp
  have hdot : ∑ i, eR i * eR i = 1 := by simpa [sq] using heR
  have ht0 := norm_nonneg t
  refine
      { layerConst := fun _ _ _ _ _ _ _ => rfl
        r1 := fun x x' _ => by simpa [rn] using hδ
        r2 := fun x _ => by simpa [heR] using hδ
        r3 := fun x _ => by simp [hdot, hrn]; positivity
        r4 := by simp [heR]; positivity
        eps_pos := hδ
        layerConst' := fun _ _ _ _ _ _ _ => rfl
        hLayerConst' := fun _ _ _ _ _ _ _ => rfl
        c1 := fun x x' _ => by simp only [sub_self, vn_zero]; exact hδ
        c2a := fun x _ => ?_
        c2b := fun x _ => ?_
        c3a := fun x _ => ?_
        c3b := fun x _ => ?_ }
  · have e : (fun i => t * (eR i : ℂ)) = fun i => t * ((eR i : ℝ) : ℂ) := rfl
    rw [e, vn_smul_complex, vn_ofReal, hrn]
    linarith
  · have e : ∑ i, ((eR i : ℂ) + t * (eR i : ℂ)) * ((eR i : ℂ) + t * (eR i : ℂ)) -
        ∑ i, (eR i : ℂ) * (eR i : ℂ) = (2 * t + t ^ 2) * ((∑ i, eR i * eR i : ℝ) : ℂ) := by
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, hdot]
    simp only [Complex.ofReal_one, mul_one]
    calc ‖2 * t + t ^ 2‖ ≤ ‖2 * t‖ + ‖t ^ 2‖ := norm_add_le _ _
      _ < δ := by
        rw [norm_mul, norm_pow]
        have : ‖(2 : ℂ)‖ = 2 := by simp
        rw [this]
        nlinarith
  · have h0 : vn ((fun (_ : Torus d (N₀ * L ^ k)) (_ : Fin N) => (0 : ℂ)) x) = 0 := vn_zero
    rw [h0, mul_zero]; positivity
  · simp only [mul_zero, Finset.sum_const_zero, norm_zero]; positivity

/-- The constant datum `((1 + t) e, e)` along a real unit vector `e` lies in the complex data domain
for `‖t‖ ≤ δ/4`, `0 < δ ≤ 1`. -/
theorem inDomainC_const (hG : IsLevel G n) (eR : Fin N → ℝ) (heR : ∑ i, eR i ^ 2 = 1) {ν δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℂ) (ht : ‖t‖ ≤ δ / 4) :
    InDomainC G ν δ δ (constBg hG ((1 + t) • fun i => (eR i : ℂ)) (fun i => (eR i : ℂ))) := by
  refine ⟨fun _ i => eR i, eR, fun _ i => t * (eR i : ℂ), fun _ _ => 0,
    inPsiTildeC_const eR heR hδ hδ1 t ht, ?_, ?_⟩
  · intro x _ i; simp [constBg]; ring
  · intro x _ i; simp [constBg]

/-- The real constant datum `(e, e)` lies in the real data domain `Ψ̃(𝔹_k; δ)`. -/
theorem inDomainR_const (hG : IsLevel G n) (eR : Fin N → ℝ) (heR : ∑ i, eR i ^ 2 = 1) {ν δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    InDomainR G ν δ (constBg hG (fun i => (eR i : ℂ)) (fun i => (eR i : ℂ))) :=
  ⟨fun _ i => eR i, eR, (inPsiTildeC_const (G := G) eR heR hδ hδ1 0 (by simp; positivity)).toInPsiTilde,
    fun x _ i => by simp [constBg], fun x _ i => by simp [constBg]⟩

/-- At a site of a whole-lattice level `ℓ² · (a_n L^{-2n} |t|) = |a_n| |t|`. -/
theorem sq_spacing_mul_norm (hG : IsLevel G n) (a : ℕ → ℝ) (t : ℂ) (x : G.Ω 1) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) * t‖ =
      |a n| * ‖t‖ := by
  have hx : G.layerIndex (x : Torus d (N₀ * L ^ k)) = n := (hG x).2
  have hLn : (0 : ℝ) < ((L : ℝ) ^ n) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  show ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 * _ = _
  have hL0 : (L : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)
  rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hLn]
  field_simp

/-- The constant datum `((1 + t) e, e)` lies in the complex union domain. -/
theorem inUnionDomainC_const {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν) (hG : IsLevel G n)
    (eR : Fin N → ℝ) (heR : ∑ i, eR i ^ 2 = 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδc : δ ≤ bgC1 d L N) (t : ℂ) (ht : ‖t‖ ≤ δ / 4) :
    InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν
      (constBg hG ((1 + t) • fun i => (eR i : ℂ)) (fun i => (eR i : ℂ))) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hδ0c : δ ≤ bgC0 d L N := hδc.trans (bgC1_le_bgC0 d L N hd0)
  have hνε : ν * ((L : ℝ) ^ k) ^ 2 * δ ^ 2 ≤ δ ^ 2 := mul_le_of_le_one_left (sq_nonneg _) H.massLe
  exact ⟨δ, δ, hδ, le_rfl, hδ0c, hδc, hνε, inDomainC_const hG eR heR hδ hδ1 t ht⟩

/-- **The background of the constant datum `((1+t)e, e)` is the constant `e`**, with the multiplier
`a_n L^{-2n} t` (for `‖t‖ ≤ δ/4`, `δ ≤ min (1, c₁/…)`; the multiplier is small: `a_n ‖t‖ < c₀`). -/
theorem bgFieldC_const {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν) (hG : IsLevel G n)
    (eR : Fin N → ℝ) (heR : ∑ i, eR i ^ 2 = 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδc : δ ≤ bgC1 d L N) (t : ℂ) (ht : ‖t‖ ≤ δ / 4) (hα : |a n| * ‖t‖ < bgC0 d L N) :
    bgFieldC G a ν (bgC0 d L N)
        (constBg hG ((1 + t) • fun i => (eR i : ℂ)) (fun i => (eR i : ℂ))) =
        (fun p => (eR p.2 : ℂ)) ∧
      bgMultC G a ν (bgC0 d L N)
        (constBg hG ((1 + t) • fun i => (eR i : ℂ)) (fun i => (eR i : ℂ))) =
        fun _ => ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) * t := by
  have hU := inUnionDomainC_const H hG eR heR hδ hδ1 hδc t ht
  obtain ⟨hex, -, -⟩ := theorem72 H hU
  obtain ⟨s, -, hsu⟩ := hex
  have hdot : ∑ i, eR i * eR i = 1 := by simpa [sq] using heR
  have hdotC : ∑ i, (eR i : ℂ) * (eR i : ℂ) = 1 := by exact_mod_cast hdot
  have hel := isEL_const hG a ν (fun i => (eR i : ℂ)) hdotC (1 + t) 1
  have hα' : (fun _ : G.Ω 1 => ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) * (1 + t - 1) + (ν : ℂ) * (1 - 1)) =
      (fun _ : G.Ω 1 => ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) * t) := by
    funext _; ring
  have hel' := hel
  rw [one_smul, hα'] at hel'
  have hs : IsSmallSolution G a ν (bgC0 d L N)
      (constBg hG ((1 + t) • fun i => (eR i : ℂ)) (fun i => (eR i : ℂ))) (fun p => (eR p.2 : ℂ))
      (fun _ => ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) * t) := by
    refine ⟨?_, fun x => ?_⟩
    · exact hel'
    · have e := sq_spacing_mul_norm (d := d) (L := L) hG a t x
      rw [e]; exact hα
  have hu : ∀ (φ' : G.Ω 1 × Fin N → ℂ) (α' : G.Ω 1 → ℂ),
      IsSmallSolution G a ν (bgC0 d L N)
        (constBg hG ((1 + t) • fun i => (eR i : ℂ)) (fun i => (eR i : ℂ))) φ' α' →
      φ' = (fun p : G.Ω 1 × Fin N => (eR p.2 : ℂ)) ∧
        α' = (fun _ : G.Ω 1 => ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) * t) := by
    intro φ' α' h'
    have h1 : (φ', α') = s := hsu (φ', α') h'
    have h2 : ((fun p : G.Ω 1 × Fin N => (eR p.2 : ℂ)),
        (fun _ : G.Ω 1 => ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) * t)) = s :=
      hsu ((fun p : G.Ω 1 × Fin N => (eR p.2 : ℂ)),
        (fun _ : G.Ω 1 => ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) * t)) hs
    have h3 := h1.trans h2.symm
    exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩
  exact bgFieldC_eq hs hu

/-- The block average of a constant field is the constant. -/
theorem blockAvg_const (hG : IsLevel G n) (e : Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    blockAvg G (fun p => e p.2) x i = e i := by
  have hx : G.layerIndex x = n := (hG x).2
  have hcard := card_blk_cast G (G.layerIndex x) (G.layerIndex_spec (hG x).1).2.1 x
  have hz : ∀ y, svec G (fun p : G.Ω 1 × Fin N => e p.2) y i = e i := fun y => by
    simp [svec, zeroExt, (hG y).1]
  unfold blockAvg
  simp only [hz, Finset.sum_const, nsmul_eq_mul]
  rw [hx] at hcard ⊢
  have : ((G.blk n x).card : ℂ) = (((L : ℝ) ^ n) ^ d : ℝ) := by exact_mod_cast hcard
  rw [this]
  have hL0 : ((L : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)
  push_cast
  field_simp

/-- A constant field has no bond terms: `bondSite = 0`. -/
theorem bondSite_const (hG : IsLevel G n) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (e : Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) : bondSite G Ψ (fun p => e p.2) x = 0 := by
  have hb : ∀ y i, barField G Ψ (fun p : G.Ω 1 × Fin N => e p.2) y i = e i := fun y i => by
    simp [barField, (hG y).1]
  unfold bondSite
  refine Finset.sum_eq_zero fun μ _ => ?_
  split_ifs
  · simp [hb]
  · rfl

open Filter Topology in
/-- **The `ψ`-derivative of the site density of `C₁` at constant data** (row 1 of the renormalization
system, P4 (E1)).  For a whole-lattice level, the site density of `C₁` evaluated at the constant data
`((1+t) e, e)`, with the background `bgFieldC` of the data, has `t`-derivative
`a_n L^{-2n} (1 + ξ₃)(ζ + ζ²)` at `t = 0`, `ζ = renZeta εζ ξ`: the block term `½ ξ₃ |ψ − Qφ|²` is
quadratic, the mass and bond terms vanish at the constant background. -/
theorem relDpsi_renC1Site {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν) (hG : IsLevel G n)
    (i₀ : Fin N) (εζ : ℝ) (ξ : Fin 3 → ℂ) (x : Torus d (N₀ * L ^ k)) :
    relDpsi (fun ψ h => renC1Site G a ν εζ ξ (fun _ => ψ) (fun _ => h)
        (bgFieldC G a ν (bgC0 d L N) (constBg hG ψ h)) x) i₀ =
      (blockWt G a x : ℂ) * (1 + ξ 2) * (renZeta εζ ξ + renZeta εζ ξ ^ 2) := by
  classical
  set eR : Fin N → ℝ := Pi.single i₀ 1 with heRdef
  have heR : ∑ i, eR i ^ 2 = 1 := by simp [heRdef, Pi.single_apply]
  have hdot : ∑ i, eR i * eR i = 1 := by simpa [sq] using heR
  have hdotC : ∑ i, (eR i : ℂ) * (eR i : ℂ) = 1 := by exact_mod_cast hdot
  have hE : (relE i₀ : Fin N → ℂ) = fun i => (eR i : ℂ) := by
    funext i; simp [relE, heRdef, Pi.single_apply]; split_ifs <;> simp
  have hd0 : 0 < d := by have := H.hd; omega
  set δ : ℝ := min (min 1 (bgC1 d L N)) (bgC0 d L N / (|a n| + 1)) with hδdef
  have hc0 := bgC0_pos d L N hd0
  have hc1 : 0 < bgC1 d L N := by
    have h0 := bgC0_pos d L N hd0
    have hK := bgK1_pos d L N
    have hC := lemma53Const_pos d L
    have ha : 0 < approxDelta d L := approxDelta_pos d L
    have hδs := deltaStar_pos d L N hd0
    unfold bgC1; positivity
  have hδpos : 0 < δ := lt_min (lt_min one_pos hc1) (div_pos hc0 (by have := abs_nonneg (a n); linarith))
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδc : δ ≤ bgC1 d L N := (min_le_left _ _).trans (min_le_right _ _)
  set ζ : ℂ := renZeta εζ ξ with hζ
  set w : ℝ := blockWt G a x with hw
  let g : ℂ → ℂ := fun t => (w : ℂ) * (ξ 2 / 2 * (t * t) +
    (1 + ξ 2) * (ζ * ((1 + t) * t) + ζ ^ 2 / 2 * ((1 + t) * (1 + t))))
  have hev : (fun t : ℂ => (fun ψ h => renC1Site G a ν εζ ξ (fun _ => ψ) (fun _ => h)
        (bgFieldC G a ν (bgC0 d L N) (constBg hG ψ h)) x) ((1 + t) • relE i₀) (relE i₀)) =ᶠ[𝓝 0] g := by
    have hmem : Metric.closedBall (0 : ℂ) (δ / 4) ∈ 𝓝 (0 : ℂ) :=
      Metric.closedBall_mem_nhds 0 (by linarith)
    filter_upwards [hmem] with t ht
    have ht' : ‖t‖ ≤ δ / 4 := by simpa using ht
    have hα : |a n| * ‖t‖ < bgC0 d L N := by
      have h1 : δ ≤ bgC0 d L N / (|a n| + 1) := (min_le_right _ _)
      have h2 : δ * (|a n| + 1) ≤ bgC0 d L N := by
        rwa [le_div_iff₀ (by positivity)] at h1
      have h3 : |a n| * ‖t‖ ≤ |a n| * (δ / 4) :=
        mul_le_mul_of_nonneg_left ht' (abs_nonneg _)
      nlinarith [abs_nonneg (a n)]
    have hb := bgFieldC_const H hG eR heR hδpos hδ1 hδc t ht' hα
    rw [hE]
    rw [hb.1]
    have hx : x ∈ G.Ω 1 := (hG x).1
    unfold renC1Site
    rw [ite_eq_left_iff.2 (fun h => absurd hx h), bondSite_const hG _ (fun i => (eR i : ℂ))]
    simp only [blockAvg_const hG (fun i => (eR i : ℂ)), Pi.smul_apply, smul_eq_mul, svec, zeroExt,
      hx, dite_true, sub_self, mul_zero, Finset.sum_const_zero, add_zero]
    have s1 : ∑ i, ((1 + t) * (eR i : ℂ) - (eR i : ℂ)) * ((1 + t) * (eR i : ℂ) - (eR i : ℂ)) =
        t * t := by
      calc _ = ∑ i, (t * t) * ((eR i : ℂ) * (eR i : ℂ)) := Finset.sum_congr rfl fun i _ => by ring
        _ = t * t := by rw [← Finset.mul_sum, hdotC, mul_one]
    have s2 : ∑ i, (1 + t) * (eR i : ℂ) * ((1 + t) * (eR i : ℂ) - (eR i : ℂ)) = (1 + t) * t := by
      calc _ = ∑ i, ((1 + t) * t) * ((eR i : ℂ) * (eR i : ℂ)) := Finset.sum_congr rfl fun i _ => by ring
        _ = (1 + t) * t := by rw [← Finset.mul_sum, hdotC, mul_one]
    have s3 : ∑ i, (1 + t) * (eR i : ℂ) * ((1 + t) * (eR i : ℂ)) = (1 + t) * (1 + t) := by
      calc _ = ∑ i, ((1 + t) * (1 + t)) * ((eR i : ℂ) * (eR i : ℂ)) := Finset.sum_congr rfl fun i _ => by ring
        _ = (1 + t) * (1 + t) := by rw [← Finset.mul_sum, hdotC, mul_one]
    rw [s1, s2, s3]
  have hder : HasDerivAt g ((w : ℂ) * (1 + ξ 2) * (ζ + ζ ^ 2)) 0 := by
    have := (((hasDerivAt_id (0 : ℂ)).mul (hasDerivAt_id (0 : ℂ))).const_mul (ξ 2 / 2)).add
      ((((((hasDerivAt_id (0 : ℂ)).const_add 1).mul (hasDerivAt_id (0 : ℂ))).const_mul ζ).add
        ((((hasDerivAt_id (0 : ℂ)).const_add 1).mul ((hasDerivAt_id (0 : ℂ)).const_add 1)).const_mul
          (ζ ^ 2 / 2))).const_mul (1 + ξ 2))
    have h2 := this.const_mul (w : ℂ)
    have h3 := h2.congr_of_eventuallyEq (f₁ := g) (Filter.Eventually.of_forall fun t => by
      simp only [g, Pi.add_apply, Pi.mul_apply, id])
    refine h3.congr_deriv ?_
    simp
    ring
  unfold relDpsi
  rw [hev.deriv_eq]
  exact hder.deriv

/-- The extension of a constant field is the constant. -/
theorem barField_const (hG : IsLevel G n) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (e : Fin N → ℂ)
    (y : Torus d (N₀ * L ^ k)) (i : Fin N) : barField G Ψ (fun p => e p.2) y i = e i := by
  simp [barField, (hG y).1]

/-- **The constant configuration is in the class `Ξ^c_k(𝔹; 1, ε)`**: the real centre `(e, e)` with the
displacement `t e` (for `‖t‖` small), with the constant background `e`, multiplier `0` resp.
`a_n L^{-2n} t`. -/
theorem xiC_const {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν) (hG : IsLevel G n) (eR : Fin N → ℝ)
    (heR : ∑ i, eR i ^ 2 = 1) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδc : δ ≤ bgC1 d L N) (t : ℂ) (ht : ‖t‖ ≤ δ / 4) (hα : |a n| * ‖t‖ < bgC0 d L N)
    (htε : ‖t‖ < ε) (hαε : |a n| * ‖t‖ < ε) :
    XiC G a ν k 1 ε (fun _ i => eR i) eR (fun _ i => t * (eR i : ℂ)) (fun _ _ => 0) := by
  have hd0 : 0 < d := by have := H.hd; omega
  set e : Fin N → ℂ := fun i => (eR i : ℂ) with he
  have hdot : ∑ i, eR i * eR i = 1 := by simpa [sq] using heR
  have hdotC : ∑ i, e i * e i = 1 := by simp only [he]; exact_mod_cast hdot
  have hrn : rn eR = 1 := by unfold rn; rw [heR]; simp
  have hUR : InUnionDomainR G (bgC1 d L N) ν (constBg hG e e) :=
    ⟨δ, hδ, hδc, inDomainR_const hG eR heR hδ hδ1⟩
  have h0 := bgFieldC_const H hG eR heR hδ hδ1 hδc 0 (by simp; positivity)
    (by simpa using bgC0_pos d L N hd0)
  have e1 : ((1 : ℂ) + 0) • (fun i => (eR i : ℂ)) = e := by simp [he]
  rw [e1] at h0
  have hreal := theorem72_real H hUR
  have hbf : bgField G a ν (constBg hG e e) = fun p => e p.2 := by rw [← hreal.1]; exact h0.1
  have hbm : bgMult G a ν (constBg hG e e) = fun _ => 0 := by
    rw [← hreal.2, h0.2]; funext _; simp
  have hc := bgFieldC_const H hG eR heR hδ hδ1 hδc t ht hα
  have hnz : ∀ y i, barField G (constBg hG e e).Ψ (fun p : G.Ω 1 × Fin N => e p.2) y i = e i :=
    barField_const hG _ e
  have hbc : ∀ y i, barField G (constBg hG ((1 + t) • e) e).Ψ (fun p : G.Ω 1 × Fin N => e p.2) y i =
      e i := barField_const hG _ e
  have hz0 : (0 : Fin N → ℂ) = fun _ => 0 := rfl
  refine ⟨one_pos, hε, constBg hG e e, constBg hG ((1 + t) • e) e, ⟨⟨?_, ?_⟩, hUR, ?_⟩, ⟨?_, ?_⟩,
    inUnionDomainC_const H hG eR heR hδ hδ1 hδc t ht, ?_⟩
  · intro x _ i; simp [constBg, he]
  · intro x _ i; simp [constBg, he]
  · rw [hbf, hbm]
    refine
      { grad := fun x hx μ => ?_
        lap := fun x hx => ?_
        mult := fun x => ?_
        close := fun x hx => ?_
        collarBond := fun z hz => absurd hz (by rw [hG.collar_eq]; exact Finset.notMem_empty z)
        mass := fun z => ?_
        hnorm := ?_ }
    · have h0' : (fun i => barField G (constBg hG e e).Ψ (fun p : G.Ω 1 × Fin N => e p.2)
          (x + Pi.single μ 1) i - barField G (constBg hG e e).Ψ (fun p : G.Ω 1 × Fin N => e p.2) x i)
          = fun _ => 0 := by funext i; simp only [hnz, sub_self]
      have h1 : (fun i => barField G (constBg hG e e).Ψ (fun p : G.Ω 1 × Fin N => e p.2)
          (x - Pi.single μ 1) i - barField G (constBg hG e e).Ψ (fun p : G.Ω 1 × Fin N => e p.2) x i)
          = fun _ => 0 := by funext i; simp only [hnz, sub_self]
      have hℓ : 0 < G.spacing x := spacing_pos G
      rw [h0', h1, show (fun _ : Fin N => (0 : ℂ)) = 0 from rfl, vn_zero]
      exact ⟨by positivity, by positivity⟩
    · have h0' : (fun i => ∑ μ : Fin d,
          (barField G (constBg hG e e).Ψ (fun p : G.Ω 1 × Fin N => e p.2) (x + Pi.single μ 1) i +
            barField G (constBg hG e e).Ψ (fun p : G.Ω 1 × Fin N => e p.2) (x - Pi.single μ 1) i -
            2 * barField G (constBg hG e e).Ψ (fun p : G.Ω 1 × Fin N => e p.2) x i)) = 0 := by
        funext i; simp only [hnz]; simp; ring
      have hℓ : 0 < G.spacing x := spacing_pos G
      rw [h0', vn_zero]; positivity
    · simp only [norm_zero, mul_zero]; positivity
    · have h0' : (fun i => (constBg hG e e).Ψ x i - blockAvg G (fun p : G.Ω 1 × Fin N => e p.2) x i)
          = 0 := by funext i; simp [constBg, blockAvg_const hG]
      rw [h0', vn_zero]; positivity
    · have h0' : (fun i => (fun p : G.Ω 1 × Fin N => e p.2) (z, i) - (eR i : ℂ)) = 0 := by
        funext i; simp [he]
      rw [h0', vn_zero]; simp
      positivity
    · simp [heR]; positivity
  · intro x _ i; simp [constBg, he]; ring
  · intro x _ i; simp [constBg, he]
  · rw [hbf, hbm, hc.1, hc.2]
    have hz : ∀ i, (0 : ℂ) = (0 : Fin N → ℂ) i := fun _ => rfl
    refine
      { grad := fun x hx μ => ?_
        lap := fun x hx => ?_
        mult := fun x => ?_
        val := fun x => ?_
        close := fun x hx => ?_
        collarBond := fun z hz => absurd hz (by rw [hG.collar_eq]; exact Finset.notMem_empty z)
        hAbs := fun x hx => ?_
        hDot := fun x => ?_ }
    · have hℓ : 0 < G.spacing x := spacing_pos G
      have hb : ∀ y i, barField G (constBg hG ((1 + t) • e) e).Ψ (fun p : G.Ω 1 × Fin N => e p.2) y i -
          barField G (constBg hG e e).Ψ (fun p : G.Ω 1 × Fin N => e p.2) y i = 0 := fun y i => by
        rw [hbc, hnz, sub_self]
      have h1 : (fun i => (barField G (constBg hG ((1 + t) • e) e).Ψ (fun p : G.Ω 1 × Fin N => e p.2)
          (x + Pi.single μ 1) i - barField G (constBg hG e e).Ψ (fun p : G.Ω 1 × Fin N => e p.2)
          (x + Pi.single μ 1) i) - (barField G (constBg hG ((1 + t) • e) e).Ψ
          (fun p : G.Ω 1 × Fin N => e p.2) x i - barField G (constBg hG e e).Ψ
          (fun p : G.Ω 1 × Fin N => e p.2) x i)) = 0 := by
        funext i; simp only [hb, sub_self]; rfl
      have h2 : (fun i => (barField G (constBg hG ((1 + t) • e) e).Ψ (fun p : G.Ω 1 × Fin N => e p.2)
          (x - Pi.single μ 1) i - barField G (constBg hG e e).Ψ (fun p : G.Ω 1 × Fin N => e p.2)
          (x - Pi.single μ 1) i) - (barField G (constBg hG ((1 + t) • e) e).Ψ
          (fun p : G.Ω 1 × Fin N => e p.2) x i - barField G (constBg hG e e).Ψ
          (fun p : G.Ω 1 × Fin N => e p.2) x i)) = 0 := by
        funext i; simp only [hb, sub_self]; rfl
      rw [h1, h2, vn_zero]
      exact ⟨by positivity, by positivity⟩
    · have hℓ : 0 < G.spacing x := spacing_pos G
      have h1 : (fun i => ∑ μ : Fin d, ((barField G (constBg hG ((1 + t) • e) e).Ψ
          (fun p : G.Ω 1 × Fin N => e p.2) (x + Pi.single μ 1) i - barField G (constBg hG e e).Ψ
          (fun p : G.Ω 1 × Fin N => e p.2) (x + Pi.single μ 1) i) +
          (barField G (constBg hG ((1 + t) • e) e).Ψ (fun p : G.Ω 1 × Fin N => e p.2)
          (x - Pi.single μ 1) i - barField G (constBg hG e e).Ψ (fun p : G.Ω 1 × Fin N => e p.2)
          (x - Pi.single μ 1) i) - 2 * (barField G (constBg hG ((1 + t) • e) e).Ψ
          (fun p : G.Ω 1 × Fin N => e p.2) x i - barField G (constBg hG e e).Ψ
          (fun p : G.Ω 1 × Fin N => e p.2) x i))) = 0 := by
        funext i; simp only [hbc, hnz, sub_self]; simp
      rw [h1, vn_zero]; positivity
    · rw [sub_zero, sq_spacing_mul_norm hG a t x]; nlinarith
    · have h0 : vn (fun _ : Fin N => (0 : ℂ)) = 0 := vn_zero
      have h1 : (fun i => (eR i : ℂ) - e i) = fun _ => (0 : ℂ) := by funext i; simp [he]
      show vn (fun i => (eR i : ℂ) - e i) < ε
      rw [h1, h0]; exact hε
    · have hs : ((fun p : G.Ω 1 × Fin N => e p.2) - (fun p : G.Ω 1 × Fin N => e p.2)) =
          fun p => (fun _ : Fin N => (0 : ℂ)) p.2 := by funext p; simp
      rw [hs]
      simp only [blockAvg_const hG (fun _ => (0 : ℂ)), sub_zero]
      have e' : (fun i => t * (eR i : ℂ)) = fun i => t * ((eR i : ℝ) : ℂ) := rfl
      have hrn' : rn eR = 1 := by unfold rn; rw [heR]; simp
      show vn (fun i => t * (eR i : ℂ)) < 1 ^ 2 * ε
      rw [e', vn_smul_complex, vn_ofReal, hrn']
      nlinarith
    · have h0 : vn ((fun (_ : Torus d (N₀ * L ^ k)) (_ : Fin N) => (0 : ℂ)) x) = 0 := vn_zero
      rw [h0, mul_zero]; positivity
    · simp only [mul_zero, Finset.sum_const_zero, norm_zero]; positivity

end Balaban.Fluctuation
