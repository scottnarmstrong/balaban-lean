/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LastIntegral
public import Balaban.Fluctuation.SizeModG1
public import Balaban.SmallField.Def6BridgeDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The inherited observable activities in Root-F's form
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.Multiscale Balaban.Background

section Explicit

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- On the torus `ℓ = N₁ L^{m₁} L^k` itself the site map `sfSite` is the identity. -/
theorem sfSite_eq_self {N₁ : ℕ} [NeZero N₁] (x : Localization.CTorus d L N₁ m₁ k) :
    sfSite (N₁ * L ^ m₁ * L ^ k) x = x := by
  funext μ
  simp only [sfSite]
  exact ZMod.natCast_zmod_val (x μ)

/-- On the torus `ℓ = N₁ L^{m₁} L^k` the set `sfPre` is the set `X` itself. -/
theorem sfPre_eq_coe {N₁ : ℕ} [NeZero N₁] (X : Finset (Torus d (N₁ * L ^ m₁ * L ^ k))) :
    sfPre (L := L) (m₁ := m₁) (k := k) N₁ (N₁ * L ^ m₁ * L ^ k) X =
      (X : Set (Localization.CTorus d L N₁ m₁ k)) := by
  ext x
  simp [sfPre, sfSite_eq_self]

open Classical in
/-- The inherited activities when `ℓ / (L^{m₁} L^k) = N₁` is the Def-6 torus index, with the
`ℓ`-dependent case split resolved. -/
theorem inhObs_eq_of_div (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    {ℓ N₁ : ℕ} [NeZero N₁] (e : ℓ / (L ^ m₁ * L ^ k) = N₁) (j : ℕ) (X : Finset (Torus d ℓ))
    (g : Torus d ℓ → Fin N → ℂ) :
    inhObs sf m₀ hv ℓ j X g =
      if 1 ≤ j ∧ j ≤ k ∧ Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
          (sfPre N₁ ℓ X) then
        ∑ x : Localization.CTorus d L N₁ m₁ k, if sfSite ℓ x ∈ X then
          ∑ i, g (sfSite ℓ x) i * (sf.Tm N₁).M j x (sfPre N₁ ℓ X)
            (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) (fun y => g (sfSite ℓ y)) i else 0
      else 0 := by
  subst e
  unfold inhObs
  simp only [NeZero.ne _, ↓reduceDIte]

open Classical in
/-- **The inherited activities on the torus `ℓ = N₁ L^{m₁} L^k`**, written on the sites of the
Def-6 torus `N₁` (the site map is the identity). -/
theorem inhObs_eq_explicit (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    {N₁ : ℕ} [NeZero N₁] (j : ℕ) (X : Finset (Torus d (N₁ * L ^ m₁ * L ^ k)))
    (g : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ) :
    inhObs sf m₀ hv (N₁ * L ^ m₁ * L ^ k) j X g =
      if 1 ≤ j ∧ j ≤ k ∧ Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
          (X : Set (Localization.CTorus d L N₁ m₁ k)) then
        ∑ x : Localization.CTorus d L N₁ m₁ k, if x ∈ X then
          ∑ i, g x i * (sf.Tm N₁).M j x (X : Set (Localization.CTorus d L N₁ m₁ k))
            (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) g i else 0
      else 0 := by
  have e : N₁ * L ^ m₁ * L ^ k / (L ^ m₁ * L ^ k) = N₁ := by
    rw [Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (mul_ne_zero
      (pow_ne_zero _ (NeZero.ne L)) (pow_ne_zero _ (NeZero.ne L))))]
  rw [inhObs_eq_of_div sf m₀ hv e]
  simp only [sfPre_eq_coe, sfSite_eq_self]

/-- Two sites in the same cell of side `a` of a box of side `L a` based at an aligned point lie in
that box. -/
theorem mem_box_of_sameCell {n : ℕ} [NeZero n] {a s : ℕ} (ha : a ∣ n)
    {b : Torus d n} (hb : Aligned a b) {x y : Torus d n} (hx : x ∈ Localization.box b (s * a))
    (hxy : ∀ μ, (x μ).val / a = (y μ).val / a) : y ∈ Localization.box b (s * a) := by
  have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha (Nat.pos_of_ne_zero (NeZero.ne n))
  obtain ⟨w, hw, rfl⟩ := hx
  have hc : cbase a y = cbase a (b + natT w) := by
    funext μ; simp only [cbase]; rw [hxy μ]
  obtain ⟨u, hu, hyu⟩ := mem_box_cbase (d := d) (n := n) ha0 y
  rw [hc, cbase_add ha hb] at hyu
  refine ⟨(fun μ => w μ - w μ % a) + u, fun μ => ?_, ?_⟩
  · have h1 : w μ / a < s := by rw [Nat.div_lt_iff_lt_mul ha0]; simpa [mul_comm] using hw μ
    have h2 : w μ - w μ % a = a * (w μ / a) := by
      have := Nat.div_add_mod (w μ) a
      omega
    have h3 : a * (w μ / a) + a ≤ s * a := by
      calc a * (w μ / a) + a = a * (w μ / a + 1) := by ring
        _ ≤ a * s := Nat.mul_le_mul_left _ h1
        _ = s * a := Nat.mul_comm _ _
    simp only [Pi.add_apply, h2]
    have := hu μ
    omega
  · rw [natT_add, ← add_assoc]
    exact hyu

/-- **A polymer of the class is a polymer of Root-F** (general `m₀`): a set of sites of the
torus `ℓ = N₁ L^{m₁} L^k` in `𝒟_j` (a connected union of `π'_j`-cubes of side `L M L^j`, aligned to
the cells of side `M L^j`, `M = L^{m₀+m₁}`) satisfies `IsPolymer d ℓ (M L^j)`. -/
theorem isPolymer_of_isPolyDom {N₁ m₀ j : ℕ} [NeZero N₁] (hN : L ^ m₀ ∣ N₁) (hj : j ≤ k)
    {X : Finset (Torus d (N₁ * L ^ m₁ * L ^ k))}
    (hX : Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
      (X : Set (Localization.CTorus d L N₁ m₁ k))) :
    IsPolymer d (N₁ * L ^ m₁ * L ^ k) (L ^ (m₀ + m₁) * L ^ j) X := by
  obtain ⟨hne, ⟨𝒦, hK1, hK2⟩, hconn⟩ := hX
  have hcs : L ^ (m₀ + m₁) * L ^ j = cellSide L m₀ m₁ j := by
    unfold cellSide; rw [← pow_add]; congr 1; omega
  have hdvd := cellSide_dvd (K := k) (m₁ := m₁) hN hj
  rw [hcs]
  refine ⟨Finset.coe_nonempty.1 hne, ?_, hconn⟩
  intro x hx y hxy
  obtain ⟨b, hb𝒦, hxb⟩ := hK2 x hx
  obtain ⟨hba, hbs⟩ := hK1 b hb𝒦
  exact hbs (mem_box_of_sameCell hdvd hba hxb hxy)

end Explicit

section Domain

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The constant unit field is in the data domain `Ψ̃^c`** with zero displacements, for every
generating set with the layers above `j` empty: `Ψ = h = v`, `|v| = 1`, `Ψ' = h' = 0`. -/
theorem inPsiTildeC_const {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {j : ℕ}
    (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k) {ν δ : ℝ} (hδ0 : 0 < δ) (v : Fin N → ℝ)
    (hv : ∑ i, v i ^ 2 = 1) :
    InPsiTildeC G ν δ δ (fun _ => v) v (fun _ _ => 0) (fun _ _ => 0) := by
  have hz : vn (0 : Fin N → ℂ) = 0 := by unfold vn; exact norm_eq_zero.2 rfl
  have hrn : rn v = 1 := by unfold rn; rw [hv]; simp
  have hvv : ∑ i, v i * v i = 1 := by simpa [sq] using hv
  have hδ2 : 0 < δ ^ 2 := by positivity
  refine
    { layerConst := isLayerConstant_of_jBlock hjk hΩ (fun _ _ _ => rfl)
      r1 := fun x x' _ => ?_
      r2 := fun x _ => ?_
      r3 := fun x _ => ?_
      r4 := ?_
      eps_pos := hδ0
      layerConst' := isLayerConstant_of_jBlock hjk hΩ (fun _ _ _ => rfl)
      hLayerConst' := isLayerConstant_of_jBlock hjk hΩ (fun _ _ _ => rfl)
      c1 := fun x x' _ => ?_
      c2a := fun x _ => ?_
      c2b := fun x _ => ?_
      c3a := fun x hx => ?_
      c3b := fun x hx => ?_ }
  · simp [rn]; exact hδ0
  · simp [hv]; exact hδ0
  · simp [hvv, hrn]; exact hδ2
  · simp [hv]; exact hδ2
  · simp only [sub_self]
    rw [hz]; exact hδ0
  · show vn (0 : Fin N → ℂ) < δ + δ
    rw [hz]; linarith
  · simp
    exact hδ0
  · show _ * vn (0 : Fin N → ℂ) < δ ^ 2 / δ
    rw [hz, mul_zero]
    positivity
  · simp
    exact hδ2

/-- **The constant configuration is in the analyticity domain** `Ξ^c_j(𝔹; 1, ε)`: for every
generating set with the layers above `j` empty, the constant unit field `Ψ = h = v` lies in
`XiDom` (zero complex displacements). -/
theorem xiDom_const {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν)
    {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {j : ℕ} (hΩ : ∀ i, j < i → G.Ω i = ∅)
    (hjk : j ≤ k) {ε : ℝ} (hε : 0 < ε) (v : Fin N → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    XiDom G a ν j ε (fun _ i => (v i : ℂ)) (fun _ i => (v i : ℂ)) := by
  have hd : 0 < d := by have := H.hd; omega
  have hK := bgK1_pos d L N
  have h0 := bgC0_pos (L := L) (N := N) d hd
  have h1 := bgC1_pos' (L := L) (N := N) hd
  have hq : 0 < ε / (2 * bgK1 d L N + 2) := by positivity
  set δ : ℝ := min (min (bgC0 d L N) (bgC1 d L N)) (ε / (2 * bgK1 d L N + 2)) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min h0 h1) hq
  have hδc0 : δ ≤ bgC0 d L N := (min_le_left _ _).trans (min_le_left _ _)
  have hδc1 : δ ≤ bgC1 d L N := (min_le_left _ _).trans (min_le_right _ _)
  have hδε : (2 * bgK1 d L N + 2) * δ ≤ ε := by
    have := min_le_right (min (bgC0 d L N) (bgC1 d L N)) (ε / (2 * bgK1 d L N + 2))
    calc _ ≤ (2 * bgK1 d L N + 2) * (ε / (2 * bgK1 d L N + 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ε := by field_simp
  have hP := inPsiTildeC_const (G := G) (ν := ν) hΩ hjk hδ0 v hv
  have hX := psiTildeC_subset_xiC (G := G) (a := a) H hδ0 le_rfl hδc0 hδc1
    (by
      have := H.massLe
      nlinarith [sq_nonneg δ]) hP (εb := ε) (by nlinarith)
  have hX' := xiC_level_irrel (n' := j) hv hX
  exact ⟨fun _ => v, v, fun _ _ => 0, fun _ _ => 0, fun x i => by simp, fun x i => by simp, hX'⟩

end Domain

section Bound

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- The Euclidean norm of a vector is at most the sum of the moduli of its entries. -/
theorem vn_le_sum_norm (v : Fin N → ℂ) : vn v ≤ ∑ i, ‖v i‖ := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => ‖v i‖)
    (fun _ _ => norm_nonneg _)
  rw [← vn_sq] at h
  exact abs_le_of_sq_le_sq' h (Finset.sum_nonneg fun _ _ => norm_nonneg _) |>.2

/-- A unit vector of `EuclideanSpace ℝ (Fin N)` has squared coordinates summing to `1`. -/
theorem sum_sq_eq_one_of_norm_eq_one (hv : EuclideanSpace ℝ (Fin N)) (h : ‖hv‖ = 1) :
    ∑ i, (hv i) ^ 2 = 1 := by
  have := EuclideanSpace.norm_eq hv
  rw [h] at this
  have h2 : ∑ i, ‖hv i‖ ^ 2 = 1 := by
    have h3 := congrArg (· ^ 2) this
    simp only [one_pow] at h3
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h3
    exact h3.symm
  simpa [Real.norm_eq_abs, sq_abs] using h2

/-- The constants `ε_j` of the class are positive. -/
theorem eps_pos_of_admissible {P : Def6.Consts} (hP : P.Admissible d L) (j : ℕ) :
    0 < P.eps d L j := by
  unfold Def6.Consts.eps epsSeq epsTail
  have h1 : 0 ≤ ∑' m : ℕ, if j ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0 :=
    tsum_nonneg fun m => by split_ifs <;> positivity
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have := hP.α₀_pos
  positivity

end Bound

section Arith

/-- **The decay conversion**: if `|X| ≤ c₁ a^d (1 + s)`, `κ c₁ ≤ κ_flow`-type tie
`c₁ (κ + 1) ≤ κ_f` and `c₉^{f} ≤ (c₉/2) e^{-κ_f}`, then
`c₉^{f} e^{-κ_f s} ≤ (c₉/2) e^{-κ |X| / a^d}`. -/
theorem decay_arith {κ κf c9 c9f s card ad c1 : ℝ} (hκ : 0 < κ) (had : 0 < ad) (hs : 0 ≤ s)
    (hc1 : 0 ≤ c1) (hc90 : 0 ≤ c9) (hcard : card ≤ c1 * ad * (1 + s)) (hκf : c1 * (κ + 1) ≤ κf)
    (hc9 : c9f ≤ c9 / 2 * Real.exp (-κf)) :
    c9f * Real.exp (-κf * s) ≤ c9 / 2 * Real.exp (-κ * card / ad) := by
  have h1 : κ * card / ad ≤ κf * (1 + s) := by
    rw [div_le_iff₀ had]
    have h2 : κ * card ≤ κ * (c1 * ad * (1 + s)) := mul_le_mul_of_nonneg_left hcard hκ.le
    have h3 : c1 * κ * (1 + s) ≤ κf * (1 + s) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
    calc κ * card ≤ κ * (c1 * ad * (1 + s)) := h2
      _ = (c1 * κ * (1 + s)) * ad := by ring
      _ ≤ (κf * (1 + s)) * ad := mul_le_mul_of_nonneg_right h3 had.le
  have h4 : Real.exp (-κf * (1 + s)) ≤ Real.exp (-κ * card / ad) := by
    apply Real.exp_le_exp.2
    have : -κ * card / ad = -(κ * card / ad) := by ring
    rw [this]; nlinarith
  calc c9f * Real.exp (-κf * s) ≤ (c9 / 2 * Real.exp (-κf)) * Real.exp (-κf * s) :=
        mul_le_mul_of_nonneg_right hc9 (Real.exp_pos _).le
    _ = c9 / 2 * Real.exp (-κf * (1 + s)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ c9 / 2 * Real.exp (-κ * card / ad) :=
        mul_le_mul_of_nonneg_left h4 (by linarith)

/-- The negative power of the scale: `(L^j)^{-e₁} ≤ L^{-j e₂}` for `e₂ ≤ e₁`, `L ≥ 1`. -/
theorem inv_pow_rpow_le {L : ℝ} (hL : 1 ≤ L) (j : ℕ) {e1 e2 : ℝ} (h : e2 ≤ e1) :
    ((L ^ j)⁻¹) ^ e1 ≤ L ^ (-((j : ℝ) * e2)) := by
  have hL0 : 0 ≤ L := by linarith
  rw [Real.inv_rpow (pow_nonneg hL0 j), ← Real.rpow_natCast, ← Real.rpow_mul hL0,
    ← Real.rpow_neg hL0 ((j : ℝ) * e1)]
  exact Real.rpow_le_rpow_of_exponent_le hL (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])

/-- The constant of (G1) is at most `3^{d+1} L^{2d+1}`. -/
theorem c1_le_pow (d L : ℕ) (hL : 1 ≤ L) :
    Fluctuation.c1 d L ≤ (3 : ℝ) ^ (d + 1) * (L : ℝ) ^ (2 * d + 1) := by
  unfold Fluctuation.c1
  have h1 : ((3 * (2 * L - 1) : ℕ) : ℝ) ≤ 3 * (L : ℝ) ^ 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    have : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [this]
    push_cast
    nlinarith [sq_nonneg (m : ℝ)]
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  calc ((3 * (2 * L - 1) : ℕ) : ℝ) ^ d ≤ (3 * (L : ℝ) ^ 2) ^ d :=
        pow_le_pow_left₀ (by positivity) h1 d
    _ = 3 ^ d * (L : ℝ) ^ (2 * d) := by rw [mul_pow, ← pow_mul]
    _ ≤ 3 ^ (d + 1) * (L : ℝ) ^ (2 * d + 1) := by
        rw [pow_succ 3 d, pow_succ (L : ℝ) (2 * d)]
        have : (0 : ℝ) ≤ 3 ^ d * (L : ℝ) ^ (2 * d) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hL1 this]

end Arith

section Core

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The constant configuration is in the term domain**: the pair `(h, h)` of constant unit fields
lies in the domain `sfDom` of the terms of a polymer `X ∈ 𝒟_j` (the domain is the birth-mass
domain `birthXiDom`; the standing hypotheses `BgHyp` of the background theory at the birth mass of
the level `j`). -/
theorem inhObs_constDom {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    (hsf : SFFlat2 P6 k0 sf)
    (hBg : ∀ j, 1 ≤ j → j ≤ k →
      BgHyp d L k ϱ (aIdeal L k (sf.a k)) (physMass L j (sf.ν j)))
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P6.m₀ ∣ N₁) (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {X : Set (Localization.CTorus d L N₁ m₁ k)}
    (hX : Def6.IsPolyDom P6.m₀ j X) :
    (sfDom P6 k0 sf N₁).dom j ((sf.Tm N₁).gs j X) (Def6.constFld (hC hv))
      (Def6.constFld (hC hv)) := by
  obtain ⟨ρsf, hρ⟩ := hsf.torus
  have hΩ := ((hρ N₁ hN).terms.gs_spec j hj1 hjk X hX).2
  have hε := eps_pos_of_admissible hsf.admissible j
  exact xiDom_const (hBg j hj1 hjk) hΩ hjk hε (fun i => hv i)
    (sum_sq_eq_one_of_norm_eq_one hv hunit)

/-- **The bound (H.7) at the constant configuration**: for a polymer `X ∈ 𝒟_j`, `x ∈ X` and a
source `g` with `‖g‖₁ < 1`, the term `ℳ^{(j)}(x, X; h, h, g)` of a member of (D2♭) is bounded by
`c₉^{flow} L^{-j((d-2)/2+γ-α₁)} e^{-κ_flow d_j(X)}`. -/
theorem inhObs_term_bound {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    (hsf : SFFlat2 P6 k0 sf)
    (hBg : ∀ j, 1 ≤ j → j ≤ k →
      BgHyp d L k ϱ (aIdeal L k (sf.a k)) (physMass L j (sf.ν j)))
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P6.m₀ ∣ N₁) (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {X : Set (Localization.CTorus d L N₁ m₁ k)}
    (hX : Def6.IsPolyDom P6.m₀ j X) {x : Localization.CTorus d L N₁ m₁ k} (hx : x ∈ X)
    {g : Fld d L N₁ m₁ k N} (hg : Def6.l1 g < 1) :
    vn ((sf.Tm N₁).M j x X (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) g) <
      P6.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P6.γ - P6.α₁) *
        Real.exp (-P6.κ * sizeJ P6.m₀ j X) := by
  obtain ⟨ρsf, hρ⟩ := hsf.torus
  exact (hρ N₁ hN).terms.boundM j hj1 hjk x X hX hx _ _ g
    (inhObs_constDom hsf hBg hN hv hunit hj1 hjk hX) hg

/-- The `ℓ¹` norm `Def6.l1` of a source is at most the sum of the moduli of its entries. -/
theorem l1_le_sum {N₁ : ℕ} [NeZero N₁] (g : Fld d L N₁ m₁ k N) :
    Def6.l1 g ≤ ∑ y, ∑ i, ‖g y i‖ :=
  Finset.sum_le_sum fun y _ => vn_le_sum_norm (g y)

/-- **The inherited activities are bounded** on the unit `ℓ¹` ball by the bound (H.7) of the
polymer. -/
theorem inhObs_norm_le {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    (hsf : SFFlat2 P6 k0 sf)
    (hBg : ∀ j, 1 ≤ j → j ≤ k →
      BgHyp d L k ϱ (aIdeal L k (sf.a k)) (physMass L j (sf.ν j)))
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P6.m₀ ∣ N₁) (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {X : Finset (Torus d (N₁ * L ^ m₁ * L ^ k))}
    (hX : Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P6.m₀ j
      (X : Set (Localization.CTorus d L N₁ m₁ k)))
    (g : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ) (hg : ∑ y, ∑ i, ‖g y i‖ < 1) :
    ‖inhObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) j X g‖ ≤
      P6.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P6.γ - P6.α₁) *
        Real.exp (-P6.κ * sizeJ P6.m₀ j (X : Set (Localization.CTorus d L N₁ m₁ k))) := by
  classical
  set B := P6.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P6.γ - P6.α₁) *
    Real.exp (-P6.κ * sizeJ P6.m₀ j (X : Set (Localization.CTorus d L N₁ m₁ k))) with hB
  have hl1 : Def6.l1 g < 1 := (l1_le_sum g).trans_lt hg
  have hterm : ∀ x ∈ X, vn ((sf.Tm N₁).M j x (X : Set (Localization.CTorus d L N₁ m₁ k))
      (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) g) < B := fun x hx =>
    inhObs_term_bound hsf hBg hN hv hunit hj1 hjk hX (Finset.mem_coe.2 hx) hl1
  have hB0 : 0 ≤ B := by
    obtain ⟨x, hx⟩ := hX.1
    exact (vn_nonneg _).trans (hterm x (Finset.mem_coe.1 hx)).le
  rw [inhObs_eq_explicit]
  simp only [hj1, hjk, hX, and_self, ↓reduceIte]
  calc ‖∑ x : Localization.CTorus d L N₁ m₁ k, if x ∈ X then
        ∑ i, g x i * (sf.Tm N₁).M j x (X : Set (Localization.CTorus d L N₁ m₁ k))
          (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) g i else 0‖
      ≤ ∑ x : Localization.CTorus d L N₁ m₁ k, (∑ i, ‖g x i‖) * B := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        by_cases hx : x ∈ X
        · simp only [hx, ↓reduceIte]
          refine (norm_sum_le _ _).trans ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            ((norm_le_vn _ i).trans (hterm x hx).le) (norm_nonneg _)
        · simp only [hx, ↓reduceIte, norm_zero]
          exact mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) hB0
    _ = (∑ x : Localization.CTorus d L N₁ m₁ k, ∑ i, ‖g x i‖) * B := by rw [Finset.sum_mul]
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right hg.le hB0
    _ = B := one_mul B

/-- The `i`-th coordinate is an analytic function on `ℂ^N`. -/
theorem analyticAt_pi_coord (i : Fin N) (w : Fin N → ℂ) :
    AnalyticAt ℂ (fun v : Fin N → ℂ => v i) w :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).analyticAt w

/-- The `i`-th coordinate of a source at a site is an analytic function of the source. -/
theorem analyticOnNhd_coord {ℓ : ℕ} [NeZero ℓ] (x : Torus d ℓ) (i : Fin N) (s : Set (Torus d ℓ → Fin N → ℂ)) :
    AnalyticOnNhd ℂ (fun g : Torus d ℓ → Fin N → ℂ => g x i) s := fun g _ =>
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Torus d ℓ => Fin N → ℂ) x)).analyticAt g

/-- **The inherited activities are analytic** on the unit `ℓ¹` ball. -/
theorem inhObs_analytic {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    (hsf : SFFlat2 P6 k0 sf)
    (hBg : ∀ j, 1 ≤ j → j ≤ k →
      BgHyp d L k ϱ (aIdeal L k (sf.a k)) (physMass L j (sf.ν j)))
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P6.m₀ ∣ N₁) (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1) (j : ℕ)
    (X : Finset (Torus d (N₁ * L ^ m₁ * L ^ k))) :
    AnalyticOnNhd ℂ (inhObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) j X)
      {g | ∑ y, ∑ i, ‖g y i‖ < 1} := by
  classical
  have e : inhObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) j X = fun g =>
      if 1 ≤ j ∧ j ≤ k ∧ Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P6.m₀ j
          (X : Set (Localization.CTorus d L N₁ m₁ k)) then
        ∑ x : Localization.CTorus d L N₁ m₁ k, if x ∈ X then
          ∑ i, g x i * (sf.Tm N₁).M j x (X : Set (Localization.CTorus d L N₁ m₁ k))
            (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) g i else 0
      else 0 := funext fun g => inhObs_eq_explicit sf P6.m₀ hv j X g
  rw [e]
  by_cases hc : 1 ≤ j ∧ j ≤ k ∧ Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P6.m₀ j
      (X : Set (Localization.CTorus d L N₁ m₁ k))
  · obtain ⟨hj1, hjk, hpoly⟩ := hc
    simp only [hj1, hjk, hpoly, and_self, ↓reduceIte]
    have key : ∀ x ∈ (Finset.univ : Finset (Localization.CTorus d L N₁ m₁ k)),
        AnalyticOnNhd ℂ (fun g : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ =>
          if x ∈ X then ∑ i, g x i * (sf.Tm N₁).M j x (X : Set (Localization.CTorus d L N₁ m₁ k))
            (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) g i else 0)
          {g | ∑ y, ∑ i, ‖g y i‖ < 1} := by
      intro x _
      by_cases hx : x ∈ X
      · simp only [hx, ↓reduceIte]
        have key2 : ∀ i ∈ (Finset.univ : Finset (Fin N)),
            AnalyticOnNhd ℂ (fun g : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ =>
              g x i * (sf.Tm N₁).M j x (X : Set (Localization.CTorus d L N₁ m₁ k))
                (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) g i)
              {g | ∑ y, ∑ i, ‖g y i‖ < 1} := by
          intro i _
          refine (analyticOnNhd_coord x i _).mul ?_
          obtain ⟨ρsf, hρ⟩ := hsf.torus
          have hM := (hρ N₁ hN).terms.analyticM j hj1 hjk x _ hpoly hx
          have hΦ : AnalyticOnNhd ℂ (fun g : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ =>
              ((Def6.constFld (hC hv) : Fld d L N₁ m₁ k N),
                (Def6.constFld (hC hv) : Fld d L N₁ m₁ k N), g))
              {g | ∑ y, ∑ i, ‖g y i‖ < 1} :=
            analyticOnNhd_const.prod (analyticOnNhd_const.prod analyticOnNhd_id)
          have hcomp := hM.comp hΦ (fun g hg => ⟨inhObs_constDom hsf hBg hN hv hunit hj1 hjk hpoly,
            (l1_le_sum g).trans_lt hg⟩)
          intro g hg
          exact (analyticAt_pi_coord i _).comp (hcomp g hg)
        exact Finset.analyticOnNhd_fun_sum _ key2
      · simp only [hx, ↓reduceIte]
        exact analyticOnNhd_const
    exact Finset.analyticOnNhd_fun_sum _ key
  · simp only [hc, ↓reduceIte]
    exact analyticOnNhd_const

/-- **Support** of the inherited activities: they vanish off the scale-`j` polymers of Root-F. -/
theorem actSupportAt_inhObs {P6 : Def6.Consts} {sf : SFData d L m₁ k N ϱ} {N₁ M : ℕ}
    [NeZero N₁] (hN : L ^ P6.m₀ ∣ N₁) (hM : M = L ^ (P6.m₀ + m₁))
    (hv : EuclideanSpace ℝ (Fin N)) :
    ActSupportAt d N L M k (N₁ * L ^ m₁ * L ^ k) (inhObs sf P6.m₀ hv) := by
  classical
  intro j X hnot g
  rw [inhObs_zero, inhObs_eq_explicit]
  by_cases hc : 1 ≤ j ∧ j ≤ k ∧ Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P6.m₀ j
      (X : Set (Localization.CTorus d L N₁ m₁ k))
  · exact absurd ⟨Finset.mem_Icc.2 ⟨hc.1, hc.2.1⟩, by
      rw [hM]; exact isPolymer_of_isPolyDom hN hc.2.1 hc.2.2⟩ hnot
  · simp only [hc, ↓reduceIte]

omit [NeZero L] in
/-- A set of `𝒟_j` in the sense of the class is a set of `𝒟_j` in the sense of the size estimate
(G1). -/
theorem isDj_of_isPolyDom {N₁ m₀ j : ℕ} [NeZero N₁]
    {X : Set (Localization.CTorus d L N₁ m₁ k)} (hX : Def6.IsPolyDom m₀ j X) :
    Fluctuation.IsDj m₀ j X := by
  obtain ⟨hne, ⟨𝒦, hK1, hK2⟩, hconn⟩ := hX
  refine ⟨hne, fun z hz => ?_, hconn⟩
  obtain ⟨b, hb, hzb⟩ := hK2 z hz
  exact ⟨b, (hK1 b hb).1, hzb, (hK1 b hb).2⟩

/-- **The bound clause of Root-F's form for the inherited activities** (the conversion of
`c₉^{flow} L^{-j((d-2)/2+γ-α₁)} e^{-κ_flow d_j(X)}` to `(c₉/2) L^{-j((d-2)/2+δ)} e^{-κ|X|/(M L^j)^d}`
through `|X| ≤ c₁ (M L^j)^d (1 + d_j(X))` (`G1_card`) and the ties `δ ≤ γ - α₁`,
`κ_flow ≥ 3^{d+1} L^{2d+1} (κ+1)`, `c₉^{flow} ≤ (c₉/2) e^{-κ_flow}`). -/
theorem actBoundAt_inhObs {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    (hsf : SFFlat2 P6 k0 sf)
    (hBg : ∀ j, 1 ≤ j → j ≤ k →
      BgHyp d L k ϱ (aIdeal L k (sf.a k)) (physMass L j (sf.ν j)))
    {N₁ M : ℕ} [NeZero N₁] (hN : L ^ P6.m₀ ∣ N₁) (hM : M = L ^ (P6.m₀ + m₁))
    (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1) {κ c₉ δ : ℝ} (hκ : 0 < κ) (hc₉ : 0 ≤ c₉)
    (hc₉f : 0 ≤ P6.c₉) (hδ : δ ≤ P6.γ - P6.α₁) (hL : 1 ≤ L)
    (hκf : (3 : ℝ) ^ (d + 1) * (L : ℝ) ^ (2 * d + 1) * (κ + 1) ≤ P6.κ)
    (hc₉t : P6.c₉ ≤ c₉ / 2 * Real.exp (-P6.κ)) :
    ActBoundAt d N L M κ c₉ δ k (N₁ * L ^ m₁ * L ^ k) (inhObs sf P6.m₀ hv) := by
  classical
  intro j hj X g hg
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
  rw [inhObs_zero, sub_zero]
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hR : 0 ≤ c₉ / 2 * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
      Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d) := by
    have : 0 < (L : ℝ) := by linarith
    positivity
  by_cases hpoly : Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P6.m₀ j
      (X : Set (Localization.CTorus d L N₁ m₁ k))
  · refine (inhObs_norm_le hsf hBg hN hv hunit hj1 hjk hpoly g hg).trans ?_
    have hG := Fluctuation.G1_card (m₀ := P6.m₀) hN hjk (isDj_of_isPolyDom hpoly)
    have hs : 0 ≤ sizeJ P6.m₀ j (X : Set (Localization.CTorus d L N₁ m₁ k)) :=
      treeLenCovOne_nonneg P6.m₀ j _
    have hcs : ((cellSide L P6.m₀ m₁ j : ℕ) : ℝ) = (M : ℝ) * (L : ℝ) ^ j := by
      unfold cellSide
      rw [hM]
      push_cast
      rw [← pow_add]
      congr 1
      omega
    have had : 0 < ((M : ℝ) * (L : ℝ) ^ j) ^ d := by
      rw [← hcs]; have := cellSide_pos (L := L) P6.m₀ m₁ j; positivity
    have hcard : ((X : Set (Localization.CTorus d L N₁ m₁ k)).ncard : ℝ) = X.card := by
      rw [Set.ncard_coe_finset]
    have hc1 : 0 ≤ Fluctuation.c1 d L := by unfold Fluctuation.c1; positivity
    have hdec := decay_arith (κ := κ) (κf := P6.κ) (c9 := c₉) (c9f := P6.c₉)
      (s := sizeJ P6.m₀ j (X : Set (Localization.CTorus d L N₁ m₁ k)))
      (card := (X.card : ℝ)) (ad := ((M : ℝ) * (L : ℝ) ^ j) ^ d) (c1 := Fluctuation.c1 d L)
      hκ had hs hc1 hc₉ (by rw [← hcard, ← hcs]; exact hG)
      (((mul_le_mul_of_nonneg_right (c1_le_pow d L hL) (by linarith)).trans hκf))
      hc₉t
    have hrp := inv_pow_rpow_le hL1 j (e1 := ((d : ℝ) - 2) / 2 + P6.γ - P6.α₁)
      (e2 := ((d : ℝ) - 2) / 2 + δ) (by linarith)
    calc P6.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P6.γ - P6.α₁) *
          Real.exp (-P6.κ * sizeJ P6.m₀ j (X : Set (Localization.CTorus d L N₁ m₁ k)))
        = ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P6.γ - P6.α₁) *
          (P6.c₉ * Real.exp (-P6.κ * sizeJ P6.m₀ j (X : Set (Localization.CTorus d L N₁ m₁ k)))) := by
          ring
      _ ≤ (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
          (c₉ / 2 * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)) :=
          mul_le_mul hrp hdec (by positivity) (by positivity)
      _ = _ := by ring
  · rw [inhObs_eq_explicit]
    simp only [hpoly, and_false, ↓reduceIte, norm_zero]
    exact hR

end Core


section Mass

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

omit [NeZero L] in
/-- **The standing hypotheses `BgHyp` for the ideal weights `a_n` of scale `k`**, at any separation
`ϱ' ≥ R₀(d, L)` and any mass `m ≥ 0` with `m L^{2k} ≤ 1`: the weights are those of the ideal flow
(`aIdeal_mem`) for a coefficient `a_k` in the window `[9/10 (1 - L⁻²)⁻¹, 3/2)` of (H.6). -/
theorem bgHyp_of_ideal {ak ϱ' m : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ')
    (h1 : 9 / 10 * (1 - ((L : ℝ) ^ 2)⁻¹)⁻¹ ≤ ak) (h2 : ak < 3 / 2) (hm0 : 0 ≤ m)
    (hcap : m * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    BgHyp d L k ϱ' (aIdeal L k ak) m where
  hd := hd
  hL := hL
  hϱ := hϱ
  weights := fun _ hj hjk => aIdeal_mem hL h1 h2 hj hjk
  mass := hm0
  massLe := hcap

/-- **The standing hypotheses of the background theory at the birth mass of the level `j ≤ k`**
for a member of (D2♭): the weights `a_n` are those of the ideal flow (`aIdeal_mem`), the
mass `ν_j L^{-2j}` is nonnegative, and `ν_j L^{-2j} L^{2k} ≤ 1` (`hcap`). -/
theorem bgHyp_birth {P6 : Def6.Consts} {k0 : ℕ} {sf : SFData d L m₁ k N ϱ}
    (hsf : SFFlat2 P6 k0 sf) (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ) {j : ℕ}
    (hν0 : 0 ≤ sf.ν j) (hcap : physMass L j (sf.ν j) * ((L : ℝ) ^ k) ^ 2 ≤ 1) :
    BgHyp d L k ϱ (aIdeal L k (sf.a k)) (physMass L j (sf.ν j)) :=
  bgHyp_of_ideal hd hL hϱ hsf.coeff.a_ge hsf.coeff.a_lt (by unfold physMass; positivity) hcap

omit [NeZero L] in
/-- The mass cap expression: `(ν L^{2j} δ_j) L^{-2j} L^{2k} = ν L^{2k} δ_j`. -/
theorem physMass_cap_eq {j : ℕ} (hL : 3 ≤ L) (ν δj : ℝ) :
    physMass L j (ν * (L : ℝ) ^ (2 * j) * δj) * ((L : ℝ) ^ k) ^ 2 =
      ν * ((L : ℝ) ^ k) ^ 2 * δj := by
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  unfold physMass
  rw [pow_mul]
  field_simp
  ring

omit [NeZero L] in
/-- **The mass cap at the stopping scale**: if `ν_j = ν L^{2j} δ_j` and `ν_k = ν L^{2k} δ_k` with
`|log δ_j|, |log δ_k| ≤ 1/20` and `ν_k ≤ 9/10`, then `ν_j L^{-2j} L^{2k} ≤ 1`
(`δ_j ≤ e^{1/10} δ_k ≤ (10/9) δ_k`). -/
theorem physMass_cap_of_top {j : ℕ} (hL : 3 ≤ L) {ν δj δk : ℝ} (hν : 0 < ν) (hδj0 : 0 < δj)
    (hδj : |Real.log δj| ≤ 1 / 20) (hδk0 : 0 < δk) (hδk : |Real.log δk| ≤ 1 / 20)
    (hνk : ν * (L : ℝ) ^ (2 * k) * δk ≤ 9 / 10) :
    physMass L j (ν * (L : ℝ) ^ (2 * j) * δj) * ((L : ℝ) ^ k) ^ 2 ≤ 1 := by
  rw [physMass_cap_eq hL]
  have hexp : Real.exp (1 / 10) ≤ 10 / 9 := by
    have := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 10) (by norm_num) (by norm_num)
    linarith
  have hδ : δj ≤ 10 / 9 * δk := by
    have h1 : Real.log δj ≤ Real.log δk + 1 / 10 := by
      have := (abs_le.1 hδj).2
      have := (abs_le.1 hδk).1
      linarith
    calc δj = Real.exp (Real.log δj) := (Real.exp_log hδj0).symm
      _ ≤ Real.exp (Real.log δk + 1 / 10) := Real.exp_le_exp.2 h1
      _ = δk * Real.exp (1 / 10) := by rw [Real.exp_add, Real.exp_log hδk0]
      _ ≤ δk * (10 / 9) := mul_le_mul_of_nonneg_left hexp hδk0.le
      _ = 10 / 9 * δk := by ring
  have hx : 0 ≤ ν * ((L : ℝ) ^ k) ^ 2 := by positivity
  have h2 : ν * (L : ℝ) ^ (2 * k) = ν * ((L : ℝ) ^ k) ^ 2 := by rw [pow_mul']
  rw [h2] at hνk
  calc ν * ((L : ℝ) ^ k) ^ 2 * δj ≤ ν * ((L : ℝ) ^ k) ^ 2 * (10 / 9 * δk) :=
        mul_le_mul_of_nonneg_left hδ hx
    _ = 10 / 9 * (ν * ((L : ℝ) ^ k) ^ 2 * δk) := by ring
    _ ≤ 1 := by linarith

omit [NeZero L] in
/-- **The mass cap below the horizon**: if `ν_j = ν L^{2j} δ_j` with `|log δ_j| ≤ 1/20`,
`ν L^{2k+2} < 1` and `L ≥ 3`, then `ν_j L^{-2j} L^{2k} ≤ 1`. -/
theorem physMass_cap_of_lt {j : ℕ} (hL : 3 ≤ L) {ν δj : ℝ} (hν : 0 < ν) (hδ0 : 0 < δj)
    (hδ : |Real.log δj| ≤ 1 / 20) (hlt : ν * (L : ℝ) ^ (2 * k + 2) < 1) :
    physMass L j (ν * (L : ℝ) ^ (2 * j) * δj) * ((L : ℝ) ^ k) ^ 2 ≤ 1 := by
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hδ3 : δj ≤ 3 := by
    have h1 : Real.log δj ≤ 1 / 20 := (abs_le.1 hδ).2
    calc δj = Real.exp (Real.log δj) := (Real.exp_log hδ0).symm
      _ ≤ Real.exp (1 / 20) := Real.exp_le_exp.2 h1
      _ ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
      _ ≤ 3 := (Real.exp_one_lt_d9.le.trans (by norm_num))
  rw [physMass_cap_eq hL]
  have ha : ν * ((L : ℝ) ^ k) ^ 2 * (L : ℝ) ^ 2 < 1 := by
    calc ν * ((L : ℝ) ^ k) ^ 2 * (L : ℝ) ^ 2 = ν * (L : ℝ) ^ (2 * k + 2) := by ring
      _ < 1 := hlt
  have hL9 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hpos : 0 < ν * ((L : ℝ) ^ k) ^ 2 := by positivity
  nlinarith

omit [NeZero L] in
/-- **The mass cap at every inherited level** `j ≤ k` of a member of `ℛ♭_k` at the horizon `k̂_f`:
with (I.2), `ν_j = ν L^{2j} δ_j`, `|log δ_j| ≤ 1/20`, and `ν_k ≤ 9/10` at the stopping scale,
`ν_j L^{-2j} L^{2k} ≤ 1`: below the horizon by `physMass_cap_of_lt`, at the horizon by
`physMass_cap_of_top`. -/
theorem birth_cap_of_run {L k kf : ℕ} (hL : 3 ≤ L) {ν : ℝ} (hν : 0 < ν) {νs : ℕ → ℝ}
    (hnu : ∀ j, j ≤ k → ∃ δ : ℝ, 0 < δ ∧ |Real.log δ| ≤ 1 / 20 ∧
      νs j = ν * (L : ℝ) ^ (2 * j) * δ)
    (hkf : IsHorizon L ν kf) (hkkf : k ≤ kf) (h9 : νs k ≤ 9 / 10) (j : ℕ) (hj : j ≤ k) :
    physMass L j (νs j) * ((L : ℝ) ^ k) ^ 2 ≤ 1 := by
  obtain ⟨δj, hδj0, hδj, hνj⟩ := hnu j hj
  rcases hkkf.lt_or_eq with hlt | heq
  · rw [hνj]
    exact physMass_cap_of_lt hL hν hδj0 hδj (hkf.2 k hlt)
  · subst heq
    obtain ⟨δk, hδk0, hδk, hνk'⟩ := hnu k le_rfl
    rw [hνj]
    refine physMass_cap_of_top hL hν hδj0 hδj hδk0 hδk ?_
    rw [← hνk']
    exact h9

end Mass

section Final

variable (d N : ℕ) (δ : ℝ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **`InheritedBoundInput` from `PrefixInput`.** For a member of `ℛ♭_k` at the stopping scale, the
inherited observable activities vanish off the scale-`j` polymers of Root-F, are analytic on the
unit `ℓ¹` ball, and obey Root-F's bound, on every admissible torus: the constant configuration lies
in the term domain (`xiDom_const`, `inhObs_constDom`), the clauses (H.7) of the class give the bound
(`inhObs_term_bound`), and the ties of `PrefixInput` convert it (`actBoundAt_inhObs`, through
`G1_card`). The dimension `d ≥ 3` and `ϱ ≥ R₀(d, L)` are clauses of `PrefixInput`. The standing mass
hypothesis `ν_j L^{-2j} L^{2k} ≤ 1` of the background theory at every inherited level `j ≤ k` holds
below the horizon by (I.2) (`physMass_cap_of_lt`) and at the horizon `k = k̂_f` by (I.2) and the
mass bound `ν_k ≤ 9/10` of the class (`physMass_cap_of_top`). -/
theorem inheritedBoundInput_of_prefix (hPre : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ) :
    InheritedBoundInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ hκ c₉ hc₉
  refine ⟨0, fun β _ ν hν _ h hh kf hkf _ _ k hk1 hkkf ρ νk hM6 hkK R geo cs P F St vc hF _
    ℓ _ hℓ => ?_⟩
  obtain ⟨hL3, -, -, -, -, -, -, hMpow, hadm, hc9pos, -, -, hδγ, hκf, hc9f, hTy, hϱ, -⟩ :=
    hPre κ hκ c₉ hc₉
  have hd : 3 ≤ d := hTy.1.three_le_d
  have hsf := hF.sfFlat
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hνkF, hrun, -, hν9⟩ := id hF
  obtain ⟨-, -, -, hν0', -, -, -, -, -, hnu⟩ := hrun
  have hBg : ∀ j, 1 ≤ j → j ≤ k →
      BgHyp d (T κ c₉).L k (ϱ κ c₉) (aIdeal (T κ c₉).L k (F.sf.a k)) (physMass (T κ c₉).L j (F.sf.ν j)) := by
    intro j hj1 hjk
    obtain ⟨δj, hδj0, hδj, hνj⟩ := hnu j hjk
    have hνj0 : 0 ≤ F.sf.ν j := by rw [hνj]; positivity
    exact bgHyp_birth hsf hd hL3 hϱ hνj0
      (birth_cap_of_run hL3 hν0' hnu hkf hkkf (by rw [hνkF]; exact hν9) j hjk)
  obtain ⟨c', hc'⟩ := hℓ
  obtain ⟨N₁, hℓN, hN₁⟩ : ∃ N₁ : ℕ, ℓ = N₁ * (T κ c₉).L ^ (C7 κ c₉).m₁ * (T κ c₉).L ^ k ∧
      (T κ c₉).L ^ (P6 κ c₉).m₀ ∣ N₁ := by
    refine ⟨(T κ c₉).L ^ ((P6 κ c₉).m₀ + kf + 1 - k) * c', ?_, ?_⟩
    · have e : (T κ c₉).L ^ ((P6 κ c₉).m₀ + (C7 κ c₉).m₁) * (T κ c₉).L ^ (kf + 1) =
          (T κ c₉).L ^ ((P6 κ c₉).m₀ + kf + 1 - k) * (T κ c₉).L ^ k * (T κ c₉).L ^ (C7 κ c₉).m₁ := by
        rw [← pow_add, ← pow_add, ← pow_add]
        congr 1
        omega
      rw [hc', hMpow, e]
      ring
    · exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
  subst hℓN
  have hne : N₁ * (T κ c₉).L ^ (C7 κ c₉).m₁ * (T κ c₉).L ^ k ≠ 0 := NeZero.ne _
  have : NeZero N₁ := ⟨fun h0 => hne (by rw [h0]; simp)⟩
  have hL1 : 1 ≤ (T κ c₉).L := le_trans (by norm_num) hL3
  exact ⟨actSupportAt_inhObs hN₁ hMpow h, fun j X => inhObs_analytic hsf hBg hN₁ h hh j X,
    actBoundAt_inhObs hsf hBg hN₁ hMpow h hh hκ hc₉.le hc9pos.le hδγ hL1 hκf hc9f⟩

end Final

end Balaban.RootFSpine
