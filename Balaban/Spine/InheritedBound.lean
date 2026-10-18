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
    {N₁ : ℕ} [NeZero N₁] (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {X : Set (Localization.CTorus d L N₁ m₁ k)}
    (hX : Def6.IsPolyDom P6.m₀ j X) :
    (sfDom P6 k0 sf N₁).dom j ((sf.Tm N₁).gs j X) (Def6.constFld (hC hv))
      (Def6.constFld (hC hv)) := by
  obtain ⟨ρsf, hρ⟩ := hsf.torus
  have hΩ := ((hρ N₁).terms.gs_spec j hj1 hjk X hX).2
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
    {N₁ : ℕ} [NeZero N₁] (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {X : Set (Localization.CTorus d L N₁ m₁ k)}
    (hX : Def6.IsPolyDom P6.m₀ j X) {x : Localization.CTorus d L N₁ m₁ k} (hx : x ∈ X)
    {g : Fld d L N₁ m₁ k N} (hg : Def6.l1 g < 1) :
    vn ((sf.Tm N₁).M j x X (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) g) <
      P6.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P6.γ - P6.α₁) *
        Real.exp (-P6.κ * sizeJ P6.m₀ j X) := by
  obtain ⟨ρsf, hρ⟩ := hsf.torus
  exact (hρ N₁).terms.boundM j hj1 hjk x X hX hx _ _ g
    (inhObs_constDom hsf hBg hv hunit hj1 hjk hX) hg

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
    {N₁ : ℕ} [NeZero N₁] (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
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
    inhObs_term_bound hsf hBg hv hunit hj1 hjk hX (Finset.mem_coe.2 hx) hl1
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
    {N₁ : ℕ} [NeZero N₁] (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1) (j : ℕ)
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
          have hM := (hρ N₁).terms.analyticM j hj1 hjk x _ hpoly hx
          have hΦ : AnalyticOnNhd ℂ (fun g : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ =>
              ((Def6.constFld (hC hv) : Fld d L N₁ m₁ k N),
                (Def6.constFld (hC hv) : Fld d L N₁ m₁ k N), g))
              {g | ∑ y, ∑ i, ‖g y i‖ < 1} :=
            analyticOnNhd_const.prod (analyticOnNhd_const.prod analyticOnNhd_id)
          have hcomp := hM.comp hΦ (fun g hg => ⟨inhObs_constDom hsf hBg hv hunit hj1 hjk hpoly,
            (l1_le_sum g).trans_lt hg⟩)
          intro g hg
          exact (analyticAt_pi_coord i _).comp (hcomp g hg)
        exact Finset.analyticOnNhd_fun_sum _ key2
      · simp only [hx, ↓reduceIte]
        exact analyticOnNhd_const
    exact Finset.analyticOnNhd_fun_sum _ key
  · simp only [hc, ↓reduceIte]
    exact analyticOnNhd_const

end Core

end Balaban.RootFSpine
