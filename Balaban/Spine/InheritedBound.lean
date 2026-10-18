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

end Balaban.RootFSpine
