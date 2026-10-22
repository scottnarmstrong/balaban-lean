/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoefD1Corr
public import Balaban.SmallField.Def6InfSum

/-!
# Decay of the coefficients of the correction of P5 (1.8)

The coefficients `v^{(j)}_{1,2}(z)` of the boundary correction `corrSum` of `ℰ^{(j)}` (P5 (1.8),
P1 (3.106)–(3.110)) are the thermodynamic limits of whole-torus sums, over the polymers `X ∋ 0`, of
first and mixed second derivatives of the class terms `ℰ^{(j)}(0, X)` at the site `z`.  A derivative
at `z` vanishes unless `z ∈ X` (locality), and the class bound `E₀ e^{-κ d_j(X)}` with the covering
size `d_j(X) ≥ |z_μ| / L^{m₀+m₁} - 2 √d L` (`coord_le_of_good`) and the entropy bound of the
shapes (`exp_sum_le_at`, `κ₁ ≥ a_ent + 1`) give, for `κ₁ + κ₂ = κ`,

`|v^{(j)}_1(z)| ≤ (E₀ / ρ) K₀(κ₁) e^{-κ₂ (|z_μ| / L^{m₀+m₁} - 2 √d L)}`,
`|v^{(j)}_2(z)| ≤ (E₀ / ρ²) K₀(κ₁) e^{-κ₂ (|z_μ| / L^{m₀+m₁} - 2 √d L)}`

for every direction `μ`, on every torus of the sequence and in the limit.

* `norm_shapeSum_le_decay`: the shape sums of a coefficient that vanishes off the shapes through `z`;
* `CoefFam.norm_v1T_le`, `CoefFam.norm_v2T_le`: the bounds on the tori;
* `norm_vc_v1_le`, `norm_vc_v2_le`: the bounds of any coefficient data with `D1CorrLim`
  (`exists_unit_orth`: the transverse direction for `N ≥ 2`).
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7 Balaban.Fluctuation
  Filter Topology

section Shapes

variable {d L m₁ k : ℕ} [NeZero L]

/-- **The shape sum of a coefficient vanishing off the shapes through `z` decays in `z`.**  On the
`n`-th torus of the sequence, let `cN X'` vanish unless `z ∈ X'` and be bounded by
`C e^{-(κ₁ + κ₂) d_j(X')}` on the good shapes through `0`.  Then for every direction `μ` the sum
over the good shapes through `0` is at most `C K₀(κ₁) e^{-κ₂ (|z_μ| / L^{m₀+m₁} - 2 √d L)}`. -/
theorem norm_shapeSum_le_decay {m₀ j : ℕ} (hjk : j ≤ k) {κ₁ κ₂ : ℝ} (hκ₁ : aEnt d L + 1 ≤ κ₁)
    (hκ₂ : 0 ≤ κ₂) (z : SmallField.Site d) (n : ℕ) (cN : Finset (SmallField.Site d) → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hzero : ∀ X', z ∉ X' → cN X' = 0)
    (hbound : ∀ X', (0 : SmallField.Site d) ∈ X' → GoodAt L m₁ k m₀ j X' n →
      ‖cN X'‖ ≤ C * Real.exp (-(κ₁ + κ₂) * sizeSeq L m₁ k m₀ j X' n)) (μ : Fin d) :
    ‖∑ᶠ X' ∈ ShAt (d := d) L m₁ k m₀ j 0 n, cN X'‖ ≤
      C * K0 d L κ₁ * Real.exp (-κ₂ * (((|z μ| : ℤ) : ℝ) / (L : ℝ) ^ (m₀ + m₁) -
        2 * Real.sqrt d * L)) := by
  classical
  have : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
  set S : Finset (Finset (SmallField.Site d)) :=
    (shAt_finite (d := d) (L := L) (m₁ := m₁) (k := k) m₀ j 0 n).toFinset with hS
  have hmemS : ∀ X', X' ∈ S ↔ (0 : SmallField.Site d) ∈ X' ∧ GoodAt L m₁ k m₀ j X' n := by
    intro X'; simp [hS, ShAt]
  rw [finsum_mem_eq_finite_toFinset_sum _ (shAt_finite (d := d) (L := L) (m₁ := m₁) (k := k)
    m₀ j 0 n)]
  set D : ℝ := ((|z μ| : ℤ) : ℝ) / (L : ℝ) ^ (m₀ + m₁) - 2 * Real.sqrt d * L with hD
  have hLp : (0 : ℝ) < (L : ℝ) ^ (m₀ + m₁) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  -- each term
  have hterm : ∀ X' ∈ S, ‖cN X'‖ ≤
      C * Real.exp (-κ₂ * D) * Real.exp (-κ₁ * sizeSeq L m₁ k m₀ j X' n) := by
    intro X' hX'
    obtain ⟨h0, hgood⟩ := (hmemS X').1 hX'
    by_cases hz : z ∈ X'
    · have hsz : D ≤ sizeSeq L m₁ k m₀ j X' n := by
        have hc := coord_le_of_good (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) hjk
          hgood.1 hgood.2 h0 hz μ
        have e0 : (((|(0 : SmallField.Site d) μ| : ℤ) : ℝ)) = 0 := by simp
        rw [e0, zero_add] at hc
        have hc' : ((|z μ| : ℤ) : ℝ) / (L : ℝ) ^ (m₀ + m₁) ≤
            sizeSeq L m₁ k m₀ j X' n + 2 * Real.sqrt d * L := by
          rw [div_le_iff₀ hLp]
          unfold sizeSeq
          linarith
        rw [hD]; linarith
      refine (hbound X' h0 hgood).trans (le_of_eq_of_le rfl ?_)
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC
      nlinarith
    · rw [hzero X' hz, norm_zero]; positivity
  calc ‖∑ X' ∈ S, cN X'‖ ≤ ∑ X' ∈ S, ‖cN X'‖ := norm_sum_le _ _
    _ ≤ ∑ X' ∈ S, C * Real.exp (-κ₂ * D) * Real.exp (-κ₁ * sizeSeq L m₁ k m₀ j X' n) :=
        Finset.sum_le_sum hterm
    _ = C * Real.exp (-κ₂ * D) * ∑ X' ∈ S, Real.exp (-κ₁ * sizeSeq L m₁ k m₀ j X' n) := by
        rw [Finset.mul_sum]
    _ ≤ C * Real.exp (-κ₂ * D) * K0 d L κ₁ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact exp_sum_le_at hjk (torusSeq_dvd m₀ n) hκ₁ 0 S fun X' hX' =>
          ⟨((hmemS X').1 hX').1, ((hmemS X').1 hX').2.1, ((hmemS X').1 hX').2.2⟩
    _ = C * K0 d L κ₁ * Real.exp (-κ₂ * D) := by ring

end Shapes

section Fam

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}
  {P : Consts} {νk : ℝ} {Dom : ∀ (N₁ : ℕ) [NeZero N₁], FieldDom d L N₁ m₁ k N ϱ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ} {j : ℕ} {ρ : ℝ}

/-- **The radial whole-torus coefficient decays**: on the `n`-th torus (with the block corners of
`0` and `z` centred) `|v1T(0, z)| ≤ (E₀ / ρ) K₀(κ₁) e^{-κ₂ (|z_μ| / L^{m₀+m₁} - 2 √d L)}`,
`κ₁ + κ₂ = κ`. -/
theorem CoefFam.norm_v1T_le (fam : CoefFam P νk Dom Tm j ρ) (i₀ : Fin N)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b)))
    (z : SmallField.Site d) (n : ℕ)
    (h0u : unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j
      (blockPt j (0 : SmallField.Site d)) = 0)
    (hzu : unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j (blockPt j z) = z)
    {κ₁ κ₂ : ℝ} (hκ : κ₁ + κ₂ = P.κ) (hκ₁ : aEnt d L + 1 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (μ : Fin d) :
    ‖(haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩;
      v1T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k νk j) (Pi.single i₀ 1)
        (blockPt j (0 : SmallField.Site d)) (blockPt j z))‖ ≤
      P.E₀ / ρ * K0 d L κ₁ * Real.exp (-κ₂ * (((|z μ| : ℤ) : ℝ) / (L : ℝ) ^ (P.m₀ + m₁) -
        2 * Real.sqrt d * L)) := by
  have hjk := (fam.ctx 0).jk
  have hC : 0 ≤ P.E₀ / ρ := by
    have := fam.E0_nonneg
    have := (fam.ctx 0).rho_pos
    positivity
  rw [fam.v1T_eq_sum i₀ St hsrc 0 z n h0u hzu]
  refine norm_shapeSum_le_decay hjk hκ₁ hκ₂ z n _ hC (fun X' hz => ?_) (fun X' h0 hg => ?_) μ
  · unfold GEderN; simp [hz]
  · rw [hκ]; exact fam.norm_GEderN_le i₀ h0 hg

/-- **The transverse whole-torus coefficient decays**: on the `n`-th torus
`|v2T(0, z)| ≤ (E₀ / ρ²) K₀(κ₁) e^{-κ₂ (|z_μ| / L^{m₀+m₁} - 2 √d L)}`, `κ₁ + κ₂ = κ`. -/
theorem CoefFam.norm_v2T_le (fam : CoefFam P νk Dom Tm j ρ) (i₀ i₁ : Fin N)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b)))
    (z : SmallField.Site d) (n : ℕ)
    (h0u : unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j
      (blockPt j (0 : SmallField.Site d)) = 0)
    (hzu : unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j (blockPt j z) = z)
    {κ₁ κ₂ : ℝ} (hκ : κ₁ + κ₂ = P.κ) (hκ₁ : aEnt d L + 1 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (μ : Fin d) :
    ‖(haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩;
      v2T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k νk j) (Pi.single i₀ 1) (Pi.single i₁ 1)
        (blockPt j (0 : SmallField.Site d)) (blockPt j z))‖ ≤
      P.E₀ / ρ / ρ * K0 d L κ₁ * Real.exp (-κ₂ * (((|z μ| : ℤ) : ℝ) / (L : ℝ) ^ (P.m₀ + m₁) -
        2 * Real.sqrt d * L)) := by
  have hjk := (fam.ctx 0).jk
  have hC : 0 ≤ P.E₀ / ρ / ρ := by
    have := fam.E0_nonneg
    have := (fam.ctx 0).rho_pos
    positivity
  rw [fam.v2T_eq_sum i₀ i₁ St hsrc 0 z n h0u hzu]
  refine norm_shapeSum_le_decay hjk hκ₁ hκ₂ z n _ hC (fun X' hz => ?_) (fun X' h0 hg => ?_) μ
  · unfold G2derN; simp [hz]
  · rw [hκ]; exact fam.norm_G2derN_le i₀ i₁ h0 hg

end Fam

section Limit

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts}
  {Dom : ∀ (N₁ : ℕ) [NeZero N₁], FieldDom d L N₁ m₁ k N ϱ} {j : ℕ} {ρ : ℝ}

/-- **The radial coefficient of the correction decays** (P1 (3.110)): for coefficient data `vc`
with `D1CorrLim` (the thermodynamic limits at the physical field `h`, `|h| = 1`) and a coefficient
family of the terms at the level `j`,
`|v^{(j)}_1(z)| ≤ (E₀ / ρ) K₀(κ₁) e^{-κ₂ (|z_μ| / L^{m₀+m₁} - 2 √d L)}` for every direction `μ`,
`κ₁ + κ₂ = κ`, `κ₁ ≥ a_ent + 1`. -/
theorem norm_vc_v1_le {sf : SFData d L m₁ k N ϱ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N} {hv : EuclideanSpace ℝ (Fin N)}
    (hhv : ‖hv‖ = 1) {vc : CorrCoef d} (hD : D1CorrLim P.m₀ sf St hv vc)
    (fam : CoefFam P (sf.ν k) Dom sf.Tm j ρ) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {κ₁ κ₂ : ℝ} (hκ : κ₁ + κ₂ = P.κ) (hκ₁ : aEnt d L + 1 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    (z : Fin d → ℤ) (μ : Fin d) :
    ‖vc.v1 j z‖ ≤ P.E₀ / ρ * K0 d L κ₁ * Real.exp (-κ₂ * (((|z μ| : ℤ) : ℝ) /
      (L : ℝ) ^ (P.m₀ + m₁) - 2 * Real.sqrt d * L)) := by
  have hN : 0 < N := by
    by_contra h
    have : N = 0 := by omega
    subst this
    have : hv = 0 := Subsingleton.elim _ _
    rw [this] at hhv; simp at hhv
  set i₀ : Fin N := ⟨0, hN⟩
  have hν := (fam.ctx 0).nuj_pos
  have hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (sf.Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k (sf.ν k) j : ℝ) : ℂ)⁻¹ • b)) :=
    fun N₁ _ y Y Ψ b => hD.src_pos N₁ j hj1 hjk hν y Y Ψ b
  obtain ⟨Q, hQ, hw⟩ := exists_rot_axis i₀ hv hhv
  refine le_of_tendsto (tendsto_norm.comp (hD.v1_lim j hj1 hjk z)) ?_
  filter_upwards [eventually_unlift_blockPt (L := L) (m₁ := m₁) (k := k) hjk P.m₀ 0,
    eventually_unlift_blockPt (L := L) (m₁ := m₁) (k := k) hjk P.m₀ z] with n h1 h2
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have e := fam.v1T_axis_eq hQ St hsrc hw n 0 (blockPt j z)
  show ‖v1T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k (sf.ν k) j) (hC hv) 0
    (blockPt j z)‖ ≤ _
  rw [e, ← blockPt_zero (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) (d := d) j]
  exact fam.norm_v1T_le i₀ St hsrc z n h1 h2 hκ hκ₁ hκ₂ μ

omit [NeZero L] in
/-- A unit vector orthogonal to a given vector of `ℝ^N`, `N ≥ 2`. -/
theorem exists_unit_orth {N : ℕ} (hN : 2 ≤ N) (hv : EuclideanSpace ℝ (Fin N)) :
    ∃ e₂ : Fin N → ℝ, ∑ i, e₂ i ^ 2 = 1 ∧ ∑ i, hv i * e₂ i = 0 := by
  classical
  set i0 : Fin N := ⟨0, by omega⟩
  set i1 : Fin N := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  -- an orthogonal nonzero vector `w`
  obtain ⟨w, hw0, hwo⟩ : ∃ w : Fin N → ℝ, w ≠ 0 ∧ ∑ i, hv i * w i = 0 := by
    by_cases h : hv i0 = 0 ∧ hv i1 = 0
    · refine ⟨Pi.single i0 1, fun h' => by simpa using congrFun h' i0, ?_⟩
      rw [Finset.sum_eq_single i0 (fun b _ hb => by simp [hb])
        (fun h' => absurd (Finset.mem_univ _) h')]
      simp [h.1]
    · refine ⟨fun i => if i = i0 then hv i1 else if i = i1 then -hv i0 else 0, ?_, ?_⟩
      · intro h'
        have h0 := congrFun h' i0
        have h1 := congrFun h' i1
        simp only [↓reduceIte, Pi.zero_apply] at h0
        simp only [Ne.symm hne, ↓reduceIte, Pi.zero_apply, neg_eq_zero] at h1
        exact h ⟨h1, h0⟩
      · rw [Finset.sum_eq_add_of_mem i0 i1 (Finset.mem_univ _) (Finset.mem_univ _) hne
          (fun b _ hb => by simp [hb.1, hb.2])]
        simp only [↓reduceIte, Ne.symm hne]
        ring
  have hpos : 0 < ∑ i, w i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hw0
    have hi2 : 0 < w i ^ 2 := lt_of_le_of_ne (sq_nonneg (w i)) (Ne.symm (pow_ne_zero 2 hi))
    exact lt_of_lt_of_le hi2 (Finset.single_le_sum (f := fun i => w i ^ 2)
      (fun i _ => sq_nonneg (w i)) (Finset.mem_univ i))
  set r := Real.sqrt (∑ i, w i ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hpos
  refine ⟨fun i => w i / r, ?_, ?_⟩
  · have e : ∑ i, (w i / r) ^ 2 = (∑ i, w i ^ 2) / r ^ 2 := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    rw [e, hr, Real.sq_sqrt hpos.le, div_self hpos.ne']
  · have e : ∑ i, hv i * (w i / r) = (∑ i, hv i * w i) / r := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    rw [e, hwo, zero_div]

/-- **The transverse coefficient of the correction decays** (P1 (3.110)): for coefficient data `vc`
with `D1CorrLim` and a coefficient family of the terms at the level `j`, `N ≥ 2`,
`|v^{(j)}_2(z)| ≤ (E₀ / ρ²) K₀(κ₁) e^{-κ₂ (|z_μ| / L^{m₀+m₁} - 2 √d L)}` for every direction `μ`,
`κ₁ + κ₂ = κ`, `κ₁ ≥ a_ent + 1`. -/
theorem norm_vc_v2_le (hN2 : 2 ≤ N) {sf : SFData d L m₁ k N ϱ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N} {hv : EuclideanSpace ℝ (Fin N)}
    (hhv : ‖hv‖ = 1) {vc : CorrCoef d} (hD : D1CorrLim P.m₀ sf St hv vc)
    (fam : CoefFam P (sf.ν k) Dom sf.Tm j ρ) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {κ₁ κ₂ : ℝ} (hκ : κ₁ + κ₂ = P.κ) (hκ₁ : aEnt d L + 1 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    (z : Fin d → ℤ) (μ : Fin d) :
    ‖vc.v2 j z‖ ≤ P.E₀ / ρ / ρ * K0 d L κ₁ * Real.exp (-κ₂ * (((|z μ| : ℤ) : ℝ) /
      (L : ℝ) ^ (P.m₀ + m₁) - 2 * Real.sqrt d * L)) := by
  set i₀ : Fin N := ⟨0, by omega⟩
  set i₁ : Fin N := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by intro h; have := congrArg Fin.val h; simp [i₀, i₁] at this
  have hν := (fam.ctx 0).nuj_pos
  have hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (sf.Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k (sf.ν k) j : ℝ) : ℂ)⁻¹ • b)) :=
    fun N₁ _ y Y Ψ b => hD.src_pos N₁ j hj1 hjk hν y Y Ψ b
  obtain ⟨e₂, he, hort⟩ := exists_unit_orth hN2 hv
  set b : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 e₂ with hb
  have hb1 : ‖b‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp only [hb, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
    rw [he, Real.sqrt_one]
  have hab : inner ℝ hv b = 0 := by
    simp only [hb, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    rw [← hort]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨Q, hQ, hwa, hwb⟩ := exists_rot_pair i₀ i₁ hne hv b hhv hb1 hab
  refine le_of_tendsto (tendsto_norm.comp (hD.v2_lim j hj1 hjk e₂ he hort z)) ?_
  filter_upwards [eventually_unlift_blockPt (L := L) (m₁ := m₁) (k := k) hjk P.m₀ 0,
    eventually_unlift_blockPt (L := L) (m₁ := m₁) (k := k) hjk P.m₀ z] with n h1 h2
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have e := fam.v2T_axis_eq hQ St hsrc hwa hwb n 0 (blockPt j z)
  show ‖v2T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k (sf.ν k) j) (hC hv)
    (fun i => (e₂ i : ℂ)) 0 (blockPt j z)‖ ≤ _
  rw [show (hC hv : Fin N → ℂ) = fun i => ((hv i : ℝ) : ℂ) from rfl,
    show (fun i => (e₂ i : ℂ)) = fun i => ((b i : ℝ) : ℂ) from rfl, e,
    ← blockPt_zero (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) (d := d) j]
  exact fam.norm_v2T_le i₀ i₁ St hsrc z n h1 h2 hκ hκ₁ hκ₂ μ

end Limit

end Balaban.LargeField.Def7v2
