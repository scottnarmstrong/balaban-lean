/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgDens

/-!
# Reynolds averaging: the sum of the averaged family at constant data

* `tsum_GE_pack_const`: the sum over the polymers of the cut-off terms of `T∞` at a centre `y` at a
  configuration that is constant on every polymer is the density `ℰ_∞(y; const, const)`;
* `avg_tsum_pack`: the sum over the polymers of the averaged family at such configurations is the
  density `ℰ_∞(0; const, const)` at the origin (each of the translates of the Reynolds average
  contributes the density at its own centre, and these coincide by translation invariance at constant
  data, `ElocInf_const_translate`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- A configuration that is constant on the polymer and close to the reference point lies in the ball. -/
theorem pack_const_mem_ball (i₀ : Fin N) (νj ρ : ℝ) (hρ : 0 < ρ) (X : Finset (Site d))
    (p b : Spin N) (hp : ∀ i, ‖p i - (Pi.single i₀ 1 : Spin N) i‖ < ρ)
    (hb : ∀ i, ‖b i - ((νj : ℂ) • (Pi.single i₀ 1 : Spin N)) i‖ < ρ) :
    pack X (fun _ => p) b ∈ ball (refPt i₀ νj X) ρ := by
  rw [mem_ball, dist_eq_norm, pi_norm_lt_iff hρ]
  rintro (⟨x, i⟩ | i)
  · simpa [pack, refPt] using hp i
  · simpa [pack, refPt] using hb i

/-- The translate of a polymer as an equivalence of the finite sets. -/
def shiftEquiv (t : Site d) : Finset (Site d) ≃ Finset (Site d) where
  toFun := shiftFin t
  invFun := shiftFin (-t)
  left_inv X := by ext z; simp [mem_shiftFin]
  right_inv X := by ext z; simp [mem_shiftFin]

theorem shiftCfg_pack (t : Site d) (X : Finset (Site d)) (p b : Spin N) :
    shiftCfg t X (pack X (fun _ => p) b) = pack (shiftFin t X) (fun _ => p) b := by
  ext (⟨x, i⟩ | i) <;> rfl

section Const

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ : Fin N}
include hF hn

theorem GE_pack_const {y : Site d} {X' : Finset (Site d)} (hy : y ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') (p b : Spin N)
    (hc : pack X' (fun _ => p) b ∈
      ball (refPt i₀ (nuIdeal L k (ν k) j) X') (liftRadius d L N P j)) :
    GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' (pack X' (fun _ => p) b) =
      Einf P.m₀ Tm j y X' (constInf p) (constInf (fun i => b i / ((nuIdeal L k (ν k) j : ℝ) : ℂ))) := by
  rw [GE_of_ball hF hn hX hy hc]
  refine Einf_congr hF hn.hj1 hn.hjk hy hX (fun z hz => ?_) (fun z hz => rfl)
  funext i
  simp only [fieldInfOf, hz, ↓reduceDIte, pack, constInf]
  rfl

open Classical in
theorem tsum_GE_pack_const (y : Site d) (p b : Spin N)
    (hball : ∀ X' : Finset (Site d), pack X' (fun _ => p) b ∈
      ball (refPt i₀ (nuIdeal L k (ν k) j) X') (liftRadius d L N P j)) :
    ∑' X' : Finset (Site d), GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' (pack X' (fun _ => p) b) =
      ElocInf P.m₀ Tm j y (constInf p)
        (constInf (fun i => b i / ((nuIdeal L k (ν k) j : ℝ) : ℂ))) := by
  unfold ElocInf
  refine tsum_congr fun X' => ?_
  by_cases h : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧ y ∈ X'
  · rw [ite_eq_left h]
    exact GE_pack_const hF hn h.2 h.1 p b (hball X')
  · rw [ite_eq_right h]
    exact GE_eq_zero (fun h' => h ⟨h'.1, h'.2⟩) _ _


omit hF hn in
theorem nuIdeal_nonneg' (hν : 0 < ν k) (j : ℕ) : 0 ≤ nuIdeal L k (ν k) j :=
  (nuIdeal_pos' (L := L) hν j).le

omit hF hn in
theorem hb_of_hw (i₀ : Fin N) (νj ρ : ℝ) (hν : 0 ≤ νj) (w : Spin N)
    (hw : ∀ i, νj * ‖w i - (Pi.single i₀ 1 : Spin N) i‖ < ρ) (i : Fin N) :
    ‖((νj : ℂ) • w) i - ((νj : ℂ) • (Pi.single i₀ 1 : Spin N)) i‖ < ρ := by
  have : ((νj : ℂ) • w) i - ((νj : ℂ) • (Pi.single i₀ 1 : Spin N)) i =
      (νj : ℂ) * (w i - (Pi.single i₀ 1 : Spin N) i) := by
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν]
  exact hw i

omit hF hn in
theorem div_smul_cancel' (νj : ℝ) (hν : νj ≠ 0) (w : Spin N) :
    (fun i => ((νj : ℂ) • w) i / (νj : ℂ)) = w := by
  funext i
  have : (νj : ℂ) ≠ 0 := by exact_mod_cast hν
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- **Translation invariance of the sum of the cut-off terms at constant data**: the density
`ℰ_∞(y; const, const)` of every centre `y` is `ℰ_∞(0; const, const)`. -/
theorem tsum_GE_pack_zero (y : Site d) (p w : Spin N)
    (hp : ∀ i, ‖p i - (Pi.single i₀ 1 : Spin N) i‖ < liftRadius d L N P j)
    (hw : ∀ i, nuIdeal L k (ν k) j * ‖w i - (Pi.single i₀ 1 : Spin N) i‖ < liftRadius d L N P j) :
    ∑' X' : Finset (Site d), GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X'
        (pack X' (fun _ => p) (((nuIdeal L k (ν k) j : ℝ) : ℂ) • w)) =
      ElocInf P.m₀ Tm j 0 (constInf p) (constInf w) := by
  have hν := nuIdeal_nonneg' (L := L) hF.coeff.nu_pos j
  have hν' : nuIdeal L k (ν k) j ≠ 0 := (nuIdeal_pos' (L := L) hF.coeff.nu_pos j).ne'
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  rw [tsum_GE_pack_const hF hn y p _ (fun X' => pack_const_mem_ball i₀ _ _ hρ0 X' p _ hp
    (hb_of_hw i₀ _ _ hν w hw)), div_smul_cancel' _ hν']
  exact ElocInf_const_translate hF hn i₀ p w (fun i => (hp i).le) (fun i => (hw i).le) y

/-- The summands at a centre are summable. -/
theorem summable_GE_pack (y : Site d) (p w : Spin N)
    (hp : ∀ i, ‖p i - (Pi.single i₀ 1 : Spin N) i‖ < liftRadius d L N P j)
    (hw : ∀ i, nuIdeal L k (ν k) j * ‖w i - (Pi.single i₀ 1 : Spin N) i‖ < liftRadius d L N P j) :
    Summable fun X' : Finset (Site d) => GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X'
        (pack X' (fun _ => p) (((nuIdeal L k (ν k) j : ℝ) : ℂ) • w)) := by
  classical
  have hν := nuIdeal_nonneg' (L := L) hF.coeff.nu_pos j
  have hν' : nuIdeal L k (ν k) j ≠ 0 := (nuIdeal_pos' (L := L) hF.coeff.nu_pos j).ne'
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  have hD := xiAll_const hF hn i₀ p w (fun i => (hp i).le) (fun i => (hw i).le)
  have hE0 := hF.admissible.E₀_nonneg
  have heq : ∀ X', GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X'
        (pack X' (fun _ => p) (((nuIdeal L k (ν k) j : ℝ) : ℂ) • w)) =
      ElocInfTerm P Tm j y (constInf p) (constInf w) X' := by
    intro X'
    unfold ElocInfTerm
    by_cases h : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧ y ∈ X'
    · rw [ite_eq_left h, GE_pack_const hF hn h.2 h.1 p _
        (pack_const_mem_ball i₀ _ _ hρ0 X' p _ hp (hb_of_hw i₀ _ _ hν w hw)), div_smul_cancel' _ hν']
    · rw [ite_eq_right h]
      exact GE_eq_zero (fun h' => h ⟨h'.1, h'.2⟩) _ _
  simp_rw [heq]
  refine Summable.of_norm ?_
  refine (summable_shapes (L := L) (m₁ := m₁) (m₀ := P.m₀) (j := j) hn.hjk (κ := P.κ) (by linarith [hn.hκ, aEnt_nonneg d L]) y _ hE0
    ?_ ?_).1
  · intro X' hy hX
    unfold ElocInfTerm
    rw [ite_eq_left ⟨hX, hy⟩]
    exact Einf_norm_le_dom hF hn.hj1 hn.hjk hX hy hD.extAll
  · intro X' hX
    unfold ElocInfTerm
    rw [ite_eq_right (fun h' => hX ⟨h'.2, h'.1⟩)]

omit hF hn in
theorem tsum_GEs_pack {Mb : ℕ} (t : Fin d → Fin Mb) (p b : Spin N) :
    ∑' X : Finset (Site d), GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) t X (pack X (fun _ => p) b) =
      ∑' X' : Finset (Site d), GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs t) X'
        (pack X' (fun _ => p) b) := by
  rw [← (shiftEquiv (offs t)).tsum_eq (fun X' => GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs t) X'
    (pack X' (fun _ => p) b))]
  refine tsum_congr fun X => ?_
  unfold GEs
  rw [shiftCfg_pack]
  rfl

theorem summable_GEs_pack {Mb : ℕ} (t : Fin d → Fin Mb) (p w : Spin N)
    (hp : ∀ i, ‖p i - (Pi.single i₀ 1 : Spin N) i‖ < liftRadius d L N P j)
    (hw : ∀ i, nuIdeal L k (ν k) j * ‖w i - (Pi.single i₀ 1 : Spin N) i‖ < liftRadius d L N P j) :
    Summable fun X : Finset (Site d) => GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) t X
      (pack X (fun _ => p) (((nuIdeal L k (ν k) j : ℝ) : ℂ) • w)) := by
  have h := summable_GE_pack hF hn (i₀ := i₀) (offs t) p w hp hw
  refine ((shiftEquiv (offs t)).summable_iff.2 h).congr fun X => ?_
  unfold GEs
  rw [shiftCfg_pack]
  rfl


variable {i₁ : Fin N} (hne : i₁ ≠ i₀)
include hne

open Classical in
/-- **The sum of the averaged family at constant data** (CLASS-RULINGS Q-A): at configurations that
are constant on the polymers and close to the reference point, the sum over the polymers of the
averaged family is the density `ℰ_∞(0; const, const)` of the origin. -/
theorem avg_tsum_pack (p w : Spin N)
    (hp : ∀ i, ‖p i - (Pi.single i₀ 1 : Spin N) i‖ < liftRadius d L N P j)
    (hw : ∀ i, nuIdeal L k (ν k) j * ‖w i - (Pi.single i₀ 1 : Spin N) i‖ < liftRadius d L N P j) :
    ∑' X : (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys,
      (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).term X.1
        (pack X.1 (fun _ => p) (((nuIdeal L k (ν k) j : ℝ) : ℂ) • w)) =
      ElocInf P.m₀ Tm j 0 (constInf p) (constInf w) := by
  obtain ⟨r, hr⟩ := avgB_eq_sum hF hn.hj1 hn.hjk
  have hν := nuIdeal_nonneg' (L := L) hF.coeff.nu_pos j
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  have hball : ∀ X : Finset (Site d), pack X (fun _ => p) (((nuIdeal L k (ν k) j : ℝ) : ℂ) • w) ∈
      ball (refPt i₀ (nuIdeal L k (ν k) j) X) (liftRadius d L N P j) := fun X =>
    pack_const_mem_ball i₀ _ _ hρ0 X p _ hp (hb_of_hw i₀ _ _ hν w hw)
  set g : Finset (Site d) → ℂ := fun X =>
    (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
      ∑ q, GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (r q) X
        (pack X (fun _ => p) (((nuIdeal L k (ν k) j : ℝ) : ℂ) • w)) with hg
  have h1 : ∀ X : (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys,
      (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).term X.1
        (pack X.1 (fun _ => p) (((nuIdeal L k (ν k) j : ℝ) : ℂ) • w)) = g X.1 := by
    intro X
    show trickFn i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)
      (avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X.1) _ = _
    rw [trickFn_of_ball (avgB_tubeHyp hF hn hne X.1) (hball X.1), hr i₀ _ X.1 _]
  rw [tsum_congr h1]
  have hsupp : Function.support g ⊆ avgPolys (d := d) L m₁ k P j := by
    intro X hX
    have hX' : ∑ q, GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (r q) X
        (pack X (fun _ => p) (((nuIdeal L k (ν k) j : ℝ) : ℂ) • w)) ≠ 0 := by
      intro h0
      apply hX
      simp only [hg, h0, mul_zero]
    obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hX'
    by_contra hXn
    apply hq
    unfold GEs
    apply GE_eq_zero
    rintro ⟨hI, hmem⟩
    exact hXn ⟨by simpa using mem_shiftFin.1 hmem, r q, hI⟩
  have hsum : ∀ q ∈ (Finset.univ : Finset (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j)),
      Summable fun X : Finset (Site d) => GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (r q) X
        (pack X (fun _ => p) (((nuIdeal L k (ν k) j : ℝ) : ℂ) • w)) :=
    fun q _ => summable_GEs_pack hF hn (r q) p w hp hw
  have hcard : (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ↥(GG d L j) ⧸ KK d L P.m₀ m₁ j)).ne'
  have := tsum_subtype_eq_of_support_subset (f := g) hsupp
  refine Eq.trans this ?_
  simp only [hg]
  rw [tsum_mul_left, Summable.tsum_finsetSum hsum]
  have h2 : ∀ q : ↥(GG d L j) ⧸ KK d L P.m₀ m₁ j,
      ∑' X : Finset (Site d), GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (r q) X
        (pack X (fun _ => p) (((nuIdeal L k (ν k) j : ℝ) : ℂ) • w)) =
      ElocInf P.m₀ Tm j 0 (constInf p) (constInf w) := by
    intro q
    rw [tsum_GEs_pack (r q) p _]
    exact tsum_GE_pack_zero hF hn (offs (r q)) p w hp hw
  rw [Finset.sum_congr rfl fun q _ => h2 q, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end Const

end Balaban.SmallField.Def6
