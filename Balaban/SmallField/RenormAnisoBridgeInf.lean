/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6BridgeInfLift
public import Balaban.SmallField.RenormAnisoBridge
public import Balaban.SmallField.RenormAnisoIrrel

/-!
# The bridge Def-6 to the anisotropic I-6 from the infinite-volume family `T∞`

* `termLInfA`, `liftInfA`: the centred `ℤ^d` term family of `T∞` on the anisotropic tube (the
  analogue of `termLInf`, `liftInf` with `polyAniso` in place of the ball); `termLInfA_eq`: on
  every torus on which the polymer does not wind it is the torus term `termLA`;
* `IsSFFamily.premisesTermAnisoInf`: a member of the class supplies `PremisesTermAniso` for
  `liftInfA` at every scale `1 ≤ j ≤ k`, with the anisotropic radius `r_j = anisoRadius ≍ ε_j`,
  under P1's smallness of `ε_j` (`ε_j ≤ (2 K₁ + 2) min (c₀, c₁)`, the hypothesis of the landed
  `premisesCoreInf`);
* `IsSFFamily.termwise_irrelevant_aniso_class`: the termwise I-6 for the class,
  `|I(y,X)| ≤ C E₀ σ^{3-α₁} (ε/r_j)² e^{-(κ-1) d_j(X)}` with `C` independent of `k, j`, the polymer
  and the data; `..._eps` is the same bound in the source form `(ε/ε_j)²`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

open Classical in
/-- **The term of the infinite-volume lifted family on the anisotropic tube**: as `termLA`, with
the centred term of `T∞`. -/
noncomputable def termLInfA (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
    (m₀ j : ℕ) (i₀ : Fin N) (νj r : ℝ) (X' : Finset (Fin d → ℤ)) (c : Cfg d N X') : ℂ :=
  if h : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X' c ∈ polyAniso i₀ νj r X' then
    EauxInf Tm m₀ j i₀ νj X' (rotCfgL (Classical.choose h) X' c)
  else EauxInf Tm m₀ j i₀ νj X' c

/-- The term of the infinite-volume lifted family on the anisotropic tube is the term `termLA` of
every torus on which the polymer does not wind. -/
theorem termLInfA_eq {P : Consts} {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
    (hT : TorusIndep P.m₀ Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (i₀ : Fin N)
    (νj r : ℝ) {X' : Finset (Fin d → ℤ)} (h0 : (0 : Fin d → ℤ) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') (N₁ : ℕ) [NeZero N₁]
    (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (c : Cfg d N X') :
    termLInfA Tm P.m₀ j i₀ νj r X' c = termLA (Tm N₁) j i₀ νj r X' c := by
  unfold termLInfA termLA
  simp only [EauxInf_eq hT hj1 hjk i₀ νj h0 hX N₁ hnw hpd]

/-- **The centred `ℤ^d` term family of `T∞` at the scale `j` on the anisotropic tube**: the
polymers of `T∞` containing the origin, size `dInf`, term `termLInfA`. -/
noncomputable def liftInfA (P : Consts) (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
    (j : ℕ) (i₀ : Fin N) (νj r : ℝ) : TermFamily d N where
  polys := {X' | (0 : Site d) ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X'}
  dist := dInf L m₁ k P.m₀ j
  term := termLInfA Tm P.m₀ j i₀ νj r

section Premises

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

section Fam

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
  (hj1 : 1 ≤ j) (hjk : j ≤ k)
  (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
include hF hd hL hϱ hj1 hjk hsmall

omit hd hL hϱ hj1 hjk in
/-- The anisotropic radius condition holds for the class at `r_j = anisoRadius`. -/
theorem IsSFFamily.anisoRadiusOK (i₀ : Fin N) : AnisoRadiusOK d L N P j (anisoRadius d L N P j) :=
  anisoRadius_spec (eps_pos hF.admissible.α₀_pos j) i₀ hsmall

/-- The anisotropic tube bound of the term of `T∞`, by the covering size on any torus on which the
polymer is a non-winding polymer. -/
theorem IsSFFamily.termLInfA_tube_le {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)}
    (h0 : (0 : Site d) ∈ X') (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') {n : ℕ}
    (hn : GoodAt L m₁ k P.m₀ j X' n) {c : Cfg d N X'}
    (hc : c ∈ TubeAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X') :
    ‖termLInfA Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X' c‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeSeq L m₁ k P.m₀ j X' n) := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  rw [termLInfA_eq hF.torusIndep hj1 hjk i₀ _ _ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2 c]
  exact termLA_bdd_tube (hF.torus _) (bgHyp_of_class hF.admissible hF.coeff hd hL hϱ)
    hF.coeff.nu_pos hj1 hjk (hF.anisoRadiusOK hsmall i₀) hne hn.2 h0 hc

/-- The bound of the term of `T∞` on the data domain. -/
theorem IsSFFamily.termLInfA_dom_le {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)}
    (h0 : (0 : Site d) ∈ X') (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') {n : ℕ}
    (hn : GoodAt L m₁ k P.m₀ j X' n) {p : (Site d → Spin N) × Spin N}
    (hp : p ∈ liftDomInf P β ν a Tm j i₀) :
    ‖termLInfA Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X' (pack X' p.1 p.2)‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeSeq L m₁ k P.m₀ j X' n) := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  rw [termLInfA_eq hF.torusIndep hj1 hjk i₀ _ _ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2 _]
  exact termLA_bdd_dom_at (hF.torus _) (bgHyp_of_class hF.admissible hF.coeff hd hL hϱ)
    hF.coeff.nu_pos hj1 hjk (hF.anisoRadiusOK hsmall i₀) hne hn.2 h0
    (hp X' h0 hX n hn)

/-- Analyticity of the term of `T∞` on the anisotropic tube. -/
theorem IsSFFamily.termLInfA_analytic {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)}
    (h0 : (0 : Site d) ∈ X') (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') :
    AnalyticOnNhd ℂ (termLInfA Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X')
      (TubeAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X') := by
  obtain ⟨n, hn⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have e : termLInfA Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X' =
      termLA (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X' :=
    funext fun c => termLInfA_eq hF.torusIndep hj1 hjk i₀ _ _ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2 c
  rw [e]
  exact termLA_analytic (hF.torus _) (bgHyp_of_class hF.admissible hF.coeff hd hL hϱ)
    hF.coeff.nu_pos hj1 hjk (hF.anisoRadiusOK hsmall i₀) hne hn.2 h0

/-- Rotation invariance of the term of `T∞` on the anisotropic tube. -/
theorem IsSFFamily.termLInfA_rot_inv {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)}
    (h0 : (0 : Site d) ∈ X') (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {c : Cfg d N X'} (hc : c ∈ TubeAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X')
    (R : Matrix (Fin N) (Fin N) ℂ) (hR : IsOrth R) (hRb : EntryBd N R)
    (hRc : rotCfgL R X' c ∈ TubeAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X') :
    termLInfA Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X' (rotCfgL R X' c) =
      termLInfA Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X' c := by
  obtain ⟨n, hn⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  rw [termLInfA_eq hF.torusIndep hj1 hjk i₀ _ _ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2,
    termLInfA_eq hF.torusIndep hj1 hjk i₀ _ _ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2]
  exact termLA_rot_inv (hF.torus _) (bgHyp_of_class hF.admissible hF.coeff hd hL hϱ)
    hF.coeff.nu_pos hj1 hjk (hF.anisoRadiusOK hsmall i₀) hne hn.2 h0 hc hR hRb hRc

/-- **`IsSFFamily.premisesTermAnisoInf`**: a member of the class supplies the premises of the
anisotropic termwise I-6 at each scale `1 ≤ j ≤ k` for the lifted family `liftInfA` of `T∞`:
the geometric fields as in `premisesCoreInf`, the analytic fields from the class on any torus on
which the polymer does not wind, on `TubeAniso` with the radius `r_j = anisoRadius ≍ ε_j`. -/
theorem IsSFFamily.premisesTermAnisoInf (hκ : aEnt d L + 3 ≤ P.κ) {i₀ i₁ : Fin N}
    (hne : i₁ ≠ i₀) :
    PremisesTermAniso (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
      (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) P.E₀ P.κ
      (diamA d L P.m₀ m₁)
      ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
        K0 d L (P.κ - 2)) (liftDomInf P β ν a Tm j i₀) := by
  have hC := hF.premisesCoreInf hd hL hϱ hκ hj1 hjk hsmall hne
  -- the approximation argument for the sup (as in `premisesCoreInf`)
  have approx : ∀ {X' : Finset (Site d)} {n₀ : ℕ} (_ : GoodAt L m₁ k P.m₀ j X' n₀) {x : ℝ}
      (_ : 0 ≤ x), (∀ n, GoodAt L m₁ k P.m₀ j X' n →
        x ≤ P.E₀ * Real.exp (-P.κ * sizeSeq L m₁ k P.m₀ j X' n)) →
      x ≤ P.E₀ * Real.exp (-P.κ * dInf L m₁ k P.m₀ j X') := by
    intro X' n₀ hn₀ x hx0 hx
    have hE0 : 0 ≤ P.E₀ := by
      have h1 := hx0.trans (hx n₀ hn₀)
      by_contra hneg
      push Not at hneg
      have : P.E₀ * Real.exp (-P.κ * sizeSeq L m₁ k P.m₀ j X' n₀) < 0 :=
        mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
      linarith
    refine le_mul_exp_of_forall fun ε hε => ?_
    obtain ⟨n, hn, hlt⟩ := exists_goodAt_gt hn₀ hε
    refine (hx n hn).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hE0
    have hκ0 : 0 ≤ P.κ := hF.admissible.κ_pos.le
    nlinarith
  refine ⟨hC.ne, hC.zero_mem, hC.dist_nonneg, hC.diam, hC.count_summable, hC.count_le, ?_, ?_,
    ?_, ?_⟩
  · intro X' hX
    exact hF.termLInfA_analytic hd hL hϱ hj1 hjk hsmall hne hX.1 hX.2
  · intro X' hX c hc
    obtain ⟨n, hn⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX.2
    exact approx hn (norm_nonneg _) fun n hn =>
      hF.termLInfA_tube_le hd hL hϱ hj1 hjk hsmall hne hX.1 hX.2 hn hc
  · intro X' hX p hp
    obtain ⟨n, hn⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX.2
    exact approx hn (norm_nonneg _) fun n hn =>
      hF.termLInfA_dom_le hd hL hϱ hj1 hjk hsmall hne hX.1 hX.2 hn hp
  · intro X' hX c hc R hR hRb hRc
    exact hF.termLInfA_rot_inv hd hL hϱ hj1 hjk hsmall hne hX.1 hX.2 hc R hR hRb hRc

end Fam

end Premises

/-! ### The termwise I-6 for the class -/

theorem anisoRadius_eq (d L N : ℕ) [NeZero L] (P : Consts) (j : ℕ) :
    anisoRadius d L N P j =
      P.eps d L j / ((2 * bgK1 d L N + 2) * (4 * N * (1 + N * rotB N))) := rfl

/-- **Lemma 3.2 (iii) for the class on the anisotropic domain** (P1 Lemma 3.8 / Proposition 3.10
termwise, I6-ANISO (2.7)): for a member of the small-field class, at every scale `1 ≤ j ≤ k` with
`ε_j ≤ (2 K₁ + 2) min (c₀, c₁)`, every polymer `X` of `T∞` containing the origin and every
configuration with the properties `DataHypAniso` on the data domain of `T∞`,
`‖I(y,X)‖ ≤ C E₀ e^{-(κ-1) d_j(X)} σ^{3-α₁} (ε/r_j)²`, `r_j = anisoRadius ≍ ε_j`.  The constant
`C` depends on `d, N, L, m₁` and the class constants only (not on `k, j`, the torus sequence,
the polymer or the data). -/
theorem IsSFFamily.termwise_irrelevant_aniso_class (d L N m₁ : ℕ) [NeZero L] (P : Consts)
    (hP : P.Admissible d L) (Λ Ksig : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (ϱ : ℝ) (β ν a Ek : ℕ → ℝ)
      (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
      (ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ),
      IsSFFamily P β ν a Tm ρd Ek → 3 ≤ d → 3 ≤ L → bgR0 d L ≤ ϱ → aEnt d L + 3 ≤ P.κ →
      ∀ (j : ℕ), 1 ≤ j → j ≤ k →
      P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N) →
      ∀ (i₀ i₁ : Fin N), i₁ ≠ i₀ →
      ∀ (ψ : Site d → Spin N) (b : Spin N) (σ ε K₂ : ℝ),
      DataHypAniso (liftDomInf P β ν a Tm j i₀) (nuIdeal L k (ν k) j) σ ε K₂ ψ b →
      ∀ (X : Finset (Site d)), (0 : Site d) ∈ X →
      InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X →
      0 < ε → ε ≤ Λ * anisoRadius d L N P j → 0 < σ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 →
      nuIdeal L k (ν k) j ≤ σ ^ 2 → K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε →
      ‖Itw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
          (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (ν k) j) X ψ b‖ ≤
        C * P.E₀ * Real.exp (-(P.κ - 1) * dInf L m₁ k P.m₀ j X) *
          (σ ^ (3 - P.α₁) * (ε / anisoRadius d L N P j) ^ 2) := by
  have hα₁ : 0 < P.α₁ := hP.α₁_pos
  have hα₁' : P.α₁ < 1 := by have := hP.α₁_lt; have := hP.γ_pos; linarith
  obtain ⟨C, hC0, hC⟩ := termwise_irrelevant_aniso d N (diamA d L P.m₀ m₁) Λ Ksig P.α₁
    (diamA_nonneg d L P.m₀ m₁) hΛ hKsig hα₁ hα₁'
  refine ⟨C, hC0, ?_⟩
  intro k ϱ β ν a Ek Tm ρd hF hd hL hϱ hκ j hj1 hjk hsmall i₀ i₁ hne ψ b σ ε K₂ dat X h0 hX
    hε hεΛ hσ hσ1 hτ hνσ hK
  have hPA := hF.premisesTermAnisoInf hd hL hϱ hj1 hjk hsmall hκ hne
  obtain ⟨hr0, hr1, -⟩ := hF.anisoRadiusOK hsmall i₀
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hν0 : 0 ≤ nuIdeal L k (ν k) j := by
    have := hF.coeff.nu_pos
    unfold nuIdeal; positivity
  have hXp : X ∈ (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
      (anisoRadius d L N P j)).polys := ⟨h0, hX⟩
  -- `E₀ ≥ 0` from the bound at the reference point
  have hE0 : 0 ≤ P.E₀ := by
    have h1 := hPA.bdd_tube X hXp _
      (polyAniso_subset_tubeAniso (refPt_mem_polyAniso (i₀ := i₀)
        (ν := nuIdeal L k (ν k) j) (X := X) hr0))
    have h2 := (norm_nonneg _).trans h1
    by_contra hneg
    push Not at hneg
    have : P.E₀ * Real.exp (-P.κ * (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀
        (nuIdeal L k (ν k) j) (anisoRadius d L N P j)).dist X) < 0 :=
      mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
    linarith
  exact hC _ i₀ i₁ _ _ P.E₀ P.κ _ _ hPA ψ b σ ε K₂ dat X hXp hr0 hr1 hε hεΛ hσ hσ1 hτ hν0 hνσ hE0
    hK

/-- **The termwise I-6 for the class in the source form**: with the class radius `ε_j`,
`‖I(y,X)‖ ≤ C E₀ σ^{3-α₁} (ε/ε_j)² e^{-(κ-1) d_j(X)}` (I6-ANISO (2.7); `ε = ε_k`). -/
theorem IsSFFamily.termwise_irrelevant_aniso_class_eps (d L N m₁ : ℕ) [NeZero L] (P : Consts)
    (hP : P.Admissible d L) (Λ Ksig : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (ϱ : ℝ) (β ν a Ek : ℕ → ℝ)
      (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
      (ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ),
      IsSFFamily P β ν a Tm ρd Ek → 3 ≤ d → 3 ≤ L → bgR0 d L ≤ ϱ → aEnt d L + 3 ≤ P.κ →
      ∀ (j : ℕ), 1 ≤ j → j ≤ k →
      P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N) →
      ∀ (i₀ i₁ : Fin N), i₁ ≠ i₀ →
      ∀ (ψ : Site d → Spin N) (b : Spin N) (σ ε K₂ : ℝ),
      DataHypAniso (liftDomInf P β ν a Tm j i₀) (nuIdeal L k (ν k) j) σ ε K₂ ψ b →
      ∀ (X : Finset (Site d)), (0 : Site d) ∈ X →
      InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X →
      0 < ε → ε ≤ Λ * anisoRadius d L N P j → 0 < σ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 →
      nuIdeal L k (ν k) j ≤ σ ^ 2 → K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε →
      ‖Itw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
          (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (ν k) j) X ψ b‖ ≤
        C * P.E₀ * Real.exp (-(P.κ - 1) * dInf L m₁ k P.m₀ j X) *
          (σ ^ (3 - P.α₁) * (ε / P.eps d L j) ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := IsSFFamily.termwise_irrelevant_aniso_class d L N m₁ P hP Λ Ksig hΛ hKsig
  set Kr : ℝ := (2 * bgK1 d L N + 2) * (4 * N * (1 + N * rotB N)) with hKr
  have hK1 := bgK1_pos d L N
  have hKr0 : 0 ≤ Kr := by
    have : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
    rw [hKr]; positivity
  refine ⟨C * Kr ^ 2, by positivity, ?_⟩
  intro k ϱ β ν a Ek Tm ρd hF hd hL hϱ hκ j hj1 hjk hsmall i₀ i₁ hne ψ b σ ε K₂ dat X h0 hX
    hε hεΛ hσ hσ1 hτ hνσ hK
  have h := hC k ϱ β ν a Ek Tm ρd hF hd hL hϱ hκ j hj1 hjk hsmall i₀ i₁ hne ψ b σ ε K₂ dat X h0
    hX hε hεΛ hσ hσ1 hτ hνσ hK
  have hεj : 0 < P.eps d L j := eps_pos hF.admissible.α₀_pos j
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hKrpos : 0 < Kr := by
    have : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
    rw [hKr]; positivity
  have hq : ε / anisoRadius d L N P j = Kr * (ε / P.eps d L j) := by
    rw [anisoRadius_eq, ← hKr]; field_simp
  rw [hq] at h
  refine h.trans (le_of_eq ?_)
  ring

end Balaban.SmallField.Def6
