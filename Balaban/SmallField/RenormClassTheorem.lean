/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormClassFamily
public import Balaban.SmallField.RenormClassCrude
public import Balaban.SmallField.RenormTheorem
public import Balaban.SmallField.RenormTorus

/-!
# The renormalization theorem I-6 for the class on the anisotropic domain

For a member of the small-field class (`IsSFFamily`) with the numerical conditions `MomNum` and the
Reynolds-averaged family `avgFamilyA` of terms of `T∞` on the anisotropic tube of radius
`r_j = anisoRadius ≍ ε_j`:

* `IsSFFamily.sumCondsAvgA`: the renormalization conditions (H.5)(1)-(4);
* `IsSFFamily.premisesTermAvgA`: the isotropic premises `PremisesTerm` at the radius `r_j²`
  (the anisotropic polydisc contains the isotropic ball of radius `r_j²`), together with the
  point-group invariance;
* `IsSFFamily.termwise_irrelevant_avg_aniso`, `..._scaled`: the termwise bounds for the individual
  terms `I(y,X)` of the averaged family, in the source form `(ε/ε_j)²` and in the scaled form
  `C_I E₀ s^{d+α₃}` for all scales;
* `IsSFFamily.renormalization_aniso`, `IsSFFamily.renormalization_aniso_scaled`: Theorem 2.1 /
  Lemma 3.2 for the class: `ℰ(y;ψ,b) - A_y = Σ_X I(y,X)`, `Σ_X |I(y,X)| ≤ C E₀ σ^{3-α₁} (ε/ε_j)²`
  (resp. `≤ C_I E₀ s^{d+α₃}`), and `Σ_y A_y = 0` on every torus.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.SmallField Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Fluctuation Metric Set Filter

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

theorem c1_nonneg_aux (d L : ℕ) : 0 ≤ c1 d L := by
  unfold c1; positivity

theorem K0_nonneg_aux (d L : ℕ) (κ : ℝ) : 0 ≤ K0 d L κ := by
  unfold K0
  have : Real.exp (-1) < 1 := by simp
  exact div_nonneg (Real.exp_pos _).le (by linarith)

/-- The premises of the anisotropic termwise I-6 at the radius `r ≤ 1` give the isotropic premises
at the radius `r²`, once the point-group invariance of the polymers and the terms is supplied. -/
theorem _root_.Balaban.SmallField.PremisesTermAniso.toTerm {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (h : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (sym_mem : ∀ r : Site d → Site d, IsLatGen r → ∀ X ∈ T.polys, X.image r ∈ T.polys)
    (sym_inv : ∀ r : Site d → Site d, IsLatGen r → ∀ X ∈ T.polys, ∀ (ψ : Site d → Spin N)
      (b : Spin N), T.term (X.image r) (pack (X.image r) (fun x => ψ (r x)) b) =
        T.term X (pack X ψ b)) :
    PremisesTerm T i₀ i₁ ν (r ^ 2) E₀ κ A K₀ Dom :=
  ⟨h.ne, h.zero_mem, h.dist_nonneg, h.diam, h.count_summable, h.count_le,
    fun X hX => (h.analytic X hX).mono (tube_subset_tubeAniso hr hr1),
    fun X hX c hc => h.bdd_tube X hX c (tube_subset_tubeAniso hr hr1 hc), h.bdd_dom,
    fun X hX c hc R hR hb hm => h.rot_inv X hX c (tube_subset_tubeAniso hr hr1 hc) R hR hb
      (tube_subset_tubeAniso hr hr1 hm), sym_mem, sym_inv⟩

section Avg

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

section Facts

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
  (hne : i₁ ≠ i₀)
include hF hn hne

/-- The term of the averaged family on the anisotropic tube agrees with the term of the
isotropic averaged family near the reference point. -/
theorem avgFamilyA_germ {X : Finset (Site d)} :
    (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)).term X
      =ᶠ[nhds (refPt i₀ (nuIdeal L k (ν k) j) X)]
    (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).term X := by
  obtain ⟨hr0, -, -⟩ := hF.anisoRadiusOK hn.hsmall i₀
  have hρ0 := liftRadius_pos (d := d) (L := L) (N := N) (P := P) (j := j)
    (eps_pos hF.admissible.α₀_pos j) i₀
  have hopen : IsOpen (polyAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X ∩
      ball (refPt i₀ (nuIdeal L k (ν k) j) X) (liftRadius d L N P j)) :=
    isOpen_polyAniso.inter isOpen_ball
  filter_upwards [hopen.mem_nhds ⟨refPt_mem_polyAniso hr0, mem_ball_self hρ0⟩] with c hc
  show trickFnA i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)
      (avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X) c =
    trickFn i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)
      (avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X) c
  rw [trickFnA_of_poly (avgB_tubeHypA hF hn hne X) hc.1,
    trickFn_of_ball (avgB_tubeHyp hF hn hne X) hc.2]

/-- **`SumConds` for the averaged family on the anisotropic tube**: the renormalization
conditions (H.5)(1)-(4) involve the term only through its germ at the reference point, which is
that of the isotropic averaged family (`sumCondsAvg`). -/
theorem IsSFFamily.sumCondsAvgA :
    SumConds (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
      (nuIdeal L k (ν k) j) := by
  have hS := hF.sumCondsAvg hn hne
  have germ := fun X : Finset (Site d) => avgFamilyA_germ hF hn hne (X := X)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Eq.trans (tsum_congr fun X => ?_) hS.ren_val
    exact (germ X.1).eq_of_nhds
  · refine Eq.trans (tsum_congr fun X => ?_) hS.ren_b
    rw [(germ X.1).fderiv_eq]
  · refine Eq.trans (tsum_congr fun X => Finset.sum_congr rfl fun x _ => ?_) hS.ren_psi
    unfold tensA
    rw [(germ X.1).fderiv_eq]
  · refine Eq.trans (tsum_congr fun X => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun x' _ => ?_) hS.moment
    unfold tensB D2
    rw [((germ X.1).fderiv).fderiv_eq]

/-- **The isotropic premises for the averaged family on the anisotropic tube**: at the radius
`r_j²` of the isotropic ball contained in the polydisc, with the point-group invariance. -/
theorem IsSFFamily.premisesTermAvgA :
    PremisesTerm (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
      (nuIdeal L k (ν k) j) (anisoRadius d L N P j ^ 2) P.E₀ P.κ (diamA d L P.m₀ m₁)
      (((L : ℝ) ^ (P.m₀ + m₁)) ^ d * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
        (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)))
      (avgDom P β ν a Tm j i₀ (nuIdeal L k (ν k) j)) := by
  obtain ⟨hr0, hr1, -⟩ := hF.anisoRadiusOK hn.hsmall i₀
  exact (hF.premisesTermAnisoAvg hn hne).toTerm hr0 hr1
    (fun _ hr _ hX => avgPolys_image hr hX hn.hjk)
    (fun _ hr X _ ψ b => avgFamilyA_sym_inv hF hn hne hr X ψ b)

/-- **The termwise decomposition for the averaged family on the anisotropic domain**
(Lemma 3.2): `𝓔(y;ψ,b) - A_y(ψ) = Σ_X I(y,X;ψ,b)`. -/
theorem IsSFFamily.energy_sub_Aterm_avgA {ψ : Site d → Spin N} {b : Spin N} {σ ε K₂ : ℝ}
    (dat : DataHyp (avgDom P β ν a Tm j i₀ (nuIdeal L k (ν k) j)) (nuIdeal L k (ν k) j) σ ε K₂
      ψ b) :
    energy (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) ψ b -
        Aterm (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀
          (nuIdeal L k (ν k) j) ψ =
      ∑' X : (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
          (anisoRadius d L N P j)).polys,
        Itw (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
          (nuIdeal L k (ν k) j) X.1 ψ b := by
  obtain ⟨hr0, hr1, -⟩ := hF.anisoRadiusOK hn.hsmall i₀
  exact energy_sub_Aterm_eq_tsum_Itw (hF.premisesTermAvgA hn hne) (hF.sumCondsAvgA hn hne)
    (pow_pos hr0 2) hF.admissible.E₀_nonneg (diamA_nonneg d L P.m₀ m₁) dat

/-- **`Σ_y A_y = 0` on every torus** for the averaged family on the anisotropic domain. -/
theorem IsSFFamily.Aterm_torus_sum_avgA (ℓ : ℕ) [NeZero ℓ] (ψT : Torus d ℓ → Spin N) :
    ∑ y : Torus d ℓ, (1 / 2 : ℂ) * ∑' z : Site d,
      aCoef (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀
        (nuIdeal L k (ν k) j) z *
      (dot (ψT (y + liftSite ℓ z)) (ψT (y + liftSite ℓ z)) - dot (ψT y) (ψT y)) = 0 := by
  obtain ⟨hr0, hr1, -⟩ := hF.anisoRadiusOK hn.hsmall i₀
  exact Aterm_torus_sum_tw (hF.premisesTermAvgA hn hne) (hF.sumCondsAvgA hn hne)
    (pow_pos hr0 2) hF.admissible.E₀_nonneg ℓ ψT

end Facts

end Avg

/-! ### The sums of the termwise bounds -/

theorem exp_le_wt {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (hP : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    Real.exp (-(κ - 1) * T.dist X) ≤ wt κ X (T.dist X) := by
  unfold wt
  have hd0 := hP.dist_nonneg X hX
  have hc : (1 : ℝ) ≤ X.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, hP.zero_mem X hX⟩
  have h1 : (1 : ℝ) ≤ (X.card : ℝ) ^ 2 := one_le_pow₀ hc
  have h2 : (1 : ℝ) ≤ (1 + T.dist X) ^ 6 := one_le_pow₀ (by linarith)
  have h3 : (1 : ℝ) ≤ (X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6 := one_le_mul_of_one_le_of_one_le h1 h2
  have h4 := Real.exp_pos (-(κ - 1) * T.dist X)
  nlinarith

/-- A termwise bound by `B e^{-(κ-1) d_j(X)}` sums to at most `B K₀`. -/
theorem tsum_norm_le_of_termwise {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (hP : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom)
    {f : T.polys → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ X : T.polys, ‖f X‖ ≤ B * Real.exp (-(κ - 1) * T.dist X.1)) :
    Summable (fun X : T.polys => ‖f X‖) ∧ ∑' X : T.polys, ‖f X‖ ≤ B * K₀ := by
  have hle : ∀ X : T.polys, ‖f X‖ ≤ B * wt κ X.1 (T.dist X.1) := fun X =>
    (h X).trans (mul_le_mul_of_nonneg_left (exp_le_wt hP X.2) hB)
  have hs : Summable (fun X : T.polys => B * wt κ X.1 (T.dist X.1)) :=
    hP.count_summable.mul_left B
  have hsum : Summable (fun X : T.polys => ‖f X‖) :=
    Summable.of_nonneg_of_le (fun X => norm_nonneg _) hle hs
  refine ⟨hsum, ?_⟩
  calc ∑' X : T.polys, ‖f X‖ ≤ ∑' X : T.polys, B * wt κ X.1 (T.dist X.1) :=
        hsum.tsum_le_tsum hle hs
    _ = B * ∑' X : T.polys, wt κ X.1 (T.dist X.1) := tsum_mul_left
    _ ≤ B * K₀ := mul_le_mul_of_nonneg_left hP.count_le hB

/-! ### The termwise bounds for the averaged family -/

/-- **The termwise I-6 for the averaged family of the class on the anisotropic domain**, in the
source form: `‖I(y,X)‖ ≤ C E₀ σ^{3-α₁} (ε/ε_j)² e^{-(κ-1) d_j(X)}`, with `C` independent of
`k, j`, the polymer and the data. -/
theorem IsSFFamily.termwise_irrelevant_avg_aniso (d L N m₁ : ℕ) [NeZero L] (P : Consts)
    (hP : P.Admissible d L) (Λ Ksig : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (ϱ : ℝ) (β ν a Ek : ℕ → ℝ)
      (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
      (ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ),
      IsSFFamily P β ν a Tm ρd Ek → ∀ (j : ℕ), MomNum d L N k j ϱ P →
      ∀ (i₀ i₁ : Fin N), i₁ ≠ i₀ →
      ∀ (ψ : Site d → Spin N) (b : Spin N) (σ ε K₂ : ℝ),
      DataHypAniso (avgDom P β ν a Tm j i₀ (nuIdeal L k (ν k) j)) (nuIdeal L k (ν k) j) σ ε K₂
        ψ b →
      ∀ (X : Finset (Site d)),
      X ∈ (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)).polys →
      0 < ε → ε ≤ Λ * anisoRadius d L N P j → 0 < σ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 →
      nuIdeal L k (ν k) j ≤ σ ^ 2 → K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε →
      ‖Itw (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
          (nuIdeal L k (ν k) j) X ψ b‖ ≤
        C * P.E₀ * Real.exp (-(P.κ - 1) * avgDist L m₁ k P j X) *
          (σ ^ (3 - P.α₁) * (ε / P.eps d L j) ^ 2) := by
  have hα₁ : 0 < P.α₁ := hP.α₁_pos
  have hα₁' : P.α₁ < 1 := by have := hP.α₁_lt; have := hP.γ_pos; linarith
  obtain ⟨C, hC0, hC⟩ := termwise_irrelevant_aniso d N (diamA d L P.m₀ m₁) Λ Ksig P.α₁
    (diamA_nonneg d L P.m₀ m₁) hΛ hKsig hα₁ hα₁'
  set Kr : ℝ := (2 * bgK1 d L N + 2) * (4 * N * (1 + N * rotB N)) with hKr
  have hK1 := bgK1_pos d L N
  have hKr0 : 0 ≤ Kr := by
    have : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
    rw [hKr]; positivity
  refine ⟨C * Kr ^ 2, by positivity, ?_⟩
  intro k ϱ β ν a Ek Tm ρd hF j hn i₀ i₁ hne ψ b σ ε K₂ dat X hX hε hεΛ hσ hσ1 hτ hνσ hK
  have hPA := hF.premisesTermAnisoAvg hn hne
  obtain ⟨hr0, hr1, -⟩ := hF.anisoRadiusOK hn.hsmall i₀
  have hν0 : 0 ≤ nuIdeal L k (ν k) j := by
    have := hF.coeff.nu_pos
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    unfold nuIdeal; positivity
  have h := hC _ i₀ i₁ _ _ P.E₀ P.κ _ _ hPA ψ b σ ε K₂ dat X hX hr0 hr1 hε hεΛ hσ hσ1 hτ hν0 hνσ
    hF.admissible.E₀_nonneg hK
  have hεj : 0 < P.eps d L j := eps_pos hF.admissible.α₀_pos j
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hKrpos : 0 < Kr := by
    have : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
    rw [hKr]; positivity
  have hq : ε / anisoRadius d L N P j = Kr * (ε / P.eps d L j) := by
    rw [anisoRadius_eq, ← hKr]; field_simp
  rw [hq] at h
  refine h.trans (le_of_eq ?_)
  show _ = _
  simp only [avgFamilyA]
  ring

/-- **The scaled termwise I-6 for the averaged family, all scales**: with `σ = C₀ s`,
`ε/ε_j ≤ K_R s^{(d-2)/2 - γ}` and `α₃ = 1 - 2γ - α₁`, for every `0 < s ≤ 1` (also the crude last
scales): `‖I(y,X)‖ ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)}`. -/
theorem IsSFFamily.termwise_irrelevant_avg_aniso_scaled (d L N m₁ : ℕ) [NeZero L] (P : Consts)
    (hP : P.Admissible d L) (Λ Ksig γ C₀ KR : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hC₀ : 0 < C₀)
    (hα₃ : 0 ≤ (d : ℝ) + (1 - 2 * γ - P.α₁)) :
    ∃ CI : ℝ, 0 ≤ CI ∧ ∀ (k : ℕ) (ϱ : ℝ) (β ν a Ek : ℕ → ℝ)
      (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
      (ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ),
      IsSFFamily P β ν a Tm ρd Ek → ∀ (j : ℕ), MomNum d L N k j ϱ P →
      ∀ (i₀ i₁ : Fin N), i₁ ≠ i₀ →
      ∀ (ψ : Site d → Spin N) (b : Spin N) (s σ ε K₂ : ℝ),
      DataHypAniso (avgDom P β ν a Tm j i₀ (nuIdeal L k (ν k) j)) (nuIdeal L k (ν k) j) σ ε K₂
        ψ b →
      ∀ (X : Finset (Site d)),
      X ∈ (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)).polys →
      0 < s → s ≤ 1 → σ = C₀ * s → ε / P.eps d L j ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ) →
      0 < ε → ε ≤ Λ * anisoRadius d L N P j → σ ^ 2 * ε ≤ 1 / 4 →
      nuIdeal L k (ν k) j ≤ σ ^ 2 → K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε →
      ‖Itw (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
          (nuIdeal L k (ν k) j) X ψ b‖ ≤
        CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) *
          Real.exp (-(P.κ - 1) * avgDist L m₁ k P j X) := by
  have hα₁ : 0 < P.α₁ := hP.α₁_pos
  have hα₁' : P.α₁ < 1 := by have := hP.α₁_lt; have := hP.γ_pos; linarith
  set Kr : ℝ := (2 * bgK1 d L N + 2) * (4 * N * (1 + N * rotB N)) with hKr
  have hK1 := bgK1_pos d L N
  have hKr0 : 0 ≤ Kr := by
    have : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
    rw [hKr]; positivity
  obtain ⟨CI, hCI0, hCI⟩ := termwise_irrelevant_aniso_all_scales d N (diamA d L P.m₀ m₁) Λ Ksig
    P.α₁ γ C₀ (Kr * KR) (diamA_nonneg d L P.m₀ m₁) hΛ hKsig hα₁ hα₁' hC₀ hα₃
  refine ⟨CI, hCI0, ?_⟩
  intro k ϱ β ν a Ek Tm ρd hF j hn i₀ i₁ hne ψ b s σ ε K₂ dat X hX hs hs1 hσs hR hε hεΛ hτ hνσ hK
  have hPA := hF.premisesTermAnisoAvg hn hne
  obtain ⟨hr0, hr1, -⟩ := hF.anisoRadiusOK hn.hsmall i₀
  have hν0 : 0 ≤ nuIdeal L k (ν k) j := by
    have := hF.coeff.nu_pos
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    unfold nuIdeal; positivity
  have hεj : 0 < P.eps d L j := eps_pos hF.admissible.α₀_pos j
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hKrpos : 0 < Kr := by
    have : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
    rw [hKr]; positivity
  have hq : ε / anisoRadius d L N P j = Kr * (ε / P.eps d L j) := by
    rw [anisoRadius_eq, ← hKr]; field_simp
  have hR' : ε / anisoRadius d L N P j ≤ Kr * KR * s ^ (((d : ℝ) - 2) / 2 - γ) := by
    rw [hq]
    calc Kr * (ε / P.eps d L j) ≤ Kr * (KR * s ^ (((d : ℝ) - 2) / 2 - γ)) :=
          mul_le_mul_of_nonneg_left hR hKr0
      _ = Kr * KR * s ^ (((d : ℝ) - 2) / 2 - γ) := by ring
  exact hCI _ i₀ i₁ _ _ P.E₀ P.κ _ _ hPA ψ b s σ ε K₂ dat X hX hs hs1 hσs hR' hr0 hr1 hε hεΛ hτ
    hν0 hνσ hF.admissible.E₀_nonneg hK

/-! ### The renormalization theorem -/

/-- **The renormalization theorem I-6 for the class on the anisotropic domain** (SMALLFIELD.md
Theorem 2.1, FLUCTUATION.md Lemma 3.2): for a member of the small-field class, the Reynolds
average `T` over paving offsets of the terms of `T∞` on the anisotropic tube of radius
`r_j = anisoRadius ≍ ε_j`, and data `(ψ, b)` of the anisotropic data domain (`DataHypAniso`):

* `ℰ(y;ψ,b) - A_y(ψ) = Σ_X I(y,X;ψ,b)`;
* `Σ_X ‖I(y,X;ψ,b)‖ ≤ C E₀ σ^{3-α₁} (ε/ε_j)²` (`ε = ε_k`), the series being summable, with `C`
  independent of `k, j`, the torus sequence and the data;
* `Σ_y A_y = 0` on every torus `ℤ^d / ℓℤ^d`. -/
theorem IsSFFamily.renormalization_aniso (d L N m₁ : ℕ) [NeZero L] (P : Consts)
    (hP : P.Admissible d L) (Λ Ksig : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (ϱ : ℝ) (β ν a Ek : ℕ → ℝ)
      (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
      (ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ),
      IsSFFamily P β ν a Tm ρd Ek → ∀ (j : ℕ), MomNum d L N k j ϱ P →
      ∀ (i₀ i₁ : Fin N), i₁ ≠ i₀ →
      ∀ (ψ : Site d → Spin N) (b : Spin N) (σ ε K₂ : ℝ),
      DataHypAniso (avgDom P β ν a Tm j i₀ (nuIdeal L k (ν k) j)) (nuIdeal L k (ν k) j) σ ε K₂
        ψ b →
      0 < ε → ε ≤ Λ * anisoRadius d L N P j → 0 < σ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 →
      nuIdeal L k (ν k) j ≤ σ ^ 2 → K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε →
      (energy (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) ψ b -
          Aterm (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀
            (nuIdeal L k (ν k) j) ψ =
        ∑' X : (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
            (anisoRadius d L N P j)).polys,
          Itw (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
            (nuIdeal L k (ν k) j) X.1 ψ b) ∧
      Summable (fun X : (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
          (anisoRadius d L N P j)).polys =>
        ‖Itw (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
          (nuIdeal L k (ν k) j) X.1 ψ b‖) ∧
      ∑' X : (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
            (anisoRadius d L N P j)).polys,
          ‖Itw (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
            (nuIdeal L k (ν k) j) X.1 ψ b‖ ≤
        C * P.E₀ * (σ ^ (3 - P.α₁) * (ε / P.eps d L j) ^ 2) ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (ψT : Torus d ℓ → Spin N),
        ∑ y : Torus d ℓ, (1 / 2 : ℂ) * ∑' z : Site d,
          aCoef (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀
            (nuIdeal L k (ν k) j) z *
          (dot (ψT (y + liftSite ℓ z)) (ψT (y + liftSite ℓ z)) - dot (ψT y) (ψT y)) = 0 := by
  obtain ⟨C, hC0, hC⟩ := IsSFFamily.termwise_irrelevant_avg_aniso d L N m₁ P hP Λ Ksig hΛ hKsig
  have hK0 : 0 ≤ ((L : ℝ) ^ (P.m₀ + m₁)) ^ d * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
      (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)) := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have h1 := c1_nonneg_aux d L
    have h2 := K0_nonneg_aux d L (P.κ - 2)
    positivity
  refine ⟨C * (((L : ℝ) ^ (P.m₀ + m₁)) ^ d * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
      (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2))), by positivity, ?_⟩
  intro k ϱ β ν a Ek Tm ρd hF j hn i₀ i₁ hne ψ b σ ε K₂ dat hε hεΛ hσ hσ1 hτ hνσ hK
  have hPA := hF.premisesTermAnisoAvg hn hne
  have hE0 := hF.admissible.E₀_nonneg
  have hB0 : 0 ≤ C * P.E₀ * (σ ^ (3 - P.α₁) * (ε / P.eps d L j) ^ 2) := by
    have : 0 ≤ σ ^ (3 - P.α₁) := (Real.rpow_pos_of_pos hσ _).le
    positivity
  have hsum := tsum_norm_le_of_termwise hPA
    (f := fun X : (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
      (anisoRadius d L N P j)).polys => Itw (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
        (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (ν k) j) X.1 ψ b) hB0 (fun X => by
    have h := hC k ϱ β ν a Ek Tm ρd hF j hn i₀ i₁ hne ψ b σ ε K₂ dat X.1 X.2 hε hεΛ hσ hσ1 hτ hνσ hK
    refine h.trans (le_of_eq ?_)
    show _ = _
    simp only [avgFamilyA]
    ring)
  refine ⟨hF.energy_sub_Aterm_avgA hn hne dat.toDataHyp, hsum.1, ?_, fun ℓ _ ψT =>
    hF.Aterm_torus_sum_avgA hn hne ℓ ψT⟩
  refine hsum.2.trans (le_of_eq ?_)
  ring

/-- **The renormalization theorem I-6 for the class on the anisotropic domain, scaled form (3.1),
all scales**: with `σ = C₀ s`, `ε/ε_j ≤ K_R s^{(d-2)/2 - γ}`, `α₃ = 1 - 2γ - α₁`, for every
`0 < s ≤ 1`: `ℰ(y;ψ,b) - A_y = Σ_X I(y,X)` and `Σ_X ‖I(y,X)‖ ≤ C_I E₀ s^{d+α₃}`; and `Σ_y A_y = 0`
on every torus. -/
theorem IsSFFamily.renormalization_aniso_scaled (d L N m₁ : ℕ) [NeZero L] (P : Consts)
    (hP : P.Admissible d L) (Λ Ksig γ C₀ KR : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hC₀ : 0 < C₀)
    (hα₃ : 0 ≤ (d : ℝ) + (1 - 2 * γ - P.α₁)) :
    ∃ CI : ℝ, 0 ≤ CI ∧ ∀ (k : ℕ) (ϱ : ℝ) (β ν a Ek : ℕ → ℝ)
      (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
      (ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ),
      IsSFFamily P β ν a Tm ρd Ek → ∀ (j : ℕ), MomNum d L N k j ϱ P →
      ∀ (i₀ i₁ : Fin N), i₁ ≠ i₀ →
      ∀ (ψ : Site d → Spin N) (b : Spin N) (s σ ε K₂ : ℝ),
      DataHypAniso (avgDom P β ν a Tm j i₀ (nuIdeal L k (ν k) j)) (nuIdeal L k (ν k) j) σ ε K₂
        ψ b →
      0 < s → s ≤ 1 → σ = C₀ * s → ε / P.eps d L j ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ) →
      0 < ε → ε ≤ Λ * anisoRadius d L N P j → σ ^ 2 * ε ≤ 1 / 4 →
      nuIdeal L k (ν k) j ≤ σ ^ 2 → K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε →
      (energy (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) ψ b -
          Aterm (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀
            (nuIdeal L k (ν k) j) ψ =
        ∑' X : (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
            (anisoRadius d L N P j)).polys,
          Itw (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
            (nuIdeal L k (ν k) j) X.1 ψ b) ∧
      Summable (fun X : (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
          (anisoRadius d L N P j)).polys =>
        ‖Itw (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
          (nuIdeal L k (ν k) j) X.1 ψ b‖) ∧
      ∑' X : (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
            (anisoRadius d L N P j)).polys,
          ‖Itw (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
            (nuIdeal L k (ν k) j) X.1 ψ b‖ ≤
        CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (ψT : Torus d ℓ → Spin N),
        ∑ y : Torus d ℓ, (1 / 2 : ℂ) * ∑' z : Site d,
          aCoef (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀
            (nuIdeal L k (ν k) j) z *
          (dot (ψT (y + liftSite ℓ z)) (ψT (y + liftSite ℓ z)) - dot (ψT y) (ψT y)) = 0 := by
  obtain ⟨CI, hCI0, hCI⟩ := IsSFFamily.termwise_irrelevant_avg_aniso_scaled d L N m₁ P hP Λ Ksig
    γ C₀ KR hΛ hKsig hC₀ hα₃
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hK0 : 0 ≤ ((L : ℝ) ^ (P.m₀ + m₁)) ^ d * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
      (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)) := by
    have h1 := c1_nonneg_aux d L
    have h2 := K0_nonneg_aux d L (P.κ - 2)
    positivity
  refine ⟨CI * (((L : ℝ) ^ (P.m₀ + m₁)) ^ d * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
      (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2))), by positivity, ?_⟩
  intro k ϱ β ν a Ek Tm ρd hF j hn i₀ i₁ hne ψ b s σ ε K₂ dat hs hs1 hσs hR hε hεΛ hτ hνσ hK
  have hPA := hF.premisesTermAnisoAvg hn hne
  have hE0 := hF.admissible.E₀_nonneg
  have hB0 : 0 ≤ CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) := by
    have : 0 ≤ s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) := (Real.rpow_pos_of_pos hs _).le
    positivity
  have hsum := tsum_norm_le_of_termwise hPA
    (f := fun X : (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
      (anisoRadius d L N P j)).polys => Itw (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j)
        (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (ν k) j) X.1 ψ b) hB0 (fun X => by
    have h := hCI k ϱ β ν a Ek Tm ρd hF j hn i₀ i₁ hne ψ b s σ ε K₂ dat X.1 X.2 hs hs1 hσs hR hε hεΛ
      hτ hνσ hK
    refine h.trans (le_of_eq ?_)
    show _ = _
    simp only [avgFamilyA])
  refine ⟨hF.energy_sub_Aterm_avgA hn hne dat.toDataHyp, hsum.1, ?_, fun ℓ _ ψT =>
    hF.Aterm_torus_sum_avgA hn hne ℓ ψT⟩
  exact hsum.2.trans (le_of_eq (by ring))

end Balaban.SmallField.Def6
