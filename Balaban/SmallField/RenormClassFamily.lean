/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgBridge
public import Balaban.SmallField.RenormClassGE
public import Balaban.SmallField.RenormAnisoCtx

/-!
# The Reynolds-averaged family on the anisotropic tube

* `avgFamilyA`: the averaged centred term family of the class (`avgFamily`) with the term extended
  to `TubeAniso` (radius `r = anisoRadius`) by complex orthogonal rotations (`trickFnA`);
* `IsSFFamily.premisesTermAnisoAvg`: it satisfies `PremisesTermAniso` at `r = anisoRadius`;
* `avgFamilyA_sym_inv`, `avgPolys_image`: the point-group invariance;
* `IsSFFamily.sumCondsAvgA`: it satisfies the renormalization conditions `SumConds` (the term of
  `avgFamilyA` agrees near the reference point with the term of `avgFamily`, which satisfies them
  by `sumCondsAvg`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.SmallField Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Fluctuation Metric Set Filter

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

section Avg

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

theorem mem_polyAniso_shiftCfg (t : Site d) (X : Finset (Site d)) (i₀ : Fin N) (ν r : ℝ)
    (c : Cfg d N X) :
    shiftCfg t X c ∈ polyAniso i₀ ν r (shiftFin t X) ↔ c ∈ polyAniso i₀ ν r X :=
  mem_polyAniso_reCfg (X := shiftFin t X) (X' := X) (fun z => z - t) (fun x => x + t)
    sub_mem_of_mem_shiftFin add_mem_shiftFin (fun x _ => by simp) i₀ ν r c

section Facts

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
  (hne : i₁ ≠ i₀)
include hF hn hne

theorem GEs_tubeHypA {Mb : ℕ} (t : Fin d → Fin Mb) (X : Finset (Site d)) :
    TubeHypA i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)
      (GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) t X) := by
  by_cases h : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j (shiftFin (offs t) X) ∧
      offs t ∈ shiftFin (offs t) X
  · have hT : TubeHypA i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)
        (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs t) (shiftFin (offs t) X)) :=
      ⟨fun _ hc => GE_analyticAtA hF hn h.1 h.2 hc,
        fun _ hM hMb _ _ hu hu' hr => GE_rotA hF hn hne h.1 h.2 hM hMb hu hu' hr⟩
    exact hT.comp (reCfgL (X := shiftFin (offs t) X) (X' := X) (fun z => z - offs t)
      sub_mem_of_mem_shiftFin)
      (fun R c => reCfg_rot (X := shiftFin (offs t) X) (X' := X) (fun z => z - offs t)
        sub_mem_of_mem_shiftFin R c)
      (fun c => mem_polyAniso_shiftCfg (offs t) X i₀ _ _ c)
  · have h0 : GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) t X = fun _ => 0 := by
      funext c; exact GE_eq_zero h _ _
    rw [h0]
    exact ⟨fun _ _ => analyticAt_const, fun _ _ _ _ _ _ _ _ => rfl⟩

omit hne in
theorem GEs_norm_leA {Mb : ℕ} (t : Fin d → Fin Mb) (X : Finset (Site d)) {B : ℝ}
    (hB : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j (shiftFin (offs t) X) ∧
      offs t ∈ shiftFin (offs t) X →
        P.E₀ * Real.exp (-P.κ * dInf L m₁ k P.m₀ j (shiftFin (offs t) X)) ≤ B) (hB0 : 0 ≤ B)
    {c : Cfg d N X}
    (hc : c ∈ polyAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X) :
    ‖GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) t X c‖ ≤ B := by
  by_cases h : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j (shiftFin (offs t) X) ∧
      offs t ∈ shiftFin (offs t) X
  · refine (GE_norm_leA hF hn h.1 h.2 ((mem_polyAniso_shiftCfg (offs t) X i₀ _ _ c).2 hc)).trans ?_
    exact hB h
  · unfold GEs
    rw [GE_eq_zero h]
    simpa using hB0

theorem avgB_tubeHypA (X : Finset (Site d)) :
    TubeHypA i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)
      (avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X) := by
  obtain ⟨r, hr⟩ := avgB_eq_sum hF hn.hj1 hn.hjk
  have : avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X = fun c =>
      (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
        ∑ q, GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (r q) X c := by
    funext c; exact hr i₀ _ X c
  rw [this]
  refine ⟨fun c hc => ?_, fun M hM hMb u u' hu hu' hrot => ?_⟩
  · exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun q _ =>
      (GEs_tubeHypA hF hn hne (r q) X).analytic c hc)
  · rw [Finset.sum_congr rfl fun q _ =>
      (GEs_tubeHypA hF hn hne (r q) X).rot M hM hMb u u' hu hu' hrot]

omit hne in
/-- **The bound on the anisotropic polydisc**: `|avgB X (c)| ≤ E₀ e^{-κ d(X)}`. -/
theorem avgB_norm_leA {X : Finset (Site d)} {c : Cfg d N X}
    (hc : c ∈ polyAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X) :
    ‖avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X c‖ ≤
      P.E₀ * Real.exp (-P.κ * avgDist L m₁ k P j X) := by
  obtain ⟨r, hr⟩ := avgB_eq_sum hF hn.hj1 hn.hjk
  have hE0 := hF.admissible.E₀_nonneg
  have hκ0 := hF.admissible.κ_pos
  have hB0 : 0 ≤ P.E₀ * Real.exp (-P.κ * avgDist L m₁ k P j X) := by positivity
  rw [hr i₀ _ X c]
  have hcard : 0 < Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) := Fintype.card_pos
  have hterm : ∀ q, ‖GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (r q) X c‖ ≤
      P.E₀ * Real.exp (-P.κ * avgDist L m₁ k P j X) := by
    intro q
    refine GEs_norm_leA hF hn (r q) X (fun h => ?_) hB0 hc
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hE0
    have := avgDist_le (d := d) (L := L) (m₁ := m₁) (k := k) (P := P) (j := j) (X := X)
      (t := r q) h.1
    nlinarith
  calc _ = ((Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℝ))⁻¹ *
        ‖∑ q, GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (r q) X c‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ ((Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℝ))⁻¹ *
        ∑ q : ↥(GG d L j) ⧸ KK d L P.m₀ m₁ j, P.E₀ * Real.exp (-P.κ * avgDist L m₁ k P j X) := by
        refine mul_le_mul_of_nonneg_left
          ((norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => hterm q)) (by positivity)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

end Facts

variable (P β ν a Tm j) in
/-- **The averaged centred term family of the class on the anisotropic tube**: the polymers and
sizes of `avgFamily`, the term the extension to `TubeAniso i₀ νj r` (by complex orthogonal
rotations) of the Reynolds average `avgB` over the cosets of the paving group. -/
noncomputable def avgFamilyA (i₀ : Fin N) (νj r : ℝ) : TermFamily d N where
  polys := avgPolys (d := d) L m₁ k P j
  dist := avgDist (d := d) L m₁ k P j
  term := fun X c => trickFnA i₀ νj r (avgB P β ν a Tm j i₀ νj X) c

/-- **The point-group invariance of the averaged terms on the anisotropic tube**. -/
theorem avgFamilyA_sym_inv (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : Site d → Site d} (hr : IsLatGen r)
    (X : Finset (Site d)) (ψ : Site d → Spin N) (b : Spin N) :
    (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)).term (X.image r)
        (pack (X.image r) (fun x => ψ (r x)) b) =
      (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)).term X
        (pack X ψ b) := by
  obtain ⟨g, hg, rfl⟩ := exists_latGen (L := L) (j := j) hr
  set ρ := anisoRadius d L N P j
  set νj := nuIdeal L k (ν k) j
  have hW : 0 < L ^ j := pow_pos (NeZero.pos L) j
  have hinv : ∀ x, (blkZ (L ^ j) g) ((blkZ (L ^ j) g) x) = x := latGen_invol hr
  have hzero : (blkZ (L ^ j) g) 0 = 0 := latGen_zero hr
  have hσ : ∀ x ∈ X, (blkZ (L ^ j) g) x ∈ X.image (blkZ (L ^ j) g) :=
    fun x hx => Finset.mem_image_of_mem _ hx
  have hτ : ∀ x ∈ X.image (blkZ (L ^ j) g), (blkZ (L ^ j) g) x ∈ X := by
    intro x hx
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hx
    rw [hinv]; exact hb'
  set c'' : Cfg d N (X.image (blkZ (L ^ j) g)) :=
    pack (X.image (blkZ (L ^ j) g)) (fun x => ψ ((blkZ (L ^ j) g) x)) b with hc''
  have hc : reCfg (blkZ (L ^ j) g) hσ c'' = pack X ψ b := by
    ext (p | i)
    · simp [reCfg_inl, hc'', pack, hinv]
    · simp [reCfg_inr, hc'', pack]
  have hav : ∀ c : Cfg d N (X.image (blkZ (L ^ j) g)),
      avgB P β ν a Tm j i₀ νj (X.image (blkZ (L ^ j) g)) c =
        avgB P β ν a Tm j i₀ νj X (reCfg (blkZ (L ^ j) g) hσ c) := by
    intro c
    unfold avgB
    have := act_state hg i₀ νj X 0 c
    rw [hzero] at this
    rw [← this]
    exact avgFB_act hF hn.hj1 hn.hjk hg _
  have hT := avgB_tubeHypA hF hn hne X
  have hcomp := trickFnA_comp hT
    (reCfgL (X := X) (X' := X.image (blkZ (L ^ j) g)) (blkZ (L ^ j) g) hσ)
    (fun R c => reCfg_rot (blkZ (L ^ j) g) hσ R c)
    (fun c => mem_polyAniso_reCfg (blkZ (L ^ j) g) (blkZ (L ^ j) g) hσ hτ (fun x _ => hinv x)
      i₀ νj ρ c) c''
  show trickFnA i₀ νj ρ (avgB P β ν a Tm j i₀ νj (X.image (blkZ (L ^ j) g))) c'' =
    trickFnA i₀ νj ρ (avgB P β ν a Tm j i₀ νj X) (pack X ψ b)
  have e : avgB P β ν a Tm j i₀ νj (X.image (blkZ (L ^ j) g)) = fun c =>
      avgB P β ν a Tm j i₀ νj X
        (reCfgL (X := X) (X' := X.image (blkZ (L ^ j) g)) (blkZ (L ^ j) g) hσ c) := funext hav
  rw [e, hcomp]
  show trickFnA i₀ νj ρ (avgB P β ν a Tm j i₀ νj X) (reCfg (blkZ (L ^ j) g) hσ c'') = _
  rw [hc]

/-- **`PremisesTermAniso` for the averaged family** (CLASS-RULINGS Q-A, Q-D): a member of the class
supplies the premises of the anisotropic termwise I-6 for the Reynolds average over paving offsets
of the terms of `T∞`, on `TubeAniso` of radius `r = anisoRadius`, with the counting constant
multiplied by the number `(L^{m₀+m₁})^d` of paving offsets. -/
theorem IsSFFamily.premisesTermAnisoAvg (hF : IsSFFamily P β ν a Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    PremisesTermAniso
      (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀ i₁
      (nuIdeal L k (ν k) j) (anisoRadius d L N P j) P.E₀ P.κ (diamA d L P.m₀ m₁)
      (((L : ℝ) ^ (P.m₀ + m₁)) ^ d * ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
        (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2)))
      (avgDom P β ν a Tm j i₀ (nuIdeal L k (ν k) j)) := by
  have hC := avgFamily_core hF hn hne
  refine ⟨hC.ne, hC.zero_mem, hC.dist_nonneg, hC.diam, hC.count_summable, hC.count_le, ?_, ?_, ?_,
    ?_⟩
  · intro X hX
    exact (avgB_tubeHypA hF hn hne X).trickFnA_analytic
  · intro X hX c hc
    exact (avgB_tubeHypA hF hn hne X).trickFnA_bound (fun c' hc' => avgB_norm_leA hF hn hc') hc
  · intro X hX p hp
    show ‖trickFnA i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)
      (avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X) (pack X p.1 p.2)‖ ≤ _
    by_cases hT : pack X p.1 p.2 ∈
        TubeAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X
    · exact (avgB_tubeHypA hF hn hne X).trickFnA_bound
        (fun c' hc' => avgB_norm_leA hF hn hc') hT
    · have : trickFnA i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)
          (avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X) (pack X p.1 p.2) =
          avgB P β ν a Tm j i₀ (nuIdeal L k (ν k) j) X (pack X p.1 p.2) := by
        have hnex : ¬ ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
            rotCfgL R X (pack X p.1 p.2) ∈
              polyAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X := hT
        unfold trickFnA
        rw [dite_eq_right hnex]
      rw [this]
      exact avgB_norm_le_dom hF hn (fun t ht => hp X hX t ht)
  · intro X hX c hc R hR hRb hRc
    exact (avgB_tubeHypA hF hn hne X).trickFnA_rot hc hR hRb hRc

end Avg

end Balaban.SmallField.Def6
