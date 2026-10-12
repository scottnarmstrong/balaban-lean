/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6BridgeInfDer

/-!
# The bridge Def-6 to I-6 from `T∞`: the renormalization conditions `SumConds`

For the lifted family `liftInf` of the infinite-volume terms `T∞`:

* `Einf_congr`: locality of `ℰ_∞(y, X'; ψ, h)` in `(ψ, h)` on the blocks of `X'`;
* `IsSFFamily.termLInf_pack_const`: the term at a constant configuration on the ball is `ℰ_∞(0, X')`
  at the constant fields;
* `ElocInf_eq_tsum_polys`: `ElocInf` at the origin is the sum over `liftInf.polys`;
* `IsSFFamily.liftInf_ren_val`, `liftInf_ren_b`, `liftInf_ren_psi`: the conditions (H.5)(1)-(3) of
  `SumConds` from the infinite-volume `RenormCond` (`val`, `dh`, `dpsi`); the derivative conditions
  use differentiation under the sum (`hasFDerivAt_tsum_term`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation Balaban.SmallField Filter Metric Set

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

section Local

/-- **Locality of the terms of `T∞`**: `ℰ_∞(y, X'; ψ, h)` depends only on `(ψ, h)` on the blocks of
`X'`. -/
theorem Einf_congr (hF : IsSFFamily P β ν a Tm ρd Ek) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : Fin d → ℤ} {X' : Finset (Fin d → ℤ)} (hy : y ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') {ψ ψ' h h' : InfFld d N}
    (hψ : ∀ z, blockOf L j z ∈ X' → ψ z = ψ' z) (hh : ∀ z, blockOf L j z ∈ X' → h z = h' z) :
    Einf P.m₀ Tm j y X' ψ h = Einf P.m₀ Tm j y X' ψ' h' := by
  obtain ⟨n, hn⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  rw [Einf_eq_torus hF.torusIndep hj1 hjk hy hX ψ h (torusSeq L P.m₀ n) hn.1 hn.2,
    Einf_eq_torus hF.torusIndep hj1 hjk hy hX ψ' h' (torusSeq L P.m₀ n) hn.1 hn.2]
  refine (hF.torus (torusSeq L P.m₀ n)).localE j _ _ _ _ _ _ fun x hx => ?_
  have hb : blockOf L j (fineLift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j x) ∈ X' := by
    rw [blockOf_fineLift]; exact hx
  exact ⟨hψ _ hb, hh _ hb⟩

end Local


section Lin

/-- The linear map `v ↦ (0, ν v)` from the field `h` to the `b`-component of a configuration. -/
noncomputable def bLin (X : Finset (Site d)) (νj : ℝ) : (Fin N → ℂ) →L[ℂ] Cfg d N X :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Sum.elim (fun _ => 0) (fun i => (νj : ℂ) * v i)
      map_add' := fun v w => by
        funext idx; cases idx <;> simp [mul_add]
      map_smul' := fun t v => by
        funext idx; cases idx <;> simp [mul_left_comm] }

theorem bLin_apply_inr (X : Finset (Site d)) (νj : ℝ) (v : Fin N → ℂ) (i : Fin N) :
    bLin X νj v (Sum.inr i) = (νj : ℂ) * v i := rfl

theorem bLin_apply_inl (X : Finset (Site d)) (νj : ℝ) (v : Fin N → ℂ) (p : ↥X × Fin N) :
    bLin X νj v (Sum.inl p) = 0 := rfl

theorem norm_bLin_le (X : Finset (Site d)) {νj : ℝ} (hν : 0 ≤ νj) : ‖bLin (N := N) X νj‖ ≤ νj := by
  refine ContinuousLinearMap.opNorm_le_bound _ hν fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun idx => ?_
  cases idx with
  | inl p => simp [bLin_apply_inl]; positivity
  | inr i =>
    rw [bLin_apply_inr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) hν

/-- The vector `∑_{x ∈ X} δ_{(x, i₀)}` of the `ψ`-components of a configuration: the direction of
the constant change of `ψ_{i₀}` on the polymer. -/
noncomputable def psiDir (X : Finset (Site d)) (i₀ : Fin N) : Cfg d N X :=
  ∑ x : ↥X, Pi.single (Sum.inl (x, i₀)) 1

theorem psiDir_inl (X : Finset (Site d)) (i₀ : Fin N) (x : ↥X) (i : Fin N) :
    psiDir X i₀ (Sum.inl (x, i)) = if i = i₀ then 1 else 0 := by
  unfold psiDir
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single x]
  · by_cases h : i = i₀
    · subst h; simp
    · simp [h]
  · intro y _ hy
    simp [hy.symm]
  · simp

theorem psiDir_inr (X : Finset (Site d)) (i₀ i : Fin N) : psiDir X i₀ (Sum.inr i) = 0 := by
  unfold psiDir
  simp [Finset.sum_apply]

theorem norm_psiDir_le (X : Finset (Site d)) (i₀ : Fin N) : ‖psiDir X i₀‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun idx => ?_
  cases idx with
  | inl p =>
    obtain ⟨x, i⟩ := p
    rw [psiDir_inl]; split_ifs <;> simp
  | inr i => rw [psiDir_inr]; simp

/-- The linear map `t ↦ t · ∑_{x ∈ X} δ_{(x, i₀)}`. -/
noncomputable def tLin (X : Finset (Site d)) (i₀ : Fin N) : ℂ →L[ℂ] Cfg d N X :=
  LinearMap.toContinuousLinearMap (LinearMap.toSpanSingleton ℂ _ (psiDir X i₀))

theorem tLin_apply (X : Finset (Site d)) (i₀ : Fin N) (t : ℂ) :
    tLin X i₀ t = t • psiDir X i₀ := rfl

theorem norm_tLin_le (X : Finset (Site d)) (i₀ : Fin N) : ‖tLin X i₀‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => ?_
  rw [tLin_apply, norm_smul]
  have := norm_psiDir_le X i₀
  nlinarith [norm_nonneg t, norm_nonneg (psiDir X i₀)]

end Lin

section Pack

variable (hF : IsSFFamily P β ν a Tm ρd Ek)
include hF

/-- On the ball around the reference point the term of `T∞` is the centred term `EauxInf`. -/
theorem IsSFFamily.termLInf_of_ball (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') {c : Cfg d N X'}
    (hc : c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') (liftRadius d L N P j)) :
    termLInf Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X' c =
      EauxInf Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) X' c := by
  obtain ⟨n, hn⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := hF.liftCtx (torusSeq L P.m₀ n) hd hL hϱ hj1 hjk
    (liftRadius_pos (eps_pos hF.admissible.α₀_pos j) i₀)
    (liftRadius_spec (eps_pos hF.admissible.α₀_pos j) i₀ hsmall)
  rw [termLInf_eq hF.torusIndep hj1 hjk i₀ _ _ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2,
    EauxInf_eq hF.torusIndep hj1 hjk i₀ _ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2]
  exact ctx.termL_of_ball hne hn.2 h0 hc

/-- **The term of `T∞` at a constant configuration on the ball**: it is `ℰ_∞(0, X')` at the
constant fields. -/
theorem IsSFFamily.termLInf_pack_const (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') (p b : Spin N)
    (hc : pack X' (fun _ => p) b ∈
      ball (refPt i₀ (nuIdeal L k (ν k) j) X') (liftRadius d L N P j)) :
    termLInf Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X' (pack X' (fun _ => p) b) =
      Einf P.m₀ Tm j 0 X' (constInf p) (constInf (fun i => b i / ((nuIdeal L k (ν k) j : ℝ) : ℂ))) := by
  rw [hF.termLInf_of_ball hd hL hϱ hj1 hjk hsmall hne h0 hX hc]
  unfold EauxInf
  refine Einf_congr hF hj1 hjk h0 hX (fun z hz => ?_) (fun z hz => rfl)
  funext i
  simp only [fieldInfOf, hz, ↓reduceDIte, pack, constInf]
  rfl


omit hF in
theorem nuIdeal_pos' (hν : 0 < ν k) (j : ℕ) : 0 < nuIdeal L k (ν k) j := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold nuIdeal; positivity

omit hF in
/-- The configuration of the polymer at which a constant `ψ` and the field `b` are given, at the
reference point. -/
theorem refPt_eq_pack (i₀ : Fin N) (νj : ℝ) (X' : Finset (Site d)) :
    refPt i₀ νj X' = pack X' (fun _ => (Pi.single i₀ 1 : Fin N → ℂ))
      ((νj : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)) := rfl

open Classical in
omit hF in
/-- `ElocInf` at the origin is the sum over the polymers of `T∞` containing the origin. -/
theorem ElocInf_eq_tsum_polys (P : Consts) (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
    (j : ℕ) (ψ h : InfFld d N) :
    ElocInf P.m₀ Tm j 0 ψ h = ∑' X : {X' : Finset (Site d) // (0 : Site d) ∈ X' ∧
      InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X'}, Einf P.m₀ Tm j 0 X.1 ψ h := by
  set S : Set (Finset (Site d)) := {X' | (0 : Site d) ∈ X' ∧
    InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X'} with hS
  calc ElocInf P.m₀ Tm j 0 ψ h = ∑' X', S.indicator (fun X' => Einf P.m₀ Tm j 0 X' ψ h) X' := by
        unfold ElocInf
        refine tsum_congr fun X' => ?_
        simp only [Set.indicator, hS, Set.mem_ofPred_eq, and_comm]
    _ = ∑' X : ↥S, Einf P.m₀ Tm j 0 X.1 ψ h := (tsum_subtype S _).symm
    _ = _ := rfl

/-- **(H.5)(1) for `T∞`**: the potential of `liftInf` vanishes at the reference point. -/
theorem IsSFFamily.liftInf_ren_val (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    ∑' X : (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (liftRadius d L N P j)).polys,
      (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (liftRadius d L N P j)).term X.1 (refPt i₀ (nuIdeal L k (ν k) j) X.1) = 0 := by
  have hνj := nuIdeal_pos' (L := L) hF.coeff.nu_pos j
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  have key : ∀ X : (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (liftRadius d L N P j)).polys,
      (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (liftRadius d L N P j)).term X.1 (refPt i₀ (nuIdeal L k (ν k) j) X.1) =
      Einf P.m₀ Tm j 0 X.1 (constInf (Pi.single i₀ 1)) (constInf (Pi.single i₀ 1)) := by
    intro X
    show termLInf Tm P.m₀ j i₀ _ _ X.1 (refPt i₀ (nuIdeal L k (ν k) j) X.1) = _
    rw [refPt_eq_pack, hF.termLInf_pack_const hd hL hϱ hj1 hjk hsmall hne X.2.1 X.2.2 _ _
      (by rw [← refPt_eq_pack]; exact mem_ball_self hρ0)]
    congr 2
    have : ((nuIdeal L k (ν k) j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
    simp [this]
  rw [tsum_congr key]
  have := ElocInf_eq_tsum_polys (L := L) (m₁ := m₁) (k := k) P Tm j
    (constInf (Pi.single i₀ 1)) (constInf (Pi.single i₀ 1))
  exact this.symm.trans ((hF.renorm j hj1 hjk).val i₀)


/-- **(H.5)(2) for `T∞`**: `∂_b 𝒱 · e = 0` for `liftInf`, from the `h`-derivative condition of
`RenormCond` (differentiation under the sum, `hasFDerivAt_tsum_term`). -/
theorem IsSFFamily.liftInf_ren_b (hE0 : 0 ≤ P.E₀) (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
    (hκ : aEnt d L + 3 ≤ P.κ) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    ∑' X : (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (liftRadius d L N P j)).polys,
      fderiv ℂ ((liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (liftRadius d L N P j)).term X.1) (refPt i₀ (nuIdeal L k (ν k) j) X.1)
        (Pi.single (Sum.inr i₀) 1) = 0 := by
  have hνj := nuIdeal_pos' (L := L) hF.coeff.nu_pos j
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  have hP := hF.premisesCoreInf hd hL hϱ hκ hj1 hjk hsmall hne
  set T := liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
    (liftRadius d L N P j) with hT
  set νj := nuIdeal L k (ν k) j with hνjdef
  set e : Fin N → ℂ := Pi.single i₀ 1 with he
  let Aop : ∀ X : T.polys, (Fin N → ℂ) →L[ℂ] Cfg d N X.1 := fun X => bLin X.1 νj
  have hD := hasFDerivAt_tsum_term hP hρ0 hE0 Aop hνj (fun X => norm_bLin_le X.1 hνj.le) e
  have hS := summable_fderiv_comp hP hρ0 hE0 Aop (fun X => norm_bLin_le X.1 hνj.le)
  -- the sum agrees with `ElocInf` near `e`
  have hcfg : ∀ (X : T.polys) (h : Fin N → ℂ),
      refPt i₀ νj X.1 + Aop X (h - e) = pack X.1 (fun _ => e) ((νj : ℂ) • h) := by
    intro X h
    funext idx
    cases idx with
    | inl p => simp [Aop, bLin_apply_inl, pack, refPt, he]
    | inr i =>
      simp only [Pi.add_apply, Aop, bLin_apply_inr, refPt, pack, Sum.elim_inr, Pi.smul_apply,
        Pi.sub_apply, smul_eq_mul]
      ring
  have hev : (fun h : Fin N → ℂ => ElocInf P.m₀ Tm j 0 (constInf e) (constInf h)) =ᶠ[nhds e]
      fun z : Fin N → ℂ => ∑' X : T.polys, T.term X.1 (refPt i₀ νj X.1 + Aop X (z - e)) := by
    have hball : ball e (liftRadius d L N P j / νj) ∈ nhds e := ball_mem_nhds _ (by positivity)
    filter_upwards [hball] with h hh
    rw [ElocInf_eq_tsum_polys]
    refine tsum_congr fun X => ?_
    have hmem : pack X.1 (fun _ => e) ((νj : ℂ) • h) ∈ ball (refPt i₀ νj X.1)
        (liftRadius d L N P j) := by
      rw [← hcfg X h, mem_ball, dist_eq_norm, add_sub_cancel_left]
      rw [mem_ball, dist_eq_norm] at hh
      calc ‖Aop X (h - e)‖ ≤ νj * ‖h - e‖ :=
            (bLin X.1 νj |>.le_opNorm _).trans
              (mul_le_mul_of_nonneg_right (norm_bLin_le X.1 hνj.le) (norm_nonneg _))
        _ < νj * (liftRadius d L N P j / νj) := mul_lt_mul_of_pos_left hh hνj
        _ = liftRadius d L N P j := by field_simp
    show Einf P.m₀ Tm j 0 X.1 (constInf e) (constInf h) = termLInf Tm P.m₀ j i₀ νj
      (liftRadius d L N P j) X.1 (refPt i₀ νj X.1 + Aop X (h - e))
    rw [hcfg X h, hF.termLInf_pack_const hd hL hϱ hj1 hjk hsmall hne X.2.1 X.2.2 _ _ hmem]
    congr 2
    have : ((νj : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
    simp only [← hνjdef]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hg := hD.congr_of_eventuallyEq hev
  have hdh := (hF.renorm j hj1 hjk).dh i₀ hνj
  have hap := (ContinuousLinearMap.apply ℂ ℂ e).map_tsum hS
  simp only [ContinuousLinearMap.apply_apply] at hap
  rw [hg.fderiv, hap] at hdh
  have hL_e : ∀ X : T.polys, ((fderiv ℂ (T.term X.1) (refPt i₀ νj X.1)).comp (Aop X)) e =
      (νj : ℂ) * fderiv ℂ (T.term X.1) (refPt i₀ νj X.1) (Pi.single (Sum.inr i₀) 1) := by
    intro X
    simp only [ContinuousLinearMap.comp_apply]
    have : Aop X e = (νj : ℂ) • (Pi.single (Sum.inr i₀) 1 : Cfg d N X.1) := by
      funext idx
      cases idx with
      | inl p => simp [Aop, bLin_apply_inl]
      | inr i =>
        simp only [Aop, bLin_apply_inr, Pi.smul_apply, smul_eq_mul, he]
        by_cases h : i = i₀
        · subst h; simp
        · simp [h]
    rw [this, map_smul, smul_eq_mul]
  rw [tsum_congr hL_e, tsum_mul_left] at hdh
  have : ((νj : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
  exact (mul_eq_zero.1 hdh).resolve_left this


/-- **(H.5)(3) for `T∞`**: `∑_{y'} ∂_{ψ(y')} 𝓔 · e = 0` for `liftInf`, from the `ψ`-derivative
condition of `RenormCond`. -/
theorem IsSFFamily.liftInf_ren_psi (hE0 : 0 ≤ P.E₀) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hϱ : bgR0 d L ≤ ϱ) (hκ : aEnt d L + 3 ≤ P.κ) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    ∑' X : (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (liftRadius d L N P j)).polys,
      ∑ x : ↥X.1, tensA i₀ (nuIdeal L k (ν k) j) X.1
        ((liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
          (liftRadius d L N P j)).term X.1) x = 0 := by
  have hνj := nuIdeal_pos' (L := L) hF.coeff.nu_pos j
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  have hP := hF.premisesCoreInf hd hL hϱ hκ hj1 hjk hsmall hne
  set T := liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
    (liftRadius d L N P j) with hT
  set νj := nuIdeal L k (ν k) j with hνjdef
  set e : Fin N → ℂ := Pi.single i₀ 1 with he
  let Aop : ∀ X : T.polys, ℂ →L[ℂ] Cfg d N X.1 := fun X => tLin X.1 i₀
  have hD := hasFDerivAt_tsum_term hP hρ0 hE0 Aop one_pos (fun X => norm_tLin_le X.1 i₀) 0
  have hS := summable_fderiv_comp hP hρ0 hE0 Aop (fun X => norm_tLin_le X.1 i₀)
  have hcfg : ∀ (X : T.polys) (t : ℂ),
      refPt i₀ νj X.1 + Aop X (t - 0) = pack X.1 (fun _ => (1 + t) • e) ((νj : ℂ) • e) := by
    intro X t
    funext idx
    cases idx with
    | inl p =>
      obtain ⟨x, i⟩ := p
      simp only [Pi.add_apply, Aop, tLin_apply, psiDir_inl, refPt, pack, Sum.elim_inl, sub_zero,
        Pi.smul_apply, smul_eq_mul, he]
      by_cases h : i = i₀
      · subst h; simp
      · simp [h]
    | inr i =>
      simp [Aop, tLin_apply, psiDir_inr, refPt, pack, he]
  have hev : (fun t : ℂ => ElocInf P.m₀ Tm j 0 (constInf ((1 + t) • e)) (constInf e)) =ᶠ[nhds 0]
      fun z : ℂ => ∑' X : T.polys, T.term X.1 (refPt i₀ νj X.1 + Aop X (z - 0)) := by
    have hball : ball (0 : ℂ) (liftRadius d L N P j) ∈ nhds (0 : ℂ) := ball_mem_nhds _ hρ0
    filter_upwards [hball] with t ht
    rw [ElocInf_eq_tsum_polys]
    refine tsum_congr fun X => ?_
    have hmem : pack X.1 (fun _ => (1 + t) • e) ((νj : ℂ) • e) ∈ ball (refPt i₀ νj X.1)
        (liftRadius d L N P j) := by
      rw [← hcfg X t, mem_ball, dist_eq_norm, add_sub_cancel_left]
      rw [mem_ball, dist_zero_right] at ht
      calc ‖Aop X (t - 0)‖ ≤ 1 * ‖t - 0‖ :=
            ((Aop X).le_opNorm _).trans
              (mul_le_mul_of_nonneg_right (norm_tLin_le X.1 i₀) (norm_nonneg _))
        _ < liftRadius d L N P j := by rw [sub_zero, one_mul]; exact ht
    show Einf P.m₀ Tm j 0 X.1 (constInf ((1 + t) • e)) (constInf e) = termLInf Tm P.m₀ j i₀ νj
      (liftRadius d L N P j) X.1 (refPt i₀ νj X.1 + Aop X (t - 0))
    rw [hcfg X t, hF.termLInf_pack_const hd hL hϱ hj1 hjk hsmall hne X.2.1 X.2.2 _ _ hmem]
    congr 2
    have : ((νj : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
    simp only [← hνjdef]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hg := hD.congr_of_eventuallyEq hev
  have hdp := (hF.renorm j hj1 hjk).dpsi i₀
  rw [hg.hasDerivAt.deriv] at hdp
  have hap := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).map_tsum hS
  simp only [ContinuousLinearMap.apply_apply] at hap
  rw [hap] at hdp
  rw [← hdp]
  refine tsum_congr fun X => ?_
  simp only [ContinuousLinearMap.comp_apply, Aop, tLin_apply, one_smul, psiDir, map_sum]
  rfl

end Pack

end Balaban.SmallField.Def6
