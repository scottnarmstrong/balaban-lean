/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6InfTail

/-!
# The bridge Def-6 to I-6 from `T∞`: the second moment and `SumConds`

* `momentSeq_eq`: the second-moment sum of the `n`-th torus of the sequence is the sum, over the
  small polymers of `T∞`, of their contributions `Sinf` plus the tail `tailAt`;
* `IsSFFamily.tendsto_momentSeq`: along the tori, `momentSum` converges to the relative-pair sum of
  `T∞` (dominated convergence from the counting weight; CLASS-RULINGS Q-B (1), Q-C (2));
* `IsSFFamily.liftInf_moment`: that sum vanishes, by the thermodynamic condition of `RenormCond`;
* `IsSFFamily.sumCondsInf`: `SumConds` for `liftInf`; `IsSFFamily.bridgeInf`: with `premisesCoreInf`,
  for every family that `RepresentsInf` the class term of `T∞`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

/-- The second-moment sum of the `n`-th torus of the sequence. -/
noncomputable def momentSeq (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (P : Consts)
    (j : ℕ) (i₀ i₁ : Fin N) (n : ℕ) : ℂ :=
  haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  momentSum P.m₀ (Tm (torusSeq L P.m₀ n)) j i₀ i₁

open Classical in
/-- The part of the second moment of the `n`-th torus carried by the small polymers of `T∞`. -/
noncomputable def fnSeq (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (P : Consts) (j : ℕ)
    (i₀ i₁ : Fin N) (νj ρ : ℝ) (n : ℕ) (X' : Finset (Fin d → ℤ)) : ℂ :=
  if ((0 : Fin d → ℤ) ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') ∧
      GoodAt L m₁ k P.m₀ j X' n ∧ SmallAt L m₁ k P j X' n
  then Sinf Tm P j i₀ i₁ νj ρ X' else 0

open Classical in
/-- The limit function: the contribution of the polymers of `T∞`. -/
noncomputable def gInf (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (P : Consts) (j : ℕ)
    (i₀ i₁ : Fin N) (νj ρ : ℝ) (X' : Finset (Fin d → ℤ)) : ℂ :=
  if (0 : Fin d → ℤ) ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X'
  then Sinf Tm P j i₀ i₁ νj ρ X' else 0

open Classical in
/-- **The second moment of the `n`-th torus is the sum over the small polymers of `T∞` plus the
tail.** -/
theorem momentSeq_eq (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) (n : ℕ) :
    momentSeq Tm P j i₀ i₁ n =
      ∑' X', fnSeq Tm P j i₀ i₁ (nuIdeal L k (ν k) j) (liftRadius d L N P j) n X' +
        tailAt (ν := ν) Tm P j i₀ i₁ n := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  have hrad := liftRadius_spec (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀ hn.hsmall
  have ctx := hF.liftCtx (torusSeq L P.m₀ n) hn.hd hn.hL hn.hϱ hn.hj1 hn.hjk hρ0 hrad
  have h1 : momentSeq Tm P j i₀ i₁ n =
      ∑ X' ∈ shapesAt L m₁ k P j n, SnSeq Tm P j i₀ i₁ (nuIdeal L k (ν k) j)
        (liftRadius d L N P j) n X' := by
    unfold momentSeq SnSeq shapesAt Sn
    exact ctx.momentSum_shapes (torusSeq_dvd P.m₀ n) hne
  rw [h1, ← Finset.sum_filter_add_sum_filter_not (shapesAt L m₁ k P j n)
    (fun X' => SmallAt L m₁ k P j X' n)]
  have hinf : ∀ X' : Finset (Fin d → ℤ), X' ∈ shapesAt L m₁ k P j n → SmallAt L m₁ k P j X' n →
      InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' := by
    intro X' hX hs
    have hzs := zsmall_of_smallAt hn.hjk hX hs
    have hg := (mem_shapesAt.1 hX).2
    exact Filter.eventually_atTop.2 ⟨n, fun n' hn' => goodAt_of_small hn.hjk hg hzs hn'⟩
  congr 1
  rw [tsum_eq_sum (s := (shapesAt L m₁ k P j n).filter (fun X' => SmallAt L m₁ k P j X' n))]
  · refine Finset.sum_congr rfl fun X' hX' => ?_
    have hX := (Finset.mem_filter.1 hX').1
    have hs := (Finset.mem_filter.1 hX').2
    have hm := mem_shapesAt.1 hX
    have hI := hinf X' hX hs
    unfold fnSeq
    rw [ite_eq_left ⟨⟨hm.1, hI⟩, hm.2, hs⟩]
    exact Sn_eq_Sinf hF hn.hj1 hn.hjk hm.1 hI hm.2 i₁ _ _ (zsmall_of_smallAt hn.hjk hX hs)
  · intro X' hX'
    unfold fnSeq
    by_contra hne'
    rw [ite_eq_right] at hne'
    · exact hne' rfl
    · intro h
      exact hX' (Finset.mem_filter.2 ⟨mem_shapesAt.2 ⟨h.1.1, h.2.1⟩, h.2.2⟩)


open Classical in
/-- The bound of the contribution of a polymer of `T∞` to the second moment. -/
theorem norm_gInf_le (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) (X' : Finset (Fin d → ℤ)) :
    ‖gInf Tm P j i₀ i₁ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X'‖ ≤
      ((liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (liftRadius d L N P j)).polys.indicator
        (fun X => (16 * diamA d L P.m₀ m₁ ^ 2 * P.E₀ / liftRadius d L N P j ^ 2) *
          wt P.κ X (dInf L m₁ k P.m₀ j X)) X') := by
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  have hP := hF.premisesCoreInf hn.hd hn.hL hn.hϱ hn.hκ hn.hj1 hn.hjk hn.hsmall hne
  unfold gInf
  by_cases h : (0 : Fin d → ℤ) ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X'
  · rw [ite_eq_left h, Set.indicator_of_mem (show X' ∈ (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀
      (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys from h)]
    exact hP.norm_moment_term_le hρ0 hn.hE0 (X := X') h
  · rw [ite_eq_right h, Set.indicator_of_notMem (show X' ∉ (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀
      (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys from h)]
    simp


/-- A polymer of `T∞` is eventually good and small along the tori. -/
theorem eventually_good_small (hd : 0 < d) {j : ℕ} (hjk : j ≤ k) (P : Consts)
    {X' : Finset (Fin d → ℤ)} (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') :
    ∀ᶠ n in atTop, GoodAt L m₁ k P.m₀ j X' n ∧ SmallAt L m₁ k P j X' n := by
  have hA := diamA_pos hd (NeZero.pos L) P.m₀ m₁
  set B : ℝ := ((X'.card : ℝ) * ((L : ℝ) ^ j) ^ d) ^ 2 with hB
  set T : ℝ := 4 * (diamA d L P.m₀ m₁ * (1 + B) + ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) with hT
  filter_upwards [hX, Filter.eventually_ge_atTop ⌈T⌉₊] with n hn hnT
  refine ⟨hn, ?_⟩
  unfold SmallAt
  have h1 : sizeSeq L m₁ k P.m₀ j X' n ≤ B := sizeSeq_le hjk hn
  have h2 : T < (n : ℝ) + 1 := by
    have := Nat.le_ceil T
    have h3 : (⌈T⌉₊ : ℝ) ≤ n := by exact_mod_cast hnT
    linarith
  have h4 : (n : ℝ) + 1 ≤ ((torusSeq L P.m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) := by
    have h := succ_le_torusSeq (L := L) P.m₀ n
    have h2 : torusSeq L P.m₀ n ≤ torusSeq L P.m₀ n * L ^ m₁ * L ^ (k - j) := by
      have h1' : 1 ≤ L ^ m₁ := Nat.one_le_pow _ _ (NeZero.pos L)
      have h2' : 1 ≤ L ^ (k - j) := Nat.one_le_pow _ _ (NeZero.pos L)
      calc torusSeq L P.m₀ n = torusSeq L P.m₀ n * 1 * 1 := by ring
        _ ≤ _ := by gcongr
    exact_mod_cast h.trans h2
  have h5 : 4 * (diamA d L P.m₀ m₁ * (1 + sizeSeq L m₁ k P.m₀ j X' n) +
      ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) ≤ T := by
    rw [hT]
    have := mul_le_mul_of_nonneg_left (show 1 + sizeSeq L m₁ k P.m₀ j X' n ≤ 1 + B by linarith)
      hA.le
    linarith
  linarith

open Classical in
theorem tendsto_fnSeq (hn : MomNum d L N k j ϱ P) (i₀ i₁ : Fin N) (νj ρ : ℝ)
    (X' : Finset (Fin d → ℤ)) :
    Tendsto (fun n => fnSeq Tm P j i₀ i₁ νj ρ n X') atTop
      (nhds (gInf Tm P j i₀ i₁ νj ρ X')) := by
  have hd0 : 0 < d := by have := hn.hd; omega
  by_cases h : (0 : Fin d → ℤ) ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X'
  · have hev := eventually_good_small (L := L) (m₁ := m₁) (k := k) hd0 hn.hjk P h.2
    have : gInf Tm P j i₀ i₁ νj ρ X' = Sinf Tm P j i₀ i₁ νj ρ X' := by
      unfold gInf; rw [ite_eq_left h]
    rw [this]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn'
    unfold fnSeq
    rw [ite_eq_left ⟨h, hn'.1, hn'.2⟩]
  · have : gInf Tm P j i₀ i₁ νj ρ X' = 0 := by unfold gInf; rw [ite_eq_right h]
    rw [this]
    refine tendsto_const_nhds.congr fun n => ?_
    unfold fnSeq
    rw [ite_eq_right (fun h' => h h'.1)]


open Classical in
/-- **The thermodynamic limit of the second moment** (CLASS-RULINGS Q-B equation (1), Q-C (2)): along
the tori of the sequence the second-moment sums `momentSum` converge to the relative-pair sum of the
infinite-volume family `T∞`. -/
theorem IsSFFamily.tendsto_momentSeq (hF : IsSFFamily P β ν a Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    Tendsto (momentSeq Tm P j i₀ i₁) atTop
      (nhds (∑' X' : Finset (Fin d → ℤ),
        gInf Tm P j i₀ i₁ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X')) := by
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  have hP := hF.premisesCoreInf hn.hd hn.hL hn.hϱ hn.hκ hn.hj1 hn.hjk hn.hsmall hne
  set S : Set (Finset (Fin d → ℤ)) := (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀
    (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys with hS
  set bd : Finset (Fin d → ℤ) → ℝ := fun X => (16 * diamA d L P.m₀ m₁ ^ 2 * P.E₀ /
    liftRadius d L N P j ^ 2) * wt P.κ X (dInf L m₁ k P.m₀ j X) with hbd
  have hsum : Summable (S.indicator bd) := by
    rw [← summable_subtype_iff_indicator]
    exact hP.count_summable.mul_left _
  have hbd0 : ∀ X, 0 ≤ bd X := fun X => by
    have := hn.hE0
    have : 0 ≤ wt P.κ X (dInf L m₁ k P.m₀ j X) := by unfold wt; positivity
    simp only [hbd]; positivity
  have hdct := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (bound := S.indicator bd)
    hsum (fun X' => tendsto_fnSeq (Tm := Tm) (P := P) (j := j) hn i₀ i₁ _ _ X')
    (Eventually.of_forall fun n X' => by
      have hg := norm_gInf_le hF hn hne X'
      by_cases h : (0 : Fin d → ℤ) ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧
          GoodAt L m₁ k P.m₀ j X' n ∧ SmallAt L m₁ k P j X' n
      · have h' : (0 : Fin d → ℤ) ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' :=
          ⟨h.1, h.2.1⟩
        have : fnSeq Tm P j i₀ i₁ (nuIdeal L k (ν k) j) (liftRadius d L N P j) n X' =
            gInf Tm P j i₀ i₁ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X' := by
          unfold fnSeq gInf
          rw [ite_eq_left ⟨h', h.2.2.1, h.2.2.2⟩, ite_eq_left h']
        rw [this]; exact hg
      · have : fnSeq Tm P j i₀ i₁ (nuIdeal L k (ν k) j) (liftRadius d L N P j) n X' = 0 := by
          unfold fnSeq
          rw [ite_eq_right]
          rintro ⟨h1, h2, h3⟩
          exact h ⟨h1.1, h1.2, h2, h3⟩
        rw [this, norm_zero]
        exact Set.indicator_nonneg (fun X _ => hbd0 X) X')
  have hsum2 := hdct.add (tendsto_tailAt (ν := ν) hF hn hne)
  rw [add_zero] at hsum2
  refine hsum2.congr fun n => ?_
  exact (momentSeq_eq hF hn hne n).symm


theorem momentSum_congr {m₀ j : ℕ} {i₀ i₁ : Fin N} {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]
    (h : N₁ = N₂) :
    momentSum m₀ (Tm N₁) j i₀ i₁ = momentSum m₀ (Tm N₂) j i₀ i₁ := by
  subst h; rfl

open Classical in
/-- **(H.5)(4) for `T∞`** (CLASS-RULINGS Q-B, Q-C): the second moment of the infinite-volume family
vanishes, from the thermodynamic condition `RenormCond.moment` and the tail lemma. -/
theorem IsSFFamily.liftInf_moment (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    ∑' X : (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (liftRadius d L N P j)).polys,
      ∑ x : ↥X.1, ∑ x' : ↥X.1, tensB i₀ i₁ (nuIdeal L k (ν k) j) X.1
        ((liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
          (liftRadius d L N P j)).term X.1) x x' * (∑ μ, (((x.1 μ - x'.1 μ : ℤ) : ℂ)) ^ 2) = 0 := by
  have hlim := hF.tendsto_momentSeq hn hne
  have hmom := (hF.renorm j hn.hj1 hn.hjk).moment i₀ i₁ hne.symm
  have hφ : Tendsto (fun n : ℕ => torusSeq L P.m₀ n - 1) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    have := succ_le_torusSeq (L := L) P.m₀ n
    simp only [id]; omega
  have hcomp := hmom.comp hφ
  have hsub : Tendsto (momentSeq Tm P j i₀ i₁) atTop (nhds 0) := by
    refine hcomp.congr fun n => ?_
    have h1 : torusSeq L P.m₀ n - 1 + 1 = torusSeq L P.m₀ n := by
      have := succ_le_torusSeq (L := L) P.m₀ n; omega
    have : NeZero (torusSeq L P.m₀ n - 1 + 1) := ⟨Nat.succ_ne_zero _⟩
    have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
    simp only [Function.comp, momentSeq]
    exact momentSum_congr h1
  have huniq := tendsto_nhds_unique hlim hsub
  rw [← huniq]
  set S : Set (Finset (Fin d → ℤ)) := (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀
    (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys with hS
  have := tsum_subtype S (fun X' => Sinf Tm P j i₀ i₁ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X')
  unfold gInf
  refine Eq.trans ?_ (this.trans (tsum_congr fun X' => ?_))
  · rfl
  · by_cases h : (0 : Fin d → ℤ) ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X'
    · rw [ite_eq_left h, Set.indicator_of_mem (show X' ∈ S from h)]
    · rw [ite_eq_right h, Set.indicator_of_notMem (show X' ∉ S from h)]


/-- **`SumConds` for the infinite-volume family** (item 5 of the brief): a member of the class
satisfies the renormalization conditions (H.5)(1)-(4) of I-6 on the lifted family `liftInf` of `T∞`:
the first three from the infinite-volume conditions `val`, `dh`, `dpsi` (differentiation under the
sum), the second moment from the thermodynamic condition `moment` and the tail lemma. -/
theorem IsSFFamily.sumCondsInf (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    SumConds (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
      (liftRadius d L N P j)) i₀ i₁ (nuIdeal L k (ν k) j) :=
  ⟨hF.liftInf_ren_val hn.hd hn.hL hn.hϱ hn.hj1 hn.hjk hn.hsmall hne,
    hF.liftInf_ren_b hn.hE0 hn.hd hn.hL hn.hϱ hn.hκ hn.hj1 hn.hjk hn.hsmall hne,
    hF.liftInf_ren_psi hn.hE0 hn.hd hn.hL hn.hϱ hn.hκ hn.hj1 hn.hjk hn.hsmall hne,
    hF.liftInf_moment hn hne⟩

/-- **The bridge from the infinite-volume family**: a term family that represents the class term of
`T∞` (`RepresentsInf`) has the core premises of the termwise I-6 (every field of `PremisesTerm`
except the point-group invariance, whose symmetrization is treated separately) and satisfies the
renormalization conditions `SumConds`. -/
theorem IsSFFamily.bridgeInf (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {T : TermFamily d N}
    (hT : RepresentsInf (L := L) (m₁ := m₁) (k := k) T P Tm j i₀ (nuIdeal L k (ν k) j)
      (liftRadius d L N P j)) :
    PremisesCore T i₀ i₁ (nuIdeal L k (ν k) j) (liftRadius d L N P j) P.E₀ P.κ
      (diamA d L P.m₀ m₁)
      ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
        K0 d L (P.κ - 2)) (liftDomInf P β ν a Tm j i₀) ∧
    SumConds T i₀ i₁ (nuIdeal L k (ν k) j) := by
  subst hT
  exact ⟨hF.premisesCoreInf hn.hd hn.hL hn.hϱ hn.hκ hn.hj1 hn.hjk hn.hsmall hne,
    hF.sumCondsInf hn hne⟩

end Balaban.SmallField.Def6
