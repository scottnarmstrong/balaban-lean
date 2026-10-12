/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6BridgeInfDict

/-!
# The bridge Def-6 to I-6 from the infinite-volume family `T∞`: the core premises

* `liftInf`: the centred `ℤ^d` term family of `T∞` (polymers: `InfPoly` containing the origin;
  size `dInf`; term `termLInf`); `RepresentsInf` says a family is `liftInf`;
* `liftDomInf`: its data domain;
* `IsSFFamily.premisesCoreInf`: every field of the termwise I-6 premises except the point-group
  invariance, with the constants of the finite-torus bridge `IsSFFamily.premisesCore`.  The
  analytic fields are those of `premisesCore` (radius `liftRadius`, isotropic tube).
-/


@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation Balaban.SmallField Filter Metric Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The centred `ℤ^d` term family of `T∞` at the scale `j`**: the polymers of `T∞` containing the
origin, size `dInf`, term `termLInf`. -/
noncomputable def liftInf (P : Consts) (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
    (j : ℕ) (i₀ : Fin N) (νj ρ : ℝ) : TermFamily d N where
  polys := {X' | (0 : Site d) ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X'}
  dist := dInf L m₁ k P.m₀ j
  term := termLInf Tm P.m₀ j i₀ νj ρ

/-- **`T` represents the class term of `T∞` at the scale `j`**: `T` is the lifted family. -/
def RepresentsInf (T : TermFamily d N) (P : Consts)
    (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (j : ℕ) (i₀ : Fin N) (νj ρ : ℝ) :
    Prop :=
  T = liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ νj ρ

/-- **The data domain of the lifted family of `T∞`**: the configurations `(ψ, b)` such that for
every polymer of `T∞` containing the origin and every torus of the sequence on which it is a
non-winding polymer, the restriction to the polymer extends to torus fields in
`Ξ^c_j(𝔹_j(Y); 1, ε_j)`. -/
def liftDomInf (P : Consts) (β ν a : ℕ → ℝ)
    (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (j : ℕ) (i₀ : Fin N) :
    Set ((Site d → Spin N) × Spin N) :=
  {p | ∀ X' : Finset (Site d), (0 : Site d) ∈ X' →
    InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' → ∀ n : ℕ,
    GoodAt L m₁ k P.m₀ j X' n →
    haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
    ∃ (Ψ h : Fld d L (torusSeq L P.m₀ n) m₁ k N),
      (∀ x ∈ Ypoly (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j X',
        Ψ x = fieldOf j i₀ X' (pack X' p.1 p.2) x ∧
          h x = hOf (nuIdeal L k (ν k) j) X' (pack X' p.1 p.2) x) ∧
      XiDom ((Tm (torusSeq L P.m₀ n)).gs j (Ypoly j X')) (aIdeal L k (a k))
        (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h}

/-- A bound that holds with `d - ε` for all `ε > 0` holds with `d`. -/
theorem le_mul_exp_of_forall {x E κ δ : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → x ≤ E * Real.exp (-κ * (δ - ε))) : x ≤ E * Real.exp (-κ * δ) := by
  have hc : Continuous fun ε : ℝ => E * Real.exp (-κ * (δ - ε)) := by fun_prop
  have ht : Tendsto (fun ε : ℝ => E * Real.exp (-κ * (δ - ε))) (nhdsWithin 0 (Ioi 0))
      (nhds (E * Real.exp (-κ * (δ - 0)))) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [sub_zero] at ht
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => h ε hε)


section Premises

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

omit [NeZero L] in
theorem exists_goodAt {m₀ : ℕ} {X' : Finset (Site d)}
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X') : ∃ n, GoodAt L m₁ k m₀ j X' n :=
  hX.exists

/-- The bound of the term of a torus, with the witness of the data domain only for the polymer
itself (the proof of `LiftCtx.bdd_dom`). -/
theorem LiftCtx.bdd_dom_at [NeZero N₁] {ρ : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
    {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    {Ek : ℝ} (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {X' : Finset (Site d)} (hX' : X' ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j)
    {p : (Site d → Spin N) × Spin N}
    (hwit : ∃ (Ψ h : Fld d L N₁ m₁ k N),
      (∀ x ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X',
        Ψ x = fieldOf j i₀ X' (pack X' p.1 p.2) x ∧
          h x = hOf (nuIdeal L k (ν k) j) X' (pack X' p.1 p.2) x) ∧
      XiDom (Tm.gs j (Ypoly j X')) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        Ψ h) :
    ‖termL Tm j i₀ (nuIdeal L k (ν k) j) ρ X' (pack X' p.1 p.2)‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X')) := by
  obtain ⟨h0, hnw, hX⟩ := hX'
  by_cases hex : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
      rotCfgL R X' (pack X' p.1 p.2) ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ
  · obtain ⟨R, h1, h2, h3⟩ := hex
    rw [ctx.termL_eq hX h0 hne h1 h2 h3]
    exact ctx.norm_Eaux_le i₀ hX h0 (ctx.mem_xiDom i₀ hX h3)
  · unfold termL
    simp only [hex, dite_false]
    obtain ⟨Ψ, h, hag, hXi⟩ := hwit
    have hloc : Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' (pack X' p.1 p.2) =
        Tm.E j 0 (Ypoly j X') Ψ h := by
      unfold Eaux
      exact (ctx.sf.localE j 0 (Ypoly j X') _ _ _ _
        (fun x hx => ⟨(hag x hx).1.symm, (hag x hx).2.symm⟩))
    rw [hloc]
    exact ctx.sf.boundE j ctx.j1 ctx.jk 0 (Ypoly j X') hX (zero_mem_Ypoly h0) Ψ h hXi


/-- The weight of a shape with `|X'| ≤ C₁ (1 + t)` is at most `C₁² 8! e · e^{-(κ-2) t}` (the
algebra of `liftWt_le`). -/
theorem wt_le_of_card_le {κ C₁ t : ℝ} {X' : Finset (Site d)} (ht0 : 0 ≤ t)
    (hc : (X'.card : ℝ) ≤ C₁ * (1 + t)) :
    wt κ X' t ≤ C₁ ^ 2 * (Nat.factorial 8 * Real.exp 1) * Real.exp (-(κ - 2) * t) := by
  have hcard2 : (X'.card : ℝ) ^ 2 ≤ C₁ ^ 2 * (1 + t) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
  have hpow : (1 + t) ^ 8 ≤ Nat.factorial 8 * Real.exp (1 + t) := by
    have := Real.pow_div_factorial_le_exp (1 + t) (by linarith) 8
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  unfold wt
  have e1 : Real.exp (1 + t) * Real.exp (-(κ - 1) * t) = Real.exp 1 * Real.exp (-(κ - 2) * t) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc (X'.card : ℝ) ^ 2 * (1 + t) ^ 6 * Real.exp (-(κ - 1) * t)
      ≤ C₁ ^ 2 * (1 + t) ^ 2 * (1 + t) ^ 6 * Real.exp (-(κ - 1) * t) := by
        gcongr
    _ = C₁ ^ 2 * (1 + t) ^ 8 * Real.exp (-(κ - 1) * t) := by ring
    _ ≤ C₁ ^ 2 * (Nat.factorial 8 * Real.exp (1 + t)) * Real.exp (-(κ - 1) * t) := by
        gcongr
    _ = C₁ ^ 2 * (Nat.factorial 8 * Real.exp 1) * Real.exp (-(κ - 2) * t) := by
        rw [mul_assoc, mul_assoc, e1]; ring

/-- **Counting for `T∞`** (from (G1), (G2) on a torus on which the finitely many shapes are good):
`∑_{X' ∈ S} |X'|² (1 + d)⁶ e^{-(κ-1) d} ≤ K₀` for every finite set `S` of polymers of `T∞`
containing the origin, `d = dInf`. -/
theorem sum_wt_dInf_le (P : Consts) (hjk : j ≤ k) {κ : ℝ} (hκ : aEnt d L + 3 ≤ κ)
    (S : Finset (Finset (Site d)))
    (hS : ∀ X' ∈ S, (0 : Site d) ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') :
    ∑ X' ∈ S, wt κ X' (dInf L m₁ k P.m₀ j X') ≤
      (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
        K0 d L (κ - 2) := by
  have hev : ∀ᶠ n in atTop, ∀ X' ∈ S, GoodAt L m₁ k P.m₀ j X' n := by
    rw [Filter.eventually_all_finset]
    exact fun X' hX' => (hS X' hX').2
  obtain ⟨n, hn⟩ := hev.exists
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  set Cw := (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) with hCw
  have hC₁0 : 0 ≤ c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d := by
    have : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  calc ∑ X' ∈ S, wt κ X' (dInf L m₁ k P.m₀ j X')
      ≤ ∑ X' ∈ S, Cw * Real.exp (-(κ - 2) * sizeSeq L m₁ k P.m₀ j X' n) := by
        refine Finset.sum_le_sum fun X' hX' => ?_
        have hgood := hn X' hX'
        have hs := sizeSeq_le_dInf hjk hgood
        have hs0 := sizeSeq_nonneg (L := L) (m₁ := m₁) (k := k) P.m₀ j X' n
        have hcard := liftPolys_card_le (P := P)
          (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) hjk (torusSeq_dvd P.m₀ n)
          (X' := X') ⟨(hS X' hX').1, hgood.1, hgood.2⟩
        have hseq : sizeJ (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) P.m₀ j
            (Ypoly (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j X') =
            sizeSeq L m₁ k P.m₀ j X' n := rfl
        rw [hseq] at hcard
        refine (wt_le_of_card_le (C₁ := c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) (by linarith) ?_).trans ?_
        · refine hcard.trans ?_
          exact mul_le_mul_of_nonneg_left (by linarith) hC₁0
        · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
          have haE := aEnt_nonneg d L
          nlinarith
    _ = Cw * ∑ X' ∈ S, Real.exp (-(κ - 2) * sizeSeq L m₁ k P.m₀ j X' n) := by rw [Finset.mul_sum]
    _ ≤ Cw * K0 d L (κ - 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact exp_sum_le_at hjk (torusSeq_dvd P.m₀ n) (by linarith) 0 S fun X' hX' =>
          ⟨(hS X' hX').1, (hn X' hX').1, (hn X' hX').2⟩


section Fam

variable (hF : IsSFFamily P β ν a Tm ρd Ek)
include hF

/-- The tube bound of the term of `T∞`, by the covering size on any torus on which the polymer is a
non-winding polymer. -/
theorem IsSFFamily.termLInf_tube_le (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') {n : ℕ}
    (hn : GoodAt L m₁ k P.m₀ j X' n) {c : Cfg d N X'}
    (hc : c ∈ Tube i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X') :
    ‖termLInf Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X' c‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeSeq L m₁ k P.m₀ j X' n) := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := hF.liftCtx (torusSeq L P.m₀ n) hd hL hϱ hj1 hjk
    (liftRadius_pos (eps_pos hF.admissible.α₀_pos j) i₀)
    (liftRadius_spec (eps_pos hF.admissible.α₀_pos j) i₀ hsmall)
  rw [termLInf_eq hF.torusIndep hj1 hjk i₀ _ _ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2 c]
  exact ctx.bdd_tube hne hn.2 h0 hc

/-- The bound of the term of `T∞` on the data domain, by the covering size on any torus on which
the polymer is a non-winding polymer. -/
theorem IsSFFamily.termLInf_dom_le (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') {n : ℕ}
    (hn : GoodAt L m₁ k P.m₀ j X' n) {p : (Site d → Spin N) × Spin N}
    (hp : p ∈ liftDomInf P β ν a Tm j i₀) :
    ‖termLInf Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X' (pack X' p.1 p.2)‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeSeq L m₁ k P.m₀ j X' n) := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := hF.liftCtx (torusSeq L P.m₀ n) hd hL hϱ hj1 hjk
    (liftRadius_pos (eps_pos hF.admissible.α₀_pos j) i₀)
    (liftRadius_spec (eps_pos hF.admissible.α₀_pos j) i₀ hsmall)
  rw [termLInf_eq hF.torusIndep hj1 hjk i₀ _ _ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2 _]
  exact ctx.bdd_dom_at hne ⟨h0, hn.1, hn.2⟩ (hp X' h0 hX n hn)

/-- Analyticity of the term of `T∞` on the tube. -/
theorem IsSFFamily.termLInf_analytic (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') :
    AnalyticOnNhd ℂ (termLInf Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X')
      (Tube i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X') := by
  obtain ⟨n, hn⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := hF.liftCtx (torusSeq L P.m₀ n) hd hL hϱ hj1 hjk
    (liftRadius_pos (eps_pos hF.admissible.α₀_pos j) i₀)
    (liftRadius_spec (eps_pos hF.admissible.α₀_pos j) i₀ hsmall)
  have e : termLInf Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X' =
      termL (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X' :=
    funext fun c => termLInf_eq hF.torusIndep hj1 hjk i₀ _ _ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2 c
  rw [e]
  exact ctx.analytic hne hn.2 h0

/-- Rotation invariance of the term of `T∞` on the tube. -/
theorem IsSFFamily.termLInf_rot_inv (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    {c : Cfg d N X'} (hc : c ∈ Tube i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X')
    (R : Matrix (Fin N) (Fin N) ℂ) (hR : IsOrth R) (hRb : EntryBd N R)
    (hRc : rotCfgL R X' c ∈ Tube i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X') :
    termLInf Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X' (rotCfgL R X' c) =
      termLInf Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X' c := by
  obtain ⟨n, hn⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := hF.liftCtx (torusSeq L P.m₀ n) hd hL hϱ hj1 hjk
    (liftRadius_pos (eps_pos hF.admissible.α₀_pos j) i₀)
    (liftRadius_spec (eps_pos hF.admissible.α₀_pos j) i₀ hsmall)
  rw [termLInf_eq hF.torusIndep hj1 hjk i₀ _ _ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2,
    termLInf_eq hF.torusIndep hj1 hjk i₀ _ _ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2]
  exact ctx.rot_inv hne hn.2 h0 hc hR hRb hRc


/-- **`IsSFFamily.premisesCoreInf`**: a member of the class supplies the premises of the termwise
I-6 at each scale `1 ≤ j ≤ k` for the lifted family `liftInf` of `T∞` (the polymers obtained by
stabilization along the tori), except the point-group invariance: the geometric fields from
(G1), (G2), (G5) transported along the tori on which the polymers do not wind, the analytic fields
from the class on any such torus (`Einf_eq_torus`), with the tube radius `ρ = liftRadius`. -/
theorem IsSFFamily.premisesCoreInf (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ)
    (hκ : aEnt d L + 3 ≤ P.κ) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    PremisesCore (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
      (liftRadius d L N P j)) i₀ i₁ (nuIdeal L k (ν k) j) (liftRadius d L N P j) P.E₀ P.κ
      (diamA d L P.m₀ m₁)
      ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
        K0 d L (P.κ - 2)) (liftDomInf P β ν a Tm j i₀) := by
  have hκ0 : 0 ≤ P.κ := hF.admissible.κ_pos.le
  -- the approximation argument for the sup
  have approx : ∀ {X' : Finset (Site d)} {n₀ : ℕ} (hn₀ : GoodAt L m₁ k P.m₀ j X' n₀) {x : ℝ} (hx0 : 0 ≤ x),
      (∀ n, GoodAt L m₁ k P.m₀ j X' n →
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
    nlinarith
  have inst0 : ∀ (X' : Finset (Site d)),
      X' ∈ (liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (liftRadius d L N P j)).polys → ∃ n, GoodAt L m₁ k P.m₀ j X' n :=
    fun X' hX => exists_goodAt hX.2
  have hsumF : ∀ F : Finset ↥(liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀
      (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys,
      ∑ X ∈ F, wt P.κ X.1 (dInf L m₁ k P.m₀ j X.1) ≤
        (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
          K0 d L (P.κ - 2) := by
    intro F
    rw [← Finset.sum_image (f := fun X' => wt P.κ X' (dInf L m₁ k P.m₀ j X'))
      (fun X _ Y _ h => Subtype.ext h)]
    exact sum_wt_dInf_le P hjk hκ _ fun X' hX' => by
      obtain ⟨X, -, rfl⟩ := Finset.mem_image.1 hX'
      exact X.2
  have hsum : Summable fun X : ↥(liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀
      (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys => wt P.κ X.1 (dInf L m₁ k P.m₀ j X.1) :=
    summable_of_sum_le (fun X => by unfold wt; positivity) hsumF
  refine ⟨hne.symm, fun _ hX => hX.1, ?_, ?_, hsum, hsum.tsum_le_of_sum_le hsumF, ?_, ?_, ?_, ?_⟩
  · intro X' hX
    obtain ⟨n, hn⟩ := inst0 X' hX
    exact dInf_nonneg hjk hn
  · intro X' hX x hx
    obtain ⟨n, hn⟩ := inst0 X' hX
    have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
    have := liftPolys_diam (P := P) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) hjk
      (X' := X') ⟨hX.1, hn.1, hn.2⟩ hx
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (diamA_nonneg d L P.m₀ m₁))
    have := sizeSeq_le_dInf hjk hn
    show 1 + sizeSeq L m₁ k P.m₀ j X' n ≤ 1 + dInf L m₁ k P.m₀ j X'
    linarith
  · intro X' hX
    exact hF.termLInf_analytic hd hL hϱ hj1 hjk hsmall hne hX.1 hX.2
  · intro X' hX c hc
    obtain ⟨n, hn⟩ := inst0 X' hX
    exact approx hn (norm_nonneg _) fun n hn =>
      hF.termLInf_tube_le hd hL hϱ hj1 hjk hsmall hne hX.1 hX.2 hn hc
  · intro X' hX p hp
    obtain ⟨n, hn⟩ := inst0 X' hX
    exact approx hn (norm_nonneg _) fun n hn =>
      hF.termLInf_dom_le hd hL hϱ hj1 hjk hsmall hne hX.1 hX.2 hn hp
  · intro X' hX c hc R hR hRb hRc
    exact hF.termLInf_rot_inv hd hL hϱ hj1 hjk hsmall hne hX.1 hX.2 hc R hR hRb hRc

end Fam

end Premises

end Balaban.SmallField.Def6
