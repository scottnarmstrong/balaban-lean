module

public import Balaban.LargeField.Def7Variants
public import Balaban.LargeField.Budget.LemmaB
import Mathlib.Tactic.Linarith

/-!
# Def-7, consequences (Lemma II.6.3 and the restriction facts of §II.6.3) — DRAFT

* `IsRep.mem_repClass`: a represented density lies in the class `𝓡_k(𝖼)`.
* `D2SF.toFlat`, `D9Coeff.toFlat`: (D2) ⇒ (D2♭) and (D9) ⇒ (D9♭) (the mass range `ν_k ≤ ν̄`
  implies `ν_k ≤ 1`; §II.6.3, audit P2-01).
* `Rep.gpost_eq_gpre`, `Rep.rg_ripe`: the hypothesis (Rg) of LF-2 holds for the budgets of a
  representation (Lemma II.6.3 (d), "(Rg) of LF-2 is then … an identity plus (S3)", §II.6.4): at
  the non-kept components `G = G^pre` by Definition II.5.11, at the kept ones it is the pinned
  exponent (D4) and the kept exponent bound `γ - log C_dec ≥ A'_3 λ̂^{p_R}` of (S3).
* `Rep.lf2Hyp`: the abstract history `LF2Hyp` of every history of a representation (Lemma II.6.3
  (d): "the hypotheses of LF-2 not involving `R` hold for every representation"), with (B) from
  Lemma B (`lemmaB_recursive`), for horizons `K ≤ top`.
* `Rep.budget_of_LF2`, `Rep.budgetPre_of_LF2`, `Rep.budgetFlat_of_LF2`: LF-2 (i), (ii) give
  (D6), (H6′)^pre and (H6♭) for a representation (the source's (D6) is LF-2's conclusion,
  §II.6.4).
* `Rep.tau_le_Gpost`, `Rep.p2_le_Gpost`, `Rep.p2_le_Gpost_flat`: Lemma II.6.3 (c): under (D6),
  `G_k(Z) ≥ τ_{k+1} ≥ 2 p₂(β_k)`; under (H6♭), `G_k(Z) ≥ p₂(β_{k₀})`.
* `Rep.budgetFlat_of_budget`, `IsRep.toFlat`: Lemma IV.2.1 (transfer): `IsRep_{k₀}` implies
  `IsRep^♭_{k₀}` for the same representation.
Lemma II.6.3 (a) ("(D4) implies (D5)") is `Rep.opBound_of_data` (`Def7Counts`).  Lemma II.6.3 (b)
(the sum over the localized histories with labels) is not formalized: the landed Lemma II.5.15
(`sum_inv_logC_le_one`) sums over unlabelled localized histories without the kept decorations.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7

open MeasureTheory Balaban RegionHistory

section Class

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {P6 : SmallField.Def6.Consts} {C7 : Consts7} {β ν : ℝ} {hv : EuclideanSpace ℝ (Fin N)}
  {k : ℕ} {ϱ : ℝ} {hM6 : M = S.L ^ (P6.m₀ + C7.m₁)} {hkK : k ≤ K}

/-- A represented density family lies in the class `𝓡_k(𝖼)`. -/
theorem IsRep.mem_repClass {F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ}
    {ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
      (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ}
    (h : IsRep S R k0 K M N geo cs P P6 C7 β ν hv k hM6 hkK F ρ) :
    ρ ∈ RepClass S R k0 K M N geo cs P P6 C7 β ν hv k ϱ hM6 hkK :=
  ⟨F, h⟩

end Class

section SF

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P6 : SmallField.Def6.Consts}
  {sf : SFData d L m₁ k N ϱ}

theorem nuBar_le_one (hP : P6.Admissible d L) : P6.νbar ≤ 1 := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have h2 : ((L : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL)
  have := hP.νbar_le
  nlinarith

/-- **(D2) ⇒ (D2♭)** (§II.6.3 (iii), audit P2-01): a member of Def-6 with `ν_k ≤ ν̄` satisfies the
clauses of Def-6 with the mass range `ν_k ≤ 1`. -/
theorem D2SF.toFlat (h : D2SF P6 sf (fun _ => 1)) : SFFlat P6 sf := by
  obtain ⟨ρsf, hF⟩ := h.sfClass
  exact
    { admissible := hF.admissible
      coeff :=
        { flow := hF.coeff.flow
          beta_gt := hF.coeff.beta_gt
          nu_pos := hF.coeff.nu_pos
          nu_le := hF.coeff.nu_le.trans (nuBar_le_one hF.admissible)
          a_ge := hF.coeff.a_ge
          a_lt := hF.coeff.a_lt }
      torus := ⟨ρsf, fun N₁ _ => hF.torus N₁⟩
      torusIndep := hF.torusIndep
      renorm := hF.renorm
      rTerms := h.rTerms }

/-- **(D9) ⇒ (D9♭)** for admissible constants (`ν̄ ≤ 7/8 L^{-2} ≤ 1`). -/
theorem D9Coeff.toFlat {k0 : ℕ} (h : D9Coeff P6 k0 sf) (hP : P6.Admissible d L) :
    D9Flat P6 sf :=
  ⟨h.beta_gt, h.nu_pos, h.nu_le.trans (nuBar_le_one hP)⟩

end SF

/-! ### The hypotheses (Rg) and the abstract history of LF-2 -/

section LF2

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  (rep : Rep S n R k0 K M N geo cs P k)

/-- At a component that is not kept, the budget is the pre-`R` budget (Definition II.5.11). -/
theorem Rep.gpost_eq_gpre (A : LabHist S n R k0 K) {j : ℕ} (c : A.H.Comp j)
    (h : ¬ A.H.IsKeptEvent j c) : rep.Gpost A j c = rep.Gpre A j c := by
  cases j with
  | zero => exact (A.H.F.isEmpty_comp_zero.false c).elim
  | succ j =>
    simp only [Rep.Gpost, Rep.Gpre, RegionHistory.budgetPost, RegionHistory.budgetPre,
      RegionHistory.Gpost, RegionHistory.Gpre, RegionHistory.kappa, RegionHistory.logC, h,
      ite_false, add_zero]

/-- **(Rg), kept ripe components** (Lemma II.6.3 (d), §II.6.4): with the pinned exponent (D4) and
the kept exponent bound of (S3), `G^pre_j - C_R λ̂_j^{2d+1} + A'_3 λ̂_j^{p_R} ≤ G_j`. -/
theorem Rep.rg_ripe {top : ℕ} (hpin : D4Pin top rep) {A : LabHist S n R k0 K}
    (hA : A ∈ rep.hist) {j : ℕ} (hj1 : 1 ≤ j) (hjt : j < top) (hj0 : j ≤ k0) (c : A.H.Comp j)
    (hc : c.1 ∉ A.H.rem j) (hr : S.Ripe j (A.H.bk j c)) :
    rep.Gpre A j c - S.CR * S.lam j ^ (2 * S.d + 1) + S.A3' * S.lam j ^ S.pR ≤
      rep.Gpost A j c := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hkept : A.H.IsKeptEvent (j + 1) c := ⟨hj1, hj0, hr⟩
  have hpinc := hpin A hA (j + 1) hj1 hjt c ⟨hj1, hj0, hr⟩ hc
  have hg := rep.KD.gam_ge (j + 1) (A.lab (j + 1) c.1)
  simp only [Rep.Gpost, Rep.Gpre, RegionHistory.budgetPost, RegionHistory.budgetPre,
    RegionHistory.Gpost, RegionHistory.Gpre, RegionHistory.kappa, RegionHistory.logC, hkept,
    ite_true, BudgetConsts.budgetG]
  simp only [Rep.keptExp, hpinc, Rep.kappaPreH, Rep.kappaH, Rep.decor]
  linarith

open Classical in
/-- The budget handed to LF-2: `G_j` at the scales `j < top` carrying the data of the
representation, and the value forced by (Rg) at the others (they are not read by the conclusions
of LF-2 at the scales `< top`). -/
noncomputable def Rep.Gtrunc (top : ℕ) (A : LabHist S n R k0 K) : ∀ j, A.H.Comp j → ℝ :=
  fun j c => if j < top then rep.Gpost A j c else
    if A.H.IsKeptEvent j c then
      rep.Gpre A j c - S.CR * S.lam j ^ (2 * S.d + 1) + S.A3' * S.lam j ^ S.pR
    else rep.Gpre A j c

theorem Rep.gtrunc_of_lt {top : ℕ} (A : LabHist S n R k0 K) {j : ℕ} (c : A.H.Comp j)
    (h : j < top) : rep.Gtrunc top A j c = rep.Gpost A j c := by
  simp [Rep.Gtrunc, h]

/-- **The abstract history of LF-2 of a history of a representation** (Lemma II.6.3 (d),
§I.5.7): the region history with its bookkeeping, `G^pre` the pre-`R` budget of the
representation, `G` its budget below `top`; (B) is Lemma B (`lemmaB_recursive`), (Rg) is
`Rep.rg_ripe` and Definition II.5.11. -/
noncomputable def Rep.lf2Hyp (B : BudgetSetup S P) (ok : S.Ok) {top : ℕ} (hpin : D4Pin top rep)
    (hKtop : K ≤ top) (A : LabHist S n R k0 K) (hA : A ∈ rep.hist) : LF2Hyp S n k0 K :=
  A.H.toLF2Hyp A.adm (rep.Gpre A) (rep.Gtrunc top A)
    (fun j hj Z' => by
      have hb := A.H.lemmaB_recursive B ok (rep.keptExp A) (rep.decor A) j hj Z'
      have he : ∑ c ∈ A.H.parts j Z', rep.Gtrunc top A j c =
          ∑ c ∈ A.H.parts j Z', rep.Gpost A j c :=
        Finset.sum_congr rfl fun c _ => rep.gtrunc_of_lt A c (by omega)
      rw [he]
      exact hb)
    (fun j hj1 hj0 c hc hr => by
      by_cases ht : j < top
      · rw [rep.gtrunc_of_lt A c ht]
        exact rep.rg_ripe hpin hA hj1 ht hj0 c hc hr
      · have hk : A.H.IsKeptEvent j c := ⟨hj1, hj0, hr⟩
        simp [Rep.Gtrunc, ht, hk])
    (fun j hj1 hj0 c hc hr => by
      have hk : ¬ A.H.IsKeptEvent j c := fun h => hr h.2.2
      by_cases ht : j < top
      · rw [rep.gtrunc_of_lt A c ht]
        exact rep.gpost_eq_gpre A c hk
      · simp [Rep.Gtrunc, ht, hk])
    (fun j hj c => by
      have hk : ¬ A.H.IsKeptEvent j c := fun h => by have := h.2.1; omega
      by_cases ht : j < top
      · rw [rep.gtrunc_of_lt A c ht]
        exact rep.gpost_eq_gpre A c hk
      · simp [Rep.Gtrunc, ht, hk])

/-- **LF-2 (i) for a representation: (D6)** (§II.6.4: "(D6) for `rep'` is LF-2 (i)"): under the
conditions `S.Good` of LF-2, the hypotheses of Lemma B, the pinned exponents (D4) and a horizon
`K ≤ top`, every history of the representation satisfies (H6′) at the scale `1 ≤ k ≤ k₀`. -/
theorem Rep.budget_of_LF2 (G : S.Good) (B : BudgetSetup S P) {top : ℕ} (hpin : D4Pin top rep)
    (hKtop : K ≤ top) (hk1 : 1 ≤ k) (hk0 : k ≤ k0) (hkK : k ≤ K) (hkt : k < top) :
    D6Budget rep := by
  intro A hA c
  have h := (G.window_budget ((rep.lf2Hyp B G.ok hpin hKtop A hA).toCounterHist G.ok) k hk1 hk0
    hkK).2 c.1 (fun h' => c.2 ((A.H.mem_remC k c.1).mp h'))
  have hG : ((rep.lf2Hyp B G.ok hpin hKtop A hA).toCounterHist G.ok).G k c.1 =
      rep.Gpost A k c.1 := rep.gtrunc_of_lt A c.1 hkt
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  rw [← hG]
  exact h2

/-- **LF-2 (i) for a representation: (H6′)^pre** (the budget clause of `IsRep^pre_k`). -/
theorem Rep.budgetPre_of_LF2 (G : S.Good) (B : BudgetSetup S P) {top : ℕ}
    (hpin : D4Pin top rep) (hKtop : K ≤ top) (hk1 : 1 ≤ k) (hk0 : k ≤ k0) (hkK : k ≤ K) :
    D6Pre rep := by
  intro A hA c
  exact (G.window_budget ((rep.lf2Hyp B G.ok hpin hKtop A hA).toCounterHist G.ok) k hk1 hk0
    hkK).1 c

/-- **LF-2 (ii) for a representation: (H6♭)** at `k₀ ≤ k ≤ K`, with the horizon conditions of
LF-2 for `k̂_f = khat`. -/
theorem Rep.budgetFlat_of_LF2 (G : S.Good) (B : BudgetSetup S P) {top : ℕ}
    (hpin : D4Pin top rep) (hKtop : K ≤ top) {khat : ℕ} (hk0K : k0 ≤ K) (hKk : K ≤ khat)
    (hH1 : (khat : ℝ) - k0 < S.lam k0) (hH2 : S.lam khat ≤ S.d / 2 * S.lam k0 + S.cH)
    (hk0k : k0 ≤ k) (hk1 : 1 ≤ k) (hkK : k ≤ K) (hkt : k < top) : D6Flat khat rep := by
  intro A hA c
  have h := G.frozen_budget ((rep.lf2Hyp B G.ok hpin hKtop A hA).toCounterHist G.ok) hk0K hKk hH1
    hH2 k hk0k hk1 hkK c.1 (fun h' => c.2 ((A.H.mem_remC k c.1).mp h'))
  have hG : ((rep.lf2Hyp B G.ok hpin hKtop A hA).toCounterHist G.ok).G k c.1 =
      rep.Gpost A k c.1 := rep.gtrunc_of_lt A c.1 hkt
  unfold CounterHist.H6flat at h
  rw [hG] at h
  exact h

/-- **Lemma II.6.3 (c), first inequality**: under (D6), `G_k(Z) ≥ τ_{t^*(Z)} ≥ τ_{k+1}`. -/
theorem Rep.tau_le_Gpost (G : S.Good) (h : D6Budget rep) {A : LabHist S n R k0 K}
    (hA : A ∈ rep.hist) (c : PostComp A k) : S.tau (k + 1) ≤ rep.Gpost A k c.1 := by
  obtain ⟨h1, h2⟩ := h A hA c
  have ht := G.ok.tau_mono (show k + 1 ≤ S.tStar (S.postBook k0 k (A.H.bk k c.1)) from h1)
  have hs := G.ok.sigma_nonneg k
  have hl : 0 ≤ (S.postBook k0 k (A.H.bk k c.1)).len := by
    rw [RegionHistory.postBook_len, A.H.bk_len]; exact (A.H.spine k c.1).length_nonneg
  have hW := G.ok.W_nonneg (k + 1) (S.tStar (S.postBook k0 k (A.H.bk k c.1)))
  have hn : (0 : ℝ) ≤ ((S.postBook k0 k (A.H.bk k c.1)).nu : ℝ) := Nat.cast_nonneg _
  have hb := G.bank_nonneg (S.postBook k0 k (A.H.bk k c.1))
  have : 0 ≤ 2 * S.sigma k * (S.postBook k0 k (A.H.bk k c.1)).len := by positivity
  linarith

/-- **Lemma II.6.3 (c)** (the threshold of (1.31), `ℓ = 2`): under (D6), with the running constants
satisfying (I.2) and the bookkeeping on the a priori `λ̂` (`λ̂_0 ≥ 3`),
`G_k(Z) ≥ τ_{k+1} = 2A₂ λ̂_{k+1}^{p₂} ≥ 2 p₂(β_k)`. -/
theorem Rep.p2_le_Gpost (G : S.Good) (h : D6Budget rep) {β ν a ε : ℝ} {nRun : ℕ → ℝ}
    (hrun : RunningHyp S.d S.L β ν a ε P.beta nRun)
    (hlam : ∀ j, S.lam j = lamHat S.d S.L β a j) (h3 : 3 ≤ lamHat S.d S.L β a 0)
    {A : LabHist S n R k0 K} (hA : A ∈ rep.hist) (c : PostComp A k) :
    2 * p2Run S.A2 S.p2 P.beta k ≤ rep.Gpost A k c.1 := by
  have h1 := hrun.p2Run_le G.ok.A2_pos.le S.p2 h3 k
  have h2 := rep.tau_le_Gpost G h hA c
  unfold Setting.tau at h2
  rw [hlam (k + 1)] at h2
  have hθ := hrun.theta_nonneg
  have hm : lamHat S.d S.L β a k ≤ lamHat S.d S.L β a (k + 1) := by
    unfold lamHat; push_cast; nlinarith
  have h0 : 0 ≤ lamHat S.d S.L β a k := by have := hrun.lamHat_mono k; linarith
  have hp : lamHat S.d S.L β a k ^ S.p2 ≤ lamHat S.d S.L β a (k + 1) ^ S.p2 :=
    pow_le_pow_left₀ h0 hm _
  have hA2 := G.ok.A2_pos
  nlinarith

/-- **Lemma II.6.3 (c)** for `IsRep^♭` (the frozen threshold, `ℓ = 1`, the repaired P6 Theorem 4):
under (H6♭), `G_k(Z) ≥ A₂ λ̂_{k₀}^{p₂} ≥ p₂(β_{k₀})`. -/
theorem Rep.p2_le_Gpost_flat (G : S.Good) {khat : ℕ} (h : D6Flat khat rep) {β ν a ε : ℝ}
    {nRun : ℕ → ℝ} (hrun : RunningHyp S.d S.L β ν a ε P.beta nRun)
    (hlam : ∀ j, S.lam j = lamHat S.d S.L β a j) (h3 : 3 ≤ lamHat S.d S.L β a 0)
    {A : LabHist S n R k0 K} (hA : A ∈ rep.hist) (c : PostComp A k) :
    p2Run S.A2 S.p2 P.beta k0 ≤ rep.Gpost A k c.1 := by
  have h1 := hrun.p2Run_le G.ok.A2_pos.le S.p2 h3 k0
  have h2 := h A hA c
  rw [hlam k0] at h2
  have hs := G.ok.sigma_nonneg k
  have hl : 0 ≤ (A.H.bk k c.1).len := by
    rw [A.H.bk_len]; exact (A.H.spine k c.1).length_nonneg
  have hW := G.ok.W_nonneg (k + 1) khat
  have : 0 ≤ 2 * S.sigma k * (A.H.bk k c.1).len := by positivity
  linarith

/-- **(H6′) at `k₀` implies (H6♭) at `k₀`** for a representation (the transfer of Part I §I.5.6,
(B.20), (Λ11); Lemma IV.2.1). -/
theorem Rep.budgetFlat_of_budget (G : S.Good) (B : BudgetSetup S P) {top : ℕ}
    (hpin : D4Pin top rep) (hKtop : K ≤ top) (hkt : k < top) (hk : k = k0) {khat : ℕ}
    (hk0 : k0 ≤ khat) (hH1 : (khat : ℝ) - k0 < S.lam k0)
    (hH2 : S.lam khat ≤ S.d / 2 * S.lam k0 + S.cH) (h : D6Budget rep) : D6Flat khat rep := by
  subst hk
  intro A hA c
  have hpost : ((rep.lf2Hyp B G.ok hpin hKtop A hA).toCounterHist G.ok).PostH6 k c.1 := by
    have hG : ((rep.lf2Hyp B G.ok hpin hKtop A hA).toCounterHist G.ok).G k c.1 =
        rep.Gpost A k c.1 := rep.gtrunc_of_lt A c.1 hkt
    obtain ⟨h1, h2⟩ := h A hA c
    refine ⟨h1, ?_⟩
    rw [hG]
    exact h2
  have h := G.transfer ((rep.lf2Hyp B G.ok hpin hKtop A hA).toCounterHist G.ok) hk0 hH1 hH2 c.1
    hpost
  have hG : ((rep.lf2Hyp B G.ok hpin hKtop A hA).toCounterHist G.ok).G k c.1 =
      rep.Gpost A k c.1 := rep.gtrunc_of_lt A c.1 hkt
  unfold CounterHist.H6flat at h
  rw [hG] at h
  exact h

end LF2

section Transfer

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {P6 : SmallField.Def6.Consts} {C7 : Consts7} {β ν : ℝ} {hv : EuclideanSpace ℝ (Fin N)}
  {k : ℕ} {ϱ : ℝ} {hM6 : M = S.L ^ (P6.m₀ + C7.m₁)} {hkK : k ≤ K}

/-- **Lemma IV.2.1 (transfer): `IsRep_{k₀}` implies `IsRep^♭_{k₀}`** for the same representation
(the window states are derived data, discarded by `(T7)`): the clauses (D1), (D3)-(D5), (D7), (D8)
are the same, (D2) ⇒ (D2♭), (D9) ⇒ (D9♭), and (D6) ⇒ (H6♭) by the transfer of Part I §I.5.6,
under the conditions of LF-2 (`S.Good`, Lemma B), a horizon `K ≤ k₀ + 1`, and the horizon
conditions of LF-2 for `k̂_f = khat`. -/
theorem IsRep.toFlat {F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ}
    {ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
      (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ}
    (h : IsRep S R k0 K M N geo cs P P6 C7 β ν hv k hM6 hkK F ρ) (hk : k = k0) (G : S.Good)
    (B : BudgetSetup S P) (hK : K ≤ k + 1) {khat : ℕ} (hk0 : k0 ≤ khat)
    (hH1 : (khat : ℝ) - k0 < S.lam k0) (hH2 : S.lam khat ≤ S.d / 2 * S.lam k0 + S.cH) :
    IsRepFlat S R k0 K M N geo cs P P6 C7 β ν hv k khat hM6 hkK F ρ where
  range := hk.ge
  coh := h.coh
  field := h.field
  complete := h.complete
  form := h.form
  sfData := h.sfData.toFlat
  pin := h.pin
  opBound := h.opBound
  budget := fun nK _ => (F.lf nK).budgetFlat_of_budget G B (h.pin nK) hK (Nat.lt_succ_self k) hk
    hk0 hH1 hH2 (h.budget nK)
  bdry := h.bdry
  coherent := h.coherent
  coeff := h.coeff.toFlat (by obtain ⟨_, hF⟩ := h.sfData.sfClass; exact hF.admissible)

end Transfer

end Balaban.LargeField.Def7
