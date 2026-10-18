/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Basic

/-!
# LF-2 (ii) with the counter history truncated at the current scale

The landed `Rep.lf2Hyp` ties the top scale of the counter history to the torus horizon `K`
(`K ≤ top`).  Here the abstract history of LF-2 is built with its top scale `K'` a parameter,
`K' ≤ K`, so the budget at the scale `k` is read from the history truncated at `K' = k`,
independently of `K`.

* `RegionHistory.toLF2HypTrunc`, `Rep.lf2HypTrunc`: the truncated abstract history.
* `Rep.budgetFlat_of_LF2_trunc`: (H6♭) at `k₀ ≤ k ≤ K` for any `K`, with `k ≤ k̂`.
* `Rep.budgetFlat_of_budget_trunc`: the transfer (H6′) ⇒ (H6♭) at `k = k₀`, any `K`.
* `IsRep2.toFlat_of_all_horizons`: Lemma IV.2.1 for every torus horizon `K`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K)

/-- The abstract history of LF-2 of an admissible region history, truncated at the scale
`K' ≤ K`. -/
noncomputable def toLF2HypTrunc {K' : ℕ} (hK : K' ≤ K) (hadm : H.Admissible)
    (Gp G : ∀ k, H.Comp k → ℝ)
    (budget : ∀ k, k < K' → ∀ Z' : H.Comp (k + 1),
      ∑ c ∈ H.parts k Z', G k c + S.g k * (Z'.1 ∩ H.newCubes (k + 1)).card -
        S.cv * S.lam (k + 1) * Z'.1.card ≤ Gp (k + 1) Z')
    (rg_ripe : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k → S.Ripe k (H.bk k c) →
      Gp k c - S.CR * S.lam k ^ (2 * S.d + 1) + S.A3' * S.lam k ^ S.pR ≤ G k c)
    (rg_nonripe : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k → ¬ S.Ripe k (H.bk k c) →
      G k c = Gp k c)
    (rg_frozen : ∀ k, k0 < k → ∀ c : H.Comp k, G k c = Gp k c) : LF2Hyp S n k0 K' where
  n_succ := fun k hk => H.F.hnn k (lt_of_lt_of_le hk hK)
  Zp := H.Zp
  Zp_zero := H.F.Zp_zero
  newCubes := H.newCubes
  rem := H.remC
  rem_empty := fun k hk => by
    classical
    simp [remC, H.rem_empty k hk]
  spine := H.spine
  bk := H.bk
  bk_len := H.bk_len
  rem_ripe := fun k c hc => hadm k c ((H.mem_remC k c).mp hc)
  IsSucc := H.IsSucc
  parts := H.parts
  mem_parts := fun k c Z' => by
    rw [H.mem_parts]
    constructor
    · rintro ⟨h, e⟩
      exact ⟨fun h' => h ((H.mem_remC k c).mp h'), e⟩
    · rintro ⟨h, e⟩
      exact ⟨fun h' => h ((H.mem_remC k c).mpr h'), e⟩
  Gp := Gp
  G := G
  spine_contains := fun k _ hk c => H.spine_contains k (hk.trans hK) c
  seed_pos := fun k hk Z' => H.seed_pos (lt_of_lt_of_le hk hK) Z'
  book_rule := fun k hk Z' => H.book_rule (lt_of_lt_of_le hk hK) Z'
  budget := budget
  rg_ripe := fun k hk1 hk2 c hc => rg_ripe k hk1 hk2 c (fun h => hc ((H.mem_remC k c).mpr h))
  rg_nonripe := fun k hk1 hk2 c hc => rg_nonripe k hk1 hk2 c (fun h => hc ((H.mem_remC k c).mpr h))
  rg_frozen := rg_frozen

end RegionHistory

namespace Def7

section Trunc

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  (rep : Rep S n R k0 K M N geo cs P k)

/-- The abstract history of LF-2 of a history of a representation, truncated at `K' ≤ K` with
`K' ≤ top` (the scales `j < K'` carry the data of the representation). -/
noncomputable def Rep.lf2HypTrunc (B : BudgetSetup S P) (ok : S.Ok) {top K' : ℕ}
    (hpin : D4Pin top rep) (hK : K' ≤ K) (hKtop : K' ≤ top) (A : LabHist S n R k0 K)
    (hA : A ∈ rep.hist) : LF2Hyp S n k0 K' :=
  A.H.toLF2HypTrunc hK A.adm (rep.Gpre A) (rep.Gtrunc top A)
    (fun j hj Z' => by
      have hb := A.H.lemmaB_recursive B ok (rep.keptExp A) (rep.decor A) j (by omega) Z'
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

/-- **LF-2 (ii) for a representation, truncated counter history: (H6♭)** at `k₀ ≤ k ≤ K`,
`k ≥ 1`, with no relation between `K` and `k̂`: only `k ≤ k̂` and `k < top` are used (the counter
history is truncated at the scale `k`). -/
theorem Rep.budgetFlat_of_LF2_trunc (G : S.Good) (B : BudgetSetup S P) {top : ℕ}
    (hpin : D4Pin top rep) {khat : ℕ}
    (hH1 : (khat : ℝ) - k0 < S.lam k0) (hH2 : S.lam khat ≤ S.d / 2 * S.lam k0 + S.cH)
    (hk0k : k0 ≤ k) (hk1 : 1 ≤ k) (hkK : k ≤ K) (hkhat : k ≤ khat) (hkt : k < top) :
    D6Flat khat rep := by
  intro A hA c
  have h := G.frozen_budget ((rep.lf2HypTrunc B G.ok hpin hkK hkt.le A hA).toCounterHist G.ok)
    hk0k hkhat hH1 hH2 k hk0k hk1 le_rfl c.1 (fun h' => c.2 ((A.H.mem_remC k c.1).mp h'))
  have hG : ((rep.lf2HypTrunc B G.ok hpin hkK hkt.le A hA).toCounterHist G.ok).G k c.1 =
      rep.Gpost A k c.1 := rep.gtrunc_of_lt A c.1 hkt
  unfold CounterHist.H6flat at h
  rw [hG] at h
  exact h

/-- **(H6′) at `k₀` implies (H6♭) at `k₀`**, for every torus horizon `K ≥ k₀`. -/
theorem Rep.budgetFlat_of_budget_trunc (G : S.Good) (B : BudgetSetup S P) {top : ℕ}
    (hpin : D4Pin top rep) (hkK : k ≤ K) (hkt : k < top) (hk : k = k0) {khat : ℕ}
    (hk0 : k0 ≤ khat) (hH1 : (khat : ℝ) - k0 < S.lam k0)
    (hH2 : S.lam khat ≤ S.d / 2 * S.lam k0 + S.cH) (h : D6Budget rep) : D6Flat khat rep := by
  subst hk
  intro A hA c
  have hG : ((rep.lf2HypTrunc B G.ok hpin hkK hkt.le A hA).toCounterHist G.ok).G k c.1 =
      rep.Gpost A k c.1 := rep.gtrunc_of_lt A c.1 hkt
  have hpost : ((rep.lf2HypTrunc B G.ok hpin hkK hkt.le A hA).toCounterHist G.ok).PostH6 k c.1 := by
    obtain ⟨h1, h2⟩ := h A hA c
    refine ⟨h1, ?_⟩
    rw [hG]
    exact h2
  have h := G.transfer ((rep.lf2HypTrunc B G.ok hpin hkK hkt.le A hA).toCounterHist G.ok) hk0
    hH1 hH2 c.1 hpost
  unfold CounterHist.H6flat at h
  rw [hG] at h
  exact h

end Trunc

end Def7

namespace Def7v2

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7
  RegionHistory

section Class

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {P6 : Def6.Consts} {C7 : Consts7} {β ν : ℝ} {hv : EuclideanSpace ℝ (Fin N)} {rH : ℝ}
  {k : ℕ} {ϱ : ℝ} {hM6 : M = S.L ^ (P6.m₀ + C7.m₁)} {hkK : k ≤ K}
  {F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ}
  {ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
    (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ}
  {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ C7.m₁ k N} {vc : CorrCoef S.d}

/-- **Lemma IV.2.1 (transfer), second version, every torus horizon `K`**: `IsRep2_{k₀}` implies
`IsRepFlat2_{k₀}` for the same representation, with no relation between `K` and `k₀`. -/
theorem IsRep2.toFlat_of_all_horizons
    (h : IsRep2 S R k0 K M N geo cs P P6 C7 β ν hv rH k hM6 hkK F ρ St vc)
    (hk : k = k0) (G : S.Good) (B : BudgetSetup S P) {khat : ℕ} (hk0 : k0 ≤ khat)
    (hH1 : (khat : ℝ) - k0 < S.lam k0) (hH2 : S.lam khat ≤ S.d / 2 * S.lam k0 + S.cH) :
    IsRepFlat2 S R k0 K M N geo cs P P6 C7 β ν hv rH k khat hM6 hkK F ρ St vc where
  range := hk.ge
  coh := h.coh
  field := h.field
  complete := h.complete
  form := h.form
  corr := h.corr
  sfData := h.sfData.toFlat2
  pin := h.pin
  opBound := h.opBound
  budget := fun nK _ => (F.lf nK).budgetFlat_of_budget_trunc G B (h.pin nK) hkK
    (Nat.lt_succ_self k) hk hk0 hH1 hH2 (h.budget nK)
  bdry := h.bdry
  coherent := h.coherent
  coeff := h.coeff.toFlat (by obtain ⟨_, hF⟩ := h.sfData.sfClass; exact hF.admissible)

end Class

end Def7v2

end Balaban.LargeField
