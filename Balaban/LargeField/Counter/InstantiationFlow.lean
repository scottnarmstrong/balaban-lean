module

public import Balaban.LargeField.Counter.Instantiation
public import Balaban.LargeField.Counter.FlowHorizon
public import Balaban.LargeField.History.LocalHistory

/-!
# LF-2 for the flow (Part I, §I.5.7)

`RegionHistory.flow_counter` assembles the instantiation: the region history of the flow gives
the abstract history `LF2Hyp` (`toLF2Hyp`, with (B) and (Rg) as hypotheses), the horizon
conditions come from Lemma I.5.6 (`FlowSeq.hLambda_of_flow'`), and `LF2` gives the conclusion of
Theorem I.5.4 up to `k̂_f`.
-/

@[expose] public section

namespace Balaban.LargeField

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}

/-- **LF-2 for the flow**: for the flow data `F` (with `S` its counter), an admissible region
history up to `K = k_f`, and the hypotheses (B), (Rg), the conclusion of Theorem I.5.4 holds
up to `k̂_f`. -/
theorem flow_counter (G : S.Good) (F : FlowSeq) (hS : F.Matches S) (H : RegionHistory S n R F.k0 F.kf)
    (hadm : H.Admissible) (hkf : 1 ≤ F.kf)
    (hΛ12 : ((F.d : ℝ) + 3) / 2 ≤ S.lam F.k0 * (1 - 1 / (2 * Real.log F.L)))
    (hgen : F.beta F.k0 * F.nu F.k0 ≤ 1 → 2 * (F.L : ℝ) ^ 2 ≤ F.beta F.k0)
    (Gp G' : ∀ k, H.Comp k → ℝ)
    (budget : ∀ k, k < F.kf → ∀ Z' : H.Comp (k + 1),
      ∑ c ∈ H.parts k Z', G' k c + S.g k * (Z'.1 ∩ H.newCubes (k + 1)).card -
        S.cv * S.lam (k + 1) * Z'.1.card ≤ Gp (k + 1) Z')
    (rg_ripe : ∀ k, 1 ≤ k → k ≤ F.k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k → S.Ripe k (H.bk k c) →
      Gp k c - S.CR * S.lam k ^ (2 * S.d + 1) + S.A3' * S.lam k ^ S.pR ≤ G' k c)
    (rg_nonripe : ∀ k, 1 ≤ k → k ≤ F.k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k →
      ¬ S.Ripe k (H.bk k c) → G' k c = Gp k c)
    (rg_frozen : ∀ k, F.k0 < k → ∀ c : H.Comp k, G' k c = Gp k c) :
    CounterConclusion
      ((H.toLF2Hyp hadm Gp G' budget rg_ripe rg_nonripe rg_frozen).toCounterHist G.ok)
      F.kfhat := by
  obtain ⟨hH1, hH2⟩ := F.hLambda_of_flow' hS hkf hΛ12 hgen
  exact LF2 G (H.toLF2Hyp hadm Gp G' budget rg_ripe rg_nonripe rg_frozen)
    (F.k0_lt_kf hkf hgen).le F.kfhat_bounds.1 hH1 hH2

end RegionHistory

end Balaban.LargeField
