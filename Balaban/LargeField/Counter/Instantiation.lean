module

public import Balaban.LargeField.History.FlowBook
public import Balaban.LargeField.Counter.LF2

/-!
# Instantiation of LF-2 for the flow's region history (Part I, §I.5.7)

For a `RegionHistory` whose removed components are ripe, `RegionHistory.toLF2Hyp` is the abstract
history `LF2Hyp` with every geometric field proved:

* `spine_contains`: (3.1), from the spine consistency lemma (Lemma I.4.8, `exists_step_spine`);
* the spine length rule (4.1), the pure-shadow rule, the clock rules and the window-state rules
  (T1)-(T5) in `book_rule` (`Setting.nextBook_rule`);
* `seed_pos`: every component of `Z^pre_{k+1}` contains an old part or a new cube
  (Lemma I.3.7 (a), Lemma I.3.8 and the hull closure).

The remaining fields are the hypotheses of the instantiation: (B) `budget` (Lemma B, Part II) and
(Rg) `rg_ripe`, `rg_nonripe`, `rg_frozen` (LF-4R, Part III), for given reals `Gp`, `G`.
-/

@[expose] public section

namespace Balaban.LargeField

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0)

/-- **Instantiation of LF-2** (§I.5.7): the abstract history `LF2Hyp` of an admissible region
history, with the numbers `G^pre_k(Z)`, `G_k(Z)` given and (B), (Rg) as hypotheses. -/
noncomputable def toLF2Hyp (hadm : H.Admissible) (K : ℕ) (Gp G : ∀ k, H.Comp k → ℝ)
    (budget : ∀ k, k < K → ∀ Z' : H.Comp (k + 1),
      ∑ c ∈ H.parts k Z', G k c + S.g k * (Z'.1 ∩ H.newCubes (k + 1)).card -
        S.cv * S.lam (k + 1) * Z'.1.card ≤ Gp (k + 1) Z')
    (rg_ripe : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k → S.Ripe k (H.bk k c) →
      Gp k c - S.CR * S.lam k ^ (2 * S.d + 1) + S.A3' * S.lam k ^ S.pR ≤ G k c)
    (rg_nonripe : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k → ¬ S.Ripe k (H.bk k c) →
      G k c = Gp k c)
    (rg_frozen : ∀ k, k0 < k → ∀ c : H.Comp k, G k c = Gp k c) : LF2Hyp S n k0 K where
  n_succ := fun k _ => H.F.hnn k
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
  succ := H.succ
  parts := H.parts
  mem_parts := fun k c Z' => by
    rw [H.mem_parts, H.mem_remC]
  Gp := Gp
  G := G
  spine_contains := fun k _ _ c => H.spine_contains k c
  seed_pos := fun k _ Z' => H.seed_pos k Z'
  book_rule := fun k _ Z' => H.book_rule k Z'
  budget := budget
  rg_ripe := fun k hk1 hk2 c hc => rg_ripe k hk1 hk2 c (fun h => hc ((H.mem_remC k c).mpr h))
  rg_nonripe := fun k hk1 hk2 c hc => rg_nonripe k hk1 hk2 c (fun h => hc ((H.mem_remC k c).mpr h))
  rg_frozen := rg_frozen

end RegionHistory

end Balaban.LargeField
