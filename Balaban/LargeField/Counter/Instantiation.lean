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

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K)

/-- **Instantiation of LF-2** (§I.5.7): the abstract history `LF2Hyp` of an admissible region
history, with the numbers `G^pre_k(Z)`, `G_k(Z)` given and (B), (Rg) as hypotheses. -/
noncomputable def toLF2Hyp (hadm : H.Admissible) (Gp G : ∀ k, H.Comp k → ℝ)
    (budget : ∀ k, k < K → ∀ Z' : H.Comp (k + 1),
      ∑ c ∈ H.parts k Z', G k c + S.g k * (Z'.1 ∩ H.newCubes (k + 1)).card -
        S.cv * S.lam (k + 1) * Z'.1.card ≤ Gp (k + 1) Z')
    (rg_ripe : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k → S.Ripe k (H.bk k c) →
      Gp k c - S.CR * S.lam k ^ (2 * S.d + 1) + S.A3' * S.lam k ^ S.pR ≤ G k c)
    (rg_nonripe : ∀ k, 1 ≤ k → k ≤ k0 → ∀ c : H.Comp k, c.1 ∉ H.rem k → ¬ S.Ripe k (H.bk k c) →
      G k c = Gp k c)
    (rg_frozen : ∀ k, k0 < k → ∀ c : H.Comp k, G k c = Gp k c) : LF2Hyp S n k0 K where
  n_succ := fun k hk => H.F.hnn k hk
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
  spine_contains := fun k _ hk c => H.spine_contains k hk c
  seed_pos := fun k hk Z' => H.seed_pos hk Z'
  book_rule := fun k hk Z' => H.book_rule hk Z'
  budget := budget
  rg_ripe := fun k hk1 hk2 c hc => rg_ripe k hk1 hk2 c (fun h => hc ((H.mem_remC k c).mpr h))
  rg_nonripe := fun k hk1 hk2 c hc => rg_nonripe k hk1 hk2 c (fun h => hc ((H.mem_remC k c).mpr h))
  rg_frozen := rg_frozen

/-- (H-T) implies the size condition `n_k ≥ 4ρ_k + 21` of Lemma I.2.10 (d). -/
theorem _root_.Balaban.LargeField.Setting.Ok.four_rho_le {S : Setting} (ok : S.Ok) {k m : ℕ}
    (h : 4 * S.numax k * (S.crit k + S.omega k) + 4 ≤ m) : 4 * S.rho k + 21 ≤ m := by
  have h1 := ok.one_le_numax k
  have h2 : S.crit k = 2 * S.rho k + 10 := rfl
  have h3 : 4 * 1 * (S.crit k + S.omega k) ≤ 4 * S.numax k * (S.crit k + S.omega k) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
  omega

/-- **Lemma I.4.8** (point spines) under (H-T): for `1 ≤ k ≤ k₀` the spine of a component `Z` of
`Z^pre_k` is a point iff `Z` is small of side `≤ crit_k`, and then `Z` is a box with spine
`{c(Z)}`. -/
theorem spine_point_iff_HT (ok : S.Ok)
    (hT : ∀ k, 1 ≤ k → k ≤ k0 → 4 * S.numax k * (S.crit k + S.omega k) + 4 ≤ n k)
    {k : ℕ} (hk1 : 1 ≤ k) (hk0 : k ≤ k0) (hkK : k ≤ K) (Z : H.Comp k) :
    (H.spine k Z).length = 0 ↔
      IsSmall (Z.1 : Set (Torus S.d (n k))) ∧ side (Z.1 : Set (Torus S.d (n k))) ≤ S.crit k :=
  H.spine_point_iff hk1 hk0 hkK (ok.four_rho_le (hT k hk1 hk0)) Z

end RegionHistory

end Balaban.LargeField
