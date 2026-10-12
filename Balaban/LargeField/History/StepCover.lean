module

public import Balaban.LargeField.History.StepSpine
public import Balaban.LargeField.History.BoxCover

/-!
# Box covers of the components of `Z^pre_{k+1}` without new cubes (Lemma I.4.10 (a), cover)

Assume every component `Y` of `Z_k` is covered by at most `ν(Y) ≥ 1` boxes of side `≤ cb`.
Then a component `Z'` of `Z^pre_{k+1}` that contains no new cube is covered by at most
`∑ ν(Y)` (over the old parts `Y` of `Z'`) boxes of side `≤ cb'`, where
`⌊(cb + L - 2)/L⌋ + 1 + 8 r ≤ cb'` and the hull threshold `b ≤ cb'`: by round `0` (attribution:
each cube is within `4 r` of an old seed, `shadow_cover`) and the hull rounds (a hulled component
is replaced by its hull box, one box).  This is the cover statement of (T1) (one part) and (T4)
(a merge; the count adds up).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionStep

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ}
  (st : RegionStep d L n0 n1 Rprev Rk)

/-- Cover data of the good old components `Y` (`G Y`): boxes `bx Y` of side `≤ cb`, at most
`ν Y ≥ 1` of them. -/
structure OldCover (G : Finset (Torus d n0) → Prop) (ωk cb : ℕ) (ν : Finset (Torus d n0) → ℕ)
    (bx : Finset (Torus d n0) → Finset (Torus d n0 × (Fin d → ℕ))) : Prop where
  card_le : ∀ Y ∈ comps ωk (finOf st.Z), G Y → (bx Y).card ≤ ν Y
  side_le : ∀ Y ∈ comps ωk (finOf st.Z), G Y → ∀ b ∈ bx Y, ∀ i, b.2 i ≤ cb
  cover : ∀ Y ∈ comps ωk (finOf st.Z), G Y → (Y : Set (Torus d n0)) ⊆ ⋃ b ∈ bx Y, box b.1 b.2
  pos : ∀ Y ∈ comps ωk (finOf st.Z), G Y → 1 ≤ ν Y

/-- All seeds of `C` are old seeds of good components. -/
def AllGood (G : Finset (Torus d n0) → Prop) (ωk : ℕ) (C : Finset (Torus d n1)) : Prop :=
  ∀ a ∈ st.seedsIn ωk C, ∃ Y, a = Sum.inl Y ∧ G Y

/-- The weight of a seed index: `ν Y` for the old seed of `Y`, `0` for a new seed. -/
def wt (ν : Finset (Torus d n0) → ℕ) : SeedIdx d n0 n1 → ℕ
  | .inl Y => ν Y
  | .inr _ => 0

variable {G : Finset (Torus d n0) → Prop} {ωk ω r cb cb' : ℕ} {ν : Finset (Torus d n0) → ℕ}
  {bx : Finset (Torus d n0) → Finset (Torus d n0 × (Fin d → ℕ))}

/-- The cover claim for a set of cubes. -/
def CoverClaim (ωk cb' : ℕ) (ν : Finset (Torus d n0) → ℕ) (C : Finset (Torus d n1)) : Prop :=
  ∃ B : Finset (Torus d n1 × (Fin d → ℕ)), B.card ≤ ∑ a ∈ st.seedsIn ωk C, wt (n1 := n1) ν a ∧
    (∀ b ∈ B, ∀ i, b.2 i ≤ cb') ∧ (C : Set (Torus d n1)) ⊆ ⋃ b ∈ B, box b.1 b.2

theorem wt_pos (hcov : st.OldCover G ωk cb ν bx) {a : SeedIdx d n0 n1} (ha : a ∈ st.idx ωk)
    {Y : Finset (Torus d n0)} (hY : a = Sum.inl Y) (hG : G Y) : 1 ≤ wt (n1 := n1) ν a := by
  subst hY
  exact hcov.pos Y ((st.inl_mem_idx).mp ha) hG

/-- Round `0`. -/
theorem coverClaim_base (hg : StepGeom L n0 n1 ωk ω r Rprev Rk) (hcov : st.OldCover G ωk cb ν bx)
    (hside : (cb + L - 2) / L + 1 + 2 * (4 * r) ≤ cb')
    {C : Finset (Torus d n1)} (hC : C ∈ comps ω (finOf st.Z0))
    (hgood : st.AllGood G ωk C) : st.CoverClaim ωk cb' ν C := by
  classical
  -- the cover of the seed `a`
  let Bs : SeedIdx d n0 n1 → Finset (Torus d n1 × (Fin d → ℕ)) := fun a =>
    match a with
    | .inl Y => (bx Y).image fun b => (fun k => blockMap L n1 b.1 k - ((4 * r : ℕ) : ZMod n1),
        fun k => (b.2 k + L - 2) / L + 1 + 2 * (4 * r))
    | .inr _ => ∅
  refine ⟨(st.seedsIn ωk C).biUnion Bs, ?_, ?_, ?_⟩
  · refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun a ha => ?_)
    obtain ⟨Y0, hY0, hG⟩ := hgood a ha
    subst hY0
    exact (Finset.card_image_le).trans
      (hcov.card_le Y0 ((st.inl_mem_idx).mp (st.mem_seedsIn.mp ha).1) hG)
  · intro b hb i
    obtain ⟨a, ha, hba⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨Y, hY0, hG⟩ := hgood a ha
    subst hY0
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.mp hba
    have := hcov.side_le Y ((st.inl_mem_idx).mp (st.mem_seedsIn.mp ha).1) hG b0 hb0 i
    show (b0.2 i + L - 2) / L + 1 + 2 * (4 * r) ≤ cb'
    have h2 : (b0.2 i + L - 2) / L ≤ (cb + L - 2) / L := Nat.div_le_div_right (by omega)
    omega
  · intro x hx
    obtain ⟨a, ha, y, hy, hd, hl⟩ := st.attr_seed hg (mem_finOf.mp (comp_subset hC hx))
    have hsub := st.sset_subset_of_linked hg hC hx ha hy hl
    have haC : a ∈ st.seedsIn ωk C := st.mem_seedsIn.mpr ⟨ha, hsub⟩
    obtain ⟨Y, hY0, hG⟩ := hgood a haC
    subst hY0
    have hYmem := (st.inl_mem_idx).mp ha
    have hxn : x ∈ nbhd (4 * r) (blockMap L n1 '' (Y : Set (Torus d n0))) := by
      refine mem_nbhd.mpr ⟨y, hy, ?_⟩
      simpa [seedWt] using hd
    have hshadow := shadow_cover hg.hn (bx Y) (fun b => b.1) (fun b => b.2)
      (hcov.cover Y hYmem hG) (4 * r) (Z' := nbhd (4 * r) (blockMap L n1 '' (Y : Set (Torus d n0))))
      subset_rfl hxn
    obtain ⟨b0, hb0, hxb⟩ := Set.mem_iUnion₂.mp hshadow
    refine Set.mem_iUnion₂.mpr ⟨(fun k => blockMap L n1 b0.1 k - ((4 * r : ℕ) : ZMod n1),
      fun k => (b0.2 k + L - 2) / L + 1 + 2 * (4 * r)), Finset.mem_biUnion.mpr ⟨Sum.inl Y, haC, ?_⟩, hxb⟩
    exact Finset.mem_image.mpr ⟨b0, hb0, rfl⟩

/-- A hull round. -/
theorem coverClaim_step (hg : StepGeom L n0 n1 ωk ω r Rprev Rk) (hcov : st.OldCover G ωk cb ν bx)
    {b : ℕ} (hb : b ≤ cb') {X : Set (Torus d n1)} (hZX : st.Z0 ⊆ X)
    (hcont : ∀ C ∈ comps ω (finOf X), ∃ C0 ∈ comps ω (finOf st.Z0), C0 ⊆ C)
    (IH : ∀ C ∈ comps ω (finOf X), st.AllGood G ωk C → st.CoverClaim ωk cb' ν C)
    {C' : Finset (Torus d n1)} (hC' : C' ∈ comps ω (finOf (hullRound ω b X)))
    (hgood : st.AllGood G ωk C') : st.CoverClaim ωk cb' ν C' := by
  classical
  have hω2 := hg.hω2
  set P := (comps ω (finOf X)).filter (fun C => C ⊆ C') with hP
  have hXY : X ⊆ hullRound ω b X := subset_hullRound X
  have hmemP : ∀ C ∈ P, C ∈ comps ω (finOf X) ∧ C ⊆ C' := fun C hC => Finset.mem_filter.mp hC
  have hcoverP : ∀ y ∈ C', ∃ C ∈ P, y ∈ partSet b C := by
    intro y hy
    obtain ⟨C, hC, hCC', hyC⟩ := (hullRound_comp_iff hω2 hC').mp hy
    exact ⟨C, Finset.mem_filter.mpr ⟨hC, hCC'⟩, hyC⟩
  have hseeds : st.seedsIn ωk C' = P.biUnion (st.seedsIn ωk) :=
    st.seedsIn_biUnion hg hZX hXY hC'
  have hdisj : ∀ C ∈ P, ∀ C2 ∈ P, C ≠ C2 → Disjoint (st.seedsIn ωk C) (st.seedsIn ωk C2) :=
    fun C hC C2 hC2 hne => st.seedsIn_disjoint (hmemP C hC).1 (hmemP C2 hC2).1 hne
  have hsumS : ∑ a ∈ st.seedsIn ωk C', wt (n1 := n1) ν a =
      ∑ C ∈ P, ∑ a ∈ st.seedsIn ωk C, wt (n1 := n1) ν a := by
    rw [hseeds, Finset.sum_biUnion]
    exact fun C hC C2 hC2 hne => hdisj C hC C2 hC2 hne
  have hsub_seeds : ∀ C ∈ P, st.seedsIn ωk C ⊆ st.seedsIn ωk C' := by
    intro C hC
    rw [hseeds]
    exact fun a ha => Finset.mem_biUnion.mpr ⟨C, hC, ha⟩
  have hpart : ∀ C ∈ P, ∃ B' : Finset (Torus d n1 × (Fin d → ℕ)),
      B'.card ≤ ∑ a ∈ st.seedsIn ωk C, wt (n1 := n1) ν a ∧ (∀ b ∈ B', ∀ i, b.2 i ≤ cb') ∧
        partSet b C ⊆ ⋃ b ∈ B', box b.1 b.2 := by
    intro C hC
    obtain ⟨hCX, -⟩ := hmemP C hC
    have hgoodC : st.AllGood G ωk C := fun a ha => hgood a (hsub_seeds C hC ha)
    obtain ⟨B0, hB0c, hB0s, hB0cov⟩ := IH C hCX hgoodC
    by_cases hh : IsSmall (C : Set (Torus d n1)) ∧ side (C : Set (Torus d n1)) ≤ b
    · obtain ⟨a, s, hhull, -, hside⟩ := hull_eq_box (Finset.coe_nonempty.mpr (comp_nonempty hCX)) hh.1
      have hsi : ∀ i, s i ≤ cb' := fun i =>
        le_trans (hside ▸ Finset.le_sup (f := s) (Finset.mem_univ i)) (hh.2.trans hb)
      have hpos : 1 ≤ ∑ a ∈ st.seedsIn ωk C, wt (n1 := n1) ν a := by
        have hne := Finset.card_pos.mp (st.seedsIn_card_pos hg (hcont C hCX))
        obtain ⟨a0, ha0⟩ := hne
        have h1 : 1 ≤ wt (n1 := n1) ν a0 := by
          obtain ⟨Y0, hY0, hG0⟩ := hgoodC a0 ha0
          exact st.wt_pos hcov (st.mem_seedsIn.mp ha0).1 hY0 hG0
        exact h1.trans (Finset.single_le_sum (f := fun a => wt (n1 := n1) ν a)
          (fun _ _ => Nat.zero_le _) ha0)
      refine ⟨{(a, s)}, by simpa using hpos, by simpa using hsi, ?_⟩
      intro y hy
      refine Set.mem_iUnion₂.mpr ⟨(a, s), Finset.mem_singleton_self _, ?_⟩
      rw [← hhull] at *
      rcases hy with hy | ⟨-, -, hy⟩
      · rw [← hhull]; exact subset_hull _ hy
      · exact hy
    · have hpe : partSet b C = (C : Set (Torus d n1)) := by
        ext y
        constructor
        · rintro (h | ⟨h1, h2, -⟩)
          · exact h
          · exact absurd ⟨h1, h2⟩ hh
        · exact fun h => Or.inl h
      exact ⟨B0, hB0c, hB0s, by rw [hpe]; exact hB0cov⟩
  choose! B' hB' using hpart
  refine ⟨P.biUnion B', ?_, ?_, ?_⟩
  · rw [hsumS]
    exact (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun C hC => (hB' C hC).1)
  · intro b hb i
    obtain ⟨C, hC, hbC⟩ := Finset.mem_biUnion.mp hb
    exact (hB' C hC).2.1 b hbC i
  · intro y hy
    obtain ⟨C, hC, hyC⟩ := hcoverP y hy
    obtain ⟨b0, hb0, hyb⟩ := Set.mem_iUnion₂.mp ((hB' C hC).2.2 hyC)
    exact Set.mem_iUnion₂.mpr ⟨b0, Finset.mem_biUnion.mpr ⟨C, hC, hb0⟩, hyb⟩

/-- The cover claim along all hull rounds. -/
theorem coverClaim_iter (hg : StepGeom L n0 n1 ωk ω r Rprev Rk) (hcov : st.OldCover G ωk cb ν bx)
    (hside : (cb + L - 2) / L + 1 + 2 * (4 * r) ≤ cb') {b : ℕ} (hb : b ≤ cb') (t : ℕ) :
    ∀ C ∈ comps ω (finOf ((hullRound ω b)^[t] st.Z0)),
      st.AllGood G ωk C → st.CoverClaim ωk cb' ν C := by
  induction t with
  | zero => exact fun C hC hn => st.coverClaim_base hg hcov hside hC hn
  | succ t ih =>
    intro C' hC' hn
    rw [Function.iterate_succ_apply'] at hC'
    refine st.coverClaim_step hg hcov hb (iter_mono_of_le st.Z0 (Nat.zero_le t)) ?_ ih hC' hn
    intro C hC
    exact iter_comp_contains hg.hω2 st.Z0 t hC

/-- **Lemma I.4.10 (a), cover** for (T1) and (T4): a component `Z'` of `Z^pre_{k+1}` with no new
cube is covered by `∑_{Y ⊂ Z'} ν(Y)` boxes of side `≤ cb'`. -/
theorem exists_step_cover (hg : StepGeom L n0 n1 ωk ω r Rprev Rk) (hcov : st.OldCover G ωk cb ν bx)
    (hside : (cb + L - 2) / L + 1 + 2 * (4 * r) ≤ cb') {crit : Option ℕ}
    (hcrit : ∀ b, crit = some b → b ≤ cb') {Z' : Finset (Torus d n1)}
    (hZ' : Z' ∈ comps ω (finOf (st.Zpre ω crit))) (hnew : st.newIn Z' = ∅)
    (hG : ∀ Y ∈ st.oldIn ωk Z', G Y) :
    ∃ B : Finset (Torus d n1 × (Fin d → ℕ)), B.card ≤ ∑ Y ∈ st.oldIn ωk Z', ν Y ∧
      (∀ b ∈ B, ∀ i, b.2 i ≤ cb') ∧ (Z' : Set (Torus d n1)) ⊆ ⋃ b ∈ B, box b.1 b.2 := by
  classical
  have hn : st.AllGood G ωk Z' := by
    intro a ha
    rw [seedsIn_eq] at ha
    simp only [Finset.mem_union, Finset.mem_image] at ha
    rcases ha with ⟨Y, hY, rfl⟩ | ⟨q', hq', h⟩
    · exact ⟨Y, rfl, hG Y hY⟩
    · rw [hnew] at hq'; simp at hq'
  have hclaim : st.CoverClaim ωk cb' ν Z' := by
    cases crit with
    | none => exact st.coverClaim_base hg hcov hside hZ' hn
    | some b => exact st.coverClaim_iter hg hcov hside (hcrit b rfl) _ Z' hZ' hn
  obtain ⟨B, h1, h2, h3⟩ := hclaim
  refine ⟨B, ?_, h2, h3⟩
  refine h1.trans (le_of_eq ?_)
  rw [seedsIn_eq, Finset.sum_union, Finset.sum_image (fun _ _ _ _ h => Sum.inl_injective h),
    Finset.sum_image (fun _ _ _ _ h => Sum.inr_injective h)]
  · simp [wt, hnew]
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image] at ha hb
    obtain ⟨_, -, rfl⟩ := ha
    obtain ⟨_, -, h⟩ := hb
    exact Sum.inr_ne_inl h

end RegionStep

end Balaban.LargeField
