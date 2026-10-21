/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairHatLift

/-!
# The active closure of a read set and its block hull (geometry of P3 (4.41)–(4.47) at one point)

For a cover `C` (centres `C.cubeIdx`, footprints `𝒬(z)`, interaction boxes `□_z = intBox z`) and a
vector `s` of decoupling factors, a centre `z` is *active* when `s_z = ∏_{P ∈ 𝒬(z)} s_P ≠ 0`.  The
decoupled objects at `s` (background, Green's operator, covariance) see a site only through the
active centres connected to it; this file builds, for a finite *seed* (the sites read by a term),
the set of active centres reachable from the seed by chains of active centres whose interaction
boxes come within `D` of each other, and the union `T` of the `(k+1)`-blocks within `L^{k+1}` of
their interaction boxes.  These are the sets `T ⊂ Y` of the cross lemmas
(`Dec2.decBg_value_cross`, `Dec2.localLift_eq_localLift_on_component`) for one pair at two vectors.

* `ActC`, `ActAdj`, `actComp`, `actHull`: active centres, their adjacency at distance `D`, the
  closure of a seed, its block hull;
* `act_of_mem_actComp`, `mem_actComp_of_adj`, `intBox_subset_actHull`, `isBlockUnion_actHull`,
  `exists_of_mem_actHull`;
* `mem_actComp_of_near`, `actC_dich`: **the dichotomy**: an active centre whose interaction box comes
  within `r` of the hull, `r + 2 L^{k+1} ≤ D`, belongs to the closure (so its box lies in the hull);
* `actComp_mono`, `actHull_mono`, `actComp_eq_of_sProd_eq`, `actHull_eq_of_sProd_eq`: the closure only grows with the
  active set, and two vectors with the same factors on the closure of a common larger vector have the
  same closure and hull;
* `seed_subset_actHull`: a seed covered by interaction boxes of active centres lies in the hull;
* `hRespects_of_near_iff`, `hRespects_actHull`: the proviso `HRespects` of the covariance for the
  hull (a non-zero entry of the Dirichlet operator joins sites within `L^{k+1}`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Balaban.SmallField

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] (C : DecCover d L N₁ m₁ (k + 1))

/-- An *active* centre: a centre of the cover with non-zero decoupling factor `s_z`. -/
def ActC (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) : Prop :=
  q ∈ C.cubeIdx ∧ C.sProd s q ≠ 0

/-- Two active centres whose interaction boxes come within sup-distance `D`. -/
def ActAdj (D : ℕ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
    (q q' : ℕ × CTorus d L N₁ m₁ (k + 1)) : Prop :=
  ActC C s q ∧ ActC C s q' ∧ ∃ x ∈ intBox q, ∃ x' ∈ intBox q', supDist x x' ≤ D

open Classical in
/-- **The active closure of a seed**: the active centres reachable by an `ActAdj`-chain from an
active centre whose interaction box comes within `D` of the seed. -/
noncomputable def actComp (D : ℕ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
    (seed : Finset (CTorus d L N₁ m₁ (k + 1))) : Finset (ℕ × CTorus d L N₁ m₁ (k + 1)) :=
  C.cubeIdx.filter fun q => ∃ q₀, ActC C s q₀ ∧ (∃ x ∈ intBox q₀, ∃ y ∈ seed, supDist x y ≤ D) ∧
    Relation.ReflTransGen (ActAdj C D s) q₀ q

open Classical in
/-- **The block hull of the active closure**: the `(k+1)`-blocks meeting the `L^{k+1}`-neighbourhood
of the interaction boxes of the closure. -/
noncomputable def actHull (D : ℕ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
    (seed : Finset (CTorus d L N₁ m₁ (k + 1))) : Finset (CTorus d L N₁ m₁ (k + 1)) :=
  Finset.univ.filter fun y => ∃ z, jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) z =
    jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y ∧
    ∃ q ∈ actComp C D s seed, ∃ x ∈ intBox q, supDist x z ≤ L ^ (k + 1)

variable {C}

theorem mem_actComp {D : ℕ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {seed : Finset (CTorus d L N₁ m₁ (k + 1))} {q : ℕ × CTorus d L N₁ m₁ (k + 1)} :
    q ∈ actComp C D s seed ↔ q ∈ C.cubeIdx ∧ ∃ q₀, ActC C s q₀ ∧
      (∃ x ∈ intBox q₀, ∃ y ∈ seed, supDist x y ≤ D) ∧ Relation.ReflTransGen (ActAdj C D s) q₀ q := by
  classical
  simp [actComp]

theorem mem_actHull {D : ℕ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {seed : Finset (CTorus d L N₁ m₁ (k + 1))} {y : CTorus d L N₁ m₁ (k + 1)} :
    y ∈ actHull C D s seed ↔ ∃ z, jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) z =
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y ∧
      ∃ q ∈ actComp C D s seed, ∃ x ∈ intBox q, supDist x z ≤ L ^ (k + 1) := by
  classical
  simp [actHull]

theorem actC_of_reflTransGen {D : ℕ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {q₀ q : ℕ × CTorus d L N₁ m₁ (k + 1)} (h₀ : ActC C s q₀)
    (h : Relation.ReflTransGen (ActAdj C D s) q₀ q) : ActC C s q := by
  induction h with
  | refl => exact h₀
  | tail _ hab _ => exact hab.2.1

/-- The centres of the closure are active. -/
theorem act_of_mem_actComp {D : ℕ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {seed : Finset (CTorus d L N₁ m₁ (k + 1))} {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ actComp C D s seed) : ActC C s q := by
  obtain ⟨-, q₀, h₀, -, hch⟩ := mem_actComp.1 hq
  exact actC_of_reflTransGen h₀ hch

/-- The closure is closed under adjacency. -/
theorem mem_actComp_of_adj {D : ℕ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {seed : Finset (CTorus d L N₁ m₁ (k + 1))} {q q' : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ actComp C D s seed) (hadj : ActAdj C D s q q') : q' ∈ actComp C D s seed := by
  obtain ⟨-, q₀, h₀, hseed, hch⟩ := mem_actComp.1 hq
  exact mem_actComp.2 ⟨hadj.2.1.1, q₀, h₀, hseed, hch.tail hadj⟩

/-- The interaction boxes of the closure lie in the hull. -/
theorem intBox_subset_actHull {D : ℕ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {seed : Finset (CTorus d L N₁ m₁ (k + 1))} {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ actComp C D s seed) {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ intBox q) :
    x ∈ actHull C D s seed :=
  mem_actHull.2 ⟨x, rfl, q, hq, x, hx, by rw [supDist_self]; exact Nat.zero_le _⟩

/-- The sites within `L^{k+1}` of an interaction box of the closure lie in the hull. -/
theorem mem_actHull_of_near {D : ℕ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {seed : Finset (CTorus d L N₁ m₁ (k + 1))} {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ actComp C D s seed) {x y : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ intBox q)
    (hxy : supDist x y ≤ L ^ (k + 1)) : y ∈ actHull C D s seed :=
  mem_actHull.2 ⟨y, rfl, q, hq, x, hx, hxy⟩

/-- The hull is a union of `(k+1)`-blocks. -/
theorem isBlockUnion_actHull (D : ℕ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
    (seed : Finset (CTorus d L N₁ m₁ (k + 1))) :
    IsBlockUnion L (N₁ * L ^ m₁) (k + 1) (k + 1) (actHull C D s seed) := by
  intro y y' hyy'
  rw [mem_actHull, mem_actHull]
  constructor
  · rintro ⟨z, hz, h⟩; exact ⟨z, hz.trans hyy', h⟩
  · rintro ⟨z, hz, h⟩; exact ⟨z, hz.trans hyy'.symm, h⟩

/-- A site of the hull is within `2 L^{k+1}` of an interaction box of the closure. -/
theorem exists_of_mem_actHull {D : ℕ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {seed : Finset (CTorus d L N₁ m₁ (k + 1))} {y : CTorus d L N₁ m₁ (k + 1)}
    (hy : y ∈ actHull C D s seed) :
    ∃ q ∈ actComp C D s seed, ∃ x ∈ intBox q, supDist x y ≤ 2 * L ^ (k + 1) := by
  obtain ⟨z, hz, q, hq, x, hx, hxz⟩ := mem_actHull.1 hy
  have hzy : supDist z y ≤ L ^ (k + 1) :=
    supDist_le_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
      (sameCell_of_jBlock_eq le_rfl hz)
  exact ⟨q, hq, x, hx, (supDist_triangle x z y).trans (by omega)⟩

/-- **The closure catches every active centre near the hull**: if an active centre has a site of its
interaction box within `r` of the hull and `r + 2 L^{k+1} ≤ D`, it belongs to the closure. -/
theorem mem_actComp_of_near {D r : ℕ} (hD : r + 2 * L ^ (k + 1) ≤ D)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {seed : Finset (CTorus d L N₁ m₁ (k + 1))}
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : ActC C s q) {x y : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ intBox q) (hy : y ∈ actHull C D s seed) (hxy : supDist x y ≤ r) :
    q ∈ actComp C D s seed := by
  obtain ⟨q'', hq'', x'', hx'', hd⟩ := exists_of_mem_actHull hy
  refine mem_actComp_of_adj hq'' ⟨act_of_mem_actComp hq'', hq, x'', hx'', x, hx, ?_⟩
  have := supDist_triangle x'' y x
  rw [supDist_comm y x] at this
  omega

/-- **The dichotomy**: an active centre has its interaction box inside the hull or at distance more
than `r` from it, when `r + 2 L^{k+1} ≤ D`. -/
theorem actC_dich {D r : ℕ} (hD : r + 2 * L ^ (k + 1) ≤ D)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {seed : Finset (CTorus d L N₁ m₁ (k + 1))}
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : ActC C s q) :
    (∀ x ∈ intBox q, x ∈ actHull C D s seed) ∨
      ∀ x ∈ intBox q, ∀ y ∈ actHull C D s seed, r < supDist x y := by
  by_cases h : ∃ x ∈ intBox q, ∃ y ∈ actHull C D s seed, supDist x y ≤ r
  · obtain ⟨x, hx, y, hy, hxy⟩ := h
    have hqc := mem_actComp_of_near hD hq hx hy hxy
    exact Or.inl fun x' hx' => intBox_subset_actHull hqc hx'
  · refine Or.inr fun x hx y hy => ?_
    by_contra hle
    exact h ⟨x, hx, y, hy, not_lt.1 hle⟩

/-- The closure only grows with the active set. -/
theorem actComp_mono {D : ℕ} {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hss : ∀ q, ActC C s q → ActC C s' q) (seed : Finset (CTorus d L N₁ m₁ (k + 1))) :
    actComp C D s seed ⊆ actComp C D s' seed := by
  intro q hq
  obtain ⟨hqC, q₀, h₀, hseed, hch⟩ := mem_actComp.1 hq
  refine mem_actComp.2 ⟨hqC, q₀, hss q₀ h₀, hseed, ?_⟩
  have hle : ActAdj C D s ≤ ActAdj C D s' := fun a b hab => ⟨hss a hab.1, hss b hab.2.1, hab.2.2⟩
  exact Relation.ReflTransGen.mono hle _ _ hch

/-- The hull only grows with the active set. -/
theorem actHull_mono {D : ℕ} {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hss : ∀ q, ActC C s q → ActC C s' q) (seed : Finset (CTorus d L N₁ m₁ (k + 1))) :
    actHull C D s seed ⊆ actHull C D s' seed := by
  intro y hy
  obtain ⟨z, hz, q, hq, x, hx, hxz⟩ := mem_actHull.1 hy
  exact mem_actHull.2 ⟨z, hz, q, actComp_mono hss seed hq, x, hx, hxz⟩

/-- **Two vectors with the same factors on the closure of a common larger vector have the same
closure.** -/
theorem actComp_eq_of_sProd_eq {D : ℕ} {s s' smax : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {seed : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hs : ∀ q, ActC C s q → ActC C smax q) (hs' : ∀ q, ActC C s' q → ActC C smax q)
    (heq : ∀ q ∈ actComp C D smax seed, C.sProd s q = C.sProd s' q) :
    actComp C D s seed = actComp C D s' seed := by
  -- a chain of active centres of `s` from a seeded centre stays in the closure of `smax`
  have key : ∀ {t t' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}, (∀ q, ActC C t q → ActC C smax q) →
      (∀ q ∈ actComp C D smax seed, C.sProd t q = C.sProd t' q) →
      actComp C D t seed ⊆ actComp C D t' seed := by
    intro t t' ht hteq q hq
    obtain ⟨hqC, q₀, h₀, hseed, hch⟩ := mem_actComp.1 hq
    have h₀max : q₀ ∈ actComp C D smax seed :=
      mem_actComp.2 ⟨h₀.1, q₀, ht q₀ h₀, hseed, Relation.ReflTransGen.refl⟩
    have hact' : ∀ a, a ∈ actComp C D smax seed → ActC C t a → ActC C t' a :=
      fun a ha hta => ⟨hta.1, by rw [← hteq a ha]; exact hta.2⟩
    -- transport the chain
    have hchain : ∀ b, Relation.ReflTransGen (ActAdj C D t) q₀ b →
        b ∈ actComp C D smax seed ∧ Relation.ReflTransGen (ActAdj C D t') q₀ b := by
      intro b hb
      induction hb with
      | refl => exact ⟨h₀max, Relation.ReflTransGen.refl⟩
      | tail _ hab ih =>
        obtain ⟨hamax, hch'⟩ := ih
        have hbmax : _ := mem_actComp_of_adj hamax ⟨ht _ hab.1, ht _ hab.2.1, hab.2.2⟩
        exact ⟨hbmax, hch'.tail ⟨hact' _ hamax hab.1, hact' _ hbmax hab.2.1, hab.2.2⟩⟩
    exact mem_actComp.2 ⟨hqC, q₀, hact' q₀ h₀max h₀, hseed, (hchain q hch).2⟩
  exact Finset.Subset.antisymm (key hs heq) (key hs' fun q hq => (heq q hq).symm)

/-- The hulls of two such vectors agree. -/
theorem actHull_eq_of_sProd_eq {D : ℕ} {s s' smax : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {seed : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hs : ∀ q, ActC C s q → ActC C smax q) (hs' : ∀ q, ActC C s' q → ActC C smax q)
    (heq : ∀ q ∈ actComp C D smax seed, C.sProd s q = C.sProd s' q) :
    actHull C D s seed = actHull C D s' seed := by
  ext y
  rw [mem_actHull, mem_actHull, actComp_eq_of_sProd_eq hs hs' heq]

/-- **A seed covered by the interaction boxes of active centres lies in the hull.** -/
theorem seed_subset_actHull {D : ℕ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {seed : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : ∀ y ∈ seed, ∃ q, ActC C s q ∧ y ∈ intBox q) : ∀ y ∈ seed, y ∈ actHull C D s seed := by
  intro y hy
  obtain ⟨q, hq, hyq⟩ := hcov y hy
  have hqc : q ∈ actComp C D s seed :=
    mem_actComp.2 ⟨hq.1, q, hq, ⟨y, hyq, y, hy, by rw [supDist_self]; exact Nat.zero_le _⟩,
      Relation.ReflTransGen.refl⟩
  exact intBox_subset_actHull hqc hyq

/-! ### The proviso `HRespects` for the hull -/

/-- **The proviso `HRespects` from a two-sided condition near the core**: if, for every site `y'` of
the core `Core(C, s)` and every site `y` within `L^{k+1}` of it, `y ∈ T ↔ y' ∈ T`, then no non-zero
entry of the x-shifted Dirichlet operator of `H` joins a site of the core to the other side of `T`. -/
theorem hRespects_of_near_iff {ϱ : ℝ} {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (a : ℕ → ℝ) (aT x ν : ℝ) (α : H.Ω 1 → ℂ) {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hT : ∀ y' ∈ Dec2.Core C s, ∀ y : CTorus d L N₁ m₁ (k + 1), supDist y' y ≤ L ^ (k + 1) →
      (y ∈ T ↔ y' ∈ T)) :
    Dec2.HRespects C H a aT x ν α s T := by
  intro y y' hne hcore
  have hL1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  by_cases hyy : y = y'
  · rw [hyy]
  have hd : supDist (y' : CTorus d L N₁ m₁ (k + 1)) (y : CTorus d L N₁ m₁ (k + 1)) ≤
      L ^ (k + 1) := by
    rcases xDirichlet_ne_zero_near hyy hne with ⟨μ, h | h⟩ | h
    · rw [h, supDist_comm]
      exact (supDist_add_single_le _ μ).trans hL1
    · rw [h]
      exact (supDist_add_single_le _ μ).trans hL1
    · exact (supDist_le_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _) h.symm).trans
        (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L))
          (layerIndex_le_of_Ω_empty H H.top _))
  exact hT _ hcore _ hd

/-- **`HRespects` for the hull** (`L^{k+1} + 2 L^{k+1} ≤ D`): a core site of a centre of the closure
and its `L^{k+1}`-neighbours lie in the hull; a core site of an active centre outside the closure is
farther than `L^{k+1}` from the hull, and so are its neighbours. -/
theorem hRespects_actHull {ϱ : ℝ} {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (a : ℕ → ℝ) (aT x ν : ℝ) (α : H.Ω 1 → ℂ) {D : ℕ} (hD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ D)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (seed : Finset (CTorus d L N₁ m₁ (k + 1))) :
    Dec2.HRespects C H a aT x ν α s (actHull C D s seed) := by
  refine hRespects_of_near_iff a aT x ν α fun y' hy' y hyy => ?_
  obtain ⟨z, hz, hyz⟩ := Finset.mem_biUnion.1 hy'
  have hzact : ActC C s z := by
    unfold Dec2.Zs at hz
    rw [Finset.mem_filter] at hz
    exact hz
  have hy'box : y' ∈ intBox z := coreBox_subset_box hyz
  rcases actC_dich (seed := seed) hD hzact with hin | hout
  · -- the centre is in the closure
    have hzc : z ∈ actComp C D s seed := by
      have := hin y' hy'box
      exact mem_actComp_of_near (r := 0) (by omega) hzact hy'box this
        (by rw [supDist_self])
    exact iff_of_true (mem_actHull_of_near hzc hy'box hyy) (hin y' hy'box)
  · refine iff_of_false (fun hy => ?_) (fun hy => ?_)
    · have := hout y' hy'box y hy
      omega
    · have := hout y' hy'box y' hy
      rw [supDist_self] at this
      omega

end Balaban.Fluctuation
