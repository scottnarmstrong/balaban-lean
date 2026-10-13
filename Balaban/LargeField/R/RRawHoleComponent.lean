module

public import Balaban.LargeField.History.OmegaPost
public import Balaban.LargeField.Geometry.DomainsMod
public import Balaban.LargeField.R.GasIdentity

/-!
# Raw-hole components of the scale-`k` large-field region (VMOD-38 §2, §3)

For a region history `H` the large-field renormalization `R^{(k)}` removes the components
`H.rem k` of `Z^pre_k`; the region afterwards is `Ω_k^post = Ω_k^pre ∪ ⋃ Rem_k`
(`RegionHistory.omegaPost`, with `Ω_k^pre = Def7.OmegaCube H k`).  For a finite coarse label `X`
the cells that become active are `A_X = X ∩ (removedSet_k ∖ Ω_k^pre)` (`newlyActive`).

* `OmegaCube_compl_subset_Zpre` (`1 ≤ k`): the raw hole `(Ω_k^pre)ᶜ` lies in `Z^pre_k`.
* `NNAdj.supDist_le_one`, `mem_comp_of_nnAdj`: a nearest-neighbour step inside `Z^pre_k` stays in
  one component of width `ω_k ≥ 11`.
* `mem_of_nnPath_rawHole`, `rawHole_nnConnected_subset_comp`: a nearest-neighbour path (or
  connected set) in `X ∩ (Ω_k^pre)ᶜ` that meets a removed component `c` lies wholly in `c`;
  corollaries `rawHole_subset_newlyActive`, `rem_eq_of_nnPath_rawHole` (distinct removed components
  are not joined by a path in the raw hole) and `newlyActive_partition` (the nearest-neighbour
  components of `X ∩ (Ω_k^pre)ᶜ` meeting `A_X` partition `A_X`).
* `coe_newlyActive_eq`, `newlyActive_eq_empty`: `A_X = X ∩ Ω_k^post ∖ Ω_k^pre`, empty for `k = 0`
  or `k₀ < k`.
* `REndpointIndex` part: `lt_iff_succ_le`, `omegaPost_eq_OmegaCube_of_gt`, `removal_allowed_iff`.

Source comparison for the endpoint: P5 Theorem 2 and P7 Theorem 5 apply `R^{(j+1)}` for
`j < k₀`, hence `R^{(k₀)}`; the sentence "`k < k₀`" in P7 Theorem 2 is inconsistent with them at
`k = k₀`, and the landed `RegionHistory.rem_empty` follows the consistent reading.

NOT proved here: the cover-extension estimate itself (packages 2-5 of `notes/phase1/VMOD-38.md`),
the charge inequality, and everything analytic about `R`.  The cardinality of a removed ripe
component is the companion `R/RRipeCard.lean`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

section Adjacency

variable {d n : ℕ} [NeZero n]

theorem cycNorm_one_le : cycNorm n (1 : ZMod n) ≤ 1 :=
  (cycNorm_le_iff _ _).mpr ⟨1, by simp, by simp⟩

/-- A nearest-neighbour pair has index distance at most `1`. -/
theorem NNAdj.supDist_le_one {x y : Torus d n} (h : NNAdj x y) : supDist x y ≤ 1 := by
  have h0 : cycNorm n (0 : ZMod n) ≤ 1 := ((cycNorm_zero_iff _).mpr rfl).le.trans (by omega)
  obtain ⟨μ, h | h⟩ := h
  · refine supDist_le_iff.mpr fun i => ?_
    subst h
    simp only [Pi.add_apply]
    by_cases hi : i = μ
    · subst hi
      rw [show x i - (x i + (Pi.single i 1 : Fin d → ZMod n) i) = -1 by simp, cycNorm_neg]
      exact cycNorm_one_le
    · rw [show x i - (x i + (Pi.single μ 1 : Fin d → ZMod n) i) = 0 by simp [hi]]
      exact h0
  · refine supDist_le_iff.mpr fun i => ?_
    subst h
    simp only [Pi.add_apply]
    by_cases hi : i = μ
    · subst hi
      rw [cycNorm_sub_comm, show y i - (y i + (Pi.single i 1 : Fin d → ZMod n) i) = -1 by simp,
        cycNorm_neg]
      exact cycNorm_one_le
    · rw [show y i + (Pi.single μ 1 : Fin d → ZMod n) i - y i = 0 by simp [hi]]
      exact h0

end Adjacency

namespace RegionHistory

open Balaban.LargeField.RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K)

/-- **T1.**  For `1 ≤ k` the raw hole `(Ω_k^pre)ᶜ` lies in `Z^pre_k`. -/
theorem OmegaCube_compl_subset_Zpre {k : ℕ} (hk : 1 ≤ k) :
    (Def7.OmegaCube H k)ᶜ ⊆ H.F.Zpre k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  intro x hx
  exact ((H.step j).Z0_subset_Zpre _ _) ((H.step j).Omega_compl_subset_Z0 hx)

/-- **T2.**  A nearest-neighbour neighbour in `Z^pre_k` of a point of a component `c` of
`Z^pre_k` (width `ω_k`) lies in `c`. -/
theorem mem_comp_of_nnAdj {k : ℕ} {c : Finset (Torus S.d (n k))}
    (hc : c ∈ comps (S.omega k) (H.Zp k)) {x y : Torus S.d (n k)} (hx : x ∈ c)
    (hy : y ∈ H.F.Zpre k) (h : NNAdj x y) : y ∈ c :=
  mem_comp_of_close hc hx (mem_finOf.mpr hy)
    (lt_of_le_of_lt h.supDist_le_one (lt_of_lt_of_le (by norm_num) (omega_ge_eleven S k)))

/-- Two nearest neighbours in `Z^pre_k` lie in the same component of `Z^pre_k`. -/
theorem exists_comp_of_nnAdj {k : ℕ} {x y : Torus S.d (n k)} (hx : x ∈ H.F.Zpre k)
    (hy : y ∈ H.F.Zpre k) (h : NNAdj x y) :
    ∃ c ∈ comps (S.omega k) (H.Zp k), x ∈ c ∧ y ∈ c := by
  classical
  have hxZ : x ∈ H.Zp k := mem_finOf.mpr hx
  have hc : linkClass (S.omega k) (H.Zp k) x ∈ comps (S.omega k) (H.Zp k) :=
    mem_comps_iff.mpr ⟨x, hxZ, rfl⟩
  have hxc : x ∈ linkClass (S.omega k) (H.Zp k) x := mem_linkClass.mpr ⟨hxZ, Linked.refl _⟩
  exact ⟨_, hc, hxc, H.mem_comp_of_nnAdj hc hxc hy h⟩

/-- A nearest-neighbour path inside `Z^pre_k` stays in one component. -/
theorem mem_comp_of_nnPath {k : ℕ} {c : Finset (Torus S.d (n k))}
    (hc : c ∈ comps (S.omega k) (H.Zp k)) {T : Set (Torus S.d (n k))} (hT : T ⊆ H.F.Zpre k)
    {x y : Torus S.d (n k)} (hx : x ∈ c)
    (hp : Relation.ReflTransGen (fun u v => u ∈ T ∧ v ∈ T ∧ NNAdj u v) x y) : y ∈ c := by
  induction hp with
  | refl => exact hx
  | tail _ hbc ih => exact H.mem_comp_of_nnAdj hc ih (hT hbc.2.1) hbc.2.2

/-- **T3 (path form).**  A nearest-neighbour path inside the raw hole `X ∩ (Ω_k^pre)ᶜ` that starts
in a removed component `c` stays in `c`. -/
theorem mem_of_nnPath_rawHole {k : ℕ} (hk : 1 ≤ k) {c : Finset (Torus S.d (n k))}
    (hc : c ∈ H.rem k) {T : Set (Torus S.d (n k))} (hT : T ⊆ (Def7.OmegaCube H k)ᶜ)
    {x y : Torus S.d (n k)} (hx : x ∈ c)
    (hp : Relation.ReflTransGen (fun u v => u ∈ T ∧ v ∈ T ∧ NNAdj u v) x y) : y ∈ c :=
  H.mem_comp_of_nnPath (H.rem_sub k hc) (hT.trans (H.OmegaCube_compl_subset_Zpre hk)) hx hp

/-- **T3.**  A nearest-neighbour connected set `Q ⊆ X ∩ (Ω_k^pre)ᶜ` meeting a removed component
`c` lies wholly in `c`. -/
theorem rawHole_nnConnected_subset_comp {k : ℕ} (hk : 1 ≤ k) (X : Finset (Torus S.d (n k)))
    {c : Finset (Torus S.d (n k))} (hc : c ∈ H.rem k) {Q : Set (Torus S.d (n k))}
    (hQ : Q ⊆ (X : Set (Torus S.d (n k))) ∩ (Def7.OmegaCube H k)ᶜ)
    (hconn : ∀ x ∈ Q, ∀ y ∈ Q,
      Relation.ReflTransGen (fun u v => u ∈ Q ∧ v ∈ Q ∧ NNAdj u v) x y)
    (hmeet : (Q ∩ (c : Set (Torus S.d (n k)))).Nonempty) : Q ⊆ (c : Set (Torus S.d (n k))) := by
  obtain ⟨x, hxQ, hxc⟩ := hmeet
  intro y hy
  exact H.mem_of_nnPath_rawHole hk hc (fun z hz => (hQ hz).2) hxc (hconn x hxQ y hy)

/-- The newly active coarse cells `A_X = X ∩ (removedSet_k ∖ Ω_k^pre)` (VMOD-38 (2)). -/
noncomputable def newlyActive {k : ℕ} (X : Finset (Torus S.d (n k))) : Finset (Torus S.d (n k)) :=
  open Classical in X.filter fun x => x ∈ H.removedSet k ∧ x ∉ Def7.OmegaCube H k

theorem mem_newlyActive {k : ℕ} {X : Finset (Torus S.d (n k))} {x : Torus S.d (n k)} :
    x ∈ H.newlyActive X ↔ x ∈ X ∧ x ∈ H.removedSet k ∧ x ∉ Def7.OmegaCube H k := by
  classical
  simp [newlyActive]

/-- **T3 (i).**  A nearest-neighbour connected subset of the raw hole meeting a removed component
lies in `A_X`. -/
theorem rawHole_nnConnected_subset_newlyActive {k : ℕ} (hk : 1 ≤ k)
    (X : Finset (Torus S.d (n k))) {c : Finset (Torus S.d (n k))} (hc : c ∈ H.rem k)
    {Q : Set (Torus S.d (n k))}
    (hQ : Q ⊆ (X : Set (Torus S.d (n k))) ∩ (Def7.OmegaCube H k)ᶜ)
    (hconn : ∀ x ∈ Q, ∀ y ∈ Q,
      Relation.ReflTransGen (fun u v => u ∈ Q ∧ v ∈ Q ∧ NNAdj u v) x y)
    (hmeet : (Q ∩ (c : Set (Torus S.d (n k)))).Nonempty) :
    Q ⊆ (H.newlyActive X : Set (Torus S.d (n k))) := by
  intro y hy
  have hyc := H.rawHole_nnConnected_subset_comp hk X hc hQ hconn hmeet hy
  exact H.mem_newlyActive.mpr ⟨(hQ hy).1, H.mem_removedSet_iff.mpr ⟨c, hc, hyc⟩, (hQ hy).2⟩

/-- **T3 (ii).**  Two removed components are never joined by a nearest-neighbour path inside the
raw hole: if `x ∈ c`, `y ∈ c'` and a path in `T ⊆ (Ω_k^pre)ᶜ` joins them, then `c = c'`. -/
theorem rem_eq_of_nnPath_rawHole {k : ℕ} (hk : 1 ≤ k) {c c' : Finset (Torus S.d (n k))}
    (hc : c ∈ H.rem k) (hc' : c' ∈ H.rem k) {T : Set (Torus S.d (n k))}
    (hT : T ⊆ (Def7.OmegaCube H k)ᶜ) {x y : Torus S.d (n k)} (hx : x ∈ c) (hy : y ∈ c')
    (hp : Relation.ReflTransGen (fun u v => u ∈ T ∧ v ∈ T ∧ NNAdj u v) x y) : c = c' :=
  comp_eq_of_mem (H.rem_sub k hc) (H.rem_sub k hc') (H.mem_of_nnPath_rawHole hk hc hT hx hp) hy

/-- **T3 (iii).**  The nearest-neighbour components of `X ∩ (Ω_k^pre)ᶜ` meeting `A_X` lie in `A_X`
and partition it: there is a family `P` of such components, pairwise disjoint, with union `A_X`
and `Σ_{Q ∈ P} |Q| = |A_X|`. -/
theorem newlyActive_partition {k : ℕ} (hk : 1 ≤ k) (X : Finset (Torus S.d (n k))) :
    ∃ P : Finset (Finset (Torus S.d (n k))),
      (∀ Q ∈ P, ∃ a ∈ H.newlyActive X,
        (Q : Set (Torus S.d (n k))) =
          nnComp ((X : Set (Torus S.d (n k))) ∩ (Def7.OmegaCube H k)ᶜ) a) ∧
      (∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → Disjoint Q Q') ∧
      P.biUnion id = H.newlyActive X ∧ ∑ Q ∈ P, Q.card = (H.newlyActive X).card := by
  classical
  set T : Set (Torus S.d (n k)) := (X : Set (Torus S.d (n k))) ∩ (Def7.OmegaCube H k)ᶜ with hTdef
  have hsub : ∀ a ∈ H.newlyActive X, nnComp T a ⊆ (H.newlyActive X : Set (Torus S.d (n k))) := by
    intro a ha b hb
    obtain ⟨haX, haR, haO⟩ := H.mem_newlyActive.mp ha
    obtain ⟨c, hc, hac⟩ := H.mem_removedSet_iff.mp haR
    have hbc := H.mem_of_nnPath_rawHole hk hc (T := T) (fun z hz => hz.2) hac hb.2
    exact H.mem_newlyActive.mpr ⟨hb.1.1, H.mem_removedSet_iff.mpr ⟨c, hc, hbc⟩, hb.1.2⟩
  have hd : ∀ Q ∈ (H.newlyActive X).image (fun a => finOf (nnComp T a)),
      ∀ Q' ∈ (H.newlyActive X).image (fun a => finOf (nnComp T a)), Q ≠ Q' → Disjoint Q Q' := by
    intro Q hQ Q' hQ' hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hQ'
    rw [Finset.disjoint_left]
    intro z hza hzb
    rw [mem_finOf] at hza hzb
    exact hne (by rw [← nnComp_eq_of_mem hza, ← nnComp_eq_of_mem hzb])
  have hU : ((H.newlyActive X).image (fun a => finOf (nnComp T a))).biUnion id
      = H.newlyActive X := by
    ext z
    simp only [Finset.mem_biUnion, Finset.mem_image, id, exists_exists_and_eq_and]
    constructor
    · rintro ⟨a, ha, hz⟩
      rw [mem_finOf] at hz
      exact hsub a ha hz
    · intro hz
      have h := H.mem_newlyActive.mp hz
      exact ⟨z, hz, mem_finOf.mpr (mem_nnComp_self ⟨h.1, h.2.2⟩)⟩
  refine ⟨(H.newlyActive X).image fun a => finOf (nnComp T a), ?_, hd, hU, ?_⟩
  · intro Q hQ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hQ
    exact ⟨a, ha, by ext z; simp⟩
  · have := Finset.card_biUnion hd (t := id)
    rw [hU] at this
    exact this.symm

/-- **T4.**  `A_X = X ∩ Ω_k^post ∖ Ω_k^pre`. -/
theorem coe_newlyActive_eq {k : ℕ} (X : Finset (Torus S.d (n k))) :
    (H.newlyActive X : Set (Torus S.d (n k))) =
      (X : Set (Torus S.d (n k))) ∩ (H.omegaPost k \ Def7.OmegaCube H k) := by
  ext x
  simp only [Finset.mem_coe, H.mem_newlyActive, Set.mem_inter_iff, Set.mem_sdiff, omegaPost,
    Set.mem_union]
  tauto

/-- **T4.**  No cell becomes active at `k = 0` or `k₀ < k`. -/
theorem newlyActive_eq_empty {k : ℕ} (hk : k = 0 ∨ k0 < k) (X : Finset (Torus S.d (n k))) :
    H.newlyActive X = ∅ := by
  ext x
  simp only [H.mem_newlyActive, Finset.notMem_empty, iff_false]
  rintro ⟨-, hx, -⟩
  obtain ⟨c, hc, -⟩ := H.mem_removedSet_iff.mp hx
  simp [H.rem_empty k hk] at hc

/-! ### `REndpointIndex` (VMOD-38 §3) -/

omit [∀ k, NeZero (n k)] in
theorem lt_iff_succ_le (j k0 : ℕ) : j < k0 ↔ j + 1 ≤ k0 := Nat.lt_iff_add_one_le

/-- For `k₀ < k` the region is unchanged by `R^{(k)}`: `Ω_k^post = Ω_k^pre`. -/
theorem omegaPost_eq_OmegaCube_of_gt {k : ℕ} (hk : k0 < k) :
    H.omegaPost k = Def7.OmegaCube H k :=
  H.omegaPost_eq_OmegaCube_of_rem_empty (H.rem_empty k (Or.inr hk))

/-- Likewise at `k = 0`. -/
theorem omegaPost_zero_eq : H.omegaPost 0 = Def7.OmegaCube H 0 :=
  H.omegaPost_eq_OmegaCube_of_rem_empty (H.rem_empty 0 (Or.inl rfl))

/-- Removal at scale `k` is allowed (the hypothesis of `rem_empty` fails) exactly for
`1 ≤ k ≤ k₀`; in particular at `k = k₀`, and `R^{(j+1)}` for `j < k₀` covers all of them. -/
theorem removal_allowed_iff (k k0 : ℕ) : ¬ (k = 0 ∨ k0 < k) ↔ 1 ≤ k ∧ k ≤ k0 := by omega

end RegionHistory

end Balaban.LargeField
