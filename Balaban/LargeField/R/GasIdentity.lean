module

public import Balaban.LargeField.R.RemCluster

/-!
# The gas identity (Part III, Lemma III.10.4)

For a fixed admissible kept configuration `Kc`, the removed parts `Rm` with `Kc ∪ Rm` an admissible
configuration correspond bijectively, via `Rm ↦ clusters Rm` (the classes of "index distance
`≤ 4ω_k`"), to the families of pairwise compatible removed clusters with `∏ admFactor = 1`
(`gas_identity`).  The factor of a cluster does not depend on `Kc` if its support is disjoint
from `Y_k` (`admFactor_eq_of_supp_disjoint`).  Joint admissibility factorizes over the clusters by
Lemma III.10.2 (`adm_of_cliques`, `adm_sub`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban RegionHistory
open scoped Classical

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M k : ℕ} [NeZero M]

section Clusters

variable {Rm : Finset (ConfigPair S n M K k)} {m m' m1 m2 : ConfigPair S n M K k}

theorem clusterRel_symm (h : ClusterRel S n M K k Rm m m') : ClusterRel S n M K k Rm m' m := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (r := fun a b => a ∈ Rm ∧ b ∈ Rm ∧ Near4 S n M K k a b)
        ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩) ih

theorem clusterRel_trans (h1 : ClusterRel S n M K k Rm m1 m2) (h2 : ClusterRel S n M K k Rm m2 m) :
    ClusterRel S n M K k Rm m1 m :=
  Relation.ReflTransGen.trans h1 h2

theorem mem_clusterOf (S : Setting) (n : ℕ → ℕ) (M K k : ℕ) {Rm : Finset (ConfigPair S n M K k)}
    {m m' : ConfigPair S n M K k} :
    m' ∈ clusterOf S n M K k Rm m ↔ m' ∈ Rm ∧ ClusterRel S n M K k Rm m m' := by
  simp [clusterOf]

theorem mem_clusterOf_self (hm : m ∈ Rm) : m ∈ clusterOf S n M K k Rm m :=
  (mem_clusterOf S n M K k).mpr ⟨hm, Relation.ReflTransGen.refl⟩

theorem clusterOf_subset : clusterOf S n M K k Rm m ⊆ Rm := fun _ h =>
  ((mem_clusterOf S n M K k).mp h).1

theorem clusterOf_eq_of_mem (h : m' ∈ clusterOf S n M K k Rm m) :
    clusterOf S n M K k Rm m' = clusterOf S n M K k Rm m := by
  obtain ⟨-, hr⟩ := (mem_clusterOf S n M K k).mp h
  ext x
  rw [mem_clusterOf, mem_clusterOf]
  constructor
  · rintro ⟨hx, hx'⟩
    exact ⟨hx, clusterRel_trans hr hx'⟩
  · rintro ⟨hx, hx'⟩
    exact ⟨hx, clusterRel_trans (clusterRel_symm hr) hx'⟩

theorem biUnion_clusters : (clusters S n M K k Rm).biUnion id = Rm := by
  ext x
  simp only [clusters, Finset.mem_biUnion, Finset.mem_image, id]
  constructor
  · rintro ⟨C, ⟨m, hm, rfl⟩, hx⟩
    exact clusterOf_subset hx
  · intro hx
    exact ⟨_, ⟨x, hx, rfl⟩, mem_clusterOf_self hx⟩

theorem not_near4_of_ne {C C' : Finset (ConfigPair S n M K k)} (hC : C ∈ clusters S n M K k Rm)
    (hC' : C' ∈ clusters S n M K k Rm) (hne : C ≠ C') {a b : ConfigPair S n M K k} (ha : a ∈ C)
    (hb : b ∈ C') : ¬ Near4 S n M K k a b := by
  intro hab
  simp only [clusters, Finset.mem_image] at hC hC'
  obtain ⟨m, hm, rfl⟩ := hC
  obtain ⟨m', hm', rfl⟩ := hC'
  obtain ⟨haR, hra⟩ := (mem_clusterOf S n M K k).mp ha
  obtain ⟨hbR, -⟩ := (mem_clusterOf S n M K k).mp hb
  have hb' : b ∈ clusterOf S n M K k Rm m := by
    refine (mem_clusterOf S n M K k).mpr ⟨hbR, hra.tail ⟨haR, hbR, hab⟩⟩
  have e1 := clusterOf_eq_of_mem hb'
  have e2 := clusterOf_eq_of_mem hb
  exact hne (e1.symm.trans e2)

theorem connected_clusterOf {a b : ConfigPair S n M K k}
    (ha : a ∈ clusterOf S n M K k Rm m) (hb : b ∈ clusterOf S n M K k Rm m) :
    Relation.ReflTransGen (fun x y => x ∈ clusterOf S n M K k Rm m ∧
      y ∈ clusterOf S n M K k Rm m ∧ Near4 S n M K k x y) a b := by
  have e := clusterOf_eq_of_mem ha
  obtain ⟨-, hr⟩ := (mem_clusterOf S n M K k).mp hb
  have hr' : ClusterRel S n M K k Rm a b := by
    obtain ⟨-, hra⟩ := (mem_clusterOf S n M K k).mp ha
    exact clusterRel_trans (clusterRel_symm hra) hr
  -- induction on the chain from `a` to `b` inside `Rm`
  have key : ∀ c, ClusterRel S n M K k Rm a c → c ∈ clusterOf S n M K k Rm m ∧
      Relation.ReflTransGen (fun x y => x ∈ clusterOf S n M K k Rm m ∧
        y ∈ clusterOf S n M K k Rm m ∧ Near4 S n M K k x y) a c := by
    intro c hc
    induction hc with
    | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
    | tail hab' hbc ih =>
      obtain ⟨hbmem, hch⟩ := ih
      rename_i b' c'
      obtain ⟨-, hrb⟩ := (mem_clusterOf S n M K k).mp hbmem
      have hcmem : c' ∈ clusterOf S n M K k Rm m :=
        (mem_clusterOf S n M K k).mpr ⟨hbc.2.1, clusterRel_trans hrb (Relation.ReflTransGen.single hbc)⟩
      exact ⟨hcmem, hch.tail ⟨hbmem, hcmem, hbc.2.2⟩⟩
  exact (key b hr').2

end Clusters

section Supports

variable {m m' : ConfigPair S n M K k}

theorem near4_iff_not_disjoint :
    Near4 S n M K k m m' ↔ ¬ Disjoint (nbhd (2 * S.omega k) ((m.1 : Finset (Torus S.d (n k))) :
      Set (Torus S.d (n k)))) (nbhd (2 * S.omega k) ((m'.1 : Finset (Torus S.d (n k))) :
      Set (Torus S.d (n k)))) := by
  rw [Set.not_disjoint_iff]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨z, h1, h2⟩ := exists_split (x := x) (z := y) (a := 2 * S.omega k) (b := 2 * S.omega k)
      (by omega)
    exact ⟨z, mem_nbhd.mpr ⟨x, hx, by rwa [supDist_comm]⟩, mem_nbhd.mpr ⟨y, hy, h2⟩⟩
  · rintro ⟨z, hz, hz'⟩
    obtain ⟨x, hx, h1⟩ := mem_nbhd.mp hz
    obtain ⟨y, hy, h2⟩ := mem_nbhd.mp hz'
    refine ⟨x, hx, y, hy, ?_⟩
    have := supDist_triangle x z y
    rw [supDist_comm x z] at this
    omega

theorem disjoint_clusterSupp_iff {C C' : Finset (ConfigPair S n M K k)} :
    Disjoint (clusterSupp S n M K k C) (clusterSupp S n M K k C') ↔
      ∀ a ∈ C, ∀ b ∈ C', ¬ Near4 S n M K k a b := by
  constructor
  · intro h a ha b hb hab
    rw [near4_iff_not_disjoint] at hab
    have s1 : nbhd (2 * S.omega k) ((a.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) ⊆
        clusterSupp S n M K k C := fun z hz => Set.mem_biUnion ha hz
    have s2 : nbhd (2 * S.omega k) ((b.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) ⊆
        clusterSupp S n M K k C' := fun z hz => Set.mem_biUnion hb hz
    exact hab (h.mono s1 s2)
  · intro h
    rw [Set.disjoint_left]
    intro z hz hz'
    simp only [clusterSupp, Set.mem_iUnion, exists_prop] at hz hz'
    obtain ⟨a, ha, hza⟩ := hz
    obtain ⟨b, hb, hzb⟩ := hz'
    exact h a ha b hb (near4_iff_not_disjoint.mpr (Set.not_disjoint_iff.mpr ⟨z, hza, hzb⟩))

theorem pair_nonempty (h : m.2 ∈ localizedHistories (S := S) (n := n) R k0 K M k m.1) :
    m.1.Nonempty := by
  obtain ⟨H', -, c, hc, -⟩ := h
  rw [← hc]
  exact comp_nonempty c.2

theorem omega_ge_eleven (S : Setting) (k : ℕ) : 11 ≤ S.omega k := by
  have h := le_omegaW S.L S.Rb S.lam k
  rw [← Setting.omega_eq_omegaW] at h
  omega

end Supports

/-- `IsAdmConfig` only depends on the members. -/
theorem isAdmConfig_congr {F F' : Config S n R k0 K M k} (h : F.members = F'.members)
    (hF : IsAdmConfig F) : IsAdmConfig F' := by
  obtain ⟨H, hadm, hc1, hc2⟩ := hF
  exact ⟨H, hadm, fun c => h ▸ hc1 c, fun m hm => hc2 m (h ▸ hm)⟩

/-- The configuration with members `Kc ∪ Rm`. -/
noncomputable def unionConfig (Kc : Config S n R k0 K M k) (Rm : Finset (ConfigPair S n M K k))
    (hmem : ∀ m ∈ Rm, m.2 ∈ localizedHistories (S := S) (n := n) R k0 K M k m.1)
    (hsepR : ∀ m ∈ Rm, ∀ m' ∈ Rm, m ≠ m' → ∀ x ∈ m.1, ∀ y ∈ m'.1, S.omega k ≤ supDist x y)
    (hsepK : ∀ m ∈ Rm, ∀ m' ∈ Kc.members, ∀ x ∈ m.1, ∀ y ∈ m'.1, S.omega k ≤ supDist x y) :
    Config S n R k0 K M k where
  members := Kc.members ∪ Rm
  mem_hist m hm := by
    rcases Finset.mem_union.mp hm with h | h
    · exact Kc.mem_hist m h
    · exact hmem m h
  sep m hm m' hm' hne x hx y hy := by
    rcases Finset.mem_union.mp hm with h | h <;> rcases Finset.mem_union.mp hm' with h' | h'
    · exact Kc.sep m h m' h' hne x hx y hy
    · have := hsepK m' h' m h y hy x hx
      rwa [supDist_comm] at this
    · exact hsepK m h m' h' x hx y hy
    · exact hsepR m h m' h' hne x hx y hy

section Main

variable (hk : k ≤ K)

include hk

/-- **Lemma III.10.4**, first half: the clusters of an admissible `Kc ∪ Rm` form a family of
pairwise compatible removed clusters with `∏ admFactor = 1`. -/
theorem isClusterFamily_clusters {Kc : Config S n R k0 K M k}
    {Rm : Finset (ConfigPair S n M K k)} (h : IsRemSet Kc Rm) :
    IsClusterFamily Kc (clusters S n M K k Rm) := by
  obtain ⟨hrip, hdis, F, hFm, hFadm⟩ := h
  have hRmF : ∀ m ∈ Rm, m ∈ F.members := fun m hm => hFm ▸ Finset.mem_union_right _ hm
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hC
    exact
      { nonempty := ⟨m0, mem_clusterOf_self hm0⟩
        ripe := fun m hm => hrip m (clusterOf_subset hm)
        mem_hist := fun m hm => F.mem_hist m (hRmF m (clusterOf_subset hm))
        sep := fun m hm m' hm' hne =>
          F.sep m (hRmF m (clusterOf_subset hm)) m' (hRmF m' (clusterOf_subset hm')) hne
        sepKept := fun m hm m' hm' x hx y hy =>
          F.sep m (hRmF m (clusterOf_subset hm)) m' (hFm ▸ Finset.mem_union_left _ hm')
            (fun heq => Finset.disjoint_left.mp hdis (clusterOf_subset hm) (heq ▸ hm')) x hx y hy
        connected := fun m hm m' hm' => connected_clusterOf hm hm' }
  · intro C hC C' hC' hne
    exact disjoint_clusterSupp_iff.mpr fun a ha b hb => not_near4_of_ne hC hC' hne ha hb
  · refine Finset.prod_eq_one fun C hC => ?_
    obtain ⟨m0, -, rfl⟩ := Finset.mem_image.mp hC
    have hG : clusterOf S n M K k Rm m0 ∪ keptNear (R := R) (k0 := k0) Kc
        (clusterOf S n M K k Rm m0) ⊆ F.members := by
      intro q hq
      rcases Finset.mem_union.mp hq with h | h
      · exact hRmF q (clusterOf_subset h)
      · exact hFm ▸ Finset.mem_union_left _ (Finset.mem_filter.mp h).1
    have hfam : IsAdmFamily (S := S) (n := n) R k0 K M k
        (clusterOf S n M K k Rm m0 ∪ keptNear (R := R) (k0 := k0) Kc (clusterOf S n M K k Rm m0)) :=
      ⟨F.sub _ hG, rfl, adm_sub hk hFadm hG⟩
    simp [admFactor, hfam]

/-- A family of pairwise compatible removed clusters with `∏ admFactor = 1` is the family of
clusters of an admissible `Kc ∪ Rm`, `Rm` the union of the clusters. -/
theorem isRemSet_biUnion {Kc : Config S n R k0 K M k} (hKc : IsAdmConfig Kc)
    {𝒞 : Finset (Finset (ConfigPair S n M K k))} (h : IsClusterFamily Kc 𝒞) :
    IsRemSet Kc (𝒞.biUnion id) ∧ clusters S n M K k (𝒞.biUnion id) = 𝒞 := by
  obtain ⟨hcl, hcomp, hprod⟩ := h
  set Rm := 𝒞.biUnion id with hRm
  have hmemR : ∀ m, m ∈ Rm ↔ ∃ C ∈ 𝒞, m ∈ C := by
    intro m; simp [hRm, Finset.mem_biUnion]
  have hfar : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, C ≠ C' → ∀ a ∈ C, ∀ b ∈ C', ¬ Near4 S n M K k a b :=
    fun C hC C' hC' hne a ha b hb => disjoint_clusterSupp_iff.mp (hcomp C hC C' hC' hne) a ha b hb
  have hmem : ∀ m ∈ Rm, m.2 ∈ localizedHistories (S := S) (n := n) R k0 K M k m.1 := by
    intro m hm
    obtain ⟨C, hC, hmC⟩ := (hmemR m).mp hm
    exact (hcl C hC).mem_hist m hmC
  have hsepR : ∀ m ∈ Rm, ∀ m' ∈ Rm, m ≠ m' → ∀ x ∈ m.1, ∀ y ∈ m'.1, S.omega k ≤ supDist x y := by
    intro m hm m' hm' hne x hx y hy
    obtain ⟨C, hC, hmC⟩ := (hmemR m).mp hm
    obtain ⟨C', hC', hmC'⟩ := (hmemR m').mp hm'
    by_cases hCC : C = C'
    · subst hCC
      exact (hcl C hC).sep m hmC m' hmC' hne x hx y hy
    · by_contra hlt
      push Not at hlt
      exact hfar C hC C' hC' hCC m hmC m' hmC' ⟨x, hx, y, hy, by omega⟩
  have hsepK : ∀ m ∈ Rm, ∀ m' ∈ Kc.members, ∀ x ∈ m.1, ∀ y ∈ m'.1,
      S.omega k ≤ supDist x y := by
    intro m hm m' hm' x hx y hy
    obtain ⟨C, hC, hmC⟩ := (hmemR m).mp hm
    exact (hcl C hC).sepKept m hmC m' hm' x hx y hy
  have hdis : Disjoint Rm Kc.members := by
    rw [Finset.disjoint_left]
    intro m hm hmK
    obtain ⟨x, hx⟩ := pair_nonempty (hmem m hm)
    have := hsepK m hm m hmK x hx x hx
    rw [supDist_self] at this
    have := omega_ge_eleven S k
    omega
  let F := unionConfig Kc Rm hmem hsepR hsepK
  have hadm : IsAdmConfig F := by
    refine adm_of_cliques hk F fun Q hQ hQcl => ?_
    by_cases hQR : ∃ r ∈ Q, r ∈ Rm
    · obtain ⟨r, hrQ, hrR⟩ := hQR
      obtain ⟨C, hC, hrC⟩ := (hmemR r).mp hrR
      have hne0 : admFactor Kc C ≠ 0 := by
        intro h0
        have := Finset.prod_eq_zero hC h0
        rw [hprod] at this
        exact one_ne_zero this
      have hfam : IsAdmFamily (S := S) (n := n) R k0 K M k (C ∪ keptNear Kc C) := by
        by_contra hn'
        exact hne0 (by simp [admFactor, hn'])
      obtain ⟨G, hGm, hGadm⟩ := hfam
      have hQG : Q ⊆ G.members := by
        intro q hq
        rw [hGm]
        have hqF : q ∈ Kc.members ∪ Rm := hQ hq
        rcases Finset.mem_union.mp hqF with hqK | hqR
        · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hqK, ?_⟩)
          obtain ⟨x, hx, y, hy, hxy⟩ := hQcl q hq r hrQ
          exact ⟨x, hx, y, Set.mem_biUnion hrC hy, hxy⟩
        · obtain ⟨C', hC', hqC'⟩ := (hmemR q).mp hqR
          by_cases hCC : C = C'
          · subst hCC; exact Finset.mem_union_left _ hqC'
          · exfalso
            obtain ⟨x, hx, y, hy, hxy⟩ := hQcl r hrQ q hq
            exact hfar C hC C' hC' hCC r hrC q hqC' ⟨x, hx, y, hy, by omega⟩
      exact isAdmConfig_congr (F := G.sub Q hQG) (F' := F.sub Q hQ) rfl (adm_sub hk hGadm hQG)
    · push Not at hQR
      have hQK : Q ⊆ Kc.members := by
        intro q hq
        rcases Finset.mem_union.mp (hQ hq) with h' | h'
        · exact h'
        · exact absurd h' (hQR q hq)
      exact isAdmConfig_congr (F := Kc.sub Q hQK) (F' := F.sub Q hQ) rfl (adm_sub hk hKc hQK)
  have hclusters : ∀ C ∈ 𝒞, ∀ m ∈ C, clusterOf S n M K k Rm m = C := by
    intro C hC m hmC
    ext m'
    rw [mem_clusterOf]
    constructor
    · rintro ⟨hm'R, hrel⟩
      have key : ∀ c, ClusterRel S n M K k Rm m c → c ∈ C := by
        intro c hc
        induction hc with
        | refl => exact hmC
        | tail _ hbc ih =>
          obtain ⟨-, hcR, hnear⟩ := hbc
          obtain ⟨C', hC', hcC'⟩ := (hmemR _).mp hcR
          by_cases hCC : C = C'
          · subst hCC; exact hcC'
          · exact absurd hnear (hfar C hC C' hC' hCC _ ih _ hcC')
      exact key m' hrel
    · intro hm'C
      have hCR : C ⊆ Rm := fun x hx => (hmemR x).mpr ⟨C, hC, hx⟩
      refine ⟨hCR hm'C, ?_⟩
      have key : ∀ c, Relation.ReflTransGen
          (fun a b => a ∈ C ∧ b ∈ C ∧ Near4 S n M K k a b) m c → ClusterRel S n M K k Rm m c := by
        intro c hc
        induction hc with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih =>
          exact Relation.ReflTransGen.tail ih ⟨hCR hbc.1, hCR hbc.2.1, hbc.2.2⟩
      exact key m' ((hcl C hC).connected m hmC m' hm'C)
  refine ⟨⟨fun m hm => ?_, hdis, F, rfl, hadm⟩, ?_⟩
  · obtain ⟨C, hC, hmC⟩ := (hmemR m).mp hm
    exact (hcl C hC).ripe m hmC
  · ext C'
    simp only [clusters, Finset.mem_image]
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨C, hC, hmC⟩ := (hmemR m).mp hm
      rw [hclusters C hC m hmC]; exact hC
    · intro hC'
      obtain ⟨m, hm⟩ := (hcl C' hC').nonempty
      exact ⟨m, (hmemR m).mpr ⟨C', hC', hm⟩, hclusters C' hC' m hm⟩

/-- **Lemma III.10.4 (gas identity)**: for an admissible kept configuration `Kc`, the removed
parts `Rm` with `Kc ∪ Rm` admissible correspond bijectively, by `Rm ↦ clusters Rm`, to the
families of pairwise compatible removed clusters with `∏ admFactor = 1`. -/
theorem gas_identity {Kc : Config S n R k0 K M k} (hKc : IsAdmConfig Kc) :
    Set.BijOn (clusters S n M K k) {Rm | IsRemSet Kc Rm} {𝒞 | IsClusterFamily Kc 𝒞} := by
  refine ⟨fun Rm h => isClusterFamily_clusters hk h, fun Rm1 h1 Rm2 h2 he => ?_, fun 𝒞 h => ?_⟩
  · rw [← biUnion_clusters (Rm := Rm1), ← biUnion_clusters (Rm := Rm2)]
    exact congrArg (fun c => c.biUnion id) he
  · exact ⟨_, (isRemSet_biUnion hk hKc h).1, (isRemSet_biUnion hk hKc h).2⟩

end Main

/-- The region `Y_k = ⋃ Z` of a kept configuration. -/
def keptRegion (Kc : Config S n R k0 K M k) : Set (Torus S.d (n k)) :=
  ⋃ m ∈ Kc.members, ((m.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k)))

theorem keptNear_eq_empty (Kc : Config S n R k0 K M k) {C : Finset (ConfigPair S n M K k)}
    (h : Disjoint (clusterSupp S n M K k C) (keptRegion Kc)) : keptNear Kc C = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro q hq
  obtain ⟨hqK, x, hx, y, hy, hxy⟩ := Finset.mem_filter.mp hq
  simp only [clusterCore, Set.mem_iUnion, exists_prop] at hy
  obtain ⟨r, hrC, hyr⟩ := hy
  refine Set.disjoint_left.mp h ?_ (Set.mem_biUnion hqK hx)
  exact Set.mem_biUnion hrC (mem_nbhd.mpr ⟨y, hyr, hxy⟩)

/-- **Lemma III.10.4**, second half: the admissibility factor of a cluster does not depend on the
kept history if its support is disjoint from `Y_k`. -/
theorem admFactor_eq_of_supp_disjoint (Kc Kc' : Config S n R k0 K M k)
    (C : Finset (ConfigPair S n M K k))
    (h : Disjoint (clusterSupp S n M K k C) (keptRegion Kc))
    (h' : Disjoint (clusterSupp S n M K k C) (keptRegion Kc')) :
    admFactor Kc C = admFactor Kc' C := by
  simp only [admFactor, keptNear_eq_empty Kc h, keptNear_eq_empty Kc' h']

/-- Inhabitation of `RemCluster`: a single ripe member, separated from `Y_k`, is a removed
cluster. -/
theorem RemCluster.singleton (Kc : Config S n R k0 K M k) {m : ConfigPair S n M K k}
    (hr : IsRipeMember R k0 K M k m)
    (hh : m.2 ∈ localizedHistories (S := S) (n := n) R k0 K M k m.1)
    (hsep : ∀ m' ∈ Kc.members, ∀ x ∈ m.1, ∀ y ∈ m'.1, S.omega k ≤ supDist x y) :
    RemCluster Kc {m} where
  nonempty := Finset.singleton_nonempty m
  ripe := fun a ha => by rw [Finset.mem_singleton] at ha; exact ha ▸ hr
  mem_hist := fun a ha => by rw [Finset.mem_singleton] at ha; exact ha ▸ hh
  sep := fun a ha b hb hne => by
    rw [Finset.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hne
  sepKept := fun a ha m' hm' x hx y hy => by
    rw [Finset.mem_singleton] at ha
    exact hsep m' hm' x (ha ▸ hx) y hy
  connected := fun a ha b hb => by
    rw [Finset.mem_singleton] at ha hb
    rw [ha, hb]

/-- Inhabitation of `IsRemSet` and `IsClusterFamily`: the empty removed part. -/
theorem isRemSet_empty {Kc : Config S n R k0 K M k} (hKc : IsAdmConfig Kc) :
    IsRemSet Kc ∅ :=
  ⟨by simp, Finset.disjoint_empty_left _, ⟨Kc, by simp, hKc⟩⟩

theorem isClusterFamily_empty (Kc : Config S n R k0 K M k) : IsClusterFamily Kc ∅ :=
  ⟨by simp, by simp, by simp⟩

end Balaban.LargeField
