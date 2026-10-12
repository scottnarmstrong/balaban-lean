module

public import Balaban.LargeField.R.StepGlueMain
public import Balaban.LargeField.R.LocalLemmas
public import Balaban.LargeField.R.Config
public import Balaban.LargeField.Budget.LogC
import Mathlib.Tactic.Linarith

/-!
# Assembling a history from localized histories (the history-level core of Lemma III.10.2)

Let `Hm i`, `i ∈ F`, be histories with components `cm i` of scale `k` whose sets are pairwise at
index distance `≥ ω_k`, and suppose that every clique (pairwise at index distance `≤ 2ω_k`) of
them occurs in one history with the same localized histories.  Then (`exists_assembled`) the
whole family occurs in one history without removals: at every scale `j < k` the localization
steps of the members are glued by `glue_step`, with the witnesses coming from the cliques.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban RegionHistory

section Assembly

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {M k : ℕ} [NeZero M] {ι : Type*} {F : Finset ι}
  {Hm : ι → RegionHistory S n R k0 K} {cm : ∀ i, (Hm i).Comp k}

/-- Two cubes in the lineages at scale `a ≤ k` of components of scale `k` of two histories lie over
points of the two components at index distance at most their own. -/
theorem exists_over_of_mem_lin {H1 H2 : RegionHistory S n R k0 K} {a : ℕ} (hak : a ≤ k)
    (hkK : k ≤ K) {Z1 : H1.Comp k} {Z2 : H2.Comp k} {w1 w2 : Torus S.d (n a)}
    (h1 : w1 ∈ ((H1.lin a k Z1 : Finset _) : Set _)) (h2 : w2 ∈ ((H2.lin a k Z2 : Finset _) : Set _)) :
    ∃ z1 ∈ Z1.1, ∃ z2 ∈ Z2.1, supDist z1 z2 ≤ supDist w1 w2 := by
  have hnn := H1.F.hnn
  have hL : 1 ≤ S.L := by have := H1.F.ok.two_le_L; omega
  have := H1.neZero_L
  obtain ⟨x1, hx1⟩ := cubeMap_surjective (S := S) (n := n) (M := 1) (K := K) hnn
    (hak.trans hkK) w1
  obtain ⟨x2, hx2⟩ := cubeMap_surjective (S := S) (n := n) (M := 1) (K := K) hnn
    (hak.trans hkK) w2
  refine ⟨cubeMap n S.L 1 K k x1, ?_, cubeMap n S.L 1 K k x2, ?_, ?_⟩
  · exact cubeMap_mem_of_lin hkK (hx1 ▸ h1)
  · exact cubeMap_mem_of_lin hkK (hx2 ▸ h2)
  · have := supDist_cubeMap_le hnn hL hak hkK x1 x2
    rwa [hx1, hx2] at this

variable (F0 : FlowSteps S n R k0 K) (hk : k ≤ K)
  (hsepZ : ∀ i ∈ F, ∀ i' ∈ F, i ≠ i' → ∀ x ∈ (cm i).1, ∀ y ∈ (cm i').1,
    S.omega k ≤ supDist x y)
  (hW : ∀ C ⊆ F, (∀ i ∈ C, ∀ i' ∈ C, ∃ x ∈ (cm i).1, ∃ y ∈ (cm i').1,
      supDist x y ≤ 2 * S.omega k) →
    ∃ H : RegionHistory S n R k0 K, ∀ i ∈ C, ∃ c : H.Comp k, c.1 = (cm i).1 ∧
      H.localHistory M K k c = (Hm i).localHistory M K k (cm i))

/-- The localization step of the member `i` at the scale `j`. -/
noncomputable abbrev locSt (Hm : ι → RegionHistory S n R k0 K) (cm : ∀ i, (Hm i).Comp k) (i : ι) (j : ℕ) :=
  ((Hm i).locRH k (cm i)).step j

theorem locSt_Zpre {j : ℕ} (hjk : j < k) (hk : k ≤ K) (i : ι) :
    (locSt Hm cm i j).Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1)) =
      ((Hm i).lin (j + 1) k (cm i) : Finset (Torus S.d (n (j + 1)))) :=
  locRH_Zpre (cm i) (show j + 1 ≤ k by omega) (show j + 1 ≤ K by omega)

include hsepZ hW hk F0

/-- The members' `Z^pre` at the scale `j + 1` are pairwise `ω_{j+1}`-separated. -/
theorem sep_locSt {j : ℕ} (hjk : j < k) :
    SepFam (S.omega (j + 1)) F
      (fun i => (locSt Hm cm i j).Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1))) := by
  classical
  intro i hi i' hi' hne w hw w' hw'
  change w ∈ (locSt Hm cm i j).Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1)) at hw
  change w' ∈ (locSt Hm cm i' j).Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1)) at hw'
  rw [locSt_Zpre hjk hk] at hw hw'
  have hmono : S.omega (j + 1) ≤ S.omega k := F0.ok.omega_mono (by omega)
  by_cases hl : ∃ x ∈ (cm i).1, ∃ y ∈ (cm i').1, supDist x y ≤ 2 * S.omega k
  · -- linked: use the witness for the pair
    have hne' : (cm i).1 ≠ (cm i').1 := by
      intro he
      obtain ⟨x, hx⟩ := comp_nonempty (cm i).2
      have := hsepZ i hi i' hi' hne x hx x (he ▸ hx)
      rw [supDist_self] at this
      have h13 : 13 ≤ S.omega k := by
        have := F0.ok.omega_mono (Nat.zero_le k)
        have h := le_omegaW S.L S.Rb S.lam 0
        rw [← Setting.omega_eq_omegaW] at h
        have := F0.ok.two_le_L
        omega
      omega
    obtain ⟨H, hH⟩ := hW {i, i'} (by
      intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption) (by
      intro a ha b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      have hself : ∀ c, ∃ x ∈ (cm c).1, ∃ y ∈ (cm c).1, supDist x y ≤ 2 * S.omega k := by
        intro c
        obtain ⟨x, hx⟩ := comp_nonempty (cm c).2
        exact ⟨x, hx, x, hx, by rw [supDist_self]; omega⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact hself _
      · exact hl
      · obtain ⟨x, hx, y, hy, hxy⟩ := hl
        exact ⟨y, hy, x, hx, by rwa [supDist_comm]⟩
      · exact hself _)
    obtain ⟨c, hc1, hc2⟩ := hH i (by simp)
    obtain ⟨c', hc1', hc2'⟩ := hH i' (by simp)
    have hlin : ∀ (a : ι) (ca : H.Comp k), ca.1 = (cm a).1 →
        H.localHistory M K k ca = (Hm a).localHistory M K k (cm a) →
        ((Hm a).lin (j + 1) k (cm a) : Finset (Torus S.d (n (j + 1)))) =
          H.lin (j + 1) k ca := fun a ca _ hca =>
      (lin_eq_of_localHistory_eq hk ca (cm a) hca (by omega)).symm
    rw [hlin i c hc1 hc2] at hw
    rw [hlin i' c' hc1' hc2'] at hw'
    have hcc : c ≠ c' := by
      intro he; subst he; exact hne' (hc1.symm.trans hc1')
    by_contra hlt
    push Not at hlt
    have hcl := lin_linkClosed (H := H) (j + 1) k c
    have hw'Z := lin_sub_Zpre (H := H) (j + 1) k c' (Finset.mem_coe.mp hw')
    have := hcl w (Finset.mem_coe.mp hw) w' hw'Z hlt
    exact Finset.disjoint_left.mp (RegionHistory.lin_disjoint H (j + 1) hcc)
      (Finset.mem_coe.mp this) (Finset.mem_coe.mp hw')
  · push Not at hl
    obtain ⟨z1, hz1, z2, hz2, hd⟩ := exists_over_of_mem_lin (H1 := Hm i) (H2 := Hm i')
      (a := j + 1) (by omega) hk (Finset.mem_coe.mp hw) (Finset.mem_coe.mp hw')
    have := hl z1 hz1 z2 hz2
    omega

theorem glueRadius_le {j : ℕ} (hjk : j < k) :
    glueRadius S.L (R j) ≤ S.omega (j + 1) := by
  have hg := F0.stepGeom (show j < K by omega)
  have := hg.rad.omega_rho
  unfold glueRadius
  have := hg.rad.L_two
  omega

/-- The members near a point are pairwise linked. -/
theorem near_linked {j : ℕ} (hjk : j < k) (x : Torus S.d (n (j + 1))) :
    ∀ i ∈ near (critOpt S k0 (j + 1)) F (fun i => locSt Hm cm i j) (S.omega (j + 1)) x,
      ∀ i' ∈ near (critOpt S k0 (j + 1)) F (fun i => locSt Hm cm i j) (S.omega (j + 1)) x,
      ∃ a ∈ (cm i).1, ∃ b ∈ (cm i').1, supDist a b ≤ 2 * S.omega k := by
  classical
  intro i hi i' hi'
  simp only [near, Finset.mem_filter] at hi hi'
  obtain ⟨-, w, hw, hxw⟩ := hi
  obtain ⟨-, w', hw', hxw'⟩ := hi'
  change w ∈ (locSt Hm cm i j).Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1)) at hw
  change w' ∈ (locSt Hm cm i' j).Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1)) at hw'
  rw [locSt_Zpre hjk hk] at hw hw'
  obtain ⟨z1, hz1, z2, hz2, hd⟩ := exists_over_of_mem_lin (H1 := Hm i) (H2 := Hm i')
    (a := j + 1) (by omega) hk (Finset.mem_coe.mp hw) (Finset.mem_coe.mp hw')
  refine ⟨z1, hz1, z2, hz2, ?_⟩
  have h1 := supDist_triangle w x w'
  have h2 : supDist w x = supDist x w := supDist_comm _ _
  have h3 := glueRadius_le F0 hk hsepZ hW hjk
  have h4 : S.omega (j + 1) ≤ S.omega k := F0.ok.omega_mono (by omega)
  omega

theorem witness_locSt {j : ℕ} (hjk : j < k) (x : Torus S.d (n (j + 1))) :
    Witness (S.omega (j + 1)) (critOpt S k0 (j + 1)) (fun i => locSt Hm cm i j)
      (near (critOpt S k0 (j + 1)) F (fun i => locSt Hm cm i j) (S.omega (j + 1)) x) := by
  classical
  set C := near (critOpt S k0 (j + 1)) F (fun i => locSt Hm cm i j) (S.omega (j + 1)) x with hC
  obtain ⟨H, hH⟩ := hW C (near_subset x) (near_linked F0 hk hsepZ hW hjk x)
  refine ⟨H.step j, fun i => if h : i ∈ C then
    ((H.lin (j + 1) k (Classical.choose (hH i h)) : Finset (Torus S.d (n (j + 1)))) :
      Set (Torus S.d (n (j + 1)))) else ∅, ?_, ?_⟩
  · intro i hi
    simp only [hi, dite_true]
    exact lin_linkClosed (H := H) (j + 1) k _
  · intro i hi
    simp only [hi, dite_true]
    obtain ⟨hc1, hc2⟩ := Classical.choose_spec (hH i hi)
    have := locRH_step_eq_of_localHistory_eq hk (cm i) (Classical.choose (hH i hi)) hc1.symm
      hc2.symm j
    show ((Hm i).locRH k (cm i)).step j = _
    rw [this]
    exact locRH_step (Classical.choose (hH i hi)) hjk (by omega)

/-- The properties of the glued step. -/
def GlueProps {j : ℕ} (F : Finset ι) (st : ι → RegionStep S.d S.L (n j) (n (j + 1)) (R (j - 1)) (R j))
    (ω : ℕ) (crit : Option ℕ) (u : RegionStep S.d S.L (n j) (n (j + 1)) (R (j - 1)) (R j)) :
    Prop :=
  u.Z = ⋃ i ∈ F, (st i).Z ∧ u.P = ⋃ i ∈ F, (st i).P ∧ u.Q = ⋃ i ∈ F, (st i).Q ∧
    u.R = ⋃ i ∈ F, (st i).R ∧ u.S = ⋃ i ∈ F, (st i).S ∧
    u.Z0 = ⋃ i ∈ F, (st i).Z0 ∧ u.Zpre ω crit = ⋃ i ∈ F, (st i).Zpre ω crit ∧
    ∀ i ∈ F, u.restrict ((st i).Zpre ω crit) = st i

theorem exists_glue {j : ℕ} (hjk : j < k) :
    ∃ u : RegionStep S.d S.L (n j) (n (j + 1)) (R (j - 1)) (R j),
      GlueProps F (fun i => locSt Hm cm i j) (S.omega (j + 1)) (critOpt S k0 (j + 1)) u := by
  have hg := F0.stepGeom (show j < K by omega)
  exact glue_step hg.hn hg.rad (witness_locSt F0 hk hsepZ hW hjk)
    (sep_locSt F0 hk hsepZ hW hjk)

omit hsepZ hW hk F0 in
/-- The regions `Z^pre_j` of the assembled history: the union of the lineages up to scale `k`, then
the regions of steps without new cubes. -/
noncomputable def asmZ (F : Finset ι) (Hm : ι → RegionHistory S n R k0 K)
    (cm : ∀ i, (Hm i).Comp k) : ∀ j, Set (Torus S.d (n j))
  | 0 => ∅
  | j + 1 =>
    if j + 1 ≤ k then ⋃ i ∈ F, (((Hm i).lin (j + 1) k (cm i) : Finset (Torus S.d (n (j + 1)))) :
        Set (Torus S.d (n (j + 1))))
    else (emptyStep S n R j (asmZ F Hm cm j)).Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1))

omit hsepZ hW hk F0 in
theorem asmZ_of_le {j : ℕ} (hj : j ≤ k) :
    asmZ F Hm cm j = ⋃ i ∈ F, (((Hm i).lin j k (cm i) : Finset (Torus S.d (n j))) :
        Set (Torus S.d (n j))) := by
  cases j with
  | zero => simp [asmZ, lin_zero]
  | succ j => simp [asmZ, hj]

omit hsepZ hW hk in
open Classical in
/-- The steps of the assembled history. -/
noncomputable def asmStep (F : Finset ι)
    (Hm : ι → RegionHistory S n R k0 K) (cm : ∀ i, (Hm i).Comp k) (j : ℕ) :
    RegionStep S.d S.L (n j) (n (j + 1)) (R (j - 1)) (R j) :=
  if j < k then
    (if h : ∃ u : RegionStep S.d S.L (n j) (n (j + 1)) (R (j - 1)) (R j),
        GlueProps F (fun i => locSt Hm cm i j) (S.omega (j + 1)) (critOpt S k0 (j + 1)) u
      then h.choose else emptyStep S n R j (asmZ F Hm cm j))
  else emptyStep S n R j (asmZ F Hm cm j)

omit hsepZ hW hk in
/-- The assembled flow. -/
noncomputable def asmF (F0 : FlowSteps S n R k0 K) (F : Finset ι)
    (Hm : ι → RegionHistory S n R k0 K) (cm : ∀ i, (Hm i).Comp k) : FlowSteps S n R k0 K :=
  { F0 with step := asmStep F Hm cm }

theorem asmStep_spec {j : ℕ} (hjk : j < k) :
    GlueProps F (fun i => locSt Hm cm i j) (S.omega (j + 1)) (critOpt S k0 (j + 1))
      (asmStep F Hm cm j) := by
  classical
  have h := exists_glue F0 hk hsepZ hW hjk
  unfold asmStep
  simp only [hjk, ↓reduceIte, h, ↓reduceDIte]
  exact h.choose_spec

theorem asmStep_Z (j : ℕ) : (asmStep F Hm cm j).Z = asmZ F Hm cm j := by
  by_cases hjk : j < k
  · have := (asmStep_spec F0 hk hsepZ hW hjk).1
    rw [this, asmZ_of_le hjk.le]
    refine Set.iUnion₂_congr fun i _ => ?_
    exact locRH_Z (cm i) hjk.le (by omega)
  · unfold asmStep
    simp only [hjk, ↓reduceIte]
    rfl

theorem asmF_Zpre (j : ℕ) : (asmF F0 F Hm cm).Zpre j = asmZ F Hm cm j := by
  cases j with
  | zero => rfl
  | succ j =>
    show ((asmF F0 F Hm cm).step j).Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1)) = _
    by_cases hjk : j < k
    · have h := (asmStep_spec F0 hk hsepZ hW hjk).2.2.2.2.2.2.1
      show (asmStep F Hm cm j).Zpre _ _ = _
      rw [h, asmZ_of_le (show j + 1 ≤ k by omega)]
      refine Set.iUnion₂_congr fun i _ => ?_
      exact locSt_Zpre hjk hk i
    · have : ¬ (j + 1 ≤ k) := by omega
      show (asmStep F Hm cm j).Zpre _ _ = _
      unfold asmStep
      simp only [hjk, ↓reduceIte]
      simp [asmZ, this]

omit hsepZ hW hk F0 in
/-- The assembled history: no removals. -/
noncomputable def asmRH (F0 : FlowSteps S n R k0 K) (F : Finset ι) (Hm : ι → RegionHistory S n R k0 K)
    (cm : ∀ i, (Hm i).Comp k) (hz : ∀ j, (asmStep F Hm cm j).Z = (asmF F0 F Hm cm).Zpre j) :
    RegionHistory S n R k0 K where
  F := asmF F0 F Hm cm
  rem := fun _ => ∅
  rem_sub := fun _ => Finset.empty_subset _
  rem_empty := fun _ _ => rfl
  Z_eq := fun j => by
    show (asmStep F Hm cm j).Z = (asmF F0 F Hm cm).Zpre j \ ⋃ c ∈ (∅ : Finset (Finset (Torus S.d (n j)))),
      (c : Set (Torus S.d (n j)))
    rw [hz j]; simp

theorem asmStep_Zpre_eq (j : ℕ) :
    (asmStep F Hm cm j).Z = (asmF F0 F Hm cm).Zpre j := by
  rw [asmStep_Z F0 hk hsepZ hW, asmF_Zpre F0 hk hsepZ hW]

theorem lin_asm_eq (H : RegionHistory S n R k0 K) (hrem : ∀ j, H.rem j = ∅)
    (hZpre : ∀ j, H.F.Zpre j = asmZ F Hm cm j) {i : ι} (hi : i ∈ F)
    {c : H.Comp k} (hc : c.1 = (cm i).1) {j : ℕ} (hj : j ≤ k) :
    H.lin j k c = (Hm i).lin j k (cm i) := by
  have := H.neZero_L
  ext y
  obtain ⟨x, rfl⟩ := cubeMap_surjective (S := S) (n := n) (M := 1) (K := K) H.F.hnn
    (hj.trans hk) y
  rw [← Finset.mem_coe, ← Finset.mem_coe (s := (Hm i).lin j k (cm i)),
    mem_lin_iff_of_rem hrem hj hk]
  constructor
  · rintro ⟨hz, hxc⟩
    rw [hZpre j, asmZ_of_le hj] at hz
    simp only [Set.mem_iUnion, exists_prop] at hz
    obtain ⟨i', hi', hyi'⟩ := hz
    have h1 := cubeMap_mem_of_lin hk (M := 1) (Finset.mem_coe.mp hyi')
    by_cases hii : i' = i
    · subst hii; exact hyi'
    · have := hsepZ i' hi' i hi hii _ h1 _ (hc ▸ hxc)
      rw [supDist_self] at this
      have h13 : 13 ≤ S.omega k := by
        have h := le_omegaW S.L S.Rb S.lam k
        rw [← Setting.omega_eq_omegaW] at h
        have := F0.ok.two_le_L
        omega
      omega
  · intro hy
    refine ⟨?_, hc ▸ cubeMap_mem_of_lin hk (M := 1) hy⟩
    rw [hZpre j, asmZ_of_le hj]
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨i, hi, hy⟩

variable (hcomps : ∀ i ∈ F, comps (S.omega k) (cm i).1 = {(cm i).1})

include hcomps in
/-- **Assembly of a history from localized histories** (the history-level core of
Lemma III.10.2): if every clique of the family occurs in one history with the same localized
histories, then the whole family occurs in one history without removals. -/
theorem exists_assembled :
    ∃ H : RegionHistory S n R k0 K, (∀ j, H.rem j = ∅) ∧
      (∀ c : H.Comp k, ∃ i ∈ F, (cm i).1 = c.1) ∧
      ∀ i ∈ F, ∃ c : H.Comp k, c.1 = (cm i).1 ∧
        H.localHistory M K k c = (Hm i).localHistory M K k (cm i) := by
  classical
  set H := asmRH F0 F Hm cm (asmStep_Zpre_eq F0 hk hsepZ hW) with hH
  have hrem : ∀ j, H.rem j = ∅ := fun _ => rfl
  have hZk : H.F.Zpre k = ⋃ i ∈ F, (((cm i).1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) := by
    show (asmF F0 F Hm cm).Zpre k = _
    rw [asmF_Zpre F0 hk hsepZ hW, asmZ_of_le le_rfl]
    refine Set.iUnion₂_congr fun i _ => ?_
    rw [lin_self]
  have hsepF : SepFam (S.omega k) F (fun i => (((cm i).1 : Finset (Torus S.d (n k))) :
      Set (Torus S.d (n k)))) := fun i hi i' hi' hne x hx y hy => hsepZ i hi i' hi' hne x hx y hy
  have hcompsH : ∀ Y, Y ∈ comps (S.omega k) (H.Zp k) ↔
      ∃ i ∈ F, Y ∈ comps (S.omega k) (cm i).1 := by
    intro Y
    show Y ∈ comps (S.omega k) (finOf (H.F.Zpre k)) ↔ _
    rw [hZk, mem_comps_iUnion_sep hsepF]
    simp only [finOf_coe_finset]
  refine ⟨H, hrem, ?_, ?_⟩
  · intro c
    obtain ⟨i, hi, hc⟩ := (hcompsH c.1).mp c.2
    rw [hcomps i hi, Finset.mem_singleton] at hc
    exact ⟨i, hi, hc.symm⟩
  · intro i hi
    have hmem : (cm i).1 ∈ comps (S.omega k) (H.Zp k) :=
      (hcompsH _).mpr ⟨i, hi, by rw [hcomps i hi]; simp⟩
    refine ⟨⟨(cm i).1, hmem⟩, rfl, ?_⟩
    have hZ : ∀ j, H.F.Zpre j = asmZ F Hm cm j := fun j => asmF_Zpre F0 hk hsepZ hW j
    have hlin : ∀ j, j ≤ k → H.lin j k ⟨(cm i).1, hmem⟩ = (Hm i).lin j k (cm i) :=
      fun j hj => lin_asm_eq F0 hk hsepZ hW H hrem hZ hi (c := ⟨(cm i).1, hmem⟩) rfl hj
    have key : ∀ j, j < k → (asmStep F Hm cm j).restrict
        (((Hm i).lin (j + 1) k (cm i) : Finset (Torus S.d (n (j + 1)))) :
          Set (Torus S.d (n (j + 1)))) = locSt Hm cm i j := fun j hj => by
      have hrs := (asmStep_spec F0 hk hsepZ hW hj).2.2.2.2.2.2.2 i hi
      rwa [locSt_Zpre hj hk i] at hrs
    have hstep : ∀ j, (H.locRH k ⟨(cm i).1, hmem⟩).step j = ((Hm i).locRH k (cm i)).step j := by
      refine locRH_step_congr hk ⟨(cm i).1, hmem⟩ (cm i) rfl hlin ?_ ?_ ?_ ?_
      · intro j hj
        rw [hlin (j + 1) hj]
        exact (congrArg RegionStep.P (key j hj)).trans (locRH_new (cm i) hj (by omega)).1
      · intro j hj
        rw [hlin (j + 1) hj]
        exact (congrArg RegionStep.Q (key j hj)).trans (locRH_new (cm i) hj (by omega)).2.1
      · intro j hj
        rw [hlin (j + 1) hj]
        exact (congrArg RegionStep.R (key j hj)).trans (locRH_new (cm i) hj (by omega)).2.2.1
      · intro j hj
        rw [hlin (j + 1) hj]
        exact (congrArg RegionStep.S (key j hj)).trans (locRH_new (cm i) hj (by omega)).2.2.2
    exact localHistory_congr _ _ rfl hstep

end Assembly

end Balaban.LargeField
