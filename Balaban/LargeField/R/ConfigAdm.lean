module

public import Balaban.LargeField.R.ConfigAssemble

/-!
# Lemma III.10.2 (cliques suffice)

* `adm_of_witness`: a configuration is admissible as soon as every clique of it occurs, with the
  same localized histories, in some history (`exists_assembled`);
* `adm_sub`: subfamilies of admissible configurations are admissible;
* `adm_of_cliques`: a configuration is admissible if every clique is admissible;
* `adm_iff_cliques`: **Lemma III.10.2**.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M k : ℕ} [NeZero M]

/-- A configuration is admissible if every clique of it occurs in some history with the same
localized histories (and some `FlowSteps` exist for the typing). -/
theorem adm_of_witness (hk : k ≤ K) (F0 : FlowSteps S n R k0 K) (G : HistConfig S n R k0 K M k)
    (hW : ∀ C ⊆ G.members, HistConfig.IsClique S n k M K C →
      ∃ H : RegionHistory S n R k0 K, ∀ m ∈ C, ∃ c : H.Comp k, c.1 = m.1 ∧
        H.localHistory M K k c = m.2) :
    IsAdmConfig G := by
  classical
  -- representatives of the members
  have hrep : ∀ m : G.members, ∃ (H' : RegionHistory S n R k0 K) (c : H'.Comp k),
      H' ∈ (RegionHistory.historiesWithFinal (R := R) (k0 := k0) (K := K) k m.1.1 :
        Set (RegionHistory S n R k0 K)) ∧ c.1 = m.1.1 ∧ H'.localHistory M K k c = m.1.2 := by
    intro m
    obtain ⟨H', hH', c, hc1, hc2⟩ := G.mem_hist m.1 m.2
    exact ⟨H', c, hH', hc1, hc2⟩
  choose Hm cm hHm hcm1 hcm2 using hrep
  have hsepZ : ∀ i ∈ (Finset.univ : Finset G.members), ∀ i' ∈ (Finset.univ : Finset G.members),
      i ≠ i' → ∀ x ∈ (cm i).1, ∀ y ∈ (cm i').1, S.omega k ≤ supDist x y := by
    intro i _ i' _ hne x hx y hy
    exact G.sep i.1 i.2 i'.1 i'.2 (fun h => hne (Subtype.ext h)) x (hcm1 i ▸ hx) y (hcm1 i' ▸ hy)
  have hcomps : ∀ i ∈ (Finset.univ : Finset G.members),
      comps (S.omega k) (cm i).1 = {(cm i).1} := by
    intro i _
    have := (hHm i).2.2
    rw [hcm1 i]
    exact this
  obtain ⟨H, hrem, hc1, hc2⟩ := exists_assembled (M := M) F0 hk hsepZ
    (by
      intro C _ hC
      obtain ⟨H, hH⟩ := hW (C.image Subtype.val) (by
        intro m hm
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hm
        exact i.2) (by
        intro m hm m' hm'
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
        obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hm'
        obtain ⟨x, hx, y, hy, hxy⟩ := hC i hi i' hi'
        exact ⟨x, hcm1 i ▸ hx, y, hcm1 i' ▸ hy, hxy⟩)
      refine ⟨H, fun i hi => ?_⟩
      obtain ⟨c, hc1, hc2⟩ := hH i.1 (Finset.mem_image_of_mem _ hi)
      exact ⟨c, hc1.trans (hcm1 i).symm, hc2.trans (hcm2 i).symm⟩)
    hcomps
  refine ⟨H, fun j c hc => by simp [hrem j] at hc, ?_, ?_⟩
  · intro c
    obtain ⟨i, -, hi⟩ := hc1 c
    exact ⟨i.1, i.2, (hcm1 i).symm.trans hi⟩
  · intro m hm
    obtain ⟨c, hc, hc'⟩ := hc2 ⟨m, hm⟩ (Finset.mem_univ _)
    exact ⟨c, hc.trans (hcm1 ⟨m, hm⟩), hc'.trans (hcm2 ⟨m, hm⟩)⟩

/-- **Lemma III.10.2**, subfamilies of admissible configurations are admissible. -/
theorem adm_sub (hk : k ≤ K) {F : HistConfig S n R k0 K M k} (hF : IsAdmConfig F)
    {G : Finset (Finset (Torus S.d (n k)) × LocalHistory S n M K)} (hG : G ⊆ F.members) :
    IsAdmConfig (F.sub G hG) := by
  obtain ⟨H, -, -, hc2⟩ := hF
  refine adm_of_witness hk H.F (F.sub G hG) fun C hC _ => ⟨H, fun m hm => ?_⟩
  exact hc2 m (hG (hC hm))

/-- **Lemma III.10.2**, a configuration is admissible if every clique is. -/
theorem adm_of_cliques (hk : k ≤ K) (F : HistConfig S n R k0 K M k)
    (hcl : ∀ (C : Finset (Finset (Torus S.d (n k)) × LocalHistory S n M K)) (hC : C ⊆ F.members),
      HistConfig.IsClique S n k M K C → IsAdmConfig (F.sub C hC)) : IsAdmConfig F := by
  obtain ⟨H0, -, -, -⟩ := hcl ∅ (Finset.empty_subset _) (by simp [HistConfig.IsClique])
  refine adm_of_witness hk H0.F F fun C hC hCl => ?_
  obtain ⟨H, -, -, hc2⟩ := hcl C hC hCl
  exact ⟨H, hc2⟩

/-- **Lemma III.10.2 (cliques suffice)**: a configuration is admissible iff every clique (a
subfamily whose members are pairwise linked) is admissible; subfamilies of admissible
configurations are admissible (`adm_sub`). -/
theorem adm_iff_cliques (hk : k ≤ K) (F : HistConfig S n R k0 K M k) :
    IsAdmConfig F ↔
      ∀ (C : Finset (Finset (Torus S.d (n k)) × LocalHistory S n M K)) (hC : C ⊆ F.members),
        HistConfig.IsClique S n k M K C → IsAdmConfig (F.sub C hC) :=
  ⟨fun hF _ hC _ => adm_sub hk hF hC, adm_of_cliques hk F⟩

end Balaban.LargeField
