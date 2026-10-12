module

public import Balaban.LargeField.Region.Inclusions
import Mathlib.Tactic.Linarith

/-!
# Seeds and attribution (Part I, Definition I.3.6, Lemmas I.3.7 and I.3.8)

The *seeds* of the step `k → k+1` are the coarsenings `Z^↑` of the components `Z` of `Z_k`
(*old seeds*) and the singletons `{q}`, `q ∈ 𝒩_{k+1}` (*new seeds*). Lemma I.3.7: seeds lie in
one component of `Z^{(0)}` (hence of `Z^pre`) and are pairwise disjoint. Lemma I.3.8 (this is
(G1) of §I.5.2): under the radius hypotheses (RH) every `x ∈ Z^{(0)}` is joined by a chain in
`Z^{(0)}` of steps `< ω_{k+1}` to a seed `σ`, at distance `≤ s_σ r_k` with `s_σ = 4` for old and
`5` for new seeds.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-- The numerical facts about the radii used by the proofs of Lemmas I.3.8-I.3.9: `r` is the
radius unit `r_k = ⌈R_base λ_k²⌉`, `ω = ω_{k+1}`. They follow from (RH) (`StepRadii.of_radiusHyp`). -/
structure StepRadii (L ω r : ℕ) (Rprev Rk : ℝ) : Prop where
  L_two : 2 ≤ L
  r_base : 4 * L + 20 ≤ r
  rho_le : ⌊Rk⌋₊ ≤ r
  rhoPrev_le : ⌊Rprev⌋₊ ≤ r
  rho2_le : ⌊2 * Rk⌋₊ ≤ 2 * r
  rho2_le' : ⌊2 * Rk⌋₊ ≤ 2 * ⌊Rk⌋₊ + 1
  omega_rho : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω
  omega_rhoPrev : ⌊Rprev⌋₊ + 2 ≤ ω

theorem StepRadii.of_real {L ω : ℕ} {Rprev Rk x : ℝ} (hL : 2 ≤ L) (hRk0 : 0 ≤ Rk) (hRk : Rk ≤ x)
    (hRp : Rprev ≤ x) (hx : (4 * L + 20 : ℝ) ≤ x)
    (hω : ω = 2 * ⌊x⌋₊ + L + 11) : StepRadii L ω ⌈x⌉₊ Rprev Rk := by
  have hx0 : 0 ≤ x := by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have hb : ⌊Rk⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor hRk
  have hbp : ⌊Rprev⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor hRp
  have hbr : ⌊x⌋₊ ≤ ⌈x⌉₊ := Nat.floor_le_ceil x
  have hxr : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  refine ⟨hL, ?_, hb.trans hbr, hbp.trans hbr, ?_, ?_, by omega, by omega⟩
  · have : ((4 * L + 20 : ℕ) : ℝ) ≤ (⌈x⌉₊ : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have h1 : (⌊2 * Rk⌋₊ : ℝ) ≤ 2 * Rk := Nat.floor_le (by linarith)
    have : (⌊2 * Rk⌋₊ : ℝ) ≤ ((2 * ⌈x⌉₊ : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have h1 := Nat.lt_floor_add_one Rk
    have h2 : ⌊2 * Rk⌋₊ < 2 * ⌊Rk⌋₊ + 2 := by
      rw [Nat.floor_lt (by linarith)]
      push_cast
      linarith
    omega

theorem RadiusHyp.stepRadii {L : ℕ} {Rbase : ℝ} {lam R : ℕ → ℝ} (h : RadiusHyp L Rbase lam R)
    (hL : 2 ≤ L) (k : ℕ) {Rprev Rk : ℝ} (hRk : Rk = R k)
    (hRp : Rprev ≤ Rbase * lam k ^ 2) :
    StepRadii L (omegaW L Rbase lam (k + 1)) (radiusUnit Rbase lam k) Rprev Rk := by
  have hlam : 1 ≤ lam k ^ 2 := one_le_pow₀ (h.one_le k)
  have hx : (4 * L + 20 : ℝ) ≤ Rbase * lam k ^ 2 := by
    have : 0 ≤ Rbase := by linarith [h.base, (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
    nlinarith [h.base]
  exact StepRadii.of_real hL (hRk ▸ h.nonneg k) (hRk ▸ h.le k) hRp hx rfl

theorem RadiusHyp.prev_le {L : ℕ} {Rbase : ℝ} {lam R : ℕ → ℝ} (h : RadiusHyp L Rbase lam R)
    {k : ℕ} (hk : 1 ≤ k) : R (k - 1) ≤ Rbase * lam k ^ 2 := by
  have h1 := h.le (k - 1)
  have h2 : lam (k - 1) ≤ lam k := h.mono (by omega)
  have h3 : 0 ≤ Rbase := by linarith [h.base, (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  have h4 : 0 ≤ lam (k - 1) := by linarith [h.one_le (k - 1)]
  calc R (k - 1) ≤ Rbase * lam (k - 1) ^ 2 := h1
    _ ≤ Rbase * lam k ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h4 h2 2) h3

theorem le_omegaW (L : ℕ) (Rbase : ℝ) (lam : ℕ → ℝ) (j : ℕ) : L + 11 ≤ omegaW L Rbase lam j := by
  cases j with
  | zero => simp [omegaW]
  | succ j => simp only [omegaW]; omega

theorem RadiusHyp.omegaW_le_succ {L : ℕ} {Rbase : ℝ} {lam R : ℕ → ℝ} (h : RadiusHyp L Rbase lam R)
    (j : ℕ) : omegaW L Rbase lam j ≤ omegaW L Rbase lam (j + 1) := by
  cases j with
  | zero => simp [omegaW]
  | succ j =>
    have h3 : 0 ≤ Rbase := by linarith [h.base, (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
    have h4 : 0 ≤ lam j := by linarith [h.one_le j]
    have : ⌊Rbase * lam j ^ 2⌋₊ ≤ ⌊Rbase * lam (j + 1) ^ 2⌋₊ :=
      Nat.floor_le_floor (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h4 (h.mono (Nat.le_succ j)) 2) h3)
    simp only [omegaW]
    omega

/-- `⌈(ω_k - 1)/L⌉ < ω_{k+1}`, the width condition of Lemma I.3.7 (a). -/
theorem coarse_width_lt {L ωk ω : ℕ} (hL : 2 ≤ L) (h1 : ωk ≤ ω) (h2 : L + 11 ≤ ω) :
    (ωk + L - 2) / L < ω :=
  lt_of_le_of_lt (Nat.div_le_div_left hL (by omega)) (by omega)

namespace RegionStep

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ}
  (st : RegionStep d L n0 n1 Rprev Rk)

/-! ### Seeds -/

/-- The old seeds `Z^↑`, `Z` a component of `Z_k` (for the width `ω_k`). -/
def oldSeeds (ωk : ℕ) : Set (Set (Torus d n1)) :=
  {σ | ∃ Y ∈ comps ωk (finOf st.Z), σ = blockMap L n1 '' (Y : Set (Torus d n0))}

/-- The new seeds `{q}`, `q ∈ 𝒩_{k+1}`. -/
def newSeeds : Set (Set (Torus d n1)) := {σ | ∃ q ∈ st.newCubes, σ = {q}}

/-- **Definition I.3.6**: the seeds of the step. -/
def seeds (ωk : ℕ) : Set (Set (Torus d n1)) := st.oldSeeds ωk ∪ st.newSeeds

open Classical in
/-- The seed weight `s_σ = s_* = 4` (old) or `s' = 5` (new). -/
noncomputable def seedWeight (ωk : ℕ) (σ : Set (Torus d n1)) : ℕ :=
  if σ ∈ st.oldSeeds ωk then 4 else 5

theorem Z_subset_U : st.Z ⊆ st.U := subset_nbhd _ _

theorem blockMap_Z_subset_Uprime {z : Torus d n0} (hz : z ∈ st.Z) :
    blockMap L n1 z ∈ st.Uprime := ⟨z, st.Z_subset_U hz, rfl⟩

theorem oldSeed_subset_Uprime {ωk : ℕ} {σ : Set (Torus d n1)} (hσ : σ ∈ st.oldSeeds ωk) :
    σ ⊆ st.Uprime := by
  obtain ⟨Y, hY, rfl⟩ := hσ
  rintro _ ⟨y, hy, rfl⟩
  exact st.blockMap_Z_subset_Uprime (mem_finOf.mp (comp_subset hY hy))

/-- **Lemma I.3.7 (a)**, first part: seeds lie in `Z^{(0)}`. -/
theorem seed_subset_Z0 {ωk : ℕ} {σ : Set (Torus d n1)} (hσ : σ ∈ st.seeds ωk) : σ ⊆ st.Z0 := by
  rcases hσ with hσ | ⟨q, hq, rfl⟩
  · exact (st.oldSeed_subset_Uprime hσ).trans st.Uprime_subset_Z0
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ st.newCubes_subset_Z0 hq

/-- New cubes are disjoint from `U'`. -/
theorem newCubes_disjoint_Uprime : Disjoint st.newCubes st.Uprime := by
  rw [Set.disjoint_right]
  intro u hu hq
  have hnot : ∀ w ∈ st.OmegaPrime, w ∉ nbhd (⌊Rk⌋₊ + 4) st.Uprime := fun w hw hw' =>
    st.nbhd_Uprime_subset hw' hw
  have hUP : u ∉ st.OmegaPrime := fun h => hnot u h (subset_nbhd _ _ hu)
  rcases hq with ((hq | hq) | hq) | hq
  · exact hUP (st.P_sub hq)
  · -- Q ⊆ Ω^{∼3}
    obtain ⟨w, hw, huw⟩ := mem_nbhd.mp (st.Q_sub hq)
    refine hnot w (st.Omega_subset_OmegaPrime hw) (mem_nbhd.mpr ⟨u, hu, ?_⟩)
    rw [supDist_comm]; omega
  · exact hUP (st.Omega_subset_OmegaPrime (st.R_sub hq))
  · exact hUP (st.Omega_subset_OmegaPrime
      (st.OmegaDD_subset_Omega (nbhdNeg_subset _ _ (st.S_sub hq))))

/-- Linkage in `Z_k` (width `ω_k`) gives linkage of the coarsenings in `Z^{(0)}` (width `ω_{k+1}`),
provided `⌈(ω_k - 1)/L⌉ < ω_{k+1}`. -/
theorem linked_coarsen (hn : n0 = L * n1) {ωk ω : ℕ} (hlt : (ωk + L - 2) / L < ω)
    {x y : Torus d n0} (h : Linked ωk (st.Z : Set (Torus d n0)) x y) :
    Linked ω st.Z0 (blockMap L n1 x) (blockMap L n1 y) := by
  induction h with
  | refl => exact Linked.refl _
  | tail _ hbc ih =>
    refine ih.trans (Linked.single ?_ ?_ ?_)
    · exact st.Uprime_subset_Z0 (st.blockMap_Z_subset_Uprime hbc.1)
    · exact st.Uprime_subset_Z0 (st.blockMap_Z_subset_Uprime hbc.2.1)
    · refine lt_of_le_of_lt (supDist_blockMap_le hn _ _) (lt_of_le_of_lt ?_ hlt)
      exact Nat.div_le_div_right (by have := hbc.2.2; omega)

/-- **Lemma I.3.7 (a)**: every seed lies in one component of `Z^{(0)}`. Here
`⌈(ω_k - 1)/L⌉ < ω_{k+1}` (in the flow: `ω_k ≤ ω_{k+1}`, `L + 11 ≤ ω_{k+1}`, `L ≥ 2`). -/
theorem seed_in_comp (hn : n0 = L * n1) {ωk ω : ℕ} (hlt : (ωk + L - 2) / L < ω)
    {σ : Set (Torus d n1)} (hσ : σ ∈ st.seeds ωk) :
    ∃ C ∈ comps ω (finOf st.Z0), σ ⊆ (C : Set (Torus d n1)) := by
  classical
  rcases hσ with ⟨Y, hY, rfl⟩ | ⟨q, hq, rfl⟩
  · obtain ⟨y0, hy0⟩ := comp_nonempty hY
    obtain ⟨C, hC, hSC⟩ := exists_comp_of_linked (ω := ω) (X := finOf st.Z0)
      (S := Finset.image (blockMap L n1) Y)
      (by
        intro s hs
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
        exact mem_finOf.mpr (st.Uprime_subset_Z0
          (st.blockMap_Z_subset_Uprime (mem_finOf.mp (comp_subset hY hx)))))
      ⟨_, Finset.mem_image_of_mem _ hy0⟩
      (by
        intro s hs t ht
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
        have := ((mem_comp_iff hY hx).mp hy).2
        rw [coe_finOf] at this
        have h2 := st.linked_coarsen hn hlt this
        rwa [coe_finOf])
    refine ⟨C, hC, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hSC (Finset.mem_image_of_mem _ hx)
  · obtain ⟨C, hC, hqC⟩ := mem_comp_self (ω := ω) (mem_finOf.mpr (st.newCubes_subset_Z0 hq))
    exact ⟨C, hC, by rintro x rfl; exact hqC⟩

/-- **Lemma I.3.7 (a)**, `Z^pre` form: a seed lies in one component of `Z^pre`. -/
theorem seed_in_comp_Zpre (hn : n0 = L * n1) {ωk ω : ℕ} (hlt : (ωk + L - 2) / L < ω)
    (crit : Option ℕ) {σ : Set (Torus d n1)} (hσ : σ ∈ st.seeds ωk) :
    ∃ C ∈ comps ω (finOf (st.Zpre ω crit)), σ ⊆ (C : Set (Torus d n1)) := by
  obtain ⟨C, hC, hσC⟩ := st.seed_in_comp hn hlt hσ
  obtain ⟨C', hC', hCC'⟩ := comp_mono (finOf_subset_finOf (st.Z0_subset_Zpre ω crit)) hC
  exact ⟨C', hC', hσC.trans fun x hx => hCC' hx⟩

/-- **Lemma I.3.7 (b)**: distinct seeds are disjoint (`L ≤ ω_k`). -/
theorem seeds_pairwise_disjoint (hn : n0 = L * n1) (hL : 0 < L) {ωk : ℕ} (hωk : L ≤ ωk)
    {σ σ' : Set (Torus d n1)} (hσ : σ ∈ st.seeds ωk) (hσ' : σ' ∈ st.seeds ωk) (hne : σ ≠ σ') :
    Disjoint σ σ' := by
  have hnew : ∀ q ∈ st.newCubes, ∀ τ ∈ st.oldSeeds ωk, q ∉ τ := fun q hq τ hτ hqτ =>
    (Set.disjoint_left.mp st.newCubes_disjoint_Uprime) hq (st.oldSeed_subset_Uprime hτ hqτ)
  rcases hσ with ⟨Y, hY, rfl⟩ | ⟨q, hq, rfl⟩ <;> rcases hσ' with ⟨Y', hY', rfl⟩ | ⟨q', hq', rfl⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    by_cases hYY : Y = Y'
    · exact hne (by rw [hYY])
    · have h1 := comps_sep hY hY' hYY hx hy
      have h2 := supDist_le_of_blockMap_eq hn hxy.symm
      omega
  · rw [Set.disjoint_singleton_right]
    exact hnew q' hq' _ ⟨Y, hY, rfl⟩
  · rw [Set.disjoint_singleton_left]
    exact hnew q hq _ ⟨Y', hY', rfl⟩
  · rw [Set.disjoint_singleton]
    intro h; exact hne (by rw [h])

/-! ### Lemma I.3.8: attribution -/

/-- **Lemma I.3.8 (attribution; this is (G1) of §I.5.2)**. Under the numerical facts `StepRadii`
(a consequence of (RH), see `attribution_of_radiusHyp`): every `x ∈ Z^{(0)}` is linked in `Z^{(0)}`
(width `ω = ω_{k+1}`) to a point `y` of an old seed with `d(x, y) ≤ 4 r`, or to a new cube `q`
with `d(x, q) ≤ 5 r`; here `r = r_k`. -/
theorem attribution {ωk ω r : ℕ} (h : StepRadii L ω r Rprev Rk) (hn : n0 = L * n1)
    {x : Torus d n1} (hx : x ∈ st.Z0) :
    (∃ Y ∈ comps ωk (finOf st.Z), ∃ y ∈ blockMap L n1 '' (Y : Set (Torus d n0)),
        supDist x y ≤ 4 * r ∧ Linked ω st.Z0 x y) ∨
    (∃ q ∈ st.newCubes, supDist x q ≤ 5 * r ∧ Linked ω st.Z0 x q) := by
  obtain ⟨hL2, hr, hρ, hρp, hρ2, hρ2', hωρ, hωp⟩ := h
  have hL : 0 < L := by omega
  have lk : ∀ a b, a ∈ st.Z0 → b ∈ st.Z0 → supDist a b < ω → Linked ω st.Z0 a b :=
    fun a b ha hb hab => Linked.single ha hb hab
  have tri : ∀ a b c : Torus d n1, supDist a c ≤ supDist a b + supDist b c := supDist_triangle
  obtain ⟨f, hfF, hxf⟩ := mem_nbhd.mp (st.Z0_subset_nbhd_FZ hL hx)
  obtain ⟨y1, h1, h2⟩ := exists_split (x := x) (z := f) (a := L - 1) (b := ⌊2 * Rk⌋₊ + 2)
    (by omega)
  have hy1 : y1 ∈ st.Z0 := st.nbhd_FZ_subset_Z0 (mem_nbhd.mpr ⟨f, hfF, h2⟩)
  have hfZ : f ∈ st.Z0 := st.FZ_subset_Z0 hfF
  have lkxf : Linked ω st.Z0 x f :=
    (lk x y1 hx hy1 (by omega)).trans (lk y1 f hy1 hfZ (by omega))
  rcases hfF with hf | hf
  · -- `f ∈ (Ω''ᶜ)^{∼4}`
    obtain ⟨g, hg, hfg⟩ := mem_nbhd.mp hf
    have hgZ : g ∈ st.Z0 := st.OmegaDD_compl_subset_Z0 hg
    have lkxg : Linked ω st.Z0 x g := lkxf.trans (lk f g hfZ hgZ (by omega))
    have dxg : supDist x g ≤ ⌊2 * Rk⌋₊ + L + 5 := by have := tri x f g; omega
    by_cases hgO : g ∈ st.Omega
    · rcases st.Omega_diff_OmegaDD_subset hL ⟨hgO, hg⟩ with hq | hq
      · obtain ⟨q, hqQ, hgq⟩ := mem_nbhd.mp hq
        have hqN : q ∈ st.newCubes := Or.inl (Or.inl (Or.inr hqQ))
        have hqZ := st.newCubes_subset_Z0 hqN
        refine Or.inr ⟨q, hqN, ?_, lkxg.trans (lk g q hgZ hqZ (by omega))⟩
        have := tri x g q; omega
      · obtain ⟨q, hqR, hgq⟩ := mem_nbhd.mp hq
        have hqN : q ∈ st.newCubes := Or.inl (Or.inr hqR)
        have hqZ := st.newCubes_subset_Z0 hqN
        refine Or.inr ⟨q, hqN, ?_, lkxg.trans (lk g q hgZ hqZ (by omega))⟩
        have := tri x g q; omega
    · by_cases hgO' : g ∈ st.OmegaPrime
      · obtain ⟨p, hpP, hgp⟩ := mem_nbhd.mp (st.OmegaPrime_diff_Omega_subset hL ⟨hgO', hgO⟩)
        have hpN : p ∈ st.newCubes := Or.inl (Or.inl (Or.inl hpP))
        have hpZ := st.newCubes_subset_Z0 hpN
        refine Or.inr ⟨p, hpN, ?_, lkxg.trans (lk g p hgZ hpZ (by omega))⟩
        have := tri x g p; omega
      · obtain ⟨u, hu, hgu⟩ := mem_nbhd.mp (st.OmegaPrime_compl_subset hL hgO')
        have huZ : u ∈ st.Z0 := st.Uprime_subset_Z0 hu
        obtain ⟨v, hv, rfl⟩ := hu
        obtain ⟨z, hz, hvz⟩ := mem_nbhd.mp hv
        obtain ⟨Y, hY, hzY⟩ := mem_comp_self (ω := ωk) (mem_finOf.mpr hz)
        have hsZ : blockMap L n1 z ∈ st.Z0 :=
          st.Uprime_subset_Z0 (st.blockMap_Z_subset_Uprime hz)
        have hdv := supDist_blockMap_le hn v z
        have hdiv : (supDist v z + L - 1) / L ≤ ⌊Rprev⌋₊ / L + 1 := by
          rw [← Nat.add_div_right _ hL]
          exact Nat.div_le_div_right (by omega)
        have hq2 : 2 * (⌊Rprev⌋₊ / L) ≤ ⌊Rprev⌋₊ := by
          calc 2 * (⌊Rprev⌋₊ / L) ≤ L * (⌊Rprev⌋₊ / L) := Nat.mul_le_mul_right _ hL2
            _ ≤ ⌊Rprev⌋₊ := Nat.mul_div_le _ _
        generalize ⌊Rprev⌋₊ / L = q at hdiv hq2
        refine Or.inl ⟨Y, hY, blockMap L n1 z, ⟨z, hzY, rfl⟩, ?_,
          lkxg.trans ((lk g _ hgZ huZ (by omega)).trans (lk _ _ huZ hsZ (by omega)))⟩
        have := tri x g (blockMap L n1 v)
        have := tri x (blockMap L n1 v) (blockMap L n1 z)
        omega
  · -- `f ∈ S^∼`
    obtain ⟨q, hqS, hfq⟩ := mem_nbhd.mp hf
    have hqN : q ∈ st.newCubes := Or.inr hqS
    have hqZ := st.newCubes_subset_Z0 hqN
    refine Or.inr ⟨q, hqN, ?_, lkxf.trans (lk f q hfZ hqZ (by omega))⟩
    have := tri x f q; omega

/-- **Lemma I.3.8**, in terms of the seeds of Definition I.3.6: every `x ∈ Z^{(0)}` is linked in
`Z^{(0)}` to a point `y` of a seed `σ` with `d(x, y) ≤ s_σ r_k`. -/
theorem attribution_seeds {ωk ω r : ℕ} (h : StepRadii L ω r Rprev Rk) (hn : n0 = L * n1)
    {x : Torus d n1} (hx : x ∈ st.Z0) :
    ∃ σ ∈ st.seeds ωk, ∃ y ∈ σ, supDist x y ≤ st.seedWeight ωk σ * r ∧ Linked ω st.Z0 x y := by
  rcases st.attribution (ωk := ωk) h hn hx with ⟨Y, hY, y, hy, hd, hl⟩ | ⟨q, hq, hd, hl⟩
  · refine ⟨_, Or.inl ⟨Y, hY, rfl⟩, y, hy, ?_, hl⟩
    simpa [seedWeight, show (blockMap L n1 '' (Y : Set (Torus d n0))) ∈ st.oldSeeds ωk from
      ⟨Y, hY, rfl⟩] using hd
  · refine ⟨{q}, Or.inr ⟨q, hq, rfl⟩, q, rfl, ?_, hl⟩
    have : ({q} : Set (Torus d n1)) ∉ st.oldSeeds ωk := fun hs =>
      (Set.disjoint_left.mp st.newCubes_disjoint_Uprime) hq (st.oldSeed_subset_Uprime hs rfl)
    simpa [seedWeight, this] using hd

/-- **Lemma I.3.8 under (RH)**: with `ω = ω_{k+1}` and `r = r_k`. -/
theorem attribution_of_radiusHyp {Rbase : ℝ} {lam R : ℕ → ℝ} (hRH : RadiusHyp L Rbase lam R)
    (hL : 2 ≤ L) (k : ℕ) (hRk : Rk = R k) (hRp : Rprev ≤ Rbase * lam k ^ 2)
    (hn : n0 = L * n1) {ωk : ℕ} {x : Torus d n1} (hx : x ∈ st.Z0) :
    ∃ σ ∈ st.seeds ωk, ∃ y ∈ σ, supDist x y ≤
      st.seedWeight ωk σ * radiusUnit Rbase lam k ∧ Linked (omegaW L Rbase lam (k + 1)) st.Z0 x y :=
  st.attribution_seeds (hRH.stepRadii hL k hRk hRp) hn hx

end RegionStep

end Balaban.LargeField
