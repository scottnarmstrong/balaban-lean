module

public import Balaban.LargeField.History.StepSeeds

/-!
# The spine of a component after one step (Part I, Definition I.4.7 and Lemma I.4.8)

Given spines `Γ_Y` of the components `Y` of `Z_k` with `Y ⊆ N_{ρ_k+4}(Γ_Y)`, every component `Z'`
of `Z^pre_{k+1}` has a spine `Γ'` with `Z' ⊆ N_{ρ_{k+1}+4}(Γ')` and the length bound (4.1)
`ℓ(Γ') ≤ ∑ ℓ(Γ_Y)/L + (m + r - 1) D`; in a pure shadow with `ℓ(Γ_Y) ≤ L`, `Γ'` is a point.

The proof follows the rounds of Definition I.4.7: the pieces of the seeds
(`pc`, the contraction `Γ_Y/L` of an old spine, or the centre of a new cube) are joined along a
connected contact graph (`exists_spine_family`) in round `0`, and along the contact graph of
the parts (components of `X_t`, or hull boxes) in the hull rounds.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-- The part of a component `C` of `X_t` in the component of `X_{t+1}`: `C` together with its
hull box if `C` is hulled (small of side `≤ b`). -/
def partSet {d n : ℕ} [NeZero n] (b : ℕ) (C : Finset (Torus d n)) : Set (Torus d n) :=
  (C : Set (Torus d n)) ∪ {y | IsSmall (C : Set (Torus d n)) ∧ side (C : Set (Torus d n)) ≤ b ∧
    y ∈ hull (C : Set (Torus d n))}

namespace RegionStep

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ}
  (st : RegionStep d L n0 n1 Rprev Rk) (Γs : Finset (Torus d n0) → Spine d)

/-- The piece spine of a seed: `Γ_Y / L` for an old seed, the centre of the cube for a new one. -/
noncomputable def pc : SeedIdx d n0 n1 → Spine d
  | .inl Y => (Γs Y).contract ((L : ℝ)⁻¹)
  | .inr q => Spine.point (fun i => ((q i).val : ℝ) + 1 / 2)

/-- The length bound of a piece: `ℓ(Γ_Y)/L` for an old seed, `0` for a new one. -/
noncomputable def bnd : SeedIdx d n0 n1 → ℝ
  | .inl Y => (Γs Y).length / L
  | .inr _ => 0

theorem bnd_nonneg (a : SeedIdx d n0 n1) : 0 ≤ bnd (L := L) Γs a := by
  rcases a with Y | q
  · exact div_nonneg (Γs Y).length_nonneg (Nat.cast_nonneg _)
  · exact le_rfl

theorem pc_length_le (a : SeedIdx d n0 n1) : (pc (L := L) Γs a).length ≤ bnd (L := L) Γs a := by
  rcases a with Y | q
  · refine (Spine.length_contract_le _ _).trans ?_
    rw [abs_of_nonneg (by positivity), inv_mul_eq_div]
    exact le_rfl
  · simp [pc, bnd, Spine.length_point]

theorem scaleDown_image_subset_contract (hn : n0 = L * n1) (sp : Spine d) :
    scaleDown (m := n1) '' sp.proj n0 ⊆ (sp.contract ((L : ℝ)⁻¹)).proj n1 := by
  rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
  refine ⟨(L : ℝ)⁻¹ • P, ?_, ?_⟩
  · rw [Spine.carrier_contract]; exact ⟨P, hP, rfl⟩
  · funext i
    rw [scaleDown_coe hn _ i (P i) rfl]
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]

theorem sset_old_subset_NR (hn : n0 = L * n1) {Y : Finset (Torus d n0)} {ρk : ℝ}
    (hY : (Y : Set (Torus d n0)) ⊆ NR ρk ((Γs Y).proj n0)) :
    sset (n0 := n0) (n1 := n1) L (Sum.inl Y) ⊆
      NR (ρk / L) ((pc (L := L) (n1 := n1) Γs (Sum.inl Y)).proj n1) :=
  (blockMap_subset_NR hn hY).trans
    (NR_mono le_rfl (scaleDown_image_subset_contract hn (Γs Y)))

theorem cubeCentre_mem_pc_proj (q : Torus d n1) :
    cubeCentre q ∈ (pc (L := L) (n0 := n0) Γs (Sum.inr q)).proj n1 := by
  refine ⟨fun i => ((q i).val : ℝ) + 1 / 2, ?_, ?_⟩
  · simp [pc, Spine.carrier_point]
  · funext i
    simp only [cubeCentre, zc, AddCircle.coe_add]

/-- Points near a seed lie in `N_ρ` of its piece spine. -/
theorem attr_mem_NR (hn : n0 = L * n1) {ωk r : ℕ} {ρk ρ : ℕ}
    (hρ1 : ((ρk : ℝ) + 4) / L + 4 * r ≤ ρ) (hρ2 : 5 * (r : ℝ) ≤ ρ)
    (hΓ : ∀ Y ∈ comps ωk (finOf st.Z), (Y : Set (Torus d n0)) ⊆ NR ((ρk : ℝ) + 4) ((Γs Y).proj n0))
    {a : SeedIdx d n0 n1} (ha : a ∈ st.idx ωk) {x y : Torus d n1}
    (hy : y ∈ sset (n0 := n0) L a) (hd : supDist x y ≤ seedWt a * r) :
    x ∈ NR (ρ : ℝ) ((pc (L := L) Γs a).proj n1) := by
  rcases a with Y | q
  · have hyN := sset_old_subset_NR Γs hn (hΓ Y ((st.inl_mem_idx).mp ha)) hy
    have h1 := NR_shift hyN x
    refine NR_mono ?_ le_rfl h1
    have : (supDist y x : ℝ) ≤ 4 * r := by
      rw [supDist_comm]; exact_mod_cast hd
    linarith
  · have hq : y = q := hy
    subst hq
    have h1 := mem_NR_cubeCentre y x
    refine NR_mono ?_ (Set.singleton_subset_iff.mpr (cubeCentre_mem_pc_proj Γs y)) h1
    have : (supDist y x : ℝ) ≤ 5 * r := by
      rw [supDist_comm]; exact_mod_cast hd
    refine max_le ?_ (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])
    linarith

/-- Numerical hypotheses of the spine construction: `(ρ_k + 4)/L + s_* r ≤ ρ_{k+1}`,
`s' r ≤ ρ_{k+1}`, and `D ≥ √d (2(ρ_{k+1}+4) + (ω-1) + 2)`. -/
structure SpineNum (d L r ω ρk ρ : ℕ) (D : ℝ) : Prop where
  hρ1 : ((ρk : ℝ) + 4) / L + 4 * r ≤ ρ
  hρ2 : 5 * (r : ℝ) ≤ ρ
  hω : 1 ≤ ω
  hD : Real.sqrt d * (2 * ((ρ : ℝ) + 4) + ((ω : ℝ) - 1) + 2) ≤ D

theorem SpineNum.D_nonneg {d L r ω ρk ρ : ℕ} {D : ℝ} (h : SpineNum d L r ω ρk ρ D) : 0 ≤ D := by
  refine le_trans (mul_nonneg (Real.sqrt_nonneg _) ?_) h.hD
  have : (1 : ℝ) ≤ ω := by exact_mod_cast h.hω
  have : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
  linarith

/-- The old components are spined: `Y ⊆ N_{ρ_k+4}(Γ_Y)`. -/
def OldSpined (ωk ρk : ℕ) : Prop :=
  ∀ Y ∈ comps ωk (finOf st.Z), (Y : Set (Torus d n0)) ⊆ NR ((ρk : ℝ) + 4) ((Γs Y).proj n0)

/-- The spine claim for a set `C` of cubes of `𝕋_{k+1}`: a spine `Γ` with `C ⊆ N_{ρ+4}(Γ)`
and the length bound; if `C` contains one seed only, either `C ⊆ N_ρ` of its piece or `C`
lies in `N_{ρ+4}` of a point. -/
def SpineClaim (ωk ρ : ℕ) (D : ℝ) (C : Finset (Torus d n1)) : Prop :=
  ∃ Γ : Spine d, (C : Set (Torus d n1)) ⊆ NR ((ρ : ℝ) + 4) (Γ.proj n1) ∧
    Γ.length ≤ ∑ a ∈ st.seedsIn ωk C, bnd (L := L) Γs a +
      (((st.seedsIn ωk C).card : ℝ) - 1) * D ∧
    ((st.seedsIn ωk C).card = 1 → ∃ a, st.seedsIn ωk C = {a} ∧
      ((C : Set (Torus d n1)) ⊆ NR (ρ : ℝ) ((pc (L := L) Γs a).proj n1) ∨
        ∃ p : CTorus d n1, (C : Set (Torus d n1)) ⊆ NR ((ρ : ℝ) + 4) {p}))

variable {ωk ω r ρk ρ : ℕ} {D : ℝ}

/-- Round `0`: the claim for the components of `Z^{(0)}` (Definition I.4.7, item 1). -/
theorem spineClaim_base (hg : StepGeom L n0 n1 ωk ω r Rprev Rk) (hnum : SpineNum d L r ω ρk ρ D)
    (hΓ : st.OldSpined Γs ωk ρk) {C : Finset (Torus d n1)} (hC : C ∈ comps ω (finOf st.Z0)) :
    st.SpineClaim Γs ωk ρ D C := by
  classical
  have hω0 : 0 < ω := hnum.hω
  set I := st.seedsIn ωk C with hI
  let V : SeedIdx d n0 n1 → Set (Torus d n1) := fun a =>
    {x | x ∈ C ∧ ∃ y ∈ sset (n0 := n0) L a, supDist x y ≤ seedWt a * r}
  have hcover : ∀ x ∈ C, ∃ a ∈ I, x ∈ V a := by
    intro x hx
    obtain ⟨a, ha, y, hy, hd, hl⟩ := st.attr_seed hg (mem_finOf.mp (comp_subset hC hx))
    have hsub := st.sset_subset_of_linked hg hC hx ha hy hl
    exact ⟨a, st.mem_seedsIn.mpr ⟨ha, hsub⟩, hx, y, hy, hd⟩
  have hsub : ∀ a ∈ I, V a ⊆ C := fun a _ x hx => hx.1
  have hne : ∀ a ∈ I, (V a).Nonempty := by
    intro a ha
    obtain ⟨hai, has⟩ := st.mem_seedsIn.mp ha
    obtain ⟨y, hy⟩ := st.sset_nonempty hai
    exact ⟨y, has hy, y, hy, by rw [supDist_self]; exact Nat.zero_le _⟩
  have hVN : ∀ a ∈ I, V a ⊆ NR (ρ : ℝ) ((pc (L := L) Γs a).proj n1) := by
    intro a ha x hx
    obtain ⟨hai, -⟩ := st.mem_seedsIn.mp ha
    obtain ⟨-, y, hy, hd⟩ := hx
    exact st.attr_mem_NR Γs hg.hn hnum.hρ1 hnum.hρ2 hΓ hai hy hd
  have hIne : I.Nonempty := by
    obtain ⟨x, hx⟩ := comp_nonempty hC
    obtain ⟨a, ha, -⟩ := hcover x hx
    exact ⟨a, ha⟩
  have hcut := cut_of_cover hω0 I V (fun x hx y hy => comp_linked_self hC hx hy) hcover hsub hne
  have hcut' : ∀ T ⊆ I, T.Nonempty → T ≠ I →
      ∃ i ∈ T, ∃ j ∈ I \ T, ∃ a ∈ V i, ∃ a' ∈ V j, (supDist a a' : ℝ) ≤ (ω : ℝ) - 1 := by
    intro T hT hTn hTI
    obtain ⟨i, hi, j, hj, a, ha, a', ha', hd⟩ := hcut T hT hTn hTI
    refine ⟨i, hi, j, hj, a, ha, a', ha', ?_⟩
    have : (supDist a a' : ℝ) ≤ ((ω - 1 : ℕ) : ℝ) := by exact_mod_cast hd
    rw [Nat.cast_sub hω0] at this
    simpa using this
  obtain ⟨Γ, hΓ1, hΓ2⟩ := exists_spine_family I hIne V (pc (L := L) Γs) (r := (ρ : ℝ) + 4)
    (w := (ω : ℝ) - 1) (D := D)
    (fun a ha => (hVN a ha).trans (NR_mono (by linarith) subset_rfl)) hcut' hnum.hD
  refine ⟨Γ, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := hcover x hx
    exact hΓ1 (Set.mem_biUnion ha hxa)
  · refine hΓ2.trans ?_
    have : ∑ a ∈ I, (pc (L := L) Γs a).length ≤ ∑ a ∈ I, bnd (L := L) Γs a :=
      Finset.sum_le_sum fun a _ => pc_length_le Γs a
    linarith
  · intro hcard
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    refine ⟨a, ha, Or.inl ?_⟩
    intro x hx
    obtain ⟨b, hb, hxb⟩ := hcover x hx
    rw [hI, ha, Finset.mem_singleton] at hb
    subst hb
    exact hVN b (by rw [hI, ha]; exact Finset.mem_singleton_self b) hxb

/-- A hull round (Definition I.4.7, item 2): the claim for the components of `X_t` gives the claim
for the components of `X_{t+1} = H_b(X_t)`. -/
theorem spineClaim_step (hg : StepGeom L n0 n1 ωk ω r Rprev Rk) (hnum : SpineNum d L r ω ρk ρ D)
    {b : ℕ} (hb : b ≤ 2 * ρ + 10) {X : Set (Torus d n1)} (hZX : st.Z0 ⊆ X)
    (hcont : ∀ C ∈ comps ω (finOf X), ∃ C0 ∈ comps ω (finOf st.Z0), C0 ⊆ C)
    (IH : ∀ C ∈ comps ω (finOf X), st.SpineClaim Γs ωk ρ D C)
    {C' : Finset (Torus d n1)} (hC' : C' ∈ comps ω (finOf (hullRound ω b X))) :
    st.SpineClaim Γs ωk ρ D C' := by
  classical
  have hD0 := hnum.D_nonneg
  have hω2 := hg.hω2
  have hω0 : 0 < ω := by omega
  set P := (comps ω (finOf X)).filter (fun C => C ⊆ C') with hP
  have hXY : X ⊆ hullRound ω b X := subset_hullRound X
  have hmemP : ∀ C ∈ P, C ∈ comps ω (finOf X) ∧ C ⊆ C' := fun C hC => Finset.mem_filter.mp hC
  have hcoverP : ∀ y ∈ C', ∃ C ∈ P, y ∈ partSet b C := by
    intro y hy
    obtain ⟨C, hC, hCC', hyC⟩ := (hullRound_comp_iff hω2 hC').mp hy
    exact ⟨C, Finset.mem_filter.mpr ⟨hC, hCC'⟩, hyC⟩
  have hsubP : ∀ C ∈ P, partSet b C ⊆ (C' : Set (Torus d n1)) := by
    intro C hC y hy
    obtain ⟨hCX, hCC'⟩ := hmemP C hC
    exact (hullRound_comp_iff hω2 hC').mpr ⟨C, hCX, hCC', hy⟩
  have hnePart : ∀ C ∈ P, (partSet b C).Nonempty := by
    intro C hC
    obtain ⟨y, hy⟩ := comp_nonempty (hmemP C hC).1
    exact ⟨y, Or.inl hy⟩
  have hpart : ∀ C ∈ P, ∃ Γ' : Spine d, partSet b C ⊆ NR ((ρ : ℝ) + 4) (Γ'.proj n1) ∧
      Γ'.length ≤ ∑ a ∈ st.seedsIn ωk C, bnd (L := L) Γs a +
        (((st.seedsIn ωk C).card : ℝ) - 1) * D ∧
      (partSet b C = (C : Set (Torus d n1)) ∨
        ∃ p : CTorus d n1, partSet b C ⊆ NR ((ρ : ℝ) + 4) {p}) := by
    intro C hC
    obtain ⟨hCX, -⟩ := hmemP C hC
    obtain ⟨Γ, hΓ1, hΓ2, -⟩ := IH C hCX
    by_cases hh : IsSmall (C : Set (Torus d n1)) ∧ side (C : Set (Torus d n1)) ≤ b
    · obtain ⟨a, s, hhull, -, hside⟩ := hull_eq_box (Finset.coe_nonempty.mpr (comp_nonempty hCX)) hh.1
      have hsi : ∀ i, s i ≤ 2 * ρ + 10 := fun i =>
        le_trans (hside ▸ Finset.le_sup (f := s) (Finset.mem_univ i)) (hh.2.trans hb)
      have hbox := box_subset_NR a s hsi
      obtain ⟨Γp, hl0, hproj⟩ := exists_point_spine (d := d) (n := n1) (boxCentre a s)
      have hsubbox : partSet b C ⊆ box a s := by
        intro y hy
        rw [← hhull]
        rcases hy with hy | ⟨-, -, hy⟩
        · exact subset_hull _ hy
        · exact hy
      refine ⟨Γp, ?_, ?_, Or.inr ⟨boxCentre a s, fun y hy => hbox (hsubbox hy)⟩⟩
      · rw [hproj]; exact fun y hy => hbox (hsubbox hy)
      · rw [hl0]
        have h1 := st.seedsIn_card_pos hg (hcont C hCX)
        have h2 : (1 : ℝ) ≤ (st.seedsIn ωk C).card := by exact_mod_cast h1
        have h3 : 0 ≤ ∑ a ∈ st.seedsIn ωk C, bnd (L := L) Γs a :=
          Finset.sum_nonneg fun a _ => bnd_nonneg Γs a
        have h4 : 0 ≤ (((st.seedsIn ωk C).card : ℝ) - 1) * D := mul_nonneg (by linarith) hD0
        linarith
    · have hpe : partSet b C = (C : Set (Torus d n1)) := by
        ext y
        constructor
        · rintro (h | ⟨h1, h2, -⟩)
          · exact h
          · exact absurd ⟨h1, h2⟩ hh
        · exact fun h => Or.inl h
      refine ⟨Γ, ?_, hΓ2, Or.inl hpe⟩
      rw [hpe]; exact hΓ1
  have : Nonempty (Spine d) := ⟨Spine.point 0⟩
  choose! Γ' hΓ' using hpart
  have hPne : P.Nonempty := by
    obtain ⟨y, hy⟩ := comp_nonempty hC'
    obtain ⟨C, hC, hCC', -⟩ := (hullRound_comp_iff hω2 hC').mp hy
    exact ⟨C, Finset.mem_filter.mpr ⟨hC, hCC'⟩⟩
  have hcut := cut_of_cover hω0 P (partSet b) (fun x hx y hy => comp_linked_self hC' hx hy)
    hcoverP hsubP hnePart
  have hcut' : ∀ T ⊆ P, T.Nonempty → T ≠ P →
      ∃ i ∈ T, ∃ j ∈ P \ T, ∃ a ∈ partSet b i, ∃ a' ∈ partSet b j,
        (supDist a a' : ℝ) ≤ (ω : ℝ) - 1 := by
    intro T hT hTn hTI
    obtain ⟨i, hi, j, hj, a, ha, a', ha', hd⟩ := hcut T hT hTn hTI
    refine ⟨i, hi, j, hj, a, ha, a', ha', ?_⟩
    have : (supDist a a' : ℝ) ≤ ((ω - 1 : ℕ) : ℝ) := by exact_mod_cast hd
    rw [Nat.cast_sub hω0] at this
    simpa using this
  obtain ⟨Γ, hΓ1, hΓ2⟩ := exists_spine_family P hPne (partSet b) Γ' (r := (ρ : ℝ) + 4)
    (w := (ω : ℝ) - 1) (D := D) (fun C hC => (hΓ' C hC).1) hcut' hnum.hD
  have hseeds : st.seedsIn ωk C' = P.biUnion (st.seedsIn ωk) :=
    st.seedsIn_biUnion hg hZX hXY hC'
  have hdisj : ∀ C ∈ P, ∀ C2 ∈ P, C ≠ C2 → Disjoint (st.seedsIn ωk C) (st.seedsIn ωk C2) :=
    fun C hC C2 hC2 hne => st.seedsIn_disjoint (hmemP C hC).1 (hmemP C2 hC2).1 hne
  have hsumS : ∑ a ∈ st.seedsIn ωk C', bnd (L := L) Γs a =
      ∑ C ∈ P, ∑ a ∈ st.seedsIn ωk C, bnd (L := L) Γs a := by
    rw [hseeds, Finset.sum_biUnion]
    exact fun C hC C2 hC2 hne => hdisj C hC C2 hC2 hne
  have hcardS : (st.seedsIn ωk C').card = ∑ C ∈ P, (st.seedsIn ωk C).card := by
    rw [hseeds, Finset.card_biUnion]
    exact fun C hC C2 hC2 hne => hdisj C hC C2 hC2 hne
  have hN1 : ∀ C ∈ P, 1 ≤ (st.seedsIn ωk C).card := fun C hC =>
    st.seedsIn_card_pos hg (hcont C (hmemP C hC).1)
  refine ⟨Γ, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨C, hC, hyC⟩ := hcoverP y hy
    exact hΓ1 (Set.mem_biUnion hC hyC)
  · have h1 : ∑ C ∈ P, (Γ' C).length ≤ ∑ C ∈ P, (∑ a ∈ st.seedsIn ωk C, bnd (L := L) Γs a +
        (((st.seedsIn ωk C).card : ℝ) - 1) * D) :=
      Finset.sum_le_sum fun C hC => (hΓ' C hC).2.1
    have h2 : ∑ C ∈ P, (∑ a ∈ st.seedsIn ωk C, bnd (L := L) Γs a +
        (((st.seedsIn ωk C).card : ℝ) - 1) * D) =
        ∑ C ∈ P, ∑ a ∈ st.seedsIn ωk C, bnd (L := L) Γs a +
          ((∑ C ∈ P, ((st.seedsIn ωk C).card : ℝ)) - P.card) * D := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]
      simp
    have h3 : (((st.seedsIn ωk C').card : ℕ) : ℝ) = ∑ C ∈ P, ((st.seedsIn ωk C).card : ℝ) := by
      rw [hcardS]; push_cast; rfl
    have h4 : ((∑ C ∈ P, ((st.seedsIn ωk C).card : ℝ)) - P.card) * D + ((P.card : ℝ) - 1) * D =
        (((st.seedsIn ωk C').card : ℝ) - 1) * D := by rw [h3]; ring
    rw [hsumS]
    linarith
  · intro hcard1
    have hPle : P.card ≤ ∑ C ∈ P, (st.seedsIn ωk C).card := by
      calc P.card = ∑ _C ∈ P, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum hN1
    have hP1 : P.card = 1 := by
      have := Finset.card_pos.mpr hPne
      omega
    obtain ⟨C1, hPeq⟩ := Finset.card_eq_one.mp hP1
    have hC1P : C1 ∈ P := by rw [hPeq]; exact Finset.mem_singleton_self _
    obtain ⟨hC1X, -⟩ := hmemP C1 hC1P
    obtain ⟨-, -, -, hQ⟩ := IH C1 hC1X
    have hN : (st.seedsIn ωk C1).card = 1 := by
      rw [hcardS, hPeq, Finset.sum_singleton] at hcard1
      exact hcard1
    obtain ⟨a, haeq, hQa⟩ := hQ hN
    have hseeds1 : st.seedsIn ωk C' = {a} := by
      rw [hseeds, hPeq, Finset.singleton_biUnion, haeq]
    refine ⟨a, hseeds1, ?_⟩
    have hCeq : (C' : Set (Torus d n1)) = partSet b C1 := by
      apply Set.Subset.antisymm
      · intro y hy
        obtain ⟨C, hC, hyC⟩ := hcoverP y hy
        rw [hPeq, Finset.mem_singleton] at hC
        subst hC
        exact hyC
      · exact hsubP C1 hC1P
    rcases (hΓ' C1 hC1P).2.2 with hpe | ⟨p, hp⟩
    · rw [hCeq, hpe]; exact hQa
    · exact Or.inr ⟨p, by rw [hCeq]; exact hp⟩

open Classical in
/-- The old parts of `Z'`: the components `Y` of `Z_k` with `Y^↑ ⊆ Z'`. -/
noncomputable def oldIn (ωk : ℕ) (Z' : Finset (Torus d n1)) : Finset (Finset (Torus d n0)) :=
  (comps ωk (finOf st.Z)).filter fun Y => blockMap L n1 '' (Y : Set (Torus d n0)) ⊆ (Z' : Set _)

/-- The new cubes in `Z'`. -/
noncomputable def newIn (Z' : Finset (Torus d n1)) : Finset (Torus d n1) := Z' ∩ finOf st.newCubes

theorem seedsIn_eq (ωk : ℕ) (Z' : Finset (Torus d n1)) :
    st.seedsIn ωk Z' = (st.oldIn ωk Z').image Sum.inl ∪ (st.newIn Z').image Sum.inr := by
  classical
  ext a
  rcases a with Y | q
  · simp [mem_seedsIn, inl_mem_idx, oldIn, sset]
  · simp [mem_seedsIn, inr_mem_idx, newIn, sset, and_comm]

theorem card_seedsIn (ωk : ℕ) (Z' : Finset (Torus d n1)) :
    (st.seedsIn ωk Z').card = (st.oldIn ωk Z').card + (st.newIn Z').card := by
  classical
  rw [seedsIn_eq, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ Sum.inr_injective]
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_image] at ha hb
  obtain ⟨_, -, rfl⟩ := ha
  obtain ⟨_, -, h⟩ := hb
  exact Sum.inr_ne_inl h

theorem sum_seedsIn (ωk : ℕ) (Z' : Finset (Torus d n1)) :
    ∑ a ∈ st.seedsIn ωk Z', bnd (L := L) Γs a = ∑ Y ∈ st.oldIn ωk Z', (Γs Y).length / L := by
  classical
  rw [seedsIn_eq, Finset.sum_union, Finset.sum_image (fun _ _ _ _ h => Sum.inl_injective h),
    Finset.sum_image (fun _ _ _ _ h => Sum.inr_injective h)]
  · simp [bnd]
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image] at ha hb
    obtain ⟨_, -, rfl⟩ := ha
    obtain ⟨_, -, h⟩ := hb
    exact Sum.inr_ne_inl h

/-- The claim for all components of the hull rounds `X_t`. -/
theorem spineClaim_iter (hg : StepGeom L n0 n1 ωk ω r Rprev Rk) (hnum : SpineNum d L r ω ρk ρ D)
    (hΓ : st.OldSpined Γs ωk ρk) {b : ℕ} (hb : b ≤ 2 * ρ + 10) (t : ℕ) :
    ∀ C ∈ comps ω (finOf ((hullRound ω b)^[t] st.Z0)), st.SpineClaim Γs ωk ρ D C := by
  induction t with
  | zero => exact fun C hC => st.spineClaim_base Γs hg hnum hΓ hC
  | succ t ih =>
    intro C' hC'
    rw [Function.iterate_succ_apply'] at hC'
    refine st.spineClaim_step Γs hg hnum hb (iter_mono_of_le st.Z0 (Nat.zero_le t)) ?_ ih hC'
    intro C hC
    exact iter_comp_contains hg.hω2 st.Z0 t hC

/-- **Lemma I.4.8** (spine consistency, existence form): every component `Z'` of `Z^pre_{k+1}`
has a spine `Γ'` with (3.1) `Z' ⊆ N_{ρ_{k+1}+4}(Γ')`, the length bound (4.1), and, in a pure
shadow with `ℓ(Γ_Y) ≤ L`, `Γ'` is a point. -/
theorem exists_step_spine (hg : StepGeom L n0 n1 ωk ω r Rprev Rk)
    (hnum : SpineNum d L r ω ρk ρ D) (hΓ : st.OldSpined Γs ωk ρk) {crit : Option ℕ}
    (hcrit : ∀ b, crit = some b → b ≤ 2 * ρ + 10) {Z' : Finset (Torus d n1)}
    (hZ' : Z' ∈ comps ω (finOf (st.Zpre ω crit))) :
    ∃ Γ' : Spine d, (Z' : Set (Torus d n1)) ⊆ NR ((ρ : ℝ) + 4) (Γ'.proj n1) ∧
      Γ'.length ≤ ∑ Y ∈ st.oldIn ωk Z', (Γs Y).length / L +
        (((st.oldIn ωk Z').card + (st.newIn Z').card : ℕ) - 1 : ℝ) * D ∧
      ((st.oldIn ωk Z').card = 1 → (st.newIn Z').card = 0 → ∀ Y ∈ st.oldIn ωk Z',
        (Γs Y).length ≤ L → Γ'.length = 0) := by
  classical
  have hclaim : st.SpineClaim Γs ωk ρ D Z' := by
    cases crit with
    | none => exact st.spineClaim_base Γs hg hnum hΓ hZ'
    | some b =>
      exact st.spineClaim_iter Γs hg hnum hΓ (hcrit b rfl) _ Z' hZ'
  obtain ⟨Γ0, h1, h2, hQ⟩ := hclaim
  rw [sum_seedsIn, card_seedsIn] at h2
  by_cases hsh : (st.oldIn ωk Z').card = 1 ∧ (st.newIn Z').card = 0 ∧
      ∀ Y ∈ st.oldIn ωk Z', (Γs Y).length ≤ L
  · obtain ⟨hc1, hc2, hYL⟩ := hsh
    have hcard : (st.seedsIn ωk Z').card = 1 := by rw [card_seedsIn]; omega
    obtain ⟨a, ha, hqa⟩ := hQ hcard
    obtain ⟨Y, hY⟩ := Finset.card_eq_one.mp hc1
    have hYmem : Y ∈ st.oldIn ωk Z' := by rw [hY]; exact Finset.mem_singleton_self _
    have haY : a = Sum.inl Y := by
      have : Sum.inl Y ∈ st.seedsIn ωk Z' := by
        rw [seedsIn_eq]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hYmem)
      rw [ha, Finset.mem_singleton] at this
      exact this.symm
    subst haY
    have hlen : (pc (L := L) (n1 := n1) Γs (Sum.inl Y)).length ≤ 1 := by
      refine (pc_length_le Γs _).trans ?_
      have hL : (0 : ℝ) < L := by exact_mod_cast (by have := hg.rad.L_two; omega : 0 < L)
      simp only [bnd]
      rw [div_le_one hL]
      exact hYL Y hYmem
    have hbnd : 0 ≤ (Γs Y).length / L := div_nonneg (Γs Y).length_nonneg (Nat.cast_nonneg _)
    have hsum : ∑ Y' ∈ st.oldIn ωk Z', (Γs Y').length / L = (Γs Y).length / L := by
      rw [hY, Finset.sum_singleton]
    have key : ∃ Γp : Spine d, Γp.length = 0 ∧
        (Z' : Set (Torus d n1)) ⊆ NR ((ρ : ℝ) + 4) (Γp.proj n1) := by
      rcases hqa with hl | ⟨p, hp⟩
      · obtain ⟨s, hs⟩ := (pc (L := L) (n1 := n1) Γs (Sum.inl Y)).nonempty
        have hP0 : s.1 ∈ (pc (L := L) (n1 := n1) Γs (Sum.inl Y)).carrier :=
          (Spine.mem_carrier _).mpr ⟨s, hs, left_mem_segment _ _ _⟩
        refine ⟨Spine.point s.1, Spine.length_point _, ?_⟩
        have : (Spine.point s.1).proj n1 = {cl n1 s.1} := by
          unfold Spine.proj; rw [Spine.carrier_point, Set.image_singleton]; rfl
        rw [this]
        exact hl.trans ((NR_subset_point hlen hP0 _).trans (NR_mono (by linarith) subset_rfl))
      · obtain ⟨Γp, hl0, hproj⟩ := exists_point_spine (d := d) (n := n1) p
        exact ⟨Γp, hl0, by rw [hproj]; exact hp⟩
    obtain ⟨Γp, hl0, hcont⟩ := key
    refine ⟨Γp, hcont, ?_, fun _ _ _ _ _ => hl0⟩
    rw [hl0, hsum, hc1, hc2]
    simpa using hbnd
  · refine ⟨Γ0, h1, h2, ?_⟩
    intro hc1 hc2 Y hY hYL
    exact absurd ⟨hc1, hc2, fun Y' hY' => by
      obtain ⟨Y1, hY1⟩ := Finset.card_eq_one.mp hc1
      rw [hY1, Finset.mem_singleton] at hY hY'
      rw [hY'] ; rw [hY] at hYL; exact hYL⟩ hsh

end RegionStep

end Balaban.LargeField
