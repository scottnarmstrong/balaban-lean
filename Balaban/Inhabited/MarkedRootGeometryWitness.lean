
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedRootGeometry

/-!
# Non-vacuity of the bridge to the root on a concrete torus

On the torus with `d = 1`, `L = 2`, `N₁ = 8`, `m₀ = m₁ = 0`, `K = 1` (sixteen sites, cells of side
`2`, `π′`-cubes of side `4`, roots `Fin 8`): the root `z = 0` with block `{0, 1}`; the domain
`Y = {2, 3, 4, 5}` of `𝒟_1`, which does not meet the block and does not contain the root cube, but
whose nearest-neighbour thickening meets the block; its bridge, which is in `𝒟_1`, contains `Y`
and the root cube, with the size bound; and the far domain `{8, 9, 10, 11}`, which is not in
`markedIdx`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

namespace MarkedRootGeometryWitness

abbrev T1 := CTorus 1 2 8 0 1

theorem val_natT (c : ℕ) (hc : c < 16) (μ : Fin 1) : ((natT (fun _ : Fin 1 => c) : T1) μ).val = c := by
  simp only [natT_apply]
  exact ZMod.val_natCast_of_lt (by simpa using hc)

theorem al2 : Aligned (cellSide 2 0 0 1) (natT (fun _ => 2) : T1) := by
  intro μ; rw [val_natT 2 (by norm_num)]; simp [cellSide]

theorem al8 : Aligned (cellSide 2 0 0 1) (natT (fun _ => 8) : T1) := by
  intro μ; rw [val_natT 8 (by norm_num)]; simp [cellSide]

theorem box_val (b : T1) (c : ℕ) (hb : b = natT (fun _ => c)) (x : T1) (hx : x ∈ box b 4) :
    ∃ v : ℕ, c ≤ v ∧ v < c + 4 ∧ x = natT (fun _ => v) := by
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨c + w 0, by omega, by have := hw 0; omega, ?_⟩
  subst hb
  funext μ
  have : μ = 0 := Subsingleton.elim _ _
  subst this
  simp [natT]

def site (v : ℕ) : T1 := natT (fun _ => v)

theorem site_val (v : ℕ) (hv : v < 16) : (site v 0).val = v := val_natT v hv 0

theorem site_inj {a b : ℕ} (ha : a < 16) (hb : b < 16) (h : site a = site b) : a = b := by
  have := congrArg (fun t : T1 => (t 0).val) h
  simpa [site_val a ha, site_val b hb] using this

theorem site_succ (a : ℕ) : site a + Pi.single 0 1 = site (a + 1) := by
  funext μ
  have : μ = 0 := Subsingleton.elim _ _
  subst this
  simp [site, natT]

theorem eq_site (y : T1) : y = site (y 0).val := by
  funext μ
  have : μ = 0 := Subsingleton.elim _ _
  subst this
  simp [site, natT]

theorem fb (v : ℕ) (hv : v < 16) : site v ∈ fineBlock (0 : RootIdx 1 2 8 0 1) ↔ v < 2 := by
  rw [mem_fineBlock]
  unfold blockIndex
  rw [funext_iff]
  have hsv : ∀ x : Fin 1, (site v x).val = v := fun x => by
    rw [Subsingleton.elim x 0]; exact site_val v hv
  simp only [hsv, pow_one]
  constructor
  · intro h
    have h0 := h 0
    simp only [Pi.zero_apply] at h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    by_contra hh
    have : v / 2 < 8 := by omega
    have := Nat.le_of_dvd (by omega) (by simpa using h0 : 8 ∣ v / 2) 
    omega
  · intro h μ
    have : v / 2 = 0 := by omega
    simp [this]

theorem box_site (c : ℕ) (x : T1) (hx : x ∈ box (site c) 4) :
    ∃ v : ℕ, c ≤ v ∧ v < c + 4 ∧ x = site v :=
  box_val (site c) c rfl x hx

theorem site_mem_box (c v : ℕ) (h1 : c ≤ v) (h2 : v < c + 4) : site v ∈ box (site c) 4 := by
  refine ⟨fun _ => v - c, fun _ => by show v - c < 4; omega, ?_⟩
  funext μ
  have : μ = 0 := Subsingleton.elim _ _
  subst this
  simp only [site, natT, Pi.add_apply]
  rw [← Nat.cast_add]; congr 1; omega

theorem fb_site (y : T1) (hy : y ∈ fineBlock (0 : RootIdx 1 2 8 0 1)) : ∃ u, u < 2 ∧ y = site u := by
  refine ⟨(y 0).val, ?_, eq_site y⟩
  have hlt : (y 0).val < 16 := ZMod.val_lt _
  rw [eq_site y] at hy
  exact (fb _ hlt).1 hy

theorem Y_fb : box (site 2) 4 ∩ fineBlock (0 : RootIdx 1 2 8 0 1) = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hz
  obtain ⟨v, h1, h2, rfl⟩ := box_site 2 x hx
  have := (fb v (by omega)).1 hz
  omega

theorem Y_thick : (psiThick (box (site 2) 4) ∩ fineBlock (0 : RootIdx 1 2 8 0 1)).Nonempty := by
  refine ⟨site 1, Or.inr ⟨site 2, site_mem_box 2 2 le_rfl (by omega), ⟨0, Or.inr ?_⟩⟩,
    (fb 1 (by norm_num)).2 (by norm_num)⟩
  rw [site_succ]

theorem far_thick : psiThick (box (site 8) 4) ∩ fineBlock (0 : RootIdx 1 2 8 0 1) = ∅ := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hy hz
  obtain ⟨u, hu, rfl⟩ := fb_site y hz
  rcases hy with hy | ⟨x, hx, μ, h | h⟩
  · obtain ⟨v, h1, h2, hv⟩ := box_site 8 _ hy
    have := site_inj (by omega) (by omega) hv
    omega
  · obtain ⟨v, h1, h2, rfl⟩ := box_site 8 _ hx
    have hμ : μ = 0 := Subsingleton.elim _ _
    subst hμ
    rw [site_succ] at h
    have := site_inj (by omega) (by omega) h
    omega
  · obtain ⟨v, h1, h2, rfl⟩ := box_site 8 _ hx
    have hμ : μ = 0 := Subsingleton.elim _ _
    subst hμ
    rw [site_succ] at h
    have := site_inj (by omega) (by omega) h
    omega

end MarkedRootGeometryWitness

open MarkedRootGeometryWitness in
open Classical in
theorem markedRootGeometry_witness :
    ∃ (z : RootIdx 1 2 8 0 1) (Y Yfar : Set (CTorus 1 2 8 0 1)),
      IsDj (L := 2) (N₁ := 8) (m₁ := 0) (K := 1) 0 1 Y ∧
      IsDj (L := 2) (N₁ := 8) (m₁ := 0) (K := 1) 0 1 Yfar ∧
      Y ∩ fineBlock z = ∅ ∧ (psiThick Y ∩ fineBlock z).Nonempty ∧
      rootCube (m₀ := 0) z ∉ blocksOf 0 1 Set.univ Y ∧
      Y ⊆ bridge 0 z Y ∧ IsDj (L := 2) (N₁ := 8) (m₁ := 0) (K := 1) 0 1 (bridge 0 z Y) ∧
      rootCube (m₀ := 0) z ∈ blocksOf 0 1 Set.univ (bridge 0 z Y) ∧
      treeLenCovOne 0 1 (bridge 0 z Y) ≤ treeLenCovOne 0 1 Y + cBr 1 2 ∧
      (psiThick Yfar ∩ fineBlock z) = ∅ ∧
      ((), Y) ∈ markedIdx (fun _ : Unit => (Set.univ : Set (CTorus 1 2 8 0 1)))
        (fun _ => {Y, Yfar}) z ∧
      ((), Yfar) ∉ markedIdx (fun _ : Unit => (Set.univ : Set (CTorus 1 2 8 0 1)))
        (fun _ => {Y, Yfar}) z ∧
      bridge 0 z Y ∈ bridgeFamily 0 (fun _ : Unit => (Set.univ : Set (CTorus 1 2 8 0 1)))
        (fun _ => {Y, Yfar}) z := by
  have hN : (2 : ℕ) ^ 0 ∣ 8 := by norm_num
  have h4 : 2 * cellSide 2 0 0 1 = 4 := by norm_num [cellSide]
  have hdj : ∀ c : ℕ, Aligned (cellSide 2 0 0 1) (site c) →
      IsDj (L := 2) (N₁ := 8) (m₁ := 0) (K := 1) 0 1 (box (site c) 4) := fun c hc => by
    have := isDj_box (L := 2) (N₁ := 8) (m₁ := 0) (K := 1) (m₀ := 0) (j := 1) hc
    rwa [h4] at this
  have hY := hdj 2 al2
  have hF := hdj 8 al8
  have hz : (0 : RootIdx 1 2 8 0 1) ∈ ({0} : Set (RootIdx 1 2 8 0 1)) := rfl
  have hnot : rootCube (m₀ := 0) (0 : RootIdx 1 2 8 0 1) ∉
      blocksOf 0 1 Set.univ (box (site 2) 4) := by
    intro h
    have hs := mem_blocksOf.1 h (rootSite_mem_box_rootCube (m₀ := 0) (0 : RootIdx 1 2 8 0 1))
    have : rootSite (0 : RootIdx 1 2 8 0 1) ∈ box (site 2) 4 ∩ fineBlock 0 :=
      ⟨hs, rootSite_mem_fineBlock _⟩
    rw [Y_fb] at this
    exact this
  have hbd := bridge_isDj_and_le (m₀ := 0) hN (0 : RootIdx 1 2 8 0 1) hY
  have hmem : ((), box (site 2) 4) ∈ markedIdx (fun _ : Unit => (Set.univ : Set (CTorus 1 2 8 0 1)))
      (fun _ => {box (site 2) 4, box (site 8) 4}) (0 : RootIdx 1 2 8 0 1) :=
    mem_markedIdx.2 ⟨by simp, ⟨rootSite 0, Set.mem_univ _, rootSite_mem_fineBlock _⟩, Y_thick⟩
  refine ⟨0, box (site 2) 4, box (site 8) 4, hY, hF, Y_fb, Y_thick, hnot, subset_bridge _ _, hbd.1,
    rootCube_mem_blocksOf_bridge hN le_rfl _ hY Y_thick, hbd.2, far_thick, hmem, ?_,
    mem_bridgeFamily.2 ⟨(), box (site 2) 4, by simp, ⟨rootSite 0, Set.mem_univ _,
      rootSite_mem_fineBlock _⟩, Y_thick, rfl⟩⟩
  intro h
  obtain ⟨-, -, hm⟩ := mem_markedIdx.1 h
  rw [far_thick] at hm
  exact Set.not_nonempty_empty hm

end Balaban.Fluctuation
