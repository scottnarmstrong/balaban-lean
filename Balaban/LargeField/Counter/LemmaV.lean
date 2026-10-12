module

public import Balaban.LargeField.History.Spine
public import Balaban.LargeField.Geometry.Continuous
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Lemma V (Part I, Lemma I.5.1)

For a spine `Γ` of length `ℓ` and `ρ ≥ 2`, the number of cubes within sup-distance `ρ + 4` of `Γ`
is at most `C_V ρ^{d-1}(ℓ + ρ)` with `C_V = 2 · 14^d`.

(The statement of Part I is for `ρ ≥ 1`; the radii of the counter satisfy `ρ_j ≥ c₀ ≥ 6`, and
the proof below uses the slack `ε = ½` in the definition of `N_r`, which needs `ρ ≥ 2`.)
-/

@[expose] public section

open Set

namespace Balaban.LargeField

variable {d : ℕ}

/-- The lattice points whose unit cube is within sup-distance `r` of the lift of the spine. -/
def latNbhd (sp : Spine d) (r : ℝ) : Set (Fin d → ℤ) :=
  {z | ∃ p ∈ sp.carrier, ∃ t : Fin d → ℝ, (∀ i, t i ∈ Icc (0 : ℝ) 1) ∧
    ‖p - ((fun i => (z i : ℝ)) + t)‖ ≤ r}

/-- The projection of the spine to the continuous torus `(ℝ/nℤ)^d`. -/
def Spine.proj (sp : Spine d) (n : ℕ) : Set (CTorus d n) :=
  (fun p i => ((p i : ℝ) : AddCircle (n : ℝ))) '' sp.carrier

/-- A maximal family of points of the spine with pairwise sup-distances `> ρ`. -/
theorem exists_maximal_sep (sp : Spine d) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ P : Finset (Fin d → ℝ), (∀ p ∈ P, p ∈ sp.carrier) ∧
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → ρ < ‖p - q‖) ∧ (∀ y ∈ sp.carrier, ∃ p ∈ P, ‖y - p‖ ≤ ρ) := by
  classical
  obtain ⟨s0, hs0⟩ := sp.nonempty
  have hp0 : s0.1 ∈ sp.carrier := (sp.mem_carrier).mpr ⟨s0, hs0, left_mem_segment _ _ _⟩
  let 𝒮 : Set (Finset (Fin d → ℝ)) := {P | (∀ p ∈ P, p ∈ sp.carrier) ∧
    ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ρ < ‖p - q‖}
  have hne : ({s0.1} : Finset (Fin d → ℝ)) ∈ 𝒮 := by
    refine ⟨by simpa using hp0, ?_⟩
    intro p hp q hq hpq
    simp at hp hq; exact absurd (hp.trans hq.symm) hpq
  have hbdd : BddAbove ((fun P : Finset (Fin d → ℝ) => P.card) '' 𝒮) := by
    refine ⟨⌈(2 * sp.length / ρ + 1)⌉₊, ?_⟩
    rintro _ ⟨P, hP, rfl⟩
    have := sp.sep_card_le hρ P hP.1 hP.2
    have h2 : (P.card : ℝ) ≤ 2 * sp.length / ρ + 1 := by
      rw [div_add_one hρ.ne', le_div_iff₀ hρ]
      nlinarith
    exact Nat.le_ceil _ |> fun h => by exact_mod_cast h2.trans h
  obtain ⟨P, hP, hPmax⟩ := Nat.sSup_mem (⟨_, ⟨_, hne, rfl⟩⟩ : ((fun P : Finset (Fin d → ℝ) =>
    P.card) '' 𝒮).Nonempty) hbdd
  refine ⟨P, hP.1, hP.2, ?_⟩
  intro y hy
  by_contra hcon
  push Not at hcon
  have hyP : y ∉ P := fun h => by have := hcon y h; simp at this; linarith
  have hnew : insert y P ∈ 𝒮 := by
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hy
      · exact hP.1 p hp
    · intro p hp q hq hpq
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · rcases Finset.mem_insert.mp hq with rfl | hq'
        · exact absurd rfl hpq
        · exact hcon q hq'
      · rcases Finset.mem_insert.mp hq with rfl | hq'
        · rw [norm_sub_rev]; exact hcon p hp'
        · exact hP.2 p hp' q hq' hpq
  have hle := le_csSup hbdd ⟨insert y P, hnew, rfl⟩
  rw [← hPmax] at hle
  have hle' : (insert y P).card ≤ P.card := hle
  rw [Finset.card_insert_of_notMem hyP] at hle'
  omega

/-- The lattice points near the spine are covered by at most `(2ℓ/ρ + 1)(14ρ)^d` points. -/
theorem latNbhd_finset (sp : Spine d) {ρ : ℝ} (hρ : 2 ≤ ρ) :
    ∃ F : Finset (Fin d → ℤ), latNbhd sp (ρ + 9 / 2) ⊆ ↑F ∧
      (F.card : ℝ) ≤ (2 * sp.length / ρ + 1) * (14 * ρ) ^ d := by
  classical
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨P, hPc, hPs, hPm⟩ := exists_maximal_sep sp hρ0
  let box : (Fin d → ℝ) → Finset (Fin d → ℤ) := fun q =>
    Fintype.piFinset (fun j => Finset.Icc ⌈q j - 2 * ρ - 11 / 2⌉ ⌊q j + 2 * ρ + 9 / 2⌋)
  refine ⟨P.biUnion box, ?_, ?_⟩
  · intro z hz
    obtain ⟨p, hp, t, ht, hpt⟩ := hz
    obtain ⟨q, hq, hpq⟩ := hPm p hp
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    refine ⟨q, hq, ?_⟩
    simp only [Finset.mem_coe, box, Fintype.mem_piFinset, Finset.mem_Icc]
    intro j
    have h1 : ‖q - (fun i => (z i : ℝ)) - t‖ ≤ 2 * ρ + 9 / 2 := by
      have : q - (fun i => (z i : ℝ)) - t = (q - p) + (p - ((fun i => (z i : ℝ)) + t)) := by
        ext i; simp; ring
      rw [this]
      calc ‖(q - p) + (p - ((fun i => (z i : ℝ)) + t))‖ ≤ ‖q - p‖ + ‖p - ((fun i => (z i : ℝ)) + t)‖ :=
            norm_add_le _ _
        _ ≤ 2 * ρ + 9 / 2 := by rw [norm_sub_rev]; linarith
    have h2 := (norm_le_pi_norm (q - (fun i => (z i : ℝ)) - t) j)
    simp only [Pi.sub_apply, Real.norm_eq_abs] at h2
    have h3 := abs_le.mp (h2.trans h1)
    have htj := ht j
    constructor
    · apply Int.ceil_le.mpr; linarith [htj.1, htj.2]
    · apply Int.le_floor.mpr; linarith [htj.1, htj.2]
  · have hbox : ∀ q : Fin d → ℝ, ((box q).card : ℝ) ≤ (14 * ρ) ^ d := by
      intro q
      simp only [box, Fintype.card_piFinset]
      push_cast
      calc ∏ j : Fin d, ((Finset.Icc ⌈q j - 2 * ρ - 11 / 2⌉ ⌊q j + 2 * ρ + 9 / 2⌋).card : ℝ)
          ≤ ∏ j : Fin d, (14 * ρ) := by
            refine Finset.prod_le_prod₀
              (f := fun j : Fin d => ((Finset.Icc ⌈q j - 2 * ρ - 11 / 2⌉ ⌊q j + 2 * ρ + 9 / 2⌋).card : ℝ))
              (g := fun _ => 14 * ρ) (fun j _ => Nat.cast_nonneg _) (fun j _ => ?_)
            rw [Int.card_Icc]
            have h1 := Int.floor_le (q j + 2 * ρ + 9 / 2)
            have h2 := Int.le_ceil (q j - 2 * ρ - 11 / 2)
            have h3 : (((⌊q j + 2 * ρ + 9 / 2⌋ + 1 - ⌈q j - 2 * ρ - 11 / 2⌉).toNat : ℤ) : ℝ) ≤
                4 * ρ + 11 := by
              have : ((⌊q j + 2 * ρ + 9 / 2⌋ + 1 - ⌈q j - 2 * ρ - 11 / 2⌉ : ℤ) : ℝ) ≤ 4 * ρ + 11 := by
                push_cast; linarith
              rcases le_total 0 (⌊q j + 2 * ρ + 9 / 2⌋ + 1 - ⌈q j - 2 * ρ - 11 / 2⌉) with h | h
              · rw [Int.toNat_of_nonneg h]; exact this
              · rw [Int.toNat_of_nonpos h]; simp; linarith
            have h4 : ((((⌊q j + 2 * ρ + 9 / 2⌋ + 1 - ⌈q j - 2 * ρ - 11 / 2⌉).toNat : ℕ) : ℝ)) ≤ 4 * ρ + 11 := by
              exact_mod_cast h3
            linarith
        _ = (14 * ρ) ^ d := by simp
    have hPcard := sp.sep_card_le hρ0 P hPc hPs
    have hPc' : (P.card : ℝ) ≤ 2 * sp.length / ρ + 1 := by
      rw [div_add_one hρ0.ne', le_div_iff₀ hρ0]
      nlinarith
    calc ((P.biUnion box).card : ℝ) ≤ ∑ q ∈ P, ((box q).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ q ∈ P, (14 * ρ) ^ d := Finset.sum_le_sum (fun q _ => hbox q)
      _ = P.card * (14 * ρ) ^ d := by simp
      _ ≤ _ := by gcongr

section Torus

variable {n : ℕ} [NeZero n]

theorem NR_subset_image (sp : Spine d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    NR (ρ + 4) (sp.proj n) ⊆
      (fun z : Fin d → ℤ => fun i => ((z i : ℤ) : ZMod n)) '' latNbhd sp (ρ + 9 / 2) := by
  intro x hx
  obtain ⟨γ, hγ, q, hq, hlt⟩ := hx (1 / 2) (by norm_num)
  obtain ⟨p, hp, rfl⟩ := hγ
  have hcoord : ∀ i, ∃ t ∈ Icc (0 : ℝ) 1, ∃ k : ℤ,
      |p i - (((x i).val : ℝ) + t) - k * n| ≤ ρ + 9 / 2 := by
    intro i
    obtain ⟨t, ht, hqi⟩ := hq i
    refine ⟨t, ht, ?_⟩
    have h1 : ‖(fun i => ((p i : ℝ) : AddCircle (n : ℝ))) i - q i‖ ≤ ρ + 9 / 2 := by
      have := norm_le_pi_norm ((fun i => ((p i : ℝ) : AddCircle (n : ℝ))) - q) i
      simp only [Pi.sub_apply] at this
      have h2 : ‖(fun i => ((p i : ℝ) : AddCircle (n : ℝ))) - q‖ ≤ ρ + 9 / 2 := by linarith
      exact (this.trans h2)
    have h3 : (fun i => ((p i : ℝ) : AddCircle (n : ℝ))) i - q i =
        ((p i - (((x i).val : ℝ) + t) : ℝ) : AddCircle (n : ℝ)) := by
      rw [hqi]
      unfold zc
      simp only [AddCircle.coe_sub, AddCircle.coe_add]
    rw [h3] at h1
    exact (norm_coe_le_iff _ _).mp h1
  choose t ht k hk using hcoord
  refine ⟨fun i => ((x i).val : ℤ) + k i * n, ?_, ?_⟩
  · refine ⟨p, hp, t, ht, ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by linarith : (0 : ℝ) ≤ ρ + 9 / 2)]
    intro i
    rw [Real.norm_eq_abs]
    have := hk i
    have e : p i - ((fun i => ((((x i).val : ℤ) + k i * n : ℤ) : ℝ)) + t) i =
        p i - (((x i).val : ℝ) + t i) - k i * n := by
      simp only [Pi.add_apply]; push_cast; ring
    rw [Pi.sub_apply, e]
    exact this
  · ext i
    simp

/-- **Lemma V** (Lemma I.5.1): the cubes within sup-distance `ρ + 4` of a spine of length `ℓ`
number at most `C_V ρ^{d-1}(ℓ + ρ)`, `C_V = 2 · 14^d` (here for `ρ ≥ 2`). -/
theorem lemmaV (sp : Spine d) (hd : 1 ≤ d) {ρ : ℝ} (hρ : 2 ≤ ρ) (Z : Finset (Torus d n))
    (hZ : (Z : Set (Torus d n)) ⊆ NR (ρ + 4) (sp.proj n)) :
    (Z.card : ℝ) ≤ 2 * 14 ^ d * ρ ^ (d - 1) * (sp.length + ρ) := by
  classical
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨F, hF, hFc⟩ := latNbhd_finset sp hρ
  have hsub : Z ⊆ F.image (fun z : Fin d → ℤ => fun i => ((z i : ℤ) : ZMod n)) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := NR_subset_image sp (by linarith : (0 : ℝ) ≤ ρ) (hZ hx)
    exact Finset.mem_image.mpr ⟨z, Finset.mem_coe.mp (hF hz), rfl⟩
  have h1 : Z.card ≤ F.card := (Finset.card_le_card hsub).trans Finset.card_image_le
  have h2 : (Z.card : ℝ) ≤ (2 * sp.length / ρ + 1) * (14 * ρ) ^ d :=
    (by exact_mod_cast h1 : (Z.card : ℝ) ≤ F.card).trans hFc
  have hpow : ρ ^ d = ρ * ρ ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h3 : (2 * sp.length / ρ + 1) * (14 * ρ) ^ d = 14 ^ d * ρ ^ (d - 1) * (2 * sp.length + ρ) := by
    rw [mul_pow, hpow]; field_simp
  rw [h3] at h2
  have hℓ := sp.length_nonneg
  have h4 : 0 ≤ 14 ^ d * ρ ^ (d - 1) := by positivity
  nlinarith [mul_nonneg h4 hℓ, mul_nonneg h4 hρ0.le]

end Torus

end Balaban.LargeField
