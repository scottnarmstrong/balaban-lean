/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusBoundaryGen

/-!
# The box room of the sets `V`

If the sites of `V = (Z'^≈)^∼` (all fine sites of the cubes within `⌊R_k⌋ + 2` of a cube of a
nonempty `Z'`) lie in the box `{4|w - c| < m}` of the torus `𝕋_m`, then `m ≥ 4 (⌊R_k⌋ + 2) P₁`
(`P₁ = L^{k+1} c M₁` the side of a `π_{k+1}`-cube): the box contains at most `(m + 1) / 2`
residues, and `V` contains `(2⌊R_k⌋ + 5) P₁` consecutive ones. This gives the size premises of
`genAgree_genBoundaryLocal` and `bgLocPiece_twoTorus` from the containment of `V` in the box.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField

set_option linter.unusedSectionVars false

theorem two_mul_le_of_box {m : ℕ} {c i₀ : ℤ} {N : ℕ} (hN : N ≤ m)
    (h : ∀ z ∈ Finset.Ico i₀ (i₀ + N), ∃ ℓ : ℤ, ((ℓ : ℤ) : ZMod m) = ((z : ℤ) : ZMod m) ∧
      4 * |ℓ - c| < (m : ℤ)) : 2 * N ≤ m + 1 := by
  classical
  choose! f hf1 hf2 using h
  have hinj : Set.InjOn f (Finset.Ico i₀ (i₀ + N) : Set ℤ) := by
    intro z hz z' hz' hff
    have hz1 := hf1 z (Finset.mem_coe.1 hz)
    have hz2 := hf1 z' (Finset.mem_coe.1 hz')
    have : ((z : ℤ) : ZMod m) = ((z' : ℤ) : ZMod m) := by rw [← hz1, ← hz2, hff]
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub z' z m).1 this.symm
    have hzI := Finset.mem_Ico.1 (Finset.mem_coe.1 hz)
    have hzI' := Finset.mem_Ico.1 (Finset.mem_coe.1 hz')
    have habs : |z - z'| < (m : ℤ) := by
      rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hd habs
    omega
  have hmaps : ∀ z ∈ Finset.Ico i₀ (i₀ + N), f z ∈ Finset.Icc (c - ((m : ℤ) - 1) / 4)
      (c + ((m : ℤ) - 1) / 4) := by
    intro z hz
    have h2 := hf2 z hz
    rw [Finset.mem_Icc]
    rcases abs_cases (f z - c) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega
  have hcard := Finset.card_le_card_of_injOn f (fun z hz => hmaps z hz) hinj
  simp only [Int.card_Ico, Int.card_Icc] at hcard
  omega

section Size

variable {d M1 c n1 L k : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n1] {ω : ℕ}
  {Zp : Set (Torus d n1)} {Z' : Finset (Torus d n1)}

/-- **The box room of `V`.** -/
theorem size_of_V (hd : 0 < d) (hc : 14 ≤ c) (ρ : ℕ) (hZ' : Z' ∈ comps ω (finOf Zp))
    {m' : ℕ} [NeZero m'] {cc : Fin d → ℤ}
    (hV : ∀ x ∈ (fineK1 M1 c n1 L k (nbhd 1 (thick ρ (Z' : Set (Torus d n1)))) : Finset _),
      InBox (M1 * (c * n1) * L ^ (k + 1)) m' cc (liftNear cc x)) :
    4 * ((L ^ (k + 1) * (c * M1)) * (ρ + 2)) ≤ M1 * (c * n1) * L ^ (k + 1) := by
  obtain ⟨x, hx⟩ := comp_nonempty hZ'
  obtain ⟨z₀, hz₀⟩ := exists_rep (m := n1) x
  set P1 := L ^ (k + 1) * (c * M1) with hP1
  have hP1pos : 0 < P1 := P1_pos
  have hP1' : (P1 : ℤ) ≠ 0 := by exact_mod_cast hP1pos.ne'
  have hm3 : 3 ≤ M1 * (c * n1) * L ^ (k + 1) := by
    have h1 : 0 < M1 := Nat.pos_of_ne_zero (NeZero.ne M1)
    have h2 : 0 < n1 := Nat.pos_of_ne_zero (NeZero.ne n1)
    have h3 : 0 < L ^ (k + 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
    calc 3 ≤ c := by omega
      _ = 1 * (c * 1) * 1 := by ring
      _ ≤ M1 * (c * n1) * L ^ (k + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 (Nat.mul_le_mul le_rfl h2)) h3
  set m := M1 * (c * n1) * L ^ (k + 1) with hm
  let μ₀ : Fin d := ⟨0, hd⟩
  let N : ℕ := min ((2 * ρ + 5) * P1) m
  have hN : N ≤ m := min_le_right _ _
  have key := two_mul_le_of_box (m := m) (c := cc μ₀) (i₀ := (z₀ μ₀ - ρ - 2) * (P1 : ℤ)) (N := N) hN
    (fun z hz => by
      rw [Finset.mem_Ico] at hz
      have hNle : (N : ℤ) ≤ ((2 * ρ + 5) * P1 : ℕ) := by exact_mod_cast min_le_left _ _
      set y : Fin d → ℤ := Function.update (fun μ => (P1 : ℤ) * z₀ μ) μ₀ z with hy
      have hyμ : y μ₀ = z := by simp [hy]
      -- the cube of `y` is within `ρ + 2` of the cube of `z₀`
      have hdiv : ∀ μ, y μ / (P1 : ℤ) = if μ = μ₀ then z / (P1 : ℤ) else z₀ μ := by
        intro μ
        by_cases h : μ = μ₀
        · simp only [h, ↓reduceIte]; rw [hyμ]
        · simp only [h, ↓reduceIte]; simp [hy, h, Int.mul_ediv_cancel_left _ hP1']
      have hbd : ∀ μ, |z₀ μ - y μ / (P1 : ℤ)| ≤ ((ρ + 2 : ℕ) : ℤ) := by
        intro μ
        rw [hdiv μ]
        by_cases h : μ = μ₀
        · simp only [h, ↓reduceIte]
          have hP : (0 : ℤ) < P1 := by exact_mod_cast hP1pos
          have h1 : z₀ μ₀ - (ρ : ℤ) - 2 ≤ z / (P1 : ℤ) := by
            have : (z₀ μ₀ - ρ - 2) * (P1 : ℤ) ≤ z := hz.1
            exact (Int.le_ediv_iff_mul_le hP).2 this
          have h2 : z / (P1 : ℤ) < z₀ μ₀ + ρ + 3 := by
            have : z < (z₀ μ₀ + ρ + 3) * (P1 : ℤ) := by
              have e : (z₀ μ₀ - ρ - 2) * (P1 : ℤ) + ((2 * ρ + 5) * P1 : ℕ) =
                  (z₀ μ₀ + ρ + 3) * (P1 : ℤ) := by push_cast; ring
              linarith [hz.2]
            exact (Int.ediv_lt_iff_lt_mul hP).2 this
          rw [abs_le]
          push_cast
          constructor <;> omega
        · simp only [h, ↓reduceIte, sub_self, abs_zero]; positivity
      have hmemV : zcast m y ∈
          (fineK1 M1 c n1 L k (nbhd 1 (thick ρ (Z' : Set (Torus d n1)))) : Set _) := by
        rw [Finset.mem_coe, mem_fineK1, blockMap_zcast fine_eq_P1 P1_pos]
        have hnb : zcast n1 (fun μ => y μ / (P1 : ℤ)) ∈ nbhd (ρ + 2) (Z' : Set (Torus d n1)) := by
          rw [mem_nbhd_zcast]
          refine ⟨fun μ => z₀ μ - y μ / (P1 : ℤ), hbd, ?_⟩
          have : ((fun μ => y μ / (P1 : ℤ)) + fun μ => z₀ μ - y μ / (P1 : ℤ)) = z₀ := by
            funext μ; simp
          rw [this, hz₀]; exact Finset.mem_coe.2 hx
        have hsub := nbhd_add_subset (Z' : Set (Torus d n1)) (ρ + 1) 1
        have e : 1 + (ρ + 1) = ρ + 2 := by omega
        rw [e] at hsub
        exact hsub hnb
      have hbox := (hV _ (Finset.mem_coe.1 hmemV)) μ₀
      refine ⟨liftNear cc (zcast m y) μ₀, ?_, hbox.1⟩
      have := congrFun (zcast_liftNear (c := cc) (zcast m y)) μ₀
      rw [← hyμ]
      simpa [zcast] using this)
  rcases min_cases ((2 * ρ + 5) * P1) m with ⟨h1, _⟩ | ⟨h1, _⟩
  · have e : N = (2 * ρ + 5) * P1 := h1
    have h2 := key
    rw [e] at h2
    nlinarith
  · have e : N = m := h1
    have h2 := key
    rw [e] at h2
    omega

end Size

end Balaban.RootFSpine
