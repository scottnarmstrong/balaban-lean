/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusGenCubeInt
public import Balaban.LargeField.Background.TwoTorusGenAgree
public import Balaban.LargeField.Background.TwoTorusPb

/-!
# The generating set of a cube on two tori

For corresponding cubes `a₁ = zcast n₁ (bidx P w₀)`, `a₂ = zcast n₂ (bidx P w₀)` of the cube tori
(side `P = L^q (c M₁)`) with `w₀` in the box with margin `5P + 2`, the generating sets
`G_q(a₁)`, `G_q(a₂)` of Definition II.2.4 (i) agree on the box (`genAgree_genCube`), and so do the
generating sets `G_{k+1}(a_i)` with top layer cut by corresponding sets (`genAgree_genCubeMixed`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField

section Cube

variable {d M1 c L q n₁ n₂ : ℕ} [NeZero M1] [NeZero c] [NeZero L] [NeZero n₁] [NeZero n₂]

omit [NeZero M1] [NeZero c] [NeZero L] in
theorem fine_eq_Pq (n : ℕ) : M1 * (c * n) * L ^ q = (L ^ q * (c * M1)) * n := by ring

theorem P_pos' : 0 < L ^ q * (c * M1) :=
  Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
    (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne c)) (Nat.pos_of_ne_zero (NeZero.ne M1)))

omit [NeZero M1] [NeZero c] [NeZero L] in
theorem twelve_le_P (hc : 14 ≤ c) : 12 * (L ^ q * M1) ≤ L ^ q * (c * M1) := by
  have h : 14 * (L ^ q * M1) ≤ c * (L ^ q * M1) := Nat.mul_le_mul_right _ hc
  have e : L ^ q * (c * M1) = c * (L ^ q * M1) := by ring
  rw [e]
  omega

/-- The integer set `pbZ` of the neighbourhood of a cube, as the exact shifts of its lift. -/
theorem mem_genCube_set_iff {n r : ℕ} [NeZero n] (a : Torus d n) (w : Fin d → ℤ) :
    zcast (M1 * (c * n) * L ^ q) w ∈ cubePre M1 (c * n) L q (L ^ q * (c * M1)) n (nbhd r {a}) ↔
      ∃ s : Fin d → ℤ, (∀ μ, |s μ| ≤ r) ∧ zcast n (bidx (L ^ q * (c * M1)) w + s) = a :=
  mem_cubePre_nbhd_zcast P_pos' (fine_eq_Pq n) a w

omit [NeZero n₁] [NeZero n₂] in
/-- On a ball of radius `12 L^q M₁` about a point of the box, membership in the neighbourhood of a
cube is the same on both tori. -/
theorem nbhd_cube_agree (hc : 14 ≤ c) {ℓ₁ ℓ₂ : ℕ} {cc w w₀ z : Fin d → ℤ} {r : ℕ}
    (hℓ₁ : ℓ₁ = (L ^ q * (c * M1)) * n₁) (hℓ₂ : ℓ₂ = (L ^ q * (c * M1)) * n₂)
    (hn₁ : 2 * r + 8 ≤ n₁) (hn₂ : 2 * r + 8 ≤ n₂) (hw : InBox ℓ₁ ℓ₂ cc w)
    (hw₀ : InBox ℓ₁ ℓ₂ cc w₀) (hz : ∀ μ, |z μ - w μ| ≤ ((12 * (L ^ q * M1) : ℕ) : ℤ)) :
    (∃ s : Fin d → ℤ, (∀ μ, |s μ| ≤ r) ∧
        zcast n₁ (bidx (L ^ q * (c * M1)) z + s) = zcast n₁ (bidx (L ^ q * (c * M1)) w₀)) ↔
      ∃ s : Fin d → ℤ, (∀ μ, |s μ| ≤ r) ∧
        zcast n₂ (bidx (L ^ q * (c * M1)) z + s) = zcast n₂ (bidx (L ^ q * (c * M1)) w₀) := by
  have hP := P_pos' (L := L) (q := q) (c := c) (M1 := M1)
  have hρ := twelve_le_P (L := L) (q := q) (c := c) (M1 := M1) hc
  have key : ∀ {ℓ n : ℕ}, ℓ = (L ^ q * (c * M1)) * n → 2 * r + 8 ≤ n →
      (∀ μ, 4 * |w μ - cc μ| < ℓ) → (∀ μ, 4 * |w₀ μ - cc μ| < ℓ) → ∀ μ,
      |bidx (L ^ q * (c * M1)) z μ - bidx (L ^ q * (c * M1)) w₀ μ| + r < n := by
    intro ℓ n hℓ hn hwb hw₀b μ
    have h1 := hz μ
    have h2 := hwb μ
    have h3 := hw₀b μ
    have hℓi : (ℓ : ℤ) = ((L ^ q * (c * M1) : ℕ) : ℤ) * n := by rw [hℓ]; push_cast; ring
    have h4 : |z μ - w₀ μ| ≤ |z μ - w μ| + |w μ - cc μ| + |cc μ - w₀ μ| := by
      have a1 := abs_sub_le (z μ) (w μ) (w₀ μ)
      have a2 := abs_sub_le (w μ) (cc μ) (w₀ μ)
      linarith
    rw [abs_sub_comm (cc μ) (w₀ μ)] at h4
    exact_mod_cast ediv_close_lt_r (P := ((L ^ q * (c * M1) : ℕ) : ℤ)) (n := n) (ρ := ((12 * (L ^ q * M1) : ℕ) : ℤ))
      (r := r) (by exact_mod_cast hP) (by exact_mod_cast hρ) (by exact_mod_cast hn)
      (by rw [hℓi] at h2 h3; linarith)
  rw [exists_shift_iff (key hℓ₁ hn₁ (fun μ => (hw μ).1) (fun μ => (hw₀ μ).1)),
    exists_shift_iff (key hℓ₂ hn₂ (fun μ => (hw μ).2) (fun μ => (hw₀ μ).2))]

/-- The layers `Ω_m` of `G_q(a)` on integer lifts. -/
theorem mem_genCube_Ω_iff {n : ℕ} [NeZero n] (a : Torus d n) (m : ℕ) (w : Fin d → ℤ) :
    zcast (M1 * (c * n) * L ^ q) w ∈
        (genCube (M1 := M1) (N₁ := c * n) (L := L) (q := q) c n a).Ω m ↔
      w ∈ minLayerZ L M1 q (pbZ (M1 * (c * n) * L ^ q)
        ((cubePre M1 (c * n) L q (L ^ q * (c * M1)) n (nbhd 2 {a}) : Finset _) :
          Set (Torus d (M1 * (c * n) * L ^ q)))) m := by
  rw [genCube_Ω, ← pbZ_minLayer (M1 := M1) (N₁ := c * n) (L := L) (q := q) (j := q) le_rfl
    (cubePre M1 (c * n) L q (L ^ q * (c * M1)) n (nbhd 2 {a})) m]
  rfl

theorem abs_ediv_sub_le_one {P a b : ℤ} (hP : 0 < P) (h : |a - b| ≤ P) : |a / P - b / P| ≤ 1 := by
  have := ediv_diff_bound hP h
  by_contra hc
  have h2 : 2 ≤ |a / P - b / P| := by omega
  nlinarith

/-- **The support of `G_q(a)` lies near the cube**: the representatives of the sites of `Ω₁`
are within `4 P` of `w₀`. -/
theorem genCube_supp (hc : 14 ≤ c) (hL : 2 ≤ L) {ℓ' : ℕ} {cc w₀ : Fin d → ℤ} {n : ℕ} [NeZero n]
    (hw₀ : InBoxK (5 * (L ^ q * (c * M1)) + 2) (M1 * (c * n) * L ^ q) ℓ' cc w₀)
    {x : Torus d (M1 * (c * n) * L ^ q)}
    (hx : x ∈ (genCube (M1 := M1) (N₁ := c * n) (L := L) (q := q) c n
      (zcast n (bidx (L ^ q * (c * M1)) w₀))).Ω 1) :
    ∀ μ, |liftNear cc x μ - w₀ μ| ≤ ((4 * (L ^ q * (c * M1)) : ℕ) : ℤ) := by
  have hP := P_pos' (L := L) (q := q) (c := c) (M1 := M1)
  have hM1 : 0 < M1 := Nat.pos_of_ne_zero (NeZero.ne M1)
  rw [← zcast_liftNear (c := cc) x, mem_genCube_Ω_iff] at hx
  obtain ⟨z, hz, hzd⟩ := minLayerZ_supp L M1 q hL hM1 1 hx
  have hz' : zcast (M1 * (c * n) * L ^ q) z ∈
      cubePre M1 (c * n) L q (L ^ q * (c * M1)) n (nbhd 2 {zcast n (bidx (L ^ q * (c * M1)) w₀)}) :=
    hz
  obtain ⟨s, hs, hsz⟩ := (mem_genCube_set_iff _ z).1 hz'
  have hρ := twelve_le_P (L := L) (q := q) (c := c) (M1 := M1) hc
  have h11 : (11 * (L ^ q * M1) : ℕ) ≤ L ^ q * (c * M1) := by omega
  have hbl : blockMap (L ^ q * (c * M1)) n x ∈
      nbhd 3 {zcast n (bidx (L ^ q * (c * M1)) w₀)} := by
    rw [← zcast_liftNear (c := cc) x, blockMap_zcast (fine_eq_Pq n) hP]
    show zcast n (bidx (L ^ q * (c * M1)) (liftNear cc x)) ∈
      nbhd 3 {zcast n (bidx (L ^ q * (c * M1)) w₀)}
    rw [mem_nbhd_zcast (bidx (L ^ q * (c * M1)) (liftNear cc x))]
    refine ⟨fun μ => s μ + bidx (L ^ q * (c * M1)) z μ - bidx (L ^ q * (c * M1)) (liftNear cc x) μ,
      fun μ => ?_, ?_⟩
    · set Pz : ℤ := ((L ^ q * (c * M1) : ℕ) : ℤ) with hPz
      have hdist : |liftNear cc x μ - z μ| ≤ Pz := by
        rw [abs_sub_comm]
        exact (hzd μ).trans (Nat.cast_le.2 h11)
      have h1 := abs_ediv_sub_le_one (P := Pz) (a := liftNear cc x μ) (b := z μ)
        (by rw [hPz]; exact_mod_cast hP) hdist
      have h5 : |z μ / Pz - liftNear cc x μ / Pz| ≤ 1 := by rw [abs_sub_comm]; exact h1
      have h2 : |s μ| ≤ 2 := by exact_mod_cast hs μ
      have h3 := abs_add_le (s μ) (z μ / Pz - liftNear cc x μ / Pz)
      have h4 : s μ + z μ / Pz - liftNear cc x μ / Pz =
          s μ + (z μ / Pz - liftNear cc x μ / Pz) := by ring
      show |s μ + z μ / Pz - liftNear cc x μ / Pz| ≤ ((3 : ℕ) : ℤ)
      rw [h4]
      push_cast
      linarith
    · rw [← hsz]
      congr 1
      funext μ
      simp only [Pi.add_apply]
      ring
  exact nbhd_cube_near (r := 3) hP (fine_eq_Pq n) (hw₀.mono (le_refl _)) (by omega) _ hbl

/-- **The generating sets `G_q(a)` of corresponding cubes of two tori agree on the box**
(Definition II.2.4 (i)): `a_i = zcast n_i (bidx P w₀)`, `w₀` in the box with margin `5 P + 2`,
`P = L^q (c M₁)`. -/
theorem genAgree_genCube (hc : 14 ≤ c) (hL : 2 ≤ L) {cc w₀ : Fin d → ℤ} (hn₁ : 12 ≤ n₁)
    (hn₂ : 12 ≤ n₂)
    (hw₀ : InBoxK (5 * (L ^ q * (c * M1)) + 2) (M1 * (c * n₁) * L ^ q) (M1 * (c * n₂) * L ^ q)
      cc w₀) :
    GenAgree (genCube (M1 := M1) (N₁ := c * n₁) (L := L) (q := q) c n₁
        (zcast n₁ (bidx (L ^ q * (c * M1)) w₀)))
      (genCube (M1 := M1) (N₁ := c * n₂) (L := L) (q := q) c n₂
        (zcast n₂ (bidx (L ^ q * (c * M1)) w₀))) cc := by
  have hP := P_pos' (L := L) (q := q) (c := c) (M1 := M1)
  have hM1 : 0 < M1 := Nat.pos_of_ne_zero (NeZero.ne M1)
  have hsupp : ∀ {ℓ ℓ' n : ℕ} [NeZero n], 12 ≤ n → ℓ = M1 * (c * n) * L ^ q →
      InBoxK (5 * (L ^ q * (c * M1)) + 2) ℓ ℓ' cc w₀ →
      ∀ x : Torus d (M1 * (c * n) * L ^ q),
        x ∈ (genCube (M1 := M1) (N₁ := c * n) (L := L) (q := q) c n
          (zcast n (bidx (L ^ q * (c * M1)) w₀))).Ω 1 →
        InBoxK 2 ℓ ℓ' cc (liftNear cc x) := by
    intro ℓ ℓ' n _ hn hℓ hb x hx
    subst hℓ
    have := genCube_supp hc hL hb hx
    intro μ
    have h1 := hb μ
    have h2 := this μ
    have h3 : |liftNear cc x μ - cc μ| ≤ |liftNear cc x μ - w₀ μ| + |w₀ μ - cc μ| := by
      have := abs_sub_le (liftNear cc x μ) (w₀ μ) (cc μ); exact this
    push_cast at h2 h1 ⊢
    constructor <;> nlinarith [h1.1, h1.2]
  refine ⟨fun x hx => hsupp hn₁ rfl hw₀ x hx, fun x hx => (hsupp hn₂ rfl hw₀.symm x hx).symm,
    fun n h1 h2 w hw => ?_⟩
  rw [mem_genCube_Ω_iff, mem_genCube_Ω_iff]
  have hagr : AgrB w (0 + 12 * (L ^ q * M1))
      (pbZ (M1 * (c * n₁) * L ^ q) ((cubePre M1 (c * n₁) L q (L ^ q * (c * M1)) n₁
        (nbhd 2 {zcast n₁ (bidx (L ^ q * (c * M1)) w₀)}) : Finset _) : Set _))
      (pbZ (M1 * (c * n₂) * L ^ q) ((cubePre M1 (c * n₂) L q (L ^ q * (c * M1)) n₂
        (nbhd 2 {zcast n₂ (bidx (L ^ q * (c * M1)) w₀)}) : Finset _) : Set _)) := by
    intro z hz
    simp only [zero_add] at hz
    simp only [mem_pbZ, Finset.mem_coe, mem_genCube_set_iff]
    exact nbhd_cube_agree hc (fine_eq_Pq n₁) (fine_eq_Pq n₂) (r := 2) (by omega) (by omega) hw
      hw₀.inBox hz
  have := AgrB.minLayer L M1 q hL hM1 n hagr
  exact this w (fun μ => by simp)

end Cube

section Mixed

variable {d L N₁ N₂ k : ℕ} [NeZero N₁] [NeZero N₂] [NeZero L] {ϱ₁ ϱ₂ : ℝ}
  {G₁ : GeneratingSet d L N₁ k ϱ₁} {G₂ : GeneratingSet d L N₂ k ϱ₂} {cc : Fin d → ℤ}

/-- Replacing the top layers by corresponding sets keeps the agreement on the box. -/
theorem GenAgree.withTop (hA : GenAgree G₁ G₂ cc) {Y₁ : Finset (Torus d (N₁ * L ^ k))}
    {Y₂ : Finset (Torus d (N₂ * L ^ k))} (hY₁ : IsBlockUnion L N₁ k k Y₁) (hYG₁ : Y₁ ⊆ G₁.Ω k)
    (hY₂ : IsBlockUnion L N₂ k k Y₂) (hYG₂ : Y₂ ⊆ G₂.Ω k)
    (hiff : ∀ w, InBox (N₁ * L ^ k) (N₂ * L ^ k) cc w →
      (zcast (N₁ * L ^ k) w ∈ Y₁ ↔ zcast (N₂ * L ^ k) w ∈ Y₂)) :
    GenAgree (G₁.withTop Y₁ hY₁ hYG₁) (G₂.withTop Y₂ hY₂ hYG₂) cc := by
  have hsub₁ : (G₁.withTop Y₁ hY₁ hYG₁).Ω 1 ⊆ G₁.Ω 1 := by
    intro x hx
    rw [GeneratingSet.withTop_Ω] at hx
    by_cases h : 1 = k
    · simp only [h, ↓reduceIte] at hx
      subst h
      exact hYG₁ hx
    · simpa [h] using hx
  have hsub₂ : (G₂.withTop Y₂ hY₂ hYG₂).Ω 1 ⊆ G₂.Ω 1 := by
    intro x hx
    rw [GeneratingSet.withTop_Ω] at hx
    by_cases h : 1 = k
    · simp only [h, ↓reduceIte] at hx
      subst h
      exact hYG₂ hx
    · simpa [h] using hx
  refine ⟨fun x hx => hA.supp₁ x (hsub₁ hx), fun x hx => hA.supp₂ x (hsub₂ hx),
    fun n h1 h2 w hw => ?_⟩
  rw [GeneratingSet.withTop_Ω, GeneratingSet.withTop_Ω]
  by_cases hnk : n = k
  · simp only [hnk, ↓reduceIte]
    exact hiff w hw
  · simp only [hnk, ↓reduceIte]
    exact hA.agree n h1 h2 w hw

end Mixed

section CubeMixed

variable {d M1 c L q n₁ n₂ : ℕ} [NeZero M1] [NeZero c] [NeZero L] [NeZero n₁] [NeZero n₂]

/-- **The generating sets `G_q(a)` with top layer `Om ∩ a^{∼2}` of corresponding cubes of two tori
agree on the box** (Definition II.2.4 (ii)), when `Om₁`, `Om₂` agree on the box. -/
theorem genAgree_genCubeMixed (hc : 14 ≤ c) (hL : 2 ≤ L) {cc w₀ : Fin d → ℤ} (hn₁ : 12 ≤ n₁)
    (hn₂ : 12 ≤ n₂)
    (hw₀ : InBoxK (5 * (L ^ q * (c * M1)) + 2) (M1 * (c * n₁) * L ^ q) (M1 * (c * n₂) * L ^ q)
      cc w₀)
    (hm₁ : (c * n₁) * L ^ (q - q) = c * n₁) (hm₂ : (c * n₂) * L ^ (q - q) = c * n₂)
    (Om₁ : Finset (Torus d (M1 * (c * n₁) * L ^ q)))
    (Om₂ : Finset (Torus d (M1 * (c * n₂) * L ^ q)))
    (hOm₁ : IsBlockUnion L (M1 * (c * n₁)) q q Om₁) (hOm₂ : IsBlockUnion L (M1 * (c * n₂)) q q Om₂)
    (hiff : ∀ w, InBox (M1 * (c * n₁) * L ^ q) (M1 * (c * n₂) * L ^ q) cc w →
      (zcast (M1 * (c * n₁) * L ^ q) w ∈ Om₁ ↔ zcast (M1 * (c * n₂) * L ^ q) w ∈ Om₂)) :
    GenAgree (genCubeMixed (M1 := M1) (N₁ := c * n₁) (L := L) (q := q) (c := c) (n := n₁) hm₁
        (zcast n₁ (bidx (L ^ q * (c * M1)) w₀)) Om₁ hOm₁)
      (genCubeMixed (M1 := M1) (N₁ := c * n₂) (L := L) (q := q) (c := c) (n := n₂) hm₂
        (zcast n₂ (bidx (L ^ q * (c * M1)) w₀)) Om₂ hOm₂) cc := by
  unfold genCubeMixed
  refine (genAgree_genCube hc hL hn₁ hn₂ hw₀).withTop _ _ _ _ fun w hw => ?_
  rw [Finset.mem_inter, Finset.mem_inter, hiff w hw, mem_cubePre, mem_cubePre,
    blockMap_zcast (fine_eq_Pq n₁) P_pos', blockMap_zcast (fine_eq_Pq n₂) P_pos']
  refine and_congr_right fun _ => ?_
  have h1 := mem_genCube_set_iff (M1 := M1) (c := c) (L := L) (q := q) (r := 2)
    (zcast n₁ (bidx (L ^ q * (c * M1)) w₀)) w
  have h2 := mem_genCube_set_iff (M1 := M1) (c := c) (L := L) (q := q) (r := 2)
    (zcast n₂ (bidx (L ^ q * (c * M1)) w₀)) w
  rw [mem_cubePre, blockMap_zcast (fine_eq_Pq n₁) P_pos'] at h1
  rw [mem_cubePre, blockMap_zcast (fine_eq_Pq n₂) P_pos'] at h2
  rw [h1, h2]
  exact nbhd_cube_agree hc (fine_eq_Pq n₁) (fine_eq_Pq n₂) (r := 2) (by omega) (by omega) hw
    hw₀.inBox (z := w) (fun μ => by simp only [sub_self, abs_zero]; positivity)

/-- **The fine sets `T_q(□^{∼r})` of corresponding cubes correspond** (`r ≤ 3`). -/
theorem setCorr_cubeNbhd (hc : 14 ≤ c) {r : ℕ} (hr : r ≤ 3) {cc w₀ : Fin d → ℤ}
    (hn₁ : 2 * r + 8 ≤ n₁) (hn₂ : 2 * r + 8 ≤ n₂)
    (hw₀ : InBoxK (5 * (L ^ q * (c * M1)) + 2) (M1 * (c * n₁) * L ^ q) (M1 * (c * n₂) * L ^ q)
      cc w₀) :
    SetCorr cc
      ((cubeNbhd M1 (c * n₁) L q c n₁ r (zcast n₁ (bidx (L ^ q * (c * M1)) w₀)) :
        Finset (Torus d (M1 * (c * n₁) * L ^ q))) : Set (Torus d (M1 * (c * n₁) * L ^ q)))
      ((cubeNbhd M1 (c * n₂) L q c n₂ r (zcast n₂ (bidx (L ^ q * (c * M1)) w₀)) :
        Finset (Torus d (M1 * (c * n₂) * L ^ q))) : Set (Torus d (M1 * (c * n₂) * L ^ q))) := by
  have hP := P_pos' (L := L) (q := q) (c := c) (M1 := M1)
  have hbox : ∀ {ℓ ℓ' n : ℕ} [NeZero n], ℓ = M1 * (c * n) * L ^ q →
      InBoxK (5 * (L ^ q * (c * M1)) + 2) ℓ ℓ' cc w₀ → ∀ x : Torus d (M1 * (c * n) * L ^ q),
      x ∈ cubeNbhd M1 (c * n) L q c n r (zcast n (bidx (L ^ q * (c * M1)) w₀)) →
      InBox ℓ ℓ' cc (liftNear cc x) := by
    intro ℓ ℓ' n _ hℓ hb x hx
    subst hℓ
    have hx' : blockMap (L ^ q * (c * M1)) n x ∈ nbhd r {zcast n (bidx (L ^ q * (c * M1)) w₀)} :=
      mem_cubePre.1 hx
    have := nbhd_cube_near (r := r) hP (fine_eq_Pq n) hb (by nlinarith) x hx'
    intro μ
    have h1 := hb μ
    have h2 := this μ
    have h3 : |liftNear cc x μ - cc μ| ≤ |liftNear cc x μ - w₀ μ| + |w₀ μ - cc μ| := by
      have := abs_sub_le (liftNear cc x μ) (w₀ μ) (cc μ); exact this
    push_cast at h2 h1 ⊢
    constructor <;> nlinarith [h1.1, h1.2]
  refine ⟨fun x hx => hbox rfl hw₀ x (Finset.mem_coe.1 hx),
    fun x hx => (hbox rfl hw₀.symm x (Finset.mem_coe.1 hx)).symm, fun x₁ x₂ hx => ?_⟩
  simp only [Finset.mem_coe]
  constructor
  · intro h
    have hb := hbox rfl hw₀ x₁ h
    obtain ⟨v, hv, rfl, rfl⟩ := ptCorr_iff_exists.1 (⟨hx, hb⟩ : PtCorr cc x₁ x₂)
    change zcast (M1 * (c * n₁) * L ^ q) v ∈ cubePre M1 (c * n₁) L q (L ^ q * (c * M1)) n₁ _ at h
    change zcast (M1 * (c * n₂) * L ^ q) v ∈ cubePre M1 (c * n₂) L q (L ^ q * (c * M1)) n₂ _
    rw [mem_genCube_set_iff] at h ⊢
    exact (nbhd_cube_agree hc (fine_eq_Pq n₁) (fine_eq_Pq n₂) (r := r) hn₁ hn₂ hv hw₀.inBox
      (z := v) (fun μ => by simp only [sub_self, abs_zero]; positivity)).1 h
  · intro h
    have hb := (hbox rfl hw₀.symm x₂ h).symm
    obtain ⟨v, hv, rfl, rfl⟩ := ptCorr_iff_exists.1 (⟨hx, hx ▸ hb⟩ : PtCorr cc x₁ x₂)
    change zcast (M1 * (c * n₂) * L ^ q) v ∈ cubePre M1 (c * n₂) L q (L ^ q * (c * M1)) n₂ _ at h
    change zcast (M1 * (c * n₁) * L ^ q) v ∈ cubePre M1 (c * n₁) L q (L ^ q * (c * M1)) n₁ _
    rw [mem_genCube_set_iff] at h ⊢
    exact (nbhd_cube_agree hc (fine_eq_Pq n₁) (fine_eq_Pq n₂) (r := r) hn₁ hn₂ hv hw₀.inBox
      (z := v) (fun μ => by simp only [sub_self, abs_zero]; positivity)).2 h

end CubeMixed

end Balaban.RootFSpine
