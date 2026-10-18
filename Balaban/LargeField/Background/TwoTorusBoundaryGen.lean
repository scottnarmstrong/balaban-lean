/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusPb
public import Balaban.LargeField.Background.TwoTorusLocal
public import Balaban.LargeField.Background.TwoTorusModel
public import Balaban.LargeField.Background.TwoTorusGenAgree

/-!
# The local boundary generating sets of two tori agree on a box

For two tori with a component `Z'` of `Z^pre_{k+1}` on each, if the fine sets of `Z'`, of
`Z_k ∩ Z'` and of `Ω_{k+1} ∩ Z'` correspond (`SetCorr`) and the sets `V = (Z'^≈)^∼` lie in the box
of both tori, the local boundary generating sets `G^{Z'}_{k+1}` of the two tori agree on the box
(`genAgree_genBoundaryLocal`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField

set_option linter.unusedSectionVars false

section Narrow

variable {d : ℕ}

theorem narrow_aux {m m' : ℕ} [NeZero m] {c : Fin d → ℤ} {A : Set (Torus d m)}
    (hA : ∀ x ∈ A, InBox m m' c (liftNear c x)) {w z : Fin d → ℤ} {R : ℕ}
    (hw : InBox m m' c w) (hz : ∀ μ, |z μ - w μ| ≤ R) (hR : 2 * (R : ℤ) ≤ m)
    (hmem : zcast m z ∈ A) : InBox m m' c z := by
  have hz₀ := hA _ hmem
  have hzz : zcast m (liftNear c (zcast m z)) = zcast m z := zcast_liftNear _
  have heq : liftNear c (zcast m z) = z := by
    refine ((zcast_eq_iff_of_abs_lt (n := m) (a := liftNear c (zcast m z)) (b := z)
      (fun μ => ?_)).1 hzz)
    have h1 := (hz₀ μ).1
    have h2 := (hw μ).1
    have h3 := hz μ
    have t1 := abs_sub_le (liftNear c (zcast m z) μ) (c μ) (z μ)
    have t2 := abs_sub_le (c μ) (w μ) (z μ)
    have e1 : |c μ - w μ| = |w μ - c μ| := abs_sub_comm _ _
    have e2 : |w μ - z μ| = |z μ - w μ| := abs_sub_comm _ _
    linarith
  rw [heq] at hz₀
  exact hz₀

theorem agrB_narrow₁ {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] {c : Fin d → ℤ} {A₁ : Set (Torus d m₁)}
    {A₂ : Set (Torus d m₂)} (hA : SetCorr c A₁ A₂) {w : Fin d → ℤ} (hw : InBox m₁ m₂ c w) {R : ℕ}
    (hR : 2 * (R : ℤ) ≤ m₁) :
    AgrB w R (pbZ m₁ A₁) {z | InBox m₁ m₂ c z ∧ zcast m₁ z ∈ A₁} := by
  intro z hz
  simp only [mem_pbZ, Set.mem_ofPred_eq]
  constructor
  · intro hmem
    exact ⟨narrow_aux hA.1 hw hz hR hmem, hmem⟩
  · exact fun h => h.2

theorem agrB_narrow₂ {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] {c : Fin d → ℤ} {A₁ : Set (Torus d m₁)}
    {A₂ : Set (Torus d m₂)} (hA : SetCorr c A₁ A₂) {w : Fin d → ℤ} (hw : InBox m₁ m₂ c w) {R : ℕ}
    (hR : 2 * (R : ℤ) ≤ m₂) :
    AgrB w R (pbZ m₂ A₂) {z | InBox m₁ m₂ c z ∧ zcast m₁ z ∈ A₁} := by
  intro z hz
  simp only [mem_pbZ, Set.mem_ofPred_eq]
  constructor
  · intro hmem
    have hbox : InBox m₂ m₁ c z :=
      narrow_aux (fun x hx => (hA.2.1 x hx).symm) hw.symm hz hR hmem
    have hbox' : InBox m₁ m₂ c z := hbox.symm
    refine ⟨hbox', ?_⟩
    exact (hA.2.2 (zcast m₁ z) (zcast m₂ z) (by
      rw [hbox'.liftNear_zcast₁, hbox'.liftNear_zcast₂])).2 hmem
  · rintro ⟨hbox, hmem⟩
    exact (hA.2.2 (zcast m₁ z) (zcast m₂ z) (by
      rw [hbox.liftNear_zcast₁, hbox.liftNear_zcast₂])).1 hmem

end Narrow

section Own

variable {d M1 c n1 L k n0 : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} {ω : ℕ} {Zp : Set (Torus d n1)} {Z' : Finset (Torus d n1)}

theorem cubeConst_zZ :
    CubeConst (L ^ (k + 1) * (c * M1))
      (pbZ (M1 * (c * n1) * L ^ (k + 1))
        ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
          Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))) := by
  intro z z' h
  rw [pbZ_fineK1]
  simp only [Set.mem_ofPred_eq]
  have : (fun μ => z μ / ((L ^ (k + 1) * (c * M1) : ℕ) : ℤ)) =
      (fun μ => z' μ / ((L ^ (k + 1) * (c * M1) : ℕ) : ℤ)) := funext h
  rw [this]

theorem P1_eq : L ^ (k + 1) * (c * M1) = L * (L ^ k * (c * M1)) := by ring

theorem twelve_le_P1 (hc : 14 ≤ c) :
    12 * (L ^ (k + 1) * M1) + 2 ≤ L ^ (k + 1) * (c * M1) := by
  have hx : 1 ≤ L ^ (k + 1) * M1 := Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
    (Nat.pos_of_ne_zero (NeZero.ne M1))
  have : L ^ (k + 1) * (c * M1) = c * (L ^ (k + 1) * M1) := by ring
  rw [this]
  nlinarith

/-- The layer `Ω_n` of the local boundary family, at the lift `w`, equals the layer of the model
built from model sets that agree with `Z'`, `Z_k ∩ Z'`, `Ω_{k+1} ∩ Z'` on the ball about `w`. -/
theorem mem_Ω_iff_model (st : RegionStep d L n0 n1 Rprev Rk) (hc : 14 ≤ c) (hn : n0 = L * n1)
    (hL : 2 ≤ L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hmono : ⌊Rprev⌋₊ ≤ ⌊Rk⌋₊)
    (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω) (hZ : st.Omegaᶜ ⊆ Zp) (hZ' : Z' ∈ comps ω (finOf Zp))
    {w : Fin d → ℤ} {M𝒵 Mℛ MℛΩ : Set (Fin d → ℤ)}
    (hAZ : AgrB w (12 * (L ^ (k + 1) * M1) + (L ^ (k + 1) * (c * M1)) * (⌊Rk⌋₊ + 1))
      (pbZ (M1 * (c * n1) * L ^ (k + 1))
        ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
          Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))) M𝒵)
    (hAR : AgrB w (12 * (L ^ (k + 1) * M1) + (L ^ (k + 1) * (c * M1)) * (⌊Rk⌋₊ + 1))
      (pbZ (M1 * (c * n1) * L ^ (k + 1))
          ((fineK M1 c n1 L k n0 st.Z : Finset _) :
            Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))) ∩
        pbZ (M1 * (c * n1) * L ^ (k + 1))
          ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
            Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))) Mℛ)
    (hAO : AgrB w (12 * (L ^ (k + 1) * M1) + (L ^ (k + 1) * (c * M1)) * (⌊Rk⌋₊ + 1))
      (pbZ (M1 * (c * n1) * L ^ (k + 1))
          ((fineK1 M1 c n1 L k st.Omega : Finset _) :
            Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))) ∩
        pbZ (M1 * (c * n1) * L ^ (k + 1))
          ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
            Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))) MℛΩ) (n : ℕ) :
    w ∈ pbZ (M1 * (c * n1) * L ^ (k + 1))
        ((((genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ').Ω n : Finset _)) :
          Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))) ↔
      w ∈ bdLayZ L M1 k
        (dilZ (L ^ k * (c * M1)) (⌊Rprev⌋₊ + 1) (dilZ (L ^ k * (c * M1)) (⌊Rprev⌋₊ + 1) Mℛᶜ) ∩
          dilZ (L ^ (k + 1) * (c * M1)) (⌊Rk⌋₊ + 1) M𝒵)
        (dilZ (L ^ (k + 1) * (c * M1)) (⌊Rk⌋₊ + 1) M𝒵) (M𝒵ᶜ ∪ MℛΩ) n := by
  rw [pbZ_genBoundaryLocal_Ω]
  have hL0 : 0 < L := by omega
  refine mem_bdLayZ_iff_model hL (Nat.pos_of_ne_zero (NeZero.ne M1)) P0_pos P1_eq
    (twelve_le_P1 hc) hmono cubeConst_zZ ?_ ?_ hAZ hAR hAO n
  · intro z hz hk
    exact mem_of_mem_Zk_near st hL0 hn hZ hZ' (D := ⌊Rk⌋₊ + 1 + (⌊Rprev⌋₊ + 1)) (by omega) hz hk
  · intro z hz hnot
    exact mem_Omega_of_not_mem_near st hZ hZ' (D := ⌊Rk⌋₊ + 2) (by omega) hz hnot

theorem nbhd_add_subset {n : ℕ} [NeZero n] (X : Set (Torus d n)) (a b : ℕ) :
    nbhd (b + a) X ⊆ nbhd b (nbhd a X) := by
  intro y hy
  obtain ⟨x, hxX, hx⟩ := mem_nbhd.1 hy
  obtain ⟨y', h1, h2⟩ := exists_split (x := y) (z := x) (a := b) (b := a) hx
  exact mem_nbhd.2 ⟨y', mem_nbhd.2 ⟨x, hxX, h2⟩, h1⟩

/-- **The region `Ω₁` of the local boundary family lies in the box with margin `2`.** -/
theorem supp_own (st : RegionStep d L n0 n1 Rprev Rk) (hc : 14 ≤ c) (hn : n0 = L * n1)
    (hL : 2 ≤ L) (hρ : 3 * L ≤ ⌊Rprev⌋₊)
    (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω) (hZ : st.Omegaᶜ ⊆ Zp) (hZ' : Z' ∈ comps ω (finOf Zp))
    {m' : ℕ} [NeZero m'] {cc : Fin d → ℤ}
    (hZn : ∀ x ∈ (fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _),
      InBox (M1 * (c * n1) * L ^ (k + 1)) m' cc (liftNear cc x))
    (hV : ∀ x ∈ (fineK1 M1 c n1 L k (nbhd 1 (thick ⌊Rk⌋₊ (Z' : Set (Torus d n1)))) : Finset _),
      InBox (M1 * (c * n1) * L ^ (k + 1)) m' cc (liftNear cc x))
    (hsize : 4 * (12 * (L ^ (k + 1) * M1) + (L ^ (k + 1) * (c * M1)) * (⌊Rk⌋₊ + 1)) + 8 ≤
      M1 * (c * n1) * L ^ (k + 1))
    {x : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hx : x ∈ (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ').Ω 1) :
    InBoxK 2 (M1 * (c * n1) * L ^ (k + 1)) m' cc (liftNear cc x) := by
  set P1 := L ^ (k + 1) * (c * M1) with hP1
  set B := 12 * (L ^ (k + 1) * M1) with hB
  set R := B + P1 * (⌊Rk⌋₊ + 1) with hR
  have hBP : B + 2 ≤ P1 := twelve_le_P1 hc
  have hP1pos : 0 < P1 := P1_pos
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Fin d → ℤ, w₀ = liftNear cc x := ⟨_, rfl⟩
  have hxw : zcast (M1 * (c * n1) * L ^ (k + 1)) w₀ = x := by rw [hw₀]; exact zcast_liftNear x
  have hmem : w₀ ∈ pbZ (M1 * (c * n1) * L ^ (k + 1))
      (((genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ').Ω 1 : Finset _) :
        Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))) := by
    rw [mem_pbZ, hxw]; exact Finset.mem_coe.2 hx
  rw [pbZ_genBoundaryLocal_Ω] at hmem
  have hL0 : 0 < L := by omega
  obtain ⟨z, hzU, hzd⟩ := bdLayZ_supp L M1 k hL (Nat.pos_of_ne_zero (NeZero.ne M1))
    (Set.inter_subset_right) 1 hmem
  obtain ⟨z'', hz''Z, hz''d⟩ := near_of_supp (L := L) (M1 := M1) (k := k) hzU hzd
  -- the point `z''` lies in the box
  have hz''mem : zcast (M1 * (c * n1) * L ^ (k + 1)) z'' ∈ (fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Set _) := hz''Z
  obtain ⟨z₀, hz₀def⟩ : ∃ z₀ : Fin d → ℤ, z₀ = liftNear cc (zcast (M1 * (c * n1) * L ^ (k + 1)) z'') := ⟨_, rfl⟩
  have hz₀ := hZn _ hz''mem
  rw [← hz₀def] at hz₀
  have hzz : zcast (M1 * (c * n1) * L ^ (k + 1)) z₀ = zcast (M1 * (c * n1) * L ^ (k + 1)) z'' := by
    rw [hz₀def]; exact zcast_liftNear _
  have hRm : 4 * (R : ℤ) + 8 ≤ ((M1 * (c * n1) * L ^ (k + 1) : ℕ) : ℤ) := by exact_mod_cast hsize
  have hRz : (R : ℤ) + 2 ≤ (P1 : ℤ) * ((⌊Rk⌋₊ + 2 : ℕ) : ℤ) := by
    have hBP' : (B : ℤ) + 2 ≤ P1 := by exact_mod_cast hBP
    have : (R : ℤ) = B + P1 * ((⌊Rk⌋₊ + 1 : ℕ) : ℤ) := by rw [hR]; push_cast; ring
    rw [this]; push_cast; nlinarith
  have hz''eq : z₀ = z'' := by
    refine (zcast_eq_iff_of_abs_lt (n := M1 * (c * n1) * L ^ (k + 1)) (a := z₀) (b := z'') (fun μ => ?_)).1 hzz
    have h1 := (hz₀ μ).1
    have h2 := liftNear_abs_le cc x μ
    rw [← hw₀] at h2
    have h3 : |z'' μ - w₀ μ| ≤ (R : ℤ) := hz''d μ
    have t1 := abs_sub_le (z₀ μ) (cc μ) (z'' μ)
    have t2 := abs_sub_le (cc μ) (w₀ μ) (z'' μ)
    have e1 : |cc μ - w₀ μ| = |w₀ μ - cc μ| := abs_sub_comm _ _
    have e2 : |w₀ μ - z'' μ| = |z'' μ - w₀ μ| := abs_sub_comm _ _
    linarith
  rw [hz''eq] at hz₀
  -- every perturbation of `w₀` by at most `2` lies in the box
  have hper : ∀ δ : Fin d → ℤ, (∀ ν, |δ ν| ≤ 2) → InBox (M1 * (c * n1) * L ^ (k + 1)) m' cc (w₀ + δ) := by
    intro δ hδ
    have hwide : ∀ ν, 2 * |(w₀ + δ) ν - cc ν| < ((M1 * (c * n1) * L ^ (k + 1) : ℕ) : ℤ) := by
      intro ν
      have h1 := (hz₀ ν).1
      have h3 : |z'' ν - w₀ ν| ≤ (R : ℤ) := hz''d ν
      have h2 := hδ ν
      have t1 := abs_sub_le ((w₀ + δ) ν) (z'' ν) (cc ν)
      have t2 := abs_sub_le ((w₀ + δ) ν) (w₀ ν) (z'' ν)
      have e2 : |w₀ ν - z'' ν| = |z'' ν - w₀ ν| := abs_sub_comm _ _
      have e3 : |(w₀ + δ) ν - w₀ ν| = |δ ν| := by simp
      linarith
    have hwide' : ∀ ν, 2 * |(w₀ + δ) ν - cc ν| < ((M1 * (c * n1) * L ^ (k + 1) : ℕ) : ℤ) := hwide
    -- the point lies in `V`
    have hlift : liftNear cc (zcast (M1 * (c * n1) * L ^ (k + 1)) (w₀ + δ)) = w₀ + δ :=
      liftNear_zcast (fun ν => hwide' ν)
    have hP1ne : (P1 : ℤ) ≠ 0 := by exact_mod_cast hP1pos.ne'
    have hz''Z' : zcast n1 (fun μ => z'' μ / (P1 : ℤ)) ∈ (Z' : Set (Torus d n1)) := by
      have := hz''mem
      rw [Finset.mem_coe, mem_fineK1, blockMap_zcast fine_eq_P1 P1_pos] at this
      exact this
    have hVmem : zcast (M1 * (c * n1) * L ^ (k + 1)) (w₀ + δ) ∈
        (fineK1 M1 c n1 L k (nbhd 1 (thick ⌊Rk⌋₊ (Z' : Set (Torus d n1)))) : Set _) := by
      rw [Finset.mem_coe, mem_fineK1, blockMap_zcast fine_eq_P1 P1_pos]
      have hnb : zcast n1 (fun μ => (w₀ + δ) μ / (P1 : ℤ)) ∈
          nbhd (⌊Rk⌋₊ + 2) (Z' : Set (Torus d n1)) := by
        rw [mem_nbhd_zcast]
        refine ⟨fun μ => z'' μ / (P1 : ℤ) - (w₀ + δ) μ / (P1 : ℤ), fun μ => ?_, ?_⟩
        · have h3 : |z'' μ - w₀ μ| ≤ (R : ℤ) := hz''d μ
          have h2 := hδ μ
          have t1 := abs_sub_le (z'' μ) (w₀ μ) ((w₀ + δ) μ)
          have e3 : |w₀ μ - (w₀ + δ) μ| = |δ μ| := by simp
          have h4 : |z'' μ - (w₀ + δ) μ| ≤ (P1 : ℤ) * ((⌊Rk⌋₊ + 2 : ℕ) : ℤ) := by
            linarith
          exact_mod_cast abs_ediv_sub_le_of_abs_le hP1pos h4
        · have : ((fun μ => (w₀ + δ) μ / (P1 : ℤ)) +
              fun μ => z'' μ / (P1 : ℤ) - (w₀ + δ) μ / (P1 : ℤ)) = fun μ => z'' μ / (P1 : ℤ) := by
            funext μ; simp
          rw [this]; exact hz''Z'
      have hsub := nbhd_add_subset (Z' : Set (Torus d n1)) (⌊Rk⌋₊ + 1) 1
      have e : 1 + (⌊Rk⌋₊ + 1) = ⌊Rk⌋₊ + 2 := by omega
      rw [e] at hsub
      exact hsub hnb
    have := hV _ hVmem
    rw [hlift] at this
    exact this
  rw [← hw₀]
  intro μ
  set σ : ℤ := if cc μ ≤ w₀ μ then 1 else -1 with hσ
  have hδ : ∀ ν, |(Pi.single μ (2 * σ) : Fin d → ℤ) ν| ≤ 2 := by
    intro ν
    by_cases hν : ν = μ
    · subst hν
      rw [Pi.single_eq_same, hσ]
      split_ifs <;> simp
    · rw [Pi.single_eq_of_ne hν]; simp
  have hb := hper _ hδ μ
  simp only [Pi.add_apply, Pi.single_eq_same] at hb
  have habs : |w₀ μ + 2 * σ - cc μ| = |w₀ μ - cc μ| + 2 := by
    rw [hσ]
    split_ifs with h
    · rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; ring
    · rw [abs_of_neg (by omega), abs_of_neg (by omega)]; ring
  rw [habs] at hb
  have h2 : ((2 : ℕ) : ℤ) = 2 := by norm_num
  rw [h2]
  exact hb

end Own

section Final

variable {d M1 c L k ω n1₁ n0₁ n1₂ n0₂ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0₁]
  [NeZero n1₁] [NeZero n0₂] [NeZero n1₂] {Rprev Rk : ℝ} {Zp₁ : Set (Torus d n1₁)}
  {Zp₂ : Set (Torus d n1₂)} {Z'₁ : Finset (Torus d n1₁)} {Z'₂ : Finset (Torus d n1₂)}

/-- **The local boundary generating sets of two tori agree on a box.** -/
theorem genAgree_genBoundaryLocal (st₁ : RegionStep d L n0₁ n1₁ Rprev Rk)
    (st₂ : RegionStep d L n0₂ n1₂ Rprev Rk) (hc : 14 ≤ c) (hn₁ : n0₁ = L * n1₁)
    (hn₂ : n0₂ = L * n1₂) (hL : 2 ≤ L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hmono : ⌊Rprev⌋₊ ≤ ⌊Rk⌋₊)
    (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω) (hZ₁ : st₁.Omegaᶜ ⊆ Zp₁) (hZ₂ : st₂.Omegaᶜ ⊆ Zp₂)
    (hZ'₁ : Z'₁ ∈ comps ω (finOf Zp₁)) (hZ'₂ : Z'₂ ∈ comps ω (finOf Zp₂)) (cc : Fin d → ℤ)
    (hZc : SetCorr cc
      ((fineK1 M1 c n1₁ L k (Z'₁ : Set (Torus d n1₁)) : Finset _) :
        Set (Torus d (M1 * (c * n1₁) * L ^ (k + 1))))
      ((fineK1 M1 c n1₂ L k (Z'₂ : Set (Torus d n1₂)) : Finset _) :
        Set (Torus d (M1 * (c * n1₂) * L ^ (k + 1)))))
    (hKc : SetCorr cc
      (((fineK M1 c n1₁ L k n0₁ st₁.Z : Finset _) : Set (Torus d (M1 * (c * n1₁) * L ^ (k + 1)))) ∩
        ((fineK1 M1 c n1₁ L k (Z'₁ : Set (Torus d n1₁)) : Finset _) :
          Set (Torus d (M1 * (c * n1₁) * L ^ (k + 1)))))
      (((fineK M1 c n1₂ L k n0₂ st₂.Z : Finset _) : Set (Torus d (M1 * (c * n1₂) * L ^ (k + 1)))) ∩
        ((fineK1 M1 c n1₂ L k (Z'₂ : Set (Torus d n1₂)) : Finset _) :
          Set (Torus d (M1 * (c * n1₂) * L ^ (k + 1))))))
    (hOc : SetCorr cc
      (((fineK1 M1 c n1₁ L k st₁.Omega : Finset _) : Set (Torus d (M1 * (c * n1₁) * L ^ (k + 1)))) ∩
        ((fineK1 M1 c n1₁ L k (Z'₁ : Set (Torus d n1₁)) : Finset _) :
          Set (Torus d (M1 * (c * n1₁) * L ^ (k + 1)))))
      (((fineK1 M1 c n1₂ L k st₂.Omega : Finset _) : Set (Torus d (M1 * (c * n1₂) * L ^ (k + 1)))) ∩
        ((fineK1 M1 c n1₂ L k (Z'₂ : Set (Torus d n1₂)) : Finset _) :
          Set (Torus d (M1 * (c * n1₂) * L ^ (k + 1))))))
    (hV₁ : ∀ x ∈ (fineK1 M1 c n1₁ L k (nbhd 1 (thick ⌊Rk⌋₊ (Z'₁ : Set (Torus d n1₁)))) : Finset _),
      InBox (M1 * (c * n1₁) * L ^ (k + 1)) (M1 * (c * n1₂) * L ^ (k + 1)) cc (liftNear cc x))
    (hV₂ : ∀ x ∈ (fineK1 M1 c n1₂ L k (nbhd 1 (thick ⌊Rk⌋₊ (Z'₂ : Set (Torus d n1₂)))) : Finset _),
      InBox (M1 * (c * n1₁) * L ^ (k + 1)) (M1 * (c * n1₂) * L ^ (k + 1)) cc (liftNear cc x))
    (hsize₁ : 4 * (12 * (L ^ (k + 1) * M1) + (L ^ (k + 1) * (c * M1)) * (⌊Rk⌋₊ + 1)) + 8 ≤
      M1 * (c * n1₁) * L ^ (k + 1))
    (hsize₂ : 4 * (12 * (L ^ (k + 1) * M1) + (L ^ (k + 1) * (c * M1)) * (⌊Rk⌋₊ + 1)) + 8 ≤
      M1 * (c * n1₂) * L ^ (k + 1)) :
    GenAgree (genBoundaryLocal M1 c n1₁ L k st₁ hc hn₁ hL hρ hω hZ₁ hZ'₁)
      (genBoundaryLocal M1 c n1₂ L k st₂ hc hn₂ hL hρ hω hZ₂ hZ'₂) cc where
  supp₁ x hx := supp_own st₁ hc hn₁ hL hρ hω hZ₁ hZ'₁ (m' := M1 * (c * n1₂) * L ^ (k + 1))
    (fun y hy => hZc.1 y hy) hV₁ hsize₁ hx
  supp₂ x hx := (supp_own st₂ hc hn₂ hL hρ hω hZ₂ hZ'₂ (m' := M1 * (c * n1₁) * L ^ (k + 1))
    (fun y hy => (hZc.2.1 y hy).symm) (fun y hy => (hV₂ y hy).symm) hsize₂ hx).symm
  agree n _ _ w hw := by
    set R := 12 * (L ^ (k + 1) * M1) + (L ^ (k + 1) * (c * M1)) * (⌊Rk⌋₊ + 1) with hR
    have h1 : 2 * (R : ℤ) ≤ ((M1 * (c * n1₁) * L ^ (k + 1) : ℕ) : ℤ) := by
      have : 4 * R + 8 ≤ M1 * (c * n1₁) * L ^ (k + 1) := hsize₁
      omega
    have h2 : 2 * (R : ℤ) ≤ ((M1 * (c * n1₂) * L ^ (k + 1) : ℕ) : ℤ) := by
      have : 4 * R + 8 ≤ M1 * (c * n1₂) * L ^ (k + 1) := hsize₂
      omega
    have e1 := mem_Ω_iff_model st₁ hc hn₁ hL hρ hmono hω hZ₁ hZ'₁ (w := w) (n := n)
      (agrB_narrow₁ hZc hw h1) (agrB_narrow₁ hKc hw h1) (agrB_narrow₁ hOc hw h1)
    have e2 := mem_Ω_iff_model st₂ hc hn₂ hL hρ hmono hω hZ₂ hZ'₂ (w := w) (n := n)
      (agrB_narrow₂ hZc hw h2) (agrB_narrow₂ hKc hw h2) (agrB_narrow₂ hOc hw h2)
    have := e1.trans e2.symm
    simpa [mem_pbZ] using this

end Final

end Balaban.RootFSpine
