/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilySetMargin
public import Balaban.Fluctuation.LocalClassDensityFamilySetPrec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The per-label settings with local generating sets on a finer cube torus
(`LocalClassDensityFamilySetCast`)

The local generating set `localB` of a set on the step torus `CTorus d L N₁ m₁ k` has an index
`ϱ ≤ minSep L L^{m₁} = 5 L^{m₁+1}`, while the class index of the tower is `rhoSep m₁ ≈ 369 · 3^{m₁}`.
A local set of the required index is the set `𝔹_j(X)` read on a torus with the same number of sites
and cubes of side `L^{m₁'} L^n` (`N₁' L^{m₁'} = N₁ L^{m₁}`, `m₁' ≥ m₁`), transported by `castG`.

* `precedes_castG`, `collar_castG_subset`, `adj_torusCast`: transport of `≺` and of the collar;
* `bgSetting_of_data`: `BgSetting` for the ambient set `Gk` and the term generator `Gj` from a base
  setting of the step (fields independent of `Gk`, `Gj`, `X₀`, `X₁f`), `Gj ≺ Gk`, the collar of `Gj`
  in `Ω₁(Gk)` and the margin;
* `margin_arith_gen`: the arithmetic of the margin;
* `bgFlSetting_castLocalB`: `BgSetting` and `FlSetting` for `Gk = 𝔹_k(Z)`, `Gj = 𝔹_j(X)` on the
  finer cube torus, under a condition on the block index `m₀`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.GsSpec Balaban.LargeField Finset

section Transport

variable {d L : ℕ} [NeZero L] {ϱ ϱ' : ℝ} {K : ℕ}

theorem adj_torusCast {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀')
    {x y : Torus d (N₀ * L ^ K)} (hxy : Adj x y) :
    Adj (torusCast x : Torus d (N₀' * L ^ K)) (torusCast y) := by
  subst h
  have e : ∀ z : Torus d (N₀ * L ^ K), (torusCast z : Torus d (N₀ * L ^ K)) = z := fun z => by
    funext μ; simp [torusCast]
  rw [e, e]
  exact hxy

/-- Transport of `≺` along `castG`. -/
theorem precedes_castG {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀' = N₀)
    {G : GeneratingSet d L N₀' K ϱ} {G' : GeneratingSet d L N₀' K ϱ'} (hP : Precedes G G') :
    Precedes (castG h G) (castG h G') := by
  intro i hi1 hiK x hx
  rw [mem_castG_Ω] at hx ⊢
  exact hP i hi1 hiK hx

/-- Transport of the collar inclusion along `castG`. -/
theorem collar_castG_subset {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀' = N₀)
    {G : GeneratingSet d L N₀' K ϱ} {G' : GeneratingSet d L N₀' K ϱ'}
    (hc : ∀ z ∈ collar G, z ∈ G'.Ω 1) : ∀ z ∈ collar (castG h G), z ∈ (castG h G').Ω 1 := by
  intro z hz
  obtain ⟨hz1, x0, hx0, hadj⟩ := (mem_collar _).1 hz
  rw [mem_castG_Ω] at hz1 hx0
  rw [mem_castG_Ω]
  refine hc _ ((mem_collar _).2 ⟨hz1, _, hx0, ?_⟩)
  exact adj_torusCast h.symm hadj

end Transport

section Settings

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ ϱ₀ ϱ₃ ϱm : ℝ}

/-- **`BgSetting` for given sets `Gk`, `Gj`.**  From a base `BgSetting` of the step (any ambient and
term generators; its fields that do not mention `Gk`, `Gj`, `X₀`, `X₁f` are used), the indices
`bgR0 ≤ ϱ₁, ϱ₂`, `Gj ≺ Gk`, the collar of `Gj` in `Ω₁(Gk)` and the margin of the data sites of `Gk`
against `X₁f`, the setting holds with `X₀ = dataSites Gk`. -/
theorem bgSetting_of_data {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {Gk0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₀}
    {Gj0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₃}
    {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀' X₁f' : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB0 : BgSetting N Gp Gk0 Gj0 a₁ ν c BG κ r₀ eps δ₃ X₀' X₁f' j₁)
    (hG' : IsLevel Gp (k + 1))
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
    (hϱ₁ : bgR0 d L ≤ ϱ₁) (hϱ₂ : bgR0 d L ≤ ϱ₂) (hq : Precedes Gj Gk)
    (hcol : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1) {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
    (hj : j ≤ k + 1)
    (hmar : ∀ x ∈ dataSites Gk, ∀ y : CTorus d L N₁ m₁ (k + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) → y ∈ X₁f) :
    BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ (dataSites Gk) X₁f j where
  hS := hB0.hS
  Sp := hB0.Sp
  ha₁ := hB0.ha₁
  HBp := hB0.HBp
  HBk := { hB0.HBp with hϱ := hϱ₁ }
  HBj := { hB0.HBp with hϱ := hϱ₂ }
  hP := precedes_of_isLevel_top hG'
  hq := hq
  colk := fun z _ => by rw [hG'.Ω_one]; exact Finset.mem_univ z
  colj := hcol
  hκ := hB0.hκ
  hM := hB0.hM
  num := hB0.num
  dsX₀ := fun _ hx => hx
  hN := fun x hx _ y hy => hmar x hx y (by rwa [hG'.spacing_eq] at hy)
  hr := hB0.hr
  hr₀ := hB0.hr₀
  dep := fun x hx y hy => hmar x hx y
    (torusDist_lt_of_mem_composeDep (by have := hB0.HBp.hd; omega) hB0.hr₀ hy)
  hj := hj

omit [NeZero L] [NeZero N₁] in
/-- **The arithmetic of the margin.**  If `ℓ₀ + D ≤ L^{m₁+k} e` and `e + r₀ L ≤ (L - 2) L^{m₀+1}`
then `ℓ₀ + D + r₀ L^{m₁} L^{k+1} ≤ (L - 2) a_{k+1}`. -/
theorem margin_arith_gen {m₀ : ℕ} {ℓ₀ D e : ℕ} {r₀ : ℝ} (hL : 2 ≤ L)
    (hℓ : ℓ₀ + D ≤ L ^ (m₁ + k) * e)
    (hm : (e : ℝ) + r₀ * L ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1)) :
    (ℓ₀ : ℝ) + D + r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) ≤
      (((L - 2) * cellSide L m₀ m₁ (k + 1) : ℕ) : ℝ) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hℓ' : (ℓ₀ : ℝ) + D ≤ (L : ℝ) ^ (m₁ + k) * e := by exact_mod_cast hℓ
  have hpk : (L : ℝ) ^ (m₁ + k) = (L : ℝ) ^ m₁ * (L : ℝ) ^ k := pow_add _ _ _
  have hcs : (((L - 2) * cellSide L m₀ m₁ (k + 1) : ℕ) : ℝ) =
      (((L - 2 : ℕ)) : ℝ) * ((L : ℝ) ^ (m₁ + k) * (L : ℝ) ^ (m₀ + 1)) := by
    unfold cellSide
    push_cast
    rw [← pow_add]
    congr 2
    ring
  have hpos : (0 : ℝ) < (L : ℝ) ^ (m₁ + k) := by positivity
  have h1 : (L : ℝ) ^ (m₁ + k) * ((e : ℝ) + r₀ * L) ≤
      (L : ℝ) ^ (m₁ + k) * ((((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1)) :=
    mul_le_mul_of_nonneg_left hm hpos.le
  have h3 : (L : ℝ) ^ (k + 1) = (L : ℝ) ^ k * L := pow_succ _ _
  have e1 : r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) = (L : ℝ) ^ (m₁ + k) * (r₀ * L) := by
    rw [hpk, h3]; ring
  rw [hcs, e1]
  nlinarith

end Settings

section Bundle

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ ϱ₀ ϱ₃ ϱm : ℝ}

/-- **`BgSetting` and `FlSetting` for `Gk = 𝔹_k(Z)` and `Gj = 𝔹_j(X)` on the finer cube torus.**
Let `N₁' L^{m₁'} = N₁ L^{m₁}` (`m₁' ≥ m₁` with `L^{m₁'} ≤ L^{m₁} c₁`), `X'` the set `X` and `Z'`
the set of sites at `𝒞_k`-cube-index distance `≤ 5 L` from `X'`, both read on the torus of
`(N₁', m₁')`.  Let `Gk = castG (𝔹_k(Z'))`, `Gj = castG (𝔹_j(X'))` (indices `ϱ₁`, `ϱ₂` below
`5 L^{m₁'+1}` and above `bgR0`).  For a covering setup `(X, 𝒦_X)` of index `m₀` and `j ≤ k`,
`X₁f = X1 Gp m₀ j 𝒦_X` and
`(5 L + 13) c₁ + r₀ L ≤ (L - 2) L^{m₀+1}`, `BgSetting` holds with `X₀ = dataSites Gk` and `FlSetting`
holds, from base settings of the step. -/
theorem bgFlSetting_castLocalB {N₁' m₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG' : IsLevel Gp (k + 1))
    {Gk0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₀}
    {Gj0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₃}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    {X₀' X₁f' X₁f'' : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB0 : BgSetting N Gp Gk0 Gj0 a₁ ν c BG κ r₀ eps δ₃ X₀' X₁f' j₁)
    (hF0 : FlSetting N Gp Gk0 Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f'')
    (hG : IsLevel Hm k) (hL : 2 ≤ L) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {m₀ : ℕ}
    {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} (hcov : CovSetup Gp m₀ j X 𝒦X)
    {X' Z' : Set (CTorus d L N₁' m₁' (k + 1))}
    (hX' : ∀ x' : CTorus d L N₁' m₁' (k + 1),
      x' ∈ X' ↔ (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ X)
    (hZ' : ∀ z' : CTorus d L N₁' m₁' (k + 1), z' ∈ Z' ↔ ∃ y' ∈ X',
      supDist (fineCubeIdx (L ^ m₁') N₁' L (k + 1) k
          (torusCast z' : Torus d (L ^ m₁' * N₁' * L ^ (k + 1))))
        (fineCubeIdx (L ^ m₁') N₁' L (k + 1) k
          (torusCast y' : Torus d (L ^ m₁' * N₁' * L ^ (k + 1)))) ≤ 5 * L)
    (hϱ₁ : bgR0 d L ≤ ϱ₁) (hϱ₂ : bgR0 d L ≤ ϱ₂) (hs₁ : ϱ₁ ≤ minSep L (L ^ m₁'))
    (hs₂ : ϱ₂ ≤ minSep L (L ^ m₁')) {c₁ : ℕ} (hm1 : L ^ m₁' ≤ L ^ m₁ * c₁)
    (hm : (((5 * L + 13) * c₁ : ℕ) : ℝ) + r₀ * L ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1))
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X) :
    BgSetting N Gp (castG hc (localB k (Nat.le_succ k) Z' hs₁))
        (castG hc (localB j (by omega) X' hs₂)) a₁ ν c BG κ r₀ eps δ₃
        (dataSites (castG hc (localB k (Nat.le_succ k) Z' hs₁))) X₁f j ∧
      FlSetting N Gp (castG hc (localB k (Nat.le_succ k) Z' hs₁)) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂
        BG₂ δ₁ δfl X₁f := by
  have hceq : N₁' * L ^ m₁' * L ^ (k + 1) = N₁ * L ^ m₁ * L ^ (k + 1) := by rw [hc]
  have hZtop := Zset_hZ (d := d) (L := L) (N₁ := N₁') (m₁ := m₁') (k := k + 1) (ϱ₂ := ϱ₁)
    (Nat.le_succ k) hZ' (h₂ := hs₁)
  have hq' := localB_precedes_localB hL hjk (Nat.le_succ k) (by omega : j ≤ k + 1) hZtop
    (h₁ := hs₂)
  have hcol' := localB_collar_subset hL hj1 hjk (Nat.le_succ k) (by omega : j ≤ k + 1) hZtop
    (h₁ := hs₂)
  have hmar : ∀ x ∈ dataSites (castG hc (localB k (Nat.le_succ k) Z' hs₁)),
      ∀ y : CTorus d L N₁ m₁ (k + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) → y ∈ X₁f := by
    intro x hx y hy
    obtain ⟨y', hy'Z, hxy'⟩ := dataSites_castG_range hc (localB k (Nat.le_succ k) Z' hs₁) Z'
      (11 * L ^ m₁' * L ^ k + 1) (fun x hx => localB_dataSites_range hL hx) hx
    obtain ⟨w', hw'X, hz'w'⟩ := Zset_dist_le (Nat.le_succ k) hZ' y' hy'Z
    have hw := (hX' w').1 hw'X
    have hsd : supDist (torusCast y' : CTorus d L N₁ m₁ (k + 1)) (torusCast w') ≤
        (5 * L + 1) * (L ^ m₁' * L ^ k) := by
      rw [supDist_torusCast_val hceq]; exact hz'w'
    have hpos : 1 ≤ L ^ m₁' * L ^ k :=
      Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
        (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
    have hnat : (5 * L + 1) * (L ^ m₁' * L ^ k) + (11 * L ^ m₁' * L ^ k + 1) ≤
        L ^ (m₁ + k) * ((5 * L + 13) * c₁) := by
      have h1 : (5 * L + 13) * (L ^ m₁' * L ^ k) ≤ (5 * L + 13) * ((L ^ m₁ * c₁) * L ^ k) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm1)
      have h2 : (5 * L + 1) * (L ^ m₁' * L ^ k) + (11 * L ^ m₁' * L ^ k + 1) ≤
          (5 * L + 13) * (L ^ m₁' * L ^ k) := by
        have : (5 * L + 13) * (L ^ m₁' * L ^ k) =
            (5 * L + 1) * (L ^ m₁' * L ^ k) + 12 * (L ^ m₁' * L ^ k) := by ring
        rw [this, show 11 * L ^ m₁' * L ^ k = 11 * (L ^ m₁' * L ^ k) by ring]
        omega
      calc _ ≤ _ := h2
        _ ≤ _ := h1
        _ = _ := by rw [pow_add]; ring
    have hr := margin_arith_gen (L := L) (m₁ := m₁) (k := k) (m₀ := m₀) hL hnat hm
    have hy1 := mem_X1_of_chain hG' hL hcov hxy' hsd hw hy hr
    rw [← Finset.mem_coe, hX₁]
    exact hy1
  have hB := bgSetting_of_data hB0 hG' hϱ₁ hϱ₂ (precedes_castG hc hq')
    (collar_castG_subset hc hcol') (by omega : j ≤ k + 1) hmar
  refine ⟨hB, flSetting_localGk hB hF0 hG' hG ?_⟩
  ext x
  simp only [Finset.notMem_empty, iff_false]
  rw [mem_castG_Ω, localB_Ω_of_gt (Nat.lt_succ_self k)]
  exact Finset.notMem_empty _

end Bundle

end Balaban.Fluctuation
