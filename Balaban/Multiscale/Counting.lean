/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PathMetricBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Counting in the multiscale metric (GREEN.md Lemma 4.4)

Geometric ingredients: the polynomial bound `#{z : dist(x,z) ≤ R} ≤ (2R+1)^d` on the `ℓ¹` torus
(`Balaban.Multiscale.card_ball_le`) and the comparison `dist_{ℓ¹}(x,z) ≤ c L^M` for a path of cost
`c` whose points all lie in layers `≤ M` (`Balaban.Multiscale.torusDist_le_of_pathCost`).
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Balaban

section Ball

variable {m : ℕ} [NeZero m]

theorem card_cyc_ball_le (x : ZMod m) (R : ℕ) :
    (Finset.univ.filter fun a : ZMod m => (Green.cycRep (x - a)).natAbs ≤ R).card ≤ 2 * R + 1 := by
  classical
  have hinj : Set.InjOn (fun a : ZMod m => Green.cycRep (x - a))
      ↑(Finset.univ.filter fun a : ZMod m => (Green.cycRep (x - a)).natAbs ≤ R) := by
    intro a _ b _ h
    have := Green.cycRep_injective h
    simpa using this
  have hsub : (Finset.univ.filter fun a : ZMod m => (Green.cycRep (x - a)).natAbs ≤ R).image
      (fun a : ZMod m => Green.cycRep (x - a)) ⊆ Finset.Icc (-(R : ℤ)) R := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hz
    have := (Finset.mem_filter.1 ha).2
    rw [Finset.mem_Icc]
    omega
  calc _ = ((Finset.univ.filter fun a : ZMod m => (Green.cycRep (x - a)).natAbs ≤ R).image
        (fun a : ZMod m => Green.cycRep (x - a))).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc (-(R : ℤ)) R).card := Finset.card_le_card hsub
    _ = 2 * R + 1 := by simp; omega

variable {d : ℕ}

/-- The `ℓ¹` ball of radius `R` on the torus has at most `(2R+1)^d` points. -/
theorem card_ball_le (x : Torus d m) (R : ℕ) :
    (Finset.univ.filter fun z : Torus d m => Green.torusDist d m x z ≤ R).card ≤ (2 * R + 1) ^ d := by
  classical
  have hsub : (Finset.univ.filter fun z : Torus d m => Green.torusDist d m x z ≤ R) ⊆
      Fintype.piFinset fun i : Fin d =>
        Finset.univ.filter fun a : ZMod m => (Green.cycRep (x i - a)).natAbs ≤ R := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : ((Green.cycRep (x i - z i)).natAbs : ℝ) ≤ Green.torusDist d m x z :=
      Finset.single_le_sum (f := fun i => ((Green.cycRep (x i - z i)).natAbs : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ i)
    exact_mod_cast h1.trans hz.2
  calc _ ≤ (Fintype.piFinset fun i : Fin d =>
        Finset.univ.filter fun a : ZMod m => (Green.cycRep (x i - a)).natAbs ≤ R).card :=
      Finset.card_le_card hsub
    _ = ∏ i : Fin d, (Finset.univ.filter fun a : ZMod m => (Green.cycRep (x i - a)).natAbs ≤ R).card :=
      Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, (2 * R + 1) := Finset.prod_le_prod fun i _ => card_cyc_ball_le _ R
    _ = _ := by simp

end Ball

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section PathBound

variable (G : GeneratingSet d L N₀ k ϱ)

/-- A path of cost `c` all of whose points lie within `pathDist`-distance `T` of `y₀` (and hence in
layers `≤ M`) has `ℓ¹` length `≤ c L^M`. -/
theorem torusDist_le_of_pathCost {y₀ : Torus d (N₀ * L ^ k)} {T : ℝ} {M : ℕ}
    (hM : ∀ w ∈ G.Ω 1, G.pathDist y₀ w ≤ ENNReal.ofReal T → G.layerIndex w ≤ M)
    {x z : Torus d (N₀ * L ^ k)} {c : ℝ} (h : G.PathCost x z c) :
    ∀ {p : ℝ}, 0 ≤ p → G.pathDist y₀ x ≤ ENNReal.ofReal p → p + c ≤ T →
      Green.torusDist d (N₀ * L ^ k) x z ≤ c * (L : ℝ) ^ M := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  induction h with
  | refl x hx =>
      intro p _ _ _
      rw [torusDist_self']; simp
  | step x y z c hx hadj hp ih =>
      intro p hp0 hpx hpT
      have hbc0 := G.bondCost_nonneg x y
      have hc0 := hp.nonneg
      have hy1 : G.pathDist y₀ y ≤ ENNReal.ofReal (p + G.bondCost x y) := by
        calc G.pathDist y₀ y ≤ G.pathDist y₀ x + G.pathDist x y := G.pathDist_triangle _ _ _
          _ ≤ ENNReal.ofReal p + ENNReal.ofReal (G.bondCost x y) :=
              add_le_add hpx (G.pathDist_le_bondCost hx hp.left_mem hadj)
          _ = _ := (ENNReal.ofReal_add hp0 hbc0).symm
      have ihy := ih (p := p + G.bondCost x y) (by positivity) hy1 (by linarith)
      have hxM : G.layerIndex x ≤ M :=
        hM x hx (hpx.trans (ENNReal.ofReal_le_ofReal (by linarith)))
      have hyM : G.layerIndex y ≤ M :=
        hM y hp.left_mem (hy1.trans (ENNReal.ofReal_le_ofReal (by linarith)))
      have hmax : max (G.spacing x) (G.spacing y) ≤ (L : ℝ) ^ M := by
        refine max_le ?_ ?_
        · exact pow_le_pow_right₀ hL hxM
        · exact pow_le_pow_right₀ hL hyM
      have hone : 1 ≤ G.bondCost x y * (L : ℝ) ^ M := by
        unfold GeneratingSet.bondCost
        have hpos : 0 < max (G.spacing x) (G.spacing y) :=
          lt_of_lt_of_le one_pos ((G.spacing_ge_one x).trans (le_max_left _ _))
        rw [one_div, inv_mul_eq_div, le_div_iff₀ hpos]
        simpa using hmax
      calc Green.torusDist d (N₀ * L ^ k) x z
          ≤ Green.torusDist d (N₀ * L ^ k) x y + Green.torusDist d (N₀ * L ^ k) y z :=
            torusDist_triangle' x y z
        _ ≤ 1 + c * (L : ℝ) ^ M := add_le_add hadj.torusDist_le ihy
        _ ≤ G.bondCost x y * (L : ℝ) ^ M + c * (L : ℝ) ^ M := by linarith
        _ = _ := by ring

end PathBound

section Counting

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The layer of a point within distance `T` of `y` differs from that of `y` by at most
`1 + ⌊T / (ϱ - 1)⌋` (Lemma 4.3 (a)). -/
theorem layerIndex_close (hϱ : 1 < ϱ) {y x : Torus d (N₀ * L ^ k)} {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (hy : y ∈ G.layer j) (hx : x ∈ G.Ω 1) {T : ℝ} (hT : 0 ≤ T)
    (h : G.pathDist y x ≤ ENNReal.ofReal T) :
    G.layerIndex x ≤ j + 1 + ⌊T / (ϱ - 1)⌋₊ ∧ j ≤ G.layerIndex x + 1 + ⌊T / (ϱ - 1)⌋₊ := by
  obtain ⟨hj'1, hj'k, hxl⟩ := G.layerIndex_spec hx
  have hsep := G.pathDist_separation hϱ.le hj1 hj'1 hjk hj'k hy hxl
  have h1 := (ENNReal.ofReal_le_ofReal_iff hT).1 (hsep.trans h)
  have hr : 0 < ϱ - 1 := by linarith
  have h2 : ((j - G.layerIndex x + (G.layerIndex x - j) - 1 : ℕ) : ℝ) ≤ T / (ϱ - 1) := by
    rw [le_div_iff₀ hr]; linarith
  have h3 := Nat.le_floor h2
  omega

/-- The weight `ℓ(z)^{-d}` of a site, i.e. the inverse of the size of its block. -/
noncomputable def siteWeight (G : GeneratingSet d L N₀ k ϱ) (z : Torus d (N₀ * L ^ k)) : ℝ :=
  (((L : ℝ) ^ G.layerIndex z)⁻¹) ^ d

theorem siteWeight_nonneg (z : Torus d (N₀ * L ^ k)) : 0 ≤ siteWeight G z := by
  unfold siteWeight; positivity

end Counting

theorem pow_two_mul_pow_le {L : ℝ} (hL : 1 ≤ L) (d q : ℕ) {T r γ : ℝ} (hr : 0 < r)
    (hq : (q : ℝ) ≤ T / r) (hT : 0 ≤ T) (hcond : 2 * d * Real.log L ≤ γ / 2 * r) :
    (L ^ (2 * q)) ^ d ≤ Real.exp (γ / 2 * T) := by
  have hL0 : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have e : (L ^ (2 * q)) ^ d = Real.exp (((2 * q * d : ℕ) : ℝ) * Real.log L) := by
    rw [← pow_mul, Real.exp_nat_mul, Real.exp_log hL0]
  rw [e]
  apply Real.exp_le_exp.2
  push_cast
  have h1 : 2 * (q : ℝ) * d * Real.log L = (2 * d * Real.log L) * q := by ring
  rw [h1]
  have h2 : (2 * d * Real.log L) * q ≤ (2 * d * Real.log L) * (T / r) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have h3 : (2 * d * Real.log L) * (T / r) ≤ (γ / 2 * r) * (T / r) :=
    mul_le_mul_of_nonneg_right hcond (by positivity)
  have h4 : (γ / 2 * r) * (T / r) = γ / 2 * T := by field_simp
  linarith

section Shell

variable (G : GeneratingSet d L N₀ k ϱ)

/-- **Lemma 4.4, one shell.**  The `ℓ(z)^{-d}`-weighted number of sites `z ∈ Ω₁` with
`d(y,z) ≤ m + 1` is at most `(3(m+2))^d L^{2d} e^{(γ/2)(m+2)}`, provided
`2 d log L ≤ (γ/2) (ϱ - 1)`. -/
theorem shell_weight_le (hϱ : 1 < ϱ) {γ : ℝ}
    (hcond : 2 * d * Real.log L ≤ γ / 2 * (ϱ - 1)) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.Ω 1)
    (m : ℕ) :
    ∑ z ∈ Finset.univ.filter
        (fun z : G.Ω 1 => G.pathDist y z ≤ ENNReal.ofReal ((m : ℝ) + 1)),
      siteWeight G z ≤
      (3 * ((m : ℝ) + 2)) ^ d * (L : ℝ) ^ (2 * d) * Real.exp (γ / 2 * ((m : ℝ) + 2)) := by
  classical
  obtain ⟨hj1, hjk, hyl⟩ := G.layerIndex_spec hy
  set j := G.layerIndex y with hj
  set T : ℝ := (m : ℝ) + 2 with hT
  have hT0 : 0 < T := by positivity
  have hr : 0 < ϱ - 1 := by linarith
  set q := ⌊T / (ϱ - 1)⌋₊ with hq
  have hqle : (q : ℝ) ≤ T / (ϱ - 1) := Nat.floor_le (by positivity)
  set M := j + 1 + q with hM
  set jlo := j - (1 + q) with hjlo
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  set R : ℕ := (m + 2) * L ^ M with hR
  have hRreal : (R : ℝ) = T * (L : ℝ) ^ M := by rw [hR, hT]; push_cast; ring
  have hM' : ∀ w ∈ G.Ω 1, G.pathDist y w ≤ ENNReal.ofReal T → G.layerIndex w ≤ M :=
    fun w hw hdw => (layerIndex_close G hϱ hj1 hjk hyl hw hT0.le hdw).1
  have hyy : G.pathDist y y ≤ ENNReal.ofReal 0 := by
    simp [G.pathDist_self hy]
  set S := Finset.univ.filter
    (fun z : G.Ω 1 => G.pathDist y z ≤ ENNReal.ofReal ((m : ℝ) + 1)) with hS
  have hz : ∀ z ∈ S, Green.torusDist d (N₀ * L ^ k) y z ≤ R ∧ jlo ≤ G.layerIndex z := by
    intro z hzS
    have hdz : G.pathDist y z ≤ ENNReal.ofReal ((m : ℝ) + 1) := (Finset.mem_filter.1 hzS).2
    have hdzT : G.pathDist y z < ENNReal.ofReal T :=
      lt_of_le_of_lt hdz ((ENNReal.ofReal_lt_ofReal_iff hT0).2 (by rw [hT]; linarith))
    have hcl := layerIndex_close G hϱ hj1 hjk hyl z.2 hT0.le (hdzT.le)
    refine ⟨?_, by omega⟩
    simp only [GeneratingSet.pathDist, iInf_lt_iff] at hdzT
    obtain ⟨c, hc, hcT⟩ := hdzT
    have hcT' : c < T := (ENNReal.ofReal_lt_ofReal_iff hT0).1 hcT
    have := torusDist_le_of_pathCost G hM' hc (p := 0) le_rfl hyy (by linarith)
    rw [hRreal]
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right hcT'.le (by positivity)
  have hcard : S.card ≤ (2 * R + 1) ^ d := by
    refine le_trans ?_ (card_ball_le y R)
    refine Finset.card_le_card_of_injOn (fun z : G.Ω 1 => (z : Torus d (N₀ * L ^ k))) ?_
      Subtype.val_injective.injOn
    intro z hzS
    simpa using (hz z hzS).1
  set wmax : ℝ := (((L : ℝ) ^ jlo)⁻¹) ^ d with hwmax
  have hsum : ∑ z ∈ S, siteWeight G z ≤ S.card • wmax := by
    refine Finset.sum_le_card_nsmul _ _ _ fun z hzS => ?_
    unfold siteWeight
    refine pow_le_pow_left₀ (by positivity) ?_ d
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hL1 (hz z hzS).2)
  refine hsum.trans ?_
  rw [nsmul_eq_mul]
  have hcardR : (S.card : ℝ) ≤ ((2 * (R : ℝ) + 1)) ^ d := by exact_mod_cast hcard
  have hR1 : (1 : ℝ) ≤ R := by
    rw [hRreal]
    have : (1 : ℝ) ≤ T := by rw [hT]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have : (1 : ℝ) ≤ (L : ℝ) ^ M := one_le_pow₀ hL1
    nlinarith
  have hmain : ((2 * (R : ℝ) + 1)) * ((L : ℝ) ^ jlo)⁻¹ ≤ 3 * T * (L : ℝ) ^ (2 + 2 * q) := by
    have h1 : 2 * (R : ℝ) + 1 ≤ 3 * T * (L : ℝ) ^ M := by
      rw [hRreal] at hR1 ⊢; nlinarith
    have h2 : (L : ℝ) ^ M ≤ (L : ℝ) ^ jlo * (L : ℝ) ^ (2 + 2 * q) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hL1 (by omega)
    have hjp : 0 < (L : ℝ) ^ jlo := by positivity
    calc ((2 * (R : ℝ) + 1)) * ((L : ℝ) ^ jlo)⁻¹ ≤ (3 * T * (L : ℝ) ^ M) * ((L : ℝ) ^ jlo)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (3 * T * ((L : ℝ) ^ jlo * (L : ℝ) ^ (2 + 2 * q))) * ((L : ℝ) ^ jlo)⁻¹ := by
          gcongr
      _ = 3 * T * (L : ℝ) ^ (2 + 2 * q) := by field_simp
  calc (S.card : ℝ) * wmax ≤ ((2 * (R : ℝ) + 1)) ^ d * wmax :=
        mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = (((2 * (R : ℝ) + 1)) * ((L : ℝ) ^ jlo)⁻¹) ^ d := by rw [hwmax, mul_pow]
    _ ≤ (3 * T * (L : ℝ) ^ (2 + 2 * q)) ^ d := pow_le_pow_left₀ (by positivity) hmain d
    _ = (3 * T) ^ d * (L : ℝ) ^ (2 * d) * (((L : ℝ) ^ (2 * q)) ^ d) := by
        rw [mul_pow, ← pow_mul, show (2 + 2 * q) * d = 2 * d + 2 * q * d by ring, pow_add]
        ring
    _ ≤ (3 * T) ^ d * (L : ℝ) ^ (2 * d) * Real.exp (γ / 2 * T) := by
        gcongr
        exact pow_two_mul_pow_le hL1 d q hr hqle hT0.le hcond

end Shell

/-- The decay factor `e^{-c D}` of a distance `D ∈ [0, ∞]` (`0` for `D = ∞`). -/
noncomputable def decay (c : ℝ) (D : ENNReal) : ℝ :=
  if D = ⊤ then 0 else Real.exp (-(c * D.toReal))

theorem decay_nonneg (c : ℝ) (D : ENNReal) : 0 ≤ decay c D := by
  unfold decay; split_ifs
  exacts [le_rfl, (Real.exp_pos _).le]

/-- The constant of Lemma 4.4. -/
noncomputable def countConst (d L : ℕ) (γ : ℝ) : ℝ :=
  ∑' m : ℕ, 3 ^ d * (L : ℝ) ^ (2 * d) * Real.exp (2 * γ) *
    (((m + 2 : ℕ) : ℝ) ^ d * Real.exp (-(γ / 2) * ((m + 2 : ℕ) : ℝ)))

theorem summable_countConst (d L : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    Summable fun m : ℕ => 3 ^ d * (L : ℝ) ^ (2 * d) * Real.exp (2 * γ) *
      (((m + 2 : ℕ) : ℝ) ^ d * Real.exp (-(γ / 2) * ((m + 2 : ℕ) : ℝ))) := by
  refine Summable.mul_left _ ?_
  exact (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ d * Real.exp (-(γ / 2) * (n : ℝ))) 2).2
    (Real.summable_pow_mul_exp_neg_nat_mul d (by positivity))

section Total

variable (G : GeneratingSet d L N₀ k ϱ)

/-- **Lemma 4.4 (counting).**  If `2 d log L ≤ (γ/2)(ϱ - 1)` (i.e. `ϱ - 1` large depending on
`d, L, γ`) then `∑_{z ∈ Ω₁} ℓ(z)^{-d} e^{-γ d(y,z)} ≤ C(d, L, γ)` uniformly in `y ∈ Ω₁`, in the
torus size and in `k`.  (The sum over sites with weight `ℓ(z)^{-d}` is the sum over blocks.) -/
theorem sum_siteWeight_decay_le (hϱ : 1 < ϱ) {γ : ℝ} (hγ : 0 < γ)
    (hcond : 2 * d * Real.log L ≤ γ / 2 * (ϱ - 1)) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.Ω 1) :
    ∑ z : G.Ω 1, siteWeight G z * decay γ (G.pathDist y z) ≤ countConst d L γ := by
  classical
  set dz : G.Ω 1 → ENNReal := fun z => G.pathDist y z with hdz
  set B : ℕ := (Finset.univ.sup fun z : G.Ω 1 => if dz z = ⊤ then 0 else ⌊(dz z).toReal⌋₊) + 1
    with hB
  set A : ℕ → ℝ := fun m => 3 ^ d * (L : ℝ) ^ (2 * d) * Real.exp (2 * γ) *
      (((m + 2 : ℕ) : ℝ) ^ d * Real.exp (-(γ / 2) * ((m + 2 : ℕ) : ℝ))) with hA
  have hsum := summable_countConst d L hγ
  have hA0 : ∀ m, 0 ≤ A m := fun m => by positivity
  -- pointwise domination by the shell indicators
  have hpt : ∀ z : G.Ω 1, siteWeight G z * decay γ (dz z) ≤
      ∑ m ∈ Finset.range B, if dz z ≤ ENNReal.ofReal ((m : ℝ) + 1) then
        siteWeight G z * Real.exp (-(γ * m)) else 0 := by
    intro z
    have hw := siteWeight_nonneg G z
    by_cases ht : dz z = ⊤
    · have : decay γ (dz z) = 0 := by simp [decay, ht]
      rw [this, mul_zero]
      exact Finset.sum_nonneg fun m _ => by split_ifs <;> positivity
    · set m₀ := ⌊(dz z).toReal⌋₊ with hm₀
      have hm₀B : m₀ < B := by
        have : m₀ ≤ Finset.univ.sup fun z : G.Ω 1 => if dz z = ⊤ then 0 else ⌊(dz z).toReal⌋₊ := by
          have := Finset.le_sup (f := fun z : G.Ω 1 => if dz z = ⊤ then 0 else ⌊(dz z).toReal⌋₊)
            (Finset.mem_univ z)
          simpa [ht] using this
        omega
      have h1 : (m₀ : ℝ) ≤ (dz z).toReal := Nat.floor_le ENNReal.toReal_nonneg
      have h2 : dz z ≤ ENNReal.ofReal ((m₀ : ℝ) + 1) := by
        rw [← ENNReal.ofReal_toReal ht]
        exact ENNReal.ofReal_le_ofReal (Nat.lt_floor_add_one _).le
      refine le_trans ?_ (Finset.single_le_sum (f := fun m : ℕ => if dz z ≤ ENNReal.ofReal ((m : ℝ) + 1)
        then siteWeight G z * Real.exp (-(γ * m)) else 0) (fun m _ => by
          split_ifs <;> positivity) (Finset.mem_range.2 hm₀B))
      simp only [h2, ite_true]
      unfold decay
      simp only [ht, ↓reduceIte]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hw
      nlinarith
  calc ∑ z : G.Ω 1, siteWeight G z * decay γ (G.pathDist y z)
      ≤ ∑ z : G.Ω 1, ∑ m ∈ Finset.range B, if dz z ≤ ENNReal.ofReal ((m : ℝ) + 1) then
        siteWeight G z * Real.exp (-(γ * m)) else 0 := Finset.sum_le_sum fun z _ => hpt z
    _ = ∑ m ∈ Finset.range B, Real.exp (-(γ * m)) *
          ∑ z ∈ Finset.univ.filter (fun z : G.Ω 1 => dz z ≤ ENNReal.ofReal ((m : ℝ) + 1)),
            siteWeight G z := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun z _ => ?_
        split_ifs <;> ring
    _ ≤ ∑ m ∈ Finset.range B, A m := by
        refine Finset.sum_le_sum fun m _ => ?_
        have := shell_weight_le G hϱ hcond hy m
        calc _ ≤ Real.exp (-(γ * m)) * ((3 * ((m : ℝ) + 2)) ^ d * (L : ℝ) ^ (2 * d) *
            Real.exp (γ / 2 * ((m : ℝ) + 2))) :=
              mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
          _ = A m := by
            rw [hA]; simp only
            have e : Real.exp (-(γ * m)) * Real.exp (γ / 2 * ((m : ℝ) + 2)) =
                Real.exp (2 * γ) * Real.exp (-(γ / 2) * ((m : ℝ) + 2)) := by
              rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
            push_cast
            calc _ = (3 * ((m : ℝ) + 2)) ^ d * (L : ℝ) ^ (2 * d) *
                (Real.exp (-(γ * m)) * Real.exp (γ / 2 * ((m : ℝ) + 2))) := by ring
              _ = _ := by rw [e, mul_pow]; ring
    _ ≤ countConst d L γ := hsum.sum_le_tsum _ (fun m _ => hA0 m)

end Total

end Balaban.Multiscale
