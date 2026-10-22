module

public import Balaban.Fluctuation.CriticalPoint
public import Balaban.Fluctuation.ExpansionGauss
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Lemma 2.3 (a): the exact expansion around the critical point -- the chord identity

Setting of `CriticalPoint`: whole-lattice generating sets `G` (level `n = k`) and `G'` (level
`n + 1`), `a = compWeight L a₁`, bilinear products (complex data).

* `coupling_add_actionC`: `couplingC(θ, Ψ) + A_n(Ψ; φ|) = A_{n+1}(θ; φ) + defectC` for all fields, the
  instance `R = 𝕋` of `RegionPair.coupling_add_actionC_on` (the identity on the new region `R` of a
  region pair, P5 (2.21));
* `chord_identity`: for `(φ₁, α₁)` a solution of (EL) of level `n + 1` and any field `φ` with
  `φ · φ = 1`, the exact expansion (2.3) of `J` around `(ψ^{(k)}, φ₁)`;
* `expansion_chord` (Lemma 2.3 (a)): the same for the complex small solutions
  `φ_{k+1} = bgFieldC D'`, `φ_k(ψ) = bgFieldC D`;
* on a region pair `G ≺ G'` (`RegionPair`, the step on a region, P5 (2.17)–(2.21)): `RegionPair.chord_identity_on`,
  `RegionPair.expansion_chord_on` — the coupling and the level energies summed over the new region
  `R = Ω'_{n+1}`, and the Hessian `⟨τ, H'(α) τ⟩` of the action of `G'` (all its layers) in place of
  `hessForm`; `chordTail_ofLevel`: for a pair of whole-lattice sets the tail is the level form, so
  `chord_identity` and `expansion_chord` are the instances `R = 𝕋` (`RegionPair.ofLevel`);
  `pair_blockVec_eq_sum` (the block form at the layers of `G`), `RegionPair.compTangentOn`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

section KeyC

variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'} {a₁ ν : ℝ} {n : ℕ}

/-- The level term of `actionC`. -/
noncomputable def levelTermC (G : GeneratingSet d L N₀ K ϱ) (a : ℕ → ℝ) {N : ℕ} (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  (1 / 2) * ∑ x : G.Ω 1, ((a (G.layerIndex (x : Torus d (N₀ * L ^ K))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2 : ℝ) : ℂ) *
      ∑ i, (D.Ψ x i - blockAvg G φ x i) * (D.Ψ x i - blockAvg G φ x i)

/-- The gradient and mass terms of `actionC`. -/
noncomputable def restTermC (G : GeneratingSet d L N₀ K ϱ) (ν : ℝ) {N : ℕ} (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  (1 / 2) * ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, (barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) *
          (barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) else 0) +
  (ν : ℂ) / 2 * ∑ x : G.Ω 1, ∑ i, (φ (x, i) - D.h x i) * (φ (x, i) - D.h x i)

theorem actionC_eq_level_add_rest (a : ℕ → ℝ) (ν : ℝ) {N : ℕ} (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) :
    actionC G a ν D φ = levelTermC G a D φ + restTermC G ν D φ := by
  unfold actionC levelTermC restTermC
  ring

theorem levelTermC_eq (hG : IsLevel G n) (a : ℕ → ℝ) {N : ℕ} (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) :
    levelTermC G a D φ = levelEnergyC G a n D.Ψ (svec G φ) := by
  unfold levelTermC levelEnergyC levelEnergyCOn
  rw [show (((1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) : ℝ) : ℂ) =
    (1 / 2) * ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) by push_cast; ring, mul_assoc]
  congr 1
  have hsum : ∀ F : Torus d (N₀ * L ^ K) → ℂ, ∑ x : G.Ω 1, F x = ∑ x, F x := fun F => by
    rw [Finset.sum_coe_sort (G.Ω 1) F, hG.Ω_one]
  rw [hsum (fun x => ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
      ∑ i, (D.Ψ x i - blockAvg G φ x i) * (D.Ψ x i - blockAvg G φ x i))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [(hG x).2]
  have hb : ∀ i, blockAvg G φ x i = blockMean G n (fun y => svec G φ y i) x := fun i => by
    unfold blockAvg blockMean
    rw [(hG x).2]
  simp only [hb]

theorem restTermC_eq (hG : IsLevel G n) (ν : ℝ) {N : ℕ} (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) :
    restTermC G ν D φ = (1 / 2) * ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d, ∑ i,
        (svec G φ (x + Pi.single μ 1) i - svec G φ x i) *
          (svec G φ (x + Pi.single μ 1) i - svec G φ x i) +
      (ν : ℂ) / 2 * ∑ x, ∑ i, (svec G φ x i - D.h x i) * (svec G φ x i - D.h x i) := by
  unfold restTermC
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
    simp only [(hG x).1, true_or, ite_true]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [barField_eq_svec hG, barField_eq_svec hG]
  · congr 1
    have hsum : ∀ F : Torus d (N₀ * L ^ K) → ℂ, ∑ x : G.Ω 1, F x = ∑ x, F x := fun F => by
      rw [Finset.sum_coe_sort (G.Ω 1) F, hG.Ω_one]
    rw [← hsum (fun x => ∑ i, (svec G φ x i - D.h x i) * (svec G φ x i - D.h x i))]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    rw [svec_of_mem]

namespace RegionPair

variable (P : RegionPair G G' n)
include P

/-- **The key identity for a region pair, bilinear form** (core of `coupling_add_actionC`). -/
theorem coupling_add_actionC_on (hL : 2 ≤ L) (ha₁ : 0 < a₁)
    (D : BgData G N) (D' : BgData G' N) (hh : ∀ x i, D.h x i = D'.h x i)
    (hΨ : ∀ x, x ∉ G'.Ω (n + 1) → D.Ψ x = D'.Ψ x) (φ' : G'.Ω 1 × Fin N → ℂ) :
    couplingCOn (G'.Ω (n + 1)) G' a₁ (n + 1) D'.Ψ D.Ψ +
        actionC G (compWeight L a₁) ν D (P.hpre.restrictφ φ') =
      actionC G' (compWeight L a₁) ν D' φ' +
        defectCOn (G'.Ω (n + 1)) G G' (compWeight L a₁) a₁ n D'.Ψ D.Ψ (svec G' φ') := by
  classical
  set R := G'.Ω (n + 1) with hRdef
  have hRsub := P.top_subset
  have hRb : ∀ z ∈ R, ∀ y ∈ G'.blk (n + 1) z, y ∈ R := fun z hz y hy => P.top_blk hz hy
  -- the block field, extended by zero off the new region
  set θ : Torus d (N₀ * L ^ K) → Fin N → ℂ := fun x i => if x ∈ R then D'.Ψ x i else 0 with hθdef
  have hθR : ∀ x ∈ R, θ x = D'.Ψ x := fun x hx => funext fun i => by simp [hθdef, hx]
  have hθc : ∀ x y i, y ∈ G'.blk (n + 1) x → θ y i = θ x i := by
    intro x y i hy
    by_cases hx : x ∈ R
    · have hyR := hRb x hx y hy
      have hxl : x ∈ G'.layer (n + 1) := by
        have hs := G'.layerIndex_spec (P.Ω_one ▸ hRsub hx)
        rw [(P.top_layer x hx).2] at hs
        exact hs.2.2
      simp only [hθdef, hx, hyR, ↓reduceIte]
      exact congrFun (D'.Ψ_layerConst (n + 1) (by omega) P.hp x hxl y hy) i
    · have hyR : y ∉ R := fun hyR => hx (hRb y hyR x (GeneratingSet.mem_blk.2
        (GeneratingSet.mem_blk.1 hy).symm))
      simp [hθdef, hx, hyR]
  have key := coupling_add_levelC_on (G := G) (G' := G') hL ha₁ P.hn P.hp R hRb θ D.Ψ
    (svec G' φ') hθc
  rw [couplingCOn_congr_left R a₁ (n + 1) D.Ψ hθR, levelEnergyCOn_congr_left R _ (n + 1) _ hθR,
    defectCOn_congr_left R hRb _ a₁ D.Ψ _ hθR] at key
  have hsv := P.svec_restrictφ φ'
  have hbar := P.barField_restrictφ D D' hΨ φ'
  have havg : ∀ x i, x ∈ G.Ω 1 → x ∉ R →
      blockAvg G (P.hpre.restrictφ φ') x i = blockAvg G' φ' x i := by
    intro x i hx hxR
    unfold blockAvg
    rw [P.off_layer x hx hxR]
    simp only [hsv]
    rfl
  have havgR : ∀ x i, x ∈ R →
      blockAvg G (P.hpre.restrictφ φ') x i = blockMean G n (fun y => svec G' φ' y i) x := by
    intro x i hx
    unfold blockAvg blockMean
    rw [(P.top_layer x hx).1]
    simp only [hsv]
  have havgR' : ∀ x i, x ∈ R →
      blockAvg G' φ' x i = blockMean G' (n + 1) (fun y => svec G' φ' y i) x := by
    intro x i hx
    unfold blockAvg blockMean
    rw [(P.top_layer x hx).2]
  set F : Torus d (N₀ * L ^ K) → ℂ := fun x =>
    ((compWeight L a₁ (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
      ∑ i, (D.Ψ x i - blockAvg G (P.hpre.restrictφ φ') x i) *
        (D.Ψ x i - blockAvg G (P.hpre.restrictφ φ') x i) with hF
  set F' : Torus d (N₀ * L ^ K) → ℂ := fun x =>
    ((compWeight L a₁ (G'.layerIndex x) / ((L : ℝ) ^ G'.layerIndex x) ^ 2 : ℝ) : ℂ) *
      ∑ i, (D'.Ψ x i - blockAvg G' φ' x i) * (D'.Ψ x i - blockAvg G' φ' x i) with hF'
  have hlev : ∑ x : G.Ω 1, F x = ∑ x ∈ G.Ω 1 \ R, F x + ∑ x ∈ R, F x := by
    rw [Finset.sum_coe_sort (G.Ω 1) F, Finset.sum_sdiff hRsub]
  have hlev' : ∑ x : G'.Ω 1, F' x = ∑ x ∈ G.Ω 1 \ R, F' x + ∑ x ∈ R, F' x := by
    rw [Finset.sum_coe_sort (G'.Ω 1) F', P.Ω_one, Finset.sum_sdiff hRsub]
  have hoff : ∑ x ∈ G.Ω 1 \ R, F x = ∑ x ∈ G.Ω 1 \ R, F' x := by
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hx1, hxR⟩ := Finset.mem_sdiff.1 hx
    simp only [hF, hF', P.off_layer x hx1 hxR, hΨ x hxR, havg x _ hx1 hxR]
  have hon : ∑ x ∈ R, F x = 2 * levelEnergyCOn R G (compWeight L a₁) n D.Ψ (svec G' φ') := by
    unfold levelEnergyCOn
    rw [Finset.mul_sum]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hF, (P.top_layer x hx).1, havgR x _ hx]
    push_cast
    ring
  have hon' : ∑ x ∈ R, F' x = 2 * levelEnergyCOn R G' (compWeight L a₁) (n + 1) D'.Ψ (svec G' φ') := by
    unfold levelEnergyCOn
    rw [Finset.mul_sum]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hF', (P.top_layer x hx).2, havgR' x _ hx]
    push_cast
    ring
  have hgrad : ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, (barField G D.Ψ (P.hpre.restrictφ φ') (x + Pi.single μ 1) i -
          barField G D.Ψ (P.hpre.restrictφ φ') x i) *
          (barField G D.Ψ (P.hpre.restrictφ φ') (x + Pi.single μ 1) i -
          barField G D.Ψ (P.hpre.restrictφ φ') x i) else 0) =
      ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d,
      (if x ∈ G'.Ω 1 ∨ x + Pi.single μ 1 ∈ G'.Ω 1 then
        ∑ i, (barField G' D'.Ψ φ' (x + Pi.single μ 1) i - barField G' D'.Ψ φ' x i) *
          (barField G' D'.Ψ φ' (x + Pi.single μ 1) i - barField G' D'.Ψ φ' x i) else 0) := by
    simp only [hbar, P.Ω_one]
  have hmass : ∑ x : G.Ω 1, ∑ i, ((P.hpre.restrictφ φ') (x, i) - D.h x i) *
      ((P.hpre.restrictφ φ') (x, i) - D.h x i) =
      ∑ x : G'.Ω 1, ∑ i, (φ' (x, i) - D'.h x i) * (φ' (x, i) - D'.h x i) := by
    have e1 : ∑ x : G.Ω 1, ∑ i, ((P.hpre.restrictφ φ') (x, i) - D.h x i) *
        ((P.hpre.restrictφ φ') (x, i) - D.h x i) =
        ∑ x ∈ G.Ω 1, ∑ i, (svec G' φ' x i - D'.h x i) * (svec G' φ' x i - D'.h x i) := by
      rw [← Finset.sum_coe_sort (G.Ω 1)]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
      rw [← hsv, svec_of_mem G _ x i, hh]
    have e2 : ∑ x : G'.Ω 1, ∑ i, (φ' (x, i) - D'.h x i) * (φ' (x, i) - D'.h x i) =
        ∑ x ∈ G'.Ω 1, ∑ i, (svec G' φ' x i - D'.h x i) * (svec G' φ' x i - D'.h x i) := by
      rw [← Finset.sum_coe_sort (G'.Ω 1)]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
      rw [svec_of_mem G' _ x i]
    rw [e1, e2, P.Ω_one]
  unfold actionC
  rw [show (∑ x : G.Ω 1, ((compWeight L a₁ (G.layerIndex (x : Torus d (N₀ * L ^ K))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2 : ℝ) : ℂ) *
      ∑ i, (D.Ψ x i - blockAvg G (P.hpre.restrictφ φ') x i) *
        (D.Ψ x i - blockAvg G (P.hpre.restrictφ φ') x i)) = ∑ x : G.Ω 1, F x from rfl,
    show (∑ x : G'.Ω 1, ((compWeight L a₁ (G'.layerIndex (x : Torus d (N₀ * L ^ K))) /
      ((L : ℝ) ^ G'.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2 : ℝ) : ℂ) *
      ∑ i, (D'.Ψ x i - blockAvg G' φ' x i) * (D'.Ψ x i - blockAvg G' φ' x i)) =
      ∑ x : G'.Ω 1, F' x from rfl,
    hlev, hlev', hoff, hon, hon', hgrad, hmass]
  linear_combination key

end RegionPair

/-- **The key identity, bilinear form**: for the data `D` of level `n` and `D'` of level `n + 1`
with the same `h̃`,
`couplingC(θ = D'.Ψ, D.Ψ) + A_n(D; φ|) = A_{n+1}(D'; φ) + defectC`. -/
theorem coupling_add_actionC (hL : 2 ≤ L) (ha₁ : 0 < a₁) (hG : IsLevel G n)
    (hG' : IsLevel G' (n + 1)) (hp : n + 1 ≤ K) {N : ℕ}
    (D : BgData G N) (D' : BgData G' N) (hh : ∀ x i, D.h x i = D'.h x i)
    (φ' : G'.Ω 1 × Fin N → ℂ) :
    couplingC G' a₁ (n + 1) D'.Ψ D.Ψ +
        actionC G (compWeight L a₁) ν D ((hG.precedes hG' hp).restrictφ φ') =
      actionC G' (compWeight L a₁) ν D' φ' +
        defectC G G' (compWeight L a₁) a₁ n D'.Ψ D.Ψ (svec G' φ') := by
  have h := (RegionPair.ofLevel hG hG' hp).coupling_add_actionC_on (ν := ν) hL ha₁ D D' hh
    (fun x hx => absurd (hG'.Ω_top ▸ Finset.mem_univ x) hx) φ'
  rw [hG'.Ω_top] at h
  exact h



end KeyC

section Chord

variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'} {a₁ ν : ℝ} {n : ℕ}

/-- `pair τ τ` as a torus sum. -/
theorem pair_self_eq {m : ℕ} (hG : IsLevel G m) {N : ℕ} (τ : G.Ω 1 × Fin N → ℂ) :
    pair G τ τ = ∑ x, ∑ i, svec G τ x i * svec G τ x i := by
  unfold pair
  rw [Fintype.sum_prod_type]
  have hsum : ∀ F : Torus d (N₀ * L ^ K) → ℂ, ∑ x : G.Ω 1, F x = ∑ x, F x := fun F => by
    rw [Finset.sum_coe_sort (G.Ω 1) F, hG.Ω_one]
  rw [← hsum (fun x => ∑ i, svec G τ x i * svec G τ x i)]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  rw [svec_of_mem]

/-- `⟨τ, -Δ τ⟩` as the bond sum. -/
theorem pair_lapVec_eq_bond {N : ℕ} (τ : G.Ω 1 × Fin N → ℂ) :
    pair G τ (lapVec G τ) = ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d, ∑ i,
      (svec G τ (x + Pi.single μ 1) i - svec G τ x i) *
        (svec G τ (x + Pi.single μ 1) i - svec G τ x i) := by
  have hT : ∀ i : Fin N, ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d,
      (svec G τ (x + Pi.single μ 1) i - svec G τ x i) *
        (svec G τ (x + Pi.single μ 1) i - svec G τ x i) =
      ∑ x : G.Ω 1, τ (x, i) * lapVec G τ (x, i) := by
    intro i
    rw [bond_sum_by_parts (fun y => svec G τ y i) (fun y => svec G τ y i)]
    rw [Green.sum_eq_sum_subtype (G.Ω 1) _ (fun x hx => by simp [svec_of_not_mem G _ hx])]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← svec_of_mem G τ x i]
    rfl
  have hsw : ∀ f : Torus d (N₀ * L ^ K) → Fin d → Fin N → ℂ,
      ∑ x, ∑ μ, ∑ i, f x μ i = ∑ i, ∑ x, ∑ μ, f x μ i := by
    intro f
    calc _ = ∑ x, ∑ i, ∑ μ, f x μ i := Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hsw]
  simp only [hT]
  unfold pair
  rw [Fintype.sum_prod_type_right]

/-- **The block form `⟨τ, Q* a Q τ⟩`** as the sum over `Ω₁` of the weighted squares of the block
averages, at the layers of `G` (core of `pair_blockVec_eq`). -/
theorem pair_blockVec_eq_sum (a : ℕ → ℝ) {N : ℕ} (τ : G.Ω 1 × Fin N → ℂ) :
    pair G τ (blockVec G a τ) = ∑ x : G.Ω 1,
      ((a (G.layerIndex (x : Torus d (N₀ * L ^ K))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2 : ℝ) : ℂ) *
        ∑ i, blockAvg G τ x i * blockAvg G τ x i := by
  have eC := sum_blockAvg (a := a) (g := fun i y => blockAvg G τ y i)
    (fun i => blockAvg_blockConst τ i) τ
  rw [eC]
  unfold pair
  exact Finset.sum_congr rfl fun p _ => by
    show τ p * blockTerm G a (zeroExt (G.Ω 1) (fun z => τ (z, p.2))) p.1 = _
    rw [blockTerm_zeroExt_eq]
    show τ p * (_ * blockAvg G τ p.1 p.2) = _
    ring

/-- `⟨τ, Q* a Q τ⟩ = 2 · level energy at `θ = 0``. -/
theorem pair_blockVec_eq {m : ℕ} (hG : IsLevel G m) (a : ℕ → ℝ) {N : ℕ}
    (τ : G.Ω 1 × Fin N → ℂ) :
    pair G τ (blockVec G a τ) = 2 * levelEnergyC G a m (fun _ _ => 0) (svec G τ) := by
  rw [pair_blockVec_eq_sum]
  unfold levelEnergyC levelEnergyCOn
  have hsum : ∀ F : Torus d (N₀ * L ^ K) → ℂ, ∑ x : G.Ω 1, F x = ∑ x, F x := fun F => by
    rw [Finset.sum_coe_sort (G.Ω 1) F, hG.Ω_one]
  rw [hsum (fun x => ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
    ∑ i, blockAvg G τ x i * blockAvg G τ x i)]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hb : ∀ i, blockAvg G τ x i = blockMean G m (fun y => svec G τ y i) x := fun i => by
    unfold blockAvg blockMean
    rw [(hG x).2]
  have h0 : ∀ i, (0 - blockMean G m (fun y => svec G τ y i) x) *
      (0 - blockMean G m (fun y => svec G τ y i) x) =
      blockMean G m (fun y => svec G τ y i) x * blockMean G m (fun y => svec G τ y i) x :=
    fun i => by ring
  simp only [(hG x).2, hb, h0]
  push_cast
  ring

/-- **The mass form** `⟨f, (-Δ + ν + α) f⟩` of fields on the torus (bond sum, mass, and the
multiplier `α` on `Ω₁`, zero outside): the quadratic form
`⟨φ', (-Δ^η + μ_k + α_{k+1}) φ'⟩_η` of (2.3), with the bilinear product. -/
noncomputable def hessForm (G : GeneratingSet d L N₀ K ϱ) (ν : ℝ) (α : G.Ω 1 → ℂ) {N : ℕ}
    (f : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d, ∑ i,
      (f (x + Pi.single μ 1) i - f x i) * (f (x + Pi.single μ 1) i - f x i) +
    (ν : ℂ) * ∑ x, ∑ i, f x i * f x i +
    ∑ x, zeroExt (G.Ω 1) α x * ∑ i, f x i * f x i

/-- The operator form of `hessForm`. -/
theorem hessForm_eq {m : ℕ} (hG : IsLevel G m) (ν : ℝ) (α : G.Ω 1 → ℂ) {N : ℕ}
    (τ : G.Ω 1 × Fin N → ℂ) :
    hessForm G ν α (svec G τ) = pair G τ (lapVec G τ) + (ν : ℂ) * pair G τ τ +
      pair G τ (fun p => α p.1 * τ p) := by
  rw [pair_lapVec_eq_bond, pair_self_eq hG]
  unfold hessForm
  congr 1
  unfold pair
  rw [Fintype.sum_prod_type]
  have hsum : ∀ F : Torus d (N₀ * L ^ K) → ℂ, ∑ x : G.Ω 1, F x = ∑ x, F x := fun F => by
    rw [Finset.sum_coe_sort (G.Ω 1) F, hG.Ω_one]
  rw [← hsum (fun x => zeroExt (G.Ω 1) α x * ∑ i, svec G τ x i * svec G τ x i)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [svec_of_mem, zeroExt_mem]
  ring

theorem psiStar_add {a : ℕ → ℝ} {n p : ℕ} (θ f g : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (x : Torus d (N₀ * L ^ K)) (i : Fin N) :
    psiStar G G' a n p θ (fun y j => f y j + g y j) x i =
      psiStar G G' a n p θ f x i + psiStar G G' a n p (fun _ _ => 0) g x i := by
  unfold psiStar
  rw [blockMean_add, blockMean_add]
  ring

theorem svec_add_fun {N : ℕ} (u v : G.Ω 1 × Fin N → ℂ) :
    svec G (u + v) = fun y j => svec G u y j + svec G v y j := by
  funext y j
  exact svec_add (G := G) u v y j

/-- **The chord identity (2.3) on a region pair, bilinear form** (FLUCTUATION Lemma 2.3 (a); P5 (2.21);
core of `chord_identity`).  Let `(φ₁, α₁)` solve (EL) for the datum `D'` of `G'`, `D` a datum of `G`
with the same `h̃` and equal to `D'` off the new region `R = Ω'_{n+1}`, `ψ' = D.Ψ - ψ_*.Ψ`
(`ψ_* = composeData …`, the point of (2.1)), and `φh` any field with `φh · φh = 1`, `τ = φh - φ₁`.  Then
`J = A'(θ, φ₁) + coupling_R(0, ψ') + level_{R,n}(ψ', τ) - level'_{R,n+1}(0, τ) + ½ ⟨τ, H'(α₁) τ⟩`,
the coupling and the level energies summed over `R`, and `⟨τ, H'(α₁) τ⟩` the Hessian of the action of
`G'` (all its layers) with the multiplier.  For a pair of whole-lattice sets the last two terms are
`½ hessForm` (`chordTail_ofLevel`). -/
theorem RegionPair.chord_identity_on (P : RegionPair G G' n) (hL : 2 ≤ L) (ha₁ : 0 < a₁)
    (D' : BgData G' N) {φ₁ : G'.Ω 1 × Fin N → ℂ} {α₁ : G'.Ω 1 → ℂ}
    (hel : IsEL G' (compWeight L a₁) ν D' φ₁ α₁) (D : BgData G N) (hh : ∀ x i, D.h x i = D'.h x i)
    (hΨ : ∀ x, x ∉ G'.Ω (n + 1) → D.Ψ x = D'.Ψ x) {φh : G'.Ω 1 × Fin N → ℂ}
    (hφh : ∀ x, ∑ i, φh (x, i) * φh (x, i) = 1) :
    couplingCOn (G'.Ω (n + 1)) G' a₁ (n + 1) D'.Ψ D.Ψ +
        actionC G (compWeight L a₁) ν D (P.hpre.restrictφ φh) =
      actionC G' (compWeight L a₁) ν D' φ₁ +
        couplingCOn (G'.Ω (n + 1)) G' a₁ (n + 1) (fun _ _ => 0) (fun x i => D.Ψ x i -
          (composeData P.hpre (compWeight L a₁) φ₁ D').Ψ x i) +
        levelEnergyCOn (G'.Ω (n + 1)) G (compWeight L a₁) n (fun x i => D.Ψ x i -
          (composeData P.hpre (compWeight L a₁) φ₁ D').Ψ x i) (svec G' (φh - φ₁)) -
        levelEnergyCOn (G'.Ω (n + 1)) G' (compWeight L a₁) (n + 1) (fun _ _ => 0)
          (svec G' (φh - φ₁)) +
        (1 / 2) * pair G' (φh - φ₁)
          (liftOp N (dirichletOperator G' (compWeight L a₁) ν α₁) *ᵥ (φh - φ₁)) := by
  set a := compWeight L a₁ with ha
  set R := G'.Ω (n + 1) with hRdef
  have hRb : ∀ z ∈ R, ∀ y ∈ G'.blk (n + 1) z, y ∈ R := fun z hz y hy => P.top_blk hz hy
  set τ : G'.Ω 1 × Fin N → ℂ := φh - φ₁ with hτ
  have hφhτ : φh = φ₁ + τ := by rw [hτ]; abel
  have Kc := P.coupling_add_actionC_on (ν := ν) hL ha₁ D D' hh hΨ φh
  set ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ := fun x i => D.Ψ x i -
    (composeData P.hpre a φ₁ D').Ψ x i with hψ'
  have hsv : svec G' φh = fun y j => svec G' φ₁ y j + svec G' τ y j := by
    rw [hφhτ]; exact svec_add_fun φ₁ τ
  have hu : ∀ x ∈ R, ∀ i, D.Ψ x i - psiStar G G' a n (n + 1) D'.Ψ (svec G' φh) x i =
      ψ' x i - psiStar G G' a n (n + 1) (fun _ _ => 0) (svec G' τ) x i := fun x hx i => by
    rw [hsv, psiStar_add, ← P.composeData_Ψ_eq_psiStar_on a φ₁ D' hx i]
    simp only [hψ']
    ring
  have hdef : defectCOn R G G' a a₁ n D'.Ψ D.Ψ (svec G' φh) =
      defectCOn R G G' a a₁ n (fun _ _ => 0) ψ' (svec G' τ) := by
    unfold defectCOn
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => by rw [hu x hx i]
    · congr 1
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
      have hb : blockMean G' (n + 1) (fun y => D.Ψ y i -
          psiStar G G' a n (n + 1) D'.Ψ (svec G' φh) y i) x =
          blockMean G' (n + 1) (fun y => ψ' y i -
            psiStar G G' a n (n + 1) (fun _ _ => 0) (svec G' τ) y i) x := by
        unfold blockMean
        congr 1
        exact Finset.sum_congr rfl fun y hy => hu y (hRb x hx y hy) i
      rw [hb]
  have hG0 := coupling_add_levelC_on (G := G) (G' := G') hL ha₁ P.hn P.hp R hRb (fun _ _ => 0) ψ'
    (svec G' τ) (fun x y i hy => rfl)
  have A := actionC_add (G := G') (a := a) (ν := ν) D' φ₁ τ
  rw [← hφhτ] at A
  have hEL : ∀ p, (liftOp N (dirichletOperator G' a ν 0) *ᵥ φ₁ - source G' a ν D') p =
      -(α₁ p.1 * φ₁ p) := fun p => by
    have h1 := congrFun hel.1 p
    rw [H_alpha_apply] at h1
    simp only [Pi.sub_apply]
    linear_combination h1
  have hlin : pair G' τ (liftOp N (dirichletOperator G' a ν 0) *ᵥ φ₁ - source G' a ν D') =
      (1 / 2) * pair G' τ (fun p => α₁ p.1 * τ p) := by
    have hcon : ∀ x, ∑ i, φ₁ (x, i) * τ (x, i) = -(1 / 2) * ∑ i, τ (x, i) * τ (x, i) := fun x => by
      have h1 := hφh x
      have h2 := hel.2 x
      rw [hφhτ] at h1
      simp only [Pi.add_apply] at h1
      have e : ∑ i, (φ₁ (x, i) + τ (x, i)) * (φ₁ (x, i) + τ (x, i)) =
          ∑ i, φ₁ (x, i) * φ₁ (x, i) + 2 * ∑ i, φ₁ (x, i) * τ (x, i) +
            ∑ i, τ (x, i) * τ (x, i) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, h2] at h1
      linear_combination (1 / 2 : ℂ) * h1
    have e1 : pair G' τ (liftOp N (dirichletOperator G' a ν 0) *ᵥ φ₁ - source G' a ν D') =
        -∑ x, α₁ x * ∑ i, τ (x, i) * φ₁ (x, i) := by
      unfold pair
      rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hEL (x, i)]
      ring
    have e2 : pair G' τ (fun p => α₁ p.1 * τ p) = ∑ x, α₁ x * ∑ i, τ (x, i) * τ (x, i) := by
      unfold pair
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2, Finset.mul_sum]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have := hcon x
    have e3 : ∑ i, τ (x, i) * φ₁ (x, i) = ∑ i, φ₁ (x, i) * τ (x, i) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e3, this]
    ring
  have hHα : pair G' τ (liftOp N (dirichletOperator G' a ν α₁) *ᵥ τ) =
      pair G' τ (liftOp N (dirichletOperator G' a ν 0) *ᵥ τ) + pair G' τ (fun p => α₁ p.1 * τ p) := by
    rw [← pair_add_right]
    congr 1
    funext p
    rw [H_alpha_apply]
    rfl
  rw [hdef] at Kc
  linear_combination Kc + A + hlin - hG0 - (1 / 2 : ℂ) * hHα

/-- **The tail of the chord identity for a pair of whole-lattice sets**: the terms
`coupling(0, ψ') + level_n(ψ', τ) - level'_{n+1}(0, τ) + ½ ⟨τ, H'(α) τ⟩` of `chord_identity_on` at
`R = 𝕋` are `coupling(0, ψ') + level_n(ψ', τ) + ½ hessForm(τ)` (`pair_blockVec_eq`, `hessForm_eq`). -/
theorem chordTail_ofLevel (hG' : IsLevel G' (n + 1)) (a : ℕ → ℝ) (ν : ℝ) (α : G'.Ω 1 → ℂ)
    (τ : G'.Ω 1 × Fin N → ℂ) (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    couplingCOn Finset.univ G' a₁ (n + 1) (fun _ _ => 0) ψ' +
        levelEnergyCOn Finset.univ G a n ψ' (svec G' τ) -
        levelEnergyCOn Finset.univ G' a (n + 1) (fun _ _ => 0) (svec G' τ) +
        (1 / 2) * pair G' τ (liftOp N (dirichletOperator G' a ν α) *ᵥ τ) =
      couplingC G' a₁ (n + 1) (fun _ _ => 0) ψ' + levelEnergyC G a n ψ' (svec G' τ) +
        (1 / 2) * hessForm G' ν α (svec G' τ) := by
  have hH : pair G' τ (liftOp N (dirichletOperator G' a ν α) *ᵥ τ) =
      pair G' τ (lapVec G' τ) + 2 * levelEnergyC G' a (n + 1) (fun _ _ => 0) (svec G' τ) +
        (ν : ℂ) * pair G' τ τ + pair G' τ (fun p => α p.1 * τ p) := by
    rw [← pair_blockVec_eq hG']
    unfold pair
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [H_alpha_apply, H0_apply]
    ring
  have hHess := hessForm_eq hG' ν α τ
  unfold couplingC levelEnergyC at hH ⊢
  linear_combination (1 / 2 : ℂ) * hH - (1 / 2 : ℂ) * hHess

/-- **The chord identity (2.3), bilinear form** (FLUCTUATION Lemma 2.3 (a)).  Let `(φ₁, α₁)` solve
(EL) for the datum `D'` of level `n + 1` (this is `(φ_{k+1}, α_{k+1})`), `ψ_* = composeData …` the
point of (2.1), `D` a datum of level `n` with the same `h̃` and `ψ' = D.Ψ - ψ_*.Ψ`, and `φh` any field
with `φh · φh = 1` (this is `φ_k(ψ)` for the complex small solution), `φ' = φh - φ₁`.  Then
`J = A_{k+1}(θ, φ₁) + ½ a₁ L^{-2(n+1)} ‖Q ψ'‖² + (a_n/2) ‖ψ' - Q_n φ'‖² + ½ ⟨φ', (-Δ + ν + α₁) φ'⟩`
with the bilinear products. -/
theorem chord_identity (hL : 2 ≤ L) (ha₁ : 0 < a₁) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) {N : ℕ} (D' : BgData G' N) {φ₁ : G'.Ω 1 × Fin N → ℂ} {α₁ : G'.Ω 1 → ℂ}
    (hel : IsEL G' (compWeight L a₁) ν D' φ₁ α₁) (D : BgData G N)
    (hh : ∀ x i, D.h x i = D'.h x i) {φh : G'.Ω 1 × Fin N → ℂ}
    (hφh : ∀ x, ∑ i, φh (x, i) * φh (x, i) = 1) :
    couplingC G' a₁ (n + 1) D'.Ψ D.Ψ +
        actionC G (compWeight L a₁) ν D ((hG.precedes hG' hp).restrictφ φh) =
      actionC G' (compWeight L a₁) ν D' φ₁ +
        couplingC G' a₁ (n + 1) (fun _ _ => 0) (fun x i => D.Ψ x i -
          (composeData (hG.precedes hG' hp) (compWeight L a₁) φ₁ D').Ψ x i) +
        levelEnergyC G (compWeight L a₁) n (fun x i => D.Ψ x i -
          (composeData (hG.precedes hG' hp) (compWeight L a₁) φ₁ D').Ψ x i) (svec G' (φh - φ₁)) +
        (1 / 2) * hessForm G' ν α₁ (svec G' (φh - φ₁)) := by
  have h := (RegionPair.ofLevel hG hG' hp).chord_identity_on (ν := ν) hL ha₁ D' hel D hh
    (fun x hx => absurd (hG'.Ω_top ▸ Finset.mem_univ x) hx) hφh
  rw [hG'.Ω_top] at h
  have ht := chordTail_ofLevel (G := G) (a₁ := a₁) hG' (compWeight L a₁) ν α₁ (φh - φ₁)
    (fun x i => D.Ψ x i - (composeData (hG.precedes hG' hp) (compWeight L a₁) φ₁ D').Ψ x i)
  unfold couplingC levelEnergyC at ht ⊢
  linear_combination h + ht

theorem svec_sub_restrict {n : ℕ} (hG : IsLevel G n) (hG' : IsLevel G' (n + 1)) (hp : n + 1 ≤ K)
    {N : ℕ} (φ : G.Ω 1 × Fin N → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ) :
    svec G' (liftφ G' hG φ - φ₁) =
      svec G (φ - (hG.precedes hG' hp).restrictφ φ₁) :=
  (RegionPair.ofLevel hG hG' hp).svec_sub_restrict φ φ₁

/-- The tangent `ψ' = ψ - ψ^{(k)}` of Lemma 2.3 on a region pair (core of `compTangent`). -/
noncomputable def RegionPair.compTangentOn (P : RegionPair G G' n) (a : ℕ → ℝ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) (D' : BgData G' N) (D : BgData G N) :
    Torus d (N₀ * L ^ K) → Fin N → ℂ := fun x i =>
  D.Ψ x i - (composeData P.hpre a φ₁ D').Ψ x i

/-- The tangent `ψ' = ψ - ψ^{(k)}` of Lemma 2.3.  It is `compTangentOn` of the region pair
`RegionPair.ofLevel` (`compTangent_eq_compTangentOn`, by `rfl`); the body is kept explicit because 25
landed proofs unfold `compTangent` to it. -/
noncomputable def compTangent {n : ℕ} (hG : IsLevel G n) (hG' : IsLevel G' (n + 1)) (hp : n + 1 ≤ K)
    (a : ℕ → ℝ) {N : ℕ} (φ₁ : G'.Ω 1 × Fin N → ℂ) (D' : BgData G' N) (D : BgData G N) :
    Torus d (N₀ * L ^ K) → Fin N → ℂ := fun x i =>
  D.Ψ x i - (composeData (hG.precedes hG' hp) a φ₁ D').Ψ x i

theorem compTangent_eq_compTangentOn {n : ℕ} (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (a : ℕ → ℝ) {N : ℕ} (φ₁ : G'.Ω 1 × Fin N → ℂ) (D' : BgData G' N)
    (D : BgData G N) :
    compTangent hG hG' hp a φ₁ D' D = (RegionPair.ofLevel hG hG' hp).compTangentOn a φ₁ D' D :=
  rfl

/-- **Lemma 2.3 (a), the chord identity (2.3), on a region pair** (P5 (2.21); core of
`expansion_chord`).  Let `D'` be the datum `(θ, h)` of `G'` in `𝒟(𝔹')` (`δ ≤ thm73C1`),
`(φ_{k+1}, α_{k+1}) = (bgFieldC, bgMultC) D'`, and `D` the datum of `ψ = ψ^{(k)} + ψ'` of `G` with the same
`h̃`, equal to `D'` off the new region `R = Ω'_{n+1}`, in the domain of the small solution
`φ_k(ψ) = bgFieldC D`.  With `τ = φ_k(ψ) - φ_{k+1}` (on `Ω'₁ = Ω₁`) and `ψ' = D.Ψ - ψ^{(k)}.Ψ`
(`compTangentOn`), in bilinear form:
`J_k(θ, ψ) = A'(θ, φ_{k+1}) + coupling_R(0, ψ') + level_{R,n}(ψ', τ) - level'_{R,n+1}(0, τ)
 + ½ ⟨τ, H'(α_{k+1}) τ⟩`. -/
theorem RegionPair.expansion_chord_on (P : RegionPair G G' n) (ha₁ : 0 < a₁)
    (H : BgHyp d L K ϱ (compWeight L a₁) ν) (H' : BgHyp d L K ϱ' (compWeight L a₁) ν)
    (D' : BgData G' N) (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C1 d L N) ν D') (D : BgData G N)
    (hh : ∀ x i, D.h x i = D'.h x i) (hΨ : ∀ x, x ∉ G'.Ω (n + 1) → D.Ψ x = D'.Ψ x)
    (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D) :
    couplingCOn (G'.Ω (n + 1)) G' a₁ (n + 1) D'.Ψ D.Ψ +
        actionC G (compWeight L a₁) ν D (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D) =
      actionC G' (compWeight L a₁) ν D' (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') +
        couplingCOn (G'.Ω (n + 1)) G' a₁ (n + 1) (fun _ _ => 0) (P.compTangentOn (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D) +
        levelEnergyCOn (G'.Ω (n + 1)) G (compWeight L a₁) n (P.compTangentOn (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D)
          (svec G (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D -
            P.hpre.restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D'))) -
        levelEnergyCOn (G'.Ω (n + 1)) G' (compWeight L a₁) (n + 1) (fun _ _ => 0)
          (svec G (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D -
            P.hpre.restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D'))) +
        (1 / 2) * pair G' (P.liftφ (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D) -
            bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (liftOp N (dirichletOperator G' (compWeight L a₁) ν
            (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')) *ᵥ
            (P.liftφ (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D) -
              bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')) := by
  have hL3 : 2 ≤ L := by have := H.hL; omega
  have hd0 : 0 < d := by have := H.hd; omega
  have hD'1 : InUnionDomainC G' (bgC0 d L N) (bgC1 d L N) ν D' := by
    obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hD'
    exact ⟨δ, ε, hδ0, hδε, hε, (thm73_small (L := L) (N := N) hd0 hδ0 hδc).1, hνε, hDC⟩
  have hs' := (theorem72 H' hD'1).2.1
  have hs := (theorem72 H hD).2.1
  have hφh : ∀ x : G'.Ω 1, ∑ i, P.liftφ (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D) (x, i) *
      P.liftφ (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D) (x, i) = 1 := fun x =>
    hs.1.2 ⟨x.1, P.Ω_one ▸ x.2⟩
  have := P.chord_identity_on (ν := ν) (a₁ := a₁) hL3 ha₁ D' hs'.1 D hh hΨ hφh
  rw [P.restrictφ_liftφ, P.svec_sub_restrict] at this
  exact this

/-- **Lemma 2.3 (a): the chord identity (2.3).**  Let `D'` be the datum `(θ, h)` of level `n + 1` in
`𝒟(𝔹'_k)` (`δ ≤ thm73C1`), `(φ_{k+1}, α_{k+1}) = (bgFieldC, bgMultC) D'`, and `D` the datum of
`ψ = ψ^{(k)} + ψ'` of level `n` with the same `h̃`, in the domain of the small solution
`φ_k(ψ) = bgFieldC D`.  With `φ' = φ_k(ψ) - φ_{k+1}` (restricted to `Ω₁`) and
`ψ' = D.Ψ - ψ^{(k)}.Ψ` (`compTangent`), in bilinear form (it is the real identity for real data,
`expansion_chord_real`):
`J_k(θ, ψ) = A^η_{k+1}(θ, φ_{k+1}) + ½ a₁ L^{-2(n+1)} ‖Qψ'‖² + (a_n/2) ‖ψ' - Q_n φ'‖²
 + ½ ⟨φ', (-Δ + ν + α_{k+1}) φ'⟩`. -/
theorem expansion_chord (ha₁ : 0 < a₁) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (H : BgHyp d L K ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L K ϱ' (compWeight L a₁) ν) {N : ℕ} (D' : BgData G' N)
    (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C1 d L N) ν D') (D : BgData G N)
    (hh : ∀ x i, D.h x i = D'.h x i)
    (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D) :
    couplingC G' a₁ (n + 1) D'.Ψ D.Ψ +
        actionC G (compWeight L a₁) ν D (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D) =
      actionC G' (compWeight L a₁) ν D' (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') +
        couplingC G' a₁ (n + 1) (fun _ _ => 0) (compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D) +
        levelEnergyC G (compWeight L a₁) n (compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D)
          (svec G (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D -
            (hG.precedes hG' hp).restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D'))) +
        (1 / 2) * hessForm G' ν (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (svec G (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D -
            (hG.precedes hG' hp).restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D'))) := by
  have h := (RegionPair.ofLevel hG hG' hp).expansion_chord_on ha₁ H H' D' hD' D hh
    (fun x hx => absurd (hG'.Ω_top ▸ Finset.mem_univ x) hx) hD
  rw [hG'.Ω_top] at h
  have ht := chordTail_ofLevel (G := G) (a₁ := a₁) hG' (compWeight L a₁) ν
    (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
    ((RegionPair.ofLevel hG hG' hp).liftφ (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D) -
      bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')
    ((RegionPair.ofLevel hG hG' hp).compTangentOn (compWeight L a₁)
      (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D)
  rw [RegionPair.svec_sub_restrict] at ht
  rw [compTangent_eq_compTangentOn]
  unfold couplingC levelEnergyC at ht ⊢
  linear_combination h + ht

end Chord

end Balaban.Fluctuation
