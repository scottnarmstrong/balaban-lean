/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.MassChangeRegion
public import Balaban.Localization.Reflection
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The sharp crossing count and the scale-uniform wall constant (MASS-RESPONSE (2.3)-(2.5))

The cubes are `Balaban.Reflection.cubeSet ℓ s c`, the coordinate cubes `{c + t : t < s}^d` of the
torus `(ℤ/ℓℤ)^d` (the cubes `B_n(x)` of the generating sets are such cubes with `s = L^n`, and
`cubeOf` is `cubeSet` with side `s L^q`).

* `crossingOf S`: bonds `(x, x + e_μ)` with exactly one endpoint in `S`; `Region.crossing_eq`;
* `crossing_card_box_le` (T1): a cube of side `s` has at most `2 d s^(d-1)` crossing bonds;
* `crossingOf_union_subset`, `crossingOf_card_biUnion_le` (T2), `Region.card_crossing_le_cubes`
  (T3);
* `massChange_region_bound_cubes` (T4): the per-cube region bound with the constants
  `C_D = (d+2) M^d L² (Km Bh)²`, `C_W = 2 d M^{d-1} L² Km Bh` with no power of `L^k`.  The
  note's `C_W` is this one times `G_∇` after `δ₀ = G_∇ δ_k`;
* `crossing_cubes_example` (T5): non-vacuity at the `Finset` level.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization
  Balaban.Reflection Finset

section Finset

variable {d n : ℕ} [NeZero n]

/-- The bonds `(x, x + e_μ)` with exactly one endpoint in `S`. -/
noncomputable def crossingOf (S : Finset (Torus d n)) : Finset (Torus d n × Fin d) :=
  Finset.univ.filter fun b => ¬ (b.1 ∈ S ↔ b.1 + Pi.single b.2 1 ∈ S)

theorem mem_crossingOf {S : Finset (Torus d n)} {b : Torus d n × Fin d} :
    b ∈ crossingOf S ↔ ¬ (b.1 ∈ S ↔ b.1 + Pi.single b.2 1 ∈ S) := by
  simp [crossingOf]

/-- Crossing bonds of a union lie among those of the pieces. -/
theorem crossingOf_union_subset (S T : Finset (Torus d n)) :
    crossingOf (S ∪ T) ⊆ crossingOf S ∪ crossingOf T := by
  classical
  intro b hb
  simp only [mem_crossingOf, mem_union] at hb ⊢
  tauto

/-- Crossing bonds of an indexed union. -/
theorem crossingOf_biUnion_subset {ι : Type*} [DecidableEq ι] (𝒞 : Finset ι)
    (B : ι → Finset (Torus d n)) :
    crossingOf (𝒞.biUnion B) ⊆ 𝒞.biUnion fun c => crossingOf (B c) := by
  classical
  intro b hb
  simp only [mem_crossingOf, mem_biUnion] at hb ⊢
  by_contra h
  apply hb
  have h' : ∀ c ∈ 𝒞, (b.1 ∈ B c ↔ b.1 + Pi.single b.2 1 ∈ B c) :=
    fun c hc => by_contra fun hn => h ⟨c, hc, hn⟩
  constructor
  · rintro ⟨c, hc, hx⟩
    exact ⟨c, hc, (h' c hc).mp hx⟩
  · rintro ⟨c, hc, hx⟩
    exact ⟨c, hc, (h' c hc).mpr hx⟩

theorem crossingOf_card_biUnion_le {ι : Type*} [DecidableEq ι] (𝒞 : Finset ι)
    (B : ι → Finset (Torus d n)) :
    (crossingOf (𝒞.biUnion B)).card ≤ ∑ c ∈ 𝒞, (crossingOf (B c)).card :=
  (card_le_card (crossingOf_biUnion_subset 𝒞 B)).trans card_biUnion_le

section OneD

variable {S c : ℕ}

omit [NeZero n] in
theorem inCube1_edge_up {z : ZMod n} (h : InCube1 n S c z) (h' : ¬ InCube1 n S c (z + 1)) :
    z = ((c + (S - 1) : ℕ) : ZMod n) := by
  obtain ⟨t, ht, rfl⟩ := h
  by_cases h1 : t + 1 < S
  · exact absurd ⟨t + 1, h1, by push_cast; ring⟩ h'
  · have : t = S - 1 := by omega
    rw [this]

omit [NeZero n] in
theorem inCube1_edge_down {z : ZMod n} (h : ¬ InCube1 n S c z) (h' : InCube1 n S c (z + 1)) :
    z = ((c : ℕ) : ZMod n) - 1 := by
  obtain ⟨t, ht, e⟩ := h'
  cases t with
  | zero =>
    push_cast at e
    linear_combination e
  | succ t' =>
    exact absurd ⟨t', by omega, by push_cast at e ⊢; linear_combination e⟩ h

end OneD

/-- The face `{x : x_μ = z₀, x_i ∈ [c_i, c_i + S) for i ≠ μ}`. -/
noncomputable def cubeFace (S : ℕ) (c : Fin d → ℕ) (μ : Fin d) (z₀ : ZMod n) :
    Finset (Torus d n) := by
  classical
  exact Finset.univ.filter fun x => x μ = z₀ ∧ ∀ i, i ≠ μ → InCube1 n S (c i) (x i)

theorem mem_cubeFace {S : ℕ} {c : Fin d → ℕ} {μ : Fin d} {z₀ : ZMod n} {x : Torus d n} :
    x ∈ cubeFace S c μ z₀ ↔ x μ = z₀ ∧ ∀ i, i ≠ μ → InCube1 n S (c i) (x i) := by
  classical
  simp [cubeFace]

theorem card_cubeFace_le (S : ℕ) (c : Fin d → ℕ) (μ : Fin d) (z₀ : ZMod n) :
    (cubeFace S c μ z₀).card ≤ S ^ (d - 1) := by
  classical
  let I : Fin d → Finset (ZMod n) := fun i =>
    if i = μ then {z₀} else (range S).image fun t => ((c i + t : ℕ) : ZMod n)
  have hsub : cubeFace S c μ z₀ ⊆ Fintype.piFinset I := by
    intro x hx
    rw [mem_cubeFace] at hx
    rw [Fintype.mem_piFinset]
    intro i
    by_cases hi : i = μ
    · subst hi; simp [I, hx.1]
    · obtain ⟨t, ht, e⟩ := hx.2 i hi
      simp only [I, hi, ite_false, mem_image, mem_range]
      exact ⟨t, ht, e.symm⟩
  refine (card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  have hle : ∀ i, (I i).card ≤ if i = μ then 1 else S := by
    intro i
    by_cases hi : i = μ
    · simp [I, hi]
    · simp only [I, hi, ite_false]
      exact card_image_le.trans (by simp)
  refine (Finset.prod_le_prod fun i _ => hle i).trans (le_of_eq ?_)
  rw [← Finset.mul_prod_erase univ _ (mem_univ μ)]
  simp only [ite_true, one_mul]
  rw [Finset.prod_congr rfl (g := fun _ => S) (fun i hi => by simp [(Finset.ne_of_mem_erase hi)])]
  simp [Finset.card_erase_of_mem]

/-- (T1) A cube of side `s` has at most `2 d s^(d-1)` crossing bonds (also when it wraps around
the whole torus, where there are none). -/
theorem crossing_card_box_le (s : ℕ) (c : Fin d → ℕ) :
    (crossingOf (cubeSet n s c)).card ≤ 2 * d * s ^ (d - 1) := by
  classical
  rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := (univ : Finset (Fin d)))
    (fun _ _ => mem_univ _)]
  have hfib : ∀ μ : Fin d, ((crossingOf (cubeSet n s c)).filter fun b => b.2 = μ).card ≤
      2 * s ^ (d - 1) := by
    intro μ
    have hsub : ((crossingOf (cubeSet n s c)).filter fun b => b.2 = μ) ⊆
        (cubeFace s c μ (((c μ + (s - 1) : ℕ)) : ZMod n) ∪
          cubeFace s c μ ((c μ : ℕ) - 1 : ZMod n)).image fun x => (x, μ) := by
      intro b hb
      rw [mem_filter, mem_crossingOf] at hb
      obtain ⟨hb, rfl⟩ := hb
      obtain ⟨x, μ⟩ := b
      simp only at hb ⊢
      have hadd : ∀ i, (x + Pi.single μ 1 : Torus d n) i = if i = μ then x μ + 1 else x i := by
        intro i
        by_cases hi : i = μ
        · subst hi; simp
        · simp [hi]
      simp only [mem_cubeSet] at hb
      simp only [mem_image, mem_union, mem_cubeFace, Prod.mk.injEq, and_true, exists_eq_right]
      by_cases hx : ∀ i, InCube1 n s (c i) (x i)
      · have hx' : ¬ ∀ i, InCube1 n s (c i) ((x + Pi.single μ 1 : Torus d n) i) := fun h => hb ⟨fun _ => h, fun _ => hx⟩
        push Not at hx'
        obtain ⟨i, hi⟩ := hx'
        have hiμ : i = μ := by
          by_contra hne
          rw [hadd] at hi; simp only [hne, ↓reduceIte] at hi
          exact hi (hx i)
        subst hiμ
        rw [hadd] at hi; simp only [↓reduceIte] at hi
        exact Or.inl ⟨inCube1_edge_up (hx i) hi, fun j hj => hx j⟩
      · have hy : ∀ i, InCube1 n s (c i) ((x + Pi.single μ 1 : Torus d n) i) := by
          by_contra hy
          exact hb ⟨fun h => absurd h hx, fun h => absurd h hy⟩ |>.elim
        push Not at hx
        obtain ⟨i, hi⟩ := hx
        have hiμ : i = μ := by
          by_contra hne
          have := hy i
          rw [hadd] at this; simp only [hne, ↓reduceIte] at this
          exact hi this
        subst hiμ
        have h2 := hy i
        rw [hadd] at h2; simp only [↓reduceIte] at h2
        refine Or.inr ⟨inCube1_edge_down hi h2, fun j hj => ?_⟩
        have := hy j
        rw [hadd] at this; simpa [hj] using this
    refine (card_le_card hsub).trans (card_image_le.trans ((card_union_le _ _).trans ?_))
    have := card_cubeFace_le (n := n) s c μ (((c μ + (s - 1) : ℕ)) : ZMod n)
    have := card_cubeFace_le (n := n) s c μ ((c μ : ℕ) - 1 : ZMod n)
    omega
  calc ∑ μ : Fin d, ((crossingOf (cubeSet n s c)).filter fun b => b.2 = μ).card
      ≤ ∑ _μ : Fin d, 2 * s ^ (d - 1) := Finset.sum_le_sum fun μ _ => hfib μ
    _ = 2 * d * s ^ (d - 1) := by
        simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
        ring

/-- (T2) A union of at most `ncube` cubes of side `s`. -/
theorem crossingOf_card_cubes_le (s : ℕ) (𝒞 : Finset (Fin d → ℕ)) :
    (crossingOf (𝒞.biUnion fun c => cubeSet n s c)).card ≤ 𝒞.card * (2 * d * s ^ (d - 1)) := by
  refine (crossingOf_card_biUnion_le 𝒞 _).trans ?_
  calc ∑ c ∈ 𝒞, (crossingOf (cubeSet n s c)).card ≤ ∑ _c ∈ 𝒞, 2 * d * s ^ (d - 1) :=
        Finset.sum_le_sum fun c _ => crossing_card_box_le s c
    _ = _ := by simp

end Finset

/-- `Region.crossing` is `crossingOf` of the sites. -/
theorem Region.crossing_eq {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    {G : GeneratingSet d L N₀ K ϱ} (D : Region G) : D.crossing = crossingOf D.sites := rfl

/-- (T3) The sharp crossing count of a region that is a union of at most `ncube` cubes of side
`s`. -/
theorem Region.card_crossing_le_cubes {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    {G : GeneratingSet d L N₀ K ϱ} (D : Region G) {s ncube : ℕ} (𝒞 : Finset (Fin d → ℕ))
    (hU : D.sites = 𝒞.biUnion fun c => cubeSet (N₀ * L ^ K) s c) (hc : 𝒞.card ≤ ncube) :
    D.crossing.card ≤ ncube * (2 * d * s ^ (d - 1)) := by
  rw [Region.crossing_eq, hU]
  exact (crossingOf_card_cubes_le s 𝒞).trans (Nat.mul_le_mul_right _ hc)




section Arith

/-- The exponent arithmetic of the wall term: `L^d (M L^k)^{d-1} L^{-k} L^{-(k+1)(d-2)} = M^{d-1} L²`
for `d = e + 2`. -/
theorem wall_exponent_arith (M Lr k e : ℕ) (hL : 0 < Lr) :
    (Lr : ℝ) ^ (e + 2) * ((M : ℝ) * (Lr : ℝ) ^ k) ^ (e + 1) / (Lr : ℝ) ^ k /
        (Lr : ℝ) ^ ((k + 1) * e) = (M : ℝ) ^ (e + 1) * (Lr : ℝ) ^ 2 := by
  have h0 : (Lr : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have h1 : (Lr : ℝ) ^ (e + 2) * ((Lr : ℝ) ^ k) ^ (e + 1) =
      (Lr : ℝ) ^ ((k + 1) * e) * (Lr : ℝ) ^ k * (Lr : ℝ) ^ 2 := by
    rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [mul_pow, div_div, div_eq_iff (by positivity)]
  calc (Lr : ℝ) ^ (e + 2) * ((M : ℝ) ^ (e + 1) * ((Lr : ℝ) ^ k) ^ (e + 1))
      = (M : ℝ) ^ (e + 1) * ((Lr : ℝ) ^ (e + 2) * ((Lr : ℝ) ^ k) ^ (e + 1)) := by ring
    _ = _ := by rw [h1]; ring

/-- The wall term with the sharp crossing count. -/
theorem cubes_wall_arith (M Lr k e : ℕ) (hL : 0 < Lr) (Kb βq m δ₀ n : ℝ) :
    Kb * (βq / (Lr : ℝ) ^ ((k + 1) * e)) * m *
        (((Lr : ℝ) ^ (e + 2) * n) *
          (2 * ((e + 2 : ℕ) : ℝ) * ((M : ℝ) * (Lr : ℝ) ^ k) ^ (e + 1)) * (δ₀ / (Lr : ℝ) ^ k)) =
      2 * ((e + 2 : ℕ) : ℝ) * (M : ℝ) ^ (e + 1) * (Lr : ℝ) ^ 2 * Kb * βq * m * δ₀ * n := by
  have h := wall_exponent_arith M Lr k e hL
  have h0 : (Lr : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have h2 : (Lr : ℝ) ^ ((k + 1) * e) ≠ 0 := pow_ne_zero _ h0
  have h3 : (Lr : ℝ) ^ k ≠ 0 := pow_ne_zero _ h0
  rw [div_div, div_eq_iff (mul_ne_zero h3 h2)] at h
  field_simp
  linear_combination (2 * ((e + 2 : ℕ) : ℝ) * Kb * βq * m * δ₀ * n) * h

/-- The chord term (as in `cube_scale_arith`). -/
theorem cubes_chord_arith (M Lr k e : ℕ) (hL : 0 < Lr) (Kb βq m n : ℝ) :
    (1 / 2) * ((2 * ((e + 2 : ℕ) : ℝ) + 4) * ((M : ℝ) ^ (e + 2) * (Lr : ℝ) ^ ((k + 1) * (e + 2))) /
        ((Lr : ℝ) ^ k) ^ 2) * Kb ^ 2 * (βq / (Lr : ℝ) ^ ((k + 1) * e)) * m ^ 2 * n =
      ((e + 2 : ℕ) + 2 : ℝ) * (M : ℝ) ^ (e + 2) * (Lr : ℝ) ^ 2 * Kb ^ 2 * βq * m ^ 2 * n := by
  have h0 : (Lr : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have h1 : (k + 1) * (e + 2) = (k + 1) * e + 2 * k + 2 := by ring
  rw [h1, pow_add, pow_add]
  push_cast
  field_simp
  ring

end Arith

section MassChange

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The region bound for the mass change with an arbitrary bound `Ncross` on the number of
crossing bonds: `massChange_region_bound` with the crude count replaced by `Ncross`. -/
theorem massChange_region_bound_ncross (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
        (a : ℕ → ℝ) (μ m Bh δ₀ : ℝ) (D : BgData G N)
        {φ0 φm : G.Ω 1 × Fin N → ℂ} {α0 αm : G.Ω 1 → ℂ} (R : Region G)
        (β ℓ₀ Nsite n Ncross : ℝ),
        IsEL G a 0 D φ0 α0 → IsEL G a μ D φm αm →
        BgBounds G D φ0 α0 δ₀ → BgBounds G D φm αm δ₀ →
        GreenSetting G a 0 → Dec2.OpSetting G a 0 →
        0 ≤ δ₀ → δ₀ ≤ min (deltaStar d L N) δw → 2 * δ₀ ≤ c6 d L N →
        0 ≤ m → 0 ≤ Bh → m * Bh ≤ min (deltaStar d L N) δw →
        0 ≤ μ → (∀ x : G.Ω 1, μ * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 ≤ m) →
        (∀ (x : G.Ω 1) (i : Fin N), ‖φm (x, i) - D.h x i‖ ≤ Bh) →
        (∀ x : G.Ω 1, vn (fun i => φ0 (x, i)) ≤ 3 / 2) →
        0 ≤ β → 0 < ℓ₀ → (∀ x ∈ R.sites, ℓ₀ ≤ G.spacing x) → μ ≤ 1 / ℓ₀ ^ 2 → δ₀ ≤ 1 →
        (R.sites.card : ℝ) ≤ Nsite * n → (R.crossing.card : ℝ) ≤ Ncross →
        β * ‖actionRegionC R a μ D φ0 - actionRegionC R a μ D φm‖ ≤
          (1 / 2) * ((2 * d + 4) * Nsite / ℓ₀ ^ 2) * ((Real.sqrt N * Kw) * Bh) ^ 2 * β * m ^ 2 * n +
            (Real.sqrt N * Kw) * Bh * β * m * (Ncross * (δ₀ / ℓ₀)) := by
  obtain ⟨Kw, δw, hK, hδ, H⟩ := massChange_sameData_response N hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₁ m₁ K _ ϱ G a μ m Bh δ₀ D φ0 φm α0 αm R β ℓ₀ Nsite n Ncross h0 hm b0 bm hG hO hδ₀ hδs h2
    hm0 hBh0 hmB hμ hμℓ hB hφ hβ hℓ hℓR hμ1 hδ1 hcard hNc
  obtain ⟨⟨hSm, hSup⟩, hresp⟩ := H a μ m Bh δ₀ D h0 hm b0 bm hG hO hδ₀ hδs h2 hm0 hBh0 hmB hμ hμℓ
    hB hφ
  have hV : 0 ≤ Kw * (m * Bh) := by positivity
  have hW0 : 0 ≤ (Real.sqrt N * Kw) * Bh * m := by positivity
  have hbond : ∀ (x : Torus d (N₁ * L ^ m₁ * L ^ K)) (μ' : Fin d),
      (x ∈ R.sites ∨ x + Pi.single μ' 1 ∈ R.sites) →
        vnorm (fun i => wExt D D φm φ0 (x + Pi.single μ' 1) i - wExt D D φm φ0 x i)
          ≤ (Real.sqrt N * Kw) * Bh * m / ℓ₀ := fun x μ' hx =>
    (massChange_hbond_of_supBounds R D hV hℓ hℓR hSup x μ' hx).trans (le_of_eq (by ring))
  exact massChange_region_bound_of_response R hm h0.2 (β := β) (m := m) (Km := Real.sqrt N * Kw)
    (Bh := Bh) (ℓ₀ := ℓ₀) (δ₀ := δ₀) (Nsite := Nsite) (n := n) (ρ := δ₀ / ℓ₀)
    (Ncross := Ncross) hβ hW0 hℓ (div_nonneg hδ₀ hℓ.le)
    (massChange_hgrad_of_bgBounds R hδ₀ hℓ hℓR bm) hresp hbond
    (massChange_hcoef_of_weights R hℓ hO.weights hℓR)
    (massChange_hα_of_small R hℓ hℓR bm.alpha) hδ₀ hδ1 hμ hμ1 hcard hNc

/-- **The region bound at scale `q = k + 1` with the scale-uniform wall constant**
(MASS-RESPONSE (2.4)-(2.5)).  `d = e + 2`, `ℓ₀ = L^k`, `β = β_q / L^{(k+1)(d-2)}`,
`Km = √N · Kw`, `Kb = Km Bh`.  The region is a union of at most `L^d n` cubes `cubeSet _ (M L^k) c`
(the scale-`k` cubes in `n` scale-`(k+1)` cubes), and has at most `M^d L^{(k+1)d} n` sites.  The
constants are `C_D = (d+2) M^d L² Kb²` and `C_W = 2 d M^{d-1} L² Kb`, with no power of `L^k`.  The
radius `δ₀` is the `BgBounds` radius of the massive background; with `δ₀ = G_∇ δ_k` the note's
`C_W = 2 d M^{d-1} L² Km Bh G_∇` is `C_W` times `G_∇`. -/
theorem massChange_region_bound_cubes (N e : ℕ) (hd : 3 ≤ e + 2) (hL : 3 ≤ L) (M k : ℕ) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet (e + 2) L (N₁ * L ^ m₁) K ϱ}
        (a : ℕ → ℝ) (μ m Bh δ₀ : ℝ) (D : BgData G N)
        {φ0 φm : G.Ω 1 × Fin N → ℂ} {α0 αm : G.Ω 1 → ℂ} (R : Region G) (βq n : ℝ),
        IsEL G a 0 D φ0 α0 → IsEL G a μ D φm αm →
        BgBounds G D φ0 α0 δ₀ → BgBounds G D φm αm δ₀ →
        GreenSetting G a 0 → Dec2.OpSetting G a 0 →
        0 ≤ δ₀ → δ₀ ≤ min (deltaStar (e + 2) L N) δw → 2 * δ₀ ≤ c6 (e + 2) L N →
        0 ≤ m → 0 ≤ Bh → m * Bh ≤ min (deltaStar (e + 2) L N) δw →
        0 ≤ μ → (∀ x : G.Ω 1, μ * G.spacing (x : CTorus (e + 2) L N₁ m₁ K) ^ 2 ≤ m) →
        (∀ (x : G.Ω 1) (i : Fin N), ‖φm (x, i) - D.h x i‖ ≤ Bh) →
        (∀ x : G.Ω 1, vn (fun i => φ0 (x, i)) ≤ 3 / 2) →
        0 ≤ βq → (∀ x ∈ R.sites, (L : ℝ) ^ k ≤ G.spacing x) → μ ≤ 1 / ((L : ℝ) ^ k) ^ 2 →
        δ₀ ≤ 1 →
        (R.sites.card : ℝ) ≤ (M : ℝ) ^ (e + 2) * (L : ℝ) ^ ((k + 1) * (e + 2)) * n →
        (∃ 𝒞 : Finset (Fin (e + 2) → ℕ),
          R.sites = 𝒞.biUnion (fun c => cubeSet (N₁ * L ^ m₁ * L ^ K) (M * L ^ k) c) ∧
            (𝒞.card : ℝ) ≤ (L : ℝ) ^ (e + 2) * n) →
        (βq / (L : ℝ) ^ ((k + 1) * e)) *
            ‖actionRegionC R a μ D φ0 - actionRegionC R a μ D φm‖ ≤
          (((e + 2 : ℕ) + 2 : ℝ) * (M : ℝ) ^ (e + 2) * (L : ℝ) ^ 2 *
              ((Real.sqrt N * Kw) * Bh) ^ 2 * βq * m ^ 2 +
            2 * ((e + 2 : ℕ) : ℝ) * (M : ℝ) ^ (e + 1) * (L : ℝ) ^ 2 *
              ((Real.sqrt N * Kw) * Bh) * βq * m * δ₀) * n := by
  obtain ⟨Kw, δw, hK, hδ, H⟩ := massChange_region_bound_ncross (d := e + 2) N hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₁ m₁ K _ ϱ G a μ m Bh δ₀ D φ0 φm α0 αm R βq n h0 hm b0 bm hG hO hδ₀ hδs h2 hm0
    hBh0 hmB hμ hμℓ hB hφ hβ hℓR hμ1 hδ1 hcard hcubes
  obtain ⟨𝒞, hU, hc⟩ := hcubes
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  have hβ' : 0 ≤ βq / (L : ℝ) ^ ((k + 1) * e) := by positivity
  have hNc : (R.crossing.card : ℝ) ≤
      ((L : ℝ) ^ (e + 2) * n) * (2 * ((e + 2 : ℕ) : ℝ) * ((M : ℝ) * (L : ℝ) ^ k) ^ (e + 1)) := by
    have h1 : R.crossing.card ≤ 𝒞.card * (2 * (e + 2) * (M * L ^ k) ^ (e + 2 - 1)) :=
      R.card_crossing_le_cubes 𝒞 hU le_rfl
    have h1' : (R.crossing.card : ℝ) ≤
        (𝒞.card : ℝ) * (2 * ((e + 2 : ℕ) : ℝ) * ((M : ℝ) * (L : ℝ) ^ k) ^ (e + 1)) := by
      exact_mod_cast h1
    refine h1'.trans (mul_le_mul_of_nonneg_right hc (by positivity))
  have := H a μ m Bh δ₀ D R (βq / (L : ℝ) ^ ((k + 1) * e)) ((L : ℝ) ^ k)
    ((M : ℝ) ^ (e + 2) * (L : ℝ) ^ ((k + 1) * (e + 2)))  n
    (((L : ℝ) ^ (e + 2) * n) * (2 * ((e + 2 : ℕ) : ℝ) * ((M : ℝ) * (L : ℝ) ^ k) ^ (e + 1)))
    h0 hm b0 bm hG hO hδ₀ hδs h2 hm0 hBh0 hmB hμ hμℓ hB hφ hβ' (by positivity) hℓR hμ1 hδ1
    hcard hNc
  refine this.trans (le_of_eq ?_)
  rw [cubes_chord_arith M L k e (by omega), cubes_wall_arith M L k e (by omega)]
  ring

end MassChange

section Example

/-- (T5) Non-vacuity at the `Finset` level: in the circle `ℤ/8` (`d = 1`) the cube of side `3`
has a nonempty crossing set of size at most `2 = 2 d s^(d-1)`, while the crude bound
`2 d |B| = 6` is strictly worse. -/
theorem crossing_cubes_example :
    ∃ B : Finset (Torus 1 8), B = cubeSet 8 3 (fun _ => 0) ∧ (crossingOf B).Nonempty ∧
      (crossingOf B).card ≤ 2 * 1 * 3 ^ (1 - 1) ∧ 2 * 1 * 3 ^ (1 - 1) < 2 * 1 * B.card := by
  have hmem : ∀ j : ℕ, j < 3 → (fun _ => (j : ZMod 8) : Torus 1 8) ∈ cubeSet 8 3 (fun _ : Fin 1 => 0) :=
    fun j hj => by
      rw [mem_cubeSet]
      exact fun _ => ⟨j, hj, by simp⟩
  have hcard : 3 ≤ (cubeSet 8 3 (fun _ : Fin 1 => (0 : ℕ)) : Finset (Torus 1 8)).card := by
    have : (({fun _ => 0, fun _ => 1, fun _ => 2} : Finset (Torus 1 8))).card = 3 := by decide
    have hsub : ({fun _ => 0, fun _ => 1, fun _ => 2} : Finset (Torus 1 8)) ⊆
        cubeSet 8 3 (fun _ : Fin 1 => (0 : ℕ)) := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · simpa using hmem 0 (by norm_num)
      · simpa using hmem 1 (by norm_num)
      · simpa using hmem 2 (by norm_num)
    have := card_le_card hsub
    omega
  refine ⟨_, rfl, ?_, crossing_card_box_le 3 _, by omega⟩
  refine ⟨((fun _ => 2 : Torus 1 8), (0 : Fin 1)), ?_⟩
  rw [mem_crossingOf]
  have h2 : (fun _ => (2 : ZMod 8) : Torus 1 8) ∈ cubeSet 8 3 (fun _ : Fin 1 => (0 : ℕ)) := by
    simpa using hmem 2 (by norm_num)
  intro h
  have h3 := h.mp h2
  rw [mem_cubeSet] at h3
  obtain ⟨t, ht, e⟩ := h3 0
  simp at e
  have : ((3 : ℕ) : ZMod 8) = ((t : ℕ) : ZMod 8) := by
    push_cast; rw [← e]; norm_num
  have h4 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 this
  omega

end Example

end Balaban.LargeField.ActionConv
