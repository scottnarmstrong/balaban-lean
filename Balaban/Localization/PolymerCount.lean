/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.TreeLengthCov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (GM3) and (GM4) for the concrete construction (LOCALIZATION.md §4.2)

* `card_cubeBases_cell`: a `π_n`-cube of side `a_n = L ^ (n + m₀ + m₁)` contains exactly
  `(L ^ m₀) ^ d = (M / M₁) ^ d` parameter cubes (aligned bases of side `L ^ (n + m₁)`).
* `gm3`: the Peierls count for the families `𝒞` with `Y[𝒞] = Y`, an instance of the landed
  `peierls_count_layers` with `G₀ = (2L+1)^d` (from `gm1`) and `A' = (L^{m₀})^d`.
* `gm4`: the exponent inequality, combining the covering `gm2` (version 3) with the landed `exponent_inequality`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Finset

section Count

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}

theorem natT_injOn {n : ℕ} [NeZero n] {x x' : Fin d → ℕ} (hx : ∀ μ, x μ < n) (hx' : ∀ μ, x' μ < n)
    (h : (natT x : Torus d n) = natT x') : x = x' := by
  funext μ
  have := congrFun h μ
  simp only [natT_apply] at this
  rw [ZMod.natCast_eq_natCast_iff'] at this
  rwa [Nat.mod_eq_of_lt (hx μ), Nat.mod_eq_of_lt (hx' μ)] at this

open Classical in
/-- A `π_n`-cube contains exactly `(L ^ m₀) ^ d` bases of parameter cubes. -/
theorem card_cubeBases_cell (hN : L ^ m₀ ∣ N₁) {n : ℕ} (hnK : n ≤ K)
    {b : CTorus d L N₁ m₁ K} (hb : Aligned (cellSide L m₀ m₁ n) b) :
    ((Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
      (fun y => CubeBase m₁ n y ∧ y ∈ box b (cellSide L m₀ m₁ n))).card = (L ^ m₀) ^ d := by
  set a := cellSide L m₀ m₁ n with ha
  set s := L ^ (n + m₁) with hs
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hs0 : 0 < s := pow_pos hL0 _
  have has : a = s * L ^ m₀ := by
    rw [ha, hs]; unfold cellSide
    rw [show n + m₀ + m₁ = (n + m₁) + m₀ by ring, pow_add]
  have haN : a ∣ (N₁ * L ^ m₁) * L ^ K := cellSide_dvd (K := K) (m₁ := m₁) hN hnK
  have hsN : s ∣ (N₁ * L ^ m₁) * L ^ K := (Dvd.intro _ has.symm).trans haN
  have hbs : Aligned s b := fun μ => by
    have := hb μ
    rw [← Nat.mod_mod_of_dvd _ (Dvd.intro _ has.symm), this]; simp
  have hNpos : 0 < (N₁ * L ^ m₁) * L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  have haleN : a ≤ (N₁ * L ^ m₁) * L ^ K := Nat.le_of_dvd hNpos haN
  let g : (Fin d → ℕ) → CTorus d L N₁ m₁ K := fun u => b + natT (fun μ => s * u μ)
  have hset : (Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter
      (fun y => CubeBase m₁ n y ∧ y ∈ box b a) =
      (Fintype.piFinset fun _ : Fin d => Finset.range (L ^ m₀)).image g := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Fintype.mem_piFinset, Finset.mem_range]
    constructor
    · rintro ⟨hcb, w, hw, rfl⟩
      have hws : ∀ μ, w μ % s = 0 := fun μ => by
        have h1 := mod_of_aligned_add hsN hbs (w := w) μ
        rw [← h1]; exact hcb μ
      refine ⟨fun μ => w μ / s, fun μ => ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hs0]
        have := hw μ
        rwa [has, mul_comm] at this
      · simp only [g]
        congr 2
        funext μ
        exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hws μ))
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun μ => ?_, fun μ => s * u μ, fun μ => ?_, rfl⟩
      · show ((g u) μ).val % s = 0
        have h1 := mod_of_aligned_add hsN hbs (w := fun μ => s * u μ) μ
        rw [show g u = b + natT (fun μ => s * u μ) from rfl, h1]
        exact Nat.mul_mod_right _ _
      · rw [has]
        exact Nat.mul_lt_mul_of_pos_left (hu μ) hs0
  rw [hset, Finset.card_image_of_injOn, Fintype.card_piFinset]
  · simp
  · intro u hu u' hu' h
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hu hu'
    simp only [Finset.mem_range] at hu hu'
    have h1 : (natT (fun μ => s * u μ) : CTorus d L N₁ m₁ K) = natT (fun μ => s * u' μ) :=
      add_left_cancel h
    have hlt : ∀ (v : Fin d → ℕ), (∀ μ, v μ < L ^ m₀) → ∀ μ, s * v μ <
        (N₁ * L ^ m₁) * L ^ K := fun v hv μ =>
      lt_of_lt_of_le (by rw [has]; exact Nat.mul_lt_mul_of_pos_left (hv μ) hs0) haleN
    have := natT_injOn (hlt u hu) (hlt u' hu') h1
    funext μ
    exact Nat.eq_of_mul_eq_mul_left hs0 (congrFun this μ)

/-- Layers are unions of `π_n`-cubes: the cube of an aligned base of layer `n` lies in `Λ_n`. -/
theorem box_subset_layer_of_base (hU : LayerUnion G m₀) (hN : L ^ m₀ ∣ N₁) {n : ℕ} (h1 : 1 ≤ n)
    (hnK : n ≤ K) {b : CTorus d L N₁ m₁ K} (hb : Aligned (cellSide L m₀ m₁ n) b)
    (hbl : b ∈ G.layer n) : box b (cellSide L m₀ m₁ n) ⊆ ↑(G.layer n) := by
  have ha0 := cellSide_pos (L := L) m₀ m₁ n
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hnK
  obtain ⟨b'', hb''al, hbm, hsub⟩ := hU n h1 hnK b hbl
  have := cell_subset_cube hdvd ha0 hb''al hbm
  rw [cbase_eq_of_mem_box hdvd hb (mem_box_self b ha0)] at this
  exact this.trans hsub

/-- The aligned bases of the `π_n`-cubes of `Y ∖ X₁` in layer `n`. -/
noncomputable def Ybases (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)
    (X₁ Y : Set (CTorus d L N₁ m₁ K)) (n : ℕ) : Finset (CTorus d L N₁ m₁ K) := by
  classical
  exact Finset.univ.filter fun b => Aligned (cellSide L m₀ m₁ n) b ∧ b ∈ Y ∧ b ∉ X₁ ∧
    b ∈ G.layer n

/-- The parameter cubes of layer `n` lying in the `π_n`-cubes of `Y ∖ X₁`. -/
noncomputable def paramSet (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)
    (X₁ Y : Set (CTorus d L N₁ m₁ K)) (n : ℕ) : Finset ↥(cubeIdx G) := by
  classical
  exact Finset.univ.filter fun i => i.1.1 = n ∧
    cbase (cellSide L m₀ m₁ n) i.1.2 ∈ Ybases G m₀ X₁ Y n

theorem mem_Ybases {X₁ Y : Set (CTorus d L N₁ m₁ K)} {n : ℕ} {b : CTorus d L N₁ m₁ K} :
    b ∈ Ybases G m₀ X₁ Y n ↔ Aligned (cellSide L m₀ m₁ n) b ∧ b ∈ Y ∧ b ∉ X₁ ∧ b ∈ G.layer n := by
  classical
  simp [Ybases]

theorem mem_paramSet {X₁ Y : Set (CTorus d L N₁ m₁ K)} {n : ℕ} {i : ↥(cubeIdx G)} :
    i ∈ paramSet G m₀ X₁ Y n ↔ i.1.1 = n ∧
      cbase (cellSide L m₀ m₁ n) i.1.2 ∈ Ybases G m₀ X₁ Y n := by
  classical
  simp [paramSet]

/-- Each `π_n`-cube of `Y ∖ X₁` carries `(M/M₁)^d` parameter cubes. -/
theorem card_paramSet (hU : LayerUnion G m₀) (hN : L ^ m₀ ∣ N₁) (X₁ Y : Set (CTorus d L N₁ m₁ K))
    {n : ℕ} (h1 : 1 ≤ n) (hnK : n ≤ K) :
    (paramSet G m₀ X₁ Y n).card = (L ^ m₀) ^ d * (Ybases G m₀ X₁ Y n).card := by
  classical
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hnK
  have hsum := Finset.card_eq_sum_card_fiberwise (s := paramSet G m₀ X₁ Y n)
    (t := Ybases G m₀ X₁ Y n) (f := fun i : ↥(cubeIdx G) => cbase (cellSide L m₀ m₁ n) i.1.2)
    (fun i hi => (mem_paramSet.1 hi).2)
  rw [hsum]
  have hfib : ∀ b ∈ Ybases G m₀ X₁ Y n,
      ((paramSet G m₀ X₁ Y n).filter
        (fun i : ↥(cubeIdx G) => cbase (cellSide L m₀ m₁ n) i.1.2 = b)).card = (L ^ m₀) ^ d := by
    intro b hb
    obtain ⟨hbal, hbY, hbX, hbl⟩ := mem_Ybases.1 hb
    rw [← card_cubeBases_cell (K := K) (m₁ := m₁) hN hnK hbal]
    refine Finset.card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨hi1, hi2⟩ := hi
      obtain ⟨hi3, -⟩ := mem_paramSet.1 hi1
      obtain ⟨-, -, hbase⟩ := (mem_cubeIdx G).1 i.2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by rw [hi3] at hbase; exact hbase, ?_⟩
      rw [← hi2]
      exact mem_box_cbase (cellSide_pos m₀ m₁ n) _
    · intro i hi i' hi' h
      rw [Finset.mem_filter] at hi hi'
      have e1 := (mem_paramSet.1 hi.1).1
      have e2 := (mem_paramSet.1 hi'.1).1
      exact Subtype.ext (Prod.ext (e1.trans e2.symm) h)
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨hycb, hyb⟩ := hy
      have hyl : y ∈ G.layer n := by
        have := box_subset_layer_of_base hU hN h1 hnK hbal hbl hyb
        exact Finset.mem_coe.1 this
      have hmem : (n, y) ∈ cubeIdx G := (mem_cubeIdx G).2 ⟨⟨h1, hnK⟩, hyl, hycb⟩
      have hcb : cbase (cellSide L m₀ m₁ n) y = b := cbase_eq_of_mem_box hdvd hbal hyb
      refine ⟨⟨(n, y), hmem⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨mem_paramSet.2 ⟨rfl, ?_⟩, hcb⟩
      show cbase (cellSide L m₀ m₁ n) y ∈ Ybases G m₀ X₁ Y n
      rw [hcb]; exact hb
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]

/-- The base of the cell of a parameter cube disjoint from `X₁` is not in `X₁` (`X₁` is a union of
`π_K`-cubes inside `Λ_K`). -/
theorem base_notMem_X₁ {X₁ : Set (CTorus d L N₁ m₁ K)} (hS : PolySetup G m₀ X₁)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) (hdisj : Disjoint (Pset m₁ q) X₁) :
    cbase (cellSide L m₀ m₁ q.1) q.2 ∉ X₁ := by
  intro hbX
  obtain ⟨⟨h1, hqK⟩, -, -⟩ := (mem_cubeIdx G).1 hq
  have hbD := mem_Dsites_of_mem_Dbases (cbase_mem_Dbases hS.hU hS.hN hq)
  have hbl : cbase (cellSide L m₀ m₁ q.1) q.2 ∈ G.layer q.1 :=
    Finset.mem_coe.1 (Dsites_subset_layer q hbD)
  have hbK : cbase (cellSide L m₀ m₁ q.1) q.2 ∈ G.layer K := Finset.mem_coe.1 (hS.X₁_layer hbX)
  have hqK' : q.1 = K := by
    by_contra hne
    exact G.layer_disjoint h1 hqK (by omega) le_rfl hne hbl hbK
  obtain ⟨b', hb'al, hbm, hb'X⟩ := hS.X₁_cubes _ hbX
  have hcs : cellSide L m₀ m₁ K = cellSide L m₀ m₁ q.1 := by rw [hqK']
  rw [hcs] at hb'al hbm hb'X
  have ha0 := cellSide_pos (L := L) m₀ m₁ q.1
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hS.hN hqK
  have hsub := cell_subset_cube hdvd ha0 hb'al hbm
  rw [cbase_eq_of_mem_box hdvd (aligned_cbase _) (mem_box_self _ ha0)] at hsub
  have hqX : q.2 ∈ X₁ :=
    hb'X (hsub (Pset_subset_cellOf m₀ q (self_mem_Pset q)))
  exact Set.disjoint_left.1 hdisj (self_mem_Pset q) hqX

/-- **(GM3), the Peierls count.**  Let `𝔖` be a finite set of families `𝒞` of parameter cubes,
each disjoint from `X₁`, with `Y[𝒞] = Y`.  If `κ₂/2 ≥ 1` and `κ₂/2 ≥ log (G₀ A')` with
`G₀ = (2L+1)^d` and `A' = (M/M₁)^d = (L^{m₀})^d` (so `G₀ A'` is the `A` of the document), then
`∑_{𝒞 ∈ 𝔖} e^{-κ₂ |𝒞|} ≤ 1`. -/
theorem gm3 {X₁ : Set (CTorus d L N₁ m₁ K)} (hS : PolySetup G m₀ X₁)
    (Y : Set (CTorus d L N₁ m₁ K)) (𝔖 : Finset (Finset ↥(cubeIdx G)))
    (h𝔖 : ∀ C ∈ 𝔖, Ysites G m₀ (fun i : ↥(cubeIdx G) => i.1) X₁ C = Y ∧
      ∀ i ∈ C, Disjoint (Pset m₁ i.1) X₁)
    (κ₂ : ℝ) (h1 : 1 ≤ κ₂ / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ κ₂ / 2) :
    ∑ C ∈ 𝔖, Real.exp (-κ₂ * C.card) ≤ 1 := by
  classical
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  refine peierls_count_layers (Finset.Icc 1 K) (paramSet G m₀ X₁ Y)
    (fun n _ n' _ hne => ?_) (fun n => (Ybases G m₀ X₁ Y n).card) 𝔖
    (((2 * L + 1) ^ d : ℕ) : ℝ) (((L ^ m₀) ^ d : ℕ) : ℝ) κ₂ (by positivity) (by positivity)
    (fun n hn => ?_) (fun C hC => ?_) h1 hlog
  · rw [Function.onFun, Finset.disjoint_left]
    intro i hi hi'
    exact hne ((mem_paramSet.1 hi).1.symm.trans (mem_paramSet.1 hi').1)
  · obtain ⟨hn1, hnK⟩ := Finset.mem_Icc.1 hn
    rw [card_paramSet hS.hU hS.hN X₁ Y hn1 hnK]
    push_cast; ring
  · obtain ⟨hY, hdisj⟩ := h𝔖 C hC
    -- every member of `C` lies in the corresponding `paramSet`
    have hmem : ∀ i ∈ C, i ∈ paramSet G m₀ X₁ Y i.1.1 := by
      intro i hi
      obtain ⟨⟨h1', hqK⟩, -, -⟩ := (mem_cubeIdx G).1 i.2
      have hbD := mem_Dsites_of_mem_Dbases (cbase_mem_Dbases hS.hU hS.hN i.2)
      refine mem_paramSet.2 ⟨rfl, mem_Ybases.2 ⟨aligned_cbase _, ?_, ?_, ?_⟩⟩
      · rw [← hY]; exact Dsites_subset_Ysites (c := fun i : ↥(cubeIdx G) => i.1) hi hbD
      · exact base_notMem_X₁ hS i.2 (hdisj i hi)
      · exact Finset.mem_coe.1 (Dsites_subset_layer i.1 hbD)
    refine ⟨fun i hi => Finset.mem_biUnion.2 ⟨i.1.1, ?_, hmem i hi⟩, fun n hn => ?_⟩
    · obtain ⟨⟨h1', hqK⟩, -, -⟩ := (mem_cubeIdx G).1 i.2
      exact Finset.mem_Icc.2 ⟨h1', hqK⟩
    · obtain ⟨hn1, hnK⟩ := Finset.mem_Icc.1 hn
      have hfil : C ∩ paramSet G m₀ X₁ Y n = C.filter (fun i => i.1.1 = n) := by
        ext i
        simp only [Finset.mem_inter, Finset.mem_filter]
        constructor
        · rintro ⟨hi, hi'⟩; exact ⟨hi, (mem_paramSet.1 hi').1⟩
        · rintro ⟨hi, rfl⟩; exact ⟨hi, hmem i hi⟩
      rw [hfil]
      have hg := gm1 (G := G) (m₀ := m₀) (fun i : ↥(cubeIdx G) => i.1) hS.hN (fun i => i.2)
        (Finset.univ.filter (· ∈ X₁)) C n
      have hsub : Ybases G m₀ X₁ Y n ⊆
          (((Finset.univ.filter (· ∈ X₁)) ∪ C.biUnion fun i : ↥(cubeIdx G) =>
            Dbases G m₀ i.1) \ (Finset.univ.filter (· ∈ X₁))).filter
            (fun b => G.layerIndex b = n) := by
        intro b hb
        obtain ⟨hbal, hbY, hbX, hbl⟩ := mem_Ybases.1 hb
        rw [← hY] at hbY
        rcases hbY with hbY | hbY
        · exact absurd hbY hbX
        · obtain ⟨i, hi, hbD⟩ := Set.mem_iUnion₂.1 hbY
          obtain ⟨⟨h1', hqK⟩, -, -⟩ := (mem_cubeIdx G).1 i.2
          have hbi : b ∈ G.layer i.1.1 := Finset.mem_coe.1 (Dsites_subset_layer i.1 hbD)
          have hin : i.1.1 = n := by
            by_contra hne
            exact G.layer_disjoint h1' hqK hn1 hnK hne hbi hbl
          simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ,
            true_and, Finset.mem_biUnion]
          refine ⟨⟨Or.inr ⟨i, hi, ?_⟩, hbX⟩, G.layerIndex_eq hn1 hnK hbl⟩
          simp only [Dbases, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hin ▸ hbal, hbD⟩
      have := (Finset.card_le_card hsub).trans hg
      have h2 : (C.filter (fun i : ↥(cubeIdx G) => (i.1 : ℕ × CTorus d L N₁ m₁ K).1 = n)) =
          C.filter (fun i => i.1.1 = n) := rfl
      exact_mod_cast (by rw [h2] at this; exact this :
        (Ybases G m₀ X₁ Y n).card ≤ (2 * L + 1) ^ d * (C.filter (fun i => i.1.1 = n)).card)

end Count

/-! ### (GM4) -/

section Exponents

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ} {j : ℕ}
variable {X : Set (CTorus d L N₁ m₁ K)}

/-- **(GM4) for the covering tree lengths.**  For a connected family `𝒞`, with
`Δ = d^cov_j(X)` and `d̃ = d̃^cov_{k+1}(Y[𝒞])`,
`(κ₁ - 1)|𝒞| + (κ - 1)Δ ≥ (κ₁/2 - 1)|𝒞| + κ₀ Δ + 2 κ d̃`, if `L ≥ 3`, `κ ≥ 3κ₀ + 3`,
`κ₁ ≥ 4 d (2L+1)^d κ`.  Here `𝒦_X` realizes `d^cov_j(X)` (see `gm2`). -/
theorem gm4 {ι : Type*} [DecidableEq ι] {c : ι → ℕ × CTorus d L N₁ m₁ K} {𝒦X : Set (CTorus d L N₁ m₁ K)}
    (hS : CovSetup G m₀ j X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L) (hc : ∀ i, c i ∈ cubeIdx G)
    (C : Finset ι)
    (hconn : IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c (X1 G m₀ j 𝒦X)) C)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (κ κ₀ κ₁ : ℝ) (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁) :
    (κ₁ - 1) * C.card + (κ - 1) * treeLenCovOne m₀ j X ≥
      (κ₁ / 2 - 1) * C.card + κ₀ * treeLenCovOne m₀ j X +
        2 * κ * treeLenCov G m₀ (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) := by
  have h2 := gm2 hS hd hc C hconn hopt
  refine exponent_inequality d L (((2 * L + 1) ^ d : ℕ) : ℝ) κ κ₀ κ₁ C.card
    (treeLenCovOne m₀ j X) (treeLenCov G m₀ (Ysites G m₀ c (X1 G m₀ j 𝒦X) C))
    (by exact_mod_cast hL) hκ₀ hκ hκ₁ (Nat.cast_nonneg _)
    (treeLenCovOne_nonneg m₀ j X) ?_
  rw [div_eq_inv_mul]
  linarith

end Exponents

end Balaban.Localization
