/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusOn
public import Balaban.SmallField.IrrelTorusBoundId
public import Balaban.SmallField.RenormAnisoPathExists
public import Balaban.Polymer.IrrelTorusOnBox

/-!
# Paths of the placed polymer of a label in the box of ruling R15

For a polymer `X ∈ 𝒟_j` with centre `y` inside the box of `relBox` (half-side `⌊L^{m₀+m₁+k}/8⌋`
around `y`), the placed polymer `S = {unlift_j (x - y) : x ∈ X aligned}` of `ℤ^d` is connected by
unit steps, and every site of `S` is joined to the origin by a lattice path inside `S` with at most
`#S - 1` steps (`exists_latPath_of_relBox`).  In the box the centred block coordinates are the floor
quotients of the centred coordinates (`unlift_eq_ediv`), so a unit step of the torus inside `X`
is a unit step or no step of the placed sites, and the connectivity of `X` passes to `S`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Polymer.TwoTorusStep

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {j : ℕ}

/-- `(v + 1) / q` is `v / q` or `v / q + 1` for `q > 0`. -/
theorem int_add_one_ediv_cases {q : ℤ} (hq : 0 < q) (v : ℤ) :
    (v + 1) / q = v / q ∨ (v + 1) / q = v / q + 1 := by
  have h1 : v / q ≤ (v + 1) / q := Int.ediv_le_ediv hq (by omega)
  have h2 : (v + 1) / q < v / q + 2 := by
    rw [Int.ediv_lt_iff_lt_mul hq]
    have := Int.lt_ediv_add_one_mul_self v hq
    nlinarith
  omega

open Classical in
/-- **The paths of the placed polymer in the box of ruling R15**: for a polymer `X ∈ 𝒟_j` with an
aligned centre `y ∈ X` and `X` inside the box of `relBox` around `y`, every site `s` of the placed
polymer `S = {unlift_j (x - y) : x ∈ X aligned}` is joined to the origin by a lattice path inside
`S` with at most `#S - 1` steps. -/
theorem exists_latPath_of_relBox {m₀ : ℕ} (hL : 3 ≤ L) (hm₀ : 2 ≤ m₀) (hN : L ^ m₀ ∣ N₁)
    (hjk : j ≤ k) {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom m₀ j X) (hyX : y ∈ X) (hbox : relBox m₀ y X)
    {S : Finset (Site d)}
    (hSdef : S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y))) :
    ∀ s ∈ S, ∃ (q : ℕ → Site d) (n : ℕ), q 0 = 0 ∧ q n = s ∧ n + 1 ≤ S.card ∧
      IsLatPath q n ∧ ∀ i ≤ n, q i ∈ S := by
  classical
  -- the numerics of the box
  have hLpos : 0 < L := by omega
  have hNpos : 0 < N₁ := Nat.pos_of_ne_zero (NeZero.ne N₁)
  have hN₁ : L ^ m₀ ≤ N₁ := Nat.le_of_dvd hNpos hN
  have hP : L ^ (m₀ + m₁ + k) ≤ N₁ * L ^ m₁ * L ^ k := by
    rw [pow_add, pow_add]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hN₁)
  have h8 : L ^ (m₀ + m₁ + k) / 8 * 8 ≤ L ^ (m₀ + m₁ + k) := Nat.div_mul_le_self _ _
  have h9 : 9 * L ^ j ≤ L ^ (m₀ + m₁ + k) := by
    have e : m₀ + m₁ + k = 2 + j + (m₀ - 2 + m₁ + (k - j)) := by omega
    rw [e, pow_add, pow_add]
    have hL2 : 9 ≤ L ^ 2 := by nlinarith
    have h1 : 1 ≤ L ^ (m₀ - 2 + m₁ + (k - j)) := Nat.one_le_pow _ _ hLpos
    calc 9 * L ^ j ≤ L ^ 2 * L ^ j := Nat.mul_le_mul_right _ hL2
      _ ≤ L ^ 2 * L ^ j * L ^ (m₀ - 2 + m₁ + (k - j)) := Nat.le_mul_of_pos_right _ h1
  have hside : N₁ * L ^ m₁ * L ^ k = L ^ j * (N₁ * L ^ m₁ * L ^ (k - j)) := by
    have e : L ^ k = L ^ j * L ^ (k - j) := by rw [← pow_add]; congr 1; omega
    rw [e]; ring
  have hQpos : 0 < L ^ j := pow_pos hLpos j
  have hrc : L ^ (m₀ + m₁ + k) / 8 < L ^ j * (L ^ (m₀ + m₁ + k) / 8 / L ^ j + 1) :=
    Nat.lt_mul_div_succ _ hQpos
  have hmul : L ^ j * (L ^ (m₀ + m₁ + k) / 8 / L ^ j) ≤ L ^ (m₀ + m₁ + k) / 8 := Nat.mul_div_le _ _
  have hc : 2 * (L ^ (m₀ + m₁ + k) / 8 / L ^ j + 1) + 1 < N₁ * L ^ m₁ * L ^ (k - j) := by
    refine Nat.lt_of_mul_lt_mul_left (a := L ^ j) ?_
    rw [← hside]
    nlinarith
  have hm : 2 * (L ^ (m₀ + m₁ + k) / 8) + 1 < N₁ * L ^ m₁ * L ^ k := by omega
  -- the placed site of a site of `X`
  set u : CTorus d L N₁ m₁ k → Site d :=
    fun z => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) with hu
  have hmem : ∀ z ∈ X, u z ∈ S := fun z hz => by
    rw [hSdef]; exact mem_placeSet hN hjk hy hX hz
  have hdiv : ∀ z ∈ X, ∀ μ, u z μ = ((z - y) μ).valMinAbs / ((L ^ j : ℕ) : ℤ) := fun z hz μ =>
    unlift_eq_ediv hjk hrc hc (hbox z hz) μ
  -- a unit step of the torus inside `X` is a unit step or no step of the placed sites
  have hstep : ∀ a ∈ X, ∀ b ∈ X, ∀ μ : Fin d, b = a + Pi.single μ 1 →
      u b = u a ∨ u b = u a + eU μ := by
    intro a ha b hb μ hab
    have hv := (step_iff hm (hbox a ha) (hbox b hb) μ).1 (by rw [hab]; abel)
    have hq : (0 : ℤ) < ((L ^ j : ℕ) : ℤ) := by exact_mod_cast hQpos
    have hcomp : ∀ ν, u b ν = (((a - y) ν).valMinAbs + (Pi.single μ (1 : ℤ) : Site d) ν) /
        ((L ^ j : ℕ) : ℤ) := fun ν => by
      rw [hdiv b hb ν]
      have := congrFun hv ν
      simp only [Pi.add_apply] at this
      rw [this]
    rcases int_add_one_ediv_cases hq (((a - y) μ).valMinAbs) with h | h
    · left
      funext ν
      rw [hcomp ν, hdiv a ha ν]
      by_cases hν : ν = μ
      · subst hν; simp only [Pi.single_eq_same]; exact h
      · simp [Pi.single_eq_of_ne hν]
    · right
      funext ν
      rw [hcomp ν, Pi.add_apply, hdiv a ha ν]
      by_cases hν : ν = μ
      · subst hν; simp only [eU, Pi.single_eq_same]; exact h
      · simp [eU, Pi.single_eq_of_ne hν]
  have hlift : ∀ a b, (a ∈ X ∧ b ∈ X ∧ Nbr a b) →
      Relation.ReflTransGen (fun s t => s ∈ S ∧ t ∈ S ∧ LatAdj s t) (u a) (u b) := by
    rintro a b ⟨ha, hb, μ, h | h⟩
    · rcases hstep a ha b hb μ h with e | e
      · rw [e]
      · exact Relation.ReflTransGen.single ⟨hmem a ha, hmem b hb, μ, Or.inl e⟩
    · rcases hstep b hb a ha μ h with e | e
      · rw [e]
      · exact Relation.ReflTransGen.single ⟨hmem a ha, hmem b hb, μ, Or.inr e⟩
  intro s hs
  have hs' := hs
  rw [hSdef] at hs'
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hs'
  have hxX : x ∈ X := (Finset.mem_filter.1 hx).2.2
  have hcon : Relation.ReflTransGen (fun s t => s ∈ S ∧ t ∈ S ∧ LatAdj s t) (u y) (u x) :=
    Relation.ReflTransGen.lift' u hlift y x (hX.2.2 y hyX x hxX)
  have hu0 : u y = 0 := by rw [hu]; simp only [sub_self]; exact unlift_zero j
  rw [hu0] at hcon
  exact exists_latPath_of_reflTransGen (hu0 ▸ hmem y hyX) hcon

end Balaban.SmallField.Def6v2
