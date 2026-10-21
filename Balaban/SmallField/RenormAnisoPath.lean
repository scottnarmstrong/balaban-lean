/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormAnisoCtx

/-!
# The data on the polymers from the clauses along paths

`DataHypAnisoOn` (the data read by the anisotropic local analysis on the polymers) from the
clauses of `DataHypAniso` asked only on a region `R` of `ℤ^d`: the first differences of the edges
in `R`, the second differences of the plaquettes in `R`, (Σ1) on `R`, and, for every site `x` of a
polymer `X`, a nearest-neighbour path from the origin to `x` of at most `ℓ X` steps whose sites lie
in `R` with their forward stars (`StarIn`).  The increments are paid along the path
(`norm_sub_le_of_path`), the frozen gradients by the second differences along it
(`norm_fdiff_sub_le_of_path`), and the frozen Taylor remainder `taylorRem` by the frozen gradients
(`norm_taylorRem_le_of_path`).  This is the path form of the data: the `ℓ¹` radii of
`DataHypAniso.toOn` are replaced by path lengths inside `R`, which for a non-convex polymer can be
much larger than the `ℓ¹` radii.
-/

@[expose] public section

namespace Balaban.SmallField

variable {d N : ℕ}

/-- `p` is a nearest-neighbour lattice path of `n` steps. -/
def IsLatPath (p : ℕ → Site d) (n : ℕ) : Prop :=
  ∀ i < n, ∃ μ : Fin d, p (i + 1) = p i + eU μ ∨ p i = p (i + 1) + eU μ

/-- The site `x` and its forward star `x + e_μ`, `x + e_μ + e_ν` lie in `R`. -/
def StarIn (R : Set (Site d)) (x : Site d) : Prop :=
  x ∈ R ∧ ∀ μ : Fin d, x + eU μ ∈ R ∧ ∀ ν : Fin d, x + eU μ + eU ν ∈ R

/-- The frozen Taylor remainder `ψ(x) - ψ(0) - Σ_μ x_μ ∂_μψ(0)`. -/
def taylorRem (ψ : Site d → Spin N) (x : Site d) : Spin N :=
  ψ x - ψ 0 - ∑ μ, ((x μ : ℤ) : ℂ) • fdiff ψ μ 0

theorem IsLatPath.mono {p : ℕ → Site d} {n m : ℕ} (hp : IsLatPath p n) (hm : m ≤ n) :
    IsLatPath p m := fun i hi => hp i (by omega)

/-- **The increments along a path**: `‖ψ(p_n) - ψ(p_0)‖ ≤ n δ` for a path in `R`. -/
theorem norm_sub_le_of_path {R : Set (Site d)} {ψ : Site d → Spin N} {δ : ℝ}
    (hadj : ∀ x μ, x ∈ R → x + eU μ ∈ R → ‖ψ (x + eU μ) - ψ x‖ ≤ δ)
    {p : ℕ → Site d} {n : ℕ} (hp : IsLatPath p n) (hR : ∀ i ≤ n, StarIn R (p i)) :
    ‖ψ (p n) - ψ (p 0)‖ ≤ n * δ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (hp.mono (Nat.le_succ n)) (fun i hi => hR i (by omega))
    have hs : ‖ψ (p (n + 1)) - ψ (p n)‖ ≤ δ := by
      obtain ⟨μ, h | h⟩ := hp n (by omega)
      · rw [h]
        exact hadj _ μ (hR n (by omega)).1 ((hR n (by omega)).2 μ).1
      · rw [h, norm_sub_rev]
        exact hadj _ μ (hR (n + 1) le_rfl).1 ((hR (n + 1) le_rfl).2 μ).1
    calc ‖ψ (p (n + 1)) - ψ (p 0)‖ = ‖(ψ (p (n + 1)) - ψ (p n)) + (ψ (p n) - ψ (p 0))‖ := by
          abel_nf
      _ ≤ δ + n * δ := (norm_add_le _ _).trans (add_le_add hs ih')
      _ = ((n + 1 : ℕ) : ℝ) * δ := by push_cast; ring

/-- The difference of the first differences at the ends of a forward edge is a second difference. -/
theorem fdiff_add_eU_sub (ψ : Site d → Spin N) (x : Site d) (μ ν : Fin d) :
    fdiff ψ ν (x + eU μ) - fdiff ψ ν x =
      ψ (x + Pi.single μ 1 + Pi.single ν 1) - ψ (x + Pi.single μ 1) -
        ψ (x + Pi.single ν 1) + ψ x := by
  simp only [fdiff, eU]
  abel

/-- **The frozen gradients along a path**: `‖∂_νψ(p_n) - ∂_νψ(p_0)‖ ≤ n K₂` for a path whose
sites lie in `R` with their forward stars. -/
theorem norm_fdiff_sub_le_of_path {R : Set (Site d)} {ψ : Site d → Spin N} {K₂ : ℝ}
    (hsec : ∀ x μ ν, x ∈ R → x + eU μ ∈ R → x + eU ν ∈ R → x + eU μ + eU ν ∈ R →
      ‖ψ (x + Pi.single μ 1 + Pi.single ν 1) - ψ (x + Pi.single μ 1) -
        ψ (x + Pi.single ν 1) + ψ x‖ ≤ K₂)
    {p : ℕ → Site d} {n : ℕ} (hp : IsLatPath p n) (hR : ∀ i ≤ n, StarIn R (p i))
    (ν : Fin d) : ‖fdiff ψ ν (p n) - fdiff ψ ν (p 0)‖ ≤ n * K₂ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (hp.mono (Nat.le_succ n)) (fun i hi => hR i (by omega))
    have hstar (x : Site d) (hx : StarIn R x) (μ : Fin d) :
        ‖fdiff ψ ν (x + eU μ) - fdiff ψ ν x‖ ≤ K₂ := by
      rw [fdiff_add_eU_sub]
      exact hsec x μ ν hx.1 (hx.2 μ).1 (hx.2 ν).1 ((hx.2 μ).2 ν)
    have hs : ‖fdiff ψ ν (p (n + 1)) - fdiff ψ ν (p n)‖ ≤ K₂ := by
      obtain ⟨μ, h | h⟩ := hp n (by omega)
      · rw [h]
        exact hstar _ (hR n (by omega)) μ
      · rw [h, norm_sub_rev]
        exact hstar _ (hR (n + 1) le_rfl) μ
    calc ‖fdiff ψ ν (p (n + 1)) - fdiff ψ ν (p 0)‖
        = ‖(fdiff ψ ν (p (n + 1)) - fdiff ψ ν (p n)) + (fdiff ψ ν (p n) - fdiff ψ ν (p 0))‖ := by
          abel_nf
      _ ≤ K₂ + n * K₂ := (norm_add_le _ _).trans (add_le_add hs ih')
      _ = ((n + 1 : ℕ) : ℝ) * K₂ := by push_cast; ring

/-- The frozen Taylor remainder across a forward edge. -/
theorem taylorRem_add_eU (ψ : Site d → Spin N) (x : Site d) (μ : Fin d) :
    taylorRem ψ (x + eU μ) - taylorRem ψ x = fdiff ψ μ x - fdiff ψ μ 0 := by
  classical
  have hs : ∑ ν, (((x + eU μ) ν : ℤ) : ℂ) • fdiff ψ ν 0 =
      ∑ ν, ((x ν : ℤ) : ℂ) • fdiff ψ ν 0 + fdiff ψ μ 0 := by
    have e : ∀ ν, (((x + eU μ) ν : ℤ) : ℂ) • fdiff ψ ν 0 =
        ((x ν : ℤ) : ℂ) • fdiff ψ ν 0 + (if ν = μ then fdiff ψ ν 0 else 0) := by
      intro ν
      by_cases h : ν = μ
      · subst h; simp [eU, add_smul]
      · simp [eU, h]
    rw [Finset.sum_congr rfl fun ν _ => e ν, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  unfold taylorRem
  rw [hs]
  simp only [fdiff, zero_add]
  abel

/-- **The frozen Taylor remainder along a path from the origin**: `‖T(p_n)‖ ≤ n² K₂`. -/
theorem norm_taylorRem_le_of_path {R : Set (Site d)} {ψ : Site d → Spin N} {K₂ : ℝ}
    (hK : 0 ≤ K₂)
    (hsec : ∀ x μ ν, x ∈ R → x + eU μ ∈ R → x + eU ν ∈ R → x + eU μ + eU ν ∈ R →
      ‖ψ (x + Pi.single μ 1 + Pi.single ν 1) - ψ (x + Pi.single μ 1) -
        ψ (x + Pi.single ν 1) + ψ x‖ ≤ K₂)
    {p : ℕ → Site d} (hp0 : p 0 = 0) {n : ℕ} (hp : IsLatPath p n)
    (hR : ∀ i ≤ n, StarIn R (p i)) :
    ‖taylorRem ψ (p n)‖ ≤ (n : ℝ) ^ 2 * K₂ := by
  induction n with
  | zero => simp [hp0, taylorRem, fdiff]
  | succ n ih =>
    have ih' := ih (hp.mono (Nat.le_succ n)) (fun i hi => hR i (by omega))
    have hg : ∀ m ≤ n + 1, ∀ μ, ‖fdiff ψ μ (p m) - fdiff ψ μ 0‖ ≤ m * K₂ := by
      intro m hm μ
      have := norm_fdiff_sub_le_of_path hsec (hp.mono hm) (fun i hi => hR i (by omega)) μ
      rwa [hp0] at this
    have hs : ‖taylorRem ψ (p (n + 1)) - taylorRem ψ (p n)‖ ≤ ((n : ℝ) + 1) * K₂ := by
      obtain ⟨μ, h | h⟩ := hp n (by omega)
      · rw [h, taylorRem_add_eU]
        refine (hg n (by omega) μ).trans ?_
        nlinarith
      · rw [h, norm_sub_rev, taylorRem_add_eU]
        have := hg (n + 1) le_rfl μ
        push_cast at this
        exact this
    calc ‖taylorRem ψ (p (n + 1))‖
        = ‖(taylorRem ψ (p (n + 1)) - taylorRem ψ (p n)) + taylorRem ψ (p n)‖ := by abel_nf
      _ ≤ ((n : ℝ) + 1) * K₂ + (n : ℝ) ^ 2 * K₂ := (norm_add_le _ _).trans (add_le_add hs ih')
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * K₂ := by push_cast; nlinarith

/-- The Taylor input of the local analysis is the difference of two frozen Taylor remainders. -/
theorem taylor_eq_taylorRem_sub (ψ : Site d → Spin N) (x x' : Site d) :
    ψ x - ψ x' - ∑ μ, ((((x - x') μ : ℤ)) : ℂ) • fdiff ψ μ 0 =
      taylorRem ψ x - taylorRem ψ x' := by
  simp only [taylorRem, Pi.sub_apply, Int.cast_sub, sub_smul, Finset.sum_sub_distrib]
  abel

/-- **The data on the polymers from the clauses along paths.**  The clauses of `DataHypAniso` on a
region `R` (first differences of the edges in `R`, second differences of the plaquettes in `R`,
(Σ1) on `R`), the point properties at the origin, the origin with its forward star in `R`, and for
every site `x` of a polymer `X` a path from the origin to `x` of at most `ℓ X` steps inside `R` with
the forward stars give `DataHypAnisoOn polys ℓ`. -/
theorem DataHypAnisoOn.of_paths {polys : Set (Finset (Site d))} {ℓ : Finset (Site d) → ℝ}
    {R : Set (Site d)} {Dom : Set ((Site d → Spin N) × Spin N)} {ν σ ε K₂ : ℝ}
    {ψ : Site d → Spin N} {b : Spin N} (hK : 0 ≤ K₂)
    (hadj : ∀ x μ, x ∈ R → x + eU μ ∈ R → ‖ψ (x + eU μ) - ψ x‖ ≤ σ * ε)
    (hsec : ∀ x μ ν, x ∈ R → x + eU μ ∈ R → x + eU ν ∈ R → x + eU μ + eU ν ∈ R →
      ‖ψ (x + Pi.single μ 1 + Pi.single ν 1) - ψ (x + Pi.single μ 1) -
        ψ (x + Pi.single ν 1) + ψ x‖ ≤ K₂)
    (hsq : ∀ x ∈ R, ‖dot (ψ x) (ψ x) - 1‖ ≤ σ ^ 2 * ε)
    (h0 : StarIn R 0) (hσε : 0 ≤ σ * ε)
    (hpath : ∀ X ∈ polys, ∀ x ∈ X, ∃ (p : ℕ → Site d) (n : ℕ), p 0 = 0 ∧ p n = x ∧
      (n : ℝ) ≤ ℓ X ∧ IsLatPath p n ∧ ∀ i ≤ n, StarIn R (p i))
    (hbdd0 : ‖ψ 0‖ ≤ 2) (hbc : ‖b - (ν : ℂ) • ψ 0‖ ≤ σ ^ 2 * ε)
    (hbl : ‖vInv ψ b - ν‖ ≤ σ ^ 2 * ε ^ 2)
    (hmem : (ψ, b) ∈ Dom) (hmemc : ((fun _ => ψ 0), b) ∈ Dom) :
    DataHypAnisoOn polys ℓ Dom ν σ ε K₂ ψ b where
  K2_nonneg := hK
  sq0 := hsq 0 h0.1
  sq X hX x hx := by
    obtain ⟨p, n, hp0, hpn, -, -, hR⟩ := hpath X hX x hx
    rw [← hpn]
    exact hsq _ (hR n le_rfl).1
  bdd0 := hbdd0
  grad0 μ := by simpa [eU] using hadj 0 μ h0.1 (h0.2 μ).1
  incr X hX x hx := by
    obtain ⟨p, n, hp0, hpn, hn, hp, hR⟩ := hpath X hX x hx
    have h := norm_sub_le_of_path hadj hp hR
    rw [hpn, hp0] at h
    exact h.trans (mul_le_mul_of_nonneg_right hn hσε)
  taylor X hX x hx x' hx' := by
    obtain ⟨p, n, hp0, hpn, hn, hp, hR⟩ := hpath X hX x hx
    obtain ⟨p', n', hp0', hpn', hn', hp', hR'⟩ := hpath X hX x' hx'
    have h1 := norm_taylorRem_le_of_path hK hsec hp0 hp hR
    have h2 := norm_taylorRem_le_of_path hK hsec hp0' hp' hR'
    rw [hpn] at h1
    rw [hpn'] at h2
    rw [taylor_eq_taylorRem_sub]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hn0' : (0 : ℝ) ≤ n' := Nat.cast_nonneg n'
    have e1 : (n : ℝ) ^ 2 ≤ ℓ X ^ 2 := pow_le_pow_left₀ hn0 hn 2
    have e2 : (n' : ℝ) ^ 2 ≤ ℓ X ^ 2 := pow_le_pow_left₀ hn0' hn' 2
    calc ‖taylorRem ψ x - taylorRem ψ x'‖ ≤ ‖taylorRem ψ x‖ + ‖taylorRem ψ x'‖ := norm_sub_le _ _
      _ ≤ (n : ℝ) ^ 2 * K₂ + (n' : ℝ) ^ 2 * K₂ := add_le_add h1 h2
      _ ≤ 6 * ℓ X ^ 2 * K₂ := by nlinarith [sq_nonneg (ℓ X)]
  b_close := hbc
  b_long := hbl
  mem := hmem
  mem_const := hmemc

end Balaban.SmallField
