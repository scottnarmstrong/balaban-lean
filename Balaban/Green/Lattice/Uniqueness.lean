module

public import Balaban.Green.Lattice.LatticeGreen

/-!
# Maximum principle and uniqueness of the lattice Green's function

A function `h : ℤ^d → ℝ` with `Δ h = 0` that tends to `0` at infinity vanishes identically.  Hence
the lattice Green's function `latticeGreen d` is the unique `G` with
`∑_μ (2 G x - G (x + e_μ) - G (x - e_μ)) = δ₀(x)` and `G → 0` along cofinite sets.
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

open Filter Topology Set

variable {d : ℕ}

/-- The maximum principle: a harmonic function tending to `0` at infinity is `≤ 0`. -/
theorem harmonic_le_zero (hd : 0 < d) (h : (Fin d → ℤ) → ℝ)
    (hharm : ∀ x, ∑ μ : Fin d, (2 * h x - h (x + Pi.single μ 1) - h (x - Pi.single μ 1)) = 0)
    (hlim : Tendsto h cofinite (𝓝 0)) (x0 : Fin d → ℤ) : h x0 ≤ 0 := by
  by_contra hpos
  have hpos := not_le.mp hpos
  have hfin : {x | h x0 / 2 ≤ h x}.Finite := by
    have := (Metric.tendsto_nhds.mp hlim) (h x0 / 2) (by linarith)
    rw [Filter.eventually_cofinite] at this
    refine this.subset fun x hx => ?_
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, not_lt] at hx ⊢
    exact (le_abs_self _).trans' hx
  obtain ⟨xs, hxs_mem, hxs⟩ := Set.exists_max_image {x | h x0 / 2 ≤ h x} h hfin
    ⟨x0, by simp only [Set.mem_ofPred_eq]; linarith⟩
  have hmax : ∀ y, h y ≤ h xs := by
    intro y
    by_cases hy : h x0 / 2 ≤ h y
    · exact hxs y hy
    · have := hxs x0 (by simp only [Set.mem_ofPred_eq]; linarith)
      have h2 : h xs ≥ h x0 / 2 := hxs_mem
      linarith [not_le.mp hy]
  -- harmonicity at a maximum forces equality at neighbours
  have hstep : ∀ y, h y = h xs → ∀ μ : Fin d, h (y + Pi.single μ 1) = h xs := by
    intro y hy μ
    have hsum := hharm y
    have hnn : ∀ ν : Fin d, 0 ≤ 2 * h y - h (y + Pi.single ν 1) - h (y - Pi.single ν 1) :=
      fun ν => by
        have := hmax (y + Pi.single ν 1)
        have := hmax (y - Pi.single ν 1)
        linarith
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun ν _ => hnn ν)).mp hsum μ
      (Finset.mem_univ μ)
    have h1 := hmax (y + Pi.single μ 1)
    have h2 := hmax (y - Pi.single μ 1)
    linarith
  let μ0 : Fin d := ⟨0, hd⟩
  have hline : ∀ k : ℕ, h (xs + (k : ℤ) • Pi.single μ0 1) = h xs := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hstep _ ih μ0
      convert this using 2
      push_cast
      rw [add_smul, one_smul, add_assoc]
  have hinj : Function.Injective fun k : ℕ => xs + (k : ℤ) • (Pi.single μ0 1 : Fin d → ℤ) := by
    intro a b hab
    have := congrFun hab μ0
    simp at this
    exact_mod_cast this
  have ht : Tendsto (fun k : ℕ => xs + (k : ℤ) • (Pi.single μ0 1 : Fin d → ℤ)) atTop cofinite := by
    rw [← Nat.cofinite_eq_atTop]
    exact hinj.tendsto_cofinite
  have h1 := hlim.comp ht
  have h2 : (h ∘ fun k : ℕ => xs + (k : ℤ) • (Pi.single μ0 1 : Fin d → ℤ)) = fun _ => h xs :=
    funext hline
  rw [h2] at h1
  have h3 := tendsto_nhds_unique h1 tendsto_const_nhds
  have : h xs ≥ h x0 / 2 := hxs_mem
  linarith

theorem harmonic_eq_zero (hd : 0 < d) (h : (Fin d → ℤ) → ℝ)
    (hharm : ∀ x, ∑ μ : Fin d, (2 * h x - h (x + Pi.single μ 1) - h (x - Pi.single μ 1)) = 0)
    (hlim : Tendsto h cofinite (𝓝 0)) : h = 0 := by
  funext x
  have h1 := harmonic_le_zero hd h hharm hlim x
  have h2 := harmonic_le_zero hd (fun y => -h y) (fun y => by
    have e : ∑ μ : Fin d, (2 * -h y - -h (y + Pi.single μ 1) - -h (y - Pi.single μ 1)) =
        -∑ μ : Fin d, (2 * h y - h (y + Pi.single μ 1) - h (y - Pi.single μ 1)) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e, hharm y, neg_zero]) (by simpa using hlim.neg) x
  simp only [Pi.zero_apply]
  linarith

end Balaban.LatticeGreen
