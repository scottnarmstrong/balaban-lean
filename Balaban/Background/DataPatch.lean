/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Data

/-!
# Patching of local splits into the complex data domain `Ψ̃^c(δ, ε)`

The complex data domain `Ψ̃^c(𝔹; δ, ε)` (`InDomainC`) asks for one split `D.Ψ = Ψ + Ψ'` of the datum
into a real layer-constant field and a complex perturbation, with conditions at the data sites and at
the interface pairs.  When splits are only known locally (one per cube test of the H7 domain, ruling
request R14), a chart map `c` attaching a split to every site, constant on the blocks of every layer,
patches them into one split: two splits of the same value differ by less than `2 (ε + δ)`, which
enlarges the tolerances of the interface conditions only.

* `rn_eq_norm`, `rn_sub_le`, `vn_sub_le`, `rn_re_le`: the norms `rn`, `vn` as Euclidean norms;
* `inDomainC_of_patch`: the patched datum lies in `Ψ̃^c(3δ + 2ε, 3δ + 2ε)`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {N : ℕ}

theorem rn_eq_norm (v : Fin N → ℝ) : rn v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖ := by
  unfold rn
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.norm_eq_abs, sq_abs]

theorem vn_sub_le (u w : Fin N → ℂ) : vn (u - w) ≤ vn u + vn w := by
  unfold vn
  rw [WithLp.toLp_sub]
  exact norm_sub_le _ _

theorem rn_sub_le (u w : Fin N → ℝ) : rn (u - w) ≤ rn u + rn w := by
  rw [rn_eq_norm, rn_eq_norm, rn_eq_norm, WithLp.toLp_sub]
  exact norm_sub_le _ _

theorem rn_re_le (v : Fin N → ℂ) : rn (fun i => (v i).re) ≤ vn v := by
  unfold rn vn
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have := Complex.abs_re_le_norm (v i)
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

/-- **Patching of local splits** (the domain `Ψ̃^c(δ, ε)` from splits of the datum attached to the
sites): a datum `D` with real constant `h̃ = h₀` whose values at the data sites are `Ψ_{c(x)} + Ψ'_{c(x)}`
for splits indexed by a chart map `c` constant on the blocks of every layer, with the conditions of
`Ψ̃^c(δ, ε)` at every site for its own split and at every interface pair `(x, x')` for the split of `x`,
lies in `Ψ̃^c(3δ + 2ε, 3δ + 2ε)`: two splits of one value differ by less than `2(ε + δ)`. -/
theorem inDomainC_of_patch (D : BgData G N) {ν δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (h₀ : Fin N → ℝ) (hDh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h₀ i : ℂ))
    (hR4 : ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < δ ^ 2)
    {ι : Type*} (c : Torus d (N₀ * L ^ k) → ι) (Ψc : ι → Torus d (N₀ * L ^ k) → Fin N → ℝ)
    (Ψc' : ι → Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hc : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ G.layer n, ∀ x' ∈ G.blk n x, c x' = c x)
    (hlc : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ G.layer n, ∀ x' ∈ G.blk n x,
      Ψc (c x) x' = Ψc (c x) x ∧ Ψc' (c x) x' = Ψc' (c x) x)
    (hsplit : ∀ x ∈ dataSites G, ∀ i, D.Ψ x i = (Ψc (c x) x i : ℂ) + Ψc' (c x) x i)
    (hR2 : ∀ x ∈ dataSites G, |∑ i, Ψc (c x) x i ^ 2 - 1| < δ)
    (hR3 : ∀ x ∈ dataSites G, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
      |1 - (∑ i, Ψc (c x) x i * h₀ i) / rn (Ψc (c x) x)| < δ ^ 2)
    (hC2a : ∀ x ∈ dataSites G, vn (Ψc' (c x) x) < ε + δ)
    (hC2b : ∀ x ∈ dataSites G, ‖∑ i, ((Ψc (c x) x i : ℂ) + Ψc' (c x) x i) *
      ((Ψc (c x) x i : ℂ) + Ψc' (c x) x i) - ∑ i, (Ψc (c x) x i : ℂ) * (Ψc (c x) x i : ℂ)‖ < δ)
    (hpair : ∀ x x', IsInterfacePair G x x' →
      rn (fun i => Ψc (c x) x i - Ψc (c x) x' i) < δ ∧ vn (Ψc' (c x) x - Ψc' (c x) x') < δ ∧
      (∀ i, D.Ψ x' i = (Ψc (c x) x' i : ℂ) + Ψc' (c x) x' i) ∧ vn (Ψc' (c x) x') < ε + δ) :
    InDomainC G ν (3 * δ + 2 * ε) (3 * δ + 2 * ε) D := by
  have hδ' : 0 < 3 * δ + 2 * ε := by linarith
  have hδle : δ ≤ 3 * δ + 2 * ε := by linarith
  have hδsq : δ ^ 2 ≤ (3 * δ + 2 * ε) ^ 2 := pow_le_pow_left₀ hδ.le hδle 2
  -- two splits of one value differ by less than `2 (ε + δ)`
  have htwo : ∀ x x', IsInterfacePair G x x' →
      vn (Ψc' (c x) x' - Ψc' (c x') x') < 2 * (ε + δ) ∧
      rn (fun i => Ψc (c x) x' i - Ψc (c x') x' i) < 2 * (ε + δ) := by
    intro x x' hxx'
    obtain ⟨-, -, h3, h4⟩ := hpair x x' hxx'
    have hx' : x' ∈ dataSites G := hxx'.2.1
    have hv : vn (Ψc' (c x) x' - Ψc' (c x') x') < 2 * (ε + δ) := by
      have := vn_sub_le (Ψc' (c x) x') (Ψc' (c x') x')
      linarith [hC2a x' hx']
    refine ⟨hv, lt_of_le_of_lt ?_ hv⟩
    have heq : (fun i => Ψc (c x) x' i - Ψc (c x') x' i) =
        fun i => ((Ψc' (c x') x' - Ψc' (c x) x') i).re := by
      funext i
      have e1 := h3 i
      have e2 := hsplit x' hx' i
      rw [e1] at e2
      have := congrArg Complex.re e2
      simp only [Complex.add_re, Complex.ofReal_re] at this
      simp only [Pi.sub_apply, Complex.sub_re]
      linarith
    rw [heq]
    refine (rn_re_le _).trans (le_of_eq ?_)
    have : Ψc' (c x') x' - Ψc' (c x) x' = -(Ψc' (c x) x' - Ψc' (c x') x') := by abel
    rw [this]
    unfold vn
    rw [WithLp.toLp_neg, norm_neg]
  refine ⟨fun x => Ψc (c x) x, h₀, fun x => Ψc' (c x) x, fun _ _ => 0, ?_, ?_, ?_⟩
  · refine
      { layerConst := ?_
        r1 := ?_
        r2 := fun x hx => (hR2 x hx).trans_le hδle
        r3 := fun x hx => (hR3 x hx).trans_le hδsq
        r4 := hR4.trans_le hδsq
        eps_pos := hδ'
        layerConst' := ?_
        hLayerConst' := fun _ _ _ _ _ _ _ => rfl
        c1 := ?_
        c2a := fun x hx => (hC2a x hx).trans_le (by linarith)
        c2b := fun x hx => (hC2b x hx).trans_le hδle
        c3a := fun x _ => by
          have h0 : vn (fun _ : Fin N => (0 : ℂ)) = 0 := by
            unfold vn
            rw [show (WithLp.toLp 2 fun _ : Fin N => (0 : ℂ)) = 0 from rfl, norm_zero]
          rw [h0, mul_zero]
          exact div_pos (pow_pos hδ' 2) hδ'
        c3b := fun x _ => by simpa using pow_pos hδ' 2 }
    · intro n hn1 hnk x hx x' hx'
      show Ψc (c x') x' = Ψc (c x) x
      rw [hc n hn1 hnk x hx x' hx']
      exact (hlc n hn1 hnk x hx x' hx').1
    · intro x x' hxx'
      obtain ⟨h1, -, -, -⟩ := hpair x x' hxx'
      have h2 := (htwo x x' hxx').2
      have hsum : (fun i => Ψc (c x) x i - Ψc (c x') x' i) =
          (fun i => Ψc (c x) x i - Ψc (c x) x' i) - fun i => Ψc (c x') x' i - Ψc (c x) x' i := by
        funext i; simp only [Pi.sub_apply]; ring
      have hneg : rn (fun i => Ψc (c x') x' i - Ψc (c x) x' i) =
          rn (fun i => Ψc (c x) x' i - Ψc (c x') x' i) := by
        rw [rn_eq_norm, rn_eq_norm, ← norm_neg]
        congr 1
        ext i
        simp
      show rn (fun i => Ψc (c x) x i - Ψc (c x') x' i) < 3 * δ + 2 * ε
      rw [hsum]
      have := rn_sub_le (fun i => Ψc (c x) x i - Ψc (c x) x' i)
        (fun i => Ψc (c x') x' i - Ψc (c x) x' i)
      linarith
    · intro n hn1 hnk x hx x' hx'
      show Ψc' (c x') x' = Ψc' (c x) x
      rw [hc n hn1 hnk x hx x' hx']
      exact (hlc n hn1 hnk x hx x' hx').2
    · intro x x' hxx'
      obtain ⟨-, h1, -, -⟩ := hpair x x' hxx'
      have h2 := (htwo x x' hxx').1
      show vn (Ψc' (c x) x - Ψc' (c x') x') < 3 * δ + 2 * ε
      have hsum : Ψc' (c x) x - Ψc' (c x') x' =
          (Ψc' (c x) x - Ψc' (c x) x') + (Ψc' (c x) x' - Ψc' (c x') x') := by abel
      have : vn (Ψc' (c x) x - Ψc' (c x') x') ≤
          vn (Ψc' (c x) x - Ψc' (c x) x') + vn (Ψc' (c x) x' - Ψc' (c x') x') := by
        rw [hsum]; unfold vn; rw [WithLp.toLp_add]; exact norm_add_le _ _
      linarith
  · intro x hx i
    exact hsplit x hx i
  · intro x hx i
    rw [hDh x hx i]
    simp

end Balaban.Background
