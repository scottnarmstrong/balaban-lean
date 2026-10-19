/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0AllPlusGas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `KF0HaloAffine`: the all-plus site pieces are affine in the source

The site function of the all-plus sector (F.11) depends on the source `g_x` linearly,
`F_x(u; g) = F_x(u; 0) + ∑_i g_{x,i} (h_i S(u·u) + ∑_j e_{j,i} u_j)`. This file records the
consequences for the walk-halo pieces of `KF0F1Assembly` and the regrouped block activities of
`KF0AllPlusGas`, so that the activities can be continued analytically to a complex source:

* `kf0HaloTerm_affine`: the halo term is affine in the coefficient family (for summable families);
* `siteSrcCoeff`: the coefficient family of the `i`-th component of the source, with the
  decomposition `siteCoeff_src_decomp`, its majorant `siteSrcCoeff_maj` and `siteSrcCoeff_zero`;
* `f1SiteSrcHalo`, `f1SiteHalo_affine`: the pieces of the coefficient of `g_{x,i}` and the
  affine decomposition of the site pieces on the cutoff event;
* `blockSrc`, `blockActivity_affine`: the coefficient of `g_{x,i}` in the regrouped block
  activity `H_X`, its vanishing off the blocks of `X` and off animals, and the weighted bound
  `|blockSrc| ≤ ε e^{-κ|X|}` (`abs_blockSrc_le`).
-/

@[expose] public section

namespace Balaban.LargeField.KF0F1

open Finset Balaban.Green Balaban.LargeField Balaban.LargeField.KF0Taylor

section Generic

variable {d m : ℕ} [NeZero m] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {D : ℕ}

theorem kf0HaloTerm_affine {κι : Type*} [Fintype κι] (ν β : ℝ) (x : Fin D → Torus d m)
    (ℓ : Fin D → W →L[ℝ] ℝ) (c₀ : (Fin D → ℕ) → ℝ) (c : κι → (Fin D → ℕ) → ℝ) (t : κι → ℝ)
    (H : Finset (Torus d m)) (ψ : Torus d m → W)
    (h0 : Summable fun a => ‖kf0WalkSeriesTerm d m ν β x ℓ c₀ ψ a‖)
    (hc : ∀ k, Summable fun a => ‖kf0WalkSeriesTerm d m ν β x ℓ (c k) ψ a‖) :
    kf0HaloTerm d m ν β x ℓ (fun α => c₀ α + ∑ k, t k * c k α) H ψ =
      kf0HaloTerm d m ν β x ℓ c₀ H ψ + ∑ k, t k * kf0HaloTerm d m ν β x ℓ (c k) H ψ := by
  unfold kf0HaloTerm haloPiece
  have hterm : ∀ a : KF0WalkSeriesIndex d D,
      kf0WalkSeriesTerm d m ν β x ℓ (fun α => c₀ α + ∑ k, t k * c k α) ψ a =
        kf0WalkSeriesTerm d m ν β x ℓ c₀ ψ a +
          ∑ k, t k * kf0WalkSeriesTerm d m ν β x ℓ (c k) ψ a := by
    intro a
    simp only [kf0WalkSeriesTerm]
    rw [add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  let S : Set (KF0WalkSeriesIndex d D) := kf0WalkSeriesHalo x ⁻¹' {H}
  have s0 : Summable fun a : S => kf0WalkSeriesTerm d m ν β x ℓ c₀ ψ a :=
    (h0.of_norm).subtype S
  have sk : ∀ k, Summable fun a : S => t k * kf0WalkSeriesTerm d m ν β x ℓ (c k) ψ a :=
    fun k => ((hc k).of_norm.subtype S).mul_left (t k)
  simp_rw [hterm]
  rw [Summable.tsum_add s0 (summable_sum fun k _ => sk k), Summable.tsum_finsetSum fun k _ => sk k]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tsum_mul_left]

end Generic

section Coeff

open SphereChart

variable {D : ℕ}

theorem linCoeff_linear {ι : Type*} [Fintype ι] (s : ι → ℝ) (B : ι → Fin D → ℝ)
    (α : Fin D → ℕ) :
    linCoeff (fun j => ∑ i, s i * B i j) α = ∑ i, s i * linCoeff (B i) α := by
  unfold linCoeff pushCoeff
  simp only [tsum_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem linCoeff_zero (α : Fin D → ℕ) : linCoeff (fun _ : Fin D => (0 : ℝ)) α = 0 := by
  unfold linCoeff pushCoeff
  simp


variable {d N n ℓ : ℕ} [NeZero ℓ] {h : EuclideanSpace ℝ (Fin N)}

noncomputable def siteSrcCoeff (e : OrthonormalBasis (Fin n) ℝ (perp h)) (i : Fin N) :
    (Fin n → ℕ) → ℝ := fun α =>
  h i * quadCoeff Finset.univ sqrtCoeff α +
    linCoeff (fun j => ((e j : perp h) : EuclideanSpace ℝ (Fin N)) i) α

omit [NeZero ℓ] in
theorem siteCoeff_src_decomp (β ν : ℝ) (e : OrthonormalBasis (Fin n) ℝ (perp h))
    (src : Torus d ℓ → Fin N → ℝ) (x : Torus d ℓ) (α : Fin n → ℕ) :
    siteCoeff β ν (f1Nrm src h x) (f1Lin e src x) α =
      siteCoeff β ν 0 (fun _ : Fin n => (0 : ℝ)) α + ∑ i, src x i * siteSrcCoeff e i α := by
  have hl : linCoeff (f1Lin e src x) α = ∑ i, src x i *
      linCoeff (fun j => ((e j : perp h) : EuclideanSpace ℝ (Fin N)) i) α :=
    linCoeff_linear (fun i => src x i) (fun i j => ((e j : perp h) : EuclideanSpace ℝ (Fin N)) i) α
  have e1 : ∑ i, src x i * (h i * quadCoeff Finset.univ sqrtCoeff α) =
      (∑ i, src x i * h i) * quadCoeff Finset.univ sqrtCoeff α := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
  unfold siteCoeff
  rw [linCoeff_zero, hl]
  simp only [siteSrcCoeff, mul_add, Finset.sum_add_distrib, f1Nrm]
  rw [e1]
  ring

theorem siteSrcCoeff_maj (e : OrthonormalBasis (Fin n) ℝ (perp h)) (i : Fin N) {ρ : ℝ}
    (hρ : 0 < ρ) (hx : (n : ℝ) * ρ ^ 2 ≤ 1 / 4) :
    Maj (siteSrcCoeff e i) ρ (|h i| * ((n : ℝ) * ρ ^ 2) +
      ρ * ∑ j, |((e j : perp h) : EuclideanSpace ℝ (Fin N)) i|) := by
  have hx' : ((Finset.univ : Finset (Fin n)).card : ℝ) * ρ ^ 2 ≤ 1 / 4 := by simpa using hx
  have m1 := (quadSqrt_maj Finset.univ hρ hx').smul (h i)
  have m2 := linCoeff_maj (fun j => ((e j : perp h) : EuclideanSpace ℝ (Fin N)) i) hρ
  have := m1.add hρ.le m2
  simp only [Finset.card_univ, Fintype.card_fin] at this
  exact this


theorem siteSrcCoeff_zero_of_small (e : OrthonormalBasis (Fin n) ℝ (perp h)) (i : Fin N) {ρ : ℝ}
    (hρ : 0 < ρ) (hx : (n : ℝ) * ρ ^ 2 ≤ 1 / 4) : siteSrcCoeff e i 0 = 0 := by
  have hx' : ((Finset.univ : Finset (Fin n)).card : ℝ) * ρ ^ 2 ≤ 1 / 4 := by simpa using hx
  have h1 := (quadSqrt_hasSum Finset.univ hρ hx' (fun _ => (0 : ℝ))
    (fun _ => by simpa using hρ.le)).mul_left (h i)
  have h2 := linCoeff_hasSum (fun j => ((e j : perp h) : EuclideanSpace ℝ (Fin N)) i) hρ
    (fun _ => (0 : ℝ))
  have h3 := h1.add h2
  have h4 : HasSum (fun α => siteSrcCoeff e i α * ∏ j, (0 : ℝ) ^ α j)
      (h i * kf0SqrtFn (∑ j : Fin n, (0 : ℝ) ^ 2) +
        ∑ j, ((e j : perp h) : EuclideanSpace ℝ (Fin N)) i * 0) := by
    convert h3 using 1
    funext α
    simp only [siteSrcCoeff]
    ring
  rw [coeff_zero_of_hasSum h4]
  simp [kf0SqrtFn]


/-- The constant coefficient of the source family vanishes. -/
theorem siteSrcCoeff_zero (e : OrthonormalBasis (Fin n) ℝ (perp h)) (i : Fin N) :
    siteSrcCoeff e i 0 = 0 := by
  refine siteSrcCoeff_zero_of_small e i (ρ := 1 / (2 * ((n : ℝ) + 1))) (by positivity) ?_
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  rw [div_pow, one_pow, mul_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg (n : ℝ)]

end Coeff

section SiteSrc

open SphereChart

variable {d N n ℓ : ℕ} [NeZero ℓ] {h : EuclideanSpace ℝ (Fin N)}

/-- `F^{src}_{x,i,H}`: the halo pieces of the coefficient of `g_{x,i}` in the site function at `x`
(the site function is affine in the source). -/
noncomputable def f1SiteSrcHalo (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (x : Torus d ℓ) (i : Fin N) (H : Finset (Torus d ℓ)) (ψ : Torus d ℓ → perp h) : ℝ :=
  kf0HaloTerm d ℓ ν β (fun _ : Fin n => x) (tcoord e) (siteSrcCoeff e i) H ψ

/-- **The site halo pieces are affine in the source.** -/
theorem f1SiteHalo_affine {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g) (hgν : g ≤ ν)
    (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (hκ : 0 ≤ κ)
    (hp : 0 < p) (hn : 1 ≤ n) (hρ1 : kf0Rho d g γ κ p β ≤ 1)
    (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (src : Torus d ℓ → Fin N → ℝ) (x : Torus d ℓ)
    (H : Finset (Torus d ℓ)) (ψ : Torus d ℓ → perp h) (hψ : ∀ y, ‖ψ y‖ ≤ p) :
    f1SiteHalo e β ν src x H ψ = f1SiteHalo e β ν (fun _ _ => 0) x H ψ +
      ∑ i, src x i * f1SiteSrcHalo e β ν x i H ψ := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  have hρpos := kf0Rho_pos (d := d) (κ := κ) hg hq hp hβ
  have hℓ1 : ∀ j, ‖tcoord e j‖ ≤ 1 := norm_tcoord_le e
  have hsum : ∀ c : (Fin n → ℕ) → ℝ,
      (Summable fun α : Fin n → ℕ => ‖c α‖ * kf0Rho d g γ κ p β ^ (∑ j, α j)) →
      Summable fun a => ‖kf0WalkSeriesTerm d ℓ ν β (fun _ : Fin n => x) (tcoord e) c ψ a‖ :=
    fun c hM => (walkSeries_hasSum (d := d) (m := ℓ) hg hgν hγ hq hκ β hp.le
      (fun _ : Fin n => x) (tcoord e) hℓ1 c hM ψ hψ).1
  have hc0 := maj_series (siteCoeff_maj_C hβ.le hν.le hν1 hn 0 (fun _ : Fin n => (0 : ℝ)) hρpos hρ1 hρ)
  have hck := fun i : Fin N => maj_series (siteSrcCoeff_maj e i hρpos hρ)
  unfold f1SiteHalo f1SiteSrcHalo
  have hc : siteCoeff β ν (f1Nrm src h x) (f1Lin e src x) =
      fun α => siteCoeff β ν 0 (fun _ : Fin n => (0 : ℝ)) α + ∑ i, src x i * siteSrcCoeff e i α :=
    funext (siteCoeff_src_decomp β ν e src x)
  have h0c : siteCoeff β ν (f1Nrm (fun (_ : Torus d ℓ) (_ : Fin N) => (0 : ℝ)) h x)
      (f1Lin e (fun (_ : Torus d ℓ) (_ : Fin N) => (0 : ℝ)) x) =
      siteCoeff β ν 0 (fun _ : Fin n => (0 : ℝ)) := by
    have e1 : f1Nrm (fun (_ : Torus d ℓ) (_ : Fin N) => (0 : ℝ)) h x = 0 := by simp [f1Nrm]
    have e2 : f1Lin e (fun (_ : Torus d ℓ) (_ : Fin N) => (0 : ℝ)) x = fun _ => 0 := by
      funext j; simp [f1Lin]
    rw [e1, e2]
  rw [hc, h0c]
  exact kf0HaloTerm_affine ν β _ _ _ _ (fun i => src x i) H ψ (hsum _ hc0.1)
    (fun i => hsum _ (hck i).1)

end SiteSrc

section BlockSrc

open SphereChart Balaban.LargeField.KF0Gas Balaban.LargeField.KF0AllPlus Balaban.Polymer

open scoped Classical

variable {d N n s m' : ℕ} [NeZero s] [NeZero m'] {h : EuclideanSpace ℝ (Fin N)}

/-- The clipped source halo piece. -/
noncomputable def f1SiteSrcHaloClip (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (x : Torus d (s * m')) (i : Fin N) (H : Finset (Torus d (s * m'))) (p : ℝ)
    (ψ : Torus d (s * m') → perp h) : ℝ :=
  f1SiteSrcHalo e β ν x i H (clipField p ψ)

/-- **The coefficient of `g_{x,i}` in the regrouped block activity** `H_X`. -/
noncomputable def blockSrc (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (x : Torus d (s * m')) (i : Fin N) (X : Finset (Torus d m'))
    (Φ : ∀ b, BlockSpace d s m' (perp h) b) : ℝ :=
  ∑ H ∈ haloFibre d s m' X, f1SiteSrcHaloClip e β ν x i H p (toSites Φ)

/-- **The regrouped block activity is affine in the source.** -/
theorem blockActivity_affine {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g) (hgν : g ≤ ν)
    (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (hκ : 0 ≤ κ)
    (hp : 0 < p) (hn : 1 ≤ n) (hρ1 : kf0Rho d g γ κ p β ≤ 1)
    (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (src : Torus d (s * m') → Fin N → ℝ)
    (X : Finset (Torus d m')) (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    blockActivity e β ν p src X Φ = blockActivity e β ν p (fun _ _ => 0) X Φ +
      ∑ x, ∑ i, src x i * blockSrc e β ν p x i X Φ := by
  have hs : ∀ x H, f1SiteHaloClip e β ν src x H p (toSites Φ) =
      f1SiteHaloClip e β ν (fun _ _ => 0) x H p (toSites Φ) +
        ∑ i, src x i * f1SiteSrcHaloClip e β ν x i H p (toSites Φ) := fun x H =>
    f1SiteHalo_affine hβ hg hgν hν1 hγ hq hκ hp hn hρ1 hρ e src x H _
      (norm_clipField_le hp.le _)
  unfold blockActivity blockSrc
  simp only [hs, Finset.sum_add_distrib]
  have e1 : ∑ x : Torus d (s * m'), ∑ H ∈ haloFibre d s m' X,
      ∑ i, src x i * f1SiteSrcHaloClip e β ν x i H p (toSites Φ) =
      ∑ x : Torus d (s * m'), ∑ i, src x i * ∑ H ∈ haloFibre d s m' X,
        f1SiteSrcHaloClip e β ν x i H p (toSites Φ) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  rw [e1]
  ring

end BlockSrc

section SrcBounds

open SphereChart Balaban.LargeField.KF0Gas Balaban.LargeField.KF0AllPlus Balaban.Polymer

open scoped Classical

variable {d N n s m' : ℕ} [NeZero s] [NeZero m'] {h : EuclideanSpace ℝ (Fin N)}

/-- The source piece vanishes unless the halo is connected and contains the anchor. -/
theorem f1SiteSrcHalo_eq_zero {ℓ : ℕ} [NeZero ℓ] (e : OrthonormalBasis (Fin n) ℝ (perp h))
    (β ν : ℝ) (x : Torus d ℓ) (i : Fin N) (H : Finset (Torus d ℓ))
    (hH : ¬ (NNConnected H ∧ x ∈ H)) (ψ : Torus d ℓ → perp h) :
    f1SiteSrcHalo e β ν x i H ψ = 0 := by
  refine kf0HaloTerm_eq_zero ν β _ _ _ (siteSrcCoeff_zero e i) (fun _ _ => Or.inl rfl) H ?_ ψ
  rintro ⟨h1, j, hj⟩
  exact hH ⟨h1, hj⟩

/-- The coefficient of `g_{x,i}` in `H_X` vanishes unless the block of `x` is in `X`. -/
theorem blockSrc_eq_zero_of_not_mem (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (x : Torus d (s * m')) (i : Fin N) (X : Finset (Torus d m'))
    (hx : blockOf d s m' x ∉ X) (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    blockSrc e β ν p x i X Φ = 0 := by
  unfold blockSrc
  refine Finset.sum_eq_zero fun H hH => ?_
  refine f1SiteSrcHalo_eq_zero e β ν x i H ?_ _
  rintro ⟨-, hxH⟩
  exact hx (by rw [← mem_haloFibre.1 hH]; exact Finset.mem_image_of_mem _ hxH)

/-- The coefficient of `g_{x,i}` in `H_X` vanishes for a non-connected block set `X`. -/
theorem blockSrc_eq_zero_of_not_isAnimal (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (x : Torus d (s * m')) (i : Fin N) (X : Finset (Torus d m'))
    (hX : ¬ IsAnimal (blockGraph d m') X) (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    blockSrc e β ν p x i X Φ = 0 := by
  unfold blockSrc
  refine Finset.sum_eq_zero fun H hH => ?_
  refine f1SiteSrcHalo_eq_zero e β ν x i H ?_ _
  rintro ⟨hc, hxH⟩
  have hA := isAnimal_image_blockOf_of_nnConnected (s := s) (m' := m') ⟨x, hxH⟩ hc
  rw [mem_haloFibre.1 hH] at hA
  exact hX hA

/-- For all configurations the clipped source piece is bounded by the cutoff supremum. -/
theorem abs_f1SiteSrcHaloClip_le {β ν g γ κ p : ℝ} (hg : 0 < g) (hgν : g ≤ ν) (hβ : 0 < β)
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (hs : 0 < s) (hκ : 0 ≤ κ)
    (hγκ : κ * 3 ^ d / s ≤ γ) (hp : 0 < p)
    (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (x : Torus d (s * m')) (i : Fin N)
    (H : Finset (Torus d (s * m'))) (ψ : Torus d (s * m') → perp h) :
    |f1SiteSrcHaloClip e β ν x i H p ψ| ≤ cutoffSup p (f1SiteSrcHalo e β ν x i H) := by
  have hρpos := kf0Rho_pos (d := d) (κ := κ) hg hq hp hβ
  obtain ⟨hM, -⟩ := maj_series (siteSrcCoeff_maj e i hρpos hρ)
  exact abs_kf0HaloTerm_le_cutoffSup hg hgν hq hs rfl hκ hγκ β hp.le (fun _ : Fin n => x)
    (tcoord e) (norm_tcoord_le e) (siteSrcCoeff e i) hM H (clipField p ψ)
    (norm_clipField_le hp.le ψ)

/-- The weighted sum of the source pieces over the halos: at most the majorant of the family. -/
theorem f1SiteSrcHalo_weighted {β ν g γ κ p : ℝ} (hg : 0 < g) (hgν : g ≤ ν) (hβ : 0 < β)
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (hs : 0 < s) (hκ : 0 ≤ κ)
    (hγκ : κ * 3 ^ d / s ≤ γ) (hp : 0 < p)
    (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (x : Torus d (s * m')) (i : Fin N) :
    ∑ H : Finset (Torus d (s * m')), Real.exp (κ * kf0BlockCount s m' H) *
        cutoffSup p (f1SiteSrcHalo e β ν x i H) ≤
      |h i| * ((n : ℝ) * kf0Rho d g γ κ p β ^ 2) +
        kf0Rho d g γ κ p β * ∑ j, |((e j : perp h) : EuclideanSpace ℝ (Fin N)) i| := by
  have hρpos := kf0Rho_pos (d := d) (κ := κ) hg hq hp hβ
  obtain ⟨hM, hM2⟩ := maj_series (siteSrcCoeff_maj e i hρpos hρ)
  exact (weighted_kf0HaloTerm_le (d := d) (m := s * m') hg hgν hq hs rfl hκ hγκ β hp.le
    (fun _ : Fin n => x) (tcoord e) (norm_tcoord_le e) (siteSrcCoeff e i) hM).trans hM2

/-- **The weighted bound for the source coefficient of `H_X`.**  If the weighted sums of the source
pieces are at most `ε` then, for all `X`, `x`, `i` and all configurations,
`|blockSrc| ≤ ε e^{-κ |X|}`. -/
theorem abs_blockSrc_le {β ν g γ κ p ε : ℝ} (hg : 0 < g) (hgν : g ≤ ν) (hβ : 0 < β)
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (hs : 0 < s) (hκ : 0 ≤ κ)
    (hγκ : κ * 3 ^ d / s ≤ γ) (hp : 0 < p)
    (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (x : Torus d (s * m')) (i : Fin N)
    (hε : ∑ H : Finset (Torus d (s * m')), Real.exp (κ * kf0BlockCount s m' H) *
        cutoffSup p (f1SiteSrcHalo e β ν x i H) ≤ ε)
    (X : Finset (Torus d m')) (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    |blockSrc e β ν p x i X Φ| ≤ ε * Real.exp (-(κ * X.card)) := by
  have hε0 : 0 ≤ ε := le_trans (Finset.sum_nonneg fun H _ =>
    mul_nonneg (Real.exp_pos _).le (cutoffSup_nonneg _ _)) hε
  by_cases hx : blockOf d s m' x ∈ X
  · have hS := fibre_sum_le (fun H => cutoffSup_nonneg p (f1SiteSrcHalo e β ν x i H)) hε X
    unfold blockSrc
    exact ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun H _ =>
      abs_f1SiteSrcHaloClip_le hg hgν hβ hq hs hκ hγκ hp hρ e x i H _)).trans hS
  · rw [blockSrc_eq_zero_of_not_mem e β ν p x i X hx, abs_zero]
    positivity

end SrcBounds

end Balaban.LargeField.KF0F1
