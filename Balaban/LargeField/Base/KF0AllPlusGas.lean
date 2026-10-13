/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0AllGoodGas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0AllPlusGas`: the all-plus, all-`ψ`-small sector as a block gas

All-plus, all-`ψ`-small sector only.  The heavy sectors, the minus sheets and the one-scale theorem
are NOT proved here.

Three pieces are supplied that `block_gas` (`KF0AllGoodGas.lean`) still needed for the product
cutoff event.

* (T1) Measurability of `f1SiteHalo` and `f1BondHalo` as functions of `ψ`: each is a `tsum` over a
  countable index of terms that are finite products of continuous functions of finitely many
  coordinates of `ψ`.
* (T2) Terms bounded for all configurations.  `clip p` is the radial retraction of the tangent
  space onto the ball `‖w‖ ≤ p`, acting sitewise.  The clipped terms are `F̃_H = F_H ∘ clip_p`;
  they agree with `F_H` on the cutoff event, depend only on `H`, are measurable, and satisfy
  `|F̃_H ψ| ≤ cutoffSup p F_H` for ALL `ψ`.  (Clipping rather than zero-extension: measurability
  and dependence on `H` are immediate, and the clipped function is continuous in `ψ`.)
* (T3) The regrouped block activities `H_X`, their vanishing off animals, their dependence on the
  blocks of `X`, and the weighted bound `|H_X Φ| ≤ A ε e^{-(κ0+κ1) |X|_St}`.
-/

@[expose] public section

namespace Balaban.LargeField.KF0AllPlus

open Finset MeasureTheory Balaban.Green Balaban.LargeField Balaban.LargeField.KF0F1

/-! ### The radial retraction -/

section Clip

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The radial retraction of `W` onto the ball `‖w‖ ≤ p`: `w` if `‖w‖ ≤ p`, else `(p/‖w‖) w`. -/
noncomputable def clip (p : ℝ) (w : W) : W := by
  classical exact if ‖w‖ ≤ p then w else (p / ‖w‖) • w

theorem clip_of_le {p : ℝ} {w : W} (h : ‖w‖ ≤ p) : clip p w = w := by
  simp [clip, h]

theorem norm_clip_le {p : ℝ} (hp : 0 ≤ p) (w : W) : ‖clip p w‖ ≤ p := by
  by_cases h : ‖w‖ ≤ p
  · rw [clip_of_le h]; exact h
  · have h' : p < ‖w‖ := not_le.1 h
    have hw : 0 < ‖w‖ := lt_of_le_of_lt hp h'
    simp only [clip, h, ite_false, norm_smul, norm_div, Real.norm_eq_abs,
      abs_of_nonneg hp, abs_norm]
    rw [div_mul_cancel₀ _ hw.ne']

theorem measurable_clip [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] (p : ℝ) :
    Measurable (clip p : W → W) := by
  classical
  have : (clip p : W → W) = fun w => if ‖w‖ ≤ p then w else (p / ‖w‖) • w := by
    funext w; simp [clip]
  rw [this]
  refine Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id ?_
  exact (measurable_const.div measurable_norm).smul measurable_id

/-- The sitewise radial retraction of a field. -/
noncomputable def clipField {ι : Type*} (p : ℝ) (ψ : ι → W) : ι → W := fun y => clip p (ψ y)

theorem clipField_eq_self {ι : Type*} {p : ℝ} {ψ : ι → W} (h : ∀ y, ‖ψ y‖ ≤ p) :
    clipField p ψ = ψ := funext fun y => clip_of_le (h y)

theorem norm_clipField_le {ι : Type*} {p : ℝ} (hp : 0 ≤ p) (ψ : ι → W) (y : ι) :
    ‖clipField p ψ y‖ ≤ p := norm_clip_le hp _

theorem measurable_clipField {ι : Type*} [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W] (p : ℝ) : Measurable (clipField (ι := ι) (W := W) p) :=
  measurable_pi_iff.2 fun y => (measurable_clip p).comp (measurable_pi_apply y)

end Clip

/-! ### (T1) Measurability of the halo pieces -/

section Meas

variable {d m : ℕ} [NeZero m] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] {D : ℕ}

instance : Countable (KF0WalkSeriesIndex d D) := by
  unfold KF0WalkSeriesIndex KF0Slot KF0Walk
  infer_instance

omit [SecondCountableTopology W] in
/-- Each walk-indexed term is a measurable function of `ψ` (a finite product of continuous
functions of finitely many coordinates). -/
theorem measurable_kf0WalkSeriesTerm (ν β : ℝ) (x : Fin D → Torus d m) (ℓ : Fin D → W →L[ℝ] ℝ)
    (c : (Fin D → ℕ) → ℝ) (a : KF0WalkSeriesIndex d D) :
    Measurable (fun ψ : Torus d m → W => kf0WalkSeriesTerm d m ν β x ℓ c ψ a) := by
  unfold kf0WalkSeriesTerm kf0WalkTerm
  refine measurable_const.mul (Finset.measurable_prod _ fun i _ => ?_)
  exact measurable_const.mul ((ℓ _).continuous.measurable.comp (measurable_pi_apply _))

omit [SecondCountableTopology W] in
/-- **(T1, generic)** `ψ ↦ F_H ψ` is measurable. -/
theorem measurable_kf0HaloTerm (ν β : ℝ) (x : Fin D → Torus d m) (ℓ : Fin D → W →L[ℝ] ℝ)
    (c : (Fin D → ℕ) → ℝ) (H : Finset (Torus d m)) :
    Measurable (kf0HaloTerm d m ν β x ℓ c H) := by
  unfold kf0HaloTerm haloPiece
  exact Measurable.tsum fun a => measurable_kf0WalkSeriesTerm ν β x ℓ c a.1

end Meas

/-! ### (T2) Pointwise bounds on the cutoff event -/

section Bound

variable {d m : ℕ} [NeZero m] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {D : ℕ}

/-- The weighted pointwise bound of one halo piece on the cutoff event (the pointwise form of
`weighted_kf0HaloTerm_le`). -/
theorem weighted_abs_kf0HaloTerm_le {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ}
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {s m' : ℕ} [NeZero m'] (hs : 0 < s)
    (hm : m = s * m') {κ : ℝ} (hκ : 0 ≤ κ) (hγ : κ * 3 ^ d / s ≤ γ) (β : ℝ) {p : ℝ}
    (hp0 : 0 ≤ p) (x : Fin D → Torus d m) (ℓ : Fin D → W →L[ℝ] ℝ) (hℓ : ∀ j, ‖ℓ j‖ ≤ 1)
    (c : (Fin D → ℕ) → ℝ)
    (hM : Summable fun α : Fin D → ℕ => ‖c α‖ * kf0Rho d g γ κ p β ^ (∑ j, α j))
    (H : Finset (Torus d m)) (ψ : Torus d m → W) (hψ : ∀ y, ‖ψ y‖ ≤ p) :
    Real.exp (κ * kf0BlockCount s m' H) * |kf0HaloTerm d m ν β x ℓ c H ψ| ≤
      haloPiece (kf0WalkSeriesHalo x)
        (kf0WalkSeriesBound d ν β γ p (Real.exp (κ * 3 ^ d)) c) H := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  obtain ⟨hB, -⟩ := kf0WalkSeriesBound_summable (d := d) (ν := ν) hg hgν hq β hp0
    (Real.exp_pos (κ * 3 ^ d)).le c hM
  have hwpos : ∀ H : Finset (Torus d m), 0 < Real.exp (κ * kf0BlockCount s m' H) :=
    fun H => Real.exp_pos _
  unfold kf0HaloTerm
  exact weighted_haloPiece_le hB hwpos (fun a => by
    have := walkSeriesTerm_weighted_le hν hs hm hκ hγ β x ℓ hℓ c a ψ hψ
    simpa only [Real.norm_eq_abs] using this) H

/-- On the cutoff event `|F_H ψ| ≤ cutoffSup p F_H`: the set of values is bounded above. -/
theorem abs_kf0HaloTerm_le_cutoffSup {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ}
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {s m' : ℕ} [NeZero m'] (hs : 0 < s)
    (hm : m = s * m') {κ : ℝ} (hκ : 0 ≤ κ) (hγ : κ * 3 ^ d / s ≤ γ) (β : ℝ) {p : ℝ}
    (hp0 : 0 ≤ p) (x : Fin D → Torus d m) (ℓ : Fin D → W →L[ℝ] ℝ) (hℓ : ∀ j, ‖ℓ j‖ ≤ 1)
    (c : (Fin D → ℕ) → ℝ)
    (hM : Summable fun α : Fin D → ℕ => ‖c α‖ * kf0Rho d g γ κ p β ^ (∑ j, α j))
    (H : Finset (Torus d m)) (ψ : Torus d m → W) (hψ : ∀ y, ‖ψ y‖ ≤ p) :
    |kf0HaloTerm d m ν β x ℓ c H ψ| ≤ cutoffSup p (kf0HaloTerm d m ν β x ℓ c H) := by
  have hwpos : 0 < Real.exp (κ * kf0BlockCount s m' H) := Real.exp_pos _
  refine le_ciSup (f := fun ψ : {ψ : Torus d m → W // ∀ y, ‖ψ y‖ ≤ p} =>
    |kf0HaloTerm d m ν β x ℓ c H ψ.1|) ⟨haloPiece (kf0WalkSeriesHalo x)
      (kf0WalkSeriesBound d ν β γ p (Real.exp (κ * 3 ^ d)) c) H /
        Real.exp (κ * kf0BlockCount s m' H), ?_⟩ ⟨ψ, hψ⟩
  rintro _ ⟨ψ', rfl⟩
  rw [le_div_iff₀' hwpos]
  exact weighted_abs_kf0HaloTerm_le hg hgν hq hs hm hκ hγ β hp0 x ℓ hℓ c hM H ψ'.1 ψ'.2

end Bound

/-! ### The clipped site and bond halo pieces -/

section F1

open SphereChart Balaban.LargeField.KF0Taylor

variable {d N ℓ n : ℕ} [NeZero ℓ] {h : EuclideanSpace ℝ (Fin N)}

/-- **(T2)** The clipped site halo piece `F̃^{site}_{x,H} = F^{site}_{x,H} ∘ clip_p`. -/
noncomputable def f1SiteHaloClip (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (g : Torus d ℓ → Fin N → ℝ) (x : Torus d ℓ) (H : Finset (Torus d ℓ)) (p : ℝ)
    (ψ : Torus d ℓ → perp h) : ℝ :=
  f1SiteHalo e β ν g x H (clipField p ψ)

/-- **(T2)** The clipped bond halo piece `F̃^{bond}_{(x,μ),H} = F^{bond}_{(x,μ),H} ∘ clip_p`. -/
noncomputable def f1BondHaloClip (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (x : Torus d ℓ) (μ : Fin d) (H : Finset (Torus d ℓ)) (p : ℝ) (ψ : Torus d ℓ → perp h) : ℝ :=
  f1BondHalo e β ν x μ H (clipField p ψ)

/-- **(T1)** `ψ ↦ F^{site}_{x,H} ψ` is measurable. -/
theorem measurable_f1SiteHalo (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (g : Torus d ℓ → Fin N → ℝ) (x : Torus d ℓ) (H : Finset (Torus d ℓ)) :
    Measurable (f1SiteHalo e β ν g x H) :=
  measurable_kf0HaloTerm ν β _ _ _ H

/-- **(T1)** `ψ ↦ F^{bond}_{(x,μ),H} ψ` is measurable. -/
theorem measurable_f1BondHalo (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (x : Torus d ℓ) (μ : Fin d) (H : Finset (Torus d ℓ)) :
    Measurable (f1BondHalo e β ν x μ H) :=
  measurable_kf0HaloTerm ν β _ _ _ H

theorem f1SiteHaloClip_eq_of_cutoff (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (g : Torus d ℓ → Fin N → ℝ) (x : Torus d ℓ) (H : Finset (Torus d ℓ)) {p : ℝ}
    {ψ : Torus d ℓ → perp h} (hψ : ∀ y, ‖ψ y‖ ≤ p) :
    f1SiteHaloClip e β ν g x H p ψ = f1SiteHalo e β ν g x H ψ := by
  unfold f1SiteHaloClip; rw [clipField_eq_self hψ]

theorem f1BondHaloClip_eq_of_cutoff (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (x : Torus d ℓ) (μ : Fin d) (H : Finset (Torus d ℓ)) {p : ℝ}
    {ψ : Torus d ℓ → perp h} (hψ : ∀ y, ‖ψ y‖ ≤ p) :
    f1BondHaloClip e β ν x μ H p ψ = f1BondHalo e β ν x μ H ψ := by
  unfold f1BondHaloClip; rw [clipField_eq_self hψ]

theorem f1SiteHaloClip_congr (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (g : Torus d ℓ → Fin N → ℝ) (x : Torus d ℓ) (H : Finset (Torus d ℓ)) (p : ℝ)
    {ψ ψ' : Torus d ℓ → perp h} (hψ : ∀ b ∈ H, ψ b = ψ' b) :
    f1SiteHaloClip e β ν g x H p ψ = f1SiteHaloClip e β ν g x H p ψ' :=
  f1SiteHalo_congr e β ν g x H fun b hb => by simp only [clipField, hψ b hb]

theorem f1BondHaloClip_congr (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (x : Torus d ℓ) (μ : Fin d) (H : Finset (Torus d ℓ)) (p : ℝ)
    {ψ ψ' : Torus d ℓ → perp h} (hψ : ∀ b ∈ H, ψ b = ψ' b) :
    f1BondHaloClip e β ν x μ H p ψ = f1BondHaloClip e β ν x μ H p ψ' :=
  f1BondHalo_congr e β ν x μ H fun b hb => by simp only [clipField, hψ b hb]

theorem measurable_f1SiteHaloClip (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (g : Torus d ℓ → Fin N → ℝ) (x : Torus d ℓ) (H : Finset (Torus d ℓ)) (p : ℝ) :
    Measurable (f1SiteHaloClip e β ν g x H p) :=
  (measurable_f1SiteHalo e β ν g x H).comp (measurable_clipField p)

theorem measurable_f1BondHaloClip (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν : ℝ)
    (x : Torus d ℓ) (μ : Fin d) (H : Finset (Torus d ℓ)) (p : ℝ) :
    Measurable (f1BondHaloClip e β ν x μ H p) :=
  (measurable_f1BondHalo e β ν x μ H).comp (measurable_clipField p)

/-- **(T2, site)** For ALL configurations `ψ`, `|F̃^{site}_{x,H} ψ| ≤ cutoffSup p F^{site}_{x,H}`. -/
theorem abs_f1SiteHaloClip_le {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g) (hgν : g ≤ ν)
    (hν1 : ν ≤ 1) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {s m' : ℕ}
    [NeZero m'] (hs : 0 < s) (hℓ : ℓ = s * m') (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ)
    (hp : 0 < p) (hn : 1 ≤ n) (hρ1 : kf0Rho d g γ κ p β ≤ 1)
    (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (src : Torus d ℓ → Fin N → ℝ) (x : Torus d ℓ)
    (H : Finset (Torus d ℓ)) (ψ : Torus d ℓ → perp h) :
    |f1SiteHaloClip e β ν src x H p ψ| ≤ cutoffSup p (f1SiteHalo e β ν src x H) := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  have hρpos := kf0Rho_pos (d := d) (κ := κ) hg hq hp hβ
  have hMaj := siteCoeff_maj_C hβ.le hν.le hν1 hn (f1Nrm src h x) (f1Lin e src x) hρpos hρ1 hρ
  obtain ⟨hM, -⟩ := maj_series hMaj
  exact abs_kf0HaloTerm_le_cutoffSup hg hgν hq hs hℓ hκ hγκ β hp.le (fun _ : Fin n => x)
    (tcoord e) (norm_tcoord_le e) (siteCoeff β ν (f1Nrm src h x) (f1Lin e src x)) hM H
    (clipField p ψ) (norm_clipField_le hp.le ψ)

/-- **(T2, bond)** For ALL configurations `ψ`, `|F̃^{bond}_{(x,μ),H} ψ| ≤ cutoffSup p F^{bond}_{(x,μ),H}`. -/
theorem abs_f1BondHaloClip_le {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g) (hgν : g ≤ ν)
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {s m' : ℕ}
    [NeZero m'] (hs : 0 < s) (hℓ : ℓ = s * m') (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ)
    (hp : 0 < p) (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (x : Torus d ℓ) (μ : Fin d)
    (H : Finset (Torus d ℓ)) (ψ : Torus d ℓ → perp h) :
    |f1BondHaloClip e β ν x μ H p ψ| ≤ cutoffSup p (f1BondHalo e β ν x μ H) := by
  have hρpos := kf0Rho_pos (d := d) (κ := κ) hg hq hp hβ
  have hMaj := bondCoeff_maj_pair hβ.le n hρpos hρ
  obtain ⟨hM, -⟩ := maj_series hMaj
  exact abs_kf0HaloTerm_le_cutoffSup hg hgν hq hs hℓ hκ hγκ β hp.le
    (bondAnchor n (x + Pi.single μ 1) x) (bondEll e) (norm_bondEll_le e)
    (bondCoeff β (bondFst n) (bondSnd n)) hM H (clipField p ψ) (norm_clipField_le hp.le ψ)

end F1

/-! ### (T3) The regrouped block activities -/

section Regroup

open Balaban.LargeField.KF0Gas Balaban.Polymer SphereChart

open scoped Classical

variable {d N n s m' : ℕ} [NeZero s] [NeZero m'] {h : EuclideanSpace ℝ (Fin N)}

/-- The site sets `H` whose set of blocks is exactly `X`. -/
noncomputable def haloFibre (d s m' : ℕ) [NeZero s] [NeZero m'] (X : Finset (Torus d m')) :
    Finset (Finset (Torus d (s * m'))) :=
  Finset.univ.filter fun H => H.image (blockOf d s m') = X

theorem mem_haloFibre {X : Finset (Torus d m')} {H : Finset (Torus d (s * m'))} :
    H ∈ haloFibre d s m' X ↔ H.image (blockOf d s m') = X := by
  simp [haloFibre]

/-- **The regrouped block activity** `H_X(Φ)`: the sum, over all anchors (sites and forward
bonds) and all site sets `H` whose blocks are exactly `X`, of the clipped halo pieces at the site
configuration `toSites Φ`. -/
noncomputable def blockActivity (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (src : Torus d (s * m') → Fin N → ℝ) (X : Finset (Torus d m'))
    (Φ : ∀ b, BlockSpace d s m' (perp h) b) : ℝ :=
  (∑ x : Torus d (s * m'), ∑ H ∈ haloFibre d s m' X, f1SiteHaloClip e β ν src x H p (toSites Φ)) +
    ∑ x : Torus d (s * m'), ∑ μ : Fin d, ∑ H ∈ haloFibre d s m' X,
      f1BondHaloClip e β ν x μ H p (toSites Φ)

/-- The activity as a sum over the fibre of the anchor-summed pieces. -/
theorem blockActivity_eq (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (src : Torus d (s * m') → Fin N → ℝ) (X : Finset (Torus d m'))
    (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    blockActivity e β ν p src X Φ = ∑ H ∈ haloFibre d s m' X,
      ((∑ x : Torus d (s * m'), f1SiteHaloClip e β ν src x H p (toSites Φ)) +
        ∑ x : Torus d (s * m'), ∑ μ : Fin d, f1BondHaloClip e β ν x μ H p (toSites Φ)) := by
  unfold blockActivity
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  calc _ = ∑ x : Torus d (s * m'), ∑ H ∈ haloFibre d s m' X, ∑ μ : Fin d,
        f1BondHaloClip e β ν x μ H p (toSites Φ) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- `H_X` depends only on the blocks of `X`. -/
theorem blockActivity_depOn (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (src : Torus d (s * m') → Fin N → ℝ) (X : Finset (Torus d m')) :
    DepOn X (fun Φ : ∀ b, BlockSpace d s m' (perp h) b =>
      ((blockActivity e β ν p src X Φ : ℝ) : ℂ)) := by
  intro Φ Φ' hΦ
  have hsite : ∀ H ∈ haloFibre d s m' X, ∀ b ∈ H, toSites Φ b = toSites Φ' b := by
    intro H hH b hb
    have hbX : blockOf d s m' b ∈ X := by
      rw [← (mem_haloFibre.1 hH)]; exact Finset.mem_image_of_mem _ hb
    have := congrFun (hΦ (blockOf d s m' b) hbX) (⟨b, rfl⟩ : Fibre d s m' (blockOf d s m' b))
    exact this
  show ((blockActivity e β ν p src X Φ : ℝ) : ℂ) = ((blockActivity e β ν p src X Φ' : ℝ) : ℂ)
  refine congrArg _ ?_
  have h1 : (∑ x : Torus d (s * m'), ∑ H ∈ haloFibre d s m' X,
      f1SiteHaloClip e β ν src x H p (toSites Φ)) = ∑ x : Torus d (s * m'),
      ∑ H ∈ haloFibre d s m' X, f1SiteHaloClip e β ν src x H p (toSites Φ') :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun H hH =>
      f1SiteHaloClip_congr e β ν src x H p (hsite H hH)
  have h2 : (∑ x : Torus d (s * m'), ∑ μ : Fin d, ∑ H ∈ haloFibre d s m' X,
      f1BondHaloClip e β ν x μ H p (toSites Φ)) = ∑ x : Torus d (s * m'), ∑ μ : Fin d,
      ∑ H ∈ haloFibre d s m' X, f1BondHaloClip e β ν x μ H p (toSites Φ') :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ =>
      Finset.sum_congr rfl fun H hH => f1BondHaloClip_congr e β ν x μ H p (hsite H hH)
  unfold blockActivity
  rw [h1, h2]

/-- `H_X` is a measurable function of the block configuration. -/
theorem measurable_blockActivity (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (src : Torus d (s * m') → Fin N → ℝ) (X : Finset (Torus d m')) :
    Measurable (fun Φ : ∀ b, BlockSpace d s m' (perp h) b =>
      ((blockActivity e β ν p src X Φ : ℝ) : ℂ)) := by
  refine Complex.measurable_ofReal.comp ?_
  unfold blockActivity
  refine Measurable.add (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun H _ => ?_)
    (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun μ _ =>
      Finset.measurable_sum _ fun H _ => ?_)
  · exact (measurable_f1SiteHaloClip e β ν src x H p).comp measurable_toSites
  · exact (measurable_f1BondHaloClip e β ν x μ H p).comp measurable_toSites

omit [NeZero s] [NeZero m'] in
theorem blockMap_eq_blockOf :
    (Balaban.blockMap (d := d) (ℓ := s * m') s m') = blockOf d s m' := rfl

theorem kf0BlockCount_eq_card {X : Finset (Torus d m')} {H : Finset (Torus d (s * m'))}
    (hH : H ∈ haloFibre d s m' X) : kf0BlockCount s m' H = X.card := by
  unfold kf0BlockCount
  rw [blockMap_eq_blockOf, mem_haloFibre.1 hH]

/-- Number of anchors `x` of a bond in direction `μ` whose bond meets the sites of `X`. -/
theorem card_bondAnchors_le (X : Finset (Torus d m')) (μ : Fin d) :
    ((Finset.univ : Finset (Torus d (s * m'))).filter
      fun x => blockOf d s m' x ∈ X ∨ blockOf d s m' (x + Pi.single μ 1) ∈ X).card ≤
      2 * (s ^ d * X.card) := by
  rw [Finset.filter_or]
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : ((Finset.univ : Finset (Torus d (s * m'))).filter
      fun x => blockOf d s m' x ∈ X).card = s ^ d * X.card := card_siteSet d s m' X
  have h2 : ((Finset.univ : Finset (Torus d (s * m'))).filter
      fun x => blockOf d s m' (x + Pi.single μ 1) ∈ X).card = s ^ d * X.card := by
    rw [← h1]
    refine Finset.card_equiv (Equiv.addRight (Pi.single μ 1 : Torus d (s * m'))) fun i => ?_
    simp
  omega

/-- A real number bound for sums over a fibre: `∑_{H ∈ fibre X} cutoffSup ≤ ε e^{-κ |X|}`. -/
theorem fibre_sum_le {κ ε : ℝ} {S : Finset (Torus d (s * m')) → ℝ} (hS : ∀ H, 0 ≤ S H)
    (hε : ∑ H : Finset (Torus d (s * m')), Real.exp (κ * kf0BlockCount s m' H) * S H ≤ ε)
    (X : Finset (Torus d m')) :
    ∑ H ∈ haloFibre d s m' X, S H ≤ ε * Real.exp (-(κ * X.card)) := by
  have h1 : ∑ H ∈ haloFibre d s m' X, Real.exp (κ * X.card) * S H ≤ ε := by
    refine le_trans (le_of_eq_of_le (Finset.sum_congr rfl fun H hH => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (haloFibre d s m' X))
        (fun H _ _ => mul_nonneg (Real.exp_pos _).le (hS H)))) hε
    rw [kf0BlockCount_eq_card hH]
  rw [← Finset.mul_sum] at h1
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  linarith [mul_comm (Real.exp (κ * X.card)) (∑ H ∈ haloFibre d s m' X, S H)]

/-- **(T3, vanishing off animals)** If `X` is not a connected block set then `H_X = 0`. -/
theorem blockActivity_eq_zero_of_not_isAnimal {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g)
    (hgν : g ≤ ν) (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1)
    (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ) (hp : 0 < p) (hn : 1 ≤ n)
    (hρ1 : kf0Rho d g γ κ p β ≤ 1) (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (src : Torus d (s * m') → Fin N → ℝ)
    (X : Finset (Torus d m')) (hX : ¬ IsAnimal (blockGraph d m') X)
    (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    blockActivity e β ν p src X Φ = 0 := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hsite : ∀ x H, H ∈ haloFibre d s m' X → f1SiteHaloClip e β ν src x H p (toSites Φ) = 0 := by
    intro x H hH
    refine (site_halo_decomposition (ℓ := s * m') hβ hg hgν hν1 hγ hq hs rfl hκ hγκ hp hn hρ1 hρ
      e src x).2.1 H ?_ _
    rintro ⟨hc, hx⟩
    have hA := isAnimal_image_blockOf_of_nnConnected (s := s) (m' := m') ⟨x, hx⟩ hc
    rw [mem_haloFibre.1 hH] at hA
    exact hX hA
  have hbond : ∀ x μ H, H ∈ haloFibre d s m' X →
      f1BondHaloClip e β ν x μ H p (toSites Φ) = 0 := by
    intro x μ H hH
    refine (bond_halo_decomposition (ℓ := s * m') hβ hg hgν hγ hq hs rfl hκ hγκ hp hρ
      e x μ).2.1 H ?_ _
    rintro ⟨hc, hx⟩
    have hne : H.Nonempty := by rcases hx with hx | hx <;> exact ⟨_, hx⟩
    have hA := isAnimal_image_blockOf_of_nnConnected (s := s) (m' := m') hne hc
    rw [mem_haloFibre.1 hH] at hA
    exact hX hA
  unfold blockActivity
  rw [Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero fun H hH => hsite x H hH),
    Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero fun μ _ =>
      Finset.sum_eq_zero fun H hH => hbond x μ H hH)]
  simp

/-- **(T3, the weighted bound)**  Let `A = (1 + 2d) s^d`.  If the weighted sums of the site pieces
and of the bond pieces are at most `ε` (the conclusion of `f1_weighted_small`) and
`κ ≥ 1 + κ0 + κ1`, `κ0 + κ1 ≥ 0`, then for ALL block sets `X` and ALL configurations `Φ`,
`|H_X Φ| ≤ A ε e^{-(κ0+κ1) |X|_St}`.  Relation used between the block count and the Steiner size:
for an animal `X`, `|X|_St ≤ |X|` and `k_s(H) = |X|` for every `H` with blocks `X`; the anchors
with a nonzero piece are at most `(1 + 2d) s^d |X|` in number, and `|X| ≤ e^{|X|}` absorbs the
factor `|X|` into one unit of `κ`. -/
theorem blockActivity_abs_le {β ν g γ κ p ε κ0 κ1 : ℝ} (hβ : 0 < β) (hg : 0 < g)
    (hgν : g ≤ ν) (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1)
    (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ) (hp : 0 < p) (hn : 1 ≤ n)
    (hρ1 : kf0Rho d g γ κ p β ≤ 1) (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (src : Torus d (s * m') → Fin N → ℝ)
    (hsite : ∀ x : Torus d (s * m'), ∑ H : Finset (Torus d (s * m')),
      Real.exp (κ * kf0BlockCount s m' H) * cutoffSup p (f1SiteHalo e β ν src x H) ≤ ε)
    (hbond : ∀ (x : Torus d (s * m')) (μ : Fin d), ∑ H : Finset (Torus d (s * m')),
      Real.exp (κ * kf0BlockCount s m' H) * cutoffSup p (f1BondHalo e β ν x μ H) ≤ ε)
    (hκ01 : 1 + κ0 + κ1 ≤ κ) (hκ01' : 0 ≤ κ0 + κ1)
    (X : Finset (Torus d m')) (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    |blockActivity e β ν p src X Φ| ≤
      ((1 + 2 * d) * s ^ d * ε) * Real.exp (-(κ0 + κ1) * stSize X) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hε : 0 ≤ ε := le_trans (Finset.sum_nonneg fun H _ =>
    mul_nonneg (Real.exp_pos _).le (cutoffSup_nonneg _ _)) (hsite 0)
  have hc : 0 ≤ ((1 + 2 * d) * s ^ d * ε) := by positivity
  by_cases hX : IsAnimal (blockGraph d m') X
  swap
  · rw [blockActivity_eq_zero_of_not_isAnimal hβ hg hgν hν1 hγ hq hκ hγκ hp hn hρ1 hρ e src X hX Φ,
      abs_zero]
    positivity
  -- the main estimate
  set E : ℝ := ε * Real.exp (-(κ * X.card)) with hE
  have hS : ∀ x, ∑ H ∈ haloFibre d s m' X, cutoffSup p (f1SiteHalo e β ν src x H) ≤ E :=
    fun x => fibre_sum_le (fun H => cutoffSup_nonneg _ _) (hsite x) X
  have hB : ∀ x μ, ∑ H ∈ haloFibre d s m' X, cutoffSup p (f1BondHalo e β ν x μ H) ≤ E :=
    fun x μ => fibre_sum_le (fun H => cutoffSup_nonneg _ _) (hbond x μ) X
  have hE0 : 0 ≤ E := by positivity
  -- the site anchors
  have hsiteSum : ∑ x : Torus d (s * m'), ∑ H ∈ haloFibre d s m' X,
      |f1SiteHaloClip e β ν src x H p (toSites Φ)| ≤ (s ^ d * X.card : ℕ) * E := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => blockOf d s m' x ∈ X)]
    have hz : ∑ x ∈ Finset.univ.filter (fun x : Torus d (s * m') => ¬ blockOf d s m' x ∈ X),
        ∑ H ∈ haloFibre d s m' X, |f1SiteHaloClip e β ν src x H p (toSites Φ)| = 0 := by
      refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun H hH => ?_
      have hxX : blockOf d s m' x ∉ X := (Finset.mem_filter.1 hx).2
      rw [abs_eq_zero]
      refine (site_halo_decomposition (ℓ := s * m') hβ hg hgν hν1 hγ hq hs rfl hκ hγκ hp hn hρ1 hρ
        e src x).2.1 H ?_ _
      rintro ⟨-, hxH⟩
      exact hxX (by rw [← mem_haloFibre.1 hH]; exact Finset.mem_image_of_mem _ hxH)
    rw [hz, add_zero]
    have hcard : (Finset.univ.filter (fun x : Torus d (s * m') => blockOf d s m' x ∈ X)).card =
        s ^ d * X.card := card_siteSet d s m' X
    calc _ ≤ ∑ x ∈ Finset.univ.filter (fun x : Torus d (s * m') => blockOf d s m' x ∈ X), E :=
          Finset.sum_le_sum fun x _ => (Finset.sum_le_sum fun H _ =>
            abs_f1SiteHaloClip_le (ℓ := s * m') hβ hg hgν hν1 hq hs rfl hκ hγκ hp hn hρ1 hρ e
              src x H _).trans (hS x)
      _ = _ := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  -- the bond anchors
  have hbondSum : ∀ μ : Fin d, ∑ x : Torus d (s * m'), ∑ H ∈ haloFibre d s m' X,
      |f1BondHaloClip e β ν x μ H p (toSites Φ)| ≤ (2 * (s ^ d * X.card) : ℕ) * E := by
    intro μ
    set P : Torus d (s * m') → Prop := fun x => blockOf d s m' x ∈ X ∨
      blockOf d s m' (x + Pi.single μ 1) ∈ X with hP
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P]
    have hz : ∑ x ∈ Finset.univ.filter (fun x => ¬ P x),
        ∑ H ∈ haloFibre d s m' X, |f1BondHaloClip e β ν x μ H p (toSites Φ)| = 0 := by
      refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun H hH => ?_
      have hxX : ¬ P x := (Finset.mem_filter.1 hx).2
      rw [abs_eq_zero]
      refine (bond_halo_decomposition (ℓ := s * m') hβ hg hgν hγ hq hs rfl hκ hγκ hp hρ
        e x μ).2.1 H ?_ _
      rintro ⟨-, hxH⟩
      refine hxX ?_
      rw [hP]
      rcases hxH with hxH | hxH
      · right; rw [← mem_haloFibre.1 hH]; exact Finset.mem_image_of_mem _ hxH
      · left; rw [← mem_haloFibre.1 hH]; exact Finset.mem_image_of_mem _ hxH
    rw [hz, add_zero]
    calc _ ≤ ∑ x ∈ Finset.univ.filter P, E :=
          Finset.sum_le_sum fun x _ => (Finset.sum_le_sum fun H _ =>
            abs_f1BondHaloClip_le (ℓ := s * m') hβ hg hgν hq hs rfl hκ hγκ hp hρ e x μ H _).trans
            (hB x μ)
      _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_bondAnchors_le X μ) hE0
  -- assemble
  have hsum : |blockActivity e β ν p src X Φ| ≤ (s ^ d * X.card : ℕ) * E +
      d * ((2 * (s ^ d * X.card) : ℕ) * E) := by
    unfold blockActivity
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _) |>.trans hsiteSum
    · calc _ ≤ ∑ x : Torus d (s * m'), ∑ μ : Fin d, ∑ H ∈ haloFibre d s m' X,
            |f1BondHaloClip e β ν x μ H p (toSites Φ)| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ _ =>
              Finset.abs_sum_le_sum_abs _ _))
        _ = ∑ μ : Fin d, ∑ x : Torus d (s * m'), ∑ H ∈ haloFibre d s m' X,
            |f1BondHaloClip e β ν x μ H p (toSites Φ)| := Finset.sum_comm
        _ ≤ ∑ μ : Fin d, ((2 * (s ^ d * X.card) : ℕ) * E) :=
          Finset.sum_le_sum fun μ _ => hbondSum μ
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine hsum.trans ?_
  -- the exponential weight
  have hcardX : (stSize X) ≤ X.card := by
    unfold stSize
    exact_mod_cast steiner_le hX (Finset.Subset.refl X)
  have hX0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  have h1 : (X.card : ℝ) ≤ Real.exp X.card := by linarith [Real.add_one_le_exp (X.card : ℝ)]
  have h2 : (X.card : ℝ) * Real.exp (-(κ * X.card)) ≤ Real.exp (-(κ0 + κ1) * stSize X) := by
    calc (X.card : ℝ) * Real.exp (-(κ * X.card))
        ≤ Real.exp X.card * Real.exp (-(κ * X.card)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (X.card - κ * X.card) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(κ0 + κ1) * stSize X) := by
          refine Real.exp_le_exp.2 ?_
          have := mul_le_mul_of_nonneg_left hcardX hκ01'
          nlinarith
  have : ((s ^ d * X.card : ℕ) : ℝ) * E + d * (((2 * (s ^ d * X.card) : ℕ) : ℝ) * E) =
      ((1 + 2 * d) * s ^ d * ε) * ((X.card : ℝ) * Real.exp (-(κ * X.card))) := by
    rw [hE]; push_cast; ring
  rw [this]
  exact mul_le_mul_of_nonneg_left h2 hc

/-- The regrouped terms of the gas: `X ↦ H_X`, as complex-valued functions on the block
configuration space, for the nonempty block sets `X`. -/
noncomputable def gasTerm (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ)
    (src : Torus d (s * m') → Fin N → ℝ) (X : NePoly (Torus d m'))
    (Φ : ∀ b, BlockSpace d s m' (perp h) b) : ℂ :=
  ((blockActivity e β ν p src X.1 Φ : ℝ) : ℂ)

/-- **(T3, regrouping)** The activities `H_X`, `X` nonempty, add up to the sum over all anchors
and all site sets `H` of the clipped halo pieces. -/
theorem sum_blockActivity {β ν g γ κ p : ℝ} (hβ : 0 < β) (hg : 0 < g)
    (hgν : g ≤ ν) (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1)
    (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ) (hp : 0 < p) (hn : 1 ≤ n)
    (hρ1 : kf0Rho d g γ κ p β ≤ 1) (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (src : Torus d (s * m') → Fin N → ℝ)
    (Φ : ∀ b, BlockSpace d s m' (perp h) b) :
    ∑ X : NePoly (Torus d m'), blockActivity e β ν p src X.1 Φ =
      (∑ x : Torus d (s * m'), ∑ H : Finset (Torus d (s * m')),
        f1SiteHaloClip e β ν src x H p (toSites Φ)) +
      ∑ x : Torus d (s * m'), ∑ μ : Fin d, ∑ H : Finset (Torus d (s * m')),
        f1BondHaloClip e β ν x μ H p (toSites Φ) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  set T : Finset (Torus d (s * m')) → ℝ := fun H =>
    (∑ x : Torus d (s * m'), f1SiteHaloClip e β ν src x H p (toSites Φ)) +
      ∑ x : Torus d (s * m'), ∑ μ : Fin d, f1BondHaloClip e β ν x μ H p (toSites Φ) with hT
  have hT0 : T ∅ = 0 := by
    have h1 : ∀ x, f1SiteHaloClip e β ν src x ∅ p (toSites Φ) = 0 := fun x =>
      (site_halo_decomposition (ℓ := s * m') hβ hg hgν hν1 hγ hq hs rfl hκ hγκ hp hn hρ1 hρ
        e src x).2.1 ∅ (by rintro ⟨-, hx⟩; simp at hx) _
    have h2 : ∀ x μ, f1BondHaloClip e β ν x μ ∅ p (toSites Φ) = 0 := fun x μ =>
      (bond_halo_decomposition (ℓ := s * m') hβ hg hgν hγ hq hs rfl hκ hγκ hp hρ
        e x μ).2.1 ∅ (by rintro ⟨-, hx⟩; rcases hx with hx | hx <;> simp at hx) _
    simp only [hT, h1, h2]; simp
  have hfib : ∑ X : Finset (Torus d m'), ∑ H ∈ haloFibre d s m' X, T H =
      ∑ H : Finset (Torus d (s * m')), T H :=
    Finset.sum_fiberwise (Finset.univ : Finset (Finset (Torus d (s * m'))))
      (fun H => H.image (blockOf d s m')) T
  have hG0 : ∑ H ∈ haloFibre d s m' ∅, T H = 0 := by
    refine Finset.sum_eq_zero fun H hH => ?_
    have : H = ∅ := Finset.image_eq_empty.1 (mem_haloFibre.1 hH)
    rw [this, hT0]
  have hne : ∑ X : NePoly (Torus d m'), ∑ H ∈ haloFibre d s m' X.1, T H =
      ∑ X : Finset (Torus d m'), ∑ H ∈ haloFibre d s m' X, T H := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun X : Finset (Torus d m') => X.Nonempty),
      Finset.sum_eq_zero (s := Finset.univ.filter fun X : Finset (Torus d m') => ¬ X.Nonempty)
        (fun X hX => by
          have : X = ∅ := Finset.not_nonempty_iff_eq_empty.1 (Finset.mem_filter.1 hX).2
          rw [this]; exact hG0), add_zero]
    exact (Finset.sum_subtype (Finset.univ.filter fun X : Finset (Torus d m') => X.Nonempty)
      (by simp) (fun X => ∑ H ∈ haloFibre d s m' X, T H)).symm
  have hL : ∑ X : NePoly (Torus d m'), blockActivity e β ν p src X.1 Φ =
      ∑ X : NePoly (Torus d m'), ∑ H ∈ haloFibre d s m' X.1, T H :=
    Finset.sum_congr rfl fun X _ => blockActivity_eq e β ν p src X.1 Φ
  rw [hL, hne, hfib, hT, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_comm
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm

end Regroup

/-! ### (T4) The all-plus, all-small sector as a block gas -/

section Sector

open Balaban.LargeField.KF0Gas Balaban.Polymer SphereChart

open scoped Classical

variable {d N n s m' : ℕ} [NeZero s] [NeZero m'] {h : EuclideanSpace ℝ (Fin N)}

/-- **(T4, fixed parameters)**  The all-plus, all-`ψ`-small contribution of the one-scale model.
For a probability measure `γ₀` on the tangent space with `γ₀(‖w‖ ≤ p) ≠ 0`, the expectation under
`⨂ γ₀` of the cutoff event times the all-plus integrand (chart Jacobian times the exponential of the
interaction exponent at the tangent field `K_ν^{-1/2} ψ`) equals
`(1 - τ)^{#sites} e^{sourceConst}` times the exponential of the cluster series of the regrouped
activities `H_X` on the block torus, with the weighted cluster bound of `block_gas`.

The hypotheses are the landed small-regime hypotheses of `site_halo_decomposition`,
`bond_halo_decomposition`, `f1_integrand_eq`; the weighted bounds `hsite`, `hbond` (the
conclusions of `f1_weighted_small`); and the numerical hypotheses of `block_gas` with
`H0 = (1 + 2d) s^d ε`.  Only the all-plus, all-`ψ`-small sector is treated. -/
theorem allPlus_gas_of_weighted {β ν g γ κ p ε κ0 κ1 κ' : ℝ} (hβ : 0 < β) (hg : 0 < g)
    (hgν : g ≤ ν) (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1)
    (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ) (hp : 0 < p) (hn : 1 ≤ n)
    (hρ1 : kf0Rho d g γ κ p β ≤ 1) (hρ : (n : ℝ) * kf0Rho d g γ κ p β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (src : Torus d (s * m') → Fin N → ℝ)
    (hsite : ∀ x : Torus d (s * m'), ∑ H : Finset (Torus d (s * m')),
      Real.exp (κ * kf0BlockCount s m' H) * cutoffSup p (f1SiteHalo e β ν src x H) ≤ ε)
    (hbond : ∀ (x : Torus d (s * m')) (μ : Fin d), ∑ H : Finset (Torus d (s * m')),
      Real.exp (κ * kf0BlockCount s m' H) * cutoffSup p (f1BondHalo e β ν x μ H) ≤ ε)
    (hq0 : ((2 * d : ℕ) : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2)
    (hκ0 : Real.log 4 + 1 ≤ κ0) (hκ' : 0 ≤ κ') (hκg : κ' + κ0 + 1 ≤ κ1 - 3 / 2)
    (hH0 : 0 ≤ (1 + 2 * d) * s ^ d * ε) (hH0log : (1 + 2 * d) * s ^ d * ε ≤ Real.log 2)
    (hH0K : (1 + 2 * d) * s ^ d * ε * (4 * Real.exp (-κ0)) ≤ 1 / 4)
    (hκ01 : 1 + κ0 + κ1 ≤ κ)
    (γ₀ : Measure (perp h)) [IsProbabilityMeasure γ₀] (hpos : γ₀ (smallSet p) ≠ 0) :
    ((∫ ψ, Set.indicator (Set.pi Set.univ fun _ : Torus d (s * m') => smallSet p)
        (fun ψ : Torus d (s * m') → perp h =>
          chartJac β (fun x => ((tfield d (s * m') ν ψ x : perp h) : EuclideanSpace ℝ (Fin N))) *
            Real.exp (chartInteractionExponent β ν h src (tfield d (s * m') ν ψ))) ψ
        ∂(Measure.pi fun _ : Torus d (s * m') => γ₀) : ℝ) : ℂ) =
      (((1 - γ₀.real (largeSet p)) ^ Fintype.card (Torus d (s * m')) *
          Real.exp (sourceConst src h) : ℝ) : ℂ) *
        Complex.exp (logSeries (shareBlock (Subtype.val : NePoly (Torus d m') →
          Finset (Torus d m'))) (mayerK (blockRef (d := d) (s := s) (m' := m')
            (ProbabilityTheory.cond γ₀ (smallSet p)))
          (fun X : NePoly (Torus d m') => X.1) (gasTerm e β ν p src))) ∧
    ∀ b : Torus d m', ∑ Y ∈ (Finset.univ : Finset (Finset (Torus d m'))).filter
        (fun Y => b ∈ Y),
      ‖PY (shareBlock (Subtype.val : NePoly (Torus d m') → Finset (Torus d m')))
          Subtype.val (mayerK (blockRef (d := d) (s := s) (m' := m')
            (ProbabilityTheory.cond γ₀ (smallSet p)))
          (fun X : NePoly (Torus d m') => X.1) (gasTerm e β ν p src)) Y‖ *
        Real.exp (κ' * stSize Y) ≤
          64 * Real.exp 1 * ((1 + 2 * d) * s ^ d * ε) * Real.exp (-(2 * κ0)) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hκ01' : 0 ≤ κ0 + κ1 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have : IsProbabilityMeasure (ProbabilityTheory.cond γ₀ (smallSet p)) :=
    cond_smallSet_isProbabilityMeasure γ₀ p hpos
  set pc := ProbabilityTheory.cond γ₀ (smallSet p) with hpc
  -- the gas
  have hgas := block_gas (Ω := BlockSpace d s m' (perp h)) (μ := blockRef (d := d) (s := s)
    (m' := m') pc) hq0 hκ0 hκ' hκg hH0 hH0log hH0K (gasTerm e β ν p src)
    (fun X => blockActivity_depOn e β ν p src X.1)
    (fun X => measurable_blockActivity e β ν p src X.1)
    (fun X Φ => by
      have := blockActivity_abs_le hβ hg hgν hν1 hγ hq hκ hγκ hp hn hρ1 hρ e src hsite hbond
        hκ01 hκ01' X.1 Φ
      simpa [gasTerm, Complex.norm_real, Real.norm_eq_abs] using this)
  refine ⟨?_, hgas.2⟩
  -- the real integral
  set K : (Torus d (s * m') → perp h) → ℝ := fun ψ =>
    (∑ x : Torus d (s * m'), ∑ H : Finset (Torus d (s * m')), f1SiteHaloClip e β ν src x H p ψ) +
      ∑ x : Torus d (s * m'), ∑ μ : Fin d, ∑ H : Finset (Torus d (s * m')),
        f1BondHaloClip e β ν x μ H p ψ with hK
  have hKmeas : Measurable K := by
    refine Measurable.add (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun H _ =>
      measurable_f1SiteHaloClip e β ν src x H p)
      (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun μ _ =>
        Finset.measurable_sum _ fun H _ => measurable_f1BondHaloClip e β ν x μ H p)
  have hagree : Set.EqOn (fun ψ : Torus d (s * m') → perp h =>
          chartJac β (fun x => ((tfield d (s * m') ν ψ x : perp h) : EuclideanSpace ℝ (Fin N))) *
            Real.exp (chartInteractionExponent β ν h src (tfield d (s * m') ν ψ)))
      (fun ψ => Real.exp (sourceConst src h) * Real.exp (K ψ))
      (Set.pi Set.univ fun _ : Torus d (s * m') => smallSet p) := by
    intro ψ hψ
    have hψ' : ∀ y, ‖ψ y‖ ≤ p := fun y => hψ y (Set.mem_univ y)
    simp only
    rw [f1_integrand_eq (ℓ := s * m') hβ hg hgν hν1 hγ hq hs rfl hκ hγκ hp hn hρ1 hρ e src ψ hψ',
      ← Real.exp_add, hK]
    simp only [f1SiteHaloClip_eq_of_cutoff e β ν src _ _ hψ', f1BondHaloClip_eq_of_cutoff e β ν _ _
      _ hψ']
    rw [add_assoc]
  rw [Set.indicator_congr hagree, integral_indicator_small_eq γ₀ p hpos, integral_const_mul]
  have hI : ∫ ψ, Real.exp (K ψ) ∂(Measure.pi fun _ : Torus d (s * m') => pc) =
      ∫ Φ, Real.exp (∑ X : NePoly (Torus d m'), blockActivity e β ν p src X.1 Φ)
        ∂(Measure.pi (blockRef (d := d) (s := s) (m' := m') pc)) := by
    have hm : AEStronglyMeasurable (fun ψ => Real.exp (K ψ)) (Measure.map toSites
        (Measure.pi (blockRef (d := d) (s := s) (m' := m') pc))) :=
      (Real.measurable_exp.comp hKmeas).aestronglyMeasurable
    rw [← map_toSites_pi pc, integral_map measurable_toSites.aemeasurable hm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
    dsimp only
    rw [sum_blockActivity hβ hg hgν hν1 hγ hq hκ hγκ hp hn hρ1 hρ e src Φ, hK]
  have hC : ((∫ Φ, Real.exp (∑ X : NePoly (Torus d m'), blockActivity e β ν p src X.1 Φ)
        ∂(Measure.pi (blockRef (d := d) (s := s) (m' := m') pc)) : ℝ) : ℂ) =
      ∫ Φ, Complex.exp (∑ X : NePoly (Torus d m'), gasTerm e β ν p src X Φ)
        ∂(Measure.pi (blockRef (d := d) (s := s) (m' := m') pc)) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
    simp [gasTerm, Complex.ofReal_exp]
  rw [hI]
  push_cast
  rw [mul_assoc]
  congr 2
  rw [hC, hgas.1]

end Sector

end Balaban.LargeField.KF0AllPlus
