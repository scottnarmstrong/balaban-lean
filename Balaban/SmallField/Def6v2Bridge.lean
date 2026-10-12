/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2
public import Balaban.SmallField.RenormAnisoBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The bridge Def-6 v2 to I-6: the mass audit and the reduction to the landed bridge

Scheme A (W2-RESOLVE §4, the author's decision): the small-field class of the second version uses
**complete backgrounds at every scale**, solver mass `Rg.sfBgMass k = ν_k L^{-2k} > 0` also for
`k ≤ k₀`, where the landed class used the mass `Def6.bgMass = 0`.  This file ports the bridge from
the class to the premises of the anisotropic I-6 to that mass.

**Audit of the landed bridge** (`Def6Bridge*`, `Def6BridgeInf*`, `Def6Inf*`, `Def6Avg*`,
`RenormAnisoBridge*`, `RenormClass*`).  The value of the background mass is read in exactly four
landed lemmas:
* `Def6.bgMass_nonneg` (`0 ≤ μ`),
* `Def6.bgHyp_of_class` (`BgHyp`: `0 ≤ μ`, `μ L^{2k} ≤ 1`),
* `Def6.bgMass_mul_le_nuIdeal` (`μ L^{2j} ≤ ν_j`),
* `Def6.bgMass_mul_norm_div_le` (`μ L^{2j} |b/ν_j - t| ≤ |b - ν_j t|`, from the two preceding
  facts);
none of them uses that the mass vanishes.  Every other landed lemma carries the mass inside the
hypothesis `IsSF`/`IsSFFamily` and passes it to `xiDom_of_close`, `xiDom_of_aniso`,
`psiTildeC_subset_xiC`, which are stated for an arbitrary mass with `BgHyp`.  The coefficient `β`
enters the landed bridge only through `bgMass L k (β k) (ν k)`: the clauses `density`,
`CoeffBounds.beta_gt` and the constant `P.p` are not used by it.

Contents.
* The mass facts for an arbitrary mass: `physMass_mul_sq_eq_nuIdeal` (**equality**
  `μ L^{2j} = ν_j` at the complete mass), `mass_mul_norm_div_le`, `mass_mul_norm_div_eq`, the domain
  inclusions `xiDom_of_fieldM`, `polyAniso_subset_xiDomM` (the anisotropic polydisc in the source
  coordinate `b = ν_j h` lies in `Ξ^c_j` at **every** mass `0 ≤ μ`, `μ L^{2j} ≤ ν_j`, with radii
  that do not depend on the mass), and both instances: `polyAniso_subset_xiDom_sf` (complete mass,
  every level) and `bgMass_mul_norm_div_le_of_mass` (the landed lemma re-derived).
* `completeXiDom`: the main instance of the field domain, `Ξ^c_j(𝔹; 1, ε_j)` at the complete mass.
* **The reduction** `IsSFFamily2.toLanded`: the terms of a member of the second version on the
  wide domain at the complete mass are the terms of a member of the landed class in its complete
  regime, for the constants `P.noChi` (`P` with empty characteristic set), the coefficients
  `betaComplete`, `nuComplete` (`β'_k ν'_k > 1`, `ν'_k = ν_k`) and the zero density
  (`isSF_of_termClauses`).  Every landed statement about the terms then holds for the second
  version; the constants of `P` other than `p` are unchanged.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k N : ℕ} {ϱ : ℝ}

/-! ### The mass facts of the bridge, for an arbitrary mass -/

section Mass

/-- **`μ L^{2j} = ν_j` at the complete mass** `μ = ν_k L^{-2k}`, `ν_j = ν_k L^{-2(k-j)}`: the
inequality `Def6.bgMass_mul_le_nuIdeal` of the landed bridge is an equality at every level `j ≤ k`
for the solver mass of the second version. -/
theorem physMass_mul_sq_eq_nuIdeal [NeZero L] {j : ℕ} (hjk : j ≤ k) (νk : ℝ) :
    physMass L k νk * ((L : ℝ) ^ j) ^ 2 = nuIdeal L k νk j := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjk
  unfold physMass nuIdeal
  rw [Nat.add_sub_cancel_left, pow_add]
  field_simp

/-- `μ_k L^{2j} = ν_j` for the solver mass of the small-field class of a regime. -/
theorem Regime.sfBgMass_mul_sq [NeZero L] (Rg : Regime L) {j : ℕ} (hjk : j ≤ k) :
    Rg.sfBgMass k * ((L : ℝ) ^ j) ^ 2 = nuIdeal L k (Rg.ν k) j :=
  physMass_mul_sq_eq_nuIdeal hjk _

/-- **The mass-weighted field deviation is at most the deviation of the source `b = ν_j h`**, for
an arbitrary mass `0 ≤ μ` with `μ L^{2j} ≤ ν_j` (the landed `Def6.bgMass_mul_norm_div_le`, in which
the mass is `bgMass`). -/
theorem mass_mul_norm_div_le {μ νj : ℝ} {j : ℕ} (hνj : 0 < νj)
    (hm : μ * ((L : ℝ) ^ j) ^ 2 ≤ νj) (w t : ℂ) :
    μ * ((L : ℝ) ^ j) ^ 2 * ‖w / (νj : ℂ) - t‖ ≤ ‖w - (νj : ℂ) * t‖ := by
  have e : w / (νj : ℂ) - t = (w - (νj : ℂ) * t) / (νj : ℂ) := by
    have hνc : (νj : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
    field_simp
  rw [e, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hνj]
  calc μ * ((L : ℝ) ^ j) ^ 2 * (‖w - (νj : ℂ) * t‖ / νj)
      = (μ * ((L : ℝ) ^ j) ^ 2 / νj) * ‖w - (νj : ℂ) * t‖ := by field_simp
    _ ≤ 1 * ‖w - (νj : ℂ) * t‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [div_le_one hνj]; exact hm
    _ = _ := one_mul _

/-- **At the complete mass the two deviations are equal**: `μ L^{2j} |b/ν_j - t| = |b - ν_j t|`
when `μ L^{2j} = ν_j`.  The condition of the domain on the field is then exactly a condition on the
source `b = ν_j h`, with no dependence on the size of the mass. -/
theorem mass_mul_norm_div_eq {μ νj : ℝ} {j : ℕ} (hνj : 0 < νj)
    (hm : μ * ((L : ℝ) ^ j) ^ 2 = νj) (w t : ℂ) :
    μ * ((L : ℝ) ^ j) ^ 2 * ‖w / (νj : ℂ) - t‖ = ‖w - (νj : ℂ) * t‖ := by
  have e : w / (νj : ℂ) - t = (w - (νj : ℂ) * t) / (νj : ℂ) := by
    have hνc : (νj : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
    field_simp
  rw [hm, e, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hνj,
    mul_div_cancel₀ _ hνj.ne']

/-- The landed `Def6.bgMass_mul_norm_div_le`, re-derived from the statement for an arbitrary
mass. -/
theorem bgMass_mul_norm_div_le_of_mass [NeZero L] {β ν : ℕ → ℝ} {j : ℕ} (hν : 0 < ν k)
    (hjk : j ≤ k) (w t : ℂ) :
    Def6.bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 * ‖w / (nuIdeal L k (ν k) j : ℂ) - t‖ ≤
      ‖w - (nuIdeal L k (ν k) j : ℂ) * t‖ := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hνj : 0 < nuIdeal L k (ν k) j := by unfold nuIdeal; positivity
  exact mass_mul_norm_div_le hνj (bgMass_mul_le_nuIdeal (βk := β k) hν.le hjk) w t

variable [NeZero L] [NeZero N₁] {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a' : ℕ → ℝ}
  {μ νj : ℝ} {j : ℕ}

/-- **The domain inclusion, anisotropic field form, for an arbitrary mass** (the landed
`Def6.xiDom_of_fieldA` with `bgMass` replaced by a mass `μ` with `μ L^{2j} ≤ ν_j`): a torus field
`Ψ`, constant on the `j`-blocks, within `ρ_s` of `e_{i₀}`, and `h = b / ν_j` with
`|b - ν_j e_{i₀}| ≤ ρ_h` (componentwise) and `|b_{i₀} - ν_j| ≤ ρ_l` lie in `Ξ^c_j(𝔹; 1, ε)` at the
mass `μ`.  The radii `ρ_s, ρ_h, ρ_l` are those of `xiDom_of_aniso`; they do not involve `μ`. -/
theorem xiDom_of_fieldM (H : BgHyp d L k ϱ a' μ) (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k)
    (hνj : 0 < νj) (hm : μ * ((L : ℝ) ^ j) ^ 2 ≤ νj) (i₀ : Fin N) {δ ρs ρh ρl ε : ℝ}
    (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N) (hρs0 : 0 ≤ ρs)
    (hρh0 : 0 ≤ ρh) (hρs : 4 * N * ρs ≤ δ) (hρh : 2 * N * ρh ≤ δ) (hρl : ρl < δ ^ 2)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ ε) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ)
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρs)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    (hb : ∀ i, ‖b i - (νj : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρh)
    (hbl : ‖b i₀ - (νj : ℂ)‖ ≤ ρl) :
    XiDom G a' μ j ε Ψ (fun _ i => b i / (νj : ℂ)) := by
  refine xiDom_of_aniso H hΩ hjk i₀ hδ0 hδc0 hδc1 hρs0 hρh0 hρs hρh hρl hε Ψ
    (fun i => b i / (νj : ℂ)) hΨ hΨb (fun i => ?_) ?_
  · exact (mass_mul_norm_div_le hνj hm _ _).trans (hb i)
  · have := mass_mul_norm_div_le (L := L) hνj hm (b i₀) 1
    rw [mul_one] at this
    exact this.trans hbl

/-- **The anisotropic polydisc lies in `Ξ^c_j` at every mass** (the landed `Def6.fp_mem_xiDomA`
for an arbitrary mass): the configurations of the polydisc `polyAniso i₀ ν_j r X'` around the
reference point `(e_{i₀}, ν_j e_{i₀})` in the variables `(ψ, b = ν_j h)` give torus fields in
`Ξ^c_j(𝔹; 1, ε)` at the mass `μ`, for `0 < r ≤ 1`, `4 N r ≤ δ`, `0 < δ ≤ min (c₀, c₁)`,
`(2 K₁ + 2) δ ≤ ε`, whenever `0 ≤ μ`, `μ L^{2k} ≤ 1` (`BgHyp`) and `μ L^{2j} ≤ ν_j`.  The radius
`r` does not depend on the mass. -/
theorem polyAniso_subset_xiDomM (H : BgHyp d L k ϱ a' μ) (hΩ : ∀ i, j < i → G.Ω i = ∅)
    (hjk : j ≤ k) (hνj : 0 < νj) (hm : μ * ((L : ℝ) ^ j) ^ 2 ≤ νj) (i₀ : Fin N) {δ r ε : ℝ}
    (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hrδ : 4 * N * r ≤ δ) (hε : (2 * bgK1 d L N + 2) * δ ≤ ε) {X' : Finset (Site d)}
    {c : Cfg d N X'} (hc : c ∈ polyAniso i₀ νj r X') :
    XiDom G a' μ j ε (fieldOf j i₀ X' c) (hOf νj X' c) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hrδ' : r < δ := by nlinarith
  exact xiDom_of_fieldM H hΩ hjk hνj hm i₀ hδ0 hδc0 hδc1 hr0.le hr0.le hrδ (by nlinarith)
    (by nlinarith) hε _ (fun i => c (Sum.inr i)) (fun x i => fieldOf_sub_le_poly hc hr0.le x i)
    (fun _ _ h => fieldOf_block c h) (fun i => (polyAniso_inr hc hr0 hr1 i).le)
    (polyAniso_inr_self hc).le

end Mass

/-! ### The main instance of the field domain -/

/-- **The main instance of the field domain of the second version** (Scheme A): on every torus
the wide P1/P4 domain `Ξ^c_j(𝔹; 1, ε_j)` in the source `b_j = ν_j h` (`xiFieldDom`), with the kernel
sequence of the ideal flow matched at `k` and the **complete** solver mass `Rg.sfBgMass k` at
every level `j ≤ k`. -/
noncomputable abbrev completeXiDom [NeZero L] (P : Consts) (Rg : Regime L) (a : ℕ → ℝ) :
    ∀ (N₁ : ℕ) [NeZero N₁], FieldDom d L N₁ m₁ k N ϱ :=
  fun _ _ => xiFieldDom (aIdeal L k (a k)) (Rg.sfBgMass k) (P.eps d L)

section Complete

variable [NeZero L] [NeZero N₁] {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}

/-- **The domain inclusion of the second version, at every level** (the port of
`Def6.fp_mem_xiDomA` to complete backgrounds): for the terms of the class on the wide domain at
the complete mass, at every scale `1 ≤ j ≤ k` -- also below the switch of the landed class -- the
anisotropic polydisc of radius `r` (`AnisoRadiusOK`) in the variables `(ψ, b = ν_j h)` around
`(e_{i₀}, ν_j e_{i₀})` lies in the domain of the term of a polymer.  The radius condition does not
involve the mass. -/
theorem polyAniso_subset_xiDom_sf (hT : SFTermClauses P
      (xiFieldDom (aIdeal L k (a k)) (Rg.sfBgMass k) (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (Rg.sfBgMass k)) (hν : 0 < Rg.ν k) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (i₀ : Fin N)
    {r : ℝ} (hr : AnisoRadiusOK d L N P j r) {c : Cfg d N X'}
    (hc : c ∈ polyAniso i₀ (nuIdeal L k (Rg.ν k) j) r X') :
    (xiFieldDom (d := d) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) (aIdeal L k (a k)) (Rg.sfBgMass k)
      (P.eps d L)).dom j (Tm.gs j (Ypoly j X')) (fieldOf j i₀ X' c)
        (hOf (nuIdeal L k (Rg.ν k) j) X' c) := by
  obtain ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ := hr
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hνj : 0 < nuIdeal L k (Rg.ν k) j := by unfold nuIdeal; positivity
  have hNB : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
  have hrδ' : 4 * (N : ℝ) * r ≤ δ := by
    have h1 : r ≤ r * (1 + N * rotB N) := by nlinarith
    have hN0 : (0 : ℝ) ≤ 4 * N := by positivity
    calc 4 * (N : ℝ) * r ≤ 4 * N * (r * (1 + N * rotB N)) := mul_le_mul_of_nonneg_left h1 hN0
      _ ≤ δ := hrδ
  exact polyAniso_subset_xiDomM hBg (hT.gs_spec j hj1 hjk _ hX).2 hjk hνj
    (Rg.sfBgMass_mul_sq hjk).le i₀ hδ0 hδc0 hδc1 hr0 hr1 hrδ' hε hc

end Complete

/-! ### Constants with empty characteristic set -/

/-- **The constants `P` with the radius function of `χ_k` replaced by `0`**: the characteristic
set `Ξ_k(1, β_k^{-1/2} p(β_k))` of the density clause (H.1) is then empty.  All the other constants
are those of `P`. -/
def _root_.Balaban.SmallField.Def6.Consts.noChi (P : Consts) : Consts :=
  { P with p := fun _ => 0 }

theorem noChi_eps (d L : ℕ) (P : Consts) : P.noChi.eps d L = P.eps d L := rfl

theorem noChi_p (P : Consts) (x : ℝ) : P.noChi.p x = 0 := rfl

theorem _root_.Balaban.SmallField.Def6.Consts.Admissible.noChi {d L : ℕ} {P : Consts}
    (h : P.Admissible d L) : P.noChi.Admissible d L :=
  ⟨h.γ_pos, h.γ_lt, h.α₁_pos, h.α₁_lt, h.α₀_pos, h.κ_pos, h.νbar_pos, h.νbar_le, h.c₈_pos,
    h.E₀_nonneg⟩

theorem _root_.Balaban.SmallField.Def6.CoeffBounds.noChi {d L k : ℕ} {P : Consts}
    {β ν a : ℕ → ℝ} (h : CoeffBounds d L k P β ν a) : CoeffBounds d L k P.noChi β ν a :=
  ⟨h.flow, h.beta_gt, h.nu_pos, h.nu_le, h.a_ge, h.a_lt⟩

theorem SFTermClauses.noChi [NeZero L] [NeZero N₁] {P : Consts}
    {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ} (h : SFTermClauses P Dom Tm) :
    SFTermClauses P.noChi Dom Tm :=
  ⟨h.gs_spec, h.analyticE, h.analyticM, h.rotE, h.pavingGS, h.eucE, h.eucEloc, h.rotM, h.eucM,
    h.eucMloc, h.localE, h.localM, h.boundE, h.boundM⟩

/-- **The term clauses give a member of the landed class with zero density** when the
characteristic set is empty (`p(β_k) = 0`): the density clause (H.1) of `Def6.IsSF` then reads
`ρ = 0`, and the other clauses are the term clauses on the landed domain.  (The landed bridge to
I-6 does not use the density clause.) -/
theorem isSF_of_termClauses [NeZero L] [NeZero N₁] {P : Consts} {β ν a : ℕ → ℝ}
    {Tm : Terms d L N₁ m₁ k N ϱ} {Ek : ℝ} (hp : P.p (β k) = 0)
    (hT : SFTermClauses P
      (xiFieldDom (aIdeal L k (a k)) (Def6.bgMass L k (β k) (ν k)) (P.eps d L)) Tm) :
    IsSF P β ν a Tm (fun _ _ _ => 0) Ek where
  density := by
    intro Ψ₀ h₀ g D _ _
    have hX : ¬ Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Def6.bgMass L k (β k) (ν k)) k 1
        (P.p (β k) / Real.sqrt (β k)) Ψ₀ h₀ := by
      rw [hp, zero_div]
      exact fun h => lt_irrefl _ h.2.1
    rw [ite_eq_right fun h => absurd h hX]
    simp
  gs_spec := hT.gs_spec
  analyticE := hT.analyticE
  analyticM := hT.analyticM
  rotE := hT.rotE
  pavingGS := hT.pavingGS
  eucE := hT.eucE
  eucEloc := hT.eucEloc
  rotM := hT.rotM
  eucM := hT.eucM
  eucMloc := hT.eucMloc
  localE := hT.localE
  localM := hT.localM
  boundE := hT.boundE
  boundM := hT.boundM

/-! ### Coefficients in the complete regime of the landed class -/

/-- The coefficients `β'_n = (|B| + 1 + ν_k^{-1}) L^{n(d-2)}` of a free flow with
`β'_k ν_k > 1` and `β'_k > B L^{k(d-2)}`. -/
noncomputable def betaComplete (d L : ℕ) (P : Consts) (νk : ℝ) (n : ℕ) : ℝ :=
  (|P.B| + 1 + νk⁻¹) * (L : ℝ) ^ (n * (d - 2))

/-- The masses `ν'_n = ν_k L^{-2k} L^{2n}` of the free flow through `ν_k` at `n = k`. -/
noncomputable def nuComplete (L k : ℕ) (νk : ℝ) (n : ℕ) : ℝ :=
  νk * ((L : ℝ) ^ k)⁻¹ ^ 2 * (L : ℝ) ^ (2 * n)

theorem nuComplete_self [NeZero L] (k : ℕ) (νk : ℝ) : nuComplete L k νk k = νk := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold nuComplete
  rw [pow_mul, pow_right_comm]
  field_simp

theorem one_lt_betaComplete_mul [NeZero L] (d k : ℕ) (P : Consts) {νk : ℝ} (hν : 0 < νk) :
    1 < betaComplete d L P νk k * νk := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL
  have h2 : 0 ≤ |P.B| := abs_nonneg _
  have h3 : νk⁻¹ * νk = 1 := inv_mul_cancel₀ hν.ne'
  have h4 : 1 < (|P.B| + 1 + νk⁻¹) * νk := by nlinarith
  unfold betaComplete
  calc 1 < (|P.B| + 1 + νk⁻¹) * νk := h4
    _ ≤ (|P.B| + 1 + νk⁻¹) * νk * (L : ℝ) ^ (k * (d - 2)) :=
        le_mul_of_one_le_right (by linarith) h1
    _ = _ := by ring

/-- The running-test mass of the landed class at the coefficients `betaComplete`, `nuComplete` is
the complete mass `ν_k L^{-2k}`. -/
theorem bgMass_complete [NeZero L] (d k : ℕ) (P : Consts) {νk : ℝ} (hν : 0 < νk) :
    Def6.bgMass L k (betaComplete d L P νk k) (nuComplete L k νk k) = physMass L k νk := by
  rw [nuComplete_self]
  unfold Def6.bgMass physMass
  rw [ite_eq_right fun h => absurd h (not_le.2 (one_lt_betaComplete_mul d k P hν))]

/-- **The coefficient bounds (H.6) hold for the free flow** `betaComplete`, `nuComplete` (with
`ξ = 0`), given them for some running coefficients with the same `ν_k`, `a_k`. -/
theorem coeffBounds_complete [NeZero L] {d k : ℕ} {P : Consts} {β ν a : ℕ → ℝ}
    (hP : P.Admissible d L) (hC : CoeffBounds d L k P β ν a) :
    CoeffBounds d L k P (betaComplete d L P (ν k)) (nuComplete L k (ν k)) a where
  flow := by
    have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    obtain ⟨-, -, -, -, hs, -⟩ := hC.flow
    refine ⟨0, |P.B| + 1 + (ν k)⁻¹, ν k * ((L : ℝ) ^ k)⁻¹ ^ 2, fun n => ?_, hs,
      fun n _ => ⟨?_, ?_⟩⟩
    · have h1 := Flow.rate_pos hL P.γ
      have h2 := hP.c₈_pos
      rw [Pi.zero_apply, norm_zero]
      positivity
    · rw [Flow.betaSeq_eq]
      simp [Flow.gammaSeq, betaComplete]
    · rw [Flow.nuSeq_eq]
      simp [Flow.deltaSeq, nuComplete]
  beta_gt := by
    have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have h1 : 0 < (L : ℝ) ^ (k * (d - 2)) := by positivity
    have h2 : P.B ≤ |P.B| := le_abs_self _
    have h3 : 0 < (ν k)⁻¹ := inv_pos.2 hC.nu_pos
    unfold betaComplete
    exact mul_lt_mul_of_pos_right (by linarith) h1
  nu_pos := by rw [nuComplete_self]; exact hC.nu_pos
  nu_le := by rw [nuComplete_self]; exact hC.nu_le
  a_ge := hC.a_ge
  a_lt := hC.a_lt

/-! ### The reduction to the landed class -/

section Reduction

variable [NeZero L] {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρ : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}

/-- **The reduction of the second version to the landed class** (the port of the bridge).  The
terms of a member of the second version on the wide domain `Ξ^c_j` at the **complete** mass --
at every level, also for `k ≤ k₀` -- are the terms of a member of the landed class `Def6.IsSFFamily`
in its complete regime: for the constants `P.noChi`, coefficients `β', ν'` with `ν'_k = ν_k` and
running-test mass `bgMass L k (β'_k) (ν'_k) = ν_k L^{-2k}` (so `β'_k ν'_k > 1`), and the zero
density.  The clauses `torusIndep` and `renorm` (H.5) are the same.

Consequently every landed statement on the terms of `Def6.IsSFFamily`, in which the coefficient
`β` enters only through `bgMass L k (β k) (ν k)`, holds for the second version at the complete
mass. -/
theorem IsSFFamily2.toLanded (h : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρ Ek) :
    ∃ β' ν' : ℕ → ℝ, ν' k = Rg.ν k ∧ Def6.bgMass L k (β' k) (ν' k) = Rg.sfBgMass k ∧
      IsSFFamily P.noChi β' ν' a Tm (fun _ _ _ _ _ => 0) Ek := by
  have hν := h.coeff.nu_pos
  have hμ : Def6.bgMass L k (betaComplete d L P (Rg.ν k) k) (nuComplete L k (Rg.ν k) k) =
      Rg.sfBgMass k := bgMass_complete d k P hν
  refine ⟨betaComplete d L P (Rg.ν k), nuComplete L k (Rg.ν k), nuComplete_self k _, hμ, ?_⟩
  refine
    { admissible := h.admissible.noChi
      coeff := (coeffBounds_complete h.admissible h.coeff).noChi
      torus := fun N₁ _ => isSF_of_termClauses (P := P.noChi) rfl ?_
      torusIndep := h.torusIndep
      renorm := fun j hj1 hjk => ?_ }
  · rw [hμ]
    exact (h.torus N₁).terms.noChi
  · rw [nuComplete_self]
    exact h.renorm j hj1 hjk

end Reduction

end Balaban.SmallField.Def6v2
