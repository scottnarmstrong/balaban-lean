/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormAnisoDomain
public import Balaban.SmallField.Def6RotFramesAniso
public import Balaban.SmallField.XiDomOpen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Complex invariance of the term on the anisotropic polydisc, for the field domain `xiFieldDom`

`rotE_aniso_of_xiFieldDom`: for the term clauses on `xiFieldDom a μ ε_j` (any mass `μ` with
`μ L^{2j} ≤ ν_j`, `ν_j ≤ ν̄`), the term `ℰ(y, X)` takes the same value at two fields
`(Ψ, h)`, `(MΨ, Mh)` of the anisotropic polydisc related by a complex orthogonal matrix `M` with
entries `≤ B`, whenever `r · aniK N B ν̄ ≤ δ`.  It is the common engine of the frame bridges
(`Eaux_rotA`, `EauxC_rotA`, `shiftTerm_rotA`): no hypothesis `CRotE`; the path is the two-stage
Cayley path of `Def6RotFramesAniso`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Topology Filter Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem rotE_aniso_of_xiFieldDom {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
    {j : ℕ} (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm) (hBg : BgHyp d L k ϱ a μ)
    (hν : 0 < ν) (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ P.νbar) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) {y X} (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) (i₀ : Fin N)
    {δ r B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hB : 0 ≤ B) (hrδ : r * aniK N B P.νbar ≤ δ)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.transpose * M = 1)
    {Ψ h : Fld d L N₁ m₁ k N} (hΨb : IsBlockConstFld j Ψ) (hh : ∀ x x', h x = h x')
    (hMe : ∀ i, ‖(M *ᵥ (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤
      r * (1 + N * B))
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r)
    (hΨM : ∀ x i, ‖M.mulVec (Ψ x) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r * (1 + N * B))
    (hb : ∀ x i, ν * ‖h x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r)
    (hbl : ∀ x, ν * ‖h x i₀ - 1‖ ≤ r ^ 2)
    (hbM : ∀ x i, ν * ‖M.mulVec (h x) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r)
    (hbMl : ∀ x, ν * ‖M.mulVec (h x) i₀ - 1‖ ≤ r ^ 2) :
    Tm.E j y X (rotField M Ψ) (rotField M h) = Tm.E j y X Ψ h := by
  have hδ1 : δ ≤ 1 / 16 := hδc0.trans (bgC0_le d L N)
  obtain ⟨e1, e2, e3, e4, e5⟩ := aniso_box_arith i₀ hr0 hr1 hB hνb hrδ hδ1
  have hΩ := (hcl.gs_spec j hj1 hjk X hX).2
  have hx0 : 0 ≤ r * (1 + N * B) := by positivity
  have hrr : r ^ 2 ≤ r := by nlinarith
  refine hcl.rotE_of_near_aniso hj1 hjk hX hy hM i₀ hν (r := r) (r' := r * (1 + N * B)) (rb := r)
    (rb' := r) (rl := r ^ 2) (rl' := r ^ 2) (re := r * (1 + N * B))
    (ρs := Real.sqrt N * (r + (2 * (r * (1 + N * B)) + 8 * (r * (1 + N * B)))))
    (ρb := Real.sqrt N * (r + (2 * r + 4 * (r * (1 + N * B)) * (ν + r ^ 2 + r))))
    (ρl := r ^ 2 * (1 + 2 * N * (1 + N * B) * (1 + 2 * (1 + N * B) * (P.νbar + 2))))
    hr0.le hx0 e2 hr0.le (by positivity) hrr hx0 e1 hMe le_rfl le_rfl ?_ ?_ ?_ ?_ hΨb hh hΨ hΨM hb hbl
    hbM hbMl
  · -- rl ≤ ρl
    have hK : (1 : ℝ) ≤ 1 + 2 * N * (1 + N * B) * (1 + 2 * (1 + N * B) * (P.νbar + 2)) := by
      have : 0 ≤ 2 * (N : ℝ) * (1 + N * B) * (1 + 2 * (1 + N * B) * (P.νbar + 2)) := by
        have : 0 ≤ P.νbar := (hν.le.trans hνb)
        positivity
      linarith
    nlinarith [sq_nonneg r]
  · -- the first-stage longitudinal change
    have hν2 : ν + r ^ 2 + r ≤ P.νbar + 2 := by nlinarith
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have h0 : 0 ≤ P.νbar := hν.le.trans hνb
    calc r ^ 2 + 2 * (N * (r * (1 + N * B)) * (r + 2 * (r * (1 + N * B)) * ((ν + r ^ 2) + r)))
        = r ^ 2 * (1 + 2 * N * (1 + N * B) * (1 + 2 * (1 + N * B) * (ν + r ^ 2 + r))) := by ring
      _ ≤ r ^ 2 * (1 + 2 * N * (1 + N * B) * (1 + 2 * (1 + N * B) * (P.νbar + 2))) := by
          gcongr
  · -- box membership
    intro Ψ' h' hΨ'b hh' hs hb' hl'
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have hnu : 0 ≤ P.νbar := hν.le.trans hνb
    have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have hρs0 : 0 ≤ Real.sqrt N * (r + (2 * (r * (1 + N * B)) + 8 * (r * (1 + N * B)))) := by
      positivity
    have hρb0 : 0 ≤ Real.sqrt N * (r + (2 * r + 4 * (r * (1 + N * B)) * (ν + r ^ 2 + r))) := by
      positivity
    have hX' := xiDom_of_fieldM (j := j) (G := Tm.gs j X) hBg hΩ hjk hν hμν i₀ hδ0 hδc0 hδc1
      hρs0 hρb0 e3 e4 e5 hε Ψ' (fun i => (ν : ℂ) * h' 0 i) hs
      (fun x x' hxx => hΨ'b x x' hxx) (fun i => by
        rw [show (ν : ℂ) * h' 0 i - (ν : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i =
          (ν : ℂ) * (h' 0 i - (Pi.single i₀ 1 : Fin N → ℂ) i) by ring, ← nu_mul_norm hν]
        exact hb' 0 i) (by
        rw [show (ν : ℂ) * h' 0 i₀ - (ν : ℂ) = (ν : ℂ) * (h' 0 i₀ - 1) by ring,
          ← nu_mul_norm hν]
        exact hl' 0)
    have hν0 : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
    have e : (fun (_ : CTorus d L N₁ m₁ k) i => (ν : ℂ) * h' 0 i / (ν : ℂ)) = h' := by
      funext x i
      rw [mul_div_cancel_left₀ _ hν0, hh' 0 x]
    rw [e] at hX'
    exact hX'
  · intro Ψ' h' hΨ'b hh' hdom
    have hev := Balaban.Fluctuation.xiDom_eventually hBg hdom
    have hsub : {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N |
        IsBlockConstFld j p.1 ∧ ∀ x x', p.2 x = p.2 x'} ⊆
        Balaban.Fluctuation.layerSub (Tm.gs j X) := fun p hp =>
      ⟨isLayerConstant_of_jBlock hjk hΩ hp.1, isLayerConstant_of_jBlock hjk hΩ
        (fun x x' _ => hp.2 x x')⟩
    exact hev.filter_mono (nhdsWithin_mono _ hsub)

theorem nuIdeal_le {νk : ℝ} (hν : 0 ≤ νk) (j : ℕ) : nuIdeal L k νk j ≤ νk := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  unfold nuIdeal
  have h1 : ((L : ℝ) ^ (k - j))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL)
  have h2 : (((L : ℝ) ^ (k - j))⁻¹) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ ((L : ℝ) ^ (k - j))⁻¹ := by positivity
    nlinarith
  calc νk * (((L : ℝ) ^ (k - j))⁻¹) ^ 2 ≤ νk * 1 := mul_le_mul_of_nonneg_left h2 hν
    _ = νk := mul_one _

theorem nu_mul_hOf_sub {ν : ℝ} (hν : 0 < ν) {S : Finset (Site d)} (c : Cfg d N S)
    (x : CTorus d L N₁ m₁ k) (i₀ i : Fin N) :
    ν * ‖hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c x i -
        (Pi.single i₀ 1 : Fin N → ℂ) i‖ =
      ‖c (Sum.inr i) - (ν : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i‖ := by
  rw [nu_mul_norm hν]
  congr 1
  have hν0 : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  simp only [hOf]
  field_simp

theorem nu_mul_hOf_long {ν : ℝ} (hν : 0 < ν) {S : Finset (Site d)} (c : Cfg d N S)
    (x : CTorus d L N₁ m₁ k) (i₀ : Fin N) :
    ν * ‖hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c x i₀ - 1‖ =
      ‖c (Sum.inr i₀) - (ν : ℂ)‖ := by
  have := nu_mul_hOf_sub hν c x i₀ i₀
  simpa using this

/-- **Complex invariance of the term on the anisotropic polydisc, for a family of fields**
`Φ c` of the configurations `c` of the polymer `S`: block-constant fields within `r` of `e` on the
polydisc, which, for the two related configurations, are on every site either rotated by `M` or
equal to `e`, and rotated at one site `x₀` (which is how `|M e - e|` is controlled). -/
theorem E_rotA_cfg {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm) (hBg : BgHyp d L k ϱ a μ)
    (hν : 0 < ν) (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ P.νbar) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) {y X} (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) (i₀ : Fin N)
    {δ r B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hB : 0 ≤ B) (hrδ : r * aniK N B P.νbar ≤ δ)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.transpose * M = 1) (hMb : ∀ i k, ‖M i k‖ ≤ B)
    {S : Finset (Site d)} {u u' : Cfg d N S} (hu : u ∈ polyAniso i₀ ν r S)
    (hu' : u' ∈ polyAniso i₀ ν r S) (hrot : rotCfgL M S u = u')
    (Φ : Cfg d N S → Fld d L N₁ m₁ k N) (hΦb : ∀ c, IsBlockConstFld j (Φ c))
    (hΦ : ∀ c ∈ polyAniso i₀ ν r S, ∀ x i,
      ‖Φ c x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r)
    (hΦrot : ∀ x, Φ u' x = M.mulVec (Φ u x) ∨ Φ u x = (Pi.single i₀ 1 : Fin N → ℂ))
    (x₀ : CTorus d L N₁ m₁ k) (hx₀ : Φ u' x₀ = M.mulVec (Φ u x₀)) :
    Tm.E j y X (rotField M (Φ u)) (rotField M (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S u)) =
      Tm.E j y X (Φ u) (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S u) := by
  have hMe := mulVec_single_sub_le (r := r) hB hMb i₀ (a := Φ u x₀) (a' := Φ u' x₀)
    (fun i => hΦ u hu x₀ i) (fun i => hΦ u' hu' x₀ i) hx₀
  have hx : 0 ≤ (N : ℝ) * B := by positivity
  have hrr : r ≤ r * (1 + N * B) := by nlinarith
  have hhOf : hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S u' =
      rotField M (hOf ν S u) := by rw [← hrot, hOf_rot]
  refine rotE_aniso_of_xiFieldDom hcl hBg hν hμν hνb hj1 hjk hX hy i₀ hδ0 hδc0 hδc1 hr0 hr1 hB hrδ
    hε hM (hΦb u) (fun _ _ => rfl) hMe (fun x i => hΦ u hu x i) (fun x i => ?_)
    (fun x i => ?_) (fun x => ?_) (fun x i => ?_) (fun x => ?_)
  · rcases hΦrot x with h1 | h1
    · rw [← h1]; exact (hΦ u' hu' x i).trans hrr
    · rw [h1]; exact hMe i
  · rw [nu_mul_hOf_sub hν]
    exact (polyAniso_inr hu hr0 hr1 i).le
  · rw [nu_mul_hOf_long hν]
    exact (polyAniso_inr_self hu).le
  · have e : M.mulVec (hOf ν S u x) = hOf ν S u' x := by rw [hhOf]; rfl
    rw [e, nu_mul_hOf_sub hν]
    exact (polyAniso_inr hu' hr0 hr1 i).le
  · have e : M.mulVec (hOf ν S u x) = hOf ν S u' x := by rw [hhOf]; rfl
    rw [e, nu_mul_hOf_long hν]
    exact (polyAniso_inr_self hu').le

end Balaban.SmallField.Def6v2
