/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorus
public import Balaban.SmallField.RenormAnisoBridge
public import Balaban.SmallField.RenormClassTube
public import Balaban.SmallField.Def6BridgeGeom
public import Balaban.SmallField.Def6InfCov
public import Balaban.SmallField.Def6InfExpand
public import Balaban.SmallField.Def6v2Bridge
public import Balaban.Fluctuation.LocalClassAssembly
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The term of a label pulled back at its centre, on the anisotropic tube

For a label `(j, y, X)` of a torus (`y` an `L^j`-aligned site of the polymer `X ∈ 𝒟_j`) and a
finite set `S` of sites of `ℤ^d` placing the blocks of `X` relative to `y` (`x ↦ unlift (x - y)`),
the term `ℰ(y, X)` pulled back at `y` is the function
`F(c) = ℰ(y, X; z ↦ fieldOf c (z - y), hOf c)` of the configurations `c` of `S` (the centred form
of FLUCTUATION.md §3.2; the landed `Eaux`, `termLA` are the case `y = 0`).  Here, for the class on
its main instance `xiFieldDom a μ ε_j` (any background mass `μ` with `μ L^{2j} ≤ ν_j`):

* `xiDom_hOf_poly`, `xiDom_shift_poly`: the configurations of the anisotropic polydisc around the
  reference point give fields in `Ξ^c_j(𝔹_j(X); 1, ε_j)` (`xiDom_of_fieldM`);
* `analyticAt_shiftTerm`, `shiftTerm_rotA`, `shiftTerm_orthA`: `F` is analytic on the polydisc and
  invariant under the complex orthogonal matrices relating two of its points (`CRotE`, through one
  real reflection for `det = -1`);
* `premisesTermAniso_centred`: the one-polymer family `{S}` with the extension of `F` to the tube
  (`trickFnA`) satisfies `PremisesTermAniso` (the geometric field from (G5)).
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-! ### The field of a configuration placed at the centre `y` -/

section Shift

variable {j : ℕ} {i₀ : Fin N} {S : Finset (Site d)}

theorem jBlock_sub_eq_of_jBlock_eq (hjk : j ≤ k) {y : CTorus d L N₁ m₁ k}
    (hy : Aligned (L ^ j) y) {z z' : CTorus d L N₁ m₁ k}
    (h : jBlock d L (N₁ * L ^ m₁) k j z = jBlock d L (N₁ * L ^ m₁) k j z') :
    jBlock d L (N₁ * L ^ m₁) k j (z - y) = jBlock d L (N₁ * L ^ m₁) k j (z' - y) := by
  have hdvd : L ^ j ∣ N₁ * L ^ m₁ * L ^ k := by rw [side_eq hjk]; exact dvd_mul_right _ _
  have hc := cbase_pow_eq_of_jBlock hjk h
  have hny : Aligned (L ^ j) (-y) := aligned_neg hdvd hy
  have e1 : cbase (L ^ j) (z - y) = cbase (L ^ j) (z' - y) := by
    rw [sub_eq_neg_add, sub_eq_neg_add, cbase_add_aligned hdvd hny, cbase_add_aligned hdvd hny, hc]
  rw [← jBlock_cbase (z - y), e1, jBlock_cbase]

theorem shiftField_block (hjk : j ≤ k) {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (c : Cfg d N S) {z z' : CTorus d L N₁ m₁ k}
    (h : jBlock d L (N₁ * L ^ m₁) k j z = jBlock d L (N₁ * L ^ m₁) k j z') :
    fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y) =
      fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z' - y) :=
  fieldOf_block c (jBlock_sub_eq_of_jBlock_eq hjk hy h)

theorem analyticAt_shift_fp (j : ℕ) (i₀ : Fin N) (νj : ℝ) (y : CTorus d L N₁ m₁ k)
    (S : Finset (Site d)) (c₀ : Cfg d N S) :
    AnalyticAt ℂ (fun c : Cfg d N S =>
      ((fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y),
        hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) νj S c) :
          Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N)) c₀ := by
  refine AnalyticAt.prod ?_ ?_
  · refine analyticAt_pi_iff.2 fun z => analyticAt_pi_iff.2 fun i => ?_
    by_cases h : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S
    · simp only [fieldOf, h, dite_true]
      exact analyticAt_proj _ c₀
    · simp only [fieldOf, h, dite_false]
      exact analyticAt_const
  · refine analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_
    simp only [hOf]
    exact (analyticAt_proj _ c₀).div_const

end Shift

/-! ### The domain inclusion -/

section Dom

variable {j : ℕ}

/-- **The domain inclusion for a configuration of the polydisc**: a block-constant field within
`ρ_s ≥ r` of `e_{i₀}` and the field `h = b/ν` of a configuration of the anisotropic polydisc of
radius `r` lie in `Ξ^c_j(𝔹; 1, ε)` when `4 N ρ_s ≤ δ`. -/
theorem xiDom_hOf_poly {a : ℕ → ℝ} {μ ν : ℝ} (hBg : BgHyp d L k ϱ a μ)
    {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k)
    (hν : 0 < ν) (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (i₀ : Fin N) {δ r ρs ε : ℝ} (hδ0 : 0 < δ)
    (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N) (hr0 : 0 < r) (hr1 : r ≤ 1) (hrs : r ≤ ρs)
    (hρs : 4 * N * ρs ≤ δ) (hε : (2 * bgK1 d L N + 2) * δ ≤ ε)
    (Ψ : Fld d L N₁ m₁ k N) (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρs)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    {S : Finset (Site d)} {u : Cfg d N S} (hu : u ∈ polyAniso i₀ ν r S) :
    XiDom G a μ j ε Ψ (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S u) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hrδ : r < δ := by nlinarith
  have h1 : (N : ℝ) * r ≤ N * ρs := mul_le_mul_of_nonneg_left hrs (by positivity)
  have hNr : 0 ≤ (N : ℝ) * r := by positivity
  exact xiDom_of_fieldM (ρh := r) (ρl := r ^ 2) hBg hΩ hjk hν hμν i₀ hδ0 hδc0 hδc1
    (hr0.le.trans hrs) hr0.le hρs (by linarith) (by nlinarith) hε Ψ (fun i => u (Sum.inr i)) hΨ hΨb
    (fun i => (polyAniso_inr hu hr0 hr1 i).le) (polyAniso_inr_self hu).le

/-- **The pulled-back fields of a configuration of the polydisc lie in the domain.** -/
theorem xiDom_shift_poly {a : ℕ → ℝ} {μ ν : ℝ} (hBg : BgHyp d L k ϱ a μ)
    {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k)
    (hν : 0 < ν) (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (i₀ : Fin N) {y : CTorus d L N₁ m₁ k}
    (hy : Aligned (L ^ j) y) {δ r ε : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N)
    (hδc1 : δ ≤ bgC1 d L N) (hr0 : 0 < r) (hr1 : r ≤ 1) (hρs : 4 * N * r ≤ δ)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ ε) {S : Finset (Site d)} {u : Cfg d N S}
    (hu : u ∈ polyAniso i₀ ν r S) :
    XiDom G a μ j ε (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S u (z - y))
      (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S u) :=
  xiDom_hOf_poly hBg hΩ hjk hν hμν i₀ hδ0 hδc0 hδc1 hr0 hr1 le_rfl hρs hε _
    (fun z i => fieldOf_sub_le_poly hu hr0.le (z - y) i) (fun _ _ h => shiftField_block hjk hy u h)
    hu

end Dom

/-! ### The pulled-back term on the polydisc -/

section Term

variable {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

/-- **Analyticity of the pulled-back term on the polydisc.** -/
theorem analyticAt_shiftTerm (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν) (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X) (i₀ : Fin N)
    {r : ℝ} (hrad : AnisoRadiusOK d L N P j r) {u₀ : Cfg d N S}
    (hu : u₀ ∈ polyAniso i₀ ν r S) :
    AnalyticAt ℂ (fun c : Cfg d N S =>
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c)) u₀ := by
  obtain ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ := hrad
  have hNB : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
  have hXi := xiDom_shift_poly hBg (hcl.gs_spec j hj1 hjk X hX).2 hjk hν hμν i₀ hy hδ0 hδc0
    hδc1 hr0 hr1 (aniK_old i₀ hr0 hrδ).2 hε hu
  have hE := hcl.analyticE j hj1 hjk y X hX hyX
    ((fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S u₀ (z - y)),
      hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S u₀) hXi
  exact AnalyticAt.comp (g := fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Tm.E j y X p.1 p.2)
    (f := fun c : Cfg d N S =>
      ((fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y),
        hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c) :
          Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N)) (x := u₀)
    hE (analyticAt_shift_fp j i₀ ν y S u₀)

/-- **The bound (H.4) on the polydisc.** -/
theorem shiftTerm_norm_le (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν) (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X) (i₀ : Fin N)
    {r : ℝ} (hrad : AnisoRadiusOK d L N P j r) {u : Cfg d N S}
    (hu : u ∈ polyAniso i₀ ν r S) :
    ‖Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S u (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S u)‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) := by
  obtain ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ := hrad
  have hNB : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
  exact hcl.boundE j hj1 hjk y X hX hyX _ _ (xiDom_shift_poly hBg (hcl.gs_spec j hj1 hjk X hX).2
    hjk hν hμν i₀ hy hδ0 hδc0 hδc1 hr0 hr1 (aniK_old i₀ hr0 hrδ).2 hε hu)

/-- **Rotation invariance of the pulled-back term on the polydisc**: two configurations of the
polydisc related by an `IsCRot` matrix with entries bounded by `B` have the same term (from the real
clause `rotE` along the two-stage Cayley path, `rotE_aniso_of_xiFieldDom`). -/
theorem shiftTerm_rotA (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ P.νbar) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y)
    (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S) (i₀ : Fin N)
    {δ r B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hB : 0 ≤ B) (hrδ : r * aniK N B P.νbar ≤ δ)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsCRot M) (hMb : ∀ i k, ‖M i k‖ ≤ B)
    {u u' : Cfg d N S} (hu : u ∈ polyAniso i₀ ν r S) (hu' : u' ∈ polyAniso i₀ ν r S)
    (hrot : rotCfgL M S u = u') :
    Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S u' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S u') =
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S u (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S u) := by
  have hy0 : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (y - y) ∈ S := hS y hyX
  have hfr : ∀ z : CTorus d L N₁ m₁ k,
      fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S u' (z - y) =
        M.mulVec (fieldOf j i₀ S u (z - y)) ∨
      fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S u (z - y) =
        (Pi.single i₀ 1 : Fin N → ℂ) := fun z => by
    by_cases hz : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S
    · left
      rw [← hrot, fieldOf_rot M u hz]; rfl
    · right
      funext i; simp [fieldOf, hz]
  have hr := E_rotA_cfg hcl hBg hν hμν hνb hj1 hjk hX hyX i₀ hδ0 hδc0 hδc1 hr0 hr1 hB hrδ
    hε hM.1 hMb hu hu' hrot
    (fun c => fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y))
    (fun c z z' hzz => funext fun i => congrFun (shiftField_block hjk hy c hzz) i)
    (fun c hc z i => fieldOf_sub_le_poly hc hr0.le (z - y) i) hfr y (by
      rw [← hrot, fieldOf_rot M u hy0]; rfl)
  rw [← hr]
  refine hcl.localE j y X _ _ _ _ (fun z hz => ⟨?_, ?_⟩)
  · have e := fieldOf_rot (j := j) (i₀ := i₀) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) M u (hS z hz)
    rw [← hrot, e]; rfl
  · rw [← hrot, hOf_rot]

/-- **Rotation invariance for `O(N, ℂ)` on the polydisc**: as `shiftTerm_rotA` for any complex
orthogonal `M`, through one real reflection of a coordinate `p ≠ i₀`. -/
theorem shiftTerm_orthA (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ P.νbar) (hj1 : 1 ≤ j) (hjk : j ≤ k) (hy : Aligned (L ^ j) y)
    (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S) {i₀ p : Fin N}
    (hp : p ≠ i₀) {δ r B : ℝ} (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hB : 1 ≤ B) (hrδ : r * aniK N B P.νbar ≤ δ)
    (hε : (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsOrth M) (hMb : ∀ i k, ‖M i k‖ ≤ B)
    {u u' : Cfg d N S} (hu : u ∈ polyAniso i₀ ν r S) (hu' : u' ∈ polyAniso i₀ ν r S)
    (hrot : rotCfgL M S u = u') :
    Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S u' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S u') =
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S u (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S u) := by
  have hB0 : 0 ≤ B := by linarith
  rcases det_isOrth hM with hd | hd
  · exact shiftTerm_rotA hcl hBg hν hμν hνb hj1 hjk hy hX hyX hS i₀ hδ0 hδc0 hδc1 hr0 hr1 hB0
      hrδ hε ⟨hM, Or.inr hd⟩ hMb hu hu' hrot
  · set Pm := reflP N p with hPm
    have hPpoly : rotCfgL Pm S u ∈ polyAniso i₀ ν r S := rotCfgL_reflP_mem_polyAniso hp hu
    have h1 := shiftTerm_rotA hcl hBg hν hμν hνb hj1 hjk hy hX hyX hS i₀ hδ0 hδc0 hδc1 hr0 hr1 hB0
      hrδ hε (isRot_reflP p).isCRot (fun i k => (reflP_norm_le p i k).trans hB) hu hPpoly rfl
    have hMP : IsCRot (M * Pm) := by
      refine ⟨?_, Or.inr ?_⟩
      · rw [Matrix.transpose_mul, hPm, reflP_transpose, Matrix.mul_assoc,
          ← Matrix.mul_assoc M.transpose, hM, Matrix.one_mul, reflP_mul_self]
      · rw [Matrix.det_mul, hd, hPm, reflP_det]; norm_num
    have hMPb : ∀ i k, ‖(M * Pm) i k‖ ≤ B := by
      intro i k
      rw [hPm]
      unfold reflP
      rw [Matrix.mul_diagonal]
      by_cases h : k = p
      · simp [h]; exact hMb i p
      · simp [h]; exact hMb i k
    have h2 := shiftTerm_rotA hcl hBg hν hμν hνb hj1 hjk hy hX hyX hS i₀ hδ0 hδc0 hδc1 hr0 hr1 hB0
      hrδ hε hMP hMPb hPpoly hu' (by
        have hPP : Pm * Pm = 1 := by rw [hPm]; exact reflP_mul_self p
        rw [← rotCfgL_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]; exact hrot)
    rw [h2, h1]

/-- **The tube hypotheses of the pulled-back term**: analyticity on the anisotropic polydisc and
invariance under the complex orthogonal matrices of entries `≤ rotB N` relating its points. -/
theorem tubeHypA_shiftTerm (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ P.νbar) (hj1 : 1 ≤ j) (hjk : j ≤ k) (hy : Aligned (L ^ j) y)
    (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S) {i₀ i₁ : Fin N}
    (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r) :
    TubeHypA i₀ ν r (fun c : Cfg d N S =>
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c)) where
  analytic := fun _ hc => analyticAt_shiftTerm hcl hBg hν hμν hj1 hjk hy hX hyX i₀ hrad hc
  rot := fun M hM hMb u u' hu hu' hrot => by
    obtain ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ := hrad
    exact shiftTerm_orthA hcl hBg hν hμν hνb hj1 hjk hy hX hyX hS hne hδ0 hδc0 hδc1 hr0 hr1
      (one_le_rotB i₀) hrδ hε hM hMb hu hu' hrot

end Term

/-! ### The path bound for the blocks placed at the centre -/

section Geom

variable {j : ℕ}

theorem aligned_ibase (hjk : j ≤ k) (z : Site d) :
    Aligned (L ^ j) (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z) := by
  have hdvd : L ^ j ∣ N₁ * L ^ m₁ * L ^ k := by rw [side_eq hjk]; exact dvd_mul_right _ _
  have : NeZero (N₁ * L ^ m₁ * L ^ k) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  rw [aligned_iff hdvd]
  intro μ
  simp only [ibase, map_intCast]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact Dvd.intro _ rfl

/-- An aligned site is the base of the block at its centred position. -/
theorem ibase_unlift_of_aligned (hjk : j ≤ k) {w : CTorus d L N₁ m₁ k} (hw : Aligned (L ^ j) w) :
    ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
      (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j w) = w := by
  have hu : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
      (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
        (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j w)) =
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j w :=
    unlift_ibase hjk fun μ => by
      simp only [unlift, ZMod.coe_valMinAbs]
  have hb : jBlock d L (N₁ * L ^ m₁) k j (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
      (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j w)) = jBlock d L (N₁ * L ^ m₁) k j w := by
    funext μ
    have := congrFun hu μ
    simp only [unlift] at this
    exact ZMod.valMinAbs_inj.1 (by exact_mod_cast this)
  have hc := cbase_pow_eq_of_jBlock hjk hb
  rwa [cbase_eq_self_of_aligned (aligned_ibase hjk _), cbase_eq_self_of_aligned hw] at hc

/-- **The path bound (G5) at the centre**: for aligned sites `x, y` of a polymer `X ∈ 𝒟_j`,
`|unlift (x - y)|₁ ≤ A (1 + d_j(X))`, `A = diamA`. -/
theorem unlift_sub_diam {m₀ : ℕ} (hjk : j ≤ k) {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom m₀ j X) {x y : CTorus d L N₁ m₁ k} (hx : x ∈ X) (hy : y ∈ X)
    (hxa : Aligned (L ^ j) x) (hya : Aligned (L ^ j) y) :
    ((∑ μ, |unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) μ| : ℤ) : ℝ) ≤
      diamA d L m₀ m₁ * (1 + sizeJ m₀ j X) := by
  have hdvd : L ^ j ∣ N₁ * L ^ m₁ * L ^ k := by rw [side_eq hjk]; exact dvd_mul_right _ _
  have hw : Aligned (L ^ j) (x - y) := by
    rw [sub_eq_add_neg]; exact aligned_add hdvd hxa (aligned_neg hdvd hya)
  set s : Site d := unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) with hs
  have hsz : ∀ μ, ZMod.valMinAbs (((s μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (k - j)))) = s μ := by
    intro μ; simp only [hs, unlift, ZMod.coe_valMinAbs]
  have hib : ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s = x - y :=
    ibase_unlift_of_aligned hjk hw
  have hG := G5 (isDj_of_isPolyDom hX) hx hy
  set Q : ℝ := ∑ μ, (((s μ).natAbs : ℕ) : ℝ) ^ 2 with hQ
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have he : euclDist x y = (L : ℝ) ^ j * Real.sqrt Q := by
    unfold euclDist
    have h1 : ∀ μ, ((LargeField.cycNorm (N₁ * L ^ m₁ * L ^ k) (x μ - y μ) : ℕ) : ℝ) =
        (L : ℝ) ^ j * ((s μ).natAbs : ℝ) := by
      intro μ
      have := cycNorm_ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hjk hsz μ
      rw [hib] at this
      simp only [Pi.sub_apply, Pi.zero_apply, sub_zero] at this
      rw [this]; push_cast; ring
    have h2 : ∑ μ, ((LargeField.cycNorm (N₁ * L ^ m₁ * L ^ k) (x μ - y μ) : ℕ) : ℝ) ^ 2 =
        ((L : ℝ) ^ j) ^ 2 * Q := by
      rw [hQ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun μ _ => by rw [h1 μ]; ring
    rw [h2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hLj.le]
  have hT : ((∑ μ, |s μ| : ℤ) : ℝ) = ∑ μ, (((s μ).natAbs : ℕ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hT2 : (∑ μ, (((s μ).natAbs : ℕ) : ℝ)) ^ 2 ≤ d * Q := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun μ => (((s μ).natAbs : ℕ) : ℝ))
    simpa [hQ] using this
  have hT3 : (∑ μ, (((s μ).natAbs : ℕ) : ℝ)) ≤ Real.sqrt d * Real.sqrt Q := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg d)]
    exact Real.le_sqrt_of_sq_le hT2
  have hcell : (cellSide L m₀ m₁ j : ℝ) = (L : ℝ) ^ j * (L : ℝ) ^ (m₀ + m₁) := by
    unfold cellSide; push_cast; rw [← pow_add]; congr 1; ring
  rw [he, hcell] at hG
  have hsz0 : 0 ≤ sizeJ m₀ j X := treeLenCovOne_nonneg _ _ _
  have hS1 : Real.sqrt Q ≤ (L : ℝ) ^ (m₀ + m₁) * (sizeJ m₀ j X + 2 * Real.sqrt d * L) := by
    have : (L : ℝ) ^ j * Real.sqrt Q ≤
        (L : ℝ) ^ j * ((L : ℝ) ^ (m₀ + m₁) * (sizeJ m₀ j X + 2 * Real.sqrt d * L)) := by
      calc _ ≤ _ := hG
        _ = _ := by unfold sizeJ; ring
    exact le_of_mul_le_mul_left this hLj
  rw [hT]
  calc _ ≤ Real.sqrt d * Real.sqrt Q := hT3
    _ ≤ Real.sqrt d * ((L : ℝ) ^ (m₀ + m₁) * (sizeJ m₀ j X + 2 * Real.sqrt d * L)) :=
        mul_le_mul_of_nonneg_left hS1 (Real.sqrt_nonneg _)
    _ ≤ diamA d L m₀ m₁ * (1 + sizeJ m₀ j X) := by
        unfold diamA
        have h0 : 0 ≤ Real.sqrt d * (L : ℝ) ^ (m₀ + m₁) := by positivity
        have h2 : 0 ≤ 2 * Real.sqrt d * L := by positivity
        nlinarith [mul_nonneg h0 h2, mul_nonneg h0 hsz0]

end Geom

/-! ### The premises of the anisotropic termwise I-6 for the pulled-back label -/

section Premises

variable {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

/-- **`PremisesTermAniso` for a label pulled back at its centre**: the one-polymer family `{S}`
with size `d_j(X)` and the extension to the tube of the pulled-back term satisfies the premises of
the anisotropic termwise I-6, on the data domain of the configurations whose fields on `X` extend
into `Ξ^c_j(𝔹_j(X); 1, ε_j)`.  Here `S` places the blocks of `X` relative to `y` (`hS`, `hS'`). -/
theorem premisesTermAniso_centred (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ P.νbar) (hj1 : 1 ≤ j) (hjk : j ≤ k) (hy : Aligned (L ^ j) y)
    (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S)
    (hS' : ∀ s ∈ S, ∃ x ∈ X, Aligned (L ^ j) x ∧
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) = s)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r) :
    PremisesTermAniso
      ({ polys := {S}, dist := fun _ => sizeJ P.m₀ j X,
         term := fun S' c => trickFnA i₀ ν r (fun c' : Cfg d N S' =>
           Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - y))
             (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c } : TermFamily d N)
      i₀ i₁ ν r P.E₀ P.κ (diamA d L P.m₀ m₁) (wt P.κ S (sizeJ P.m₀ j X))
      {p | ∃ Ψ' h' : Fld d L N₁ m₁ k N,
        (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
            (pack S p.1 p.2) (z - y) ∧
          h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (pack S p.1 p.2) z) ∧
        XiDom (Tm.gs j X) a μ j (P.eps d L j) Ψ' h'} := by
  have hT := tubeHypA_shiftTerm hcl hBg hν hμν hνb hj1 hjk hy hX hyX hS hne hrad
  have hbd := fun (c : Cfg d N S) (hc : c ∈ polyAniso i₀ ν r S) =>
    shiftTerm_norm_le hcl hBg hν hμν hj1 hjk hy hX hyX i₀ hrad hc
  refine ⟨hne.symm, fun X' hX' => ?_, fun _ _ => treeLenCovOne_nonneg _ _ _,
    fun X' hX' s hs => ?_, Summable.of_finite, ?_, fun X' hX' => ?_, fun X' hX' c hc => ?_,
    fun X' hX' p hp => ?_, fun X' hX' c hc R hR hRb hRc => ?_⟩
  · rw [Set.mem_singleton_iff] at hX'; subst hX'
    have := hS y hyX
    rwa [sub_self, unlift_zero] at this
  · rw [Set.mem_singleton_iff] at hX'; subst hX'
    obtain ⟨x, hx, hxa, rfl⟩ := hS' s hs
    exact unlift_sub_diam hjk hX hx hyX hxa hy
  · exact (tsum_singleton S (fun X' : Finset (Site d) => wt P.κ X' (sizeJ P.m₀ j X))).le
  · rw [Set.mem_singleton_iff] at hX'; subst hX'
    exact hT.trickFnA_analytic
  · rw [Set.mem_singleton_iff] at hX'; subst hX'
    exact hT.trickFnA_bound hbd hc
  · rw [Set.mem_singleton_iff] at hX'; subst hX'
    by_cases hex : ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
        rotCfgL R X' (pack X' p.1 p.2) ∈ polyAniso i₀ ν r X'
    · exact hT.trickFnA_bound hbd hex
    · dsimp only
      unfold trickFnA
      simp only [hex, dite_false]
      obtain ⟨Ψ', h', hag, hXi⟩ := hp
      rw [hcl.localE j y X _ Ψ' _ h' (fun z hz => ⟨(hag z hz).1.symm, (hag z hz).2.symm⟩)]
      exact hcl.boundE j hj1 hjk y X hX hyX Ψ' h' hXi
  · rw [Set.mem_singleton_iff] at hX'; subst hX'
    exact hT.trickFnA_rot hc hR hRb hRc

end Premises

end Balaban.SmallField.Def6v2
