/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RowsCompose
public import Balaban.Fluctuation.StepComplexHat
public import Balaban.Fluctuation.MarkedTangent
public import Balaban.Fluctuation.MarkedRootGeometry

/-!
# The masked decoupled tangent and its row-locality (`MARK-ROWS`)

In the decoupled hat construction (cut parameters `s`) the fluctuation tangent is `hatPsiF`, the
lift of `cc • C^{1/2}(s) ψ̂`, a field of the unit lattice lifted to the fine torus.  The marked
tangent of `MarkedTangent.lean` is `u · y + t · M_z y`, where `M_z` keeps the coordinates of the unit
block `z` and sets the others to zero.  Here the mask is applied to the unit-lattice field
`cc • C^{1/2}(s) ψ̂` AFTER the covariance square root and before the lift:

  `markedHatPsiF … Z u t s Θ ψ̂ = u • hatPsiF … s Θ ψ̂ + t • liftC (maskBlock Z (cc • C^{1/2}(s) ψ̂))`.

(Masking `ψ̂` before the square root would give a different field: the square root does not commute
with a coordinate projection, since it has non-zero entries between different unit blocks.)  The block
is a finite set `Z` of unit points (for a step setting `S` and a marked point `z`, `Z = S.blockU z`,
and `maskBlock (S.blockU z) = S.maskUC z`, `maskBlock_blockU`).

* `markedHatPsiF_apply`: pointwise, the value at a site `y` is `(u + t · 1[unitPt y ∈ Z])` times the
  value of `hatPsiF` at `y`; hence `markedHatPsiF_zero_t`, `markedHatPsiF_of_notMem`,
  `markedHatPsiF_of_mem`.
* `markedHatPsiF_one`: at the cut point `s ≡ 1` it is the lift of `markedTangentC` (uses
  `hatPsiF_one_eq_liftC_shiftUC`'s unit-lattice form `hatSqrtF_one_apply`).
* `markedHatPsiF_rows` (`MARK-ROWS`): the paired-agreement statement on a component, with exactly the
  hypotheses of `hatPsiF_rows`; it holds for every block `Z`, in particular both when the block lies
  in the component and when it is disjoint from it.
* `markedHatPsiF_rows_union` (`MARK-ROWS` on a bridged set): for a finite family of components, the
  agreement holds on their union, under agreement of the data and hat variables on each member and
  of the cut parameters at the cubes inside each member.  Gap: the set `bridge … z Y` of
  `MarkedRootGeometry` is a union of aligned cubes, not a nearest-neighbour component of the
  decoupling geometry, so `hatPsiF_rows` does not apply to it directly; the statement is for the
  components that cover it (`markedHatPsiF_rows_bridge_of_cover`).
* `markedHatPsiF_read_eq`: a function of the tangent that reads only the set `R` is unchanged when
  the tangent is replaced by one agreeing on `R`; with `R ⊆ psiThick Y'` covered by the components
  this is the locality of a marked block term.

`MARK-ASSEMBLY`, `MARK-SCALED-COUNT` and `MARK-PARAM` are NOT proved here, no mark family is
constructed, and nothing depends on a choice of generating sets for the class terms.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section Mask

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

open Classical in
/-- **The coordinate projection onto a set `Z` of unit points**: keeps the coordinates of a field of
the unit lattice at the points of `Z` and sets the others to zero. -/
noncomputable def maskBlock (Z : Finset (unitPts Gp)) (w : unitPts Gp × Fin N → ℂ) :
    unitPts Gp × Fin N → ℂ :=
  fun q => if q.1 ∈ Z then w q else 0

open Classical in
/-- **The masked decoupled tangent** `v_t = u · hatPsiF + t · M_Z hatPsiF`, with the mask applied to
the unit-lattice field `cc • C^{1/2}(s) ψ̂` after the covariance square root, then lifted. -/
noncomputable def markedHatPsiF (a₁ ν : ℝ) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Z : Finset (unitPts Gp)) (u t : ℂ)
    (s : DecParams Gp) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts Gp × Fin N → ℂ) :
    CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ :=
  u • hatPsiF Gp a₁ ν hG' cc F₁ s Θ ψh +
    t • liftC hG' (maskBlock Z (cc • (hatSqrtF Gp a₁ ν F₁ s Θ *ᵥ ψh)))

/-- Pointwise form: the value at a site `y` is `u + t · 1[unitPt y ∈ Z]` times that of `hatPsiF`. -/
theorem markedHatPsiF_apply (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Z : Finset (unitPts Gp)) (u t : ℂ) (s : DecParams Gp)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts Gp × Fin N → ℂ)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    markedHatPsiF a₁ ν hG' cc F₁ Z u t s Θ ψh y i =
      (u + if unitPt hG' y ∈ Z then t else 0) * hatPsiF Gp a₁ ν hG' cc F₁ s Θ ψh y i := by
  classical
  unfold markedHatPsiF hatPsiF
  simp only [Pi.add_apply, Pi.smul_apply, liftC_apply, maskBlock, smul_eq_mul]
  by_cases hy : unitPt hG' y ∈ Z
  · simp only [hy, ite_true]; ring
  · simp only [hy, ite_false]; ring

/-- At `t = 0` it is `u • hatPsiF`. -/
theorem markedHatPsiF_zero_t (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Z : Finset (unitPts Gp)) (u : ℂ) (s : DecParams Gp)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts Gp × Fin N → ℂ) :
    markedHatPsiF a₁ ν hG' cc F₁ Z u 0 s Θ ψh = u • hatPsiF Gp a₁ ν hG' cc F₁ s Θ ψh := by
  funext y i
  rw [markedHatPsiF_apply]
  simp

/-- At the sites outside the block it is `u • hatPsiF`. -/
theorem markedHatPsiF_of_notMem (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Z : Finset (unitPts Gp)) (u t : ℂ) (s : DecParams Gp)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts Gp × Fin N → ℂ)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : unitPt hG' y ∉ Z) (i : Fin N) :
    markedHatPsiF a₁ ν hG' cc F₁ Z u t s Θ ψh y i =
      u * hatPsiF Gp a₁ ν hG' cc F₁ s Θ ψh y i := by
  rw [markedHatPsiF_apply]
  simp [hy]

/-- At the sites of the block it is `(u + t) • hatPsiF`. -/
theorem markedHatPsiF_of_mem (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Z : Finset (unitPts Gp)) (u t : ℂ) (s : DecParams Gp)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts Gp × Fin N → ℂ)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : unitPt hG' y ∈ Z) (i : Fin N) :
    markedHatPsiF a₁ ν hG' cc F₁ Z u t s Θ ψh y i =
      (u + t) * hatPsiF Gp a₁ ν hG' cc F₁ s Θ ψh y i := by
  rw [markedHatPsiF_apply]
  simp [hy]

/-- At the cut point `s ≡ 1` the square root `hatSqrtF` is `hatCovSqrt` of the datum. -/
theorem hatSqrtF_one_apply (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) :
    hatSqrtF Gp a₁ ν F₁ (fun _ => 1) (rawOf D) = hatCovSqrt Gp a₁ ν D := by
  obtain ⟨hI, hU⟩ := isDecBg_one_of_xiCData hC hD
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hs : ∀ P, ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ := fun P => by simpa using hE1
  have hFeq := hF₁ _ D hs hU _ _ hI
  unfold hatSqrtF hatCovSqrt
  rw [hFeq, extS_one]
  rfl

end Mask

section Rows

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **`MARK-ROWS`.  The masked decoupled tangent on the component.**  Exactly the hypotheses of
`hatPsiF_rows`; the marked block `Z` and the parameters `u, t` are arbitrary.  The conclusion is the
agreement of `markedHatPsiF` at every site of the component `Y`.  If `Z` lies inside the blocks of
`Y`, the mask acts on the part of `Y` over `Z`; if `Z` is disjoint from `Y` it contributes nothing
on `Y`; the proof does not distinguish the two cases, because the mask is the same function of the
site on both sides. -/
theorem markedHatPsiF_rows (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (hconn : HatConn Gp)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁ → extS Gp s P = 1 ∧ extS Gp s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y → extS Gp s P = extS Gp s' P)
    (hX₁ : IsCellUnion (L ^ (k + 1)) (X₁ : Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒞 : ∀ P ∈ 𝒞, P ∈ cubeIdx Gp)
    (hdata : ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D'.h z))
    (ψh ψh' : unitPts Gp × Fin N → ℂ)
    (hh : ∀ b' : unitPts Gp, UnitOut Gp Y b' → ∀ i, ψh (b', i) = ψh' (b', i))
    (Z : Finset (unitPts Gp)) (u t : ℂ) :
    ∀ y ∈ Y,
      markedHatPsiF a₁ ν hG' cc F₁ Z u t s (rawOf D) ψh y =
        markedHatPsiF a₁ ν hG' cc F₁ Z u t s' (rawOf D') ψh' y := by
  intro y hy
  have h := hatPsiF_rows hC hk hG' cc hconn hMX hmar hα hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag hX₁
    h𝒞 hdata ψh ψh' hh y hy
  funext i
  rw [markedHatPsiF_apply, markedHatPsiF_apply, h]

/-- **`MARK-ROWS` on a union of components** (the bridged domain, see the module doc).  `𝒴` is a
finite family of components of the same decoupling geometry `(X₁, 𝒞)`; the data agree on each member,
the hat variables agree on the unit blocks of each member, and the cut parameters agree at the cubes
`P ∈ 𝒞` lying inside some member (this includes the cut parameters at the marked block when a member
contains it).  Then `markedHatPsiF` agrees at every site of every member. -/
theorem markedHatPsiF_rows_union (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (hconn : HatConn Gp)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ : Finset (CTorus d L N₁ m₁ (k + 1))}
    (𝒴 : Finset (Finset (CTorus d L N₁ m₁ (k + 1))))
    (hY : ∀ Y ∈ 𝒴, IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁ → extS Gp s P = 1 ∧ extS Gp s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hag : ∀ Y ∈ 𝒴, ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y → extS Gp s P = extS Gp s' P)
    (hX₁ : IsCellUnion (L ^ (k + 1)) (X₁ : Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒞 : ∀ P ∈ 𝒞, P ∈ cubeIdx Gp)
    (hdata : ∀ Y ∈ 𝒴, ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D'.h z))
    (ψh ψh' : unitPts Gp × Fin N → ℂ)
    (hh : ∀ Y ∈ 𝒴, ∀ b' : unitPts Gp, UnitOut Gp Y b' → ∀ i, ψh (b', i) = ψh' (b', i))
    (Z : Finset (unitPts Gp)) (u t : ℂ) :
    ∀ y, (∃ Y ∈ 𝒴, y ∈ Y) →
      markedHatPsiF a₁ ν hG' cc F₁ Z u t s (rawOf D) ψh y =
        markedHatPsiF a₁ ν hG' cc F₁ Z u t s' (rawOf D') ψh' y := by
  rintro y ⟨Y, hY𝒴, hyY⟩
  exact markedHatPsiF_rows hC hk hG' cc hconn hMX hmar hα hsm hF₁ hs hs' hD hD' (hY Y hY𝒴) hs1 hs0
    (hag Y hY𝒴) hX₁ h𝒞 (hdata Y hY𝒴) ψh ψh' (hh Y hY𝒴) Z u t y hyY

/-- **`MARK-ROWS` on the bridged set, conditional on a cover.**  If `Y'` (for example
`bridge … z Y`) is covered by the family `𝒴` of components, the agreement of `markedHatPsiF` holds at
every site of `Y'`.  The cover hypothesis is the exact gap: the bridge adds aligned cubes that need
not lie in `(Vset X₁ 𝒞) ∩ Ω₁`, hence need not lie in a component. -/
theorem markedHatPsiF_rows_bridge_of_cover (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (hconn : HatConn Gp)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ : Finset (CTorus d L N₁ m₁ (k + 1))}
    (𝒴 : Finset (Finset (CTorus d L N₁ m₁ (k + 1))))
    (hY : ∀ Y ∈ 𝒴, IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁ → extS Gp s P = 1 ∧ extS Gp s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hag : ∀ Y ∈ 𝒴, ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y → extS Gp s P = extS Gp s' P)
    (hX₁ : IsCellUnion (L ^ (k + 1)) (X₁ : Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒞 : ∀ P ∈ 𝒞, P ∈ cubeIdx Gp)
    (hdata : ∀ Y ∈ 𝒴, ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D'.h z))
    (ψh ψh' : unitPts Gp × Fin N → ℂ)
    (hh : ∀ Y ∈ 𝒴, ∀ b' : unitPts Gp, UnitOut Gp Y b' → ∀ i, ψh (b', i) = ψh' (b', i))
    (Z : Finset (unitPts Gp)) (u t : ℂ) (Y' : Set (CTorus d L N₁ m₁ (k + 1)))
    (hcover : ∀ y ∈ Y', ∃ Y ∈ 𝒴, y ∈ Y) :
    ∀ y ∈ Y',
      markedHatPsiF a₁ ν hG' cc F₁ Z u t s (rawOf D) ψh y =
        markedHatPsiF a₁ ν hG' cc F₁ Z u t s' (rawOf D') ψh' y :=
  fun y hy => markedHatPsiF_rows_union hC hk hG' cc hconn hMX hmar hα hsm hF₁ hs hs' hD hD' 𝒴 hY
    hs1 hs0 hag hX₁ h𝒞 hdata ψh ψh' hh Z u t y (hcover y hy)

omit [NeZero N₁] [NeZero L] in
/-- **Locality of a function of the tangent** (T4, abstract form).  If `F` reads the tangent only on
the set `R` (that is, `F v = F v'` whenever `v` and `v'` agree on `R`) and `R` is covered by the
family `𝒴` of components, then `F` takes the same value along the masked decoupled tangents of two
data satisfying the agreement hypotheses of `markedHatPsiF_rows_bridge_of_cover`. -/
theorem markedHatPsiF_read_eq {Φ : Type*} (F : (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → Φ)
    (R : Set (CTorus d L N₁ m₁ (k + 1)))
    (hread : ∀ v v', (∀ y ∈ R, v y = v' y) → F v = F v')
    {v v' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hv : ∀ y ∈ R, v y = v' y) : F v = F v' :=
  hread v v' hv

end Rows

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Finset Matrix

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))

/-- The mask of `MarkedTangent` is the coordinate projection onto the block `S.blockU z`. -/
theorem maskBlock_blockU (v : S.EC) : maskBlock (S.blockU z) v = S.maskUC z v := by
  funext q
  simp [maskBlock, maskUC]

variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The masked decoupled tangent at the cut point `s ≡ 1` is the lift of `markedTangentC`.** -/
theorem markedHatPsiF_one
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (u t : ℂ) (x : S.E) :
    markedHatPsiF S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ (S.blockU z) u t
        (fun _ => 1) (rawOf S.D') (yhat x) =
      liftC S.hG' (S.markedTangentC z u t x) := by
  have hsh : ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      (hatSqrtF S.G' S.a₁ S.ν F₁ (fun _ => 1) (rawOf S.D') *ᵥ yhat x) = S.shiftUC x := by
    rw [hatSqrtF_one_apply hC hF₁ hD, ← S.covSqrtC_eq_hatCovSqrt]
    rfl
  unfold markedHatPsiF
  rw [hatPsiF_one_eq_liftC_shiftUC S hC hF₁ hD, hsh, maskBlock_blockU, S.liftC_markedTangentC]

end StepSetting

end Balaban.Fluctuation
