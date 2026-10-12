module

public import Balaban.LargeField.Operators.MainAction
public import Balaban.LargeField.Base.BaseRecord
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The main action of the base step (BASE-KERNEL §4, LF-RECONSTRUCTION Definition II.5.4 at `k = 0`)

At `k = 0` the level-zero layer `Λ_0 = Ω^c ∩ X` carries the *spin field* (P2's convention
`a_0 = +∞`), not the local background.  `mainActionLoc` evaluates the action at `locPhi`, which
extends the local background by the lifted data, and beyond the data collar need not equal the
retained fine spin.  `baseFieldHat` is the field `φ̂^X` of BASE-KERNEL (4.1): the retained spin on
`Ω^c ∩ X`, and the local background field `locPhi` elsewhere (on `Ω ∩ X` it is `e^loc`; the
boundary sites outside `X` carry the lifted data fixed for the component).  `baseMainAction` is the
main action `𝒜^base_1(X)` of (4.1): the same `actionG`-expression and `starBondE` expression as
`mainActionLoc`, evaluated at `φ̂^X`.

* `baseFieldHat_of_spin`: on `Ω^c ∩ X` the field is the spin field;
* `baseMainAction_nonneg`;
* `baseMainAction_bond_ge` (BASE-KERNEL (4.2)): for a bond with both end points in `Ω^c ∩ X`,
  `𝒜^base_1(X) ≥ (β^{(1)}_0 / 2) |∂φ(b)|²`, where `β^{(1)}_0 = betaCanon …` is the prefactor of the
  action (the `β/(1+ξ_3^{(0)})` of (4.1));
* `baseMainAction_site_ge`: the site analogue, `𝒜^base_1(X) ≥ β^{(1)}_0 μ |φ̂_x - h|² / 2` for
  `x ∈ X` (regime (B) witness).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory


theorem actionG_ge_bondE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d L N₀ q : ℕ}
    [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ q ϱ) {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) {μ : ℝ} (hμ : 0 ≤ μ) (h : E) (X : Finset (Site d L N₀ q))
    (ψ : (m : ℕ) → Blk d L N₀ q m → E) (φ : Site d L N₀ q → E) :
    (1 / 2) * bondE X φ ≤ actionG G a μ h X ψ φ := by
  unfold actionG
  have h1 : 0 ≤ ∑ n ∈ Finset.Icc 1 q, ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
      a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun y _ => by
      have := ha n
      positivity
  have h3 : 0 ≤ μ / 2 * ∑ x ∈ X, ‖φ x - h‖ ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  linarith

theorem actionG_ge_mass {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d L N₀ q : ℕ}
    [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ q ϱ) {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) {μ : ℝ} (_hμ : 0 ≤ μ) (h : E) (X : Finset (Site d L N₀ q))
    (ψ : (m : ℕ) → Blk d L N₀ q m → E) (φ : Site d L N₀ q → E) :
    μ / 2 * ∑ x ∈ X, ‖φ x - h‖ ^ 2 ≤ actionG G a μ h X ψ φ := by
  unfold actionG
  have h1 : 0 ≤ ∑ n ∈ Finset.Icc 1 q, ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
      a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun y _ => by
      have := ha n
      positivity
  have h2 := bondE_nonneg X φ
  linarith

/-- A bond with both end points in `X` contributes its term to `bondE X`. -/
theorem bondE_ge_term {E : Type*} [NormedAddCommGroup E] {d ℓ : ℕ} [NeZero ℓ]
    (X : Finset (Torus d ℓ)) (φ : Torus d ℓ → E) (μ : Fin d) (z : Torus d ℓ) (h1 : z ∈ X)
    (h2 : z + Pi.single μ 1 ∈ X) : bondTerm φ μ z ≤ bondE X φ := by
  classical
  unfold bondE
  refine le_trans ?_ (Finset.single_le_sum (f := fun μ => bondEdir μ X φ)
    (fun μ _ => bondEdir_nonneg μ X φ) (Finset.mem_univ μ))
  unfold bondEdir
  refine le_trans ?_ (Finset.single_le_sum (f := fun z => if z ∈ X ∧ z + Pi.single μ 1 ∈ X then
    bondTerm φ μ z else 0) (fun z _ => by split_ifs; exacts [bondTerm_nonneg φ μ z, le_rfl])
    (Finset.mem_univ z))
  simp [h1, h2]

section BaseAction

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K)
  (Zc : Finset (Torus S.d (n (0 + 1))))
  (hZc : Zc ∈ comps (S.omega (0 + 1)) (Hl.F.Zp (0 + 1))) (hk : 0 + 1 ≤ K) (cs : OpConsts)

open Classical in
/-- **The fine field `φ̂^X`** of BASE-KERNEL §4 on the sites of the level-`1` torus: the retained
spin `ψ_0` on `Ω^c ∩ X` (`X = Xfine`, `Ω = Ω_1` of the record), and the local background field
`locPhi` (`e^loc` on `Ω ∩ X`, the lifted data outside `X`) elsewhere. -/
noncomputable def baseFieldHat
    (o : OutT N R (locHist Hl M K (0 + 1) Zc) (0 + 1))
    (x : NewCfg N (locHist Hl M K (0 + 1) Zc) 0) (hv : EuclideanSpace ℝ (Fin N)) :
    Site S.d S.L (g.M1 * (g.c * n (0 + 1))) (0 + 1) → EuclideanSpace ℝ (Fin N) :=
  fun z =>
    if z ∈ Xfine g Hl 0 Zc ∧
        z ∉ fineK1 g.M1 g.c (n (0 + 1)) S.L 0 ((Hl.step 0).Omega : Set (Torus S.d (n (0 + 1)))) then
      subVarField N x 0 (torusCast (histScale_eq g.hM Hl.F.hnn (Nat.zero_le 1) hk) z)
    else locPhi g Hl 0 Zc hZc hk cs o x hv z

theorem baseFieldHat_of_spin
    (o : OutT N R (locHist Hl M K (0 + 1) Zc) (0 + 1))
    (x : NewCfg N (locHist Hl M K (0 + 1) Zc) 0) (hv : EuclideanSpace ℝ (Fin N))
    (z : Site S.d S.L (g.M1 * (g.c * n (0 + 1))) (0 + 1)) (hzX : z ∈ Xfine g Hl 0 Zc)
    (hzΩ : z ∉ fineK1 g.M1 g.c (n (0 + 1)) S.L 0
      ((Hl.step 0).Omega : Set (Torus S.d (n (0 + 1))))) :
    baseFieldHat g Hl Zc hZc hk cs o x hv z =
      subVarField N x 0 (torusCast (histScale_eq g.hM Hl.F.hnn (Nat.zero_le 1) hk) z) := by
  unfold baseFieldHat
  simp only [hzX, hzΩ, not_false_eq_true, and_self, ↓reduceIte]

variable (hrem : ∀ j, Hl.rem j = ∅)

/-- **The base main action `𝒜^base_1(X)`** (BASE-KERNEL (4.1)): the main action of
Definition II.5.4 at `k = 0`, evaluated at the field `φ̂^X` (`baseFieldHat`) instead of the extended
local background `locPhi`; the coefficients and the interior/star-bond partition are those of
`actionG` and `starBondE`. -/
noncomputable def baseMainAction (o : OutT N R (locHist Hl M K (0 + 1) Zc) (0 + 1))
    (x : NewCfg N (locHist Hl M K (0 + 1) Zc) 0) (hv : EuclideanSpace ℝ (Fin N)) : ℝ :=
  betaCanon S.d S.L (cs.beta (0 + 1)) (0 + 1) 0 *
    (actionG (histGenLevel g Hl 0 hk hrem) cs.aw (cs.muAct (0 + 1)) hv (Xfine g Hl 0 Zc)
        (psiLevel g Hl 0 hk
          (subMultiscaleField N (locHist Hl M K (0 + 1) Zc) (0 + 1)
            (Vblk R (locHist Hl M K (0 + 1) Zc) (0 + 1)) x o))
        (baseFieldHat g Hl Zc hZc hk cs o x hv) +
      1 / 4 * starBondE (Xfine g Hl 0 Zc) (baseFieldHat g Hl Zc hZc hk cs o x hv))

/-- The prefactor `β^{(1)}_0` of the base main action (the `β/(1+ξ_3^{(0)})` of (4.1)). -/
noncomputable def baseBeta (S : Setting) (cs : OpConsts) : ℝ :=
  betaCanon S.d S.L (cs.beta (0 + 1)) (0 + 1) 0

/-- The three non-negative parts of `𝒜^base_1(X) / β^{(1)}_0`. -/
theorem baseMainAction_eq (o : OutT N R (locHist Hl M K (0 + 1) Zc) (0 + 1))
    (x : NewCfg N (locHist Hl M K (0 + 1) Zc) 0) (hv : EuclideanSpace ℝ (Fin N)) :
    baseMainAction g Hl Zc hZc hk cs hrem o x hv = baseBeta S cs *
      (actionG (histGenLevel g Hl 0 hk hrem) cs.aw (cs.muAct (0 + 1)) hv (Xfine g Hl 0 Zc)
        (psiLevel g Hl 0 hk
          (subMultiscaleField N (locHist Hl M K (0 + 1) Zc) (0 + 1)
            (Vblk R (locHist Hl M K (0 + 1) Zc) (0 + 1)) x o))
        (baseFieldHat g Hl Zc hZc hk cs o x hv) +
      1 / 4 * starBondE (Xfine g Hl 0 Zc) (baseFieldHat g Hl Zc hZc hk cs o x hv)) := rfl

theorem baseMainAction_nonneg (hb : 0 ≤ cs.beta (0 + 1)) (ha : ∀ n, 0 ≤ cs.aw n)
    (hμ : 0 ≤ cs.muAct (0 + 1)) (o : OutT N R (locHist Hl M K (0 + 1) Zc) (0 + 1))
    (x : NewCfg N (locHist Hl M K (0 + 1) Zc) 0) (hv : EuclideanSpace ℝ (Fin N)) :
    0 ≤ baseMainAction g Hl Zc hZc hk cs hrem o x hv := by
  unfold baseMainAction betaCanon
  have h1 := actionG_nonneg (histGenLevel g Hl 0 hk hrem) ha hμ hv (Xfine g Hl 0 Zc)
    (psiLevel g Hl 0 hk
      (subMultiscaleField N (locHist Hl M K (0 + 1) Zc) (0 + 1)
        (Vblk R (locHist Hl M K (0 + 1) Zc) (0 + 1)) x o))
    (baseFieldHat g Hl Zc hZc hk cs o x hv)
  have h2 := starBondE_nonneg (Xfine g Hl 0 Zc) (baseFieldHat g Hl Zc hZc hk cs o x hv)
  have h3 : 0 ≤ cs.beta (0 + 1) / (S.L : ℝ) ^ ((0 + 1 - 0) * (S.d - 2)) := by positivity
  positivity

/-- The action is at least `β^{(1)}_0` times the interior-bond term. -/
theorem baseMainAction_ge_bondE (hb : 0 ≤ cs.beta (0 + 1)) (ha : ∀ n, 0 ≤ cs.aw n)
    (hμ : 0 ≤ cs.muAct (0 + 1)) (o : OutT N R (locHist Hl M K (0 + 1) Zc) (0 + 1))
    (x : NewCfg N (locHist Hl M K (0 + 1) Zc) 0) (hv : EuclideanSpace ℝ (Fin N)) :
    baseBeta S cs * ((1 / 2) * bondE (Xfine g Hl 0 Zc) (baseFieldHat g Hl Zc hZc hk cs o x hv)) ≤
      baseMainAction g Hl Zc hZc hk cs hrem o x hv := by
  have hβ : 0 ≤ baseBeta S cs := by
    unfold baseBeta betaCanon; positivity
  rw [baseMainAction_eq]
  have h1 := actionG_ge_bondE (histGenLevel g Hl 0 hk hrem) ha hμ hv (Xfine g Hl 0 Zc)
    (psiLevel g Hl 0 hk
      (subMultiscaleField N (locHist Hl M K (0 + 1) Zc) (0 + 1)
        (Vblk R (locHist Hl M K (0 + 1) Zc) (0 + 1)) x o))
    (baseFieldHat g Hl Zc hZc hk cs o x hv)
  have h2 := starBondE_nonneg (Xfine g Hl 0 Zc) (baseFieldHat g Hl Zc hZc hk cs o x hv)
  exact mul_le_mul_of_nonneg_left (by linarith) hβ

/-- The action is at least `β^{(1)}_0` times the mass term. -/
theorem baseMainAction_ge_mass (hb : 0 ≤ cs.beta (0 + 1)) (ha : ∀ n, 0 ≤ cs.aw n)
    (hμ : 0 ≤ cs.muAct (0 + 1)) (o : OutT N R (locHist Hl M K (0 + 1) Zc) (0 + 1))
    (x : NewCfg N (locHist Hl M K (0 + 1) Zc) 0) (hv : EuclideanSpace ℝ (Fin N)) :
    baseBeta S cs * (cs.muAct (0 + 1) / 2 * ∑ z ∈ Xfine g Hl 0 Zc,
        ‖baseFieldHat g Hl Zc hZc hk cs o x hv z - hv‖ ^ 2) ≤
      baseMainAction g Hl Zc hZc hk cs hrem o x hv := by
  have hβ : 0 ≤ baseBeta S cs := by
    unfold baseBeta betaCanon; positivity
  rw [baseMainAction_eq]
  have h1 := actionG_ge_mass (histGenLevel g Hl 0 hk hrem) ha hμ hv (Xfine g Hl 0 Zc)
    (psiLevel g Hl 0 hk
      (subMultiscaleField N (locHist Hl M K (0 + 1) Zc) (0 + 1)
        (Vblk R (locHist Hl M K (0 + 1) Zc) (0 + 1)) x o))
    (baseFieldHat g Hl Zc hZc hk cs o x hv)
  have h2 := starBondE_nonneg (Xfine g Hl 0 Zc) (baseFieldHat g Hl Zc hZc hk cs o x hv)
  exact mul_le_mul_of_nonneg_left (by linarith) hβ

/-- **The bond-witness inequality (BASE-KERNEL (4.2))**: for a bond `b = (z, z + e_μ)` with both
end points in `Ω^c ∩ X`, `𝒜^base_1(X) ≥ (β^{(1)}_0 / 2) |∂φ(b)|²`, `φ` the retained spin field. -/
theorem baseMainAction_bond_ge (hb : 0 ≤ cs.beta (0 + 1)) (ha : ∀ n, 0 ≤ cs.aw n)
    (hμ : 0 ≤ cs.muAct (0 + 1)) (o : OutT N R (locHist Hl M K (0 + 1) Zc) (0 + 1))
    (x : NewCfg N (locHist Hl M K (0 + 1) Zc) 0) (hv : EuclideanSpace ℝ (Fin N))
    (μ : Fin S.d) (z : Site S.d S.L (g.M1 * (g.c * n (0 + 1))) (0 + 1))
    (hz : z ∈ Xfine g Hl 0 Zc ∧ z ∉ fineK1 g.M1 g.c (n (0 + 1)) S.L 0
      ((Hl.step 0).Omega : Set (Torus S.d (n (0 + 1)))))
    (hz' : z + Pi.single μ 1 ∈ Xfine g Hl 0 Zc ∧ z + Pi.single μ 1 ∉ fineK1 g.M1 g.c (n (0 + 1)) S.L 0
      ((Hl.step 0).Omega : Set (Torus S.d (n (0 + 1))))) :
    baseBeta S cs / 2 *
        ‖subVarField N x 0 (torusCast (histScale_eq g.hM Hl.F.hnn (Nat.zero_le 1) hk)
            (z + Pi.single μ 1)) -
          subVarField N x 0 (torusCast (histScale_eq g.hM Hl.F.hnn (Nat.zero_le 1) hk) z)‖ ^ 2 ≤
      baseMainAction g Hl Zc hZc hk cs hrem o x hv := by
  refine le_trans ?_ (baseMainAction_ge_bondE g Hl Zc hZc hk cs hrem hb ha hμ o x hv)
  have hβ : 0 ≤ baseBeta S cs := by
    unfold baseBeta betaCanon; positivity
  have hbd := bondE_ge_term (Xfine g Hl 0 Zc) (baseFieldHat g Hl Zc hZc hk cs o x hv) μ z hz.1 hz'.1
  unfold bondTerm at hbd
  rw [baseFieldHat_of_spin g Hl Zc hZc hk cs o x hv _ hz'.1 hz'.2,
    baseFieldHat_of_spin g Hl Zc hZc hk cs o x hv _ hz.1 hz.2] at hbd
  nlinarith [hbd, hβ]

/-- **The site-witness inequality** (regime (B)): for `z ∈ X`,
`𝒜^base_1(X) ≥ β^{(1)}_0 μ |φ̂_z - h|² / 2`, `μ = muAct`. -/
theorem baseMainAction_site_ge (hb : 0 ≤ cs.beta (0 + 1)) (ha : ∀ n, 0 ≤ cs.aw n)
    (hμ : 0 ≤ cs.muAct (0 + 1)) (o : OutT N R (locHist Hl M K (0 + 1) Zc) (0 + 1))
    (x : NewCfg N (locHist Hl M K (0 + 1) Zc) 0) (hv : EuclideanSpace ℝ (Fin N))
    (z : Site S.d S.L (g.M1 * (g.c * n (0 + 1))) (0 + 1)) (hz : z ∈ Xfine g Hl 0 Zc) :
    baseBeta S cs * cs.muAct (0 + 1) / 2 * ‖baseFieldHat g Hl Zc hZc hk cs o x hv z - hv‖ ^ 2 ≤
      baseMainAction g Hl Zc hZc hk cs hrem o x hv := by
  refine le_trans ?_ (baseMainAction_ge_mass g Hl Zc hZc hk cs hrem hb ha hμ o x hv)
  have hβ : 0 ≤ baseBeta S cs := by
    unfold baseBeta betaCanon; positivity
  have h1 : ‖baseFieldHat g Hl Zc hZc hk cs o x hv z - hv‖ ^ 2 ≤ ∑ z ∈ Xfine g Hl 0 Zc,
      ‖baseFieldHat g Hl Zc hZc hk cs o x hv z - hv‖ ^ 2 :=
    Finset.single_le_sum (f := fun z => ‖baseFieldHat g Hl Zc hZc hk cs o x hv z - hv‖ ^ 2)
      (fun _ _ => by positivity) hz
  have : baseBeta S cs * cs.muAct (0 + 1) / 2 *
      ‖baseFieldHat g Hl Zc hZc hk cs o x hv z - hv‖ ^ 2 =
      baseBeta S cs * (cs.muAct (0 + 1) / 2 *
      ‖baseFieldHat g Hl Zc hZc hk cs o x hv z - hv‖ ^ 2) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) hβ

end BaseAction

end Balaban.LargeField
