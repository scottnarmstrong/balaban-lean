/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormAnisoDefs
public import Balaban.SmallField.RenormTermwiseDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The reference-jet certificate of the pinned class (PIN-I6) -- DRAFT

**Draft, pending Roland's answer to Q13.**  `notes/phase1/PIN-I6.md` ("the pinned class does not
inherit the anisotropic I-6 estimate"), in the objects of `RenormAnisoDefs` / `RenormTermwiseDefs`
(`Cfg`, `refPt`, `anisoWt`, `tensA`, `tensB`, `tensAA`, `tensM`, `Itw`, `SumConds`).

* `RefJet i₀ ν r M X f`: **the reference-jet certificate** (PIN-I6 §3, `PinJet.germ`) of a term
  `f` in centred packed form on a polymer `X`: `f` is analytic at the reference point
  `(e_{i₀}, ν e_{i₀})` and its value and its first and second jets there have the sizes that the
  anisotropic polydisc of radius `r` would give by Cauchy (`aniso_norm_fderiv_basis_le`,
  `aniso_norm_D2_le`): `|f| ≤ M`, `|∂_p f| ≤ M / r_p`, `|∂_p ∂_q f| ≤ 4 M / (r_p r_q)`, with `r_p = r`
  on the spin and transverse source coordinates and `r²` on the longitudinal source coordinate.
  In particular (`RefJet.d2_bperp`) the **second transverse-`b` derivative** is `≤ 4 M / r²`, and
  the tensors `a_X`, `B_X`, `A_X`, `m_X` have the bounds of PIN-I6 §3 item 1 (`RefJet.tensA_le`,
  `tensB_le`, `tensAA_le`, `tensM_le`).
* `RefJet.of_polyAniso`: analyticity and the bound `M` on the wide anisotropic polydisc give the
  certificate (so the landed class has it as a theorem; on the pinned chart, whose transverse
  source radius is `≲ ν r_h`, it is an additional hypothesis).
* **The counterexample of PIN-I6 §2** (`pinCexF`, `pinCexFamily`): the one-site term
  `f_m(p, b) = (c/m)[(p·p)(b·b) - (p·b)²]`.  It satisfies the four renormalization conditions
  (`pinCex_sumConds`), all its first reference jets vanish, it is bounded by `2 c m (N B²)²` on the
  pinned physical chart `b = m h` (`pinCex_pinned_bound`), and its I-6 remainder at a constant
  rotated spin is `c m sin² θ` (`pinCex_itw`).  Hence **no constant `C` gives the termwise I-6 bound
  `C E₀ σ^{3-α₁} (ε/r)²` on the pinned class without the certificate**
  (`pinI6_no_uniform_bound`); the certificate fails because `D²_{b⊥} f_m = 2c/m`
  (`pinCex_D2_bperp`, `pinCex_not_refJet`).

The other facts of `PinJet` (items 2-4 of PIN-I6 §3: the Taylor difference along the actual
interpolation, the constant-potential bound (3.1) on connecting segments, the tail case) concern
the output configurations and are not reference-point facts; they are not part of `RefJet`.

**Relation to `RenormPinJet` / `RenormPinCounter` (W149, landed in parallel).**  The landed
`PinJetTerm` / `PinJet` is the full, data-dependent certificate consumed by
`termwise_irrelevant_pin` (`germ` with rotation invariance, the four tensor bounds, the
small-polymer Taylor clause, the constant-potential clause (3.1)).  `RefJet` is its
data-independent reference-point part, extended to all first and second coordinate jets (in
particular `D²_{b⊥}`), and is the form used as a class clause in `Def6v2.SourceForm`;
`RefJet.pinJet_tensors` gives the fields `tensA_le`, `tensB_le`, `tensAA_le`, `tensM_le` of
`PinJetTerm`.  The counterexample here (`pinCexFamily`) and the landed `oneSite` family are the
same term of PIN-I6 (2.1); the landed `pin_no_uniform_constant`, `pin_jet_fails` verify the data
hypotheses `DataHypAniso` and the failure of the `potential` clause, the theorems here the
failure of the reference-jet clause `RefJet` and the closed form of the remainder.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

/-! ### The certificate -/

/-- **The reference-jet certificate** (PIN-I6 §3 item 1, `PinJet.germ`; the clause `refJet` of
`Def6v2.SourceForm`).  For a term `f` in centred packed form on the polymer `X`, the reference
point `refPt i₀ ν X = (e_{i₀}, ν e_{i₀})`, the radius `r` (`= r_j = anisoRadius ≍ ε_j`) and the
bound `M` (`= M_X = E₀ e^{-κ d_j(X)}`): analyticity at the reference point, and the bounds on the
value and on the first and second jets in the coordinate directions that the anisotropic polydisc
`polyAniso i₀ ν r X` would give by the Cauchy estimates.  Draft pending Roland's answer to Q13. -/
structure RefJet (i₀ : Fin N) (ν r M : ℝ) (X : Finset (Site d)) (f : Cfg d N X → ℂ) : Prop where
  /-- `f` is analytic near the reference point -/
  analytic : AnalyticAt ℂ f (refPt i₀ ν X)
  /-- the value -/
  val : ‖f (refPt i₀ ν X)‖ ≤ M
  /-- the first jet: `M / r` in the spin and transverse source directions, `M / r²` in the
  longitudinal source direction -/
  d1 : ∀ p : Idx d N X, ‖fderiv ℂ f (refPt i₀ ν X) (Pi.single p 1)‖ ≤ M / anisoWt i₀ r X p
  /-- the second jet, including the second transverse source derivative -/
  d2 : ∀ p q : Idx d N X, ‖D2 f (refPt i₀ ν X) (Pi.single p 1) (Pi.single q 1)‖ ≤
    4 * M / (anisoWt i₀ r X p * anisoWt i₀ r X q)

section Cert

variable {i₀ : Fin N} {ν r M : ℝ} {X : Finset (Site d)} {f : Cfg d N X → ℂ}

/-- **The wide anisotropic polydisc gives the certificate** (the Cauchy estimates of
`RenormAnisoDefs`). -/
theorem RefJet.of_polyAniso (hr : 0 < r) (han : AnalyticOnNhd ℂ f (polyAniso i₀ ν r X))
    (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖f c‖ ≤ M) : RefJet i₀ ν r M X f where
  analytic := aniso_analyticAt_refPt hr han
  val := hM _ (refPt_mem_polyAniso hr)
  d1 := aniso_norm_fderiv_basis_le hr han hM
  d2 := fun p q => by
    have h := aniso_norm_D2_le hr han hM (Pi.single p 1) (Pi.single q 1)
    rw [anisoGauge_single hr, anisoGauge_single hr] at h
    refine h.trans (le_of_eq ?_)
    have hp := anisoWt_pos (i₀ := i₀) (X := X) hr p
    have hq := anisoWt_pos (i₀ := i₀) (X := X) hr q
    field_simp

/-- A constant term has the certificate with `M = |c|`. -/
theorem refJet_const (i₀ : Fin N) (ν : ℝ) (hr : 0 < r) (X : Finset (Site d)) (c : ℂ) :
    RefJet i₀ ν r ‖c‖ X (fun _ : Cfg d N X => c) :=
  RefJet.of_polyAniso hr analyticOnNhd_const fun _ _ => le_rfl

theorem RefJet.mono {M' : ℝ} (hr : 0 < r) (hM : M ≤ M') (h : RefJet i₀ ν r M X f) :
    RefJet i₀ ν r M' X f where
  analytic := h.analytic
  val := h.val.trans hM
  d1 := fun p => (h.d1 p).trans (div_le_div_of_nonneg_right hM (anisoWt_pos hr p).le)
  d2 := fun p q => (h.d2 p q).trans (div_le_div_of_nonneg_right (by linarith)
    (mul_pos (anisoWt_pos hr p) (anisoWt_pos hr q)).le)

/-- PIN-I6 §3 item 1: `|a_X(x)| ≤ M_X / r`. -/
theorem RefJet.tensA_le (h : RefJet i₀ ν r M X f) (x : ↥X) : ‖tensA i₀ ν X f x‖ ≤ M / r :=
  h.d1 (Sum.inl (x, i₀))

/-- PIN-I6 §3 item 1: `|B_X(x, x')| ≤ 4 M_X / r²`. -/
theorem RefJet.tensB_le (h : RefJet i₀ ν r M X f) (i₁ : Fin N) (x x' : ↥X) :
    ‖tensB i₀ i₁ ν X f x x'‖ ≤ 4 * M / r ^ 2 := by
  have := h.d2 (Sum.inl (x, i₁)) (Sum.inl (x', i₁))
  rwa [anisoWt_inl, anisoWt_inl, ← sq] at this

/-- PIN-I6 §3 item 1: `|A_X(x, x')| ≤ 4 M_X / r²`. -/
theorem RefJet.tensAA_le (h : RefJet i₀ ν r M X f) (x x' : ↥X) :
    ‖tensAA i₀ ν X f x x'‖ ≤ 4 * M / r ^ 2 := by
  have := h.d2 (Sum.inl (x, i₀)) (Sum.inl (x', i₀))
  rwa [anisoWt_inl, anisoWt_inl, ← sq] at this

/-- PIN-I6 §3 item 1: `|m_X(x')| ≤ 4 M_X / r²` (mixed transverse source/spin derivative). -/
theorem RefJet.tensM_le (h : RefJet i₀ ν r M X f) {i₁ : Fin N} (hne : i₁ ≠ i₀) (x' : ↥X) :
    ‖tensM i₀ i₁ ν X f x'‖ ≤ 4 * M / r ^ 2 := by
  have := h.d2 (Sum.inr i₁) (Sum.inl (x', i₁))
  rwa [anisoWt_inr_ne hne, anisoWt_inl, ← sq] at this

/-- **The second transverse-`b` derivative** at the reference point is `≤ 4 M / r²` (PIN-I6 (2.4):
the control missing from the pinned class without the certificate). -/
theorem RefJet.d2_bperp (h : RefJet i₀ ν r M X f) {i₁ : Fin N} (hne : i₁ ≠ i₀) :
    ‖D2 f (refPt i₀ ν X) (Pi.single (Sum.inr i₁) 1) (Pi.single (Sum.inr i₁) 1)‖ ≤
      4 * M / r ^ 2 := by
  have := h.d2 (Sum.inr i₁) (Sum.inr i₁)
  rwa [anisoWt_inr_ne hne, ← sq] at this

/-- **The certificate gives the reference-tensor bounds of the landed `PinJetTerm`** (PIN-I6 §3
item 1; `RenormPinJet`): for a term family `T` and `M_X = E₀ e^{-κ d_j(X)}`, the fields `tensA_le`,
`tensB_le`, `tensAA_le`, `tensM_le` of `PinJetTerm T i₀ i₁ ν r E₀ κ A Λ ψ b σ ε R X`. -/
theorem RefJet.pinJet_tensors {T : TermFamily d N} {i₁ : Fin N} {E₀ κ : ℝ} (hne : i₁ ≠ i₀)
    (h : RefJet i₀ ν r (E₀ * Real.exp (-κ * T.dist X)) X (T.term X)) :
    (∀ x : ↥X, ‖tensA i₀ ν X (T.term X) x‖ ≤ E₀ * Real.exp (-κ * T.dist X) / r) ∧
      (∀ x x' : ↥X,
        ‖tensB i₀ i₁ ν X (T.term X) x x'‖ ≤ 4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2) ∧
      (∀ x x' : ↥X,
        ‖tensAA i₀ ν X (T.term X) x x'‖ ≤ 4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2) ∧
      ∀ x : ↥X, ‖tensM i₀ i₁ ν X (T.term X) x‖ ≤ 4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2 :=
  ⟨h.tensA_le, h.tensB_le i₁, h.tensAA_le, h.tensM_le hne⟩

end Cert

/-! ### The one-site counterexample of PIN-I6 §2 -/

section Cex

/-- The one-site polymer `{0}`. -/
abbrev site0 (d : ℕ) : Finset (Site d) := {0}

/-- The centre of the one-site polymer. -/
def ctr0 (d : ℕ) : ↥(site0 d) := ⟨0, Finset.mem_singleton_self 0⟩

/-- The spin at the centre of a configuration of `{0}`. -/
def spin0 (c : Cfg d N (site0 d)) : Spin N := fun i => c (Sum.inl (ctr0 d, i))

/-- The source `b` of a configuration. -/
def srcOf {X : Finset (Site d)} (c : Cfg d N X) : Spin N := fun i => c (Sum.inr i)

/-- **The one-site term of PIN-I6 (2.1)**: `f(p, b) = a [(p·p)(b·b) - (p·b)²]`, `a = c/m`. -/
def pinCexF (a : ℂ) (c : Cfg d N (site0 d)) : ℂ :=
  a * (dot (spin0 c) (spin0 c) * dot (srcOf c) (srcOf c) - dot (spin0 c) (srcOf c) ^ 2)

open Classical in
/-- **The centred one-site family** of PIN-I6 §2: the only polymer is `{0}`, with the term
`pinCexF a`. -/
noncomputable def pinCexFamily (d N : ℕ) (a : ℂ) : TermFamily d N where
  polys := {site0 d}
  dist := fun _ => 0
  term := fun X c => if h : X = site0 d then pinCexF a (h ▸ c) else 0

theorem pinCexFamily_term (a : ℂ) : (pinCexFamily d N a).term (site0 d) = pinCexF a := by
  funext c
  simp [pinCexFamily]

theorem ctr0_eq (x : ↥(site0 d)) : x = ctr0 d := Subtype.ext (Finset.mem_singleton.1 x.2)

theorem spin0_pack (ψ : Site d → Spin N) (b : Spin N) : spin0 (pack (site0 d) ψ b) = ψ 0 := rfl

theorem srcOf_pack (X : Finset (Site d)) (ψ : Site d → Spin N) (b : Spin N) :
    srcOf (pack X ψ b) = b := rfl

theorem pinCexF_pack (a : ℂ) (ψ : Site d → Spin N) (b : Spin N) :
    pinCexF a (pack (site0 d) ψ b) = a * (dot (ψ 0) (ψ 0) * dot b b - dot (ψ 0) b ^ 2) := rfl

theorem spin0_add_smul (c z : Cfg d N (site0 d)) (t : ℂ) :
    spin0 (c + t • z) = spin0 c + t • spin0 z := rfl

theorem srcOf_add_smul {X : Finset (Site d)} (c z : Cfg d N X) (t : ℂ) :
    srcOf (c + t • z) = srcOf c + t • srcOf z := rfl

theorem spin0_refPt (i₀ : Fin N) (ν : ℝ) : spin0 (refPt i₀ ν (site0 d)) = Pi.single i₀ 1 := rfl

theorem srcOf_refPt (i₀ : Fin N) (ν : ℝ) (X : Finset (Site d)) :
    srcOf (refPt (d := d) i₀ ν X) = (ν : ℂ) • Pi.single i₀ 1 := rfl

theorem spin0_single_inl (i : Fin N) :
    spin0 (Pi.single (Sum.inl (ctr0 d, i)) 1 : Cfg d N (site0 d)) = Pi.single i 1 := by
  funext l
  by_cases h : l = i
  · subst h; simp [spin0]
  · have h' : (Sum.inl (ctr0 d, l) : Idx d N (site0 d)) ≠ Sum.inl (ctr0 d, i) := by
      intro e; exact h (Prod.mk.inj (Sum.inl.inj e)).2
    simp [spin0, Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]

theorem spin0_single_inr (i : Fin N) :
    spin0 (Pi.single (Sum.inr i) 1 : Cfg d N (site0 d)) = 0 := by
  funext l; simp [spin0]

theorem srcOf_single_inl {X : Finset (Site d)} (p : ↥X × Fin N) :
    srcOf (Pi.single (Sum.inl p) 1 : Cfg d N X) = 0 := by
  funext l; simp [srcOf]

theorem srcOf_single_inr {X : Finset (Site d)} (i : Fin N) :
    srcOf (Pi.single (Sum.inr i) 1 : Cfg d N X) = Pi.single i 1 := by
  funext l
  by_cases h : l = i
  · subst h; simp [srcOf]
  · have h' : (Sum.inr l : Idx d N X) ≠ Sum.inr i := fun e => h (Sum.inr.inj e)
    simp [srcOf, Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]

theorem analyticAt_coord {X : Finset (Site d)} (p : Idx d N X) (c : Cfg d N X) :
    AnalyticAt ℂ (fun c : Cfg d N X => c p) c :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Idx d N X => ℂ) p).analyticAt c

theorem analyticAt_dotCoord {X : Finset (Site d)} (u v : Fin N → Idx d N X) (c : Cfg d N X) :
    AnalyticAt ℂ (fun c : Cfg d N X => ∑ i, c (u i) * c (v i)) c := by
  have h := Finset.analyticAt_sum (𝕜 := ℂ)
    (f := fun (i : Fin N) (c : Cfg d N X) => c (u i) * c (v i)) (c := c) Finset.univ
    (fun i _ => (analyticAt_coord (u i) c).mul (analyticAt_coord (v i) c))
  have e : (∑ i : Fin N, fun c : Cfg d N X => c (u i) * c (v i)) =
      fun c => ∑ i, c (u i) * c (v i) := by
    funext c; simp [Finset.sum_apply]
  rwa [e] at h

/-- The one-site term is entire. -/
theorem pinCexF_analyticAt (a : ℂ) (c : Cfg d N (site0 d)) : AnalyticAt ℂ (pinCexF (N := N) a) c :=
  analyticAt_const.mul
    (((analyticAt_dotCoord (fun i => Sum.inl (ctr0 d, i)) (fun i => Sum.inl (ctr0 d, i)) c).mul
      (analyticAt_dotCoord (fun i => Sum.inr i) (fun i => Sum.inr i) c)).sub
      ((analyticAt_dotCoord (fun i => Sum.inl (ctr0 d, i)) (fun i => Sum.inr i) c).pow 2))

variable {i₀ i₁ : Fin N}

/-- Along the radial spin direction through the reference point the term vanishes. -/
theorem pinCexF_line_spin (a : ℂ) (i₀ : Fin N) (ν : ℝ) (t : ℂ) :
    pinCexF a (refPt i₀ ν (site0 d) + t • Pi.single (Sum.inl (ctr0 d, i₀)) 1) = 0 := by
  unfold pinCexF
  rw [spin0_add_smul, srcOf_add_smul, spin0_refPt, srcOf_refPt, spin0_single_inl, srcOf_single_inl]
  simp only [dot_add_left, dot_add_right, dot_smul_left, dot_smul_right, dot_single_left,
    Pi.single_eq_same, smul_zero, add_zero]
  ring

/-- Along the longitudinal source direction through the reference point the term vanishes. -/
theorem pinCexF_line_blong (a : ℂ) (i₀ : Fin N) (ν : ℝ) (t : ℂ) :
    pinCexF a (refPt i₀ ν (site0 d) + t • Pi.single (Sum.inr i₀) 1) = 0 := by
  unfold pinCexF
  rw [spin0_add_smul, srcOf_add_smul, spin0_refPt, srcOf_refPt, spin0_single_inr, srcOf_single_inr]
  simp only [dot_add_left, dot_add_right, dot_smul_left, dot_smul_right, dot_single_left,
    Pi.single_eq_same, smul_zero, add_zero]
  ring

/-- Along a transverse source direction through the reference point the term is `a t²`. -/
theorem pinCexF_line_bperp (a : ℂ) (hne : i₁ ≠ i₀) (ν : ℝ) (t : ℂ) :
    pinCexF a (refPt i₀ ν (site0 d) + t • Pi.single (Sum.inr i₁) 1) = a * t ^ 2 := by
  unfold pinCexF
  rw [spin0_add_smul, srcOf_add_smul, spin0_refPt, srcOf_refPt, spin0_single_inr, srcOf_single_inr]
  simp only [dot_add_left, dot_add_right, dot_smul_left, dot_smul_right, dot_single_left,
    Pi.single_eq_same, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm, smul_zero, add_zero,
    mul_zero]
  ring

theorem pinCexF_refPt (a : ℂ) (i₀ : Fin N) (ν : ℝ) : pinCexF a (refPt i₀ ν (site0 d)) = 0 := by
  have := pinCexF_line_spin (d := d) a i₀ ν 0
  simpa using this

/-- The first reference jets of the one-site term vanish in the radial spin direction… -/
theorem pinCex_fderiv_spin (a : ℂ) (i₀ : Fin N) (ν : ℝ) :
    fderiv ℂ (pinCexF a) (refPt i₀ ν (site0 d)) (Pi.single (Sum.inl (ctr0 d, i₀)) 1) = 0 := by
  rw [← iteratedDeriv_one_line (pinCexF_analyticAt a _).differentiableAt, iteratedDeriv_one]
  have e : (fun t : ℂ => pinCexF a (refPt i₀ ν (site0 d) +
      t • Pi.single (Sum.inl (ctr0 d, i₀)) 1)) = fun _ => 0 := funext (pinCexF_line_spin a i₀ ν)
  rw [e]; simp

/-- … and in the longitudinal source direction. -/
theorem pinCex_fderiv_blong (a : ℂ) (i₀ : Fin N) (ν : ℝ) :
    fderiv ℂ (pinCexF a) (refPt i₀ ν (site0 d)) (Pi.single (Sum.inr i₀) 1) = 0 := by
  rw [← iteratedDeriv_one_line (pinCexF_analyticAt a _).differentiableAt, iteratedDeriv_one]
  have e : (fun t : ℂ => pinCexF a (refPt i₀ ν (site0 d) +
      t • Pi.single (Sum.inr i₀) 1)) = fun _ => 0 := funext (pinCexF_line_blong a i₀ ν)
  rw [e]; simp

theorem iteratedDeriv_two_mul_sq (a : ℂ) : iteratedDeriv 2 (fun t : ℂ => a * t ^ 2) 0 = 2 * a := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : deriv (fun t : ℂ => a * t ^ 2) = fun t => a * (2 * t) := by
    funext t
    simp
  rw [h1]
  simp [mul_comm]

/-- **PIN-I6 (2.4)**: the second transverse-`b` derivative of the one-site term at the reference
point is `2a = 2c/m`. -/
theorem pinCex_D2_bperp (a : ℂ) (hne : i₁ ≠ i₀) (ν : ℝ) :
    D2 (pinCexF a) (refPt i₀ ν (site0 d)) (Pi.single (Sum.inr i₁) 1) (Pi.single (Sum.inr i₁) 1) =
      2 * a := by
  rw [← iteratedDeriv_two_line (ρ := 1) one_pos fun c _ => pinCexF_analyticAt a c]
  have e : (fun t : ℂ => pinCexF a (refPt i₀ ν (site0 d) + t • Pi.single (Sum.inr i₁) 1)) =
      fun t => a * t ^ 2 := funext (pinCexF_line_bperp a hne ν)
  rw [e]; exact iteratedDeriv_two_mul_sq a

/-- **The one-site term has no reference-jet certificate with constants uniform in the mass**: the
certificate with bound `M` and radius `r` fails as soon as `4 M / r² < 2 c / m`. -/
theorem pinCex_not_refJet (hne : i₁ ≠ i₀) {m c₀ r M : ℝ} (hm : 0 < m) (hc : 0 ≤ c₀)
    (h : 4 * M / r ^ 2 < 2 * c₀ / m) :
    ¬ RefJet i₀ m r M (site0 d) (pinCexF (N := N) ((c₀ / m : ℝ) : ℂ)) := by
  intro hJ
  have h1 := hJ.d2_bperp hne
  rw [pinCex_D2_bperp _ hne] at h1
  have e : ‖(2 : ℂ) * ((c₀ / m : ℝ) : ℂ)‖ = 2 * c₀ / m := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg hc hm.le)]
    simp only [Complex.norm_ofNat]; ring
  rw [e] at h1
  linarith

/-- **The renormalization conditions (H.5)(1)-(4)** hold for the one-site family (PIN-I6 §2): the
value and the two first reference jets vanish, and the moment condition is void (both spin
derivatives are at the centre). -/
theorem pinCex_sumConds (a : ℂ) (i₀ i₁ : Fin N) (ν : ℝ) :
    SumConds (pinCexFamily d N a) i₀ i₁ ν where
  ren_val := by
    have h : ∀ X : (pinCexFamily d N a).polys,
        (pinCexFamily d N a).term X.1 (refPt i₀ ν X.1) = 0 := by
      rintro ⟨X, hX⟩
      obtain rfl : X = site0 d := hX
      rw [pinCexFamily_term]; exact pinCexF_refPt a i₀ ν
    simp only [h, tsum_zero]
  ren_b := by
    have h : ∀ X : (pinCexFamily d N a).polys,
        fderiv ℂ ((pinCexFamily d N a).term X.1) (refPt i₀ ν X.1) (Pi.single (Sum.inr i₀) 1) = 0 := by
      rintro ⟨X, hX⟩
      obtain rfl : X = site0 d := hX
      rw [pinCexFamily_term]; exact pinCex_fderiv_blong a i₀ ν
    simp only [h, tsum_zero]
  ren_psi := by
    have h : ∀ X : (pinCexFamily d N a).polys,
        ∑ x : ↥X.1, tensA i₀ ν X.1 ((pinCexFamily d N a).term X.1) x = 0 := by
      rintro ⟨X, hX⟩
      obtain rfl : X = site0 d := hX
      rw [pinCexFamily_term]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [ctr0_eq x]; exact pinCex_fderiv_spin a i₀ ν
    simp only [h, tsum_zero]
  moment := by
    have h : ∀ X : (pinCexFamily d N a).polys, ∑ x : ↥X.1, ∑ x' : ↥X.1,
        tensB i₀ i₁ ν X.1 ((pinCexFamily d N a).term X.1) x x' *
          (∑ μ, (((x.1 μ - x'.1 μ : ℤ) : ℂ)) ^ 2) = 0 := by
      rintro ⟨X, hX⟩
      obtain rfl : X = site0 d := hX
      refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun x' _ => ?_
      rw [ctr0_eq x, ctr0_eq x']
      simp
    simp only [h, tsum_zero]

/-- **The I-6 remainder of the one-site family is the term itself** (PIN-I6 §2): `Ttw = 0` (the
value and the first reference jets vanish), `Ax = 0` (the radial spin derivative vanishes),
`Phitw = 0` (the second moment tensor of a one-site polymer is zero). -/
theorem pinCex_itw_eq (a : ℂ) (i₀ i₁ : Fin N) (ν : ℝ) (ψ : Site d → Spin N) (b : Spin N) :
    Itw (pinCexFamily d N a) i₀ i₁ ν (site0 d) ψ b =
      a * (dot (ψ 0) (ψ 0) * dot b b - dot (ψ 0) b ^ 2) := by
  have hA : ∀ x : ↥(site0 d), tensA i₀ ν (site0 d) ((pinCexFamily d N a).term (site0 d)) x = 0 := by
    intro x
    rw [pinCexFamily_term, ctr0_eq x]; exact pinCex_fderiv_spin a i₀ ν
  have hT : Ttw (pinCexFamily d N a) i₀ ν (site0 d) ψ b = 0 := by
    unfold Ttw
    simp only [hA, Finset.sum_const_zero, mul_zero, add_zero]
    rw [pinCexFamily_term, pinCexF_refPt, pinCex_fderiv_blong, mul_zero, add_zero]
  have hAx : Ax (pinCexFamily d N a) i₀ ν ψ (site0 d) = 0 := by
    unfold Ax
    simp only [hA, zero_mul, Finset.sum_const_zero, mul_zero]
  have hS : ∀ μ μ' : Fin d, Sx (pinCexFamily d N a) i₀ i₁ ν (site0 d) μ μ' = 0 := by
    intro μ μ'
    unfold Sx
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun x' _ => ?_
    rw [ctr0_eq x, ctr0_eq x']
    simp
  have hP : Phitw (pinCexFamily d N a) i₀ i₁ ν (site0 d) ψ = 0 := by
    unfold Phitw
    simp only [hS, mul_zero, Finset.sum_const_zero]
  unfold Itw
  rw [hT, hAx, hP, pinCexFamily_term, pinCexF_pack]
  ring

theorem norm_dot_le {v w : Spin N} {B : ℝ} (hv : ∀ i, ‖v i‖ ≤ B) (hw : ∀ i, ‖w i‖ ≤ B)
    (hB : 0 ≤ B) : ‖dot v w‖ ≤ N * B ^ 2 := by
  unfold dot
  calc ‖∑ i, v i * w i‖ ≤ ∑ i : Fin N, ‖v i * w i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, B ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [norm_mul, sq]; exact mul_le_mul (hv i) (hw i) (norm_nonneg _) hB
    _ = N * B ^ 2 := by simp

/-- **The pinned bound of the one-site term** (PIN-I6 §2: "on any fixed pinned chart with bounded
`p, h` it has norm at most `C_pin c m`"): at the physical source `b = m h` with `|p|, |h| ≤ B`
coordinatewise, `|f_m(p, m h)| ≤ 2 c m (N B²)²`, uniformly small as `m ↓ 0`. -/
theorem pinCex_pinned_bound {m c₀ B : ℝ} (hm : 0 < m) (hc : 0 ≤ c₀) (hB : 0 ≤ B)
    (ψ : Site d → Spin N) (h : Spin N) (hψ : ∀ i, ‖ψ 0 i‖ ≤ B) (hh : ∀ i, ‖h i‖ ≤ B) :
    ‖pinCexF ((c₀ / m : ℝ) : ℂ) (pack (site0 d) ψ ((m : ℂ) • h))‖ ≤
      2 * c₀ * m * ((N : ℝ) * B ^ 2) ^ 2 := by
  rw [pinCexF_pack]
  have e : ((c₀ / m : ℝ) : ℂ) * (dot (ψ 0) (ψ 0) * dot ((m : ℂ) • h) ((m : ℂ) • h) -
      dot (ψ 0) ((m : ℂ) • h) ^ 2) =
      ((c₀ * m : ℝ) : ℂ) * (dot (ψ 0) (ψ 0) * dot h h - dot (ψ 0) h ^ 2) := by
    simp only [dot_smul_left, dot_smul_right]
    push_cast
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hc hm.le)]
  have h1 := norm_dot_le hψ hψ hB
  have h2 := norm_dot_le hh hh hB
  have h3 := norm_dot_le hψ hh hB
  have hNB : (0 : ℝ) ≤ N * B ^ 2 := by positivity
  have h4 : ‖dot (ψ 0) (ψ 0) * dot h h - dot (ψ 0) h ^ 2‖ ≤ 2 * ((N : ℝ) * B ^ 2) ^ 2 := by
    calc ‖dot (ψ 0) (ψ 0) * dot h h - dot (ψ 0) h ^ 2‖
        ≤ ‖dot (ψ 0) (ψ 0) * dot h h‖ + ‖dot (ψ 0) h ^ 2‖ := norm_sub_le _ _
      _ = ‖dot (ψ 0) (ψ 0)‖ * ‖dot h h‖ + ‖dot (ψ 0) h‖ ^ 2 := by rw [norm_mul, norm_pow]
      _ ≤ (N * B ^ 2) * (N * B ^ 2) + (N * B ^ 2) ^ 2 :=
        add_le_add (mul_le_mul h1 h2 (norm_nonneg _) hNB)
          (pow_le_pow_left₀ (norm_nonneg _) h3 2)
      _ = 2 * ((N : ℝ) * B ^ 2) ^ 2 := by ring
  calc c₀ * m * ‖dot (ψ 0) (ψ 0) * dot h h - dot (ψ 0) h ^ 2‖
      ≤ c₀ * m * (2 * ((N : ℝ) * B ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left h4 (mul_nonneg hc hm.le)
    _ = _ := by ring

/-- **PIN-I6 (2.3)**: at the constant rotated spin `p_θ = cos θ e + sin θ e₂` and the aligned
physical source `b = m e`, the I-6 remainder of the one-site family is `c m sin² θ`. -/
theorem pinCex_itw (hne : i₁ ≠ i₀) {m : ℝ} (hm : m ≠ 0) (c₀ θ : ℝ) :
    Itw (pinCexFamily d N ((c₀ / m : ℝ) : ℂ)) i₀ i₁ m (site0 d)
        (fun _ => (Real.cos θ : ℂ) • Pi.single i₀ 1 + (Real.sin θ : ℂ) • Pi.single i₁ 1)
        ((m : ℂ) • Pi.single i₀ 1) = ((c₀ * m * Real.sin θ ^ 2 : ℝ) : ℂ) := by
  rw [pinCex_itw_eq]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  simp only [dot_add_left, dot_add_right, dot_smul_left, dot_smul_right, dot_single_left,
    Pi.single_eq_same, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm, mul_zero, add_zero,
    zero_add, mul_one]
  push_cast
  field_simp
  ring

/-- **The termwise I-6 bound fails on the pinned class without the reference-jet certificate** (PIN-I6 §2, (2.3)).  For the one-site family (which satisfies the renormalization
conditions `pinCex_sumConds` and the pinned bound `pinCex_pinned_bound`), every claimed constant
`C` in the estimate `|Itw| ≤ C E₀ σ^{3-α₁} (ε/r)²` of PIN-I6 (3.2), with `E₀`, `r`, `ε`, `α₁ < 1`
fixed, is violated at some `0 < σ ≤ 1`, with the mass `m = σ²`, the constant spin
`p_θ`, `θ = ε/2`, and the aligned source `b = m e`.  So the clause `refJet` of `SourceForm` cannot be
dropped. -/
theorem pinI6_no_uniform_bound (hne : i₁ ≠ i₀) {c₀ E₀ r α₁ ε : ℝ} (hc₀ : 0 < c₀) (hα : α₁ < 1)
    (hε : 0 < ε) (hε1 : ε < 1) (C : ℝ) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧
      C * E₀ * σ ^ (3 - α₁) * (ε / r) ^ 2 <
        ‖Itw (pinCexFamily d N ((c₀ / σ ^ 2 : ℝ) : ℂ)) i₀ i₁ (σ ^ 2) (site0 d)
          (fun _ => (Real.cos (ε / 2) : ℂ) • Pi.single i₀ 1 +
            (Real.sin (ε / 2) : ℂ) • Pi.single i₁ 1)
          (((σ ^ 2 : ℝ) : ℂ) • Pi.single i₀ 1)‖ := by
  set s := Real.sin (ε / 2) with hs
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.two_le_pi])
  set K := C * E₀ * (ε / r) ^ 2 with hK
  set q := 1 - α₁ with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  set t := c₀ * s ^ 2 / (|K| + 1) with ht
  have ht0 : 0 < t := by positivity
  set σ := min 1 (t ^ (1 / q)) with hσ
  have hσ0 : 0 < σ := lt_min one_pos (Real.rpow_pos_of_pos ht0 _)
  have hσ1 : σ ≤ 1 := min_le_left _ _
  have hσq : σ ^ q ≤ t := by
    calc σ ^ q ≤ (t ^ (1 / q)) ^ q := Real.rpow_le_rpow hσ0.le (min_le_right _ _) hq0.le
      _ = t := by rw [← Real.rpow_mul ht0.le, one_div_mul_cancel hq0.ne', Real.rpow_one]
  refine ⟨σ, hσ0, hσ1, ?_⟩
  rw [pinCex_itw hne (pow_ne_zero 2 hσ0.ne'), Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have hpow : σ ^ (3 - α₁) = σ ^ 2 * σ ^ q := by
    rw [show (3 : ℝ) - α₁ = (2 : ℕ) + q by rw [hq]; push_cast; ring,
      Real.rpow_add hσ0, Real.rpow_natCast]
  have hσq0 : 0 ≤ σ ^ q := (Real.rpow_pos_of_pos hσ0 q).le
  have h1 : K * σ ^ q < c₀ * s ^ 2 := by
    have hKt : |K| * t < c₀ * s ^ 2 := by
      rw [ht, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
      have : 0 < c₀ * s ^ 2 := by positivity
      nlinarith [abs_nonneg K]
    calc K * σ ^ q ≤ |K| * σ ^ q := mul_le_mul_of_nonneg_right (le_abs_self K) hσq0
      _ ≤ |K| * t := mul_le_mul_of_nonneg_left hσq (abs_nonneg K)
      _ < c₀ * s ^ 2 := hKt
  calc C * E₀ * σ ^ (3 - α₁) * (ε / r) ^ 2 = σ ^ 2 * (K * σ ^ q) := by rw [hpow, hK]; ring
    _ < σ ^ 2 * (c₀ * s ^ 2) := mul_lt_mul_of_pos_left h1 (by positivity)
    _ = c₀ * σ ^ 2 * s ^ 2 := by ring

end Cex

end Balaban.SmallField
