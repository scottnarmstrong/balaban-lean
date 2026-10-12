module

public import Balaban.LargeField.Operators.QuietInt

/-!
# One-step bound for quiet steps (Part II, Lemma II.5.14; block K4)

`quietKernel_bound`: the quiet kernel satisfies (S1)-(S2) of Definition II.5.7 in the Gaussian
form of `GaussStepSpec`, with the exponent `κ^{(k)} = -(c₁ log β_k + c₂) |Z^c_k ∩ Z'|_{k+1}`.
The witness is `W = {*}`, `F ≡ 1`, `K̃ =` `quietRest` (`quietKernel_eq`); `K̃` does not read
`ψ_{k+1}` on the Gaussian blocks (`quietRest_congr`); the majorant is
`e^{(C_b log β_k + C_b B_0)|Z^c_k ∩ Z'|_{k+1}}` times the product of the shell indicators of the
new′ variables (`shell_newOut`, `shell_newPrime`), whose integral is `≤ (c_N · 3dLδ_k)^# ≤ 1`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal

section Final

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0} {k : ℕ}
  (geo : Geo S n R M) (cs : OpConsts)

open Classical in
/-- **Lemma II.5.14 (one-step bound for quiet steps; version 1.1, audit P2-02).**  Let the step
`k → k+1` be quiet in `Z'`, `T` a large-field kernel whose `K` is the quiet kernel (S1), whose `b`
satisfies (S0) on the domain `χ^new_k`, `c₁ ≥ C_b`, `c₂ ≥ C_b B₀`, and (Λ17′)
`3dL c_N δ_k ≤ 1/2`.  Then (S1)-(S2) hold with the single witness function `F ≡ 1` and
`κ^{(k)} = -(c₁ log β_k + c₂) |Z^c_k ∩ Z'|_{k+1}`, for every `z_{k+1}` (the Gaussian factor is
integrated first, whatever the sign of `z_{k+1}`; positivity of `z_{k+1}` is needed only to use the
bound in `preOp_pkgBound`).

Scope/typing premises (recorded): `2 ≤ N`, `1 ≤ k` (the scale-`0` variables are spins and are
treated in Lemma II.7.8), `0 < β_k a L^{d-2}`, `0 ≤ log β_k`, `0 < δ_k`, `3 d L δ_k ≤ 1/2` (the
shell inequality `t ≤ 1/2` of the proof; it does not follow from (Λ17′) when `c_N < 1`), and the
signs `0 ≤ β_{k+1}`, `0 ≤ a_n`, `0 ≤ ν_{k+1} L^{-2(k+1)}` of the main action. -/
theorem quietKernel_bound [NeZero N] (hN : 2 ≤ N) (hk1 : 1 ≤ k) (hK : k + 1 ≤ K)
    (Z' : H.Comp (k + 1)) (hq : IsQuiet (H.locRH (k + 1) Z') k Z'.1)
    (T : LFKernel (OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
      (NewCfg N (H.localHistory M K (k + 1) Z') k) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N))
    (hTK : ∀ o x hv, T.K o x hv = quietKernel geo (H.locRH (k + 1) Z') k Z'.1
      (locComp_mem H Z') cs hK (locRH_rem (k + 1) Z') o x hv)
    (hb : ∀ o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
      ChiNewAt geo cs H k Z' o x →
      ‖T.b o x hv g‖ ≤ (cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
        volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
          z ∉ (H.localHistory M K (k + 1) Z').Z k})
    (c1 c2 : ℝ) (hc1 : cs.Cb ≤ c1) (hc2 : cs.Cb * cs.B0 ≤ c2)
    (hlog : 0 ≤ Real.log (cs.beta k))
    (hc : 0 < cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hδ : 0 < cs.delta k) (hδ1 : 3 * S.d * S.L * cs.delta k ≤ 1 / 2)
    (hΛ : 3 * S.d * S.L * cShell N * cs.delta k ≤ 1 / 2)
    (hβ : 0 ≤ cs.beta (k + 1)) (haw : ∀ n, 0 ≤ cs.aw n) (hμ : 0 ≤ cs.muAct (k + 1)) :
    ∃ wit : GaussWit N R (H.localHistory M K (k + 1) Z') k,
      GaussStepSpec cs R (H.localHistory M K (k + 1) Z') k
        (-(c1 * Real.log (cs.beta k) + c2) *
          volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
            z ∉ (H.localHistory M K (k + 1) Z').Z k}) T wit := by
  have hd0 : (0 : ℝ) < S.d := by
    have := H.F.ok.three_le_d; exact_mod_cast (by omega : 0 < S.d)
  have hL0 : (0 : ℝ) < S.L := by
    have := H.F.ok.two_le_L; exact_mod_cast (by omega : 0 < S.L)
  have hdL : 1 ≤ S.d * S.L := by
    have h1 := H.F.ok.three_le_d; have h2 := H.F.ok.two_le_L; nlinarith
  have ht : 0 < 3 * (S.d : ℝ) * S.L * cs.delta k := by positivity
  have hct : cShell N * (3 * (S.d : ℝ) * S.L * cs.delta k) ≤ 1 := by
    have : cShell N * (3 * (S.d : ℝ) * S.L * cs.delta k) =
        3 * S.d * S.L * cShell N * cs.delta k := by ring
    linarith
  have hvol0 : 0 ≤ volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
      z ∉ (H.localHistory M K (k + 1) Z').Z k} := by
    unfold volScale; positivity
  let wit : GaussWit N R (H.localHistory M K (k + 1) Z') k :=
    { W := Unit
      F := fun _ _ => 1
      Kt := fun _ o x hv => quietRest geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H Z') cs hK
        (locRH_rem (k + 1) Z') o x hv }
  refine ⟨wit, ?_⟩
  have hunit := fun o x hv => quietRest_unit (N := N) geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H Z') cs hK
    (locRH_rem (k + 1) Z') hβ haw hμ o x hv
  refine ⟨fun _ _ => ⟨zero_le_one, le_rfl⟩, fun _ => measurable_const,
    fun _ o x hv => (hunit o x hv).1,
    fun _ o o' x hv hoo => quietRest_congr geo cs hK Z' o o' x hv hoo, ?_, ?_⟩
  · intro o x hv
    rw [hTK]
    refine (quietKernel_eq geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H Z') cs hK
      (locRH_rem (k + 1) Z') o x hv).trans ?_
    simp only [wit, Finset.univ_unique, Finset.sum_singleton, one_mul]
    rfl
  · let Sw : wit.W → OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (newOutP (H.localHistory M K (k + 1) Z') k) →
        SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
          (newPrimeVars (H.localHistory M K (k + 1) Z') k) →
        OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
          (parOutP (H.localHistory M K (k + 1) Z') k) →
        EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → ℝ≥0∞ :=
      fun _ on x' _ _ _ => ENNReal.ofReal (Real.exp ((cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
        volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
          z ∉ (H.localHistory M K (k + 1) Z').Z k})) *
        ((if ∀ y, |‖on y‖ ^ 2 - 1| < 3 * (S.d : ℝ) * S.L * cs.delta k then (1 : ℝ≥0∞) else 0) *
         (if ∀ p : ↥(newPrimeVars (H.localHistory M K (k + 1) Z') k),
            |‖VarVal.toEuc (x' p)‖ ^ 2 - 1| < 3 * (S.d : ℝ) * S.L * cs.delta k then
            (1 : ℝ≥0∞) else 0))
    refine ⟨Sw, ?_, ?_, ?_⟩
    · intro w par hv g
      have hm1 := measurable_indOut N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (newOutP (H.localHistory M K (k + 1) Z') k) (3 * (S.d : ℝ) * S.L * cs.delta k)
      have hm2 := measurable_indNew N (H.localHistory M K (k + 1) Z')
        (newPrimeVars (H.localHistory M K (k + 1) Z') k) (3 * (S.d : ℝ) * S.L * cs.delta k)
      refine measurable_const.mul (Measurable.mul ?_ ?_)
      · exact hm1.comp measurable_fst
      · exact hm2.comp measurable_snd
    · intro w o x hv g hg
      by_cases hchi : ChiNewAt geo cs H k Z' o x
      · have h1 : wit.Kt w o x hv ≤ 1 := (hunit o x hv).2
        have h2 : Real.exp (T.b o x hv g).re ≤ Real.exp ((cs.Cb * Real.log (cs.beta k) +
            cs.Cb * cs.B0) * volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
              z ∉ (H.localHistory M K (k + 1) Z').Z k}) :=
          Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (hb o x hv g hg hchi))
        have hI1 : (if ∀ y : {y : BlockAt S n M K (k + 1) //
            y ∈ Vblk R (H.localHistory M K (k + 1) Z') (k + 1) ∧
              newOutP (H.localHistory M K (k + 1) Z') k y},
            |‖restrictOutPart o (newOutP (H.localHistory M K (k + 1) Z') k) y‖ ^ 2 - 1| <
              3 * (S.d : ℝ) * S.L * cs.delta k then (1 : ℝ≥0∞) else 0) = 1 := by
          have hall : ∀ y : {y : BlockAt S n M K (k + 1) //
              y ∈ Vblk R (H.localHistory M K (k + 1) Z') (k + 1) ∧
                newOutP (H.localHistory M K (k + 1) Z') k y},
              |‖restrictOutPart o (newOutP (H.localHistory M K (k + 1) Z') k) y‖ ^ 2 - 1| <
                3 * (S.d : ℝ) * S.L * cs.delta k := by
            intro y
            have := shell_newOut geo cs hK Z' o x hchi y.1 y.2.2
            simpa [restrictOutPart, outField, y.2.1] using this
          simp only [hall, implies_true, ↓reduceIte]
        have hI2 : (if ∀ p : ↥(newPrimeVars (H.localHistory M K (k + 1) Z') k),
            |‖VarVal.toEuc (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k) x p)‖ ^ 2 - 1| <
              3 * (S.d : ℝ) * S.L * cs.delta k then (1 : ℝ≥0∞) else 0) = 1 := by
          have hall : ∀ p : ↥(newPrimeVars (H.localHistory M K (k + 1) Z') k),
              |‖VarVal.toEuc (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k) x p)‖ ^ 2 - 1| <
                3 * (S.d : ℝ) * S.L * cs.delta k := fun p =>
            shell_newPrime geo cs hK hk1 hδ.le hdL Z' hq o x hchi p.1 p.2
          simp only [hall, implies_true, ↓reduceIte]
        show ENNReal.ofReal (wit.Kt w o x hv * _) ≤ ENNReal.ofReal (_) * ((if _ then _ else _) * (if _ then _ else _))
        rw [hI1, hI2]
        simp only [mul_one]
        refine ENNReal.ofReal_le_ofReal ?_
        calc _ ≤ 1 * Real.exp (T.b o x hv g).re :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          _ ≤ _ := by rw [one_mul]; exact h2
      · have hz0 := quietRest_eq_zero geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H Z') cs hK
          (locRH_rem (k + 1) Z') o x hv hchi
        have hK0 : wit.Kt w o x hv = 0 := hz0
        show ENNReal.ofReal (wit.Kt w o x hv * _) ≤ _
        rw [hK0, zero_mul, ENNReal.ofReal_zero]
        exact zero_le
    · intro par hv g hg
      have hA : ∀ p ∈ newPrimeVars (H.localHistory M K (k + 1) Z') k, p.isSpin = false := by
        intro p hp
        unfold InternalVars.isSpin
        have h1 : p.1.1.val = k := hp.1
        exact decide_eq_false (fun h => by omega)
      have hm1 := measurable_indOut N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (newOutP (H.localHistory M K (k + 1) Z') k) (3 * (S.d : ℝ) * S.L * cs.delta k)
      have hm2 := measurable_indNew N (H.localHistory M K (k + 1) Z')
        (newPrimeVars (H.localHistory M K (k + 1) Z') k) (3 * (S.d : ℝ) * S.L * cs.delta k)
      have hi1 := lintegral_indOut_le_one N hN (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
        (newOutP (H.localHistory M K (k + 1) Z') k) ht hδ1 hct
      have hi2 := lintegral_indNew_le_one N hN (H.localHistory M K (k + 1) Z')
        (newPrimeVars (H.localHistory M K (k + 1) Z') k) hA ht hδ1 hct
      have hmw := mWit_one N hc (H.localHistory M K (k + 1) Z') k
      simp only [Finset.univ_unique, Finset.sum_singleton]
      show mWit N _ _ k (fun (_ : Unit) _ => (1 : ℝ)) () * _ ≤ _
      rw [hmw, one_mul]
      have e1 : ∫⁻ q : OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
            (newOutP (H.localHistory M K (k + 1) Z') k) ×
            SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
              (newPrimeVars (H.localHistory M K (k + 1) Z') k), Sw () q.1 q.2 (parC _ k par) hv g
          ∂((outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
            (newOutP (H.localHistory M K (k + 1) Z') k)).prod
            (subMeasure N (H.localHistory M K (k + 1) Z') (k + 1)
              (newPrimeVars (H.localHistory M K (k + 1) Z') k))) =
          ENNReal.ofReal (Real.exp ((cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
            volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
              z ∉ (H.localHistory M K (k + 1) Z').Z k})) *
          ((∫⁻ on, (if ∀ y, |‖on y‖ ^ 2 - 1| < 3 * (S.d : ℝ) * S.L * cs.delta k then (1 : ℝ≥0∞) else 0)
              ∂(outPartMeasure N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
                (newOutP (H.localHistory M K (k + 1) Z') k))) *
           ∫⁻ x', (if ∀ p : ↥(newPrimeVars (H.localHistory M K (k + 1) Z') k),
              |‖VarVal.toEuc (x' p)‖ ^ 2 - 1| < 3 * (S.d : ℝ) * S.L * cs.delta k then (1 : ℝ≥0∞) else 0)
              ∂(subMeasure N (H.localHistory M K (k + 1) Z') (k + 1)
                (newPrimeVars (H.localHistory M K (k + 1) Z') k))) := by
        show ∫⁻ q, ENNReal.ofReal _ * (_ * _) ∂_ = _
        rw [lintegral_const_mul]
        · congr 1
          exact lintegral_prod_mul
            (f := fun on : OutPart N (Vblk R (H.localHistory M K (k + 1) Z') (k + 1))
              (newOutP (H.localHistory M K (k + 1) Z') k) =>
              (if ∀ y, |‖on y‖ ^ 2 - 1| < 3 * (S.d : ℝ) * S.L * cs.delta k then (1 : ℝ≥0∞) else 0))
            (g := fun x' : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
              (newPrimeVars (H.localHistory M K (k + 1) Z') k) =>
              (if ∀ p : ↥(newPrimeVars (H.localHistory M K (k + 1) Z') k),
                |‖VarVal.toEuc (x' p)‖ ^ 2 - 1| < 3 * (S.d : ℝ) * S.L * cs.delta k then
                (1 : ℝ≥0∞) else 0))
            hm1.aemeasurable hm2.aemeasurable
        · refine Measurable.mul ?_ ?_
          · exact hm1.comp measurable_fst
          · exact hm2.comp measurable_snd
      rw [e1]
      calc _ ≤ ENNReal.ofReal (Real.exp ((cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
            volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
              z ∉ (H.localHistory M K (k + 1) Z').Z k})) * (1 * 1) := by gcongr
        _ ≤ _ := by
          rw [mul_one, mul_one]
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          have : (cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) ≤ c1 * Real.log (cs.beta k) + c2 :=
            add_le_add (mul_le_mul_of_nonneg_right hc1 hlog) hc2
          nlinarith [mul_le_mul_of_nonneg_right this hvol0]

end Final

end Balaban.LargeField
