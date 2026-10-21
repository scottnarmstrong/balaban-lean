/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkCluster
public import Balaban.Fluctuation.HoleStepMarks

/-!
# Reality of the local terms of the cluster expansion (Theorem 3.4)

The local terms of the cluster expansion with one mark are real when the activities (at real values
of the interpolation parameter) and the mark are real: the activities of the polymers are integrals of
products of `e^{H} - 1` (`mayerK_conj`), the local terms `P(Y)` are series of products of them with
integer coefficients (`PY_conj`), and `G*(Y₀, S)` is the derivative at `0` of a function real on the
real line (`D1_conj_of_real`).

* `PY_conj`, `mayerK_conj`, `D1_conj_of_real`, `Gst_conj`;
* `markTerm_conj`: the cluster term `∫₀¹ G*(Y₀, S) du` of one mark;
* `HoleStep.markOf_conj`: the cut-off mark of a function real at real fields, with real fixed values.
-/

@[expose] public section


open MeasureTheory ComplexConjugate

namespace Balaban.Polymer

section Real

/-- The local term `P(Y)` of the cluster sum is real when the activities are real. -/
theorem PY_conj {P : Type*} [Fintype P] (inc : P → P → Prop) {B : Type*} [Fintype B]
    (supp : P → Finset B) (K : P → ℂ) (hK : ∀ Z, conj (K Z) = K Z) (Y : Finset B) :
    conj (PY inc supp K Y) = PY inc supp K Y := by
  unfold PY
  rw [Complex.conj_tsum]
  congr 1
  funext n
  unfold Pterm
  simp only [map_mul, map_inv₀, map_natCast, map_sum, map_prod, map_intCast, hK]

/-- The activity of a polymer of the Mayer expansion is real when the terms are real. -/
theorem mayerK_conj {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
    (μ : ∀ b, Measure (Ω b)) {T : Type*} [Fintype T] (sup : T → Finset B)
    (H : T → (∀ b, Ω b) → ℂ) (hH : ∀ t Φ, conj (H t Φ) = H t Φ) (Y : NePoly B) :
    conj (mayerK μ sup H Y) = mayerK μ sup H Y := by
  unfold mayerK mayerAct polyAct
  rw [← integral_conj]
  congr 1
  funext Φ
  simp only [map_sum, map_prod, map_sub, map_one, ← Complex.exp_conj, hH]

/-- **The derivative at `0` of a function real on the real line is real.** -/
theorem D1_conj_of_real {f : (Unit → ℂ) → ℂ} (hf : ∀ t : ℝ, conj (f fun _ => (t : ℂ)) =
    f fun _ => (t : ℂ)) : conj (D1 () f) = D1 () f := by
  rw [Complex.conj_eq_iff_im]
  unfold D1
  by_cases hd : DifferentiableAt ℂ f 0
  · set e : ℝ →L[ℝ] (Unit → ℂ) := (ContinuousLinearMap.pi fun _ : Unit => Complex.ofRealCLM)
      with he
    have hg : HasDerivAt (fun t : ℝ => f (e t)) (fderiv ℂ f 0 (Pi.single () 1)) 0 := by
      have h1 : HasFDerivAt f ((fderiv ℂ f 0).restrictScalars ℝ) (e 0) := by
        rw [show e 0 = 0 from map_zero e]
        exact hd.hasFDerivAt.restrictScalars ℝ
      have h2 := h1.comp_hasDerivAt (0 : ℝ) e.hasFDerivAt.hasDerivAt
      convert h2 using 1
      show _ = (fderiv ℂ f 0) (e 1)
      congr 1
      funext u
      simp [he]
    have him : HasDerivAt (fun t : ℝ => (f (e t)).im) (fderiv ℂ f 0 (Pi.single () 1)).im 0 :=
      (Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg)
    have hzero : (fun t : ℝ => (f (e t)).im) = fun _ => 0 := by
      funext t
      have := hf t
      rw [Complex.conj_eq_iff_im] at this
      simpa [he] using this
    rw [hzero] at him
    exact him.unique (hasDerivAt_const 0 0)
  · rw [fderiv_zero_of_not_differentiableAt hd]
    simp

end Real

end Balaban.Polymer

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

/-- **`G*(Y₀, S)` is real when the activities and the mark are real.** -/
theorem Gst_conj {Lb : Type*} [Fintype Lb] {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ j Ω Lb)
    (H : Lb → (∀ b, Ωb b) → ℂ) (S₀ : Finset 𝔅) (G : (∀ b, Ωb b) → ℂ) (S : Finset 𝔅)
    (hH : ∀ y Φ, conj (H y Φ) = H y Φ) (hG : ∀ Φ, conj (G Φ) = G Φ) :
    conj (Gst μ Lab H S₀ G S) = Gst μ Lab H S₀ G S := by
  unfold Gst
  refine D1_conj_of_real fun t => ?_
  unfold Ff
  refine PY_conj _ _ _ (fun Z => ?_) S
  unfold marksK
  refine mayerK_conj _ _ _ (fun T Φ => ?_) Z
  unfold Hlam presum gMark
  simp only [map_add, map_sum, map_mul, Complex.conj_ofReal, hH]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [hG]

variable {Lb : Type*} [Fintype Lb]
  {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω Lb}
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {εH κH κ0 Kc : ℝ}

/-- **The cluster term of one mark is real** when the activities at real parameters and the mark
are real (`Gst_conj`). -/
theorem markTerm_conj (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (V : Set (CTorus d L N₁ m₁ K)) (G : (∀ b, Ωb b) → ℂ)
    (S : Finset 𝔅) (hA : ∀ (u : ℝ) y Φ, conj ((A (u : ℂ)).H y Φ) = (A (u : ℂ)).H y Φ)
    (hG : ∀ Φ, conj (G Φ) = G Φ) : conj (markTerm μ A V G S) = markTerm μ A V G S := by
  unfold markTerm
  have hre : ∀ u : ℝ, Gst μ Lab (A (u : ℂ)).H (blocksOf m₀ j Ω V) G S =
      ((Gst μ Lab (A (u : ℂ)).H (blocksOf m₀ j Ω V) G S).re : ℂ) := fun u =>
    (Complex.conj_eq_iff_re.1 (Gst_conj μ Lab _ _ G S (hA u) hG)).symm
  rw [intervalIntegral.integral_congr (fun u _ => hre u), intervalIntegral.integral_ofReal,
    Complex.conj_ofReal]

namespace HoleStep

variable {k N : ℕ} {ϱ ϱ' : ℝ} (S : HoleStep d L N₁ m₁ k N ϱ ϱ') {Cb : Type*}

/-- **The cut-off mark of a function real at real fields is real**, when the fixed values are
real. -/
theorem markOf_conj (inner : Finset S.U) (cb : inner → Cb) {ψout : S.U → Fin N → ℂ}
    (U₀ : Finset S.U) (r : ℝ) {T : (S.U → Fin N → ℂ) → ℂ}
    (hout : ∀ b i, conj (ψout b i) = ψout b i)
    (hT : ∀ ψ : S.U → Fin N → ℂ, (∀ b i, conj (ψ b i) = ψ b i) → (∀ b ∈ U₀, vn (ψ b) < r) →
      conj (T ψ) = T ψ) (Φ : ∀ b, {u : inner // cb u = b} → Rn N) :
    conj (S.markOf inner cb ψout U₀ r T Φ) = S.markOf inner cb ψout U₀ r T Φ := by
  unfold markOf
  split_ifs with h
  · refine hT _ (fun b i => ?_) h
    unfold fill
    split_ifs
    · exact Complex.conj_ofReal _
    · exact hout b i
  · exact map_zero _

end HoleStep

end Balaban.Fluctuation
