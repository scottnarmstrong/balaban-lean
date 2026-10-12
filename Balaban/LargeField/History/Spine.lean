module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Spines (Part I, Definition I.4.5) and the separation estimate behind Lemma V

A *spine* is a finite, nonempty set of segments of `ℝ^d` (here the lift of the spine to `ℝ^d`)
whose union is connected.  Its length is the sum of the Euclidean lengths of the segments.

The main result is `Spine.sep_card_le`: a family of points of a spine with pairwise sup-distances
`> ρ` has at most `2 ℓ / ρ + 1` elements (the "separated points" step of Lemma I.5.1).
-/

@[expose] public section

open MeasureTheory Set

namespace Balaban.LargeField

/-- The Euclidean length of the segment `[a, b]`. -/
noncomputable def segLen {d : ℕ} (a b : Fin d → ℝ) : ℝ := Real.sqrt (∑ i, (b i - a i) ^ 2)

theorem segLen_nonneg {d : ℕ} (a b : Fin d → ℝ) : 0 ≤ segLen a b := Real.sqrt_nonneg _

/-- The sup-norm is at most the Euclidean norm. -/
theorem norm_le_segLen {d : ℕ} (a b : Fin d → ℝ) : ‖b - a‖ ≤ segLen a b := by
  rw [pi_norm_le_iff_of_nonneg (segLen_nonneg a b)]
  intro i
  rw [Real.norm_eq_abs, Pi.sub_apply]
  unfold segLen
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun i => (b i - a i) ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

/-- A spine (lift to `ℝ^d`): finitely many segments with connected union. -/
structure Spine (d : ℕ) where
  /-- the segments, as pairs of endpoints -/
  segs : Finset ((Fin d → ℝ) × (Fin d → ℝ))
  nonempty : segs.Nonempty
  /-- the union of the segments is connected -/
  conn : IsPreconnected (⋃ s ∈ segs, segment ℝ s.1 s.2)

namespace Spine

variable {d : ℕ} (sp : Spine d)

/-- The union of the segments. -/
def carrier : Set (Fin d → ℝ) := ⋃ s ∈ sp.segs, segment ℝ s.1 s.2

/-- The length `ℓ(Γ)`: the sum of the Euclidean lengths of the segments. -/
noncomputable def length : ℝ := ∑ s ∈ sp.segs, segLen s.1 s.2

theorem length_nonneg : 0 ≤ sp.length := Finset.sum_nonneg (fun s _ => segLen_nonneg _ _)

theorem mem_carrier {y : Fin d → ℝ} : y ∈ sp.carrier ↔ ∃ s ∈ sp.segs, y ∈ segment ℝ s.1 s.2 := by
  unfold carrier; simp

theorem isPreconnected_carrier : IsPreconnected sp.carrier := sp.conn

end Spine

section Sep

variable {d : ℕ}

/-- The point `a + t (b - a)` of the segment `[a, b]`. -/
def segPt (s : (Fin d → ℝ) × (Fin d → ℝ)) (t : ℝ) : Fin d → ℝ := s.1 + t • (s.2 - s.1)

theorem continuous_segPt (s : (Fin d → ℝ) × (Fin d → ℝ)) : Continuous (segPt s) := by
  unfold segPt; fun_prop

theorem segPt_sub (s : (Fin d → ℝ) × (Fin d → ℝ)) (t t' : ℝ) :
    segPt s t - segPt s t' = (t - t') • (s.2 - s.1) := by
  unfold segPt; simp only [sub_smul]; abel

theorem mem_segment_iff (s : (Fin d → ℝ) × (Fin d → ℝ)) (y : Fin d → ℝ) :
    y ∈ segment ℝ s.1 s.2 ↔ ∃ t ∈ Icc (0 : ℝ) 1, segPt s t = y := by
  rw [segment_eq_image']; rfl

/-- The function `t ↦ ‖γ_s(t) - p‖` is `ℓ(s)`-Lipschitz. -/
theorem lipschitz_dist (s : (Fin d → ℝ) × (Fin d → ℝ)) (p : Fin d → ℝ) :
    LipschitzWith (segLen s.1 s.2).toNNReal (fun t => ‖segPt s t - p‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro t t'
  rw [Real.dist_eq, Real.dist_eq]
  have hK : (((segLen s.1 s.2).toNNReal : NNReal) : ℝ) = segLen s.1 s.2 :=
    Real.coe_toNNReal _ (segLen_nonneg _ _)
  rw [hK]
  have h1 : |‖segPt s t - p‖ - ‖segPt s t' - p‖| ≤ ‖segPt s t - segPt s t'‖ := by
    have := abs_norm_sub_norm_le (segPt s t - p) (segPt s t' - p)
    simpa using this
  have h2 : ‖segPt s t - segPt s t'‖ ≤ |t - t'| * segLen s.1 s.2 := by
    rw [segPt_sub, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_le_segLen _ _) (abs_nonneg _)
  linarith [mul_comm (segLen s.1 s.2) |t - t'|]

end Sep

variable {d : ℕ}

namespace Spine

variable (sp : Spine d)

/-- A family of points of a spine with pairwise sup-distances `> ρ` has at most
`2 ℓ / ρ + 1` elements (the separated-points step of Lemma I.5.1). -/
theorem sep_card_le {ρ : ℝ} (hρ : 0 < ρ) (P : Finset (Fin d → ℝ))
    (hP : ∀ p ∈ P, p ∈ sp.carrier) (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ρ < ‖p - q‖) :
    (P.card : ℝ) * (ρ / 2) ≤ sp.length + ρ / 2 := by
  classical
  by_cases hn : P.card ≤ 1
  · have : (P.card : ℝ) ≤ 1 := by exact_mod_cast hn
    nlinarith [sp.length_nonneg]
  have hn2 : 2 ≤ P.card := by omega
  suffices h : (P.card : ℝ) * (ρ / 2) ≤ sp.length by linarith [hρ]
  -- the pieces `J s p` of the segment `s` inside the ball of radius `ρ/2` around `p`
  set J : (Fin d → ℝ) × (Fin d → ℝ) → (Fin d → ℝ) → Set ℝ :=
    fun s p => Icc (0 : ℝ) 1 ∩ {t | ‖segPt s t - p‖ ≤ ρ / 2} with hJ
  have hJmeas : ∀ s p, MeasurableSet (J s p) := fun s p =>
    (isClosed_Icc.inter (isClosed_le ((continuous_segPt s).sub continuous_const).norm
      continuous_const)).measurableSet
  have hJdisj : ∀ s, (P : Set (Fin d → ℝ)).PairwiseDisjoint (J s) := by
    intro s p hp q hq hpq
    rw [Function.onFun, Set.disjoint_left]
    rintro t ⟨-, ht1⟩ ⟨-, ht2⟩
    have h1 : ‖p - q‖ ≤ ρ := by
      have : p - q = (segPt s t - q) - (segPt s t - p) := by abel
      rw [this]
      calc ‖(segPt s t - q) - (segPt s t - p)‖ ≤ ‖segPt s t - q‖ + ‖segPt s t - p‖ :=
            norm_sub_le _ _
        _ ≤ ρ := by simp only [Set.mem_ofPred_eq] at ht1 ht2; linarith
    exact absurd (hsep p hp q hq hpq) (not_lt.mpr h1)
  have hJsum : ∀ s, ∑ p ∈ P, volume (J s p) ≤ 1 := by
    intro s
    rw [← measure_biUnion_finset (hJdisj s) (fun p _ => hJmeas s p)]
    calc volume (⋃ p ∈ P, J s p) ≤ volume (Icc (0 : ℝ) 1) := by
          apply measure_mono
          intro t ht
          simp only [Set.mem_iUnion] at ht
          obtain ⟨p, -, hp⟩ := ht
          exact hp.1
      _ = 1 := by simp
  -- every value in `[0, ρ/2]` is the distance to `p` of a point of a segment inside the ball
  have hcover : ∀ p ∈ P, Icc (0 : ℝ) (ρ / 2) ⊆
      ⋃ s ∈ sp.segs, (fun t => ‖segPt s t - p‖) '' J s p := by
    intro p hp u hu
    obtain ⟨q, hq, hqp⟩ : ∃ q ∈ P, q ≠ p := by
      by_contra hcon
      push Not at hcon
      have : P.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
        rw [hcon a ha, hcon b hb])
      omega
    have hconn : IsPreconnected ((fun y => ‖y - p‖) '' sp.carrier) :=
      sp.isPreconnected_carrier.image _ ((continuous_id.sub continuous_const).norm.continuousOn)
    have h0 : (0 : ℝ) ∈ (fun y => ‖y - p‖) '' sp.carrier := ⟨p, hP p hp, by simp⟩
    have hqd : ρ < ‖q - p‖ := hsep q hq p hp hqp
    have h1 : ‖q - p‖ ∈ (fun y => ‖y - p‖) '' sp.carrier := ⟨q, hP q hq, rfl⟩
    have := hconn.Icc_subset h0 h1 ⟨hu.1, by linarith [hu.2]⟩
    obtain ⟨y, hy, hyu⟩ := this
    obtain ⟨s, hs, hys⟩ := (sp.mem_carrier).mp hy
    obtain ⟨t, ht, hty⟩ := (mem_segment_iff s y).mp hys
    simp only [Set.mem_iUnion]
    refine ⟨s, hs, t, ⟨ht, ?_⟩, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      rw [hty]; simp only at hyu; rw [hyu]; exact hu.2
    · simp only; rw [hty]; exact hyu
  -- the measure estimate
  have hLip : ∀ s p, volume ((fun t => ‖segPt s t - p‖) '' J s p) ≤
      ENNReal.ofReal (segLen s.1 s.2) * volume (J s p) := by
    intro s p
    have h := ((lipschitz_dist s p).lipschitzOnWith (s := J s p)).hausdorffMeasure_image_le
      (d := 1) zero_le_one
    rw [MeasureTheory.hausdorffMeasure_real, ENNReal.rpow_one] at h
    exact h
  have hper : ∀ p ∈ P, ENNReal.ofReal (ρ / 2) ≤
      ∑ s ∈ sp.segs, ENNReal.ofReal (segLen s.1 s.2) * volume (J s p) := by
    intro p hp
    calc ENNReal.ofReal (ρ / 2) = volume (Icc (0 : ℝ) (ρ / 2)) := by simp
      _ ≤ volume (⋃ s ∈ sp.segs, (fun t => ‖segPt s t - p‖) '' J s p) :=
          measure_mono (hcover p hp)
      _ ≤ ∑ s ∈ sp.segs, volume ((fun t => ‖segPt s t - p‖) '' J s p) :=
          measure_biUnion_finset_le _ _
      _ ≤ _ := Finset.sum_le_sum (fun s _ => hLip s p)
  -- sum over `p`
  have htot : (P.card : ENNReal) * ENNReal.ofReal (ρ / 2) ≤ ENNReal.ofReal sp.length := by
    calc (P.card : ENNReal) * ENNReal.ofReal (ρ / 2) = ∑ p ∈ P, ENNReal.ofReal (ρ / 2) := by simp
      _ ≤ ∑ p ∈ P, ∑ s ∈ sp.segs, ENNReal.ofReal (segLen s.1 s.2) * volume (J s p) :=
          Finset.sum_le_sum hper
      _ = ∑ s ∈ sp.segs, ENNReal.ofReal (segLen s.1 s.2) * ∑ p ∈ P, volume (J s p) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro s _; rw [Finset.mul_sum]
      _ ≤ ∑ s ∈ sp.segs, ENNReal.ofReal (segLen s.1 s.2) * 1 :=
          Finset.sum_le_sum (fun s _ => mul_le_mul' le_rfl (hJsum s))
      _ = ENNReal.ofReal sp.length := by
          simp only [mul_one]
          unfold Spine.length
          rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => segLen_nonneg _ _)]
  have : ENNReal.ofReal ((P.card : ℝ) * (ρ / 2)) ≤ ENNReal.ofReal sp.length := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    exact htot
  exact (ENNReal.ofReal_le_ofReal_iff sp.length_nonneg).mp this

end Spine

end Balaban.LargeField
