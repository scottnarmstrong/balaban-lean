module

public import Balaban.LargeField.Base.BaseWitness
public import Balaban.LargeField.Base.BaseGauss
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Gaussian measures `m^w_0` of the witness functions (Lemma II.7.8, block witnesses)

`m^w_0 = ∫ ∏_y g_0(u_y) F^w_0(u) du` is the Gaussian measure of the witness function.  For the
cubes of `P_1` with witness type `blk` the factor `1 - A(□')` forces a Gaussian block of the cube
to leave the ball of radius `2 δ₀`; by the union bound over the `M^d` blocks of the cube and the
independence of the blocks,
```
m^w_0 ≤ (M^d · 2^{N/2} e^{-¼ c (2δ₀)²})^{#{□' ∈ P_1 : w = blk}}        (c = β a L^{d-2}).
```
This is the block-witness factor of the proof of Lemma II.7.8 (P6 (3.4), first factor).  The cubes
with witness type `bd` and the cubes of `Ω^c ∖ P_1` contribute at most `1` to `m^w_0`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal

section MW

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  (a : LocalHistory S n M K) (k : ℕ)

/-- The cubes of `P_{k+1} ∩ Z'` with witness type `blk`. -/
noncomputable def baseBlk (w : BaseW a k) : Finset ↥(basePCubes a k) :=
  open Classical in Finset.univ.filter fun b => w b = true

theorem baseF_le_blk (δ₀ : ℝ) (w : BaseW a k) (u : gaussBlocks a k → EuclideanSpace ℝ (Fin N)) :
    baseF a k δ₀ w u ≤ ∏ b ∈ baseBlk a k w, (1 - baseA a k δ₀ b.1 u) := by
  classical
  unfold baseF baseBlk
  rw [Finset.prod_filter]
  have hO : ∏ c ∈ baseOCubes a k, baseA a k δ₀ c u ≤ 1 :=
    Finset.prod_le_one₀ (fun c _ => (baseA_mem_unit a k δ₀ c u).1)
      fun c _ => (baseA_mem_unit a k δ₀ c u).2
  have hG : (∏ c : ↥(basePCubes a k), if w c then 1 - baseA a k δ₀ c.1 u else baseA a k δ₀ c.1 u) ≤
      ∏ c : ↥(basePCubes a k), if w c = true then 1 - baseA a k δ₀ c.1 u else 1 := by
    refine Finset.prod_le_prod₀ (fun c _ => ?_) fun c _ => ?_
    · have := baseA_mem_unit a k δ₀ c.1 u
      split_ifs <;> linarith
    · have := baseA_mem_unit a k δ₀ c.1 u
      split_ifs <;> linarith
  have hGnn : 0 ≤ ∏ c : ↥(basePCubes a k), if w c = true then 1 - baseA a k δ₀ c.1 u else 1 :=
    Finset.prod_nonneg fun c _ => by
      have := baseA_mem_unit a k δ₀ c.1 u
      split_ifs <;> linarith
  have hOnn : 0 ≤ ∏ c ∈ baseOCubes a k, baseA a k δ₀ c u :=
    Finset.prod_nonneg fun c _ => (baseA_mem_unit a k δ₀ c u).1
  calc _ ≤ (∏ c : ↥(basePCubes a k), if w c = true then 1 - baseA a k δ₀ c.1 u else 1) * 1 :=
        mul_le_mul hG hO hOnn hGnn
    _ = _ := mul_one _

/-- `1 - A(□')` is at most the number of Gaussian blocks of the cube with `|u_y| ≥ 2δ₀`. -/
theorem ofReal_one_sub_baseA_le (δ₀ : ℝ) (b : Torus S.d (n (k + 1)))
    (u : gaussBlocks a k → EuclideanSpace ℝ (Fin N)) :
    ENNReal.ofReal (1 - baseA a k δ₀ b u) ≤
      ∑ y ∈ (open Classical in Finset.univ.filter fun y : gaussBlocks a k =>
        blockCube S n M K (k + 1) y.1 = b), tailInd N (2 * δ₀) (u y) := by
  classical
  by_cases h : BaseBlockProp a k δ₀ u b
  · have : baseA a k δ₀ b u = 1 := charFn_eq_one h
    rw [this, sub_self, ENNReal.ofReal_zero]
    exact zero_le
  · have h0 : baseA a k δ₀ b u = 0 := charFn_eq_zero h
    rw [h0, sub_zero, ENNReal.ofReal_one]
    unfold BaseBlockProp at h
    push Not at h
    obtain ⟨y, hy, hyn⟩ := h
    calc (1 : ℝ≥0∞) = tailInd N (2 * δ₀) (u y) := by
          unfold tailInd; simp [hyn]
      _ ≤ _ := by
          refine Finset.single_le_sum (f := fun y => tailInd N (2 * δ₀) (u y)) (fun _ _ => zero_le)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)

/-- The number of `(k+1)`-blocks of a cube is `M^d`. -/
theorem card_blocks_cube (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hK : k + 1 ≤ K)
    (b : Torus S.d (n (k + 1))) :
    (open Classical in (Finset.univ.filter fun y : BlockAt S n M K (k + 1) =>
      blockCube S n M K (k + 1) y = b)).card = M ^ S.d := by
  classical
  have hℓ : M * n K * S.L ^ (K - (k + 1)) = M * n (k + 1) := by
    rw [nn_eq_pow' hnn hK]; ring
  have := card_blockFibre (d := S.d) (ℓ := M * n K * S.L ^ (K - (k + 1))) (N := M)
    (m := n (k + 1)) hℓ b
  rw [← this]
  unfold blockFibre blockCube
  rfl

/-- **The Gaussian measure of the witness function** (Lemma II.7.8, block witnesses):
`m^w_0 ≤ (M^d · q)^{#blk(w)}`, `q = 2^{N/2} e^{-c (2δ₀)²/4}`. -/
theorem mWit_baseF_le [NeZero N] (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hK : k + 1 ≤ K) {c : ℝ}
    (hc : 0 < c) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (w : BaseW a k) :
    mWit N c a k (baseF a k δ₀) w ≤
      ((M : ℝ≥0∞) ^ S.d * tailQ N c (2 * δ₀)) ^ (baseBlk a k w).card := by
  classical
  unfold mWit
  let _ : Fintype ↥(gaussBlocks a k) := Fintype.ofFinite _
  set Cw : Finset (Torus S.d (n (k + 1))) := (baseBlk a k w).image Subtype.val with hCw
  have hinj : Function.Injective (Subtype.val : ↥(basePCubes a k) → _) := Subtype.val_injective
  have hCcard : Cw.card = (baseBlk a k w).card := Finset.card_image_of_injective _ hinj
  set col : ↥(gaussBlocks a k) → Torus S.d (n (k + 1)) :=
    fun y => blockCube S n M K (k + 1) y.1 with hcol
  have hpt : ∀ u : ↥(gaussBlocks a k) → EuclideanSpace ℝ (Fin N),
      ENNReal.ofReal (∏ y, gaussT N c (u y) 0) * ENNReal.ofReal (baseF a k δ₀ w u) ≤
        (∏ y, gaussE N c (u y)) *
          ∏ b : ↥Cw, ∑ y ∈ Finset.univ.filter (fun y => col y = b.1), tailInd N (2 * δ₀) (u y) := by
    intro u
    have h1 : ENNReal.ofReal (∏ y, gaussT N c (u y) 0) = ∏ y, gaussE N c (u y) := by
      rw [ENNReal.ofReal_prod_of_nonneg fun y _ => gaussT_nonneg N c hc.le _ _]
      rfl
    rw [h1]
    refine mul_le_mul_right ?_ _
    calc ENNReal.ofReal (baseF a k δ₀ w u)
        ≤ ENNReal.ofReal (∏ b ∈ baseBlk a k w, (1 - baseA a k δ₀ b.1 u)) :=
          ENNReal.ofReal_le_ofReal (baseF_le_blk a k δ₀ w u)
      _ = ∏ b ∈ baseBlk a k w, ENNReal.ofReal (1 - baseA a k δ₀ b.1 u) :=
          ENNReal.ofReal_prod_of_nonneg fun b _ => by
            have := baseA_mem_unit a k δ₀ b.1 u; linarith [this.2]
      _ ≤ ∏ b ∈ baseBlk a k w, ∑ y ∈ Finset.univ.filter (fun y => col y = b.1),
            tailInd N (2 * δ₀) (u y) :=
          Finset.prod_le_prod fun b _ => ofReal_one_sub_baseA_le a k δ₀ b.1 u
      _ = ∏ b : ↥Cw, ∑ y ∈ Finset.univ.filter (fun y => col y = b.1), tailInd N (2 * δ₀) (u y) := by
          rw [Finset.prod_coe_sort Cw
            (fun b => ∑ y ∈ Finset.univ.filter (fun y => col y = b), tailInd N (2 * δ₀) (u y)),
            hCw, Finset.prod_image (fun b _ b' _ h => hinj h)]
  calc _ ≤ ∫⁻ u : ↥(gaussBlocks a k) → EuclideanSpace ℝ (Fin N), (∏ y, gaussE N c (u y)) *
          ∏ b : ↥Cw, ∑ y ∈ Finset.univ.filter (fun y => col y = b.1), tailInd N (2 * δ₀) (u y)
        ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) :=
        lintegral_mono hpt
    _ ≤ (∏ b : ↥Cw, ((Finset.univ.filter (fun y => col y = b.1)).card : ℝ≥0∞)) *
          tailQ N c (2 * δ₀) ^ Cw.card :=
        lintegral_gauss_union_le N hc (by linarith) col Cw
    _ ≤ ((M : ℝ≥0∞) ^ S.d) ^ (baseBlk a k w).card * tailQ N c (2 * δ₀) ^ (baseBlk a k w).card := by
        rw [hCcard]
        gcongr
        calc (∏ b : ↥Cw, ((Finset.univ.filter (fun y => col y = b.1)).card : ℝ≥0∞))
            ≤ ∏ b : ↥Cw, ((M : ℝ≥0∞) ^ S.d) := by
              refine Finset.prod_le_prod fun b _ => ?_
              have hle : (Finset.univ.filter (fun y : ↥(gaussBlocks a k) => col y = b.1)).card ≤
                  (Finset.univ.filter fun y : BlockAt S n M K (k + 1) =>
                    blockCube S n M K (k + 1) y = b.1).card := by
                refine Finset.card_le_card_of_injOn Subtype.val (fun y hy => ?_)
                  (fun y _ y' _ h => Subtype.ext h)
                simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
                  hcol] at hy ⊢
                exact hy
              rw [card_blocks_cube k hnn hK b.1] at hle
              exact_mod_cast hle
          _ = ((M : ℝ≥0∞) ^ S.d) ^ (baseBlk a k w).card := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, hCcard]
    _ = _ := by rw [mul_pow]

end MW

end Balaban.LargeField
