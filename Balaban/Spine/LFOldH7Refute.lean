/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldH7Loc
public import Balaban.Spine.LFOldCluster
public import Balaban.LargeField.Background.CubeUnitBg
public import Balaban.Fluctuation.LocalClassDensityH
public import Balaban.Fluctuation.ClassOldTermInputM

/-!
# The named input `H7MixedDatumLoc` is false as stated (complex rotations of the H7 domain)

`H7MixedDatumLoc` (`Spine/LFOldH7Loc.lean`, OPEN-H7-MIXED for the local pair, reading HS-1′) asks
that for every field of the H7 domain of scale `k + 1` the datum of the local pair lie in
`Ψ̃^c(G′_V; δ_b, δ_b)`, the domain of Theorems I-4b, I-4c used by the coefficient bound
(`norm_oldCoefLoc_le_of_inputs`, with `δ_b ≤ c₇`).  The cube tests `Δ^c_q(□; 1, ε)` of the H7 domain
(Definition II.3.5 (a)) put the lifted datum in the union domain `𝒟(G_q(□))` of Theorem 5.2, whose
complex part may have size up to `c₀ + c₁` (`InUnionDomainC`, `ε ≤ c₀`), and at zero sharp mass
(the scales below `k₀`) no regularity inequality bounds the imaginary part of a constant field:
a complex rotation `R e` of a real unit vector passes every cube test.  Since `2 c₇ < c₀`, its
datum is outside `Ψ̃^c(δ_b, δ_b)`.

* `inUnionDomainC_of_const`, `bgFieldC_of_rotConst`, `regIneq_of_rotConst`,
  `regIneq_of_Ω_one_eq_empty`: a datum equal to `R e` on the data sites (`Rᵀ R = 1`, `e` real
  unit, a real external field) lies in `𝒟(G)` when `|R e - e| < c₀`, its background is the
  constant `R e` with multiplier `0` (`bgFieldC_rot`), and the regularity inequalities hold with
  deviation `0` (zero mass);
* `not_inDomainC_of_im`: a datum with a coordinate of imaginary part `≥ ε + δ` at a data site is
  outside `Ψ̃^c(δ, ε)`;
* `boostMat`, `boostMat_orth`, `boostMat_mulVec_single`: the complex rotation by the imaginary angle
  `i t` in a coordinate plane (`e_{i₀} ↦ cosh t e_{i₀} - i sinh t e_{i₁}`);
* `deltaC_rotConst`, `h7Domain_rotConst`: the constant field `R e` lies in every cube domain
  `Δ^c_q(□; 1, ε)`, `ε > 0`, at zero mass, and in the H7 domain at every set on which the mixed
  cube tests are void;
* `not_h7MixedDatumLoc`: **`H7MixedDatumLoc` is false** for every set `V` whose local set `G′_V`
  has a data site, at zero sharp masses, whenever `2 δ_b ≤ min(1, |z|) sinh t`, `2 sinh t ≤ c₀`;
* `c7_le_bgC0_div_eight`, `not_h7MixedDatumLoc_of_le_c7`: the instance at the constants of its use
  (`δ_b ≤ c₇ ≤ c₀ / 8`, `|z| ≥ 1/2`).

Consequence: at zero sharp masses the hypothesis `H7MixedDatumLoc` of `norm_oldCoefLoc_le_of_inputs`,
`norm_oldMarkLF_le`, `oldClusterLF_spec`, `norm_oldBAt_le`, `norm_oldB_le` fails for every history with
a set `V` and a set `Y_f` as in `not_h7MixedDatumLoc` (for instance `V` one `𝒞_1`-cube of the old
operator set and `Y_f` the fine image of the data sites of `G′_V`, which contains no cube of `𝕋_{i+1}`,
so that the mixed tests are void).  The repair needs a ruling on the complex radius of the H7 domain (`notes/phase1/PLAN-B.md`,
"Obstruction (W1154b, 2026-10-21)").
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Matrix

namespace Balaban.LargeField

section RotConst

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ q ϱ}

/-- A complex orthogonal matrix maps a real unit vector to a vector `w` with `w · w = 1`. -/
theorem sum_mulVec_mul_mulVec_of_orth {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) :
    ∑ i, (R *ᵥ fun j => (e j : ℂ)) i * (R *ᵥ fun j => (e j : ℂ)) i = 1 := by
  have h := rotFld_bilin (ι := Unit) hR (fun p => (e p.2 : ℂ)) (fun p => (e p.2 : ℂ)) ()
  have h1 : ∀ i, rotFld R (fun p : Unit × Fin N => (e p.2 : ℂ)) ((), i) =
      (R *ᵥ fun j => (e j : ℂ)) i := fun i => by simp [rotFld, Matrix.mulVec, dotProduct]
  simp only [h1] at h
  rw [h]
  have : ∑ i, (e i : ℂ) * (e i : ℂ) = ((∑ i, e i ^ 2 : ℝ) : ℂ) := by push_cast; simp [sq]
  rw [this, he]; simp

/-- **A datum equal to a constant `w` with `w · w = 1` on the data sites and to a real constant field
on `Ω₁` lies in the union domain `𝒟(G)`** at zero mass, as soon as `w` is within `c₀` of a real unit
vector `e` (`Ψ̃^c(G; c₁, c₀)` with real part `e`, complex part `w - e`). -/
theorem inUnionDomainC_of_const {D : BgData G N} {w : Fin N → ℂ} {e hr : Fin N → ℝ}
    (hd : 0 < d) (he : ∑ i, e i ^ 2 = 1) (hw : ∑ i, w i * w i = 1)
    (hΨ : ∀ x ∈ dataSites G, D.Ψ x = w) (hh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (hr i : ℂ))
    (hwe : vn (w - fun i => (e i : ℂ)) < bgC0 d L N) :
    InUnionDomainC G (bgC0 d L N) (bgC1 d L N) 0 D := by
  have hc1 := bgC1_pos_of (L := L) (N := N) hd
  have hc10 := bgC1_le_bgC0 d L N hd
  refine ⟨bgC1 d L N, bgC0 d L N, hc1, hc10, le_rfl, le_rfl, by simp; exact sq_nonneg _, ?_⟩
  refine ⟨fun _ i => e i, hr, fun _ => w - fun i => (e i : ℂ), fun _ _ => 0, ?_, ?_, ?_⟩
  · refine
      { layerConst := fun _ _ _ _ _ _ _ => rfl
        r1 := fun _ _ _ => by simp [rn]; exact hc1
        r2 := fun _ _ => by rw [he, sub_self, abs_zero]; exact hc1
        r3 := fun _ _ => by simp; exact pow_pos hc1 2
        r4 := by simp; exact pow_pos hc1 2
        eps_pos := lt_of_lt_of_le hc1 hc10
        layerConst' := fun _ _ _ _ _ _ _ => rfl
        hLayerConst' := fun _ _ _ _ _ _ _ => rfl
        c1 := fun _ _ _ => by rw [sub_self, vn_zero]; exact hc1
        c2a := fun _ _ => by linarith
        c2b := fun _ _ => by
          have : ∑ i, ((e i : ℂ) + (w - fun i => (e i : ℂ)) i) *
              ((e i : ℂ) + (w - fun i => (e i : ℂ)) i) - ∑ i, (e i : ℂ) * (e i : ℂ) = 0 := by
            have h2 : ∑ i, (e i : ℂ) * (e i : ℂ) = 1 := by
              have : ∑ i, (e i : ℂ) * (e i : ℂ) = ((∑ i, e i ^ 2 : ℝ) : ℂ) := by
                push_cast; simp [sq]
              rw [this, he]; simp
            simp only [Pi.sub_apply, add_sub_cancel]
            rw [hw, h2, sub_self]
          rw [this, norm_zero]; exact hc1
        c3a := fun _ _ => by simp; exact div_pos (pow_pos hc1 2) (lt_of_lt_of_le hc1 hc10)
        c3b := fun _ _ => by simp; exact pow_pos hc1 2 }
  · intro x hx i
    rw [hΨ x hx]
    simp
  · intro x hx i
    rw [hh x hx i]
    simp

/-- **The background of a complex rotation of the constant unit datum** (zero mass): if `D` equals
`R e` on the data sites (`Rᵀ R = 1`, `e` a real unit vector), its complex small solution is the
constant field `R e` and its multiplier is `0` (`bgFieldC_rot`, `bgFieldC_constUnitBg`; the field
`h̃` does not enter at zero mass). -/
theorem bgFieldC_of_rotConst {a : ℕ → ℝ} (H : BgHyp d L q ϱ a 0) {R : Matrix (Fin N) (Fin N) ℂ}
    (hR : Rᵀ * R = 1) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) {D : BgData G N}
    (hΨ : ∀ x ∈ dataSites G, D.Ψ x = R *ᵥ fun i => (e i : ℂ)) :
    bgFieldC G a 0 (bgC0 d L N) D = rotFld R (constUnitPhi G e) ∧
      bgMultC G a 0 (bgC0 d L N) D = 0 := by
  have hΨ' : D.Ψ = ((constUnitBg G e).rot R).Ψ := by
    funext x
    by_cases hx : x ∈ dataSites G
    · rw [hΨ x hx]
      show _ = R *ᵥ (constUnitBg G e).Ψ x
      congr 1
      funext i
      rw [constUnitBg_Ψ hx]
    · rw [D.Ψ_zero x hx]
      show _ = R *ᵥ (constUnitBg G e).Ψ x
      rw [(constUnitBg G e).Ψ_zero x hx]
      simp
  obtain ⟨h1, h2⟩ := Balaban.Fluctuation.bgFieldC_eq_of_nu_eq_zero (G := G) (a := a)
    (c₀ := bgC0 d L N) rfl hΨ'
  obtain ⟨h3, h4⟩ := bgFieldC_rot a 0 hR (bgC0 d L N) (constUnitBg G e)
  exact ⟨by rw [h1, h3, bgFieldC_constUnitBg H he], by rw [h2, h4, bgMultC_constUnitBg H he]⟩

/-- The block average of the rotated constant field is the constant on `Ω₁`. -/
theorem blockAvg_rotConst (R : Matrix (Fin N) (Fin N) ℂ) (e : Fin N → ℝ)
    {x : Torus d (N₀ * L ^ q)} (hx : x ∈ G.Ω 1) (i : Fin N) :
    blockAvg G (rotFld R (constUnitPhi G e)) x i = (R *ᵥ fun j => (e j : ℂ)) i := by
  obtain ⟨h1, h2, h3⟩ := G.layerIndex_spec hx
  have hsub := blk_subset_Ω G h1 h2 h3
  have : blockAvg G (rotFld R (constUnitPhi G e)) x i =
      blockMean G (G.layerIndex x) (fun _ => (R *ᵥ fun j => (e j : ℂ)) i) x := by
    unfold blockAvg blockMean
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [svec_of_mem G _ ⟨y, hsub hy⟩ i]
    simp [rotFld, constUnitPhi, Matrix.mulVec, dotProduct]
  rw [this]
  exact blockMean_const G h2 _ x

/-- The extension of the rotated constant field by a datum equal to `R e` on the data sites is `R e`
at every data site. -/
theorem barVec_rotConst (R : Matrix (Fin N) (Fin N) ℂ) (e : Fin N → ℝ) {D : BgData G N}
    (hΨ : ∀ x ∈ dataSites G, D.Ψ x = R *ᵥ fun i => (e i : ℂ)) {y : Torus d (N₀ * L ^ q)}
    (hy : y ∈ dataSites G) :
    barVec G D (rotFld R (constUnitPhi G e)) y = R *ᵥ fun i => (e i : ℂ) := by
  funext i
  unfold barVec barField
  by_cases h : y ∈ G.Ω 1
  · simp [h, rotFld, constUnitPhi, Matrix.mulVec, dotProduct]
  · simp [h, hΨ y hy]

/-- **The regularity inequalities at a complex rotation of the constant unit datum** (zero mass):
`|Ψ - Qφ| = 0` on `T ⊆ Ω₁`, the extension is constant on the data sites, `α = 0`, and the field
test is void at zero mass; so they hold for every tolerance `δ > 0`. -/
theorem regIneq_of_rotConst {a : ℕ → ℝ} (H : BgHyp d L q ϱ a 0) {R : Matrix (Fin N) (Fin N) ℂ}
    (hR : Rᵀ * R = 1) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) {D : BgData G N}
    (hΨ : ∀ x ∈ dataSites G, D.Ψ x = R *ᵥ fun i => (e i : ℂ)) {δ : ℝ} (hδ : 0 < δ)
    {T S : Finset (Torus d (N₀ * L ^ q))} (hT : ∀ x ∈ T, x ∈ G.Ω 1) :
    RegIneq G a 0 D δ T S := by
  obtain ⟨hφ, hα⟩ := bgFieldC_of_rotConst H hR he hΨ
  refine ⟨?_, ?_, ?_⟩
  · rw [hφ]
    intro x hx
    have hxΩ := hT x hx
    unfold blockDev
    have : (fun i => D.Ψ x i - blockAvg G (rotFld R (constUnitPhi G e)) x i) = 0 := by
      funext i
      rw [blockAvg_rotConst R e hxΩ, hΨ x ((mem_dataSites G).2 (Or.inl hxΩ)), sub_self]
      rfl
    rw [this, vn_zero]
    exact hδ
  · rw [hφ, hα]
    intro x _
    have hxΩ := x.2
    have h0 : ∀ y ∈ dataSites G, barVec G D (rotFld R (constUnitPhi G e)) y -
        barVec G D (rotFld R (constUnitPhi G e)) x = 0 := by
      intro y hy
      rw [barVec_rotConst R e hΨ hy, barVec_rotConst R e hΨ ((mem_dataSites G).2 (Or.inl hxΩ)),
        sub_self]
    refine ⟨fun μ' => ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [h0 _ (mem_dataSites_add hxΩ μ'), vn_zero]; simpa using hδ
    · rw [h0 _ (mem_dataSites_sub hxΩ μ'), vn_zero]; simpa using hδ
    · have : barLap G D (rotFld R (constUnitPhi G e)) x = 0 := by
        unfold barLap
        refine Finset.sum_eq_zero fun μ' _ => ?_
        rw [barVec_rotConst R e hΨ (mem_dataSites_add hxΩ μ'),
          barVec_rotConst R e hΨ (mem_dataSites_sub hxΩ μ'),
          barVec_rotConst R e hΨ ((mem_dataSites G).2 (Or.inl hxΩ)), two_nsmul]
        abel
      rw [this, vn_zero]; simpa using hδ
    · simpa using hδ
  · intro hν
    simp at hν

/-- **The regularity inequalities of a generating set with empty `Ω₁`** (the level `0`): the datum
vanishes, so does the block average, and the gradient and field tests are void. -/
theorem regIneq_of_Ω_one_eq_empty (hΩ : G.Ω 1 = ∅) (a : ℕ → ℝ) (μ : ℝ) (D : BgData G N)
    {δ : ℝ} (hδ : 0 < δ) (T S : Finset (Torus d (N₀ * L ^ q))) : RegIneq G a μ D δ T S := by
  have hds : ∀ x, x ∉ dataSites G := fun x hx => by
    rcases (mem_dataSites G).1 hx with h | h
    · rw [hΩ] at h; exact absurd h (Finset.notMem_empty _)
    · obtain ⟨-, y, hy, -⟩ := (mem_collar G).1 h
      rw [hΩ] at hy; exact absurd hy (Finset.notMem_empty _)
  have hΩx : ∀ x : G.Ω 1, False := fun x => by
    have h : (x : Torus d (N₀ * L ^ q)) ∈ G.Ω 1 := x.2
    simp [hΩ] at h
  refine ⟨fun x _ => ?_, fun x => (hΩx x).elim, fun _ x => (hΩx x).elim⟩
  unfold blockDev
  have : (fun i => D.Ψ x i - blockAvg G (bgFieldC G a μ (bgC0 d L N) D) x i) = 0 := by
    funext i
    rw [D.Ψ_zero x (hds x)]
    unfold blockAvg
    rw [Finset.sum_eq_zero fun y _ => svec_of_not_mem G _ (by rw [hΩ]; exact Finset.notMem_empty _) i]
    simp
  rw [this, vn_zero]
  exact hδ

/-- **A datum with a coordinate of large imaginary part at a data site is outside `Ψ̃^c(δ, ε)`**: the
complex part `Ψ'` of any decomposition has that imaginary part, and `|Ψ'| < ε + δ` (P2 (1.12),
(C2)). -/
theorem not_inDomainC_of_im {ν δ ε : ℝ} {D : BgData G N} {x : Torus d (N₀ * L ^ q)}
    (hx : x ∈ dataSites G) {i : Fin N} (him : ε + δ ≤ |(D.Ψ x i).im|) :
    ¬ InDomainC G ν δ ε D := by
  rintro ⟨Ψ, h, Ψ', h', hP, hΨ, -⟩
  have h1 := hP.c2a x hx
  have h2 : (D.Ψ x i).im = (Ψ' x i).im := by rw [hΨ x hx i]; simp
  have h3 : |(Ψ' x i).im| ≤ ‖Ψ' x i‖ := Complex.abs_im_le_norm _
  have h4 := Balaban.Fluctuation.norm_apply_le_vn (Ψ' x) i
  rw [h2] at him
  linarith

end RotConst

section Boost

variable {N : ℕ}

noncomputable def boostCol (i₀ i₁ : Fin N) (c s : ℂ) (j : Fin N) : Fin N → ℂ :=
  if j = i₀ then Pi.single i₀ c + Pi.single i₁ (-(Complex.I * s))
  else if j = i₁ then Pi.single i₀ (Complex.I * s) + Pi.single i₁ c
  else Pi.single j 1

noncomputable def boostMat (i₀ i₁ : Fin N) (c s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => boostCol i₀ i₁ c s j i

theorem boostCol_left (i₀ i₁ : Fin N) (c s : ℂ) :
    boostCol i₀ i₁ c s i₀ = Pi.single i₀ c + Pi.single i₁ (-(Complex.I * s)) := by
  simp [boostCol]

theorem boostCol_right {i₀ i₁ : Fin N} (h : i₀ ≠ i₁) (c s : ℂ) :
    boostCol i₀ i₁ c s i₁ = Pi.single i₀ (Complex.I * s) + Pi.single i₁ c := by
  simp [boostCol, Ne.symm h]

theorem boostCol_other {i₀ i₁ j : Fin N} (h0 : j ≠ i₀) (h1 : j ≠ i₁) (c s : ℂ) :
    boostCol i₀ i₁ c s j = Pi.single j 1 := by
  simp [boostCol, h0, h1]

theorem boostMat_orth {i₀ i₁ : Fin N} (h : i₀ ≠ i₁) {c s : ℂ} (hcs : c * c - s * s = 1) :
    (boostMat i₀ i₁ c s)ᵀ * boostMat i₀ i₁ c s = 1 := by
  ext j l
  have e : ((boostMat i₀ i₁ c s)ᵀ * boostMat i₀ i₁ c s) j l =
      boostCol i₀ i₁ c s j ⬝ᵥ boostCol i₀ i₁ c s l := by
    simp [Matrix.mul_apply, boostMat, dotProduct]
  rw [e, Matrix.one_apply]
  have h' : i₁ ≠ i₀ := Ne.symm h
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  by_cases hj0 : j = i₀
  · subst hj0
    by_cases hl0 : l = j
    · subst hl0
      rw [boostCol_left]
      simp [dotProduct_add, h, h']
      linear_combination hcs + s * s * hI
    · by_cases hl1 : l = i₁
      · subst hl1
        rw [boostCol_left, boostCol_right h]
        simp [dotProduct_add, h, h']
        ring
      · rw [boostCol_left, boostCol_other hl0 hl1]
        simp [hl0, hl1, Ne.symm hl0]
  · by_cases hj1 : j = i₁
    · subst hj1
      by_cases hl0 : l = i₀
      · subst hl0
        rw [boostCol_left, boostCol_right h]
        simp [dotProduct_add, h, h']
        ring
      · by_cases hl1 : l = j
        · subst hl1
          rw [boostCol_right h]
          simp [dotProduct_add, h, h']
          linear_combination hcs + s * s * hI
        · rw [boostCol_right h, boostCol_other hl0 hl1]
          simp [hl0, hl1, Ne.symm hl1]
    · rw [boostCol_other hj0 hj1]
      by_cases hl0 : l = i₀
      · subst hl0
        rw [boostCol_left]
        simp [dotProduct_add, hj0, hj1]
      · by_cases hl1 : l = i₁
        · subst hl1
          rw [boostCol_right h]
          simp [dotProduct_add, hj0, hj1]
        · rw [boostCol_other hl0 hl1]
          simp [Pi.single_apply, eq_comm]

theorem boostMat_mulVec_single (i₀ i₁ : Fin N) (c s : ℂ) :
    boostMat i₀ i₁ c s *ᵥ (fun j => ((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) j : ℂ)) =
      Pi.single i₀ c + Pi.single i₁ (-(Complex.I * s)) := by
  have : (fun j => ((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) j : ℂ)) = Pi.single i₀ 1 := by
    funext j; by_cases hj : j = i₀ <;> simp [hj]
  rw [this]
  funext i
  simp [Matrix.mulVec, dotProduct_single, boostMat, boostCol_left]

end Boost

section Cube

variable {d M1 N₁ L N q c n : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] [NeZero n]

/-- **The constant complex rotation `R e` of a real unit field passes the cube test
`Δ^c_q(□; 1, ε)` at zero mass for every `ε > 0`** (Definition II.3.5 (a)): its lift lies in the union
domain `𝒟(G_q(□))` when `|R e - e| < c₀`, and the regularity inequalities hold with deviation `0`. -/
theorem deltaC_rotConst {a : ℕ → ℝ} (hd : 0 < d) (H : 1 ≤ q → BgHyp d L q (minSep L M1) a 0)
    (hm : N₁ * L ^ (q - q) = c * n) {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1)
    (hwe : vn ((R *ᵥ fun i => (e i : ℂ)) - fun i => (e i : ℂ)) < bgC0 d L N) (hr : Fin N → ℝ)
    {ε : ℝ} (hε : 0 < ε) (y0 : Torus d n) :
    (fun _ => R *ᵥ fun i => (e i : ℂ)) ∈
      DeltaC (M1 := M1) (N₁ := N₁) (L := L) (q := q) a 0 ε (fun i => (hr i : ℂ)) c n y0 := by
  set G := genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0 with hG
  have hΨ : ∀ x ∈ dataSites G,
      (liftSingle G (fun _ => R *ᵥ fun i => (e i : ℂ)) (fun i => (hr i : ℂ))).Ψ x =
        R *ᵥ fun i => (e i : ℂ) := fun x hx => liftSingle_Ψ G _ _ hx
  have hh : ∀ x ∈ G.Ω 1, ∀ i,
      (liftSingle G (fun _ => R *ᵥ fun i => (e i : ℂ)) (fun i => (hr i : ℂ))).h x i = (hr i : ℂ) :=
    fun x hx i => by rw [liftSingle_h G _ _ hx]
  refine ⟨inUnionDomainC_of_const hd he (sum_mulVec_mul_mulVec_of_orth hR he) hΨ hh hwe, ?_⟩
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    exact regIneq_of_Ω_one_eq_empty G.top _ _ _ hε _ _
  · exact regIneq_of_rotConst (H hq) hR he hΨ hε fun x hx =>
      G.Ω_antitone le_rfl hq (by omega) (cubeNbhd_one_subset hm y0 x hx)

end Cube

section H7

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K N : ℕ} [NeZero M] [NeZero S.L]

/-- **The constant complex rotation `R e` of a real unit field lies in the H7 domain** (Definition
II.3.5 (d)) at zero sharp masses, with zero fluctuation field and zero external field, at every set
`X_f` on which the mixed tests (1.36), second kind, are void (no cube of `X_f` of `𝕋_{i+1}` lies in
`Ω^{∼3}_{i+1} ∩ (Ω^c_{i+1})^{∼3}`), when `|R e - e| < c₀`. -/
theorem h7Domain_rotConst (M1 c : ℕ) [NeZero M1] [NeZero c] (hM : M = c * M1)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (a : RegionHistory.LocalHistory S n M K) (k : ℕ) (hkK : k ≤ K)
    (Xf : Set (Torus S.d (M * n K * S.L ^ K))) (aw μs ε ε1 νs : ℕ → ℝ) (hr : Fin N → ℝ)
    (hd : 0 < S.d) (hμ : ∀ j ≤ k, μs j = 0)
    (hBG : ∀ j, 1 ≤ j → j ≤ k → BgHyp S.d S.L j (minSep S.L M1) aw 0)
    (hε : ∀ j ≤ k, 0 < ε j) (hε1 : ∀ j < k, 0 < ε1 j)
    (hnomix : ∀ i, i + 1 ≤ k → ∀ y : Torus S.d (n (i + 1)),
      CubeSub (S := S) (n := n) M K (i + 1) y Xf → y ∈ omegaNb a k 3 (i + 1) →
        y ∉ omegaCNb a 3 (i + 1))
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1)
    (hwe : vn ((R *ᵥ fun i => (e i : ℂ)) - fun i => (e i : ℂ)) < bgC0 S.d S.L N) :
    H7Domain M1 c hM hnn a k hkK Xf aw μs ε ε1 νs (fun i => (hr i : ℂ))
      (fun _ _ => R *ᵥ fun i => (e i : ℂ)) 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hjk y _ _ _
    rw [hμ j hjk]
    exact deltaC_rotConst hd (fun hj => hBG j hj hjk) (by simp) hR he hwe hr (hε j hjk) y
  · intro i hik y hyX hyΩ hyC
    exact absurd hyC (hnomix i hik y hyX hyΩ)
  · intro j hj y _
    simp only [Pi.zero_apply, vn_zero]
    exact hε1 j hj
  · simp

end H7

end Balaban.LargeField

namespace Balaban.RootFSpine

open Balaban.LargeField Balaban.LargeField.Def7 Balaban.Localization Balaban.Fluctuation
  Balaban.LargeField.RegionHistory

section Refute

variable {N : ℕ}

/-- The boost of `e_{i₀}` is within `c₀` of `e_{i₀}` when `0 ≤ t` and `2 sinh t ≤ c₀`. -/
theorem vn_boost_sub_lt {d L : ℕ} [NeZero L] (hd : 0 < d) {i₀ i₁ : Fin N} {t : ℝ} (ht0 : 0 ≤ t)
    (ht : 2 * Real.sinh t ≤ bgC0 d L N) :
    vn ((boostMat i₀ i₁ (Real.cosh t) (Real.sinh t) *ᵥ
        fun i => ((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℂ)) -
      fun i => ((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℂ)) < bgC0 d L N := by
  have hc0 := bgC0_pos d L N hd
  have hc16 := bgC0_le (d := d) (L := L) (N := N)
  have hs0 : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.2 ht0
  have hc1 : 1 ≤ Real.cosh t := Real.one_le_cosh t
  have hcs := Real.cosh_sq_sub_sinh_sq t
  rw [boostMat_mulVec_single]
  have he : (fun i => ((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℂ)) = Pi.single i₀ 1 := by
    funext j; by_cases hj : j = i₀ <;> simp [hj]
  rw [he]
  have hsplit : (Pi.single i₀ (Real.cosh t : ℂ) + Pi.single i₁ (-(Complex.I * Real.sinh t)) -
      Pi.single i₀ (1 : ℂ) : Fin N → ℂ) =
      Pi.single i₀ ((Real.cosh t : ℂ) - 1) + Pi.single i₁ (-(Complex.I * Real.sinh t)) := by
    funext j
    by_cases hj0 : j = i₀
    · subst hj0
      by_cases hj1 : j = i₁
      · subst hj1; simp; ring
      · simp [hj1]
    · simp [hj0]
  have hvs : ∀ (j : Fin N) (x : ℂ), vn (Pi.single j x) = ‖x‖ := by
    intro j x
    rw [vn_eq_sqrt]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp [Real.sqrt_sq (norm_nonneg x)]
  rw [hsplit]
  refine lt_of_le_of_lt (vn_add _ _) ?_
  rw [hvs, hvs]
  have h1 : ‖(Real.cosh t : ℂ) - 1‖ = Real.cosh t - 1 := by
    rw [show (Real.cosh t : ℂ) - 1 = ((Real.cosh t - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have h2 : ‖-(Complex.I * (Real.sinh t : ℂ))‖ = Real.sinh t := by
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs0]
  rw [h1, h2]
  have hcm : Real.cosh t - 1 ≤ Real.sinh t ^ 2 / 2 := by nlinarith
  have hsl : Real.sinh t ≤ 1 / 32 := by linarith
  nlinarith

/-- The datum of the local pair at a constant multiscale field `w` is `w` or `z w` at each data
site (the mixed lift of `ψ_k = w` and `θ = z ψ_{k+1} = z w`). -/
theorem holeStepLoc_D'_const {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}
    {k0 K M : ℕ} [NeZero M] [NeZero S.L] {m₁ : ℕ} (g : Geo S n R M)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (w : Fin N → ℂ) (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ)
    (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {x : Torus S.d ((g.c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))}
    (hx : x ∈ dataSites (holeStepLoc g hnn hM1 H hk hk1 hρ (fun _ _ => w) z h₀ a₁ ν β p₁ δ V).G') :
    (holeStepLoc g hnn hM1 H hk hk1 hρ (fun _ _ => w) z h₀ a₁ ν β p₁ δ V).D'.Ψ x = w ∨
      (holeStepLoc g hnn hM1 H hk hk1 hρ (fun _ _ => w) z h₀ a₁ ν β p₁ δ V).D'.Ψ x =
        fun i => (z : ℂ) * w i := by
  erw [liftMixed_Ψ _ (((holeStepLF g hnn hM1 H hk hk1 hρ (fun _ _ => w) z h₀ a₁ ν β p₁ δ).G'.inter
    (locB g hM1 V)).blockUnion (k + 1) (by omega) le_rfl) subset_rfl _ _ _ hx]
  unfold mixedLift blockLift
  split_ifs
  · right; rfl
  · left; rfl

/-- `cosh² t - sinh² t = 1`, read in `ℂ`. -/
theorem cosh_mul_cosh_sub_sinh_mul_sinh_complex (t : ℝ) :
    (Real.cosh t : ℂ) * Real.cosh t - (Real.sinh t : ℂ) * Real.sinh t = 1 := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    show Real.cosh t * Real.cosh t - Real.sinh t * Real.sinh t = 1 by
      nlinarith [Real.cosh_sq_sub_sinh_sq t], Complex.ofReal_one]

/-- **OPEN-H7-MIXED, the background part (`H7MixedDatumLoc`), is false as stated** (complex
rotations).  At zero sharp masses (the scales below `k₀`), the constant complex rotation
`w = cosh t e_{i₀} - i sinh t e_{i₁}` of a real unit vector lies in the H7 domain of scale `k + 1`
at every set `Y_f` on which the mixed cube tests are void (`h7Domain_rotConst`, for
`2 sinh t ≤ c₀`), with zero fluctuation and external fields; at a data site of the local set
`G′_V` the datum of the local pair is `w` or `z w`, whose `i₁`-th coordinate has imaginary part of
modulus `sinh t` or `|z| sinh t`.  When this is at least `2 δ_b`, the datum is outside
`Ψ̃^c(G′_V; δ_b, δ_b)`, whose complex part has modulus `< 2 δ_b` (`not_inDomainC_of_im`).  Since
`δ_b ≤ c₇ < c₀ / 2` at the use of the named input, such `t` exist. -/
theorem not_h7MixedDatumLoc {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}
    {k0 K M : ℕ} [NeZero M] [NeZero S.L] {m₁ : ℕ} (g : Geo S n R M)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ)
    (aw μs ε ε1 νs : ℕ → ℝ) (hv : EuclideanSpace ℝ (Fin N)) (νb δb : ℝ) (hd : 0 < S.d)
    (hμ : ∀ j ≤ k + 1, μs j = 0)
    (hBG : ∀ j, 1 ≤ j → j ≤ k + 1 → BgHyp S.d S.L j (minSep S.L g.M1) aw 0)
    (hε : ∀ j ≤ k + 1, 0 < ε j) (hε1 : ∀ j < k + 1, 0 < ε1 j)
    (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {x₀ : Torus S.d ((g.c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))}
    (hx₀ : x₀ ∈ dataSites (locG' g hnn hM1 H hk hρ V))
    (Yf : Set (Torus S.d (M * n K * S.L ^ K)))
    (hYf : ∀ x ∈ dataSites (locG' g hnn hM1 H hk hρ V), fineOfC g hnn hM1 hk x ∈ Yf)
    (hnomix : ∀ i, i + 1 ≤ k + 1 → ∀ y : Torus S.d (n (i + 1)),
      CubeSub (S := S) (n := n) M K (i + 1) y Yf →
        y ∈ omegaNb (globalLH H M) (k + 1) 3 (i + 1) → y ∉ omegaCNb (globalLH H M) 3 (i + 1))
    {i₀ i₁ : Fin N} (hi : i₀ ≠ i₁) {t : ℝ} (ht0 : 0 ≤ t) (ht : 2 * Real.sinh t ≤ bgC0 S.d S.L N)
    (hδb : 2 * δb ≤ Real.sinh t) (hz : 2 * δb ≤ |z| * Real.sinh t) :
    ¬ H7MixedDatumLoc g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs (hC hv) νb δb := by
  intro hDat
  have hR := boostMat_orth hi (cosh_mul_cosh_sub_sinh_mul_sinh_complex t)
  have he : ∑ i, (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i ^ 2 = 1 := by
    rw [Finset.sum_eq_single i₀ (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have hdom := h7Domain_rotConst g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs
    (fun i => hv i) hd hμ hBG hε hε1 hnomix hR he (vn_boost_sub_lt hd ht0 ht)
  have hin := hDat V Yf (fun _ _ => boostMat i₀ i₁ (Real.cosh t) (Real.sinh t) *ᵥ
    fun i => ((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℂ)) 0 0 hdom hYf
  have hw : (boostMat i₀ i₁ (Real.cosh t) (Real.sinh t) *ᵥ
      fun i => ((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℂ)) i₁ = -(Complex.I * Real.sinh t) := by
    rw [boostMat_mulVec_single]
    simp [Ne.symm hi]
  have hs0 : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.2 ht0
  have him : (-(Complex.I * (Real.sinh t : ℂ))).im = -Real.sinh t := by
    simp only [Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, zero_add]
  rcases holeStepLoc_D'_const g hnn hM1 H hk hk1 hρ _ z h₀ a₁ ν β p₁ δ V hx₀ with hD | hD
  · refine not_inDomainC_of_im hx₀ (i := i₁) ?_ hin
    rw [hD, hw, him, abs_neg, abs_of_nonneg hs0]
    linarith
  · refine not_inDomainC_of_im hx₀ (i := i₁) ?_ hin
    rw [hD]
    show δb + δb ≤ |((z : ℂ) * _).im|
    rw [hw, Complex.im_ofReal_mul, him, abs_mul, abs_neg, abs_of_nonneg hs0]
    linarith

/-- `c₇ ≤ c₀ / 8`: the smallness of `δ` in Theorem I-4b is far below the complex radius `c₀` of the
data domain of Theorem 5.2 (`c₇ ≤ c₀ / (2 (K₂' C₃ + 1))`, `K₂' ≥ c_F ≥ 3`, `C₃ ≥ 500`). -/
theorem c7_le_bgC0_div_eight {d L : ℕ} [NeZero L] {BG κ : ℝ} (hBG : 0 ≤ BG) (hd : 0 < d) :
    c7 d L N BG κ ≤ bgC0 d L N / 8 := by
  have hc0 := bgC0_pos d L N hd
  have hB := famConst_ge_one (L := L) hBG κ hd
  have hN := cN'_pos (d := d) (L := L) (N := N) (B := famConst d L BG κ) (by linarith)
  have hF : 3 ≤ cF d L := by
    unfold cF
    have : (0 : ℝ) ≤ 2 * d * (L : ℝ) ^ 2 := by positivity
    linarith
  have hC : 500 ≤ lemma53Const d L := by
    have := cB7_le_const d L; have := cB7_pos d L; linarith
  have hK : 3 ≤ cK2' d L N (famConst d L BG κ) := by
    unfold cK2'
    nlinarith
  have hle : c7 d L N BG κ ≤
      bgC0 d L N / (2 * (cK2' d L N (famConst d L BG κ) * lemma53Const d L + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  refine hle.trans ?_
  have hX : (3 : ℝ) * 500 ≤ cK2' d L N (famConst d L BG κ) * lemma53Const d L :=
    mul_le_mul hK hC (by norm_num) (by linarith)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **`H7MixedDatumLoc` is false at the constants of its use** (`norm_oldCoefLoc_le_of_inputs`:
`δ_b ≤ c₇`, `0 ≤ BG`), for a field renormalization `|z| ≥ 1/2`: the instance of
`not_h7MixedDatumLoc` with `sinh t = c₀ / 2`. -/
theorem not_h7MixedDatumLoc_of_le_c7 {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}
    {k0 K M : ℕ} [NeZero M] [NeZero S.L] {m₁ : ℕ} (g : Geo S n R M)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ)
    (aw μs ε ε1 νs : ℕ → ℝ) (hv : EuclideanSpace ℝ (Fin N)) (νb δb : ℝ) (hd : 0 < S.d)
    (hμ : ∀ j ≤ k + 1, μs j = 0)
    (hBG : ∀ j, 1 ≤ j → j ≤ k + 1 → BgHyp S.d S.L j (minSep S.L g.M1) aw 0)
    (hε : ∀ j ≤ k + 1, 0 < ε j) (hε1 : ∀ j < k + 1, 0 < ε1 j)
    (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {x₀ : Torus S.d ((g.c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))}
    (hx₀ : x₀ ∈ dataSites (locG' g hnn hM1 H hk hρ V))
    (Yf : Set (Torus S.d (M * n K * S.L ^ K)))
    (hYf : ∀ x ∈ dataSites (locG' g hnn hM1 H hk hρ V), fineOfC g hnn hM1 hk x ∈ Yf)
    (hnomix : ∀ i, i + 1 ≤ k + 1 → ∀ y : Torus S.d (n (i + 1)),
      CubeSub (S := S) (n := n) M K (i + 1) y Yf →
        y ∈ omegaNb (globalLH H M) (k + 1) 3 (i + 1) → y ∉ omegaCNb (globalLH H M) 3 (i + 1))
    {i₀ i₁ : Fin N} (hi : i₀ ≠ i₁) {BG κ : ℝ} (hBG0 : 0 ≤ BG) (hδ : δb ≤ c7 S.d S.L N BG κ)
    (hz : 1 / 2 ≤ |z|) :
    ¬ H7MixedDatumLoc g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs (hC hv) νb δb := by
  have hc0 := bgC0_pos S.d S.L N hd
  have h8 := c7_le_bgC0_div_eight (N := N) (L := S.L) (κ := κ) hBG0 hd
  have hs : Real.sinh (Real.arsinh (bgC0 S.d S.L N / 2)) = bgC0 S.d S.L N / 2 := Real.sinh_arsinh _
  refine not_h7MixedDatumLoc g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs hv νb δb hd hμ hBG
    hε hε1 V hx₀ Yf hYf hnomix hi (t := Real.arsinh (bgC0 S.d S.L N / 2))
    (Real.arsinh_nonneg_iff.2 (by positivity)) (by rw [hs]; linarith)
    (by rw [hs]; linarith) ?_
  rw [hs]
  nlinarith

end Refute

end Balaban.RootFSpine
