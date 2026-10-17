/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerEnergyCells
public import Balaban.Inhabited.StepIdentityFibreExplicitCore

/-!
# Auxiliary facts for the tower's new terms on two tori (blocker 7)

* `gsumCoeff_commonLabels_congr`, `towerLab_margin` (moved here from
  `TwoTorusGapTowerEnergy.lean`, statements unchanged): the interpolation coefficient on the common
  labels depends only on the label system; the label margin of a compact support.
* `sum_exp_obsRemLab_le`: the weighted sum over the remainder labels of the observable coefficient
  is at most `a (K₀ + 1)` when every domain contains the root cube (the entropy bound
  `entropy_thick`; the dummy label has size `≥ 0`).
* `rootCube_mem_obsRowLabel_obsDomains`: for the local cover of a site `y`, every domain of the
  observable expansion contains the root cube of the block of `y`.
* `card_le_card_of_sitesOf_cells`: a set `Cs` of `π_j`-cubes whose sites are the cells of the image
  `X` of a set of cells of the coarse torus has at least `|X|` cubes.
* `exp_neg_dExt_le_card`: `e^{-κ dExt C} ≤ e^{κ} e^{-(κ / c₁) n}` for `n ≤ |C|` (from (G1),
  `card_le_dExt`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep

section Congr

/-- **The interpolation coefficient on the common labels depends only on the label system.**  If the
label types, the label systems, the amplitudes and the activities agree (`HEq`), the coefficients
with the bridge anchors of the root `z` and the marks `G` agree. -/
theorem gsumCoeff_commonLabels_congr {d L N₁ m₁ K m₀ : ℕ} [NeZero N₁] [NeZero L] {β : Type*}
    [Fintype β]
    {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ → Type*}
    [∀ b, MeasurableSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {E : Type*} {Lb Lb' : Type} [hLb : Fintype Lb] [hLb' : Fintype Lb'] (h : Lb = Lb')
    {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ Lb}
    {Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ Lb'}
    (hLab : HEq Lab Lab') (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y)
    {εH εH' κH κ0 Kc : ℝ} (hε : εH = εH')
    {A : E → ℂ → LabelAct (commonLabels Lab hN hL reads dom hdom) Ωb εH κH κ0 Kc}
    {A' : E → ℂ → LabelAct (commonLabels Lab' hN hL reads dom hdom) Ωb εH' κH κ0 Kc}
    (hA : HEq A A') (θ : E) (z : RootIdx d L N₁ m₁ K)
    (G : {Y' // Y' ∈ bridgeFamily m₀ reads dom z} → ℂ → (∀ b, Ωb b) → ℂ)
    (C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) :
    gsumCoeff μ (commonLabels Lab hN hL reads dom hdom) (A θ)
        (fun i => commonAnchor Lb reads dom z i) G C =
      gsumCoeff μ (commonLabels Lab' hN hL reads dom hdom) (A' θ)
        (fun i => commonAnchor Lb' reads dom z i) G C := by
  subst h hε
  obtain rfl : hLb = hLb' := Subsingleton.elim _ _
  obtain rfl := eq_of_heq hLab
  obtain rfl := eq_of_heq hA
  rfl

end Congr

section Margin

/-- **The label margin of a compact support.**  For `36 ≤ K`, `Dc ≤ (K - 36) / 25`,
`L ≤ (K - 26) / 25 + 1`, `4 L^(k+1) ≤ a_K` and `Ds = a_K (Dc + 1) - 1`, the label margin of
`mem_obsLabelDomains_recentred_iff` at the radius `Ds + (Ds + 1) / 4 + 2 L^(k+1)` holds below
`a_K K`. -/
theorem towerLab_margin {L aK K Dc Ds Lk : ℕ} (hK : 36 ≤ K) (hD : Dc ≤ (K - 36) / 25)
    (hKL : L ≤ (K - 26) / 25 + 1) (ha : 0 < aK) (h4 : 4 * Lk ≤ aK) (hDs : Ds = aK * (Dc + 1) - 1) :
    2 * ((Ds + (Ds + 1) / 4 + 2 * Lk) + 2 * ((L - 1) * aK + L * aK)) + 5 * (L * aK) < aK * K := by
  have h1 : Ds + 1 ≤ aK * (Dc + 1) := by
    have : 1 ≤ aK * (Dc + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have h2 : (L - 1) * aK ≤ L * aK := Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  have h3 : L * aK ≤ aK * ((K - 26) / 25 + 1) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hKL
  have h5 : 4 * (Dc + 1) + 2 + 13 * ((K - 26) / 25 + 1) < K := by omega
  have h6 : aK * (4 * (Dc + 1) + 2 + 13 * ((K - 26) / 25 + 1)) < aK * K :=
    Nat.mul_lt_mul_of_pos_left h5 ha
  have h7 : aK * (4 * (Dc + 1) + 2 + 13 * ((K - 26) / 25 + 1)) =
      4 * (aK * (Dc + 1)) + 2 * aK + 13 * (aK * ((K - 26) / 25 + 1)) := by ring
  omega

end Margin

section Entropy

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L]

/-- **The weighted sum over the remainder labels.**  If every domain of `𝒴` contains the cube `bx`
and `κ₀ ≥ a_ent + 1`, then `∑_r a e^{-κ₀ 𝗱(y_r)} ≤ a (K₀ + 1)` over the remainder labels `y_r`
(the domains of `𝒴`, of size `d^cov`, and the dummy label of the root cube). -/
theorem sum_exp_obsRemLab_le {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {Lb₀ : Type}
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ
      Lb₀)
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))) (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ)
    (hbx : ∀ Y ∈ 𝒴, bx ∈ obsRowLabel m₀ (k + 1) Y) {κ0 : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0)
    {a : ℝ} (ha : 0 ≤ a) :
    ∑ r, a * Real.exp (-κ0 * (obsLab Lab₀ hdj).dl
      (obsRemLab 𝒴 (fun Y => Sum.inl (Sum.inr Y)) (obsY0 m₀ Lb₀ 𝒴 bx) r)) ≤
      a * (K0 d L κ0 + 1) := by
  rw [Fintype.sum_option]
  have hκ00 : 0 ≤ κ0 := by linarith [aEnt_nonneg d L]
  have h1 : Real.exp (-κ0 * (obsLab Lab₀ hdj).dl (obsY0 m₀ Lb₀ 𝒴 bx)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [(obsLab Lab₀ hdj).dl_nonneg (obsY0 m₀ Lb₀ 𝒴 bx)]
  have hK := entropy_thick hN le_rfl 𝒴 hdj hκ0 bx
  have h2 : ∑ Y : {Y // Y ∈ 𝒴}, Real.exp (-κ0 * treeLenCovOne m₀ (k + 1) Y.1) ≤ K0 d L κ0 := by
    refine le_trans (le_of_eq ?_) hK
    refine Finset.sum_congr rfl fun Y _ => ?_
    simp [mem_blocksOf.1 (hbx Y.1 Y.2)]
  have h3 : ∀ Y : {Y // Y ∈ 𝒴}, (obsLab Lab₀ hdj).dl
      (obsRemLab 𝒴 (fun Y => Sum.inl (Sum.inr Y)) (obsY0 m₀ Lb₀ 𝒴 bx) (some Y)) =
      treeLenCovOne m₀ (k + 1) Y.1 := fun _ => rfl
  simp only [h3]
  have h4 : obsRemLab 𝒴 (fun Y => Sum.inl (Sum.inr Y)) (obsY0 m₀ Lb₀ 𝒴 bx) none =
      obsY0 m₀ Lb₀ 𝒴 bx := rfl
  rw [h4, ← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 ha]

/-- **The domains of the local cover of a site contain the root cube of its block.**  For the cover
data of the site `y` (cover setup of the cube of `y`, `X₁ = nbhd y`, the optimal tree, and
`y ∈ nbhd y`) every domain of the observable expansion contains `rootCube (blockIndex y)`. -/
theorem rootCube_mem_obsRowLabel_obsDomains {N : ℕ} {ϱ : ℝ} (S : StepSetting d L N₁ m₁ k N ϱ)
    (hd : 3 ≤ d) (hN : L ^ 1 ∣ N₁) (y : CTorus d L N₁ m₁ (k + 1))
    (hcs : CovSetup S.G' 1 k (LocalCover.cube 1 k y) (LocalCover.fam 1 y))
    (hX₁ : (↑(LocalCover.nbhdF 1 y) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' 1 k (LocalCover.fam 1 y))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ LocalCover.cube 1 k y) ∧ MeetsOne 1 k (LocalCover.fam 1 y) W₀ ∧
        bondCost (scaleW L 1 m₁ k) E₀ = treeLenCovOne 1 k (LocalCover.cube 1 k y))
    (hy : y ∈ LocalCover.nbhdF 1 y) :
    ∀ Y ∈ obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y),
      rootCube (m₀ := 1) (blockIndex y) ∈ obsRowLabel 1 (k + 1) Y := by
  intro Y hY
  have hx : y ∈ X1 S.G' 1 k (LocalCover.fam 1 y) := by
    rw [← hX₁]; exact Finset.mem_coe.2 hy
  exact rootCube_mem_obsRowLabel_of_polymerDomains
    (fun i : ParIdx S.G' (↑(LocalCover.nbhdF 1 y) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
    hN S.hG' hcs hd (fun i => i.1.2) hopt rfl hY hx

end Entropy

section Size

variable {d L N₁ m₁ Kc : ℕ} [NeZero N₁] [NeZero L]

/-- **Cubes of the cells of a support.**  Let the torus have `K` cells of side `a = cellSide L m₀ m₁ j`
per direction, `X` the image (centred coordinates) of a set `Y` of cells, and `Cs` a set of
`π_j`-cubes whose sites are the sites of the cells of `X`.  Then `|X| ≤ |Cs|`: the cell `b` gives the
cube based at `a b`. -/
theorem card_le_card_of_sitesOf_cells {m₀ j K : ℕ} [NeZero K]
    (hn : (N₁ * L ^ m₁) * L ^ Kc = cellSide L m₀ m₁ j * K)
    (Cs : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := Kc) m₀ j Set.univ))
    (Y : Finset (Balaban.Torus d K))
    (hs : sitesOf Cs = {x : CTorus d L N₁ m₁ Kc |
      (fun μ => (((((x μ).val / cellSide L m₀ m₁ j : ℕ)) : ZMod K)).valMinAbs) ∈
        (↑(Y.image (fun b μ => (b μ).valMinAbs)) : Set (Fin d → ℤ))}) :
    (Y.image (fun b μ => (b μ).valMinAbs)).card ≤ Cs.card := by
  refine Finset.card_image_le.trans ?_
  have ha : 0 < cellSide L m₀ m₁ j := cellSide_pos m₀ m₁ j
  have hdvd : cellSide L m₀ m₁ j ∣ (N₁ * L ^ m₁) * L ^ Kc := ⟨K, hn⟩
  have hval : ∀ (b : Balaban.Torus d K) μ,
      (((cellSide L m₀ m₁ j * (b μ).val : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ Kc))).val =
        cellSide L m₀ m₁ j * (b μ).val := by
    intro b μ
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    rw [hn]
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) ha
  have hal : ∀ b : Balaban.Torus d K, Aligned (cellSide L m₀ m₁ j)
      (fun μ => (((cellSide L m₀ m₁ j * (b μ).val : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ Kc))) :
        CTorus d L N₁ m₁ Kc) := fun b μ => by
    rw [hval]; exact Nat.mul_mod_right _ _
  refine Finset.card_le_card_of_injOn (fun b => ⟨_, hal b, Set.subset_univ _⟩)
    (fun b hb => ?_) (fun b _ b' _ h => ?_)
  · have hmem : (fun μ => (((cellSide L m₀ m₁ j * (b μ).val : ℕ) :
        ZMod ((N₁ * L ^ m₁) * L ^ Kc))) : CTorus d L N₁ m₁ Kc) ∈ sitesOf Cs := by
      rw [hs]
      have hc : (fun μ => ((((((((cellSide L m₀ m₁ j * (b μ).val : ℕ) :
          ZMod ((N₁ * L ^ m₁) * L ^ Kc))).val / cellSide L m₀ m₁ j : ℕ)) : ZMod K)).valMinAbs)) =
          fun μ => (b μ).valMinAbs := by
        funext μ
        rw [hval, Nat.mul_div_cancel_left _ ha, ZMod.natCast_zmod_val]
      simp only [Set.mem_ofPred_eq]
      rw [hc]
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hb))
    obtain ⟨c, hc, hsc⟩ := mem_sitesOf.1 hmem
    have h1 := cbase_eq_of_mem_box hdvd c.2.1 hsc
    have h2 : cbase (cellSide L m₀ m₁ j) (fun μ => (((cellSide L m₀ m₁ j * (b μ).val : ℕ) :
        ZMod ((N₁ * L ^ m₁) * L ^ Kc))) : CTorus d L N₁ m₁ Kc) =
        (fun μ => (((cellSide L m₀ m₁ j * (b μ).val : ℕ) :
          ZMod ((N₁ * L ^ m₁) * L ^ Kc))) : CTorus d L N₁ m₁ Kc) := by
      rw [cbase_eq_sub]
      have h0 : (fun μ => ((fun μ => (((cellSide L m₀ m₁ j * (b μ).val : ℕ) :
          ZMod ((N₁ * L ^ m₁) * L ^ Kc))) : CTorus d L N₁ m₁ Kc) μ).val %
            cellSide L m₀ m₁ j) = 0 := funext fun μ => hal b μ
      rw [h0, natT_zero, sub_zero]
    have : c = ⟨_, hal b, Set.subset_univ _⟩ := Subtype.ext (h1.symm.trans h2)
    rw [this] at hc
    exact Finset.mem_coe.2 hc
  · have h' := congrArg Subtype.val h
    funext μ
    have h2 := congrArg (fun x : CTorus d L N₁ m₁ Kc => (x μ).val) h'
    simp only [hval] at h2
    exact ZMod.val_injective _ (Nat.eq_of_mul_eq_mul_left ha h2)

/-- **The size of a set of cubes against the number of its cubes** ((G1), `card_le_dExt`): for
`κ ≥ 0` and `n ≤ |C|`, `e^{-κ dExt C} ≤ e^{κ} e^{-(κ / c₁) n}`. -/
theorem exp_neg_dExt_le_card {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hj : j ≤ Kc)
    {Ω : Set (CTorus d L N₁ m₁ Kc)}
    (C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := Kc) m₀ j Ω)) {κ : ℝ}
    (hκ : 0 ≤ κ) {n : ℕ} (hn : n ≤ C.card) :
    Real.exp (-κ * dExt C) ≤ Real.exp κ * Real.exp (-(κ / c1 d L) * (n : ℝ)) := by
  have hc1 : 0 < c1 d L := by linarith [one_le_c1 d L]
  have h1 := card_le_dExt (m₀ := m₀) (j := j) (Ω := Ω) hN hj C
  have hn' : (n : ℝ) ≤ C.card := by exact_mod_cast hn
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h2 : (n : ℝ) / c1 d L ≤ 1 + dExt C := by
    rw [div_le_iff₀ hc1]; linarith
  have h3 : -(κ / c1 d L) * (n : ℝ) = -κ * ((n : ℝ) / c1 d L) := by ring
  rw [h3]
  nlinarith

end Size

end Balaban.Polymer.TwoTorusStep
