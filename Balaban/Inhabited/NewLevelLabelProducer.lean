/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelLabelGap
public import Balaban.Inhabited.NewLevelHatLayer
public import Balaban.SmallField.XiComposedPullback
public import Balaban.SmallField.RelBoxPath
public import Balaban.LargeField.R.RegionalAligned
public import Balaban.Fluctuation.LocalClassDensityFamilyNumA
public import Balaban.SmallField.IrrelTorusXidomGeometry

/-!
# The data hypothesis at the composed data of a label (the producer)

`composedChartGap_dataHypAnisoOn`: for a label `(j, y, X)` of a class whose generating set
`Tm.gs j X` has the hat specification, with `X` selected by ruling R15 (`relBox m₀ y X`), every
datum `r` of the composed chart with the scale gap of its source (`composedChartGap`), pulled back
through the cells `y + L^j v` of the layer `j`, satisfies `DataHypAnisoOn` on the placed polymer
`S = {unlift_j (x - y) : x ∈ X aligned}` with the path length `#S`, at
`(σ, ε, K₂) = (C₀ L^{j-k}, 10 C₁ ε, K_Σ L^{(j-k)(2-θ')} ε)`
(`composeData_dataHypAnisoOn_of_pullback`): the region is the pullback of the layer `j` of
`Tm.gs j X`, which contains the forward stars of the sites of `X` (`hatSpec_mem_layer_of_near`); its
edges are interface pairs (`interface_shift_of_layer_of_gap`); the paths are those of
`exists_latPath_of_relBox`.  The remaining premises are the conditions on constants and the chart
membership of the pulled-back datum and of its constant configuration.
`composedChartGap_dataHypAnisoOn_size`: the same with the path length `A (1 + d_j(X))` of the
consumers, for `A ≥ L^{(m₀+m₁)d} c₁` (`#S ≤ L^{(m₀+m₁)d} #cells(X) ≤ L^{(m₀+m₁)d} c₁ (1 + d_j(X))`,
`card_placeSet_le`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec
  Balaban.LargeField

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

omit [NeZero L] [NeZero N₁] in
/-- The pullback `ibase` of the blocks of the layer `j` is additive. -/
theorem ibase_add (j : ℕ) (v w : Site d) :
    ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (v + w) =
      ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v +
        ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j w := by
  funext μ
  simp only [ibase, Pi.add_apply]
  push_cast
  ring

omit [NeZero L] [NeZero N₁] in
theorem ibase_zero (j : ℕ) :
    ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (0 : Site d) = 0 := by
  funext μ
  simp [ibase]

/-- A site moved by the pullback of a lattice vector with coordinates of size at most `c` stays
within sup-distance `c L^j`. -/
theorem supDist_add_ibase_le (j : ℕ) (x : CTorus d L N₁ m₁ k) (w : Site d) {c : ℕ}
    (hw : ∀ μ, (w μ).natAbs ≤ c) :
    supDist x (x + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j w) ≤ c * L ^ j := by
  refine supDist_le_of_lift (fun μ => ((x μ).val : ℤ))
    (fun μ => ((x μ).val : ℤ) + ((L ^ j : ℕ) : ℤ) * w μ) (fun μ => by simp)
    (fun μ => by simp [ibase]) (fun μ => ?_)
  rw [show ((x μ).val : ℤ) - (((x μ).val : ℤ) + ((L ^ j : ℕ) : ℤ) * w μ) =
      -(((L ^ j : ℕ) : ℤ) * w μ) by ring, Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast]
  rw [mul_comm]
  exact Nat.mul_le_mul_right _ (hw μ)

open Classical in
/-- **`DataHypAnisoOn` at the composed data of a label** (the producer of the data hypothesis of
`irrelTorus_bound_of_dataOn_of_threshold(_birth)` at the data the step reads).  For a label
`(j, y, X)`, `1 ≤ j ≤ k`, with `X ∈ 𝒟_j` selected by ruling R15 (`relBox m₀ y X`), a generating
set `Gj` with the hat specification of `X` (`HatSpec`, cube exponent `s < m₀`), and a datum `r` of
the composed chart of `Gj` whose source has the scale gap (`composedChartGap`, radius `ε`): the
pulled-back field `v ↦ r.1 (y + L^j v)` and external field `ν L^{2j} r.2(y)` satisfy
`DataHypAnisoOn` on the placed polymer `S` with the path length `#S`, at
`(σ, ε, K₂) = (C₀ θ, 10 C₁ ε, K_Σ θ^{2-θ'} ε)`, `θ = L^j / L^k`, on every chart domain containing
the pulled-back datum and its constant configuration. -/
theorem composedChartGap_dataHypAnisoOn (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θh : ℝ}, 0 < θh → θh < 1 →
    ∀ {N₁ m₁ k N : ℕ} [NeZero N₁] {ϱ : ℝ} {m₀ j : ℕ}
      {X : Set (CTorus d L N₁ m₁ (k + 1))} {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
      {a₁ ν ε : ℝ} {y : CTorus d L N₁ m₁ (k + 1)} {S : Finset (Site d)},
      HatSpec m₀ j X Gj → hatScale L m₁ ϱ < m₀ →
      ϱ ≤ LargeField.minSep L (L ^ (m₁ + hatScale L m₁ ϱ)) →
      ∀ {N₁' : ℕ} [NeZero N₁'], N₁' * L ^ (m₁ + hatScale L m₁ ϱ) = N₁ * L ^ m₁ →
      2 ≤ m₀ → L ^ m₀ ∣ N₁ → 1 ≤ j → j ≤ k →
      Aligned (L ^ j) y → IsPolyDom m₀ j X → y ∈ X → relBox m₀ y X →
      S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
        (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j (x - y)) →
      0 < ν → 0 < a₁ →
      (4 * d + 6) * (xiC1 d * ε) ≤ 1 → xiC1 d * ε ≤ bgC1 d L N → xiC1 d * ε ≤ 1 / 200 →
      scaledC0 d * ((L : ℝ) ^ j / (L : ℝ) ^ k) ≤ 1 →
      ν * ((L : ℝ) ^ j) ^ 2 ≤ (scaledC0 d * ((L : ℝ) ^ j / (L : ℝ) ^ k)) ^ 2 →
      ∀ r ∈ composedChartGap (N := N) Gj (compWeight L a₁) ν j 1 ε,
      ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
      ((fun v => r.1 (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j v)),
        ((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • r.2 y) ∈ Dom →
      ((fun _ => r.1 y), ((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • r.2 y) ∈ Dom →
      DataHypAnisoOn {S} (fun _ => (S.card : ℝ)) Dom (ν * ((L : ℝ) ^ j) ^ 2)
        (scaledC0 d * ((L : ℝ) ^ j / (L : ℝ) ^ k)) (10 * (xiC1 d * ε))
        (xiSigma d L N B θh * ((L : ℝ) ^ j / (L : ℝ) ^ k) ^ (2 - θh) * ε)
        (fun v => r.1 (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j v))
        (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • r.2 y) := by
  obtain ⟨B, hB0, hB⟩ := composeData_dataHypAnisoOn_of_pullback (d := d) (L := L) hd hL
  refine ⟨B, hB0, ?_⟩
  intro θh hθh0 hθh1 N₁ m₁ k N _ ϱ m₀ j X Gj a₁ ν ε y S hHat hlt hs N₁' _ hc hm₀ hN hj1 hjk hy hX
    hyX hbox hSdef hν0 ha₁ hsmall hc1 hζ1 hτ1 hντ r hr Dom hch hch0
  obtain ⟨ϱ₁, G, hq, -, HB, hgap, D, hD, -, rfl⟩ := hr
  obtain ⟨-, hnj, hsg, hcol, hjθ, hθ0, hθ1⟩ := hgap
  have hLpos : 0 < L := by omega
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hjθ' : (L : ℝ) ^ j ≤ ((L : ℝ) ^ j / (L : ℝ) ^ k) * (L : ℝ) ^ (k + 1) := by
    refine hjθ.trans (mul_le_mul_of_nonneg_left ?_ hθ0.le)
    exact pow_le_pow_right₀ hLR (Nat.le_succ k)
  -- the cells of the layer `j` through `y`
  set f : Site d → CTorus d L N₁ m₁ (k + 1) :=
    fun v => y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j v with hfdef
  have hf : ∀ x μ, f (x + Pi.single μ 1) =
      f x + Pi.single μ ((L ^ j : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) := fun x μ => by
    simp only [hfdef, ibase_add_single, add_assoc]
  have hf0 : f 0 = y := by simp only [hfdef, ibase_zero, add_zero]
  -- the forward stars of the placed sites lie in the layer `j` of `Gj`
  have hnear : ∀ x ∈ X, ∀ w : Site d, (∀ μ, (w μ).natAbs ≤ 2) →
      x + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j w ∈ Gj.layer j := by
    intro x hx w hw
    refine hatSpec_mem_layer_of_near hL hHat hlt hs hj1 (by omega) hnj hc hx ?_
    refine (supDist_add_ibase_le j x w hw).trans ?_
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hLpos (Nat.le_add_right _ _))
  have hplace : ∀ p ∈ S, f p ∈ X := by
    intro p hp
    rw [hSdef] at hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨hxa, hxX⟩ := (Finset.mem_filter.1 hx).2
    simp only [hfdef]
    rw [add_ibase_unlift_sub (by omega) hy x, cbase_eq_self_of_aligned hxa]
    exact hxX
  have hs1 : ∀ μ ρ : Fin d, ((eU μ : Site d) ρ).natAbs ≤ 1 := fun μ ρ => by
    by_cases h : ρ = μ
    · subst h; simp [eU]
    · simp [eU, Pi.single_eq_of_ne h]
  have hstar : ∀ p ∈ S, StarIn {v | f v ∈ Gj.layer j} p := by
    intro p hp
    have hx := hplace p hp
    have e : ∀ w : Site d,
        f (p + w) = f p + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j w :=
      fun w => by simp only [hfdef, ibase_add, add_assoc]
    refine ⟨?_, fun μ => ⟨?_, fun ν => ?_⟩⟩
    · show f p ∈ Gj.layer j
      have := hnear (f p) hx 0 (fun μ => by simp)
      rwa [ibase_zero, add_zero] at this
    · show f (p + eU μ) ∈ Gj.layer j
      rw [e]
      exact hnear (f p) hx _ fun ρ => (hs1 μ ρ).trans (by norm_num)
    · show f (p + eU μ + eU ν) ∈ Gj.layer j
      rw [add_assoc, e]
      refine hnear (f p) hx _ fun ρ => ?_
      calc ((eU μ + eU ν : Site d) ρ).natAbs = ((eU μ : Site d) ρ + (eU ν : Site d) ρ).natAbs := rfl
        _ ≤ ((eU μ : Site d) ρ).natAbs + ((eU ν : Site d) ρ).natAbs := Int.natAbs_add_le _ _
        _ ≤ 2 := by have := hs1 μ ρ; have := hs1 ν ρ; omega
  have h0S : (0 : Site d) ∈ S := by
    rw [hSdef]
    have h := mem_placeSet (k := k + 1) hN (by omega : j ≤ k + 1) hy hX hyX
    simpa only [sub_self, unlift_zero] using h
  -- the paths of the placed polymer
  have hpath : ∀ X' ∈ ({S} : Set (Finset (Site d))), ∀ x ∈ X', ∃ (q : ℕ → Site d) (n : ℕ),
      q 0 = 0 ∧ q n = x ∧ (n : ℝ) ≤ (S.card : ℝ) ∧ IsLatPath q n ∧
        ∀ i ≤ n, StarIn {v | f v ∈ Gj.layer j} (q i) := by
    intro X' hX' x hx
    rw [Set.mem_singleton_iff] at hX'
    rw [hX'] at hx
    obtain ⟨q, n, hq0, hqn, hn, hqp, hqS⟩ :=
      exists_latPath_of_relBox hL hm₀ hN (by omega) hy hX hyX hbox hSdef x hx
    exact ⟨q, n, hq0, hqn, by exact_mod_cast (by omega : n ≤ S.card), hqp,
      fun i hi => hstar _ (hqS i hi)⟩
  -- the edges of the region are interface pairs
  have hadj : ∀ x μ, x ∈ {v | f v ∈ Gj.layer j} → x + eU μ ∈ {v | f v ∈ Gj.layer j} →
      IsInterfacePair Gj (f (x + Pi.single μ 1)) (f x) := by
    intro x μ hx hxμ
    have hxμ' : f x + Pi.single μ ((L ^ j : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) ∈
        Gj.layer j := by
      rw [← hf]; exact hxμ
    rw [hf]
    exact interface_shift_of_layer_of_gap Gj (by omega) hj1 (by omega) (f x) μ hx hxμ'
  have H := hB hθh0 hθh1 hq HB hν0 ha₁ hθ0 hθ1 hjθ' hnj hsg hcol hsmall hc1 hζ1 hτ1 hντ hj1
    (by omega) D hD f (R := {v | f v ∈ Gj.layer j}) hf (fun x hx => hx) hadj (hstar 0 h0S)
    (polys := {S}) (ℓ := fun _ => (S.card : ℝ)) hpath (Dom := Dom)
    (by rw [hf0]; exact hch) (by rw [hf0]; exact hch0)
  rw [hf0] at H
  exact H

/-- `DataHypAnisoOn` with a larger path length. -/
theorem dataHypAnisoOn_mono_len {N : ℕ} {polys : Set (Finset (Site d))}
    {ℓ ℓ' : Finset (Site d) → ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} {ν σ ε K₂ : ℝ} {ψ : Site d → Spin N} {b : Spin N}
    (h : DataHypAnisoOn polys ℓ Dom ν σ ε K₂ ψ b) (hℓ0 : ∀ X ∈ polys, 0 ≤ ℓ X)
    (hℓ : ∀ X ∈ polys, ℓ X ≤ ℓ' X) (hσε : 0 ≤ σ * ε) :
    DataHypAnisoOn polys ℓ' Dom ν σ ε K₂ ψ b where
  K2_nonneg := h.K2_nonneg
  sq0 := h.sq0
  sq := h.sq
  bdd0 := h.bdd0
  grad0 := h.grad0
  incr X hX x hx := (h.incr X hX x hx).trans (mul_le_mul_of_nonneg_right (hℓ X hX) hσε)
  taylor X hX x hx x' hx' := (h.taylor X hX x hx x' hx').trans (by
    have h2 : ℓ X ^ 2 ≤ ℓ' X ^ 2 := pow_le_pow_left₀ (hℓ0 X hX) (hℓ X hX) 2
    have h3 := h.K2_nonneg
    nlinarith)
  b_close := h.b_close
  b_long := h.b_long
  mem := h.mem
  mem_const := h.mem_const

open Classical in
/-- **The size of the placed polymer**: `#S ≤ L^{(m₀+m₁)d} c₁ (1 + d_j(X))` (the aligned sites of a
union of cells, `card_aligned_le_cellCount`, and the cell count, `cellCount_le_one_add_treeLenCovOne`). -/
theorem card_placeSet_le {K j m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hjK : j ≤ K)
    {y : CTorus d L N₁ m₁ K} {X : Set (CTorus d L N₁ m₁ K)} (hX : IsPolyDom m₀ j X)
    {S : Finset (Site d)}
    (hSdef : S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) j (x - y))) :
    (S.card : ℝ) ≤ ((L ^ (m₀ + m₁) : ℕ) : ℝ) ^ d * c1 d L * (1 + sizeJ m₀ j X) := by
  have hD := isDj_of_isPolyDom hX
  have h1 : S.card ≤ (Finset.univ.filter fun x : CTorus d L N₁ m₁ K =>
      x ∈ X ∧ Aligned (L ^ j) x).card := by
    rw [hSdef]
    refine Finset.card_image_le.trans (le_of_eq ?_)
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
  have h2 := LargeField.RegionalAligned.card_aligned_le_cellCount hN hjK hD.2.1
  have h3 := cellCount_le_one_add_treeLenCovOne hN hjK hD
  have hq : (0 : ℝ) ≤ ((L ^ (m₀ + m₁) : ℕ) : ℝ) ^ d := by positivity
  unfold sizeJ
  calc (S.card : ℝ) ≤ _ := by exact_mod_cast h1
    _ ≤ _ := h2
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h3 hq

open Classical in
/-- **`DataHypAnisoOn` at the composed data of a label, with the path length of the consumers**:
the statement of `composedChartGap_dataHypAnisoOn` with the length `A (1 + d_j(X))` for every
`A ≥ L^{(m₀+m₁)d} c₁` (`card_placeSet_le`, `dataHypAnisoOn_mono_len`). -/
theorem composedChartGap_dataHypAnisoOn_size (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θh : ℝ}, 0 < θh → θh < 1 →
    ∀ {N₁ m₁ k N : ℕ} [NeZero N₁] {ϱ : ℝ} {m₀ j : ℕ}
      {X : Set (CTorus d L N₁ m₁ (k + 1))} {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
      {a₁ ν ε A : ℝ} {y : CTorus d L N₁ m₁ (k + 1)} {S : Finset (Site d)},
      HatSpec m₀ j X Gj → hatScale L m₁ ϱ < m₀ →
      ϱ ≤ LargeField.minSep L (L ^ (m₁ + hatScale L m₁ ϱ)) →
      ∀ {N₁' : ℕ} [NeZero N₁'], N₁' * L ^ (m₁ + hatScale L m₁ ϱ) = N₁ * L ^ m₁ →
      2 ≤ m₀ → L ^ m₀ ∣ N₁ → 1 ≤ j → j ≤ k →
      Aligned (L ^ j) y → IsPolyDom m₀ j X → y ∈ X → relBox m₀ y X →
      S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
        (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j (x - y)) →
      ((L ^ (m₀ + m₁) : ℕ) : ℝ) ^ d * c1 d L ≤ A →
      0 < ν → 0 < a₁ →
      (4 * d + 6) * (xiC1 d * ε) ≤ 1 → xiC1 d * ε ≤ bgC1 d L N → xiC1 d * ε ≤ 1 / 200 →
      scaledC0 d * ((L : ℝ) ^ j / (L : ℝ) ^ k) ≤ 1 →
      ν * ((L : ℝ) ^ j) ^ 2 ≤ (scaledC0 d * ((L : ℝ) ^ j / (L : ℝ) ^ k)) ^ 2 →
      ∀ r ∈ composedChartGap (N := N) Gj (compWeight L a₁) ν j 1 ε,
      ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
      ((fun v => r.1 (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j v)),
        ((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • r.2 y) ∈ Dom →
      ((fun _ => r.1 y), ((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • r.2 y) ∈ Dom →
      DataHypAnisoOn {S} (fun _ => A * (1 + sizeJ m₀ j X)) Dom (ν * ((L : ℝ) ^ j) ^ 2)
        (scaledC0 d * ((L : ℝ) ^ j / (L : ℝ) ^ k)) (10 * (xiC1 d * ε))
        (xiSigma d L N B θh * ((L : ℝ) ^ j / (L : ℝ) ^ k) ^ (2 - θh) * ε)
        (fun v => r.1 (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j v))
        (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • r.2 y) := by
  obtain ⟨B, hB0, hB⟩ := composedChartGap_dataHypAnisoOn (d := d) (L := L) hd hL
  refine ⟨B, hB0, ?_⟩
  intro θh hθh0 hθh1 N₁ m₁ k N _ ϱ m₀ j X Gj a₁ ν ε A y S hHat hlt hs N₁' _ hc hm₀ hN hj1 hjk hy
    hX hyX hbox hSdef hA hν0 ha₁ hsmall hc1 hζ1 hτ1 hντ r hr Dom hch hch0
  have H := hB hθh0 hθh1 hHat hlt hs hc hm₀ hN hj1 hjk hy hX hyX hbox hSdef hν0 ha₁ hsmall hc1 hζ1
    hτ1 hντ r hr hch hch0
  have hcard := card_placeSet_le (K := k + 1) hN (by omega) hX hSdef
  have hc1p : (0 : ℝ) < ((L ^ (m₀ + m₁) : ℕ) : ℝ) ^ d * c1 d L := by
    have := one_le_c1 d L
    have : (0 : ℝ) < ((L ^ (m₀ + m₁) : ℕ) : ℝ) := by exact_mod_cast pow_pos (by omega) _
    positivity
  have hs0 : (0 : ℝ) ≤ 1 + sizeJ m₀ j X := by
    have h0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    by_contra hneg
    push Not at hneg
    nlinarith
  have hσε : 0 ≤ scaledC0 d * ((L : ℝ) ^ j / (L : ℝ) ^ k) * (10 * (xiC1 d * ε)) :=
    (norm_nonneg _).trans (H.grad0 ⟨0, by omega⟩)
  refine dataHypAnisoOn_mono_len H (fun _ _ => Nat.cast_nonneg _) (fun X' hX' => ?_) hσε
  rw [Set.mem_singleton_iff] at hX'
  subst hX'
  exact hcard.trans (mul_le_mul_of_nonneg_right hA hs0)

/-- **(M3) The chart membership of the composed data of a label**: for every datum `r` of the
composed chart of `Gj` whose source has the scale gap (`composedChartGap`, radius `ε`), the
pulled-back field `v ↦ r.1 (y + L^j v)` with the external field `ν L^{2j} r.2(y)`, and its constant
configuration `v ↦ r.1 y`, lie in the chart domain `Dom` of the label bound (the premises of
`composedChartGap_dataHypAnisoOn(_size)` that give the fields `mem`, `mem_const` of
`DataHypAnisoOn`).  The class's label bound takes `Dom` the domain of the terms read through
`fieldOf`/`hOf` (`irrelTorus_bound_of_dataOn_of_threshold`). -/
def ComposedLabelMem {N : ℕ} {ϱ : ℝ} (Dom : Set ((Site d → Spin N) × Spin N))
    (Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (ν : ℝ) (j : ℕ) (ε : ℝ)
    (y : CTorus d L N₁ m₁ (k + 1)) : Prop :=
  ∀ r ∈ composedChartGap (N := N) Gj a ν j 1 ε,
    ((fun v => r.1 (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j v)),
      ((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • r.2 y) ∈ Dom ∧
    ((fun _ => r.1 y), ((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • r.2 y) ∈ Dom

/-- **`ComposedLabelMem` is inhabited** (rule 10): every composed datum lies in the whole space. -/
theorem composedLabelMem_univ {N : ℕ} {ϱ : ℝ} (Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (a : ℕ → ℝ) (ν : ℝ) (j : ℕ) (ε : ℝ) (y : CTorus d L N₁ m₁ (k + 1)) :
    ComposedLabelMem (N := N) Set.univ Gj a ν j ε y :=
  fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩

end Balaban.Inhabited
