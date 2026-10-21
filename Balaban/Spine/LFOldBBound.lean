/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldB
public import Balaban.Spine.LFBdryOldEntropy

/-!
# The bound of the re-expanded old boundary terms at an output label (P6 (4.34))

The old part `oldBAt` of the boundary terms at an output label `Y` is bounded by
`C · e^{-κ' d_{k+1}(Y mod Ω_{k+1}^c)}` with `C` polynomial in `1 + d_{k+1}(Y)` times
`2^{c₁ (1 + d_{k+1}(Y))}`: for each set `T` of cubes with output label `Y` the cluster terms are
bounded by `oldClusterSite`'s bound, the size `d_Ω(T)` is the size of `Y` (`outLabel_spec`), and the
sums are controlled by entropy bounds whose roots are the cubes of `Y ∩ Ω_{k+1}`:

* `card_le_cellsIn_of_sitesOf_subset`: the number of cubes of a set `T` inside `Z`;
* `card_filter_sitesOf_subset_le`: the number of sets `T` of cubes inside `Z`, `≤ 2^{#cells}`;
* `sum_exp_treeLen_le_of_roots`: the sum of `e^{-κ₀ 𝗱(V)}` over sites `V` of `𝒟_j` containing a cube
  of `T` is at most `|T| K₀`;
* `blocksOf_nonempty_of_isDj`;
* `norm_oldBAt_le`: **the bound of `oldBAt` at an output label** (P6 (4.34)), conditional on the named
  inputs `H7MixedInnerLoc`, `H7MixedDatumLoc` and `OldResumSite`;
* `exp_poly_le_exp`, `oldB`, `norm_oldB_le`: **the re-expanded old boundary terms as boundary terms of
  scale `k + 1`** (`BTerms`) and their (D7) bound `C e^{-rate' d^pre_{k+1}(Y)}` for
  `κ' ≥ rate' + c₁ log 2 + 2`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

/-- The number of cubes of a set `T` of cubes of `Ω` whose sites lie in `Z` is at most the number of
cells of `Z ∩ Ω`. -/
theorem card_le_cellsIn_of_sitesOf_subset {Ω Z : Set (CTorus d L N₁ m₁ K)}
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω))
    (hT : sitesOf T ⊆ Z) : T.card ≤ (cellsIn (L := L) m₀ j (Z ∩ Ω)).card := by
  classical
  rw [← Finset.card_image_of_injective T Subtype.val_injective]
  refine Finset.card_le_card fun x hx => ?_
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
  simp only [cellsIn, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨b.2.1, fun z hz => ⟨hT (mem_sitesOf.2 ⟨b, hb, hz⟩), b.2.2 hz⟩⟩

open Classical in
/-- **The number of sets of cubes of `Ω` inside `Z`** is at most `2^{#cells(Z ∩ Ω)}`. -/
theorem card_filter_sitesOf_subset_le {Ω Z : Set (CTorus d L N₁ m₁ K)} :
    (Finset.univ.filter fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀
      j Ω) => sitesOf T ⊆ Z).card ≤ 2 ^ (cellsIn (L := L) m₀ j (Z ∩ Ω)).card := by
  rw [← Finset.card_powerset]
  refine Finset.card_le_card_of_injOn (fun T => T.image Subtype.val) (fun T hT => ?_)
    (fun T _ T' _ h => Finset.image_injective Subtype.val_injective h)
  have hT' := (Finset.mem_filter.1 (Finset.mem_coe.1 hT)).2
  refine Finset.mem_coe.2 (Finset.mem_powerset.2 fun x hx => ?_)
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
  simp only [cellsIn, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨b.2.1, fun z hz => ⟨hT' (mem_sitesOf.2 ⟨b, hb, hz⟩), b.2.2 hz⟩⟩

/-- **The cubes of `Ω` inside a set of `𝒟_j` meeting `Ω` form a nonempty set.** -/
theorem blocksOf_nonempty_of_isDj (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Ω V : Set (CTorus d L N₁ m₁ K)}
    (hΩ : IsPiUnion m₀ j Ω) (hV : IsDj m₀ j V) (hm : (V ∩ Ω).Nonempty) :
    (blocksOf m₀ j Ω V).Nonempty := by
  obtain ⟨z, hz⟩ := hm
  rw [← sitesOf_blocksOf hN hj hΩ hV.2.1] at hz
  obtain ⟨b, hb, -⟩ := mem_sitesOf.1 hz
  exact ⟨b, hb⟩

open Classical in
/-- **The sites of `𝒟_j` rooted at the cubes of a set `T`** (G2): for a finite family `𝒱` of sets of
`𝒟_j` each containing the cube of a member of `T`, `∑_{V ∈ 𝒱} e^{-κ₀ 𝗱(V)} ≤ |T| K₀(κ₀)`
(`sum_exp_le_of_roots` with the region the whole torus, where the modular size is `d^cov_j`). -/
theorem sum_exp_treeLen_le_of_roots (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Ω : Set (CTorus d L N₁ m₁ K)}
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω))
    (𝒱 : Finset (Set (CTorus d L N₁ m₁ K)))
    (h𝒱 : ∀ V ∈ 𝒱, IsDj m₀ j V ∧ ∃ b ∈ T, box b.1 (cellSide L m₀ m₁ j) ⊆ V)
    {κ₀ : ℝ} (hκ : aEnt d L + 1 ≤ κ₀) :
    ∑ V ∈ 𝒱, Real.exp (-κ₀ * treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j V)
      ≤ T.card * K0 d L κ₀ := by
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hU : IsPiUnion m₀ j (Set.univ : Set (CTorus d L N₁ m₁ K)) := fun z _ =>
    ⟨cbase (cellSide L m₀ m₁ j) z, aligned_cbase z, mem_box_cbase ha0 z, Set.subset_univ _⟩
  have hD : ∀ V ∈ 𝒱, DjModFin m₀ j Set.univ V := fun V hV => by
    have hD := (h𝒱 V hV).1
    exact ⟨hD.1, hD.2.2, fun z hz => absurd (Set.mem_univ z) hz, dcovModE_ne_top_of_IsDj hD⟩
  have h := sum_exp_le_of_roots hN hj hU (T.image Subtype.val)
    (fun r hr => by
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hr
      exact ⟨b.2.1, Set.subset_univ _⟩) hκ (fun V => V ∈ 𝒱)
    (fun V _ hV => by
      obtain ⟨b, hb, hbV⟩ := (h𝒱 V hV).2
      exact ⟨b.1, Finset.mem_image_of_mem _ hb, hbV⟩)
  have hK := (K0_pos d L κ₀).le
  calc ∑ V ∈ 𝒱, Real.exp (-κ₀ * treeLenCovOne (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
        m₀ j V)
      = ∑ V ∈ 𝒱, Real.exp (-κ₀ * dcovMod m₀ j Set.univ V) :=
        Finset.sum_congr rfl fun V _ => by rw [dcovMod_of_subset (Set.subset_univ V)]
    _ ≤ ((T.image Subtype.val).card : ℝ) * K0 d L κ₀ := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun V hV => ?_)
          (fun _ _ _ => (Real.exp_pos _).le)) h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hD V hV, hV⟩
    _ ≤ T.card * K0 d L κ₀ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_image_le) hK

end Balaban.Fluctuation

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background
  Balaban.Polymer

section Bound

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- An inclusion of fine lifts on the frame torus is an inclusion of fine sets. -/
theorem fineSet_subset_of_d7Pull_subset {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {j j' : ℕ}
    {A : Set (Torus S.d (n j))} {B : Set (Torus S.d (n j'))} (h : d7Pull F j A ⊆ d7Pull F j' B) :
    fineSet (S := S) (n := n) M K j A ⊆ fineSet (S := S) (n := n) M K j' B := by
  intro y hy
  have hx : castT F.side.symm y ∈ d7Pull F j A := by
    show castT F.side (castT F.side.symm y) ∈ fineSet (S := S) (n := n) M K j A
    rw [castT_castT_symm]
    exact hy
  have h' : castT F.side (castT F.side.symm y) ∈ fineSet (S := S) (n := n) M K j' B := h hx
  rwa [castT_castT_symm] at h'

omit [NeZero M] in
/-- A site of the cover torus whose frame site lies in a fine lift lies in the fine set. -/
theorem fineOfC_mem_of_toFrame_mem {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ}
    (hk : k + 1 ≤ K) {j : ℕ} {B : Set (Torus S.d (n j))}
    {x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)} (h : toFrame g hnn hM1 F hk x ∈ d7Pull F j B) :
    fineOfC g hnn hM1 hk x ∈ fineSet (S := S) (n := n) M K j B := by
  have h' : castT F.side (castT F.side.symm (fineOfC g hnn hM1 hk x)) ∈
      fineSet (S := S) (n := n) M K j B := h
  rwa [castT_castT_symm] at h'

open Classical in
/-- **The bound of the old part of the boundary terms at an output label** (P6 (4.34); FLUCTUATION
Theorem 3.1 (c); P3 (4.45)–(4.49) through the named input `OldResumSite`): for the old labels `Xs` of
the record (boundary domains of the record meeting `Ω_{k+1}`), a field `(ψ, ψ', g)` in the H7 domain
of scale `k + 1` at the fine set of the output label `Y`, and constants with `κ_H ≤ κ_V` and
`rate - κ_X ≥ a_ent + 1`,
`|oldB(Y)| ≤ 2^{c₁(1+D)} · C_PE fac C_res · L^d c₁ (1+D) K₀(rate-κ_X) · c₁ (1+D) K₀(κ₀) · e^{-κ' D}`,
`D = d_{k+1}(Y mod Ω_{k+1}^c)`.  Each set `T` of cubes with output label `Y` and `d_Ω(T) < ∞` has
`d_Ω(T) = D` (`outLabel_spec`), at most `c₁ (1 + D)` cubes, and there are at most `2^{c₁(1+D)}` such
sets; the old labels of the nonzero terms lie in `Y` (`d7Pull_subset_outLabel`, `sum_exp_oldIn_le`),
the sites of their marks contain a cube of `T` (`sum_exp_treeLen_le_of_roots`).  Conditional on
`H7MixedInnerLoc`, `H7MixedDatumLoc`, `OldResumSite`. -/
theorem norm_oldBAt_le {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ}
    (hk : k + 1 ≤ K) {cs : OpConsts} {P : BudgetConsts} {rep : Rep S n R k0 K M N g cs P k}
    {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))} {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ}
    {hv : EuclideanSpace ℝ (Fin N)}
    (hrec : D7BdryPost Fr hnn (Nat.le_of_succ_le hk) rep Zof aw μs ε ε1 νs fac rate hv)
    {A : LabHist S n R k0 K} (hA : A ∈ rep.hist) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊)
    (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {c BG δb δc κ κ₁ rψ : ℝ}
    (hS : Dec2.DecSpecs S.d S.L (Dec2.mixedKc S.d S.L) (Cchi S.d S.L) c BG)
    (HB : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν)
    (hm₁ : 2 ≤ m₁) (hN : 5 < g.c * n (k + 1)) (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁)
    (hag : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1))
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) (hκ : 0 < κ)
    (hMc : c * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX S.d S.L (Cchi S.d S.L) * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hδ0 : 0 < δb) (hε : δb ≤ bgC0 S.d S.L N) (hδ : δb ≤ c7 S.d S.L N BG κ)
    (hphi : 3 * δb + K4 S.d S.L N BG κ * δb < 1 / 2)
    (hmarD : K4 S.d S.L N BG κ * δb + 2 * δb +
      K4 S.d S.L N BG κ * δb * (K4 S.d S.L N BG κ * δb + 2 * (1 + 3 * δb)) < δc)
    (hαD : K4 S.d S.L N BG κ * δb < coerciveConst S.d / 2)
    (hsm : δc ^ 2 * smallConstX S.d S.L κ ≤ 1 / 4) (hκ₁ : 1 ≤ κ₁) (hκ₁κ : κ₁ ≤ κ) (ρ r r' : ℕ)
    (hIn : H7MixedInnerLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r aw μs
      ε ε1 νs (hC hv) (Real.exp κ₁) rψ)
    (hDat : H7MixedDatumLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs (hC hv) ν δb)
    {Xs : Finset (Finset (Torus S.d (n k)))}
    (hXs : ∀ X ∈ Xs, X ∈ bdryDomsPost Fr A k (Zof A) ∧ X ∈ oldDoms Fr A.H k)
    (Y : Finset (Torus S.d (n (k + 1)))) {ψ : MultiFieldC S n M K N} {q' : FinFieldC S n M K N}
    {gx : GIdx S n M K N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) (k + 1) hk
      (fineSet (S := S) (n := n) M K (k + 1) (Y : Set (Torus S.d (n (k + 1))))) aw μs ε ε1 νs
      (hC hv) ψ (extK q') (fun x i => gx (x, i)))
    (inner : Finset (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))))
    (hcb : ∀ u : inner, toFrame g hnn hM1 Fr hk
      (unitRep (u : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)) ∈
        Localization.box (cb u).1 (cellSide S.L m₀ m₁ (k + 1)))
    (hp : 0 < p₁) (I : LocInteraction (fun b => {u : inner // cb u = b} → Rn N))
    (ψout : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ)
    (hrψ : 0 < rψ) (hfac : 0 < fac) {κX κV Cres : ℝ}
    (hres : OldResumSite g hnn hM1 Fr A.H hk hρ r r' κ₁ κX κV Cres) (hCres : 0 < Cres)
    (hκV : I.κH ≤ κV) (hαX : aEnt S.d S.L + 1 ≤ rate - κX) :
    ‖oldBAt g hnn hM1 Fr A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hp I ψout rψ (rho4 S.d S.L N BG κ) ρ r r' rep A Xs (extK q') hv gx Y‖ ≤
      Real.exp (Real.log 2 * (c1 S.d S.L * (1 + d7SizeAt Fr (k + 1) (OmegaCube A.H (k + 1)) Y))) *
        (CPE S.d S.L (I.Kc + 1) I.κH I.κ0 I.κ' * (fac * Cres)) *
        ((S.L : ℝ) ^ S.d * (c1 S.d S.L * (1 + d7SizeAt Fr (k + 1) (OmegaCube A.H (k + 1)) Y)) * K0 S.d S.L (rate - κX)) *
        (c1 S.d S.L * (1 + d7SizeAt Fr (k + 1) (OmegaCube A.H (k + 1)) Y) * K0 S.d S.L I.κ0) *
        Real.exp (-I.κ' * d7SizeAt Fr (k + 1) (OmegaCube A.H (k + 1)) Y) := by
  have hΩ' : IsPiUnion m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) := d7Pull_isPiUnion Fr hnn hk _
  have hprob := (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).isProbabilityMeasure_cubeMeasure
    inner cb hp
  set D := d7SizeAt Fr (k + 1) (OmegaCube A.H (k + 1)) Y with hDdef
  have hD0 : 0 ≤ D := d7SizeAt_nonneg Fr (k + 1) (OmegaCube A.H (k + 1)) Y
  have hc1 := one_le_c1 S.d S.L
  have hCPE : 0 ≤ CPE S.d S.L (I.Kc + 1) I.κH I.κ0 I.κ' := by
    unfold CPE
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith))
      (Real.exp_pos _).le
  set Cst := CPE S.d S.L (I.Kc + 1) I.κH I.κ0 I.κ' * (fac * Cres) with hCst
  have hCst0 : 0 ≤ Cst := mul_nonneg hCPE (by positivity)
  have hK0 := (K0_pos S.d S.L I.κ0).le
  set SX := ∑ X ∈ Xs.filter (fun X : Finset (Torus S.d (n k)) => d7Pull Fr k (X : Set (Torus S.d (n k))) ⊆
      d7Pull Fr (k + 1) (Y : Set (Torus S.d (n (k + 1))))),
    Real.exp (-(rate - κX) * d7Size Fr A k X) with hSX
  have hSX0 : 0 ≤ SX := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  -- the old labels: validity and meeting `Ω_{k+1}`
  have hXv : ∀ X ∈ Xs, FineValidAt Fr k (A.H.omegaPost k) X ∧
      (d7Pull Fr k (X : Set (Torus S.d (n k))) ∩ d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))).Nonempty := fun X hX => by
    obtain ⟨hb, hm⟩ := Finset.mem_filter.1 (hXs X hX).2
    exact ⟨(mem_bdryDomsAt.1 hb).2, hm⟩
  -- a good site: a family with this site, the site is in `𝒟_{k+1}` and meets `Ω_{k+1}`
  have hsite : ∀ X V, V ∈ sitesX g hnn hM1 Fr A.H hk hρ r r' X →
      ∃ J ∈ famAt g hnn hM1 Fr A.H hk hρ r r' X V, IsDj m₀ (k + 1) V ∧
        (V ∩ d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))).Nonempty := fun X V hV => exists_of_mem_sitesX g hnn hM1 hV
  -- the terms of a set `T` that is empty or of infinite size vanish
  have hbad : ∀ T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))),
      ¬ (T.Nonempty ∧ dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) ≠ ⊤) →
      ∑ X ∈ Xs, ∑ V ∈ (sitesX g hnn hM1 Fr A.H hk hρ r r' X).filter
        (fun V => blocksOf m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) V ⊆ T),
        oldClusterSite g hnn hM1 Fr A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hp I ψout rψ (rho4 S.d S.L N BG κ) ρ r r' rep A X (extK q') hv gx V T = 0 := by
    intro T hT
    refine Finset.sum_eq_zero fun X _ => Finset.sum_eq_zero fun V hV => ?_
    obtain ⟨hVs, hVT⟩ := Finset.mem_filter.1 hV
    obtain ⟨-, -, hVd, hm⟩ := hsite X V hVs
    by_cases hTne : T.Nonempty
    · have hdom : dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) = ⊤ := by
        by_contra h
        exact hT ⟨hTne, h⟩
      exact markTerm_eq_zero_of_dOmega_top _ Fr.divN₁ hk hΩ' I.A V hVd hm _ hdom
    · obtain ⟨b, hb⟩ := blocksOf_nonempty_of_isDj Fr.divN₁ hk hΩ' hVd hm
      exact absurd ⟨b, hVT hb⟩ hTne
  -- the terms of a good set `T` with output label `Y`
  have hgood : ∀ T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))), outLabel Fr k (OmegaCube A.H (k + 1)) T = Y →
      T.Nonempty → dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) ≠ ⊤ →
      ‖∑ X ∈ Xs, ∑ V ∈ (sitesX g hnn hM1 Fr A.H hk hρ r r' X).filter
        (fun V => blocksOf m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) V ⊆ T),
        oldClusterSite g hnn hM1 Fr A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hp I ψout rψ (rho4 S.d S.L N BG κ) ρ r r' rep A X (extK q') hv gx V T‖ ≤ Cst * SX * (T.card * K0 S.d S.L I.κ0) *
          Real.exp (-I.κ' * D) := by
    intro T hTY hTne hfin
    have hspec := outLabel_spec Fr hnn hk (OmegaCube A.H (k + 1)) T hTne hfin
    rw [hTY] at hspec
    obtain ⟨hYd, -, hYD⟩ := hspec
    have hX : ∀ X ∈ Xs, ‖∑ V ∈ (sitesX g hnn hM1 Fr A.H hk hρ r r' X).filter
        (fun V => blocksOf m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) V ⊆ T),
        oldClusterSite g hnn hM1 Fr A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hp I ψout rψ (rho4 S.d S.L N BG κ) ρ r r' rep A X (extK q') hv gx V T‖ ≤
        if d7Pull Fr k (X : Set (Torus S.d (n k))) ⊆ d7Pull Fr (k + 1) (Y : Set (Torus S.d (n (k + 1))))
        then Cst * Real.exp (-(rate - κX) * d7Size Fr A k X) * (T.card * K0 S.d S.L I.κ0) *
          Real.exp (-I.κ' * D) else 0 := by
      intro X hX
      by_cases hsub : d7Pull Fr k (X : Set (Torus S.d (n k))) ⊆
          d7Pull Fr (k + 1) (Y : Set (Torus S.d (n (k + 1))))
      · simp only [hsub, ↓reduceIte]
        have hXY := fineSet_subset_of_d7Pull_subset Fr hsub
        -- the sites of the terms lie in `Y`
        have hVY : ∀ V ∈ (sitesX g hnn hM1 Fr A.H hk hρ r r' X).filter
            (fun V => blocksOf m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) V ⊆ T),
            ∀ J ∈ famAt g hnn hM1 Fr A.H hk hρ r r' X V,
              markSite g hnn hM1 Fr A.H hk hρ r r' X J ⊆
                d7Pull Fr (k + 1) (Y : Set (Torus S.d (n (k + 1)))) := by
          intro V hV J hJ
          obtain ⟨-, hJg, hJV⟩ := (mem_famAt g hnn hM1).1 hJ
          have h := markSite_subset_outLabel Fr hnn hM1 A.H hk hρ r r' X J hJg T
            (hJV ▸ (Finset.mem_filter.1 hV).2) hfin
          rwa [hTY] at h
        have hterm : ∀ V ∈ (sitesX g hnn hM1 Fr A.H hk hρ r r' X).filter
            (fun V => blocksOf m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) V ⊆ T),
            ‖oldClusterSite g hnn hM1 Fr A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hp I ψout rψ (rho4 S.d S.L N BG κ) ρ r r' rep A X (extK q') hv gx V T‖ ≤
              Cst * Real.exp (-(rate - κX) * d7Size Fr A k X) * Real.exp (-I.κ' * D) *
                Real.exp (-I.κ0 * treeLenCovOne (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁)
                  (K := K) m₀ (k + 1) V) := by
          intro V hV
          have hVJ : ∀ J ∈ famAt g hnn hM1 Fr A.H hk hρ r r' X V,
              ∀ x ∈ dataSites (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
                (locSetXJ g hM1 A.H r r' X J)).G',
              fineOfC g hnn hM1 hk x ∈ fineSet (S := S) (n := n) M K (k + 1)
                (Y : Set (Torus S.d (n (k + 1)))) := by
            intro J hJ x hx
            refine fineOfC_mem_of_toFrame_mem g hnn hM1 Fr hk (hVY V hV J hJ ?_)
            refine markBase_subset_markSite g hnn hM1 Fr A.H hk hρ r r' X J ?_
            exact Or.inr ⟨x, hx, rfl⟩
          have h := norm_oldClusterSite_le g hnn hM1 hk hrec hA hk1 hρ z h₀ a₁ ν β p₁ δ hS HB hm₁ hN hM hag ha₁ ha₂ hκ hMc hMX hδ0 hε hδ hphi hmarD hαD hsm hκ₁ hκ₁κ ρ r r' hIn hDat htgt (hXs X hX).1 hXY V hVJ
            (hXs X hX).2 (Finset.mem_filter.1 hV).1 inner cb hcb hp I ψout hrψ hfac hres hCres hκV T
          rw [← hYD] at h
          refine h.trans (le_of_eq ?_)
          rw [hCst]
          ring
        have hroot := sum_exp_treeLen_le_of_roots Fr.divN₁ hk T
          ((sitesX g hnn hM1 Fr A.H hk hρ r r' X).filter
            (fun V => blocksOf m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) V ⊆ T)) (fun V hV => by
            obtain ⟨hVs, hVT⟩ := Finset.mem_filter.1 hV
            obtain ⟨-, -, hVd, hm⟩ := hsite X V hVs
            obtain ⟨b, hb⟩ := blocksOf_nonempty_of_isDj Fr.divN₁ hk hΩ' hVd hm
            exact ⟨hVd, b, hVT hb, mem_blocksOf.1 hb⟩) I.hκ0
        have hA0 : 0 ≤ Cst * Real.exp (-(rate - κX) * d7Size Fr A k X) * Real.exp (-I.κ' * D) :=
          mul_nonneg (mul_nonneg hCst0 (Real.exp_pos _).le) (Real.exp_pos _).le
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
        rw [← Finset.mul_sum]
        calc Cst * Real.exp (-(rate - κX) * d7Size Fr A k X) * Real.exp (-I.κ' * D) *
              ∑ V ∈ (sitesX g hnn hM1 Fr A.H hk hρ r r' X).filter
                (fun V => blocksOf m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) V ⊆ T),
              Real.exp (-I.κ0 * treeLenCovOne (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁)
                (K := K) m₀ (k + 1) V)
            ≤ Cst * Real.exp (-(rate - κX) * d7Size Fr A k X) * Real.exp (-I.κ' * D) *
              (T.card * K0 S.d S.L I.κ0) := mul_le_mul_of_nonneg_left hroot hA0
          _ = _ := by ring
      · simp only [hsub, ↓reduceIte]
        refine le_of_eq (norm_eq_zero.2 (Finset.sum_eq_zero fun V hV => ?_))
        exfalso
        obtain ⟨hVs, hVT⟩ := Finset.mem_filter.1 hV
        obtain ⟨J, hJ, -, -⟩ := hsite X V hVs
        obtain ⟨-, -, hJV⟩ := (mem_famAt g hnn hM1).1 hJ
        have h := d7Pull_subset_outLabel Fr hnn hM1 A.H hk hρ (hXv X hX).1 (hXv X hX).2 r r' J T
          (hJV ▸ hVT) hfin
        rw [hTY] at h
        exact hsub h
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hX).trans (le_of_eq ?_))
    rw [← Finset.sum_filter, hSX, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  -- the sum over the sets `T`
  unfold oldBAt
  refine (norm_sum_le _ _).trans ?_
  have hT : ∀ T ∈ Finset.univ.filter (fun T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))) =>
      outLabel Fr k (OmegaCube A.H (k + 1)) T = Y),
      ‖∑ X ∈ Xs, ∑ V ∈ (sitesX g hnn hM1 Fr A.H hk hρ r r' X).filter
        (fun V => blocksOf m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) V ⊆ T),
        oldClusterSite g hnn hM1 Fr A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hp I ψout rψ (rho4 S.d S.L N BG κ) ρ r r' rep A X (extK q') hv gx V T‖ ≤
      if T.Nonempty ∧ dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) ≠ ⊤ then
        Cst * SX * (T.card * K0 S.d S.L I.κ0) * Real.exp (-I.κ' * D) else 0 := by
    intro T hT
    by_cases hg : T.Nonempty ∧ dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) ≠ ⊤
    · simp only [hg, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      exact hgood T (Finset.mem_filter.1 hT).2 hg.1 hg.2
    · simp only [hg, ↓reduceIte]
      rw [hbad T hg, norm_zero]
  refine (Finset.sum_le_sum hT).trans ?_
  rw [← Finset.sum_filter]
  rcases Finset.eq_empty_or_nonempty ((Finset.univ.filter (fun T : Finset (CubeB (d := S.d)
      (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))) =>
      outLabel Fr k (OmegaCube A.H (k + 1)) T = Y)).filter
      (fun T => T.Nonempty ∧ dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))
        (sitesOf T) ≠ ⊤)) with hex | hex
  · rw [hex, Finset.sum_empty]
    have := (K0_pos S.d S.L (rate - κX)).le
    positivity
  · obtain ⟨T₀, hT₀⟩ := hex
    have hT₀' := Finset.mem_filter.1 hT₀
    have hT₀Y := (Finset.mem_filter.1 hT₀'.1).2
    have hT₀ne := hT₀'.2.1
    have hT₀fin := hT₀'.2.2
    have hspec := outLabel_spec Fr hnn hk (OmegaCube A.H (k + 1)) T₀ hT₀ne hT₀fin
    rw [hT₀Y] at hspec
    obtain ⟨-, hYv, -⟩ := hspec
    -- the number of cubes of `Y ∩ Ω_{k+1}`
    have hcells : ((cellsIn (L := S.L) m₀ (k + 1) (d7Pull Fr (k + 1) (Y : Set (Torus S.d (n (k + 1))))
        ∩ d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))).card : ℝ) ≤ c1 S.d S.L * (1 + D) := by
      rw [card_cellsIn_eq_cellCount]
      exact hYv.cellCount_le Fr.divN₁ hk
    -- the sites of a good set lie in the fine set of `Y`
    have hsitesY : ∀ T ∈ (Finset.univ.filter (fun T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))) =>
        outLabel Fr k (OmegaCube A.H (k + 1)) T = Y)).filter
        (fun T => T.Nonempty ∧ dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) ≠ ⊤),
        sitesOf T ⊆ d7Pull Fr (k + 1) (Y : Set (Torus S.d (n (k + 1)))) := by
      intro T hT
      obtain ⟨hT1, hTne, hTfin⟩ := Finset.mem_filter.1 hT
      have hspec := outLabel_spec Fr hnn hk (OmegaCube A.H (k + 1)) T hTne hTfin
      rw [(Finset.mem_filter.1 hT1).2] at hspec
      rw [hspec.1]
      exact subset_Yhat _ _
    have hcardT : ∀ T ∈ (Finset.univ.filter (fun T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))) =>
        outLabel Fr k (OmegaCube A.H (k + 1)) T = Y)).filter
        (fun T => T.Nonempty ∧ dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) ≠ ⊤),
        (T.card : ℝ) ≤ c1 S.d S.L * (1 + D) := fun T hT =>
      (Nat.cast_le.2 (card_le_cellsIn_of_sitesOf_subset T (hsitesY T hT))).trans hcells
    -- the number of good sets
    have hnum : ((((Finset.univ.filter (fun T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))) =>
        outLabel Fr k (OmegaCube A.H (k + 1)) T = Y)).filter
        (fun T => T.Nonempty ∧ dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) ≠ ⊤)).card : ℕ) : ℝ) ≤
        Real.exp (Real.log 2 * (c1 S.d S.L * (1 + D))) := by
      have h1 := Finset.card_le_card (s := (Finset.univ.filter (fun T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))) =>
        outLabel Fr k (OmegaCube A.H (k + 1)) T = Y)).filter
        (fun T => T.Nonempty ∧ dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) ≠ ⊤))
        (t := Finset.univ.filter fun T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))) =>
          sitesOf T ⊆ d7Pull Fr (k + 1) (Y : Set (Torus S.d (n (k + 1)))))
        (fun T hT => Finset.mem_filter.2 ⟨Finset.mem_univ _, hsitesY T hT⟩)
      have h2 := card_filter_sitesOf_subset_le (m₀ := m₀) (j := k + 1)
        (Ω := d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (Z := d7Pull Fr (k + 1) (Y : Set (Torus S.d (n (k + 1)))))
      have h3 : ((2 : ℕ) : ℝ) ^ (cellsIn (L := S.L) m₀ (k + 1) (d7Pull Fr (k + 1)
          (Y : Set (Torus S.d (n (k + 1)))) ∩ d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))).card ≤
          Real.exp (Real.log 2 * (c1 S.d S.L * (1 + D))) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
        refine Real.exp_le_exp.2 ?_
        have := Real.log_nonneg (show (1 : ℝ) ≤ ((2 : ℕ) : ℝ) by norm_num)
        push_cast at this ⊢
        nlinarith
      calc _ ≤ ((2 ^ (cellsIn (L := S.L) m₀ (k + 1) (d7Pull Fr (k + 1)
            (Y : Set (Torus S.d (n (k + 1)))) ∩ d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))).card : ℕ) : ℝ) := by
            exact_mod_cast h1.trans h2
        _ ≤ _ := by push_cast; exact_mod_cast h3
    -- the old labels inside `Y`
    have hSXle : SX ≤ (S.L : ℝ) ^ S.d * (c1 S.d S.L * (1 + D)) * K0 S.d S.L (rate - κX) := by
      have hinj : Set.InjOn (fun X : Finset (Torus S.d (n k)) =>
          d7Pull Fr k (X : Set (Torus S.d (n k)))) ↑(Xs.filter fun X : Finset (Torus S.d (n k)) =>
            d7Pull Fr k (X : Set (Torus S.d (n k))) ⊆
              d7Pull Fr (k + 1) (Y : Set (Torus S.d (n (k + 1))))) := fun X _ X' _ h =>
        Finset.coe_injective (Balaban.LargeField.d7Pull_injective Fr hnn (Nat.le_of_succ_le hk) h)
      have hmain := sum_exp_oldIn_le Fr.divN₁ hk
        (d7Pull_isPiUnion Fr hnn (Nat.le_of_succ_le hk) (A.H.omegaPost k)) hΩ'
        (A.H.d7Pull_OmegaCube_succ_subset Fr hnn hk) hYv hαX
      rw [hSX]
      calc ∑ X ∈ Xs.filter (fun X : Finset (Torus S.d (n k)) => d7Pull Fr k (X : Set (Torus S.d (n k))) ⊆
            d7Pull Fr (k + 1) (Y : Set (Torus S.d (n (k + 1))))),
            Real.exp (-(rate - κX) * d7Size Fr A k X)
          = ∑ X' ∈ (Xs.filter (fun X : Finset (Torus S.d (n k)) => d7Pull Fr k (X : Set (Torus S.d (n k))) ⊆
              d7Pull Fr (k + 1) (Y : Set (Torus S.d (n (k + 1)))))).image
              (fun X : Finset (Torus S.d (n k)) => d7Pull Fr k (X : Set (Torus S.d (n k)))),
              Real.exp (-(rate - κX) * dcovMod m₀ k (d7Pull Fr k (A.H.omegaPost k)) X') := by
            rw [Finset.sum_image hinj]
            rfl
        _ ≤ _ := by
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun X' hX' => ?_)
              (fun _ _ _ => (Real.exp_pos _).le)) hmain
            obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hX'
            obtain ⟨hXXs, hXsub⟩ := Finset.mem_filter.1 hX
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨(hXv X hXXs).1, hXsub, (hXv X hXXs).2⟩
    calc ∑ T ∈ (Finset.univ.filter (fun T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))) =>
          outLabel Fr k (OmegaCube A.H (k + 1)) T = Y)).filter
          (fun T => T.Nonempty ∧ dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) ≠ ⊤),
          Cst * SX * (T.card * K0 S.d S.L I.κ0) * Real.exp (-I.κ' * D)
        ≤ ∑ T ∈ (Finset.univ.filter (fun T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))) =>
          outLabel Fr k (OmegaCube A.H (k + 1)) T = Y)).filter
          (fun T => T.Nonempty ∧ dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) ≠ ⊤),
          Cst * SX * (c1 S.d S.L * (1 + D) * K0 S.d S.L I.κ0) * Real.exp (-I.κ' * D) :=
          Finset.sum_le_sum fun T hT => mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hcardT T hT) hK0) (mul_nonneg hCst0 hSX0))
            (Real.exp_pos _).le
      _ = (((Finset.univ.filter (fun T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))) =>
          outLabel Fr k (OmegaCube A.H (k + 1)) T = Y)).filter
          (fun T => T.Nonempty ∧ dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) ≠ ⊤)).card : ℝ) *
          (Cst * SX * (c1 S.d S.L * (1 + D) * K0 S.d S.L I.κ0) * Real.exp (-I.κ' * D)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.exp (Real.log 2 * (c1 S.d S.L * (1 + D))) *
          (Cst * ((S.L : ℝ) ^ S.d * (c1 S.d S.L * (1 + D)) * K0 S.d S.L (rate - κX)) *
            (c1 S.d S.L * (1 + D) * K0 S.d S.L I.κ0) * Real.exp (-I.κ' * D)) := by
          refine mul_le_mul hnum ?_ (by positivity) (Real.exp_pos _).le
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hSXle hCst0) (by positivity)) (Real.exp_pos _).le
      _ = _ := by rw [hCst]; ring

/-- **A polynomial times `2^{c₁(1+D)}` is absorbed by the rate** (`1 + D ≤ e^D`): for `D ≥ 0` and
`κ' ≥ rate' + c₁ log 2 + 2`, the bound of `norm_oldBAt_le` is at most
`2^{c₁} C L^d c₁ K₁ c₁ K₂ e^{-rate' D}`. -/
theorem exp_poly_le_exp {a C B K₁ K₂ κ' rate' D : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hD : 0 ≤ D) (hκ' : rate' + Real.log 2 * a + 2 ≤ κ') :
    Real.exp (Real.log 2 * (a * (1 + D))) * C * (B * (a * (1 + D)) * K₁) * (a * (1 + D) * K₂) *
        Real.exp (-κ' * D) ≤
      Real.exp (Real.log 2 * a) * C * (B * a * K₁) * (a * K₂) * Real.exp (-rate' * D) := by
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1D : 1 + D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have h1D0 : 0 ≤ 1 + D := by linarith
  have hsq : (1 + D) * (1 + D) ≤ Real.exp D * Real.exp D :=
    mul_le_mul h1D h1D h1D0 (Real.exp_pos _).le
  have hexp : Real.exp (Real.log 2 * (a * (1 + D))) * (Real.exp D * Real.exp D) *
      Real.exp (-κ' * D) ≤ Real.exp (Real.log 2 * a) * Real.exp (-rate' * D) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hP : 0 ≤ C * (B * a * K₁) * (a * K₂) := by positivity
  calc Real.exp (Real.log 2 * (a * (1 + D))) * C * (B * (a * (1 + D)) * K₁) * (a * (1 + D) * K₂) *
        Real.exp (-κ' * D)
      = (C * (B * a * K₁) * (a * K₂)) * (Real.exp (Real.log 2 * (a * (1 + D))) *
          ((1 + D) * (1 + D)) * Real.exp (-κ' * D)) := by ring
    _ ≤ (C * (B * a * K₁) * (a * K₂)) * (Real.exp (Real.log 2 * (a * (1 + D))) *
          (Real.exp D * Real.exp D) * Real.exp (-κ' * D)) := by
        refine mul_le_mul_of_nonneg_left ?_ hP
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le)
          (Real.exp_pos _).le
    _ ≤ (C * (B * a * K₁) * (a * K₂)) * (Real.exp (Real.log 2 * a) * Real.exp (-rate' * D)) :=
        mul_le_mul_of_nonneg_left hexp hP
    _ = _ := by ring

/-- **The re-expanded old boundary terms as boundary terms of scale `k + 1`** (P6 (4.32)–(4.34);
LFR Lemma IV.1.5 (iii)): at a history `𝔸`, an output label `Y` and fields `(ψ, ψ', h, g)`, the old
part `oldBAt` of the step on the region history of `𝔸` at the field `ψ`, with the old labels
`oldDoms` of the record, the second field `ψ'`, the external field `g`, the assignment `cb 𝔸 ψ` of the
cubes of `Ω_{k+1}` to the integration variables and the interaction `I 𝔸 ψ ψ' g` of the measure
(the field `h` enters through `hv`, the external field of (D7), `hSetB hv = {hC hv}`). -/
noncomputable def oldB {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ)
    (inner : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N),
      Finset (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N), inner A ψ →
      CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
        (d7Pull F (k + 1) (OmegaCube A.H (k + 1))))
    (hp : 0 < p₁)
    (I : ∀ (A : LabHist S n R k0 K) (ψ _ : MultiFieldC S n M K N) (_ : GIdx S n M K N → ℂ),
      LocInteraction (fun b => {u : inner A ψ // cb A ψ u = b} → Rn N))
    (ψout : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N),
      (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) (rψ : ℝ)
    (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (hv : EuclideanSpace ℝ (Fin N)) :
    BTerms S n R k0 K M N (k + 1) :=
  fun A Y ψ ψ' _ gx => oldBAt g hnn hM1 F A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (inner A ψ) (cb A ψ)
    hp (I A ψ ψ' gx) (ψout A ψ) rψ ρc ρ r r' rep A (oldDoms F A.H k) ψ' hv gx Y

/-- **The (D7) bound of the re-expanded old boundary terms** (P6 (4.34); LFR Lemma IV.1.5 (iii)): at a
history `𝔸` of the record, an output label `Y` and a field `p` in the H7 domain of scale `k + 1` at the
fine set of `Y`, with `κ' ≥ rate' + c₁ log 2 + 2`,
`|oldB(𝔸, Y)| ≤ 2^{c₁} C_PE fac C_res L^d c₁ K₀(rate-κ_X) c₁ K₀(κ₀) e^{-rate' d^pre_{k+1}(Y)}`.
Conditional on `H7MixedInnerLoc`, `H7MixedDatumLoc`, `OldResumSite`. -/
theorem norm_oldB_le {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ}
    (hk : k + 1 ≤ K) {cs : OpConsts} {P : BudgetConsts} {rep : Rep S n R k0 K M N g cs P k}
    {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))} {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ}
    {hv : EuclideanSpace ℝ (Fin N)}
    (hrec : D7BdryPost Fr hnn (Nat.le_of_succ_le hk) rep Zof aw μs ε ε1 νs fac rate hv)
    {A : LabHist S n R k0 K} (hA : A ∈ rep.hist) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊)
    (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {c BG δb δc κ κ₁ rψ : ℝ}
    (hS : Dec2.DecSpecs S.d S.L (Dec2.mixedKc S.d S.L) (Cchi S.d S.L) c BG)
    (HB : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν)
    (hm₁ : 2 ≤ m₁) (hN : 5 < g.c * n (k + 1)) (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁)
    (hag : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1))
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) (hκ : 0 < κ)
    (hMc : c * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX S.d S.L (Cchi S.d S.L) * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hδ0 : 0 < δb) (hε : δb ≤ bgC0 S.d S.L N) (hδ : δb ≤ c7 S.d S.L N BG κ)
    (hphi : 3 * δb + K4 S.d S.L N BG κ * δb < 1 / 2)
    (hmarD : K4 S.d S.L N BG κ * δb + 2 * δb +
      K4 S.d S.L N BG κ * δb * (K4 S.d S.L N BG κ * δb + 2 * (1 + 3 * δb)) < δc)
    (hαD : K4 S.d S.L N BG κ * δb < coerciveConst S.d / 2)
    (hsm : δc ^ 2 * smallConstX S.d S.L κ ≤ 1 / 4) (hκ₁ : 1 ≤ κ₁) (hκ₁κ : κ₁ ≤ κ) (ρ r r' : ℕ)
    (hIn : H7MixedInnerLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r aw μs
      ε ε1 νs (hC hv) (Real.exp κ₁) rψ)
    (hDat : H7MixedDatumLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs (hC hv) ν δb)
    (hXs : ∀ X ∈ oldDoms Fr A.H k, X ∈ bdryDomsPost Fr A k (Zof A))
    (Y : Finset (Torus S.d (n (k + 1)))) (p : FinFieldC S n M K N × FinFieldC S n M K N ×
      (GIdx S n M K N → ℂ))
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) (k + 1) hk
      (fineSet (S := S) (n := n) M K (k + 1) (Y : Set (Torus S.d (n (k + 1))))) aw μs ε ε1 νs
      (hC hv) (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)))
    (inner : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N),
      Finset (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N), inner A ψ →
      CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
        (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))))
    (hcb : ∀ u : inner A (extK p.1), toFrame g hnn hM1 Fr hk
      (unitRep (u : (holeStepLF g hnn hM1 A.H hk hk1 hρ (extK p.1) z h₀ a₁ ν β p₁ δ).U)) ∈
        Localization.box (cb A (extK p.1) u).1 (cellSide S.L m₀ m₁ (k + 1)))
    (hp : 0 < p₁)
    (I : ∀ (A : LabHist S n R k0 K) (ψ _ : MultiFieldC S n M K N) (_ : GIdx S n M K N → ℂ),
      LocInteraction (fun b => {u : inner A ψ // cb A ψ u = b} → Rn N))
    (ψout : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N),
      (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ)
    (hrψ : 0 < rψ) (hfac : 0 < fac) {κX κV Cres rate' : ℝ}
    (hres : OldResumSite g hnn hM1 Fr A.H hk hρ r r' κ₁ κX κV Cres) (hCres : 0 < Cres)
    (hκV : (I A (extK p.1) (extK p.2.1) p.2.2).κH ≤ κV) (hαX : aEnt S.d S.L + 1 ≤ rate - κX)
    (hκ' : rate' + Real.log 2 * c1 S.d S.L + 2 ≤ (I A (extK p.1) (extK p.2.1) p.2.2).κ') :
    ‖oldB g hnn hM1 Fr hk hk1 hρ z h₀ a₁ ν β p₁ δ inner cb hp I ψout rψ
        (rho4 S.d S.L N BG κ) ρ r r' rep hv A Y (extK p.1) (extK p.2.1) (hC hv) p.2.2‖ ≤
      Real.exp (Real.log 2 * c1 S.d S.L) *
        (CPE S.d S.L ((I A (extK p.1) (extK p.2.1) p.2.2).Kc + 1)
          (I A (extK p.1) (extK p.2.1) p.2.2).κH (I A (extK p.1) (extK p.2.1) p.2.2).κ0
          (I A (extK p.1) (extK p.2.1) p.2.2).κ' * (fac * Cres)) *
        ((S.L : ℝ) ^ S.d * c1 S.d S.L * K0 S.d S.L (rate - κX)) *
        (c1 S.d S.L * K0 S.d S.L (I A (extK p.1) (extK p.2.1) p.2.2).κ0) *
        Real.exp (-rate' * d7SizePre Fr A (k + 1) Y) := by
  have h := norm_oldBAt_le g hnn hM1 hk hrec hA hk1 hρ z h₀ a₁ ν β p₁ δ hS HB hm₁ hN hM hag ha₁ ha₂ hκ hMc hMX hδ0 hε hδ hphi hmarD hαD hsm hκ₁ hκ₁κ ρ r r' hIn hDat (Xs := oldDoms Fr A.H k)
    (fun X hX => ⟨hXs X hX, hX⟩) Y htgt (inner A (extK p.1)) (cb A (extK p.1)) hcb hp
    (I A (extK p.1) (extK p.2.1) p.2.2) (ψout A (extK p.1)) hrψ hfac hres hCres hκV hαX
  have hCPE : 0 ≤ CPE S.d S.L ((I A (extK p.1) (extK p.2.1) p.2.2).Kc + 1)
      (I A (extK p.1) (extK p.2.1) p.2.2).κH (I A (extK p.1) (extK p.2.1) p.2.2).κ0
      (I A (extK p.1) (extK p.2.1) p.2.2).κ' := by
    have := one_le_c1 S.d S.L
    unfold CPE
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith))
      (Real.exp_pos _).le
  refine h.trans ?_
  exact exp_poly_le_exp (by linarith [one_le_c1 S.d S.L]) (mul_nonneg hCPE (by positivity))
    (by positivity) (K0_pos _ _ _).le (K0_pos _ _ _).le
    (d7SizeAt_nonneg Fr (k + 1) (OmegaCube A.H (k + 1)) Y) hκ'

end Bound

end Balaban.RootFSpine
