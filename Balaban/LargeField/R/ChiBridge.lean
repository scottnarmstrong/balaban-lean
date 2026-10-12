module

public import Balaban.LargeField.Characteristic.Functions
public import Balaban.LargeField.Characteristic.Stencil
public import Balaban.LargeField.LF1.BlockArith
public import Balaban.LargeField.R.SmallFactorOne
public import Balaban.Background.Theorem52
public import Balaban.Background.Theorem73
public import Balaban.Background.Def5
public import Balaban.Background.CompositionEstimates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# From small-field data to the regularity predicate (Part II, Lemma II.3.3 in contrapositive form)

If the block field `ψ_q` lies in `Ψ̃(T; θ)` on the blocks of the data sites of a generating set `G`
(massless, `μ = 0`), then the data `lift_q ψ_q` lie in the real domain `Ψ̃(𝔹_q; 3θ)`, and by BG
Theorem 5.2 (3) (`bg_real`) the small solution satisfies every inequality of Definition II.3.1
with `δ` as soon as `K₁ · 3θ < δ`.

* `jBlock_adj_or`: sites at distance `1` lie in the same block or in adjacent blocks;
* `inDomainR_liftSingle`: `Ψ̃(T; θ)` for the block field gives `InDomainR G 0 (3θ)`;
* `reg_of_inDomainR`: `InDomainR G 0 δ'` with `K₁ δ' < δ` gives `Reg G a 0 D δ S S` for `S ⊂ Ω_q`;
* `chiK_eq_one_of_psiTilde`: the cube characteristic function `χ_q(□)` equals `1`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

set_option linter.unusedSectionVars false

section Blocks

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- Sites at distance one lie in the same `j`-block or in adjacent `j`-blocks. -/
theorem jBlock_adj_or {k j : ℕ} (hj : j ≤ k) {y y' : Torus d (N₀ * L ^ k)} (h : Adj y y') :
    jBlock d L N₀ k j y = jBlock d L N₀ k j y' ∨
      AdjT (jBlock d L N₀ k j y) (jBlock d L N₀ k j y') := by
  by_cases he : jBlock d L N₀ k j y = jBlock d L N₀ k j y'
  · exact Or.inl he
  · right
    refine ⟨he, ?_⟩
    obtain ⟨μ, hμ | hμ⟩ := h
    · refine ⟨μ, Or.inl ?_⟩
      subst hμ
      have := blockMap_add_single_cases (side_eq hj) y μ (t := 1) (by
        have : 1 ≤ L ^ j := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
        exact this)
      simp only [Nat.cast_one] at this
      rcases this with h | h
      · exact absurd h.symm (by simpa [jBlock] using he)
      · exact h
    · refine ⟨μ, Or.inr ?_⟩
      subst hμ
      have := blockMap_add_single_cases (side_eq hj) y' μ (t := 1) (by
        have : 1 ≤ L ^ j := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
        exact this)
      simp only [Nat.cast_one] at this
      rcases this with h | h
      · exact absurd h (by simpa [jBlock] using he)
      · exact h

theorem blockSet_jBlock (G : GeneratingSet d L N₀ q ϱ) {x y : Torus d (N₀ * L ^ q)}
    (hy : y ∈ blockSet G x) : jBlock d L N₀ q q y = jBlock d L N₀ q q x := by
  classical
  unfold blockSet at hy
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, ↓reduceIte] at hy
    obtain ⟨-, hk, -⟩ := G.layerIndex_spec hx
    exact jBlock_eq_of_le hk le_rfl (GeneratingSet.mem_blk.1 hy)
  · simp only [hx, ↓reduceIte] at hy
    rw [Finset.mem_singleton.1 hy]

theorem rn_toLp_eq (v : Fin N → ℝ) : rn v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold rn
  simp [sq_abs]

theorem sum_sq_toLp (v : Fin N → ℝ) :
    ∑ i, v i ^ 2 = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N))‖ ^ 2 := by
  rw [← rn_toLp_eq, rn_sq_sum]

/-- `ψ_q ∈ Ψ̃(T; θ)` on the blocks of the data sites puts the lifted data in the real domain
`Ψ̃(𝔹_q; 3θ)` (massless case). -/
theorem inDomainR_liftSingle (G : GeneratingSet d L N₀ q ϱ)
    (ψ : Torus d (N₀ * L ^ (q - q)) → Fin N → ℝ)
    (h : Fin N → ℝ) (T : Set (Torus d (N₀ * L ^ (q - q)))) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hT : ∀ x ∈ dataSites G, jBlock d L N₀ q q x ∈ T)
    (hψ : PsiTildeSet T (fun z => (WithLp.toLp 2 (ψ z) : EuclideanSpace ℝ (Fin N))) θ) :
    InDomainR G 0 (3 * θ)
      (liftSingle G (fun z i => (ψ z i : ℂ)) (fun i => (h i : ℂ))) := by
  refine ⟨blockLift q ψ, h, ⟨liftSingle_layerConst G ψ, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro x x' ⟨hx, hx', -, y, hy, y', hy', hadj⟩
    have e1 := blockSet_jBlock G hy
    have e2 := blockSet_jBlock G hy'
    rcases jBlock_adj_or le_rfl hadj with h | h
    · have : blockLift q ψ x = blockLift q ψ x' := by
        unfold blockLift; rw [← e1, ← e2, h]
      rw [this]
      have h0 : rn (fun i => blockLift q ψ x' i - blockLift q ψ x' i) = 0 := by simp [rn]
      linarith
    · rw [e1, e2] at h
      have := hψ.1 _ (hT x hx) _ (hT x' hx') h
      rw [rn_toLp_eq]
      have e : (WithLp.toLp 2 (fun i => blockLift q ψ x i - blockLift q ψ x' i) :
          EuclideanSpace ℝ (Fin N)) = WithLp.toLp 2 (ψ (jBlock d L N₀ q q x)) -
            WithLp.toLp 2 (ψ (jBlock d L N₀ q q x')) := rfl
      rw [e]
      linarith
  · intro x hx
    have := hψ.2 _ (hT x hx)
    have hs : ∑ i, blockLift q ψ x i ^ 2 =
        ‖(WithLp.toLp 2 (ψ (jBlock d L N₀ q q x)) : EuclideanSpace ℝ (Fin N))‖ ^ 2 :=
      sum_sq_toLp (ψ (jBlock d L N₀ q q x))
    rw [hs]
    set t := ‖(WithLp.toLp 2 (ψ (jBlock d L N₀ q q x)) : EuclideanSpace ℝ (Fin N))‖ with ht
    have ht0 : 0 ≤ t := norm_nonneg _
    have h1 : -θ < t - 1 := by have := (abs_lt.1 this).1; linarith
    have h2 : t - 1 < θ := (abs_lt.1 this).2
    rw [abs_lt]
    constructor <;> nlinarith
  · intro x hx; simp; positivity
  · simp; positivity
  · intro x hx i; simp [liftSingle_Ψ G _ _ hx, blockLift]
  · intro x hx i; simp [liftSingle_h G _ _ hx]


/-- **Regularity from small-field data** (BG Theorem 5.2 (3), massless): if the data lie in the real
domain `Ψ̃(𝔹_q; δ')` with `K₁ δ' < δ`, the small solution satisfies `Reg_q(G, D, δ; S, S)` for every
set `S` of sites of the top layer `Ω_q`. -/
theorem reg_of_inDomainR {G : GeneratingSet d L N₀ q ϱ} {a : ℕ → ℝ} (H : BgHyp d L q ϱ a 0)
    {δ' δ : ℝ} (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ bgC1 d L N) (hK : bgK1 d L N * δ' < δ)
    {D : BgData G N} (hD : InDomainR G 0 δ' D) (hq : 1 ≤ q) (S : Finset (Torus d (N₀ * L ^ q)))
    (hS : ∀ x ∈ S, x ∈ G.Ω q) : Reg G a 0 D δ S S := by
  obtain ⟨φ, α, hsol, hb, hu, -⟩ := bg_real H hδ'0 hδ'1 hD
  obtain ⟨e1, e2⟩ := bgFieldC_eq hsol hu
  have hlay : ∀ x ∈ S, x ∈ G.layer q := fun x hx =>
    G.mem_layer.2 ⟨hS x hx, by rw [G.top]; exact Finset.notMem_empty _⟩
  have hlq : ∀ x ∈ S, G.layerIndex x = q := fun x hx => G.layerIndex_eq hq le_rfl (hlay x hx)
  refine ⟨⟨δ', hδ'0, hδ'1, hD⟩, ?_, ?_, ?_⟩
  · rw [e1]
    intro x hx
    have hx1 : x ∈ G.layer q := hlay x hx
    unfold blockDev blockAvg
    rw [hlq x hx]
    have hc : ∀ y ∈ G.blk q x, (vn fun i => svec G φ y i - D.Ψ x i) ≤ bgK1 d L N * δ' := by
      intro y hy
      have hy1 : y ∈ G.Ω 1 := G.layer_subset hq le_rfl ((G.mem_layer_iff hq le_rfl (GeneratingSet.mem_blk.1 hy)).2 hx1)
      have hΨ : D.Ψ y = D.Ψ x := D.Ψ_layerConst q hq le_rfl x hx1 y hy
      have := hb.val ⟨y, hy1⟩
      have e : (fun i => svec G φ y i - D.Ψ x i) = fun i => φ (⟨y, hy1⟩, i) - D.Ψ y i := by
        funext i; rw [hΨ]; exact congrArg (· - D.Ψ x i) (svec_of_mem' φ hy1 i)
      rw [e]; exact this
    have h2 := vn_blockMean_sub_le (G := G) (n := q) le_rfl (fun y i => svec G φ y i) x (D.Ψ x) hc
    have e3 : (fun i => D.Ψ x i - blockMean G q (fun y => svec G φ y i) x) =
        fun i => -(blockMean G q (fun y => svec G φ y i) x - D.Ψ x i) := by
      funext i; ring
    show (vn fun i => D.Ψ x i - blockMean G q (fun y => svec G φ y i) x) < δ
    rw [e3, vn_neg]
    linarith
  · rw [e1, e2]
    intro x hx
    have hx' : (x : Torus d (N₀ * L ^ q)) ∈ G.layer q := hlay _ hx
    have hsp : G.spacing (x : Torus d (N₀ * L ^ q)) = (L : ℝ) ^ q := G.spacing_eq hq le_rfl hx'
    have hLp : (0 : ℝ) < (L : ℝ) ^ q := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    have hc0 : 0 ≤ bgK1 d L N * δ' := by
      have := bgK1_pos d L N
      positivity
    have key : ∀ (v c ℓ : ℝ), 0 < ℓ → v ≤ c / ℓ → ℓ * v ≤ c := fun v c ℓ hℓ h => by
      have := (le_div_iff₀ hℓ).1 h
      linarith [mul_comm ℓ v]
    refine ⟨fun μ => ?_, ?_, ?_⟩
    · obtain ⟨g1, g2⟩ := hb.grad x μ
      rw [hsp] at g1 g2
      exact ⟨by have := key _ _ _ hLp g1; exact lt_of_le_of_lt this hK,
        by have := key _ _ _ hLp g2; exact lt_of_le_of_lt this hK⟩
    · have g := hb.lap x
      rw [hsp] at g
      have e : barLap G D φ x = fun i => ∑ μ : Fin d,
          (barField G D.Ψ φ ((x : Torus d (N₀ * L ^ q)) + Pi.single μ 1) i +
            barField G D.Ψ φ ((x : Torus d (N₀ * L ^ q)) - Pi.single μ 1) i -
            2 * barField G D.Ψ φ x i) := by
        funext i
        simp only [barLap, LargeField.barVec, Finset.sum_apply, Pi.add_apply, Pi.sub_apply, nsmul_eq_mul]
        simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ]; rfl
      rw [e]
      exact lt_of_le_of_lt (key _ _ _ (by positivity) g) hK
    · have g := hb.alpha x
      rw [hsp] at g
      exact lt_of_le_of_lt g hK
  · intro h0
    simp at h0

end Blocks


section Cube

variable {d M1 N₁ L N q c n : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] [NeZero n]

/-- The top layer of `G_q(□) = 𝔹_q(□^{∼2})` is the fine set of `□^{∼2}`. -/
theorem genCube_top_eq (hm : N₁ * L ^ (q - q) = c * n) (y0 : Torus d n) :
    (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0).Ω q =
      cubePre M1 N₁ L q (L ^ q * (c * M1)) n (nbhd 2 {y0}) := by
  rw [genCube_Ω, minLayer_self,
    (isCubeUnion_cubePre (M1 := M1) (N₁ := N₁) (L := L) (q := q) (le_refl q) hm
      (nbhd 2 {y0})).cubeInterior_eq]

/-- The fine set of `□^{∼1}` lies in the top layer of `G_q(□)`. -/
theorem cubeNbhd_one_subset (hm : N₁ * L ^ (q - q) = c * n) (y0 : Torus d n) :
    ∀ x ∈ cubeNbhd M1 N₁ L q c n 1 y0,
      x ∈ (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0).Ω q := by
  intro x hx
  rw [genCube_top_eq hm, mem_cubePre]
  unfold cubeNbhd at hx
  rw [mem_cubePre] at hx
  exact nbhd_mono (by norm_num) (fun _ h => h) hx

/-- **`χ_q(□) = 1` from small-field data** (BG Theorem 5.2 (3); Lemma III.5.3 (b)): if
`ψ_q ∈ Ψ̃(T; θ)` on a set `T` of blocks containing the blocks of the data sites of `G_q(□)`, with
`θ ≤ 1`, `3θ ≤ c₁` and `K₁ · 3θ < δ`, then `χ_q(□) = 1` (massless case `μ = 0`). -/
theorem chiK_eq_one_of_psiTilde {a : ℕ → ℝ} (H : BgHyp d L q (minSep L M1) a 0) (hq : 1 ≤ q)
    (hm : N₁ * L ^ (q - q) = c * n) (δ : ℝ) (h : Fin N → ℝ) (y0 : Torus d n)
    (ψ : BlockCfg d (M1 * N₁) L q q N) (T : Set (Torus d (M1 * N₁ * L ^ (q - q)))) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (h3 : 3 * θ ≤ bgC1 d L N) (hK : bgK1 d L N * (3 * θ) < δ)
    (hT : ∀ x ∈ dataSites (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0),
      jBlock d L (M1 * N₁) q q x ∈ T)
    (hψ : PsiTildeSet T (fun z => (WithLp.toLp 2 (ψ z) : EuclideanSpace ℝ (Fin N))) θ) :
    chiK (M1 := M1) (N₁ := N₁) (L := L) (q := q) (N := N) a 0 δ h c n y0 ψ = 1 := by
  refine charFn_eq_one ?_
  unfold ChiKProp cubeData
  exact reg_of_inDomainR H (by positivity) h3 hK
    (inDomainR_liftSingle _ ψ h T hθ0 hθ1 hT hψ) hq _ (cubeNbhd_one_subset hm y0)


/-- If `ψ_q ∈ Ψ̃(T_q(X); θ)` on the blocks inside a union `X` of `q`-blocks containing the data
sites of `G_q(□)`, then `χ_q(□) = 1`; contrapositive: `χ_q(□) = 0` gives a violation of
`Ψ̃(T_q(X); θ)`. -/
theorem not_psiTilde_of_chiK_eq_zero {a : ℕ → ℝ} (H : BgHyp d L q (minSep L M1) a 0) (hq : 1 ≤ q)
    (hm : N₁ * L ^ (q - q) = c * n) (δ : ℝ) (h : Fin N → ℝ) (y0 : Torus d n)
    (ψ : BlockCfg d (M1 * N₁) L q q N) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (h3 : 3 * θ ≤ bgC1 d L N) (hK : bgK1 d L N * (3 * θ) < δ)
    {X : Finset (Site d L (M1 * N₁) q)} (hXq : IsBlockUnion L (M1 * N₁) q q X)
    (hX : ∀ x ∈ dataSites (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0), x ∈ X)
    (hχ : chiK (M1 := M1) (N₁ := N₁) (L := L) (q := q) (N := N) a 0 δ h c n y0 ψ = 0) :
    ¬ PsiTildeSet {y : Blk d L (M1 * N₁) q q | fib d L (M1 * N₁) q q y ⊆ X}
      (fun z => (WithLp.toLp 2 (ψ z) : EuclideanSpace ℝ (Fin N))) θ := by
  intro hψ
  have hT : ∀ x ∈ dataSites (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0),
      jBlock d L (M1 * N₁) q q x ∈ {y : Blk d L (M1 * N₁) q q | fib d L (M1 * N₁) q q y ⊆ X} := by
    intro x hx x' hx'
    have hx'' : jBlock d L (M1 * N₁) q q x' = jBlock d L (M1 * N₁) q q x := by
      exact (Finset.mem_filter.1 hx').2
    exact (hXq x' x hx'').2 (hX x hx)
  have := chiK_eq_one_of_psiTilde H hq hm δ h y0 ψ _ hθ0 hθ1 h3 hK hT hψ
  rw [hχ] at this
  exact zero_ne_one this


/-- **The bridge** "a product of cube characteristic functions vanishes `⇒` a violation of `Ψ̃`
of size `δ/(6K₁)`" (Lemma III.5.3 (b), (e)): if `χ_q(□) = 0` for one of the cubes `□ ∈ A`, with the
data sites of `G_q(□)` in the union `X` of `q`-blocks, `K₁ ≥ bgK1`, then
`ψ_q ∉ Ψ̃(T_q(X); δ/(6K₁))`.  The size conditions are the constants of the source:
`δ ≤ 6K₁` (so `θ ≤ 1`) and `δ ≤ 2K₁c₁` (the data lie in `𝒟_ℝ`, (Λ17)). -/
theorem not_psiTilde_of_cubeProd_eq_zero {a : ℕ → ℝ} (H : BgHyp d L q (minSep L M1) a 0)
    (hq : 1 ≤ q) (hm : N₁ * L ^ (q - q) = c * n) {δ K1 : ℝ} (hδ : 0 < δ) (hK1 : 0 < K1)
    (hK1b : bgK1 d L N ≤ K1) (hδ1 : δ ≤ 6 * K1) (hδc : δ ≤ 2 * K1 * bgC1 d L N)
    (h : Fin N → ℝ) (A : Finset (Torus d n)) (ψ : BlockCfg d (M1 * N₁) L q q N)
    {X : Finset (Site d L (M1 * N₁) q)} (hXq : IsBlockUnion L (M1 * N₁) q q X)
    (hX : ∀ y0 ∈ A, ∀ x ∈ dataSites (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0),
      x ∈ X)
    (hχ : cubeProd (fun y0 => chiK (M1 := M1) (N₁ := N₁) (L := L) (q := q) (N := N) a 0 δ h c n y0)
      A ψ = 0) :
    ¬ PsiTildeSet {y : Blk d L (M1 * N₁) q q | fib d L (M1 * N₁) q q y ⊆ X}
      (fun z => (WithLp.toLp 2 (ψ z) : EuclideanSpace ℝ (Fin N))) (δ / (6 * K1)) := by
  unfold cubeProd at hχ
  obtain ⟨y0, hy0, hz⟩ := Finset.prod_eq_zero_iff.1 hχ
  have hθ0 : 0 < δ / (6 * K1) := by positivity
  have hθ1 : δ / (6 * K1) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hδ1
  have h3 : 3 * (δ / (6 * K1)) ≤ bgC1 d L N := by
    have : 3 * (δ / (6 * K1)) = δ / (2 * K1) := by field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]
    linarith
  have hK : bgK1 d L N * (3 * (δ / (6 * K1))) < δ := by
    have : 3 * (δ / (6 * K1)) = δ / (2 * K1) := by field_simp; ring
    rw [this]
    have hb : bgK1 d L N * (δ / (2 * K1)) ≤ K1 * (δ / (2 * K1)) :=
      mul_le_mul_of_nonneg_right hK1b (by positivity)
    have : K1 * (δ / (2 * K1)) = δ / 2 := by field_simp
    linarith
  exact not_psiTilde_of_chiK_eq_zero H hq hm δ h y0 ψ hθ0 hθ1 h3 hK hXq (hX y0 hy0) hz

end Cube

section SmallFactors

variable {d M1 N₁ L k Nspin c n : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] [NeZero n] {ϱ : ℝ}

/-- The functions `ψ_k` of the multiscale field as a real block configuration. -/
theorem toLp_ofLp_fun (ψ : Blk d L (M1 * N₁) k k → EuclideanSpace ℝ (Fin Nspin)) :
    (fun z => (WithLp.toLp 2 (fun i => ψ z i) : EuclideanSpace ℝ (Fin Nspin))) = ψ := by
  funext z; simp

/-- **Lemma III.5.3 (b), `ϰ₂`** (level-torus form): if `χ_S = ∏ χ_k(□) = 0` over the cubes `□ ∈ A`
with `□^{∼3} ⊂ Xc = Z^c_0 ∩ Z` (as fine sets), then
`𝒢^♮ + β_kA^*_k(X_win, 𝔹_k; ψ, φ) ≥ γ₂`, the left side being `𝒢^♮ + 𝒜_win + C_{k₁,k}` by (2.15′).
The bridge is `not_psiTilde_of_cubeProd_eq_zero` (BG Theorem 5.2 (3), `bg_real`); the data sites
of `G_k(□)` lie in `□^{∼3}` (`dataSites_genCube_near`), and `□^{∼3} ⊂ Z^c_0 ∩ Z` is Lemma III.5.0
(a), the hypothesis `hgeo`. -/
theorem smallFactor_two (P : SmallFactorPar) (G : GeneratingSet d L (M1 * N₁) k ϱ) (hk : 1 ≤ k)
    (hL : 2 ≤ L) (hd : 2 ≤ d) (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hadm : IsAdmissibleWeights k (compWeight L a₁)) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {Xc Xwin : Finset (Site d L (M1 * N₁) k)} (hXc : Xc ⊆ Xwin)
    (hXΩ : ∀ s ∈ Xc, s ∈ G.Ω 1 ∧ s ∉ G.Ω k) (hXk : IsBlockUnion L (M1 * N₁) k k Xc)
    (hX : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L (M1 * N₁) k n (Xc ∩ G.layer n))
    (ψ : (m : ℕ) → Blk d L (M1 * N₁) k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L (M1 * N₁) k → EuclideanSpace ℝ (Fin Nspin)) (hφ : ∀ x ∈ Xc, ‖φ x‖ = 1)
    {βk : ℝ} (hβ : 0 ≤ βk) (ϖ : ℕ → ℝ) (aN : Blk d L (M1 * N₁) k k → ℝ) (hη0 : 0 ≤ P.eta)
    (hη : P.eta ≤ 1 / 2)
    (haN : ∀ z ∈ tBlocks d L (M1 * N₁) k k Xc,
      |aN z - compWeightZ G a₁ z| ≤ P.eta * compWeightZ G a₁ z)
    {Mψ Sig Nbl : ℝ} (hM : ∀ s ∈ Xc, ‖leafField G ψ s‖ ≤ Mψ)
    (hSig : ∀ z ∈ tBlocks d L (M1 * N₁) k k Xc, Real.sqrt βk * varsigmaBar G ϖ z ≤ Sig)
    (hN : ((tBlocks d L (M1 * N₁) k k Xc).card : ℝ) ≤ Nbl) (hΛ19 : 8 * Sig ^ 2 * Nbl * Mψ ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hK1 : 0 < P.K1) (hγ0 : P.gamma0 = gamma0 d)
    (hβδ : βk * δ ^ 2 = P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a)
    (hK1b : bgK1 d L Nspin ≤ P.K1) (hδ1 : δ ≤ 6 * P.K1) (hδc : δ ≤ 2 * P.K1 * bgC1 d L Nspin)
    {aχ : ℕ → ℝ} (H : BgHyp d L k (minSep L M1) aχ 0) (hm : N₁ * L ^ (k - k) = c * n)
    (A : Finset (Torus d n))
    (hc : 12 ≤ c)
    (hgeo : ∀ y0 ∈ A, ∀ x : Site d L (M1 * N₁) k,
      blockMap (L ^ k * (c * M1)) n x ∈ nbhd 3 {y0} → x ∈ Xc)
    (hχ : cubeProd (fun y0 => chiK (M1 := M1) (N₁ := N₁) (L := L) (q := k) (N := Nspin) aχ 0 δ
      (fun i => h i) c n y0) A (fun z i => ψ k z i) = 0) :
    P.gamma2 ≤ composedGauss G βk aN ϖ ψ Xc +
      multiAction G (compWeight L a₁) βk μ h Xwin ψ φ := by
  have hv := not_psiTilde_of_cubeProd_eq_zero (N := Nspin) H hk hm hδ hK1 hK1b hδ1 hδc
    (fun i => h i) A (fun z i => ψ k z i) hXk
    (fun y0 hy0 x hx => hgeo y0 hy0 x (dataSites_genCube_near hL hc hm y0 hx)) hχ
  rw [toLp_ofLp_fun] at hv
  exact smallFactor_two_gamma2 P G hk hL hd hϱ ha₁ hadm hμ h hXc hXΩ hXk hX ψ φ hφ hβ ϖ aN hη0 hη
    haN hM hSig hN hΛ19 hδ.le hK1 hγ0 hβδ hv

/-- **Lemma III.5.3 (e), `ϰ₅`** (level-torus form): if `χ_{Z''} = ∏ χ_k(□) = 0` over the cubes
`□ ∈ A` with `□^{∼3} ⊂ X = Z` (as fine sets), then
`β_kA^*_k(Z; ψ_k, φ) ≥ γ₅` for the single-scale action. -/
theorem smallFactor_five (P : SmallFactorPar) (hk : 1 ≤ k) (hd : 2 ≤ d) (hL : 2 ≤ L)
    (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {X : Finset (Site d L (M1 * N₁) k)}
    (hXk : IsBlockUnion L (M1 * N₁) k k X)
    (ψ : (m : ℕ) → Blk d L (M1 * N₁) k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L (M1 * N₁) k → EuclideanSpace ℝ (Fin Nspin)) (hφ : ∀ x ∈ X, ‖φ x‖ = 1) {βk : ℝ}
    (hβ : 0 ≤ βk) {δ : ℝ} (hδ : 0 < δ) (hK1 : 0 < P.K1) (hγ0 : P.gamma0 = gamma0 d)
    (hβδ : βk * δ ^ 2 = P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a)
    (hK1b : bgK1 d L Nspin ≤ P.K1) (hδ1 : δ ≤ 6 * P.K1) (hδc : δ ≤ 2 * P.K1 * bgC1 d L Nspin)
    {aχ : ℕ → ℝ} (H : BgHyp d L k (minSep L M1) aχ 0) (hm : N₁ * L ^ (k - k) = c * n)
    (A : Finset (Torus d n))
    (hc : 12 ≤ c)
    (hgeo : ∀ y0 ∈ A, ∀ x : Site d L (M1 * N₁) k,
      blockMap (L ^ k * (c * M1)) n x ∈ nbhd 3 {y0} → x ∈ X)
    (hχ : cubeProd (fun y0 => chiK (M1 := M1) (N₁ := N₁) (L := L) (q := k) (N := Nspin) aχ 0 δ
      (fun i => h i) c n y0) A (fun z i => ψ k z i) = 0) :
    P.gamma5 ≤ multiAction (singleGen d L (M1 * N₁) k ϱ) a βk μ h X ψ φ := by
  have hv := not_psiTilde_of_cubeProd_eq_zero (N := Nspin) H hk hm hδ hK1 hK1b hδ1 hδc
    (fun i => h i) A (fun z i => ψ k z i) hXk
    (fun y0 hy0 x hx => hgeo y0 hy0 x (dataSites_genCube_near hL hc hm y0 hx)) hχ
  rw [toLp_ofLp_fun] at hv
  exact smallFactor_five_gamma5 P hk hd hL hϱ ha hμ h hXk ψ φ hφ hβ hδ.le hK1 hγ0 hβδ hv

end SmallFactors

end Balaban.LargeField
