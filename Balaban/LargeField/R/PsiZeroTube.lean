/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroBlocks
public import Balaban.LargeField.R.PsiZeroChain
public import Balaban.LargeField.R.ZeroDomainRef

/-!
# The tube `Ψ̃(X; δ)` around the reference vector (Lemma III.3.3, geometry of the solution set)

For a box `Z₀` of `k`-blocks with its layer `shellOut`, inside `Ω_k(G)`:

* `close_of_tube`: a block field in `Ψ̃(X; κ)` that agrees with `ψ_k ∈ Ψ̃(X ∖ Z₀; δ)` off `Z₀` is within
  `D κ + (12 d (D+2) + 3) δ` of `ψ₀ = refVec ψ_k Z₀` on `Z₀` (chain of at most `D` steps to the layer, then
  Lemma III.3.5);
* `tube_of_close`: the converse, a field within `r` of `ψ₀` on `Z₀` lies in `Ψ̃(X; δ')`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Tube

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)

/-- A real vector of `Fin N → ℝ` as an element of Euclidean space. -/
def eu (v : Fin N → ℝ) : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 v

theorem norm_eu (v : Fin N → ℝ) : ‖eu v‖ = rn v := by
  simp [eu, EuclideanSpace.norm_eq, rn]

theorem eu_sub (v w : Fin N → ℝ) : eu v - eu w = eu (fun i => v i - w i) := rfl

/-- The blocks of a set `Z` of `k`-blocks lie over `Ω_k(G)`. -/
def OverTop (Z : Set (Torus d (N₀ * L ^ (k - k)))) : Prop :=
  ∀ x, jBlock d L N₀ k k x ∈ Z → x ∈ G.Ω k

variable {G}

theorem tube_R1 {X : Set (Torus d (N₀ * L ^ (k - k)))} {κ : ℝ} {ψ : BlockField d L N₀ k N}
    (ht : TubeOn G X κ ψ) (hk : 1 ≤ k) {y y' : Torus d (N₀ * L ^ (k - k))} (hy : y ∈ X) (hy' : y' ∈ X)
    (hadj : torusAdj y y') (hΩ : OverTop G {y, y'}) : ‖eu (ψ y) - eu (ψ y')‖ < κ := by
  obtain ⟨x, x', hp, hx, hx'⟩ := exists_interface_pair G hk hadj
    (fun x hx => hΩ x (by rcases hx with h | h <;> simp [h]))
  have := ht.1 x x' hp (hx ▸ hy) (hx' ▸ hy')
  rw [eu_sub, norm_eu]
  simpa [liftR, hx, hx'] using this

theorem tube_R2 {X : Set (Torus d (N₀ * L ^ (k - k)))} {κ : ℝ} {ψ : BlockField d L N₀ k N}
    (ht : TubeOn G X κ ψ) {y : Torus d (N₀ * L ^ (k - k))} (hy : y ∈ X) (hΩ : OverTop G {y}) (hk : 1 ≤ k) :
    |‖eu (ψ y)‖ - 1| < κ := by
  obtain ⟨x, hx⟩ := Balaban.exists_blockMap_eq (fine_eq_block L N₀ k) (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k) y
  have hxΩ : x ∈ G.Ω k := hΩ x (by simp [jBlock, hx])
  have hds : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl (G.Ω_antitone le_rfl hk (by omega) hxΩ))
  have h := ht.2 x hds (by simpa [jBlock, hx] using hy)
  have hjy : jBlock d L N₀ k k x = y := hx
  rw [hjy] at h
  have e : ∑ i, ψ y i ^ 2 = ‖eu (ψ y)‖ ^ 2 := by
    simp [eu, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rw [e] at h
  have hn : 0 ≤ ‖eu (ψ y)‖ := norm_nonneg _
  have : |‖eu (ψ y)‖ - 1| ≤ |‖eu (ψ y)‖ ^ 2 - 1| := by
    have : ‖eu (ψ y)‖ ^ 2 - 1 = (‖eu (ψ y)‖ - 1) * (‖eu (ψ y)‖ + 1) := by ring
    rw [this, abs_mul, abs_of_pos (by linarith : 0 < ‖eu (ψ y)‖ + 1)]
    nlinarith [abs_nonneg (‖eu (ψ y)‖ - 1)]
  linarith

theorem torusAdj_supDist {m : ℕ} [NeZero m] {y y' : Torus d m} (h : torusAdj y y') : supDist y' y ≤ 1 := by
  obtain ⟨μ, h | h⟩ := h
  · rw [h]; exact supDist_add_single_le y μ
  · rw [supDist_comm, h]; exact supDist_add_single_le y' μ

/-- A block adjacent to a box block and outside the box lies in the layer of the box. -/
theorem mem_shellOut_of_adj {m : ℕ} [NeZero m] {Z : Set (Torus d m)} {y y' : Torus d m} (hy : y ∈ Z)
    (hy' : y' ∉ Z) (h : torusAdj y y') : y' ∈ shellOut Z := ⟨hy', y, hy, torusAdj_supDist h⟩

variable [NeZero N]

/-- **Lemma III.3.5 for the tube**: if `ψ_k ∈ Ψ̃(X ∖ Z₀; δ)` for a box `Z₀`, then `ψ_k` is within
`(12 d (D+2) + 3) δ` of `ψ₀ = refVec ψ_k Z₀` on the layer of the box. -/
theorem shell_close {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
    (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
    {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w))) {δ : ℝ}
    {ψk : BlockField d L N₀ k N} (hψk : TubeOn G (X \ box b0 w) δ ψk) :
    ∀ z' ∈ shellOut (box b0 w),
      ‖eu (ψk z') - refVec (fun z => eu (ψk z)) (box b0 w)‖ < (12 * d * (D + 2) + 3) * δ := by
  have hd0 : 0 < d := by omega
  have hRegΩ : ∀ y, y ∈ box b0 w ∪ shellOut (box b0 w) → OverTop G {y} := fun y hy x hx =>
    hΩ x (by rw [Set.mem_singleton_iff.1 hx]; exact hy)
  have hpairΩ : ∀ y y', y ∈ box b0 w ∪ shellOut (box b0 w) → y' ∈ box b0 w ∪ shellOut (box b0 w) →
      OverTop G {y, y'} := fun y y' hy hy' x hx => by
    rcases Set.mem_insert_iff.1 hx with h | h
    · exact hΩ x (h ▸ hy)
    · exact hΩ x (by rw [Set.mem_singleton_iff.1 h]; exact hy')
  intro z' hz'
  refine refVec_close hd b0 w hw1 hwD hm (fun z => eu (ψk z)) ?_ ?_ hz'
  · intro x μ hx hx'
    have hxX : x ∈ X \ box b0 w := ⟨hXreg (Or.inr hx), hx.1⟩
    have hx'X : x + Pi.single μ 1 ∈ X \ box b0 w := ⟨hXreg (Or.inr hx'), hx'.1⟩
    have := tube_R1 hψk hk hxX hx'X ⟨μ, Or.inl rfl⟩ (hpairΩ _ _ (Or.inr hx) (Or.inr hx'))
    rw [norm_sub_rev]
    have hδ : 0 < δ := by
      have := norm_nonneg (eu (ψk x) - eu (ψk (x + Pi.single μ 1)))
      linarith
    linarith
  · intro x hx
    have hxX : x ∈ X \ box b0 w := ⟨hXreg (Or.inr hx), hx.1⟩
    have := tube_R2 hψk hxX (hRegΩ x (Or.inr hx)) hk
    have hδ : 0 < δ := lt_of_le_of_lt (abs_nonneg _) this
    linarith

/-- **Lemma III.3.3, the tube is close to `ψ₀`**: if a block field `ψ` agrees with `ψ_k` off a box `Z₀` of
sides `≤ D`, `ψ_k ∈ Ψ̃(X ∖ Z₀; δ)` and `ψ ∈ Ψ̃(X; κ)`, then `|ψ(z) - ψ₀| ≤ D κ + (12 d (D+2) + 3) δ` on `Z₀`
(`ψ₀ = refVec ψ_k Z₀`; chain of at most `D` steps from `z` to the layer of the box, then Lemma III.3.5). -/
theorem close_of_tube {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
    (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
    {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w))) {δ κ : ℝ} (hκ : 0 ≤ κ)
    {ψk ψ : BlockField d L N₀ k N} (hψk : TubeOn G (X \ box b0 w) δ ψk) (hψ : TubeOn G X κ ψ)
    (hag : ∀ z, z ∉ box b0 w → ψ z = ψk z) :
    ∀ z ∈ box b0 w, ‖eu (ψ z) - refVec (fun z => eu (ψk z)) (box b0 w)‖ ≤
      D * κ + (12 * d * (D + 2) + 3) * δ := by
  have hd0 : 0 < d := by omega
  have hsm : ∀ i, w i + 2 ≤ N₀ * L ^ (k - k) := fun i => (Nat.add_le_add_right (hwD i) 2).trans hm
  have hpairΩ : ∀ y y', y ∈ box b0 w ∪ shellOut (box b0 w) → y' ∈ box b0 w ∪ shellOut (box b0 w) →
      OverTop G {y, y'} := fun y y' hy hy' x hx => by
    rcases Set.mem_insert_iff.1 hx with h | h
    · exact hΩ x (h ▸ hy)
    · exact hΩ x (by rw [Set.mem_singleton_iff.1 h]; exact hy')
  have hshell := shell_close hd hk b0 w hw1 hwD hm hXreg hΩ hψk
  intro z hz
  obtain ⟨j, hj, hzj⟩ := hz ⟨0, hd0⟩
  obtain ⟨z', hz', hb⟩ := box_chain hd0 b0 w hsm (fun z => eu (ψ z)) hκ
    (fun y y' hy hy' hadj => (tube_R1 hψ hk (hXreg hy) (hXreg hy') hadj (hpairΩ y y' hy hy')).le)
    (w ⟨0, hd0⟩ - 1) z hz j hj hzj (by omega)
  have hw0 : (((w ⟨0, hd0⟩ - 1 : ℕ) : ℝ) + 1) = (w ⟨0, hd0⟩ : ℝ) := by
    have := hw1 ⟨0, hd0⟩
    have e : w ⟨0, hd0⟩ - 1 + 1 = w ⟨0, hd0⟩ := by omega
    exact_mod_cast e
  rw [hw0] at hb
  have hwD' : (w ⟨0, hd0⟩ : ℝ) ≤ D := by exact_mod_cast hwD _
  have h1 : ‖eu (ψ z') - refVec (fun z => eu (ψk z)) (box b0 w)‖ <
      (12 * d * (D + 2) + 3) * δ := by
    rw [hag z' hz'.1]; exact hshell z' hz'
  calc ‖eu (ψ z) - refVec (fun z => eu (ψk z)) (box b0 w)‖
      = ‖(eu (ψ z) - eu (ψ z')) + (eu (ψ z') - refVec (fun z => eu (ψk z)) (box b0 w))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖eu (ψ z) - eu (ψ z')‖ + ‖eu (ψ z') - refVec (fun z => eu (ψk z)) (box b0 w)‖ := norm_add_le _ _
    _ ≤ D * κ + (12 * d * (D + 2) + 3) * δ := by
        have : (w ⟨0, hd0⟩ : ℝ) * κ ≤ D * κ := mul_le_mul_of_nonneg_right hwD' hκ
        linarith

omit [NeZero N] in
theorem norm_refVec {m : ℕ} [NeZero m] [NeZero N] (ψ : Torus d m → EuclideanSpace ℝ (Fin N)) (Z : Set (Torus d m)) :
    ‖refVec ψ Z‖ = 1 := by
  unfold refVec
  split_ifs with h
  · simp
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

/-- **The converse inclusion**: a block field agreeing with `ψ_k ∈ Ψ̃(X ∖ Z₀; δ)` off the box `Z₀` and within `r`
of `ψ₀` on `Z₀` lies in `Ψ̃(X; δ')` with `δ' = r (2 + r) + 2 r + (12 d (D+2) + 3) δ + δ` (all data blocks lie
in `X`). -/
theorem tube_of_close {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
    (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
    {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
    (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) {δ r : ℝ} (hδ : 0 < δ) (hr : 0 ≤ r)
    {ψk ψ : BlockField d L N₀ k N} (hψk : TubeOn G (X \ box b0 w) δ ψk)
    (hag : ∀ z, z ∉ box b0 w → ψ z = ψk z)
    (hclose : ∀ z ∈ box b0 w, ‖eu (ψ z) - refVec (fun z => eu (ψk z)) (box b0 w)‖ ≤ r) :
    TubeOn G Set.univ (r * (2 + r) + 2 * r + (12 * d * (D + 2) + 3) * δ + δ) ψ := by
  have hC : 0 ≤ (12 * d * (D + 2) + 3 : ℝ) := by positivity
  have hshell := shell_close hd hk b0 w hw1 hwD hm hXreg hΩ hψk
  have hpos : 0 < r * (2 + r) + 2 * r + (12 * d * (D + 2) + 3) * δ + δ := by positivity
  set ψ0 := refVec (fun z => eu (ψk z)) (box b0 w) with hψ0
  have hn0 : ‖ψ0‖ = 1 := norm_refVec _ _
  refine ⟨fun x x' hp _ _ => ?_, fun x hx _ => ?_⟩
  · -- (R1)
    have hxX := hdata x hp.1
    have hx'X := hdata x' hp.2.1
    set y := jBlock d L N₀ k k x with hy
    set y' := jBlock d L N₀ k k x' with hy'
    have hrn : rn (fun i => liftR ψ x i - liftR ψ x' i) = ‖eu (ψ y) - eu (ψ y')‖ := by
      rw [eu_sub, norm_eu]; rfl
    rw [hrn]
    have hbad : ∀ z, z ∈ box b0 w → ‖eu (ψ z) - ψ0‖ ≤ r := hclose
    rcases blocks_of_interface G hp with he | hadj
    · rw [← hy, ← hy'] at he
      rw [he, sub_self, norm_zero]; exact hpos
    · by_cases hyb : y ∈ box b0 w <;> by_cases hyb' : y' ∈ box b0 w
      · calc ‖eu (ψ y) - eu (ψ y')‖ = ‖(eu (ψ y) - ψ0) - (eu (ψ y') - ψ0)‖ := by abel_nf
          _ ≤ ‖eu (ψ y) - ψ0‖ + ‖eu (ψ y') - ψ0‖ := norm_sub_le _ _
          _ ≤ r + r := add_le_add (hbad y hyb) (hbad y' hyb')
          _ < _ := by nlinarith [mul_nonneg hr hr, mul_nonneg hC hδ.le]
      · have hs := mem_shellOut_of_adj hyb hyb' hadj
        have h1 := hshell y' hs
        rw [hag y' hyb']
        calc ‖eu (ψ y) - eu (ψk y')‖ = ‖(eu (ψ y) - ψ0) - (eu (ψk y') - ψ0)‖ := by abel_nf
          _ ≤ ‖eu (ψ y) - ψ0‖ + ‖eu (ψk y') - ψ0‖ := norm_sub_le _ _
          _ < r + (12 * d * (D + 2) + 3) * δ := add_lt_add_of_le_of_lt (hbad y hyb) h1
          _ ≤ _ := by nlinarith [mul_nonneg hr hr, mul_nonneg hC hδ.le]
      · have hadj' : torusAdj y' y := by
          obtain ⟨μ, h | h⟩ := hadj
          · exact ⟨μ, Or.inr h⟩
          · exact ⟨μ, Or.inl h⟩
        have hs := mem_shellOut_of_adj hyb' hyb hadj'
        have h1 := hshell y hs
        rw [hag y hyb]
        calc ‖eu (ψk y) - eu (ψ y')‖ = ‖(eu (ψk y) - ψ0) - (eu (ψ y') - ψ0)‖ := by abel_nf
          _ ≤ ‖eu (ψk y) - ψ0‖ + ‖eu (ψ y') - ψ0‖ := norm_sub_le _ _
          _ < (12 * d * (D + 2) + 3) * δ + r := add_lt_add_of_lt_of_le h1 (hbad y' hyb')
          _ ≤ _ := by nlinarith [mul_nonneg hr hr, mul_nonneg hC hδ.le]
      · have h1 := hψk.1 x x' hp ⟨hxX, hyb⟩ ⟨hx'X, hyb'⟩
        rw [hag y hyb, hag y' hyb', eu_sub, norm_eu]
        have h1' : rn (fun i => ψk y i - ψk y' i) < δ := h1
        nlinarith [mul_nonneg hr hr, mul_nonneg hC hδ.le]
  · -- (R2)
    set z := jBlock d L N₀ k k x with hz
    by_cases hzb : z ∈ box b0 w
    · have e : ∑ i, ψ z i ^ 2 = ‖eu (ψ z)‖ ^ 2 := by
        simp [eu, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      rw [e]
      have h1 : |‖eu (ψ z)‖ - 1| ≤ r := by
        have := abs_norm_sub_norm_le (eu (ψ z)) ψ0
        rw [hn0] at this
        exact this.trans (hclose z hzb)
      have h2 : ‖eu (ψ z)‖ ^ 2 - 1 = (‖eu (ψ z)‖ - 1) * (‖eu (ψ z)‖ + 1) := by ring
      have hn : 0 ≤ ‖eu (ψ z)‖ := norm_nonneg _
      have h3 : ‖eu (ψ z)‖ + 1 ≤ 2 + r := by
        have := (abs_le.1 h1).2
        linarith
      rw [h2, abs_mul, abs_of_pos (by linarith : 0 < ‖eu (ψ z)‖ + 1)]
      calc |‖eu (ψ z)‖ - 1| * (‖eu (ψ z)‖ + 1) ≤ r * (2 + r) :=
            mul_le_mul h1 h3 (by linarith) hr
        _ < _ := by nlinarith [mul_nonneg hr hr, mul_nonneg hC hδ.le]
    · have h1 := hψk.2 x hx ⟨hdata x hx, hzb⟩
      rw [hag z hzb]
      nlinarith [mul_nonneg hr hr, mul_nonneg hC hδ.le]

end Tube

end Balaban.LargeField
