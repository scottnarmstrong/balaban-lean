module

public import Balaban.LargeField.R.ZeroDomainScales
public import Balaban.LargeField.R.ZeroDomainBox
public import Balaban.LargeField.R.ZeroDomainCoercive
public import Balaban.LargeField.Operators.DomainGeom
public import Balaban.LargeField.History.RipeWindow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The late-scale regions `Z₀` and `Z''₀` (Part III, Definition III.3.1, Lemma III.5.0 (a))

For a component `Z` of `Z^pre_k`, `Z_j = Lin_j(Z)` (`RegionHistory.lin`).  Lengths at scale `k` are
measured in `k`-blocks.  With the fine torus `Torus d (M n_k L^k)`:

* `Zzero H k Z`: the `k`-blocks (sites of `Torus d (M n_k)`) that meet `Z_{k₂}`, i.e. contain a fine
  site lying in a `π_{k₂}`-cube of `Z_{k₂}` (P7 (2.3));
* `ZzeroDD H k Z`: the `3`-neighbourhood, in `π_k`-cubes (sites of `Torus d (n_k)`), of the `π_k`-cubes
  that meet `Z_{k₃}` (Definition III.3.1, with the threshold `8` of `k₃`).

`Zzero_cube_mem` is `Z₀ ⊆ Z''₀` (Lemma III.3.2 (c)) and `ZzeroDD_sep` is Lemma III.5.0 (a): a
`π_k`-cube outside `Z''₀` has its `3`-neighbourhood disjoint from `Z₀`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-- The side of the fine torus at scale `k`: `M · n_k · L^k` fine sites. -/
def fineSide (S : Setting) (n : ℕ → ℕ) (k : ℕ) : ℕ := S.M * (n k * S.L ^ k)

instance fineSide.neZero (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] [NeZero S.M] [NeZero S.L]
    (k : ℕ) : NeZero (fineSide S n k) := by
  unfold fineSide; infer_instance

/-- The `π_j`-cube of a fine site (blocks of side `M L^j`). -/
def cubeOf (S : Setting) (n : ℕ → ℕ) (k j : ℕ) : Torus S.d (fineSide S n k) → Torus S.d (n j) :=
  blockMap (S.M * S.L ^ j) (n j)

/-- The `k`-block of a fine site (blocks of side `L^k`); there are `M n_k` per side. -/
def zeroBlockOf (S : Setting) (n : ℕ → ℕ) (k : ℕ) : Torus S.d (fineSide S n k) → Torus S.d (S.M * n k) :=
  blockMap (S.L ^ k) (S.M * n k)

theorem blockMap_one {d ℓ : ℕ} [NeZero ℓ] (x : Torus d ℓ) : blockMap 1 ℓ x = x := by
  funext i
  simp [blockMap, blockCoord]

namespace FlowSteps

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (F : FlowSteps S n R k0 K)

include F in
/-- `n_j = L^{k-j} n_k` below the horizon. -/
theorem n_eq_pow {j k : ℕ} (hjk : j ≤ k) (hkK : k ≤ K) : n j = S.L ^ (k - j) * n k := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjk
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 := F.hnn (j + t) (by omega)
    have h2 := ih (by omega) (by omega)
    rw [show j + t + 1 = j + (t + 1) by ring] at h1
    simp only [Nat.add_sub_cancel_left] at h2 ⊢
    rw [h2, h1, pow_succ]
    ring

include F in
theorem fineSide_eq {j k : ℕ} (hjk : j ≤ k) (hkK : k ≤ K) :
    fineSide S n k = (S.M * S.L ^ j) * n j := by
  unfold fineSide
  rw [F.n_eq_pow hjk hkK]
  have : S.L ^ k = S.L ^ j * S.L ^ (k - j) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

end FlowSteps

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M]

include H

theorem cubeOf_comp {j i k : ℕ} (hji : j ≤ i) (hik : i ≤ k) (hkK : k ≤ K)
    (s : Torus S.d (fineSide S n k)) :
    blockMap (S.L ^ (i - j)) (n i) (cubeOf S n k j s) = cubeOf S n k i s := by
  unfold cubeOf
  have h1 := H.F.fineSide_eq (by omega : j ≤ k) hkK
  have h2 := H.F.n_eq_pow hji (by omega : i ≤ K)
  rw [blockMap_comp h1 h2, mul_assoc, ← pow_add, show j + (i - j) = i by omega]

theorem block_cube {k : ℕ} (s : Torus S.d (fineSide S n k)) :
    blockMap S.M (n k) (zeroBlockOf S n k s) = cubeOf S n k k s := by
  unfold zeroBlockOf cubeOf
  have h1 : fineSide S n k = S.L ^ k * (S.M * n k) := by unfold fineSide; ring
  rw [blockMap_comp h1 rfl, mul_comm]

/-- The lineages grow with the scale (Lemma I.4.3 (b), index form): coarsening a cube of `Lin_a(Z)`
by `L^{c-a}` gives a cube of `Lin_c(Z)`. -/
theorem blockMap_pow_mem_lin {a b : ℕ} (hbK : b ≤ K) (Z : H.Comp b) {x : Torus S.d (n a)}
    (hx : x ∈ (H.lin a b Z : Set _)) : ∀ c, a ≤ c → c ≤ b →
    blockMap (S.L ^ (c - a)) (n c) x ∈ (H.lin c b Z : Set _) := by
  intro c hac
  induction c, hac using Nat.le_induction with
  | base => intro _; simpa [blockMap_one] using hx
  | succ c hac ih =>
    intro hcb
    have hc := ih (by omega)
    have hn := H.F.n_eq_pow hac (by omega : c ≤ K)
    have e : blockMap S.L (n (c + 1)) (blockMap (S.L ^ (c - a)) (n c) x) =
        blockMap (S.L ^ (c + 1 - a)) (n (c + 1)) x := by
      have h1 : n a = S.L ^ (c - a) * n c := H.F.n_eq_pow hac (by omega)
      have h2 : n c = S.L * n (c + 1) := H.F.hnn c (by omega)
      rw [blockMap_comp h1 h2, show c + 1 - a = (c - a) + 1 by omega, pow_succ]
    rw [← e]
    exact blockMap_nbhd_lin hbK Z (by omega) (subset_nbhd 1 _ hc)

/-- `Z₀`: the `k`-blocks that meet `Z_{k₂}` (P7 (2.3)); `Z_j = Lin_j(Z)`. -/
def Zzero (k : ℕ) (Z : H.Comp k) : Set (Torus S.d (S.M * n k)) :=
  {b | ∃ s : Torus S.d (fineSide S n k), zeroBlockOf S n k s = b ∧
    cubeOf S n k (S.kTwo k) s ∈ (H.lin (S.kTwo k) k Z : Set (Torus S.d (n (S.kTwo k))))}

/-- The `π_k`-cubes that meet `Z_{k₃}`. -/
def cubesMeetingZ3 (k : ℕ) (Z : H.Comp k) : Set (Torus S.d (n k)) :=
  {c | ∃ s : Torus S.d (fineSide S n k), cubeOf S n k k s = c ∧
    cubeOf S n k (S.kThree k) s ∈ (H.lin (S.kThree k) k Z : Set (Torus S.d (n (S.kThree k))))}

/-- `Z''₀`: the `3`-neighbourhood, in `π_k`-cubes, of the `π_k`-cubes meeting `Z_{k₃}`
(Definition III.3.1). -/
def ZzeroDD (k : ℕ) (Z : H.Comp k) : Set (Torus S.d (n k)) := nbhd 3 (H.cubesMeetingZ3 k Z)

/-- **`Z₀ ⊆ Z''₀`** (Lemma III.3.2 (c)): the `π_k`-cube of a block of `Z₀` lies in `Z''₀`. -/
theorem Zzero_cube_mem (hS : S.Ok) {k : ℕ} (hkK : k ≤ K) (h3 : 8 ≤ S.L * S.lateR k) (Z : H.Comp k)
    {b : Torus S.d (S.M * n k)} (hb : b ∈ H.Zzero k Z) :
    blockMap S.M (n k) b ∈ H.ZzeroDD k Z := by
  obtain ⟨s, rfl, hs⟩ := hb
  refine subset_nbhd 3 _ ⟨s, (H.block_cube s).symm, ?_⟩
  have h23 := hS.kTwo_le_kThree h3
  have h3k := (hS.kThree_mem h3).1
  have := H.blockMap_pow_mem_lin hkK Z hs (S.kThree k) h23 h3k
  rw [H.cubeOf_comp h23 h3k hkK s] at this
  exact this

/-- **Lemma III.5.0 (a)**: a `π_k`-cube outside `Z''₀` has its `3`-neighbourhood disjoint from `Z₀`. -/
theorem ZzeroDD_sep (hS : S.Ok) {k : ℕ} (hkK : k ≤ K) (h3 : 8 ≤ S.L * S.lateR k) (Z : H.Comp k)
    {c : Torus S.d (n k)} (hc : c ∉ H.ZzeroDD k Z) {b : Torus S.d (S.M * n k)}
    (hb : b ∈ H.Zzero k Z) : blockMap S.M (n k) b ∉ nbhd 3 {c} := by
  intro hmem
  obtain ⟨x, hx, hd⟩ := mem_nbhd.mp hmem
  rw [Set.mem_singleton_iff] at hx
  subst hx
  obtain ⟨s, rfl, hs⟩ := hb
  rw [H.block_cube s] at hd
  refine hc (mem_nbhd.mpr ⟨cubeOf S n k k s, ⟨s, rfl, ?_⟩, by rwa [supDist_comm]⟩)
  have h23 := hS.kTwo_le_kThree h3
  have h3k := (hS.kThree_mem h3).1
  have := H.blockMap_pow_mem_lin hkK Z hs (S.kThree k) h23 h3k
  rw [H.cubeOf_comp h23 h3k hkK s] at this
  exact this

/-- **`Z₀` lies in a box of `k`-blocks**: if `Z_{k₂}` lies in the box `box a sd` of `π_{k₂}`-cubes, then `Z₀` lies
in a box of `k`-blocks whose side in direction `i` is at most `(sd_i M L^{k₂} + L^k - 2)/L^k + 1`. -/
theorem Zzero_subset_box {k : ℕ} (hkK : k ≤ K) (hk2 : S.kTwo k ≤ k) (Z : H.Comp k)
    {a : Torus S.d (n (S.kTwo k))} {sd : Fin S.d → ℕ}
    (hbox : (H.lin (S.kTwo k) k Z : Set (Torus S.d (n (S.kTwo k)))) ⊆ box a sd) :
    ∃ (b0 : Torus S.d (S.M * n k)) (w : Fin S.d → ℕ),
      (∀ i, w i ≤ (sd i * (S.M * S.L ^ S.kTwo k) + S.L ^ k - 2) / S.L ^ k + 1) ∧
      H.Zzero k Z ⊆ box b0 w := by
  have hN : fineSide S n k = S.L ^ k * (S.M * n k) := by unfold fineSide; ring
  have hu : fineSide S n k = (S.M * S.L ^ S.kTwo k) * n (S.kTwo k) := H.F.fineSide_eq hk2 hkK
  refine ⟨fun i => blockCoord (S.L ^ k) (S.M * n k)
      (((a i).val * (S.M * S.L ^ S.kTwo k) : ℕ) : ZMod (fineSide S n k)),
    fun i => (sd i * (S.M * S.L ^ S.kTwo k) + S.L ^ k - 2) / S.L ^ k + 1, fun i => le_rfl, ?_⟩
  rintro x ⟨s, rfl, hs⟩ i
  obtain ⟨j, hj, hji⟩ := hbox hs i
  have hji' : blockCoord (S.M * S.L ^ S.kTwo k) (n (S.kTwo k)) (s i) = a i + (j : ZMod _) := hji
  obtain ⟨j', hj', hx⟩ := blockCoord_box_image hN hu (a i) (sd i) j hj (s i) hji'
  exact ⟨j', Nat.lt_succ_of_le hj', hx⟩

end RegionHistory

theorem side_arith {c0 M R sd p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hR : 8 * M * R < 9 * q)
    (hsd : sd ≤ (2 * c0 + 1) * R) :
    (sd * (M * p) + p * q - 2) / (p * q) + 1 ≤ 3 * c0 + 4 := by
  have h1 : 8 * (sd * M) < 8 * ((3 * c0 + 3) * q) := by
    have : 8 * (sd * M) ≤ (2 * c0 + 1) * (8 * M * R) := by
      calc 8 * (sd * M) = 8 * sd * M := by ring
        _ ≤ 8 * ((2 * c0 + 1) * R) * M := by gcongr
        _ = (2 * c0 + 1) * (8 * M * R) := by ring
    have h2 : (2 * c0 + 1) * (8 * M * R) < (2 * c0 + 1) * (9 * q) :=
      Nat.mul_lt_mul_of_pos_left hR (by omega)
    nlinarith
  have h3 : sd * M < (3 * c0 + 3) * q := by omega
  have h4 : sd * M * p + p * q + p ≤ (3 * c0 + 4) * (p * q) := by
    have : (sd * M + q) * p + p ≤ (3 * c0 + 4) * q * p := by nlinarith
    have h5 : (3 * c0 + 4) * (p * q) = (3 * c0 + 4) * q * p := by ring
    rw [h5]; nlinarith
  have h6 : sd * (M * p) + p * q - 2 < (3 * c0 + 4) * (p * q) := by
    have : sd * (M * p) = sd * M * p := by ring
    have : 0 < p * q := Nat.mul_pos hp hq
    omega
  have := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hp hq)).mpr h6
  omega

namespace Setting.Ok

variable {S : Setting} (hS : S.Ok)
include hS

/-- `crit_j ≤ (2 c₀ + 1) [R̂_j]` as soon as `2 c₀ + 10 ≤ [R̂_j]` (the case `D-IV.2` of Lemma III.3.2). -/
theorem crit_le_lateR {j : ℕ} (hR : 2 * S.c0 + 10 ≤ S.lateR j) : S.crit j ≤ (2 * S.c0 + 1) * S.lateR j := by
  have h1 : S.r j ≤ S.lateR j + 1 := by
    have h2 : (S.r j : ℝ) < S.lateR j + 2 := by
      have := Nat.lt_floor_add_one (S.Rb * S.lam j ^ 2)
      have h3 : (S.r j : ℝ) ≤ S.Rb * S.lam j ^ 2 + 1 := hS.r_le j
      unfold lateR; linarith
    have : S.r j < S.lateR j + 2 := by exact_mod_cast h2
    omega
  unfold Setting.crit Setting.rho
  nlinarith

end Setting.Ok

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M]

/-- `Z_{k₂}` of a ripe window lies in one box of `π_{k₂}`-cubes of side `≤ crit_{k₂}` (Lemma III.1.2 (d)). -/
theorem lin_subset_box {k j : ℕ} {Z : H.Comp k} (W : H.RipeWindow k Z) (hsj : (H.bk k Z).s ≤ j) :
    ∃ (a : Torus S.d (n j)) (sd : Fin S.d → ℕ),
      (H.lin j k Z : Set (Torus S.d (n j))) ⊆ box a sd ∧ ∀ i, sd i ≤ S.crit j := by
  classical
  by_cases hex : ∃ Y : H.Comp j, H.Desc j k Y Z
  · obtain ⟨Y, hY⟩ := hex
    obtain ⟨-, ⟨B, hB, hbc, hsub⟩, huniq⟩ := W.unique_box j Y hsj hY
    have hlin : (H.lin j k Z : Set (Torus S.d (n j))) ⊆ (Y.1 : Set (Torus S.d (n j))) := by
      intro x hx
      obtain ⟨Y', hY', hxY'⟩ := mem_lin.mp hx
      rw [huniq Y' hY'] at hxY'
      exact hxY'
    have h := Finset.card_le_one.mp hB
    by_cases hBe : B = ∅
    · refine ⟨fun _ => 0, fun _ => 0, ?_, fun i => Nat.zero_le _⟩
      intro x hx
      have := hsub (hlin hx)
      simp [hBe] at this
    · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hBe
      refine ⟨b.1, b.2, ?_, hbc b hb⟩
      intro x hx
      have := hsub (hlin hx)
      simp only [Set.mem_iUnion] at this
      obtain ⟨b', hb', hxb'⟩ := this
      have := h b' hb' b hb
      rwa [this] at hxb'
  · refine ⟨fun _ => 0, fun _ => 0, ?_, fun i => Nat.zero_le _⟩
    intro x hx
    obtain ⟨Y, hY, -⟩ := mem_lin.mp hx
    exact absurd ⟨Y, hY⟩ hex

/-- **Lemma III.3.2 (c), first part**: for a ripe window, `Z₀` lies in a box of `k`-blocks of side
`≤ D₀ = 3 c₀ + 4` in every direction. -/
theorem Zzero_in_box (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    (hR0 : 2 * S.c0 + 10 ≤ S.lateR 0) {k : ℕ} (hkK : k ≤ K) {Z : H.Comp k} (W : H.RipeWindow k Z)
    (h3 : 8 ≤ S.L * S.lateR k) :
    ∃ (b0 : Torus S.d (S.M * n k)) (w : Fin S.d → ℕ),
      (∀ i, w i ≤ 3 * S.c0 + 4) ∧ H.Zzero k Z ⊆ box b0 w := by
  have hS := G.ok
  obtain ⟨-, hq2, hs2, -, -, hb2, -⟩ := G.lateScale_geom h18 W.core_window.1 W.point.2.1 h3
  have hk2 := hS.kTwo_le k
  obtain ⟨a, sd, hsub, hsd⟩ := H.lin_subset_box W (le_of_lt hs2)
  obtain ⟨b0, w, hw, hZ⟩ := H.Zzero_subset_box hkK hk2 Z hsub
  refine ⟨b0, w, fun i => (hw i).trans ?_, hZ⟩
  have hL := hS.two_le_L
  have hLpos : 0 < S.L := by omega
  -- `8 M [R] < 9 L^{n_2}`
  have hR8 : 8 * S.M * S.lateR (S.kTwo k) < 9 * S.L ^ S.lateN2 k := by
    have h1 : (8 * (S.L * (S.M * S.lateR (S.kTwo k))) : ℝ) < 9 * S.L * (S.L : ℝ) ^ S.lateN2 k := by
      push_cast at hb2; linarith
    have h2 : 8 * (S.L * (S.M * S.lateR (S.kTwo k))) < 9 * S.L * S.L ^ S.lateN2 k := by
      exact_mod_cast h1
    have h3' : S.L * (8 * S.M * S.lateR (S.kTwo k)) < S.L * (9 * S.L ^ S.lateN2 k) := by
      calc S.L * (8 * S.M * S.lateR (S.kTwo k)) = 8 * (S.L * (S.M * S.lateR (S.kTwo k))) := by ring
        _ < 9 * S.L * S.L ^ S.lateN2 k := h2
        _ = S.L * (9 * S.L ^ S.lateN2 k) := by ring
    exact Nat.lt_of_mul_lt_mul_left h3'
  have hRk2 : 2 * S.c0 + 10 ≤ S.lateR (S.kTwo k) :=
    hR0.trans (hS.lateR_mono (Nat.zero_le _))
  have hcrit := hS.crit_le_lateR hRk2
  have hk : S.L ^ k = S.L ^ S.kTwo k * S.L ^ S.lateN2 k := by
    rw [← pow_add]; congr 1; unfold Setting.lateN2; omega
  rw [hk]
  exact side_arith (c0 := S.c0) (M := S.M) (R := S.lateR (S.kTwo k)) (sd := sd i)
    (Nat.pow_pos hLpos) (Nat.pow_pos hLpos) hR8 ((hsd i).trans hcrit)

/-- **Coercivity on `Z₀`** (`c_{D₀}`, Lemma III.3.3): a field on the `k`-blocks vanishing outside `Z₀` of a ripe window
satisfies `c_{D₀} ‖f‖² ≤ ∑_x ∑_μ ‖f(x + e_μ) - f(x)‖²`, `D₀ = 3 c₀ + 4`. -/
theorem Zzero_dirichlet {V : Type*} [SeminormedAddCommGroup V] (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    (hR0 : 2 * S.c0 + 10 ≤ S.lateR 0) {k : ℕ} (hkK : k ≤ K) {Z : H.Comp k} (W : H.RipeWindow k Z)
    (h3 : 8 ≤ S.L * S.lateR k) (hd : 0 < S.d) (hn : 3 * S.c0 + 4 + 1 ≤ S.M * n k)
    (f : Torus S.d (S.M * n k) → V) (hf : ∀ x, x ∉ H.Zzero k Z → f x = 0) :
    cDirichlet (3 * S.c0 + 4) * ∑ x, ‖f x‖ ^ 2 ≤
      ∑ x, ∑ μ : Fin S.d, ‖f (x + Pi.single μ 1) - f x‖ ^ 2 := by
  obtain ⟨b0, w, hw, hZ⟩ := H.Zzero_in_box G h18 hR0 hkK W h3
  exact dirichlet_box_coercive hd b0 w hw hn f fun x hx => hf x fun h => hx (hZ h)

end RegionHistory

end Balaban.LargeField
