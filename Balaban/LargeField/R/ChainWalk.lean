module

public import Balaban.LargeField.R.ChainSetting
public import Balaban.LargeField.R.ChainPath
public import Balaban.LargeField.R.ChainCount
public import Balaban.LargeField.R.ChainExtract
public import Balaban.LargeField.R.FineBox
public import Balaban.LargeField.R.ChainEstimate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Paths from window blocks to `Ω_k ∩ Z` (Part III, Lemma III.4.3)

Facts about the localization of a ripe component used by the path construction
(`path_avoids_obstacles`, in `R/ChainWalk2.lean`):

* `supDist_nnAdj_le`, `mem_locFine_of_nn`: a nearest-neighbour neighbour of a site of `Z` outside
  `Ω_k` lies in `Z`;
* `exists_layer_of_mem`: a site of `Ω_{i₀} ∖ Ω_k` lies in a layer `i₀ ≤ i < k`;
* `jBlock_mem_box_iff`: the sites of an `i`-block form a box;
* `fine_diam_le`: the sup-diameter of the fine set of a component of `Z_i`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Multiscale

theorem supDist_nnAdj_le {d m : ℕ} [NeZero m] {x y : Torus d m} (h : NNAdj x y) : supDist x y ≤ 1 := by
  have h1 := supDist_le_torusDist x y
  have h2 := torusDist_nnAdj_le h
  exact_mod_cast h1.trans h2

theorem blockMap_supDist_le_one_of_le_one {d N m ℓ : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N)
    {x y : Torus d ℓ} (h : supDist x y ≤ 1) : supDist (blockMap N m x) (blockMap N m y) ≤ 1 := by
  refine (supDist_blockMap_le hℓ x y).trans ?_
  have : (supDist x y + N - 1) / N ≤ (1 + N - 1) / N := Nat.div_le_div_right (by omega)
  refine this.trans ?_
  rw [show 1 + N - 1 = N by omega, Nat.div_self hN]

theorem L_add_eleven_le_omega (S : Setting) (k : ℕ) : S.L + 11 ≤ S.omega k := by
  have h := le_omegaW S.L S.Rb S.lam k
  rw [← Setting.omega_eq_omegaW] at h
  exact h

namespace Setting.Ok

variable {S : Setting} (hS : S.Ok)
include hS

/-- `ν_max M (crit_k + ω_k) ≤ L^{h_k - 2}` (definition of `h_k`). -/
theorem pow_h_ge (k : ℕ) :
    (S.numax k : ℝ) * S.M * (S.crit k + S.omega k) ≤ (S.L : ℝ) ^ (S.h k - 2) := by
  have hL1 : (1 : ℝ) < S.L := by
    have := hS.two_le_L; exact_mod_cast (by omega : 1 < S.L)
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hν : (1 : ℝ) ≤ S.numax k := by exact_mod_cast hS.hatW_numax_ge_one k
  have hM : (1 : ℝ) ≤ S.M := by exact_mod_cast hS.one_le_M
  have hd : (1 : ℝ) ≤ Real.sqrt S.d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by have := hS.three_le_d; exact_mod_cast (by omega : 1 ≤ S.d))
  have hcw : (1 : ℝ) ≤ S.crit k + S.omega k := by
    have : 1 ≤ S.crit k := by unfold Setting.crit; omega
    have : (1 : ℝ) ≤ S.crit k := by exact_mod_cast this
    have : (0 : ℝ) ≤ S.omega k := Nat.cast_nonneg _
    linarith
  set A : ℝ := 2 * Real.sqrt S.d * S.numax k * S.M * (S.crit k + S.omega k) with hA
  have hApos : 0 < A := by positivity
  have hAge : (S.numax k : ℝ) * S.M * (S.crit k + S.omega k) ≤ A := by
    rw [hA]
    have h1 : (0 : ℝ) ≤ S.numax k * S.M * (S.crit k + S.omega k) := by positivity
    nlinarith
  have hh : S.h k - 2 = ⌈Real.logb S.L A⌉₊ := by
    simp [Setting.h, hA]
  rw [hh]
  have hle : A ≤ (S.L : ℝ) ^ (⌈Real.logb S.L A⌉₊ : ℕ) := by
    calc A = (S.L : ℝ) ^ (Real.logb S.L A) := (Real.rpow_logb hL0 hL1.ne' hApos).symm
      _ ≤ (S.L : ℝ) ^ ((⌈Real.logb S.L A⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1.le (Nat.le_ceil _)
      _ = (S.L : ℝ) ^ (⌈Real.logb S.L A⌉₊ : ℕ) := Real.rpow_natCast _ _
  exact hAge.trans hle

end Setting.Ok

theorem jBlock_mem_box_iff {d L N₀ k j : ℕ} [NeZero N₀] [NeZero L] (hjk : j ≤ k)
    (b : Torus d (N₀ * L ^ (k - j))) (x : Torus d (N₀ * L ^ k)) :
    jBlock d L N₀ k j x = b ↔
      x ∈ box (fun i => (((L ^ j * (b i).val : ℕ)) : ZMod (N₀ * L ^ k))) (fun _ => L ^ j) := by
  have hℓ : N₀ * L ^ k = L ^ j * (N₀ * L ^ (k - j)) := Multiscale.side_eq hjk
  have h := blockMap_mem_box_iff (d := d) (ℓ := N₀ * L ^ k) (N := L ^ j) (m := N₀ * L ^ (k - j))
    hℓ b (s := fun _ => 1) x
  have hbox : blockMap (L ^ j) (N₀ * L ^ (k - j)) x ∈ box b (fun _ => 1) ↔
      blockMap (L ^ j) (N₀ * L ^ (k - j)) x = b := by
    unfold box
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hh
      funext i
      obtain ⟨jj, hjj, hxj⟩ := hh i
      have : jj = 0 := by omega
      subst this
      simpa using hxj
    · intro hh i
      exact ⟨0, by omega, by simp [hh]⟩
  unfold jBlock
  rw [← hbox, h]
  simp only [mul_one]

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} {M : ℕ} [NeZero M] [NeZero S.L]

variable {hkK : k ≤ K} {hL : 2 ≤ S.L} {hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j}

/-- A nearest-neighbour neighbour of a site of `Z_k = Z` which is outside `Ω_k` lies in `Z`
(`(Ω_kᶜ)^{∼(⌊2R⌋+2)} ⊆ Z^{(0)}`). -/
theorem mem_locFine_of_nn (hk1 : 1 ≤ k) {x w : Torus S.d (M * n k * S.L ^ k)}
    (hx : x ∉ (H.locGen Z M hkK hL hR).Ω k) (hxw : NNAdj x w) : w ∈ H.locFine Z M k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set st := (H.locRH (k' + 1) Z).step k' with hst
  have hx' : cubeMap n S.L M (k' + 1) (k' + 1) x ∉ st.Omega := fun h =>
    hx ((mem_locGen_succ (hkK := hkK) (hL := hL) (hR := hR) (by omega)).mpr h)
  have hFZ : cubeMap n S.L M (k' + 1) (k' + 1) x ∈ st.FZ :=
    st.OmegaDD_compl_subset_FZ (st.Omega_compl_subset_OmegaDD_compl hx')
  have hd : supDist (cubeMap n S.L M (k' + 1) (k' + 1) x) (cubeMap n S.L M (k' + 1) (k' + 1) w) ≤ 1 := by
    have h1 := supDist_nnAdj_le hxw
    have hNpos : 0 < S.L ^ (k' + 1) * M := by
      have := NeZero.pos S.L; have := NeZero.pos M; positivity
    have h2 := supDist_blockMap_le (L := S.L ^ (k' + 1) * M) (m := n (k' + 1))
      (n := M * n (k' + 1) * S.L ^ (k' + 1)) (fine_eq (hnn_k H hkK) le_rfl) x w
    refine h2.trans ?_
    have : (supDist x w + S.L ^ (k' + 1) * M - 1) / (S.L ^ (k' + 1) * M) ≤
        (1 + S.L ^ (k' + 1) * M - 1) / (S.L ^ (k' + 1) * M) :=
      Nat.div_le_div_right (by omega)
    refine this.trans ?_
    rw [show 1 + S.L ^ (k' + 1) * M - 1 = S.L ^ (k' + 1) * M by omega, Nat.div_self hNpos]
  have hnb : cubeMap n S.L M (k' + 1) (k' + 1) w ∈ nbhd (⌊2 * R k'⌋₊ + 2) st.FZ :=
    mem_nbhd.mpr ⟨_, hFZ, by rw [supDist_comm]; omega⟩
  have hZ0 := st.nbhd_FZ_subset_Z0 hnb
  have hZpre := st.Z0_subset_Zpre (S.omega (k' + 1)) (critOpt S k0 (k' + 1)) hZ0
  have h3 : (H.locRH (k' + 1) Z).F.Zpre (k' + 1) =
      st.Zpre (S.omega (k' + 1)) (critOpt S k0 (k' + 1)) := rfl
  rw [← h3, locRH_Zpre Z le_rfl hkK, lin_self] at hZpre
  exact (mem_locFine_k hkK).mpr (by simpa using hZpre)

/-- A site of `Ω_{i₀} ∖ Ω_k` (`1 ≤ i₀`) lies in a layer `i₀ ≤ i < k`. -/
theorem exists_layer_of_mem {i0 : ℕ} (hi0 : 1 ≤ i0) {x : Torus S.d (M * n k * S.L ^ k)}
    (hx : x ∈ (H.locGen Z M hkK hL hR).Ω i0) (hxk : x ∉ (H.locGen Z M hkK hL hR).Ω k) :
    ∃ i, i0 ≤ i ∧ i < k ∧ x ∈ (H.locGen Z M hkK hL hR).layer i := by
  set G := H.locGen Z M hkK hL hR
  have hi0k : i0 ≤ k := by
    by_contra h
    push Not at h
    have : G.Ω i0 = ∅ := by
      by_cases hk' : i0 = k + 1
      · rw [hk', G.top]
      · exfalso
        have := (mem_locGen (hkK := hkK) (hL := hL) (hR := hR)).mp hx
        omega
    rw [this] at hx
    simp at hx
  have h1 : x ∈ G.Ω 1 := G.Ω_antitone le_rfl hi0 (by omega) hx
  obtain ⟨hi1, hik, hxl⟩ := G.layerIndex_spec h1
  refine ⟨G.layerIndex x, ?_, ?_, hxl⟩
  · by_contra hlt
    push Not at hlt
    have : x ∈ G.Ω (G.layerIndex x + 1) := G.Ω_antitone (by omega) (by omega) (by omega) hx
    exact (G.mem_layer.1 hxl).2 this
  · rcases Nat.eq_or_lt_of_le hik with h | h
    · rw [h] at hxl
      exact absurd (G.mem_layer.1 hxl).1 hxk
    · exact h

/-- The sup-diameter of the fine set of a component of `Z_i`: if two sites lie over cubes of a
component of width `ω_i` of `Lin_i(Z)`, `k₁ ≤ i ≤ k`, then
`dist(x, y) + 1 ≤ L^i M ν_max(k) (crit_k + ω_k)` (Lemma I.2.12 (c) with Lemma III.1.2 (c)). -/
theorem fine_diam_le (hkK : k ≤ K) (hW : H.RipeWindow k Z) {i : ℕ} (hi : S.k1 k ≤ i) (hik : i ≤ k)
    {C : Finset (Torus S.d (n i))} (hC : C ∈ comps (S.omega i) (H.lin i k Z))
    {x y : Torus S.d (M * n k * S.L ^ k)} (hx : cubeMap n S.L M k i x ∈ C)
    (hy : cubeMap n S.L M k i y ∈ C) :
    supDist x y + 1 ≤ S.L ^ i * M * (S.numax k * (S.crit k + S.omega k)) := by
  classical
  have hcov := hW.cover i (by rw [← hW.core_k1]; exact hi) hik
  obtain ⟨B, hB, hs, hsub⟩ := hcov
  have hω : 1 ≤ S.omega i := by
    have := L_add_eleven_le_omega S i; omega
  have hcd := comp_diam_le (ι := ↥B) (b := S.crit i) hω (fun j => j.1.1) (fun j => j.1.2)
    (fun j a => hs j.1 j.2 a) hC (fun z hz => by
      have hz' : z ∈ (H.lin i k Z : Set (Torus S.d (n i))) := by
        exact_mod_cast comp_subset hC hz
      have := hsub hz'
      simp only [Set.mem_iUnion, exists_prop] at this
      obtain ⟨b, hb, hzb⟩ := this
      exact ⟨⟨b, hb⟩, hzb⟩) _ hx _ hy
  simp only [Fintype.card_coe] at hcd
  have hcpos : 1 ≤ B.card := by
    by_contra h0
    have : B = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    have := hsub (show (cubeMap n S.L M k i x : Torus S.d (n i)) ∈
      (H.lin i k Z : Set (Torus S.d (n i))) by exact_mod_cast comp_subset hC hx)
    simp at this
  have hNpos : 0 < S.L ^ i * M := by
    have := NeZero.pos S.L; have := NeZero.pos M; positivity
  have h1 := supDist_le_blockMap (L := S.L ^ i * M) (m := n i) (n := M * n k * S.L ^ k)
    (fine_eq (hnn_k H hkK) hik) x y
  unfold cubeMap at hcd
  set D := supDist (blockMap (S.L ^ i * M) (n i) x) (blockMap (S.L ^ i * M) (n i) y) with hD
  have hcrit : 1 ≤ S.crit i := by unfold Setting.crit; omega
  have hD1 : D + 1 ≤ B.card * (S.crit i + S.omega i) := by
    obtain ⟨c', hc'⟩ : ∃ c', B.card = c' + 1 := ⟨B.card - 1, by omega⟩
    obtain ⟨a', ha'⟩ : ∃ a', S.crit i = a' + 1 := ⟨S.crit i - 1, by omega⟩
    obtain ⟨w', hw'⟩ : ∃ w', S.omega i = w' + 1 := ⟨S.omega i - 1, by omega⟩
    rw [hc', ha', hw'] at hcd ⊢
    simp only [Nat.add_sub_cancel] at hcd
    nlinarith
  have hcν : B.card ≤ S.numax k := hB.trans hW.nu_le
  have hcm : S.crit i ≤ S.crit k := H.F.ok.crit_mono hik
  have hωm : S.omega i ≤ S.omega k := H.F.ok.omega_mono hik
  have h3 : B.card * (S.crit i + S.omega i) ≤ S.numax k * (S.crit k + S.omega k) :=
    Nat.mul_le_mul hcν (by omega)
  have hN1 : 1 ≤ S.L ^ i * M := hNpos
  calc supDist x y + 1 ≤ S.L ^ i * M * D + (S.L ^ i * M - 1) + 1 := by omega
    _ = S.L ^ i * M * (D + 1) := by
        rw [mul_add, mul_one]; omega
    _ ≤ S.L ^ i * M * (S.numax k * (S.crit k + S.omega k)) :=
        Nat.mul_le_mul_left _ (by omega)

/-- An ancestor at scale `q` of a ripe component covered by one box of side `≤ crit_q` is a box
(a small component of the hull closure is a box, Lemma I.3.4 (b)). -/
theorem ancestor_box {q : ℕ} (hq1 : 1 ≤ q) (hq0 : q ≤ k0) {Y : H.Comp q}
    (hcov : CoveredBy S n q Y.1 1) (hn : 2 * S.crit q < n q) :
    ∃ (a : Torus S.d (n q)) (s : Fin S.d → ℕ), ((Y.1 : Finset (Torus S.d (n q))) : Set (Torus S.d (n q))) = box a s ∧
      ∀ i, 1 ≤ s i ∧ 2 * s i < n q := by
  classical
  obtain ⟨B, hB, hs, hsub⟩ := hcov
  obtain ⟨y0, hy0⟩ := comp_nonempty Y.2
  have hy0' := hsub (show y0 ∈ ((Y.1 : Finset (Torus S.d (n q))) : Set _) from hy0)
  simp only [Set.mem_iUnion, exists_prop] at hy0'
  obtain ⟨b0, hb0, -⟩ := hy0'
  have hBsingle : ∀ b ∈ B, b = b0 := by
    intro b hb
    have : B.card ≤ 1 := hB
    exact Finset.card_le_one.mp this b hb b0 hb0
  have hYb : ∀ x ∈ ((Y.1 : Finset (Torus S.d (n q))) : Set _), x ∈ box b0.1 b0.2 := by
    intro x hx
    have := hsub hx
    simp only [Set.mem_iUnion, exists_prop] at this
    obtain ⟨b, hb, hxb⟩ := this
    rwa [hBsingle b hb] at hxb
  have hsmall : IsSmall ((Y.1 : Finset (Torus S.d (n q))) : Set (Torus S.d (n q))) := by
    intro i
    refine ⟨b0.1 i, b0.2 i, ?_, fun x hx => ?_⟩
    · have := hs b0 hb0 i; omega
    · obtain ⟨j, hj, hxj⟩ := hYb x hx i
      exact ⟨j, hj, hxj⟩
  have hside : side ((Y.1 : Finset (Torus S.d (n q))) : Set (Torus S.d (n q))) ≤ S.crit q := by
    unfold side
    refine Finset.sup_le fun i _ => ?_
    refine (ncard_hullCoord_le (a := b0.1 i) (s := b0.2 i) (by have := hs b0 hb0 i; omega)
      (fun x hx => ?_)).trans (hs b0 hb0 i)
    obtain ⟨j, hj, hxj⟩ := hYb x hx i
    exact ⟨j, hj, hxj⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hY : Y.1 ∈ comps (S.omega (q' + 1)) (finOf (hullClosure (S.omega (q' + 1)) (S.crit (q' + 1))
      (H.step q').Z0)) := by
    have h := Y.2
    have hcrit : critOpt S k0 (q' + 1) = some (S.crit (q' + 1)) := by
      simp [critOpt, hq0]
    change Y.1 ∈ comps (S.omega (q' + 1)) (finOf ((H.step q').Zpre (S.omega (q' + 1))
      (critOpt S k0 (q' + 1)))) at h
    rw [hcrit] at h
    exact h
  have hω : 2 ≤ S.omega (q' + 1) := by have := L_add_eleven_le_omega S (q' + 1); omega
  have hbox := hullClosure_box hω _ hY hsmall hside
  obtain ⟨a, s, hh, hs', -⟩ := hull_eq_box (X := ((Y.1 : Finset (Torus S.d (n (q' + 1)))) : Set _))
    ⟨y0, hy0⟩ hsmall
  exact ⟨a, s, hbox.trans hh, hs'⟩

/-- The component `Z` lies in the interior of a small fine box `Q` (one site larger on each side than
the fine box over the box of cubes containing `Z`). -/
theorem exists_bigbox (hkK : k ≤ K) (hW : H.RipeWindow k Z) (hn : 2 * S.crit k + 5 ≤ n k) :
    ∃ (a : Torus S.d (M * n k * S.L ^ k)) (s : Fin S.d → ℕ),
      (∀ i, 1 ≤ s i ∧ 2 * s i < M * n k * S.L ^ k) ∧ H.locFine Z M k ⊆ nbhdNeg 1 (box a s) := by
  classical
  have hcov : CoveredBy S n k Z.1 1 :=
    (hW.unique_box k Z (by have := hW.point.2.1; omega) (Desc.refl Z)).2.1
  obtain ⟨B, hB, hs, hsub⟩ := hcov
  obtain ⟨y0, hy0⟩ := comp_nonempty Z.2
  have hy0' := hsub (show y0 ∈ ((Z.1 : Finset (Torus S.d (n k))) : Set _) from hy0)
  simp only [Set.mem_iUnion, exists_prop] at hy0'
  obtain ⟨b0, hb0, -⟩ := hy0'
  have hZb : ∀ x ∈ ((Z.1 : Finset (Torus S.d (n k))) : Set _), x ∈ box b0.1 b0.2 := by
    intro x hx
    have := hsub hx
    simp only [Set.mem_iUnion, exists_prop] at this
    obtain ⟨b, hb, hxb⟩ := this
    rwa [Finset.card_le_one.mp hB b hb b0 hb0] at hxb
  set Nb := S.L ^ k * M with hNb
  have hNbpos : 0 < Nb := by
    have := NeZero.pos S.L; have := NeZero.pos M; positivity
  have hℓ : M * n k * S.L ^ k = Nb * n k := by rw [hNb]; ring
  refine ⟨fun i => (((Nb * (b0.1 i).val : ℕ)) : ZMod (M * n k * S.L ^ k)) - 1,
    fun i => Nb * b0.2 i + 2, fun i => ⟨(by norm_num : 1 ≤ 2).trans (Nat.le_add_left 2 _), ?_⟩, ?_⟩
  · have h1 := hs b0 hb0 i
    rw [hℓ]
    nlinarith
  · intro x hx
    have hx' : cubeMap n S.L M k k x ∈ Z.1 := (mem_locFine_k hkK).mp hx
    have hbm : blockMap Nb (n k) x ∈ box b0.1 b0.2 := hZb _ hx'
    have := (blockMap_mem_box_iff (d := S.d) (ℓ := M * n k * S.L ^ k) (N := Nb) (m := n k) hℓ b0.1
      (s := b0.2) x).mp hbm
    exact mem_nbhdNeg_box_margin this

/-- **Lemma III.4.3, core case** (Lemma I.3.13 (c)): the core `Z_q` is a union of pairwise
`*`-separated boxes, so every site of `Z` outside it is joined to the boundary of `Q` by an nn path
avoiding the core. -/
theorem shell_path_core (hkK : k ≤ K) (hW : H.RipeWindow k Z) (hk0 : k ≤ k0)
    (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 2 * S.crit j < n j) (hd : 2 ≤ S.d)
    {a : Torus S.d (M * n k * S.L ^ k)} {s : Fin S.d → ℕ}
    (hs : ∀ i, 1 ≤ s i ∧ 2 * s i < M * n k * S.L ^ k)
    (hQ : H.locFine Z M k ⊆ nbhdNeg 1 (box a s)) {x : Torus S.d (M * n k * S.L ^ k)}
    (hx : x ∈ H.locFine Z M k) (hxZ : x ∉ H.locFine Z M (H.bk k Z).q) :
    ∃ z ∈ box a s, z ∉ nbhdNeg 1 (box a s) ∧
      TConn (box a s \ H.locFine Z M (H.bk k Z).q) x z := by
  classical
  set q := (H.bk k Z).q with hq
  have hqk : q ≤ k := by
    have := hW.core_window.1; omega
  have hqk0 : q ≤ k0 := hqk.trans hk0
  set Nq := S.L ^ q * M with hNq
  have hNqpos : 0 < Nq := by
    have := NeZero.pos S.L; have := NeZero.pos M; positivity
  have hℓ : M * n k * S.L ^ k = Nq * n q := fine_eq (hnn_k H hkK) hqk
  -- the ancestors are boxes
  let ι := {Y : H.Comp q // H.Desc q k Y Z}
  have hbox : ∀ Y : ι, ∃ (c : Torus S.d (n q)) (t : Fin S.d → ℕ),
      ((Y.1.1 : Finset (Torus S.d (n q))) : Set (Torus S.d (n q))) = box c t ∧
        ∀ i, 1 ≤ t i ∧ 2 * t i < n q := fun Y =>
    ancestor_box hq1 hqk0 (hW.core_box Y.1 Y.2) (hT q hq1 hqk0)
  choose c0 t0 hY0 hts using hbox
  -- the fine boxes
  let c : ι → Torus S.d (M * n k * S.L ^ k) := fun j i => (((Nq * (c0 j i).val : ℕ)) : ZMod _)
  let t : ι → Fin S.d → ℕ := fun j i => Nq * t0 j i
  have hfine : ∀ j : ι, ∀ y, y ∈ box (c j) (t j) ↔ cubeMap n S.L M k q y ∈ ((j.1.1 : Finset _) : Set _) := by
    intro j y
    rw [hY0 j]
    exact (blockMap_mem_box_iff (d := S.d) (ℓ := M * n k * S.L ^ k) (N := Nq) (m := n q) hℓ (c0 j)
      (s := t0 j) y).symm
  have hZc : H.locFine Z M q = ⋃ j, box (c j) (t j) := by
    ext y
    simp only [Set.mem_iUnion]
    rw [mem_locFine_iff_lin hkK hqk, Finset.mem_coe, mem_lin]
    constructor
    · rintro ⟨Y, hd', hy⟩
      exact ⟨⟨Y, hd'⟩, (hfine ⟨Y, hd'⟩ y).mpr hy⟩
    · rintro ⟨j, hj⟩
      exact ⟨j.1, j.2, (hfine j y).mp hj⟩
  have hsub : ∀ j, box (c j) (t j) ⊆ nbhdNeg 1 (box a s) := by
    intro j y hy
    have hyq : y ∈ H.locFine Z M q := by
      rw [hZc]; exact Set.mem_iUnion.mpr ⟨j, hy⟩
    exact hQ (locFine_mono hkK hqk le_rfl hyq)
  have hsep : ∀ j j' : ι, j ≠ j' → ∀ y ∈ box (c j) (t j), ∀ y' ∈ box (c j') (t j'),
      2 ≤ supDist y y' := by
    intro j j' hne y hy y' hy'
    by_contra hlt
    push Not at hlt
    have hjj : j.1 ≠ j'.1 := fun h => hne (Subtype.ext h)
    have hfar : S.omega q ≤ supDist (cubeMap n S.L M k q y) (cubeMap n S.L M k q y') :=
      hW.core_sep j.1 j'.1 hjj _ ((hfine j y).mp hy) _ ((hfine j' y').mp hy')
    have hnear := blockMap_supDist_le_one_of_le_one (d := S.d) (N := Nq) (m := n q) hℓ hNqpos
      (x := y) (y := y') (by omega)
    have := L_add_eleven_le_omega S q
    have h2 : supDist (cubeMap n S.L M k q y) (cubeMap n S.L M k q y') ≤ 1 := hnear
    omega
  have hP := torus_path_to_shell_of_boxes hd hs (c := c) (t := t)
    (fun j i => Nat.mul_pos hNqpos (hts j i).1)
    (fun j i => by have := (hts j i).2; show 2 * (Nq * t0 j i) < _; rw [hℓ]; nlinarith)
    hsub hsep (hQ hx) (by rw [← hZc]; exact hxZ)
  rw [hZc]
  exact hP

/-- **Lemma III.4.3, non-core case** (Lemma S (a), (b)): the obstacle
`O_i = Ω_iᶜ ∪ Z_q` (`q < i ≤ j`) is a union of pieces over the components of `Z_i`, each of
sup-diameter `≤ L^i M ν_max (crit_k + ω_k) ≤ L^j`; so a block of side `L^j` outside it is joined to
the boundary of `Q`. -/
theorem shell_path_small (hkK : k ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j)
    (hW : H.RipeWindow k Z) (hd : 2 ≤ S.d)
    {a : Torus S.d (M * n k * S.L ^ k)} {s : Fin S.d → ℕ}
    (hs : ∀ i, 1 ≤ s i ∧ 2 * s i < M * n k * S.L ^ k)
    (hQ : H.locFine Z M k ⊆ nbhdNeg 1 (box a s)) {i j : ℕ} (hqi : (H.bk k Z).q ≤ i) (hi1 : 1 ≤ i)
    (hij : i ≤ j) (hjk : j < k)
    (hdiam : S.L ^ i * M * (S.numax k * (S.crit k + S.omega k)) ≤ S.L ^ j)
    (hLj : 2 * S.L ^ j < M * n k * S.L ^ k)
    {b : Torus S.d (M * n k * S.L ^ (k - j))} {x : Torus S.d (M * n k * S.L ^ k)}
    (hxb : jBlock S.d S.L (M * n k) k j x = b)
    (hbQ : ∀ x', jBlock S.d S.L (M * n k) k j x' = b → x' ∈ H.locFine Z M k)
    (hbO : ∀ x', jBlock S.d S.L (M * n k) k j x' = b →
      x' ∈ (H.locGen Z M hkK hL hR).Ω i ∧ x' ∉ H.locFine Z M (H.bk k Z).q) :
    ∃ z ∈ box a s, z ∉ nbhdNeg 1 (box a s) ∧
      TConn (box a s \ ((↑((H.locGen Z M hkK hL hR).Ω i))ᶜ ∪ H.locFine Z M (H.bk k Z).q)) x z := by
  classical
  set G := H.locGen Z M hkK hL hR with hG
  set q := (H.bk k Z).q with hq
  have hik : i ≤ k := by omega
  set O : Set (Torus S.d (M * n k * S.L ^ k)) :=
    (↑(G.Ω i))ᶜ ∪ H.locFine Z M q with hO
  have hOsub : O ⊆ H.locFine Z M i := by
    intro y hy
    rcases hy with hy | hy
    · exact compl_Omega_subset (hkK := hkK) (hL := hL) (hR := hR) hi1 hik hy
    · exact locFine_mono hkK hqi hik hy
  set C := comps (S.omega i) (H.lin i k Z) with hC
  let A : ↥C → Set (Torus S.d (M * n k * S.L ^ k)) := fun m =>
    {y | cubeMap n S.L M k i y ∈ (m.1 : Finset (Torus S.d (n i)))} ∩ O
  have hUnion : (⋃ m, A m) = O := by
    ext y
    constructor
    · intro hy
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
      exact hm.2
    · intro hy
      have hz := hOsub hy
      rw [mem_locFine_iff_lin hkK hik, Finset.mem_coe] at hz
      obtain ⟨Y, hY, hyY⟩ := mem_comp_self (ω := S.omega i) hz
      exact Set.mem_iUnion.mpr ⟨⟨Y, hY⟩, hyY, hy⟩
  have hAQ : ∀ m, A m ⊆ nbhdNeg 1 (box a s) := fun m y hy =>
    hQ (locFine_mono hkK hik le_rfl (hOsub hy.2))
  have hNpos : 0 < S.L ^ i * M := by
    have := NeZero.pos S.L; have := NeZero.pos M; positivity
  have hsep : ∀ m m', m ≠ m' → ∀ y ∈ A m, ∀ y' ∈ A m', 2 ≤ supDist y y' := by
    intro m m' hne y hy y' hy'
    by_contra hlt
    push Not at hlt
    have hfar := comps_sep m.2 m'.2 (fun h => hne (Subtype.ext h)) hy.1 hy'.1
    have hnear := blockMap_supDist_le_one_of_le_one (d := S.d) (N := S.L ^ i * M) (m := n i)
      (fine_eq (hnn_k H hkK) hik) hNpos (x := y) (y := y') (by omega)
    have := L_add_eleven_le_omega S i
    have h2 : supDist (cubeMap n S.L M k i y) (cubeMap n S.L M k i y') ≤ 1 := hnear
    omega
  -- the block as a box
  set c : Torus S.d (M * n k * S.L ^ k) := fun i' => (((S.L ^ j * (b i').val : ℕ)) : ZMod _) with hc
  set t : Fin S.d → ℕ := fun _ => S.L ^ j with ht
  have hbox : ∀ x', x' ∈ box c t ↔ jBlock S.d S.L (M * n k) k j x' = b := fun x' =>
    (jBlock_mem_box_iff hjk.le b x').symm
  have hxA : x ∉ ⋃ m, A m := by
    rw [hUnion]
    intro hx
    rcases hx with hx | hx
    · exact hx (hbO x hxb).1
    · exact (hbO x hxb).2 hx
  have key := exists_shell_path_of_small_pieces hd hs (A := A) hAQ hsep (hQ (hbQ x hxb)) hxA
    (c := c) (t := t) (fun _ => Nat.one_le_pow _ _ (NeZero.pos S.L)) (fun _ => hLj)
    (fun x' hx' => ?_) ((hbox x).mpr hxb) ⟨0, by omega⟩ (fun m y hy z hz => ?_)
  · rw [hUnion] at key
    exact key
  · -- the block lies in `Q ∖ ⋃ A`
    have hx'b := (hbox x').mp hx'
    refine ⟨nbhdNeg_subset 1 _ (hQ (hbQ x' hx'b)), ?_⟩
    rw [hUnion]
    intro hO'
    rcases hO' with h | h
    · exact h (hbO x' hx'b).1
    · exact (hbO x' hx'b).2 h
  · have hi : S.k1 k ≤ i := by rw [hW.core_k1]; exact hqi
    have := fine_diam_le hkK hW hi hik m.2 hy.1 hz.1
    show supDist y z < S.L ^ j + 1
    omega

/-- **Lemma III.4.3 (paths avoid the core and the deep obstacles; ARCH Lemma CH (a))**.  From every
site `x` of a window block `y` of layer `j` there is a nearest-neighbour path to a site of
`Ω_k ∩ Z`, all of whose sites except the last lie in `⋃_{i = i₀}^{k-1} Λ_i ∖ Z_{k₁}`,
`i₀ = max {k₁, j - h_k + 2}`. -/
theorem path_avoids_obstacles [NeZero S.M] (hkK : k ≤ K) (hL : 2 ≤ S.L)
    (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j) (hW : H.RipeWindow k Z) (hk0 : k ≤ k0)
    (hq1 : 1 ≤ (H.bk k Z).q) (hT : ∀ j, 1 ≤ j → j ≤ k0 → 2 * S.crit j + 5 ≤ n j)
    {j : ℕ} (hjk : j < k) {y : BlockV S.d S.L (S.M * n k) k}
    (hy : IsWindowBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (S.k1 k) y)
    (hyj : y.1 = j) {x : Torus S.d (S.M * n k * S.L ^ k)} (hx : x ∈ y.sites) :
    ∃ (N : ℕ) (p : ℕ → Torus S.d (S.M * n k * S.L ^ k)), 0 < N ∧ p 0 = x ∧
      (∀ m < N, NNAdj (p m) (p (m + 1))) ∧
      (∀ m < N, ∃ i, S.chainFloor (S.k1 k) k j ≤ i ∧ i < k ∧
        p m ∈ (H.locGen Z S.M hkK hL hR).layer i ∧ p m ∉ H.locFine Z S.M (S.k1 k)) ∧
      p N ∈ (H.locGen Z S.M hkK hL hR).Ω k ∧ p N ∈ H.locFine Z S.M k := by
  classical
  set G := H.locGen Z S.M hkK hL hR with hG
  have hqk1 : S.k1 k = (H.bk k Z).q := hW.core_k1
  have hkk1 : 1 ≤ S.k1 k := by rw [hqk1]; exact hq1
  have hk1j : S.k1 k ≤ j := by
    obtain ⟨hh1, -, -⟩ := hy; rw [hyj] at hh1; exact hh1
  obtain ⟨j', b⟩ := y
  simp only at hyj
  subst hyj
  have hS := H.F.ok
  have hdim : 2 ≤ S.d := by have := hS.three_le_d; omega
  have hk0' : (H.bk k Z).q ≤ k := by have := hW.core_window.1; omega
  have hkq : (H.bk k Z).q < k := by
    have := hW.core_window.1
    have : 1 ≤ S.nq (H.bk k Z).q := by unfold Setting.nq; omega
    omega
  -- the sites of the block
  have hblock : ∀ x', jBlock S.d S.L (S.M * n k) k j' x' = b →
      x' ∈ G.layer j' ∧ x' ∉ H.locFine Z S.M (S.k1 k) := fun x' hx' => hy.2.2 x' hx'
  have hblockZ : ∀ x', jBlock S.d S.L (S.M * n k) k j' x' = b → x' ∈ H.locFine Z S.M k := by
    intro x' hx'
    have hl := (hblock x' hx').1
    have hnot : x' ∉ G.Ω (j' + 1) := (G.mem_layer.1 hl).2
    exact locFine_mono hkK (by omega : j' + 1 ≤ k) le_rfl
      (compl_Omega_subset (hkK := hkK) (hL := hL) (hR := hR) (by omega) (by omega) hnot)
  -- the big box
  obtain ⟨a, s, hs, hQ⟩ := exists_bigbox (M := S.M) hkK hW (by
    have := hT k (by omega) hk0; omega)
  set i0 := S.chainFloor (S.k1 k) k j' with hi0
  have hi0j : i0 ≤ j' := Setting.chainFloor_le hk1j
  have hk1i0 : S.k1 k ≤ i0 := Setting.le_chainFloor _ _ _
  have hx0 := hblock x hx
  have hxQ : x ∈ nbhdNeg 1 (box a s) := hQ (hblockZ x hx)
  set O : Set (Torus S.d (S.M * n k * S.L ^ k)) :=
    (↑(G.Ω i0))ᶜ ∪ H.locFine Z S.M (S.k1 k) with hO
  have hxO : x ∉ O := by
    intro h
    rcases h with h | h
    · exact h (G.Ω_antitone (by omega) hi0j (by omega) (G.mem_layer.1 hx0.1).1)
    · exact hx0.2 h
  -- a path to the boundary of `Q`
  have hTC : ∃ z ∈ box a s, z ∉ nbhdNeg 1 (box a s) ∧ TConn (box a s \ O) x z := by
    by_cases hcase : S.k1 k < i0
    · -- non-core case
      have hh : i0 = j' + 2 - S.h k := by
        unfold Setting.chainFloor at hi0
        omega
      have hh2 : S.h k ≤ j' + 2 := by omega
      have hdiamR : (S.L : ℝ) ^ i0 * S.M * (S.numax k * (S.crit k + S.omega k)) ≤ (S.L : ℝ) ^ j' := by
        have h1 := hS.pow_h_ge k
        have hLpos : (0 : ℝ) < (S.L : ℝ) ^ i0 := pow_pos (by exact_mod_cast (by omega : 0 < S.L)) _
        calc (S.L : ℝ) ^ i0 * S.M * (S.numax k * (S.crit k + S.omega k))
            = (S.L : ℝ) ^ i0 * ((S.numax k : ℝ) * S.M * (S.crit k + S.omega k)) := by ring
          _ ≤ (S.L : ℝ) ^ i0 * (S.L : ℝ) ^ (S.h k - 2) := mul_le_mul_of_nonneg_left h1 hLpos.le
          _ = (S.L : ℝ) ^ j' := by
              rw [← pow_add]; congr 1; omega
      have hdiam : S.L ^ i0 * S.M * (S.numax k * (S.crit k + S.omega k)) ≤ S.L ^ j' := by
        exact_mod_cast hdiamR
      have hLj : 2 * S.L ^ j' < S.M * n k * S.L ^ k := by
        have hnk : 3 ≤ n k := by have := hT k (by omega) hk0; unfold Setting.crit at this; omega
        have hM1 : 1 ≤ S.M := hS.one_le_M
        have h1 : S.L ^ j' ≤ S.L ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have h2 : 2 * S.L ^ (k - 1) ≤ S.L ^ k := by
          calc 2 * S.L ^ (k - 1) ≤ S.L * S.L ^ (k - 1) := Nat.mul_le_mul_right _ hL
            _ = S.L ^ k := by rw [← pow_succ']; congr 1; omega
        have h3 : S.L ^ k < S.L ^ k * 3 := by
          have : 0 < S.L ^ k := by have := NeZero.pos S.L; positivity
          omega
        have h4 : S.L ^ k * 3 ≤ S.M * n k * S.L ^ k := by
          calc S.L ^ k * 3 ≤ S.L ^ k * (S.M * n k) :=
                Nat.mul_le_mul_left _ (by nlinarith)
            _ = S.M * n k * S.L ^ k := by ring
        omega
      have hi1 : 1 ≤ i0 := by omega
      have := shell_path_small (M := S.M) hkK hL hR hW hdim hs hQ (i := i0) (j := j')
        (by omega) hi1 hi0j hjk hdiam hLj hx (fun x' hx' => hblockZ x' hx') (fun x' hx' => by
          refine ⟨G.Ω_antitone (by omega) hi0j (by omega) (G.mem_layer.1 (hblock x' hx').1).1,
            ?_⟩
          rw [← hqk1]; exact (hblock x' hx').2)
      rw [hO, hqk1]
      exact this
    · -- core case
      have hi0eq : i0 = S.k1 k := by omega
      have hOeq : O = H.locFine Z S.M (S.k1 k) := by
        ext y'
        constructor
        · intro hy'
          rcases hy' with hy' | hy'
          · have := compl_Omega_subset (hkK := hkK) (hL := hL) (hR := hR) (M := S.M) (Z := Z)
              (by omega) (by omega) hy'
            rw [hi0eq] at this
            exact this
          · exact hy'
        · intro hy'; exact Or.inr hy'
      have hcore := shell_path_core (M := S.M) hkK hW hk0 hq1 (fun j hj1 hj0 => by
          have := hT j hj1 hj0; omega) hdim hs hQ (hblockZ x hx) (by rw [← hqk1]; exact hx0.2)
      rw [hOeq, hqk1]
      exact hcore
  obtain ⟨z, hzQ, hzn, hz⟩ := hTC
  -- `z ∈ Ω_k`
  have hzk : z ∈ (G.Ω k : Set _) := by
    by_contra hnk
    exact hzn (hQ (compl_Omega_subset (hkK := hkK) (hL := hL) (hR := hR) (M := S.M) (Z := Z)
      (by omega) le_rfl hnk))
  have hxk : x ∉ (G.Ω k : Set _) := by
    intro h
    exact (G.mem_layer.1 hx0.1).2 (G.Ω_antitone (by omega) (by omega) (by omega) h)
  have hxS : x ∈ box a s \ O := ⟨nbhdNeg_subset 1 _ hxQ, hxO⟩
  obtain ⟨N, p, hN, hp0, hadj, hmem, hpE, hpS⟩ := exists_first_hit hxk hxS hz hzk
  refine ⟨N, p, hN, hp0, hadj, fun m hm => ?_, hpE, ?_⟩
  · -- the sites before the last lie in the window layers
    obtain ⟨hmS, hmE⟩ := hmem m hm
    have hmE' : p m ∉ G.Ω k := fun h => hmE (Finset.mem_coe.mpr h)
    have hmO : p m ∉ O := hmS.2
    have hmΩ : p m ∈ G.Ω i0 := by
      by_contra hh
      exact hmO (Or.inl (by simpa using hh))
    have hmZ : p m ∉ H.locFine Z S.M (S.k1 k) := fun h => hmO (Or.inr h)
    obtain ⟨i, hi1, hi2, hil⟩ := exists_layer_of_mem (hkK := hkK) (hL := hL) (hR := hR) (M := S.M)
      (Z := Z) (by omega) hmΩ hmE'
    exact ⟨i, hi1, hi2, hil, hmZ⟩
  · obtain ⟨hmS, hmE⟩ := hmem (N - 1) (by omega)
    have hmE' : p (N - 1) ∉ G.Ω k := fun h => hmE (Finset.mem_coe.mpr h)
    have hN1 : N - 1 + 1 = N := by omega
    have hnn := hadj (N - 1) (by omega)
    rw [hN1] at hnn
    exact mem_locFine_of_nn (hkK := hkK) (hL := hL) (hR := hR) (M := S.M) (Z := Z) (by omega) hmE' hnn

end RegionHistory

end Balaban.LargeField
