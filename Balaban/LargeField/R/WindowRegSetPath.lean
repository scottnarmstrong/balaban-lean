module

public import Balaban.LargeField.R.WindowRegSetBond
public import Balaban.LargeField.R.WindowRegSet
import Mathlib.Tactic.Linarith

/-!
# The path of `T` to the window (COLLAR-FIX §2, inner face): torus geometry

* `exists_monoWalk`: two points of the torus at `ℓ¹`-cyclic distance `≤ P` are joined by a
  coordinate-monotone nearest-neighbour walk of at most `P` steps along which every coordinate
  distance to the endpoint does not increase;
* `exists_block_lift`: a cube at sup-distance `≤ ρ` from the cube of a block `b₀` contains a block at
  sup-distance `≤ M ρ` from `b₀`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale

section Walk

variable {d m : ℕ} [NeZero m]

/-- A coordinate-monotone nearest-neighbour walk of at most `P` steps (the `ℓ¹`-cyclic distance bound). -/
theorem exists_monoWalk : ∀ (P : ℕ) (u v : Torus d m), (∑ i, cycNorm m (u i - v i)) ≤ P →
    ∃ (n : ℕ) (p : ℕ → Torus d m), n ≤ P ∧ p 0 = u ∧ p n = v ∧
      (∀ i < n, ∃ μ : Fin d, p (i + 1) = p i + Pi.single μ 1 ∨ p i = p (i + 1) + Pi.single μ 1) ∧
      ∀ i ≤ n, ∀ c, cycNorm m (p i c - v c) ≤ cycNorm m (u c - v c) := by
  intro P
  induction P with
  | zero =>
    intro u v h
    have h0 : ∀ i, cycNorm m (u i - v i) = 0 := fun i =>
      Nat.le_zero.1 ((Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans h)
    have huv : u = v := funext fun i => sub_eq_zero.1 ((cycNorm_zero_iff _).1 (h0 i))
    exact ⟨0, fun _ => u, le_rfl, rfl, huv, fun i hi => absurd hi (by omega), fun i _ c => le_rfl⟩
  | succ P ih =>
    intro u v h
    by_cases hz : ∀ i, cycNorm m (u i - v i) = 0
    · have huv : u = v := funext fun i => sub_eq_zero.1 ((cycNorm_zero_iff _).1 (hz i))
      exact ⟨0, fun _ => u, Nat.zero_le _, rfl, huv, fun i hi => absurd hi (by omega),
        fun i _ c => le_rfl⟩
    push Not at hz
    obtain ⟨c, hc⟩ := hz
    obtain ⟨t, ht, htc⟩ := (cycNorm_le_iff (n := m) (u c - v c) (cycNorm m (u c - v c))).1 le_rfl
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hc
      have : u c - v c = 0 := by rw [← htc]; simp
      rw [this]; simp [cycNorm]
    -- the step `s = -sign t`
    obtain ⟨s, hs1, hs⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ |t + s| + 1 = |t| := by
      rcases lt_or_gt_of_ne ht0 with h1 | h1
      · refine ⟨1, Or.inl rfl, ?_⟩
        rw [abs_of_neg h1, abs_of_nonpos (by omega)]; omega
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [abs_of_pos h1, abs_of_nonneg (by omega)]; omega
    set u' : Torus d m := u + Pi.single c (s : ZMod m) with hu'
    have hnorm : cycNorm m (u' c - v c) + 1 ≤ cycNorm m (u c - v c) := by
      have : u' c - v c = ((t + s : ℤ) : ZMod m) := by
        rw [hu']; simp only [Pi.add_apply, Pi.single_eq_same]; push_cast; rw [htc]; ring
      rw [this]
      have h1 := (cycNorm_le_iff (n := m) ((t + s : ℤ) : ZMod m) (t + s).natAbs).2
        ⟨t + s, by simp, rfl⟩
      have h2 : (t + s).natAbs + 1 ≤ cycNorm m (u c - v c) := by
        have : ((t + s).natAbs : ℤ) + 1 ≤ (cycNorm m (u c - v c) : ℤ) := by
          rw [Int.natCast_natAbs]; linarith [ht]
        exact_mod_cast this
      omega
    have hother : ∀ i, i ≠ c → u' i - v i = u i - v i := by
      intro i hi; rw [hu']; simp [Pi.single_eq_of_ne hi]
    have hsum : (∑ i, cycNorm m (u' i - v i)) ≤ P := by
      have hle : ∀ i, cycNorm m (u' i - v i) + (if i = c then 1 else 0) ≤ cycNorm m (u i - v i) := by
        intro i
        by_cases hi : i = c
        · subst hi; simpa using hnorm
        · rw [hother i hi]; simp [hi]
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
      rw [Finset.sum_add_distrib] at this
      simp at this
      omega
    obtain ⟨n, p, hn, hp0, hpn, hpa, hpd⟩ := ih u' v hsum
    refine ⟨n + 1, fun i => match i with | 0 => u | i + 1 => p i, by omega, rfl, hpn, ?_, ?_⟩
    · intro i hi
      match i, hi with
      | 0, _ =>
        refine ⟨c, ?_⟩
        rcases hs1 with rfl | rfl
        · exact Or.inl (by simpa [hp0] using hu')
        · refine Or.inr ?_
          simp only [hp0, hu']
          rw [add_assoc, ← Pi.single_add]
          simp
      | i + 1, hi => exact hpa i (by omega)
    · intro i hi c'
      match i, hi with
      | 0, _ => exact le_rfl
      | i + 1, hi =>
        refine (hpd i (by omega) c').trans ?_
        by_cases hc' : c' = c
        · subst hc'; omega
        · rw [hother c' hc']

end Walk

section Lift

/-- A cube at sup-distance `≤ ρ` from the cube of the block `b₀` contains a block at sup-distance
`≤ M ρ` from `b₀` (the block with the same offset inside its cube). -/
theorem exists_block_lift {d ℓ M q : ℕ} [NeZero ℓ] [NeZero q] (hℓ : ℓ = M * q) (b0 : Torus d ℓ)
    (e : Torus d q) {ρ : ℕ} (h : supDist (blockMap M q b0) e ≤ ρ) :
    ∃ t : Torus d ℓ, blockMap M q t = e ∧ supDist t b0 ≤ M * ρ := by
  have hM : 0 < M := pos_left_of_eq hℓ
  have hq : 0 < q := pos_right_of_eq hℓ
  have hs : ∀ i, ∃ s : ℤ, |s| ≤ ρ ∧ (s : ZMod q) = e i - blockCoord M q (b0 i) := by
    intro i
    have h1 : cycNorm q (e i - blockCoord M q (b0 i)) ≤ ρ := by
      rw [cycNorm_sub_comm]; exact (cycNorm_le_supDist _ _ i).trans h
    obtain ⟨s, hs, hs'⟩ := (cycNorm_le_iff _ _).1 h1
    exact ⟨s, by exact_mod_cast hs, hs'⟩
  choose s hsρ hsq using hs
  let s' : Fin d → ℕ := fun i => (s i % (q : ℤ)).toNat
  have hs'cast : ∀ i, ((s' i : ℕ) : ZMod q) = (s i : ZMod q) := by
    intro i
    have h0 : 0 ≤ s i % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
    simp only [s']
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0, ZMod.intCast_mod]
  refine ⟨fun i => b0 i + ((M * s' i : ℕ) : ZMod ℓ), ?_, ?_⟩
  · funext i
    simp only [blockMap]
    rw [blockCoord_add_natCast hℓ, Nat.mul_comm M, Nat.add_mul_div_right _ _ hM,
      Nat.div_eq_of_lt (Nat.mod_lt _ hM), zero_add, hs'cast, hsq]
    ring
  · rw [supDist_le_iff]
    intro i
    simp only [add_sub_cancel_left]
    rw [cycNorm_le_iff]
    refine ⟨M * s i, ?_, ?_⟩
    · rw [abs_mul, abs_of_nonneg (by exact_mod_cast hM.le : (0 : ℤ) ≤ M)]
      push_cast
      exact mul_le_mul_of_nonneg_left (hsρ i) (by positivity)
    · have e1 : ((M * s' i : ℕ) : ℤ) = M * s i - ℓ * (s i / q) := by
        have : (s' i : ℤ) = s i % q := Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hq.ne'))
        push_cast
        rw [this, Int.emod_def, hℓ]; push_cast; ring
      have e2 : ((M * s' i : ℕ) : ZMod ℓ) = (((M * s' i : ℕ) : ℤ) : ZMod ℓ) := by simp
      rw [e2, e1]
      push_cast
      simp
end Lift

section Adj

/-- A nearest-neighbour step on a torus of side `≥ 2` is an `AdjT` step. -/
theorem adjT_of_step {d m : ℕ} [NeZero m] (hm : 2 ≤ m) {a b : Torus d m} (μ : Fin d)
    (h : b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1) : AdjT a b := by
  have : Fact (1 < m) := ⟨hm⟩
  refine ⟨?_, μ, h⟩
  rintro rfl
  have h1 : a μ = a μ + 1 := by
    rcases h with h | h
    · simpa using congrFun h μ
    · simpa using congrFun h μ
  simp at h1

end Adj

/-- `⌈M ρ-bound⌉`: `(a + M - 1) / M ≤ ρ` when `a ≤ M ρ`. -/
theorem div_ceil_le {M ρ a : ℕ} (hM : 0 < M) (h : a ≤ M * ρ) : (a + M - 1) / M ≤ ρ := by
  refine Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hM).2 ?_)
  have e : (ρ.succ) * M = M * ρ + M := by rw [Nat.succ_mul]; ring
  rw [e]
  generalize M * ρ = X at h ⊢
  omega

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) {k : ℕ} (Z : H.Comp k) {M : ℕ} [NeZero M] [NeZero S.L]

/-- **Lemma I.3.5 (g)** in the form used for the path: a cube within `2⌊R_{q-1}⌋ + 6` of a cube off `Z_q`
lies in `Ω_q` (`Ω_q` contains `(((Z_q)ᶜ)^{≈2})^{∼4}`; no removals in the localization). -/
theorem mem_regOmega_of_near (hR0 : ∀ i, 0 ≤ R i) {q : ℕ} (hq1 : 1 ≤ q) {y e : Torus S.d (n q)}
    (he : e ∈ (regZ H Z q)ᶜ) (hd : supDist y e ≤ 2 * ⌊R (q - 1)⌋₊ + 6) : y ∈ regOmega H Z q := by
  obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
  have hO := coreW_nbhd_subset_Omega (H.locRH k Z) (fun j => rfl) (hR0 i) (m := 3) (by norm_num)
  apply hO
  simp only [thick2, thick, nbhd_nbhd]
  refine mem_nbhd.2 ⟨e, he, ?_⟩
  have hd' : supDist y e ≤ 2 * ⌊R i⌋₊ + 6 := by simpa using hd
  omega

variable {H Z} {g : Geo S n R M} (hkK : k ≤ K) (hW : H.RipeWindow k Z)

/-- **The path of `T` to the window** (COLLAR-FIX §2, inner face: "follow a coordinate-monotone block path
to the closest face of `Z_{k₁}ᶜ` and stop at the first window block"; LF-RECONSTRUCTION Lemma III.4.6).
For **every** site `x ∈ Z_{k₁} ∩ Ω₁(𝔹_{k₁}(W))` of the core piece (not only those in the top layer `k₁`,
so `hcoreTop` is not needed), the `k₁`-block of `x` is joined to a window block (a block `s ∈ Λ_{k₁}(𝔹_k)`,
`s ∉ Z_{k₁}`) by a path of at most `d (2⌊R_{k₁-1}⌋ + 3) M` adjacent `k₁`-blocks, all in `regSetTExt`; all but
the last lie in `regSetT`.  Source: the core reaches `2⌊R_{k₁-1}⌋ + 3` cubes into `Z_{k₁}` (Lemma II.2.3 (c)
for `W = (Z_{k₁}ᶜ)^{≈2}`), `Ω_{k₁}ᶜ` starts `2⌊R_{k₁-1}⌋ + 6` cubes in (Lemma I.3.5 (g)), and the first block
of the path off `Z_{k₁}` is in the layer `k₁` of `𝔹_k` (Lemma I.3.5 (f), `windowOfHistory_hexitLayer`). -/
theorem windowOfHistory_regPath {x : Torus S.d (M * n k * S.L ^ k)}
    (hxZ : x ∈ (windowOfHistory H Z g hkK hW).Zk1)
    (hx1 : x ∈ (windowOfHistory H Z g hkK hW).core.Ω 1) :
    ∃ m ≤ S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * M),
      TPathToWindow (windowOfHistory H Z g hkK hW).full (windowOfHistory H Z g hkK hW).Zk1 (S.k1 k)
        (regSetTExt H Z M (S.k1 k)) (jBlock S.d S.L (M * n k) k (S.k1 k) x) m := by
  classical
  have hq1 : 1 ≤ S.k1 k := hW.k1_pos hkK
  have hqk : S.k1 k ≤ k := k1_le hW
  have hnn : ∀ i, i < k → n i = S.L * n (i + 1) := fun i hi => H.F.hnn i (lt_of_lt_of_le hi hkK)
  have hm : M * n k * S.L ^ (k - S.k1 k) = M * n (S.k1 k) := by
    rw [nn_eq_pow' hnn hqk]; ring
  have hR0 : ∀ i, 0 ≤ R i := fun i =>
    le_trans (by have := H.F.ok.two_le_Rb; linarith) (g.hRlow i)
  have hM2 : 2 ≤ M * n k * S.L ^ (k - S.k1 k) := by
    have h1 := g.hc
    have h2 : 1 ≤ g.M1 := Nat.pos_of_ne_zero (NeZero.ne g.M1)
    have h3 : 14 ≤ M := by rw [g.hM]; nlinarith
    have h4 : 1 ≤ n k := Nat.pos_of_ne_zero (NeZero.ne _)
    have h5 : 1 ≤ S.L ^ (k - S.k1 k) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne _))
    have := Nat.mul_le_mul (Nat.mul_le_mul h3 h4) h5
    omega
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  -- the cube of `x` and a cube off `Z_{k₁}` close to it
  have hxZ' : cubeMap n S.L M k (S.k1 k) x ∈ regZ H Z (S.k1 k) := by
    rw [windowOfHistory_Zk1, mem_locFineFin] at hxZ; exact hxZ
  have hc0 : cubeMap n S.L M k (S.k1 k) x ∈ nbhd 1 (coreW H Z (S.k1 k)) :=
    cubeMap_nbhd_of_mem_cast (g := g) H.F.ok.two_le_L hnn hqk (A := coreW H Z (S.k1 k))
      (min_le_right _ _) hx1
  obtain ⟨w, hw, h1⟩ := mem_nbhd.1 hc0
  have hw' := hw
  simp only [coreW, thick2, thick, nbhd_nbhd] at hw'
  obtain ⟨e, he, h2⟩ := mem_nbhd.1 hw'
  have hce : supDist (cubeMap n S.L M k (S.k1 k) x) e ≤ 2 * ⌊R (S.k1 k - 1)⌋₊ + 3 :=
    (supDist_triangle _ w e).trans (by omega)
  -- the block of `x` and the lifted target block
  have hb0 : blockCube S n M k (S.k1 k) (jBlock S.d S.L (M * n k) k (S.k1 k) x) =
      cubeMap n S.L M k (S.k1 k) x := cubeMap_jBlock hnn hqk x
  obtain ⟨t, htq, hdt⟩ := exists_block_lift (ℓ := M * n k * S.L ^ (k - S.k1 k)) (q := n (S.k1 k))
    (ρ := 2 * ⌊R (S.k1 k - 1)⌋₊ + 3) hm (jBlock S.d S.L (M * n k) k (S.k1 k) x) e
    (show supDist (blockCube S n M k (S.k1 k) (jBlock S.d S.L (M * n k) k (S.k1 k) x)) e ≤ _ by
      rw [hb0]; exact hce)
  have hsum : (∑ i, cycNorm (M * n k * S.L ^ (k - S.k1 k))
      (jBlock S.d S.L (M * n k) k (S.k1 k) x i - t i)) ≤ S.d * (M * (2 * ⌊R (S.k1 k - 1)⌋₊ + 3)) := by
    calc _ ≤ ∑ _i : Fin S.d, M * (2 * ⌊R (S.k1 k - 1)⌋₊ + 3) :=
          Finset.sum_le_sum fun i _ => (cycNorm_le_supDist _ t i).trans (by rw [supDist_comm]; exact hdt)
      _ = _ := by simp
  obtain ⟨nn, p, hnn', hp0, hpn, hpa, hpd⟩ := exists_monoWalk _ _ t hsum
  have hpt : ∀ i ≤ nn, supDist (p i) t ≤ M * (2 * ⌊R (S.k1 k - 1)⌋₊ + 3) := by
    intro i hi
    refine supDist_le_iff.2 fun c => (hpd i hi c).trans ?_
    rw [hp0] at *
    exact (cycNorm_le_supDist _ t c).trans (by rw [supDist_comm]; exact hdt)
  have hcube : ∀ i ≤ nn, supDist (blockCube S n M k (S.k1 k) (p i)) e ≤ 2 * ⌊R (S.k1 k - 1)⌋₊ + 3 := by
    intro i hi
    have h := supDist_blockMap_le (L := M) (m := n (S.k1 k)) hm (p i) t
    rw [← htq]
    exact h.trans (div_ceil_le hMpos (hpt i hi))
  have hhit : ∃ i, i ≤ nn ∧ blockCube S n M k (S.k1 k) (p i) ∉ regZ H Z (S.k1 k) :=
    ⟨nn, le_rfl, by rw [hpn]; show blockMap M (n (S.k1 k)) t ∉ _; rw [htq]; exact he⟩
  obtain ⟨n0, hn0spec, hn0min⟩ : ∃ n0, (n0 ≤ nn ∧ blockCube S n M k (S.k1 k) (p n0) ∉
      regZ H Z (S.k1 k)) ∧ ∀ i < n0, ¬ (i ≤ nn ∧ blockCube S n M k (S.k1 k) (p i) ∉
      regZ H Z (S.k1 k)) := ⟨Nat.find hhit, Nat.find_spec hhit, fun i hi => Nat.find_min hhit hi⟩
  have hin : ∀ i < n0, p i ∈ regSetT H Z M (S.k1 k) := by
    intro i hi
    have hi' : i ≤ nn := by have := hn0spec.1; omega
    have hZi : blockCube S n M k (S.k1 k) (p i) ∈ regZ H Z (S.k1 k) := by
      by_contra hc; exact hn0min i hi ⟨hi', hc⟩
    rw [mem_regSetT, regCubes_eq]
    exact ⟨hZi, mem_regOmega_of_near H Z hR0 hq1 he (by have := hcube i hi'; omega)⟩
  have hn0pos : 0 < n0 := by
    by_contra h0
    have h0' : n0 = 0 := by omega
    apply hn0spec.2
    rw [h0', hp0, hb0]; exact hxZ'
  obtain ⟨j, rfl⟩ : ∃ j, n0 = j + 1 := ⟨n0 - 1, by omega⟩
  have hjT := hin j (by omega)
  have hjZ : blockCube S n M k (S.k1 k) (p j) ∈ regZ H Z (S.k1 k) := by
    rw [mem_regSetT, regCubes_eq] at hjT; exact hjT.1
  obtain ⟨μ, hμ⟩ := hpa j (by have := hn0spec.1; omega)
  have hadj : AdjT (p j) (p (j + 1)) := adjT_of_step hM2 μ hμ
  have hℓ := side_eq (N₀ := M * n k) (L := S.L) (k := k) (j := S.k1 k) hqk
  obtain ⟨x1, x2, hjx1, hjx2, hadjx⟩ : ∃ x1 x2 : Torus S.d (M * n k * S.L ^ k),
      jBlock S.d S.L (M * n k) k (S.k1 k) x1 = p j ∧
      jBlock S.d S.L (M * n k) k (S.k1 k) x2 = p (j + 1) ∧ Adj x2 x1 := by
    rcases hμ with hμ | hμ
    · obtain ⟨x, hx, hx'⟩ := exists_adjSites_of_adjT hℓ μ hμ
      exact ⟨x, x + Pi.single μ 1, hx, hx', ⟨μ, Or.inr rfl⟩⟩
    · obtain ⟨x, hx, hx'⟩ := exists_adjSites_of_adjT hℓ μ hμ
      exact ⟨x + Pi.single μ 1, x, hx', hx, ⟨μ, Or.inl rfl⟩⟩
  have hx1Z : x1 ∈ (windowOfHistory H Z g hkK hW).Zk1 := by
    rw [windowOfHistory_Zk1, mem_locFineFin]
    show cubeMap n S.L M k (S.k1 k) x1 ∈ regZ H Z (S.k1 k)
    rw [← cubeMap_jBlock hnn hqk x1, hjx1]; exact hjZ
  have hx2Z : x2 ∉ (windowOfHistory H Z g hkK hW).Zk1 := by
    rw [windowOfHistory_Zk1, mem_locFineFin]
    show cubeMap n S.L M k (S.k1 k) x2 ∉ regZ H Z (S.k1 k)
    rw [← cubeMap_jBlock hnn hqk x2, hjx2]; exact hn0spec.2
  have hl := windowOfHistory_hexitLayer (g := g) hkK hW x2 hx2Z x1 hadjx hx1Z
  refine ⟨j + 1, ?_, p, hp0, ?_, ?_, x2, hl, hx2Z, hjx2⟩
  · calc j + 1 ≤ nn := hn0spec.1
      _ ≤ S.d * (M * (2 * ⌊R (S.k1 k - 1)⌋₊ + 3)) := hnn'
      _ = _ := by ring
  · intro i hi
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact regSetT_subset_ext H Z M _ (hin i h)
    · have : i = j + 1 := by omega
      subst this
      exact ⟨p j, hjT, Or.inr hadj⟩
  · intro i hi
    obtain ⟨μ', hμ'⟩ := hpa i (by have := hn0spec.1; omega)
    exact adjT_of_step hM2 μ' hμ'

end RegionHistory

end Balaban.LargeField
