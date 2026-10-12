module

public import Balaban.LargeField.R.WindowRegSetPath
public import Balaban.LargeField.R.DeltaPsiCollarBound
public import Balaban.LargeField.R.WindowOfHistoryCollar
import Mathlib.Tactic.Linarith

/-!
# The inner-collar shell bound (2.2) at the actual window (COLLAR-FIX §2; LF-RECONSTRUCTION III.4.6)

* `windowOfHistory_regPath_in`: the path of `windowOfHistory_regPath` with its membership information
  in the form needed for the telescoping (all blocks before the last in `regSetT`, the last in
  `regSetTExt`); same proof as `windowOfHistory_regPath` (that statement only records `regSetTExt`
  for every block).  It does not use `hcoreTop`.
* `inner_collar_shell_bound_actual`: COLLAR-FIX (2.2) for `c ∈ C_in` of `windowOfHistory H Z g hkK hW`,
  with no geometric hypothesis: `hcT`, `hwT`, `hexitLayer`, `hmargin`, `hZk1top` are theorems of the
  actual window, `hreach` is `windowOfHistory_regPath_in`, and `hcoreTop` is not needed.  The only
  premise is the bond bound `hband` of `regSetT` against `regSetTExt`.  Its derivation from the retained
  characteristic functions is `bond_le_Creg_of_chiDomProp` (constant `C_reg = 3dL e^ε L^{(d-2)/2}`), which
  is stated on the history-horizon torus; transporting it to the window torus is the torus-cast bridge
  not yet formalized, so `hband` stays a named source premise.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Finset Balaban.Background

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} {M : ℕ} [NeZero M] [NeZero S.L]
  {g : Geo S n R M} (hkK : k ≤ K) (hW : H.RipeWindow k Z)

/-- **The regularity path with its membership information** (`windowOfHistory_regPath`, strengthened):
for every `x ∈ Z_{k₁} ∩ Ω₁(𝔹_{k₁}(W))` (any core layer) there are `m ≤ d (2⌊R_{k₁-1}⌋ + 3) M` and adjacent
`k₁`-blocks `u 0 = b_{k₁}(x), …, u m`, all `u i` (`i < m`) in `regSetT`, `u m ∈ regSetTExt`, and
`u m` the block of a window site `s ∈ Λ_{k₁}(𝔹_k) ∖ Z_{k₁}`.  Source: as `windowOfHistory_regPath`. -/
theorem windowOfHistory_regPath_in {x : Torus S.d (M * n k * S.L ^ k)}
    (hxZ : x ∈ (windowOfHistory H Z g hkK hW).Zk1)
    (hx1 : x ∈ (windowOfHistory H Z g hkK hW).core.Ω 1) :
    ∃ m ≤ S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * M),
      ∃ u : ℕ → Torus S.d (M * n k * S.L ^ (k - S.k1 k)),
        u 0 = jBlock S.d S.L (M * n k) k (S.k1 k) x ∧
        (∀ i < m, u i ∈ regSetT H Z M (S.k1 k)) ∧ (∀ i < m, AdjT (u i) (u (i + 1))) ∧
        u m ∈ regSetTExt H Z M (S.k1 k) ∧
        ∃ s ∈ (windowOfHistory H Z g hkK hW).full.layer (S.k1 k),
          s ∉ (windowOfHistory H Z g hkK hW).Zk1 ∧ jBlock S.d S.L (M * n k) k (S.k1 k) s = u m := by
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
  refine ⟨j + 1, ?_, p, hp0, hin, ?_, ⟨p j, hjT, Or.inr hadj⟩, x2, hl, hx2Z, hjx2⟩
  · calc j + 1 ≤ nn := hn0spec.1
      _ ≤ S.d * (M * (2 * ⌊R (S.k1 k - 1)⌋₊ + 3)) := hnn'
      _ = _ := by ring
  · intro i hi
    obtain ⟨μ', hμ'⟩ := hpa i (by have := hn0spec.1; omega)
    exact adjT_of_step hM2 μ' hμ'

/-- Telescoping of the bond bound along a path whose blocks before the last lie in `regSetT`. -/
theorem regPath_dist_le {E : Type*} [PseudoMetricSpace E] (ψ : BlockV S.d S.L (M * n k) k → E) {C : ℝ}
    (hband : ∀ y ∈ regSetT H Z M (S.k1 k), ∀ y' ∈ regSetTExt H Z M (S.k1 k), AdjT y y' →
      dist (ψ ⟨S.k1 k, y⟩) (ψ ⟨S.k1 k, y'⟩) ≤ C)
    {m : ℕ} {u : ℕ → Torus S.d (M * n k * S.L ^ (k - S.k1 k))}
    (huT : ∀ i < m, u i ∈ regSetT H Z M (S.k1 k)) (huA : ∀ i < m, AdjT (u i) (u (i + 1)))
    (hum : u m ∈ regSetTExt H Z M (S.k1 k)) :
    dist (ψ ⟨S.k1 k, u 0⟩) (ψ ⟨S.k1 k, u m⟩) ≤ m * C := by
  have hext : ∀ i ≤ m, u i ∈ regSetTExt H Z M (S.k1 k) := fun i hi => by
    rcases Nat.lt_or_ge i m with h | h
    · exact regSetT_subset_ext H Z M _ (huT i h)
    · have : i = m := by omega
      subst this; exact hum
  exact dist_walk_le (fun v => ψ ⟨S.k1 k, v⟩) u (fun i hi => hband _ (huT i hi) _ (hext (i + 1) hi) (huA i hi))

/-- **Inner-collar shell bound (COLLAR-FIX (2.2)) for the actual window.**  For `c ∈ C_in` of
`windowOfHistory H Z g hkK hW`, the parent spin `ψ(parentBlock 𝔹_k c)` is within `(m_W + 1) C` of the spin of
a window block `s ∈ Λ_{k₁}(𝔹_k) ∖ Z_{k₁}`, `m_W = d (2⌊R_{k₁-1}⌋ + 3) M`, where `C` bounds the bond
`dist (ψ y) (ψ y')` for `y ∈ regSetT`, `y' ∈ regSetTExt` adjacent (`C = C_reg δ_{k₁}`, LFR Definition II.5.6
and Lemma III.4.5).  No `hcoreTop`: the path starts in the block of an adjacent site of `Ω₁(G)`, in the
core (any layer, `windowOfHistory_regPath_in`) or off `Z_{k₁}` (the window block itself,
`windowOfHistory_hexitLayer`). Premise `hband`: the bond bound from the retained characteristic functions
(`bond_le_Creg_of_chiDomProp` on the history torus; its transfer to the window torus is the torus-cast
bridge, not formalized). -/
theorem inner_collar_shell_bound_actual {E : Type*} [PseudoMetricSpace E]
    (ψ : BlockV S.d S.L (M * n k) k → E) {C : ℝ} (hC : 0 ≤ C)
    (hband : ∀ y ∈ regSetT H Z M (S.k1 k), ∀ y' ∈ regSetTExt H Z M (S.k1 k), AdjT y y' →
      dist (ψ ⟨S.k1 k, y⟩) (ψ ⟨S.k1 k, y'⟩) ≤ C)
    {c : Torus S.d (M * n k * S.L ^ k)}
    (hc : c ∈ collarIn (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)) :
    ∃ s ∈ (windowOfHistory H Z g hkK hW).full.layer (S.k1 k),
      s ∉ (windowOfHistory H Z g hkK hW).Zk1 ∧
      dist (ψ (parentBlock (windowOfHistory H Z g hkK hW).full c))
        (ψ (blockOf S.d S.L (M * n k) k (S.k1 k) s)) ≤
        (((S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * M) : ℕ) : ℝ) + 1) * C := by
  have hcT := windowOfHistory_hcT (g := g) hkK hW hc
  have hpar := (windowOfHistory_inner_collar_parent_layer H Z g hkK hW hc).2.2
  obtain ⟨hcol, hcZ⟩ := (mem_collarIn _ _).1 hc
  obtain ⟨-, x, hx, hadj⟩ := (Balaban.Background.mem_collar _).1 hcol
  have hcb := jBlock_eq_or_adjT (k1_le hW) hadj
  -- one step from the block of `c` to an equal or adjacent block of `regSetTExt`
  have step : ∀ b : Torus S.d (M * n k * S.L ^ (k - S.k1 k)), b ∈ regSetTExt H Z M (S.k1 k) →
      (jBlock S.d S.L (M * n k) k (S.k1 k) c = b ∨ AdjT (jBlock S.d S.L (M * n k) k (S.k1 k) c) b) →
      dist (ψ ⟨S.k1 k, jBlock S.d S.L (M * n k) k (S.k1 k) c⟩) (ψ ⟨S.k1 k, b⟩) ≤ C := by
    intro b hb h
    rcases h with rfl | h
    · simpa using hC
    · exact hband _ hcT _ hb h
  rw [hpar]
  have e : blockOf S.d S.L (M * n k) k (S.k1 k) c = ⟨S.k1 k, jBlock S.d S.L (M * n k) k (S.k1 k) c⟩ := rfl
  rw [e]
  by_cases hxZ : x ∈ (windowOfHistory H Z g hkK hW).Zk1
  · have hxcore : x ∈ (windowOfHistory H Z g hkK hW).core.Ω 1 := by
      have := hx
      rw [WindowPieces.windowGenSet_Ω] at this
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at this
      rcases this with (⟨h1, _⟩ | ⟨_, h2, h3⟩) | ⟨_, _, h3⟩
      · exact h1
      · exact absurd hxZ h3
      · exact absurd (windowOfHistory_hZ (g := g) hkK hW hxZ) h3
    obtain ⟨m, hm, u, hu0, huT, huA, hum, s, hs, hsZ, hsu⟩ :=
      windowOfHistory_regPath_in (g := g) hkK hW hxZ hxcore
    refine ⟨s, hs, hsZ, ?_⟩
    have hu0ext : u 0 ∈ regSetTExt H Z M (S.k1 k) := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; exact hum
      · exact regSetT_subset_ext H Z M _ (huT 0 h0)
    have h1 := step (u 0) hu0ext (by
      rw [hu0]
      rcases hcb with h | h
      · exact Or.inl h.symm
      · exact Or.inr (adjT_symm' h))
    have h2 := regPath_dist_le ψ hband huT huA hum
    have e2 : blockOf S.d S.L (M * n k) k (S.k1 k) s = ⟨S.k1 k, u m⟩ := by
      simp only [blockOf]; rw [hsu]
    rw [e2]
    have h3 := dist_triangle (ψ ⟨S.k1 k, jBlock S.d S.L (M * n k) k (S.k1 k) c⟩)
      (ψ ⟨S.k1 k, u 0⟩) (ψ ⟨S.k1 k, u m⟩)
    have hm' : (m : ℝ) ≤ (S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * M) : ℕ) := by exact_mod_cast hm
    nlinarith
  · have hxl := windowOfHistory_hexitLayer (g := g) hkK hW x hxZ c hadj hcZ
    refine ⟨x, hxl, hxZ, ?_⟩
    have hxext := windowOfHistory_hwT (g := g) hkK hW
      (by rw [WindowPieces.windowGenSet_Ω]; rw [WindowPieces.windowGenSet_Ω] at hx; exact hx) hadj hcZ
    have h1 := step _ hxext (by
      rcases hcb with h | h
      · exact Or.inl h.symm
      · exact Or.inr (adjT_symm' h))
    have e2 : blockOf S.d S.L (M * n k) k (S.k1 k) x = ⟨S.k1 k, jBlock S.d S.L (M * n k) k (S.k1 k) x⟩ := rfl
    rw [e2]
    have hN : (0 : ℝ) ≤ ((S.d * ((2 * ⌊R (S.k1 k - 1)⌋₊ + 3) * M) : ℕ) : ℝ) := by positivity
    nlinarith

end RegionHistory

end Balaban.LargeField
