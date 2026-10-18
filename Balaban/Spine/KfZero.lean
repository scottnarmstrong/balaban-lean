/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LastIntegral
public import Balaban.Spine.Witness
public import Balaban.LargeField.Base.KF0BlockSplit

/-!
# The case `k_f = 0` of the spine from two sub-inputs

`kfZeroInput_of_parts` proves the spine input `KfZeroInput` (A7, LF-8 (b),
`Spine/RootFInputs.lean`) from two named sub-inputs, along the route of hard physical sectors
(`notes/phase1/LF-BASE-KF0.md` (B.1), Parts D–G; `KF0.md` (K0.2); `KF0-INFL.md`, route (A)). For
`7/8 L⁻² < ν ≤ 1` no renormalization step is performed, and the partition function itself is
expanded on the blocks of side `s = M L` (the cubes of the scale-`1` polymers of Root-F). A block is
good for a configuration `φ` if `|φ_x - h| < r` at all its sites, for a threshold `r = r(κ, c₉, β, ν)`
chosen by the provider (in the notes `r = δ_β = A log(β a)/√(β ν)`); the threshold is a parameter
`thr` of both sub-inputs. The landed exact sector identity `partitionFunction_eq_sum_kf0Sector`
(K0.2) writes `Z(g) = ∑_B Z_B(g)` over the sets `B` of bad blocks, `Z_B` the integral of
`e^{-βH + ⟨g, φ⟩}` with the indicator that the bad blocks are exactly `B` (`kf0Sector`).

* `KF0GoodSectorInput` (the all-good gas; LF-BASE-KF0 Part F.2, Theorem F.1; `KF0AllGoodGas.lean`,
  `KF0AllPlusGas.lean`): the all-good sector is `Z_∅(g) = exp(E + ⟨g, h⟩ + ∑_X a(X; g))` with
  scale-`1` activities `a` in Root-F's form at half the amplitude.
* `KF0BadSectorInput` (the bad sectors, including those with reversed spins, as a linked gas; LF-BASE-
  KF0 Parts D, E, G, `KF0-HEAVY.md`, `KF0-LINK.md`, `KF0-ONECORE.md`, `astra/KF0B.md` (Round 7: the
  singleton-gas reading of the exact cutoff cells is refuted, Theorem B.7); P7 (4.11)–(4.14);
  blocker 1): `∑_B Z_B(g) = Z_∅(g) exp(∑_X b(X; g))` with scale-`1` activities `b` in Root-F's form
  at half the amplitude.

The assembly (`kfZeroInput_of_parts`) takes `p = a + b` and the vacuum term of the all-good sector;
the clauses of `ObservableActivities` for the sum are the lemmas `ActSupportAt.add`, … of
`Spine/LastIntegral.lean`. For thresholds `r > 2` every block is good, the bad sectors vanish and
`KF0BadSectorInput` holds with `b = 0` (`kf0BadSectorInput_of_two_lt`): the sub-input is not
vacuous, and the split is a genuine one only for small thresholds. The list and the status of each
sub-input are in `notes/phase1/SPINE.md`, section "KfZeroInput sub-inputs". -/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField

/-- A torus side divisible by `M L^{kf+1}` is `M L` times a positive number of blocks. -/
theorem exists_blockCount {M L kf ℓ : ℕ} [NeZero ℓ] (hℓ : M * L ^ (kf + 1) ∣ ℓ) :
    ∃ m : ℕ, NeZero m ∧ ℓ = M * L * m := by
  obtain ⟨q, hq⟩ := hℓ
  refine ⟨L ^ kf * q, ⟨fun h0 => NeZero.ne ℓ ?_⟩, ?_⟩
  · rw [hq, pow_succ, show M * (L ^ kf * L) * q = M * L * (L ^ kf * q) by ring, h0, mul_zero]
  · rw [hq, pow_succ]
    ring

/-- **For a threshold `r > 2` every block is good**: a unit spin is at distance at most `2` from
the unit field `h`, so the only non-zero sector is `B = ∅`. -/
theorem kf0Sector_eq_zero_of_two_lt {d N ℓ : ℕ} [NeZero ℓ] (s m : ℕ) [NeZero m] {r : ℝ}
    (hr : 2 < r) (β ν : ℝ) {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1)
    {B : Finset (Torus d m)} (hB : B ≠ ∅) (g : Torus d ℓ → Fin N → ℂ) :
    kf0Sector s m r β ν h B g = 0 := by
  have hgood : ∀ φ : Cfg d N ℓ, badSet s m r h φ = ∅ := by
    intro φ
    refine Finset.eq_empty_of_forall_notMem fun Q hQ => ?_
    refine (mem_badSet s m r h Q φ).1 hQ fun x _ => ?_
    have hφ : ‖(φ x : EuclideanSpace ℝ (Fin N))‖ = 1 := norm_eq_of_mem_sphere (φ x)
    calc ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖
        ≤ ‖(φ x : EuclideanSpace ℝ (Fin N))‖ + ‖h‖ := norm_sub_le _ _
      _ = 2 := by rw [hφ, hh]; norm_num
      _ < r := hr
  unfold kf0Sector sourceIntegral sourceIntegrand
  have hw : ∀ φ : Cfg d N ℓ, sectorWeight s m r h B φ = 0 := fun φ => by
    rw [sectorWeight_eq_ite, ite_eq_right (by rw [hgood φ]; exact Ne.symm hB)]
  simp [hw]

section Inputs

variable (d N : ℕ) (δ : ℝ) (T : ℝ → ℝ → Typing) (thr : ℝ → ℝ → ℝ → ℝ → ℝ)

/-- **A7-1, the all-good sector as a polymer gas (LF-BASE-KF0 Part F.2, Theorem F.1, (F.13);
`KF0.md` "ordinary expansion"; the landed `KF0AllGoodGas`, `KF0AllPlusGas`, `KF0F1Assembly`).** For
`β ≥ β₀`, `7/8 L⁻² < ν ≤ 1`, every unit field `h` and `kf = k̂_f`: there are scale-`1` activities `a`
in Root-F's form (`ObservableActivities` with top scale `1` and half the amplitude `c₉`) and vacuum
terms `E_ℓ` such that, on every admissible torus (`M L^{kf+1} ∣ ℓ`, `m = ℓ/(M L)` blocks of side
`M L` per side) and every source of the unit `ℓ¹` ball, the all-good sector (every spin within the
threshold `r = thr κ c₉ β ν` of `h`) is `Z_∅(g) = exp(E_ℓ + ⟨g, h⟩ + ∑_X a_ℓ(X; g))`. In the source:
the chart around `h` on every site (for `r ≤ √2` all spins of the sector lie in the open upper
hemisphere), the
massive Gaussian with covariance `(-Δ + ν)^{-1}` (the mass `ν > 7/8 L⁻²` makes it decay at the
scale of one block), the walk localization of the analytic site and bond functions (Theorem F.1),
the product cutoff and the Mayer expansion on the blocks (`block_gas`); the exact two-torus
agreement from the walk localization with lifted supports. -/
def KF0GoodSectorInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 7 / 8 < ν * ((T κ c₉).L : ℝ) ^ 2 → ν ≤ 1 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
    ∃ (a : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (E : ℕ → ℂ),
      ObservableActivities d N (T κ c₉).L (T κ c₉).M κ (c₉ / 2) δ 1 kf a ∧
      ∀ (ℓ : ℕ) [NeZero ℓ], (T κ c₉).M * (T κ c₉).L ^ (kf + 1) ∣ ℓ →
        ∀ (m : ℕ) [NeZero m], ℓ = (T κ c₉).M * (T κ c₉).L * m →
        ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
          kf0Sector ((T κ c₉).M * (T κ c₉).L) m (thr κ c₉ β ν) β ν h ∅ g =
            Complex.exp (E ℓ + ∑ x, ∑ i, g x i * (h i : ℂ) + ∑ X, a ℓ 1 X g)

/-- **A7-2, the bad sectors as a linked gas (LF-BASE-KF0 Parts D, E, G; `KF0-HEAVY.md`,
`KF0-LINK.md`, `KF0-ONECORE.md`; `astra/KF0B.md`; P7 (4.11)–(4.14); blocker 1).** For `β ≥ β₀`,
`7/8 L⁻² < ν ≤ 1`, every unit field `h` and `kf = k̂_f`: there are scale-`1` activities `b` in
Root-F's form (`ObservableActivities` with top scale `1` and half the amplitude `c₉`) such that, on
every admissible torus and every source of the unit `ℓ¹` ball, the sum of the sector integrals over
all sets `B` of bad blocks (threshold `r = thr κ c₉ β ν`) is `Z_∅(g) exp(∑_X b_ℓ(X; g))`. The sets
`B ≠ ∅` contain the configurations with spins far from `h`, among them the reversed spins
(`φ_x · h ≤ 0`, every such spin is bad when `r ≤ √2`). In the source: each bad core with its collar
(the killed-walk mean and the radius (L38.2)), its Peierls charge `e^{-βν r²/2}` per bad block with
the retained crossing bonds (H37.1) and the determinant ratio, the exterior influence through the
good region, and the linked expansion of the heavy objects over the all-good reference, whose
exponentiation gives `b` (regrouped by scale-`1` polymers); the exact two-torus agreement from the
locality of the linked activities. Theorem B.7 of `astra/KF0B.md` refutes the reading of the raw
exact cutoff cells as a singleton gas; the expansion must be linked (P7 (4.11)). -/
def KF0BadSectorInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 7 / 8 < ν * ((T κ c₉).L : ℝ) ^ 2 → ν ≤ 1 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
    ∃ b : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ,
      ObservableActivities d N (T κ c₉).L (T κ c₉).M κ (c₉ / 2) δ 1 kf b ∧
      ∀ (ℓ : ℕ) [NeZero ℓ], (T κ c₉).M * (T κ c₉).L ^ (kf + 1) ∣ ℓ →
        ∀ (m : ℕ) [NeZero m], ℓ = (T κ c₉).M * (T κ c₉).L * m →
        ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
          ∑ B : Finset (Torus d m),
              kf0Sector ((T κ c₉).M * (T κ c₉).L) m (thr κ c₉ β ν) β ν h B g =
            kf0Sector ((T κ c₉).M * (T κ c₉).L) m (thr κ c₉ β ν) β ν h ∅ g *
              Complex.exp (∑ X, b ℓ 1 X g)

/-- **The case `k_f = 0` from its sub-inputs**: the exact sector identity
(`partitionFunction_eq_sum_kf0Sector`) gives `Z(g) = ∑_B Z_B(g)`; the bad sectors give
`∑_B Z_B = Z_∅ exp(∑_X b)` (`KF0BadSectorInput`) and the all-good sector gives
`Z_∅ = exp(E + ⟨g, h⟩ + ∑_X a)` (`KF0GoodSectorInput`). The activities are `p = a + b`, with the
amplitudes `c₉/4 + c₉/4`; `E` is the vacuum term of the all-good sector. The threshold is the
larger of the two thresholds; the block threshold `thr` is arbitrary. -/
theorem kfZeroInput_of_parts (hG : KF0GoodSectorInput d N δ T thr)
    (hB : KF0BadSectorInput d N δ T thr) : KfZeroInput d N δ T := by
  intro κ hκ c₉ hc₉
  obtain ⟨β₁, h₁⟩ := hG κ hκ c₉ hc₉
  obtain ⟨β₂, h₂⟩ := hB κ hκ c₉ hc₉
  refine ⟨max β₁ β₂, fun β hβ ν hν1 hν2 h hh kf hkf => ?_⟩
  obtain ⟨a, E, ⟨hA, hgA⟩, hidA⟩ := h₁ β (le_of_max_le_left hβ) ν hν1 hν2 h hh kf hkf
  obtain ⟨b, ⟨hB', hgB⟩, hidB⟩ := h₂ β (le_of_max_le_right hβ) ν hν1 hν2 h hh kf hkf
  refine ⟨actAdd a b, E, ⟨fun ℓ _ hℓ => ?_, hgA.add hgB⟩, fun ℓ _ hℓ g hg => ?_⟩
  · obtain ⟨hsA, haA, hlA, hbA⟩ := hA ℓ hℓ
    obtain ⟨hsB, haB, hlB, hbB⟩ := hB' ℓ hℓ
    have hbAB := hbA.add hbB
    rw [add_halves] at hbAB
    exact ⟨hsA.add hsB, haA.add haB, hlA.add hlB, hbAB⟩
  · obtain ⟨m, hm, hℓm⟩ := exists_blockCount hℓ
    rw [partitionFunction_eq_sum_kf0Sector ((T κ c₉).M * (T κ c₉).L) m (thr κ c₉ β ν) β ν h g,
      hidB ℓ hℓ m hℓm g hg, hidA ℓ hℓ m hℓm g hg, ← Complex.exp_add]
    congr 1
    simp only [actAdd, Finset.sum_add_distrib]
    ring

/-- **`KF0BadSectorInput` is not vacuous**: for thresholds `r > 2` every block is good, the bad
sectors vanish (`kf0Sector_eq_zero_of_two_lt`) and the sub-input holds with `b = 0`
(`observableActivities_zero`). -/
theorem kf0BadSectorInput_of_two_lt (hthr : ∀ κ c₉ β ν, 2 < thr κ c₉ β ν) :
    KF0BadSectorInput d N δ T thr := by
  intro κ _ c₉ hc₉
  refine ⟨0, fun β _ ν _ _ h hh kf _ => ⟨fun _ _ _ _ => 0,
    observableActivities_zero d N _ _ κ (c₉ / 2) δ (by positivity) 1 kf,
    fun ℓ _ _ m _ _ g _ => ?_⟩⟩
  rw [Finset.sum_eq_single (∅ : Finset (Torus d m))
    (fun B _ hB => kf0Sector_eq_zero_of_two_lt _ m (hthr κ c₉ β ν) β ν hh hB g)
    (fun h0 => absurd (Finset.mem_univ _) h0)]
  simp

end Inputs

end Balaban.RootFSpine
