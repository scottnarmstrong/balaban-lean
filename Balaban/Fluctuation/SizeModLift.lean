module

public import Balaban.Fluctuation.SizeModDefs
public import Balaban.Fluctuation.TraceEntropyCells
import Mathlib.Tactic.Ring

/-!
# Lifting an old modular cover to the next scale (VMOD-21 §3, (3.1)-(3.2))

For `a_k = cellSide L m₀ m₁ k` and `a_K = L a_k` (`K = k + 1`), an old `π'_k`-cube
`box b (L a_k)` with `b` aligned to `a_k` lies in the `π'_K`-cube `box (cbase a_K b) (L a_K)`
based at the coarsened corner (`old_box_lift`; it needs `2 ≤ L` and no divisibility hypothesis,
the cyclic seam being absorbed by the `ZMod` arithmetic).  `old_cover_covers_next` transports an
admissible old chosen cover (P6 p. 34, modular size `d^cov_k(X mod Ω^c)`,
`Fluctuation.ModAdmissible`) of `X ∩ Ω_old` to a cover of `X ∩ Ω_new` by lifted cubes, each
containing an old chosen cube and met by the old tree.  The lifted family need not lie in `X`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

/-- `box b (L a) ⊆ box (cbase (L a) b) (L (L a))` for `b` aligned to `a`, `0 < a`, `2 ≤ L`. -/
theorem old_box_lift {d n : ℕ} [NeZero n] {L a : ℕ} (ha : 0 < a) (hL : 2 ≤ L)
    {b : Torus d n} (hb : Aligned a b) :
    box b (L * a) ⊆ box (cbase (L * a) b) (L * (L * a)) := by
  rintro x ⟨w, hw, rfl⟩
  have hL0 : 0 < L := by omega
  -- the offset of `b` inside its coarse cell
  set u : Fin d → ℕ := fun μ => a * (((b μ).val / a) % L) with hu
  refine ⟨u + w, fun μ => ?_, ?_⟩
  · have h1 : ((b μ).val / a) % L < L := Nat.mod_lt _ hL0
    have h3 := hw μ
    simp only [Pi.add_apply, hu]
    have h5 : a * (((b μ).val / a) % L) + a ≤ L * a := by
      have : (((b μ).val / a) % L + 1) * a ≤ L * a := Nat.mul_le_mul_right _ h1
      nlinarith
    have h6 : 2 * (L * a) ≤ L * (L * a) := Nat.mul_le_mul_right _ hL
    omega
  · have hbv : b = cbase (L * a) b + natT u := by
      funext μ
      have hv : (b μ).val = a * ((b μ).val / a) := by
        have := Nat.div_add_mod (b μ).val a
        rw [hb μ] at this; omega
      have hdiv : (b μ).val / (L * a) = ((b μ).val / a) / L := by
        rw [mul_comm L a, ← Nat.div_div_eq_div_mul]
      have key : (b μ).val = L * a * ((b μ).val / (L * a)) + a * (((b μ).val / a) % L) := by
        rw [hdiv]
        set t := (b μ).val / a
        have ht := Nat.div_add_mod t L
        calc (b μ).val = a * t := hv
          _ = a * (L * (t / L) + t % L) := by rw [ht]
          _ = _ := by ring
      simp only [Pi.add_apply, cbase, natT, hu]
      refine (ZMod.natCast_zmod_val (b μ)).symm.trans ?_
      nth_rewrite 1 [key]
      push_cast
      ring
    conv_lhs => rw [hbv]
    rw [add_assoc, ← natT_add]

/-- **Row 3, second slice.**  Let `𝒦` be an old chosen cover (`ModAdmissible m₀ k Ωold X 𝒦 W E`)
with `Ωnew ⊆ Ωold`, and let `𝒦' ⊆ 𝒦` be any subfamily (the pruned old cover) still covering
`X ∩ Ωnew`.  Then the lifted cubes `box (cbase a_K q) (L a_K)`, `q ∈ 𝒦'`, are aligned to `a_K`,
cover `X ∩ Ωnew`, each contains an old chosen cube `box q (L a_k)`, and each is met by `W`. -/
theorem old_cover_covers_next {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ k : ℕ}
    (hK : k + 1 = K) (hL : 2 ≤ L)
    {X Ωold Ωnew 𝒦 𝒦' : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hΓ : ModAdmissible m₀ k Ωold X 𝒦 W E) (h𝒦' : 𝒦' ⊆ 𝒦)
    (hcov : X ∩ Ωnew ⊆ ⋃ q ∈ 𝒦', box q (L * cellSide L m₀ m₁ k)) :
    (X ∩ Ωnew ⊆ ⋃ Q ∈ (cbase (cellSide L m₀ m₁ K) '' 𝒦'),
        box Q (L * cellSide L m₀ m₁ K)) ∧
    ∀ Q ∈ (cbase (cellSide L m₀ m₁ K) '' 𝒦'),
      Aligned (cellSide L m₀ m₁ K) Q ∧
      (∃ q ∈ 𝒦, box q (L * cellSide L m₀ m₁ k) ⊆ box Q (L * cellSide L m₀ m₁ K)) ∧
      ∃ w ∈ W, w ∈ box Q (L * cellSide L m₀ m₁ K) := by
  have hside : cellSide L m₀ m₁ K = L * cellSide L m₀ m₁ k := by
    unfold cellSide
    rw [← hK, show k + 1 + m₀ + m₁ = (k + m₀ + m₁) + 1 by ring, pow_succ]; ring
  have hpos := cellSide_pos (L := L) m₀ m₁ k
  have lift : ∀ q ∈ 𝒦, box q (L * cellSide L m₀ m₁ k) ⊆
      box (cbase (cellSide L m₀ m₁ K) q) (L * cellSide L m₀ m₁ K) := fun q hq => by
    rw [hside]; exact old_box_lift hpos hL (hΓ.1 q hq).1
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp (hcov hx)
    exact Set.mem_iUnion₂.mpr ⟨_, ⟨q, hq, rfl⟩, lift q (h𝒦' hq) hxq⟩
  · rintro Q ⟨q, hq, rfl⟩
    refine ⟨aligned_cbase _, ⟨q, h𝒦' hq, lift q (h𝒦' hq)⟩, ?_⟩
    obtain ⟨w, hw, hwq⟩ := hΓ.2.2.2.2 q (h𝒦' hq)
    exact ⟨w, hw, lift q (h𝒦' hq) hwq⟩

/-- The unpruned case `𝒦' = 𝒦`: the covering of `X ∩ Ωnew` follows from `Ωnew ⊆ Ωold` (the
nesting of VMOD-21 §3, supplied on fine lifts by `RegionHistory.omegaNext_subset_post_fine`) and
the covering clause of `ModAdmissible`. -/
theorem old_cover_covers_next_unpruned {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ k : ℕ}
    (hK : k + 1 = K) (hL : 2 ≤ L)
    {X Ωold Ωnew 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hΓ : ModAdmissible m₀ k Ωold X 𝒦 W E) (hΩ : Ωnew ⊆ Ωold) :
    (X ∩ Ωnew ⊆ ⋃ Q ∈ (cbase (cellSide L m₀ m₁ K) '' 𝒦),
        box Q (L * cellSide L m₀ m₁ K)) ∧
    ∀ Q ∈ (cbase (cellSide L m₀ m₁ K) '' 𝒦),
      Aligned (cellSide L m₀ m₁ K) Q ∧
      (∃ q ∈ 𝒦, box q (L * cellSide L m₀ m₁ k) ⊆ box Q (L * cellSide L m₀ m₁ K)) ∧
      ∃ w ∈ W, w ∈ box Q (L * cellSide L m₀ m₁ K) :=
  old_cover_covers_next hK hL hΓ subset_rfl
    (fun _ hx => by
      have := hΓ.2.1 ⟨hx.1, hΩ hx.2⟩
      simpa using this)

end Balaban.Fluctuation
