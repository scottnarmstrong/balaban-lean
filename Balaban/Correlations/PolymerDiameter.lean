/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.PolymerCount

/-!
# The diameter of a polymer (CORRELATIONS.md, Lemma 1.2)

Conditional development of Root-C: geometry used by the consequences of the clauses of Root-F.
For a polymer `X` of block side `s` on `(ℤ/ℓ)^d`, `s ∣ ℓ`, and `x, y ∈ X`, the torus sup distance
`torusDist x y = max_μ |valMinAbs (x_μ - y_μ)|` satisfies `torusDist x y + 1 ≤ n(X) * s`, where
`n(X) = |X| / s^d` is the number of blocks.
-/

@[expose] public section

open scoped Classical

noncomputable section

namespace Balaban.Correlations

open Balaban Balaban.Polymer Finset

/-- The norm of a residue: the absolute value of its representative of least absolute value. -/
def torusNorm {ℓ : ℕ} (z : ZMod ℓ) : ℕ := z.valMinAbs.natAbs

/-- The sup distance on the torus. -/
def torusDist {d ℓ : ℕ} (x y : Fin d → ZMod ℓ) : ℕ := univ.sup fun μ => torusNorm (x μ - y μ)

section Norm

theorem torusNorm_neg {ℓ : ℕ} (z : ZMod ℓ) : torusNorm (-z) = torusNorm z :=
  ZMod.natAbs_valMinAbs_neg z

theorem torusNorm_add_le {ℓ : ℕ} (a b : ZMod ℓ) :
    torusNorm (a + b) ≤ torusNorm a + torusNorm b :=
  (ZMod.natAbs_valMinAbs_add_le a b).trans (Int.natAbs_add_le _ _)

variable {ℓ : ℕ} [NeZero ℓ]

theorem torusNorm_natCast_le (k : ℕ) : torusNorm (k : ZMod ℓ) ≤ k := by
  unfold torusNorm
  rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast]
  exact (min_le_left _ _).trans (Nat.mod_le _ _)

theorem torusNorm_intCast_le (w : ℤ) : torusNorm (w : ZMod ℓ) ≤ w.natAbs := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg w
  · simpa using torusNorm_natCast_le (ℓ := ℓ) k
  · push_cast
    rw [torusNorm_neg]
    simpa using torusNorm_natCast_le (ℓ := ℓ) k

end Norm

variable {d ℓ s m : ℕ} [NeZero ℓ] [NeZero m]

omit [NeZero m] in
/-- Two sites at block coordinate difference `t` have distance at most `s |t| + s - 1`. -/
theorem torusNorm_sub_le (hℓ : ℓ = s * m) (a b : ZMod ℓ) (t : ℤ)
    (ht : blockCoord s m b - blockCoord s m a = (t : ZMod m)) :
    torusNorm (b - a) ≤ s * t.natAbs + (s - 1) := by
  have hs : 0 < s := pos_of_eq_mul hℓ
  set A := a.val
  set B := b.val
  have hA : (a : ZMod ℓ) = (A : ZMod ℓ) := (ZMod.natCast_zmod_val a).symm
  have hB : (b : ZMod ℓ) = (B : ZMod ℓ) := (ZMod.natCast_zmod_val b).symm
  have hqa : blockCoord s m a = ((A / s : ℕ) : ZMod m) := rfl
  have hqb : blockCoord s m b = ((B / s : ℕ) : ZMod m) := rfl
  rw [hqa, hqb] at ht
  have hdvd : (m : ℤ) ∣ ((B / s : ℕ) : ℤ) - ((A / s : ℕ) : ℤ) - t := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_sub, Int.cast_natCast,
      Int.cast_natCast, ht]
    ring
  obtain ⟨c, hc⟩ := hdvd
  have hA' : (A : ℤ) = s * ((A / s : ℕ) : ℤ) + ((A % s : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod A s).symm
  have hB' : (B : ℤ) = s * ((B / s : ℕ) : ℤ) + ((B % s : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod B s).symm
  set w : ℤ := s * t + ((B % s : ℕ) : ℤ) - ((A % s : ℕ) : ℤ) with hw
  have hbw : b - a = (w : ZMod ℓ) := by
    have h1 : ((B : ℤ) - (A : ℤ) - w) = (ℓ : ℤ) * c := by
      have : ((ℓ : ℕ) : ℤ) = s * m := by exact_mod_cast hℓ
      rw [this, hw]
      linear_combination hB' - hA' + (s : ℤ) * hc
    have h2 : (((B : ℤ) - (A : ℤ) - w : ℤ) : ZMod ℓ) = 0 := by
      rw [h1]; push_cast; simp
    push_cast at h2
    rw [hA, hB]
    linear_combination h2
  rw [hbw]
  refine (torusNorm_intCast_le w).trans ?_
  have hua : A % s < s := Nat.mod_lt _ hs
  have hub : B % s < s := Nat.mod_lt _ hs
  rw [hw]
  have : (s * t + ((B % s : ℕ) : ℤ) - ((A % s : ℕ) : ℤ)).natAbs ≤
      s * t.natAbs + (s - 1) := by
    zify
    have hcast : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by
      rw [Nat.cast_sub hs]; simp
    rw [hcast]
    have h3 : |(s : ℤ) * t| = s * |t| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    have h4 : |(s : ℤ) * t + ((B % s : ℕ) : ℤ) - ((A % s : ℕ) : ℤ)| ≤
        |(s : ℤ) * t| + (s - 1) := by
      rw [abs_le]
      have : ((B % s : ℕ) : ℤ) < s := by exact_mod_cast hub
      have : ((A % s : ℕ) : ℤ) < s := by exact_mod_cast hua
      have : (0 : ℤ) ≤ ((B % s : ℕ) : ℤ) := by positivity
      have : (0 : ℤ) ≤ ((A % s : ℕ) : ℤ) := by positivity
      constructor <;> linarith [neg_abs_le ((s : ℤ) * t), le_abs_self ((s : ℤ) * t)]
    rw [h3] at h4
    simpa [Int.natCast_natAbs] using h4
  exact this

omit [NeZero m] in
theorem blockGraph_adj_coord {u v : Torus d m} (h : (blockGraph d m).Adj u v) (μ : Fin d) :
    ∃ e : ℤ, e.natAbs ≤ 1 ∧ v μ - u μ = (e : ZMod m) := by
  obtain ⟨_, ν, hν | hν⟩ := h
  · by_cases hμ : μ = ν
    · subst hμ
      exact ⟨1, by simp, by simp [hν]⟩
    · exact ⟨0, by simp, by simp [hν, Pi.single_eq_of_ne hμ]⟩
  · by_cases hμ : μ = ν
    · subst hμ
      exact ⟨-1, by simp, by simp [hν]⟩
    · exact ⟨0, by simp, by simp [hν, Pi.single_eq_of_ne hμ]⟩

omit [NeZero m] in
theorem walk_coord {S : Set (Torus d m)} {u v : S}
    (p : ((blockGraph d m).induce S).Walk u v) (μ : Fin d) :
    ∃ t : ℤ, t.natAbs ≤ p.length ∧ (v : Torus d m) μ - (u : Torus d m) μ = (t : ZMod m) := by
  induction p with
  | nil => exact ⟨0, by simp, by simp⟩
  | @cons a b c hadj p ih =>
    obtain ⟨t', ht', h'⟩ := ih
    obtain ⟨e, he, h⟩ := blockGraph_adj_coord (show (blockGraph d m).Adj a.1 b.1 from hadj) μ
    refine ⟨t' + e, ?_, ?_⟩
    · rw [SimpleGraph.Walk.length_cons]
      exact (Int.natAbs_add_le _ _).trans (by omega)
    · push_cast
      rw [← h', ← h]
      ring

/-- Lemma 1.2 (diameter): `d_ℓ(x, y) + 1 ≤ n(X) s` for `x, y ∈ X`. -/
theorem torusDist_add_one_le (hℓ : ℓ = s * m) {X : Finset (Torus d ℓ)}
    (hX : IsPolymer d ℓ s X) {x y : Torus d ℓ} (hx : x ∈ X) (hy : y ∈ X) :
    torusDist x y + 1 ≤ blockNumber d s X * s := by
  have hs : 0 < s := pos_of_eq_mul hℓ
  obtain ⟨hne, hconn⟩ := polymer_image_connected hℓ hX
  set Y := X.image (blockMap s m) with hY
  have hu : blockMap s m y ∈ (Y : Set (Torus d m)) := mem_coe.2 (mem_image_of_mem _ hy)
  have hv : blockMap s m x ∈ (Y : Set (Torus d m)) := mem_coe.2 (mem_image_of_mem _ hx)
  obtain ⟨p, hp⟩ := hconn.exists_isPath ⟨_, hu⟩ ⟨_, hv⟩
  have hlen : p.length < Y.card := by
    have := hp.length_lt
    simpa using this
  have hn : blockNumber d s X = Y.card := polymer_blockNumber_eq hℓ hX
  rw [hn]
  obtain ⟨n', hn'⟩ : ∃ n', Y.card = n' + 1 := ⟨Y.card - 1, by omega⟩
  rw [hn'] at hlen ⊢
  have hcoord : ∀ μ, torusNorm (x μ - y μ) ≤ s * n' + (s - 1) := by
    intro μ
    obtain ⟨t, ht, hteq⟩ := walk_coord p μ
    refine (torusNorm_sub_le hℓ (y μ) (x μ) t hteq).trans ?_
    have : s * t.natAbs ≤ s * n' := Nat.mul_le_mul_left _ (by omega)
    omega
  have hd : torusDist x y ≤ s * n' + (s - 1) := Finset.sup_le fun μ _ => hcoord μ
  have : (n' + 1) * s = s * n' + s := by ring
  omega

end Balaban.Correlations
