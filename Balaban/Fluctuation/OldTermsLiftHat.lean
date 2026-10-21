/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftBasic
public import Balaban.Localization.CubeAligned
public import Balaban.Localization.P6ActiveSeed
public import Balaban.SmallField.LocalGeneratorSource

/-!
# The local generating sets `𝔹_j(X̂)` of ruling R13: the cast form and the inherited levels

`GsSpec.HatSpec` specifies the generating set of a class polymer through its layers.  It is the
cast local set `castG hc (localB j … X̂ hsep)` of the chain (`hatSpec_castLocalB`,
`HatSpec.eq_castLocalB`).  The inherited levels of the class are transported to the tori of the next
scale (`liftOldGS`, `liftOldPoly`); their generating sets stay the local sets `𝔹_j(X̂)`.

* `hatSpec_castLocalB`, `HatSpec.eq_castLocalB`: the cast form;

* `fineCubeIdx_castT`, `mem_minLayer_castT`: the layers of the minimal generating set of P3
  (4.4)–(4.6) depend only on the values of the coordinates: on two descriptions
  `M1 N L^q = M1 N' L^{q'}` of one fine torus with the same cube tori up to the level `j`, they
  correspond under the identification `castT`;
* `mem_hatSet_liftOldPoly`: `X̂` commutes with the transport of polymers;
* `hatSpec_liftOldGS`: the transported generating set of an inherited level has `HatSpec`;
* `hatSpec_splice`: `HatSpec` of the spliced terms of the next scale.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec

section MinLayerCast

variable {d L : ℕ} [NeZero L]

omit [NeZero L] in
/-- The identification of two tori of equal side preserves the sup distance. -/
theorem supDist_castT_eq {n n' : ℕ} (h : n = n') (x y : Torus d n) :
    LargeField.supDist (castT h x) (castT h y) = LargeField.supDist x y := by
  subst h; rfl

/-- The cube index commutes with the identification of two descriptions of the fine torus. -/
theorem fineCubeIdx_castT {M1 N N' q q' n : ℕ} [NeZero M1] [NeZero N] [NeZero N']
    (hA : M1 * N * L ^ q = M1 * N' * L ^ q') (hB : N * L ^ (q - n) = N' * L ^ (q' - n))
    (x : Torus d (M1 * N * L ^ q)) :
    LargeField.fineCubeIdx M1 N' L q' n (castT hA x) =
      castT hB (LargeField.fineCubeIdx M1 N L q n x) := by
  funext μ
  apply ZMod.val_injective
  rw [castT_val]
  simp only [LargeField.fineCubeIdx, blockMap_apply, blockCoord, ZMod.val_natCast, castT_val, hB]

/-- **The layers of the minimal generating set correspond under `castT`.** -/
theorem mem_minLayer_castT {M1 N N' q q' j : ℕ} [NeZero M1] [NeZero N] [NeZero N']
    (hA : M1 * N * L ^ q = M1 * N' * L ^ q')
    (hB : ∀ n, n ≤ j → N * L ^ (q - n) = N' * L ^ (q' - n))
    {X : Finset (Torus d (M1 * N * L ^ q))} {X' : Finset (Torus d (M1 * N' * L ^ q'))}
    (hX : ∀ x, x ∈ X ↔ castT hA x ∈ X') (n : ℕ) (x : Torus d (M1 * N * L ^ q)) :
    x ∈ LargeField.minLayer M1 N L q j X n ↔ castT hA x ∈ LargeField.minLayer M1 N' L q' j X' n := by
  have hsurj := castT_surjective (d := d) hA
  have key : ∀ t n, n + t = j → ∀ x : Torus d (M1 * N * L ^ q),
      x ∈ LargeField.minLayer M1 N L q j X n ↔
        castT hA x ∈ LargeField.minLayer M1 N' L q' j X' n := by
    intro t
    induction t with
    | zero =>
      intro n hn x
      obtain rfl : n = j := by omega
      rw [LargeField.minLayer_self, LargeField.minLayer_self, LargeField.mem_cubeInterior,
        LargeField.mem_cubeInterior]
      constructor
      · intro h y' hy'
        obtain ⟨y, rfl⟩ := hsurj y'
        rw [fineCubeIdx_castT hA (hB n le_rfl), fineCubeIdx_castT hA (hB n le_rfl)] at hy'
        exact (hX y).1 (h y (castT_injective _ hy'))
      · intro h y hy
        refine (hX y).2 (h (castT hA y) ?_)
        rw [fineCubeIdx_castT hA (hB n le_rfl), fineCubeIdx_castT hA (hB n le_rfl), hy]
    | succ t ih =>
      intro n hn x
      have hnj : n < j := by omega
      rw [LargeField.minLayer_of_lt _ hnj, LargeField.minLayer_of_lt _ hnj,
        LargeField.mem_nearStep, LargeField.mem_nearStep]
      constructor
      · rintro ⟨y, hy, hd⟩
        refine ⟨castT hA y, (ih (n + 1) (by omega) y).1 hy, ?_⟩
        rw [fineCubeIdx_castT hA (hB n hnj.le), fineCubeIdx_castT hA (hB n hnj.le),
          supDist_castT_eq]
        exact hd
      · rintro ⟨y', hy', hd⟩
        obtain ⟨y, rfl⟩ := hsurj y'
        refine ⟨y, (ih (n + 1) (by omega) y).2 hy', ?_⟩
        rw [fineCubeIdx_castT hA (hB n hnj.le), fineCubeIdx_castT hA (hB n hnj.le),
          supDist_castT_eq] at hd
        exact hd
  by_cases hn : n ≤ j
  · exact key (j - n) n (by omega) x
  · rw [LargeField.minLayer_of_gt _ (not_le.1 hn), LargeField.minLayer_of_gt _ (not_le.1 hn)]
    simp

end MinLayerCast

section Cast

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **The cast local set `𝔹_j(X̂)` has the layers of `HatSpec`** (any cast of the fine torus with
the cube exponent `hatScale`). -/
theorem hatSpec_castLocalB {m₀ j : ℕ} (hj : j ≤ k) (X : Set (CTorus d L N₁ m₁ k)) {N₁' : ℕ}
    [NeZero N₁'] (hc : N₁' * L ^ (m₁ + hatScale L m₁ ϱ) = N₁ * L ^ m₁)
    (hs : ϱ ≤ LargeField.minSep L (L ^ (m₁ + hatScale L m₁ ϱ))) :
    HatSpec m₀ j X (castG hc (localB j hj
      {x' : CTorus d L N₁' (m₁ + hatScale L m₁ ϱ) k |
        (torusCast x' : CTorus d L N₁ m₁ k) ∈ hatSet m₀ j X} hs)) := by
  intro _ _ N₁'' _ hc'' n x
  have hpos : 0 < L ^ (m₁ + hatScale L m₁ ϱ) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  obtain rfl : N₁'' = N₁' := Nat.eq_of_mul_eq_mul_right hpos (hc''.trans hc.symm)
  have hcc : N₁'' * L ^ (m₁ + hatScale L m₁ ϱ) * L ^ k = N₁ * L ^ m₁ * L ^ k := by rw [hc]
  have hcc' : L ^ (m₁ + hatScale L m₁ ϱ) * N₁'' * L ^ k = N₁ * L ^ m₁ * L ^ k := by
    rw [mul_comm (L ^ _) N₁'', hc]
  have hv : ∀ y : Torus d (L ^ (m₁ + hatScale L m₁ ϱ) * N₁'' * L ^ k),
      (torusCast (torusCast y : CTorus d L N₁'' (m₁ + hatScale L m₁ ϱ) k) :
        CTorus d L N₁ m₁ k) = torusCast y := by
    intro y
    funext μ
    apply ZMod.val_injective
    rw [torusCast_val hcc, torusCast_val (by rw [mul_comm (L ^ _) N₁'']), torusCast_val hcc']
  have hx : (torusCast (torusCast x : CTorus d L N₁'' (m₁ + hatScale L m₁ ϱ) k) :
      Torus d (L ^ (m₁ + hatScale L m₁ ϱ) * N₁'' * L ^ k)) = torusCast x := by
    funext μ
    apply ZMod.val_injective
    rw [torusCast_val (by rw [mul_comm (L ^ _) N₁'']), torusCast_val hcc.symm,
      torusCast_val hcc'.symm]
  rw [mem_castG_Ω]
  unfold localB
  rw [mem_castG_Ω, minimalGenSetAt_Ω, hx]
  have hF : (Finset.univ.filter fun y : Torus d (L ^ (m₁ + hatScale L m₁ ϱ) * N₁'' * L ^ k) =>
      (torusCast y : CTorus d L N₁'' (m₁ + hatScale L m₁ ϱ) k) ∈
        {x' : CTorus d L N₁'' (m₁ + hatScale L m₁ ϱ) k |
          (torusCast x' : CTorus d L N₁ m₁ k) ∈ hatSet m₀ j X}) =
      Finset.univ.filter fun y : Torus d (L ^ (m₁ + hatScale L m₁ ϱ) * N₁'' * L ^ k) =>
        (torusCast y : CTorus d L N₁ m₁ k) ∈ hatSet m₀ j X := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hv]
  rw [hF]

/-- **A generating set with `HatSpec` is the cast local set `𝔹_j(X̂)`** when the cube exponent is
below `m₀` and has the separation. -/
theorem HatSpec.eq_castLocalB {m₀ j : ℕ} {X : Set (CTorus d L N₁ m₁ k)}
    {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} (h : HatSpec m₀ j X G)
    (hlt : hatScale L m₁ ϱ < m₀) (hs : ϱ ≤ LargeField.minSep L (L ^ (m₁ + hatScale L m₁ ϱ)))
    (hj : j ≤ k) {N₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ (m₁ + hatScale L m₁ ϱ) = N₁ * L ^ m₁) :
    G = castG hc (localB j hj
      {x' : CTorus d L N₁' (m₁ + hatScale L m₁ ϱ) k |
        (torusCast x' : CTorus d L N₁ m₁ k) ∈ hatSet m₀ j X} hs) := by
  apply gs_eq_of_Ω_eq
  funext n
  ext x
  rw [h hlt hs N₁' hc n x, hatSpec_castLocalB hj X hc hs hlt hs N₁' hc n x]

end Cast

section Lift

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- A box of `X̂` read through the identification `castT` of two descriptions of the torus. -/
theorem castT_mem_cubeBox {n n' : ℕ} (h : n = n') (c t s : ℕ) (x y : Torus d n) :
    castT h x ∈ box (cbase c (castT h y) - natT fun _ => t) s ↔
      x ∈ box (cbase c y - natT fun _ => t) s := by
  rw [← LargeField.castT_cbase, ← LargeField.castT_natT h (fun _ => t), ← castT_sub,
    ← LargeField.castT_image_box]
  exact (castT_injective h).mem_set_image

omit [NeZero L] [NeZero N₁] in
/-- **`X̂` commutes with the transport of polymers** to the next scale. -/
theorem mem_hatSet_liftOldPoly (m₀ j : ℕ) (X : Set (CTorus d L (L * N₁) m₁ k))
    (x : CTorus d L (L * N₁) m₁ k) :
    oldTorusEquiv x ∈ hatSet m₀ j (liftOldPoly X) ↔ x ∈ hatSet m₀ j X := by
  constructor
  · rintro ⟨y', ⟨y, hy, rfl⟩, hxy⟩
    refine ⟨y, hy, ?_⟩
    rw [oldTorusEquiv_apply, oldTorusEquiv_apply] at hxy
    exact (castT_mem_cubeBox _ _ _ _ x y).1 hxy
  · rintro ⟨y, hy, hxy⟩
    refine ⟨oldTorusEquiv y, ⟨y, hy, rfl⟩, ?_⟩
    rw [oldTorusEquiv_apply, oldTorusEquiv_apply]
    exact (castT_mem_cubeBox _ _ _ _ x y).2 hxy

/-- **The transported generating set of an inherited level is the local set `𝔹_j(X̂)`** of the
transported polymer (`HatSpec` is preserved by `liftOldGS`, `liftOldPoly`). -/
theorem hatSpec_liftOldGS {m₀ j : ℕ} (hj : j ≤ k) {X : Set (CTorus d L (L * N₁) m₁ k)}
    {G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ} (h : HatSpec m₀ j X G) :
    HatSpec m₀ j (liftOldPoly X) (liftOldGS G) := by
  intro hs hsep N₁' _ hc n x
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hN0 : 0 < N₁' := Nat.pos_of_ne_zero (NeZero.ne N₁')
  have : NeZero (L * N₁') := ⟨by positivity⟩
  have hc' : (L * N₁') * L ^ (m₁ + hatScale L m₁ ϱ) = (L * N₁) * L ^ m₁ := by
    rw [mul_assoc, hc, mul_assoc]
  have H := h hs hsep (L * N₁') hc'
  have hA : L ^ (m₁ + hatScale L m₁ ϱ) * (L * N₁') * L ^ k =
      L ^ (m₁ + hatScale L m₁ ϱ) * N₁' * L ^ (k + 1) := by ring
  have hB : ∀ n, n ≤ j → (L * N₁') * L ^ (k - n) = N₁' * L ^ (k + 1 - n) := by
    intro n hn
    rw [show k + 1 - n = (k - n) + 1 by omega, pow_succ]
    ring
  have hold : L ^ (m₁ + hatScale L m₁ ϱ) * (L * N₁') * L ^ k = (L * N₁) * L ^ m₁ * L ^ k := by
    rw [mul_comm (L ^ _) (L * N₁'), hc']
  have hnew : L ^ (m₁ + hatScale L m₁ ϱ) * N₁' * L ^ (k + 1) = N₁ * L ^ m₁ * L ^ (k + 1) := by
    rw [mul_comm (L ^ _) N₁', hc]
  have hfine : (L * N₁) * L ^ m₁ * L ^ k = N₁ * L ^ m₁ * L ^ (k + 1) :=
    oldSide_eq_newSide (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
  -- the cast of the transported site
  have hx : ∀ x0 : CTorus d L (L * N₁) m₁ k,
      (torusCast (oldTorusEquiv x0) : Torus d (L ^ (m₁ + hatScale L m₁ ϱ) * N₁' * L ^ (k + 1))) =
        castT hA (torusCast x0 : Torus d (L ^ (m₁ + hatScale L m₁ ϱ) * (L * N₁') * L ^ k)) := by
    intro x0
    funext μ
    apply ZMod.val_injective
    rw [castT_val, torusCast_val hnew.symm, torusCast_val hold.symm, oldTorusEquiv_val]
  have hy : ∀ y : Torus d (L ^ (m₁ + hatScale L m₁ ϱ) * (L * N₁') * L ^ k),
      (torusCast (castT hA y) : CTorus d L N₁ m₁ (k + 1)) =
        oldTorusEquiv (torusCast y : CTorus d L (L * N₁) m₁ k) := by
    intro y
    funext μ
    apply ZMod.val_injective
    rw [torusCast_val hnew, oldTorusEquiv_val, torusCast_val hold, castT_val]
  by_cases hn : n ≤ k
  · obtain ⟨x0, rfl⟩ := oldTorusEquiv.surjective x
    rw [liftOldGS_mem_Ω G hn, H n x0, hx x0]
    refine mem_minLayer_castT hA hB (fun y => ?_) n _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hy y, mem_hatSet_liftOldPoly]
  · have hjn : j < n := lt_of_le_of_lt hj (not_le.1 hn)
    rw [LargeField.minLayer_of_gt _ hjn]
    simp [liftOldGS, hn]

/-- **`HatSpec` of the spliced terms** (the inherited levels transported, the new level `k + 1`). -/
theorem hatSpec_splice {N : ℕ} {P : Consts} {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    {Tnew T' : Terms d L N₁ m₁ (k + 1) N ϱ}
    (hold : ∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom P.m₀ j X → HatSpec P.m₀ j X (Tm.gs j X))
    (hnew : ∀ X, IsPolyDom P.m₀ (k + 1) X → HatSpec P.m₀ (k + 1) X (Tnew.gs (k + 1) X))
    (hgs : ∀ j, j ≤ k → T'.gs j = (liftOldTerms Tm).gs j)
    (hgs' : T'.gs (k + 1) = Tnew.gs (k + 1)) :
    ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ X, IsPolyDom P.m₀ j X → HatSpec P.m₀ j X (T'.gs j X) := by
  intro j hj1 hjk X hX
  by_cases h : j ≤ k
  · rw [hgs j h]
    have hback : IsPolyDom (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k)
        P.m₀ j (oldTorusEquiv.symm '' X) := by
      apply (oldTorusEquiv_isPolyDom_iff (N₁ := N₁) (m₁ := m₁) (k := k)).2
      simpa [liftOldPoly, Set.image_image] using hX
    have hH := hatSpec_liftOldGS h (hold j hj1 h _ hback)
    simpa [liftOldTerms, liftOldPoly, Set.image_image] using hH
  · obtain rfl : j = k + 1 := by omega
    rw [hgs']
    exact hnew X hX

end Lift

end Balaban.Fluctuation
