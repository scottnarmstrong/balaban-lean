/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldBBound
public import Balaban.Fluctuation.LocalPairLevelInner
public import Balaban.Fluctuation.LocalPairDepth

/-!
# The resummation over the decoupling families at a mark site (P3 (4.45)–(4.49); P6 p. 34)

This file proves the named input `OldResumSite`.

* `subset_cubeIdx_locG'`: **the cubes of a family are cubes of the cover of its local pair** when the
  collar `r'` of the local set is at least the side `L^{k+1+m₁}` of the cells of the top layer (the
  layers of `G′ ∩ 𝔹_{k+1}(V)` are those of `G′` on the cells inside `V`); hence `|J_V| = |J|`
  (`card_locCubes_eq`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

/-- **The union of the `π'_j`-cubes based at the cells of the sites of a set** `B`. -/
def boxUnion (m₀ j : ℕ) (B : Set (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  {x | ∃ y ∈ B, x ∈ box (cbase (cellSide L m₀ m₁ j) y) (L * cellSide L m₀ m₁ j)}

open Classical in
/-- **The size of a connected union of `π'_j`-cubes by the number of its base cells** (P3 (4.48)):
if the union `V` of the `π'_j`-cubes based at the cells of the sites of `B` is a set of `𝒟_j`, then
`d^cov_j(V) ≤ (4 d L + 1 + 2 d L^{d+1}) · #cells(B)`.  The base cells, joined along the nearest-
neighbour connectivity of `V` at the cost `4 d L + 1` per pair of touching cubes (`assemble`), are
met by a connected structure; every `π'_j`-cube in `V` is then attached at the cost `2 d L`
(`extend_tree_of_linked`), and `V` has at most `L^d · #cells(B)` cells. -/
theorem treeLenCovOne_boxUnion_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (B : Set (CTorus d L N₁ m₁ K))
    (hV : IsDj m₀ j (boxUnion m₀ j B)) :
    treeLenCovOne m₀ j (boxUnion m₀ j B) ≤
      (4 * d * L + 1 + 2 * d * L * (L : ℝ) ^ d) *
        ((B.toFinset.image (cbase (cellSide L m₀ m₁ j))).card : ℝ) := by
  classical
  set a := cellSide L m₀ m₁ j with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ j
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLa : 0 < L * a := Nat.mul_pos hL0 ha0
  set V := boxUnion m₀ j B with hVdef
  set C := B.toFinset.image (cbase a) with hC
  set ω : CTorus d L N₁ m₁ K → CTorus d L N₁ m₁ K → ℝ := scaleW L m₀ m₁ j with hωdef
  have haR : ((a : ℕ) : ℝ) = (L : ℝ) ^ (m₀ + m₁ + j) := by
    rw [ha]; unfold cellSide; push_cast; congr 1; ring
  have haRpos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hω0 : ∀ x y, 0 ≤ ω x y := fun x y => by simp only [hωdef, scaleW]; positivity
  have hωa : ∀ x y, ω x y = ((a : ℕ) : ℝ)⁻¹ := fun x y => by simp only [hωdef, scaleW, haR]
  have hωc : ∀ x ∈ V, ∀ y ∈ V, ω x y ≤ ((a : ℕ) : ℝ)⁻¹ := fun x _ y _ => le_of_eq (hωa x y)
  have hainv : ((a : ℕ) : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ haRpos]; exact_mod_cast ha0
  have hpair : 2 * ((d : ℝ) * ((L * a : ℕ) : ℝ) * ((a : ℕ) : ℝ)⁻¹) = 2 * d * L := by
    push_cast; field_simp
  -- the cubes of the base cells lie in `V`
  have hmemC : ∀ c ∈ C, ∃ y ∈ B, c = cbase a y := fun c hc => by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨y, Set.mem_toFinset.1 hy, rfl⟩
  have hboxV : ∀ c ∈ C, box c (L * a) ⊆ V := fun c hc => by
    obtain ⟨y, hy, rfl⟩ := hmemC c hc
    exact fun x hx => ⟨y, hy, hx⟩
  have hcbox : ∀ c : CTorus d L N₁ m₁ K, c ∈ box c (L * a) := fun c => mem_box_self c hLa
  have hnode : ∀ x ∈ V, ∃ c ∈ C, x ∈ box c (L * a) := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨cbase a y, Finset.mem_image_of_mem _ (Set.mem_toFinset.2 hy), hxy⟩
  have hlinkbox : ∀ c ∈ C, ∀ x ∈ box c (L * a), ∀ y ∈ box c (L * a),
      Linked V ω (2 * d * L) x y := fun c hc x hx y hy => by
    have := linked_box_pair hω0 c (L * a) (hboxV c hc) hωc hx hy
    rwa [hpair] at this
  -- the nerve of the base cells
  set H : CTorus d L N₁ m₁ K → CTorus d L N₁ m₁ K → Prop := fun u v =>
    ∃ x ∈ box u (L * a), ∃ y ∈ box v (L * a), x = y ∨ Nbr x y with hHdef
  have hlink : ∀ u ∈ C, ∀ v ∈ C, H u v → ∃ x ∈ ({u} : Finset _), ∃ y ∈ ({v} : Finset _),
      Linked V ω (4 * d * L + 1) x y := by
    intro u hu v hv ⟨x, hx, y, hy, hxy⟩
    refine ⟨u, Finset.mem_singleton_self u, v, Finset.mem_singleton_self v, ?_⟩
    have h1 := hlinkbox u hu u (hcbox u) x hx
    have h3 := hlinkbox v hv y hy v (hcbox v)
    have hxV : x ∈ V := hboxV u hu hx
    have hyV : y ∈ V := hboxV v hv hy
    have h2 : Linked V ω ((a : ℕ) : ℝ)⁻¹ x y := by
      rcases hxy with rfl | hn
      · exact Linked.refl (inv_nonneg.2 haRpos.le) hxV
      · exact Linked.step hn hxV hyV (le_of_eq (hωa x y))
    refine ((h1.trans hω0 h2).trans hω0 h3).mono_c ?_
    linarith
  -- the nerve is connected
  obtain ⟨x₀, hx₀⟩ := hV.1
  obtain ⟨v₀, hv₀, hx₀v₀⟩ := hnode x₀ hx₀
  have hreach : ∀ v ∈ C, Relation.ReflTransGen (fun u v => H u v ∧ u ∈ C ∧ v ∈ C) v₀ v := by
    intro v hv
    have key : ∀ x, Relation.ReflTransGen (fun u v => u ∈ V ∧ v ∈ V ∧ Nbr u v) x₀ x →
        ∃ c ∈ C, x ∈ box c (L * a) ∧
          Relation.ReflTransGen (fun u v => H u v ∧ u ∈ C ∧ v ∈ C) v₀ c := by
      intro x hx
      induction hx with
      | refl => exact ⟨v₀, hv₀, hx₀v₀, Relation.ReflTransGen.refl⟩
      | @tail b c' _ hbc ih =>
        obtain ⟨cb, hcb, hbcb, hpath⟩ := ih
        obtain ⟨cc, hcc, hccb⟩ := hnode c' hbc.2.1
        exact ⟨cc, hcc, hccb, hpath.tail ⟨⟨b, hbcb, c', hccb, Or.inr hbc.2.2⟩, hcb, hcc⟩⟩
    obtain ⟨c, hc, hvc, hpath⟩ := key v (hV.2.2 x₀ hx₀ v (hboxV v hv (hcbox v)))
    exact hpath.tail ⟨⟨v, hvc, v, hcbox v, Or.inl rfl⟩, hc, hv⟩
  have hcov := assemble hω0 C H v₀ hv₀ hreach (fun v => {v}) (fun _ => 0)
    (fun v hv => ⟨{v}, ∅, connStruct_singleton v, by simpa using hboxV v hv (hcbox v), subset_rfl,
      by simp [bondCost]⟩) (4 * d * L + 1) hlink
  obtain ⟨W, E, hcW, hWV, hCW, hcost⟩ := hcov
  have hCW' : ∀ c ∈ C, c ∈ W := fun c hc => hCW (Finset.mem_biUnion.2 ⟨c, hc, by simp⟩)
  obtain ⟨W', E', g1, g2, g3, g4⟩ := extend_tree_of_linked (m₀ := m₀) (j := j) hω0 hcW hWV
    (by positivity : (0 : ℝ) ≤ 2 * d * L) fun b hb => by
      obtain ⟨c, hc, hbc⟩ := hnode b (hb.2 (mem_box_self b hLa))
      exact ⟨c, hCW' c hc, hlinkbox c hc c (hcbox c) b hbc⟩
  have hcells : (cellCount a V : ℝ) ≤ (L : ℝ) ^ d * C.card := by
    have h1 : (Finset.univ.filter fun b : CTorus d L N₁ m₁ K => Aligned a b ∧ box b a ⊆ V) ⊆
        C.biUnion fun c => Finset.univ.filter fun b : CTorus d L N₁ m₁ K =>
          Aligned a b ∧ b ∈ box c (L * a) := by
      intro b hb
      obtain ⟨hal, hbV⟩ := (Finset.mem_filter.1 hb).2
      obtain ⟨c, hc, hbc⟩ := hnode b (hbV (mem_box_self b ha0))
      exact Finset.mem_biUnion.2 ⟨c, hc, Finset.mem_filter.2 ⟨Finset.mem_univ _, hal, hbc⟩⟩
    have h2 : (cellCount a V) ≤ C.card * L ^ d := by
      unfold cellCount
      refine (Finset.card_le_card h1).trans (Finset.card_biUnion_le.trans ?_)
      calc ∑ c ∈ C, (Finset.univ.filter fun b : CTorus d L N₁ m₁ K =>
            Aligned a b ∧ b ∈ box c (L * a)).card ≤ ∑ _c ∈ C, L ^ d :=
            Finset.sum_le_sum fun c hc => by
              obtain ⟨y, -, rfl⟩ := hmemC c hc
              exact card_aligned_in_cube hdvd ha0 (aligned_cbase y)
        _ = C.card * L ^ d := by rw [Finset.sum_const, smul_eq_mul]
    calc (cellCount a V : ℝ) ≤ ((C.card * L ^ d : ℕ) : ℝ) := by exact_mod_cast h2
      _ = (L : ℝ) ^ d * C.card := by push_cast; ring
  have hCpos : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
  calc treeLenCovOne m₀ j V ≤ bondCost ω E' := treeLenCovOne_le_of_chosen (fullCover_chosen hV) g1 g2 g3
    _ ≤ bondCost ω E + (cellCount a V : ℝ) * (2 * d * L) := g4
    _ ≤ (∑ _v ∈ C, (0 : ℝ) + ((C.card : ℝ) - 1) * (4 * d * L + 1)) +
          (L : ℝ) ^ d * C.card * (2 * d * L) :=
        add_le_add hcost (mul_le_mul_of_nonneg_right hcells (by positivity))
    _ ≤ _ := by
        rw [Finset.sum_const_zero, zero_add]
        nlinarith [mul_nonneg hCpos (by positivity : (0 : ℝ) ≤ 4 * d * L + 1)]


section Cells

variable {n : ℕ} [NeZero n]

/-- **The cells of two sites at sup-distance `≤ R`** are at cell-index distance `≤ R / a + 1`. -/
theorem near_cbase_of_supDist_le {a : ℕ} (ha : a ∣ n) (ha0 : 0 < a) {x y : Torus d n} {R : ℕ}
    (h : LargeField.supDist x y ≤ R) : Near (R / a + 1) a (cbase a y) (cbase a x) := by
  have key : ∀ (X qx rx : ℕ), a * qx + rx = X →
      ((a * qx : ℕ) : ZMod n) = ((X : ℕ) : ZMod n) - ((rx : ℕ) : ZMod n) := by
    intro X qx rx hX
    rw [← hX]; push_cast; ring
  have hcoord : ∀ μ, ∃ q : ℤ, |q| ≤ (R / a + 1 : ℕ) ∧
      cbase a x μ = cbase a y μ + (((a : ℤ) * q : ℤ) : ZMod n) := by
    intro μ
    obtain ⟨t, ht, hte⟩ := (LargeField.cycNorm_le_iff _ R).1 (LargeField.supDist_le_iff.1 h μ)
    have hcx : cbase a x μ = ((a * ((x μ).val / a) : ℕ) : ZMod n) := rfl
    have hcy : cbase a y μ = ((a * ((y μ).val / a) : ℕ) : ZMod n) := rfl
    have hxX : (((x μ).val : ℕ) : ZMod n) = x μ := ZMod.natCast_zmod_val _
    have hyY : (((y μ).val : ℕ) : ZMod n) = y μ := ZMod.natCast_zmod_val _
    have hrx := Nat.mod_lt (x μ).val ha0
    have hry := Nat.mod_lt (y μ).val ha0
    have kx := key _ _ _ (Nat.div_add_mod (x μ).val a)
    have ky := key _ _ _ (Nat.div_add_mod (y μ).val a)
    generalize (x μ).val / a = qx at hcx kx
    generalize (y μ).val / a = qy at hcy ky
    generalize (x μ).val % a = rx at kx hrx
    generalize (y μ).val % a = ry at ky hry
    set z : ℤ := t - (rx : ℤ) + (ry : ℤ) with hz
    have hdiff : cbase a x μ - cbase a y μ = ((z : ℤ) : ZMod n) := by
      rw [hcx, hcy, kx, ky, hxX, hyY, hz]
      push_cast
      rw [hte]
      ring
    have hdvd : (a : ℤ) ∣ z := by
      have hn : ((n : ℕ) : ℤ) ∣ z - ((a * qx : ℕ) - (a * qy : ℕ) : ℤ) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have e : (((z - ((a * qx : ℕ) - (a * qy : ℕ) : ℤ)) : ℤ) : ZMod n) =
            ((z : ℤ) : ZMod n) - (((a * qx : ℕ) : ZMod n) - ((a * qy : ℕ) : ZMod n)) := by
          push_cast; ring
        rw [e, ← hdiff, hcx, hcy, sub_self]
      have ha' : (a : ℤ) ∣ ((n : ℕ) : ℤ) := by exact_mod_cast ha
      have h2 : (a : ℤ) ∣ ((a * qx : ℕ) - (a * qy : ℕ) : ℤ) := by
        push_cast
        exact ⟨(qx : ℤ) - qy, by ring⟩
      have := dvd_add (ha'.trans hn) h2
      simpa using this
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨q, ?_, ?_⟩
    · have haz : (0 : ℤ) < a := by exact_mod_cast ha0
      have hrx' : (rx : ℤ) < a := by exact_mod_cast hrx
      have hry' : (ry : ℤ) < a := by exact_mod_cast hry
      have hrx0 : (0 : ℤ) ≤ rx := by positivity
      have hry0 : (0 : ℤ) ≤ ry := by positivity
      obtain ⟨ht1, ht2⟩ := abs_le.1 ht
      have hzle : |z| ≤ (R : ℤ) + a - 1 := by
        rw [hz, abs_le]; constructor <;> linarith
      have hq' : |q| * a ≤ (R : ℤ) + a - 1 := by
        rw [hq, abs_mul, abs_of_pos haz] at hzle; linarith
      have hR : (R : ℤ) < ((R / a + 1 : ℕ) : ℤ) * a := by
        have := Nat.lt_div_mul_add (a := R) ha0
        have h1 : ((R : ℕ) : ℤ) < ((R / a * a + a : ℕ) : ℤ) := by exact_mod_cast this
        push_cast at h1 ⊢
        linarith
      by_contra hcon
      have h1 : ((R / a + 1 : ℕ) : ℤ) + 1 ≤ |q| := by
        have := lt_of_not_ge hcon
        omega
      have : (((R / a + 1 : ℕ) : ℤ) + 1) * a ≤ |q| * a := mul_le_mul_of_nonneg_right h1 haz.le
      nlinarith
    · rw [← hq, ← hdiff]; ring
  choose q hq hqe using hcoord
  exact ⟨q, fun μ => by exact_mod_cast hq μ, funext fun μ => hqe μ⟩

open Classical in
/-- **The cells of a neighbourhood**: the cells of the sites within sup-distance `R` of a finite set
`S` are at most `(2 (R / a + 1) + 1)^d` times the cells of `S`. -/
theorem card_cbase_nbhd_le {a : ℕ} (ha : a ∣ n) (ha0 : 0 < a) (S : Finset (Torus d n)) (R : ℕ) :
    ((Finset.univ.filter fun x : Torus d n => ∃ y ∈ S, LargeField.supDist x y ≤ R).image
      (cbase a)).card ≤ (2 * (R / a + 1) + 1) ^ d * (S.image (cbase a)).card := by
  have hsub : (Finset.univ.filter fun x : Torus d n => ∃ y ∈ S, LargeField.supDist x y ≤ R).image
      (cbase a) ⊆ (S.image (cbase a)).biUnion fun c =>
        Finset.univ.filter fun v => Near (R / a + 1) a c v := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨y, hy, hxy⟩ := (Finset.mem_filter.1 hx).2
    exact Finset.mem_biUnion.2 ⟨cbase a y, Finset.mem_image_of_mem _ hy,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, near_cbase_of_supDist_le ha ha0 hxy⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ c ∈ S.image (cbase a), (Finset.univ.filter fun v => Near (R / a + 1) a c v).card
      ≤ ∑ _c ∈ S.image (cbase a), (2 * (R / a + 1) + 1) ^ d :=
        Finset.sum_le_sum fun c _ => card_near_le _ _ _
    _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

omit [NeZero n] in
/-- Two sites in one cell of side `a` lie in one cell of side `b` for `a ∣ b`. -/
theorem SameCell.of_dvd {a b : ℕ} (hab : a ∣ b) {x y : Torus d n} (h : SameCell a x y) :
    SameCell b x y := by
  obtain ⟨c, rfl⟩ := hab
  intro μ
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h μ]

omit [NeZero n] in
/-- Sites in one cell of side `a` have the same base cell. -/
theorem cbase_eq_of_sameCell {a : ℕ} {x y : Torus d n} (h : SameCell a x y) : cbase a x = cbase a y := by
  funext μ
  simp only [cbase, h μ]

end Cells

end Balaban.Fluctuation

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background
  Balaban.Polymer

namespace Balaban.RootFSpine

section Resum

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

omit [NeZero M] in
/-- **The cubes of a family are cubes of the cover of its local pair** (reading HS-1′): if the collar
`r'` of the local set `V(X, J)` is at least `L^{k+1+m₁}`, every cube `(j, y)` of a family `J` of
cubes of the cover of `G′` is a cube of the cover of `G′ ∩ 𝔹_{k+1}(V(X, J))`: the cell of side
`L^{k+1+m₁}` of its base lies in `V(X, J)`, so the base is in the top layer of `𝔹_{k+1}(V(X, J))`
and the layers of the two sets agree there. -/
theorem subset_cubeIdx_locG' (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) {ρ r r' : ℕ} (hr' : S.L ^ (k + 1 + m₁) ≤ r')
    (X : Finset (Torus S.d (n k))) {J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (hJ : J ∈ allJ g hnn hM1 H hk hρ ρ) :
    J ⊆ (coverOf (locG' g hnn hM1 H hk hρ (locSetXJ g hM1 H r r' X J))).cubeIdx := by
  classical
  intro P hP
  have hPg : P ∈ (coverOf (stepG' g hnn hM1 H hk hρ)).cubeIdx :=
    (Finset.mem_filter.1 (Finset.mem_powerset.1 hJ hP)).1
  obtain ⟨hj, hlay, hbase⟩ := (mem_cubeIdx _).1 hPg
  refine (mem_cubeIdx _).2 ⟨hj, ?_, hbase⟩
  obtain ⟨hyΩ, hyΩ'⟩ := (GeneratingSet.mem_layer _).1 hlay
  have htop : P.2 ∈ (locB g hM1 (locSetXJ g hM1 H r r' X J)).Ω (k + 1) := by
    refine (mem_localB_Ω_top_sameCell le_rfl _ (minSep_le_locB g hM1) P.2).2 fun w hw => ?_
    refine ⟨P.2, Or.inr ⟨P, hP, (mem_cubeP).2 (SameCell.refl _ _)⟩, ?_⟩
    exact (supDist_le_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _) hw).trans hr'
  have hB : P.2 ∈ (locB g hM1 (locSetXJ g hM1 H r r' X J)).Ω P.1 :=
    GeneratingSet.Ω_antitone (locB g hM1 (locSetXJ g hM1 H r r' X J)) hj.1 hj.2 (Nat.le_succ _) htop
  refine (GeneratingSet.mem_layer _).2 ⟨?_, fun h => hyΩ' ?_⟩
  · show P.2 ∈ (stepG' g hnn hM1 H hk hρ).Ω P.1 ∩ (locB g hM1 (locSetXJ g hM1 H r r' X J)).Ω P.1
    exact Finset.mem_inter.2 ⟨hyΩ, hB⟩
  · have h' : P.2 ∈ (stepG' g hnn hM1 H hk hρ).Ω (P.1 + 1) ∩
        (locB g hM1 (locSetXJ g hM1 H r r' X J)).Ω (P.1 + 1) := h
    exact (Finset.mem_inter.1 h').1

omit [NeZero M] in
/-- **`|J_V| = |J|`** for the families of the old part (`subset_cubeIdx_locG'`). -/
theorem card_locCubes_eq (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) {ρ r r' : ℕ} (hr' : S.L ^ (k + 1 + m₁) ≤ r')
    (X : Finset (Torus S.d (n k))) {J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (hJ : J ∈ allJ g hnn hM1 H hk hρ ρ) :
    (locCubes g (coverOf (locG' g hnn hM1 H hk hρ (locSetXJ g hM1 H r r' X J))) J).card = J.card := by
  classical
  have hsub := subset_cubeIdx_locG' g hnn hM1 H hk hρ (r := r) hr' X hJ
  unfold locCubes
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext P
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact hQ
  · intro hP
    exact ⟨⟨P, hsub hP⟩, hP, rfl⟩

omit [NeZero M] in
/-- The cube of `𝕋_k` of a site of the cover torus is that of its site of the history torus. -/
theorem cubeMap_fineOfC_k {k : ℕ} (hk : k + 1 ≤ K)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    LargeField.cubeMap n S.L M K k (fineOfC g hnn hM1 hk x) =
      cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x := by
  have e : S.L ^ k * M = S.L ^ k * (g.c * g.M1) := congrArg _ g.hM
  unfold LargeField.cubeMap cubeKOfC fineOfC
  show _ = blockMap _ _ (LargeField.torusCast
    (congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm x)
  rw [LargeField.blockMap_torusCast, LargeField.blockMap_torusCast, e]

omit [NeZero M] in
/-- The cube of `𝕋_{k+1}` of a site of the cover torus is that of its site of the history torus. -/
theorem cubeMap_fineOfC_succ {k : ℕ} (hk : k + 1 ≤ K)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    LargeField.cubeMap n S.L M K (k + 1) (fineOfC g hnn hM1 hk x) =
      cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x := by
  have e : S.L ^ (k + 1) * M = S.L ^ (k + 1) * (g.c * g.M1) := congrArg _ g.hM
  unfold LargeField.cubeMap cubeOfC fineOfC
  show _ = blockMap _ _ (LargeField.torusCast
    (congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm x)
  rw [LargeField.blockMap_torusCast, LargeField.blockMap_torusCast, e]

omit [NeZero M] in
/-- The frame site of a site of the cover torus lies in a fine lift iff its cube does. -/
theorem toFrame_mem_d7Pull_iff {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K)
    {j : ℕ} {A : Set (Torus S.d (n j))} (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    toFrame g hnn hM1 F hk x ∈ d7Pull F j A ↔
      LargeField.cubeMap n S.L M K j (fineOfC g hnn hM1 hk x) ∈ A := by
  show castT F.side (castT F.side.symm (fineOfC g hnn hM1 hk x)) ∈
    fineSet (S := S) (n := n) M K j A ↔ _
  rw [castT_castT_symm]
  rfl

omit [NeZero M] in
/-- **The frame sites of `A_X` are the sites of `X ∩ Ω_{k+1}`.** -/
theorem toFrame_activeCoreC_subset {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (X : Finset (Torus S.d (n k)))
    {x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (hx : x ∈ activeCoreC (c := g.c) (n1 := n (k + 1)) (n0 := n k) (k := k) (H.step k) hM1 X) :
    toFrame g hnn hM1 F hk x ∈
      d7Pull F k (X : Set (Torus S.d (n k))) ∩ d7Pull F (k + 1) (OmegaCube H (k + 1)) := by
  obtain ⟨hX, hΩ⟩ := (mem_activeCoreC _).1 hx
  refine ⟨(toFrame_mem_d7Pull_iff g hnn hM1 F hk x).2 ?_, (toFrame_mem_d7Pull_iff g hnn hM1 F hk x).2 ?_⟩
  · rw [cubeMap_fineOfC_k]; exact hX
  · rw [cubeMap_fineOfC_succ]; exact hΩ

omit [NeZero M] in
/-- The frame site of a site has the same coordinates. -/
theorem toFrame_val {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (μ : Fin S.d) :
    ((toFrame g hnn hM1 F hk x) μ).val = (x μ).val := by
  unfold toFrame fineOfC
  rw [castT_val, LargeField.torusCast_val]

omit [NeZero M] in
/-- **`toFrame` maps cells to cells**: the frame site of the base of a cell is the base of the cell of
the frame site. -/
theorem toFrame_cbase {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K)
    (a : ℕ) (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    toFrame g hnn hM1 F hk (cbase a x) = cbase a (toFrame g hnn hM1 F hk x) := by
  funext μ
  apply ZMod.val_injective
  rw [toFrame_val]
  simp only [cbase]
  rw [toFrame_val]
  have hlt : a * ((x μ).val / a) < (g.c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1) :=
    lt_of_le_of_lt (Nat.mul_div_le _ _) (ZMod.val_lt _)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ZMod.val_natCast, Nat.mod_eq_of_lt]
  calc a * ((x μ).val / a) ≤ (x μ).val := Nat.mul_div_le _ _
    _ < _ := by rw [← toFrame_val g hnn hM1 F hk x μ]; exact ZMod.val_lt _

omit [NeZero M] in
/-- `toFrame` is injective. -/
theorem toFrame_injective {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K) :
    Function.Injective (toFrame g hnn hM1 F hk) := fun x y h => by
  funext μ
  apply ZMod.val_injective
  rw [← toFrame_val g hnn hM1 F hk x μ, ← toFrame_val g hnn hM1 F hk y μ, h]


end Resum

end Balaban.RootFSpine
