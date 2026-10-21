/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldBBound
public import Balaban.Fluctuation.LocalPairLevelInner
public import Balaban.Fluctuation.LocalPairDepth
public import Balaban.Fluctuation.LocalClassDensityFamilyNumA

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


omit [NeZero N₁] in
/-- The data sites of the intersection of two generating sets lie in the data sites of the second. -/
theorem dataSites_inter_subset {N₀ k' : ℕ} [NeZero N₀] {ϱ : ℝ}
    (G B : Multiscale.GeneratingSet d L N₀ k' ϱ) :
    Background.dataSites (G.inter B) ⊆ Background.dataSites B := by
  intro x hx
  rcases (Background.mem_dataSites _).1 hx with h | h
  · rw [Multiscale.GeneratingSet.inter_Ω] at h
    exact (Background.mem_dataSites _).2 (Or.inl (Finset.mem_inter.1 h).2)
  · obtain ⟨-, y, hy, hyx⟩ := (Background.mem_collar _).1 h
    rw [Multiscale.GeneratingSet.inter_Ω] at hy
    by_cases hxB : x ∈ B.Ω 1
    · exact (Background.mem_dataSites _).2 (Or.inl hxB)
    · exact (Background.mem_dataSites _).2
        (Or.inr ((Background.mem_collar _).2 ⟨hxB, y, (Finset.mem_inter.1 hy).2, hyx⟩))



/-- A site and the base of its cell lie in one cell (any torus). -/
theorem sameCell_cbase_self {a : ℕ} (x : Torus d n) : SameCell a x (cbase a x) := by
  intro μ
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · simp
  have hlt : a * ((x μ).val / a) < n := lt_of_le_of_lt (Nat.mul_div_le _ _) (ZMod.val_lt _)
  simp only [cbase]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel_left _ ha0]


/-- **The subsets of a finite set with weight `e^{-β |J|}`**: `∑_{J ⊆ T} e^{-β |J|} ≤ e^{e^{-β} |T|}`. -/
theorem sum_powerset_exp_le {α : Type*} (T : Finset α) (β : ℝ) :
    ∑ J ∈ T.powerset, Real.exp (-β * J.card) ≤ Real.exp (Real.exp (-β) * T.card) := by
  have e : ∑ J ∈ T.powerset, Real.exp (-β * J.card) =
      ∑ J ∈ T.powerset, Real.exp (-β) ^ J.card * (1 : ℝ) ^ (T.card - J.card) := by
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [one_pow, mul_one, ← Real.exp_nat_mul]; ring_nf
  rw [e, Finset.sum_pow_mul_eq_add_pow]
  calc (Real.exp (-β) + 1) ^ T.card ≤ Real.exp (Real.exp (-β)) ^ T.card :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (Real.exp (-β))]) _
    _ = Real.exp (Real.exp (-β) * T.card) := by rw [← Real.exp_nat_mul]; ring_nf

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


omit [NeZero M] in
open Classical in
/-- **The cells of the base sites of a mark** (P3 (4.48)): the cells of scale `k + 1` of `markBase`
are at most those of `X ∩ Ω_{k+1}`, of the connecting structure `optW`, and `N₀` times those of
`X ∩ Ω_{k+1}` and the cubes of `J`, `N₀ = (2 ((r + r' + 11 L^{m₁} L^{k+1} + 1) / a_{k+1} + 1) + 1)^d`
(the local set lies within `r + r'` of `A_X` and the cubes of `J`, its data sites within
`11 L^{m₁} L^{k+1} + 1` of the local set, `localB_dataSites_range`). -/
theorem card_cells_markBase_le {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊)
    (hL2 : 2 ≤ S.L) (hgc : S.L ^ m₀ ∣ g.c * n (k + 1)) {ρ r r' : ℕ}
    (X : Finset (Torus S.d (n k))) {J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (hJ : J ∈ allJ g hnn hM1 H hk hρ ρ) :
    ((markBase g hnn hM1 F H hk hρ r r' X J).toFinset.image
        (cbase (cellSide S.L m₀ m₁ (k + 1)))).card ≤
      ((d7Pull F k (X : Set (Torus S.d (n k))) ∩ d7Pull F (k + 1) (OmegaCube H (k + 1))).toFinset.image
          (cbase (cellSide S.L m₀ m₁ (k + 1)))).card +
        ((optW F k (H.omegaPost k) X).image (cbase (cellSide S.L m₀ m₁ (k + 1)))).card +
        (2 * ((r + r' + (11 * S.L ^ m₁ * S.L ^ (k + 1) + 1)) / cellSide S.L m₀ m₁ (k + 1) + 1) + 1) ^
            S.d *
          (((d7Pull F k (X : Set (Torus S.d (n k))) ∩
              d7Pull F (k + 1) (OmegaCube H (k + 1))).toFinset.image
            (cbase (cellSide S.L m₀ m₁ (k + 1)))).card + J.card) := by
  set cs := cellSide S.L m₀ m₁ (k + 1) with hcs
  have hcs0 : 0 < cs := cellSide_pos m₀ m₁ (k + 1)
  have hdvdC : cs ∣ (g.c * n (k + 1) * S.L ^ m₁) * S.L ^ (k + 1) := cellSide_dvd hgc le_rfl
  set A := d7Pull F k (X : Set (Torus S.d (n k))) ∩ d7Pull F (k + 1) (OmegaCube H (k + 1)) with hA
  set Vc := locSetXJ g hM1 H r r' X J with hVc
  set R₀ := r + r' + (11 * S.L ^ m₁ * S.L ^ (k + 1) + 1) with hR₀
  set Sb : Finset (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :=
    activeCoreC (c := g.c) (n1 := n (k + 1)) (n0 := n k) (k := k) (H.step k) hM1 X ∪
      J.biUnion cubeP with hSb
  set Nb : Finset (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :=
    Finset.univ.filter fun x => ∃ y ∈ Sb, LargeField.supDist x y ≤ R₀ with hNb
  -- the local set and its data sites lie in the neighbourhood
  have hV0 : ∀ x ∈ Vc, ∃ y ∈ Sb, LargeField.supDist x y ≤ r + r' := by
    rintro x ⟨y, hy, hxy⟩
    rcases hy with hy | ⟨P, hP, hyP⟩
    · obtain ⟨y', hy', hyy'⟩ := (mem_collarCoreC _).1 hy
      refine ⟨y', Finset.mem_union_left _ hy', ?_⟩
      calc LargeField.supDist x y' ≤ LargeField.supDist x y + LargeField.supDist y y' :=
            LargeField.supDist_triangle _ _ _
        _ ≤ r' + r := add_le_add hxy hyy'
        _ = r + r' := by ring
    · exact ⟨y, Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨P, hP, hyP⟩), by omega⟩
  have hVN : ∀ x ∈ Vc, x ∈ Nb := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := hV0 x hx
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, y, hy, by omega⟩
  have hDN : ∀ x ∈ Background.dataSites (locG' g hnn hM1 H hk hρ Vc), x ∈ Nb := by
    intro x hx
    have hx' := dataSites_inter_subset _ _ hx
    obtain ⟨v, hv, hxv⟩ := SmallField.GsSpec.localB_dataSites_range hL2 hx'
    obtain ⟨y, hySb, hvy⟩ := hV0 v hv
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, y, hySb, ?_⟩
    calc LargeField.supDist x y ≤ LargeField.supDist x v + LargeField.supDist v y :=
          LargeField.supDist_triangle _ _ _
      _ ≤ (11 * S.L ^ m₁ * S.L ^ (k + 1) + 1) + (r + r') := add_le_add hxv hvy
      _ = R₀ := by rw [hR₀]; ring
  have hsub : (markBase g hnn hM1 F H hk hρ r r' X J).toFinset.image (cbase cs) ⊆
      (A.toFinset.image (cbase cs) ∪ (optW F k (H.omegaPost k) X).image (cbase cs)) ∪
        (Nb.image (toFrame g hnn hM1 F hk)).image (cbase cs) := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    rcases Set.mem_toFinset.1 hy with ((hyA | hyW) | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Set.mem_toFinset.2 hyA)))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hyW)))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (Finset.mem_image_of_mem _ (hVN x hx)))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (Finset.mem_image_of_mem _ (hDN x (Finset.mem_coe.1 hx))))
  -- the cells of the frame sites of a set of the cover torus
  have hcast : ∀ T : Finset (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)),
      ((T.image (toFrame g hnn hM1 F hk)).image (cbase cs)).card = (T.image (cbase cs)).card := by
    intro T
    have e : (T.image (toFrame g hnn hM1 F hk)).image (cbase cs) =
        (T.image (cbase cs)).image (toFrame g hnn hM1 F hk) := by
      rw [Finset.image_image, Finset.image_image]
      congr 1
      funext x
      exact (toFrame_cbase g hnn hM1 F hk cs x).symm
    rw [e, Finset.card_image_of_injective _ (toFrame_injective g hnn hM1 F hk)]
  -- the cells of `A_X` on the cover torus
  have hAX : ((activeCoreC (c := g.c) (n1 := n (k + 1)) (n0 := n k) (k := k) (H.step k) hM1 X).image
      (cbase cs)).card ≤ (A.toFinset.image (cbase cs)).card := by
    rw [← hcast]
    refine Finset.card_le_card fun c hc => ?_
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_image_of_mem _ (Set.mem_toFinset.2 (toFrame_activeCoreC_subset g hnn hM1 F H hk X hx))
  -- the cells of the cubes of `J`
  have hJc : ((J.biUnion cubeP).image (cbase cs)).card ≤ J.card := by
    refine (Finset.card_le_card (t := J.image fun P => cbase cs P.2) fun c hc => ?_).trans
      Finset.card_image_le
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨P, hP, hyP⟩ := Finset.mem_biUnion.1 hy
    have hPl : P.1 ≤ k + 1 := by
      have hPg : P ∈ (coverOf (stepG' g hnn hM1 H hk hρ)).cubeIdx :=
        (Finset.mem_filter.1 (Finset.mem_powerset.1 hJ hP)).1
      exact ((mem_cubeIdx _).1 hPg).1.2
    have hdv : S.L ^ (P.1 + m₁) ∣ cs := by
      rw [hcs]; unfold cellSide; exact pow_dvd_pow _ (by omega)
    refine Finset.mem_image.2 ⟨P, hP, ?_⟩
    exact (cbase_eq_of_sameCell (SameCell.of_dvd hdv ((mem_cubeP).1 hyP))).symm
  have hSbc : (Sb.image (cbase cs)).card ≤ (A.toFinset.image (cbase cs)).card + J.card := by
    rw [hSb, Finset.image_union]
    exact (Finset.card_union_le _ _).trans (add_le_add hAX hJc)
  have hNbc := card_cbase_nbhd_le hdvdC hcs0 Sb R₀
  calc ((markBase g hnn hM1 F H hk hρ r r' X J).toFinset.image (cbase cs)).card
      ≤ ((A.toFinset.image (cbase cs) ∪ (optW F k (H.omegaPost k) X).image (cbase cs)) ∪
          (Nb.image (toFrame g hnn hM1 F hk)).image (cbase cs)).card := Finset.card_le_card hsub
    _ ≤ (A.toFinset.image (cbase cs)).card + ((optW F k (H.omegaPost k) X).image (cbase cs)).card +
          ((Nb.image (toFrame g hnn hM1 F hk)).image (cbase cs)).card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add (Finset.card_union_le _ _) le_rfl)
    _ ≤ _ := by
        rw [hcast]
        exact Nat.add_le_add le_rfl (hNbc.trans (Nat.mul_le_mul_left _ hSbc))


include hnn in
open Classical in
/-- **The cells of `X ∩ Ω_{k+1}`** (G1 at scale `k`): at most `c₁ (1 + d_k(X mod Ω_k^c))` for a valid
old label `X`; a cell of scale `k + 1` meeting `X ∩ Ω_{k+1}` contains a cell of scale `k` of
`X ∩ Ω_k^post`. -/
theorem card_cells_inter_le {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) {X : Finset (Torus S.d (n k))}
    (hX : FineValidAt F k (H.omegaPost k) X) :
    (((d7Pull F k (X : Set (Torus S.d (n k))) ∩ d7Pull F (k + 1) (OmegaCube H (k + 1))).toFinset.image
        (cbase (cellSide S.L m₀ m₁ (k + 1)))).card : ℝ) ≤
      c1 S.d S.L * (1 + d7SizeAt F k (H.omegaPost k) X) := by
  set ck := cellSide S.L m₀ m₁ k with hck
  have hck0 : 0 < ck := cellSide_pos m₀ m₁ k
  have hkK : k ≤ K := Nat.le_of_succ_le hk
  have hdk : ck ∣ cellSide S.L m₀ m₁ (k + 1) := by
    rw [hck]; unfold cellSide; exact pow_dvd_pow _ (by omega)
  have hcell : ∀ {Y : Set (Torus S.d (n k))} {x}, x ∈ d7Pull F k Y →
      Localization.box (cbase ck x) ck ⊆ d7Pull F k Y := fun {Y x} hx => by
    rcases cell_dichotomy F.divN₁ hkK (d7Pull_isPiUnion F hnn hkK Y)
        (aligned_cbase (a := ck) x) with h | h
    · exact h
    · exact absurd hx (h (mem_box_cbase hck0 x))
  have hsub : (d7Pull F k (X : Set (Torus S.d (n k))) ∩
      d7Pull F (k + 1) (OmegaCube H (k + 1))).toFinset.image (cbase (cellSide S.L m₀ m₁ (k + 1))) ⊆
      (cellsIn (L := S.L) m₀ k (d7Pull F k (X : Set (Torus S.d (n k))) ∩
        d7Pull F k (H.omegaPost k))).image (cbase (cellSide S.L m₀ m₁ (k + 1))) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨hxX, hxΩ⟩ := Set.mem_toFinset.1 hx
    have hxΩk := H.d7Pull_OmegaCube_succ_subset F hnn hk hxΩ
    refine Finset.mem_image.2 ⟨cbase ck x, ?_, ?_⟩
    · simp only [cellsIn, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨aligned_cbase x, fun z hz => ⟨hcell hxX hz, hcell hxΩk hz⟩⟩
    · exact cbase_eq_of_sameCell (SameCell.of_dvd hdk (sameCell_cbase_self x)).symm
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := cellsIn (L := S.L) m₀ k (d7Pull F k
    (X : Set (Torus S.d (n k))) ∩ d7Pull F k (H.omegaPost k)))
    (f := cbase (cellSide S.L m₀ m₁ (k + 1)))
  have h3 := hX.cellCount_le F.divN₁ hkK
  rw [← card_cellsIn_eq_cellCount] at h3
  calc _ ≤ ((cellsIn (L := S.L) m₀ k (d7Pull F k (X : Set (Torus S.d (n k))) ∩
        d7Pull F k (H.omegaPost k))).card : ℝ) := by exact_mod_cast h1.trans h2
    _ ≤ _ := h3

omit [NeZero M] in
/-- **The cells of the connecting structure of an optimal cover** (`card_image_cbase_le`): at most
`3^d (d_k(X mod Ω_k^c) / L + 1)` cells of scale `k + 1`. -/
theorem card_cells_optW_le {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) {X : Finset (Torus S.d (n k))}
    (hX : FineValidAt F k (H.omegaPost k) X) :
    (((optW F k (H.omegaPost k) X).image (cbase (cellSide S.L m₀ m₁ (k + 1)))).card : ℝ) ≤
      3 ^ S.d * ((S.L : ℝ)⁻¹ * d7SizeAt F k (H.omegaPost k) X + 1) := by
  obtain ⟨𝒦, E, hadm, hcost⟩ := optW_spec F hX
  have h := card_image_cbase_le F.divN₁ hk hadm.2.2.1
  rw [bondCost_scaleW_succ (m₀ := m₀) (j := k) E, hcost] at h
  exact h


open Classical in
/-- **The cubes of the cover of the step inside a site**: the cubes of levels `k`, `k + 1` of the
localization range whose frame sites lie in `V`. -/
noncomputable def cubesIn {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) (H : RegionHistory S n R k0 K)
    {k : ℕ} (hk : k + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ρ : ℕ)
    (V : Set (CTorus S.d S.L F.N₁ m₁ K)) :
    Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :=
  ((coverOf (stepG' g hnn hM1 H hk hρ)).cubeIdx.filter fun P => k ≤ P.1 ∧
    (cubeP P : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) ⊆ locRange g hM1 H ρ).filter
      fun P => toFrame g hnn hM1 F hk '' (cubeP P : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
        ⊆ V

omit [NeZero M] in
/-- **A family with the site `V` consists of cubes inside `V`.** -/
theorem subset_cubesIn_of_mem_famAt {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊)
    {ρ r r' : ℕ} {X : Finset (Torus S.d (n k))} {V : Set (CTorus S.d S.L F.N₁ m₁ K)}
    {J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (hJ : J ∈ famAt g hnn hM1 F H hk hρ ρ r r' X V) :
    J ⊆ cubesIn g hnn hM1 F H hk hρ ρ V := by
  classical
  obtain ⟨hJa, -, hJV⟩ := (mem_famAt g hnn hM1).1 hJ
  intro P hP
  refine Finset.mem_filter.2 ⟨Finset.mem_powerset.1 hJa hP, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← hJV]
  refine markBase_subset_markSite g hnn hM1 F H hk hρ r r' X J (Or.inl (Or.inr ⟨x, ?_, rfl⟩))
  exact cubeP_subset_locSetXJ g hM1 H r r' X hP hx

omit [NeZero M] in
open Classical in
/-- **The number of cubes of one level inside a union of `π'_{k+1}`-cubes**: at most
`L^{d (k + 1 + m₀ - j)}` per cell of scale `k + 1`. -/
theorem card_cubesIn_level_le {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ρ : ℕ)
    {V : Set (CTorus S.d S.L F.N₁ m₁ K)} (hV : IsPiPrimeUnion m₀ (k + 1) V) {j : ℕ}
    (hjk : j ≤ k + 1) :
    ((cubesIn g hnn hM1 F H hk hρ ρ V).filter fun P => P.1 = j).card ≤
      cellCount (cellSide S.L m₀ m₁ (k + 1)) V * (S.L ^ (k + 1 + m₀ - j)) ^ S.d := by
  set cs := cellSide S.L m₀ m₁ (k + 1) with hcs
  set a := S.L ^ (j + m₁) with ha
  have hcs0 : 0 < cs := cellSide_pos m₀ m₁ (k + 1)
  have hdvd : cs ∣ (F.N₁ * S.L ^ m₁) * S.L ^ K := cellSide_dvd F.divN₁ hk
  have hcs_eq : cs = S.L ^ (k + 1 + m₀ - j) * a := by
    rw [hcs, ha, ← pow_add]; unfold cellSide; congr 1; omega
  have hadvd : a ∣ cs := ⟨S.L ^ (k + 1 + m₀ - j), by rw [hcs_eq, mul_comm]⟩
  have ha0 : 0 < a := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _
  have hinj : Set.InjOn (fun P : ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1) =>
      toFrame g hnn hM1 F hk P.2) ↑((cubesIn g hnn hM1 F H hk hρ ρ V).filter fun P => P.1 = j) := by
    intro P hP Q hQ h
    have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hP)).2
    have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hQ)).2
    exact Prod.ext (h1.trans h2.symm) (toFrame_injective g hnn hM1 F hk h)
  rw [← Finset.card_image_of_injOn hinj]
  have hsub : ((cubesIn g hnn hM1 F H hk hρ ρ V).filter fun P => P.1 = j).image
      (fun P => toFrame g hnn hM1 F hk P.2) ⊆
      (Finset.univ.filter fun b : CTorus S.d S.L F.N₁ m₁ K => Aligned cs b ∧ Localization.box b cs ⊆ V).biUnion
        fun c => Finset.univ.filter fun t : CTorus S.d S.L F.N₁ m₁ K =>
          Aligned a t ∧ t ∈ Localization.box c (S.L ^ (k + 1 + m₀ - j) * a) := by
    intro t ht
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨hPc, hPj⟩ := Finset.mem_filter.1 hP
    obtain ⟨hPa, hPV⟩ := Finset.mem_filter.1 hPc
    have hPg := (Finset.mem_filter.1 hPa).1
    obtain ⟨-, -, hbase⟩ := (mem_cubeIdx _).1 hPg
    have htV : toFrame g hnn hM1 F hk P.2 ∈ V := hPV ⟨P.2, (mem_cubeP).2 (SameCell.refl _ _), rfl⟩
    obtain ⟨b, hb, htb, hbV⟩ := hV _ htV
    refine Finset.mem_biUnion.2 ⟨cbase cs (toFrame g hnn hM1 F hk P.2), ?_, ?_⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, aligned_cbase _,
        (cell_subset_cube hdvd hcs0 hb htb).trans hbV⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun μ => ?_, ?_⟩
      · rw [toFrame_val, ha, ← hPj]; exact hbase μ
      · rw [← hcs_eq]; exact mem_box_cbase hcs0 _
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ c ∈ (Finset.univ.filter fun b : CTorus S.d S.L F.N₁ m₁ K => Aligned cs b ∧ Localization.box b cs ⊆ V),
        (Finset.univ.filter fun t : CTorus S.d S.L F.N₁ m₁ K =>
          Aligned a t ∧ t ∈ Localization.box c (S.L ^ (k + 1 + m₀ - j) * a)).card
      ≤ ∑ _c ∈ (Finset.univ.filter fun b : CTorus S.d S.L F.N₁ m₁ K => Aligned cs b ∧ Localization.box b cs ⊆ V),
          (S.L ^ (k + 1 + m₀ - j)) ^ S.d :=
        Finset.sum_le_sum fun c hc => card_aligned_in_box_mul (hadvd.trans hdvd) ha0 _
          (Localization.aligned_of_dvd hadvd (Finset.mem_filter.1 hc).2.1)
    _ = _ := by rw [Finset.sum_const, smul_eq_mul]; rfl


omit [NeZero M] in
/-- **The number of cubes of the cover inside a site of `𝒟_{k+1}`**: at most
`2 L^{d (m₀ + 1)} c₁ (1 + d^cov_{k+1}(V))`. -/
theorem card_cubesIn_le {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ρ : ℕ)
    {V : Set (CTorus S.d S.L F.N₁ m₁ K)} (hV : IsDj m₀ (k + 1) V) :
    ((cubesIn g hnn hM1 F H hk hρ ρ V).card : ℝ) ≤
      2 * ((S.L : ℝ) ^ (m₀ + 1)) ^ S.d * (c1 S.d S.L * (1 + treeLenCovOne (d := S.d) (L := S.L)
        (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1) V)) := by
  classical
  have hsplit : cubesIn g hnn hM1 F H hk hρ ρ V ⊆
      ((cubesIn g hnn hM1 F H hk hρ ρ V).filter fun P => P.1 = k) ∪
        ((cubesIn g hnn hM1 F H hk hρ ρ V).filter fun P => P.1 = k + 1) := by
    intro P hP
    have hPa := (Finset.mem_filter.1 hP).1
    have hkP := (Finset.mem_filter.1 hPa).2.1
    have hPk : P.1 ≤ k + 1 := ((mem_cubeIdx _).1 (Finset.mem_filter.1 hPa).1).1.2
    rcases (show P.1 = k ∨ P.1 = k + 1 by omega) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hP, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hP, h⟩)
  have h1 := card_cubesIn_level_le g hnn hM1 F H hk hρ ρ hV.2.1 (j := k) (by omega)
  have h2 := card_cubesIn_level_le g hnn hM1 F H hk hρ ρ hV.2.1 (j := k + 1) le_rfl
  have hcc := cellCount_le_one_add_treeLenCovOne F.divN₁ hk hV
  have hcard : (cubesIn g hnn hM1 F H hk hρ ρ V).card ≤
      cellCount (cellSide S.L m₀ m₁ (k + 1)) V * (S.L ^ (k + 1 + m₀ - k)) ^ S.d +
        cellCount (cellSide S.L m₀ m₁ (k + 1)) V * (S.L ^ (k + 1 + m₀ - (k + 1))) ^ S.d :=
    (Finset.card_le_card hsplit).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add h1 h2))
  have e1 : k + 1 + m₀ - k = m₀ + 1 := by omega
  have e2 : k + 1 + m₀ - (k + 1) = m₀ := by omega
  rw [e1, e2] at hcard
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne S.L)
  have hpow : ((S.L : ℝ) ^ m₀) ^ S.d ≤ ((S.L : ℝ) ^ (m₀ + 1)) ^ S.d :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 (by omega)) _
  have hcR : ((cubesIn g hnn hM1 F H hk hρ ρ V).card : ℝ) ≤
      (cellCount (cellSide S.L m₀ m₁ (k + 1)) V : ℝ) * ((S.L : ℝ) ^ (m₀ + 1)) ^ S.d +
        (cellCount (cellSide S.L m₀ m₁ (k + 1)) V : ℝ) * ((S.L : ℝ) ^ m₀) ^ S.d := by
    exact_mod_cast hcard
  have hc0 : (0 : ℝ) ≤ cellCount (cellSide S.L m₀ m₁ (k + 1)) V := Nat.cast_nonneg _
  calc _ ≤ (cellCount (cellSide S.L m₀ m₁ (k + 1)) V : ℝ) * ((S.L : ℝ) ^ (m₀ + 1)) ^ S.d +
        (cellCount (cellSide S.L m₀ m₁ (k + 1)) V : ℝ) * ((S.L : ℝ) ^ (m₀ + 1)) ^ S.d :=
        hcR.trans (by nlinarith [mul_le_mul_of_nonneg_left hpow hc0])
    _ = 2 * ((S.L : ℝ) ^ (m₀ + 1)) ^ S.d * (cellCount (cellSide S.L m₀ m₁ (k + 1)) V : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcc (by positivity)


end Resum

end Balaban.RootFSpine
