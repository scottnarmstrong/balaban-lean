module

public import Balaban.Polymer.BlockTorus
public import Balaban.Polymer.Support
public import Balaban.Frozen.Geometry.IsPolymer

/-!
# The bridge to the frozen geometry

For `ℓ = s * m` the torus `Torus d ℓ` is partitioned into the blocks of side `s`, indexed by
`Torus d m`.  `blockOf` is the block index; `siteSet Y` is the union of the blocks in `Y`.
Then `Balaban.IsPolymer d (s * m) s (siteSet Y)` holds iff `Y` is a polymer of the block torus
(`isPolymer_siteSet_iff`), `|siteSet Y| = s ^ d * |Y|` (`card_siteSet`), and every frozen polymer
is `siteSet` of its set of blocks.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

variable (d s m : ℕ) [NeZero s] [NeZero m]

theorem val_div_lt (x : ZMod (s * m)) : x.val / s < m := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have := ZMod.val_lt x
  rw [Nat.div_lt_iff_lt_mul hs]
  linarith [mul_comm s m]

/-- The index of the block of side `s` containing a site. -/
def blockOf (x : Balaban.Torus d (s * m)) : Balaban.Torus d m :=
  fun μ => (((x μ).val / s : ℕ) : ZMod m)

theorem blockOf_val (x : Balaban.Torus d (s * m)) (μ : Fin d) :
    (blockOf d s m x μ).val = (x μ).val / s := by
  unfold blockOf
  exact ZMod.val_cast_of_lt (val_div_lt s m _)

theorem blockOf_eq_iff (x y : Balaban.Torus d (s * m)) :
    blockOf d s m x = blockOf d s m y ↔ ∀ μ, (x μ).val / s = (y μ).val / s := by
  constructor
  · intro h μ
    rw [← blockOf_val d s m x μ, ← blockOf_val d s m y μ, h]
  · intro h
    funext μ
    apply ZMod.val_injective
    rw [blockOf_val, blockOf_val, h]

/-- The union of the blocks indexed by `Y`. -/
def siteSet (Y : Finset (Balaban.Torus d m)) : Finset (Balaban.Torus d (s * m)) :=
  Finset.univ.filter (fun x => blockOf d s m x ∈ Y)

theorem mem_siteSet {Y : Finset (Balaban.Torus d m)} {x : Balaban.Torus d (s * m)} :
    x ∈ siteSet d s m Y ↔ blockOf d s m x ∈ Y := by
  simp [siteSet]

omit [NeZero s] [NeZero m] in
theorem lt_of_cell {c r : ℕ} (hc : c < m) (hr : r < s) : s * c + r < s * m := by
  have : s * (c + 1) ≤ s * m := Nat.mul_le_mul_left s hc
  rw [Nat.mul_add, Nat.mul_one] at this
  omega

theorem cell_div {c r : ℕ} (hr : r < s) : (s * c + r) / s = c := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  rw [Nat.mul_add_div hs, Nat.div_eq_of_lt hr, Nat.add_zero]

theorem card_fiber_blockOf (c : Balaban.Torus d m) :
    (Finset.univ.filter (fun x : Balaban.Torus d (s * m) => blockOf d s m x = c)).card = s ^ d := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hval : ∀ (r : Fin d → Fin s) μ,
      (((s * (c μ).val + (r μ).val : ℕ) : ZMod (s * m))).val = s * (c μ).val + (r μ).val :=
    fun r μ => ZMod.val_cast_of_lt (lt_of_cell s m (ZMod.val_lt _) (r μ).2)
  symm
  calc s ^ d = (Finset.univ : Finset (Fin d → Fin s)).card := by simp
    _ = _ := by
      refine Finset.card_bij (fun r _ => fun μ => (((s * (c μ).val + (r μ).val : ℕ) : ZMod (s * m))))
        ?_ ?_ ?_
      · intro r _
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        funext μ
        apply ZMod.val_injective
        rw [blockOf_val, hval, cell_div s (r μ).2]
      · intro r _ r' _ h
        funext μ
        have := congrFun h μ
        have h2 := congrArg ZMod.val this
        rw [hval, hval] at h2
        exact Fin.ext (by omega)
      · intro x hx
        rw [Finset.mem_filter] at hx
        have hb := fun μ => (blockOf_eq_iff d s m x x).mp rfl μ
        have hx' : ∀ μ, (x μ).val / s = (c μ).val := fun μ => by
          rw [← blockOf_val d s m x μ, hx.2]
        have hr : ∀ μ, (x μ).val - s * (c μ).val < s := fun μ => by
          have h1 := Nat.div_add_mod (x μ).val s
          have h2 := Nat.mod_lt (x μ).val hs
          rw [hx' μ] at h1
          omega
        refine ⟨fun μ => ⟨(x μ).val - s * (c μ).val, hr μ⟩, Finset.mem_univ _, ?_⟩
        funext μ
        apply ZMod.val_injective
        have h3 := hval (fun μ => ⟨(x μ).val - s * (c μ).val, hr μ⟩) μ
        refine h3.trans ?_
        have h1 := Nat.div_add_mod (x μ).val s
        rw [hx' μ] at h1
        show s * (c μ).val + ((x μ).val - s * (c μ).val) = (x μ).val
        omega

theorem card_siteSet (Y : Finset (Balaban.Torus d m)) :
    (siteSet d s m Y).card = s ^ d * Y.card := by
  have h1 : (siteSet d s m Y).card =
      ∑ c ∈ Y, (Finset.univ.filter (fun x : Balaban.Torus d (s * m) => blockOf d s m x = c)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := blockOf d s m) (t := Y)]
    · refine Finset.sum_congr rfl (fun c hc => ?_)
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_siteSet]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨h ▸ hc, h⟩
    · intro x hx; exact (mem_siteSet d s m).mp hx
  rw [h1, Finset.sum_congr rfl (fun c _ => card_fiber_blockOf d s m c)]
  simp [mul_comm]

section Steps

variable {d s m}

theorem val_add_single (x : Balaban.Torus d (s * m)) (μ ν : Fin d) :
    ((x + (Pi.single μ 1 : Balaban.Torus d (s * m))) ν).val =
      if ν = μ then ((x μ).val + 1 % (s * m)) % (s * m) else (x ν).val := by
  by_cases h : ν = μ
  · subst h
    simp only [Pi.add_apply, Pi.single_eq_same, ite_true]
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod]
  · simp [h]

theorem blockOf_add_single_ne (x : Balaban.Torus d (s * m)) {μ ν : Fin d} (h : ν ≠ μ) :
    blockOf d s m (x + Pi.single μ 1) ν = blockOf d s m x ν := by
  apply ZMod.val_injective
  rw [blockOf_val, blockOf_val, val_add_single]
  simp [h]

theorem blockOf_add_single_eq (x : Balaban.Torus d (s * m)) (μ : Fin d) :
    blockOf d s m (x + Pi.single μ 1) μ =
      ((((x μ).val + 1 % (s * m)) / s : ℕ) : ZMod m) := by
  unfold blockOf
  rw [val_add_single]
  simp only [↓reduceIte]
  rw [Nat.mod_mul_right_div_self, ZMod.natCast_mod]

theorem div_succ_cases (v : ℕ) : (v + 1) / s = v / s ∨ (v + 1) / s = v / s + 1 := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have h1 := Nat.div_add_mod v s
  have h2 := Nat.mod_lt v hs
  rcases Nat.lt_or_ge (v % s + 1) s with h | h
  · left
    have : v + 1 = s * (v / s) + (v % s + 1) := by omega
    rw [this, cell_div s h]
  · right
    have : v + 1 = s * (v / s + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [this, Nat.mul_div_cancel_left _ hs]

theorem blockOf_step (x : Balaban.Torus d (s * m)) (μ : Fin d) :
    blockOf d s m (x + Pi.single μ 1) = blockOf d s m x ∨
      blockOf d s m (x + Pi.single μ 1) = blockOf d s m x + Pi.single μ 1 := by
  have hv : ∀ ν, ν = μ → blockOf d s m (x + Pi.single μ 1) ν = blockOf d s m x ν ∨
      blockOf d s m (x + Pi.single μ 1) ν = blockOf d s m x ν + 1 := by
    intro ν hν
    subst hν
    rw [blockOf_add_single_eq]
    have hb : blockOf d s m x ν = (((x ν).val / s : ℕ) : ZMod m) := rfl
    rw [hb]
    by_cases h1 : 1 % (s * m) = 1
    · rw [h1]
      rcases div_succ_cases (s := s) (x ν).val with h | h
      · left; rw [h]
      · right; rw [h]; push_cast; rfl
    · have : 1 % (s * m) = 0 := by
        have := Nat.mod_le 1 (s * m)
        omega
      rw [this, Nat.add_zero]
      left; rfl
  by_cases h : (blockOf d s m (x + Pi.single μ 1)) μ = blockOf d s m x μ
  · left
    funext ν
    by_cases hν : ν = μ
    · subst hν; exact h
    · exact blockOf_add_single_ne x hν
  · right
    funext ν
    by_cases hν : ν = μ
    · subst hν
      rcases hv ν rfl with h' | h'
      · exact absurd h' h
      · simpa using h'
    · rw [blockOf_add_single_ne x hν]
      simp [Pi.single_eq_of_ne hν]

theorem blockOf_surj (c : Balaban.Torus d m) : ∃ x, blockOf d s m x = c := by
  refine ⟨fun ν => (((s * (c ν).val : ℕ)) : ZMod (s * m)), ?_⟩
  funext ν
  apply ZMod.val_injective
  have h : ((s * (c ν).val : ℕ) : ZMod (s * m)).val = s * (c ν).val :=
    ZMod.val_cast_of_lt (by
      have := lt_of_cell s m (ZMod.val_lt (c ν)) (Nat.pos_of_ne_zero (NeZero.ne s))
      simpa using this)
  rw [blockOf_val, h]
  exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne s))

omit [NeZero s] in
theorem ne_one_of_ne {a b : Balaban.Torus d m} (h : a ≠ b) : m ≠ 1 := by
  rintro rfl
  exact h (Subsingleton.elim a b)

/-- The last site of the block `c` in the direction `μ`. -/
def exitSite (c : Balaban.Torus d m) (μ : Fin d) : Balaban.Torus d (s * m) :=
  fun ν => ((s * (c ν).val + (if ν = μ then s - 1 else 0) : ℕ) : ZMod (s * m))

theorem exitSite_val (c : Balaban.Torus d m) (μ ν : Fin d) :
    (exitSite (s := s) c μ ν).val = s * (c ν).val + (if ν = μ then s - 1 else 0) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  unfold exitSite
  refine ZMod.val_cast_of_lt (lt_of_cell s m (ZMod.val_lt (c ν)) ?_)
  split_ifs <;> omega

theorem blockOf_exitSite (c : Balaban.Torus d m) (μ : Fin d) :
    blockOf d s m (exitSite (s := s) c μ) = c := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  funext ν
  apply ZMod.val_injective
  rw [blockOf_val, exitSite_val]
  split_ifs
  · exact cell_div s (by omega)
  · rw [Nat.add_zero]; exact Nat.mul_div_cancel_left _ hs

theorem blockOf_exitSite_step (c : Balaban.Torus d m) (μ : Fin d) (hm : m ≠ 1) :
    blockOf d s m (exitSite (s := s) c μ + Pi.single μ 1) = c + Pi.single μ 1 := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hn : 1 % (s * m) = 1 := by
    apply Nat.mod_eq_of_lt
    have : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have h2 : 2 ≤ m := by omega
    nlinarith
  funext ν
  by_cases hν : ν = μ
  · subst hν
    rw [blockOf_add_single_eq, hn, exitSite_val]
    simp only [↓reduceIte]
    have : s * (c ν).val + (s - 1) + 1 = s * ((c ν).val + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [this, Nat.mul_div_cancel_left _ hs]
    simp
  · rw [blockOf_add_single_ne _ hν, blockOf_exitSite]
    simp [Pi.single_eq_of_ne hν]

theorem val_add_single_of_lt (x : Balaban.Torus d (s * m)) (μ ν : Fin d)
    (h : (x μ).val + 1 < s * m) :
    ((x + (Pi.single μ 1 : Balaban.Torus d (s * m))) ν).val =
      if ν = μ then (x μ).val + 1 else (x ν).val := by
  rw [val_add_single]
  have h1 : 1 % (s * m) = 1 := Nat.mod_eq_of_lt (by omega)
  by_cases hν : ν = μ
  · simp only [hν, ↓reduceIte]
    rw [h1, Nat.mod_eq_of_lt h]
  · simp [hν]

theorem blockOf_add_single_of_div (x : Balaban.Torus d (s * m)) (μ : Fin d)
    (h : (x μ).val + 1 < s * m) (h2 : ((x μ).val + 1) / s = (x μ).val / s) :
    blockOf d s m (x + Pi.single μ 1) = blockOf d s m x := by
  rw [blockOf_eq_iff]
  intro ν
  rw [val_add_single_of_lt x μ ν h]
  by_cases hν : ν = μ
  · subst hν; simpa using h2
  · simp [hν]

/-- The distance between two sites. -/
def vdist (x y : Balaban.Torus d (s * m)) : ℕ :=
  ∑ μ, ((x μ).val - (y μ).val + ((y μ).val - (x μ).val))

theorem vdist_step_lt (x y : Balaban.Torus d (s * m)) (μ : Fin d)
    (hlt : (x μ).val < (y μ).val) :
    vdist (x + (Pi.single μ 1 : Balaban.Torus d (s * m))) y < vdist x y := by
  have hy := ZMod.val_lt (y μ)
  have h : (x μ).val + 1 < s * m := by omega
  unfold vdist
  refine Finset.sum_lt_sum (fun ν _ => ?_) ⟨μ, Finset.mem_univ _, ?_⟩
  · rw [val_add_single_of_lt x μ ν h]
    by_cases hν : ν = μ
    · subst hν; simp only [↓reduceIte]; omega
    · simp [hν]
  · rw [val_add_single_of_lt x μ μ h]
    simp only [↓reduceIte]; omega

omit [NeZero s] [NeZero m] in
theorem vdist_comm (x y : Balaban.Torus d (s * m)) : vdist x y = vdist y x := by
  unfold vdist
  exact Finset.sum_congr rfl (fun μ _ => by omega)

/-- Sites of one block are connected inside any union of blocks containing it. -/
theorem cell_connected (X : Finset (Balaban.Torus d (s * m)))
    (hsat : ∀ x ∈ X, ∀ y, blockOf d s m y = blockOf d s m x → y ∈ X) :
    ∀ (N : ℕ) (x y : Balaban.Torus d (s * m)), vdist x y = N → x ∈ X →
      blockOf d s m x = blockOf d s m y →
      Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧
        ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1) x y := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro x y hN hx hxy
    by_cases hxy' : x = y
    · subst hxy'; exact Relation.ReflTransGen.refl
    obtain ⟨μ, hμ⟩ : ∃ μ, x μ ≠ y μ := by
      by_contra hcon
      push Not at hcon
      exact hxy' (funext hcon)
    have hμv : (x μ).val ≠ (y μ).val := fun h => hμ (ZMod.val_injective _ h)
    have hdiv := (blockOf_eq_iff d s m x y).mp hxy μ
    have hxl := ZMod.val_lt (x μ)
    have hyl := ZMod.val_lt (y μ)
    rcases Nat.lt_or_gt_of_ne hμv with hlt | hgt
    · have h : (x μ).val + 1 < s * m := by omega
      have h2 : ((x μ).val + 1) / s = (x μ).val / s := by
        have a1 : (x μ).val / s ≤ ((x μ).val + 1) / s := Nat.div_le_div_right (by omega)
        have a2 : ((x μ).val + 1) / s ≤ (y μ).val / s := Nat.div_le_div_right (by omega)
        omega
      have hb := blockOf_add_single_of_div x μ h h2
      have hx' : x + Pi.single μ 1 ∈ X := hsat x hx _ hb
      have hlt' := vdist_step_lt x y μ hlt
      have := ih _ (hN ▸ hlt') (x + Pi.single μ 1) y rfl hx' (hb.trans hxy)
      exact Relation.ReflTransGen.head ⟨hx, hx', μ, Or.inl rfl⟩ this
    · have h : (y μ).val + 1 < s * m := by omega
      have h2 : ((y μ).val + 1) / s = (y μ).val / s := by
        have a1 : (y μ).val / s ≤ ((y μ).val + 1) / s := Nat.div_le_div_right (by omega)
        have a2 : ((y μ).val + 1) / s ≤ (x μ).val / s := Nat.div_le_div_right (by omega)
        omega
      have hb := blockOf_add_single_of_div y μ h h2
      have hy : y ∈ X := hsat x hx y hxy.symm
      have hy' : y + Pi.single μ 1 ∈ X := hsat y hy _ hb
      have hlt' := vdist_step_lt y x μ hgt
      have h3 : vdist x (y + (Pi.single μ 1 : Balaban.Torus d (s * m))) < N := by
        rw [vdist_comm x, ← hN, vdist_comm x y]; exact hlt'
      have := ih _ h3 x (y + Pi.single μ 1) rfl hx (hxy.trans hb.symm)
      exact Relation.ReflTransGen.tail this ⟨hy', hy, μ, Or.inr rfl⟩

end Steps

section Iff

variable {d s m}

theorem site_rtg_to_block (Y : Finset (Balaban.Torus d m)) {x y : Balaban.Torus d (s * m)}
    (h : Relation.ReflTransGen (fun a b => a ∈ siteSet d s m Y ∧ b ∈ siteSet d s m Y ∧
      ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1) x y) :
    Relation.ReflTransGen (fun a b => a ∈ Y ∧ b ∈ Y ∧ (blockGraph d m).Adj a b)
      (blockOf d s m x) (blockOf d s m y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hc, μ, hμ⟩ := hbc
    rw [mem_siteSet] at hb hc
    by_cases heq : blockOf d s m c = blockOf d s m b
    · rw [heq]; exact ih
    · refine ih.tail ⟨hb, hc, heq ∘ Eq.symm, μ, ?_⟩
      rcases hμ with hμ | hμ
      · subst hμ
        rcases blockOf_step b μ with h1 | h1
        · exact absurd h1 heq
        · exact Or.inl h1
      · subst hμ
        rcases blockOf_step c μ with h1 | h1
        · exact absurd h1.symm heq
        · exact Or.inr h1

theorem block_rtg_to_site (Y : Finset (Balaban.Torus d m)) {b₁ b₂ : Balaban.Torus d m}
    (h : Relation.ReflTransGen (fun a b => a ∈ Y ∧ b ∈ Y ∧ (blockGraph d m).Adj a b) b₁ b₂)
    (h1 : b₁ ∈ Y) (x y : Balaban.Torus d (s * m))
    (hx : blockOf d s m x = b₁) (hy : blockOf d s m y = b₂) :
    Relation.ReflTransGen (fun a b => a ∈ siteSet d s m Y ∧ b ∈ siteSet d s m Y ∧
      ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1) x y := by
  have hsat : ∀ a ∈ siteSet d s m Y, ∀ z, blockOf d s m z = blockOf d s m a →
      z ∈ siteSet d s m Y := fun a ha z hz => by
    rw [mem_siteSet] at ha ⊢; rw [hz]; exact ha
  subst hx
  induction h generalizing y with
  | refl =>
    have hxX : x ∈ siteSet d s m Y := by rw [mem_siteSet]; exact h1
    exact cell_connected _ hsat _ _ _ rfl hxX hy.symm
  | @tail b c hab hbc ih =>
    obtain ⟨hbY, hcY, hne, μ, hμ⟩ := hbc
    have hxX : x ∈ siteSet d s m Y := by rw [mem_siteSet]; exact h1
    have hm := ne_one_of_ne hne
    rcases hμ with hμ | hμ
    · have hz := blockOf_exitSite (s := s) b μ
      have hw : blockOf d s m (exitSite (s := s) b μ + Pi.single μ 1) = c := by
        rw [blockOf_exitSite_step b μ hm, hμ]
      have h2 := ih (exitSite (s := s) b μ) hz
      have hzX : exitSite (s := s) b μ ∈ siteSet d s m Y := by rw [mem_siteSet, hz]; exact hbY
      have hwX : exitSite (s := s) b μ + Pi.single μ 1 ∈ siteSet d s m Y := by
        rw [mem_siteSet, hw]; exact hcY
      have h3 := cell_connected _ hsat _ _ _ rfl hwX (hw.trans hy.symm)
      exact (h2.tail ⟨hzX, hwX, μ, Or.inl rfl⟩).trans h3
    · have hz := blockOf_exitSite (s := s) c μ
      have hw : blockOf d s m (exitSite (s := s) c μ + Pi.single μ 1) = b := by
        rw [blockOf_exitSite_step c μ (ne_one_of_ne hne.symm), hμ]
      have h2 := ih (exitSite (s := s) c μ + Pi.single μ 1) hw
      have hzX : exitSite (s := s) c μ ∈ siteSet d s m Y := by rw [mem_siteSet, hz]; exact hcY
      have hwX : exitSite (s := s) c μ + Pi.single μ 1 ∈ siteSet d s m Y := by
        rw [mem_siteSet, hw]; exact hbY
      have h3 := cell_connected _ hsat _ _ _ rfl hzX (hz.trans hy.symm)
      exact (h2.tail ⟨hwX, hzX, μ, Or.inr rfl⟩).trans h3

/-- A union of blocks is a frozen polymer iff its set of blocks is a block-torus polymer. -/
theorem isPolymer_siteSet_iff (Y : Finset (Balaban.Torus d m)) :
    Balaban.IsPolymer d (s * m) s (siteSet d s m Y) ↔ IsAnimal (blockGraph d m) Y := by
  have hsat : ∀ a ∈ siteSet d s m Y, ∀ z, blockOf d s m z = blockOf d s m a →
      z ∈ siteSet d s m Y := fun a ha z hz => by
    rw [mem_siteSet] at ha ⊢; rw [hz]; exact ha
  constructor
  · rintro ⟨hne, -, hconn⟩
    rw [isAnimal_iff]
    refine ⟨?_, fun b₁ hb₁ b₂ hb₂ => ?_⟩
    · obtain ⟨x, hx⟩ := hne
      exact ⟨blockOf d s m x, (mem_siteSet d s m).mp hx⟩
    · obtain ⟨x, rfl⟩ := blockOf_surj (s := s) b₁
      obtain ⟨y, rfl⟩ := blockOf_surj (s := s) b₂
      exact site_rtg_to_block Y (hconn x ((mem_siteSet d s m).mpr hb₁) y
        ((mem_siteSet d s m).mpr hb₂))
  · intro hY
    rw [isAnimal_iff] at hY
    refine ⟨?_, ?_, fun x hx y hy => ?_⟩
    · obtain ⟨b, hb⟩ := hY.1
      obtain ⟨x, rfl⟩ := blockOf_surj (s := s) b
      exact ⟨x, (mem_siteSet d s m).mpr hb⟩
    · intro x hx y hxy
      exact hsat x hx y ((blockOf_eq_iff d s m y x).mpr (fun μ => (hxy μ).symm))
    · rw [mem_siteSet] at hx hy
      exact block_rtg_to_site Y (hY.2 _ hx _ hy) hx x y rfl rfl

theorem siteSet_image_blockOf {X : Finset (Balaban.Torus d (s * m))}
    (hsat : ∀ x ∈ X, ∀ y : Balaban.Torus d (s * m), (∀ μ, (x μ).val / s = (y μ).val / s) → y ∈ X) :
    siteSet d s m (X.image (blockOf d s m)) = X := by
  ext y
  rw [mem_siteSet, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact hsat x hx y ((blockOf_eq_iff d s m x y).mp hxy)
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem image_siteSet (Y : Finset (Balaban.Torus d m)) :
    (siteSet d s m Y).image (blockOf d s m) = Y := by
  ext b
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact (mem_siteSet d s m).mp hx
  · intro hb
    obtain ⟨x, rfl⟩ := blockOf_surj (s := s) b
    exact ⟨x, (mem_siteSet d s m).mpr hb, rfl⟩

theorem isAnimal_image_blockOf {X : Finset (Balaban.Torus d (s * m))}
    (hX : Balaban.IsPolymer d (s * m) s X) :
    IsAnimal (blockGraph d m) (X.image (blockOf d s m)) := by
  rw [← isPolymer_siteSet_iff (s := s), siteSet_image_blockOf hX.2.1]
  exact hX

theorem card_div_eq (X : Finset (Balaban.Torus d (s * m)))
    (hsat : ∀ x ∈ X, ∀ y : Balaban.Torus d (s * m), (∀ μ, (x μ).val / s = (y μ).val / s) → y ∈ X) :
    (X.card : ℝ) / (s : ℝ) ^ d = ((X.image (blockOf d s m)).card : ℝ) := by
  have h := card_siteSet d s m (X.image (blockOf d s m))
  rw [siteSet_image_blockOf hsat] at h
  have hs : (s : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne s)
  rw [h]
  push_cast
  field_simp

end Iff

end Balaban.Polymer
