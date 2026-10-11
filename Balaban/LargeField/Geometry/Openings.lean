module

public import Balaban.LargeField.Geometry.Distance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The cover by `L`-blocks and block openings (Part I, Definition I.2.5, Lemma I.2.6)

For `c ∈ 𝕋_{k+1}`, `lblock L c = Bl(c) = {c + v : v ∈ {0, …, L-1}^d}`. The block openings are
`opening m F = Op_m(F) = ⋃ {Bl(c) : d(Bl(c), F) ≥ m}` and
`openingIn m F Ω = Op_m(F; Ω) = ⋃ {Bl(c) : Bl(c) ⊆ Ω, d(Bl(c), F) ≥ m}`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

variable {d n : ℕ}

/-- `Bl(c) = {c + v : v ∈ {0, …, L-1}^d}`, the `L`-block with corner `c`. -/
def lblock (L : ℕ) (c : Torus d n) : Set (Torus d n) :=
  {y | ∃ v : Fin d → ℕ, (∀ i, v i < L) ∧ y = fun i => c i + (v i : ZMod n)}

/-- `Op_m(F) = ⋃ {Bl(c) : d(Bl(c), F) ≥ m}`. -/
def opening (L m : ℕ) (F : Set (Torus d n)) : Set (Torus d n) :=
  {y | ∃ c, y ∈ lblock L c ∧ (m : ℕ∞) ≤ setDist (lblock L c) F}

/-- `Op_m(F; Ω) = ⋃ {Bl(c) : Bl(c) ⊆ Ω, d(Bl(c), F) ≥ m}`. -/
def openingIn (L m : ℕ) (F Ω : Set (Torus d n)) : Set (Torus d n) :=
  {y | ∃ c, y ∈ lblock L c ∧ lblock L c ⊆ Ω ∧ (m : ℕ∞) ≤ setDist (lblock L c) F}

theorem le_setDist_iff {X Y : Set (Torus d n)} {m : ℕ} :
    (m : ℕ∞) ≤ setDist X Y ↔ ∀ x ∈ X, ∀ y ∈ Y, m ≤ supDist x y := by
  unfold setDist
  simp only [le_iInf_iff]
  exact_mod_cast Iff.rfl

theorem setDist_mono {X X' Y Y' : Set (Torus d n)} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    setDist X' Y' ≤ setDist X Y :=
  iInf₂_mono' fun x hx => ⟨x, hX hx, iInf₂_mono' fun y hy => ⟨y, hY hy, le_rfl⟩⟩

section Blocks

variable {L : ℕ}

theorem mem_lblock_self (hL : 0 < L) (x : Torus d n) : x ∈ lblock L x :=
  ⟨fun _ => 0, fun _ => hL, by funext i; simp⟩

/-- **Lemma I.2.6 (a)**: any two points of a block are within `L - 1`. -/
theorem supDist_le_of_mem_lblock [NeZero n] {c x y : Torus d n} (hx : x ∈ lblock L c) (hy : y ∈ lblock L c) :
    supDist x y ≤ L - 1 := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  refine supDist_le_iff.mpr fun i => (cycNorm_le_iff _ _).mpr ⟨(v i : ℤ) - w i, ?_, ?_⟩
  · have h1 := hv i
    have h2 := hw i
    rw [abs_le]
    constructor <;> push_cast [Nat.cast_sub (by omega : 1 ≤ L)] <;> omega
  · push_cast; ring

variable {m : ℕ}

/-- **Lemma I.2.6 (b)**: `Op_m(F) ∩ F^{∼(m-1)} = ∅`. -/
theorem opening_disjoint_nbhd (hm : 1 ≤ m) (F : Set (Torus d n)) :
    ∀ y ∈ opening L m F, y ∉ nbhd (m - 1) F := by
  rintro y ⟨c, hy, hc⟩ hn
  obtain ⟨f, hf, hd⟩ := mem_nbhd.mp hn
  have := le_setDist_iff.mp hc y hy f hf
  omega

/-- **Lemma I.2.6 (b)**: `Op_m(F)ᶜ ⊆ F^{∼(m+L-2)}`. -/
theorem opening_compl_subset [NeZero n] (hL : 0 < L) (hm : 1 ≤ m) (F : Set (Torus d n)) :
    (opening L m F)ᶜ ⊆ nbhd (m + L - 2) F := by
  intro x hx
  by_contra hxn
  apply hx
  refine ⟨x, mem_lblock_self hL x, le_setDist_iff.mpr fun y hy f hf => ?_⟩
  have h1 := supDist_le_of_mem_lblock (mem_lblock_self hL x) hy
  have h2 : ¬ supDist x f ≤ m + L - 2 := fun h => hxn (mem_nbhd.mpr ⟨f, hf, h⟩)
  have h3 := supDist_triangle x y f
  omega

/-- **Lemma I.2.6 (c)**: `Op_m(F; Ω) ⊆ Ω ∖ F^{∼(m-1)}`. -/
theorem openingIn_subset (hm : 1 ≤ m) (F Ω : Set (Torus d n)) :
    openingIn L m F Ω ⊆ Ω \ nbhd (m - 1) F := by
  rintro y ⟨c, hy, hΩ, hc⟩
  refine ⟨hΩ hy, fun hn => ?_⟩
  obtain ⟨f, hf, hd⟩ := mem_nbhd.mp hn
  have := le_setDist_iff.mp hc y hy f hf
  omega

/-- **Lemma I.2.6 (c)**: if `Ω` is a union of `L`-blocks, `Ω ∖ Op_m(F; Ω) ⊆ F^{∼(m+L-2)}`. -/
theorem openingIn_diff_subset [NeZero n] (hL : 0 < L) (hm : 1 ≤ m) (F Ω : Set (Torus d n))
    (hΩ : ∀ x ∈ Ω, ∃ c, x ∈ lblock L c ∧ lblock L c ⊆ Ω) :
    Ω \ openingIn L m F Ω ⊆ nbhd (m + L - 2) F := by
  rintro x ⟨hxΩ, hx⟩
  by_contra hxn
  obtain ⟨c, hxc, hcΩ⟩ := hΩ x hxΩ
  apply hx
  refine ⟨c, hxc, hcΩ, le_setDist_iff.mpr fun y hy f hf => ?_⟩
  have h1 := supDist_le_of_mem_lblock hxc hy
  have h2 : ¬ supDist x f ≤ m + L - 2 := fun h => hxn (mem_nbhd.mpr ⟨f, hf, h⟩)
  have h3 := supDist_triangle x y f
  omega

/-- **Lemma I.2.6 (d)**: `Op_m(F)` is decreasing in `F`. -/
theorem opening_anti {F F' : Set (Torus d n)} (h : F ⊆ F') :
    opening L m F' ⊆ opening L m F := by
  rintro y ⟨c, hy, hc⟩
  exact ⟨c, hy, hc.trans (setDist_mono subset_rfl h)⟩

/-- **Lemma I.2.6 (d)**: `Op_m(F; Ω)` is decreasing in `F`. -/
theorem openingIn_anti {F F' : Set (Torus d n)} (Ω : Set (Torus d n)) (h : F ⊆ F') :
    openingIn L m F' Ω ⊆ openingIn L m F Ω := by
  rintro y ⟨c, hy, hΩ, hc⟩
  exact ⟨c, hy, hΩ, hc.trans (setDist_mono subset_rfl h)⟩

/-- **Lemma I.2.6 (d)**: `Op_m(F; Ω)` is increasing in `Ω`. -/
theorem openingIn_mono (F : Set (Torus d n)) {Ω Ω' : Set (Torus d n)} (h : Ω ⊆ Ω') :
    openingIn L m F Ω ⊆ openingIn L m F Ω' := by
  rintro y ⟨c, hy, hΩ, hc⟩
  exact ⟨c, hy, hΩ.trans h, hc⟩

theorem openingIn_subset_opening (F Ω : Set (Torus d n)) :
    openingIn L m F Ω ⊆ opening L m F := by
  rintro y ⟨c, hy, _, hc⟩
  exact ⟨c, hy, hc⟩

end Blocks

end Balaban.LargeField
