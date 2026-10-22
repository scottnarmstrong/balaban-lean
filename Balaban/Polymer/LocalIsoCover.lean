/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoOps
public import Balaban.Polymer.TwoTorusSY
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the exact transport of the cover

For two generating sets `G`, `H` carried onto each other by the box map (`OmegaIso G H ρ`), the
cover of `G` (`coverOf G`: the centres `cubeIdx G` and the partition of unity `chi G`) goes to that
of `H`: the centre `(j, y0)` goes to `(j, bm y0)`.

* `OmegaIso.mem_cubeIdx_map`, `OmegaIso.cubeIdx_image`, `OmegaIso.cubeEquiv`: the centres;
* `OmegaIso.coverDenom_eq`, `OmegaIso.chi_eq`: the denominator and the partition weights at a site
  of the box;
* `OmegaIso.qset_image`, `OmegaIso.sProd_eq`: the parameter cubes `𝒬(z)` of a centre and the cut
  weights `s_z = ∏_{P ∈ 𝒬(z)} s_P`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Matrix

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ' : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)
local notation "cm" => (Prod.map id bm : ℕ × CTorus d L N₁ m₁ K → ℕ × CTorus d L N₁' m₁ K)

namespace OmegaIso

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'}
  {ρ : ℕ}

/-! ### The centres -/

/-- The base point of a centre lies in the box. -/
theorem base_inBox (hI : OmegaIso G H ρ) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    InBox d ρ ((N₁ * L ^ m₁) * L ^ K) q.2 := by
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := (mem_cubeIdx G).1 hq
  exact hI.boxG _ (G.layer_subset h1 h2 h3)

theorem base_inBox' (hI : OmegaIso G H ρ) {q : ℕ × CTorus d L N₁' m₁ K} (hq : q ∈ cubeIdx H) :
    InBox d ρ ((N₁' * L ^ m₁) * L ^ K) q.2 := by
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := (mem_cubeIdx H).1 hq
  exact hI.boxH _ (H.layer_subset h1 h2 h3)

theorem lt_left (hI : OmegaIso G H ρ) : 2 * ρ + 1 < (N₁ * L ^ m₁) * L ^ K := by
  have := hI.two_lt.1; omega

theorem lt_right (hI : OmegaIso G H ρ) : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ K := by
  have := hI.two_lt.2; omega

/-- **The image of a centre is a centre.** -/
theorem mem_cubeIdx_map (hI : OmegaIso G H ρ) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) : cm q ∈ cubeIdx H := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (mem_cubeIdx G).1 hq
  have hb := hI.base_inBox hq
  refine (mem_cubeIdx H).2 ⟨⟨h1, h2⟩, (hI.layer_iff (inBox_mono (Nat.le_succ ρ) hb) h1 h2).2 h3,
    ?_⟩
  exact aligned_boxMap (pow_dvd_side h2 N₁) (pow_dvd_side h2 N₁') h4

/-- **Every centre of `H` is the image of a centre of `G`.** -/
theorem exists_cubeIdx_of (hI : OmegaIso G H ρ) {q' : ℕ × CTorus d L N₁' m₁ K}
    (hq' : q' ∈ cubeIdx H) : ∃ q ∈ cubeIdx G, cm q = q' := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (mem_cubeIdx H).1 hq'
  have hb := hI.base_inBox' hq'
  have hlt := hI.lt_left
  have hxb : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (bm' q'.2) := inBox_boxMap hlt hb
  have hback : bm (bm' q'.2) = q'.2 := boxMap_boxMap hlt hb
  refine ⟨(q'.1, bm' q'.2), (mem_cubeIdx G).2 ⟨⟨h1, h2⟩, ?_, ?_⟩, ?_⟩
  · refine (hI.layer_iff (inBox_mono (Nat.le_succ ρ) hxb) h1 h2).1 ?_
    rw [hback]; exact h3
  · exact aligned_boxMap (pow_dvd_side h2 N₁') (pow_dvd_side h2 N₁) h4
  · show ((q'.1, bm (bm' q'.2)) : ℕ × CTorus d L N₁' m₁ K) = q'
    rw [hback]

/-- The map of the centres is injective on the centres of `G`. -/
theorem cm_injOn (hI : OmegaIso G H ρ) : Set.InjOn cm (↑(cubeIdx G) : Set _) := by
  intro q hq q₂ hq₂ h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext h1 (boxMap_inj (hm' := hI.lt_right) (hI.base_inBox hq) (hI.base_inBox hq₂) h2)

/-- **The centres of `H` are the images of those of `G`.** -/
theorem cubeIdx_image (hI : OmegaIso G H ρ) : (cubeIdx G).image cm = cubeIdx H := by
  ext q'
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h
    exact hI.mem_cubeIdx_map hq
  · intro h
    obtain ⟨q, hq, rfl⟩ := hI.exists_cubeIdx_of h
    exact Finset.mem_image_of_mem _ hq

/-- **The bijection of the centres.** -/
def cubeEquiv (hI : OmegaIso G H ρ) : cubeIdx G ≃ cubeIdx H :=
  Equiv.ofBijective (fun q => ⟨cm q, hI.mem_cubeIdx_map q.2⟩)
    ⟨fun q q₂ h => Subtype.ext (hI.cm_injOn q.2 q₂.2 (congrArg Subtype.val h)),
      fun q' => by
        obtain ⟨q, hq, he⟩ := hI.exists_cubeIdx_of q'.2
        exact ⟨⟨q, hq⟩, Subtype.ext he⟩⟩

@[simp] theorem coe_cubeEquiv (hI : OmegaIso G H ρ) (q : cubeIdx G) :
    ((hI.cubeEquiv q : cubeIdx H) : ℕ × CTorus d L N₁' m₁ K) = cm q := rfl

/-! ### The partition of unity -/

/-- The cube bump of a centre of the box at a site of the box, on the two tori. -/
theorem cubeBump_eq (hI : OmegaIso G H ρ) {j : ℕ} (hj : j ≤ K) {x y0 : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0) :
    cubeBump m₁ j (bm y0) (bm x) = cubeBump m₁ j y0 x := by
  obtain ⟨-, -, h3, -, -, -⟩ := pow_le_room (L := L) (m₁ := m₁) hj
  have := hI.room; have := hI.room'
  exact cubeBump_boxMap hx hy0 (by omega) (by omega) (by omega) (by omega)

/-- **The denominator of the cover at a site of the box.** -/
theorem coverDenom_eq (hI : OmegaIso G H ρ) {x : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) : coverDenom H (bm x) = coverDenom G x := by
  unfold coverDenom
  rw [← hI.cubeIdx_image, Finset.sum_image hI.cm_injOn]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨⟨-, h2⟩, -, -⟩ := (mem_cubeIdx G).1 hq
  exact hI.cubeBump_eq h2 hx (hI.base_inBox hq)

/-- **The partition weights of a centre at a site of the box.** -/
theorem chi_eq (hI : OmegaIso G H ρ) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    {x : CTorus d L N₁ m₁ K} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    chi H (cm q) (bm x) = chi G q x := by
  unfold chi
  rw [hI.coverDenom_eq hx]
  congr 1
  obtain ⟨⟨-, h2⟩, -, -⟩ := (mem_cubeIdx G).1 hq
  exact hI.cubeBump_eq h2 hx (hI.base_inBox hq)

/-! ### The parameter cubes and the cut weights -/

/-- **The parameter cubes of a centre and of its image** (`𝒬(z)` of the cover of each set). -/
theorem qset_mem_iff (hI : OmegaIso G H ρ) {q P : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    (hP : P ∈ cubeIdx G) :
    P ∈ Qset G q ↔ cm P ∈ Qset H (cm q) := by
  obtain ⟨⟨hj1, hj⟩, -, -⟩ := (mem_cubeIdx G).1 hq
  obtain ⟨⟨hj1', hj'⟩, -, hbP⟩ := (mem_cubeIdx G).1 hP
  obtain ⟨j, y0⟩ := q
  obtain ⟨j', y1⟩ := P
  have hy0 := hI.base_inBox hq
  have hy1 := hI.base_inBox hP
  simp only at hj1 hj hj1' hj' hbP hy0 hy1
  obtain ⟨-, -, h3, h4, h5, -⟩ := pow_le_room (L := L) (m₁ := m₁) hj
  obtain ⟨-, -, h3', -, h5', -⟩ := pow_le_room (L := L) (m₁ := m₁) hj'
  have hR := hI.room; have hR' := hI.room'
  have hLK : L ^ (K + m₁) ≤ L ^ (K + m₁ + 2) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)
  have hjK : L ^ (j' + m₁) ≤ L ^ (K + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)
  set ρ₀ : ℕ := ρ + L ^ (K + m₁) with hρ₀
  have hy0' : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0 := inBox_mono (by omega) hy0
  have hE : 2 * (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 < (N₁ * L ^ m₁) * L ^ K := by
    omega
  have hE' : 2 * (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 < (N₁' * L ^ m₁) * L ^ K := by
    omega
  have hcs : L * cellSide L 0 m₁ j' = L * L ^ (j' + m₁) := by
    unfold cellSide; rw [Nat.add_zero]
  have hpimg : bm '' Pset m₁ ((j', y1) : ℕ × CTorus d L N₁ m₁ K) =
      Pset m₁ ((j', bm y1) : ℕ × CTorus d L N₁' m₁ K) :=
    pset_image (m₀ := 0) (N₁' := N₁') hj' (by rw [hcs]; omega) hy1 hbP
  have hPbox : ∀ y ∈ Pset m₁ ((j', y1) : ℕ × CTorus d L N₁ m₁ K),
      InBox d (ρ + L ^ (j' + m₁)) ((N₁ * L ^ m₁) * L ^ K) y := fun y hy =>
    pset_inBox hj' hbP hy1 (by omega) hy
  have hPmem : ∀ y ∈ Pset m₁ ((j', y1) : ℕ × CTorus d L N₁ m₁ K),
      InBox d (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) ((N₁ * L ^ m₁) * L ^ K) y :=
    fun y hy => inBox_mono (by omega) (hPbox y hy)
  rw [mem_Qset_hat, mem_Qset_hat]
  constructor
  · rintro ⟨-, y, hyP, hyH⟩
    refine ⟨hI.mem_cubeIdx_map hP, bm y, ?_, ?_⟩
    · have : bm y ∈ bm '' Pset m₁ ((j', y1) : ℕ × CTorus d L N₁ m₁ K) := ⟨y, hyP, rfl⟩
      rw [hpimg] at this; exact this
    · exact (mem_hatBox_boxMap_iff hy0' hE hE' (hPmem y hyP)).1 hyH
  · rintro ⟨-, y', hyP', hyH'⟩
    have hP' : y' ∈ bm '' Pset m₁ ((j', y1) : ℕ × CTorus d L N₁ m₁ K) := by
      rw [hpimg]; exact hyP'
    obtain ⟨y, hyP, rfl⟩ := hP'
    exact ⟨hP, y, hyP, (mem_hatBox_boxMap_iff hy0' hE hE' (hPmem y hyP)).2 hyH'⟩

/-- **The parameter cubes of the image of a centre are the images of its parameter cubes.** -/
theorem qset_image (hI : OmegaIso G H ρ) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    Qset H (cm q) = (Qset G q).image cm := by
  ext P'
  constructor
  · intro h
    obtain ⟨P, hP, rfl⟩ := hI.exists_cubeIdx_of (Qset_subset_cubeIdx _ h)
    exact Finset.mem_image_of_mem _ ((hI.qset_mem_iff hq hP).2 h)
  · intro h
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 h
    exact (hI.qset_mem_iff hq (Qset_subset_cubeIdx _ hP)).1 hP

/-- **The cut weights of a centre and of its image**, for parameters corresponding on the
centres. -/
theorem sProd_eq (hI : OmegaIso G H ρ) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hs : ∀ P ∈ cubeIdx G, s' (cm P) = s P) :
    sProd H s' (cm q) = sProd G s q := by
  unfold sProd
  rw [hI.qset_image hq, Finset.prod_image (fun P hP P₂ hP₂ h => hI.cm_injOn
    (Qset_subset_cubeIdx _ hP) (Qset_subset_cubeIdx _ hP₂) h)]
  exact Finset.prod_congr rfl fun P hP => hs P (Qset_subset_cubeIdx _ hP)

end OmegaIso

end Balaban.Polymer.LocalIso
