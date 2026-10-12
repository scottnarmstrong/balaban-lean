module

public import Balaban.LargeField.Region.Seeds
import Mathlib.Tactic.Linarith

/-!
# Locality of the region calculus (Part I, Lemma I.3.9)

Let `Z'` be a component of `Z^pre_{k+1}` (width `ω = ω_{k+1}`). The *local step* of `Z'`
(`RegionStep.restrict`) keeps the components `Z` of `Z_k` with `Z^↑ ⊆ Z'` (the cubes `z ∈ Z_k` with
`z^↑ ∈ Z'`; a coarsened component lies in one component, Lemma I.3.7) and `P ∩ Z'`, `Q ∩ Z'`,
`R ∩ Z'`, `S ∩ Z'`. Then:

(a) the constraints (R4)-(R6) hold for the local data (a field of the structure);
(b) `Ω'ᶜ ∩ Z' = Ω'ᶜ(loc)`, `Ωᶜ ∩ Z' = Ωᶜ(loc)`, `Ω''ᶜ ∩ Z' = Ω''ᶜ(loc)`, `Z^{(0)} ∩ Z' = Z^{(0)}(loc)`;
(c) `Z' = Z^pre(loc)` and `Z'` is the only component of it;
(d) the complements are the disjoint unions of the local complements over the components.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-! ### Monotonicity of the set functions -/

namespace Region

variable {d n0 n1 : ℕ}

theorem Uprime_mono {L r : ℕ} {Z Z' : Set (Torus d n0)} (h : Z' ⊆ Z) :
    Uprime L n1 r Z' ⊆ Uprime L n1 r Z :=
  Set.image_mono (nbhd_mono le_rfl h)

theorem OmegaPrime_anti {L ρ : ℕ} {U U' : Set (Torus d n1)} (h : U ⊆ U') :
    OmegaPrime L ρ U' ⊆ OmegaPrime L ρ U :=
  opening_anti (nbhd_mono le_rfl h)

theorem Omega_anti_mono {L : ℕ} {P P' Ω Ω' : Set (Torus d n1)} (hP : P' ⊆ P) (hΩ : Ω ⊆ Ω') :
    Omega L P Ω ⊆ Omega L P' Ω' :=
  (openingIn_anti Ω (nbhd_mono le_rfl hP)).trans (openingIn_mono _ hΩ)

theorem FDD_mono {ρ : ℕ} {Q Q' R R' : Set (Torus d n1)} (hQ : Q' ⊆ Q) (hR : R' ⊆ R) :
    FDD ρ Q' R' ⊆ FDD ρ Q R :=
  Set.union_subset_union (nbhd_mono le_rfl hQ) (nbhd_mono le_rfl hR)

theorem OmegaDD_anti_mono {L : ℕ} {F F' Ω Ω' : Set (Torus d n1)} (hF : F' ⊆ F) (hΩ : Ω ⊆ Ω') :
    OmegaDD L F Ω ⊆ OmegaDD L F' Ω' :=
  (openingIn_anti Ω hF).trans (openingIn_mono _ hΩ)

theorem FZ_anti_mono {Ω Ω' S S' : Set (Torus d n1)} (hΩ : Ω ⊆ Ω') (hS : S' ⊆ S) :
    FZ Ω' S' ⊆ FZ Ω S :=
  Set.union_subset_union (nbhd_mono le_rfl (Set.compl_subset_compl.mpr hΩ)) (nbhd_mono le_rfl hS)

theorem Z0_mono {L ρ2 : ℕ} {F F' : Set (Torus d n1)} (h : F' ⊆ F) : Z0 L ρ2 F' ⊆ Z0 L ρ2 F :=
  Set.compl_subset_compl.mpr (opening_anti h)

end Region

/-! ### Generic local lemmas for openings -/

section Opening

variable {d n : ℕ} [NeZero n]

/-- If `F_l` contains every point of `F` within `L - 1 + (m - 1)` of `x`, and `x ∉ Op_m(F)`, then
`x ∉ Op_m(F_l)`. -/
theorem not_mem_opening_local {L m : ℕ} {F Fl : Set (Torus d n)} {x : Torus d n}
    (hF : ∀ f ∈ F, supDist x f ≤ (L - 1) + (m - 1) → f ∈ Fl) (hnot : x ∉ opening L m F) :
    x ∉ opening L m Fl := by
  rintro ⟨c, hxc, hc⟩
  apply hnot
  refine ⟨c, hxc, ?_⟩
  by_contra hlt
  rw [le_setDist_iff] at hlt
  push Not at hlt
  obtain ⟨b, hb, f, hf, hbf⟩ := hlt
  have h1 := supDist_le_of_mem_lblock hxc hb
  have h2 := supDist_triangle x b f
  have hfl := hF f hf (by omega)
  have := le_setDist_iff.mp hc b hb f hfl
  omega

/-- The same for constrained openings with `m = 1`. -/
theorem not_mem_openingIn_local {L : ℕ} {G Gl Θ Θl : Set (Torus d n)} {x : Torus d n}
    (hΘ : ∀ y, supDist x y ≤ L - 1 → y ∉ Θ → y ∉ Θl)
    (hG : ∀ g ∈ G, supDist x g ≤ L - 1 → g ∈ Gl) (hnot : x ∉ openingIn L 1 G Θ) :
    x ∉ openingIn L 1 Gl Θl := by
  rintro ⟨c, hxc, hcΘl, hc⟩
  apply hnot
  have hcΘ : lblock L c ⊆ Θ := by
    intro y hy
    by_contra hyΘ
    exact hΘ y (supDist_le_of_mem_lblock hxc hy) hyΘ (hcΘl hy)
  refine ⟨c, hxc, hcΘ, ?_⟩
  by_contra hlt
  rw [le_setDist_iff] at hlt
  push Not at hlt
  obtain ⟨b, hb, g, hg, hbg⟩ := hlt
  have hbg0 : b = g := supDist_eq_zero.mp (by omega)
  subst hbg0
  have hgl := hG b hg (supDist_le_of_mem_lblock hxc hb)
  have := le_setDist_iff.mp hc b hb b hgl
  rw [supDist_self] at this
  omega

end Opening

/-! ### Components: generic facts -/

section CompsGeneric

variable {d n : ℕ} [NeZero n] {ω : ℕ}

theorem finOf_coe_finset (X : Finset (Torus d n)) : finOf (X : Set (Torus d n)) = X := by
  ext; simp

/-- A component `Y` of `X` is a single component of itself. -/
theorem comp_mem_comps_self {X Y : Finset (Torus d n)} (hY : Y ∈ comps ω X) : Y ∈ comps ω Y := by
  obtain ⟨y0, hy0⟩ := comp_nonempty hY
  refine mem_comps_iff.mpr ⟨y0, hy0, ?_⟩
  ext z
  rw [mem_linkClass]
  constructor
  · intro hz
    have h := (mem_comp_iff hY hy0).mp hz
    have hY' : Y ∈ comps ω (finOf (X : Set (Torus d n))) := by rwa [finOf_coe_finset]
    obtain ⟨-, hl⟩ := linked_inter_comp (A := (X : Set (Torus d n))) (Xc := (X : Set (Torus d n)))
      subset_rfl hY' hy0 h.2
    exact ⟨hz, hl.mono Set.inter_subset_right⟩
  · exact fun h => h.1

/-- Distinct components are disjoint. -/
theorem comps_disjoint {X Y Y' : Finset (Torus d n)} (hY : Y ∈ comps ω X) (hY' : Y' ∈ comps ω X)
    (hne : Y ≠ Y') : Disjoint (Y : Set (Torus d n)) (Y' : Set (Torus d n)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact hne (comp_eq_of_mem hY hY' hx hx')

/-- If `A ⊆ X` meets each component `Z'` of `X` in `A_l(Z')`, then `A = ⋃ A_l`. -/
theorem eq_iUnion_of_inter {X A : Set (Torus d n)} {Al : Finset (Torus d n) → Set (Torus d n)}
    (hA : A ⊆ X) (h : ∀ Z' ∈ comps ω (finOf X), A ∩ (Z' : Set (Torus d n)) = Al Z') :
    A = ⋃ Z' ∈ comps ω (finOf X), Al Z' := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro hx
    obtain ⟨Z', hZ', hxZ⟩ := mem_comp_self (ω := ω) (mem_finOf.mpr (hA hx))
    exact ⟨Z', hZ', by rw [← h Z' hZ']; exact ⟨hx, hxZ⟩⟩
  · rintro ⟨Z', hZ', hx⟩
    rw [← h Z' hZ'] at hx
    exact hx.1

end CompsGeneric

/-! ### Sub-steps and the local step -/

namespace RegionStep

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ}
  (st : RegionStep d L n0 n1 Rprev Rk)

/-- A step with smaller data (`Z' ⊆ Z`, `P' ⊆ P`, ...); the constraints (R4)-(R6) persist by
monotonicity (the proof of Lemma I.3.9 (a)). -/
def sub (Z' : Set (Torus d n0)) (P' Q' R' S' : Set (Torus d n1)) (hZ : Z' ⊆ st.Z)
    (hP : P' ⊆ st.P) (hQ : Q' ⊆ st.Q) (hR : R' ⊆ st.R) (hS : S' ⊆ st.S) :
    RegionStep d L n0 n1 Rprev Rk where
  Z := Z'
  P := P'
  Q := Q'
  R := R'
  S := S'
  P_sub := hP.trans (st.P_sub.trans (Region.OmegaPrime_anti (Region.Uprime_mono hZ)))
  Q_sub := hQ.trans (st.Q_sub.trans (nbhd_mono le_rfl
    (Region.Omega_anti_mono hP (Region.OmegaPrime_anti (Region.Uprime_mono hZ)))))
  R_sub := hR.trans (st.R_sub.trans
    (Region.Omega_anti_mono hP (Region.OmegaPrime_anti (Region.Uprime_mono hZ))))
  S_sub := hS.trans (st.S_sub.trans (nbhdNeg_mono (Region.OmegaDD_anti_mono
    (Region.FDD_mono hQ hR)
    (Region.Omega_anti_mono hP (Region.OmegaPrime_anti (Region.Uprime_mono hZ))))))

variable {st}
variable {Z' : Set (Torus d n0)} {P' Q' R' S' : Set (Torus d n1)} {hZ : Z' ⊆ st.Z}
  {hP : P' ⊆ st.P} {hQ : Q' ⊆ st.Q} {hR : R' ⊆ st.R} {hS : S' ⊆ st.S}

theorem sub_Uprime_subset : (st.sub Z' P' Q' R' S' hZ hP hQ hR hS).Uprime ⊆ st.Uprime :=
  Region.Uprime_mono hZ

theorem sub_OmegaPrime_supset : st.OmegaPrime ⊆ (st.sub Z' P' Q' R' S' hZ hP hQ hR hS).OmegaPrime :=
  Region.OmegaPrime_anti (Region.Uprime_mono hZ)

theorem sub_Omega_supset : st.Omega ⊆ (st.sub Z' P' Q' R' S' hZ hP hQ hR hS).Omega :=
  Region.Omega_anti_mono hP sub_OmegaPrime_supset

theorem sub_OmegaDD_supset : st.OmegaDD ⊆ (st.sub Z' P' Q' R' S' hZ hP hQ hR hS).OmegaDD :=
  Region.OmegaDD_anti_mono (Region.FDD_mono hQ hR) sub_Omega_supset

theorem sub_FZ_subset : (st.sub Z' P' Q' R' S' hZ hP hQ hR hS).FZ ⊆ st.FZ :=
  Region.FZ_anti_mono sub_OmegaDD_supset hS

theorem sub_Z0_subset : (st.sub Z' P' Q' R' S' hZ hP hQ hR hS).Z0 ⊆ st.Z0 :=
  Region.Z0_mono sub_FZ_subset

variable (st)

/-- The local step of a set `Zp ⊆ 𝕋_{k+1}` (a component of `Z^pre_{k+1}`): the cubes `z ∈ Z_k` with
`z^↑ ∈ Zp` and the new cubes in `Zp`. -/
def restrict (Zp : Set (Torus d n1)) : RegionStep d L n0 n1 Rprev Rk :=
  st.sub {z | z ∈ st.Z ∧ blockMap L n1 z ∈ Zp} (st.P ∩ Zp) (st.Q ∩ Zp) (st.R ∩ Zp) (st.S ∩ Zp)
    (fun _ h => h.1) Set.inter_subset_left Set.inter_subset_left Set.inter_subset_left
    Set.inter_subset_left

variable {st}

theorem restrict_Uprime_subset (Zp : Set (Torus d n1)) : (st.restrict Zp).Uprime ⊆ st.Uprime :=
  sub_Uprime_subset

theorem restrict_OmegaPrime_supset (Zp : Set (Torus d n1)) :
    st.OmegaPrime ⊆ (st.restrict Zp).OmegaPrime := sub_OmegaPrime_supset

theorem restrict_Omega_supset (Zp : Set (Torus d n1)) : st.Omega ⊆ (st.restrict Zp).Omega :=
  sub_Omega_supset

theorem restrict_OmegaDD_supset (Zp : Set (Torus d n1)) :
    st.OmegaDD ⊆ (st.restrict Zp).OmegaDD := sub_OmegaDD_supset

theorem restrict_Z0_subset (Zp : Set (Torus d n1)) : (st.restrict Zp).Z0 ⊆ st.Z0 :=
  sub_Z0_subset

theorem restrict_newCubes_subset (Zp : Set (Torus d n1)) : (st.restrict Zp).newCubes ⊆ Zp := by
  rintro x (((hx | hx) | hx) | hx) <;> exact hx.2

/-! ### Lemma I.3.9 (b): global complements near a component are local -/

section Loc

variable {ω r : ℕ} {Zp : Set (Torus d n1)}
  (hn : n0 = L * n1) (rad : StepRadii L ω r Rprev Rk)
  (hW : ∀ x ∈ Zp, ∀ y ∈ st.Z0, supDist x y < ω → y ∈ Zp)

include hn rad hW

theorem mem_restrict_Uprime {u : Torus d n1} (hu : u ∈ st.Uprime) (huZ : u ∈ Zp) :
    u ∈ (st.restrict Zp).Uprime := by
  obtain ⟨v, hv, rfl⟩ := hu
  obtain ⟨z, hz, hvz⟩ := mem_nbhd.mp hv
  have hzU : blockMap L n1 z ∈ st.Z0 := st.Uprime_subset_Z0 (st.blockMap_Z_subset_Uprime hz)
  have hd : supDist (blockMap L n1 v) (blockMap L n1 z) < ω := by
    have h1 := supDist_blockMap_le hn v z
    have h2 : (supDist v z + L - 1) / L ≤ ⌊Rprev⌋₊ + 1 := by
      apply Nat.div_le_of_le_mul
      have : ⌊Rprev⌋₊ ≤ L * ⌊Rprev⌋₊ := Nat.le_mul_of_pos_left _ (by have := rad.L_two; omega)
      rw [Nat.mul_succ]
      omega
    have := rad.omega_rhoPrev
    omega
  have hzZp := hW _ huZ _ hzU hd
  exact ⟨v, mem_nbhd.mpr ⟨z, ⟨hz, hzZp⟩, hvz⟩, rfl⟩

theorem not_mem_OmegaPrime_restrict {x : Torus d n1} (hx : x ∈ Zp) (hnot : x ∉ st.OmegaPrime) :
    x ∉ (st.restrict Zp).OmegaPrime := by
  refine not_mem_opening_local (fun f hf hd => ?_) hnot
  obtain ⟨u, hu, hfu⟩ := mem_nbhd.mp hf
  have huZ := st.Uprime_subset_Z0 hu
  have := supDist_triangle x f u
  have := rad.omega_rho
  have huZp := hW x hx u huZ (by omega)
  exact mem_nbhd.mpr ⟨u, mem_restrict_Uprime hn rad hW hu huZp, hfu⟩

theorem not_mem_Omega_restrict {x : Torus d n1} (hx : x ∈ Zp) (hnot : x ∉ st.Omega) :
    x ∉ (st.restrict Zp).Omega := by
  have := rad.omega_rho
  have := rad.L_two
  refine not_mem_openingIn_local (fun y hd hy => ?_) (fun g hg hd => ?_) hnot
  · have hyZ := st.OmegaPrime_compl_subset_Z0 hy
    exact not_mem_OmegaPrime_restrict hn rad hW (hW x hx y hyZ (by omega)) hy
  · obtain ⟨p, hp, hgp⟩ := mem_nbhd.mp hg
    have hpN : p ∈ st.newCubes := Or.inl (Or.inl (Or.inl hp))
    have := supDist_triangle x g p
    have hpZp := hW x hx p (st.newCubes_subset_Z0 hpN) (by omega)
    exact mem_nbhd.mpr ⟨p, ⟨hp, hpZp⟩, hgp⟩

theorem not_mem_OmegaDD_restrict {x : Torus d n1} (hx : x ∈ Zp) (hnot : x ∉ st.OmegaDD) :
    x ∉ (st.restrict Zp).OmegaDD := by
  have := rad.omega_rho
  have := rad.L_two
  refine not_mem_openingIn_local (fun y hd hy => ?_) (fun g hg hd => ?_) hnot
  · have hyZ := st.Omega_compl_subset_Z0 hy
    exact not_mem_Omega_restrict hn rad hW (hW x hx y hyZ (by omega)) hy
  · rcases hg with hg | hg
    · obtain ⟨q, hq, hgq⟩ := mem_nbhd.mp hg
      have hqN : q ∈ st.newCubes := Or.inl (Or.inl (Or.inr hq))
      have := supDist_triangle x g q
      have hqZp := hW x hx q (st.newCubes_subset_Z0 hqN) (by omega)
      exact Or.inl (mem_nbhd.mpr ⟨q, ⟨hq, hqZp⟩, hgq⟩)
    · obtain ⟨q, hq, hgq⟩ := mem_nbhd.mp hg
      have hqN : q ∈ st.newCubes := Or.inl (Or.inr hq)
      have := supDist_triangle x g q
      have hqZp := hW x hx q (st.newCubes_subset_Z0 hqN) (by omega)
      exact Or.inr (mem_nbhd.mpr ⟨q, ⟨hq, hqZp⟩, hgq⟩)

theorem mem_restrict_Z0 {x : Torus d n1} (hx : x ∈ Zp) (hz : x ∈ st.Z0) :
    x ∈ (st.restrict Zp).Z0 := by
  have := rad.omega_rho
  have := rad.rho2_le'
  have := rad.L_two
  refine not_mem_opening_local (fun f hf hd => ?_) hz
  rcases hf with hf | hf
  · obtain ⟨g, hg, hfg⟩ := mem_nbhd.mp hf
    have hgZ := st.OmegaDD_compl_subset_Z0 hg
    have := supDist_triangle x f g
    have hgZp := hW x hx g hgZ (by omega)
    have hgl : g ∉ (st.restrict Zp).OmegaDD := not_mem_OmegaDD_restrict hn rad hW hgZp hg
    exact Or.inl (mem_nbhd.mpr ⟨g, hgl, hfg⟩)
  · obtain ⟨s, hs, hfs⟩ := mem_nbhd.mp hf
    have hsZ := st.FZ_subset_Z0 (st.S_subset_FZ hs)
    have := supDist_triangle x f s
    have hsZp := hW x hx s hsZ (by omega)
    exact Or.inr (mem_nbhd.mpr ⟨s, ⟨hs, hsZp⟩, hfs⟩)

end Loc

/-! ### Lemma I.3.9: the local step of a component -/

section Comp

variable {ω r : ℕ} (crit : Option ℕ) {Z' : Finset (Torus d n1)}
  (hn : n0 = L * n1) (rad : StepRadii L ω r Rprev Rk)
  (hZ' : Z' ∈ comps ω (finOf (st.Zpre ω crit)))

theorem comp_W (hZ' : Z' ∈ comps ω (finOf (st.Zpre ω crit))) :
    ∀ x ∈ (Z' : Set (Torus d n1)), ∀ y ∈ st.Z0, supDist x y < ω → y ∈ (Z' : Set (Torus d n1)) :=
  fun _ hx _ hy h => mem_comp_of_close hZ' hx (mem_finOf.mpr (st.Z0_subset_Zpre ω crit hy)) h

include hn rad hZ'

/-- The complement sets of the local step lie in the component. -/
theorem restrict_Z0_subset_comp :
    (st.restrict (Z' : Set (Torus d n1))).Z0 ⊆ (Z' : Set (Torus d n1)) := by
  intro x hx
  have hxZ : x ∈ st.Z0 := st.restrict_Z0_subset _ hx
  have hxP : x ∈ finOf (st.Zpre ω crit) := mem_finOf.mpr (st.Z0_subset_Zpre ω crit hxZ)
  have key : ∀ y ∈ (Z' : Set (Torus d n1)), Linked ω (st.restrict (Z' : Set _)).Z0 x y →
      x ∈ Z' := by
    intro y hy hl
    have hl' : Linked ω ((finOf (st.Zpre ω crit) : Finset (Torus d n1)) : Set (Torus d n1)) y x := by
      rw [coe_finOf]
      exact hl.symm.mono ((st.restrict_Z0_subset _).trans (st.Z0_subset_Zpre ω crit))
    exact mem_comp_of_linked hZ' hy hxP hl'
  rcases (st.restrict (Z' : Set (Torus d n1))).attribution (ωk := 0) rad hn hx with
    ⟨Y, hY, _, ⟨z, hz, rfl⟩, -, hl⟩ | ⟨q, hq, -, hl⟩
  · have hzY : z ∈ (st.restrict (Z' : Set _)).Z :=
      mem_finOf.mp (comp_subset hY hz)
    exact key _ hzY.2 hl
  · exact key q (st.restrict_newCubes_subset _ hq) hl

/-- **Lemma I.3.9 (b)**, `Ω'`: `Ω'ᶜ ∩ Z' = Ω'ᶜ(loc)`. -/
theorem OmegaPrime_compl_inter_comp :
    st.OmegaPrimeᶜ ∩ (Z' : Set (Torus d n1)) = (st.restrict (Z' : Set (Torus d n1))).OmegaPrimeᶜ := by
  have hW := comp_W crit hZ'
  ext x
  constructor
  · rintro ⟨hxO, hxZ⟩
    exact not_mem_OmegaPrime_restrict hn rad hW hxZ hxO
  · intro hx
    exact ⟨fun h => hx (st.restrict_OmegaPrime_supset _ h),
      restrict_Z0_subset_comp crit hn rad hZ' (RegionStep.OmegaPrime_compl_subset_Z0 _ hx)⟩

/-- **Lemma I.3.9 (b)**, `Ω`: `Ωᶜ ∩ Z' = Ωᶜ(loc)`. -/
theorem Omega_compl_inter_comp :
    st.Omegaᶜ ∩ (Z' : Set (Torus d n1)) = (st.restrict (Z' : Set (Torus d n1))).Omegaᶜ := by
  have hW := comp_W crit hZ'
  ext x
  constructor
  · rintro ⟨hxO, hxZ⟩
    exact not_mem_Omega_restrict hn rad hW hxZ hxO
  · intro hx
    exact ⟨fun h => hx (st.restrict_Omega_supset _ h),
      restrict_Z0_subset_comp crit hn rad hZ' (RegionStep.Omega_compl_subset_Z0 _ hx)⟩

/-- **Lemma I.3.9 (b)**, `Ω''`: `Ω''ᶜ ∩ Z' = Ω''ᶜ(loc)`. -/
theorem OmegaDD_compl_inter_comp :
    st.OmegaDDᶜ ∩ (Z' : Set (Torus d n1)) = (st.restrict (Z' : Set (Torus d n1))).OmegaDDᶜ := by
  have hW := comp_W crit hZ'
  ext x
  constructor
  · rintro ⟨hxO, hxZ⟩
    exact not_mem_OmegaDD_restrict hn rad hW hxZ hxO
  · intro hx
    exact ⟨fun h => hx (st.restrict_OmegaDD_supset _ h),
      restrict_Z0_subset_comp crit hn rad hZ' (RegionStep.OmegaDD_compl_subset_Z0 _ hx)⟩

/-- **Lemma I.3.9 (b)**, `Z^{(0)}`: `Z^{(0)} ∩ Z' = Z^{(0)}(loc)`. -/
theorem Z0_inter_comp :
    st.Z0 ∩ (Z' : Set (Torus d n1)) = (st.restrict (Z' : Set (Torus d n1))).Z0 := by
  have hW := comp_W crit hZ'
  ext x
  constructor
  · rintro ⟨hxO, hxZ⟩
    exact mem_restrict_Z0 hn rad hW hxZ hxO
  · intro hx
    exact ⟨st.restrict_Z0_subset _ hx, restrict_Z0_subset_comp crit hn rad hZ' hx⟩

/-- **Lemma I.3.9 (c)**: `Z' = Z^pre(loc)`. -/
theorem restrict_Zpre (hω2 : 2 ≤ ω) :
    (st.restrict (Z' : Set (Torus d n1))).Zpre ω crit = (Z' : Set (Torus d n1)) := by
  have hZ0 := Z0_inter_comp crit hn rad hZ'
  cases crit with
  | none =>
    show (st.restrict (Z' : Set (Torus d n1))).Z0 = _
    rw [← hZ0]
    have : (Z' : Set (Torus d n1)) ⊆ st.Z0 := fun x hx => mem_finOf.mp (comp_subset hZ' hx)
    exact Set.inter_eq_right.mpr this
  | some b =>
    show hullClosure ω b (st.restrict (Z' : Set (Torus d n1))).Z0 = _
    rw [← hZ0]
    exact hullClosure_inter_comp hω2 st.Z0 hZ'

/-- **Lemma I.3.9 (c)**: the local result is one component. -/
theorem restrict_Zpre_comp (hω2 : 2 ≤ ω) :
    Z' ∈ comps ω (finOf ((st.restrict (Z' : Set (Torus d n1))).Zpre ω crit)) := by
  rw [restrict_Zpre crit hn rad hZ' hω2, finOf_coe_finset]
  exact comp_mem_comps_self hZ'

end Comp

/-! ### Lemma I.3.9 (d) -/

section Decomp

variable {ω r : ℕ} (crit : Option ℕ) (hn : n0 = L * n1) (rad : StepRadii L ω r Rprev Rk)

include hn rad

/-- **Lemma I.3.9 (d)**: `Ω'ᶜ` is the union of the local complements over the components of
`Z^pre`. -/
theorem OmegaPrime_compl_eq_iUnion :
    st.OmegaPrimeᶜ = ⋃ Y ∈ comps ω (finOf (st.Zpre ω crit)),
      (st.restrict (Y : Set (Torus d n1))).OmegaPrimeᶜ :=
  eq_iUnion_of_inter (fun _ hx => st.Z0_subset_Zpre ω crit (st.OmegaPrime_compl_subset_Z0 hx))
    (fun _ hY => OmegaPrime_compl_inter_comp crit hn rad hY)

theorem Omega_compl_eq_iUnion :
    st.Omegaᶜ = ⋃ Y ∈ comps ω (finOf (st.Zpre ω crit)),
      (st.restrict (Y : Set (Torus d n1))).Omegaᶜ :=
  eq_iUnion_of_inter (fun _ hx => st.Z0_subset_Zpre ω crit (st.Omega_compl_subset_Z0 hx))
    (fun _ hY => Omega_compl_inter_comp crit hn rad hY)

theorem OmegaDD_compl_eq_iUnion :
    st.OmegaDDᶜ = ⋃ Y ∈ comps ω (finOf (st.Zpre ω crit)),
      (st.restrict (Y : Set (Torus d n1))).OmegaDDᶜ :=
  eq_iUnion_of_inter (fun _ hx => st.Z0_subset_Zpre ω crit (st.OmegaDD_compl_subset_Z0 hx))
    (fun _ hY => OmegaDD_compl_inter_comp crit hn rad hY)

theorem Z0_eq_iUnion :
    st.Z0 = ⋃ Y ∈ comps ω (finOf (st.Zpre ω crit)), (st.restrict (Y : Set (Torus d n1))).Z0 :=
  eq_iUnion_of_inter (fun _ hx => st.Z0_subset_Zpre ω crit hx)
    (fun _ hY => Z0_inter_comp crit hn rad hY)

/-- The local sets of distinct components are disjoint (they lie in their components). -/
theorem restrict_disjoint {Y Y' : Finset (Torus d n1)}
    (hY : Y ∈ comps ω (finOf (st.Zpre ω crit))) (hY' : Y' ∈ comps ω (finOf (st.Zpre ω crit)))
    (hne : Y ≠ Y') :
    Disjoint (st.restrict (Y : Set (Torus d n1))).Z0 (st.restrict (Y' : Set (Torus d n1))).Z0 :=
  (comps_disjoint hY hY' hne).mono (restrict_Z0_subset_comp (ω := ω) crit hn rad hY)
    (restrict_Z0_subset_comp (ω := ω) crit hn rad hY')

end Decomp

end RegionStep

end Balaban.LargeField
