module

public import Balaban.LargeField.Region.SymmLat
public import Balaban.LargeField.History.RegionHistory

/-!
# Covariance of the region calculus under lattice symmetries

Let `e₀, e₁` be affine lattice isometries of the cube tori `𝕋_k, 𝕋_{k+1}` commuting with the
coarsening `blockMap L n₁`.  If the steps `st, st'` of the region calculus correspond (the region
`Z_k` and the new cubes `P, Q, R, S` of `st'` are the images of those of `st`), then so are the
derived sets `U, U', Ω', Ω, F'', Ω'', F^Z, Z^{(0)}` (`RegionStep.image_Omega`, ...).

`RegionIso σ H H'` says that a lattice symmetry `σ` maps the region history `H` to `H'` (the
records of every step below the horizon correspond under the cube actions `σ.ec j`);
`nonempty_regionIso` shows the relation is inhabited (by the identity), and
`RegionIso.omega` is the covariance of the domains `Ω_{j+1}`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

theorem IsAff.exists_lblock {d n L : ℕ} {e : Equiv.Perm (Torus d n)} (he : IsAff e) (hL : 0 < L) :
    (∀ c, ∃ c', e '' lblock L c = lblock L c') ∧ (∀ c', ∃ c, e '' lblock L c = lblock L c') := by
  obtain ⟨A, hA⟩ := he
  have hf : (e : Torus d n → Torus d n) = A.toFun := funext hA
  refine ⟨fun c => ?_, fun c' => ?_⟩
  · refine ⟨fun i => A.toFun c i -
      (if A.flip (A.perm.symm i) then ((L - 1 : ℕ) : ZMod n) else 0), ?_⟩
    show (e : Torus d n → Torus d n) '' lblock L c = _
    rw [hf]
    exact A.image_lblock hL c
  · obtain ⟨c, hc⟩ := A.exists_lblock_image hL c'
    exact ⟨c, by rw [show (e : Torus d n → Torus d n) '' lblock L c = A.toFun '' lblock L c by rw [hf]]; exact hc⟩

section Step

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rp Rk : ℝ} {st st' : RegionStep d L n0 n1 Rp Rk}
  {e0 : Equiv.Perm (Torus d n0)} {e1 : Equiv.Perm (Torus d n1)} (h0 : IsAff e0) (h1 : IsAff e1)
  (hb : ∀ x, blockMap L n1 (e0 x) = e1 (blockMap L n1 x)) (hL : 0 < L)
  (hZ : st'.Z = e0 '' st.Z) (hP : st'.P = e1 '' st.P)

include h0 hZ in
theorem RegionStep.image_U : st'.U = e0 '' st.U := by
  show Region.U ⌊Rp⌋₊ st'.Z = e0 '' Region.U ⌊Rp⌋₊ st.Z
  unfold Region.U
  rw [hZ, image_thick h0.supDist_eq]

include h0 hb hZ in
theorem RegionStep.image_Uprime : st'.Uprime = e1 '' st.Uprime := by
  show blockMap L n1 '' st'.U = e1 '' (blockMap L n1 '' st.U)
  rw [RegionStep.image_U h0 hZ, Set.image_image, Set.image_image]
  exact Set.image_congr (fun x _ => hb x)

include h0 h1 hb hL hZ in
theorem RegionStep.image_OmegaPrime : st'.OmegaPrime = e1 '' st.OmegaPrime := by
  show Region.OmegaPrime L ⌊Rk⌋₊ st'.Uprime = e1 '' Region.OmegaPrime L ⌊Rk⌋₊ st.Uprime
  unfold Region.OmegaPrime
  obtain ⟨hW, hW'⟩ := h1.exists_lblock hL
  rw [RegionStep.image_Uprime h0 hb hZ, image_opening h1.supDist_eq hW hW',
    image_nbhd h1.supDist_eq]

include h0 h1 hb hL hZ hP in
theorem RegionStep.image_Omega : st'.Omega = e1 '' st.Omega := by
  show Region.Omega L st'.P st'.OmegaPrime = e1 '' Region.Omega L st.P st.OmegaPrime
  unfold Region.Omega
  obtain ⟨hW, hW'⟩ := h1.exists_lblock hL
  rw [RegionStep.image_OmegaPrime h0 h1 hb hL hZ, hP, image_openingIn h1.supDist_eq hW hW',
    image_nbhd h1.supDist_eq]

end Step


section Hist

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L]

/-- The lattice symmetry `σ` maps the region history `H` to the region history `H'`: the region
`Z_j` and the new cubes `P, Q, R, S` of every step below the horizon correspond under the actions
`σ.ec j` on the cubes. -/
structure RegionIso (σ : LatTorusSym S n M K) (H H' : RegionHistory S n R k0 K) : Prop where
  hZ : ∀ j, j ≤ K → (H'.step j).Z = σ.ec j '' (H.step j).Z
  hP : ∀ j, j + 1 ≤ K → (H'.step j).P = σ.ec (j + 1) '' (H.step j).P
  hQ : ∀ j, j + 1 ≤ K → (H'.step j).Q = σ.ec (j + 1) '' (H.step j).Q
  hR : ∀ j, j + 1 ≤ K → (H'.step j).R = σ.ec (j + 1) '' (H.step j).R
  hS : ∀ j, j + 1 ≤ K → (H'.step j).S = σ.ec (j + 1) '' (H.step j).S

/-- Hard rule 10: `RegionIso` is inhabited (the identity symmetry maps `H` to itself). -/
theorem nonempty_regionIso (H : RegionHistory S n R k0 K) :
    Nonempty (RegionIso (LatTorusSym.refl S n M K) H H) :=
  ⟨⟨fun _ _ => by simp [LatTorusSym.refl], fun _ _ => by simp [LatTorusSym.refl],
    fun _ _ => by simp [LatTorusSym.refl], fun _ _ => by simp [LatTorusSym.refl],
    fun _ _ => by simp [LatTorusSym.refl]⟩⟩

variable {σ : LatTorusSym S n M K} {H H' : RegionHistory S n R k0 K}

/-- Covariance of the domains: `Ω'_{j+1} = σ Ω_{j+1}`. -/
theorem RegionIso.omega (h : RegionIso σ H H') {j : ℕ} (hj : j + 1 ≤ K) :
    (H'.step j).Omega = σ.ec (j + 1) '' (H.step j).Omega := by
  have hL : 0 < S.L := NeZero.pos S.L
  exact RegionStep.image_Omega (σ.isAff_ec H.F.hnn (by omega)) (σ.isAff_ec H.F.hnn hj)
    (fun x => (σ.ec_blockMap H.F.hnn hj x).symm) hL (h.hZ j (by omega)) (h.hP j hj)

end Hist

end Balaban.LargeField
