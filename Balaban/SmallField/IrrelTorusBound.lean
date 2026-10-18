/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusBoundId
public import Balaban.SmallField.RenormAnisoIrrel

/-!
# The bound of the label functional, conditional on the data hypotheses (P1 Corollary 3.11)

For a label `(j, y, X)` with `X ≠ □(y)` and data `(Ψ, h)`, `Ψ` constant on the `j`-blocks and `h`
constant:

* `sum_placeSet`: sums over the placement `S` of the blocks of `X` relative to `y` are sums over the
  aligned sites of `X`;
* `irrelTorus_eq_Itw_centred`: the label functional `ℰ^{(j)}_{irrel}(y, X; Ψ, h)` is the termwise
  `Itw` (FLUCTUATION.md §3.2) of the one-polymer family of `premisesTermAniso_centred` at the data
  pulled back at `y`, `ψ_y(s) = Ψ(y + ibase s)`, `b = ν_j h`, whenever the pulled-back configuration
  lies in the anisotropic polydisc or outside the anisotropic tube (where the extension of the
  term to the tube is the term itself);
* `irrelTorus_bound_of_dataHyp_of_poly`: **conditional on `DataHypAniso`** at the pulled-back data
  (the open analytic input P-2: `σ = C₀ s_{jk}`, `ε = ε_k`), and for data in the polydisc or
  outside the tube, `|ℰ^{(j)}_{irrel}(y, X)| ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)}`, `α₃ = 1 - 2γ - α₁`
  (P1 (3.128)), with `C_I` independent of the torus, `k`, `j`, the label and the data.

Not covered: data whose pulled-back configuration lies in the anisotropic tube but not in the
polydisc (the extension of the term to the tube is the term at a complex frame rotation of the
data, which equals the term at the data only if that rotation keeps the data in the class domain:
OPEN-I6-XIDOM, CROTE.md §2), and the label `X = □(y)`, whose functional also carries the resummed
relevant local parts (their smallness on the torus is the torus form of the renormalization
conditions, P1 (H.6) p. 118, which the class states in infinite volume only, P4 (H.5) pp. 677–678).
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

section Reindex

variable {j : ℕ}

open Classical in
/-- Sums over the placement `S` of the blocks of `X` relative to `y` are sums over the aligned
sites of `X`. -/
theorem sum_placeSet (hjk : j ≤ k) {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}
    (hSdef : S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)))
    (F : ↥S → ℂ) :
    ∑ s : ↥S, F s = ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
      (if hm : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) ∈ S then F ⟨_, hm⟩
        else 0) := by
  set G : Site d → ℂ := fun s => if hs : s ∈ S then F ⟨s, hs⟩ else 0 with hG
  have h1 : ∑ s : ↥S, F s = ∑ s : ↥S, G s.1 :=
    Finset.sum_congr rfl fun s _ => by simp only [hG, s.2, ↓reduceDIte]
  have h2 : ∑ s ∈ S, G s = ∑ s ∈ (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)), G s := by
    rw [← hSdef]
  rw [h1, Finset.sum_coe_sort S G, h2, Finset.sum_image]
  intro x hx x' hx' h
  exact placeSet_inj hjk hy (Finset.mem_filter.1 hx).2.1 (Finset.mem_filter.1 hx').2.1 h

end Reindex

section Ident

variable {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

open Classical in
/-- **The label functional is the termwise `Itw` of the label pulled back at its centre**: for
`X ≠ □(y)`, `Ψ` constant on the `j`-blocks and the constant field `h`, with
`ψ_y(s) = Ψ(y + ibase s)` and `b = ν_j h`,
`ℰ^{(j)}_{irrel}(y, X; Ψ, h) = Itw(T_{y,X})(S; ψ_y, b)` for the one-polymer family `T_{y,X}` of
`premisesTermAniso_centred`, whenever the configuration `pack S ψ_y b` lies in the anisotropic
polydisc or outside the anisotropic tube. -/
theorem irrelTorus_eq_Itw_centred (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hj1 : 1 ≤ j) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hXne : X ≠ box (cbase (cellSide L P.m₀ m₁ j) y -
      natT fun _ => L / 2 * cellSide L P.m₀ m₁ j) (L * cellSide L P.m₀ m₁ j))
    (hSdef : S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    {Ψ : Fld d L N₁ m₁ k N}
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    (hv : Fin N → ℂ)
    (hpack : pack S (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        ((ν : ℂ) • hv) ∈ polyAniso i₀ ν r S ∨
      pack S (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        ((ν : ℂ) • hv) ∉ TubeAniso i₀ ν r S) :
    irrelTorus P.m₀ Tm i₀ i₁ j y X Ψ (constFld hv) =
      Itw (⟨{S}, fun _ => sizeJ P.m₀ j X, fun S' c => trickFnA i₀ ν r (fun c' : Cfg d N S' =>
           Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - y))
             (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ : TermFamily d N)
        i₀ i₁ ν S (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        ((ν : ℂ) • hv) := by
  have hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S :=
    fun z hz => by rw [hSdef]; exact mem_placeSet hN hjk hy hX hz
  have hmS : ∀ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) ∈ S :=
    fun x hx => by rw [hSdef]; exact Finset.mem_image_of_mem _ hx
  have hT := tubeHypA_shiftTerm hcl hBg hν hμν hj1 hjk hy hX hyX hS hne hrad
  have hr0 := hrad.1
  have hr1 := hrad.2.1
  have hE := analyticAt_term_ref (y := y) hcl hBg hν hμν hj1 hjk hX hyX i₀ hrad
  have hνc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  set ψ : Site d → Spin N := fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)
    with hψ
  have hψ0 : ψ 0 = Ψ y := by simp only [hψ, ibase_zero, add_zero]
  have hψeU : ∀ μ, ψ (eU μ) = Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) :=
    fun μ => by simp only [hψ, ibase_eU]
  have hψx : ∀ x, Aligned (L ^ j) x →
      ψ (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)) = Ψ x := fun x hx => by
    simp only [hψ]
    rw [add_ibase_unlift_sub hjk hy x, cbase_eq_self_of_aligned hx]
  -- the term at the data
  have hterm : trickFnA i₀ ν r (fun c' : Cfg d N S =>
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')) (pack S ψ ((ν : ℂ) • hv)) =
      Tm.E j y X Ψ (constFld hv) := by
    have hF : trickFnA i₀ ν r (fun c' : Cfg d N S =>
        Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
          (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')) (pack S ψ ((ν : ℂ) • hv)) =
        Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
          (pack S ψ ((ν : ℂ) • hv)) (z - y))
          (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (pack S ψ ((ν : ℂ) • hv))) := by
      rcases hpack with hp | hp
      · exact trickFnA_of_poly hT hp
      · have hp' : ¬ ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
            rotCfgL R S (pack S ψ ((ν : ℂ) • hv)) ∈ polyAniso i₀ ν r S := hp
        unfold trickFnA
        simp only [hp', dite_false]
    rw [hF]
    refine hcl.localE j y X _ _ _ _ fun z hz => ⟨shiftField_pack hjk hy hS hΨb _ hz, ?_⟩
    rw [hOf_pack_smul hν.ne']
  -- the family
  set T : TermFamily d N := ⟨{S}, fun _ => sizeJ P.m₀ j X, fun S' c => trickFnA i₀ ν r
    (fun c' : Cfg d N S' =>
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S' c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S' c')) c⟩ with hTdef
  have hTterm : T.term S = trickFnA i₀ ν r (fun c' : Cfg d N S =>
      Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')) := rfl
  -- the tensors
  have hA : ∀ x (hx : x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)),
      tensA i₀ ν S (T.term S) ⟨_, hmS x hx⟩ =
        fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1)))
          (constFld (Pi.single i₀ 1)) (blockDir L j x i₀) := fun x hx => by
    rw [hTterm]
    exact tensA_centred hT hjk hy hν hr0 hE (Finset.mem_filter.1 hx).2.1 _
  have hB : ∀ x (hx : x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X))
      x' (hx' : x' ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)),
      tensB i₀ i₁ ν S (T.term S) ⟨_, hmS x hx⟩ ⟨_, hmS x' hx'⟩ =
        D2 (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1))) (constFld (Pi.single i₀ 1))
          (blockDir L j x i₁) (blockDir L j x' i₁) := fun x hx x' hx' => by
    rw [hTterm]
    exact tensB_centred hT hjk hy hν hr0 hr1 hE i₁ (Finset.mem_filter.1 hx).2.1
      (Finset.mem_filter.1 hx').2.1 _ _
  have hsumA : ∀ G : Site d → ℂ, ∑ s : ↥S, tensA i₀ ν S (T.term S) s * G s.1 =
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
        fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1)))
          (constFld (Pi.single i₀ 1)) (blockDir L j x i₀) *
          G (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)) := by
    intro G
    rw [sum_placeSet hjk hy hSdef]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hmS x hx, ↓reduceDIte]
    rw [hA x hx]
  -- `T_X`
  have hTtw : Ttw T i₀ ν S ψ ((ν : ℂ) • hv) =
      Tm.E j y X (constFld (Pi.single i₀ 1)) (constFld (Pi.single i₀ 1)) +
        (sqrtC (dot (Ψ y) (Ψ y)) - 1) *
          ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
            fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1)))
              (constFld (Pi.single i₀ 1)) (blockDir L j x i₀) +
        (dot (Ψ y) hv / sqrtC (dot (Ψ y) (Ψ y)) - 1) *
          fderiv ℂ (fun h' => Tm.E j y X (constFld (Pi.single i₀ 1)) h')
            (constFld (Pi.single i₀ 1)) (constFld (Pi.single i₀ 1)) := by
    have h1 := hsumA (fun _ => 1)
    simp only [mul_one] at h1
    simp only [Ttw, uInv, vInv, hψ0]
    rw [h1, hTterm, term_refPt_centred hT hν hr0, fderivB_centred hT hν hr0 hE, dot_smul_right]
    have e : ((ν : ℂ) * dot (Ψ y) hv / sqrtC (dot (Ψ y) (Ψ y)) - ν) *
        ((ν : ℂ)⁻¹ * fderiv ℂ (fun h' => Tm.E j y X (constFld (Pi.single i₀ 1)) h')
          (constFld (Pi.single i₀ 1)) (constFld (Pi.single i₀ 1))) =
        ((ν : ℂ) * (ν : ℂ)⁻¹) * ((dot (Ψ y) hv / sqrtC (dot (Ψ y) (Ψ y)) - 1) *
          fderiv ℂ (fun h' => Tm.E j y X (constFld (Pi.single i₀ 1)) h')
            (constFld (Pi.single i₀ 1)) (constFld (Pi.single i₀ 1))) := by ring
    rw [e, mul_inv_cancel₀ hνc, one_mul]
  -- `A_{y,X}`
  have hAx : Ax T i₀ ν ψ S = (1 / 2 : ℂ) *
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
        fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1)))
          (constFld (Pi.single i₀ 1)) (blockDir L j x i₀) *
          (dot (Ψ x) (Ψ x) - dot (Ψ y) (Ψ y)) := by
    have h1 := hsumA (fun s => dot (ψ s) (ψ s) - dot (ψ 0) (ψ 0))
    unfold Ax
    rw [h1]
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hψx x (Finset.mem_filter.1 hx).2.1, hψ0]
  -- `Φ_{y,X}`
  have hSx : ∀ μ μ' : Fin d, Sx T i₀ i₁ ν S μ μ' =
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
        ∑ x' ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
          D2 (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1))) (constFld (Pi.single i₀ 1))
            (blockDir L j x i₁) (blockDir L j x' i₁) *
          ((((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) μ : ℤ) : ℂ) -
              ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y) μ : ℤ) : ℂ)) *
            (((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) μ' : ℤ) : ℂ) -
              ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y) μ' : ℤ) : ℂ))) := by
    intro μ μ'
    unfold Sx
    rw [sum_placeSet hjk hy hSdef]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hmS x hx, ↓reduceDIte]
    rw [sum_placeSet hjk hy hSdef]
    refine Finset.sum_congr rfl fun x' hx' => ?_
    simp only [hmS x' hx', ↓reduceDIte]
    rw [hB x hx x' hx']
    simp only [Pi.sub_apply, Int.cast_sub]
  have hPhi : Phitw T i₀ i₁ ν S ψ = -(1 / 4 : ℂ) * ∑ μ, ∑ μ',
      (dot (Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y)
          (Ψ (y + (L ^ j) • (Pi.single μ' 1 : CTorus d L N₁ m₁ k)) - Ψ y) -
        dot (Ψ y) (Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y) *
          dot (Ψ y) (Ψ (y + (L ^ j) • (Pi.single μ' 1 : CTorus d L N₁ m₁ k)) - Ψ y) /
          dot (Ψ y) (Ψ y)) *
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
        ∑ x' ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
          D2 (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1))) (constFld (Pi.single i₀ 1))
            (blockDir L j x i₁) (blockDir L j x' i₁) *
          ((((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) μ : ℤ) : ℂ) -
              ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y) μ : ℤ) : ℂ)) *
            (((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) μ' : ℤ) : ℂ) -
              ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y) μ' : ℤ) : ℂ))) := by
    unfold Phitw
    congr 1
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun μ' _ => ?_
    rw [hSx μ μ']
    congr 1
    unfold gradInv
    rw [hψeU μ, hψeU μ', hψ0]
  -- assembly
  have hcy : (constFld hv : Fld d L N₁ m₁ k N) y = hv := rfl
  unfold Itw
  rw [hTtw, hAx, hPhi, hTterm, hterm]
  simp only [irrelTorus, hXne, ↓reduceIte, add_zero, hcy]
  ring

end Ident

/-! ### The bound, conditional on the data hypotheses -/

open Classical in
/-- **The per-label bound of the irrelevant part, conditional on `DataHypAniso`** (P1 Corollary
3.11, (3.128), p. 153; the open analytic input P-2 is the premise `DataHypAniso` at the data pulled
back at `y`, with `σ = C₀ s`, `s = s_{jk} = L^{-(k-j)}`, `ε = ε_k`): for a torus of the class on
its main instance `xiFieldDom a μ ε_j` (term clauses, `CRotE`, `BgHyp`, `μ L^{2j} ≤ ν_j`), a label
`(j, y, X)` with `X ≠ □(y)`, `Ψ` constant on the `j`-blocks and the constant field `h`, and data
whose pulled-back configuration lies in the anisotropic polydisc or outside the anisotropic tube,
`|ℰ^{(j)}_{irrel}(y, X; Ψ, h)| ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)}`, `α₃ = 1 - 2γ - α₁`.  The
constant `C_I` depends on `d, N, L, m₁`, `P` and the numerical parameters only: not on the torus,
`k`, `j`, the regime, the label or the data.  Not used to close a source node (P-2 is OPEN). -/
theorem irrelTorus_bound_of_dataHyp_of_poly (d L N m₁ : ℕ) [NeZero L] (P : Consts)
    (hP : P.Admissible d L) (Λ Ksig γ C₀ KR : ℝ) (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig)
    (hC₀ : 0 < C₀) :
    ∃ CI : ℝ, 0 ≤ CI ∧ ∀ (N₁ k : ℕ) [NeZero N₁] (ϱ : ℝ) (a : ℕ → ℝ) (μ : ℝ)
      (Tm : Terms d L N₁ m₁ k N ϱ),
      SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm →
      BgHyp d L k ϱ a μ → L ^ P.m₀ ∣ N₁ →
      ∀ (ν : ℝ) (j : ℕ), 0 < ν → μ * ((L : ℝ) ^ j) ^ 2 ≤ ν → 1 ≤ j → j ≤ k →
      ∀ (r : ℝ), AnisoRadiusOK d L N P j r →
      ∀ (y : CTorus d L N₁ m₁ k) (X : Set (CTorus d L N₁ m₁ k)), Aligned (L ^ j) y →
      IsPolyDom P.m₀ j X → y ∈ X →
      X ≠ box (cbase (cellSide L P.m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L P.m₀ m₁ j)
        (L * cellSide L P.m₀ m₁ j) →
      ∀ (S : Finset (Site d)), S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
        (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)) →
      ∀ (i₀ i₁ : Fin N), i₁ ≠ i₀ →
      ∀ (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ),
      (∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x') →
      ∀ (s σ ε K₂ : ℝ),
      DataHypAniso {p | ∃ Ψ' h' : Fld d L N₁ m₁ k N,
          (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
              (pack S p.1 p.2) (z - y) ∧
            h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (pack S p.1 p.2) z) ∧
          XiDom (Tm.gs j X) a μ j (P.eps d L j) Ψ' h'} ν σ ε K₂
        (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)) ((ν : ℂ) • hv) →
      (pack S (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
          ((ν : ℂ) • hv) ∈ polyAniso i₀ ν r S ∨
        pack S (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
          ((ν : ℂ) • hv) ∉ TubeAniso i₀ ν r S) →
      0 < s → σ = C₀ * s → ε / r ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ) → 0 < ε → ε ≤ Λ * r →
      σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 → ν ≤ σ ^ 2 → K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε →
      ‖irrelTorus P.m₀ Tm i₀ i₁ j y X Ψ (constFld hv)‖ ≤
        CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := by
  have hα1 : P.α₁ < 1 := by have := hP.α₁_lt; have := hP.γ_pos; linarith
  obtain ⟨CI, hCI0, hCI⟩ := termwise_irrelevant_aniso_scaled d N (diamA d L P.m₀ m₁) Λ Ksig P.α₁ γ
    C₀ KR (diamA_nonneg d L P.m₀ m₁) hΛ hKsig hP.α₁_pos hα1 hC₀
  refine ⟨CI, hCI0, ?_⟩
  intro N₁ k _ ϱ a μ Tm hcl hBg hN ν j hν hμν hj1 hjk r hrad y X hy hX hyX hXne S hSdef i₀ i₁
    hne Ψ hv hΨb s σ ε K₂ dat hpack hs hσs hR hε hεΛ hσ1 hτ hνσ hK
  have hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S :=
    fun z hz => by rw [hSdef]; exact mem_placeSet hN hjk hy hX hz
  have hS' : ∀ s ∈ S, ∃ x ∈ X, Aligned (L ^ j) x ∧
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) = s := by
    intro s hs
    rw [hSdef] at hs
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hs
    exact ⟨x, (Finset.mem_filter.1 hx).2.2, (Finset.mem_filter.1 hx).2.1, rfl⟩
  rw [irrelTorus_eq_Itw_centred hcl hBg hν hμν hj1 hjk hN hy hX hyX hXne hSdef hne hrad hΨb hv
    hpack]
  exact hCI _ i₀ i₁ ν r P.E₀ P.κ _ _
    (premisesTermAniso_centred hcl hBg hν hμν hj1 hjk hy hX hyX hS hS' hne hrad) _ _ s σ ε K₂
    dat S (Set.mem_singleton S) hs hσs hR hrad.1 hrad.2.1 hε hεΛ hσ1 hτ hν.le hνσ hP.E₀_nonneg hK

end Balaban.SmallField.Def6v2
