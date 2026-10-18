/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvPieces
public import Balaban.LargeField.R.PieceChain
public import Balaban.LargeField.R.WindowRegionUnion
public import Balaban.LargeField.R.WindowNodeCongr

/-!
# The sum of the main actions of the pieces of the window (blocker 4, item S5)

`notes/phase1/LF4R-PLAN.md` §9.3, item S5.  The pieces `(j, c)` of the window (`k₁ ≤ j ≤ m'`, `c` an
ancestor of `Z` at scale `j + 1`), their regions on the window generating set (W959), their chains of
conversions `pieceChain` (W958) form a `PieceWindowSetup`; `window_conversion_pieces` then gives
`∑_i 𝒜_{j_i+1}(c_i; ψ) = Re(β_k A*_k(X_win)) - Re C` with `|C| ≤ C₁₅ ∑_i |X_i|`.

* `sum_mainActionLoc_eq_gen`: for any finite family of pieces, injective and covering the window;
* `sum_mainActionLoc_eq`: the family `(j, P, c)` of `locOp_absW_le_chain` and the top piece `(m', Z)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory
  Balaban.LargeField.ActionConv Balaban.SmallField

section Gen

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

/-- The sites of two different pieces of the window are disjoint (from `piece_sites_disjoint_same`,
`piece_sites_disjoint_lt`): the regions `X_i` of a family of pieces with injective `(j_i, c_i)`. -/
theorem pieces_regions_disjoint {k1 m' : ℕ} {Z : H.Comp (m' + 1)} (g : Geo S n R M)
    (hmK : m' + 1 ≤ K) {ι : Type*} (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, k1 ≤ jf i ∧ jf i ≤ m') (hcf : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z)
    (hinj : Function.Injective fun i => (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)))
    {i i' : ι} (hne : i ≠ i') (x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)))
    (hx : torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (hx' : torusCast (piece_torus_eq g H.F.hnn hmK (hjf i').2) x ∈
      Xfine g (H.locRH (jf i' + 1) (cf i')) (jf i') (cf i').1) : False := by
  have hK : ∀ i, jf i + 1 ≤ K := fun i => by have := (hjf i).2; omega
  obtain ⟨h1, h2⟩ := (mem_Xfine_cast_iff g hmK (hjf i).2 (cf i) (hK i) x).mp hx
  obtain ⟨h1', h2'⟩ := (mem_Xfine_cast_iff g hmK (hjf i').2 (cf i') (hK i') x).mp hx'
  rcases lt_trichotomy (jf i) (jf i') with hlt | heq | hgt
  · exact piece_sites_disjoint_lt hmK hlt (hjf i').2 (hcf i) (hcf i') h1 h1' h2'
  · have key : ∀ (j j' : ℕ) (c : H.Comp (j + 1)) (c' : H.Comp (j' + 1)), j = j' →
        (⟨j, c⟩ : Σ j, H.Comp (j + 1)) ≠ ⟨j', c'⟩ →
        cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1 → cubeMap n S.L M (m' + 1) (j' + 1) x ∈ c'.1 →
        False := by
      intro j j' c c' h
      subst h
      intro hne' hx1 hx2
      exact piece_sites_disjoint_same (fun hcc => hne' (by rw [hcc])) hx1 hx2
    exact key _ _ _ _ heq (fun h => hne (hinj h)) h1 h1'
  · exact piece_sites_disjoint_lt hmK hgt (hjf i).2 (hcf i') (hcf i) h1' h1 h2

/-- The geometric `PieceWindowSetup` used by `sum_mainActionLoc_eq_gen`.  The parameters
`ak`, `νk`, `βk`, `Datw`, and `φw` are explicit so that a physical read comparison can
specialize them to the window configuration of P7 p. 501 (2.14)–(2.16). -/
noncomputable def pieceWindowSetupOfFamily (g : Geo S n R M)
    {k1 m' : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K)
    {ϱ : ℝ} (Wp : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ)
    (hWh : Wp.Hyp) {ι : Type*} [Fintype ι] (jf : ι → ℕ)
    (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, k1 ≤ jf i ∧ jf i ≤ m')
    (hcf : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z)
    (hinj : Function.Injective fun i => (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)))
    (hjK : ∀ i, jf i + 1 ≤ K)
    (Xw : ι → Region (Wp.windowGenSet hWh))
    (hXw : ∀ i x, x ∈ (Xw i).sites ↔
      torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
        Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (Xwin : Region (Wp.windowGenSet hWh))
    (hsites : Xwin.sites = Finset.univ.biUnion fun i => (Xw i).sites)
    (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i)))
    (decomp : ∀ i, StepDecomp (Xc i))
    (ak : ℕ → ℝ) (νk βk : ℝ) (Datw : BgData (Wp.windowGenSet hWh) N)
    (φw : (Wp.windowGenSet hWh).Ω 1 × Fin N → ℂ) (br : MassBranch)
    (chain : ∀ i, ConvChain (Set.univ : Set Unit) (jf i) (m' + 1)
      (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
        (locComp_mem H (hjK i) (cf i)) (hjK i)) (Xc i) br N) :
    PieceWindowSetup S.d S.L (M * n (m' + 1)) (m' + 1) N
      (Set.univ : Set Unit) ι jf k1 (m' + 1) := by
  classical
  exact
    { sc_mem := fun i => Finset.mem_Ico.2 ⟨(hjf i).1, by have := (hjf i).2; omega⟩
      ϱw := ϱ
      Gw := Wp.windowGenSet hWh
      Xw := Xw
      Xwin := Xwin
      Xwin_sites := hsites
      Xw_disj := fun i _ i' _ hne => Finset.disjoint_left.2 fun x hx hx' =>
        pieces_regions_disjoint g hmK jf cf hjf hcf hinj hne x ((hXw i x).mp hx) ((hXw i' x).mp hx')
      ak := ak
      νk := νk
      βk := βk
      Datw := fun _ => Datw
      φw := fun _ => φw
      N₀c := fun i => g.M1 * (g.c * n (jf i + 1))
      neN₀c := fun _ => inferInstance
      Kc := fun i => jf i + 1
      ϱc := fun _ => minSep S.L g.M1
      Gc := fun i => locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
        (locComp_mem H (hjK i) (cf i)) (hjK i)
      Xc := Xc
      br := fun _ => br
      chain := chain
      decomp := decomp
      mcount := fun i => (decomp i).total
      mcount_eq := fun _ => rfl }


open Classical in
/-- **S5 for a family of pieces** (LFR (2.15′), P7 (2.12)-(2.16)).  Let `(j_i, c_i)_{i ∈ ι}` be an injective
family of pieces of the window of `Z` (`k₁ ≤ j_i ≤ m'`, `c_i` an ancestor of `Z` at scale `j_i + 1`) that covers
all pieces, with the regions `X_i` of the pieces on the window generating set and on `locGen`, and let
`chain i` be the chain of conversions `pieceChain` of the piece `i` at the configuration `(ou i, xu i, hv)`.
Under the named source estimates of `window_conversion_pieces` (`p7_first`, `window_decay`, `hflow` with the
scale couplings `cs.beta`), the sum of the main actions of the pieces is `Re(β_k A*_k(X_win)) - Re C` with
`‖C‖ ≤ C₁₅ ∑_i |X_i|_{j_i+1}`. -/
theorem sum_mainActionLoc_eq_gen (g : Geo S n R M) (cs : OpConsts) {k1 m' : ℕ} {Z : H.Comp (m' + 1)}
    (hmK : m' + 1 ≤ K) {ϱ : ℝ} (Wp : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ)
    (hWh : Wp.Hyp) {ι : Type*} [Fintype ι] (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, k1 ≤ jf i ∧ jf i ≤ m') (hcf : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z)
    (hinj : Function.Injective fun i => (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)))
    (hcov : ∀ j (c : H.Comp (j + 1)), k1 ≤ j → j ≤ m' → c ∈ H.ancFin (j + 1) (m' + 1) Z →
      ∃ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = ⟨j, c⟩)
    (hjK : ∀ i, jf i + 1 ≤ K) (hk1p : 1 ≤ k1)
    (Xw : ι → Region (Wp.windowGenSet hWh))
    (hXw : ∀ i x, x ∈ (Xw i).sites ↔ torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (Xwin : Region (Wp.windowGenSet hWh))
    (hXwin : ∀ x, x ∈ Xwin.sites ↔ ∃ j, ∃ hj : k1 ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
      c ∈ H.ancFin (j + 1) (m' + 1) Z ∧
        torusCast (piece_torus_eq g H.F.hnn hmK hj.2) x ∈ Xfine g (H.locRH (j + 1) c) j c.1)
    (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i)))
    (hXc : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (decomp : ∀ i, StepDecomp (Xc i))
    (ak : ℕ → ℝ) (νk βk : ℝ) (Datw : BgData (Wp.windowGenSet hWh) N)
    (φw : (Wp.windowGenSet hWh).Ω 1 × Fin N → ℂ) (br : MassBranch)
    (ou : ∀ i, OutT N R (H.localHistory M K (jf i + 1) (cf i)) (jf i + 1))
    (xu : ∀ i, NewCfg N (H.localHistory M K (jf i + 1) (cf i)) (jf i))
    (hv : EuclideanSpace ℝ (Fin N))
    (hβ : ∀ i m, jf i + 1 ≤ m → m ≤ m' + 1 → cs.beta m ≠ 0)
    (hμ : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 → cs.muAct m ≠ 0)
    (hB0 : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1) cs.aw (cs.muBg (jf i + 1)))
    (hBn : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 → BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1)
      (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (jf i + 1)) (jf i + 1) 0 /
        betaCanon S.d S.L (cs.beta m) m 0)) (br.elMass (cs.muAct m)))
    (hS : ∀ i, InUnionDomainR (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
        (locComp_mem H (hjK i) (cf i)) (hjK i)) (bgC1 S.d S.L N) (cs.muBg (jf i + 1))
        (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv) ∧
      ∀ m, jf i + 2 ≤ m → m ≤ m' + 1 →
        InUnionDomainR (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
          (locComp_mem H (hjK i) (cf i)) (hjK i)) (bgC1 S.d S.L N) (br.elMass (cs.muAct m))
          (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
            (hjK i) (ou i) (xu i) hv))
    (chain : ∀ i, ConvChain (Set.univ : Set Unit) (jf i) (m' + 1)
      (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))
      (Xc i) br N)
    (hchain : ∀ i, chain i = pieceChain g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i) cs Set.univ (m' + 1) br (Xc i) (fun _ => ou i)
      (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i) (fun _ _ => hS i))
    {Kconv Kbg γw M₀ M₁ : ℝ} {ε Rhat : ℕ → ℝ}
    (p7_first : ∀ i, ∀ m, jf i + 2 ≤ m → m ≤ m' + 1 → ‖(chain i).cost () m‖ ≤ Kconv *
      ((cs.beta (jf i + 1) * ε (jf i + 1) ^ 2) / (cs.beta m * ε m ^ 2)) * (decomp i).total)
    (window_decay : ∀ i, ‖(chain i).T () (m' + 1) -
        (βk : ℂ) * actionRegionC (Xw i) ak νk Datw φw‖ ≤
      Kbg * Real.exp (-γw * (M₀ * (Rhat (jf i - 1) - 1) - 2 * M₁)) * (decomp i).total)
    {γ η α α₀ : ℝ} (hd : 2 ≤ S.d) (hL : 1 < S.L) (hγ : 0 < γ) (hα₀ : 0 < α₀)
    (hε : ε = epsSeq S.L α α₀) (hγα : (S.d : ℝ) - 2 - 2 * α = 2 * γ)
    (hflow : ∀ i, ∃ B : ℝ, 0 < B ∧ ∃ gg : ℕ → ℝ,
      (∀ m, Real.exp (-η) ≤ gg m ∧ gg m ≤ Real.exp η) ∧
      ∀ m, jf i + 1 ≤ m → m ≤ m' + 1 →
        cs.beta m = B * (S.L : ℝ) ^ ((S.d - 2) * m) * gg m)
    (hKc : 0 ≤ Kconv) (hKb : 0 ≤ Kbg) (hγw : 0 ≤ γw)
    (hsep : ∀ i, 0 ≤ M₀ * (Rhat (jf i - 1) - 1) - 2 * M₁) :
    ∃ C : ℂ, ∑ i, mainActionLoc g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
        (locComp_mem H (hjK i) (cf i)) (hjK i) cs (locRH_rem (jf i + 1) (cf i)) (ou i) (xu i) hv =
      ((βk : ℂ) * actionRegionC Xwin ak νk Datw φw).re - C.re ∧
    ‖C‖ ≤ (9 * Real.exp (2 * η) * Kconv / (1 - (S.L : ℝ) ^ (-(2 * γ))) + Kbg) *
      ∑ i, (decomp i).total := by
  classical
  have hQ : ∀ (x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))) (s s' : Σ j, H.Comp (j + 1)),
      s = s' → ((∃ hj : s.1 ≤ m', torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈
        Xfine g (H.locRH (s.1 + 1) s.2) s.1 s.2.1) ↔
      ∃ hj : s'.1 ≤ m', torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈
        Xfine g (H.locRH (s'.1 + 1) s'.2) s'.1 s'.2.1) := by
    intro x s s' h
    subst h
    exact Iff.rfl
  have hsites : Xwin.sites = Finset.univ.biUnion fun i => (Xw i).sites := by
    ext x
    rw [hXwin, Finset.mem_biUnion]
    constructor
    · rintro ⟨j, hj, c, hc, hx⟩
      obtain ⟨i, hi⟩ := hcov j c hj.1 hj.2 hc
      refine ⟨i, Finset.mem_univ _, (hXw i x).mpr ?_⟩
      have := (hQ x _ _ hi.symm).mp ⟨hj.2, hx⟩
      exact this.2
    · rintro ⟨i, -, hx⟩
      exact ⟨jf i, hjf i, cf i, hcf i, (hXw i x).mp hx⟩
  let W := pieceWindowSetupOfFamily g hmK Wp hWh jf cf hjf hcf hinj hjK Xw hXw
    Xwin hsites Xc decomp ak νk βk Datw φw br chain
  have hanT : ∀ (i : ι) (m : ℕ), jf i + 1 ≤ m → m ≤ m' + 1 →
      AnalyticOnNhd ℂ (fun u => (W.chain i).T u m) Set.univ := by
    intro i m _ _
    have : (fun u => (W.chain i).T u m) = fun _ => (W.chain i).T () m :=
      funext fun u => by rw [Subsingleton.elim u ()]
    rw [this]; exact analyticOnNhd_const
  have hanW : ∀ i, AnalyticOnNhd ℂ (fun u => (W.βk : ℂ) *
      actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)) Set.univ := by
    intro i
    have : (fun u => (W.βk : ℂ) * actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)) =
        fun _ => (W.βk : ℂ) * actionRegionC (W.Xw i) W.ak W.νk (W.Datw ()) (W.φw ()) :=
      funext fun u => by rw [Subsingleton.elim u ()]
    rw [this]; exact analyticOnNhd_const
  obtain ⟨C, hC, -, hCb⟩ := window_conversion_pieces W (Kconv := Kconv) (Kbg := Kbg) (γw := γw)
    (M := M₀) (M₁ := M₁) (ε := ε) (Rhat := Rhat) (fun _ m => cs.beta m)
    (fun i m h1 h2 => hanT i m (by omega) h2)
    (fun i m h1 h2 u _ => by simpa only [W, pieceWindowSetupOfFamily] using p7_first i m h1 h2)
    (fun i u _ => by simpa only [W, pieceWindowSetupOfFamily] using window_decay i)
    (fun i => hanW i) hd hL hγ hα₀ hε hγα
    (fun i => hflow i) hKc hKb hγw hsep
  refine ⟨C (), ?_, by simpa only [W, pieceWindowSetupOfFamily] using hCb () (Set.mem_univ _)⟩
  have h1 := hC () (Set.mem_univ _)
  have h2 := congrArg Complex.re h1
  rw [Complex.add_re, Complex.re_sum] at h2
  have h3 : ∀ i, ((chain i).T () (jf i + 1)).re = mainActionLoc g (H.locRH (jf i + 1) (cf i)) (jf i)
      (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) cs (locRH_rem (jf i + 1) (cf i)) (ou i)
      (xu i) hv := by
    intro i
    show ((chain i).T () (jf i + 1)).re = _
    rw [hchain i]
    have hj1 : 1 ≤ jf i := le_trans hk1p (hjf i).1
    exact pieceChain_T g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
      (hjK i) cs (locRH_rem (jf i + 1) (cf i)) hj1 Set.univ (m' + 1) br (Xc i) (hXc i)
      (fun _ => ou i) (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i) (fun _ _ => hS i)
      (by have := (hjf i).2; omega) (Set.mem_univ ())
  simp only [W, pieceWindowSetupOfFamily] at h2
  simp only [h3] at h2
  linarith

/-- An ancestor `Y` of `Z` at a scale `a < b` is an old part of an ancestor `P` of `Z` at scale `a + 1`. -/
theorem exists_part_of_desc {a b : ℕ} (hab : a < b) {Y : H.Comp a} {Z : H.Comp b}
    (h : H.Desc a b Y Z) : ∃ P : H.Comp (a + 1), Y ∈ H.parts a P ∧ H.Desc (a + 1) b P Z := by
  obtain ⟨t, rfl⟩ : ∃ t, b = a + 1 + t := ⟨b - (a + 1), by omega⟩
  clear hab
  induction t with
  | zero =>
    obtain ⟨c, hc, hd⟩ := (desc_succ_iff (le_refl a)).mp h
    have : c = Y := hd.unique (Desc.refl Y)
    subst this
    exact ⟨Z, hc, Desc.refl Z⟩
  | succ t ih =>
    obtain ⟨c, hc, hd⟩ := (desc_succ_iff (by omega : a ≤ a + 1 + t)).mp h
    obtain ⟨P, hP, hPc⟩ := ih hd
    exact ⟨P, hP, (desc_succ_iff (by omega : a + 1 ≤ a + 1 + t)).mpr ⟨c, hc, hPc⟩⟩

/-- The pieces `(j, c)` of the window in the shape of `locOp_absW_le_chain`: the top piece `(m', Z)` and
the pieces `(j, P, c)`, `k₁ ≤ j < m'`, `P` an ancestor of `Z` at scale `j + 2`, `c` an old part of `P`. -/
theorem chain_piece_inj {k1 m' : ℕ} {Z : H.Comp (m' + 1)} :
    Function.Injective fun i : Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
      ↥(H.parts (j.1 + 1) P.1)) =>
      (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩) := by
  rintro (_ | ⟨⟨j, hj⟩, ⟨P, hP⟩, ⟨c, hc⟩⟩) (_ | ⟨⟨j', hj'⟩, ⟨P', hP'⟩, ⟨c', hc'⟩⟩) h
  · rfl
  · have := (Sigma.mk.inj h).1
    have := Finset.mem_Ico.mp hj'
    simp_all
  · have := (Sigma.mk.inj h).1
    have := Finset.mem_Ico.mp hj
    simp_all
  · obtain ⟨hjj, hcc⟩ := Sigma.mk.inj h
    simp only at hjj hcc
    subst hjj
    have hcc := eq_of_heq hcc
    subst hcc
    have hPP : P = P' := RegionHistory.IsSucc.unique (H := H) ((H.mem_parts _ _ _).mp hc).2
      ((H.mem_parts _ _ _).mp hc').2
    subst hPP
    rfl

theorem chain_piece_spec {k1 m' : ℕ} {Z : H.Comp (m' + 1)} (hk1m : k1 ≤ m')
    (i : Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
      ↥(H.parts (j.1 + 1) P.1))) :
    k1 ≤ (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 ∧
    (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 ≤ m' ∧
    (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2 ∈
      H.ancFin ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1)
        (m' + 1) Z := by
  rcases i with _ | ⟨⟨j, hj⟩, ⟨P, hP⟩, ⟨c, hc⟩⟩
  · exact ⟨hk1m, le_rfl, mem_ancFin.mpr (Desc.refl Z)⟩
  · have hj' := Finset.mem_Ico.mp hj
    refine ⟨hj'.1, hj'.2.le, mem_ancFin.mpr ?_⟩
    exact Desc.trans (Desc.single ((H.mem_parts _ _ _).mp hc).1 ((H.mem_parts _ _ _).mp hc).2)
      (mem_ancFin.mp hP)

theorem chain_piece_cover {k1 m' : ℕ} {Z : H.Comp (m' + 1)} (j : ℕ) (c : H.Comp (j + 1))
    (hj1 : k1 ≤ j) (hj2 : j ≤ m') (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) :
    ∃ i : Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
      ↥(H.parts (j.1 + 1) P.1)),
      (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩) = ⟨j, c⟩ := by
  rcases hj2.lt_or_eq with hlt | rfl
  · obtain ⟨P, hP, hd⟩ := exists_part_of_desc (by omega : j + 1 < m' + 1) (mem_ancFin.mp hc)
    exact ⟨some ⟨⟨j, Finset.mem_Ico.mpr ⟨hj1, hlt⟩⟩, ⟨P, mem_ancFin.mpr hd⟩, ⟨c, hP⟩⟩, rfl⟩
  · rw [ancFin_self, Finset.mem_singleton] at hc
    exact ⟨none, by rw [hc]; rfl⟩

end Gen

end Balaban.LargeField
