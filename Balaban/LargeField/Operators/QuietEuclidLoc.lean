module

public import Balaban.LargeField.Region.SymmStep
public import Balaban.LargeField.Region.SymmLevel
public import Balaban.LargeField.Operators.QuietEuclidChi
public import Balaban.LargeField.Operators.QuietEuclidDom
public import Balaban.LargeField.Operators.QuietSymmEuclid
public import Balaban.LargeField.Operators.ActionSymm
public import Balaban.LargeField.Background.LiftSymm
public import Balaban.LargeField.Operators.Quiet
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The local background and the main action under lattice symmetries

Let `σ` be a lattice symmetry (`LatTorusSym`) mapping the region history `Hl` to `Hl'`
(`RegionIso`) and the component `Zc` to `Zc'`.  On the level-`q` torus of the characteristic functions
`σ` acts by the affine isometry `LatTorusSym.levAff`.  Then:

* the generating set `G^{Z'}_{k+1}` of the local background is mapped to that of `Zc'`
  (`locGen_latSymm`), the history generating set `𝔹_{k+1}` likewise (`histGenLevel_latSymm`);
* the lifted data, the local background and the field `φ̄` correspond (`locData_sym`, `locBg_sym`,
  `locPhi_sym`);
* the main action is invariant (`mainActionLoc_euclid`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory

section Level

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L]

theorem levEq (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {q : ℕ}
    (hqK : q ≤ K) : g.M1 * (g.c * n q) * S.L ^ q = M * n K * S.L ^ K := by
  have := histScale_eq (n := n) (L := S.L) (M1 := g.M1) (c := g.c) (M := M) (K := K) g.hM hnn
    (Nat.zero_le q) hqK
  simpa using this

/-- The action of `σ` on the level-`q` torus of the characteristic functions. -/
def LatTorusSym.levAff (σ : LatTorusSym S n M K) (g : Geo S n R M)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {q : ℕ} (hqK : q ≤ K) :
    AffIso S.d (g.M1 * (g.c * n q) * S.L ^ q) :=
  σ.aff.cast (levEq g hnn hqK).symm

theorem LatTorusSym.levAff_aligned (σ : LatTorusSym S n M K) (g : Geo S n R M)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {q : ℕ} (hqK : q ≤ K) :
    (σ.levAff g hnn hqK).Aligned (g.c * g.M1 * S.L ^ q) := by
  refine AffIso.cast_aligned _ _ (AffIso.Aligned.mono _ σ.align ?_)
  have e : M * S.L ^ K = (g.c * g.M1) * S.L ^ K :=
    congrArg (· * S.L ^ K) g.hM
  rw [e]
  exact Nat.mul_dvd_mul_left _ (pow_dvd_pow S.L hqK)

theorem AffIso.coarse_target_cast {d ℓ m m' : ℕ} (A : AffIso d ℓ) (P : ℕ) (h : m = m') :
    (A.coarse P m).cast h = A.coarse P m' := by
  subst h; rfl

theorem torusCast_coarse {d ℓ m m' : ℕ} (A : AffIso d ℓ) (P : ℕ) (h : m = m') (z : Torus d m) :
    torusCast h ((A.coarse P m).toFun z) = (A.coarse P m').toFun (torusCast h z) := by
  rw [← AffIso.cast_toFun, AffIso.coarse_target_cast]

theorem torusCast_levAff_coarse (σ : LatTorusSym S n M K) (g : Geo S n R M)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {q i : ℕ} (hiq : i ≤ q) (hqK : q ≤ K)
    (z : Torus S.d (g.M1 * (g.c * n q) * S.L ^ (q - i))) :
    torusCast (histScale_eq g.hM hnn hiq hqK)
      (((σ.levAff g hnn hqK).coarse (S.L ^ i) (g.M1 * (g.c * n q) * S.L ^ (q - i))).toFun z) =
      σ.eb i (torusCast (histScale_eq g.hM hnn hiq hqK) z) := by
  unfold LatTorusSym.levAff
  rw [AffIso.coarse_cast, torusCast_coarse _ _ (histScale_eq g.hM hnn hiq hqK),
    σ.eb_eq (hiq.trans hqK)]

/-- The transported block configuration of a field with `f' ∘ σ.eb = f`. -/
theorem blockCfgOf_euclid (σ : LatTorusSym S n M K) (g : Geo S n R M)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {q i : ℕ} (hiq : i ≤ q) (hqK : q ≤ K) {N : ℕ}
    (f f' : BlockAt S n M K i → EuclideanSpace ℝ (Fin N)) (hf : ∀ y, f' (σ.eb i y) = f y)
    (z : Torus S.d (g.M1 * (g.c * n q) * S.L ^ (q - i))) :
    blockCfgOf g hnn hiq hqK f'
        (((σ.levAff g hnn hqK).coarse (S.L ^ i) (g.M1 * (g.c * n q) * S.L ^ (q - i))).toFun z) =
      blockCfgOf g hnn hiq hqK f z := by
  funext j
  unfold blockCfgOf
  have : torusCast (histScale_eq g.hM hnn hiq hqK)
      (((σ.levAff g hnn hqK).coarse (S.L ^ i) (g.M1 * (g.c * n q) * S.L ^ (q - i))).toFun z) =
      σ.eb i (torusCast (histScale_eq g.hM hnn hiq hqK) z) := by
    unfold LatTorusSym.levAff
    rw [AffIso.coarse_cast, torusCast_coarse _ _ (histScale_eq g.hM hnn hiq hqK),
      σ.eb_eq (hiq.trans hqK)]
  rw [this, hf]

theorem LatTorusSym.ec_eq_geo (σ : LatTorusSym S n M K) (g : Geo S n R M)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {q j : ℕ} (hqK : q ≤ K) (hjK : j ≤ K)
    (y : Torus S.d (n j)) :
    σ.ec j y = ((σ.levAff g hnn hqK).coarse (S.L ^ j * (g.c * g.M1)) (n j)).toFun y := by
  have e : S.L ^ j * M = S.L ^ j * (g.c * g.M1) := congrArg (S.L ^ j * ·) g.hM
  unfold LatTorusSym.levAff
  rw [AffIso.coarse_cast, ← e]
  exact σ.ec_eq hnn hjK y

end Level

section Loc

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (σ : LatTorusSym S n M K) (g : Geo S n R M)
  {Hl Hl' : RegionHistory S n R k0 K} (hiso : RegionIso σ Hl Hl') (k : ℕ)
  {Zc Zc' : Finset (Torus S.d (n (k + 1)))}
  (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hZc' : Zc' ∈ comps (S.omega (k + 1)) (Hl'.F.Zp (k + 1))) (hk : k + 1 ≤ K)
  (hZ : (Zc' : Set (Torus S.d (n (k + 1)))) = σ.ec (k + 1) '' (Zc : Set (Torus S.d (n (k + 1)))))
include hiso hZ

theorem locGen_map :
    ∀ m, (locGen g Hl' k Zc' hZc' hk).Ω m =
      ((locGen g Hl k Zc hZc hk).Ω m).map (σ.levAff g Hl.F.hnn hk).toEquiv.toEmbedding := by
  have hnn := Hl.F.hnn
  have hal := σ.levAff_aligned g hnn hk
  unfold locGen
  refine genBoundaryLocal_map hal (hnn k (by omega)) (Hl.step k) (Hl'.step k) g.hc _ _ _ _ _ _ _
    ?_ ?_ ?_
  · rw [hiso.hZ k (by omega)]
    exact Set.image_congr (fun y _ => σ.ec_eq_geo g hnn hk (by omega) y)
  · rw [hiso.omega hk]
    exact (Set.image_congr (fun y _ => (σ.ec_eq_geo g hnn hk hk y)))
  · rw [hZ]
    exact (Set.image_congr (fun y _ => (σ.ec_eq_geo g hnn hk hk y)))

/-- The lattice symmetry between the local generating sets. -/
noncomputable def locGen_latSymm :
    LatSymm (locGen g Hl k Zc hZc hk) (locGen g Hl' k Zc' hZc' hk)
      (σ.levAff g Hl.F.hnn hk).toEquiv :=
  (σ.levAff g Hl.F.hnn hk).latSymm
    (AffIso.Aligned.mono _ (σ.levAff_aligned g Hl.F.hnn hk) ⟨g.c * g.M1, by ring⟩)
    (locGen_map σ g hiso k hZc hZc' hk hZ)

theorem fineK1_omega_map :
    fineK1 g.M1 g.c (n (k + 1)) S.L k (Hl'.step k).Omega =
      (fineK1 g.M1 g.c (n (k + 1)) S.L k (Hl.step k).Omega).map
        (σ.levAff g Hl.F.hnn hk).toEquiv.toEmbedding := by
  have hnn := Hl.F.hnn
  rw [fineK1_map (σ.levAff_aligned g hnn hk) (hnn k (by omega)), hiso.omega hk]
  congr 1
  exact (Set.image_congr (fun y _ => σ.ec_eq_geo g hnn hk hk y))

end Loc

section LocData

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (σ : LatTorusSym S n M K) (g : Geo S n R M)
  {Hl Hl' : RegionHistory S n R k0 K} (hiso : RegionIso σ Hl Hl') (k : ℕ)
  {Zc Zc' : Finset (Torus S.d (n (k + 1)))}
  (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hZc' : Zc' ∈ comps (S.omega (k + 1)) (Hl'.F.Zp (k + 1))) (hk : k + 1 ≤ K)
  (hZ : (Zc' : Set (Torus S.d (n (k + 1)))) = σ.ec (k + 1) '' (Zc : Set (Torus S.d (n (k + 1)))))
  (hI : HistImage σ.toTorusSym (locHist Hl M K (k + 1) Zc) (locHist Hl' M K (k + 1) Zc'))
  {o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1)}
  {o' : OutT N R (locHist Hl' M K (k + 1) Zc') (k + 1)}
  {x : NewCfg N (locHist Hl M K (k + 1) Zc) k} {x' : NewCfg N (locHist Hl' M K (k + 1) Zc') k}
  (ho : RelOut (k := k + 1) σ.toTorusSym o o') (hx : RelVal hI hk x x')
  (hv : EuclideanSpace ℝ (Fin N))
include hiso hZ ho hx

theorem locData_sym :
    (locGen_latSymm σ g hiso k hZc hZc' hk hZ).sym (locData g Hl k Zc hZc hk o x hv) =
      locData g Hl' k Zc' hZc' hk o' x' hv := by
  have hnn := Hl.F.hnn
  have hal := σ.levAff_aligned g hnn hk
  have hq : (σ.levAff g hnn hk).Aligned (S.L ^ (k + 1)) :=
    AffIso.Aligned.mono _ hal ⟨g.c * g.M1, by ring⟩
  have hsub : RelSub hI hk x x' := ⟨subCorr_newVars hI hk, hx⟩
  unfold locData
  refine (locGen_latSymm σ g hiso k hZc hZc' hk hZ).liftMixed_sym _ _ _ _
    (fun y => ?_) (((σ.levAff g hnn hk).coarse (S.L ^ k) _).toEquiv)
    (((σ.levAff g hnn hk).coarse (S.L ^ (k + 1)) _).toEquiv)
    (fun y => jBlock_aff0 _ hq (Nat.le_succ k) y) (fun y => jBlock_aff0 _ hq le_rfl y)
    _ _ (fun y => ?_) _ _ (fun y => ?_) _
  · have h := fineK1_omega_map σ g hiso k hk hZ
    rw [h, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  · funext i
    show ((blockCfgOf g Hl'.F.hnn (Nat.le_succ k) hk (subVarField N x' k)
      (((σ.levAff g hnn hk).coarse (S.L ^ k) _).toFun y) i : ℝ) : ℂ) = _
    rw [blockCfgOf_euclid σ g hnn (Nat.le_succ k) hk (subVarField N x k) (subVarField N x' k)
      (fun y => hsub.read_large k y) y]
    rfl
  · funext i
    show ((blockCfgOf g Hl'.F.hnn le_rfl hk (outField N o')
      (((σ.levAff g hnn hk).coarse (S.L ^ (k + 1)) _).toFun y) i : ℝ) : ℂ) = _
    rw [blockCfgOf_euclid σ g hnn le_rfl hk (outField N o) (outField N o') (fun y => ho y) y]
    rfl

variable (cs : OpConsts)

theorem locBg_sym :
    locBg g Hl' k Zc' hZc' hk cs o' x' hv =
      (locGen_latSymm σ g hiso k hZc hZc' hk hZ).fld (locBg g Hl k Zc hZc hk cs o x hv) := by
  have h1 := ((locGen_latSymm σ g hiso k hZc hZc' hk hZ).bgFieldC_sym cs.aw (cs.mu (k + 1))
    (bgC0 S.d S.L N) (locData g Hl k Zc hZc hk o x hv)).1
  rw [locData_sym σ g hiso k hZc hZc' hk hZ hI ho hx hv] at h1
  exact h1

theorem locPhi_sym (z : Site S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1)) :
    locPhi g Hl' k Zc' hZc' hk cs o' x' hv ((σ.levAff g Hl.F.hnn hk).toEquiv z) =
      locPhi g Hl k Zc hZc hk cs o x hv z := by
  unfold locPhi
  refine congrArg (WithLp.toLp 2) (funext fun i => ?_)
  have h := (locGen_latSymm σ g hiso k hZc hZc' hk hZ).barField_sym
    (locData g Hl k Zc hZc hk o x hv) (locBg g Hl k Zc hZc hk cs o x hv) z i
  rw [locData_sym σ g hiso k hZc hZc' hk hZ hI ho hx hv,
    ← locBg_sym σ g hiso k hZc hZc' hk hZ hI ho hx hv cs] at h
  exact congrArg Complex.re h

end LocData


section Action

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (σ : LatTorusSym S n M K) (g : Geo S n R M)
  {Hl Hl' : RegionHistory S n R k0 K} (hiso : RegionIso σ Hl Hl') (k : ℕ) (hk : k + 1 ≤ K)
  (hrem : ∀ j, Hl.rem j = ∅) (hrem' : ∀ j, Hl'.rem j = ∅)

theorem histEq (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hk : k + 1 ≤ K) :
    M * n K * S.L ^ K = M * n (k + 1) * S.L ^ (k + 1) := by
  have : S.L ^ K = S.L ^ (K - (k + 1)) * S.L ^ (k + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [nn_eq_pow' hnn hk, this]; ring

include hiso in
theorem histGenLevel_map :
    ∀ j, (histGenLevel g Hl' k hk hrem').Ω j =
      ((histGenLevel g Hl k hk hrem).Ω j).map (σ.levAff g Hl.F.hnn hk).toEquiv.toEmbedding := by
  intro j
  have hnn := Hl.F.hnn
  let A : AffIso S.d (M * n (k + 1) * S.L ^ (k + 1)) := σ.aff.cast (histEq hnn hk)
  have hal : A.Aligned (M * S.L ^ (k + 1)) :=
    AffIso.cast_aligned _ _ (AffIso.Aligned.mono _ σ.align (Nat.mul_dvd_mul_left _
      (pow_dvd_pow S.L hk)))
  have hG : ∀ j, (Hl'.histGen (M := M) (K' := k + 1) hk hrem' Hl'.F.ok.two_le_L
      (fun j _ _ => g.hRlow j)).Ω j = ((Hl.histGen (M := M) (K' := k + 1) hk hrem Hl.F.ok.two_le_L
      (fun j _ _ => g.hRlow j)).Ω j).map A.toEquiv.toEmbedding := by
    intro j
    refine flowOmega_map (Hl.toSeq hk hrem) (Hl'.toSeq hk hrem') (fun i hi => hnn i (by omega)) A
      hal ?_ j
    intro j' hj'
    cases j' with
    | zero => simp [RegionSeq.OmegaAt]
    | succ i =>
      show (Hl'.F.step i).Omega = _ '' (Hl.F.step i).Omega
      rw [hiso.omega (by omega)]
      exact Set.image_congr (fun y _ => by
        have := σ.ec_eq hnn (by omega : i + 1 ≤ K) y
        rw [this]
        exact congrArg (fun B => B.toFun y) (AffIso.coarse_cast _ σ.aff _ _).symm)
  unfold histGenLevel
  have h : M * n (k + 1) = g.M1 * (g.c * n (k + 1)) :=
    (congrArg (· * n (k + 1)) g.hM).trans (by ring)
  have := castGen_map h A hG j
  rw [this]
  congr 2
  unfold LatTorusSym.levAff
  rw [AffIso.cast_cast]


include hiso in
theorem Xfine_map {Zc Zc' : Finset (Torus S.d (n (k + 1)))}
    (hZ : (Zc' : Set (Torus S.d (n (k + 1)))) = σ.ec (k + 1) '' (Zc : Set (Torus S.d (n (k + 1))))) :
    Xfine g Hl' k Zc' = (Xfine g Hl k Zc).map (σ.levAff g Hl.F.hnn hk).toEquiv.toEmbedding := by
  have hnn := Hl.F.hnn
  have hal := σ.levAff_aligned g hnn hk
  unfold Xfine
  rw [Finset.map_sdiff, fineK1_map hal (hnn k (by omega)), fineK_map hal (hnn k (by omega)), hZ,
    hiso.hZ k (by omega)]
  congr 2
  · exact (Set.image_congr (fun y _ => σ.ec_eq_geo g hnn hk hk y))
  · exact (Set.image_congr (fun y _ => σ.ec_eq_geo g hnn hk (by omega) y))

theorem psiLevel_euclid (ψ ψ' : MultiField S n M K N) (hψ : ∀ j y, ψ' j (σ.eb j y) = ψ j y)
    (m : ℕ) (y : Blk S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) m) :
    psiLevel g Hl' k hk ψ' m
        (((σ.levAff g Hl.F.hnn hk).coarse (S.L ^ m)
          (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - m))).toFun y) = psiLevel g Hl k hk ψ m y := by
  unfold psiLevel
  by_cases hm : m ≤ k + 1
  · simp only [hm, ↓reduceDIte]
    rw [torusCast_levAff_coarse σ g Hl.F.hnn hm hk y, hψ]
  · simp [hm]

end Action


section MainAction

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (σ : LatTorusSym S n M K) (g : Geo S n R M)
  {Hl Hl' : RegionHistory S n R k0 K} (hiso : RegionIso σ Hl Hl') (k : ℕ)
  {Zc Zc' : Finset (Torus S.d (n (k + 1)))}
  (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hZc' : Zc' ∈ comps (S.omega (k + 1)) (Hl'.F.Zp (k + 1))) (hk : k + 1 ≤ K)
  (hZ : (Zc' : Set (Torus S.d (n (k + 1)))) = σ.ec (k + 1) '' (Zc : Set (Torus S.d (n (k + 1)))))
  (hI : HistImage σ.toTorusSym (locHist Hl M K (k + 1) Zc) (locHist Hl' M K (k + 1) Zc'))
  {o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1)}
  {o' : OutT N R (locHist Hl' M K (k + 1) Zc') (k + 1)}
  {x : NewCfg N (locHist Hl M K (k + 1) Zc) k} {x' : NewCfg N (locHist Hl' M K (k + 1) Zc') k}
  (ho : RelOut (k := k + 1) σ.toTorusSym o o') (hx : RelVal hI hk x x')
  (hv : EuclideanSpace ℝ (Fin N)) (cs : OpConsts)
  (hrem : ∀ j, Hl.rem j = ∅) (hrem' : ∀ j, Hl'.rem j = ∅)
include hiso hZ ho hx

/-- **Lemma II.5.10, lattice part, for the main action**: `𝒜_{k+1}(Z'; ψ)` is invariant under a
lattice symmetry mapping the history, the component, the output and the new internal variables. -/
theorem mainActionLoc_euclid :
    mainActionLoc g Hl' k Zc' hZc' hk cs hrem' o' x' hv =
      mainActionLoc g Hl k Zc hZc hk cs hrem o x hv := by
  have hnn := Hl.F.hnn
  have hal := σ.levAff_aligned g hnn hk
  have hq : (σ.levAff g hnn hk).Aligned (S.L ^ (k + 1)) :=
    AffIso.Aligned.mono _ hal ⟨g.c * g.M1, by ring⟩
  have hsub : RelSub hI hk x x' := ⟨subCorr_newVars hI hk, hx⟩
  let SG := (σ.levAff g hnn hk).latSymm hq (histGenLevel_map σ g hiso k hk hrem hrem')
  have hX := Xfine_map σ g hiso k hk hZ
  have hφ : locPhi g Hl' k Zc' hZc' hk cs o' x' hv =
      fun z => locPhi g Hl k Zc hZc hk cs o x hv ((σ.levAff g hnn hk).toEquiv.symm z) := by
    funext z
    obtain ⟨w, rfl⟩ := (σ.levAff g hnn hk).toEquiv.surjective z
    rw [locPhi_sym σ g hiso k hZc hZc' hk hZ hI ho hx hv cs, Equiv.symm_apply_apply]
  have hact : actionG (histGenLevel g Hl' k hk hrem') cs.aw (cs.muAct (k + 1)) hv
      (Xfine g Hl' k Zc')
      (psiLevel g Hl' k hk (subMultiscaleField N (locHist Hl' M K (k + 1) Zc') (k + 1)
        (Vblk R (locHist Hl' M K (k + 1) Zc') (k + 1)) x' o'))
      (locPhi g Hl' k Zc' hZc' hk cs o' x' hv) =
      actionG (histGenLevel g Hl k hk hrem) cs.aw (cs.muAct (k + 1)) hv (Xfine g Hl k Zc)
      (psiLevel g Hl k hk (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
        (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) x o))
      (locPhi g Hl k Zc hZc hk cs o x hv) := by
    rw [hX, hφ]
    exact SG.actionG_sym cs.aw (cs.muAct (k + 1)) hv (Xfine g Hl k Zc)
      (fun m => ((σ.levAff g hnn hk).coarse (S.L ^ m)
        (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - m))).toEquiv)
      (fun m _ _ y => jBlock_aff0 _ hq (by omega) y) _ _
      (fun m y => psiLevel_euclid σ g k hk _ _
        (fun j y => subMultiscaleField_euclid hk ho hsub j y) m y) _
  have hbond : starBondE (Xfine g Hl' k Zc') (locPhi g Hl' k Zc' hZc' hk cs o' x' hv) =
      starBondE (Xfine g Hl k Zc) (locPhi g Hl k Zc hZc hk cs o x hv) := by
    rw [hX, hφ]
    exact SG.starBondE_sym _ _
  unfold mainActionLoc
  rw [hact, hbond]

end MainAction

end Balaban.LargeField
