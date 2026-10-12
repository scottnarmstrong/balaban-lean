module

public import Balaban.LargeField.Operators.Quiet
public import Balaban.LargeField.Operators.KerBound
public import Balaban.LargeField.Operators.Symm

/-!
# Step data and kept data (Part II, Definition II.5.7, block J5)

The large-field operators of a localized history are built from *data*: per localized history
prefix `a` (a `LocalHistory`, so (S4) holds by construction)

* the step kernel `(K_k, b_k)(Z', a)` (`StepData.ker`), an `LFKernel` of the output `ψ_{k+1}|_V` and
  the **new** internal variables `I^new_k` (so it depends on nothing else), with
  (S0) the support of `b_k` in `g|_V`, its bound, its `O(N)`-covariance;
  (S1) `K_k = K^q_k` for quiet steps, the vanishing of `K_k` off the new part `χ^new_k` of the
  domain, and the Gaussian structure
  `K_k = ∏_y z^N t_k(z ψ_{k+1}(y), (Qψ_k)(y)) · ∑_{w∈W} F^w(u) K̃^w` with `K̃^w` independent of
  `ψ_{k+1}|_{Ω^c_{k+1}}` (version 1.2, D-IV.3);
  (S2) the one-step bound: majorants `S^w` of the new′ variables with
  `K̃^w e^{Re b} ≤ S^w` for all values of the old variables and `∑_w m^w ∫ S^w ≤ e^{-κ^{(k)}}`;
* the kept data `(K'', b'')` of a ripe kept component (S3), an `LFKernel` of the output and a
  subset `I''` of the internal variables containing those of the multiscale and fluctuation fields,
  with the bound (1.26) for the exponent `κ'' = κ - C_R λ̂^{2d+1} + γ(ϰ)`.

The properties that involve the history (the bounds, `K_k = K^q_k` for quiet steps, the domain)
are required for the localized histories of admissible region histories.  Euclidean invariance
is `StepData.euclid_*` (symmetries preserving the localized history).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal

section Data

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The volume `|X|_j = L^{-jd} #X` in scale-`j` units of a set of fine sites. -/
noncomputable def volScale (S : Setting) {m : ℕ} (j : ℕ) (X : Set (Torus S.d m)) : ℝ :=
  (Set.ncard X : ℝ) / (S.L : ℝ) ^ (j * S.d)

/-- The new′ internal variables: those of scale `k` other than `ψ_k` on `Z_k ∩ Z'`. -/
def newPrimeVars (a : LocalHistory S n M K) (k : ℕ) : Set (InternalVars a (k + 1)) :=
  {p | p.1.1.val = k ∧ (p.1.2.1 = VarKind.fluct ∨
    BlockSub (S := S) (n := n) (M := M) (K := K) (↑p.1.1) p.1.2.2 (a.Z k)ᶜ)}

theorem newPrimeVars_sub (a : LocalHistory S n M K) (k : ℕ) : newPrimeVars a k ⊆ newVars a k :=
  fun _ hp => hp.1

/-- The output blocks `ψ_{k+1}` on `Ω_{k+1} ∩ Z'` (new′ output variables). -/
def newOutP (a : LocalHistory S n M K) (k : ℕ) (y : BlockAt S n M K (k + 1)) : Prop :=
  BlockSub (S := S) (n := n) (M := M) (K := K) (k + 1) y (a.Z (k + 1)) ∧
    BlockSub (S := S) (n := n) (M := M) (K := K) (k + 1) y (a.Omega k)

/-- The output blocks outside `Z'` (parameters). -/
def parOutP (a : LocalHistory S n M K) (k : ℕ) (y : BlockAt S n M K (k + 1)) : Prop :=
  ¬ BlockSub (S := S) (n := n) (M := M) (K := K) (k + 1) y (a.Z (k + 1))

/-- The new part `χ^new_k(Z')` of the domain of the localized history of a component `Z'` of a
region history `H` (with the generating set `𝔹_K` of the lineage localization), at the
configuration `(o, x)` of the output and the new variables. -/
def ChiNewAt (geo : Geo S n R M) (cs : OpConsts) (H : RegionHistory S n R k0 K) (k : ℕ)
    (Z' : H.Comp (k + 1)) (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) : Prop :=
  ChiNewProp (H.localHistory M K (k + 1) Z') k
    ((H.locRH (k + 1) Z').histGen (M := M) (K' := K) le_rfl (locRH_rem (k + 1) Z') H.F.ok.two_le_L
      (fun j _ _ => geo.hRlow j))
    (fineSet (S := S) (n := n) M K (k + 1) (Z'.1 : Set (Torus S.d (n (k + 1))))) cs.delta cs.p0
    cs.Cpsi
    (subMultiscaleField N (H.localHistory M K (k + 1) Z') (k + 1)
      (Vblk R (H.localHistory M K (k + 1) Z') (k + 1)) x o)
    (subFluctField N (H.localHistory M K (k + 1) Z') (k + 1) x)

/-- The domain condition `χ^dom_k(Z, 𝔞) = 1` of Definition II.3.4 for the localized history of a
component `Z` of a region history `H`, at the configuration `(o, x)` of the output and of the
internal variables in `A`. -/
def ChiDomAt (geo : Geo S n R M) (cs : OpConsts) (H : RegionHistory S n R k0 K) (k : ℕ)
    (Z : H.Comp k) {A : Set (InternalVars (H.localHistory M K k Z) k)}
    (o : OutT N R (H.localHistory M K k Z) k) (x : SubCfg N (H.localHistory M K k Z) k A) :
    Prop :=
  ChiDomProp (H.localHistory M K k Z) k
    ((H.locRH k Z).histGen (M := M) (K' := K) le_rfl (locRH_rem k Z) H.F.ok.two_le_L (fun j _ _ => geo.hRlow j))
    (fineSet (S := S) (n := n) M K k (Z.1 : Set (Torus S.d (n k)))) cs.delta cs.p0 cs.Cpsi
    (subMultiscaleField N (H.localHistory M K k Z) k (Vblk R (H.localHistory M K k Z) k) x o)
    (subFluctField N (H.localHistory M K k Z) k x)

/-- The witnesses `(W, F^w, K̃^w)` of the Gaussian structure (S1). -/
structure GaussWit (N : ℕ) (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ) where
  /-- the finite index set `W` -/
  W : Type
  [fin : Fintype W]
  /-- the Borel functions `F^w : (ℝ^N)^{Ω^c_{k+1} ∩ Z'} → [0,1]` of `u` -/
  F : W → (gaussBlocks a k → EuclideanSpace ℝ (Fin N)) → ℝ
  /-- the factors `K̃^w ≥ 0` -/
  Kt : W → OutT N R a (k + 1) → NewCfg N a k → EuclideanSpace ℝ (Fin N) → ℝ

attribute [instance] GaussWit.fin

open Classical in
/-- `m^w = ∫ ∏_y g_k(u_y) F^w(u) du`, with `g_k` the centred Gaussian density of `t_k`. -/
noncomputable def mWit (N : ℕ) (c : ℝ) (a : LocalHistory S n M K) (k : ℕ) {W : Type}
    (F : W → (gaussBlocks a k → EuclideanSpace ℝ (Fin N)) → ℝ) (w : W) : ℝ≥0∞ :=
  haveI := Fintype.ofFinite (gaussBlocks a k)
  ∫⁻ u, ENNReal.ofReal (∏ y, gaussT N c (u y) 0) * ENNReal.ofReal (F w u)
    ∂(Measure.pi fun _ : gaussBlocks a k => (volume : Measure (EuclideanSpace ℝ (Fin N))))

open Classical in
/-- **(S1) Gaussian structure and (S2) one-step bound** of a step kernel `T` with witnesses
`wit` and exponent `κ`. -/
def GaussStepSpec (cs : OpConsts) (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ) (κ : ℝ)
    (T : LFKernel (OutT N R a (k + 1)) (NewCfg N a k) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N))
    (wit : GaussWit N R a k) : Prop :=
  (∀ w u, 0 ≤ wit.F w u ∧ wit.F w u ≤ 1) ∧
  (∀ w, Measurable (wit.F w)) ∧
  (∀ w o x hv, 0 ≤ wit.Kt w o x hv) ∧
  (∀ w o o' x hv, (∀ y : Vblk R a (k + 1), y.1 ∉ gaussBlocks a k → o y = o' y) →
    wit.Kt w o x hv = wit.Kt w o' x hv) ∧
  (∀ o x hv, T.K o x hv = gaussProd N a k cs o x *
    ∑ w, wit.F w (fun y => gaussArg N (cs.z (k + 1)) o x y.1) * wit.Kt w o x hv) ∧
  ∃ Sw : wit.W → OutPart N (Vblk R a (k + 1)) (newOutP a k) →
      SubCfg N a (k + 1) (newPrimeVars a k) → OutPart N (Vblk R a (k + 1)) (parOutP a k) →
      EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → ℝ≥0∞,
    (∀ w par hv g, Measurable fun q : OutPart N (Vblk R a (k + 1)) (newOutP a k) ×
        SubCfg N a (k + 1) (newPrimeVars a k) => Sw w q.1 q.2 par hv g) ∧
    (∀ w o x hv g, g ∈ l1Ball (GIdx S n M K N) →
      ENNReal.ofReal (wit.Kt w o x hv * Real.exp (T.b o x hv g).re) ≤
        Sw w (restrictOutPart o (newOutP a k)) (restrictSub (newPrimeVars_sub a k) x)
          (restrictOutPart o (parOutP a k)) hv g) ∧
    (∀ par hv g, g ∈ l1Ball (GIdx S n M K N) →
      ∑ w, mWit N (cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) a k wit.F w *
          ∫⁻ q, Sw w q.1 q.2 par hv g
            ∂((outPartMeasure N (Vblk R a (k + 1)) (newOutP a k)).prod
              (subMeasure N a (k + 1) (newPrimeVars a k))) ≤
        ENNReal.ofReal (Real.exp (-κ)))

/-- The step data of Definition II.5.7 (S0)-(S2), indexed by localized prefixes.  `κs k a` is the
exponent `κ^{(k)}(Z', a)` of Definition II.5.11 (block K1). -/
structure StepData (k0 : ℕ) (geo : Geo S n R M) (cs : OpConsts) (N : ℕ)
    (κs : ℕ → LocalHistory S n M K → ℝ) where
  /-- the step kernel `K_k(Z', a)` and boundary factor `b_k(Z', a)` -/
  ker : ∀ (k : ℕ) (a : LocalHistory S n M K),
    LFKernel (OutT N R a (k + 1)) (NewCfg N a k) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N)
  /-- the Gaussian witnesses of (S1) -/
  wit : ∀ (k : ℕ) (a : LocalHistory S n M K), GaussWit N R a k
  /-- (S0) `b_k` depends on `g` only through `g|_V` -/
  b_supp : ∀ k a o x hv (g g' : GIdx S n M K N → ℂ),
    (∀ i : GIdx S n M K N, i.1 ∈ Vsites R a (k + 1) → g i = g' i) →
      (ker k a).b o x hv g = (ker k a).b o x hv g'
  /-- (S0)/(S1) `O(N)`-covariance of the kernel -/
  rot_K : ∀ k a (ρ : OrthN N) o x hv,
    (ker k a).K (rotOut ρ o) (rotSub ρ x) (ρ hv) = (ker k a).K o x hv
  /-- (S0) `O(N)`-covariance of the boundary factor -/
  rot_b : ∀ k a (ρ : OrthN N) o x hv g,
    (ker k a).b (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) = (ker k a).b o x hv g
  /-- (S0)/(S1) Euclidean covariance of the kernel: for a Euclidean symmetry `σ` and the images
  `a' = σ a` of a localized history, corresponding configurations give the same value -/
  euclid_K : ∀ (k : ℕ) (σ : TorusSym S n M K) (a a' : LocalHistory S n M K)
    (hI : HistImage σ a a') (hk : k + 1 ≤ K) o o' x x' hv,
    RelOut σ o o' → RelSub hI hk x x' → (ker k a').K o' x' hv = (ker k a).K o x hv
  /-- (S0) Euclidean covariance of the boundary factor (the external field is transported) -/
  euclid_b : ∀ (k : ℕ) (σ : TorusSym S n M K) (a a' : LocalHistory S n M K)
    (hI : HistImage σ a a') (hk : k + 1 ≤ K) o o' x x' hv g g',
    RelOut σ o o' → RelSub hI hk x x' → RelG σ g g' →
      (ker k a').b o' x' hv g' = (ker k a).b o x hv g
  /-- (S0) the bound `|b_k| ≤ (C_b log β_k + C_b B_0) |Z^c_k ∩ Z'|_{k+1}` on the domain -/
  b_bound : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (k : ℕ)
    (Z' : H.Comp (k + 1)) o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
    ChiNewAt geo cs H k Z' o x →
    ‖(ker k (H.localHistory M K (k + 1) Z')).b o x hv g‖ ≤
      (cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
        volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
          z ∉ (H.localHistory M K (k + 1) Z').Z k}
  /-- (S1) the kernel of a quiet step is the quiet kernel -/
  quiet : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (k : ℕ) (hk : k + 1 ≤ K)
    (Z' : H.Comp (k + 1)), IsQuiet (H.locRH (k + 1) Z') k Z'.1 →
    ∀ o x hv, (ker k (H.localHistory M K (k + 1) Z')).K o x hv =
      quietKernel geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs (locRH_rem (k + 1) Z') o x hv
  /-- (S1) the kernel vanishes off the new part `χ^new_k` of the domain -/
  dom : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (k : ℕ)
    (Z' : H.Comp (k + 1)) o x hv,
    ¬ ChiNewAt geo cs H k Z' o x →
    (ker k (H.localHistory M K (k + 1) Z')).K o x hv = 0
  /-- (S1)-(S2) the Gaussian structure and the one-step bound -/
  gauss : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (k : ℕ) (Z' : H.Comp (k + 1)),
    GaussStepSpec cs R (H.localHistory M K (k + 1) Z') k (κs k (H.localHistory M K (k + 1) Z'))
      (ker k (H.localHistory M K (k + 1) Z')) (wit k (H.localHistory M K (k + 1) Z'))

/-! ### Kept data (S3) -/

/-- The internal variables of the multiscale and fluctuation fields of the history: the
fluctuation variables and the large-field variables on `Λ_j = Ω_j ∖ Ω_{j+1}`. -/
def IsMsFluctVar (a : LocalHistory S n M K) (k : ℕ) (p : InternalVars a k) : Prop :=
  p.1.2.1 = VarKind.fluct ∨ (p.1.2.1 = VarKind.large ∧ (p.1.1.val = 0 ∨
    BlockSub (S := S) (n := n) (M := M) (K := K) (↑p.1.1) p.1.2.2 (a.Omega (↑p.1.1 - 1))))

/-- The kept kernel `(K'', b'')` at a prefix: an `LFKernel` with the output variables of
`𝕋^pre_k(Z, a)` and internal variables `I'' ⊆ I(Z, a)` containing all variables of the
multiscale and fluctuation fields. -/
structure KeptDatum (N : ℕ) (R : ℕ → ℝ) (a : LocalHistory S n M K) (k : ℕ) where
  /-- the internal variables `I''` -/
  Ikeep : Set (InternalVars a k)
  contains : ∀ p : InternalVars a k, IsMsFluctVar a k p → p ∈ Ikeep
  /-- the kept kernel and exponent -/
  ker : LFKernel (OutT N R a k) (SubCfg N a k Ikeep) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N)

/-- The kept data of Definition II.5.7 (S3): per prefix and label `ϰ ∈ 𝔎 = Fin 5`, the kept
kernel; the numbers `C_dec(ϰ) ≥ 1` with `∑ C_dec⁻¹ ≤ 1`; the kept exponents `γ_k(ϰ)` with
`γ - log C_dec ≥ A'_3 λ̂_k^{p_R}`; and, for the localized histories of ripe kept components, the
bound (1.26) with exponent `κ'' = κ_k(Z, a) - C_R λ̂_k^{2d+1} + γ(ϰ)`. -/
structure KeptData (k0 : ℕ) (geo : Geo S n R M) (cs : OpConsts) (N : ℕ)
    (κ : ℕ → LocalHistory S n M K → ℝ) (lamHat : ℕ → ℝ) where
  datum : ∀ (k : ℕ) (a : LocalHistory S n M K), Fin 5 → KeptDatum (S := S) N R a k
  Cdec : Fin 5 → ℝ
  gam : ℕ → Fin 5 → ℝ
  one_le_Cdec : ∀ ϰ, 1 ≤ Cdec ϰ
  sum_inv_Cdec : ∑ ϰ, (Cdec ϰ)⁻¹ ≤ 1
  gam_ge : ∀ k ϰ, S.A3' * lamHat k ^ S.pR ≤ gam k ϰ - Real.log (Cdec ϰ)
  /-- (S0) for the kept boundary factor: support in `g|_V` -/
  b_supp : ∀ k a ϰ o x hv (g g' : GIdx S n M K N → ℂ),
    (∀ i : GIdx S n M K N, i.1 ∈ Vsites R a k → g i = g' i) →
      (datum k a ϰ).ker.b o x hv g = (datum k a ϰ).ker.b o x hv g'
  /-- `O(N)`-covariance of the kept kernel -/
  rot_K : ∀ k a ϰ (ρ : OrthN N) o x hv,
    (datum k a ϰ).ker.K (rotOut ρ o) (rotSub ρ x) (ρ hv) = (datum k a ϰ).ker.K o x hv
  /-- `O(N)`-covariance of the kept boundary factor -/
  rot_b : ∀ k a ϰ (ρ : OrthN N) o x hv g,
    (datum k a ϰ).ker.b (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) =
      (datum k a ϰ).ker.b o x hv g
  /-- Euclidean covariance: the variables `I''` correspond under `σ` -/
  euclid_I : ∀ (k : ℕ) (σ : TorusSym S n M K) (a a' : LocalHistory S n M K)
    (hI : HistImage σ a a') (hk : k ≤ K) (ϰ : Fin 5) (p : InternalVars a k),
    p ∈ (datum k a ϰ).Ikeep ↔ symVar hI hk p ∈ (datum k a' ϰ).Ikeep
  /-- Euclidean covariance of the kept kernel -/
  euclid_K : ∀ (k : ℕ) (σ : TorusSym S n M K) (a a' : LocalHistory S n M K)
    (hI : HistImage σ a a') (hk : k ≤ K) (ϰ : Fin 5) o o' x x' hv,
    RelOut σ o o' → RelSub hI hk x x' → (datum k a' ϰ).ker.K o' x' hv = (datum k a ϰ).ker.K o x hv
  /-- Euclidean covariance of the kept boundary factor -/
  euclid_b : ∀ (k : ℕ) (σ : TorusSym S n M K) (a a' : LocalHistory S n M K)
    (hI : HistImage σ a a') (hk : k ≤ K) (ϰ : Fin 5) o o' x x' hv g g',
    RelOut σ o o' → RelSub hI hk x x' → RelG σ g g' →
      (datum k a' ϰ).ker.b o' x' hv g' = (datum k a ϰ).ker.b o x hv g
  /-- the bound (1.26) of the kept operator (which includes the vanishing off `χ^dom_k`) -/
  bound : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (k : ℕ) (Z : H.Comp k),
    1 ≤ k → k ≤ k0 → S.Ripe k (H.bk k Z) → ∀ ϰ : Fin 5,
    (∀ o x hv, ¬ ChiDomAt geo cs H k Z o x → (datum k (H.localHistory M K k Z) ϰ).ker.K o x hv = 0) ∧
    KerBound (H.localHistory M K k Z) k (datum k (H.localHistory M K k Z) ϰ).ker
      (κ k (H.localHistory M K k Z) - S.CR * lamHat k ^ (2 * S.d + 1) + gam k ϰ)

end Data

end Balaban.LargeField
