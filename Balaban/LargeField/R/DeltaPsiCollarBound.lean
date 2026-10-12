module

public import Balaban.LargeField.R.DeltaPsiCollar
public import Balaban.LargeField.R.DeltaPsiCore
import Mathlib.Tactic.Linarith

/-!
# The data-change bound on all data sites and the inner-collar path bound (COLLAR-FIX §§2-3)

* `DataChangeBound'`: the bound on `δψ′` on `Ω₁(G)` and on the whole collar `C_G`, the form of the
  hypothesis of P3 Proposition 2.1 that uses the corrected `deltaPsiColl`; it is inhabited
  (`dataChangeBound'_nonempty`) and implies the landed `DataChangeBound` when the child and parent
  layers agree on `Ω₁(G)` and the collar is off `Ω₁(B)` (`dataChangeBound_of_prime`);
* `dataChangeBound'_of_pieces`: `DataChangeBound'` from the bound on `Ω₁(G)`, the exact outer identity
  (2.1) and the inner-collar bound (2.3);
* `core_shell_path_bound`, `inner_collar_shell_bound`: COLLAR-FIX (2.2), the bound
  `|ψ_{k₁}(b_{k₁}(c)) - ψ_{k₁}(y)| ≤ (m_W + 1) C_reg δ_{k₁}` along the regularity path.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

section DCB

variable (W : WindowPieces d L N₀ k ϱ) (hWh : W.Hyp) (href : ParentRefines (W.windowGenSet hWh) W.full)
  (hprec : Precedes (W.windowGenSet hWh) W.bdry) (a : ℕ → ℝ)
  (ψ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)

/-- **`DataChangeBound′`** (COLLAR-FIX §3): `|δψ′| ≤ τ_{n(x)}` on `Ω₁(G)` and `≤ τ₁` on the whole collar,
for the corrected `deltaPsiColl` (the difference of the two actual `BgData.Ψ` fields on all data sites). -/
def DataChangeBound' (τ : ℕ → ℝ) : Prop :=
  (∀ x ∈ (W.windowGenSet hWh).Ω 1,
      vn (deltaPsiColl W hWh href hprec a ψ ψ0 h x) ≤ τ ((W.windowGenSet hWh).layerIndex x)) ∧
    ∀ c ∈ collar (W.windowGenSet hWh), vn (deltaPsiColl W hWh href hprec a ψ ψ0 h c) ≤ τ 1

/-- The landed `DataChangeBound` follows when the parent and window layers agree on `Ω₁(G)` and the collar
lies off `Ω₁(B)`. -/
theorem dataChangeBound_of_prime {τ : ℕ → ℝ} (hD : DataChangeBound' W hWh href hprec a ψ ψ0 h τ)
    (hlay : ∀ x ∈ (W.windowGenSet hWh).Ω 1,
      W.full.layerIndex x = (W.windowGenSet hWh).layerIndex x)
    (hcol : ∀ c ∈ collar (W.windowGenSet hWh), c ∉ W.full.Ω 1) :
    DataChangeBound (W.windowGenSet hWh) W.bdry a ψ ψ0 h τ := by
  refine ⟨fun x hx => ?_, fun c hc => ?_⟩
  · have e : deltaPsiColl W hWh href hprec a ψ ψ0 h x =
        deltaPsi (W.windowGenSet hWh) W.bdry a ψ ψ0 h x :=
      funext fun i => deltaPsiColl_eq_deltaPsi W hWh href hprec a ψ ψ0 h hx (hlay x hx) i
    rw [← e]; exact hD.1 x hx
  · have e : deltaPsiColl W hWh href hprec a ψ ψ0 h c =
        fun i => ((psiTilde (W.windowGenSet hWh) ψ c i : ℝ) : ℂ) -
          psiZeroWin (W.windowGenSet hWh) W.bdry a ψ0 h c i :=
      funext fun i => deltaPsiColl_collar_eq_of_not_mem W hWh href hprec a ψ ψ0 h hc (hcol c hc) i
    rw [← e]; exact hD.2 c hc

/-- **`DataChangeBound′` from its pieces**: the bound on `Ω₁(G)`, the exact identity (2.1) on the outer collar
(its premises `hk`, `hOmK1`, `hsupp`, `hOmK`, `hoff` as in `deltaPsiColl_eq_zero_outer`) and the inner-collar
bound (2.3). -/
theorem dataChangeBound'_of_pieces {τ : ℕ → ℝ} (hτ1 : 0 ≤ τ 1) (hk : 1 ≤ k)
    (hOmK1 : ∀ x, x ∉ W.Zk1 → x ∈ W.full.Ω 1) (hsupp : ∀ x ∈ W.bdry.Ω 1, x ∈ W.Unb)
    (hOmK : ∀ x, x ∉ W.Z → x ∈ W.full.Ω k)
    (hoff : ∀ x ∈ dataSites W.bdry, x ∉ W.Z →
      ψ0 ⟨k, jBlock d L N₀ k k x⟩ = ψ ⟨k, jBlock d L N₀ k k x⟩)
    (hΩ : ∀ x ∈ (W.windowGenSet hWh).Ω 1,
      vn (deltaPsiColl W hWh href hprec a ψ ψ0 h x) ≤ τ ((W.windowGenSet hWh).layerIndex x))
    (hin : ∀ c ∈ collarIn W hWh, vn (deltaPsiColl W hWh href hprec a ψ ψ0 h c) ≤ τ 1) :
    DataChangeBound' W hWh href hprec a ψ ψ0 h τ := by
  refine ⟨hΩ, fun c hc => ?_⟩
  by_cases hcZ : c ∈ W.Zk1
  · exact hin c ((mem_collarIn W hWh).2 ⟨hc, hcZ⟩)
  · have hz : deltaPsiColl W hWh href hprec a ψ ψ0 h c = 0 :=
      funext fun i => deltaPsiColl_eq_zero_outer W hWh href hprec a ψ ψ0 h hk hOmK1 hsupp hOmK hoff
        ((mem_collarOut W hWh).2 ⟨hc, hcZ⟩) i
    rw [hz, vn_zero]; exact hτ1

end DCB

/-- The sample window pieces: the parent refines the window generating set. -/
theorem sample_parentRefines :
    ParentRefines ((WindowPieces.sample : WindowPieces d L N₀ k ϱ).windowGenSet
      WindowPieces.sample_hyp) (WindowPieces.sample : WindowPieces d L N₀ k ϱ).full :=
  window_parent_refines _ _ (fun n _ _ => by simp [WindowPieces.sample])
    (fun n _ _ => by simp [WindowPieces.sample])

theorem sample_Ω (n : ℕ) :
    ((WindowPieces.sample : WindowPieces d L N₀ k ϱ).windowGenSet WindowPieces.sample_hyp).Ω n =
      (WindowPieces.sample : WindowPieces d L N₀ k ϱ).full.Ω n := by
  rw [WindowPieces.windowGenSet_Ω]
  simp [WindowPieces.sample]

/-- `DataChangeBound′` is inhabited (the sample pieces, the zero fields, `τ ≥ 0`). -/
theorem dataChangeBound'_nonempty (hk : 1 ≤ k) {a : ℕ → ℝ} (ha : a k ≠ 0) {τ : ℕ → ℝ}
    (hτ : ∀ n, 0 ≤ τ n) (h : Fin N → ℝ) :
    ∃ (W : WindowPieces d L N₀ k ϱ) (hWh : W.Hyp) (href : ParentRefines (W.windowGenSet hWh) W.full)
      (hprec : Precedes (W.windowGenSet hWh) W.bdry)
      (ψ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)),
      DataChangeBound' W hWh href hprec a ψ ψ0 h τ := by
  classical
  have hprec : Precedes ((WindowPieces.sample : WindowPieces d L N₀ k ϱ).windowGenSet
      WindowPieces.sample_hyp) (WindowPieces.sample : WindowPieces d L N₀ k ϱ).bdry := by
    intro i hi hik x _
    simp [WindowPieces.sample, singleGen_Ω hik]
  refine ⟨WindowPieces.sample, WindowPieces.sample_hyp, sample_parentRefines, hprec,
    fun _ => 0, fun _ => 0, ?_, ?_⟩
  · intro x hx
    have hxZ : x ∈ (WindowPieces.sample : WindowPieces d L N₀ k ϱ).Z := by
      simp [WindowPieces.sample]
    have hxc : x ∉ (WindowPieces.sample : WindowPieces d L N₀ k ϱ).Zk1 := by
      simp [WindowPieces.sample]
    rw [deltaPsiColl_eq_deltaPsi_outer _ _ _ _ _ _ _ _ hx hxZ hxc |> fun e => funext e]
    have hlay : ((WindowPieces.sample : WindowPieces d L N₀ k ϱ).windowGenSet
        WindowPieces.sample_hyp).layerIndex x = k := by
      refine GeneratingSet.layerIndex_eq _ hk le_rfl ?_
      rw [GeneratingSet.mem_layer, sample_Ω, sample_Ω]
      simp [WindowPieces.sample, singleGen_Ω, singleGen_Ω_succ]
    have hlay' : (WindowPieces.sample : WindowPieces d L N₀ k ϱ).bdry.layerIndex x = k := by
      refine GeneratingSet.layerIndex_eq _ hk le_rfl ?_
      rw [GeneratingSet.mem_layer]
      simp [WindowPieces.sample, singleGen_Ω, singleGen_Ω_succ]
    have hxd : x ∈ dataSites (WindowPieces.sample : WindowPieces d L N₀ k ϱ).bdry :=
      (mem_dataSites _).2 (Or.inl (by simp [WindowPieces.sample, singleGen_Ω hk]))
    have hd0 : deltaPsi ((WindowPieces.sample : WindowPieces d L N₀ k ϱ).windowGenSet
        WindowPieces.sample_hyp) (WindowPieces.sample : WindowPieces d L N₀ k ϱ).bdry a
        (fun _ => 0) (fun _ => 0) h x = 0 := by
      funext i
      have hz : psiZeroWin ((WindowPieces.sample : WindowPieces d L N₀ k ϱ).windowGenSet
          WindowPieces.sample_hyp) (WindowPieces.sample : WindowPieces d L N₀ k ϱ).bdry a
          (fun _ => (0 : EuclideanSpace ℝ (Fin N))) h x i = 0 := by
        unfold psiZeroWin
        rw [composeField_eq_data_top _ _ hx ha hlay hlay' i]
        unfold psiZeroData
        rw [liftSingle_Ψ _ _ _ hxd]
        simp
      rw [deltaPsi_of_mem _ _ _ _ _ _ hx i, hz, psiTilde_of_mem _ _ hx i]
      simp
    rw [hd0, vn_zero]
    exact hτ _
  · intro c hc
    obtain ⟨hc1, -⟩ := (mem_collar _).1 hc
    exact absurd (by rw [sample_Ω]; simp [WindowPieces.sample, singleGen_Ω hk]) hc1

/-! ### The path bound (2.2) -/

section PathBound

variable {B : GeneratingSet d L N₀ k ϱ'} {Zc : Finset (Torus d (N₀ * L ^ k))} {k1 : ℕ}
  {T : Set (Torus d (N₀ * L ^ (k - k1)))}

/-- **`core_shell_path_bound`** (COLLAR-FIX (2.2)): along a path of `m` adjacent `k₁`-blocks in the regularity set
`T`, on which adjacent values of `ψ_{k₁}` differ by at most `C_reg δ_{k₁}` (the retained (1.24) band: `C_reg
= 3dL e^ε L^{(d-2)/2}`, or `3` for the stronger regularity of Lemma III.4.6), the value at the start is within
`m C_reg δ_{k₁}` of the value at the window block at the end. -/
theorem core_shell_path_bound (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) {Creg δ1 : ℝ}
    (hT : ∀ y ∈ T, ∀ y' ∈ T, AdjT y y' → ‖ψ ⟨k1, y⟩ - ψ ⟨k1, y'⟩‖ ≤ Creg * δ1)
    {b : Torus d (N₀ * L ^ (k - k1))} {m : ℕ} (hp : TPathToWindow B Zc k1 T b m) :
    ∃ s ∈ B.layer k1, s ∉ Zc ∧
      dist (ψ ⟨k1, b⟩) (ψ (blockOf d L N₀ k k1 s)) ≤ m * (Creg * δ1) := by
  obtain ⟨u, hu0, huT, huA, s, hs, hsZ, hsu⟩ := hp
  refine ⟨s, hs, hsZ, ?_⟩
  have hbond : ∀ i < m, dist ((fun v => ψ ⟨k1, v⟩) (u i)) ((fun v => ψ ⟨k1, v⟩) (u (i + 1))) ≤
      Creg * δ1 := fun i hi => by
    rw [dist_eq_norm]
    exact hT _ (huT i hi.le) _ (huT (i + 1) hi) (huA i hi)
  have hw := dist_walk_le (fun v => ψ ⟨k1, v⟩) u hbond
  simp only [hu0] at hw
  have e : blockOf d L N₀ k k1 s = ⟨k1, u m⟩ := by simp only [blockOf]; rw [hsu]
  rw [e]
  exact hw

end PathBound

/-- **Inner-collar shell bound** (COLLAR-FIX (2.2) at a collar site): for `c ∈ C_in`, the parent spin
`ψ_{k₁}(b_{k₁}(c))` read by the physical datum is within `(m_W + 1) C_reg δ_{k₁}` of the spin of a window
block `s ∈ Λ_{k₁}(B) ∖ Z_{k₁}`.  The premises are those of `inner_collar_in_regular_T` and the
band regularity `hT`. -/
theorem inner_collar_shell_bound (W : WindowPieces d L N₀ k ϱ) (hWh : W.Hyp) {k1 : ℕ}
    (hk1 : 1 ≤ k1) (hk1k : k1 ≤ k) (T : Set (Torus d (N₀ * L ^ (k - k1)))) (mW : ℕ)
    (hZ : W.Zk1 ⊆ W.Z)
    (hcoreTop : ∀ x ∈ W.Zk1, x ∈ W.core.Ω 1 → x ∈ W.core.layer k1)
    (hreach : ∀ x ∈ W.core.layer k1, x ∈ W.Zk1 → ∃ m ≤ mW, TPathToWindow W.full W.Zk1 k1 T
      (jBlock d L N₀ k k1 x) m)
    (hexitLayer : ∀ x ∈ (W.windowGenSet hWh).Ω 1, x ∉ W.Zk1 → ∀ c, Adj x c → c ∈ W.Zk1 →
      x ∈ W.full.layer k1)
    (hcT : ∀ c ∈ collarIn W hWh, jBlock d L N₀ k k1 c ∈ T)
    (hwT : ∀ x ∈ (W.windowGenSet hWh).Ω 1, x ∉ W.Zk1 → x ∈ W.full.layer k1 →
      jBlock d L N₀ k k1 x ∈ T)
    (hmargin : ∀ x ∈ (W.windowGenSet hWh).Ω 1, ∀ c, Adj x c → c ∈ W.Zk1 → c ∈ W.full.Ω k1)
    (hZk1top : ∀ x ∈ W.Zk1, x ∉ W.full.Ω (k1 + 1))
    (ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) {Creg δ1 : ℝ}
    (hC : 0 ≤ Creg * δ1)
    (hT : ∀ y ∈ T, ∀ y' ∈ T, AdjT y y' → ‖ψ ⟨k1, y⟩ - ψ ⟨k1, y'⟩‖ ≤ Creg * δ1)
    {c : Torus d (N₀ * L ^ k)} (hc : c ∈ collarIn W hWh) :
    ∃ s ∈ W.full.layer k1, s ∉ W.Zk1 ∧
      dist (ψ (parentBlock W.full c)) (ψ (blockOf d L N₀ k k1 s)) ≤ (mW + 1) * (Creg * δ1) := by
  obtain ⟨m, hm, hp⟩ := inner_collar_in_regular_T W hWh hk1k T mW hZ hcoreTop hreach hexitLayer hcT hwT hc
  obtain ⟨s, hs, hsZ, hd⟩ := core_shell_path_bound ψ hT hp
  refine ⟨s, hs, hsZ, ?_⟩
  rw [(inner_collar_parent_layer W hWh hk1 hk1k hmargin hZk1top hc).2.2]
  have e : blockOf d L N₀ k k1 c = ⟨k1, jBlock d L N₀ k k1 c⟩ := rfl
  rw [e]
  refine hd.trans ?_
  have : (m : ℝ) ≤ mW + 1 := by exact_mod_cast hm
  nlinarith

end Balaban.LargeField
