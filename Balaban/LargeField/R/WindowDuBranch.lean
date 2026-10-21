/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowHSDom
public import Balaban.LargeField.R.WindowConvR2

/-!
# The mass branch of the window chain (blocker 4, target 0)

P631 §1 prescribes the massless Euler–Lagrange system for the conversions `r - 1 ≤ k₀`.  The landed
class (ruling R2, route R-YM′; `Def7.FieldClauses.muBg_eq`, `muAct_eq`) evaluates the actions at the
complete backgrounds at every scale: the background mass is `ν_j L^{-2j}`.  The chains of the window
(`WindowDuConv`, `WindowDuPt`) are therefore chains of the `complete` branch, and this is the branch the
class supports:

* `FieldClauses.muBg_massless_iff`: the coherence `μ_Bg(q) = br.elMass (μ_act q)` of the pieces of a
  chain (`pieceChain_φ_first`) holds for the massless branch exactly when the physical mass `ν_q`
  vanishes, so the premise `hbr : m' + 1 ≤ k₀ → br = massless` of
  `removedKernel_kerBound_of_hid_action_cl_hS` cannot hold at a call site with a positive mass;
* `windowHS_of_kernel_complete`: both clauses of `hS` for the `complete` branch on the support of the
  kernel, for a unit external field and masses with `2 μ_act(m) L^{2(j_i+1)} < c₁²`
  (`window_pieces_hS`): no inequality between `μ_act(m)` and `μ_Bg(j_i+1)` is used.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization
  ActionConv RegionHistory Balaban.SmallField

section Branch

variable {S : Setting} [NeZero S.L] {cs : OpConsts}

/-- Under the field clauses the background mass at a scale `q ≤ k'` is the massless-branch mass
`0` exactly when the physical mass `ν_q` of the scale vanishes. -/
theorem _root_.Balaban.LargeField.Def7.FieldClauses.muBg_massless_iff {k0 k' m₁ N' : ℕ} {ϱ : ℝ}
    {sf : Def7.SFData S.d S.L m₁ k' N' ϱ} {hv : EuclideanSpace ℝ (Fin N')}
    (h : Def7.FieldClauses S k0 k' cs sf hv) {q : ℕ} (hq : q ≤ k') (x : ℝ) :
    cs.muBg q = MassBranch.massless.elMass x ↔ sf.ν q = 0 := by
  rw [h.muBg_eq q hq]
  have hL : ((S.L : ℝ) ^ (2 * q)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne S.L))
  simp [MassBranch.elMass, hL]

end Branch

section HS

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}
  {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) (hmk : k1 < m' + 1) {Z : H.Comp (m' + 1)}
  (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
  (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)

open Classical in
/-- **`WindowHS` for the complete branch on the support of the kernel**: if the kernel of the operator
of `Z` is nonzero at the window point `(o, x)`, the external field is a unit vector and the masses
satisfy `2 μ_act(m) L^{2(j_i+1)} < c₁²` (the choice of `ν`), then both clauses of `hS` hold for the
pieces of the window with the clause masses of the complete branch. -/
theorem windowHS_of_kernel_complete (hW : H.RipeWindow (m' + 1) Z) (hk1def : S.k1 (m' + 1) = k1)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A) (hv : EuclideanSpace ℝ (Fin N))
    (hK : (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K o x hv ≠ 0)
    (hd : 0 < S.d) (hunit : ‖hv‖ = 1) (hμ0 : ∀ m, 0 ≤ cs.muAct m)
    (hmass : ∀ (i : Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
        ↥(H.parts (j.1 + 1) P.1))) m,
      (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 2 ≤ m →
      m ≤ m' + 1 → 2 * cs.muAct m *
        ((S.L : ℝ) ^ ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1))
          fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1)) ^ 2 < (bgC1 S.d S.L N) ^ 2) :
    WindowHS geo cs SD KD hk1 hm hmk hq ρ MassBranch.complete o x hv := by
  subst hk1def
  unfold WindowHS
  intro ou xu hou0 hxu0 hou1 hxu1 i
  exact window_pieces_hS geo cs SD KD hm hW hq ρ hρ o x hv hK
    (fun i => (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1)
    (fun i => (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)
    (fun _ => rfl) (fun i => ⟨(chain_piece_spec hk1 i).1, (chain_piece_spec hk1 i).2.1⟩)
    (fun i => le_trans (Nat.succ_le_succ (chain_piece_spec hk1 i).2.1) hm) ou xu
    (heq_of_eq hou0) (heq_of_eq hxu0) (fun j P c => heq_of_eq (hou1 j P c))
    (fun j P c => heq_of_eq (hxu1 j P c)) hd hunit hμ0 hmass i

end HS


section MassSize

/-- **The mass-size condition from `β_m ν_m ≤ 1`.**  If `β_m μ_m L^{2m} ≤ 1` (`μ_m = ν_m L^{-2m}`, P5 (1.9)
below the switch) and `β_m > 2/(L² c²)` for some `m ≥ j + 2`, then `2 μ_m L^{2(j+1)} < c²`. -/
theorem mass_size_lt {L : ℕ} (hL : 1 ≤ L) {j m : ℕ} (hjm : j + 2 ≤ m) {c μ b : ℝ} (hc : 0 < c)
    (hμ : 0 ≤ μ) (hb : 2 / ((L : ℝ) ^ 2 * c ^ 2) < b) (hbν : b * (μ * (L : ℝ) ^ (2 * m)) ≤ 1) :
    2 * μ * ((L : ℝ) ^ (j + 1)) ^ 2 < c ^ 2 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hb0 : 0 < b := lt_trans (by positivity) hb
  have hpow : (L : ℝ) ^ 2 * ((L : ℝ) ^ (j + 1)) ^ 2 ≤ (L : ℝ) ^ (2 * m) := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ hL1 (by omega)
  have h1 : b * (μ * ((L : ℝ) ^ 2 * ((L : ℝ) ^ (j + 1)) ^ 2)) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hμ) hb0.le) hbν
  have hc2 : 0 < (L : ℝ) ^ 2 * c ^ 2 := by positivity
  have h2 : 2 < b * ((L : ℝ) ^ 2 * c ^ 2) := by
    rwa [div_lt_iff₀ hc2] at hb
  by_contra hcon
  push Not at hcon
  have h3 : b * (L : ℝ) ^ 2 * (c ^ 2) ≤ b * (L : ℝ) ^ 2 * (2 * μ * ((L : ℝ) ^ (j + 1)) ^ 2) :=
    mul_le_mul_of_nonneg_left hcon (by positivity)
  nlinarith

end MassSize

end Balaban.LargeField
