module

public import Balaban.LargeField.R.ChainGraph
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Linarith

/-!
# From a site path to a chain (Part III, Lemma III.4.4, chain existence)

A nearest-neighbour path of fine sites whose sites except the last lie in window layers
`i₀ ≤ i < k` outside the core and whose last site lies in `Ω_k ∩ Z` gives a path in the chain graph
from the window block of the first site to a terminal block, all of whose vertices except the last
are window blocks of layers `≥ i₀`, visiting every vertex at most once (a shortest chain).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Multiscale

section Extract

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
  (Zc Zf : Set (Torus d (N₀ * L ^ k))) (k1 i0 : ℕ)

/-- The window blocks of layers `≥ i₀`. -/
def WinSet : Set (BlockV d L N₀ k) := {b | IsWindowBlock G Zc k1 b ∧ i0 ≤ b.1}

/-- The chain graph restricted to the window blocks of layers `≥ i₀`. -/
def winGraph : SimpleGraph ↥(WinSet G Zc k1 i0) := (chainGraph G Zc Zf k1).induce (WinSet G Zc k1 i0)

variable {G Zc Zf k1 i0}

theorem layerIndex_eq' {i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer i) : G.layerIndex x = i := G.layerIndex_eq hi hik hx

/-- **Chain existence (Lemma III.4.4, first part)**. -/
theorem exists_chain (hϱ : 1 ≤ ϱ) (hk1 : 1 ≤ k1) (hi0 : k1 ≤ i0)
    (hblk : ∀ x x', jBlock d L N₀ k k1 x = jBlock d L N₀ k k1 x' → (x ∈ Zc ↔ x' ∈ Zc))
    (hΩ : ∀ x ∈ Zc, x ∉ G.Ω (k1 + 1))
    (hZf : ∀ x x', jBlock d L N₀ k k x = jBlock d L N₀ k k x' → (x ∈ Zf ↔ x' ∈ Zf))
    {N : ℕ} (hN : 0 < N) (p : ℕ → Torus d (N₀ * L ^ k)) (hadj : ∀ m < N, NNAdj (p m) (p (m + 1)))
    (hwin : ∀ m < N, ∃ i, i0 ≤ i ∧ i < k ∧ p m ∈ G.layer i ∧ p m ∉ Zc)
    (hend : p N ∈ G.Ω k ∧ p N ∈ Zf) :
    ∃ (len : ℕ) (x : ℕ → BlockV d L N₀ k),
      x 0 = blockOf d L N₀ k (G.layerIndex (p 0)) (p 0) ∧
      (∀ m < len, IsWindowBlock G Zc k1 (x m) ∧ i0 ≤ (x m).1) ∧
      IsTerminalBlock G Zf (x len) ∧
      (∀ m < len, (chainGraph G Zc Zf k1).Adj (x m) (x (m + 1))) ∧
      (∀ m ≤ len, ∀ m' ≤ len, x m = x m' → m = m') := by
  classical
  have hk : 1 ≤ k := by
    obtain ⟨i, h1, h2, -⟩ := hwin 0 hN
    omega
  -- the window blocks of the path sites
  have hmemW : ∀ m < N, blockOf d L N₀ k (G.layerIndex (p m)) (p m) ∈ WinSet G Zc k1 i0 := by
    intro m hm
    obtain ⟨i, hi1, hi2, hl, hZ⟩ := hwin m hm
    rw [layerIndex_eq' (by omega) hi2.le hl]
    exact ⟨isWindowBlock_blockOf G hblk hΩ hk1 (by omega) hi2 hl hZ, hi1⟩
  have hlayer : ∀ m < N, ∃ i, i0 ≤ i ∧ i < k ∧ p m ∈ G.layer i ∧ G.layerIndex (p m) = i := by
    intro m hm
    obtain ⟨i, hi1, hi2, hl, hZ⟩ := hwin m hm
    exact ⟨i, hi1, hi2, hl, layerIndex_eq' (by omega) hi2.le hl⟩
  -- one step: equal or adjacent
  have hstep : ∀ m, m + 1 < N →
      blockOf d L N₀ k (G.layerIndex (p m)) (p m) =
        blockOf d L N₀ k (G.layerIndex (p (m + 1))) (p (m + 1)) ∨
      (chainGraph G Zc Zf k1).Adj (blockOf d L N₀ k (G.layerIndex (p m)) (p m))
        (blockOf d L N₀ k (G.layerIndex (p (m + 1))) (p (m + 1))) := by
    intro m hm
    obtain ⟨i, hi1, hi2, hl, hli⟩ := hlayer m (by omega)
    obtain ⟨i', hi1', hi2', hl', hli'⟩ := hlayer (m + 1) hm
    rw [hli, hli']
    have hnn := hadj m (by omega)
    have hW := hmemW m (by omega)
    have hW' := hmemW (m + 1) hm
    rw [hli] at hW
    rw [hli'] at hW'
    obtain ⟨h1, h2, h3⟩ := nn_layers_adj G hϱ hnn (by omega) hi2.le (by omega) hi2'.le hl hl'
    have hchain : IsChainVertex G Zc Zf k1 (blockOf d L N₀ k i (p m)) := Or.inl hW.1
    have hchain' : IsChainVertex G Zc Zf k1 (blockOf d L N₀ k i' (p (m + 1))) := Or.inl hW'.1
    by_cases hii : i = i'
    · subst hii
      by_cases hbb : blockOf d L N₀ k i (p m) = blockOf d L N₀ k i (p (m + 1))
      · exact Or.inl hbb
      · exact Or.inr ⟨hchain, hchain', Or.inl ⟨rfl, hbb, p m, rfl, p (m + 1), rfl, hnn⟩⟩
    · rcases (show i = i' + 1 ∨ i' = i + 1 by omega) with h | h
      · exact Or.inr ⟨hchain, hchain', Or.inr (Or.inl (h3 h))⟩
      · have h3' := (nn_layers_adj G hϱ (nnAdj_symm' hnn) (by omega) hi2'.le (by omega) hi2.le hl' hl).2.2 h
        exact Or.inr ⟨hchain, hchain', Or.inr (Or.inr h3')⟩
  -- reachability in the window graph
  have hreach : ∀ n (hn : n < N), (winGraph G Zc Zf k1 i0).Reachable
      ⟨blockOf d L N₀ k (G.layerIndex (p 0)) (p 0), hmemW 0 hN⟩
      ⟨blockOf d L N₀ k (G.layerIndex (p n)) (p n), hmemW n hn⟩ := by
    intro n
    induction n with
    | zero => intro _; exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      intro hn
      refine (ih (by omega)).trans ?_
      rcases hstep n hn with h | h
      · have : (⟨blockOf d L N₀ k (G.layerIndex (p n)) (p n), hmemW n (by omega)⟩ :
            ↥(WinSet G Zc k1 i0)) = ⟨blockOf d L N₀ k (G.layerIndex (p (n + 1))) (p (n + 1)),
              hmemW (n + 1) hn⟩ := Subtype.ext h
        rw [this]
      · exact SimpleGraph.Adj.reachable (by
          show (chainGraph G Zc Zf k1).Adj _ _
          exact h)
  -- the last window block is adjacent to the terminal block
  set T : BlockV d L N₀ k := blockOf d L N₀ k k (p N) with hT
  have hTterm : IsTerminalBlock G Zf T :=
    isTerminalBlock_blockOf G hk hZf hend.1 hend.2
  have hlast : (chainGraph G Zc Zf k1).Adj
      (blockOf d L N₀ k (G.layerIndex (p (N - 1))) (p (N - 1))) T := by
    obtain ⟨i, hi1, hi2, hl, hli⟩ := hlayer (N - 1) (by omega)
    have hnn := hadj (N - 1) (by omega)
    have hN1 : N - 1 + 1 = N := by omega
    rw [hN1] at hnn
    have hlk : p N ∈ G.layer k := by
      rw [G.mem_layer]
      exact ⟨hend.1, by rw [G.top]; simp⟩
    obtain ⟨h1, h2, h3⟩ := nn_layers_adj G hϱ (nnAdj_symm' hnn) (by omega) le_rfl (by omega) hi2.le hlk hl
    have hik : k = i + 1 := by omega
    rw [hli]
    refine ⟨Or.inl (hmemW (N - 1) (by omega) |> fun h => by rw [hli] at h; exact h.1), Or.inr hTterm, ?_⟩
    exact Or.inr (Or.inr (h3 hik))
  -- a path in the window graph
  obtain ⟨w⟩ := hreach (N - 1) (by omega)
  set P := w.bypass with hP
  have hPpath : P.IsPath := w.bypass_isPath
  refine ⟨P.length + 1, fun m => if m ≤ P.length then (P.getVert m).1 else T, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Nat.zero_le, ite_true]
    have := P.getVert_zero
    rw [this]
  · intro m hm
    have hm' : m ≤ P.length := by omega
    simp only [hm', ite_true]
    exact (P.getVert m).2
  · simp only [show ¬ (P.length + 1 ≤ P.length) by omega, ite_false]
    exact hTterm
  · intro m hm
    by_cases hmP : m < P.length
    · have hm1 : m + 1 ≤ P.length := hmP
      simp only [hmP.le, hm1, ite_true]
      exact (P.adj_getVert_succ hmP)
    · have hmeq : m = P.length := by omega
      subst hmeq
      simp only [le_refl, ite_true, show ¬ (P.length + 1 ≤ P.length) by omega, ite_false]
      rw [P.getVert_length]
      exact hlast
  · intro m hm m' hm' he
    by_cases hmP : m ≤ P.length <;> by_cases hmP' : m' ≤ P.length
    · simp only [hmP, hmP', ite_true] at he
      exact hPpath.getVert_injOn hmP hmP' (Subtype.ext he)
    · simp only [hmP, hmP', ite_true, ite_false] at he
      exfalso
      have h1 := (((P.getVert m).2).1).2.1
      have h2 := hTterm.1
      have h3 : (P.getVert m).1.1 = T.1 := congrArg Sigma.fst he
      omega
    · simp only [hmP, hmP', ite_true, ite_false] at he
      exfalso
      have h1 := (((P.getVert m').2).1).2.1
      have h2 := hTterm.1
      have h3 : T.1 = (P.getVert m').1.1 := congrArg Sigma.fst he
      omega
    · omega

end Extract

end Balaban.LargeField
