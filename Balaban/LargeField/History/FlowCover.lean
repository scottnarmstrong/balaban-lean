module

public import Balaban.LargeField.History.StepCover
public import Balaban.LargeField.History.FlowBook

/-!
# Box covers along a region history (Lemma I.4.10 (a), cover; (T1) and (T4))

`CoveredBy k c N`: the set `c` of cubes of `𝕋_k` is covered by at most `N` boxes of side
`≤ crit_k`.  If the non-removed parts of a component `Z'` of `Z^pre_{k+1}` without new cubes
are covered by `ν_i ≥ 1` boxes, `Z'` is covered by `∑ ν_i` boxes (`cover_step`): this is the
cover statement of (T1) (one part, `ν' = ν`) and of (T4) (a merge, `ν' = ∑ ν_i`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

theorem Setting.Ok.cover_side {S : Setting} (ok : S.Ok) (s4 : 4 ≤ S.sS) (k : ℕ) :
    (S.crit k + S.L - 2) / S.L + 1 + 2 * (4 * S.r k) ≤ S.crit (k + 1) := by
  have hc : ((4 : ℕ) : ℝ) + 1 ≤ S.c0 * (1 - 1 / (S.L : ℝ)) := by
    have := ok.c0_sS
    have h4 : (4 : ℝ) ≤ S.sS := by exact_mod_cast s4
    push_cast; linarith
  have := shadow_box_side (L := S.L) (c0 := S.c0) (sS := 4) (r := S.r k) (r' := S.r (k + 1))
    ok.two_le_L hc (ok.two_le_r k) (ok.r_mono (Nat.le_succ k)) (by norm_num)
  unfold Setting.crit Setting.rho
  exact this

/-- `c` is covered by at most `N` boxes of side `≤ crit_k`. -/
def CoveredBy (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (k : ℕ)
    (c : Finset (Torus S.d (n k))) (N : ℕ) : Prop :=
  ∃ B : Finset (Torus S.d (n k) × (Fin S.d → ℕ)), B.card ≤ N ∧
    (∀ b ∈ B, ∀ i, b.2 i ≤ S.crit k) ∧ (c : Set (Torus S.d (n k))) ⊆ ⋃ b ∈ B, box b.1 b.2

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0)

/-- **Lemma I.4.10 (a), cover** for (T1) and (T4): a component of `Z^pre_{k+1}` without new cubes
whose old parts are covered by `ν_c ≥ 1` boxes is covered by `∑ ν_c` boxes. -/
theorem cover_step (k : ℕ) (Z' : H.Comp (k + 1)) (hnew : Z'.1 ∩ H.newCubes (k + 1) = ∅)
    (ν : H.Comp k → ℕ) (hpos : ∀ c ∈ H.parts k Z', 1 ≤ ν c)
    (hcov : ∀ c ∈ H.parts k Z', CoveredBy S n k c.1 (ν c)) :
    CoveredBy S n (k + 1) Z'.1 (∑ c ∈ H.parts k Z', ν c) := by
  classical
  let G : Finset (Torus S.d (n k)) → Prop := fun Y => ∃ c ∈ H.parts k Z', c.1 = Y
  let ν' : Finset (Torus S.d (n k)) → ℕ := fun Y =>
    if h : Y ∈ comps (S.omega k) (H.Zp k) then ν ⟨Y, h⟩ else 0
  let bxc : H.Comp k → Finset (Torus S.d (n k) × (Fin S.d → ℕ)) := fun c =>
    if hc : c ∈ H.parts k Z' then (hcov c hc).choose else ∅
  let bx : Finset (Torus S.d (n k)) → Finset (Torus S.d (n k) × (Fin S.d → ℕ)) := fun Y =>
    if h : Y ∈ comps (S.omega k) (H.Zp k) then bxc ⟨Y, h⟩ else ∅
  have hν' : ∀ c : H.Comp k, ν' c.1 = ν c := fun c => by simp only [ν', c.2, ↓reduceDIte]
  have hbx' : ∀ c : H.Comp k, bx c.1 = bxc c := fun c => by simp only [bx, c.2, ↓reduceDIte]
  have hOC : (H.step k).OldCover G (S.omega k) (S.crit k) ν' bx := by
    have key : ∀ c ∈ H.parts k Z', (bxc c).card ≤ ν c ∧ (∀ b ∈ bxc c, ∀ i, b.2 i ≤ S.crit k) ∧
        (c.1 : Set (Torus S.d (n k))) ⊆ ⋃ b ∈ bxc c, box b.1 b.2 := by
      intro c hc
      simp only [bxc, hc, ↓reduceDIte]
      exact (hcov c hc).choose_spec
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro _ _ ⟨c, hc, rfl⟩
      rw [hν', hbx']; exact (key c hc).1
    · rintro _ _ ⟨c, hc, rfl⟩
      rw [hbx']; exact (key c hc).2.1
    · rintro _ _ ⟨c, hc, rfl⟩
      rw [hbx']; exact (key c hc).2.2
    · rintro _ _ ⟨c, hc, rfl⟩
      rw [hν']; exact hpos c hc
  have hG : ∀ Y ∈ (H.step k).oldIn (S.omega k) Z'.1, G Y := by
    intro Y hY
    rw [← H.parts_image] at hY
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hY
    exact ⟨c, hc, rfl⟩
  have hcrit : ∀ b, critOpt S k0 (k + 1) = some b → b ≤ S.crit (k + 1) := by
    intro b hb
    unfold critOpt at hb
    split_ifs at hb
    · cases hb; exact le_rfl
  obtain ⟨B, h1, h2, h3⟩ := (H.step k).exists_step_cover (G := G) (H.stepGeom k) hOC
    (H.F.ok.cover_side H.F.s4 k) hcrit Z'.2 (by rw [← H.inter_newCubes]; exact hnew) hG
  refine ⟨B, ?_, h2, h3⟩
  have hsum : ∑ c ∈ H.parts k Z', ν c = ∑ Y ∈ (H.step k).oldIn (S.omega k) Z'.1, ν' Y := by
    rw [← H.parts_sum k Z' ν']
    exact Finset.sum_congr rfl fun c _ => (hν' c).symm
  rw [hsum]
  exact h1

end RegionHistory

end Balaban.LargeField
