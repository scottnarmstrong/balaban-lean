module

public import Balaban.LargeField.History.RegionHistory
import Mathlib.Tactic.Linarith

/-!
# Spines and bookkeeping of a region history (Part I, Definitions I.4.6-I.4.7)

For a `RegionHistory` the spine of every component of `Z^pre_k` is defined by recursion on `k`:
at `k = 0` there are no components, and the spine of a component `Z'` of `Z^pre_{k+1}` is a spine
`Γ'` given by Lemma I.4.8 (`RegionStep.exists_step_spine`) from the spines of the components of
`Z_k` (chosen by `Classical.choose` among the spines with the properties `SpineOK`).  The books
are `Setting.nextBook` of the post-`R` books of the parts.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0)

theorem parts_image (k : ℕ) (Z' : H.Comp (k + 1)) :
    (H.parts k Z').image Subtype.val = (H.step k).oldIn (S.omega k) Z'.1 := by
  classical
  ext Y
  simp only [Finset.mem_image, RegionStep.oldIn, Finset.mem_filter, H.mem_parts]
  constructor
  · rintro ⟨c, ⟨hc, hs⟩, rfl⟩
    exact ⟨H.comp_mem_Z hc, (H.succ_eq_iff k hc).mp hs⟩
  · rintro ⟨hY, hsub⟩
    obtain ⟨hY1, hY2⟩ := (H.mem_comps_Z k).mp hY
    refine ⟨⟨Y, hY1⟩, ⟨hY2, (H.succ_eq_iff k hY2).mpr hsub⟩, rfl⟩

theorem parts_card (k : ℕ) (Z' : H.Comp (k + 1)) :
    (H.parts k Z').card = ((H.step k).oldIn (S.omega k) Z'.1).card := by
  rw [← H.parts_image, Finset.card_image_of_injective _ Subtype.val_injective]

theorem parts_sum (k : ℕ) (Z' : H.Comp (k + 1)) (g : Finset (Torus S.d (n k)) → ℝ) :
    ∑ c ∈ H.parts k Z', g c.1 = ∑ Y ∈ (H.step k).oldIn (S.omega k) Z'.1, g Y := by
  rw [← H.parts_image, Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]

theorem inter_newCubes (k : ℕ) (Z' : H.Comp (k + 1)) :
    Z'.1 ∩ H.newCubes (k + 1) = (H.step k).newIn Z'.1 := rfl

/-- The properties of the spine `Γ'` of a component `Z'` of `Z^pre_{k+1}`, given the spines `Γs`
of the components of `Z^pre_k` (Lemma I.4.8): (3.1), (4.1), and the pure-shadow rule. -/
def SpineOK (k : ℕ) (Γs : H.Comp k → Spine S.d) (Z' : H.Comp (k + 1)) (Γ' : Spine S.d) : Prop :=
  (Z'.1 : Set (Torus S.d (n (k + 1)))) ⊆ NR ((S.rho (k + 1) : ℝ) + 4) (Γ'.proj (n (k + 1))) ∧
  Γ'.length ≤ ∑ c ∈ H.parts k Z', (Γs c).length / S.L +
      ((((H.parts k Z').card + (Z'.1 ∩ H.newCubes (k + 1)).card : ℕ) : ℝ) - 1) * S.D (k + 1) ∧
  ((Z'.1 ∩ H.newCubes (k + 1)).card = 0 → ∀ c, H.parts k Z' = {c} → (Γs c).length ≤ S.L →
    Γ'.length = 0)

theorem _root_.Balaban.LargeField.critOpt_le (S : Setting) (k0 k : ℕ) :
    ∀ b, critOpt S k0 (k + 1) = some b → b ≤ 2 * S.rho (k + 1) + 10 := by
  intro b hb
  unfold critOpt at hb
  split_ifs at hb
  · cases hb; exact le_rfl

/-- **Lemma I.4.8** for a region history: the spines of the components of `Z_k` with
`Z ⊆ N_{ρ_k+4}(Γ)` give spines for the components of `Z^pre_{k+1}`. -/
theorem exists_spineOK (k : ℕ) (Γs : H.Comp k → Spine S.d)
    (h : ∀ c : H.Comp k, (c.1 : Set (Torus S.d (n k))) ⊆
      NR ((S.rho k : ℝ) + 4) ((Γs c).proj (n k))) (Z' : H.Comp (k + 1)) :
    ∃ Γ', H.SpineOK k Γs Z' Γ' := by
  classical
  let Γs' : Finset (Torus S.d (n k)) → Spine S.d := fun Y =>
    if hY : Y ∈ comps (S.omega k) (H.Zp k) then Γs ⟨Y, hY⟩ else Spine.point 0
  have hΓ : (H.step k).OldSpined Γs' (S.omega k) (S.rho k) := by
    intro Y hY
    obtain ⟨hY1, -⟩ := (H.mem_comps_Z k).mp hY
    have : Γs' Y = Γs ⟨Y, hY1⟩ := by simp only [Γs', hY1, ↓reduceDIte]
    rw [this]
    exact h ⟨Y, hY1⟩
  obtain ⟨Γ', h1, h2, h3⟩ := (H.step k).exists_step_spine Γs' (H.stepGeom k)
    (H.F.ok.spineNum H.F.s4 H.F.s5 k) hΓ (crit := critOpt S k0 (k + 1)) (critOpt_le S k0 k)
    (Z' := Z'.1) Z'.2
  refine ⟨Γ', h1, ?_, ?_⟩
  · have e1 : ∑ c ∈ H.parts k Z', (Γs c).length / S.L =
        ∑ Y ∈ (H.step k).oldIn (S.omega k) Z'.1, (Γs' Y).length / S.L := by
      rw [← H.parts_sum k Z' (fun Y => (Γs' Y).length / S.L)]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Γs', c.2, ↓reduceDIte]
    rw [e1, H.parts_card, H.inter_newCubes]
    exact h2
  · intro hnew c hc hL
    have hcmem : c ∈ H.parts k Z' := by rw [hc]; exact Finset.mem_singleton_self c
    have hY : c.1 ∈ (H.step k).oldIn (S.omega k) Z'.1 := by
      rw [← H.parts_image]; exact Finset.mem_image_of_mem _ hcmem
    refine h3 ?_ (by rw [← H.inter_newCubes]; exact hnew) c.1 hY ?_
    · rw [← H.parts_card, hc]; simp
    · have : Γs' c.1 = Γs c := by simp only [Γs', c.2, ↓reduceDIte]
      rw [this]; exact hL

open Classical in
/-- The spine of a component of `Z^pre_{k+1}`, given the spines at scale `k`. -/
noncomputable def nextSpine (k : ℕ) (Γs : H.Comp k → Spine S.d) (Z' : H.Comp (k + 1)) :
    Spine S.d :=
  if h : ∃ Γ', H.SpineOK k Γs Z' Γ' then h.choose else Spine.point 0

/-- The spines of the components of `Z^pre_k` (Definition I.4.7). -/
noncomputable def spine : ∀ k, H.Comp k → Spine S.d
  | 0 => fun _ => Spine.point 0
  | k + 1 => H.nextSpine k (spine k)

/-- The bookkeeping of the components of `Z^pre_k` (Definition I.4.6). -/
noncomputable def bk : ∀ k, H.Comp k → Book
  | 0 => fun c => { st := .pre, s := 0, len := (H.spine 0 c).length,
                    pt := (H.spine 0 c).length = 0 }
  | k + 1 => fun Z' => S.nextBook (k + 1) (H.parts k Z')
      (fun c => S.postBook k0 k (bk k c)) (Z'.1 ∩ H.newCubes (k + 1)).card (H.spine (k + 1) Z')

theorem spine_contains : ∀ k, ∀ c : H.Comp k, (c.1 : Set (Torus S.d (n k))) ⊆
    NR ((S.rho k : ℝ) + 4) ((H.spine k c).proj (n k)) := by
  intro k
  induction k with
  | zero => exact fun c => (H.F.isEmpty_comp_zero.false c).elim
  | succ k ih =>
    intro Z'
    classical
    have h := H.exists_spineOK k (H.spine k) ih Z'
    have : H.spine (k + 1) Z' = h.choose := by
      show H.nextSpine k (H.spine k) Z' = _
      unfold nextSpine
      simp only [h, ↓reduceDIte]
    rw [this]
    exact h.choose_spec.1

theorem spineOK_spine (k : ℕ) (Z' : H.Comp (k + 1)) :
    H.SpineOK k (H.spine k) Z' (H.spine (k + 1) Z') := by
  classical
  have h := H.exists_spineOK k (H.spine k) (H.spine_contains k) Z'
  have : H.spine (k + 1) Z' = h.choose := by
    show H.nextSpine k (H.spine k) Z' = _
    unfold nextSpine
    simp only [h, ↓reduceDIte]
  rw [this]
  exact h.choose_spec

theorem bk_len (k : ℕ) (c : H.Comp k) : (H.bk k c).len = (H.spine k c).length := by
  cases k <;> rfl

theorem bk_pt (k : ℕ) (c : H.Comp k) : (H.bk k c).pt = ((H.spine k c).length = 0) := by
  cases k <;> rfl

theorem postBook_len (k : ℕ) (b : Book) : (S.postBook k0 k b).len = b.len := by
  unfold Setting.postBook; split_ifs <;> rfl

theorem postBook_pt (k : ℕ) (b : Book) : (S.postBook k0 k b).pt = b.pt := by
  unfold Setting.postBook; split_ifs <;> rfl

theorem book_rule (k : ℕ) (Z' : H.Comp (k + 1)) :
    S.BookRule (k + 1) (k + 1 ≤ k0) (H.parts k Z') (fun c => S.postBook k0 k (H.bk k c))
      (Z'.1 ∩ H.newCubes (k + 1)).card (H.bk (k + 1) Z') := by
  obtain ⟨-, h2, h3⟩ := H.spineOK_spine k Z'
  refine S.nextBook_rule (k + 1) (k + 1 ≤ k0) (H.parts k Z') _ _ (H.spine (k + 1) Z') ?_ ?_ ?_
  · simp only [postBook_len, bk_len]
    exact h2
  · intro hr c hc hL
    simp only [postBook_len, bk_len] at hL
    exact h3 hr c hc hL
  · intro c _ hp
    rw [postBook_pt, bk_pt] at hp
    rw [postBook_len, bk_len]
    exact hp

/-- Every component of `Z^pre_{k+1}` contains a seed: one old part or one new cube. -/
theorem seed_pos (k : ℕ) (Z' : H.Comp (k + 1)) :
    1 ≤ (H.parts k Z').card + (Z'.1 ∩ H.newCubes (k + 1)).card := by
  have hg := H.stepGeom k
  have hcont : ∃ C0 ∈ comps (S.omega (k + 1)) (finOf (H.step k).Z0), C0 ⊆ Z'.1 := by
    have hZ' : Z'.1 ∈ comps (S.omega (k + 1))
        (finOf ((H.step k).Zpre (S.omega (k + 1)) (critOpt S k0 (k + 1)))) := Z'.2
    by_cases hk : k + 1 ≤ k0
    · have hc : critOpt S k0 (k + 1) = some (S.crit (k + 1)) := by simp [critOpt, hk]
      rw [hc] at hZ'
      exact hullClosure_comp_contains hg.hω2 (H.step k).Z0 hZ'
    · have hc : critOpt S k0 (k + 1) = none := by simp [critOpt, hk]
      rw [hc] at hZ'
      exact ⟨Z'.1, hZ', subset_rfl⟩
  have h := (H.step k).seedsIn_card_pos hg hcont
  rw [(H.step k).card_seedsIn] at h
  rwa [H.parts_card, H.inter_newCubes]

/-- The removed components are ripe (Definition I.4.1). -/
def Admissible : Prop := ∀ k, ∀ c : H.Comp k, c.1 ∈ H.rem k → S.Ripe k (H.bk k c)

open Classical in
/-- The removed components as a finset of components. -/
noncomputable def remC (k : ℕ) : Finset (H.Comp k) := Finset.univ.filter fun c => c.1 ∈ H.rem k

theorem mem_remC (k : ℕ) (c : H.Comp k) : c ∈ H.remC k ↔ c.1 ∈ H.rem k := by
  classical
  simp [remC]

end RegionHistory

end Balaban.LargeField
