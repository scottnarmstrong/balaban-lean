module

public import Balaban.LargeField.History.Branch

/-!
# The core at scale `q` (Lemma I.4.13 (e4))

For `Z` of scale `k ≤ k₀`, `Active` or `Pending` with core `q`, every ancestor of `Z` at scale `q`
is one box of side `≤ crit_q` (`core_box`), and distinct ancestors are at distance `≥ ω_q`
(`core_sep`).

The proof follows Lemma I.4.13 (e4): the branch of an ancestor `Y` at scale `q` is a chain of
pure shadows from an event `W` (`back`); if `W` is a merge (T4) at scale `ξ`, its record `ξ` is
either still in `𝓜(Z) ⊂ (q, k]` or has been released with core `> ξ + h_ξ` (`recInv_liveDesc`),
so `ξ + h_ξ < q`; the spine length `≤ ν_max D_ξ ≤ L^{h_ξ}` of `W` is divided by `L` at each of the
`q - ξ > h_ξ` pure shadows and the spine of `Y` becomes a point, which is a box
(Lemma I.4.8, `cover_of_pt`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

theorem Setting.Ok.numax_D_le_pow {S : Setting} (ok : S.Ok) (ξ : ℕ) :
    (S.numax ξ : ℝ) * S.D ξ ≤ (S.L : ℝ) ^ S.h ξ := by
  have hL := ok.cast_L_ge
  have hL1 : (1 : ℝ) < S.L := by linarith
  set A : ℝ := 2 * Real.sqrt S.d * S.numax ξ * S.M * (S.crit ξ + S.omega ξ) with hA
  have hA1 : 1 ≤ A := ok.h_arg_ge ξ
  have h1 : A ≤ (S.L : ℝ) ^ ⌈Real.logb S.L A⌉₊ := by
    have h2 : A ≤ (S.L : ℝ) ^ (⌈Real.logb S.L A⌉₊ : ℝ) := by
      calc A = (S.L : ℝ) ^ (Real.logb S.L A) := (Real.rpow_logb (by linarith) (by linarith)
            (by linarith)).symm
        _ ≤ (S.L : ℝ) ^ (⌈Real.logb S.L A⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1.le (Nat.le_ceil _)
    rwa [Real.rpow_natCast] at h2
  have h2 : (S.numax ξ : ℝ) * S.D ξ ≤ A := by
    unfold Setting.D Setting.crit at *
    have hM : (1 : ℝ) ≤ S.M := by exact_mod_cast ok.one_le_M
    have hs : 0 ≤ Real.sqrt S.d := Real.sqrt_nonneg _
    have hn : (0 : ℝ) ≤ S.numax ξ := Nat.cast_nonneg _
    have hc : (0 : ℝ) ≤ 2 * S.rho ξ + 10 + S.omega ξ := by positivity
    have e : (S.numax ξ : ℝ) * (Real.sqrt S.d * (2 * S.rho ξ + 10 + S.omega ξ)) =
        Real.sqrt S.d * S.numax ξ * (2 * S.rho ξ + 10 + S.omega ξ) := by ring
    rw [e, hA]
    push_cast
    have : Real.sqrt S.d * S.numax ξ * (2 * S.rho ξ + 10 + S.omega ξ) ≥ 0 := by positivity
    nlinarith
  calc (S.numax ξ : ℝ) * S.D ξ ≤ A := h2
    _ ≤ (S.L : ℝ) ^ ⌈Real.logb S.L A⌉₊ := h1
    _ ≤ (S.L : ℝ) ^ S.h ξ := by
      apply pow_le_pow_right₀ hL1.le
      have hh : S.h ξ = ⌈Real.logb S.L A⌉₊ + 2 := by rw [hA]; rfl
      omega

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  {H : RegionHistory S n R k0}

variable (H) in
/-- A path of ancestors along which every step is live and every predecessor is not ripe. -/
inductive LiveDesc (a : ℕ) : (b : ℕ) → H.Comp a → H.Comp b → Prop
  | refl (Y : H.Comp a) : LiveDesc a a Y Y
  | step (b : ℕ) (Y : H.Comp a) (Y' : H.Comp b) (Y'' : H.Comp (b + 1)) :
      LiveDesc a b Y Y' → (h : Y'.1 ∉ H.rem b) → H.succ b Y' h = Y'' → LiveAt (b + 1) Y'' →
        ¬ S.Ripe b (H.bk b Y') → LiveDesc a (b + 1) Y Y''

theorem LiveDesc.toDesc {a b : ℕ} {W : H.Comp a} {Y : H.Comp b} (h : H.LiveDesc a b W Y) :
    H.Desc a b W Y := by
  induction h with
  | refl => exact Desc.refl _
  | step b _ Y' Y'' _ hrem hs _ _ ih => exact Desc.step b _ Y' Y'' ih hrem hs

theorem LiveDesc.trans {a b c : ℕ} {Y : H.Comp a} {Y' : H.Comp b} {Z : H.Comp c}
    (h1 : H.LiveDesc a b Y Y') (h2 : H.LiveDesc b c Y' Z) : H.LiveDesc a c Y Z := by
  induction h2 with
  | refl => exact h1
  | step c _ Y'' Z'' _ hrem hs hl hn ih => exact LiveDesc.step c Y Y'' Z'' (ih h1) hrem hs hl hn

theorem ShDesc.toLiveDesc {a b : ℕ} {W : H.Comp a} {Y : H.Comp b} (h : H.ShDesc a b W Y) :
    H.LiveDesc a b W Y := by
  induction h with
  | refl => exact LiveDesc.refl _
  | step b _ Y' Y'' _ hrem hs hparts hr hact hrip ih =>
    refine LiveDesc.step b _ Y' Y'' ih hrem hs ?_ hrip
    refine ⟨hr, fun c hc => ?_, Or.inl (by rw [hparts]; simp)⟩
    have : c = Y' := by rw [hparts] at hc; simpa using hc
    subst this; exact hact

variable (G : S.Good)

include G

/-- A merge record is kept or released with a large core, along a live path. -/
theorem recInv_liveDesc {ξ b : ℕ} {W : H.Comp ξ} {Z : H.Comp b} (h : H.LiveDesc ξ b W Z)
    (hξ : ξ < b) (hb : b ≤ k0) (hbase : S.RecInv ξ (H.bk ξ W)) : S.RecInv ξ (H.bk b Z) := by
  induction h with
  | refl => omega
  | step b' W' Y' Y'' hd hrem hs hl hn ih =>
    have hmem : Y' ∈ H.parts b' Y'' := (H.mem_parts b' Y' Y'').mpr ⟨hrem, hs⟩
    have hle := hd.toDesc.le
    have hR : S.RecInv ξ (H.pb b' Y') := by
      rw [show H.pb b' Y' = H.bk b' Y' from S.postBook_of_not_ripe hn]
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · subst heq
        have : Y' = W' := hd.toDesc.unique (Desc.refl W')
        subst this; exact hbase
      · exact ih hlt (by omega) hbase
    exact recInv_step G hb hl hmem hR

/-- The path from an ancestor `Y` at scale `a` to `Z`, not ripe at `a`, is live. -/
theorem liveDesc_of_desc {k : ℕ} {Z : H.Comp k} (hk0 : k ≤ k0)
    (hZ : (H.bk k Z).IsActive ∨ (H.bk k Z).IsPending) {a : ℕ} {Y : H.Comp a}
    (hd : H.Desc a k Y Z) (hq : (H.bk k Z).q ≤ a) (hnr : ¬ S.Ripe a (H.bk a Y)) :
    H.LiveDesc a k Y Z := by
  have key : ∀ (b : ℕ) (Y' : H.Comp b), H.Desc a b Y Y' → H.Desc b k Y' Z →
      H.LiveDesc a b Y Y' := by
    intro b Y' hd1 hd2
    induction hd1 with
    | refl => exact LiveDesc.refl _
    | step b' W' Y1 Y2 hd' hrem hs ih =>
      have hrest : H.Desc (b' + 1) k Y2 Z := hd2
      have hsingle : H.Desc b' (b' + 1) Y1 Y2 := Desc.single hrem hs
      have hle := hd'.le
      refine LiveDesc.step b' _ Y1 Y2 (ih hd hnr (hsingle.trans hrest)) hrem hs ?_ ?_
      · exact live_of_desc G hk0 hZ hrest (by omega)
      · rcases Nat.eq_or_lt_of_le hle with heq | hlt
        · subst heq
          have : Y1 = W' := hd'.unique (Desc.refl W')
          subst this; exact hnr
        · exact not_ripe_of_desc G hk0 hZ (hsingle.trans hrest) (by omega) (by have := hrest.le; omega)
  exact key k Z hd (Desc.refl Z)

omit G in
/-- A component with a point spine (length `0` of the book) is one box. -/
theorem cover_of_len (hT : ∀ k, 1 ≤ k → k ≤ k0 → 4 * S.rho k + 21 ≤ n k) {e : ℕ} (he1 : 1 ≤ e)
    (he0 : e ≤ k0) (Y : H.Comp e) (h : (H.bk e Y).len = 0) : CoveredBy S n e Y.1 1 :=
  H.cover_of_pt he1 he0 (hT e he1 he0) Y (by rw [← H.bk_len]; exact h)

variable {k : ℕ} {Z : H.Comp k}

/-- **Lemma I.4.13 (e4)**: for `Z` `Active` or `Pending` of scale `k ≤ k₀` with core `q`, every
ancestor of `Z` at scale `q` is one box of side `≤ crit_q`. -/
theorem core_box (hT : ∀ k, 1 ≤ k → k ≤ k0 → 4 * S.rho k + 21 ≤ n k) (hk0 : k ≤ k0)
    (hZ : (H.bk k Z).IsActive ∨ (H.bk k Z).IsPending) {q : ℕ} (hq : (H.bk k Z).q = q)
    {Y : H.Comp q} (hd : H.Desc q k Y Z) : CoveredBy S n q Y.1 1 := by
  have hqk := hd.le
  have hq1 : 1 ≤ q := not_isEmpty_comp Y (by omega)
  have hap := nonpre_of_desc G hk0 hZ hd (by omega)
  have hinvY := (H.window_inv' G q hq1 (by omega) Y).1
  by_cases hrip : S.Ripe q (H.bk q Y)
  · exact cover_of_len hT hq1 (by omega) Y (len_zero_of_ripe hinvY hrip)
  · obtain ⟨ξ, W, hsh, hkind⟩ := back G q Y (by omega) hap
    rcases hkind with hz | ⟨hrec, hlen, hnr⟩
    · have hl := ShDesc.len_le G hsh
      rw [hz, zero_div] at hl
      exact cover_of_len hT hq1 (by omega) Y (le_antisymm hl hinvY.len_nonneg)
    · have hLD : H.LiveDesc ξ k W Z :=
        hsh.toLiveDesc.trans (liveDesc_of_desc G hk0 hZ hd (by omega) hrip)
      have hξq : ξ ≤ q := hsh.le
      have hk1 : 1 ≤ k := not_isEmpty_comp Z hk0
      have hinvZ := (H.window_inv' G k hk1 hk0 Z).1
      have hrecZ : S.RecInv ξ (H.bk k Z) := by
        rcases Nat.eq_or_lt_of_le (hξq.trans hqk) with heq | hlt
        · subst heq
          have : Z = W := hLD.toDesc.unique (Desc.refl W)
          subst this; exact hrec
        · exact recInv_liveDesc G hLD hlt hk0 hrec
      have hh : ξ + S.h ξ < q := by
        rcases hrecZ with hM | hh
        · exfalso
          have hadm := hinvZ.adm
          rcases hZ with ⟨q', ν, M', hst⟩ | ⟨q', ν, hst⟩
          · rw [S.adm_active hst] at hadm
            rw [Book.M_active hst] at hM
            have := (hadm.2.2.2 ξ hM).1
            rw [Book.q_active hst] at hq
            omega
          · rw [Book.M_pending hst] at hM
            simp at hM
        · omega
      have hh2 : 2 ≤ S.h ξ := by unfold Setting.h; omega
      have hL : (1 : ℝ) ≤ S.L := by linarith [G.ok.cast_L_ge]
      have hW : (H.bk ξ W).len ≤ (S.L : ℝ) ^ (q - ξ) :=
        hlen.trans ((G.ok.numax_D_le_pow ξ).trans (pow_le_pow_right₀ hL (by omega)))
      exact cover_of_len hT hq1 (by omega) Y
        (ShDesc.len_zero G hsh (by omega) hW)

omit G in
/-- **Lemma I.4.13 (e4)**: distinct components of `Z^pre_q` are at distance `≥ ω_q`. -/
theorem core_sep {q : ℕ} {Y Y' : H.Comp q} (hne : Y ≠ Y') {x y : Torus S.d (n q)} (hx : x ∈ Y.1)
    (hy : y ∈ Y'.1) : S.omega q ≤ supDist x y :=
  comps_sep Y.2 Y'.2 (fun h => hne (Subtype.ext h)) hx hy

end RegionHistory

end Balaban.LargeField
