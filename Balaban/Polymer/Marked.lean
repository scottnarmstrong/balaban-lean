module

public import Balaban.Polymer.Holomorphic
public import Balaban.Polymer.CauchySum

/-!
# The marked polymer expansion (PE-M)

Activities `K Z l` depend holomorphically on marks `l = (l_i)_{i ∈ ι}` in a polydisc `Δ` of
polyradius `r`, with the Kotecký–Preiss bound uniform on `Δ`, and `K Z` does not depend on `l_i`
unless `Z` contains the set `S i` of blocks (`hdep`).  Writing `Ff Y l = P(Y)(l)` for the local
term, we prove at `l = 0`:

* (M1) `D1_Ff_eq_zero`, `D2_Ff_eq_zero`: `∂_i P(Y) = 0` unless `S i ⊆ Y`, and `∂_j ∂_i P(Y) = 0`
  unless `S i ∪ S j ⊆ Y`;
* (M2) `norm_D1_Ff_le`, `norm_D2_Ff_le`: Cauchy bounds, and the weighted bounds
  `sum_norm_D1_Ff_le`, `sum_norm_D2_Ff_le`;
* (M3) `D1_Xi_eq`, `D2_Xi_eq`: if a function `Zf` equals the polymer gas `Ξ` on `Δ`, then
  `∂_i Zf / Zf = ∑_Y ∂_i P(Y)` and the truncated second moment
  `∂_j ∂_i Zf / Zf − (∂_i Zf / Zf)(∂_j Zf / Zf) = ∑_Y ∂_j ∂_i P(Y)`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset Balaban.Analysis

namespace Balaban.Polymer

section Calculus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fderiv_single_eq_zero {f : (ι → ℂ) → ℂ} {w : ι → ℂ} (hd : DifferentiableAt ℂ f w) (i : ι)
    (h : ∀ t : ℂ, f (w + t • Pi.single i 1) = f w) : fderiv ℂ f w (Pi.single i 1) = 0 := by
  have h1 : HasDerivAt (fun t : ℂ => w + t • (Pi.single i 1 : ι → ℂ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single i 1 : ι → ℂ)).const_add w
  have h2 : HasFDerivAt f (fderiv ℂ f w) (w + (0 : ℂ) • (Pi.single i 1 : ι → ℂ)) := by
    simpa using hd.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℂ) h1
  have h4 : HasDerivAt (fun t : ℂ => f (w + t • (Pi.single i 1 : ι → ℂ))) 0 0 := by
    have : (fun t : ℂ => f (w + t • (Pi.single i 1 : ι → ℂ))) = fun _ => f w := funext h
    rw [this]; exact hasDerivAt_const _ _
  exact h3.unique h4

end Calculus

variable {P : Type*} [Fintype P] (inc : P → P → Prop) {κ a : P → ℝ}
  {B : Type*} (supp : P → Finset B) {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℝ}

/-- The local term `P(Y)` as a function of the marks. -/
def Ff (K : P → (ι → ℂ) → ℂ) (Y : Finset B) : (ι → ℂ) → ℂ :=
  fun l => PY inc supp (fun Z => K Z l) Y

section Marked

variable (S : ι → Finset B) (K : P → (ι → ℂ) → ℂ)

/-- `K Z` does not depend on the mark `l_i` unless `Z` contains `S i`. -/
def MarkDep : Prop :=
  ∀ i Z, ¬ S i ⊆ supp Z → ∀ (l : ι → ℂ) (t : ℂ), K Z (l + t • Pi.single i 1) = K Z l

variable {S K}

omit [Fintype ι] in
theorem Ff_translate (hdep : MarkDep supp S K) {i : ι} {Y : Finset B} (hY : ¬ S i ⊆ Y)
    (l : ι → ℂ) (t : ℂ) : Ff inc supp K Y (l + t • Pi.single i 1) = Ff inc supp K Y l := by
  unfold Ff
  refine PY_congr inc supp Y (fun x hx => hdep i x (fun hS => hY (hS.trans hx)) l t)

variable (h : KPCond inc κ a) (hr : ∀ i, 0 < r i)
  (hK : ∀ Z, AnalyticOnNhd ℂ (K Z) (polydisc 0 r))
  (hb : ∀ Z l, l ∈ polydisc (0 : ι → ℂ) r → ‖K Z l‖ ≤ κ Z)

omit [Fintype ι] [DecidableEq ι] in
include hr in
theorem zero_mem_polydisc : (0 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) r := fun k => by simpa using hr k

omit [DecidableEq ι] in
include h hK hb in
theorem analyticOnNhd_Ff (Y : Finset B) : AnalyticOnNhd ℂ (Ff inc supp K Y) (polydisc 0 r) :=
  pe_PY_analyticOnNhd inc supp h (isOpen_polydisc _ _) K hK hb Y

include h hr hK hb in
/-- (M1), first order. -/
theorem D1_Ff_eq_zero (hdep : MarkDep supp S K) {i : ι} {Y : Finset B} (hY : ¬ S i ⊆ Y) :
    D1 i (Ff inc supp K Y) = 0 :=
  fderiv_single_eq_zero ((analyticOnNhd_Ff inc supp h hK hb Y) 0
    (zero_mem_polydisc hr)).differentiableAt i (fun t => by
      simpa using Ff_translate inc supp hdep hY 0 t)

include h hr hK hb in
/-- (M1), second order. -/
theorem D2_Ff_eq_zero (hdep : MarkDep supp S K) {i j : ι} {Y : Finset B}
    (hY : ¬ S i ⊆ Y ∨ ¬ S j ⊆ Y) : D2 i j (Ff inc supp K Y) = 0 := by
  have h0 := zero_mem_polydisc hr
  have hopen := isOpen_polydisc (0 : ι → ℂ) r
  have hF := analyticOnNhd_Ff inc supp h hK hb Y
  rcases hY with hY | hY
  · -- the first derivative vanishes on `Δ`
    have hev : (fun w => fderiv ℂ (Ff inc supp K Y) w (Pi.single i 1)) =ᶠ[nhds (0 : ι → ℂ)]
        fun _ => 0 := by
      filter_upwards [hopen.mem_nhds h0] with w hw
      exact fderiv_single_eq_zero (hF w hw).differentiableAt i
        (fun t => Ff_translate inc supp hdep hY w t)
    unfold D2
    rw [hev.fderiv_eq]
    simp
  · -- the first derivative does not depend on the mark `j`
    have hg : DifferentiableAt ℂ (fun w => fderiv ℂ (Ff inc supp K Y) w (Pi.single i 1)) 0 :=
      ((hF.fderiv 0 h0).differentiableAt).clm_apply (differentiableAt_const _)
    refine fderiv_single_eq_zero hg j (fun t => ?_)
    have h1 : (fun z => Ff inc supp K Y (z + t • Pi.single j 1)) = Ff inc supp K Y :=
      funext (fun z => Ff_translate inc supp hdep hY z t)
    have h2 := fderiv_comp_add_right (𝕜 := ℂ) (t • (Pi.single j 1 : ι → ℂ))
      (f := Ff inc supp K Y) (x := 0)
    rw [h1] at h2
    simp only [zero_add] at h2 ⊢
    rw [← h2]

include h hr hK hb in
/-- (M2): Cauchy bound for the first derivative of a local term. -/
theorem norm_D1_Ff_le (Y : Finset B) (i : ι) :
    ‖D1 i (Ff inc supp K Y)‖ ≤ (∑' n, sp inc κ (fun _ => True) n) / r i := by
  have := norm_fderiv_single_le (analyticOnNhd_Ff inc supp h hK hb Y).differentiableOn
    (fun l hl => norm_PY_le inc supp h _ (fun Z => hb Z l hl) Y) (zero_mem_polydisc hr) i
  simpa [D1] using this

include h hr hK hb in
/-- (M2): Cauchy bound for the mixed second derivative of a local term. -/
theorem norm_D2_Ff_le (Y : Finset B) {i j : ι} (hij : i ≠ j) :
    ‖D2 i j (Ff inc supp K Y)‖ ≤ (∑' n, sp inc κ (fun _ => True) n) / r i / r j :=
  norm_mixed_fderiv_le hr (analyticOnNhd_Ff inc supp h hK hb Y)
    (fun l hl => norm_PY_le inc supp h _ (fun Z => hb Z l hl) Y) hij

section Weighted

variable [Fintype B] {κ0 : P → ℝ} (g : Finset B → ℝ) (c : ℝ) (hc : 0 ≤ c) (hg : ∀ Y, 0 ≤ g Y)
  (hG3 : ∀ (n : ℕ) (X : Fin (n + 1) → P), (clusterGraph inc X).Connected →
      g (unionOf supp X) ≤ ∑ i, g (supp (X i)) + c * n)
  (hκ : ∀ x, κ x = κ0 x * Real.exp (g (supp x) + c))
  (hK0 : ∀ x l, l ∈ polydisc (0 : ι → ℂ) r → ‖K x l‖ ≤ κ0 x) (b : B)

include h hr hK hb hc hg hG3 hκ hK0 in
/-- (M2), weighted form for the first derivative: `∑_{Y ∋ b} e^{g(Y)} |∂_i P(Y)| ≤ A / r_i`, where
`A` is the bound of `pe_PY_bound`. -/
theorem sum_norm_D1_Ff_le (i : ι) :
    ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        Real.exp (g Y) * ‖D1 i (Ff inc supp K Y)‖ ≤
      (∑ x, (if b ∈ supp x then κ x * Real.exp (a x) else 0)) / r i := by
  refine sum_norm_D1_le hr _ (Ff inc supp K)
    (fun Y => analyticOnNhd_Ff inc supp h hK hb Y) _ (fun Y => (Real.exp_pos _).le) ?_ i
  intro l hl
  have := pe_PY_bound inc supp g c hc hg hG3 hκ h (fun Z => K Z l) (fun x => hK0 x l hl) b
  simpa only [mul_comm, Ff] using this

include h hr hK hb hc hg hG3 hκ hK0 in
/-- (M2), weighted form for the mixed second derivative:
`∑_{Y ∋ b} e^{g(Y)} |∂_j ∂_i P(Y)| ≤ A / (r_i r_j)`. -/
theorem sum_norm_D2_Ff_le {i j : ι} (hij : i ≠ j) :
    ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        Real.exp (g Y) * ‖D2 i j (Ff inc supp K Y)‖ ≤
      (∑ x, (if b ∈ supp x then κ x * Real.exp (a x) else 0)) / r i / r j := by
  refine sum_norm_D2_le hr _ (Ff inc supp K)
    (fun Y => analyticOnNhd_Ff inc supp h hK hb Y) _ (fun Y => (Real.exp_pos _).le) ?_ hij
  intro l hl
  have := pe_PY_bound inc supp g c hc hg hG3 hκ h (fun Z => K Z l) (fun x => hK0 x l hl) b
  simpa only [mul_comm, Ff] using this

end Weighted

section Truncated

variable [Fintype B] (hrefl : ∀ x, inc x x)

/-- The cluster sum as a function of the marks. -/
def Lf (K : P → (ι → ℂ) → ℂ) : (ι → ℂ) → ℂ := fun l => logSeries inc (fun Z => K Z l)

omit [DecidableEq ι] in
include h hK hb in
theorem analyticOnNhd_Lf : AnalyticOnNhd ℂ (Lf inc K) (polydisc 0 r) :=
  pe_analyticOnNhd inc h (isOpen_polydisc _ _) K hK hb

omit [Fintype ι] [DecidableEq ι] in
include h hb in
theorem Lf_eq_sum_Ff {l : ι → ℂ} (hl : l ∈ polydisc (0 : ι → ℂ) r) :
    Lf inc K l = ∑ Y : Finset B, Ff inc supp K Y l :=
  logSeries_eq_sum_PY inc supp h _ (fun Z => hb Z l hl)

include h hr hK hb in
theorem D1_Lf_eq_sum (i : ι) : D1 i (Lf inc K) = ∑ Y : Finset B, D1 i (Ff inc supp K Y) := by
  have h0 := zero_mem_polydisc hr
  have hev : Lf inc K =ᶠ[nhds (0 : ι → ℂ)] fun l => ∑ Y : Finset B, Ff inc supp K Y l := by
    filter_upwards [(isOpen_polydisc (0 : ι → ℂ) r).mem_nhds h0] with l hl
    exact Lf_eq_sum_Ff inc supp h hb hl
  unfold D1
  rw [hev.fderiv_eq, fderiv_fun_sum (fun Y _ => (analyticOnNhd_Ff inc supp h hK hb Y 0 h0).differentiableAt)]
  simp [_root_.sum_apply]

include h hr hK hb in
theorem D2_Lf_eq_sum (i j : ι) :
    D2 i j (Lf inc K) = ∑ Y : Finset B, D2 i j (Ff inc supp K Y) := by
  have h0 := zero_mem_polydisc hr
  have hopen := isOpen_polydisc (0 : ι → ℂ) r
  have hev : (fun w => fderiv ℂ (Lf inc K) w (Pi.single i 1)) =ᶠ[nhds (0 : ι → ℂ)]
      fun w => ∑ Y : Finset B, fderiv ℂ (Ff inc supp K Y) w (Pi.single i 1) := by
    filter_upwards [hopen.mem_nhds h0] with w hw
    have hev' : Lf inc K =ᶠ[nhds w] fun l => ∑ Y : Finset B, Ff inc supp K Y l := by
      filter_upwards [hopen.mem_nhds hw] with l hl
      exact Lf_eq_sum_Ff inc supp h hb hl
    rw [hev'.fderiv_eq, fderiv_fun_sum (fun Y _ =>
      (analyticOnNhd_Ff inc supp h hK hb Y w hw).differentiableAt)]
    simp [_root_.sum_apply]
  unfold D2
  rw [hev.fderiv_eq, fderiv_fun_sum (fun Y _ =>
    (((analyticOnNhd_Ff inc supp h hK hb Y).fderiv 0 h0).differentiableAt.clm_apply
      (differentiableAt_const _)))]
  simp [_root_.sum_apply]

variable (hdep : MarkDep supp S K) (Zf : (ι → ℂ) → ℂ) (hZ : ∀ l ∈ polydisc (0 : ι → ℂ) r, Zf l = Xi inc (fun Z => K Z l))

omit [Fintype ι] [DecidableEq ι] in
include h hb hZ hrefl in
theorem Zf_eq_exp {l : ι → ℂ} (hl : l ∈ polydisc (0 : ι → ℂ) r) : Zf l = Complex.exp (Lf inc K l) :=
  (hZ l hl).trans (pe_xi_eq_exp inc h hrefl _ (fun Z => hb Z l hl))

omit [Fintype ι] [DecidableEq ι] in
include h hr hb hZ hrefl in
theorem Zf_zero_ne : Zf 0 ≠ 0 := by
  rw [Zf_eq_exp inc h hb hrefl Zf hZ (zero_mem_polydisc hr)]
  exact Complex.exp_ne_zero _

include h hr hK hb hZ hrefl in
theorem D1_Zf (i : ι) : D1 i Zf = Zf 0 * D1 i (Lf inc K) := by
  have h0 := zero_mem_polydisc hr
  have hL := (analyticOnNhd_Lf inc h hK hb 0 h0).differentiableAt.hasFDerivAt
  have hev : Zf =ᶠ[nhds (0 : ι → ℂ)] fun l => Complex.exp (Lf inc K l) := by
    filter_upwards [(isOpen_polydisc (0 : ι → ℂ) r).mem_nhds h0] with l hl
    exact Zf_eq_exp inc h hb hrefl Zf hZ hl
  unfold D1
  rw [hev.fderiv_eq, hL.cexp.fderiv, Zf_eq_exp inc h hb hrefl Zf hZ h0]
  simp

include h hr hK hb hZ hrefl in
theorem D2_Zf (i j : ι) :
    D2 i j Zf = Zf 0 * (D2 i j (Lf inc K) + D1 j (Lf inc K) * D1 i (Lf inc K)) := by
  have h0 := zero_mem_polydisc hr
  have hopen := isOpen_polydisc (0 : ι → ℂ) r
  have hLa := analyticOnNhd_Lf inc h hK hb
  have hev : (fun w => fderiv ℂ Zf w (Pi.single i 1)) =ᶠ[nhds (0 : ι → ℂ)]
      fun w => Complex.exp (Lf inc K w) * fderiv ℂ (Lf inc K) w (Pi.single i 1) := by
    filter_upwards [hopen.mem_nhds h0] with w hw
    have hev' : Zf =ᶠ[nhds w] fun l => Complex.exp (Lf inc K l) := by
      filter_upwards [hopen.mem_nhds hw] with l hl
      exact Zf_eq_exp inc h hb hrefl Zf hZ hl
    rw [hev'.fderiv_eq, (hLa w hw).differentiableAt.hasFDerivAt.cexp.fderiv]
    simp
  have hc : HasFDerivAt (fun w => Complex.exp (Lf inc K w))
      (Complex.exp (Lf inc K 0) • fderiv ℂ (Lf inc K) 0) 0 :=
    (hLa 0 h0).differentiableAt.hasFDerivAt.cexp
  have hd : DifferentiableAt ℂ (fun w => fderiv ℂ (Lf inc K) w (Pi.single i 1)) 0 :=
    ((hLa.fderiv 0 h0).differentiableAt).clm_apply (differentiableAt_const _)
  have hm := hc.fun_mul hd.hasFDerivAt
  unfold D2
  rw [hev.fderiv_eq, hm.fderiv, Zf_eq_exp inc h hb hrefl Zf hZ h0]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  unfold D1
  ring

include h hr hK hb hZ hrefl in
/-- (M3), first order: `∂_i Ξ / Ξ = ∑_Y ∂_i P(Y)` at `l = 0`. -/
theorem D1_Zf_div (i : ι) : D1 i Zf / Zf 0 = ∑ Y : Finset B, D1 i (Ff inc supp K Y) := by
  rw [D1_Zf inc h hr hK hb hrefl Zf hZ, mul_div_cancel_left₀ _ (Zf_zero_ne inc h hr hb hrefl Zf hZ),
    D1_Lf_eq_sum inc supp h hr hK hb]

include h hr hK hb hZ hrefl in
/-- (M3), second order, the truncated second moment:
`∂_j ∂_i Ξ / Ξ − (∂_i Ξ / Ξ)(∂_j Ξ / Ξ) = ∑_Y ∂_j ∂_i P(Y)` at `l = 0`. -/
theorem D2_Zf_div (i j : ι) :
    D2 i j Zf / Zf 0 - (D1 i Zf / Zf 0) * (D1 j Zf / Zf 0) =
      ∑ Y : Finset B, D2 i j (Ff inc supp K Y) := by
  have hne := Zf_zero_ne inc h hr hb hrefl Zf hZ
  rw [D2_Zf inc h hr hK hb hrefl Zf hZ, D1_Zf inc h hr hK hb hrefl Zf hZ,
    D1_Zf inc h hr hK hb hrefl Zf hZ, ← D2_Lf_eq_sum inc supp h hr hK hb i j]
  field_simp
  ring

section TruncatedBound

variable {κ0 : P → ℝ} (g : Finset B → ℝ) (c : ℝ) (hc : 0 ≤ c) (hg : ∀ Y, 0 ≤ g Y)
  (hG3 : ∀ (n : ℕ) (X : Fin (n + 1) → P), (clusterGraph inc X).Connected →
      g (unionOf supp X) ≤ ∑ i, g (supp (X i)) + c * n)
  (hκ : ∀ x, κ x = κ0 x * Real.exp (g (supp x) + c))
  (hK0 : ∀ x l, l ∈ polydisc (0 : ι → ℂ) r → ‖K x l‖ ≤ κ0 x)

include h hr hK hb hZ hrefl hdep in
/-- The truncated second moment only sees the local terms of sets containing both marks. -/
theorem D2_Zf_div_eq_sum_filter (i j : ι) :
    D2 i j Zf / Zf 0 - (D1 i Zf / Zf 0) * (D1 j Zf / Zf 0) =
      ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => S i ⊆ Y ∧ S j ⊆ Y),
        D2 i j (Ff inc supp K Y) := by
  rw [D2_Zf_div inc supp h hr hK hb hrefl Zf hZ i j]
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) (fun Y _ hY => ?_)
  refine D2_Ff_eq_zero inc supp h hr hK hb hdep ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or] at hY
  exact hY

include h hr hK hb hZ hrefl hdep hc hg hG3 hκ hK0 in
/-- The truncated second moment decays like the weight: if `b ∈ S i` and `G ≤ g Y` whenever
`Y ⊇ S i ∪ S j`, then `|∂_j ∂_i Ξ / Ξ − (∂_i Ξ / Ξ)(∂_j Ξ / Ξ)| e^{G} ≤ A / (r_i r_j)`. -/
theorem norm_truncated_second_le {i j : ι} (hij : i ≠ j) {b : B} (hb' : b ∈ S i) {G : ℝ}
    (hG : ∀ Y, S i ⊆ Y → S j ⊆ Y → G ≤ g Y) :
    ‖D2 i j Zf / Zf 0 - (D1 i Zf / Zf 0) * (D1 j Zf / Zf 0)‖ * Real.exp G ≤
      (∑ x, (if b ∈ supp x then κ x * Real.exp (a x) else 0)) / r i / r j := by
  rw [D2_Zf_div_eq_sum_filter inc supp h hr hK hb hrefl hdep Zf hZ i j]
  refine le_trans ?_ (sum_norm_D2_Ff_le inc supp h hr hK hb g c hc hg hG3 hκ hK0 b hij)
  calc _ ≤ (∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => S i ⊆ Y ∧ S j ⊆ Y),
        ‖D2 i j (Ff inc supp K Y)‖) * Real.exp G :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le
    _ = ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => S i ⊆ Y ∧ S j ⊆ Y),
        Real.exp G * ‖D2 i j (Ff inc supp K Y)‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    _ ≤ ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => S i ⊆ Y ∧ S j ⊆ Y),
        Real.exp (g Y) * ‖D2 i j (Ff inc supp K Y)‖ := by
        refine Finset.sum_le_sum (fun Y hY => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hG Y hY.1 hY.2)) (norm_nonneg _)
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro Y hY
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY ⊢
        exact hY.1 hb'

include h hr hK hb hZ hrefl hdep hc hg hG3 hκ hK0 in
/-- The truncated first moment: if `b ∈ S i` and `G ≤ g Y` whenever `Y ⊇ S i`, then
`|∂_i Ξ / Ξ| e^{G} ≤ A / r_i`. -/
theorem norm_truncated_first_le (i : ι) {b : B} (hb' : b ∈ S i) {G : ℝ}
    (hG : ∀ Y, S i ⊆ Y → G ≤ g Y) :
    ‖D1 i Zf / Zf 0‖ * Real.exp G ≤
      (∑ x, (if b ∈ supp x then κ x * Real.exp (a x) else 0)) / r i := by
  have hsum : D1 i Zf / Zf 0 =
      ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => S i ⊆ Y),
        D1 i (Ff inc supp K Y) := by
    rw [D1_Zf_div inc supp h hr hK hb hrefl Zf hZ]
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun Y _ hY => ?_)
    refine D1_Ff_eq_zero inc supp h hr hK hb hdep ?_
    simpa using hY
  rw [hsum]
  refine le_trans ?_ (sum_norm_D1_Ff_le inc supp h hr hK hb g c hc hg hG3 hκ hK0 b i)
  calc _ ≤ (∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => S i ⊆ Y),
        ‖D1 i (Ff inc supp K Y)‖) * Real.exp G :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le
    _ = ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => S i ⊆ Y),
        Real.exp G * ‖D1 i (Ff inc supp K Y)‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    _ ≤ ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => S i ⊆ Y),
        Real.exp (g Y) * ‖D1 i (Ff inc supp K Y)‖ := by
        refine Finset.sum_le_sum (fun Y hY => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hG Y hY)) (norm_nonneg _)
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro Y hY
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY ⊢
        exact hY hb'

end TruncatedBound

end Truncated

end Marked

end Balaban.Polymer
