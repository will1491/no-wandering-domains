/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Schwarz Reflection Principle

Let `Ω ⊆ ℂ` be open and symmetric under complex conjugation. Suppose
`f` is holomorphic on the open upper portion `Ω ∩ { z | 0 < z.im }`,
continuous on the closed upper portion `Ω ∩ { z | 0 ≤ z.im }`, and
real-valued on the real axis `Ω ∩ ℝ`. Then the reflected function
`f̃ : ℂ → ℂ` defined by

  `f̃(z) := f(z)`              if `0 ≤ z.im`,
  `f̃(z) := conj(f(conj z))`   if `z.im < 0`,

is holomorphic on all of `Ω`. The two piecewise branches agree on
`Ω ∩ ℝ` because `f` is real-valued there, so `f̃` is well-defined and
continuous across the real axis.

The proof is the standard Morera argument: for every closed rectangle
contained in `Ω`, the contour integral of `f̃` over its boundary
vanishes. We split such a rectangle into its upper and lower halves
(both with one edge on the real axis), apply the Cauchy–Goursat theorem
for rectangles (`integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`)
to each half, and observe that the integrals over the shared real-axis
edge cancel. From vanishing rectangle integrals on every ball
contained in `Ω`, `Complex.IsConservativeOn.isExactOn_ball` yields a
local primitive; the primitive is holomorphic, and `f̃` is its derivative.

The main consumer is the surjectivity argument for `modularLambdaH` onto
the triply-punctured plane: extending `λ` from `ℍ` across the real
axis on a fundamental-domain arc and lifting any target point in
`ℂ ∖ {0, 1}` to a preimage in `ℍ`.
-/

namespace NoWanderingDomains

open Complex Set Topology

/-- A set `Ω ⊆ ℂ` is *real-symmetric* if it is preserved under complex
conjugation. -/
def IsRealSymmetric (Ω : Set ℂ) : Prop := ∀ z, z ∈ Ω → (starRingEnd ℂ z) ∈ Ω

/-- The Schwarz-reflected function: agrees with `f` on the closed upper
half-plane, and is `conj ∘ f ∘ conj` on the open lower half-plane.
On the real axis (`z.im = 0`), both branches coincide for `f` whose
values on the real axis are themselves real. -/
noncomputable def schwarzReflect (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then f z else starRingEnd ℂ (f (starRingEnd ℂ z))

/-! ## Basic identities of `schwarzReflect` -/

/-- On the closed upper half-plane, the reflected function equals `f`. -/
@[simp] theorem schwarzReflect_apply_of_im_nonneg (f : ℂ → ℂ) {z : ℂ} (hz : 0 ≤ z.im) :
    schwarzReflect f z = f z := by
  simp [schwarzReflect, hz]

/-- On the open lower half-plane, the reflected function is the conjugate
of `f` at the reflected point. -/
@[simp] theorem schwarzReflect_apply_of_im_neg (f : ℂ → ℂ) {z : ℂ} (hz : z.im < 0) :
    schwarzReflect f z = starRingEnd ℂ (f (starRingEnd ℂ z)) := by
  have h_not : ¬ (0 ≤ z.im) := not_le.mpr hz
  simp [schwarzReflect, h_not]

/-- On the real axis, the reflected function equals `f`. (The other
branch — `conj ∘ f ∘ conj` — would also evaluate to `f`, but only when
`f` is real-valued on the real axis; we do not need that here.) -/
theorem schwarzReflect_apply_of_im_zero (f : ℂ → ℂ) {z : ℂ} (hz : z.im = 0) :
    schwarzReflect f z = f z :=
  schwarzReflect_apply_of_im_nonneg f hz.ge

/-! ## Holomorphy on each open half-plane -/

/-- On the open upper half-plane, `schwarzReflect f` is `f`. So it
inherits `f`'s differentiability there. -/
theorem schwarzReflect_differentiableAt_of_im_pos {f : ℂ → ℂ} {z : ℂ}
    (hz : 0 < z.im) (hf : DifferentiableAt ℂ f z) :
    DifferentiableAt ℂ (schwarzReflect f) z := by
  -- `schwarzReflect f` equals `f` on the neighborhood `{z | 0 < z.im}` of `z`.
  apply hf.congr_of_eventuallyEq
  have h_nbhd : {w : ℂ | 0 < w.im} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
  filter_upwards [h_nbhd] with w hw using
    schwarzReflect_apply_of_im_nonneg f hw.le

/-- On the open lower half-plane, `schwarzReflect f = conj ∘ f ∘ conj`,
which inherits differentiability from `f` at the conjugate point. -/
theorem schwarzReflect_differentiableAt_of_im_neg {f : ℂ → ℂ} {z : ℂ}
    (hz : z.im < 0)
    (hf : DifferentiableAt ℂ f (starRingEnd ℂ z)) :
    DifferentiableAt ℂ (schwarzReflect f) z := by
  -- On a neighborhood of `z`, `schwarzReflect f = conj ∘ f ∘ conj`.
  -- That composition is differentiable at `z` by `DifferentiableAt.conj_conj`,
  -- after converting between `(starRingEnd ℂ) (z)` and `Complex.conj z`.
  have h_diff : DifferentiableAt ℂ (starRingEnd ℂ ∘ f ∘ starRingEnd ℂ)
      (starRingEnd ℂ (starRingEnd ℂ z)) := hf.conj_conj
  rw [Complex.conj_conj] at h_diff
  apply h_diff.congr_of_eventuallyEq
  have h_nbhd : {w : ℂ | w.im < 0} ∈ 𝓝 z :=
    (isOpen_lt Complex.continuous_im continuous_const).mem_nhds hz
  filter_upwards [h_nbhd] with w hw
  simp [schwarzReflect_apply_of_im_neg f hw, Function.comp]

/-! ## Continuity of `schwarzReflect` on a symmetric domain -/

/-- **Continuity of the reflected function.** Under the standing
hypotheses — `Ω` open and real-symmetric, `f` continuous on the
closed upper half of `Ω`, real-valued on `Ω ∩ ℝ` — the reflected
function `schwarzReflect f` is continuous on the whole of `Ω`. The
proof decomposes `Ω = (Ω ∩ {0 ≤ im}) ∪ (Ω ∩ {im ≤ 0})` and applies
`ContinuousWithinAt.union`: on the upper half `schwarzReflect f = f`
(continuous via `hf_cont`), on the lower half
`schwarzReflect f = conj ∘ f ∘ conj` (continuous via symmetry of
`Ω` and the conjugate transport), and the two branches agree on the
overlap `Ω ∩ {im = 0}` because `f` is real-valued there. -/
theorem schwarzReflect_continuousOn
    {Ω : Set ℂ} (_hΩ_open : IsOpen Ω) (hΩ_sym : IsRealSymmetric Ω)
    {f : ℂ → ℂ}
    (hf_cont : ContinuousOn f (Ω ∩ {z | 0 ≤ z.im}))
    (hf_real : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    ContinuousOn (schwarzReflect f) Ω := by
  have h_conj_cont : Continuous (starRingEnd ℂ) := Complex.continuous_conj
  -- Continuity of `conj ∘ f ∘ conj` on the closed lower half of `Ω`.
  have h_lower_cont : ContinuousOn (fun w => starRingEnd ℂ (f (starRingEnd ℂ w)))
      (Ω ∩ {z : ℂ | z.im ≤ 0}) := by
    have h_maps : Set.MapsTo (starRingEnd ℂ)
        (Ω ∩ {z : ℂ | z.im ≤ 0}) (Ω ∩ {z : ℂ | 0 ≤ z.im}) := by
      intro w hw
      refine ⟨hΩ_sym w hw.1, ?_⟩
      have hw_im : w.im ≤ 0 := hw.2
      change 0 ≤ (starRingEnd ℂ w).im
      rw [Complex.conj_im]
      linarith
    have h_f_after_conj : ContinuousOn (f ∘ starRingEnd ℂ) (Ω ∩ {z : ℂ | z.im ≤ 0}) :=
      hf_cont.comp h_conj_cont.continuousOn h_maps
    exact h_conj_cont.continuousOn.comp h_f_after_conj (Set.mapsTo_univ _ _)
  intro z hz_Ω
  -- Split `Ω = (Ω ∩ {0 ≤ im}) ∪ (Ω ∩ {im ≤ 0})`.
  have h_split : Ω = (Ω ∩ {w : ℂ | 0 ≤ w.im}) ∪ (Ω ∩ {w : ℂ | w.im ≤ 0}) := by
    ext w
    refine ⟨fun hw_Ω => ?_, fun h => h.elim And.left And.left⟩
    rcases le_or_gt 0 w.im with h | h
    · exact Or.inl ⟨hw_Ω, h⟩
    · exact Or.inr ⟨hw_Ω, h.le⟩
  rw [h_split]
  refine ContinuousWithinAt.union ?_ ?_
  · -- ContinuousWithinAt schwarzReflect (Ω ∩ {0 ≤ im}) z.
    by_cases hz_im : 0 ≤ z.im
    · have h_z_in : z ∈ Ω ∩ {w : ℂ | 0 ≤ w.im} := ⟨hz_Ω, hz_im⟩
      apply (hf_cont z h_z_in).congr
        (fun w hw => schwarzReflect_apply_of_im_nonneg f hw.2)
      exact schwarzReflect_apply_of_im_nonneg f hz_im
    · have hz_lt : z.im < 0 := not_le.mp hz_im
      apply continuousWithinAt_of_notMem_closure
      intro h_cl
      have h_cl_sub : closure (Ω ∩ {w : ℂ | 0 ≤ w.im}) ⊆ {w : ℂ | 0 ≤ w.im} :=
        closure_minimal Set.inter_subset_right
          (isClosed_le continuous_const Complex.continuous_im)
      exact absurd (h_cl_sub h_cl) (not_le.mpr hz_lt)
  · -- ContinuousWithinAt schwarzReflect (Ω ∩ {im ≤ 0}) z.
    by_cases hz_im : z.im ≤ 0
    · have h_z_in : z ∈ Ω ∩ {w : ℂ | w.im ≤ 0} := ⟨hz_Ω, hz_im⟩
      have h_eq_on : ∀ w ∈ Ω ∩ {v : ℂ | v.im ≤ 0},
          schwarzReflect f w = starRingEnd ℂ (f (starRingEnd ℂ w)) := by
        intro w hw
        have hw_im_le : w.im ≤ 0 := hw.2
        rcases lt_or_eq_of_le hw_im_le with hw_lt | hw_eq
        · exact schwarzReflect_apply_of_im_neg f hw_lt
        · have hw_im : w.im = 0 := hw_eq
          have h_conj_w : starRingEnd ℂ w = w := by
            apply Complex.ext
            · simp
            · simp [hw_im]
          rw [schwarzReflect_apply_of_im_zero f hw_im, h_conj_w]
          have h_f_real := hf_real w hw.1 hw_im
          apply Complex.ext
          · simp
          · simp [h_f_real]
      apply (h_lower_cont z h_z_in).congr h_eq_on
      exact h_eq_on z h_z_in
    · have hz_lt : 0 < z.im := not_le.mp hz_im
      apply continuousWithinAt_of_notMem_closure
      intro h_cl
      have h_cl_sub : closure (Ω ∩ {w : ℂ | w.im ≤ 0}) ⊆ {w : ℂ | w.im ≤ 0} :=
        closure_minimal Set.inter_subset_right
          (isClosed_le Complex.continuous_im continuous_const)
      exact absurd (h_cl_sub h_cl) (not_le.mpr hz_lt)

/-! ## Main theorem: Schwarz reflection -/

/-- **Schwarz Reflection Principle.** Let `Ω ⊆ ℂ` be open and
real-symmetric. Let `f : ℂ → ℂ` be holomorphic on the open upper
half `Ω ∩ {0 < z.im}`, continuous on the closed upper half
`Ω ∩ {0 ≤ z.im}`, and real-valued on the real-axis slice
`Ω ∩ {z.im = 0}`. Then the Schwarz-reflected function `schwarzReflect f`
is holomorphic on all of `Ω`.

The proof reduces holomorphy to `IsConservativeOn + ContinuousOn` via
`Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`.
Continuity is `schwarzReflect_continuousOn`. For `IsConservativeOn` —
the vanishing of the contour integral around every rectangle in `Ω` —
we case-split on the rectangle's imaginary range:

* If the rectangle is contained in the closed upper half (`min ≥ 0`),
  `schwarzReflect f` equals `f` on the closed rectangle and is
  differentiable on the open interior (which lies in `{0 < im}` where
  `f` is differentiable). Direct application of
  `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`.
* If the rectangle is contained in the closed lower half (`max ≤ 0`),
  symmetric argument using `conj ∘ f ∘ conj`.
* If the rectangle crosses the real axis (`min < 0 < max`), split it
  at the real axis into upper and lower sub-rectangles with corners
  `(z'.re, 0), w'` and `z', (w'.re, 0)` respectively. Each sub-
  rectangle is in one closed half, so the previous cases apply. Sum
  the two boundary integrals: the shared real-axis edge cancels (the
  `∫ f(x + 0·I) dx` terms appear once with each sign), and the side
  integrals combine via `intervalIntegral.integral_add_adjacent_intervals`
  applied at `y = 0`. The final algebraic identity is discharged by
  `linear_combination` (after aligning `•` with `*` via `smul_eq_mul`). -/
theorem schwarzReflect_differentiableOn
    {Ω : Set ℂ} (hΩ_open : IsOpen Ω) (hΩ_sym : IsRealSymmetric Ω)
    {f : ℂ → ℂ}
    (hf_cont : ContinuousOn f (Ω ∩ {z | 0 ≤ z.im}))
    (hf_diff : DifferentiableOn ℂ f (Ω ∩ {z | 0 < z.im}))
    (hf_real : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    DifferentiableOn ℂ (schwarzReflect f) Ω := by
  have h_cont_Ω : ContinuousOn (schwarzReflect f) Ω :=
    schwarzReflect_continuousOn hΩ_open hΩ_sym hf_cont hf_real
  rw [← Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hΩ_open]
  refine ⟨?_, h_cont_Ω⟩
  -- DifferentiableAt of `schwarzReflect f` at points off the real axis.
  have h_sr_diff_at_pos : ∀ p ∈ Ω, 0 < p.im → DifferentiableAt ℂ (schwarzReflect f) p := by
    intro p hp_Ω hp_pos
    have h_open_upper : IsOpen (Ω ∩ {z : ℂ | 0 < z.im}) :=
      hΩ_open.inter (isOpen_lt continuous_const Complex.continuous_im)
    have hp_in : p ∈ Ω ∩ {z : ℂ | 0 < z.im} := ⟨hp_Ω, hp_pos⟩
    have hf_at : DifferentiableAt ℂ f p :=
      hf_diff.differentiableAt (h_open_upper.mem_nhds hp_in)
    exact schwarzReflect_differentiableAt_of_im_pos hp_pos hf_at
  have h_sr_diff_at_neg : ∀ p ∈ Ω, p.im < 0 → DifferentiableAt ℂ (schwarzReflect f) p := by
    intro p hp_Ω hp_neg
    have h_conj_in : starRingEnd ℂ p ∈ Ω ∩ {z : ℂ | 0 < z.im} := by
      refine ⟨hΩ_sym p hp_Ω, ?_⟩
      change 0 < (starRingEnd ℂ p).im
      rw [Complex.conj_im]; linarith
    have h_open_upper : IsOpen (Ω ∩ {z : ℂ | 0 < z.im}) :=
      hΩ_open.inter (isOpen_lt continuous_const Complex.continuous_im)
    have hf_at : DifferentiableAt ℂ f (starRingEnd ℂ p) :=
      hf_diff.differentiableAt (h_open_upper.mem_nhds h_conj_in)
    exact schwarzReflect_differentiableAt_of_im_neg hp_neg hf_at
  intro z' w' h_rect_sub
  rw [eq_neg_iff_add_eq_zero, Complex.wedgeIntegral_add_wedgeIntegral_eq]
  -- Goal: rectangle boundary integral of `schwarzReflect f` = 0.
  -- ContinuousOn on the closed rectangle.
  have h_cont_rect : ContinuousOn (schwarzReflect f)
      (Set.uIcc z'.re w'.re ×ℂ Set.uIcc z'.im w'.im) :=
    h_cont_Ω.mono h_rect_sub
  -- Membership in `a ×ℂ b` ↔ re ∈ a ∧ im ∈ b.
  -- Three cases on the imaginary range.
  rcases le_or_gt 0 (min z'.im w'.im) with h_min_nn | h_min_neg
  · -- Case A: closed rectangle in upper closed half (im ≥ 0).
    refine Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      _ z' w' h_cont_rect ?_
    intro p hp
    have hp_im_lt : min z'.im w'.im < p.im := hp.2.1
    have hp_im_pos : 0 < p.im := lt_of_le_of_lt h_min_nn hp_im_lt
    have hp_in_Ω : p ∈ Ω := by
      apply h_rect_sub
      refine ⟨?_, ?_⟩
      · exact Set.Ioo_subset_Icc_self hp.1
      · exact Set.Ioo_subset_Icc_self hp.2
    exact (h_sr_diff_at_pos p hp_in_Ω hp_im_pos).differentiableWithinAt
  · rcases le_or_gt (max z'.im w'.im) 0 with h_max_np | h_max_pos
    · -- Case B: closed rectangle in lower closed half (im ≤ 0).
      refine Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
        _ z' w' h_cont_rect ?_
      intro p hp
      have hp_im_lt : p.im < max z'.im w'.im := hp.2.2
      have hp_im_neg : p.im < 0 := lt_of_lt_of_le hp_im_lt h_max_np
      have hp_in_Ω : p ∈ Ω := by
        apply h_rect_sub
        refine ⟨?_, ?_⟩
        · exact Set.Ioo_subset_Icc_self hp.1
        · exact Set.Ioo_subset_Icc_self hp.2
      exact (h_sr_diff_at_neg p hp_in_Ω hp_im_neg).differentiableWithinAt
    · -- Case C: rectangle crosses real axis. Split into upper + lower halves.
      -- Set up corner points for the two half-rectangles.
      set z_up : ℂ := ⟨z'.re, 0⟩ with hz_up_def
      set w_up : ℂ := w' with hw_up_def
      set z_low : ℂ := z' with hz_low_def
      set w_low : ℂ := ⟨w'.re, 0⟩ with hw_low_def
      -- `0 ∈ Set.uIcc z'.im w'.im` from `min < 0 < max`.
      have h_zero_in_im : (0 : ℝ) ∈ Set.uIcc z'.im w'.im := by
        rw [Set.uIcc, Set.mem_Icc]
        exact ⟨h_min_neg.le, h_max_pos.le⟩
      have h_uIcc_zero_w : Set.uIcc (0 : ℝ) w'.im ⊆ Set.uIcc z'.im w'.im :=
        Set.uIcc_subset_uIcc h_zero_in_im Set.right_mem_uIcc
      have h_uIcc_z_zero : Set.uIcc z'.im (0 : ℝ) ⊆ Set.uIcc z'.im w'.im :=
        Set.uIcc_subset_uIcc Set.left_mem_uIcc h_zero_in_im
      -- Sub-rectangles ⊆ Ω.
      have h_up_sub_Ω : Set.uIcc z_up.re w_up.re ×ℂ Set.uIcc z_up.im w_up.im ⊆ Ω :=
        fun p hp => h_rect_sub ⟨hp.1, h_uIcc_zero_w hp.2⟩
      have h_low_sub_Ω : Set.uIcc z_low.re w_low.re ×ℂ Set.uIcc z_low.im w_low.im ⊆ Ω :=
        fun p hp => h_rect_sub ⟨hp.1, h_uIcc_z_zero hp.2⟩
      -- Continuity of `schwarzReflect` on each sub-rectangle.
      have h_cont_up : ContinuousOn (schwarzReflect f)
          (Set.uIcc z_up.re w_up.re ×ℂ Set.uIcc z_up.im w_up.im) :=
        h_cont_Ω.mono h_up_sub_Ω
      have h_cont_low : ContinuousOn (schwarzReflect f)
          (Set.uIcc z_low.re w_low.re ×ℂ Set.uIcc z_low.im w_low.im) :=
        h_cont_Ω.mono h_low_sub_Ω
      -- `0 ∉ Ioo (min 0 w'.im) (max 0 w'.im)`: `0` is one of the endpoints.
      have h_zero_not_in_w_Ioo : (0 : ℝ) ∉ Set.Ioo (min 0 w'.im) (max 0 w'.im) := by
        intro h
        rcases le_total (0 : ℝ) w'.im with hw | hw
        · have : min (0 : ℝ) w'.im = 0 := min_eq_left hw
          rw [this] at h; exact lt_irrefl 0 h.1
        · have : max (0 : ℝ) w'.im = 0 := max_eq_left hw
          rw [this] at h; exact lt_irrefl 0 h.2
      have h_zero_not_in_z_Ioo : (0 : ℝ) ∉ Set.Ioo (min z'.im 0) (max z'.im 0) := by
        intro h
        rcases le_total z'.im (0 : ℝ) with hz | hz
        · have : max z'.im (0 : ℝ) = 0 := max_eq_right hz
          rw [this] at h; exact lt_irrefl 0 h.2
        · have : min z'.im (0 : ℝ) = 0 := min_eq_right hz
          rw [this] at h; exact lt_irrefl 0 h.1
      -- Differentiability on each sub-rectangle's open interior.
      have h_diff_up : DifferentiableOn ℂ (schwarzReflect f)
          (Set.Ioo (min z_up.re w_up.re) (max z_up.re w_up.re) ×ℂ
            Set.Ioo (min z_up.im w_up.im) (max z_up.im w_up.im)) := by
        intro p hp
        have hp_in_Ω : p ∈ Ω :=
          h_up_sub_Ω ⟨Set.Ioo_subset_Icc_self hp.1, Set.Ioo_subset_Icc_self hp.2⟩
        have hp_im_in : p.im ∈ Set.Ioo (min (0 : ℝ) w'.im) (max (0 : ℝ) w'.im) := hp.2
        have hp_im_ne : p.im ≠ 0 := by
          intro h
          apply h_zero_not_in_w_Ioo
          rcases hp_im_in with ⟨h1, h2⟩
          exact ⟨by linarith, by linarith⟩
        rcases lt_or_gt_of_ne hp_im_ne with hp_neg | hp_pos
        · exact (h_sr_diff_at_neg p hp_in_Ω hp_neg).differentiableWithinAt
        · exact (h_sr_diff_at_pos p hp_in_Ω hp_pos).differentiableWithinAt
      have h_diff_low : DifferentiableOn ℂ (schwarzReflect f)
          (Set.Ioo (min z_low.re w_low.re) (max z_low.re w_low.re) ×ℂ
            Set.Ioo (min z_low.im w_low.im) (max z_low.im w_low.im)) := by
        intro p hp
        have hp_in_Ω : p ∈ Ω :=
          h_low_sub_Ω ⟨Set.Ioo_subset_Icc_self hp.1, Set.Ioo_subset_Icc_self hp.2⟩
        have hp_im_in : p.im ∈ Set.Ioo (min z'.im (0 : ℝ)) (max z'.im (0 : ℝ)) := hp.2
        have hp_im_ne : p.im ≠ 0 := by
          intro h
          apply h_zero_not_in_z_Ioo
          rcases hp_im_in with ⟨h1, h2⟩
          exact ⟨by linarith, by linarith⟩
        rcases lt_or_gt_of_ne hp_im_ne with hp_neg | hp_pos
        · exact (h_sr_diff_at_neg p hp_in_Ω hp_neg).differentiableWithinAt
        · exact (h_sr_diff_at_pos p hp_in_Ω hp_pos).differentiableWithinAt
      -- Apply Cauchy-Goursat to each half.
      have h_up_eq := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
        (schwarzReflect f) z_up w_up h_cont_up h_diff_up
      have h_low_eq := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
        (schwarzReflect f) z_low w_low h_cont_low h_diff_low
      -- IntervalIntegrability of the side integrands.
      have h_int_w : IntervalIntegrable
          (fun y => schwarzReflect f (↑w'.re + ↑y * Complex.I)) MeasureTheory.volume
          z'.im w'.im := by
        apply ContinuousOn.intervalIntegrable
        have h_emb : ContinuousOn (fun y : ℝ => (↑w'.re + ↑y * Complex.I : ℂ))
            (Set.uIcc z'.im w'.im) :=
          Continuous.continuousOn (by fun_prop)
        have h_maps : Set.MapsTo (fun y : ℝ => (↑w'.re + ↑y * Complex.I : ℂ))
            (Set.uIcc z'.im w'.im) Ω := by
          intro y hy
          apply h_rect_sub
          refine ⟨?_, ?_⟩
          · change (↑w'.re + ↑y * Complex.I).re ∈ Set.uIcc z'.re w'.re
            simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
              mul_zero, Complex.I_im, mul_one, Complex.ofReal_im, sub_self, add_zero]
            exact Set.right_mem_uIcc
          · change (↑w'.re + ↑y * Complex.I).im ∈ Set.uIcc z'.im w'.im
            simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
              mul_one, Complex.I_re, mul_zero, Complex.ofReal_re, zero_add, add_zero]
            exact hy
        exact h_cont_Ω.comp h_emb h_maps
      have h_int_z : IntervalIntegrable
          (fun y => schwarzReflect f (↑z'.re + ↑y * Complex.I)) MeasureTheory.volume
          z'.im w'.im := by
        apply ContinuousOn.intervalIntegrable
        have h_emb : ContinuousOn (fun y : ℝ => (↑z'.re + ↑y * Complex.I : ℂ))
            (Set.uIcc z'.im w'.im) :=
          Continuous.continuousOn (by fun_prop)
        have h_maps : Set.MapsTo (fun y : ℝ => (↑z'.re + ↑y * Complex.I : ℂ))
            (Set.uIcc z'.im w'.im) Ω := by
          intro y hy
          apply h_rect_sub
          refine ⟨?_, ?_⟩
          · change (↑z'.re + ↑y * Complex.I).re ∈ Set.uIcc z'.re w'.re
            simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
              mul_zero, Complex.I_im, mul_one, Complex.ofReal_im, sub_self, add_zero]
            exact Set.left_mem_uIcc
          · change (↑z'.re + ↑y * Complex.I).im ∈ Set.uIcc z'.im w'.im
            simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
              mul_one, Complex.I_re, mul_zero, Complex.ofReal_re, zero_add, add_zero]
            exact hy
        exact h_cont_Ω.comp h_emb h_maps
      -- Splitting of y-integrals at 0 via adjacency.
      have h_int_w_z_0 := h_int_w.mono_set
        (Set.uIcc_subset_uIcc Set.left_mem_uIcc h_zero_in_im)
      have h_int_w_0_w := h_int_w.mono_set
        (Set.uIcc_subset_uIcc h_zero_in_im Set.right_mem_uIcc)
      have h_int_z_z_0 := h_int_z.mono_set
        (Set.uIcc_subset_uIcc Set.left_mem_uIcc h_zero_in_im)
      have h_int_z_0_w := h_int_z.mono_set
        (Set.uIcc_subset_uIcc h_zero_in_im Set.right_mem_uIcc)
      have h_split_w :
          (∫ y in z'.im..(0 : ℝ), schwarzReflect f (↑w'.re + ↑y * Complex.I)) +
          (∫ y in (0 : ℝ)..w'.im, schwarzReflect f (↑w'.re + ↑y * Complex.I)) =
          (∫ y in z'.im..w'.im, schwarzReflect f (↑w'.re + ↑y * Complex.I)) :=
        intervalIntegral.integral_add_adjacent_intervals h_int_w_z_0 h_int_w_0_w
      have h_split_z :
          (∫ y in z'.im..(0 : ℝ), schwarzReflect f (↑z'.re + ↑y * Complex.I)) +
          (∫ y in (0 : ℝ)..w'.im, schwarzReflect f (↑z'.re + ↑y * Complex.I)) =
          (∫ y in z'.im..w'.im, schwarzReflect f (↑z'.re + ↑y * Complex.I)) :=
        intervalIntegral.integral_add_adjacent_intervals h_int_z_z_0 h_int_z_0_w
      -- The corners' re/im fields evaluate definitionally.
      -- The sum `h_up_eq + h_low_eq = 0` rearranges (via cancellations and adjacency)
      -- to the full rectangle's boundary integral = 0.
      have h_up_re_eq : z_up.re = z'.re := rfl
      have h_up_im_eq : z_up.im = (0 : ℝ) := rfl
      have h_w_up_re_eq : w_up.re = w'.re := rfl
      have h_w_up_im_eq : w_up.im = w'.im := rfl
      have h_low_re_eq : z_low.re = z'.re := rfl
      have h_low_im_eq : z_low.im = z'.im := rfl
      have h_w_low_re_eq : w_low.re = w'.re := rfl
      have h_w_low_im_eq : w_low.im = (0 : ℝ) := rfl
      rw [h_up_re_eq, h_up_im_eq, h_w_up_re_eq, h_w_up_im_eq] at h_up_eq
      rw [h_low_re_eq, h_low_im_eq, h_w_low_re_eq, h_w_low_im_eq] at h_low_eq
      -- Combine `h_up_eq + h_low_eq` into a single equation; the boundary
      -- integral of the full rectangle then follows via `h_split_w` and `h_split_z`.
      have h_sum_eq :
          ((∫ x in z'.re..w'.re, schwarzReflect f (↑x + ↑(0 : ℝ) * Complex.I)) -
              (∫ x in z'.re..w'.re, schwarzReflect f (↑x + ↑w'.im * Complex.I)) +
              Complex.I • (∫ y in (0 : ℝ)..w'.im, schwarzReflect f (↑w'.re + ↑y * Complex.I)) -
              Complex.I • (∫ y in (0 : ℝ)..w'.im, schwarzReflect f (↑z'.re + ↑y * Complex.I))) +
            ((∫ x in z'.re..w'.re, schwarzReflect f (↑x + ↑z'.im * Complex.I)) -
              (∫ x in z'.re..w'.re, schwarzReflect f (↑x + ↑(0 : ℝ) * Complex.I)) +
              Complex.I • (∫ y in z'.im..(0 : ℝ), schwarzReflect f (↑w'.re + ↑y * Complex.I)) -
              Complex.I • (∫ y in z'.im..(0 : ℝ), schwarzReflect f (↑z'.re + ↑y * Complex.I)))
              = 0 := by
        rw [h_up_eq, h_low_eq]; ring
      -- Rearrange to the target form using h_split_w and h_split_z.
      simp only [smul_eq_mul] at h_sum_eq ⊢
      linear_combination h_sum_eq - Complex.I * h_split_w + Complex.I * h_split_z

end NoWanderingDomains
