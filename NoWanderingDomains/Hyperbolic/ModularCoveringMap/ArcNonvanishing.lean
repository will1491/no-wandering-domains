/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.ModularCoveringMap.FundamentalDomainGeometry

/-! # Nonvanishing along the arc of the F_Y contour

Nonvanishing of `λ − w` along the shifted arc `|τ − (1/2 + δ·i)| = R₀` of the `F_Y`
contour. The middle of the arc is controlled by a Lipschitz bound for `Im λ` against
the real-valued `F°` semicircle; the two cusp regions are controlled by the `S`- and
`T`-action identities together with exponential decay bounds. The three cases assemble
into `modularLambdaH_F_Y_arc_ne`.
-/

namespace NoWanderingDomains
open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-! ### Lipschitz control of `Im λ` along the arc

The shifted arc `|τ − (1/2 + δ·i)| = R₀` (for `R₀ > √(1/4 − δ²)`) lies
inside `F^o`, and is close to the F^o semicircle `|τ − 1/2| = 1/2` with
distance bounded by `O(δ)`. On the F^o semicircle, `λ` takes real
values. By continuity of `λ` on the open upper half-plane,
`|Im(λ(arc point))| ≤ M · O(δ)` where `M` is a Lipschitz constant for
`Im λ` on a compact neighborhood of the arc + semicircle.

The infrastructure below packages these helpers as separate lemmas. -/

/-- **Helper 8.1 — Arc-to-semicircle distance.** For arc point
`τ_arc(θ) = (1/2 + δ·i) + R₀·exp(iθ)` and `θ ∈ [0, π]`, there exists
a corresponding F^o semicircle point `τ_sc(θ) = 1/2 + (1/2)·exp(iθ)`
with `|τ_arc(θ) − τ_sc(θ)| ≤ δ + |R₀ − 1/2|`.

Proof: direct triangle inequality:
`τ_arc(θ) − τ_sc(θ) = δ·i + (R₀ − 1/2)·exp(iθ)`,
so `|τ_arc − τ_sc| ≤ δ + |R₀ − 1/2|`. -/
theorem modularLambdaH_arc_to_semicircle_dist
    {δ R₀ : ℝ} (hδ : 0 < δ) (_hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (θ : ℝ) :
    ‖_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ
        - _root_.circleMap (1/2 : ℂ) (1/2) θ‖ ≤ δ + (1/2 - R₀) := by
  -- circleMap c r θ = c + r * exp(θ·I).
  have h_diff_eq : _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ
        - _root_.circleMap (1/2 : ℂ) (1/2) θ
      = (δ : ℂ) * Complex.I + (R₀ - 1/2 : ℝ) * Complex.exp (θ * Complex.I) := by
    unfold circleMap
    push_cast
    ring
  rw [h_diff_eq]
  refine le_trans (norm_add_le _ _) ?_
  have h_norm_δi : ‖(δ : ℂ) * Complex.I‖ = δ := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ]
  have h_norm_R₀_exp : ‖((R₀ - 1/2 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)‖
      = 1/2 - R₀ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith : (R₀ - 1/2 : ℝ) < 0)]
    linarith
  rw [h_norm_δi, h_norm_R₀_exp]

/-- **Helper 8.2 — Im(λ) is locally Lipschitz on the upper half-plane.**
On any closed ball `closedBall τ₀ r` contained in `{Im > 0}`, `Im ∘ λ`
satisfies a Lipschitz bound with constant `M_τ₀_r` (computable from
the supremum of `‖λ'‖` over the ball, which is finite by analyticity
of `λ` on the open upper half-plane).

This is a standard analytic fact (analytic function on a compact
subset of its domain has bounded derivative, hence is Lipschitz). -/
theorem modularLambdaH_im_lipschitz_on_compact
    {τ₀ : ℂ} (_hτ₀ : 0 < τ₀.im) {r : ℝ} (hr : 0 < r)
    (h_ball_in : Metric.closedBall τ₀ r ⊆ {z : ℂ | 0 < z.im}) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ τ' : ℂ,
      τ ∈ Metric.closedBall τ₀ r → τ' ∈ Metric.closedBall τ₀ r →
      |(modularLambdaH τ).im - (modularLambdaH τ').im| ≤ M * ‖τ - τ'‖ := by
  -- Step 1: Open upper half-plane is open.
  have h_open_H : IsOpen ({z : ℂ | 0 < z.im} : Set ℂ) := by
    have h_set_eq : ({z : ℂ | 0 < z.im} : Set ℂ) = Complex.im ⁻¹' Set.Ioi 0 := by
      ext; simp
    rw [h_set_eq]
    exact isOpen_Ioi.preimage Complex.continuous_im
  -- Step 2: From `closedBall τ₀ r ⊆ {Im > 0}`, the minimum imaginary part is
  -- `τ₀.im - r`. Take a slightly larger open ball that still lies in `{Im > 0}`.
  have h_τ₀_minus_r_pos : 0 < τ₀.im - r := by
    have h_min : ((τ₀ - (r : ℂ) * Complex.I)).im = τ₀.im - r := by
      simp [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    have h_in : τ₀ - (r : ℂ) * Complex.I ∈ Metric.closedBall τ₀ r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h_diff : τ₀ - (r : ℂ) * Complex.I - τ₀ = -((r : ℂ) * Complex.I) := by ring
      rw [h_diff, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr]
    have h_im_pos : 0 < (τ₀ - (r : ℂ) * Complex.I).im := h_ball_in h_in
    rw [h_min] at h_im_pos
    exact h_im_pos
  set r' : ℝ := (r + τ₀.im) / 2 with hr'_def
  have hr'_pos : 0 < r' := by rw [hr'_def]; linarith
  have hr_lt_r' : r < r' := by rw [hr'_def]; linarith
  have hr'_lt_τ₀_im : r' < τ₀.im := by rw [hr'_def]; linarith
  -- Both `ball τ₀ r'` and `closedBall τ₀ r'` are contained in `{Im > 0}`,
  -- since for any x in either, `|τ₀.im − x.im| ≤ r' < τ₀.im`, so `x.im > 0`.
  have h_ball'_closed_in : Metric.closedBall τ₀ r' ⊆ ({z : ℂ | 0 < z.im} : Set ℂ) := by
    intro x hx_ball
    rw [Metric.mem_closedBall, dist_eq_norm] at hx_ball
    have h_im_diff : |x.im - τ₀.im| ≤ ‖x - τ₀‖ := by
      have := abs_im_le_norm (x - τ₀)
      rwa [Complex.sub_im] at this
    have h_lower : τ₀.im - x.im ≤ |x.im - τ₀.im| := by
      rw [abs_sub_comm]; exact le_abs_self _
    have : τ₀.im - x.im ≤ r' := le_trans (le_trans h_lower h_im_diff) hx_ball
    change 0 < x.im
    linarith
  have h_ball'_in : Metric.ball τ₀ r' ⊆ ({z : ℂ | 0 < z.im} : Set ℂ) :=
    (Metric.ball_subset_closedBall).trans h_ball'_closed_in
  have h_lam_an : AnalyticOnNhd ℂ modularLambdaH {z : ℂ | 0 < z.im} :=
    modularLambdaH_differentiableOn.analyticOnNhd h_open_H
  have h_deriv_cont_uhp : ContinuousOn (deriv modularLambdaH) {z : ℂ | 0 < z.im} :=
    h_lam_an.deriv.continuousOn
  -- Step 4: Bound `‖deriv λ‖` on closedBall τ₀ r' via compactness.
  have h_compact' : IsCompact (Metric.closedBall τ₀ r') := isCompact_closedBall τ₀ r'
  have h_ne' : (Metric.closedBall τ₀ r').Nonempty :=
    ⟨τ₀, Metric.mem_closedBall_self hr'_pos.le⟩
  have h_deriv_cont' : ContinuousOn (deriv modularLambdaH) (Metric.closedBall τ₀ r') :=
    h_deriv_cont_uhp.mono h_ball'_closed_in
  obtain ⟨τ_max, _hτ_max_in, hτ_max_le⟩ :=
    h_compact'.exists_isMaxOn h_ne' h_deriv_cont'.norm
  set M : ℝ := ‖deriv modularLambdaH τ_max‖ + 1 with hM_def
  have hM_pos : 0 < M := by rw [hM_def]; positivity
  have h_deriv_bound : ∀ x ∈ Metric.closedBall τ₀ r', ‖deriv modularLambdaH x‖ ≤ M := by
    intro x hx
    have h_max : ‖deriv modularLambdaH x‖ ≤ ‖deriv modularLambdaH τ_max‖ :=
      hτ_max_le hx
    rw [hM_def]; linarith
  refine ⟨M, hM_pos, ?_⟩
  intro τ τ' hτ_in hτ'_in
  -- τ, τ' ∈ closedBall τ₀ r ⊆ ball τ₀ r'.
  have hτ_in' : τ ∈ Metric.ball τ₀ r' := by
    rw [Metric.mem_closedBall] at hτ_in
    rw [Metric.mem_ball]
    linarith
  have hτ'_in' : τ' ∈ Metric.ball τ₀ r' := by
    rw [Metric.mem_closedBall] at hτ'_in
    rw [Metric.mem_ball]
    linarith
  -- Step 5: λ is ℂ-differentiable on `ball τ₀ r'` (open ⊆ UHP).
  have h_ball'_open : IsOpen (Metric.ball τ₀ r') := Metric.isOpen_ball
  have h_diff_ℂ_on_ball' : DifferentiableOn ℂ modularLambdaH (Metric.ball τ₀ r') :=
    modularLambdaH_differentiableOn.mono (h_ball'_in.trans (fun _ h => h))
  -- Step 6: UniqueDiffOn ℂ for the open ball.
  have h_unique_diff_ℂ : UniqueDiffOn ℂ (Metric.ball τ₀ r') :=
    h_ball'_open.uniqueDiffOn
  -- Step 7: Bound `‖fderivWithin ℂ λ s x‖` on the open ball, via
  --   `fderivWithin = fderiv` (open set), then `‖fderiv ℂ λ‖ = ‖deriv λ‖`.
  have h_convex_ball' : Convex ℝ (Metric.ball τ₀ r') := convex_ball _ _
  have h_fderiv_bound_ball' : ∀ x ∈ Metric.ball τ₀ r',
      ‖fderivWithin ℂ modularLambdaH (Metric.ball τ₀ r') x‖ ≤ M := by
    intro x hx
    have hx_uhp : x ∈ ({z : ℂ | 0 < z.im} : Set ℂ) := h_ball'_in hx
    have h_diff_ℂ_at : DifferentiableAt ℂ modularLambdaH x :=
      (h_lam_an x hx_uhp).differentiableAt
    rw [h_diff_ℂ_at.fderivWithin (h_unique_diff_ℂ x hx), ← norm_deriv_eq_norm_fderiv]
    have hx_closed : x ∈ Metric.closedBall τ₀ r' := Metric.ball_subset_closedBall hx
    exact h_deriv_bound x hx_closed
  -- Step 8: Apply MVT (𝕜 = ℂ) on the open ball.
  have h_mvt : ‖modularLambdaH τ - modularLambdaH τ'‖ ≤ M * ‖τ - τ'‖ :=
    h_convex_ball'.norm_image_sub_le_of_norm_fderivWithin_le
      h_diff_ℂ_on_ball' h_fderiv_bound_ball' hτ'_in' hτ_in'
  -- Step 9: |Im (a - b)| ≤ ‖a - b‖.
  have h_im_bound : |(modularLambdaH τ).im - (modularLambdaH τ').im| ≤
      ‖modularLambdaH τ - modularLambdaH τ'‖ := by
    have h_le := abs_im_le_norm (modularLambdaH τ - modularLambdaH τ')
    rwa [Complex.sub_im] at h_le
  linarith

/-- **Helper 8.3.a — Lipschitz ball lies in the upper half-plane.**
The closed ball `closedBall ((1/2 : ℂ) + i/(2 sin θ_0)) ((1 + cos θ_0)/
(4 sin θ_0))` (used in Helper 8.3) is contained in `{Im > 0}`. -/
theorem modularLambdaH_arc_lipschitz_ball_in_uhp
    {θ_0 : ℝ} (hθ_0_pos : 0 < θ_0) (hθ_0_lt : θ_0 < Real.pi / 2) :
    Metric.closedBall ((1/2 : ℂ) +
        Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ))
        ((1 + Real.cos θ_0) / (4 * Real.sin θ_0)) ⊆
      ({z : ℂ | 0 < z.im} : Set ℂ) := by
  have hθ_0_lt_pi : θ_0 < Real.pi := lt_trans hθ_0_lt (by linarith [Real.pi_pos])
  have hs_pos : 0 < Real.sin θ_0 :=
    Real.sin_pos_of_pos_of_lt_pi hθ_0_pos hθ_0_lt_pi
  have hc_pos : 0 < Real.cos θ_0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_0_lt⟩
  have hs_le_one : Real.sin θ_0 ≤ 1 := Real.sin_le_one θ_0
  have hc_le_one : Real.cos θ_0 ≤ 1 := Real.cos_le_one θ_0
  have hsc_sq : Real.sin θ_0 ^ 2 + Real.cos θ_0 ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq θ_0
  have hc_lt_one : Real.cos θ_0 < 1 := by
    nlinarith [hsc_sq, sq_nonneg (Real.sin θ_0), hs_pos]
  have h_2s_pos : 0 < 2 * Real.sin θ_0 := by linarith
  have h_4s_pos : 0 < 4 * Real.sin θ_0 := by linarith
  -- The center has Im = 1/(2 sin θ_0).
  have hτ_K_im : ((1/2 : ℂ) + Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ)).im =
      1 / (2 * Real.sin θ_0) := by
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by
      rw [Complex.div_im]; simp
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_im]
    ring
  -- The radius is < center's Im, so the ball is in UHP.
  have hr_K_lt : (1 + Real.cos θ_0) / (4 * Real.sin θ_0) <
      1 / (2 * Real.sin θ_0) := by
    rw [div_lt_div_iff₀ h_4s_pos h_2s_pos]
    nlinarith [hc_lt_one, hs_pos]
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  have h_im_le : |x.im -
      ((1/2 : ℂ) + Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ)).im| ≤
      ‖x - ((1/2 : ℂ) + Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ))‖ := by
    have := abs_im_le_norm (x -
      ((1/2 : ℂ) + Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ)))
    rwa [Complex.sub_im] at this
  have h_lower : ((1/2 : ℂ) +
      Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ)).im - x.im ≤
      |x.im - ((1/2 : ℂ) + Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ)).im| := by
    rw [abs_sub_comm]; exact le_abs_self _
  have h_diff_le : ((1/2 : ℂ) +
      Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ)).im - x.im ≤
      (1 + Real.cos θ_0) / (4 * Real.sin θ_0) :=
    le_trans (le_trans h_lower h_im_le) hx
  change 0 < x.im
  rw [hτ_K_im] at h_diff_le
  linarith [hr_K_lt]

/-- **Helper 8.3.b — Semicircle point lies in the Lipschitz ball.**
For `θ ∈ [θ_0, π − θ_0]`, the F^o semicircle point
`circleMap (1/2) (1/2) θ` is contained in the closed ball used by
Helper 8.3. -/
theorem modularLambdaH_arc_lipschitz_semi_in_ball
    {θ_0 : ℝ} (hθ_0_pos : 0 < θ_0) (hθ_0_lt : θ_0 < Real.pi / 2)
    {θ : ℝ} (hθ_lo : θ_0 ≤ θ) (hθ_hi : θ ≤ Real.pi - θ_0) :
    _root_.circleMap (1/2 : ℂ) (1/2) θ ∈
      Metric.closedBall ((1/2 : ℂ) +
        Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ))
        ((1 + Real.cos θ_0) / (4 * Real.sin θ_0)) := by
  have hθ_0_lt_pi : θ_0 < Real.pi := lt_trans hθ_0_lt (by linarith [Real.pi_pos])
  have hs_pos : 0 < Real.sin θ_0 :=
    Real.sin_pos_of_pos_of_lt_pi hθ_0_pos hθ_0_lt_pi
  have hc_pos : 0 < Real.cos θ_0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_0_lt⟩
  have hs_le_one : Real.sin θ_0 ≤ 1 := Real.sin_le_one θ_0
  have hc_le_one : Real.cos θ_0 ≤ 1 := Real.cos_le_one θ_0
  have hsc_sq : Real.sin θ_0 ^ 2 + Real.cos θ_0 ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq θ_0
  have h_2s_pos : 0 < 2 * Real.sin θ_0 := by linarith
  have h_4s_pos : 0 < 4 * Real.sin θ_0 := by linarith
  have h_16s2_pos : 0 < 16 * Real.sin θ_0 ^ 2 := by positivity
  have h_4s2_pos : 0 < 4 * Real.sin θ_0 ^ 2 := by positivity
  -- sin θ ≥ sin θ_0 for θ ∈ [θ_0, π - θ_0].
  have hθ_pos : 0 < θ := lt_of_lt_of_le hθ_0_pos hθ_lo
  have hθ_lt_pi : θ < Real.pi := by linarith
  have hθ_sin_lo : Real.sin θ_0 ≤ Real.sin θ := by
    by_cases h : θ ≤ Real.pi / 2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h hθ_lo
    · push Not at h
      have h_pi_sub_lo : θ_0 ≤ Real.pi - θ := by linarith
      have h_pi_sub_hi : Real.pi - θ ≤ Real.pi / 2 := by linarith
      have h_sym : Real.sin θ = Real.sin (Real.pi - θ) := (Real.sin_pi_sub θ).symm
      rw [h_sym]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h_pi_sub_hi h_pi_sub_lo
  have hθ_sq_sum : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  -- Compute distance² = (cos θ / 2)² + (sin θ / 2 - 1/(2s))².
  rw [Metric.mem_closedBall, dist_eq_norm]
  -- Use sq_le_sq' or sqrt_le_sqrt argument.
  set semi : ℂ := _root_.circleMap (1/2 : ℂ) (1/2) θ with hsemi_def
  set τ_K : ℂ := (1/2 : ℂ) +
    Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ) with hτ_K_def
  set r_K : ℝ := (1 + Real.cos θ_0) / (4 * Real.sin θ_0) with hr_K_def
  have hr_K_nn : 0 ≤ r_K := by
    rw [hr_K_def]; positivity
  -- semi.re and semi.im.
  have hsemi_re : semi.re = 1/2 + (1/2) * Real.cos θ := by
    rw [hsemi_def, _root_.circleMap]
    simp [Complex.add_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
  have hsemi_im : semi.im = (1/2) * Real.sin θ := by
    rw [hsemi_def, _root_.circleMap]
    simp [Complex.add_im, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  -- τ_K.re and τ_K.im.
  have hτ_K_re : τ_K.re = 1/2 := by
    rw [hτ_K_def]
    have h_half_re : ((1 : ℂ) / 2).re = 1/2 := by rw [Complex.div_re]; simp
    rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_re]
    ring
  have hτ_K_im : τ_K.im = 1 / (2 * Real.sin θ_0) := by
    rw [hτ_K_def]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_im]
    ring
  -- Difference.
  have h_sub_re : (semi - τ_K).re = (1/2) * Real.cos θ := by
    rw [Complex.sub_re, hsemi_re, hτ_K_re]; ring
  have h_sub_im : (semi - τ_K).im = (1/2) * Real.sin θ - 1 / (2 * Real.sin θ_0) := by
    rw [Complex.sub_im, hsemi_im, hτ_K_im]
  -- Squared norm.
  have h_normSq_eq : ‖semi - τ_K‖ ^ 2 = ((1/2) * Real.cos θ) ^ 2 +
      ((1/2) * Real.sin θ - 1 / (2 * Real.sin θ_0)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, h_sub_re, h_sub_im]
    ring
  -- The bound: ((1/2) cos θ)² + ((1/2) sin θ - 1/(2 sin θ_0))² ≤ r_K².
  have h_bound : ‖semi - τ_K‖ ^ 2 ≤ r_K ^ 2 := by
    rw [h_normSq_eq, hr_K_def, div_pow]
    have h_denom : (4 * Real.sin θ_0) ^ 2 = 16 * Real.sin θ_0 ^ 2 := by ring
    rw [h_denom]
    rw [le_div_iff₀ h_16s2_pos]
    -- Goal: (cos²θ/4 + (sin θ/2 - 1/(2 s))²) * (16 s²) ≤ (1+c)²
    have h_expand : (((1/2) * Real.cos θ) ^ 2 +
        ((1/2) * Real.sin θ - 1 / (2 * Real.sin θ_0)) ^ 2) *
        (16 * Real.sin θ_0 ^ 2) =
        4 * Real.sin θ_0 ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) -
        8 * Real.sin θ_0 * Real.sin θ + 4 := by
      field_simp
      ring
    rw [h_expand, add_comm (Real.cos θ ^ 2) _, hθ_sq_sum, mul_one]
    -- Goal: 4 s² - 8 s sin θ + 4 ≤ (1+c)²
    -- Using sin θ ≥ s: 8 s sin θ ≥ 8 s².
    -- 4 s² - 8 s² + 4 = -4 s² + 4 = 4(1 - s²) = 4 c².
    -- Need 4 c² ≤ (1+c)² i.e., (1-c)(1+3c) ≥ 0.
    have h_step1 : 4 * Real.sin θ_0 ^ 2 - 8 * Real.sin θ_0 * Real.sin θ + 4 ≤
        4 * Real.sin θ_0 ^ 2 - 8 * Real.sin θ_0 * Real.sin θ_0 + 4 := by
      have h_mul_le : 8 * Real.sin θ_0 * Real.sin θ_0 ≤
          8 * Real.sin θ_0 * Real.sin θ := by
        have h_8s_pos : 0 < 8 * Real.sin θ_0 := by linarith
        exact mul_le_mul_of_nonneg_left hθ_sin_lo h_8s_pos.le
      linarith
    apply le_trans h_step1
    -- Goal: 4 s² - 8 s² + 4 ≤ (1+c)²
    -- = -4 s² + 4 = 4(1 - s²) = 4 c². Need 4 c² ≤ (1+c)².
    nlinarith [hsc_sq, hc_pos, hc_le_one, sq_nonneg (1 - Real.cos θ_0),
               sq_nonneg (Real.cos θ_0)]
  -- Take square roots.
  have h_sqrt := Real.sqrt_le_sqrt h_bound
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hr_K_nn] at h_sqrt
  exact h_sqrt

/-- **Helper 8.3.c.aux — Pure polynomial inequality used by Helper 8.3.c.**
For `s, c ∈ [0, 1]` with `s² + c² = 1` and `δ ∈ (0, s/4]`:
`16 s⁴ δ² + 4 c² (1 − 2sδ)² ≤ (1 + c)²`. The proof reduces to two
bounds (`16 s⁴ δ² ≤ s⁶ = (1-c²)³` and `4 c² (1-2sδ)² ≤ 4c²`) and the
polynomial inequality `(1-c²)³ + 4c² ≤ (1+c)²`. -/
theorem modularLambdaH_arc_lipschitz_poly_ineq
    {s c δ : ℝ} (hs_pos : 0 < s) (hs_le_one : s ≤ 1)
    (hc_pos : 0 < c) (hc_le_one : c ≤ 1) (hsc_sq : s ^ 2 + c ^ 2 = 1)
    (hδ : 0 < δ) (hδ_small : δ ≤ s / 4) :
    16 * s ^ 4 * δ ^ 2 + 4 * c ^ 2 * (1 - 2 * s * δ) ^ 2 ≤ (1 + c) ^ 2 := by
  -- 16 s⁴ δ² ≤ s⁶ (since δ ≤ s/4 gives δ² ≤ s²/16).
  have h_first_le : 16 * s ^ 4 * δ ^ 2 ≤ s ^ 6 := by
    have h_4δ_le_s : 4 * δ ≤ s := by linarith [hδ_small]
    have h_sq_bound : 16 * δ ^ 2 ≤ s ^ 2 := by
      nlinarith [h_4δ_le_s, hδ, hs_pos]
    have h_s6_eq : s ^ 6 = s ^ 4 * s ^ 2 := by ring
    rw [h_s6_eq]
    have h_s4_nn : 0 ≤ s ^ 4 := by positivity
    nlinarith [h_sq_bound, h_s4_nn]
  -- 4 c² (1 - 2sδ)² ≤ 4 c² (since 0 ≤ 1 - 2sδ ≤ 1, so (1-2sδ)² ≤ 1).
  have h_2sδ_nn : 0 ≤ 1 - 2 * s * δ := by
    nlinarith [hs_le_one, hδ_small, hs_pos]
  have h_2sδ_le_one : 1 - 2 * s * δ ≤ 1 := by nlinarith [hs_pos, hδ]
  have h_sq_le_one : (1 - 2 * s * δ) ^ 2 ≤ 1 := by
    nlinarith [h_2sδ_nn, h_2sδ_le_one]
  have h_second_le : 4 * c ^ 2 * (1 - 2 * s * δ) ^ 2 ≤ 4 * c ^ 2 := by
    nlinarith [sq_nonneg c, h_sq_le_one, hc_pos]
  -- s⁶ = (1 - c²)³.
  have h_s6_eq : s ^ 6 = (1 - c ^ 2) ^ 3 := by
    have hs_sq_eq : s ^ 2 = 1 - c ^ 2 := by linarith [hsc_sq]
    have : s ^ 6 = (s ^ 2) ^ 3 := by ring
    rw [this, hs_sq_eq]
  have h_LHS_le : 16 * s ^ 4 * δ ^ 2 + 4 * c ^ 2 * (1 - 2 * s * δ) ^ 2 ≤
      (1 - c ^ 2) ^ 3 + 4 * c ^ 2 := by
    linarith [h_first_le, h_second_le, h_s6_eq]
  apply le_trans h_LHS_le
  -- Polynomial inequality: (1 - c²)³ + 4 c² ≤ (1+c)² for c ∈ [0, 1].
  -- Reduces to (1-c)²(1+c)³ ≤ 1 + 3c, i.e., c(2 + 2c + 2c² - c³ - c⁴) ≥ 0.
  nlinarith [hc_pos, hc_le_one, sq_nonneg c, sq_nonneg (1 - c),
             sq_nonneg (1 + c), mul_nonneg hc_pos.le hc_pos.le,
             mul_nonneg (sq_nonneg c) (sq_nonneg (1 - c)),
             mul_nonneg (sq_nonneg (1 - c)) (sq_nonneg (1 - c))]

set_option maxHeartbeats 400000 in
-- nlinarith chain over the arc-ball geometry exceeds the default 200000 budget.
/-- **Helper 8.3.c — Arc point lies in the Lipschitz ball.**
For F^o arc parameters with `R₀ > √(1/4 − δ²)`, `R₀ < 1/2`, and
`δ ≤ sin θ_0 / 4`, the arc point
`circleMap (1/2 + δi) R₀ θ` lies in the closed ball used by Helper 8.3
for any `θ ∈ [θ_0, π − θ_0]`. The lower bound on `R₀` is essential:
the geometric argument shows
`|arc(θ) − τ_K|² ≤ (sδ)² + (1/(2s) − δ)² cos² θ_0`, which is sharp
because `R₀ > 1/2 − s δ` (a strict consequence of `R₀ > √(1/4 − δ²)`
when `δ ≤ s/4`). -/
theorem modularLambdaH_arc_lipschitz_arc_in_ball
    {δ R₀ : ℝ} (hδ : 0 < δ)
    (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀) (hR₀_lt : R₀ < 1 / 2)
    {θ_0 : ℝ} (hθ_0_pos : 0 < θ_0) (hθ_0_lt : θ_0 < Real.pi / 2)
    (hδ_small : δ ≤ Real.sin θ_0 / 4)
    {θ : ℝ} (hθ_lo : θ_0 ≤ θ) (hθ_hi : θ ≤ Real.pi - θ_0) :
    _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ ∈
      Metric.closedBall ((1/2 : ℂ) +
        Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ))
        ((1 + Real.cos θ_0) / (4 * Real.sin θ_0)) := by
  have hθ_0_lt_pi : θ_0 < Real.pi := lt_trans hθ_0_lt (by linarith [Real.pi_pos])
  have hs_pos : 0 < Real.sin θ_0 :=
    Real.sin_pos_of_pos_of_lt_pi hθ_0_pos hθ_0_lt_pi
  have hc_pos : 0 < Real.cos θ_0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_0_lt⟩
  have hs_le_one : Real.sin θ_0 ≤ 1 := Real.sin_le_one θ_0
  have hc_le_one : Real.cos θ_0 ≤ 1 := Real.cos_le_one θ_0
  have hsc_sq : Real.sin θ_0 ^ 2 + Real.cos θ_0 ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq θ_0
  have h_2s_pos : 0 < 2 * Real.sin θ_0 := by linarith
  have h_4s_pos : 0 < 4 * Real.sin θ_0 := by linarith
  have h_16s2_pos : 0 < 16 * Real.sin θ_0 ^ 2 := by positivity
  -- Useful arithmetic: δ ≤ 1/4 (since δ ≤ s/4 ≤ 1/4).
  have hδ_le_quarter : δ ≤ 1 / 4 := by
    have : δ ≤ Real.sin θ_0 / 4 := hδ_small
    linarith [hs_le_one]
  -- 2 s δ ≤ 1/2, so 1 - 2 s δ ≥ 1/2 > 0.
  have h_2sδ_le_half : 2 * Real.sin θ_0 * δ ≤ 1 / 2 := by
    nlinarith [hs_le_one, hδ_le_quarter]
  -- R₀ > 1/2 - s δ. Key reduction via R₀ > √(1/4 - δ²).
  have h_half_sub_sδ_pos : 0 < 1 / 2 - Real.sin θ_0 * δ := by
    nlinarith [hs_le_one, hδ_le_quarter]
  have h_arg_nn : (0 : ℝ) ≤ 1 / 4 - δ ^ 2 := by nlinarith [hδ_le_quarter]
  have h_sqrt_gt_us : 1 / 2 - Real.sin θ_0 * δ < Real.sqrt (1 / 4 - δ ^ 2) := by
    have h_diff_pos : (1 / 2 - Real.sin θ_0 * δ) ^ 2 < 1 / 4 - δ ^ 2 := by
      nlinarith [hδ_small, hs_pos, hs_le_one, sq_nonneg (Real.sin θ_0),
                 sq_nonneg δ, mul_pos hs_pos hδ]
    calc 1 / 2 - Real.sin θ_0 * δ
        = Real.sqrt ((1 / 2 - Real.sin θ_0 * δ) ^ 2) := by
          rw [Real.sqrt_sq h_half_sub_sδ_pos.le]
      _ < Real.sqrt (1 / 4 - δ ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) h_diff_pos
  have hR₀_gt_us : 1 / 2 - Real.sin θ_0 * δ < R₀ :=
    lt_trans h_sqrt_gt_us hR₀_lo
  -- sin θ ≥ sin θ_0 for θ ∈ [θ_0, π - θ_0].
  have hθ_pos : 0 < θ := lt_of_lt_of_le hθ_0_pos hθ_lo
  have hθ_lt_pi : θ < Real.pi := by linarith
  have hθ_sin_lo : Real.sin θ_0 ≤ Real.sin θ := by
    by_cases h : θ ≤ Real.pi / 2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h hθ_lo
    · push Not at h
      have h_sym : Real.sin θ = Real.sin (Real.pi - θ) := (Real.sin_pi_sub θ).symm
      rw [h_sym]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith)
        (by linarith)
  have hθ_sq_sum : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  -- Set up.
  rw [Metric.mem_closedBall, dist_eq_norm]
  set arc : ℂ := _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ
    with harc_def
  set τ_K : ℂ := (1/2 : ℂ) +
    Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ) with hτ_K_def
  set r_K : ℝ := (1 + Real.cos θ_0) / (4 * Real.sin θ_0) with hr_K_def
  have hr_K_nn : 0 ≤ r_K := by rw [hr_K_def]; positivity
  -- arc.re and arc.im.
  have harc_re : arc.re = 1/2 + R₀ * Real.cos θ := by
    rw [harc_def, _root_.circleMap]
    simp [Complex.add_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have harc_im : arc.im = δ + R₀ * Real.sin θ := by
    rw [harc_def, _root_.circleMap]
    simp [Complex.add_im, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  -- τ_K.re and τ_K.im.
  have hτ_K_re : τ_K.re = 1/2 := by
    rw [hτ_K_def]
    have h_half_re : ((1 : ℂ) / 2).re = 1/2 := by rw [Complex.div_re]; simp
    rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_re]
    ring
  have hτ_K_im : τ_K.im = 1 / (2 * Real.sin θ_0) := by
    rw [hτ_K_def]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_im]
    ring
  -- Difference.
  have h_sub_re : (arc - τ_K).re = R₀ * Real.cos θ := by
    rw [Complex.sub_re, harc_re, hτ_K_re]; ring
  have h_sub_im : (arc - τ_K).im = δ + R₀ * Real.sin θ - 1 / (2 * Real.sin θ_0) := by
    rw [Complex.sub_im, harc_im, hτ_K_im]
  -- Squared norm.
  have h_normSq_eq : ‖arc - τ_K‖ ^ 2 = (R₀ * Real.cos θ) ^ 2 +
      (δ + R₀ * Real.sin θ - 1 / (2 * Real.sin θ_0)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, h_sub_re, h_sub_im]
    ring
  -- Bound: |arc - τ_K|² ≤ r_K².
  -- Strategy: use the algebraic identity
  --   (R₀ cos θ)² + (δ + R₀ sin θ - 1/(2s))²
  --   ≤ (R₀ - (1/2 - sδ))² + (1/(2s) - δ)² c²    (using sin θ ≥ s)
  --   ≤ (sδ)² + (1/(2s) - δ)² c²                  (using R₀ - (1/2-sδ) < sδ)
  --   ≤ ((1+c)/(4s))² = r_K²                       (polynomial inequality)
  have h_bound : ‖arc - τ_K‖ ^ 2 ≤ r_K ^ 2 := by
    rw [h_normSq_eq]
    -- Step A: LHS = R₀² - 2 R₀ (1/(2s) - δ) sin θ + (1/(2s) - δ)²
    have h_step_A_eq : (R₀ * Real.cos θ) ^ 2 +
        (δ + R₀ * Real.sin θ - 1 / (2 * Real.sin θ_0)) ^ 2 =
        R₀ ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) -
        2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) * Real.sin θ +
        (1 / (2 * Real.sin θ_0) - δ) ^ 2 := by ring
    rw [h_step_A_eq, add_comm (Real.cos θ ^ 2) _, hθ_sq_sum, mul_one]
    -- Now goal: R₀² - 2 R₀ u sin θ + u² ≤ r_K²  where u := 1/(2s) - δ.
    -- Step B: replace sin θ by s (since coefficient of sin θ is negative).
    have h_u_pos : 0 < 1 / (2 * Real.sin θ_0) - δ := by
      have h_one_2s_ge : 1 / (2 * Real.sin θ_0) ≥ 1 / 2 := by
        rw [ge_iff_le, le_div_iff₀ h_2s_pos]
        nlinarith [hs_le_one, hs_pos]
      linarith [hs_le_one, hs_pos, hδ_small,
                show Real.sin θ_0 / 4 ≤ 1 / 4 from by linarith]
    have hR₀_pos : 0 < R₀ := by
      have h_sqrt_nn : 0 ≤ Real.sqrt (1 / 4 - δ ^ 2) := Real.sqrt_nonneg _
      linarith
    have h_factor_pos : 0 < 2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) := by positivity
    have h_step_B :
        R₀ ^ 2 -
          2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) * Real.sin θ +
          (1 / (2 * Real.sin θ_0) - δ) ^ 2 ≤
        R₀ ^ 2 -
          2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) * Real.sin θ_0 +
          (1 / (2 * Real.sin θ_0) - δ) ^ 2 := by
      have h_mul_le :
          2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) * Real.sin θ_0 ≤
          2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) * Real.sin θ :=
        mul_le_mul_of_nonneg_left hθ_sin_lo h_factor_pos.le
      linarith
    apply le_trans h_step_B
    -- Step C: identity R₀² - 2 R₀ u s + u² = (R₀ - us)² + u² c²
    have h_step_C_eq :
        R₀ ^ 2 -
          2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) * Real.sin θ_0 +
          (1 / (2 * Real.sin θ_0) - δ) ^ 2 =
        (R₀ - Real.sin θ_0 * (1 / (2 * Real.sin θ_0) - δ)) ^ 2 +
        (1 / (2 * Real.sin θ_0) - δ) ^ 2 * Real.cos θ_0 ^ 2 := by
      have hs_sq_sub : 1 - Real.sin θ_0 ^ 2 = Real.cos θ_0 ^ 2 := by linarith [hsc_sq]
      have h_eq : R₀ ^ 2 -
          2 * R₀ * (1 / (2 * Real.sin θ_0) - δ) * Real.sin θ_0 +
          (1 / (2 * Real.sin θ_0) - δ) ^ 2 =
          (R₀ - Real.sin θ_0 * (1 / (2 * Real.sin θ_0) - δ)) ^ 2 +
          (1 / (2 * Real.sin θ_0) - δ) ^ 2 * (1 - Real.sin θ_0 ^ 2) := by ring
      rw [h_eq, hs_sq_sub]
    rw [h_step_C_eq]
    -- Step D: simplify s·(1/(2s) - δ) = 1/2 - sδ.
    have h_us_eq : Real.sin θ_0 * (1 / (2 * Real.sin θ_0) - δ) =
        1 / 2 - Real.sin θ_0 * δ := by
      field_simp
    rw [h_us_eq]
    -- Step E: (R₀ - (1/2 - sδ))² ≤ (sδ)² (key R₀ bound).
    have h_R₀_diff_pos : 0 < R₀ - (1 / 2 - Real.sin θ_0 * δ) := by linarith
    have h_R₀_diff_lt : R₀ - (1 / 2 - Real.sin θ_0 * δ) < Real.sin θ_0 * δ := by linarith
    have h_R₀_sq_le : (R₀ - (1 / 2 - Real.sin θ_0 * δ)) ^ 2 ≤
        (Real.sin θ_0 * δ) ^ 2 := by
      nlinarith [h_R₀_diff_pos, h_R₀_diff_lt, sq_nonneg (Real.sin θ_0 * δ)]
    have h_step_D :
        (R₀ - (1 / 2 - Real.sin θ_0 * δ)) ^ 2 +
          (1 / (2 * Real.sin θ_0) - δ) ^ 2 * Real.cos θ_0 ^ 2 ≤
        (Real.sin θ_0 * δ) ^ 2 +
          (1 / (2 * Real.sin θ_0) - δ) ^ 2 * Real.cos θ_0 ^ 2 := by
      linarith [h_R₀_sq_le]
    apply le_trans h_step_D
    -- Step F: (sδ)² + (1/(2s) - δ)² c² ≤ r_K² = ((1+c)/(4s))².
    -- Reformulate the bound using `1/(2s) - δ = (1 - 2sδ)/(2s)`.
    have h_u_rewrite : 1 / (2 * Real.sin θ_0) - δ =
        (1 - 2 * Real.sin θ_0 * δ) / (2 * Real.sin θ_0) := by
      field_simp
    rw [h_u_rewrite, hr_K_def]
    simp only [div_pow]
    have h_denom : (4 * Real.sin θ_0) ^ 2 = 16 * Real.sin θ_0 ^ 2 := by ring
    rw [h_denom, le_div_iff₀ h_16s2_pos]
    -- After substitution: ((sδ)² + (1 - 2sδ)²/(2s)² · c²) · 16 s² ≤ (1+c)²
    have h_normalize :
        ((Real.sin θ_0 * δ) ^ 2 +
          (1 - 2 * Real.sin θ_0 * δ) ^ 2 / (2 * Real.sin θ_0) ^ 2 *
            Real.cos θ_0 ^ 2) * (16 * Real.sin θ_0 ^ 2) =
        16 * Real.sin θ_0 ^ 4 * δ ^ 2 +
        4 * Real.cos θ_0 ^ 2 * (1 - 2 * Real.sin θ_0 * δ) ^ 2 := by
      field_simp
      ring
    rw [h_normalize]
    -- Apply the pure polynomial helper.
    exact modularLambdaH_arc_lipschitz_poly_ineq hs_pos hs_le_one hc_pos hc_le_one
      hsc_sq hδ hδ_small
  -- Take square roots.
  have h_sqrt := Real.sqrt_le_sqrt h_bound
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hr_K_nn] at h_sqrt
  exact h_sqrt

/-- **Helper 8.3 — Compact-set Lipschitz bound on the arc.**
For F^o arc parameters `(δ, R₀)` with `R₀ > √(1/4 − δ²)`, `R₀ < 1/2`,
`δ ≤ sin θ_0 / 4`, and `θ ∈ [θ_0, π − θ_0]` (away from the two cusps
by `θ_0`), the arc point `circleMap (1/2 + δi) R₀ θ` and the F^o
semicircle point `circleMap (1/2) (1/2) θ` both lie in the fixed
compact ball `closedBall (1/2 + i/(2 sin θ_0)) ((1 + cos θ_0)/
(4 sin θ_0))` contained in the upper half-plane (Helpers 8.3.a/b/c).
Apply Helper 8.2 to obtain a Lipschitz constant `M`, then chain with
Helper 8.1's distance bound to conclude.

The cusp endpoints (`θ ∈ [0, θ_0) ∪ (π − θ_0, π]`) are handled
separately in `modularLambdaH_F_Y_arc_ne` via cusp asymptotics. -/
theorem modularLambdaH_arc_lipschitz_away_from_cusps
    {δ R₀ : ℝ} (hδ : 0 < δ) (hR₀_pos : 0 < R₀)
    (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀) (hR₀_lt : R₀ < 1 / 2)
    {θ_0 : ℝ} (hθ_0_pos : 0 < θ_0) (hθ_0_lt : θ_0 < Real.pi / 2)
    (hδ_small : δ ≤ Real.sin θ_0 / 4) :
    ∃ M : ℝ, 0 < M ∧ ∀ θ : ℝ, θ_0 ≤ θ → θ ≤ Real.pi - θ_0 →
      |(modularLambdaH (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ)).im|
        ≤ M * (δ + (1/2 - R₀)) := by
  have hθ_0_lt_pi : θ_0 < Real.pi := lt_trans hθ_0_lt (by linarith [Real.pi_pos])
  have hs_pos : 0 < Real.sin θ_0 :=
    Real.sin_pos_of_pos_of_lt_pi hθ_0_pos hθ_0_lt_pi
  have h_2s_pos : 0 < 2 * Real.sin θ_0 := by linarith
  -- The center τ_K = (1/2 : ℂ) + i/(2 sin θ_0) has positive Im.
  have hτ_K_im_pos : 0 < ((1/2 : ℂ) +
      Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ)).im := by
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_im]
    have h_pos : 0 < 1 / (2 * Real.sin θ_0) := by positivity
    linarith
  have hr_K_pos : 0 < (1 + Real.cos θ_0) / (4 * Real.sin θ_0) := by
    have hc_nn : 0 ≤ Real.cos θ_0 :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθ_0_lt.le⟩
    have h_4s_pos : 0 < 4 * Real.sin θ_0 := by linarith
    positivity
  -- Apply Helper 8.3.a: ball is in UHP.
  have h_ball_in := modularLambdaH_arc_lipschitz_ball_in_uhp hθ_0_pos hθ_0_lt
  -- Apply Helper 8.2: Lipschitz constant M.
  obtain ⟨M, hM_pos, hM_lipschitz⟩ :=
    modularLambdaH_im_lipschitz_on_compact hτ_K_im_pos hr_K_pos h_ball_in
  refine ⟨M, hM_pos, ?_⟩
  intro θ hθ_lo hθ_hi
  -- Apply Helpers 8.3.b and 8.3.c.
  have h_semi_in := modularLambdaH_arc_lipschitz_semi_in_ball hθ_0_pos hθ_0_lt hθ_lo hθ_hi
  have h_arc_in := modularLambdaH_arc_lipschitz_arc_in_ball hδ hR₀_lo hR₀_lt
    hθ_0_pos hθ_0_lt hδ_small hθ_lo hθ_hi
  -- semicircle point has positive Im (sin θ > 0).
  have hθ_pos : 0 < θ := lt_of_lt_of_le hθ_0_pos hθ_lo
  have hθ_lt_pi : θ < Real.pi := by linarith
  have hθ_sin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  have h_semi_im_pos : 0 < (_root_.circleMap (1/2 : ℂ) (1/2) θ).im := by
    rw [_root_.circleMap]
    show 0 < ((1/2 : ℂ) + ((1/2 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)).im
    rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [h_half_im]
    have h_pos : 0 < (1 / 2 : ℝ) * Real.sin θ := by positivity
    linarith
  -- The point is on the semicircle: ‖2 · semi - 1‖ = 1.
  have h_semi_circle : ‖2 * (_root_.circleMap (1/2 : ℂ) (1/2) θ) - 1‖ = 1 := by
    rw [_root_.circleMap]
    have h_simplify : 2 * ((1/2 : ℂ) + ((1/2 : ℝ) : ℂ) *
        Complex.exp (θ * Complex.I)) - 1 = Complex.exp (θ * Complex.I) := by
      push_cast; ring
    rw [h_simplify, Complex.norm_exp]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  -- Im λ(semi) = 0 (semicircle real-valued).
  have h_semi_im_zero : (modularLambdaH (_root_.circleMap (1/2 : ℂ) (1/2) θ)).im = 0 :=
    modularLambdaH_semicircle_real h_semi_im_pos h_semi_circle
  -- Apply Helper 8.2 Lipschitz to arc and semicircle points.
  have h_lip := hM_lipschitz
    (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ)
    (_root_.circleMap (1/2 : ℂ) (1/2) θ) h_arc_in h_semi_in
  rw [h_semi_im_zero, sub_zero] at h_lip
  -- Apply Helper 8.1: distance bound `δ + (1/2 - R₀)`.
  have h_dist := modularLambdaH_arc_to_semicircle_dist hδ hR₀_pos hR₀_lt θ
  -- Combine: |Im λ(arc)| ≤ M · ‖arc - semi‖ ≤ M · (δ + (1/2 - R₀)).
  calc |(modularLambdaH (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ)).im|
      ≤ M * ‖_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ -
              _root_.circleMap (1/2 : ℂ) (1/2) θ‖ := h_lip
    _ ≤ M * (δ + (1/2 - R₀)) := by
        apply mul_le_mul_of_nonneg_left _ hM_pos.le
        convert h_dist using 1

/-! ### Arc nonvanishing near the cusps -/

/-- **Arc has positive imaginary part.** For
`δ > 0` and `θ ∈ [0, π]`, the arc point `circleMap (1/2 + δi) R₀ θ`
has `Im > 0`. -/
theorem modularLambdaH_F_Y_arc_im_pos
    {δ R₀ : ℝ} (hδ : 0 < δ) (hR₀_nn : 0 ≤ R₀)
    {θ : ℝ} (hθ_lo : 0 ≤ θ) (hθ_hi : θ ≤ Real.pi) :
    0 < (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ).im := by
  rw [_root_.circleMap]
  simp only [Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, mul_zero,
    mul_one, zero_mul]
  have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
  rw [h_half_im]
  have h_sin_nn : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ_lo, hθ_hi⟩
  have h_term : 0 ≤ R₀ * Real.sin θ := mul_nonneg hR₀_nn h_sin_nn
  linarith [hδ, h_term]

/-- **Squared norm of the arc.** Convenience lemma. -/
theorem modularLambdaH_F_Y_arc_normSq_eq
    (δ R₀ : ℝ) (θ : ℝ) :
    Complex.normSq (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) =
      (1/2 + R₀ * Real.cos θ)^2 + (δ + R₀ * Real.sin θ)^2 := by
  rw [_root_.circleMap, Complex.normSq_apply]
  have h_re : ((1/2 : ℂ) + (δ : ℂ) * Complex.I +
      (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re =
      1/2 + R₀ * Real.cos θ := by
    simp [Complex.add_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_im : ((1/2 : ℂ) + (δ : ℂ) * Complex.I +
      (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im =
      δ + R₀ * Real.sin θ := by
    simp [Complex.add_im, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [h_re, h_im]; ring

/-- **`η²/4 ≤ R₀ sin η` for the cusp range.**
Used to prove `arc.Re ≤ arc.Im` in the cusp 0 region. Combines Jordan's
inequality `sin η ≥ 2η/π` with `R₀ > 1/3` and `η ≤ 1/π`. -/
theorem modularLambdaH_F_Y_arc_eta_sq_le_R₀_sin
    {R₀ η : ℝ} (hR₀_gt : (1 : ℝ) / 3 < R₀) (hη_nn : 0 ≤ η)
    (hη_le_inv_pi : η ≤ 1 / Real.pi) (hη_le_pi_2 : η ≤ Real.pi / 2) :
    η ^ 2 / 4 ≤ R₀ * Real.sin η := by
  -- sin η ≥ 2η/π (Jordan's inequality on [0, π/2]).
  have h_sin_lower : (2 / Real.pi) * η ≤ Real.sin η :=
    Real.mul_le_sin hη_nn hη_le_pi_2
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_gt_three : 3 < Real.pi := Real.pi_gt_three
  -- R₀ sin η ≥ R₀ · (2η/π) ≥ (1/3) · (2η/π) = 2η/(3π).
  have h_R₀_sin_lower : (2 * η) / (3 * Real.pi) ≤ R₀ * Real.sin η := by
    have h1 : R₀ * ((2/Real.pi) * η) ≤ R₀ * Real.sin η := by
      have hR₀_pos : 0 < R₀ := by linarith
      exact mul_le_mul_of_nonneg_left h_sin_lower hR₀_pos.le
    have h2 : (1:ℝ)/3 * ((2/Real.pi) * η) ≤ R₀ * ((2/Real.pi) * η) := by
      have : 0 ≤ (2/Real.pi) * η := by positivity
      nlinarith [hR₀_gt, this]
    have h_eq : (1:ℝ)/3 * ((2/Real.pi) * η) = (2 * η) / (3 * Real.pi) := by
      rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
      ring
    linarith [h1, h2, h_eq]
  -- η²/4 ≤ 2η/(3π).
  -- Equivalent: η ≤ 8/(3π) (after dividing by η/4 for η > 0).
  -- We have η ≤ 1/π. And 1/π ≤ 8/(3π) iff 1 ≤ 8/3 iff 3 ≤ 8. ✓.
  have h_η_sq_le_target : η^2 / 4 ≤ (2 * η) / (3 * Real.pi) := by
    -- Show η/4 ≤ 2/(3π) via 3πη ≤ 3 ≤ 8.
    have h_πη_le_one : Real.pi * η ≤ 1 := by
      have h2 : Real.pi * η ≤ Real.pi * (1/Real.pi) :=
        mul_le_mul_of_nonneg_left hη_le_inv_pi h_pi_pos.le
      have h3 : Real.pi * (1/Real.pi) = 1 := by field_simp
      linarith
    have h_quart_le : η / 4 ≤ 2 / (3 * Real.pi) := by
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 4) (by positivity : (0:ℝ) < 3 * Real.pi)]
      nlinarith [h_πη_le_one]
    have h_mul : η * (η/4) ≤ η * (2/(3 * Real.pi)) :=
      mul_le_mul_of_nonneg_left h_quart_le hη_nn
    have h_lhs : η * (η/4) = η^2 / 4 := by ring
    have h_rhs : η * (2/(3 * Real.pi)) = (2 * η) / (3 * Real.pi) := by ring
    linarith [h_mul, h_lhs, h_rhs]
  linarith [h_η_sq_le_target, h_R₀_sin_lower]

/-- **Pure polynomial inequality.**
For `u ≥ 0`, `v > 0` with `u ≤ v` and `v ≤ 1/(2K)`, we have
`K · (u² + v²) ≤ v` (i.e., `K ≤ v/(u² + v²)`). Used to derive
`K ≤ Im(−1/arc)` from `arc.Re ≤ arc.Im` and `arc.Im ≤ 1/(2K)`. -/
theorem modularLambdaH_F_Y_arc_cusp_0_poly_bound
    {u v K : ℝ} (hu_nn : 0 ≤ u) (hv_pos : 0 < v)
    (hu_le_v : u ≤ v) (hv_upper : v ≤ 1 / (2 * K)) (hK_pos : 0 < K) :
    K * (u ^ 2 + v ^ 2) ≤ v := by
  -- u² ≤ v² (from u ≤ v and both ≥ 0).
  have hu_sq_le : u^2 ≤ v^2 := by nlinarith [hu_le_v, hu_nn, hv_pos.le]
  -- u² + v² ≤ 2v².
  have h_uv_sum : u^2 + v^2 ≤ 2 * v^2 := by linarith
  -- 2 K v ≤ 1.
  have h_2K_pos : 0 < 2 * K := by linarith
  have h_2Kv_le : 2 * K * v ≤ 1 := by
    have h1 : 2 * K * v ≤ 2 * K * (1/(2*K)) :=
      mul_le_mul_of_nonneg_left hv_upper (by linarith)
    have h2 : 2 * K * (1/(2*K)) = 1 := by
      field_simp
    linarith
  -- K · (u² + v²) ≤ K · 2v² = 2Kv · v ≤ 1 · v = v.
  nlinarith [h_uv_sum, hv_pos, h_2Kv_le, hK_pos, sq_nonneg v]

/-- **V ≤ 1/(2K) bound.**
For δ + R₀ sin η bounded above by `1/(2K)` when `δ, η ≤ 1/(4K)`. -/
theorem modularLambdaH_F_Y_arc_cusp_0_v_bound
    {δ R₀ η K : ℝ} (_hδ_nn : 0 ≤ δ) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (hη_nn : 0 ≤ η) (h_sin_η_le_η : Real.sin η ≤ η)
    (hδ_le : δ ≤ 1 / (4 * K)) (hη_le : η ≤ 1 / (4 * K))
    (hK_pos : 0 < K) :
    δ + R₀ * Real.sin η ≤ 1 / (2 * K) := by
  have h_4K_pos : 0 < 4 * K := by linarith
  have h_2K_pos : 0 < 2 * K := by linarith
  have h_8K_pos : 0 < 8 * K := by linarith
  -- R₀ sin η ≤ (1/2) η.
  have h_R₀_sin_le : R₀ * Real.sin η ≤ (1/2) * η := by
    have h1 : R₀ * Real.sin η ≤ R₀ * η :=
      mul_le_mul_of_nonneg_left h_sin_η_le_η hR₀_pos.le
    nlinarith [h1, hR₀_lt.le, hη_nn]
  -- (1/2) · η ≤ (1/2) · 1/(4K) = 1/(8K).
  have h_η_half_le : (1/2) * η ≤ 1/(8*K) := by
    have h1 : (1/2) * η ≤ (1/2) * (1/(4*K)) :=
      mul_le_mul_of_nonneg_left hη_le (by norm_num)
    have h2 : (1:ℝ)/2 * (1/(4*K)) = 1/(8*K) := by
      have hK_ne : K ≠ 0 := ne_of_gt hK_pos
      field_simp
      ring
    linarith
  -- δ + R₀ sin η ≤ 1/(4K) + 1/(8K) = 3/(8K) ≤ 1/(2K).
  have h_sum : δ + R₀ * Real.sin η ≤ 1/(4*K) + 1/(8*K) := by
    linarith
  -- 1/(4K) + 1/(8K) ≤ 1/(2K). Equivalent to 1/(4K) ≤ 3/(8K), i.e., 2 ≤ 3 ✓.
  -- Or direct: 8K · (1/(4K)) + 8K · (1/(8K)) = 2 + 1 = 3 ≤ 4 = 8K · (1/(2K)).
  have h_chain : (1:ℝ)/(4*K) + 1/(8*K) ≤ 1/(2*K) := by
    rw [div_add_div _ _ (ne_of_gt h_4K_pos) (ne_of_gt h_8K_pos)]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (4*K) * (8*K)) h_2K_pos]
    ring_nf
    nlinarith [sq_nonneg K, hK_pos]
  linarith

set_option maxHeartbeats 400000 in
-- Cusp-0 helper combines five polynomial sub-helpers and arc-point
-- complex-arithmetic simp chains; exceeds the default 200000 budget.
/-- **Lower bound on `Im(−1/arc(θ))` in cusp region.**
Given any target `K > 0`, there exist parameters `δ_K, θ_K` (depending
on `K`) such that for `δ ≤ δ_K`, `R₀ ∈ (√(1/4 − δ²), 1/2)`, and
`θ ∈ [π − θ_K, π]`: `Im(−1/arc(θ)) ≥ K`. The cusp width `θ_K` shrinks
as `K` grows. Used to apply
`modularLambdaH_norm_le_exp_of_im_ge_one`.

Proof: take `δ_K := min(1/4, 1/(4K))`, `θ_K := min(1/π, 1/(4K))`.
Setting `η := π − θ ∈ [0, θ_K]` and `u := arc.Re, v := arc.Im`:
* `u ≤ 2δ² + η²/4` (from `R₀ > √(1/4 − δ²) > 1/2 − 2δ²` and
  `1 − cos η ≤ η²/2`).
* `R₀ > √(3/16) > 1/3` (from `δ ≤ 1/4`).
* `u ≤ v` (from `2δ² ≤ δ` for `δ ≤ 1/2` and `η²/4 ≤ R₀ sin η`
  via Jordan's `sin η ≥ 2η/π`, `R₀ > 1/3`, and `η ≤ 1/π < 8/(3π)`).
* `v ≤ 1/(2K)` (from `δ ≤ 1/(4K)`, `η ≤ 1/(4K)`).
* Then `u² + v² ≤ 2v²` so `Im(−1/arc) = v/(u² + v²) ≥ 1/(2v) ≥ K`. -/
theorem modularLambdaH_F_Y_arc_im_inv_lower_cusp_0
    (K : ℝ) (hK_pos : 0 < K) :
    ∃ δ_K θ_K : ℝ, 0 < δ_K ∧ δ_K ≤ 1 / 4 ∧
      0 < θ_K ∧ θ_K ≤ Real.pi / 4 ∧
    ∀ δ R₀ : ℝ, 0 < δ → δ ≤ δ_K →
    Real.sqrt (1 / 4 - δ ^ 2) < R₀ → R₀ < 1 / 2 →
    ∀ θ : ℝ, Real.pi - θ_K ≤ θ → θ ≤ Real.pi →
      K ≤
        (-(_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ)⁻¹).im := by
  -- Strategy: δ_K := min(1/4, 1/(4K)), θ_K := min(1/π, 1/(4K)).
  -- Show arc.Re ≤ arc.Im, hence |arc|² ≤ 2·arc.Im², hence Im(-1/arc) ≥ 1/(2·arc.Im).
  -- Combined with arc.Im ≤ 1/(2K), get Im(-1/arc) ≥ K.
  have h_4K_pos : 0 < 4 * K := by linarith
  have h_2K_pos : 0 < 2 * K := by linarith
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_inv_pi_pos : 0 < (1:ℝ)/Real.pi := by positivity
  have h_pi_gt_three : 3 < Real.pi := Real.pi_gt_three
  have h_inv_pi_le_pi_4 : (1:ℝ)/Real.pi ≤ Real.pi/4 := by
    rw [div_le_div_iff₀ h_pi_pos (by norm_num : (0:ℝ) < 4)]
    nlinarith [h_pi_gt_three]
  refine ⟨min (1/4) (1/(4*K)), min (1/Real.pi) (1/(4*K)),
    lt_min (by norm_num) (by positivity),
    min_le_left _ _,
    lt_min h_inv_pi_pos (by positivity),
    le_trans (min_le_left _ _) h_inv_pi_le_pi_4, ?_⟩
  intro δ R₀ hδ hδ_le hR₀_lo hR₀_lt θ hθ_lo hθ_hi
  have hδ_le_quarter : δ ≤ 1/4 := le_trans hδ_le (min_le_left _ _)
  have hδ_le_inv_4K : δ ≤ 1/(4*K) := le_trans hδ_le (min_le_right _ _)
  have hR₀_pos : 0 < R₀ := by
    have := Real.sqrt_nonneg (1/4 - δ^2); linarith
  -- Set up η.
  set η : ℝ := Real.pi - θ with hη_def
  have hη_nn : 0 ≤ η := by rw [hη_def]; linarith
  have h_θ_K_le_min : Real.pi - θ ≤ min (1/Real.pi) (1/(4*K)) := by
    rw [hη_def] at hη_def; linarith
  have hη_le_inv_pi : η ≤ 1/Real.pi := by
    have h1 : η ≤ min (1/Real.pi) (1/(4*K)) := by rw [hη_def]; linarith
    exact le_trans h1 (min_le_left _ _)
  have hη_le_inv_4K : η ≤ 1/(4*K) := by
    have h1 : η ≤ min (1/Real.pi) (1/(4*K)) := by rw [hη_def]; linarith
    exact le_trans h1 (min_le_right _ _)
  have hη_le_pi_2 : η ≤ Real.pi / 2 := by
    have h1 : η ≤ Real.pi / 4 := le_trans hη_le_inv_pi h_inv_pi_le_pi_4
    linarith
  have hη_lt_pi : η < Real.pi := by linarith
  -- Trig values.
  have h_sin_η_nn : 0 ≤ Real.sin η := Real.sin_nonneg_of_mem_Icc ⟨hη_nn, by linarith⟩
  have h_sin_η_le_η : Real.sin η ≤ η := Real.sin_le hη_nn
  have h_one_minus_cos : 1 - Real.cos η ≤ η^2 / 2 := by
    have := @Real.one_sub_sq_div_two_le_cos η; linarith
  have h_sin_θ_eq : Real.sin θ = Real.sin η := by
    rw [hη_def, Real.sin_pi_sub]
  have h_cos_θ_eq : Real.cos θ = -Real.cos η := by
    rw [hη_def, Real.cos_pi_sub]; ring
  -- R₀ > √(3/16) > 1/3.
  have hR₀_gt_sqrt_3_16 : Real.sqrt (3/16) < R₀ := by
    have h_sqrt_mono : Real.sqrt (1/4 - (1/4)^2) ≤ Real.sqrt (1/4 - δ^2) := by
      apply Real.sqrt_le_sqrt; nlinarith [hδ_le_quarter, hδ.le]
    have h_3_16 : 1/4 - (1/4:ℝ)^2 = 3/16 := by ring
    rw [h_3_16] at h_sqrt_mono
    linarith [hR₀_lo, h_sqrt_mono]
  have hR₀_gt_one_third : (1:ℝ)/3 < R₀ := by
    have h_sqrt_3_16_pos : (0:ℝ) ≤ Real.sqrt (3/16) := Real.sqrt_nonneg _
    have h_sqrt_3_16_gt : (1:ℝ)/3 < Real.sqrt (3/16) := by
      have h_sq_lt : ((1:ℝ)/3)^2 < 3/16 := by norm_num
      have h_third_nn : (0:ℝ) ≤ 1/3 := by norm_num
      have h_sqrt_mono : Real.sqrt ((1/3:ℝ)^2) < Real.sqrt (3/16) :=
        Real.sqrt_lt_sqrt (by norm_num) h_sq_lt
      rw [Real.sqrt_sq h_third_nn] at h_sqrt_mono
      exact h_sqrt_mono
    linarith
  -- Names for arc.Re and arc.Im.
  set u : ℝ := 1/2 + R₀ * Real.cos θ with hu_def
  set v : ℝ := δ + R₀ * Real.sin θ with hv_def
  have hu_eq : u = 1/2 - R₀ * Real.cos η := by rw [hu_def, h_cos_θ_eq]; ring
  have hv_eq : v = δ + R₀ * Real.sin η := by rw [hv_def, h_sin_θ_eq]
  -- v > 0 (since δ > 0, sin η ≥ 0, R₀ > 0).
  have hv_pos : 0 < v := by rw [hv_eq]; positivity
  -- u ≥ 0 (since R₀ < 1/2 and cos η ≤ 1).
  have h_cos_η_le_one : Real.cos η ≤ 1 := Real.cos_le_one η
  have hu_nn : 0 ≤ u := by
    rw [hu_eq]
    nlinarith [hR₀_lt, hR₀_pos, h_cos_η_le_one,
               Real.cos_nonneg_of_mem_Icc (⟨by linarith, by linarith⟩ :
                 η ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2))]
  -- u ≤ 2δ² + η²/4.
  have h_half_minus_R₀ : 1/2 - R₀ ≤ 2 * δ^2 := by
    have hR₀_sq_gt : 1/4 - δ^2 < R₀^2 := by
      have h2 : 0 ≤ 1/4 - δ^2 := by nlinarith [hδ_le_quarter]
      have h3 : Real.sqrt (1/4 - δ^2)^2 = 1/4 - δ^2 := Real.sq_sqrt h2
      nlinarith [hR₀_lo, Real.sqrt_nonneg (1/4 - δ^2), sq_nonneg R₀, h3]
    nlinarith [hR₀_sq_gt, hR₀_lt, hR₀_pos]
  have hu_upper : u ≤ 2 * δ^2 + η^2 / 4 := by
    rw [hu_eq]
    have h1 : 1/2 - R₀ * Real.cos η = (1/2 - R₀) + R₀ * (1 - Real.cos η) := by ring
    rw [h1]
    have h2 : R₀ * (1 - Real.cos η) ≤ R₀ * (η^2 / 2) :=
      mul_le_mul_of_nonneg_left h_one_minus_cos hR₀_pos.le
    have h3 : R₀ * (η^2 / 2) ≤ (1/2) * (η^2 / 2) := by
      nlinarith [hR₀_lt, sq_nonneg η, hR₀_pos]
    linarith
  -- Key: u ≤ v (i.e., arc.Re ≤ arc.Im).
  -- u ≤ 2δ² + η²/4 ≤ δ + R₀ sin η = v.
  --   2δ² ≤ δ (using δ ≤ 1/2)
  --   η²/4 ≤ R₀ sin η (using R₀ > 1/3 > 0 and sin η ≥ (2/π) η)
  have h_η_sq_le_R₀_sin : η^2 / 4 ≤ R₀ * Real.sin η :=
    modularLambdaH_F_Y_arc_eta_sq_le_R₀_sin hR₀_gt_one_third hη_nn
      hη_le_inv_pi hη_le_pi_2
  have hu_le_v : u ≤ v := by
    rw [hv_eq]
    calc u ≤ 2 * δ^2 + η^2 / 4 := hu_upper
      _ = (2 * δ^2) + (η^2 / 4) := by ring
      _ ≤ δ + R₀ * Real.sin η := by
        have h_2δ_sq : 2 * δ^2 ≤ δ := by nlinarith [hδ.le, hδ_le_quarter]
        linarith [h_η_sq_le_R₀_sin]
  -- v ≤ 1/(2K) (via sub-helper).
  have hv_upper : v ≤ 1/(2*K) := by
    rw [hv_eq]
    exact modularLambdaH_F_Y_arc_cusp_0_v_bound hδ.le hR₀_pos hR₀_lt hη_nn
      h_sin_η_le_η hδ_le_inv_4K hη_le_inv_4K hK_pos
  -- Im(-1/arc) computation.
  have h_normSq_eq := modularLambdaH_F_Y_arc_normSq_eq δ R₀ θ
  have hθ_nn : 0 ≤ θ := by
    have h_pi_4_pos : 0 < Real.pi / 4 := by positivity
    have h_min_le : min (1/Real.pi) (1/(4*K)) ≤ 1/Real.pi := min_le_left _ _
    have h1 : Real.pi - min (1/Real.pi) (1/(4*K)) ≥ 0 := by
      linarith [h_inv_pi_pos]
    linarith
  have harc_im_pos := modularLambdaH_F_Y_arc_im_pos hδ hR₀_pos.le hθ_nn hθ_hi
  have harc_ne_zero :
      _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ ≠ 0 := by
    intro h_eq
    have : (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ).im = 0 := by
      rw [h_eq]; rfl
    linarith [harc_im_pos]
  have h_normSq_pos : 0 < Complex.normSq
      (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) :=
    Complex.normSq_pos.mpr harc_ne_zero
  have h_im_inv :
      (-(_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ)⁻¹).im =
      (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ).im /
      Complex.normSq (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) := by
    rw [Complex.neg_im, Complex.inv_im]; ring
  rw [h_im_inv, le_div_iff₀ h_normSq_pos, h_normSq_eq]
  -- Express arc.Im in terms of θ.
  have harc_im_eq : (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ).im = v := by
    rw [_root_.circleMap]
    simp [Complex.add_im, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hv_def]
  rw [harc_im_eq]
  -- Goal: K * ((1/2 + R₀ cos θ)² + (δ + R₀ sin θ)²) ≤ v
  -- = K * (u² + v²) ≤ v
  -- Show: K * (u² + v²) ≤ K * (2 * v²) ≤ v.
  have h_normSq_uv : (1/2 + R₀ * Real.cos θ)^2 + (δ + R₀ * Real.sin θ)^2 = u^2 + v^2 := by
    rw [hu_def, hv_def]
  rw [h_normSq_uv]
  exact modularLambdaH_F_Y_arc_cusp_0_poly_bound hu_nn hv_pos hu_le_v hv_upper hK_pos


/-- **`1/2 - R₀ ≤ 2δ²` from `R₀ > √(1/4 - δ²)`.** -/
theorem modularLambdaH_F_Y_arc_half_minus_R₀_bound
    {δ R₀ : ℝ} (hδ_pos : 0 < δ) (hδ_le_quarter : δ ≤ 1 / 4)
    (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀) (hR₀_lt : R₀ < 1 / 2)
    (hR₀_pos : 0 < R₀) :
    1 / 2 - R₀ ≤ 2 * δ ^ 2 := by
  have hR₀_sq_gt : 1 / 4 - δ ^ 2 < R₀ ^ 2 := by
    have h2 : 0 ≤ 1 / 4 - δ ^ 2 := by nlinarith
    have h3 : Real.sqrt (1 / 4 - δ ^ 2) ^ 2 = 1 / 4 - δ ^ 2 := Real.sq_sqrt h2
    nlinarith [hR₀_lo, Real.sqrt_nonneg (1 / 4 - δ ^ 2), sq_nonneg R₀, h3]
  nlinarith [hR₀_sq_gt, hR₀_lt, hR₀_pos]

/-- **Middle-case polynomial bound.**
Given `M, δ, R₀, w_im` with the appropriate hypotheses (`δ ≤ 1/4`,
`δ ≤ w_im/(4M)`, `1/2 − R₀ ≤ 2δ²`, `w_im > 0`), `M · (δ + (1/2 − R₀)) < w_im`. -/
theorem modularLambdaH_F_Y_arc_middle_poly_bound
    {M δ R₀ w_im : ℝ} (hM_pos : 0 < M) (hδ_pos : 0 < δ)
    (hδ_le_quarter : δ ≤ 1 / 4) (hδ_le_M : δ ≤ w_im / (4 * M))
    (h_half_minus_R₀ : 1 / 2 - R₀ ≤ 2 * δ ^ 2) (hw_im_pos : 0 < w_im) :
    M * (δ + (1 / 2 - R₀)) < w_im := by
  -- δ + 1/2 - R₀ ≤ δ + 2δ² ≤ (3/2) δ (using δ ≤ 1/4 ⟹ 2δ² ≤ δ/2).
  have h_2δ_sq_le : 2 * δ^2 ≤ δ/2 := by nlinarith [hδ_pos.le, hδ_le_quarter]
  have h_sum_le : δ + (1/2 - R₀) ≤ (3/2) * δ := by linarith
  -- M · (3/2)δ ≤ M · (3/2) · w_im/(4M) = 3 w_im / 8 < w_im.
  have hM_δ_le : M * δ ≤ M * (w_im / (4*M)) :=
    mul_le_mul_of_nonneg_left hδ_le_M hM_pos.le
  have h_M_inv : M * (w_im / (4*M)) = w_im / 4 := by
    field_simp
  have h_M_sum : M * (δ + (1/2 - R₀)) ≤ M * ((3/2) * δ) :=
    mul_le_mul_of_nonneg_left h_sum_le hM_pos.le
  have h_M_3_2_δ : M * ((3/2) * δ) = (3/2) * (M * δ) := by ring
  have h_3_2_le : (3/2 : ℝ) * (M * δ) ≤ (3/2) * (w_im / 4) := by
    have h_M_δ_le' : M * δ ≤ w_im / 4 := by rw [← h_M_inv]; exact hM_δ_le
    linarith
  have h_final : (3/2 : ℝ) * (w_im / 4) < w_im := by linarith
  linarith

/-- **Cusp-1 norm inequality.**
Given `0 ≤ w_norm`, `0 < c`, `c < 1/(w_norm + 2)`, `1 - c ≤ X`,
we have `w_norm < X / c`. -/
theorem modularLambdaH_F_Y_arc_cusp_1_norm_bound
    {w_norm c X : ℝ} (hw_nn : 0 ≤ w_norm) (hc_pos : 0 < c)
    (hc_lt : c < 1 / (w_norm + 2)) (h_one_minus_c_le_X : 1 - c ≤ X) :
    w_norm < X / c := by
  have h_w_plus_two_pos : 0 < w_norm + 2 := by linarith
  have h_c_w_plus_two_lt_one : c * (w_norm + 2) < 1 := by
    rw [lt_div_iff₀ h_w_plus_two_pos] at hc_lt; linarith
  rw [lt_div_iff₀ hc_pos]
  nlinarith [h_one_minus_c_le_X, h_c_w_plus_two_lt_one, hc_pos, hw_nn]

/-- **Exponential bound (mul form).** Given `C > 0`,
with `L := log(160000 · C)` and `K := max L 1 + 1`, we have
`160000 · exp(-π · K) < 1/C`. Used for cusp 1 where `C = ‖w‖ + 2`. -/
theorem modularLambdaH_F_Y_arc_ne_exp_bound_mul (C : ℝ) (hC_pos : 0 < C) :
    160000 * Real.exp (-Real.pi * (max (Real.log (160000 * C)) 1 + 1)) < 1 / C := by
  set L : ℝ := Real.log (160000 * C) with hL_def
  set K : ℝ := max L 1 + 1 with hK_def
  have hK_pos : 0 < K := by
    have : 1 ≤ max L 1 := le_max_right _ _
    rw [hK_def]; linarith
  have h_pi_gt_one : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have hL_lt_πK : L < Real.pi * K := by
    have h1 : L ≤ max L 1 := le_max_left _ _
    have h2 : max L 1 < K := by rw [hK_def]; linarith
    have h3 : L < K := lt_of_le_of_lt h1 h2
    nlinarith [h3, h_pi_gt_one, hK_pos]
  have h_exp_neg_L : Real.exp (-L) = 1 / (160000 * C) := by
    rw [hL_def]
    rw [show -Real.log (160000 * C) = Real.log ((160000 * C)⁻¹) from
      (Real.log_inv _).symm]
    rw [Real.exp_log (by positivity : (0:ℝ) < (160000 * C)⁻¹), one_div]
  have h_exp_lt : Real.exp (-Real.pi * K) < Real.exp (-L) := by
    apply Real.exp_lt_exp.mpr; linarith
  calc 160000 * Real.exp (-Real.pi * K)
      < 160000 * Real.exp (-L) := mul_lt_mul_of_pos_left h_exp_lt (by norm_num)
    _ = 160000 * (1 / (160000 * C)) := by rw [h_exp_neg_L]
    _ = 1 / C := by field_simp

/-- **Exponential bound (div form).** Given `C > 0`,
with `L := log(160000 / C)` and `K := max L 1 + 1`, we have
`160000 · exp(-π · K) < C`. Used for cusp 0 where `C = ‖w − 1‖`. -/
theorem modularLambdaH_F_Y_arc_ne_exp_bound_div (C : ℝ) (hC_pos : 0 < C) :
    160000 * Real.exp (-Real.pi * (max (Real.log (160000 / C)) 1 + 1)) < C := by
  set L : ℝ := Real.log (160000 / C) with hL_def
  set K : ℝ := max L 1 + 1 with hK_def
  have hK_pos : 0 < K := by
    have : 1 ≤ max L 1 := le_max_right _ _
    rw [hK_def]; linarith
  have h_pi_gt_one : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have hL_lt_πK : L < Real.pi * K := by
    have h1 : L ≤ max L 1 := le_max_left _ _
    have h2 : max L 1 < K := by rw [hK_def]; linarith
    have h3 : L < K := lt_of_le_of_lt h1 h2
    nlinarith [h3, h_pi_gt_one, hK_pos]
  have h_exp_neg_L : Real.exp (-L) = C / 160000 := by
    rw [hL_def]
    rw [show -Real.log (160000 / C) = Real.log ((160000 / C)⁻¹) from
      (Real.log_inv _).symm]
    rw [Real.exp_log (by positivity : (0:ℝ) < (160000 / C)⁻¹), inv_div]
  have h_exp_lt : Real.exp (-Real.pi * K) < Real.exp (-L) := by
    apply Real.exp_lt_exp.mpr; linarith
  calc 160000 * Real.exp (-Real.pi * K)
      < 160000 * Real.exp (-L) := mul_lt_mul_of_pos_left h_exp_lt (by norm_num)
    _ = 160000 * (C / 160000) := by rw [h_exp_neg_L]
    _ = C := by field_simp

set_option maxHeartbeats 400000 in
-- Three-case arc nonvanishing (middle Lipschitz + cusp-0 + cusp-1 conjugation)
-- with extensive complex-arithmetic and bound chaining; exceeds the default
-- 200000 budget even after extracting many sub-helpers.
/-- **Shifted arc non-vanishing (existential δ_w form).**
For `w ∈ ℍ`, there exists `δ_w ∈ (0, 1/2)` such that for all `δ ∈ (0, δ_w]`,
`R₀ ∈ (√(1/4 − δ²), 1/2)`, and `θ ∈ [0, π]`:
`λ(circleMap (1/2 + δ·i) R₀ θ) − w ≠ 0`.

The existential form (matching the two strip lemmas) replaces the previous
universal statement, since the proof genuinely requires `δ` small enough
relative to `w` to control the arc's `Im λ` against `Im w > 0`. In the
main F_Y theorem, this `δ_w` is passed to
`modularLambdaH_F_Y_params_exist_arc` as `δ_max`.

Proof structure: `θ_0 := min(θ_K_0, θ_K_1)` where `K_0, K_1` are derived
from `‖w − 1‖` and `‖w‖ + 2`. Middle of arc handled by extracting
uniform Lipschitz constant `M` directly via Helper 8.2 on the fixed
ball used by Helper 8.3, combined with the geometry of Helpers
8.3.a/b/c. Cusp 0 (`θ ∈ [π − θ_0, π]`): S-action + cusp helper.
Cusp 1 (`θ ∈ [0, θ_0]`): conjugation symmetry + T-action chain
reduces to cusp-0 analysis of `1 - conj(arc(θ)) = arc(π − θ)`. -/
theorem modularLambdaH_F_Y_arc_ne
    {w : ℂ} (hw : 0 < w.im) :
    ∃ δ_w : ℝ, 0 < δ_w ∧ δ_w < 1 / 2 ∧
    ∀ δ R₀ : ℝ, 0 < δ → δ ≤ δ_w →
    Real.sqrt (1 / 4 - δ ^ 2) < R₀ → R₀ < 1 / 2 →
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
      modularLambdaH (_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w
        ≠ 0 := by
  -- Three-case proof:
  -- (a) Middle θ ∈ [θ_0, π - θ_0]: Helper 8.3-style bound on |Im λ|.
  -- (b) Cusp 0 θ ∈ (π - θ_K_0, π]: S-action + norm bound; ‖λ - 1‖ < ‖w - 1‖.
  -- (c) Cusp 1 θ ∈ [0, θ_K_1): conjugation + T; |λ| > ‖w‖.
  -- The three pieces of `δ_w` come from these three regimes.
  have hw_ne_one : w ≠ 1 := by
    intro h_eq
    rw [h_eq] at hw
    simp at hw
  have hw_one_norm_pos : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw_ne_one)
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  -- K_0 for cusp 0: 160000·exp(-π·K_0) < ‖w - 1‖.
  set L_0 : ℝ := Real.log (160000 / ‖w - 1‖) with hL_0_def
  set K_0 : ℝ := max L_0 1 + 1 with hK_0_def
  have hK_0_pos : 0 < K_0 := by
    rw [hK_0_def]
    have : 1 ≤ max L_0 1 := le_max_right _ _
    linarith
  have hK_0_ge_one : 1 ≤ K_0 := by
    rw [hK_0_def]
    have : 1 ≤ max L_0 1 := le_max_right _ _
    linarith
  -- K_1 for cusp 1: 160000·exp(-π·K_1) < 1/(‖w‖ + 2).
  set L_1 : ℝ := Real.log (160000 * (‖w‖ + 2)) with hL_1_def
  set K_1 : ℝ := max L_1 1 + 1 with hK_1_def
  have hK_1_pos : 0 < K_1 := by
    rw [hK_1_def]; have : 1 ≤ max L_1 1 := le_max_right _ _; linarith
  have hK_1_ge_one : 1 ≤ K_1 := by
    rw [hK_1_def]; have : 1 ≤ max L_1 1 := le_max_right _ _; linarith
  -- Cusp helpers.
  obtain ⟨δ_K_0, θ_K_0, hδ_K_0_pos, hδ_K_0_le_quarter, hθ_K_0_pos, hθ_K_0_le_pi_4,
    h_cusp_0_bound⟩ :=
    modularLambdaH_F_Y_arc_im_inv_lower_cusp_0 K_0 hK_0_pos
  obtain ⟨δ_K_1, θ_K_1, hδ_K_1_pos, hδ_K_1_le_quarter, hθ_K_1_pos, hθ_K_1_le_pi_4,
    h_cusp_1_bound⟩ :=
    modularLambdaH_F_Y_arc_im_inv_lower_cusp_0 K_1 hK_1_pos
  -- θ_0 := min(θ_K_0, θ_K_1). Then sin θ_0 > 0.
  set θ_0 : ℝ := min θ_K_0 θ_K_1 with hθ_0_def
  have hθ_0_pos : 0 < θ_0 := lt_min hθ_K_0_pos hθ_K_1_pos
  have hθ_0_le_θ_K_0 : θ_0 ≤ θ_K_0 := min_le_left _ _
  have hθ_0_le_θ_K_1 : θ_0 ≤ θ_K_1 := min_le_right _ _
  have hθ_0_lt_pi_2 : θ_0 < Real.pi / 2 := by
    have : θ_0 ≤ Real.pi / 4 := le_trans hθ_0_le_θ_K_0 hθ_K_0_le_pi_4
    linarith
  have hθ_0_lt_pi : θ_0 < Real.pi := by linarith
  have h_sin_θ_0_pos : 0 < Real.sin θ_0 :=
    Real.sin_pos_of_pos_of_lt_pi hθ_0_pos hθ_0_lt_pi
  -- Setup the ball for Lipschitz extraction (Helper 8.3's internal setup).
  set τ_K : ℂ := (1/2 : ℂ) +
    Complex.I * ((1 / (2 * Real.sin θ_0) : ℝ) : ℂ) with hτ_K_def
  set r_K : ℝ := (1 + Real.cos θ_0) / (4 * Real.sin θ_0) with hr_K_def
  have h_cos_θ_0_pos : 0 < Real.cos θ_0 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_0_lt_pi_2⟩
  have h_4s_pos : 0 < 4 * Real.sin θ_0 := by linarith
  have hr_K_pos : 0 < r_K := by
    rw [hr_K_def]; exact div_pos (by linarith) h_4s_pos
  -- τ_K.im = 1/(2 sin θ_0) > 0.
  have hτ_K_im_eq : τ_K.im = 1/(2*Real.sin θ_0) := by
    rw [hτ_K_def]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.ofReal_re, h_half_im]
    ring
  have hτ_K_im_pos : 0 < τ_K.im := by rw [hτ_K_im_eq]; positivity
  -- Apply Helper 8.3.a (ball in UHP) and Helper 8.2 to get M.
  have h_ball_in :=
    modularLambdaH_arc_lipschitz_ball_in_uhp hθ_0_pos hθ_0_lt_pi_2
  obtain ⟨M, hM_pos, hM_lipschitz⟩ :=
    modularLambdaH_im_lipschitz_on_compact hτ_K_im_pos hr_K_pos h_ball_in
  -- δ_w := min of constraints.
  set δ_M : ℝ := w.im / (4 * M) with hδ_M_def
  have hδ_M_pos : 0 < δ_M := by rw [hδ_M_def]; positivity
  set δ_w : ℝ := min (min δ_K_0 δ_K_1)
    (min (Real.sin θ_0 / 4) (min δ_M (1/4))) with hδ_w_def
  have hδ_w_pos : 0 < δ_w :=
    lt_min (lt_min hδ_K_0_pos hδ_K_1_pos)
      (lt_min (by positivity) (lt_min hδ_M_pos (by norm_num)))
  have hδ_w_lt_half : δ_w < 1/2 := by
    have h1 : δ_w ≤ 1/4 := by
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      rfl
    linarith
  refine ⟨δ_w, hδ_w_pos, hδ_w_lt_half, ?_⟩
  intro δ R₀ hδ_pos hδ_le hR₀_lo hR₀_lt θ hθ_lo hθ_hi
  -- Extract individual constraints on δ.
  have hδ_le_δ_K_0 : δ ≤ δ_K_0 := le_trans hδ_le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ_le_δ_K_1 : δ ≤ δ_K_1 := le_trans hδ_le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ_le_sin_θ_0_quarter : δ ≤ Real.sin θ_0 / 4 :=
    le_trans hδ_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ_le_δ_M : δ ≤ δ_M :=
    le_trans hδ_le (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδ_le_quarter : δ ≤ 1/4 :=
    le_trans hδ_le (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- The arc point and basic facts.
  have hR₀_pos : 0 < R₀ := by have := Real.sqrt_nonneg (1/4 - δ^2); linarith
  set arc : ℂ := _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ
    with harc_def
  -- Assume λ(arc) = w for contradiction.
  intro h_lam_eq_w
  have h_lam_arc_eq : modularLambdaH arc = w := by
    linear_combination h_lam_eq_w
  have harc_im_pos : 0 < arc.im :=
    modularLambdaH_F_Y_arc_im_pos hδ_pos hR₀_pos.le hθ_lo hθ_hi
  -- Case split on θ position.
  by_cases h_θ_le_θ_0 : θ ≤ θ_0
  · -- Cusp 1 case: θ ∈ [0, θ_0] ⊆ [0, θ_K_1].
    -- arc(π - θ) is in [π - θ_K_1, π] (cusp 0 of arc).
    have hπθ_le : Real.pi - θ ≤ Real.pi := by linarith [hθ_lo]
    have hπθ_ge_θ_K_1 : Real.pi - θ_K_1 ≤ Real.pi - θ := by
      linarith [hθ_0_le_θ_K_1, h_θ_le_θ_0]
    -- Im(-1/arc(π - θ)) ≥ K_1.
    have h_im_inv_πθ_ge :
        K_1 ≤ (-(_root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀
          (Real.pi - θ))⁻¹).im :=
      h_cusp_1_bound δ R₀ hδ_pos hδ_le_δ_K_1 hR₀_lo hR₀_lt (Real.pi - θ)
        hπθ_ge_θ_K_1 hπθ_le
    -- Define σ = arc - 1 and τ' = -conj σ = arc(π - θ).
    set σ : ℂ := arc - 1 with hσ_def
    set arcπθ : ℂ := _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (Real.pi - θ) with harcπθ_def
    -- arc.Im > 0 already established.
    have hσ_im : σ.im = arc.im := by rw [hσ_def]; simp
    have hσ_im_pos : 0 < σ.im := by rw [hσ_im]; exact harc_im_pos
    -- arc(π - θ) = (1/2 - R₀ cos θ) + i(δ + R₀ sin θ) = 1 - conj(arc).
    -- Compute arc.re, arc.im, arcπθ.re, arcπθ.im, σ.re separately.
    have harc_re : arc.re = 1/2 + R₀ * Real.cos θ := by
      rw [harc_def, _root_.circleMap]
      simp [Complex.add_re, Complex.mul_re,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have harc_im_eq : arc.im = δ + R₀ * Real.sin θ := by
      rw [harc_def, _root_.circleMap]
      simp [Complex.add_im, Complex.mul_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have harcπθ_re : arcπθ.re = 1/2 - R₀ * Real.cos θ := by
      have h_eq : arcπθ.re = 1/2 + R₀ * Real.cos (Real.pi - θ) := by
        rw [harcπθ_def, _root_.circleMap]
        simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
          Complex.exp_ofReal_mul_I_im, mul_zero, zero_mul, sub_zero, mul_one,
          add_zero]
        have h_half_re : ((1 : ℂ) / 2).re = 1 / 2 := by rw [Complex.div_re]; simp
        rw [h_half_re]
      rw [h_eq, Real.cos_pi_sub]; ring
    have harcπθ_im : arcπθ.im = δ + R₀ * Real.sin θ := by
      have h_eq : arcπθ.im = δ + R₀ * Real.sin (Real.pi - θ) := by
        rw [harcπθ_def, _root_.circleMap]
        simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
          Complex.exp_ofReal_mul_I_im, mul_zero, zero_mul, mul_one]
        have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
        rw [h_half_im]; ring
      rw [h_eq, Real.sin_pi_sub]
    have hσ_re : σ.re = -1/2 + R₀ * Real.cos θ := by
      rw [hσ_def, Complex.sub_re, harc_re, Complex.one_re]; ring
    have hσ_im_eq : σ.im = δ + R₀ * Real.sin θ := by
      rw [hσ_def, Complex.sub_im, harc_im_eq, Complex.one_im]; ring
    -- Equivalently, -conj σ = arc(π - θ).
    have h_neg_conj_σ_eq : -(starRingEnd ℂ σ) = arcπθ := by
      apply Complex.ext
      · rw [Complex.neg_re, Complex.conj_re, hσ_re, harcπθ_re]; ring
      · rw [Complex.neg_im, Complex.conj_im, hσ_im_eq, harcπθ_im]; ring
    -- λ(arc(π - θ)) = conj(λ σ).
    have h_conj_lam : modularLambdaH arcπθ = starRingEnd ℂ (modularLambdaH σ) := by
      rw [← h_neg_conj_σ_eq]
      exact modularLambdaH_conj_symmetry hσ_im_pos
    -- Norm bound on arc(π - θ).
    have h_im_inv_πθ_ge_one : 1 ≤ (-(arcπθ)⁻¹).im := by
      rw [harcπθ_def] at h_im_inv_πθ_ge ⊢
      exact le_trans hK_1_ge_one h_im_inv_πθ_ge
    have h_norm_lam_inv_πθ : ‖modularLambdaH (-(arcπθ : ℂ)⁻¹)‖ ≤
        160000 * Real.exp (-Real.pi * (-(arcπθ : ℂ)⁻¹).im) :=
      modularLambdaH_norm_le_exp_of_im_ge_one h_im_inv_πθ_ge_one
    -- S-action on arc(π - θ): λ(arc(π-θ)) + λ(-1/arc(π-θ)) = 1.
    have h_arcπθ_im_pos : 0 < arcπθ.im := by
      rw [harcπθ_def]
      exact modularLambdaH_F_Y_arc_im_pos hδ_pos hR₀_pos.le
        (by linarith [hθ_hi]) hπθ_le
    have h_S_πθ : modularLambdaH arcπθ + modularLambdaH (-1/arcπθ) = 1 :=
      modularLambdaH_add_S_smul_eq_one h_arcπθ_im_pos
    have h_neg_eq_πθ : -1/arcπθ = -arcπθ⁻¹ := by field_simp
    rw [h_neg_eq_πθ] at h_S_πθ
    have h_diff_πθ : modularLambdaH arcπθ - 1 = -modularLambdaH (-(arcπθ : ℂ)⁻¹) := by
      linear_combination h_S_πθ
    have h_norm_diff_πθ : ‖modularLambdaH arcπθ - 1‖ = ‖modularLambdaH (-(arcπθ : ℂ)⁻¹)‖ := by
      rw [h_diff_πθ, norm_neg]
    -- ‖λ(arc(π-θ)) - 1‖ ≤ 160000 · exp(-π · K_1) < 1/(‖w‖ + 2).
    have h_exp_mono_πθ : Real.exp (-Real.pi * (-(arcπθ : ℂ)⁻¹).im) ≤
        Real.exp (-Real.pi * K_1) := by
      apply Real.exp_le_exp.mpr
      have := h_im_inv_πθ_ge
      rw [harcπθ_def] at this
      nlinarith [Real.pi_pos, this]
    have h_bound_πθ : ‖modularLambdaH arcπθ - 1‖ ≤ 160000 * Real.exp (-Real.pi * K_1) := by
      rw [h_norm_diff_πθ]
      exact le_trans h_norm_lam_inv_πθ (mul_le_mul_of_nonneg_left h_exp_mono_πθ (by norm_num))
    have h_w_norm_plus_two_pos : (0 : ℝ) < ‖w‖ + 2 := by
      have : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
      linarith
    have h_inv_pos : (0 : ℝ) < 1 / (‖w‖ + 2) := by positivity
    -- 160000 · exp(-π K_1) < 1/(‖w‖+2) via exp_bound helper.
    have h_final_πθ : 160000 * Real.exp (-Real.pi * K_1) < 1 / (‖w‖ + 2) := by
      have h_helper := modularLambdaH_F_Y_arc_ne_exp_bound_mul (‖w‖ + 2) h_w_norm_plus_two_pos
      have hK_1_eq : K_1 = max (Real.log (160000 * (‖w‖ + 2))) 1 + 1 := by
        rw [hK_1_def, hL_1_def]
      rw [hK_1_eq]; exact h_helper
    have h_strict_πθ : ‖modularLambdaH arcπθ - 1‖ < 1 / (‖w‖ + 2) :=
      lt_of_le_of_lt h_bound_πθ h_final_πθ
    -- Transfer to σ via conjugation.
    have h_norm_diff_σ : ‖modularLambdaH σ - 1‖ = ‖modularLambdaH arcπθ - 1‖ := by
      rw [h_conj_lam]
      rw [show starRingEnd ℂ (modularLambdaH σ) - 1 = starRingEnd ℂ (modularLambdaH σ - 1) by
        rw [map_sub, map_one]]
      rw [norm_conj]
    have h_strict_σ : ‖modularLambdaH σ - 1‖ < 1 / (‖w‖ + 2) := by
      rw [h_norm_diff_σ]; exact h_strict_πθ
    -- T-action: λ(σ + 1) = λ σ / (λ σ - 1).
    have h_T : modularLambdaH (σ + 1) = modularLambdaH σ / (modularLambdaH σ - 1) :=
      modularLambdaH_add_one_eq_div_sub_one hσ_im_pos
    have h_σ_plus_one : σ + 1 = arc := by simp [hσ_def]
    rw [h_σ_plus_one] at h_T
    -- λ(σ) - 1 ≠ 0.
    have h_lam_σ_sub_one_ne : modularLambdaH σ - 1 ≠ 0 :=
      sub_ne_zero.mpr (modularLambdaH_ne_one hσ_im_pos)
    -- |λ(σ)| ≥ 1 - ‖λ(σ) - 1‖.
    have h_lam_σ_norm_ge : 1 - ‖modularLambdaH σ - 1‖ ≤ ‖modularLambdaH σ‖ := by
      have h_rtri : ‖(1 : ℂ)‖ - ‖modularLambdaH σ‖ ≤ ‖(1 : ℂ) - modularLambdaH σ‖ :=
        norm_sub_norm_le (1 : ℂ) (modularLambdaH σ)
      have h_simp : (1 : ℂ) - modularLambdaH σ = -(modularLambdaH σ - 1) := by ring
      rw [norm_one, h_simp, norm_neg] at h_rtri
      linarith
    -- |λ(arc)| = |λ σ| / |λ σ - 1|.
    have h_norm_lam_arc : ‖modularLambdaH arc‖ = ‖modularLambdaH σ‖ / ‖modularLambdaH σ - 1‖ := by
      rw [h_T, norm_div]
    -- Show |λ(arc)| > ‖w‖.
    set c : ℝ := ‖modularLambdaH σ - 1‖ with hc_def
    have hc_lt : c < 1 / (‖w‖ + 2) := h_strict_σ
    have hc_pos : 0 < c := by
      rw [hc_def, norm_pos_iff]; exact h_lam_σ_sub_one_ne
    have h_lam_σ_ge : 1 - c ≤ ‖modularLambdaH σ‖ := by
      rw [hc_def]; exact h_lam_σ_norm_ge
    have h_norm_lam_arc_gt : ‖w‖ < ‖modularLambdaH arc‖ := by
      rw [h_norm_lam_arc]
      exact modularLambdaH_F_Y_arc_cusp_1_norm_bound (norm_nonneg w) hc_pos hc_lt h_lam_σ_ge
    rw [h_lam_arc_eq] at h_norm_lam_arc_gt
    exact lt_irrefl _ h_norm_lam_arc_gt
  · push Not at h_θ_le_θ_0
    -- θ > θ_0. Check if θ ≥ π - θ_0.
    by_cases h_θ_ge : Real.pi - θ_0 ≤ θ
    · -- Cusp 0 case: θ ∈ [π - θ_0, π] ⊆ [π - θ_K_0, π].
      have hθ_in_cusp_0 : Real.pi - θ_K_0 ≤ θ := by linarith [hθ_0_le_θ_K_0]
      have h_im_inv_ge : K_0 ≤ (-(arc)⁻¹).im := by
        have := h_cusp_0_bound δ R₀ hδ_pos hδ_le_δ_K_0 hR₀_lo hR₀_lt θ hθ_in_cusp_0 hθ_hi
        rw [harc_def]; exact this
      have h_im_inv_ge_one : 1 ≤ (-(arc)⁻¹).im := le_trans hK_0_ge_one h_im_inv_ge
      -- Norm bound: ‖λ(-arc⁻¹)‖ ≤ 160000 · exp(-π · Im(-arc⁻¹)) ≤ 160000 · exp(-π K_0).
      have h_norm_lam_inv : ‖modularLambdaH (-(arc : ℂ)⁻¹)‖ ≤
          160000 * Real.exp (-Real.pi * (-(arc : ℂ)⁻¹).im) :=
        modularLambdaH_norm_le_exp_of_im_ge_one h_im_inv_ge_one
      -- S-action: λ(τ) + λ(-1/τ) = 1.
      have h_S : modularLambdaH arc + modularLambdaH (-1/arc) = 1 :=
        modularLambdaH_add_S_smul_eq_one harc_im_pos
      have h_neg_eq : -1/arc = -arc⁻¹ := by field_simp
      rw [h_neg_eq] at h_S
      have h_diff_eq : modularLambdaH arc - 1 = -modularLambdaH (-(arc : ℂ)⁻¹) := by
        linear_combination h_S
      have h_norm_diff : ‖modularLambdaH arc - 1‖ = ‖modularLambdaH (-(arc : ℂ)⁻¹)‖ := by
        rw [h_diff_eq, norm_neg]
      -- exp(-π · Im(-arc⁻¹)) ≤ exp(-π · K_0).
      have h_exp_mono : Real.exp (-Real.pi * (-(arc : ℂ)⁻¹).im) ≤
          Real.exp (-Real.pi * K_0) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos, h_im_inv_ge]
      have h_bound : ‖modularLambdaH arc - 1‖ ≤ 160000 * Real.exp (-Real.pi * K_0) := by
        rw [h_norm_diff]
        refine le_trans h_norm_lam_inv ?_
        exact mul_le_mul_of_nonneg_left h_exp_mono (by norm_num)
      -- 160000 · exp(-π · K_0) < ‖w - 1‖ via exp_bound helper.
      have h_final_bound : 160000 * Real.exp (-Real.pi * K_0) < ‖w - 1‖ := by
        have h_helper := modularLambdaH_F_Y_arc_ne_exp_bound_div ‖w - 1‖ hw_one_norm_pos
        have hK_0_eq : K_0 = max (Real.log (160000 / ‖w - 1‖)) 1 + 1 := by
          rw [hK_0_def, hL_0_def]
        rw [hK_0_eq]; exact h_helper
      have h_strict : ‖modularLambdaH arc - 1‖ < ‖w - 1‖ :=
        lt_of_le_of_lt h_bound h_final_bound
      rw [h_lam_arc_eq] at h_strict
      exact lt_irrefl _ h_strict
    · -- Middle case: θ ∈ (θ_0, π - θ_0).
      push Not at h_θ_ge
      have hθ_in_middle_lo : θ_0 ≤ θ := le_of_lt h_θ_le_θ_0
      have hθ_in_middle_hi : θ ≤ Real.pi - θ_0 := le_of_lt h_θ_ge
      -- arc ∈ closedBall τ_K r_K (Helper 8.3.c).
      have h_arc_in_ball := modularLambdaH_arc_lipschitz_arc_in_ball
        hδ_pos hR₀_lo hR₀_lt hθ_0_pos hθ_0_lt_pi_2 hδ_le_sin_θ_0_quarter
        hθ_in_middle_lo hθ_in_middle_hi
      -- semi ∈ closedBall τ_K r_K (Helper 8.3.b).
      have h_semi_in_ball := modularLambdaH_arc_lipschitz_semi_in_ball
        hθ_0_pos hθ_0_lt_pi_2 hθ_in_middle_lo hθ_in_middle_hi
      -- Apply Lipschitz bound M.
      have h_lipschitz_bd := hM_lipschitz arc
        (_root_.circleMap (1/2 : ℂ) (1/2) θ)
        (by rw [harc_def]; exact h_arc_in_ball) h_semi_in_ball
      -- semicircle real-valued: Im λ(semi) = 0.
      have hθ_pos : 0 < θ := by linarith [hθ_0_pos]
      have hθ_lt_pi : θ < Real.pi := by linarith [hθ_0_pos]
      have hθ_sin_pos : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
      have h_semi_im_pos : 0 < (_root_.circleMap (1/2 : ℂ) (1/2) θ).im := by
        rw [_root_.circleMap]
        show 0 < ((1/2 : ℂ) + ((1/2 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)).im
        rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
        have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
        rw [h_half_im]
        have h_pos : 0 < (1 / 2 : ℝ) * Real.sin θ := by positivity
        linarith
      have h_semi_circle : ‖2 * (_root_.circleMap (1/2 : ℂ) (1/2) θ) - 1‖ = 1 := by
        rw [_root_.circleMap]
        have : 2 * ((1/2 : ℂ) + ((1/2 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) - 1 =
            Complex.exp (θ * Complex.I) := by push_cast; ring
        rw [this, Complex.norm_exp]
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
      have h_semi_im_zero : (modularLambdaH (_root_.circleMap (1/2 : ℂ) (1/2) θ)).im = 0 :=
        modularLambdaH_semicircle_real h_semi_im_pos h_semi_circle
      rw [h_semi_im_zero, sub_zero] at h_lipschitz_bd
      -- Helper 8.1: distance bound.
      have h_arc_to_semi := modularLambdaH_arc_to_semicircle_dist hδ_pos hR₀_pos hR₀_lt θ
      -- |Im λ(arc)| ≤ M · ‖arc - semi‖ ≤ M · (δ + 1/2 - R₀).
      have h_im_bound : |(modularLambdaH arc).im| ≤ M * (δ + (1/2 - R₀)) := by
        calc |(modularLambdaH arc).im|
            ≤ M * ‖arc - _root_.circleMap (1/2 : ℂ) (1/2) θ‖ := by
              rw [harc_def] at h_lipschitz_bd ⊢; exact h_lipschitz_bd
          _ ≤ M * (δ + (1/2 - R₀)) := by
              apply mul_le_mul_of_nonneg_left _ hM_pos.le
              rw [harc_def]
              exact h_arc_to_semi
      -- 1/2 - R₀ ≤ 2δ² (from R₀ > √(1/4 - δ²)).
      have h_half_minus_R₀ : 1/2 - R₀ ≤ 2 * δ^2 :=
        modularLambdaH_F_Y_arc_half_minus_R₀_bound hδ_pos hδ_le_quarter
          hR₀_lo hR₀_lt hR₀_pos
      -- δ ≤ w.im/(4M) (from hδ_le_δ_M and δ_M definition).
      have hδ_le_wim_4M : δ ≤ w.im / (4*M) := by
        have h_δ_M_eq : δ_M = w.im / (4*M) := hδ_M_def
        linarith [hδ_le_δ_M, h_δ_M_eq]
      -- Apply the pure polynomial helper.
      have h_M_bound : M * (δ + (1/2 - R₀)) < w.im :=
        modularLambdaH_F_Y_arc_middle_poly_bound hM_pos hδ_pos hδ_le_quarter
          hδ_le_wim_4M h_half_minus_R₀ hw
      -- λ(arc) = w gives Im λ(arc) = w.im. |Im λ(arc)| = w.im (since w.im > 0).
      -- But |Im λ(arc)| ≤ M · (δ + 1/2 - R₀) < w.im. Contradiction.
      rw [h_lam_arc_eq] at h_im_bound
      have h_abs_w_im : |w.im| = w.im := abs_of_pos hw
      rw [h_abs_w_im] at h_im_bound
      linarith [h_M_bound, h_im_bound]

end NoWanderingDomains
