/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.ModularFunction.QExpansionBounds

/-!
# Four-term q-expansion bounds: theta functions and bracket helpers

Four-term q-expansion bounds for `jacobiTheta₂ (τ/2) τ`, `θ₂`, and `θ₃` on `τ.im ≥ 1`
(`jacobiTheta₂_half_sub_four_term_norm_le_of_im_ge_one`,
`theta2_norm_sub_four_term_le_of_im_ge_one`,
`theta3_sub_four_term_norm_le_of_im_ge_one`), and the bracket-bound helpers
(`modularLambda_four_term_bracket_bound` and its widened variant) expanding `(θ₂/θ₃)⁴`
one order beyond the three-term version.

These bounds extend the three-term q-expansion infrastructure by one order: the
underlying `jacobiTheta₂` series gains one more term and the algebraic `(θ₂/θ₃)⁴`
expansion one more order. Via the `λ` bound in `FourTermBounds/Lambda.lean` they power
the Cauchy estimate that closes
`modularLambdaH_deriv_norm_sub_three_term_le_of_im_ge_one` in
`Gamma2FundamentalDomain/CuspAsymptotics.lean`.
-/

namespace NoWanderingDomains
open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped ModularForm Manifold MatrixGroups

/-- **Four-term q-expansion of `jacobiTheta₂(τ/2, τ)`.** For `τ.im ≥ 1`,
`‖jacobiTheta₂(τ/2, τ) - 2 - 2·exp(2πi τ) - 2·exp(6πi τ) - 2·exp(12πi τ)‖ ≤ 8·exp(-20π·τ.im)`.
Tail of `2 ∑_{k≥0} exp(πi k(k+1) τ)` starting at
`k = 4` (i.e., `2·exp(20πi τ)`). Extends
`jacobiTheta₂_half_sub_three_term_norm_le_of_im_ge_one` by one term. -/
theorem jacobiTheta₂_half_sub_four_term_norm_le_of_im_ge_one
    {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta₂ (τ / 2) τ - 2 - 2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
        2 * Complex.exp (6 * Real.pi * Complex.I * τ) -
        2 * Complex.exp (12 * Real.pi * Complex.I * τ)‖ ≤
      8 * Real.exp (-20 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  set r : ℝ := Real.exp (-2 * Real.pi * τ.im) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_nn : 0 ≤ r := hr_pos.le
  have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_2pi_gt_1 : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h_exp_2pi_gt_2 : (2 : ℝ) < Real.exp (2 * Real.pi) := by
    have h_mono : Real.exp 1 ≤ Real.exp (2 * Real.pi) := Real.exp_le_exp.mpr h_2pi_gt_1.le
    linarith
  have hr_lt : r < 1 / 2 := by
    have h_arg : -2 * Real.pi * τ.im ≤ -2 * Real.pi := by nlinarith
    have h_le : r ≤ Real.exp (-2 * Real.pi) := Real.exp_le_exp.mpr h_arg
    have h_exp_neg_lt : Real.exp (-2 * Real.pi) < 1/2 := by
      rw [show (-2 * Real.pi : ℝ) = -(2 * Real.pi) from by ring, Real.exp_neg]
      rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ from by ring]
      exact inv_strictAnti₀ (by norm_num : (0:ℝ) < 2) h_exp_2pi_gt_2
    linarith
  have hr_lt_one : r < 1 := by linarith
  have hr5_lt_one : r^5 < 1 := by
    have : r^5 < (1/2)^5 := pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    nlinarith
  have hr5_lt_half : r^5 < 1/2 := by
    have h1 : r^5 < (1/2)^5 := pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    have h2 : ((1/2 : ℝ))^5 ≤ 1/2 := by norm_num
    linarith
  have h_one_sub_r5_pos : 0 < 1 - r^5 := by linarith
  have h_inv_one_sub_r5_le : (1 - r^5)⁻¹ ≤ 2 := by
    rw [show (2 : ℝ) = (1/2)⁻¹ from by norm_num]
    exact inv_anti₀ (by norm_num : (0:ℝ) < 1/2) (by linarith)
  -- HasSum setup.
  have h_hasSum_int := hasSum_jacobiTheta₂_term (τ / 2) hτim_pos
  have h_term_zero : jacobiTheta₂_term 0 (τ / 2) τ = 1 := by
    unfold jacobiTheta₂_term; simp
  have h_term_one : jacobiTheta₂_term 1 (τ / 2) τ = Complex.exp (2 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  have h_term_neg_one : jacobiTheta₂_term (-1 : ℤ) (τ / 2) τ = 1 := by
    unfold jacobiTheta₂_term
    have h_arg : (2 : ℂ) * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * (τ / 2) +
        Real.pi * Complex.I * ((-1 : ℤ) : ℂ)^2 * τ = 0 := by push_cast; ring
    rw [h_arg, Complex.exp_zero]
  have h_term_two : jacobiTheta₂_term 2 (τ / 2) τ =
      Complex.exp (6 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  have h_term_neg_two : jacobiTheta₂_term (-2 : ℤ) (τ / 2) τ =
      Complex.exp (2 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  have h_term_three : jacobiTheta₂_term 3 (τ / 2) τ =
      Complex.exp (12 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  have h_term_neg_three : jacobiTheta₂_term (-3 : ℤ) (τ / 2) τ =
      Complex.exp (6 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  have h_term_four : jacobiTheta₂_term 4 (τ / 2) τ =
      Complex.exp (20 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  have h_term_neg_four : jacobiTheta₂_term (-4 : ℤ) (τ / 2) τ =
      Complex.exp (12 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  -- Pair HasSum.
  have h_pair_hasSum : HasSum (fun n : ℕ =>
      jacobiTheta₂_term (n : ℤ) (τ/2) τ + jacobiTheta₂_term (-(n : ℤ)) (τ/2) τ)
      (jacobiTheta₂ (τ/2) τ + 1) := by
    have := h_hasSum_int.nat_add_neg
    rw [h_term_zero] at this
    exact this
  have h_pair_summable : Summable (fun n : ℕ =>
      jacobiTheta₂_term ((n : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-((n : ℕ) : ℤ)) (τ/2) τ) := h_pair_hasSum.summable
  -- Sum of first 5 nats (n=0,1,2,3,4):
  -- 2 + (Q² + 1) + (Q⁶ + Q²) + (Q¹² + Q⁶) + (Q²⁰ + Q¹²)
  --   = 3 + 2Q² + 2Q⁶ + 2Q¹² + Q²⁰.
  have h_sum_five :
      ∑ i ∈ Finset.range 5, (jacobiTheta₂_term ((i : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-((i : ℕ) : ℤ)) (τ/2) τ) =
      3 + 2 * Complex.exp (2 * Real.pi * Complex.I * τ) +
      2 * Complex.exp (6 * Real.pi * Complex.I * τ) +
      2 * Complex.exp (12 * Real.pi * Complex.I * τ) +
      Complex.exp (20 * Real.pi * Complex.I * τ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    simp only [Nat.cast_zero, neg_zero, Nat.cast_one, Nat.cast_ofNat]
    rw [h_term_zero, h_term_one, h_term_neg_one, h_term_two, h_term_neg_two,
        h_term_three, h_term_neg_three, h_term_four, h_term_neg_four]
    ring
  have h_pair_tsum : ∑' n : ℕ, (jacobiTheta₂_term ((n : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-((n : ℕ) : ℤ)) (τ/2) τ) =
      jacobiTheta₂ (τ/2) τ + 1 := h_pair_hasSum.tsum_eq
  -- HasSum tail starting at n=5.
  have h_tail_hasSum : HasSum (fun n : ℕ =>
      jacobiTheta₂_term (((n + 5) : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-(((n + 5) : ℕ) : ℤ)) (τ/2) τ)
      (jacobiTheta₂ (τ/2) τ - 2 -
        2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
        2 * Complex.exp (6 * Real.pi * Complex.I * τ) -
        2 * Complex.exp (12 * Real.pi * Complex.I * τ) -
        Complex.exp (20 * Real.pi * Complex.I * τ)) := by
    have h_shift_summable : Summable (fun n : ℕ =>
        jacobiTheta₂_term (((n + 5) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 5) : ℕ) : ℤ)) (τ/2) τ) := by
      have := (summable_nat_add_iff (k := 5)).mpr h_pair_summable
      exact this
    rw [Summable.hasSum_iff h_shift_summable]
    have h_eq := (Summable.sum_add_tsum_nat_add 5 h_pair_summable).symm
    rw [h_pair_tsum] at h_eq
    rw [h_sum_five] at h_eq
    linear_combination -h_eq
  -- Express target as exp(20πi τ) + tail.
  have h_eq : jacobiTheta₂ (τ/2) τ - 2 -
      2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
      2 * Complex.exp (6 * Real.pi * Complex.I * τ) -
      2 * Complex.exp (12 * Real.pi * Complex.I * τ) =
      Complex.exp (20 * Real.pi * Complex.I * τ) +
      ∑' n : ℕ, (jacobiTheta₂_term (((n + 5) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 5) : ℕ) : ℤ)) (τ/2) τ) := by
    rw [h_tail_hasSum.tsum_eq]; ring
  rw [h_eq]
  refine (norm_add_le _ _).trans ?_
  -- ‖exp(20πi τ)‖ = r¹⁰ (where r = exp(-2π τ.im)).
  have h_norm_exp_20 : ‖Complex.exp (20 * Real.pi * Complex.I * τ)‖ = r^10 := by
    rw [Complex.norm_exp, hr_def, ← Real.exp_nat_mul]
    congr 1
    have h_eq : (20 * Real.pi * Complex.I * τ : ℂ) =
        ((20 * Real.pi : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [h_norm_exp_20]
  -- Termwise bound: for n : ℕ, ‖term(n+5) + term(-(n+5))‖ ≤ 2 r¹⁰ (r⁵)^n.
  -- For k = n+5 ≥ 5: k(k+1) ≥ 30, k(k-1) ≥ 20. With r = exp(-2π τ.im),
  -- ‖term(k)‖ = r^{k(k+1)/2}, ‖term(-k)‖ = r^{k(k-1)/2}.
  -- (n+5)(n+4)/2 ≥ 10 + 5n: (n+5)(n+4)/2 - 10 - 5n = (n²-n)/2 ≥ 0.
  -- (n+5)(n+6)/2 ≥ (n+5)(n+4)/2 ≥ 10 + 5n.
  have h_termwise : ∀ n : ℕ,
      ‖jacobiTheta₂_term (((n + 5) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 5) : ℕ) : ℤ)) (τ/2) τ‖ ≤ 2 * (r^10 * (r^5)^n) := by
    intro n
    refine (norm_add_le _ _).trans ?_
    have h_bound_eq : r^10 * (r^5)^n = Real.exp ((10 + 5 * (n : ℝ)) * (-2 * Real.pi * τ.im)) := by
      have h_r10_eq : r^10 = Real.exp (10 * (-2 * Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul]; push_cast; ring_nf
      have h_r5_pow_eq : (r^5)^n = Real.exp ((5 * (n : ℝ)) * (-2 * Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1; push_cast; ring
      rw [h_r10_eq, h_r5_pow_eq, ← Real.exp_add]
      congr 1; ring
    have h_pi_tau_nn : 0 ≤ Real.pi * τ.im := mul_nonneg hπ_pos.le hτim_pos.le
    have hN_pos : ((((n + 5) : ℕ) : ℤ) : ℝ) = (n : ℝ) + 5 := by push_cast; ring
    have h_pos_norm : ‖jacobiTheta₂_term (((n + 5) : ℕ) : ℤ) (τ/2) τ‖ ≤ r^10 * (r^5)^n := by
      rw [jacobiTheta₂_term_half_norm, hN_pos, h_bound_eq]
      apply Real.exp_le_exp.mpr
      -- (n+5)(n+6) ≥ 2·(10 + 5n) = 20 + 10n.
      have h_ineq : 20 + 10 * (n : ℝ) ≤ ((n : ℝ) + 5) * ((n : ℝ) + 6) := by nlinarith
      have h_mul : Real.pi * τ.im * (20 + 10 * (n : ℝ)) ≤
          Real.pi * τ.im * (((n : ℝ) + 5) * ((n : ℝ) + 6)) :=
        mul_le_mul_of_nonneg_left h_ineq h_pi_tau_nn
      linarith
    have h_neg_norm : ‖jacobiTheta₂_term (-(((n + 5) : ℕ) : ℤ)) (τ/2) τ‖ ≤
        r^10 * (r^5)^n := by
      rw [jacobiTheta₂_term_half_norm]
      have hN' : ((-(((n + 5) : ℕ) : ℤ) : ℤ) : ℝ) = -((n : ℝ) + 5) := by push_cast; ring
      rw [hN', h_bound_eq]
      apply Real.exp_le_exp.mpr
      -- (-(n+5))(-(n+5)+1) = (n+5)(n+4) ≥ 2·(10 + 5n) = 20 + 10n.
      have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h_n_sq_ge : (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simp
        · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          nlinarith
      have h_ineq : 20 + 10 * (n : ℝ) ≤ (-((n : ℝ) + 5)) * (-((n : ℝ) + 5) + 1) := by nlinarith
      have h_mul : Real.pi * τ.im * (20 + 10 * (n : ℝ)) ≤
          Real.pi * τ.im * ((-((n : ℝ) + 5)) * (-((n : ℝ) + 5) + 1)) :=
        mul_le_mul_of_nonneg_left h_ineq h_pi_tau_nn
      linarith
    linarith
  -- Summability.
  have h_bound_summable : Summable (fun n : ℕ => 2 * (r^10 * (r^5)^n)) := by
    have h_geo : Summable (fun n : ℕ => (r^5)^n) :=
      summable_geometric_of_lt_one (by positivity) hr5_lt_one
    have : Summable (fun n : ℕ => r^10 * (r^5)^n) := h_geo.mul_left _
    exact this.mul_left _
  have h_bound_tsum : ∑' n : ℕ, 2 * (r^10 * (r^5)^n) =
      2 * r^10 * (1 - r^5)⁻¹ := by
    rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr5_lt_one]
    ring
  have h_norm_summable : Summable (fun n : ℕ =>
      ‖jacobiTheta₂_term (((n + 5) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 5) : ℕ) : ℤ)) (τ/2) τ‖) :=
    h_bound_summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_termwise
  have h_norm_tsum_le := norm_tsum_le_tsum_norm h_norm_summable
  have h_tsum_le : (∑' n : ℕ,
      ‖jacobiTheta₂_term (((n + 5) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 5) : ℕ) : ℤ)) (τ/2) τ‖) ≤
      2 * r^10 * (1 - r^5)⁻¹ := by
    rw [← h_bound_tsum]
    exact h_norm_summable.tsum_le_tsum h_termwise h_bound_summable
  have h_step : ‖∑' n : ℕ, (jacobiTheta₂_term (((n + 5) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 5) : ℕ) : ℤ)) (τ/2) τ)‖ ≤ 2 * r^10 * (1 - r^5)⁻¹ :=
    h_norm_tsum_le.trans h_tsum_le
  have hr10_pos : 0 < r^10 := by positivity
  have h_final : r^10 + 2 * r^10 * (1 - r^5)⁻¹ ≤ 8 * r^10 := by
    have h1 : 2 * r^10 * (1 - r^5)⁻¹ ≤ 2 * r^10 * 2 := by
      apply mul_le_mul_of_nonneg_left h_inv_one_sub_r5_le
      positivity
    linarith
  have hr10_eq : r^10 = Real.exp (-20 * Real.pi * τ.im) := by
    rw [hr_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc r^10 + ‖∑' n : ℕ, (jacobiTheta₂_term (((n + 5) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 5) : ℕ) : ℤ)) (τ/2) τ)‖
      ≤ r^10 + 2 * r^10 * (1 - r^5)⁻¹ := by linarith [h_step]
    _ ≤ 8 * r^10 := h_final
    _ = 8 * Real.exp (-20 * Real.pi * τ.im) := by rw [hr10_eq]

/-- **Four-term leading bound for `θ₂`.** For `τ.im ≥ 1`,
`‖θ₂(τ) − 2·exp(πi τ/4)·(1 + exp(2πi τ) + exp(6πi τ) + exp(12πi τ))‖ ≤ 8·exp(−81π·τ.im/4)`.
Extends the three-term
`theta2_norm_sub_three_term_le_of_im_ge_one` using the four-term
`jacobiTheta₂` bound. -/
theorem theta2_norm_sub_four_term_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta2 τ - 2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
        (1 + Complex.exp (2 * Real.pi * Complex.I * τ) +
          Complex.exp (6 * Real.pi * Complex.I * τ) +
          Complex.exp (12 * Real.pi * Complex.I * τ))‖ ≤
      8 * Real.exp (-(81 * Real.pi * τ.im / 4)) := by
  unfold theta2
  have h_factor :
      Complex.exp (Real.pi * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ -
        2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
          (1 + Complex.exp (2 * Real.pi * Complex.I * τ) +
            Complex.exp (6 * Real.pi * Complex.I * τ) +
            Complex.exp (12 * Real.pi * Complex.I * τ)) =
      Complex.exp (Real.pi * Complex.I * τ / 4) *
        (jacobiTheta₂ (τ / 2) τ - 2 -
          2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
          2 * Complex.exp (6 * Real.pi * Complex.I * τ) -
          2 * Complex.exp (12 * Real.pi * Complex.I * τ)) := by
    ring
  rw [h_factor, norm_mul]
  have h_norm_exp :
      ‖Complex.exp (Real.pi * Complex.I * τ / 4)‖ = Real.exp (-(Real.pi * τ.im / 4)) := by
    rw [Complex.norm_exp]
    congr 1
    have h_eq : (Real.pi * Complex.I * τ / 4 : ℂ) =
        ((Real.pi / 4 : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [h_norm_exp]
  have h_tail := jacobiTheta₂_half_sub_four_term_norm_le_of_im_ge_one hτ
  have h_exp_nn : 0 ≤ Real.exp (-(Real.pi * τ.im / 4)) := (Real.exp_pos _).le
  have h_combine :
      Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-20 * Real.pi * τ.im)) =
      8 * Real.exp (-(81 * Real.pi * τ.im / 4)) := by
    rw [show (Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-20 * Real.pi * τ.im)) : ℝ) =
        8 * (Real.exp (-(Real.pi * τ.im / 4)) * Real.exp (-20 * Real.pi * τ.im)) from by ring]
    rw [← Real.exp_add]
    exact congr_arg (fun x => 8 * Real.exp x) (by ring)
  calc Real.exp (-(Real.pi * τ.im / 4)) *
        ‖jacobiTheta₂ (τ / 2) τ - 2 -
          2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
          2 * Complex.exp (6 * Real.pi * Complex.I * τ) -
          2 * Complex.exp (12 * Real.pi * Complex.I * τ)‖
      ≤ Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-20 * Real.pi * τ.im)) := by
        exact mul_le_mul_of_nonneg_left h_tail h_exp_nn
    _ = 8 * Real.exp (-(81 * Real.pi * τ.im / 4)) := h_combine

/-- **Four-term q-expansion of `θ₃`.** For `τ.im ≥ 1`,
`‖θ₃(τ) − 1 − 2·exp(πi τ) − 2·exp(4πi τ) − 2·exp(9πi τ)‖ ≤ 4·exp(−16π·τ.im)`.
Extends
`theta3_sub_one_minus_2q_minus_2q4_norm_le_of_im_ge_one` by one term.
With `q = exp(πi τ)`, the first four non-zero terms of
`θ₃ = 1 + 2q + 2q⁴ + 2q⁹ + 2q^{16} + …` are subtracted; the tail starts at `2 q^{16}`. -/
theorem theta3_sub_four_term_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta3 τ - 1 - 2 * Complex.exp (Real.pi * Complex.I * τ) -
        2 * Complex.exp (4 * Real.pi * Complex.I * τ) -
        2 * Complex.exp (9 * Real.pi * Complex.I * τ)‖ ≤
      4 * Real.exp (-16 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  set r : ℝ := Real.exp (-Real.pi * τ.im) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_le_exp_neg_pi : r ≤ Real.exp (-Real.pi) := by
    rw [hr_def]; apply Real.exp_le_exp.mpr; nlinarith
  have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_exp3_gt_16 : (16 : ℝ) < Real.exp 3 := by
    have h_eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
    rw [h_eq]; nlinarith [h_e_gt, Real.exp_pos (1 : ℝ)]
  have h_exp_pi_gt_16 : (16 : ℝ) < Real.exp Real.pi :=
    h_exp3_gt_16.trans_le (Real.exp_le_exp.mpr Real.pi_gt_three.le)
  have h_exp_neg_pi_lt : Real.exp (-Real.pi) < 1/16 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/16),
        show (1/16 : ℝ)⁻¹ = 16 from by norm_num]
    exact h_exp_pi_gt_16
  have hr_lt : r < 1/16 := lt_of_le_of_lt hr_le_exp_neg_pi h_exp_neg_pi_lt
  have hr_lt_one : r < 1 := by linarith
  -- r⁸ < 1.
  have hr8_lt_one : r^8 < 1 := by
    have h1 : r^8 < (1/16)^8 := pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    have h2 : ((1/16 : ℝ))^8 < 1 := by norm_num
    linarith
  -- r⁸ < 1/2.
  have hr8_lt_half : r^8 < 1/2 := by
    have h1 : r^8 < (1/16)^8 := pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    have h2 : ((1/16 : ℝ))^8 ≤ 1/2 := by norm_num
    linarith
  have h_one_sub_r8_pos : 0 < 1 - r^8 := by linarith
  have h_inv_le_2 : (1 - r^8)⁻¹ ≤ 2 := by
    rw [show (2 : ℝ) = (1/2)⁻¹ from by norm_num]
    apply inv_anti₀ (by norm_num : (0:ℝ) < 1/2) (by linarith)
  -- HasSum on ℕ for jacobiTheta.
  have h_hasSum := hasSum_nat_jacobiTheta hτim_pos
  have h_summable := h_hasSum.summable
  -- Sum of first three terms: q + q⁴ + q⁹.
  have h_sum_three : ∑ i ∈ Finset.range 3,
      Complex.exp (Real.pi * Complex.I * ((i : ℂ) + 1)^2 * τ) =
      Complex.exp (Real.pi * Complex.I * τ) +
      Complex.exp (4 * Real.pi * Complex.I * τ) +
      Complex.exp (9 * Real.pi * Complex.I * τ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    push_cast
    congr 2
    · congr 1; ring
    · congr 1; ring
    · congr 1; ring
  -- Split off n=0,1,2.
  have h_shifted : Summable (fun n : ℕ =>
      Complex.exp (Real.pi * Complex.I * ((n + 3 : ℕ) + 1 : ℂ)^2 * τ)) :=
    (summable_nat_add_iff (k := 3)).mpr h_summable
  have h_split := h_summable.sum_add_tsum_nat_add 3
  rw [h_sum_three, h_hasSum.tsum_eq] at h_split
  unfold theta3
  have h_id : jacobiTheta τ - 1 - 2 * Complex.exp (Real.pi * Complex.I * τ) -
      2 * Complex.exp (4 * Real.pi * Complex.I * τ) -
      2 * Complex.exp (9 * Real.pi * Complex.I * τ) =
      2 * ∑' n : ℕ, Complex.exp (Real.pi * Complex.I *
        (((n + 3 : ℕ) : ℂ) + 1)^2 * τ) := by
    linear_combination -2 * h_split
  rw [h_id, norm_mul, Complex.norm_two]
  -- Termwise: ‖exp(πi (n+4)² τ)‖ ≤ exp(-π · (n+4)² · τ.im) ≤ r^16 · (r^8)^n.
  have hr8_lt_one' : r^8 < 1 := hr8_lt_one
  have h_term_norm : ∀ n : ℕ,
      ‖Complex.exp (Real.pi * Complex.I * (((n + 3 : ℕ) : ℂ) + 1)^2 * τ)‖ ≤
      r^16 * (r^8)^n := by
    intro n
    rw [Complex.norm_exp]
    have h_re : (Real.pi * Complex.I * (((n + 3 : ℕ) : ℂ) + 1)^2 * τ).re =
        -(Real.pi * ((n : ℝ) + 4)^2 * τ.im) := by
      have h_factor : Real.pi * Complex.I * (((n + 3 : ℕ) : ℂ) + 1)^2 * τ =
          ((Real.pi * ((n : ℝ) + 4)^2 : ℝ) : ℂ) * (Complex.I * τ) := by
        push_cast; ring
      rw [h_factor, Complex.re_ofReal_mul]
      rw [show (Complex.I * τ).re = -τ.im from by
        rw [Complex.mul_re, Complex.I_re, Complex.I_im]; ring]
      ring
    rw [h_re]
    -- Goal: exp(-π (n+4)² τ.im) ≤ r^16 · (r^8)^n.
    have h_bound_eq : r^16 * (r^8)^n =
        Real.exp ((16 + 8 * (n : ℝ)) * (-Real.pi * τ.im)) := by
      have h_r16_eq : r^16 = Real.exp (16 * (-Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul]; push_cast; ring_nf
      have h_r8_pow_eq : (r^8)^n = Real.exp ((8 * (n : ℝ)) * (-Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1; push_cast; ring
      rw [h_r16_eq, h_r8_pow_eq, ← Real.exp_add]
      congr 1; ring
    rw [h_bound_eq]
    apply Real.exp_le_exp.mpr
    -- -(π (n+4)² τ.im) ≤ (16 + 8n)(-π τ.im) ⟺ (n+4)² ≥ 16 + 8n.
    have h_ineq : ((n : ℝ) + 4)^2 ≥ 16 + 8 * (n : ℝ) := by nlinarith [sq_nonneg ((n : ℝ))]
    have h_pi_tau_nn : 0 ≤ Real.pi * τ.im := mul_nonneg hπ_pos.le hτim_pos.le
    nlinarith
  -- Summability of bound.
  have h_bound_summable : Summable (fun n : ℕ => r^16 * (r^8)^n) :=
    (summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ r^8) hr8_lt_one).mul_left _
  have h_norm_summable : Summable (fun n : ℕ =>
      ‖Complex.exp (Real.pi * Complex.I * (((n + 3 : ℕ) : ℂ) + 1)^2 * τ)‖) :=
    h_bound_summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_term_norm
  have h_tsum_norm_le := norm_tsum_le_tsum_norm h_norm_summable
  have h_tsum_bound : (∑' n : ℕ,
      ‖Complex.exp (Real.pi * Complex.I * (((n + 3 : ℕ) : ℂ) + 1)^2 * τ)‖) ≤
      r^16 * (1 - r^8)⁻¹ := by
    refine (h_norm_summable.tsum_le_tsum h_term_norm h_bound_summable).trans ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr8_lt_one]
  have h_chain : ‖∑' n : ℕ,
      Complex.exp (Real.pi * Complex.I * (((n + 3 : ℕ) : ℂ) + 1)^2 * τ)‖ ≤
      r^16 * (1 - r^8)⁻¹ := h_tsum_norm_le.trans h_tsum_bound
  -- r^16 · (1 - r^8)⁻¹ ≤ 2 r^16.
  have hr16_pos : 0 < r^16 := by positivity
  have h_inv_bound : r^16 * (1 - r^8)⁻¹ ≤ 2 * r^16 := by
    have : r^16 * (1 - r^8)⁻¹ ≤ r^16 * 2 :=
      mul_le_mul_of_nonneg_left h_inv_le_2 hr16_pos.le
    linarith
  have hr16_eq : r^16 = Real.exp (-16 * Real.pi * τ.im) := by
    rw [hr_def, ← Real.exp_nat_mul]; congr 1; ring
  calc (2 : ℝ) * ‖∑' n : ℕ,
        Complex.exp (Real.pi * Complex.I * (((n + 3 : ℕ) : ℂ) + 1)^2 * τ)‖
      ≤ 2 * (r^16 * (1 - r^8)⁻¹) := by
        apply mul_le_mul_of_nonneg_left h_chain (by norm_num)
    _ ≤ 2 * (2 * r^16) := by
        apply mul_le_mul_of_nonneg_left h_inv_bound (by norm_num)
    _ = 4 * r^16 := by ring
    _ = 4 * Real.exp (-16 * Real.pi * τ.im) := by rw [hr16_eq]

/-- **Four-term bracket bound.** With `u = -2q + 5q² - 10q³` and
`t = v + 2q - 5q² + 10q³`: if `‖q‖ = rq < 1/16` and `‖t‖ ≤ 100·rq⁴` (`ht_bound`), the
bracket `4(1+u)³t + 6(1+u)²t² + 4(1+u)t³ + t⁴ + q-remainder` has norm at most `4406·rq⁴`. -/
theorem modularLambda_four_term_bracket_bound (v q : ℂ) (rq : ℝ)
    (hq_norm : ‖q‖ = rq) (hrq_pos : 0 < rq) (hrq_lt : rq < 1 / 16)
    (ht_bound : ‖v + 2 * q - 5 * q ^ 2 + 10 * q ^ 3‖ ≤ 100 * rq ^ 4) :
    ‖4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) +
      6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2 +
      4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3 +
      (v + 2*q - 5*q^2 + 10*q^3)^4 +
      646*q^4 - 1840*q^5 + 4420*q^6 - 8800*q^7 + 15025*q^8 -
        21000*q^9 + 23000*q^10 - 20000*q^11 + 10000*q^12‖ ≤ 4406 * rq^4 := by
  have hrq_nn : 0 ≤ rq := hrq_pos.le
  have hrq_le_one : rq ≤ 1 := by linarith
  have hrq4_nn : 0 ≤ rq^4 := by positivity
  have hq_pow_norm (k : ℕ) : ‖q^k‖ = rq^k := by rw [norm_pow, hq_norm]
  -- ‖1 + u‖ ≤ 2.
  have h_1pu_norm_le : ‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖ ≤ 2 := by
    have h_eq : (1 + (-2*q + 5*q^2 - 10*q^3) : ℂ) = ((1 - 2*q) + 5*q^2) - 10*q^3 := by ring
    rw [h_eq]
    have h_t1 := norm_sub_le ((1 - 2*q : ℂ) + 5*q^2) (10*q^3)
    have h_t2 := norm_add_le ((1 : ℂ) - 2*q) (5*q^2)
    have h_t3 := norm_sub_le ((1 : ℂ)) (2*q)
    have h_1_norm : ‖((1 : ℂ))‖ = 1 := norm_one
    have h_2q_norm : ‖((2 : ℂ) * q)‖ = 2 * rq := by
      rw [show ((2 * q : ℂ)) = (((2 : ℝ) : ℂ)) * q from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, hq_norm]; simp
    have h_5q2_norm : ‖((5 : ℂ) * q^2)‖ = 5 * rq^2 := by
      rw [show ((5 * q^2 : ℂ)) = (((5 : ℝ) : ℂ)) * q^2 from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, hq_pow_norm 2]; simp
    have h_10q3_norm : ‖((10 : ℂ) * q^3)‖ = 10 * rq^3 := by
      rw [show ((10 * q^3 : ℂ)) = (((10 : ℝ) : ℂ)) * q^3 from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, hq_pow_norm 3]; simp
    have h_2rq_le : 2 * rq ≤ 1/4 := by linarith
    have h_5rq2_le : 5 * rq^2 ≤ 1/4 := by
      have h_rq2 : rq^2 ≤ rq * (1/16) := by
        have h_eq : rq^2 = rq * rq := by ring
        rw [h_eq]; exact mul_le_mul_of_nonneg_left hrq_lt.le hrq_nn
      have h_rq2_le_256 : rq^2 ≤ 1/256 := by
        have : rq * (1/16 : ℝ) ≤ (1/16) * (1/16) :=
          mul_le_mul_of_nonneg_right hrq_lt.le (by norm_num)
        linarith
      linarith
    have h_10rq3_le : 10 * rq^3 ≤ 1/4 := by
      have h_rq3 : rq^3 ≤ (1/16)^3 := pow_le_pow_left₀ hrq_nn hrq_lt.le 3
      have : ((1/16 : ℝ))^3 = 1/4096 := by norm_num
      linarith [this, h_rq3]
    linarith [h_t1, h_t2, h_t3, h_1_norm, h_2q_norm, h_5q2_norm, h_10q3_norm]
  have h_1pu_sq_le : ‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)^2‖ ≤ 4 := by
    rw [norm_pow]
    have := pow_le_pow_left₀ (norm_nonneg _) h_1pu_norm_le 2
    linarith
  have h_1pu_cube_le : ‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)^3‖ ≤ 8 := by
    rw [norm_pow]
    have := pow_le_pow_left₀ (norm_nonneg _) h_1pu_norm_le 3
    linarith
  -- Bound term 1.
  have h_term1_le : ‖4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3)‖ ≤
      3200 * rq^4 := by
    have h_eq : (4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) : ℂ) =
        (((4 : ℝ) : ℂ)) * ((1 + (-2*q + 5*q^2 - 10*q^3))^3 *
          (v + 2*q - 5*q^2 + 10*q^3)) := by push_cast; ring
    rw [h_eq, norm_mul]
    have h_4 : ‖(((4 : ℝ) : ℂ))‖ = 4 := by simp
    rw [h_4, norm_mul, norm_pow]
    have h_prod : ‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖^3 * ‖v + 2*q - 5*q^2 + 10*q^3‖ ≤
        8 * (100 * rq^4) := by
      have h := pow_le_pow_left₀ (norm_nonneg _) h_1pu_norm_le 3
      have h3 : ‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖^3 ≤ 8 := by
        have h_8 : (2:ℝ)^3 = 8 := by norm_num
        linarith
      exact mul_le_mul h3 ht_bound (norm_nonneg _) (by norm_num)
    calc 4 * (‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖^3 * ‖v + 2*q - 5*q^2 + 10*q^3‖)
        ≤ 4 * (8 * (100 * rq^4)) := mul_le_mul_of_nonneg_left h_prod (by norm_num)
      _ = 3200 * rq^4 := by ring
  -- Bound term 2.
  have h_rq4_small : rq^4 ≤ 1/65536 := by
    have h_rq4_le : rq^4 ≤ (1/16:ℝ)^4 := pow_le_pow_left₀ hrq_nn hrq_lt.le 4
    have : ((1/16 : ℝ))^4 = 1/65536 := by norm_num
    linarith
  have h_term2_le : ‖6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2‖ ≤
      4 * rq^4 := by
    have h_eq : (6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2 : ℂ) =
        (((6 : ℝ) : ℂ)) * ((1 + (-2*q + 5*q^2 - 10*q^3))^2 *
          (v + 2*q - 5*q^2 + 10*q^3)^2) := by push_cast; ring
    rw [h_eq, norm_mul]
    have h_6 : ‖(((6 : ℝ) : ℂ))‖ = 6 := by simp
    rw [h_6, norm_mul, norm_pow, norm_pow]
    have h_t_sq : ‖v + 2*q - 5*q^2 + 10*q^3‖^2 ≤ (100 * rq^4)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) ht_bound 2
    have h_1pu_sq : ‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖^2 ≤ 4 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) h_1pu_norm_le 2
      have : (2:ℝ)^2 = 4 := by norm_num
      linarith
    have h_prod : ‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖^2 * ‖v + 2*q - 5*q^2 + 10*q^3‖^2 ≤
        4 * (100 * rq^4)^2 :=
      mul_le_mul h_1pu_sq h_t_sq (by positivity) (by norm_num)
    have h_rq8_le : rq^8 ≤ rq^4 * (1/65536) := by
      have h_eq : rq^8 = rq^4 * rq^4 := by ring
      rw [h_eq]; exact mul_le_mul_of_nonneg_left h_rq4_small hrq4_nn
    calc 6 * (‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖^2 * ‖v + 2*q - 5*q^2 + 10*q^3‖^2)
        ≤ 6 * (4 * (100 * rq^4)^2) := mul_le_mul_of_nonneg_left h_prod (by norm_num)
      _ = 240000 * rq^8 := by ring
      _ ≤ 240000 * (rq^4 * (1/65536)) := mul_le_mul_of_nonneg_left h_rq8_le (by norm_num)
      _ = (240000 / 65536) * rq^4 := by ring
      _ ≤ 4 * rq^4 := by
          have h_ratio : (240000 / 65536 : ℝ) ≤ 4 := by norm_num
          exact mul_le_mul_of_nonneg_right h_ratio hrq4_nn
  -- Bound term 3.
  have h_rq8_small : rq^8 ≤ 1/4294967296 := by
    have h_rq8_le : rq^8 ≤ (1/16:ℝ)^8 := pow_le_pow_left₀ hrq_nn hrq_lt.le 8
    have : ((1/16 : ℝ))^8 = 1/4294967296 := by norm_num
    linarith
  have h_term3_le : ‖4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3‖ ≤
      rq^4 := by
    have h_eq : (4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3 : ℂ) =
        (((4 : ℝ) : ℂ)) * ((1 + (-2*q + 5*q^2 - 10*q^3)) *
          (v + 2*q - 5*q^2 + 10*q^3)^3) := by push_cast; ring
    rw [h_eq, norm_mul]
    have h_4 : ‖(((4 : ℝ) : ℂ))‖ = 4 := by simp
    rw [h_4, norm_mul, norm_pow]
    have h_t_cube : ‖v + 2*q - 5*q^2 + 10*q^3‖^3 ≤ (100 * rq^4)^3 :=
      pow_le_pow_left₀ (norm_nonneg _) ht_bound 3
    have h_prod : ‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖ * ‖v + 2*q - 5*q^2 + 10*q^3‖^3 ≤
        2 * (100 * rq^4)^3 :=
      mul_le_mul h_1pu_norm_le h_t_cube (by positivity) (by norm_num)
    have h_rq12_le : rq^12 ≤ rq^4 * (1/4294967296) := by
      have h_eq : rq^12 = rq^4 * rq^8 := by ring
      rw [h_eq]; exact mul_le_mul_of_nonneg_left h_rq8_small hrq4_nn
    calc 4 * (‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖ * ‖v + 2*q - 5*q^2 + 10*q^3‖^3)
        ≤ 4 * (2 * (100 * rq^4)^3) := mul_le_mul_of_nonneg_left h_prod (by norm_num)
      _ = 8000000 * rq^12 := by ring
      _ ≤ 8000000 * (rq^4 * (1/4294967296)) :=
            mul_le_mul_of_nonneg_left h_rq12_le (by norm_num)
      _ = (8000000 / 4294967296) * rq^4 := by ring
      _ ≤ rq^4 := by
          have : (8000000 / 4294967296 : ℝ) ≤ 1 := by norm_num
          calc (8000000 / 4294967296) * rq^4 ≤ 1 * rq^4 :=
                mul_le_mul_of_nonneg_right this hrq4_nn
            _ = rq^4 := one_mul _
  -- Bound term 4.
  have h_term4_le : ‖(v + 2*q - 5*q^2 + 10*q^3)^4‖ ≤ rq^4 := by
    rw [norm_pow]
    have h_t_4 : ‖v + 2*q - 5*q^2 + 10*q^3‖^4 ≤ (100 * rq^4)^4 :=
      pow_le_pow_left₀ (norm_nonneg _) ht_bound 4
    have h_rq12_small : rq^12 ≤ 1/281474976710656 := by
      have h_rq12_le : rq^12 ≤ (1/16:ℝ)^12 := pow_le_pow_left₀ hrq_nn hrq_lt.le 12
      have : ((1/16 : ℝ))^12 = 1/281474976710656 := by norm_num
      linarith
    have h_rq16_le : rq^16 ≤ rq^4 * (1/281474976710656) := by
      have h_eq : rq^16 = rq^4 * rq^12 := by ring
      rw [h_eq]; exact mul_le_mul_of_nonneg_left h_rq12_small hrq4_nn
    calc ‖v + 2*q - 5*q^2 + 10*q^3‖^4
        ≤ (100 * rq^4)^4 := h_t_4
      _ = 100000000 * rq^16 := by ring
      _ ≤ 100000000 * (rq^4 * (1/281474976710656)) :=
            mul_le_mul_of_nonneg_left h_rq16_le (by norm_num)
      _ = (100000000 / 281474976710656) * rq^4 := by ring
      _ ≤ rq^4 := by
          have : (100000000 / 281474976710656 : ℝ) ≤ 1 := by norm_num
          calc (100000000 / 281474976710656) * rq^4 ≤ 1 * rq^4 :=
                mul_le_mul_of_nonneg_right this hrq4_nn
            _ = rq^4 := one_mul _
  -- q-remainder bound.
  have h_const_norm (n : ℕ) (k : ℕ) :
      ‖((n : ℂ) * q^k)‖ = n * rq^k := by
    rw [show ((n : ℂ) * q^k) = (((n : ℝ) : ℂ)) * q^k from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, norm_pow, hq_norm]; simp
  have h_646q4_norm : ‖((646 : ℂ) * q^4)‖ = 646 * rq^4 := h_const_norm 646 4
  have h_1840q5_norm : ‖((1840 : ℂ) * q^5)‖ = 1840 * rq^5 := h_const_norm 1840 5
  have h_4420q6_norm : ‖((4420 : ℂ) * q^6)‖ = 4420 * rq^6 := h_const_norm 4420 6
  have h_8800q7_norm : ‖((8800 : ℂ) * q^7)‖ = 8800 * rq^7 := h_const_norm 8800 7
  have h_15025q8_norm : ‖((15025 : ℂ) * q^8)‖ = 15025 * rq^8 := h_const_norm 15025 8
  have h_21000q9_norm : ‖((21000 : ℂ) * q^9)‖ = 21000 * rq^9 := h_const_norm 21000 9
  have h_23000q10_norm : ‖((23000 : ℂ) * q^10)‖ = 23000 * rq^10 := h_const_norm 23000 10
  have h_20000q11_norm : ‖((20000 : ℂ) * q^11)‖ = 20000 * rq^11 := h_const_norm 20000 11
  have h_10000q12_norm : ‖((10000 : ℂ) * q^12)‖ = 10000 * rq^12 := h_const_norm 10000 12
  have h_rq5_to_rq4 : rq^5 ≤ rq^4 / 16 := by
    have h_eq : rq^5 = rq^4 * rq := by ring
    rw [h_eq]
    calc rq^4 * rq ≤ rq^4 * (1/16) := mul_le_mul_of_nonneg_left hrq_lt.le hrq4_nn
      _ = rq^4 / 16 := by ring
  have h_rq6_to_rq4 : rq^6 ≤ rq^4 / 256 := by
    have h_eq : rq^6 = rq^4 * (rq * rq) := by ring
    rw [h_eq]
    have h_rq_rq_le : rq * rq ≤ (1/16) * (1/16) :=
      mul_le_mul hrq_lt.le hrq_lt.le hrq_nn (by norm_num)
    calc rq^4 * (rq * rq) ≤ rq^4 * ((1/16) * (1/16)) :=
          mul_le_mul_of_nonneg_left h_rq_rq_le hrq4_nn
      _ = rq^4 / 256 := by ring
  have h_rq_high : ∀ k : ℕ, k ≥ 6 → rq^k ≤ rq^4 / 256 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact h_rq6_to_rq4
    | succ n hn ih =>
      have h_pow_nn : 0 ≤ rq^n := by positivity
      have h_eq : rq^(n+1) = rq^n * rq := by ring
      rw [h_eq]
      calc rq^n * rq ≤ rq^n * 1 := mul_le_mul_of_nonneg_left hrq_le_one h_pow_nn
        _ = rq^n := mul_one _
        _ ≤ rq^4 / 256 := ih
  have h_rq7_to_rq4 : rq^7 ≤ rq^4 / 256 := h_rq_high 7 (by omega)
  have h_rq8_to_rq4 : rq^8 ≤ rq^4 / 256 := h_rq_high 8 (by omega)
  have h_rq9_to_rq4 : rq^9 ≤ rq^4 / 256 := h_rq_high 9 (by omega)
  have h_rq10_to_rq4 : rq^10 ≤ rq^4 / 256 := h_rq_high 10 (by omega)
  have h_rq11_to_rq4 : rq^11 ≤ rq^4 / 256 := h_rq_high 11 (by omega)
  have h_rq12_to_rq4 : rq^12 ≤ rq^4 / 256 := h_rq_high 12 (by omega)
  have h_qrem : ‖(646*q^4 - 1840*q^5 + 4420*q^6 - 8800*q^7 + 15025*q^8 -
      21000*q^9 + 23000*q^10 - 20000*q^11 + 10000*q^12 : ℂ)‖ ≤ 1200 * rq^4 := by
    have h_eq : (646*q^4 - 1840*q^5 + 4420*q^6 - 8800*q^7 + 15025*q^8 -
        21000*q^9 + 23000*q^10 - 20000*q^11 + 10000*q^12 : ℂ) =
        (((((((646*q^4 - 1840*q^5) + 4420*q^6) - 8800*q^7) + 15025*q^8) - 21000*q^9) +
          23000*q^10) - 20000*q^11) + 10000*q^12 := by ring
    rw [h_eq]
    have h_t1 := norm_add_le
      (((((((646*q^4 - 1840*q^5) + 4420*q^6) - 8800*q^7) + 15025*q^8) - 21000*q^9) +
        23000*q^10) - 20000*q^11) (10000*q^12)
    have h_t2 := norm_sub_le
      ((((((646*q^4 - 1840*q^5) + 4420*q^6) - 8800*q^7) + 15025*q^8) - 21000*q^9) +
        23000*q^10) (20000*q^11)
    have h_t3 := norm_add_le
      (((((646*q^4 - 1840*q^5) + 4420*q^6) - 8800*q^7) + 15025*q^8) - 21000*q^9) (23000*q^10)
    have h_t4 := norm_sub_le
      ((((646*q^4 - 1840*q^5) + 4420*q^6) - 8800*q^7) + 15025*q^8) (21000*q^9)
    have h_t5 := norm_add_le
      (((646*q^4 - 1840*q^5) + 4420*q^6) - 8800*q^7) (15025*q^8)
    have h_t6 := norm_sub_le ((646*q^4 - 1840*q^5) + 4420*q^6) (8800*q^7)
    have h_t7 := norm_add_le (646*q^4 - 1840*q^5) (4420*q^6)
    have h_t8 := norm_sub_le (646*q^4) (1840*q^5)
    linarith [h_t1, h_t2, h_t3, h_t4, h_t5, h_t6, h_t7, h_t8,
              h_646q4_norm.le, h_1840q5_norm.le, h_4420q6_norm.le, h_8800q7_norm.le,
              h_15025q8_norm.le, h_21000q9_norm.le, h_23000q10_norm.le,
              h_20000q11_norm.le, h_10000q12_norm.le,
              h_rq5_to_rq4, h_rq6_to_rq4, h_rq7_to_rq4, h_rq8_to_rq4,
              h_rq9_to_rq4, h_rq10_to_rq4, h_rq11_to_rq4, h_rq12_to_rq4, hrq4_nn]
  -- Combine: 3200 + 4 + 1 + 1 + 1200 = 4406 rq⁴.
  have h_eq : (4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) +
      6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2 +
      4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3 +
      (v + 2*q - 5*q^2 + 10*q^3)^4 +
      646*q^4 - 1840*q^5 + 4420*q^6 - 8800*q^7 + 15025*q^8 - 21000*q^9 + 23000*q^10 -
        20000*q^11 + 10000*q^12 : ℂ) =
      ((((4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) +
        6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2) +
        4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3) +
        (v + 2*q - 5*q^2 + 10*q^3)^4) +
        (646*q^4 - 1840*q^5 + 4420*q^6 - 8800*q^7 + 15025*q^8 - 21000*q^9 + 23000*q^10 -
          20000*q^11 + 10000*q^12)) := by ring
  rw [h_eq]
  have h_a1 := norm_add_le
    ((((4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) +
      6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2) +
      4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3) +
      (v + 2*q - 5*q^2 + 10*q^3)^4))
    ((646*q^4 - 1840*q^5 + 4420*q^6 - 8800*q^7 + 15025*q^8 - 21000*q^9 + 23000*q^10 -
      20000*q^11 + 10000*q^12 : ℂ))
  have h_a2 := norm_add_le
    (((4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) +
      6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2) +
      4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3))
    ((v + 2*q - 5*q^2 + 10*q^3)^4)
  have h_a3 := norm_add_le
    ((4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) +
      6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2))
    (4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3)
  have h_a4 := norm_add_le
    (4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3))
    (6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2)
  linarith [h_a1, h_a2, h_a3, h_a4, h_term1_le, h_term2_le, h_term3_le, h_term4_le, h_qrem]

/-- **Tightened four-term bracket bound.** Same hypotheses as
`modularLambda_four_term_bracket_bound`, but uses the sharper
`‖1 + (−2q + 5q² − 10q³)‖ ≤ 5/4` (provable from `rq < 1/16`) to give the
tighter total `2100·rq^4`. Required for the widened `λ` bound
`modularLambdaH_norm_sub_four_term_le_of_im_ge_nine_tenths`: the
constant `35000 = 16 · K` forces `K ≤ 2187.5`, so the looser `4406`
of the standard bracket bound does not suffice. -/
theorem modularLambda_four_term_bracket_bound_widened (v q : ℂ) (rq : ℝ)
    (hq_norm : ‖q‖ = rq) (hrq_pos : 0 < rq) (hrq_lt : rq < 1 / 16)
    (ht_bound : ‖v + 2 * q - 5 * q ^ 2 + 10 * q ^ 3‖ ≤ 100 * rq ^ 4) :
    ‖4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) +
      6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2 +
      4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3 +
      (v + 2*q - 5*q^2 + 10*q^3)^4 +
      646*q^4 - 1840*q^5 + 4420*q^6 - 8800*q^7 + 15025*q^8 -
        21000*q^9 + 23000*q^10 - 20000*q^11 + 10000*q^12‖ ≤ 2100 * rq^4 := by
  have hrq_nn : 0 ≤ rq := hrq_pos.le
  have hrq_le_one : rq ≤ 1 := by linarith
  have hrq4_nn : 0 ≤ rq^4 := by positivity
  have hq_pow_norm (k : ℕ) : ‖q^k‖ = rq^k := by rw [norm_pow, hq_norm]
  -- Sharper inner bound: ‖1 + u‖ ≤ 5/4.
  have h_1pu_norm_le : ‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖ ≤ 5/4 := by
    have h_eq : (1 + (-2*q + 5*q^2 - 10*q^3) : ℂ) = ((1 - 2*q) + 5*q^2) - 10*q^3 := by ring
    rw [h_eq]
    have h_t1 := norm_sub_le ((1 - 2*q : ℂ) + 5*q^2) (10*q^3)
    have h_t2 := norm_add_le ((1 : ℂ) - 2*q) (5*q^2)
    have h_t3 := norm_sub_le ((1 : ℂ)) (2*q)
    have h_1_norm : ‖((1 : ℂ))‖ = 1 := norm_one
    have h_2q_norm : ‖((2 : ℂ) * q)‖ = 2 * rq := by
      rw [show ((2 * q : ℂ)) = (((2 : ℝ) : ℂ)) * q from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, hq_norm]; simp
    have h_5q2_norm : ‖((5 : ℂ) * q^2)‖ = 5 * rq^2 := by
      rw [show ((5 * q^2 : ℂ)) = (((5 : ℝ) : ℂ)) * q^2 from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, hq_pow_norm 2]; simp
    have h_10q3_norm : ‖((10 : ℂ) * q^3)‖ = 10 * rq^3 := by
      rw [show ((10 * q^3 : ℂ)) = (((10 : ℝ) : ℂ)) * q^3 from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, hq_pow_norm 3]; simp
    have h_2rq_le : 2 * rq ≤ 1/8 := by linarith
    have h_rq2_le : rq^2 ≤ 1/256 := by
      have h_rq2 : rq^2 ≤ (1/16:ℝ)^2 := pow_le_pow_left₀ hrq_nn hrq_lt.le 2
      have : ((1/16:ℝ))^2 = 1/256 := by norm_num
      linarith
    have h_5rq2_le : 5 * rq^2 ≤ 5/256 := by linarith
    have h_rq3_le : rq^3 ≤ 1/4096 := by
      have h_rq3 : rq^3 ≤ (1/16:ℝ)^3 := pow_le_pow_left₀ hrq_nn hrq_lt.le 3
      have : ((1/16 : ℝ))^3 = 1/4096 := by norm_num
      linarith
    have h_10rq3_le : 10 * rq^3 ≤ 10/4096 := by linarith
    linarith [h_t1, h_t2, h_t3, h_1_norm, h_2q_norm, h_5q2_norm, h_10q3_norm]
  -- ‖1+u‖^2 ≤ (5/4)^2 = 25/16.
  have h_1pu_sq_le : ‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖^2 ≤ 25/16 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) h_1pu_norm_le 2
    have h_eq : ((5/4:ℝ))^2 = 25/16 := by norm_num
    linarith
  -- ‖1+u‖^3 ≤ (5/4)^3 = 125/64.
  have h_1pu_cube_le : ‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖^3 ≤ 125/64 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) h_1pu_norm_le 3
    have h_eq : ((5/4:ℝ))^3 = 125/64 := by norm_num
    linarith
  -- Term 1: ‖4(1+u)^3 t‖ ≤ 4 · 125/64 · 100 · rq^4 = 781.25 rq^4 ≤ 800 rq^4.
  have h_term1_le : ‖4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3)‖ ≤
      800 * rq^4 := by
    have h_eq : (4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) : ℂ) =
        (((4 : ℝ) : ℂ)) * ((1 + (-2*q + 5*q^2 - 10*q^3))^3 *
          (v + 2*q - 5*q^2 + 10*q^3)) := by push_cast; ring
    rw [h_eq, norm_mul]
    have h_4 : ‖(((4 : ℝ) : ℂ))‖ = 4 := by simp
    rw [h_4, norm_mul, norm_pow]
    have h_prod : ‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖^3 * ‖v + 2*q - 5*q^2 + 10*q^3‖ ≤
        (125/64) * (100 * rq^4) :=
      mul_le_mul h_1pu_cube_le ht_bound (norm_nonneg _) (by norm_num)
    calc 4 * (‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖^3 * ‖v + 2*q - 5*q^2 + 10*q^3‖)
        ≤ 4 * ((125/64) * (100 * rq^4)) :=
          mul_le_mul_of_nonneg_left h_prod (by norm_num)
      _ ≤ 800 * rq^4 := by nlinarith
  -- Term 2: ‖6(1+u)^2 t²‖ ≤ 6 · 25/16 · 10000 · rq^8 ≤ 2 rq^4.
  have h_rq4_small : rq^4 ≤ 1/65536 := by
    have h_rq4_le : rq^4 ≤ (1/16:ℝ)^4 := pow_le_pow_left₀ hrq_nn hrq_lt.le 4
    have : ((1/16 : ℝ))^4 = 1/65536 := by norm_num
    linarith
  have h_term2_le : ‖6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2‖ ≤
      2 * rq^4 := by
    have h_eq : (6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2 : ℂ) =
        (((6 : ℝ) : ℂ)) * ((1 + (-2*q + 5*q^2 - 10*q^3))^2 *
          (v + 2*q - 5*q^2 + 10*q^3)^2) := by push_cast; ring
    rw [h_eq, norm_mul]
    have h_6 : ‖(((6 : ℝ) : ℂ))‖ = 6 := by simp
    rw [h_6, norm_mul, norm_pow, norm_pow]
    have h_t_sq : ‖v + 2*q - 5*q^2 + 10*q^3‖^2 ≤ (100 * rq^4)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) ht_bound 2
    have h_prod : ‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖^2 * ‖v + 2*q - 5*q^2 + 10*q^3‖^2 ≤
        (25/16) * (100 * rq^4)^2 :=
      mul_le_mul h_1pu_sq_le h_t_sq (by positivity) (by norm_num)
    have h_rq8_le : rq^8 ≤ rq^4 * (1/65536) := by
      have h_eq : rq^8 = rq^4 * rq^4 := by ring
      rw [h_eq]; exact mul_le_mul_of_nonneg_left h_rq4_small hrq4_nn
    calc 6 * (‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖^2 * ‖v + 2*q - 5*q^2 + 10*q^3‖^2)
        ≤ 6 * ((25/16) * (100 * rq^4)^2) :=
          mul_le_mul_of_nonneg_left h_prod (by norm_num)
      _ = 93750 * rq^8 := by ring
      _ ≤ 93750 * (rq^4 * (1/65536)) := mul_le_mul_of_nonneg_left h_rq8_le (by norm_num)
      _ = (93750 / 65536) * rq^4 := by ring
      _ ≤ 2 * rq^4 := by
          have h_ratio : (93750 / 65536 : ℝ) ≤ 2 := by norm_num
          exact mul_le_mul_of_nonneg_right h_ratio hrq4_nn
  -- Term 3: same as standard, ≤ rq^4. Use ‖1+u‖ ≤ 5/4 (looser is also OK).
  have h_rq8_small : rq^8 ≤ 1/4294967296 := by
    have h_rq8_le : rq^8 ≤ (1/16:ℝ)^8 := pow_le_pow_left₀ hrq_nn hrq_lt.le 8
    have : ((1/16 : ℝ))^8 = 1/4294967296 := by norm_num
    linarith
  have h_term3_le : ‖4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3‖ ≤
      rq^4 := by
    have h_eq : (4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3 : ℂ) =
        (((4 : ℝ) : ℂ)) * ((1 + (-2*q + 5*q^2 - 10*q^3)) *
          (v + 2*q - 5*q^2 + 10*q^3)^3) := by push_cast; ring
    rw [h_eq, norm_mul]
    have h_4 : ‖(((4 : ℝ) : ℂ))‖ = 4 := by simp
    rw [h_4, norm_mul, norm_pow]
    have h_t_cube : ‖v + 2*q - 5*q^2 + 10*q^3‖^3 ≤ (100 * rq^4)^3 :=
      pow_le_pow_left₀ (norm_nonneg _) ht_bound 3
    have h_prod : ‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖ * ‖v + 2*q - 5*q^2 + 10*q^3‖^3 ≤
        (5/4) * (100 * rq^4)^3 :=
      mul_le_mul h_1pu_norm_le h_t_cube (by positivity) (by norm_num)
    have h_rq12_le : rq^12 ≤ rq^4 * (1/4294967296) := by
      have h_eq : rq^12 = rq^4 * rq^8 := by ring
      rw [h_eq]; exact mul_le_mul_of_nonneg_left h_rq8_small hrq4_nn
    calc 4 * (‖(1 + (-2*q + 5*q^2 - 10*q^3) : ℂ)‖ * ‖v + 2*q - 5*q^2 + 10*q^3‖^3)
        ≤ 4 * ((5/4) * (100 * rq^4)^3) :=
          mul_le_mul_of_nonneg_left h_prod (by norm_num)
      _ = 5000000 * rq^12 := by ring
      _ ≤ 5000000 * (rq^4 * (1/4294967296)) :=
            mul_le_mul_of_nonneg_left h_rq12_le (by norm_num)
      _ = (5000000 / 4294967296) * rq^4 := by ring
      _ ≤ rq^4 := by
          have : (5000000 / 4294967296 : ℝ) ≤ 1 := by norm_num
          calc (5000000 / 4294967296) * rq^4 ≤ 1 * rq^4 :=
                mul_le_mul_of_nonneg_right this hrq4_nn
            _ = rq^4 := one_mul _
  -- Term 4: same as standard, ≤ rq^4.
  have h_term4_le : ‖(v + 2*q - 5*q^2 + 10*q^3)^4‖ ≤ rq^4 := by
    rw [norm_pow]
    have h_t_4 : ‖v + 2*q - 5*q^2 + 10*q^3‖^4 ≤ (100 * rq^4)^4 :=
      pow_le_pow_left₀ (norm_nonneg _) ht_bound 4
    have h_rq12_small : rq^12 ≤ 1/281474976710656 := by
      have h_rq12_le : rq^12 ≤ (1/16:ℝ)^12 := pow_le_pow_left₀ hrq_nn hrq_lt.le 12
      have : ((1/16 : ℝ))^12 = 1/281474976710656 := by norm_num
      linarith
    have h_rq16_le : rq^16 ≤ rq^4 * (1/281474976710656) := by
      have h_eq : rq^16 = rq^4 * rq^12 := by ring
      rw [h_eq]; exact mul_le_mul_of_nonneg_left h_rq12_small hrq4_nn
    calc ‖v + 2*q - 5*q^2 + 10*q^3‖^4
        ≤ (100 * rq^4)^4 := h_t_4
      _ = 100000000 * rq^16 := by ring
      _ ≤ 100000000 * (rq^4 * (1/281474976710656)) :=
            mul_le_mul_of_nonneg_left h_rq16_le (by norm_num)
      _ = (100000000 / 281474976710656) * rq^4 := by ring
      _ ≤ rq^4 := by
          have : (100000000 / 281474976710656 : ℝ) ≤ 1 := by norm_num
          calc (100000000 / 281474976710656) * rq^4 ≤ 1 * rq^4 :=
                mul_le_mul_of_nonneg_right this hrq4_nn
            _ = rq^4 := one_mul _
  -- q-remainder bound (same as standard ≤ 1200 rq^4).
  have h_const_norm (n : ℕ) (k : ℕ) :
      ‖((n : ℂ) * q^k)‖ = n * rq^k := by
    rw [show ((n : ℂ) * q^k) = (((n : ℝ) : ℂ)) * q^k from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, norm_pow, hq_norm]; simp
  have h_646q4_norm : ‖((646 : ℂ) * q^4)‖ = 646 * rq^4 := h_const_norm 646 4
  have h_1840q5_norm : ‖((1840 : ℂ) * q^5)‖ = 1840 * rq^5 := h_const_norm 1840 5
  have h_4420q6_norm : ‖((4420 : ℂ) * q^6)‖ = 4420 * rq^6 := h_const_norm 4420 6
  have h_8800q7_norm : ‖((8800 : ℂ) * q^7)‖ = 8800 * rq^7 := h_const_norm 8800 7
  have h_15025q8_norm : ‖((15025 : ℂ) * q^8)‖ = 15025 * rq^8 := h_const_norm 15025 8
  have h_21000q9_norm : ‖((21000 : ℂ) * q^9)‖ = 21000 * rq^9 := h_const_norm 21000 9
  have h_23000q10_norm : ‖((23000 : ℂ) * q^10)‖ = 23000 * rq^10 := h_const_norm 23000 10
  have h_20000q11_norm : ‖((20000 : ℂ) * q^11)‖ = 20000 * rq^11 := h_const_norm 20000 11
  have h_10000q12_norm : ‖((10000 : ℂ) * q^12)‖ = 10000 * rq^12 := h_const_norm 10000 12
  have h_rq5_to_rq4 : rq^5 ≤ rq^4 / 16 := by
    have h_eq : rq^5 = rq^4 * rq := by ring
    rw [h_eq]
    calc rq^4 * rq ≤ rq^4 * (1/16) := mul_le_mul_of_nonneg_left hrq_lt.le hrq4_nn
      _ = rq^4 / 16 := by ring
  have h_rq6_to_rq4 : rq^6 ≤ rq^4 / 256 := by
    have h_eq : rq^6 = rq^4 * (rq * rq) := by ring
    rw [h_eq]
    have h_rq_rq_le : rq * rq ≤ (1/16) * (1/16) :=
      mul_le_mul hrq_lt.le hrq_lt.le hrq_nn (by norm_num)
    calc rq^4 * (rq * rq) ≤ rq^4 * ((1/16) * (1/16)) :=
          mul_le_mul_of_nonneg_left h_rq_rq_le hrq4_nn
      _ = rq^4 / 256 := by ring
  have h_rq_high : ∀ k : ℕ, k ≥ 6 → rq^k ≤ rq^4 / 256 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact h_rq6_to_rq4
    | succ n hn ih =>
      have h_pow_nn : 0 ≤ rq^n := by positivity
      have h_eq : rq^(n+1) = rq^n * rq := by ring
      rw [h_eq]
      calc rq^n * rq ≤ rq^n * 1 := mul_le_mul_of_nonneg_left hrq_le_one h_pow_nn
        _ = rq^n := mul_one _
        _ ≤ rq^4 / 256 := ih
  have h_rq7_to_rq4 : rq^7 ≤ rq^4 / 256 := h_rq_high 7 (by omega)
  have h_rq8_to_rq4 : rq^8 ≤ rq^4 / 256 := h_rq_high 8 (by omega)
  have h_rq9_to_rq4 : rq^9 ≤ rq^4 / 256 := h_rq_high 9 (by omega)
  have h_rq10_to_rq4 : rq^10 ≤ rq^4 / 256 := h_rq_high 10 (by omega)
  have h_rq11_to_rq4 : rq^11 ≤ rq^4 / 256 := h_rq_high 11 (by omega)
  have h_rq12_to_rq4 : rq^12 ≤ rq^4 / 256 := h_rq_high 12 (by omega)
  have h_qrem : ‖(646*q^4 - 1840*q^5 + 4420*q^6 - 8800*q^7 + 15025*q^8 -
      21000*q^9 + 23000*q^10 - 20000*q^11 + 10000*q^12 : ℂ)‖ ≤ 1200 * rq^4 := by
    have h_eq : (646*q^4 - 1840*q^5 + 4420*q^6 - 8800*q^7 + 15025*q^8 -
        21000*q^9 + 23000*q^10 - 20000*q^11 + 10000*q^12 : ℂ) =
        (((((((646*q^4 - 1840*q^5) + 4420*q^6) - 8800*q^7) + 15025*q^8) - 21000*q^9) +
          23000*q^10) - 20000*q^11) + 10000*q^12 := by ring
    rw [h_eq]
    have h_t1 := norm_add_le
      (((((((646*q^4 - 1840*q^5) + 4420*q^6) - 8800*q^7) + 15025*q^8) - 21000*q^9) +
        23000*q^10) - 20000*q^11) (10000*q^12)
    have h_t2 := norm_sub_le
      ((((((646*q^4 - 1840*q^5) + 4420*q^6) - 8800*q^7) + 15025*q^8) - 21000*q^9) +
        23000*q^10) (20000*q^11)
    have h_t3 := norm_add_le
      (((((646*q^4 - 1840*q^5) + 4420*q^6) - 8800*q^7) + 15025*q^8) - 21000*q^9) (23000*q^10)
    have h_t4 := norm_sub_le
      ((((646*q^4 - 1840*q^5) + 4420*q^6) - 8800*q^7) + 15025*q^8) (21000*q^9)
    have h_t5 := norm_add_le
      (((646*q^4 - 1840*q^5) + 4420*q^6) - 8800*q^7) (15025*q^8)
    have h_t6 := norm_sub_le ((646*q^4 - 1840*q^5) + 4420*q^6) (8800*q^7)
    have h_t7 := norm_add_le (646*q^4 - 1840*q^5) (4420*q^6)
    have h_t8 := norm_sub_le (646*q^4) (1840*q^5)
    linarith [h_t1, h_t2, h_t3, h_t4, h_t5, h_t6, h_t7, h_t8,
              h_646q4_norm.le, h_1840q5_norm.le, h_4420q6_norm.le, h_8800q7_norm.le,
              h_15025q8_norm.le, h_21000q9_norm.le, h_23000q10_norm.le,
              h_20000q11_norm.le, h_10000q12_norm.le,
              h_rq5_to_rq4, h_rq6_to_rq4, h_rq7_to_rq4, h_rq8_to_rq4,
              h_rq9_to_rq4, h_rq10_to_rq4, h_rq11_to_rq4, h_rq12_to_rq4, hrq4_nn]
  -- Combine: 800 + 2 + 1 + 1 + 1200 = 2004 ≤ 2100 rq^4.
  have h_eq : (4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) +
      6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2 +
      4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3 +
      (v + 2*q - 5*q^2 + 10*q^3)^4 +
      646*q^4 - 1840*q^5 + 4420*q^6 - 8800*q^7 + 15025*q^8 - 21000*q^9 + 23000*q^10 -
        20000*q^11 + 10000*q^12 : ℂ) =
      ((((4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) +
        6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2) +
        4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3) +
        (v + 2*q - 5*q^2 + 10*q^3)^4) +
        (646*q^4 - 1840*q^5 + 4420*q^6 - 8800*q^7 + 15025*q^8 - 21000*q^9 + 23000*q^10 -
          20000*q^11 + 10000*q^12)) := by ring
  rw [h_eq]
  have h_a1 := norm_add_le
    ((((4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) +
      6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2) +
      4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3) +
      (v + 2*q - 5*q^2 + 10*q^3)^4))
    ((646*q^4 - 1840*q^5 + 4420*q^6 - 8800*q^7 + 15025*q^8 - 21000*q^9 + 23000*q^10 -
      20000*q^11 + 10000*q^12 : ℂ))
  have h_a2 := norm_add_le
    (((4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) +
      6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2) +
      4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3))
    ((v + 2*q - 5*q^2 + 10*q^3)^4)
  have h_a3 := norm_add_le
    ((4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) +
      6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2))
    (4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3)
  have h_a4 := norm_add_le
    (4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3))
    (6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2)
  linarith [h_a1, h_a2, h_a3, h_a4, h_term1_le, h_term2_le, h_term3_le, h_term4_le, h_qrem]

end NoWanderingDomains
