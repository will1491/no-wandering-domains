/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.ModularFunction.FourTermBounds.Theta

/-!
# Four-term q-expansion bounds: the widened variants and the modular lambda

Widened four-term bounds on `τ.im ≥ 9/10` for `jacobiTheta₂ (τ/2) τ`, `θ₂`, `θ₃`, and
`λ` (`modularLambdaH_norm_sub_four_term_le_of_im_ge_nine_tenths`, with the tight
constant `35000`), which power the Cauchy estimate on the derivative of the cusp
function at the boundary `τ.im = 1`.

The Cauchy estimate behind `modularLambdaH_deriv_norm_sub_three_term_le_of_im_ge_one`
(in `Gamma2FundamentalDomain/CuspAsymptotics.lean`) needs the four-term bounds on a
disk of radius `R = exp(−9π/10)`, strictly larger than `‖q‖ ≤ exp(−π)` — that is, down
to `τ.im ≥ 9/10`. The threshold still satisfies `exp(−9π/10) < 1/16`, so each widened
theta bound replicates its `τ.im ≥ 1` counterpart with the geometric-series constants
recomputed at `r = exp(−π·9/10)`.
-/

namespace NoWanderingDomains
open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped ModularForm Manifold MatrixGroups

/-- **Widened jacobi-theta four-term bound.**
`‖jacobiTheta₂(τ/2, τ) − 2 − 2·exp(2πi τ) − 2·exp(6πi τ) − 2·exp(12πi τ)‖ ≤ 8·exp(−20π·τ.im)`
for `τ.im ≥ 9/10`. Same shape as
`jacobiTheta₂_half_sub_four_term_norm_le_of_im_ge_one`, with the
weaker hypothesis `9/10 ≤ τ.im` that admits `q = exp(πi τ)` up to
norm `exp(−9π/10) > exp(−π)`. Required for the widened four-term `λ`
bound that powers the Cauchy step at the boundary `τ.im = 1`. -/
theorem jacobiTheta₂_half_sub_four_term_norm_le_of_im_ge_nine_tenths
    {τ : ℂ} (hτ : (9 : ℝ) / 10 ≤ τ.im) :
    ‖jacobiTheta₂ (τ / 2) τ - 2 - 2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
        2 * Complex.exp (6 * Real.pi * Complex.I * τ) -
        2 * Complex.exp (12 * Real.pi * Complex.I * τ)‖ ≤
      8 * Real.exp (-20 * Real.pi * τ.im) := by
  have hπ_pos := Real.pi_pos
  have hτim_pos : 0 < τ.im := by nlinarith
  set r : ℝ := Real.exp (-2 * Real.pi * τ.im) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_nn : 0 ≤ r := hr_pos.le
  have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  -- r ≤ exp(-9π/5) < 1/2 (using exp(1) > 2 and 9π/5 ≥ 1).
  have h_9pi_5_ge_1 : (1 : ℝ) ≤ 9 * Real.pi / 5 := by
    have h_pi_gt_3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    linarith
  have h_exp_9pi5_gt_2 : (2 : ℝ) < Real.exp (9 * Real.pi / 5) := by
    have h_mono : Real.exp 1 ≤ Real.exp (9 * Real.pi / 5) := Real.exp_le_exp.mpr h_9pi_5_ge_1
    linarith
  have hr_lt : r < 1 / 2 := by
    have h_arg : -2 * Real.pi * τ.im ≤ -(9 * Real.pi / 5) := by nlinarith
    have h_le : r ≤ Real.exp (-(9 * Real.pi / 5)) := Real.exp_le_exp.mpr h_arg
    have h_exp_neg_lt : Real.exp (-(9 * Real.pi / 5)) < 1/2 := by
      rw [Real.exp_neg]
      rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ from by ring]
      exact inv_strictAnti₀ (by norm_num : (0:ℝ) < 2) h_exp_9pi5_gt_2
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
  have h_pair_hasSum : HasSum (fun n : ℕ =>
      jacobiTheta₂_term (n : ℤ) (τ/2) τ + jacobiTheta₂_term (-(n : ℤ)) (τ/2) τ)
      (jacobiTheta₂ (τ/2) τ + 1) := by
    have := h_hasSum_int.nat_add_neg
    rw [h_term_zero] at this
    exact this
  have h_pair_summable : Summable (fun n : ℕ =>
      jacobiTheta₂_term ((n : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-((n : ℕ) : ℤ)) (τ/2) τ) := h_pair_hasSum.summable
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

/-- **Widened `θ₂` four-term bound.** Combines the widened
jacobi-theta four-term bound with the factor `2·exp(πi τ/4)`. Same
shape as `theta2_norm_sub_four_term_le_of_im_ge_one` but with
hypothesis `9/10 ≤ τ.im`. -/
theorem theta2_norm_sub_four_term_le_of_im_ge_nine_tenths
    {τ : ℂ} (hτ : (9 : ℝ) / 10 ≤ τ.im) :
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
  have h_tail := jacobiTheta₂_half_sub_four_term_norm_le_of_im_ge_nine_tenths hτ
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

/-- **Widened `θ₃` four-term bound.** Same shape as
`theta3_sub_four_term_norm_le_of_im_ge_one` but with hypothesis
`9/10 ≤ τ.im`. The first four nonzero terms of `θ₃` are subtracted;
the tail starts at `2 q^{16}`, where `q = exp(πi τ)`. -/
theorem theta3_sub_four_term_norm_le_of_im_ge_nine_tenths
    {τ : ℂ} (hτ : (9 : ℝ) / 10 ≤ τ.im) :
    ‖theta3 τ - 1 - 2 * Complex.exp (Real.pi * Complex.I * τ) -
        2 * Complex.exp (4 * Real.pi * Complex.I * τ) -
        2 * Complex.exp (9 * Real.pi * Complex.I * τ)‖ ≤
      4 * Real.exp (-16 * Real.pi * τ.im) := by
  have hπ_pos := Real.pi_pos
  have hτim_pos : 0 < τ.im := by nlinarith
  set r : ℝ := Real.exp (-Real.pi * τ.im) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_nn : 0 ≤ r := hr_pos.le
  -- r ≤ exp(-9π/10) < 1/16 (using 9π/10 > 4·log 2 via π > 3.14 and log 2 < 0.6931471808).
  have hr_le_exp_neg : r ≤ Real.exp (-(9 * Real.pi / 10)) := by
    rw [hr_def]; apply Real.exp_le_exp.mpr; nlinarith
  have h_log2_lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h_pi_gt_d2 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h_9pi10_gt_4log2 : 4 * Real.log 2 < 9 * Real.pi / 10 := by nlinarith
  have h_log16_eq : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2^(4 : ℕ) from by norm_num, Real.log_pow]; push_cast; ring
  have h_9pi10_gt_log16 : Real.log 16 < 9 * Real.pi / 10 := by
    rw [h_log16_eq]; exact h_9pi10_gt_4log2
  have h_exp_9pi10_gt_16 : (16 : ℝ) < Real.exp (9 * Real.pi / 10) := by
    have h_eq : (16 : ℝ) = Real.exp (Real.log 16) := by
      rw [Real.exp_log (by norm_num : (0:ℝ) < 16)]
    rw [h_eq]; exact Real.exp_lt_exp.mpr h_9pi10_gt_log16
  have h_exp_neg_9pi10_lt : Real.exp (-(9 * Real.pi / 10)) < 1/16 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/16),
        show (1/16 : ℝ)⁻¹ = 16 from by norm_num]
    exact h_exp_9pi10_gt_16
  have hr_lt : r < 1/16 := lt_of_le_of_lt hr_le_exp_neg h_exp_neg_9pi10_lt
  have hr_lt_one : r < 1 := by linarith
  have hr8_lt_one : r^8 < 1 := by
    have h1 : r^8 < (1/16)^8 := pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    have h2 : ((1/16 : ℝ))^8 < 1 := by norm_num
    linarith
  have hr8_lt_half : r^8 < 1/2 := by
    have h1 : r^8 < (1/16)^8 := pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    have h2 : ((1/16 : ℝ))^8 ≤ 1/2 := by norm_num
    linarith
  have h_one_sub_r8_pos : 0 < 1 - r^8 := by linarith
  have h_inv_le_2 : (1 - r^8)⁻¹ ≤ 2 := by
    rw [show (2 : ℝ) = (1/2)⁻¹ from by norm_num]
    apply inv_anti₀ (by norm_num : (0:ℝ) < 1/2) (by linarith)
  have h_hasSum := hasSum_nat_jacobiTheta hτim_pos
  have h_summable := h_hasSum.summable
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
    have h_ineq : ((n : ℝ) + 4)^2 ≥ 16 + 8 * (n : ℝ) := by nlinarith [sq_nonneg ((n : ℝ))]
    have h_pi_tau_nn : 0 ≤ Real.pi * τ.im := mul_nonneg hπ_pos.le hτim_pos.le
    nlinarith
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

/-- **Widened four-term `λ` bound.**
`‖λ(τ) − 16 q + 128 q² − 704 q³ + 3072 q⁴‖ ≤ 35000·exp(−5π·τ.im)`
for `τ.im ≥ 9/10`, where `q = exp(πi τ)`. The constant `35000` is
tight where a direct bracket assembly would give `131072`; the tighter
constant is required for the Cauchy closure of
`modularLambdaH_deriv_norm_sub_three_term_le_of_im_ge_one`: combined
with the algebraic `12288·‖q‖³` correction, `C ≤ ~35 000` keeps
`π·(C·12.21·exp(−π) + 12288) ≤ 100000`. The proof invokes the widened
bracket helper `modularLambda_four_term_bracket_bound_widened`
(constant `2100` vs. `4406`), which sharpens the triangle bound to
`‖1 + (−2q + 5q² − 10q³)‖ ≤ 5/4` (instead of the loose `≤ 2` in the
`τ.im ≥ 1` helper) and splits across the four bracket terms. -/
theorem modularLambdaH_norm_sub_four_term_le_of_im_ge_nine_tenths
    {τ : ℂ} (hτ : (9 : ℝ) / 10 ≤ τ.im) :
    ‖modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ) +
        128 * Complex.exp (2 * Real.pi * Complex.I * τ) -
        704 * Complex.exp (3 * Real.pi * Complex.I * τ) +
        3072 * Complex.exp (4 * Real.pi * Complex.I * τ)‖ ≤
      35000 * Real.exp (-5 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := by nlinarith
  have hπ_pos := Real.pi_pos
  set q : ℂ := Complex.exp (Real.pi * Complex.I * τ) with hq_def
  set Q2 : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ) with hQ2_def
  set Q3 : ℂ := Complex.exp (3 * Real.pi * Complex.I * τ) with hQ3_def
  set Q4 : ℂ := Complex.exp (4 * Real.pi * Complex.I * τ) with hQ4_def
  set Q6 : ℂ := Complex.exp (6 * Real.pi * Complex.I * τ) with hQ6_def
  set Q9 : ℂ := Complex.exp (9 * Real.pi * Complex.I * τ) with hQ9_def
  set Q12 : ℂ := Complex.exp (12 * Real.pi * Complex.I * τ) with hQ12_def
  set rq : ℝ := Real.exp (-Real.pi * τ.im) with hrq_def
  have hrq_pos : 0 < rq := Real.exp_pos _
  have hrq_nn : 0 ≤ rq := hrq_pos.le
  have hq_norm : ‖q‖ = rq := by
    rw [hq_def, Complex.norm_exp, hrq_def]
    congr 1
    have h_eq : (Real.pi * Complex.I * τ : ℂ) = ((Real.pi : ℝ) : ℂ) * (Complex.I * τ) := by ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
  have hQ2_eq : Q2 = q^2 := by
    rw [hQ2_def, hq_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hQ3_eq : Q3 = q^3 := by
    rw [hQ3_def, hq_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hQ4_eq : Q4 = q^4 := by
    rw [hQ4_def, hq_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hQ6_eq : Q6 = q^6 := by
    rw [hQ6_def, hq_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hQ9_eq : Q9 = q^9 := by
    rw [hQ9_def, hq_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hQ12_eq : Q12 = q^12 := by
    rw [hQ12_def, hq_def, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  -- rq < 1/16 via exp(9π/10) > 16 (from log 16 < 9π/10).
  have hrq_le_exp_neg : rq ≤ Real.exp (-(9 * Real.pi / 10)) := by
    rw [hrq_def]; apply Real.exp_le_exp.mpr; nlinarith
  have h_log2_lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h_pi_gt_d2 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h_9pi10_gt_4log2 : 4 * Real.log 2 < 9 * Real.pi / 10 := by nlinarith
  have h_log16_eq : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2^(4 : ℕ) from by norm_num, Real.log_pow]; push_cast; ring
  have h_9pi10_gt_log16 : Real.log 16 < 9 * Real.pi / 10 := by
    rw [h_log16_eq]; exact h_9pi10_gt_4log2
  have h_exp_9pi10_gt_16 : (16 : ℝ) < Real.exp (9 * Real.pi / 10) := by
    have h_eq : (16 : ℝ) = Real.exp (Real.log 16) := by
      rw [Real.exp_log (by norm_num : (0:ℝ) < 16)]
    rw [h_eq]; exact Real.exp_lt_exp.mpr h_9pi10_gt_log16
  have h_exp_neg_9pi10_lt : Real.exp (-(9 * Real.pi / 10)) < 1/16 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/16),
        show (1/16 : ℝ)⁻¹ = 16 from by norm_num]
    exact h_exp_9pi10_gt_16
  have hrq_lt : rq < 1/16 := lt_of_le_of_lt hrq_le_exp_neg h_exp_neg_9pi10_lt
  have hrq_lt_one : rq < 1 := by linarith
  have hrq_le_one : rq ≤ 1 := hrq_lt_one.le
  have hrq3_pos : 0 < rq^3 := by positivity
  have hrq3_nn : 0 ≤ rq^3 := hrq3_pos.le
  have hrq4_pos : 0 < rq^4 := by positivity
  have hrq4_nn : 0 ≤ rq^4 := hrq4_pos.le
  have hrq5_pos : 0 < rq^5 := by positivity
  have hrq5_nn : 0 ≤ rq^5 := hrq5_pos.le
  have hrq5_eq : rq^5 = Real.exp (-5 * Real.pi * τ.im) := by
    rw [hrq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- A := 2 exp(πi τ/4); A⁴ = 16q.
  set A : ℂ := 2 * Complex.exp (Real.pi * Complex.I * τ / 4) with hA_def
  have hA_pow : A^4 = 16 * q := by
    rw [hA_def, hq_def, mul_pow]
    rw [show (Complex.exp (Real.pi * Complex.I * τ / 4))^4 =
        Complex.exp (4 * (Real.pi * Complex.I * τ / 4)) from by
      rw [← Complex.exp_nat_mul]; norm_cast]
    rw [show (4 : ℂ) * (Real.pi * Complex.I * τ / 4) = Real.pi * Complex.I * τ from by ring]
    norm_num
  have hA_norm : ‖A‖ = 2 * Real.exp (-(Real.pi * τ.im / 4)) := by
    rw [hA_def, norm_mul, Complex.norm_exp]
    have h_re : (Real.pi * Complex.I * τ / 4 : ℂ).re = -(Real.pi * τ.im / 4) := by
      have h_eq : (Real.pi * Complex.I * τ / 4 : ℂ) =
          ((Real.pi / 4 : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
      rw [h_eq, Complex.mul_re]
      simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im]
      ring
    rw [h_re]; simp
  have hA_pow_norm : ‖A^4‖ = 16 * rq := by
    rw [hA_pow, norm_mul, hq_norm]; simp
  have hA_norm_pos : 0 < ‖A‖ := by rw [hA_norm]; positivity
  have hA_ne : A ≠ 0 := norm_ne_zero_iff.mp hA_norm_pos.ne'
  -- r₂', r₃' bounds (widened).
  set r₂' : ℂ := (theta2 τ - A * (1 + Q2 + Q6 + Q12)) / A with hr2_def
  set r₃' : ℂ := theta3 τ - 1 - 2 * q - 2 * Q4 - 2 * Q9 with hr3_def
  have hr2_bound : ‖r₂'‖ ≤ 4 * rq^20 := by
    rw [hr2_def, norm_div, hA_norm]
    have h_denom_pos : 0 < 2 * Real.exp (-(Real.pi * τ.im / 4)) := by positivity
    rw [div_le_iff₀ h_denom_pos]
    have hrq20_eq : rq^20 = Real.exp (-(20 * Real.pi * τ.im)) := by
      rw [hrq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h_target_eq : 4 * rq^20 * (2 * Real.exp (-(Real.pi * τ.im / 4))) =
        8 * Real.exp (-(81 * Real.pi * τ.im / 4)) := by
      rw [hrq20_eq]
      rw [show (4 * Real.exp (-(20 * Real.pi * τ.im)) *
          (2 * Real.exp (-(Real.pi * τ.im / 4))) : ℝ) =
          8 * (Real.exp (-(20 * Real.pi * τ.im)) *
            Real.exp (-(Real.pi * τ.im / 4))) from by ring]
      rw [← Real.exp_add]
      exact congr_arg (fun x => 8 * Real.exp x) (by ring)
    rw [h_target_eq]
    have h_eq_A : A * (1 + Q2 + Q6 + Q12) =
        2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
          (1 + Complex.exp (2 * Real.pi * Complex.I * τ) +
            Complex.exp (6 * Real.pi * Complex.I * τ) +
            Complex.exp (12 * Real.pi * Complex.I * τ)) := by
      rw [hA_def, hQ2_def, hQ6_def, hQ12_def]
    rw [h_eq_A]
    exact theta2_norm_sub_four_term_le_of_im_ge_nine_tenths hτ
  have hr3_bound : ‖r₃'‖ ≤ 4 * rq^16 := by
    rw [hr3_def, hq_def, hQ4_def, hQ9_def]
    have hrq16_eq : rq^16 = Real.exp (-16 * Real.pi * τ.im) := by
      rw [hrq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hrq16_eq]
    exact theta3_sub_four_term_norm_le_of_im_ge_nine_tenths hτ
  -- Loose bounds.
  have hr2_loose : ‖r₂'‖ ≤ rq^4 := by
    refine hr2_bound.trans ?_
    have h_4rq16_le : (4 : ℝ) * rq^16 ≤ 1 := by
      have h1 : rq^16 ≤ (1/16 : ℝ)^16 := pow_le_pow_left₀ hrq_nn hrq_lt.le _
      have h2 : ((1/16:ℝ))^16 ≤ 1/4 := by norm_num
      linarith
    have h_eq : (4 : ℝ) * rq^20 = (4 * rq^16) * rq^4 := by ring
    rw [h_eq]
    calc (4 * rq^16) * rq^4 ≤ 1 * rq^4 :=
          mul_le_mul_of_nonneg_right h_4rq16_le hrq4_nn
      _ = rq^4 := one_mul _
  have hr3_loose : ‖r₃'‖ ≤ rq^4 := by
    refine hr3_bound.trans ?_
    have h_4rq12_le : (4 : ℝ) * rq^12 ≤ 1 := by
      have h1 : rq^12 ≤ (1/16 : ℝ)^12 := pow_le_pow_left₀ hrq_nn hrq_lt.le _
      have h2 : ((1/16:ℝ))^12 ≤ 1/4 := by norm_num
      linarith
    have h_eq : (4 : ℝ) * rq^16 = (4 * rq^12) * rq^4 := by ring
    rw [h_eq]
    calc (4 * rq^12) * rq^4 ≤ 1 * rq^4 :=
          mul_le_mul_of_nonneg_right h_4rq12_le hrq4_nn
      _ = rq^4 := one_mul _
  have h_th2_eq : theta2 τ = A * (1 + Q2 + Q6 + Q12 + r₂') := by
    rw [hr2_def]; field_simp; ring
  have h_th3_eq : theta3 τ = 1 + 2 * q + 2 * Q4 + 2 * Q9 + r₃' := by rw [hr3_def]; ring
  have hq_pow_norm (k : ℕ) : ‖q^k‖ = rq^k := by rw [norm_pow, hq_norm]
  have hD_sub1_norm_le : ‖(2*q + 2*Q4 + 2*Q9 + r₃' : ℂ)‖ ≤ 1/2 := by
    have h_2q_norm : ‖((2 : ℂ) * q)‖ = 2 * rq := by
      rw [show ((2 * q : ℂ)) = (((2 : ℝ) : ℂ)) * q from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, hq_norm]; simp
    have h_2Q4_norm : ‖((2 : ℂ) * Q4)‖ = 2 * rq^4 := by
      rw [show ((2 * Q4 : ℂ)) = (((2 : ℝ) : ℂ)) * Q4 from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, hQ4_eq, hq_pow_norm]; simp
    have h_2Q9_norm : ‖((2 : ℂ) * Q9)‖ = 2 * rq^9 := by
      rw [show ((2 * Q9 : ℂ)) = (((2 : ℝ) : ℂ)) * Q9 from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, hQ9_eq, hq_pow_norm]; simp
    have h_t1 := norm_add_le (2*q + 2*Q4 + 2*Q9) r₃'
    have h_t2 := norm_add_le (2*q + 2*Q4) (2*Q9)
    have h_t3 := norm_add_le (2*q) (2*Q4)
    have h_2rq_le : 2 * rq ≤ 1/8 := by linarith
    have h_rq4_le_rq16 : rq^4 ≤ 1/16 := by
      have h_rq3_le : rq^3 ≤ (1/16 : ℝ)^3 := pow_le_pow_left₀ hrq_nn hrq_lt.le _
      have h_eq : rq^4 = rq^3 * rq := by ring
      rw [h_eq]
      calc rq^3 * rq ≤ (1/16)^3 * rq := mul_le_mul_of_nonneg_right h_rq3_le hrq_nn
        _ ≤ (1/16)^3 * (1/16) := by
              apply mul_le_mul_of_nonneg_left hrq_lt.le
              positivity
        _ = (1/16:ℝ)^4 := by ring
        _ ≤ 1/16 := by norm_num
    have h_rq9_le_rq16 : rq^9 ≤ 1/16 := by
      have h_rq8_le : rq^8 ≤ (1/16 : ℝ)^8 := pow_le_pow_left₀ hrq_nn hrq_lt.le _
      have h_eq : rq^9 = rq^8 * rq := by ring
      rw [h_eq]
      calc rq^8 * rq ≤ (1/16)^8 * rq := mul_le_mul_of_nonneg_right h_rq8_le hrq_nn
        _ ≤ (1/16)^8 * (1/16) := by
              apply mul_le_mul_of_nonneg_left hrq_lt.le
              positivity
        _ ≤ 1/16 := by norm_num
    linarith [h_t1, h_t2, h_t3, h_2q_norm, h_2Q4_norm, h_2Q9_norm, hr3_loose,
              h_2rq_le, h_rq4_le_rq16, h_rq9_le_rq16, hrq4_nn]
  have hD_norm_ge : (1/2 : ℝ) ≤ ‖(1 + 2*q + 2*Q4 + 2*Q9 + r₃' : ℂ)‖ := by
    have h_eq : (1 + 2*q + 2*Q4 + 2*Q9 + r₃' : ℂ) = 1 + (2*q + 2*Q4 + 2*Q9 + r₃') := by ring
    rw [h_eq]
    have h_tri : ‖(1 : ℂ)‖ ≤ ‖(1 + (2*q + 2*Q4 + 2*Q9 + r₃') : ℂ)‖ +
        ‖(2*q + 2*Q4 + 2*Q9 + r₃' : ℂ)‖ := by
      have h_one_sub :
          (1 : ℂ) = (1 + (2*q + 2*Q4 + 2*Q9 + r₃')) - (2*q + 2*Q4 + 2*Q9 + r₃') := by ring
      conv_lhs => rw [h_one_sub]
      exact norm_sub_le (1 + (2*q + 2*Q4 + 2*Q9 + r₃') : ℂ) (2*q + 2*Q4 + 2*Q9 + r₃')
    have h_norm_1 : ‖(1 : ℂ)‖ = 1 := norm_one
    linarith [h_tri, hD_sub1_norm_le]
  have h_lambda_eq : modularLambdaH τ =
      A^4 * ((1 + Q2 + Q6 + Q12 + r₂') / (1 + 2*q + 2*Q4 + 2*Q9 + r₃'))^4 := by
    unfold modularLambdaH
    rw [h_th2_eq, h_th3_eq, mul_pow, div_pow]; ring
  rw [h_lambda_eq]
  rw [show (16 * Complex.exp (Real.pi * Complex.I * τ) : ℂ) = A^4 from hA_pow.symm]
  rw [show (128 * Complex.exp (2 * Real.pi * Complex.I * τ) : ℂ) = 8 * q * A^4 from by
    rw [show Complex.exp (2 * Real.pi * Complex.I * τ) = Q2 from rfl]
    rw [hA_pow, hQ2_eq]; ring]
  rw [show (704 * Complex.exp (3 * Real.pi * Complex.I * τ) : ℂ) = 44 * q^2 * A^4 from by
    rw [show Complex.exp (3 * Real.pi * Complex.I * τ) = Q3 from rfl]
    rw [hA_pow, hQ3_eq]; ring]
  rw [show (3072 * Complex.exp (4 * Real.pi * Complex.I * τ) : ℂ) = 192 * q^3 * A^4 from by
    rw [show Complex.exp (4 * Real.pi * Complex.I * τ) = Q4 from rfl]
    rw [hA_pow, hQ4_eq]; ring]
  rw [show (A^4 * ((1 + Q2 + Q6 + Q12 + r₂') / (1 + 2*q + 2*Q4 + 2*Q9 + r₃'))^4 - A^4 +
      8 * q * A^4 - 44 * q^2 * A^4 + 192 * q^3 * A^4 : ℂ) =
      A^4 * (((1 + Q2 + Q6 + Q12 + r₂') / (1 + 2*q + 2*Q4 + 2*Q9 + r₃'))^4 - 1 +
        8 * q - 44 * q^2 + 192 * q^3) from by ring]
  rw [norm_mul, hA_pow_norm]
  rw [hQ2_eq, hQ4_eq, hQ6_eq, hQ9_eq, hQ12_eq]
  have hD_norm_q : (1/2 : ℝ) ≤ ‖(1 + 2*q + 2*q^4 + 2*q^9 + r₃' : ℂ)‖ := by
    rw [show (1 + 2*q + 2*q^4 + 2*q^9 + r₃' : ℂ) = 1 + 2*q + 2*Q4 + 2*Q9 + r₃' from by
      rw [hQ4_eq, hQ9_eq]]
    exact hD_norm_ge
  set v : ℂ := (1 + q^2 + q^6 + q^12 + r₂') / (1 + 2*q + 2*q^4 + 2*q^9 + r₃') - 1 with hv_def
  rw [show ((1 + q^2 + q^6 + q^12 + r₂') / (1 + 2*q + 2*q^4 + 2*q^9 + r₃')) = 1 + v from by
    rw [hv_def]; ring]
  rw [modularLambda_four_term_bracket_identity v q]
  have hv_bound : ‖v‖ ≤ 6 * rq :=
    modularLambda_four_term_v_bound q r₂' r₃' rq hq_norm hrq_pos hrq_lt
      hr2_loose hr3_loose hD_norm_q
  have ht_bound : ‖v + 2*q - 5*q^2 + 10*q^3‖ ≤ 100 * rq^4 :=
    modularLambda_four_term_t_bound q r₂' r₃' rq hq_norm hrq_pos hrq_lt
      hr2_loose hr3_loose hD_norm_q
  -- Use the widened bracket bound helper: ≤ 2100 rq^4.
  have h_bracket_le := modularLambda_four_term_bracket_bound_widened v q rq hq_norm hrq_pos hrq_lt
    ht_bound
  -- 16 rq · 2100 rq^4 = 33600 rq^5 ≤ 35000 rq^5.
  have h_step : (16 * rq) * ‖(4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) +
      6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2 +
      4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3 +
      (v + 2*q - 5*q^2 + 10*q^3)^4 +
      646*q^4 - 1840*q^5 + 4420*q^6 - 8800*q^7 + 15025*q^8 - 21000*q^9 + 23000*q^10 -
        20000*q^11 + 10000*q^12 : ℂ)‖ ≤ 33600 * rq^5 := by
    have h_mul : (16 * rq) * ‖(4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 *
        (v + 2*q - 5*q^2 + 10*q^3) +
        6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2 +
        4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3 +
        (v + 2*q - 5*q^2 + 10*q^3)^4 +
        646*q^4 - 1840*q^5 + 4420*q^6 - 8800*q^7 + 15025*q^8 - 21000*q^9 + 23000*q^10 -
          20000*q^11 + 10000*q^12 : ℂ)‖ ≤
        (16 * rq) * (2100 * rq^4) :=
      mul_le_mul_of_nonneg_left h_bracket_le (by positivity)
    have h_eq : (16 : ℝ) * rq * (2100 * rq^4) = 33600 * rq^5 := by ring
    linarith
  have h_final : 33600 * rq^5 ≤ 35000 * Real.exp (-5 * Real.pi * τ.im) := by
    rw [← hrq5_eq]
    have h_pos : 0 ≤ rq^5 := by positivity
    linarith
  linarith [h_step, h_final]

end NoWanderingDomains
