/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.ModularFunction.ThetaTransformations

/-! # Two- and three-term q-expansion bounds at the cusp

Two- and three-term q-expansion bounds at the cusp for `θ₃`, `jacobiTheta₂ (τ/2) τ`,
and `θ₂` on `τ.im ≥ 1`, obtained by subtracting the leading series terms and bounding
the geometric tails. Together with pure ring identities and norm helpers, these combine
into the two- and three-term truncation bounds for `λ`:
`‖λ − 16q + 128q²‖ ≤ 8192·exp(−3π·τ.im)` and
`‖λ − 16q + 128q² − 704q³‖ ≤ 32768·exp(−4π·τ.im)` with `q = exp(πi τ)`. The four-term
ring identity and its norm bounds are also provided here for the four-term chain.
-/

namespace NoWanderingDomains
open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped ModularForm Manifold MatrixGroups

/-- **Two-term q-expansion of `θ₃`.** For `τ.im ≥ 1`,
`‖θ₃(τ) − 1 − 2·exp(πi τ)‖ ≤ 4·exp(−4π·τ.im)`. The first two
non-zero terms of the q-series `θ₃ = 1 + 2q + 2q⁴ + 2q⁹ + …` are
subtracted; the remaining tail starts at `2q⁴` and is bounded
geometrically. -/
theorem theta3_sub_one_minus_2q_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta3 τ - 1 - 2 * Complex.exp (Real.pi * Complex.I * τ)‖ ≤
      4 * Real.exp (-4 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- Set r := exp(-π τ.im). For τ.im ≥ 1, r ≤ exp(-π) < 1/16.
  set r : ℝ := Real.exp (-Real.pi * τ.im) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_le_exp_neg_pi : r ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr; nlinarith
  -- exp(-π) < 1/16 via exp(π) > 16.
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
  -- r⁴ < 1/2.
  have hr4_lt_half : r^4 < 1/2 := by
    have h1 : r^4 < (1/16)^4 :=
      pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    have h2 : (1/16 : ℝ)^4 < 1/2 := by norm_num
    linarith
  have hr4_pos : 0 < r^4 := by positivity
  have h_1_sub_r4_pos : 0 < 1 - r^4 := by linarith
  have h_inv_le_2 : (1 - r^4)⁻¹ ≤ 2 := by
    rw [show (2 : ℝ) = (1/2)⁻¹ from by norm_num]
    apply inv_anti₀ (by norm_num : (0:ℝ) < 1/2) (by linarith)
  -- hasSum_nat_jacobiTheta gives HasSum over ℕ.
  have h_hasSum := hasSum_nat_jacobiTheta hτim_pos
  have h_summable := h_hasSum.summable
  -- Sum of first term = q.
  have h_sum_one : ∑ i ∈ Finset.range 1,
      Complex.exp (Real.pi * Complex.I * ((i : ℂ) + 1)^2 * τ) =
      Complex.exp (Real.pi * Complex.I * τ) := by
    rw [Finset.sum_range_one]
    congr 1; push_cast; ring
  -- Split: HasSum (fun n => f(n+1)) ((jacobiTheta - 1)/2 - q).
  have h_shifted : Summable (fun n : ℕ =>
      Complex.exp (Real.pi * Complex.I * ((n + 1 : ℕ) + 1 : ℂ)^2 * τ)) :=
    (summable_nat_add_iff (k := 1)).mpr h_summable
  have h_split := h_summable.sum_add_tsum_nat_add 1
  rw [h_sum_one, h_hasSum.tsum_eq] at h_split
  -- h_split : q + ∑'_{n} f(n+1) = (jacobiTheta - 1)/2.
  -- Hence 2(∑' f(n+1)) = jacobiTheta - 1 - 2q.
  unfold theta3
  have h_id : jacobiTheta τ - 1 - 2 * Complex.exp (Real.pi * Complex.I * τ) =
      2 * ∑' n : ℕ, Complex.exp (Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ) := by
    linear_combination -2 * h_split
  rw [h_id, norm_mul, Complex.norm_two]
  -- ‖2 · tsum‖ = 2 · ‖tsum‖. We bound 2 · ‖tsum‖ ≤ 2 · 2 r⁴ = 4 r⁴.
  -- Termwise: ‖f(n+1)‖ = exp(-π (n+2)² τ.im) ≤ r⁴ · (r⁴)^n.
  -- Tail bound: ∑ ‖f(n+1)‖ ≤ r⁴/(1 - r⁴) ≤ 2 r⁴.
  have hr4_lt_one : r^4 < 1 := by linarith
  have h_term_norm : ∀ n : ℕ,
      ‖Complex.exp (Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ)‖ ≤
      r^4 * (r^4)^n := by
    intro n
    rw [Complex.norm_exp]
    -- Re argument: Re(π i (n+2)² τ) = -π (n+2)² τ.im.
    have h_re : (Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ).re =
        -(Real.pi * ((n : ℝ) + 2)^2 * τ.im) := by
      have h_factor : Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ =
          ((Real.pi * ((n : ℝ) + 2)^2 : ℝ) : ℂ) * (Complex.I * τ) := by
        push_cast; ring
      rw [h_factor, Complex.re_ofReal_mul]
      rw [show (Complex.I * τ).re = -τ.im from by
        rw [Complex.mul_re, Complex.I_re, Complex.I_im]; ring]
      ring
    rw [h_re]
    -- Goal: exp(-π (n+2)² τ.im) ≤ r⁴ · (r⁴)^n.
    have h_bound_eq : r^4 * (r^4)^n = Real.exp ((1 + (n : ℝ)) * (-4 * Real.pi * τ.im)) := by
      have h_r4_eq : r^4 = Real.exp (-4 * Real.pi * τ.im) := by
        rw [hr_def, ← Real.exp_nat_mul]; congr 1; ring
      rw [h_r4_eq, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; ring
    rw [h_bound_eq]
    apply Real.exp_le_exp.mpr
    -- Goal: -(π (n+2)² τ.im) ≤ (1 + n) · (-4π τ.im).
    have h_ineq : ((n : ℝ) + 2)^2 ≥ 4 * ((n : ℝ) + 1) := by nlinarith [sq_nonneg ((n : ℝ))]
    have h_pi_tau_pos : 0 ≤ Real.pi * τ.im := mul_nonneg hπ_pos.le hτim_pos.le
    nlinarith
  -- Summability of bound.
  have h_bound_summable : Summable (fun n : ℕ => r^4 * (r^4)^n) :=
    (summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ r^4) hr4_lt_one).mul_left _
  -- Bound the tsum of norms.
  have h_norm_summable : Summable (fun n : ℕ =>
      ‖Complex.exp (Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ)‖) :=
    h_bound_summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_term_norm
  have h_tsum_norm_le := norm_tsum_le_tsum_norm h_norm_summable
  have h_tsum_bound : (∑' n : ℕ,
      ‖Complex.exp (Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ)‖) ≤
      r^4 * (1 - r^4)⁻¹ := by
    refine (h_norm_summable.tsum_le_tsum h_term_norm h_bound_summable).trans ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr4_lt_one]
  -- Conclude.
  have h_chain : ‖∑' n : ℕ,
      Complex.exp (Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ)‖ ≤
      r^4 * (1 - r^4)⁻¹ := h_tsum_norm_le.trans h_tsum_bound
  have h_inv_bound : r^4 * (1 - r^4)⁻¹ ≤ 2 * r^4 := by
    have : r^4 * (1 - r^4)⁻¹ ≤ r^4 * 2 :=
      mul_le_mul_of_nonneg_left h_inv_le_2 hr4_pos.le
    linarith
  -- Now ‖2 · tsum‖ = 2 · ‖tsum‖. With ‖tsum‖ ≤ 2 r⁴, get 4 r⁴.
  -- r⁴ = exp(-4π τ.im).
  have hr4_eq : r^4 = Real.exp (-4 * Real.pi * τ.im) := by
    rw [hr_def, ← Real.exp_nat_mul]
    congr 1; ring
  calc (2 : ℝ) * ‖∑' n : ℕ,
        Complex.exp (Real.pi * Complex.I * (((n + 1 : ℕ) : ℂ) + 1)^2 * τ)‖
      ≤ 2 * (r^4 * (1 - r^4)⁻¹) := by
        apply mul_le_mul_of_nonneg_left h_chain (by norm_num)
    _ ≤ 2 * (2 * r^4) := by
        apply mul_le_mul_of_nonneg_left h_inv_bound (by norm_num)
    _ = 4 * r^4 := by ring
    _ = 4 * Real.exp (-4 * Real.pi * τ.im) := by rw [hr4_eq]

/-- **Three-term q-expansion of `θ₃`.** For `τ.im ≥ 1`,
`‖θ₃(τ) − 1 − 2·exp(πi τ) − 2·exp(4πi τ)‖ ≤ 4·exp(−9π·τ.im)`. The
first three non-zero terms of `θ₃ = 1 + 2q + 2q⁴ + 2q⁹ + …` are
subtracted; the remaining tail starts at `2q⁹`. This is the building
block (together with three-term θ₂ and the algebraic combination
yielding three-term λ) for the cusp-1 sign control in
`modularLambdaH_cusp_one_im_nonneg_nbhd_in_F`. -/
theorem theta3_sub_one_minus_2q_minus_2q4_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta3 τ - 1 - 2 * Complex.exp (Real.pi * Complex.I * τ) -
        2 * Complex.exp (4 * Real.pi * Complex.I * τ)‖ ≤
      4 * Real.exp (-9 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- r := exp(-π τ.im). For τ.im ≥ 1, r ≤ exp(-π) < 1/16.
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
  -- r⁵ < 1.
  have hr5_lt_one : r^5 < 1 := by
    have h1 : r^5 < (1/16)^5 := pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    have h2 : ((1/16 : ℝ))^5 < 1 := by norm_num
    linarith
  -- r⁵ < 1/2 for the (1-r⁵)⁻¹ ≤ 2 bound.
  have hr5_lt_half : r^5 < 1/2 := by
    have h1 : r^5 < (1/16)^5 := pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    have h2 : ((1/16 : ℝ))^5 ≤ 1/2 := by norm_num
    linarith
  have h_one_sub_r5_pos : 0 < 1 - r^5 := by linarith
  have h_inv_le_2 : (1 - r^5)⁻¹ ≤ 2 := by
    rw [show (2 : ℝ) = (1/2)⁻¹ from by norm_num]
    apply inv_anti₀ (by norm_num : (0:ℝ) < 1/2) (by linarith)
  -- HasSum on ℕ for jacobiTheta.
  have h_hasSum := hasSum_nat_jacobiTheta hτim_pos
  have h_summable := h_hasSum.summable
  -- Sum of first two terms: q + q⁴.
  have h_sum_two : ∑ i ∈ Finset.range 2,
      Complex.exp (Real.pi * Complex.I * ((i : ℂ) + 1)^2 * τ) =
      Complex.exp (Real.pi * Complex.I * τ) +
      Complex.exp (4 * Real.pi * Complex.I * τ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    push_cast
    congr 1
    · congr 1; ring
    · congr 1; ring
  -- Split off n=0,1.
  have h_shifted : Summable (fun n : ℕ =>
      Complex.exp (Real.pi * Complex.I * ((n + 2 : ℕ) + 1 : ℂ)^2 * τ)) :=
    (summable_nat_add_iff (k := 2)).mpr h_summable
  have h_split := h_summable.sum_add_tsum_nat_add 2
  rw [h_sum_two, h_hasSum.tsum_eq] at h_split
  -- h_split : (q + q⁴) + ∑'_{n} f(n+2) = (jacobiTheta - 1)/2.
  -- ⟹ 2 (q + q⁴) + 2 ∑' = jacobiTheta - 1.
  -- ⟹ jacobiTheta - 1 - 2q - 2q⁴ = 2 ∑'.
  unfold theta3
  have h_id : jacobiTheta τ - 1 - 2 * Complex.exp (Real.pi * Complex.I * τ) -
      2 * Complex.exp (4 * Real.pi * Complex.I * τ) =
      2 * ∑' n : ℕ, Complex.exp (Real.pi * Complex.I *
        (((n + 2 : ℕ) : ℂ) + 1)^2 * τ) := by
    linear_combination -2 * h_split
  rw [h_id, norm_mul, Complex.norm_two]
  -- Termwise: ‖exp(πi (n+3)² τ)‖ ≤ exp(-π · (n+3)² · τ.im) ≤ r^9 · (r^5)^n.
  have hr5_lt_one' : r^5 < 1 := hr5_lt_one
  have h_term_norm : ∀ n : ℕ,
      ‖Complex.exp (Real.pi * Complex.I * (((n + 2 : ℕ) : ℂ) + 1)^2 * τ)‖ ≤
      r^9 * (r^5)^n := by
    intro n
    rw [Complex.norm_exp]
    -- Re argument: -π · (n+3)² · τ.im.
    have h_re : (Real.pi * Complex.I * (((n + 2 : ℕ) : ℂ) + 1)^2 * τ).re =
        -(Real.pi * ((n : ℝ) + 3)^2 * τ.im) := by
      have h_factor : Real.pi * Complex.I * (((n + 2 : ℕ) : ℂ) + 1)^2 * τ =
          ((Real.pi * ((n : ℝ) + 3)^2 : ℝ) : ℂ) * (Complex.I * τ) := by
        push_cast; ring
      rw [h_factor, Complex.re_ofReal_mul]
      rw [show (Complex.I * τ).re = -τ.im from by
        rw [Complex.mul_re, Complex.I_re, Complex.I_im]; ring]
      ring
    rw [h_re]
    -- Goal: exp(-π (n+3)² τ.im) ≤ r^9 · (r^5)^n.
    -- r^9 · (r^5)^n = exp(-π τ.im · (9 + 5n)).
    have h_bound_eq : r^9 * (r^5)^n = Real.exp ((9 + 5 * (n : ℝ)) * (-Real.pi * τ.im)) := by
      have h_r9_eq : r^9 = Real.exp (9 * (-Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul]; push_cast; ring_nf
      have h_r5_pow_eq : (r^5)^n = Real.exp ((5 * (n : ℝ)) * (-Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1; push_cast; ring
      rw [h_r9_eq, h_r5_pow_eq, ← Real.exp_add]
      congr 1; ring
    rw [h_bound_eq]
    apply Real.exp_le_exp.mpr
    -- -(π (n+3)² τ.im) ≤ (9 + 5n)(-π τ.im) ⟺ (n+3)² ≥ 9 + 5n.
    have h_ineq : ((n : ℝ) + 3)^2 ≥ 9 + 5 * (n : ℝ) := by nlinarith [sq_nonneg ((n : ℝ))]
    have h_pi_tau_nn : 0 ≤ Real.pi * τ.im := mul_nonneg hπ_pos.le hτim_pos.le
    nlinarith
  -- Summability of bound.
  have h_bound_summable : Summable (fun n : ℕ => r^9 * (r^5)^n) :=
    (summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ r^5) hr5_lt_one).mul_left _
  -- Norm-summability of tail.
  have h_norm_summable : Summable (fun n : ℕ =>
      ‖Complex.exp (Real.pi * Complex.I * (((n + 2 : ℕ) : ℂ) + 1)^2 * τ)‖) :=
    h_bound_summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_term_norm
  have h_tsum_norm_le := norm_tsum_le_tsum_norm h_norm_summable
  have h_tsum_bound : (∑' n : ℕ,
      ‖Complex.exp (Real.pi * Complex.I * (((n + 2 : ℕ) : ℂ) + 1)^2 * τ)‖) ≤
      r^9 * (1 - r^5)⁻¹ := by
    refine (h_norm_summable.tsum_le_tsum h_term_norm h_bound_summable).trans ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr5_lt_one]
  have h_chain : ‖∑' n : ℕ,
      Complex.exp (Real.pi * Complex.I * (((n + 2 : ℕ) : ℂ) + 1)^2 * τ)‖ ≤
      r^9 * (1 - r^5)⁻¹ := h_tsum_norm_le.trans h_tsum_bound
  -- r^9 · (1 - r^5)⁻¹ ≤ 2 r^9.
  have hr9_pos : 0 < r^9 := by positivity
  have h_inv_bound : r^9 * (1 - r^5)⁻¹ ≤ 2 * r^9 := by
    have : r^9 * (1 - r^5)⁻¹ ≤ r^9 * 2 :=
      mul_le_mul_of_nonneg_left h_inv_le_2 hr9_pos.le
    linarith
  have hr9_eq : r^9 = Real.exp (-9 * Real.pi * τ.im) := by
    rw [hr_def, ← Real.exp_nat_mul]; congr 1; ring
  calc (2 : ℝ) * ‖∑' n : ℕ,
        Complex.exp (Real.pi * Complex.I * (((n + 2 : ℕ) : ℂ) + 1)^2 * τ)‖
      ≤ 2 * (r^9 * (1 - r^5)⁻¹) := by
        apply mul_le_mul_of_nonneg_left h_chain (by norm_num)
    _ ≤ 2 * (2 * r^9) := by
        apply mul_le_mul_of_nonneg_left h_inv_bound (by norm_num)
    _ = 4 * r^9 := by ring
    _ = 4 * Real.exp (-9 * Real.pi * τ.im) := by rw [hr9_eq]

/-- **Two-term q-expansion of `jacobiTheta₂(τ/2, τ)`.** For `τ.im ≥ 1`,
`‖jacobiTheta₂(τ/2, τ) − 2 − 2·exp(2πi τ)‖ ≤ 4·exp(−6π·τ.im)`.
By the symmetric pairing `n ↔ −n−1` and
`jacobiTheta₂_term_half_norm`, the series splits as
`jacobiTheta₂(τ/2, τ) = 2 ∑_{k≥0} exp(πi·k(k+1)·τ) = 2 + 2q² + 2q⁶ + …`;
subtracting the first two terms leaves a tail starting at `2q⁶`. -/
theorem jacobiTheta₂_half_sub_two_minus_two_q2_norm_le_of_im_ge_one
    {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta₂ (τ / 2) τ - 2 - 2 * Complex.exp (2 * Real.pi * Complex.I * τ)‖ ≤
      8 * Real.exp (-6 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- r := exp(-2π τ.im). Need r < 1/2.
  set r : ℝ := Real.exp (-2 * Real.pi * τ.im) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_lt_half : r < 1 / 2 := by
    have h_arg : -2 * Real.pi * τ.im ≤ -2 * Real.pi := by nlinarith
    have h_le : r ≤ Real.exp (-2 * Real.pi) := Real.exp_le_exp.mpr h_arg
    have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h_2pi_gt_1 : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h_exp_2pi_gt_2 : (2 : ℝ) < Real.exp (2 * Real.pi) := by
      have h_mono : Real.exp 1 ≤ Real.exp (2 * Real.pi) := Real.exp_le_exp.mpr h_2pi_gt_1.le
      linarith
    have h_exp_neg_lt : Real.exp (-2 * Real.pi) < 1 / 2 := by
      rw [show (-2 * Real.pi : ℝ) = -(2 * Real.pi) from by ring, Real.exp_neg]
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by ring]
      exact inv_strictAnti₀ (by norm_num : (0:ℝ) < 2) h_exp_2pi_gt_2
    linarith
  have hr_lt_one : r < 1 := by linarith
  have hr2_lt_one : r^2 < 1 := by
    have : r^2 < (1/2)^2 := pow_lt_pow_left₀ hr_lt_half hr_nn (by norm_num)
    nlinarith
  have h_one_sub_r2_pos : 0 < 1 - r^2 := by linarith
  have h_inv_one_sub_r2_le : (1 - r^2)⁻¹ ≤ 2 := by
    have h_r2_le : r^2 ≤ 1/2 := by
      have : r^2 < (1/2)^2 := pow_lt_pow_left₀ hr_lt_half hr_nn (by norm_num)
      nlinarith
    rw [show (2 : ℝ) = (1 / 2)⁻¹ from by norm_num]
    exact inv_anti₀ (by norm_num : (0:ℝ) < 1/2) (by linarith)
  -- HasSum on ℤ, then nat_add_neg.
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
  -- ‖exp(2πi τ)‖ = r, ‖exp(6πi τ)‖ = r³.
  have h_norm_exp_2 : ‖Complex.exp (2 * Real.pi * Complex.I * τ)‖ = r := by
    rw [Complex.norm_exp, hr_def]
    congr 1
    have h_eq : (2 * Real.pi * Complex.I * τ : ℂ) =
        ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
  have h_norm_exp_6 : ‖Complex.exp (6 * Real.pi * Complex.I * τ)‖ = r^3 := by
    rw [Complex.norm_exp, hr_def, ← Real.exp_nat_mul]
    congr 1
    have h_eq : (6 * Real.pi * Complex.I * τ : ℂ) =
        ((6 * Real.pi : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  -- Apply HasSum.nat_add_neg.
  have h_pair_hasSum : HasSum (fun n : ℕ =>
      jacobiTheta₂_term (n : ℤ) (τ/2) τ + jacobiTheta₂_term (-(n : ℤ)) (τ/2) τ)
      (jacobiTheta₂ (τ/2) τ + 1) := by
    have := h_hasSum_int.nat_add_neg
    rw [h_term_zero] at this
    exact this
  have h_pair_summable : Summable (fun n : ℕ =>
      jacobiTheta₂_term ((n : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-((n : ℕ) : ℤ)) (τ/2) τ) := h_pair_hasSum.summable
  -- Sum of first 3 terms: 3 + 2 exp(2πi τ) + exp(6πi τ).
  have h_sum_three :
      ∑ i ∈ Finset.range 3, (jacobiTheta₂_term ((i : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-((i : ℕ) : ℤ)) (τ/2) τ) =
      3 + 2 * Complex.exp (2 * Real.pi * Complex.I * τ) +
      Complex.exp (6 * Real.pi * Complex.I * τ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    simp only [Nat.cast_zero, neg_zero, Nat.cast_one, Nat.cast_ofNat]
    rw [h_term_zero, h_term_one, h_term_neg_one, h_term_two, h_term_neg_two]
    ring
  -- Shift by 3: HasSum tail.
  have h_pair_tsum : ∑' n : ℕ, (jacobiTheta₂_term ((n : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-((n : ℕ) : ℤ)) (τ/2) τ) =
      jacobiTheta₂ (τ/2) τ + 1 := h_pair_hasSum.tsum_eq
  have h_tail_hasSum : HasSum (fun n : ℕ =>
      jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ)
      (jacobiTheta₂ (τ/2) τ - 2 -
        2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
        Complex.exp (6 * Real.pi * Complex.I * τ)) := by
    have h_shift_summable : Summable (fun n : ℕ =>
        jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ) := by
      have := (summable_nat_add_iff (k := 3)).mpr h_pair_summable
      exact this
    rw [Summable.hasSum_iff h_shift_summable]
    have h_eq := (Summable.sum_add_tsum_nat_add 3 h_pair_summable).symm
    rw [h_pair_tsum] at h_eq
    rw [h_sum_three] at h_eq
    linear_combination -h_eq
  -- Rearrange.
  have h_eq : jacobiTheta₂ (τ/2) τ - 2 - 2 * Complex.exp (2 * Real.pi * Complex.I * τ) =
      Complex.exp (6 * Real.pi * Complex.I * τ) +
      ∑' n : ℕ, (jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ) := by
    rw [h_tail_hasSum.tsum_eq]; ring
  rw [h_eq]
  -- Triangle inequality.
  refine (norm_add_le _ _).trans ?_
  rw [h_norm_exp_6]
  -- Termwise bound: ‖term((n+3)) + term(-(n+3))‖ ≤ 2 · r³ · (r²)^n.
  have h_termwise : ∀ n : ℕ,
      ‖jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ‖ ≤ 2 * (r^3 * (r^2)^n) := by
    intro n
    refine (norm_add_le _ _).trans ?_
    -- Compute r³ · (r²)^n = exp(-2π τ.im · (3 + 2n)).
    have h_bound_eq : r^3 * (r^2)^n = Real.exp ((3 + 2 * (n : ℝ)) * (-2 * Real.pi * τ.im)) := by
      have h_r3_eq : r^3 = Real.exp (3 * (-2 * Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul]; push_cast; ring_nf
      have h_r2_pow_eq : (r^2)^n = Real.exp ((2 * (n : ℝ)) * (-2 * Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1; push_cast; ring
      rw [h_r3_eq, h_r2_pow_eq, ← Real.exp_add]
      congr 1; ring
    have h_pi_tau_nn : 0 ≤ Real.pi * τ.im := mul_nonneg hπ_pos.le hτim_pos.le
    have hN_pos : ((((n + 3) : ℕ) : ℤ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    -- ‖term((n+3))‖ ≤ r³ · (r²)^n.
    have h_pos_norm : ‖jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ‖ ≤ r^3 * (r^2)^n := by
      rw [jacobiTheta₂_term_half_norm, hN_pos, h_bound_eq]
      apply Real.exp_le_exp.mpr
      -- -(π · (n+3) · (n+4) · τ.im) ≤ (3 + 2n) · (-2π τ.im).
      -- ⟺ (n+3)(n+4) ≥ 2(3 + 2n) = 6 + 4n.
      have h_ineq : 6 + 4 * (n : ℝ) ≤ ((n : ℝ) + 3) * ((n : ℝ) + 4) := by nlinarith
      have h_mul : Real.pi * τ.im * (6 + 4 * (n : ℝ)) ≤
          Real.pi * τ.im * (((n : ℝ) + 3) * ((n : ℝ) + 4)) :=
        mul_le_mul_of_nonneg_left h_ineq h_pi_tau_nn
      linarith
    -- ‖term(-(n+3))‖ ≤ r³ · (r²)^n.
    have h_neg_norm : ‖jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ‖ ≤
        r^3 * (r^2)^n := by
      rw [jacobiTheta₂_term_half_norm]
      have hN' : ((-(((n + 3) : ℕ) : ℤ) : ℤ) : ℝ) = -((n : ℝ) + 3) := by push_cast; ring
      rw [hN', h_bound_eq]
      apply Real.exp_le_exp.mpr
      -- -(π · (-(n+3)) · (-(n+3)+1) · τ.im) = -(π · (n+3)(n+2) · τ.im) ≤ (3 + 2n) · (-2π τ.im).
      -- ⟺ (n+3)(n+2) ≥ 6 + 4n.
      have h_ineq : 6 + 4 * (n : ℝ) ≤ (-((n : ℝ) + 3)) * (-((n : ℝ) + 3) + 1) := by nlinarith
      have h_mul : Real.pi * τ.im * (6 + 4 * (n : ℝ)) ≤
          Real.pi * τ.im * ((-((n : ℝ) + 3)) * (-((n : ℝ) + 3) + 1)) :=
        mul_le_mul_of_nonneg_left h_ineq h_pi_tau_nn
      linarith
    linarith
  -- Summability of bound: ∑ 2 r³ (r²)^n.
  have hr3_pos : 0 < r^3 := by positivity
  have hr2_nn : 0 ≤ r^2 := by positivity
  have h_bound_summable : Summable (fun n : ℕ => 2 * (r^3 * (r^2)^n)) := by
    have h_geo : Summable (fun n : ℕ => (r^2)^n) :=
      summable_geometric_of_lt_one hr2_nn hr2_lt_one
    have : Summable (fun n : ℕ => r^3 * (r^2)^n) := h_geo.mul_left _
    exact this.mul_left _
  -- Tsum of bound: 2 r³ / (1 - r²).
  have h_bound_tsum : ∑' n : ℕ, 2 * (r^3 * (r^2)^n) =
      2 * r^3 * (1 - r^2)⁻¹ := by
    rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr2_nn hr2_lt_one]
    ring
  -- norm-summability of tail.
  have h_norm_summable : Summable (fun n : ℕ =>
      ‖jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ‖) :=
    h_bound_summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_termwise
  have h_norm_tsum_le := norm_tsum_le_tsum_norm h_norm_summable
  -- ∑ ‖term + term‖ ≤ 2 r³ / (1 - r²).
  have h_tsum_le : (∑' n : ℕ,
      ‖jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ‖) ≤
      2 * r^3 * (1 - r^2)⁻¹ := by
    rw [← h_bound_tsum]
    exact h_norm_summable.tsum_le_tsum h_termwise h_bound_summable
  have h_step : ‖∑' n : ℕ, (jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ)‖ ≤ 2 * r^3 * (1 - r^2)⁻¹ :=
    h_norm_tsum_le.trans h_tsum_le
  -- Final: r³ + 2 r³ · (1 - r²)⁻¹ ≤ r³ + 4 r³ = 5 r³ ≤ 8 r³.
  have h_final : r^3 + 2 * r^3 * (1 - r^2)⁻¹ ≤ 8 * r^3 := by
    have h1 : 2 * r^3 * (1 - r^2)⁻¹ ≤ 2 * r^3 * 2 := by
      apply mul_le_mul_of_nonneg_left h_inv_one_sub_r2_le
      positivity
    linarith
  -- r³ = exp(-6π τ.im).
  have hr3_eq : r^3 = Real.exp (-6 * Real.pi * τ.im) := by
    rw [hr_def, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  calc r^3 + ‖∑' n : ℕ, (jacobiTheta₂_term (((n + 3) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 3) : ℕ) : ℤ)) (τ/2) τ)‖
      ≤ r^3 + 2 * r^3 * (1 - r^2)⁻¹ := by linarith [h_step]
    _ ≤ 8 * r^3 := h_final
    _ = 8 * Real.exp (-6 * Real.pi * τ.im) := by rw [hr3_eq]

/-- **Three-term q-expansion of `jacobiTheta₂(τ/2, τ)`.** For `τ.im ≥ 1`,
`‖jacobiTheta₂(τ/2, τ) − 2 − 2·exp(2πi τ) − 2·exp(6πi τ)‖ ≤ 8·exp(−12π·τ.im)`.
Subtracts three pairs `(k = 0, 1, 2)` from
`jacobiTheta₂(τ/2, τ) = 2 ∑_{k≥0} exp(πi·k(k+1)·τ)`; the tail starts
at `2 exp(12πi τ)` from `k = 3`. -/
theorem jacobiTheta₂_half_sub_three_term_norm_le_of_im_ge_one
    {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta₂ (τ / 2) τ - 2 - 2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
        2 * Complex.exp (6 * Real.pi * Complex.I * τ)‖ ≤
      8 * Real.exp (-12 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- r := exp(-2π τ.im).
  set r : ℝ := Real.exp (-2 * Real.pi * τ.im) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_nn : 0 ≤ r := hr_pos.le
  -- r < 1/256 (since rq < 1/16 implies rq² < 1/256, and r = rq²).
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
  have hr4_lt_one : r^4 < 1 := by
    have : r^4 < (1/2)^4 := pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    nlinarith
  -- r⁴ < 1/16.
  have hr4_lt_half : r^4 < 1/2 := by
    have h1 : r^4 < (1/2)^4 := pow_lt_pow_left₀ hr_lt hr_nn (by norm_num)
    have h2 : ((1/2 : ℝ))^4 ≤ 1/2 := by norm_num
    linarith
  have h_one_sub_r4_pos : 0 < 1 - r^4 := by linarith
  have h_inv_one_sub_r4_le : (1 - r^4)⁻¹ ≤ 2 := by
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
  -- Sum of first 4 nats (n=0,1,2,3):
  -- 2 + (Q² + 1) + (Q^6 + Q²) + (Q^12 + Q^6) = 3 + 2Q² + 2Q^6 + Q^12.
  have h_sum_four :
      ∑ i ∈ Finset.range 4, (jacobiTheta₂_term ((i : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-((i : ℕ) : ℤ)) (τ/2) τ) =
      3 + 2 * Complex.exp (2 * Real.pi * Complex.I * τ) +
      2 * Complex.exp (6 * Real.pi * Complex.I * τ) +
      Complex.exp (12 * Real.pi * Complex.I * τ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    simp only [Nat.cast_zero, neg_zero, Nat.cast_one, Nat.cast_ofNat]
    rw [h_term_zero, h_term_one, h_term_neg_one, h_term_two, h_term_neg_two,
        h_term_three, h_term_neg_three]
    ring
  have h_pair_tsum : ∑' n : ℕ, (jacobiTheta₂_term ((n : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-((n : ℕ) : ℤ)) (τ/2) τ) =
      jacobiTheta₂ (τ/2) τ + 1 := h_pair_hasSum.tsum_eq
  -- HasSum tail starting at n=4.
  have h_tail_hasSum : HasSum (fun n : ℕ =>
      jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ)
      (jacobiTheta₂ (τ/2) τ - 2 -
        2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
        2 * Complex.exp (6 * Real.pi * Complex.I * τ) -
        Complex.exp (12 * Real.pi * Complex.I * τ)) := by
    have h_shift_summable : Summable (fun n : ℕ =>
        jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ) := by
      have := (summable_nat_add_iff (k := 4)).mpr h_pair_summable
      exact this
    rw [Summable.hasSum_iff h_shift_summable]
    have h_eq := (Summable.sum_add_tsum_nat_add 4 h_pair_summable).symm
    rw [h_pair_tsum] at h_eq
    rw [h_sum_four] at h_eq
    linear_combination -h_eq
  -- Express target as exp(12πi τ) + tail.
  have h_eq : jacobiTheta₂ (τ/2) τ - 2 -
      2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
      2 * Complex.exp (6 * Real.pi * Complex.I * τ) =
      Complex.exp (12 * Real.pi * Complex.I * τ) +
      ∑' n : ℕ, (jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ) := by
    rw [h_tail_hasSum.tsum_eq]; ring
  rw [h_eq]
  refine (norm_add_le _ _).trans ?_
  -- ‖exp(12πi τ)‖ = r⁶.
  have h_norm_exp_12 : ‖Complex.exp (12 * Real.pi * Complex.I * τ)‖ = r^6 := by
    rw [Complex.norm_exp, hr_def, ← Real.exp_nat_mul]
    congr 1
    have h_eq : (12 * Real.pi * Complex.I * τ : ℂ) =
        ((12 * Real.pi : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [h_norm_exp_12]
  -- Termwise bound: for n : ℕ, ‖term(n+4) + term(-(n+4))‖ ≤ 2 r⁶ (r⁴)^n.
  -- For k = n+4 ≥ 4: k(k+1) ≥ 20, k(k-1) ≥ 12. With r = exp(-2π τ.im),
  -- ‖term(n)‖ = r^{n(n+1)/2}.
  -- So ‖term(n+4)‖ ≤ r^{(n+4)(n+5)/2}, ‖term(-(n+4))‖ ≤ r^{(n+4)(n+3)/2}.
  -- (n+4)(n+3)/2 ≥ 6 + 4n: verify (n+4)(n+3)/2 - 6 - 4n = (n²-n)/2 ≥ 0.
  -- (n+4)(n+5)/2 ≥ (n+4)(n+3)/2 ≥ 6 + 4n.
  have h_termwise : ∀ n : ℕ,
      ‖jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ‖ ≤ 2 * (r^6 * (r^4)^n) := by
    intro n
    refine (norm_add_le _ _).trans ?_
    have h_bound_eq : r^6 * (r^4)^n = Real.exp ((6 + 4 * (n : ℝ)) * (-2 * Real.pi * τ.im)) := by
      have h_r6_eq : r^6 = Real.exp (6 * (-2 * Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul]; push_cast; ring_nf
      have h_r4_pow_eq : (r^4)^n = Real.exp ((4 * (n : ℝ)) * (-2 * Real.pi * τ.im)) := by
        rw [hr_def, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1; push_cast; ring
      rw [h_r6_eq, h_r4_pow_eq, ← Real.exp_add]
      congr 1; ring
    have h_pi_tau_nn : 0 ≤ Real.pi * τ.im := mul_nonneg hπ_pos.le hτim_pos.le
    have hN_pos : ((((n + 4) : ℕ) : ℤ) : ℝ) = (n : ℝ) + 4 := by push_cast; ring
    have h_pos_norm : ‖jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ‖ ≤ r^6 * (r^4)^n := by
      rw [jacobiTheta₂_term_half_norm, hN_pos, h_bound_eq]
      apply Real.exp_le_exp.mpr
      -- -(π · (n+4) · (n+5) · τ.im) ≤ (6 + 4n)·(-2π τ.im) ⟺ (n+4)(n+5) ≥ 2·(6 + 4n) = 12 + 8n.
      have h_ineq : 12 + 8 * (n : ℝ) ≤ ((n : ℝ) + 4) * ((n : ℝ) + 5) := by nlinarith
      have h_mul : Real.pi * τ.im * (12 + 8 * (n : ℝ)) ≤
          Real.pi * τ.im * (((n : ℝ) + 4) * ((n : ℝ) + 5)) :=
        mul_le_mul_of_nonneg_left h_ineq h_pi_tau_nn
      linarith
    have h_neg_norm : ‖jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ‖ ≤
        r^6 * (r^4)^n := by
      rw [jacobiTheta₂_term_half_norm]
      have hN' : ((-(((n + 4) : ℕ) : ℤ) : ℤ) : ℝ) = -((n : ℝ) + 4) := by push_cast; ring
      rw [hN', h_bound_eq]
      apply Real.exp_le_exp.mpr
      -- -(π · (-(n+4)) · (-(n+4)+1) · τ.im) = -(π · (n+4)(n+3) · τ.im) ≤ (6 + 4n)(-2π τ.im).
      -- ⟺ (n+4)(n+3) ≥ 12 + 8n, i.e. n² + 7n + 12 ≥ 12 + 8n, i.e. n² ≥ n.
      have h_n_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h_n_sq_ge : (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simp
        · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          nlinarith
      have h_ineq : 12 + 8 * (n : ℝ) ≤ (-((n : ℝ) + 4)) * (-((n : ℝ) + 4) + 1) := by nlinarith
      have h_mul : Real.pi * τ.im * (12 + 8 * (n : ℝ)) ≤
          Real.pi * τ.im * ((-((n : ℝ) + 4)) * (-((n : ℝ) + 4) + 1)) :=
        mul_le_mul_of_nonneg_left h_ineq h_pi_tau_nn
      linarith
    linarith
  -- Summability of bound.
  have h_bound_summable : Summable (fun n : ℕ => 2 * (r^6 * (r^4)^n)) := by
    have h_geo : Summable (fun n : ℕ => (r^4)^n) :=
      summable_geometric_of_lt_one (by positivity) hr4_lt_one
    have : Summable (fun n : ℕ => r^6 * (r^4)^n) := h_geo.mul_left _
    exact this.mul_left _
  -- Tsum of bound = 2 r⁶ / (1 - r⁴).
  have h_bound_tsum : ∑' n : ℕ, 2 * (r^6 * (r^4)^n) =
      2 * r^6 * (1 - r^4)⁻¹ := by
    rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr4_lt_one]
    ring
  have h_norm_summable : Summable (fun n : ℕ =>
      ‖jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ‖) :=
    h_bound_summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_termwise
  have h_norm_tsum_le := norm_tsum_le_tsum_norm h_norm_summable
  have h_tsum_le : (∑' n : ℕ,
      ‖jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ‖) ≤
      2 * r^6 * (1 - r^4)⁻¹ := by
    rw [← h_bound_tsum]
    exact h_norm_summable.tsum_le_tsum h_termwise h_bound_summable
  have h_step : ‖∑' n : ℕ, (jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ)‖ ≤ 2 * r^6 * (1 - r^4)⁻¹ :=
    h_norm_tsum_le.trans h_tsum_le
  have hr6_pos : 0 < r^6 := by positivity
  have h_final : r^6 + 2 * r^6 * (1 - r^4)⁻¹ ≤ 8 * r^6 := by
    have h1 : 2 * r^6 * (1 - r^4)⁻¹ ≤ 2 * r^6 * 2 := by
      apply mul_le_mul_of_nonneg_left h_inv_one_sub_r4_le
      positivity
    linarith
  have hr6_eq : r^6 = Real.exp (-12 * Real.pi * τ.im) := by
    rw [hr_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc r^6 + ‖∑' n : ℕ, (jacobiTheta₂_term (((n + 4) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 4) : ℕ) : ℤ)) (τ/2) τ)‖
      ≤ r^6 + 2 * r^6 * (1 - r^4)⁻¹ := by linarith [h_step]
    _ ≤ 8 * r^6 := h_final
    _ = 8 * Real.exp (-12 * Real.pi * τ.im) := by rw [hr6_eq]

/-- **Two-term leading bound for `θ₂`.** For `τ.im ≥ 1`,
`‖θ₂(τ) − 2·exp(πi τ/4)·(1 + exp(2πi τ))‖ ≤ 4·exp(−25π·τ.im/4)`.
Follows from `jacobiTheta₂_half_sub_two_minus_two_q2_norm_le_of_im_ge_one`
and `θ₂(τ) = exp(πi τ/4) · jacobiTheta₂(τ/2, τ)`, factoring out
`exp(πi τ/4)` with `|exp(πi τ/4)| = exp(−π τ.im/4)`. -/
theorem theta2_norm_sub_two_term_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta2 τ - 2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
        (1 + Complex.exp (2 * Real.pi * Complex.I * τ))‖ ≤
      8 * Real.exp (-(25 * Real.pi * τ.im / 4)) := by
  unfold theta2
  -- theta2 τ - 2 exp(πi τ/4)(1 + exp(2πi τ)) =
  --   exp(πi τ/4) · (jacobiTheta₂(τ/2, τ) - 2 - 2 exp(2πi τ)).
  have h_factor :
      Complex.exp (Real.pi * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ -
        2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
          (1 + Complex.exp (2 * Real.pi * Complex.I * τ)) =
      Complex.exp (Real.pi * Complex.I * τ / 4) *
        (jacobiTheta₂ (τ / 2) τ - 2 -
          2 * Complex.exp (2 * Real.pi * Complex.I * τ)) := by
    ring
  rw [h_factor, norm_mul]
  -- |exp(πi τ/4)| = exp(-π τ.im/4).
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
  have h_tail := jacobiTheta₂_half_sub_two_minus_two_q2_norm_le_of_im_ge_one hτ
  have h_exp_nn : 0 ≤ Real.exp (-(Real.pi * τ.im / 4)) := (Real.exp_pos _).le
  have h_combine :
      Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-6 * Real.pi * τ.im)) =
      8 * Real.exp (-(25 * Real.pi * τ.im / 4)) := by
    rw [show (Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-6 * Real.pi * τ.im)) : ℝ) =
        8 * (Real.exp (-(Real.pi * τ.im / 4)) * Real.exp (-6 * Real.pi * τ.im)) from by ring]
    rw [← Real.exp_add]
    exact congr_arg (fun x => 8 * Real.exp x) (by ring)
  calc Real.exp (-(Real.pi * τ.im / 4)) *
        ‖jacobiTheta₂ (τ / 2) τ - 2 - 2 * Complex.exp (2 * Real.pi * Complex.I * τ)‖
      ≤ Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-6 * Real.pi * τ.im)) :=
        mul_le_mul_of_nonneg_left h_tail h_exp_nn
    _ = 8 * Real.exp (-(25 * Real.pi * τ.im / 4)) := h_combine

/-- **Three-term leading bound for `θ₂`.** For `τ.im ≥ 1`,
`‖θ₂(τ) − 2·exp(πi τ/4)·(1 + exp(2πi τ) + exp(6πi τ))‖ ≤ 8·exp(−49π·τ.im/4)`.
Follows from `jacobiTheta₂_half_sub_three_term_norm_le_of_im_ge_one`
and `θ₂(τ) = exp(πi τ/4) · jacobiTheta₂(τ/2, τ)`. -/
theorem theta2_norm_sub_three_term_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta2 τ - 2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
        (1 + Complex.exp (2 * Real.pi * Complex.I * τ) +
          Complex.exp (6 * Real.pi * Complex.I * τ))‖ ≤
      8 * Real.exp (-(49 * Real.pi * τ.im / 4)) := by
  unfold theta2
  have h_factor :
      Complex.exp (Real.pi * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ -
        2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
          (1 + Complex.exp (2 * Real.pi * Complex.I * τ) +
            Complex.exp (6 * Real.pi * Complex.I * τ)) =
      Complex.exp (Real.pi * Complex.I * τ / 4) *
        (jacobiTheta₂ (τ / 2) τ - 2 -
          2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
          2 * Complex.exp (6 * Real.pi * Complex.I * τ)) := by
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
  have h_tail := jacobiTheta₂_half_sub_three_term_norm_le_of_im_ge_one hτ
  have h_exp_nn : 0 ≤ Real.exp (-(Real.pi * τ.im / 4)) := (Real.exp_pos _).le
  have h_combine :
      Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-12 * Real.pi * τ.im)) =
      8 * Real.exp (-(49 * Real.pi * τ.im / 4)) := by
    rw [show (Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-12 * Real.pi * τ.im)) : ℝ) =
        8 * (Real.exp (-(Real.pi * τ.im / 4)) * Real.exp (-12 * Real.pi * τ.im)) from by ring]
    rw [← Real.exp_add]
    exact congr_arg (fun x => 8 * Real.exp x) (by ring)
  calc Real.exp (-(Real.pi * τ.im / 4)) *
        ‖jacobiTheta₂ (τ / 2) τ - 2 -
          2 * Complex.exp (2 * Real.pi * Complex.I * τ) -
          2 * Complex.exp (6 * Real.pi * Complex.I * τ)‖
      ≤ Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-12 * Real.pi * τ.im)) :=
        mul_le_mul_of_nonneg_left h_tail h_exp_nn
    _ = 8 * Real.exp (-(49 * Real.pi * τ.im / 4)) := h_combine

/-- **Two-term leading bound for `λ`.** For `τ.im ≥ 1`,
`‖λ(τ) − 16·exp(πi τ) + 128·exp(2πi τ)‖ ≤ K·exp(−3π·τ.im)` with
explicit constant `K = 8192`. Derives from
`theta2_norm_sub_two_term_le_of_im_ge_one` and
`theta3_sub_one_minus_2q_norm_le_of_im_ge_one` via the algebraic
expansion `(θ₂/θ₃)⁴ = 16q · (1 + r₂)⁴ · (1 + r₃)⁻⁴` (where
`r₂, r₃` are the second-order corrections of `θ₂, θ₃`), with two
applications of the geometric-series expansion `(1 + x)⁻¹ = 1 − x + O(x²)`.

This is the load-bearing q²-correction lemma needed for the
cusp-1 sign control in `modularLambdaH_cusp_one_im_nonneg_nbhd_in_F`:
the `−128q²` coefficient is what makes `Im(δ_λ)` strictly
non-positive uniformly on `F^o`-shifted neighbourhoods of `0`. -/
theorem modularLambdaH_norm_sub_two_term_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ) +
        128 * Complex.exp (2 * Real.pi * Complex.I * τ)‖ ≤
      8192 * Real.exp (-3 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- Setup: q := exp(πi τ), Q2 := exp(2πi τ).
  set q : ℂ := Complex.exp (Real.pi * Complex.I * τ) with hq_def
  set Q2 : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ) with hQ2_def
  -- rq := exp(-π τ.im). ‖q‖ = rq, ‖Q2‖ = rq² ≤ rq.
  set rq : ℝ := Real.exp (-Real.pi * τ.im) with hrq_def
  have hrq_pos : 0 < rq := Real.exp_pos _
  have hrq_nn : 0 ≤ rq := hrq_pos.le
  have hq_norm : ‖q‖ = rq := by
    rw [hq_def, Complex.norm_exp, hrq_def]
    congr 1
    have h_eq : (Real.pi * Complex.I * τ : ℂ) = ((Real.pi : ℝ) : ℂ) * (Complex.I * τ) := by
      ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
  have hQ2_eq_q_sq : Q2 = q^2 := by
    rw [hQ2_def, hq_def, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hQ2_norm : ‖Q2‖ = rq^2 := by rw [hQ2_eq_q_sq, norm_pow, hq_norm]
  -- exp(π) > 16, so rq < 1/16.
  have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_exp3_gt_16 : (16 : ℝ) < Real.exp 3 := by
    have h_eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
    rw [h_eq]; nlinarith [h_e_gt, Real.exp_pos (1 : ℝ)]
  have h_exp_pi_gt_16 : (16 : ℝ) < Real.exp Real.pi :=
    h_exp3_gt_16.trans_le (Real.exp_le_exp.mpr Real.pi_gt_three.le)
  have hrq_le : rq ≤ Real.exp (-Real.pi) := by
    rw [hrq_def]; apply Real.exp_le_exp.mpr; nlinarith
  have h_exp_neg_pi_lt : Real.exp (-Real.pi) < 1/16 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/16),
        show (1/16 : ℝ)⁻¹ = 16 from by norm_num]
    exact h_exp_pi_gt_16
  have hrq_lt : rq < 1/16 := lt_of_le_of_lt hrq_le h_exp_neg_pi_lt
  have hrq_lt_one : rq < 1 := by linarith
  have hrq3_eq : rq^3 = Real.exp (-3 * Real.pi * τ.im) := by
    rw [hrq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- A := 2 exp(πi τ/4); A⁴ = 16 q; ‖A⁴‖ = 16 rq.
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
    rw [h_re]
    simp
  have hA_pow_norm : ‖A^4‖ = 16 * rq := by
    rw [hA_pow, norm_mul, hq_norm]; simp
  have hA_norm_pos : 0 < ‖A‖ := by rw [hA_norm]; positivity
  have hA_ne : A ≠ 0 := norm_ne_zero_iff.mp hA_norm_pos.ne'
  -- r₂' and r₃' bounds via two-term theta lemmas.
  set r₂' : ℂ := (theta2 τ - A * (1 + Q2)) / A with hr2_def
  set r₃' : ℂ := theta3 τ - 1 - 2 * q with hr3_def
  have h_th2_sub := theta2_norm_sub_two_term_le_of_im_ge_one hτ
  have h_unfold_A1Q2 : 2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
      (1 + Complex.exp (2 * Real.pi * Complex.I * τ)) = A * (1 + Q2) := by
    rw [hA_def, hQ2_def]
  have hr2_bound : ‖r₂'‖ ≤ 4 * rq^6 := by
    rw [hr2_def, norm_div, hA_norm]
    have h_denom_pos : 0 < 2 * Real.exp (-(Real.pi * τ.im / 4)) := by positivity
    rw [div_le_iff₀ h_denom_pos]
    have hrq6_eq : rq^6 = Real.exp (-(6 * Real.pi * τ.im)) := by
      rw [hrq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h_target_eq : 4 * rq^6 * (2 * Real.exp (-(Real.pi * τ.im / 4))) =
        8 * Real.exp (-(25 * Real.pi * τ.im / 4)) := by
      rw [hrq6_eq]
      rw [show (4 * Real.exp (-(6 * Real.pi * τ.im)) *
          (2 * Real.exp (-(Real.pi * τ.im / 4))) : ℝ) =
          8 * (Real.exp (-(6 * Real.pi * τ.im)) * Real.exp (-(Real.pi * τ.im / 4))) from by ring]
      rw [← Real.exp_add]
      exact congr_arg (fun x => 8 * Real.exp x) (by ring)
    rw [h_target_eq, ← h_unfold_A1Q2]
    exact h_th2_sub
  have hr3_bound : ‖r₃'‖ ≤ 4 * rq^4 := by
    rw [hr3_def, hq_def]
    have hrq4_eq : rq^4 = Real.exp (-4 * Real.pi * τ.im) := by
      rw [hrq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hrq4_eq]
    exact theta3_sub_one_minus_2q_norm_le_of_im_ge_one hτ
  -- Loose bounds: ‖r₂'‖ ≤ rq², ‖r₃'‖ ≤ rq (using rq < 1/16).
  -- 4 rq^6 ≤ rq²: need 4 rq^4 ≤ 1, i.e., rq ≤ (1/4)^{1/4} ≈ 0.707. We have rq < 1/16. ✓
  have hrq2_pos : 0 < rq^2 := by positivity
  have hr2_bound_loose : ‖r₂'‖ ≤ rq^2 := by
    refine hr2_bound.trans ?_
    -- 4 rq^6 ≤ rq^2 ⟺ 4 rq^4 ≤ 1. We have rq < 1/16, so rq^4 < 1/65536 < 1/4.
    have h_rq4_lt : rq^4 < 1/4 := by
      have : rq^4 < (1/16)^4 := pow_lt_pow_left₀ hrq_lt hrq_nn (by norm_num)
      have h_pow : ((1/16)^4 : ℝ) ≤ 1/4 := by norm_num
      linarith
    have : 4 * rq^6 ≤ rq^2 := by
      have h_rq6 : rq^6 = rq^4 * rq^2 := by ring
      rw [h_rq6]
      have h_ineq : 4 * rq^4 ≤ 1 := by linarith
      calc 4 * (rq^4 * rq^2) = (4 * rq^4) * rq^2 := by ring
        _ ≤ 1 * rq^2 := mul_le_mul_of_nonneg_right h_ineq hrq2_pos.le
        _ = rq^2 := by ring
    linarith
  have hr3_bound_loose : ‖r₃'‖ ≤ rq := by
    refine hr3_bound.trans ?_
    -- 4 rq^4 ≤ rq ⟺ 4 rq^3 ≤ 1.
    have h_rq3_lt : rq^3 < 1/4 := by
      have : rq^3 < (1/16)^3 := pow_lt_pow_left₀ hrq_lt hrq_nn (by norm_num)
      have h_pow : ((1/16 : ℝ))^3 ≤ 1/4 := by norm_num
      linarith
    have : 4 * rq^4 ≤ rq := by
      have h_rq4 : rq^4 = rq^3 * rq := by ring
      rw [h_rq4]
      have h_ineq : 4 * rq^3 ≤ 1 := by linarith
      calc 4 * (rq^3 * rq) = (4 * rq^3) * rq := by ring
        _ ≤ 1 * rq := mul_le_mul_of_nonneg_right h_ineq hrq_nn
        _ = rq := by ring
    linarith
  -- θ₂ = A(1 + Q2 + r₂'); θ₃ = 1 + 2q + r₃'.
  have h_th2_eq : theta2 τ = A * (1 + Q2 + r₂') := by
    rw [hr2_def]; field_simp; ring
  have h_th3_eq : theta3 τ = 1 + 2 * q + r₃' := by rw [hr3_def]; ring
  -- ‖θ₃‖ ≥ 1/2, so 1 + 2q + r₃' ≠ 0 and ‖1+2q+r₃'‖ ≥ 1/2.
  have h_th3_norm_ge := theta3_norm_ge_half_of_im_ge_one hτ
  have h_th3_norm_ge' : (1/2 : ℝ) ≤ ‖(1 + 2*q + r₃' : ℂ)‖ := by
    rw [← h_th3_eq]; exact h_th3_norm_ge
  have h_th3_pos : 0 < ‖(1 + 2*q + r₃' : ℂ)‖ :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) h_th3_norm_ge'
  have h_th3_ne : (1 + 2*q + r₃' : ℂ) ≠ 0 := norm_ne_zero_iff.mp h_th3_pos.ne'
  -- λ = A⁴ · ((1+Q2+r₂')/(1+2q+r₃'))⁴.
  have h_lambda_eq : modularLambdaH τ = A^4 * ((1 + Q2 + r₂') / (1 + 2*q + r₃'))^4 := by
    unfold modularLambdaH
    rw [h_th2_eq, h_th3_eq, mul_pow, div_pow]
    ring
  rw [h_lambda_eq]
  -- Rewrite 16 q = A^4 and 128 Q2 = 8 q · A^4.
  rw [show (16 * Complex.exp (Real.pi * Complex.I * τ) : ℂ) = A^4 from hA_pow.symm]
  have h_128_eq : (128 * Complex.exp (2 * Real.pi * Complex.I * τ) : ℂ) = 8 * q * A^4 := by
    rw [show Complex.exp (2 * Real.pi * Complex.I * τ) = Q2 from rfl]
    rw [hA_pow, hQ2_eq_q_sq]; ring
  rw [h_128_eq]
  -- Goal: ‖A^4 * ratio^4 - A^4 + 8 q · A^4‖ ≤ ...
  -- = ‖A^4 · (ratio^4 - 1 + 8 q)‖.
  rw [show (A^4 * ((1 + Q2 + r₂') / (1 + 2*q + r₃'))^4 - A^4 + 8 * q * A^4 : ℂ) =
      A^4 * (((1 + Q2 + r₂') / (1 + 2*q + r₃'))^4 - 1 + 8 * q) from by ring]
  rw [norm_mul, hA_pow_norm]
  -- Set v := (1+Q2+r₂')/(1+2q+r₃') - 1.
  set v : ℂ := (1 + Q2 + r₂') / (1 + 2*q + r₃') - 1 with hv_def
  have hv_add : (1 + Q2 + r₂') / (1 + 2*q + r₃') = 1 + v := by rw [hv_def]; ring
  rw [hv_add]
  -- (1+v)^4 - 1 + 8 q = 4 (v + 2 q) + 6 v² + 4 v³ + v⁴.
  rw [show ((1 + v)^4 - 1 + 8 * q : ℂ) = 4 * (v + 2*q) + 6 * v^2 + 4 * v^3 + v^4 from by ring]
  -- v + 2q identity: v + 2q = (Q2 + r₂' - 2q - r₃' + 2q(1+2q+r₃'))/(1+2q+r₃')
  --                       = (Q2 + r₂' - r₃' + 4q² + 2q r₃')/(1+2q+r₃').
  -- Substituting Q2 = q²: numerator = q² + 4q² + r₂' - r₃' + 2q r₃' = 5q² + r₂' - r₃' + 2q r₃'.
  -- But this uses Q2 = q². Since we want a CLEAN identity, let's keep Q2 generic.
  have hv_plus_2q_eq : v + 2*q =
      (Q2 + r₂' - r₃' + 4*q^2 + 2*q*r₃') / (1 + 2*q + r₃') := by
    rw [hv_def]
    field_simp
    ring
  -- |Q2| ≤ rq²; |r₂'| ≤ rq²; |r₃'| ≤ rq²; |4q²| = 4 rq²; |2q r₃'| ≤ 2 rq².
  -- We have ‖r₃'‖ ≤ 4 rq^4 ≤ rq² (since 4 rq² ≤ 1 for rq ≤ 1/2).
  have hr3_bound_better : ‖r₃'‖ ≤ rq^2 := by
    refine hr3_bound.trans ?_
    -- 4 rq^4 ≤ rq² ⟺ 4 rq² ≤ 1. We have rq < 1/16, so rq² < 1/256 < 1/4.
    have h_rq2_lt : rq^2 < 1/4 := by
      have : rq^2 < (1/16)^2 := pow_lt_pow_left₀ hrq_lt hrq_nn (by norm_num)
      have h_pow : ((1/16 : ℝ))^2 ≤ 1/4 := by norm_num
      linarith
    have : 4 * rq^4 ≤ rq^2 := by
      have h_rq4 : rq^4 = rq^2 * rq^2 := by ring
      rw [h_rq4]
      have h_ineq : 4 * rq^2 ≤ 1 := by linarith
      calc 4 * (rq^2 * rq^2) = (4 * rq^2) * rq^2 := by ring
        _ ≤ 1 * rq^2 := mul_le_mul_of_nonneg_right h_ineq hrq2_pos.le
        _ = rq^2 := by ring
    linarith
  -- |2q r₃'| ≤ 2 rq · rq² ≤ rq² for rq ≤ 1/2.
  -- Actually 2 rq · rq² = 2 rq³. For rq ≤ 1/2: 2 rq³ ≤ rq² (since 2 rq ≤ 1).
  -- So |2q r₃'| ≤ 2 rq · rq² ≤ rq² (since 2 rq ≤ 2/16 = 1/8 ≤ 1).
  -- Therefore: ‖num‖ ≤ rq² + rq² + rq² + 4 rq² + rq² = 8 rq².
  have h_num_bound : ‖(Q2 + r₂' - r₃' + 4*q^2 + 2*q*r₃' : ℂ)‖ ≤ 8 * rq^2 := by
    have h1 : ‖(Q2 + r₂' - r₃' + 4*q^2 + 2*q*r₃' : ℂ)‖ ≤
        ‖Q2‖ + ‖r₂'‖ + ‖r₃'‖ + ‖(4 * q^2 : ℂ)‖ + ‖(2 * q * r₃' : ℂ)‖ := by
      have h_step1 := norm_add_le (Q2 + r₂' - r₃' + 4*q^2) (2 * q * r₃')
      have h_step2 := norm_add_le (Q2 + r₂' - r₃') (4*q^2)
      have h_step3 := norm_sub_le (Q2 + r₂') r₃'
      have h_step4 := norm_add_le Q2 r₂'
      have h_rewrite_a : Q2 + r₂' - r₃' + 4 * q^2 + 2 * q * r₃' =
          (Q2 + r₂' - r₃' + 4 * q^2) + 2 * q * r₃' := by ring
      have h_rewrite_b : Q2 + r₂' - r₃' + 4 * q^2 =
          (Q2 + r₂' - r₃') + 4 * q^2 := by ring
      have h_rewrite_c : Q2 + r₂' - r₃' = (Q2 + r₂') - r₃' := by ring
      rw [h_rewrite_a]
      refine h_step1.trans ?_
      rw [h_rewrite_b] at h_step2 ⊢
      have h_step2' := h_step2
      have h_combine : ‖Q2 + r₂' - r₃' + 4 * q^2‖ + ‖2 * q * r₃'‖ ≤
          ‖Q2 + r₂' - r₃'‖ + ‖(4 * q^2 : ℂ)‖ + ‖2 * q * r₃'‖ := by linarith
      refine h_combine.trans ?_
      rw [h_rewrite_c] at h_step3
      have h_step3' : ‖(Q2 + r₂') - r₃'‖ ≤ ‖Q2 + r₂'‖ + ‖r₃'‖ := norm_sub_le _ _
      have h_combine2 : ‖Q2 + r₂' - r₃'‖ ≤ ‖Q2 + r₂'‖ + ‖r₃'‖ := by
        rw [h_rewrite_c]; exact h_step3'
      have h_combine3 : ‖Q2 + r₂'‖ ≤ ‖Q2‖ + ‖r₂'‖ := h_step4
      linarith
    have h_4q2 : ‖(4 * q^2 : ℂ)‖ = 4 * rq^2 := by
      rw [show ((4 * q^2 : ℂ)) = (((4 : ℝ) : ℂ)) * q^2 from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, norm_pow, hq_norm]
      simp
    have h_2qr3 : ‖(2 * q * r₃' : ℂ)‖ ≤ 2 * rq * rq^2 := by
      rw [norm_mul, norm_mul, hq_norm, Complex.norm_ofNat]
      have h_step : (2 : ℝ) * rq * ‖r₃'‖ ≤ 2 * rq * rq^2 :=
        mul_le_mul_of_nonneg_left hr3_bound_better (by positivity)
      linarith
    -- Bound 2*rq*rq^2 by rq^2 (since 2*rq ≤ 1/8 < 1).
    have h_2rq_le : (2 : ℝ) * rq ≤ 1 := by linarith
    have h_2qr3_loose : ‖(2 * q * r₃' : ℂ)‖ ≤ rq^2 := by
      refine h_2qr3.trans ?_
      have h_step : (2 : ℝ) * rq * rq^2 ≤ 1 * rq^2 :=
        mul_le_mul_of_nonneg_right h_2rq_le hrq2_pos.le
      linarith
    rw [h_4q2] at h1
    linarith [hQ2_norm.le, hr2_bound_loose, hr3_bound_better, h1, h_2qr3_loose]
  -- |1 + 2q + r₃'| ≥ 1/2 from h_th3_norm_ge'.
  -- |v + 2q| = ‖num‖/‖1+2q+r₃'‖ ≤ (8 rq²)/(1/2) = 16 rq².
  have hv_plus_2q_bound : ‖v + 2*q‖ ≤ 16 * rq^2 := by
    rw [hv_plus_2q_eq, norm_div]
    rw [div_le_iff₀ h_th3_pos]
    have h1 : 16 * rq^2 * ‖(1 + 2*q + r₃' : ℂ)‖ ≥ 16 * rq^2 * (1/2) := by
      apply mul_le_mul_of_nonneg_left h_th3_norm_ge' (by positivity)
    have h2 : 16 * rq^2 * (1/2 : ℝ) = 8 * rq^2 := by ring
    linarith [h_num_bound]
  -- |v| ≤ 6 rq (from |Q-R|/|1+R|).
  -- v = (Q2 + r₂' - 2q - r₃')/(1+2q+r₃').
  have hv_alt : v = (Q2 + r₂' - 2*q - r₃') / (1 + 2*q + r₃') := by
    rw [hv_def]; field_simp; ring
  have hv_bound : ‖v‖ ≤ 6 * rq := by
    rw [hv_alt, norm_div]
    rw [div_le_iff₀ h_th3_pos]
    -- ‖Q2 + r₂' - 2q - r₃'‖ ≤ rq² + rq² + 2 rq + rq² = 2 rq + 3 rq² ≤ 3 rq.
    have h_num : ‖(Q2 + r₂' - 2*q - r₃' : ℂ)‖ ≤ rq^2 + rq^2 + 2 * rq + rq^2 := by
      have h1 : ‖(Q2 + r₂' - 2*q - r₃' : ℂ)‖ ≤
          ‖Q2‖ + ‖r₂'‖ + ‖(2 * q : ℂ)‖ + ‖r₃'‖ := by
        have h_step1 := norm_sub_le (Q2 + r₂' - 2*q) r₃'
        have h_step2 := norm_sub_le (Q2 + r₂') (2*q)
        have h_step3 := norm_add_le Q2 r₂'
        have h_rewrite : Q2 + r₂' - 2 * q - r₃' = (Q2 + r₂' - 2 * q) - r₃' := by ring
        rw [h_rewrite]
        have h_rewrite_b : Q2 + r₂' - 2 * q = (Q2 + r₂') - 2 * q := by ring
        rw [h_rewrite_b] at h_step2
        linarith
      have h_2q : ‖(2 * q : ℂ)‖ = 2 * rq := by
        rw [show ((2 * q : ℂ)) = (((2 : ℝ) : ℂ)) * q from by push_cast; ring]
        rw [norm_mul, Complex.norm_real, hq_norm]
        simp
      rw [h_2q] at h1
      linarith [hQ2_norm.le, hr2_bound_loose, hr3_bound_better]
    have h_num_simp : rq^2 + rq^2 + 2 * rq + rq^2 = 2 * rq + 3 * rq^2 := by ring
    rw [h_num_simp] at h_num
    -- 2 rq + 3 rq² ≤ 3 rq (since 3 rq² ≤ rq for rq ≤ 1/3, true).
    have h_rq2_le : 3 * rq^2 ≤ rq := by
      have : 3 * rq ≤ 1 := by linarith
      calc 3 * rq^2 = (3 * rq) * rq := by ring
        _ ≤ 1 * rq := mul_le_mul_of_nonneg_right this hrq_nn
        _ = rq := by ring
    have h_num_loose : ‖(Q2 + r₂' - 2*q - r₃' : ℂ)‖ ≤ 3 * rq := by linarith
    -- Now ‖num‖ ≤ 3 rq, ‖1+R‖ ≥ 1/2, so ‖v‖ ≤ 6 rq.
    have h1 : 6 * rq * ‖(1 + 2*q + r₃' : ℂ)‖ ≥ 6 * rq * (1/2) := by
      apply mul_le_mul_of_nonneg_left h_th3_norm_ge' (by positivity)
    linarith
  -- Now bound the bracket: ‖4(v+2q) + 6v² + 4v³ + v⁴‖.
  have hv_sq : ‖v‖^2 ≤ 36 * rq^2 := by
    have := pow_le_pow_left₀ (norm_nonneg v) hv_bound 2
    have h_sq : (6 * rq)^2 = 36 * rq^2 := by ring
    linarith [this, h_sq.le]
  have hv_cube : ‖v‖^3 ≤ 216 * rq^3 := by
    have := pow_le_pow_left₀ (norm_nonneg v) hv_bound 3
    have h_cube : (6 * rq)^3 = 216 * rq^3 := by ring
    linarith [this, h_cube.le]
  have hv_fourth : ‖v‖^4 ≤ 1296 * rq^4 := by
    have := pow_le_pow_left₀ (norm_nonneg v) hv_bound 4
    have h_fourth : (6 * rq)^4 = 1296 * rq^4 := by ring
    linarith [this, h_fourth.le]
  have h_4v_bound : ‖(4 * (v + 2 * q) : ℂ)‖ ≤ 4 * (16 * rq^2) := by
    rw [norm_mul, Complex.norm_ofNat]
    have h_step : (4 : ℝ) * ‖v + 2 * q‖ ≤ 4 * (16 * rq^2) :=
      mul_le_mul_of_nonneg_left hv_plus_2q_bound (by norm_num)
    linarith
  have h_6v2_bound : ‖(6 * v^2 : ℂ)‖ ≤ 6 * (36 * rq^2) := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
    have h_step : (6 : ℝ) * ‖v‖^2 ≤ 6 * (36 * rq^2) :=
      mul_le_mul_of_nonneg_left hv_sq (by norm_num)
    linarith
  have h_4v3_bound : ‖(4 * v^3 : ℂ)‖ ≤ 4 * (216 * rq^3) := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
    have h_step : (4 : ℝ) * ‖v‖^3 ≤ 4 * (216 * rq^3) :=
      mul_le_mul_of_nonneg_left hv_cube (by norm_num)
    linarith
  have h_v4_bound : ‖(v^4 : ℂ)‖ ≤ 1296 * rq^4 := by
    rw [norm_pow]; exact hv_fourth
  -- Combine: ‖bracket‖ ≤ 64 rq² + 216 rq² + 864 rq³ + 1296 rq⁴.
  have h_bracket_bound : ‖(4 * (v + 2*q) + 6 * v^2 + 4 * v^3 + v^4 : ℂ)‖ ≤
      64 * rq^2 + 216 * rq^2 + 864 * rq^3 + 1296 * rq^4 := by
    have h1 := norm_add_le ((4 * (v + 2*q) + 6 * v^2 + 4 * v^3 : ℂ)) ((v^4 : ℂ))
    have h2 := norm_add_le ((4 * (v + 2*q) + 6 * v^2 : ℂ)) ((4 * v^3 : ℂ))
    have h3 := norm_add_le ((4 * (v + 2*q) : ℂ)) ((6 * v^2 : ℂ))
    -- ‖4(v+2q) + 6v² + 4v³ + v⁴‖ ≤ ‖4(v+2q)‖ + ‖6v²‖ + ‖4v³‖ + ‖v⁴‖.
    have h_chain : ‖(4 * (v + 2*q) + 6 * v^2 + 4 * v^3 + v^4 : ℂ)‖ ≤
        ‖(4 * (v + 2*q) : ℂ)‖ + ‖(6 * v^2 : ℂ)‖ + ‖(4 * v^3 : ℂ)‖ + ‖(v^4 : ℂ)‖ := by linarith
    linarith [h_4v_bound, h_6v2_bound, h_4v3_bound, h_v4_bound, h_chain]
  -- Now want: 16 rq · (bracket bound) ≤ 8192 · exp(-3π τ.im) = 8192 rq³.
  -- 64 rq² + 216 rq² + 864 rq³ + 1296 rq⁴
  --   ≤ 280 rq² + 864 rq³ + 1296 rq⁴
  -- For rq ≤ 1/16: rq³ ≤ rq²/16, rq⁴ ≤ rq²/256.
  -- 864 rq³ ≤ 864 rq² /16 = 54 rq². 1296 rq⁴ ≤ 1296 rq²/256 ≈ 5 rq².
  -- Sum ≤ 280 + 54 + 5 = 339 rq². Use 400 rq² for buffer.
  -- 16 rq · 400 rq² = 6400 rq³ ≤ 8192 rq³. ✓
  have hrq3_le_rq2 : rq^3 ≤ rq^2 / 16 := by
    -- rq^3 = rq^2 * rq ≤ rq^2 * (1/16)
    have h1 : rq^3 = rq^2 * rq := by ring
    rw [h1]
    have h2 : rq^2 * rq ≤ rq^2 * (1/16) :=
      mul_le_mul_of_nonneg_left (by linarith : rq ≤ 1/16) hrq2_pos.le
    linarith
  have hrq4_le_rq2 : rq^4 ≤ rq^2 / 256 := by
    -- rq^4 = rq^2 * rq^2 ≤ rq^2 * (1/256)
    have h1 : rq^4 = rq^2 * rq^2 := by ring
    rw [h1]
    have h_rq2_le : rq^2 ≤ 1/256 := by
      have : rq^2 < (1/16)^2 := pow_lt_pow_left₀ hrq_lt hrq_nn (by norm_num)
      have h_pow : ((1/16 : ℝ))^2 = 1/256 := by norm_num
      linarith
    have h2 : rq^2 * rq^2 ≤ rq^2 * (1/256) :=
      mul_le_mul_of_nonneg_left h_rq2_le hrq2_pos.le
    linarith
  have h_final_bound : 64 * rq^2 + 216 * rq^2 + 864 * rq^3 + 1296 * rq^4 ≤ 400 * rq^2 := by
    have h1 : 864 * rq^3 ≤ 864 * (rq^2 / 16) :=
      mul_le_mul_of_nonneg_left hrq3_le_rq2 (by norm_num)
    have h2 : 1296 * rq^4 ≤ 1296 * (rq^2 / 256) :=
      mul_le_mul_of_nonneg_left hrq4_le_rq2 (by norm_num)
    have h_simp1 : 864 * (rq^2 / 16) = 54 * rq^2 := by ring
    rw [h_simp1] at h1
    have h_const : (1296 : ℝ) / 256 ≤ 6 := by norm_num
    have h_step : 1296 * (rq^2 / 256) ≤ 6 * rq^2 := by
      calc 1296 * (rq^2 / 256) = (1296 / 256) * rq^2 := by ring
        _ ≤ 6 * rq^2 := mul_le_mul_of_nonneg_right h_const hrq2_pos.le
    have h2' : 1296 * rq^4 ≤ 6 * rq^2 := h2.trans h_step
    linarith
  -- Combine: 16 rq · (bracket norm) ≤ 16 rq · 400 rq² = 6400 rq³ ≤ 8192 rq³.
  have h_step : (16 * rq) * ‖(4 * (v + 2*q) + 6 * v^2 + 4 * v^3 + v^4 : ℂ)‖ ≤
      (16 * rq) * (400 * rq^2) := by
    apply mul_le_mul_of_nonneg_left
    · linarith [h_bracket_bound, h_final_bound]
    · positivity
  have h_simp : (16 : ℝ) * rq * (400 * rq^2) = 6400 * rq^3 := by ring
  rw [h_simp] at h_step
  have h_final : 6400 * rq^3 ≤ 8192 * Real.exp (-3 * Real.pi * τ.im) := by
    rw [← hrq3_eq]
    have h_pos : 0 ≤ rq^3 := by positivity
    linarith
  linarith

/-- Pure ring identity used in the three-term `λ` bound. With
`s := v + 2q − 5q²`, the bracket
`(1 + v)⁴ − 1 + 8q − 44q²` decomposes into a `−120q³` leading correction
plus terms quadratic and higher in `s` and `v`. -/
theorem modularLambda_three_term_bracket_identity (v q : ℂ) :
    (1 + v)^4 - 1 + 8 * q - 44 * q^2 =
      -120 * q^3 + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2) +
        6 * (v + 2*q - 5*q^2)^2 + 150 * q^4 + 4 * v^3 + v^4 := by
  ring

/-- Norm bound on `v := (1 + q² + q⁶ + r₂') / D − 1` with
`D := 1 + 2q + 2q⁴ + r₃'`. Used in the three-term `λ` bound. -/
theorem modularLambda_three_term_v_bound (q r₂' r₃' : ℂ) (rq : ℝ)
    (hq_norm : ‖q‖ = rq) (hrq_pos : 0 < rq) (hrq_lt : rq < 1 / 16)
    (hr2_loose : ‖r₂'‖ ≤ rq ^ 3) (hr3_loose : ‖r₃'‖ ≤ rq ^ 3)
    (hD_norm : (1 / 2 : ℝ) ≤ ‖(1 + 2 * q + 2 * q ^ 4 + r₃' : ℂ)‖) :
    ‖(1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') - 1‖ ≤ 6 * rq := by
  have hrq_nn : 0 ≤ rq := hrq_pos.le
  have hrq_le_one : rq ≤ 1 := by linarith
  have hrq2_pos : 0 < rq^2 := by positivity
  have hD_pos : 0 < ‖(1 + 2*q + 2*q^4 + r₃' : ℂ)‖ := by linarith
  have hD_ne : (1 + 2*q + 2*q^4 + r₃' : ℂ) ≠ 0 := norm_ne_zero_iff.mp hD_pos.ne'
  -- Rewrite v as num/D.
  have h_v_eq : (1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') - 1 =
      (q^2 + q^6 + r₂' - 2*q - 2*q^4 - r₃') / (1 + 2*q + 2*q^4 + r₃') := by
    rw [div_sub_one hD_ne]
    congr 1; ring
  rw [h_v_eq, norm_div]
  rw [div_le_iff₀ hD_pos]
  -- Goal: ‖num‖ ≤ 6 * rq * ‖D‖.
  have h_q2_norm : ‖q^2‖ = rq^2 := by rw [norm_pow, hq_norm]
  have h_q4_norm : ‖q^4‖ = rq^4 := by rw [norm_pow, hq_norm]
  have h_q6_norm : ‖q^6‖ = rq^6 := by rw [norm_pow, hq_norm]
  have h_2q_norm : ‖((2 : ℂ) * q)‖ = 2 * rq := by
    rw [show ((2 * q : ℂ)) = (((2 : ℝ) : ℂ)) * q from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, hq_norm]; simp
  have h_2q4_norm : ‖((2 : ℂ) * q^4)‖ = 2 * rq^4 := by
    rw [show ((2 * q^4 : ℂ)) = (((2 : ℝ) : ℂ)) * q^4 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q4_norm]; simp
  -- Triangle inequality.
  have h_eq : q^2 + q^6 + r₂' - 2*q - 2*q^4 - r₃' =
      (((q^2 + q^6 + r₂') - 2*q) - 2*q^4) - r₃' := by ring
  rw [h_eq]
  have h_t1 := norm_sub_le (((q^2 + q^6 + r₂') - 2*q) - 2*q^4) r₃'
  have h_t2 := norm_sub_le ((q^2 + q^6 + r₂') - 2*q) (2*q^4)
  have h_t3 := norm_sub_le (q^2 + q^6 + r₂') (2*q)
  have h_t4 := norm_add_le (q^2 + q^6) r₂'
  have h_t5 := norm_add_le (q^2) (q^6)
  -- Power ladder.
  have h_rq3_le_rq2 : rq^3 ≤ rq^2 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq4_le_rq2 : rq^4 ≤ rq^2 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq6_le_rq2 : rq^6 ≤ rq^2 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq2_le_rq16 : rq^2 ≤ rq * (1/16) := by
    have h_eq2 : rq^2 = rq * rq := by ring
    rw [h_eq2]; exact mul_le_mul_of_nonneg_left hrq_lt.le hrq_nn
  -- Bound LHS ≤ 3 rq.
  have h_lhs_le : ‖(((q^2 + q^6 + r₂') - 2*q) - 2*q^4) - r₃'‖ ≤ 3 * rq := by
    have h_chain : ‖(((q^2 + q^6 + r₂') - 2*q) - 2*q^4) - r₃'‖ ≤
        rq^2 + rq^6 + rq^3 + 2*rq + 2*rq^4 + rq^3 := by
      linarith [h_t1, h_t2, h_t3, h_t4, h_t5, h_q2_norm.le, h_q6_norm.le,
                hr2_loose, hr3_loose, h_2q_norm.le, h_2q4_norm.le]
    -- rq² + rq⁶ + 2*rq³ + 2*rq⁴ ≤ 6 rq² ≤ 6·rq/16 ≤ rq.
    linarith [h_chain, h_rq3_le_rq2, h_rq4_le_rq2, h_rq6_le_rq2, h_rq2_le_rq16]
  -- 6 rq · ‖D‖ ≥ 6 rq · (1/2) = 3 rq.
  have h_rhs_ge : 3 * rq ≤ 6 * rq * ‖(1 + 2*q + 2*q^4 + r₃' : ℂ)‖ := by
    have h_step : 6 * rq * (1/2 : ℝ) ≤ 6 * rq * ‖(1 + 2*q + 2*q^4 + r₃' : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hD_norm (by positivity)
    linarith
  linarith

/-- Norm bound on `s := v + 2q − 5q²` for the three-term `λ` setup. -/
theorem modularLambda_three_term_s_bound (q r₂' r₃' : ℂ) (rq : ℝ)
    (hq_norm : ‖q‖ = rq) (hrq_pos : 0 < rq) (hrq_lt : rq < 1 / 16)
    (hr2_loose : ‖r₂'‖ ≤ rq ^ 3) (hr3_loose : ‖r₃'‖ ≤ rq ^ 3)
    (hD_norm : (1 / 2 : ℝ) ≤ ‖(1 + 2 * q + 2 * q ^ 4 + r₃' : ℂ)‖) :
    ‖((1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') - 1) + 2*q - 5*q^2‖ ≤ 64 * rq^3 := by
  have hrq_nn : 0 ≤ rq := hrq_pos.le
  have hrq_le_one : rq ≤ 1 := by linarith
  have hrq2_pos : 0 < rq^2 := by positivity
  have hrq3_pos : 0 < rq^3 := by positivity
  have hD_pos : 0 < ‖(1 + 2*q + 2*q^4 + r₃' : ℂ)‖ := by linarith
  have hD_ne : (1 + 2*q + 2*q^4 + r₃' : ℂ) ≠ 0 := norm_ne_zero_iff.mp hD_pos.ne'
  -- s = num/D where num = -10q³ - 2q⁴ + 4q⁵ - 9q⁶ + r₂' - r₃'(1 - 2q + 5q²).
  have h_s_eq : ((1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') - 1) + 2*q - 5*q^2 =
      (-10*q^3 - 2*q^4 + 4*q^5 - 9*q^6 + r₂' - r₃' * (1 - 2*q + 5*q^2)) /
        (1 + 2*q + 2*q^4 + r₃') := by
    have h_lhs_mul : (((1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') - 1) + 2*q - 5*q^2) *
        (1 + 2*q + 2*q^4 + r₃') =
        (-10*q^3 - 2*q^4 + 4*q^5 - 9*q^6 + r₂' - r₃' * (1 - 2*q + 5*q^2)) := by
      have h_div_mul : (1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') *
          (1 + 2*q + 2*q^4 + r₃') = 1 + q^2 + q^6 + r₂' := div_mul_cancel₀ _ hD_ne
      have h_expand : (((1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') - 1) + 2*q - 5*q^2) *
          (1 + 2*q + 2*q^4 + r₃') =
          (1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') * (1 + 2*q + 2*q^4 + r₃') -
            (1 + 2*q + 2*q^4 + r₃') + 2*q * (1 + 2*q + 2*q^4 + r₃') -
            5*q^2 * (1 + 2*q + 2*q^4 + r₃') := by ring
      rw [h_expand, h_div_mul]
      ring
    rw [eq_div_iff hD_ne]
    exact h_lhs_mul
  rw [h_s_eq, norm_div]
  rw [div_le_iff₀ hD_pos]
  -- Goal: ‖num‖ ≤ 64 rq³ · ‖D‖.
  have h_q2_norm : ‖q^2‖ = rq^2 := by rw [norm_pow, hq_norm]
  have h_q3_norm : ‖q^3‖ = rq^3 := by rw [norm_pow, hq_norm]
  have h_q4_norm : ‖q^4‖ = rq^4 := by rw [norm_pow, hq_norm]
  have h_q5_norm : ‖q^5‖ = rq^5 := by rw [norm_pow, hq_norm]
  have h_q6_norm : ‖q^6‖ = rq^6 := by rw [norm_pow, hq_norm]
  have h_10q3_norm : ‖((10 : ℂ) * q^3)‖ = 10 * rq^3 := by
    rw [show ((10 * q^3 : ℂ)) = (((10 : ℝ) : ℂ)) * q^3 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q3_norm]; simp
  have h_2q4_norm : ‖((2 : ℂ) * q^4)‖ = 2 * rq^4 := by
    rw [show ((2 * q^4 : ℂ)) = (((2 : ℝ) : ℂ)) * q^4 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q4_norm]; simp
  have h_4q5_norm : ‖((4 : ℂ) * q^5)‖ = 4 * rq^5 := by
    rw [show ((4 * q^5 : ℂ)) = (((4 : ℝ) : ℂ)) * q^5 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q5_norm]; simp
  have h_9q6_norm : ‖((9 : ℂ) * q^6)‖ = 9 * rq^6 := by
    rw [show ((9 * q^6 : ℂ)) = (((9 : ℝ) : ℂ)) * q^6 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q6_norm]; simp
  -- ‖1 - 2q + 5q²‖ ≤ 2.
  have h_1_2q_5q2_le : ‖((1 : ℂ) - 2*q + 5*q^2)‖ ≤ 2 := by
    have h_5q2_norm : ‖((5 : ℂ) * q^2)‖ = 5 * rq^2 := by
      rw [show ((5 * q^2 : ℂ)) = (((5 : ℝ) : ℂ)) * q^2 from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, h_q2_norm]; simp
    have h_2q_norm : ‖((2 : ℂ) * q)‖ = 2 * rq := by
      rw [show ((2 * q : ℂ)) = (((2 : ℝ) : ℂ)) * q from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, hq_norm]; simp
    have h_1_norm : ‖((1 : ℂ))‖ = 1 := norm_one
    have h_add := norm_add_le ((1 : ℂ) - 2*q) (5*q^2)
    have h_sub := norm_sub_le ((1 : ℂ)) (2*q)
    have h_5rq2 : 5 * rq^2 ≤ 1/2 := by
      have h_rq2_le : rq^2 ≤ rq * (1/16) := by
        have h_eq2 : rq^2 = rq * rq := by ring
        rw [h_eq2]; exact mul_le_mul_of_nonneg_left hrq_lt.le hrq_nn
      have h_rq16 : rq * (1/16 : ℝ) ≤ (1/16) * (1/16) := by
        apply mul_le_mul_of_nonneg_right hrq_lt.le; norm_num
      have : rq^2 ≤ (1/256 : ℝ) := by
        have h_simp : (1/16 : ℝ) * (1/16) = 1/256 := by norm_num
        linarith
      linarith
    have h_2rq : 2 * rq ≤ 1/2 := by linarith
    linarith [h_add, h_sub, h_5q2_norm.le, h_2q_norm.le, h_5rq2, h_2rq, h_1_norm]
  -- ‖r₃' · (1 - 2q + 5q²)‖ ≤ 2 rq³.
  have h_r3_mul_le : ‖r₃' * (1 - 2*q + 5*q^2)‖ ≤ 2 * rq^3 := by
    rw [norm_mul]
    have h : ‖r₃'‖ * ‖((1 : ℂ) - 2*q + 5*q^2)‖ ≤ rq^3 * 2 :=
      mul_le_mul hr3_loose h_1_2q_5q2_le (norm_nonneg _) hrq3_pos.le
    linarith
  -- Triangle inequality.
  have h_eq : -10*q^3 - 2*q^4 + 4*q^5 - 9*q^6 + r₂' - r₃' * (1 - 2*q + 5*q^2) =
      (((((-(10*q^3)) - 2*q^4) + 4*q^5) - 9*q^6) + r₂') - r₃' * (1 - 2*q + 5*q^2) := by ring
  rw [h_eq]
  have h_t1 := norm_sub_le ((((((-(10*q^3)) - 2*q^4) + 4*q^5) - 9*q^6) + r₂'))
    (r₃' * (1 - 2*q + 5*q^2))
  have h_t2 := norm_add_le (((((-(10*q^3)) - 2*q^4) + 4*q^5) - 9*q^6)) r₂'
  have h_t3 := norm_sub_le ((((-(10*q^3)) - 2*q^4) + 4*q^5)) (9*q^6)
  have h_t4 := norm_add_le (((-(10*q^3)) - 2*q^4)) (4*q^5)
  have h_t5 := norm_sub_le (-(10*q^3)) (2*q^4)
  have h_neg10q3 : ‖(-((10 : ℂ) * q^3))‖ = 10 * rq^3 := by
    rw [norm_neg]; exact h_10q3_norm
  -- Power bounds.
  have h_rq4_le : rq^4 ≤ rq^3 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq5_le : rq^5 ≤ rq^3 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq6_le : rq^6 ≤ rq^3 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  -- Numerator bound: 10 + 2 + 4 + 9 + 1 + 2 = 28 rq³.
  have h_num_le : ‖(((((-(10*q^3)) - 2*q^4) + 4*q^5) - 9*q^6) + r₂') -
      r₃' * (1 - 2*q + 5*q^2)‖ ≤ 28 * rq^3 := by
    linarith [h_t1, h_t2, h_t3, h_t4, h_t5, h_neg10q3, h_2q4_norm.le, h_4q5_norm.le,
              h_9q6_norm.le, hr2_loose, h_r3_mul_le, h_rq4_le, h_rq5_le, h_rq6_le]
  -- 64 rq³ · ‖D‖ ≥ 64 rq³ · 1/2 = 32 rq³ ≥ 28 rq³.
  have h_rhs_ge : 28 * rq^3 ≤ 64 * rq^3 * ‖(1 + 2*q + 2*q^4 + r₃' : ℂ)‖ := by
    have h_step : 64 * rq^3 * (1/2 : ℝ) ≤ 64 * rq^3 * ‖(1 + 2*q + 2*q^4 + r₃' : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hD_norm (by positivity)
    linarith
  linarith

/-- Pure ring identity used in the four-term `λ` bound. With
`t := v + 2q − 5q² + 10q³` and `u := −2q + 5q² − 10q³`, the bracket
`(1 + v)⁴ − 1 + 8q − 44q² + 192q³` decomposes into a binomial expansion
in `(1+u)`-powers of `t` plus the explicit `q`-only remainder
`646q⁴ − 1840q⁵ + 4420q⁶ − 8800q⁷ + 15025q⁸ − 21000q⁹ + 23000q¹⁰
− 20000q¹¹ + 10000q¹²`. -/
theorem modularLambda_four_term_bracket_identity (v q : ℂ) :
    (1 + v)^4 - 1 + 8 * q - 44 * q^2 + 192 * q^3 =
      4 * (1 + (-2*q + 5*q^2 - 10*q^3))^3 * (v + 2*q - 5*q^2 + 10*q^3) +
      6 * (1 + (-2*q + 5*q^2 - 10*q^3))^2 * (v + 2*q - 5*q^2 + 10*q^3)^2 +
      4 * (1 + (-2*q + 5*q^2 - 10*q^3)) * (v + 2*q - 5*q^2 + 10*q^3)^3 +
      (v + 2*q - 5*q^2 + 10*q^3)^4 +
      646 * q^4 - 1840 * q^5 + 4420 * q^6 - 8800 * q^7 + 15025 * q^8 -
        21000 * q^9 + 23000 * q^10 - 20000 * q^11 + 10000 * q^12 := by
  ring

/-- Norm bound on `v := (1 + q² + q⁶ + q¹² + r₂') / D − 1` with
`D := 1 + 2q + 2q⁴ + 2q⁹ + r₃'`. Used in the four-term `λ` bound. -/
theorem modularLambda_four_term_v_bound (q r₂' r₃' : ℂ) (rq : ℝ)
    (hq_norm : ‖q‖ = rq) (hrq_pos : 0 < rq) (hrq_lt : rq < 1 / 16)
    (hr2_loose : ‖r₂'‖ ≤ rq ^ 4) (hr3_loose : ‖r₃'‖ ≤ rq ^ 4)
    (hD_norm : (1 / 2 : ℝ) ≤ ‖(1 + 2 * q + 2 * q ^ 4 + 2 * q ^ 9 + r₃' : ℂ)‖) :
    ‖(1 + q^2 + q^6 + q^12 + r₂') / (1 + 2*q + 2*q^4 + 2*q^9 + r₃') - 1‖ ≤ 6 * rq := by
  have hrq_nn : 0 ≤ rq := hrq_pos.le
  have hrq_le_one : rq ≤ 1 := by linarith
  have hD_pos : 0 < ‖(1 + 2*q + 2*q^4 + 2*q^9 + r₃' : ℂ)‖ := by linarith
  have hD_ne : (1 + 2*q + 2*q^4 + 2*q^9 + r₃' : ℂ) ≠ 0 := norm_ne_zero_iff.mp hD_pos.ne'
  have h_v_eq : (1 + q^2 + q^6 + q^12 + r₂') / (1 + 2*q + 2*q^4 + 2*q^9 + r₃') - 1 =
      (q^2 + q^6 + q^12 + r₂' - 2*q - 2*q^4 - 2*q^9 - r₃') /
        (1 + 2*q + 2*q^4 + 2*q^9 + r₃') := by
    rw [div_sub_one hD_ne]; congr 1; ring
  rw [h_v_eq, norm_div]
  rw [div_le_iff₀ hD_pos]
  have h_q2_norm : ‖q^2‖ = rq^2 := by rw [norm_pow, hq_norm]
  have h_q4_norm : ‖q^4‖ = rq^4 := by rw [norm_pow, hq_norm]
  have h_q6_norm : ‖q^6‖ = rq^6 := by rw [norm_pow, hq_norm]
  have h_q9_norm : ‖q^9‖ = rq^9 := by rw [norm_pow, hq_norm]
  have h_q12_norm : ‖q^12‖ = rq^12 := by rw [norm_pow, hq_norm]
  have h_2q_norm : ‖((2 : ℂ) * q)‖ = 2 * rq := by
    rw [show ((2 * q : ℂ)) = (((2 : ℝ) : ℂ)) * q from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, hq_norm]; simp
  have h_2q4_norm : ‖((2 : ℂ) * q^4)‖ = 2 * rq^4 := by
    rw [show ((2 * q^4 : ℂ)) = (((2 : ℝ) : ℂ)) * q^4 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q4_norm]; simp
  have h_2q9_norm : ‖((2 : ℂ) * q^9)‖ = 2 * rq^9 := by
    rw [show ((2 * q^9 : ℂ)) = (((2 : ℝ) : ℂ)) * q^9 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q9_norm]; simp
  have h_eq : q^2 + q^6 + q^12 + r₂' - 2*q - 2*q^4 - 2*q^9 - r₃' =
      ((((q^2 + q^6 + q^12 + r₂') - 2*q) - 2*q^4) - 2*q^9) - r₃' := by ring
  rw [h_eq]
  have h_t1 := norm_sub_le ((((q^2 + q^6 + q^12 + r₂') - 2*q) - 2*q^4) - 2*q^9) r₃'
  have h_t2 := norm_sub_le (((q^2 + q^6 + q^12 + r₂') - 2*q) - 2*q^4) (2*q^9)
  have h_t3 := norm_sub_le ((q^2 + q^6 + q^12 + r₂') - 2*q) (2*q^4)
  have h_t4 := norm_sub_le (q^2 + q^6 + q^12 + r₂') (2*q)
  have h_t5 := norm_add_le (q^2 + q^6 + q^12) r₂'
  have h_t6 := norm_add_le (q^2 + q^6) (q^12)
  have h_t7 := norm_add_le (q^2) (q^6)
  -- Powers ladder.
  have h_rq2_le_rq16 : rq^2 ≤ rq * (1/16) := by
    have h_eq : rq^2 = rq * rq := by ring
    rw [h_eq]; exact mul_le_mul_of_nonneg_left hrq_lt.le hrq_nn
  have h_rq4_le_rq2 : rq^4 ≤ rq^2 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq6_le_rq2 : rq^6 ≤ rq^2 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq9_le_rq2 : rq^9 ≤ rq^2 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq12_le_rq2 : rq^12 ≤ rq^2 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  -- Bound LHS ≤ 3 rq.
  have h_lhs_le : ‖((((q^2 + q^6 + q^12 + r₂') - 2*q) - 2*q^4) - 2*q^9) - r₃'‖ ≤ 3 * rq := by
    have h_chain : ‖((((q^2 + q^6 + q^12 + r₂') - 2*q) - 2*q^4) - 2*q^9) - r₃'‖ ≤
        rq^2 + rq^6 + rq^12 + rq^4 + 2*rq + 2*rq^4 + 2*rq^9 + rq^4 := by
      linarith [h_t1, h_t2, h_t3, h_t4, h_t5, h_t6, h_t7, h_q2_norm.le, h_q6_norm.le,
                h_q12_norm.le, hr2_loose, hr3_loose, h_2q_norm.le, h_2q4_norm.le, h_2q9_norm.le]
    -- rq² + rq⁶ + rq¹² + rq⁴ + 2rq + 2rq⁴ + 2rq⁹ + rq⁴ ≤ 7 rq² + 2 rq ≤ rq + 2 rq = 3 rq.
    -- Need 7 rq² ≤ rq, i.e. 7 rq ≤ 1. Since rq < 1/16, 7 rq < 7/16 < 1. ✓
    have h_7rq_le : 7 * rq ≤ 7/16 := by linarith
    have h_7rq_le_1 : 7 * rq ≤ 1 := by linarith
    have h_7rq2_le_rq : 7 * rq^2 ≤ rq := by
      have h_eq : 7 * rq^2 = (7 * rq) * rq := by ring
      rw [h_eq]
      calc (7 * rq) * rq ≤ 1 * rq := mul_le_mul_of_nonneg_right h_7rq_le_1 hrq_nn
        _ = rq := one_mul _
    linarith [h_chain, h_rq4_le_rq2, h_rq6_le_rq2, h_rq9_le_rq2, h_rq12_le_rq2]
  -- 6 rq · ‖D‖ ≥ 6 rq · (1/2) = 3 rq.
  have h_rhs_ge : 3 * rq ≤ 6 * rq * ‖(1 + 2*q + 2*q^4 + 2*q^9 + r₃' : ℂ)‖ := by
    have h_step : 6 * rq * (1/2 : ℝ) ≤ 6 * rq * ‖(1 + 2*q + 2*q^4 + 2*q^9 + r₃' : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hD_norm (by positivity)
    linarith
  linarith

/-- Norm bound on `t := v + 2q − 5q² + 10q³` where
`v := (1 + q² + q⁶ + q¹² + r₂') / D − 1` and
`D := 1 + 2q + 2q⁴ + 2q⁹ + r₃'`. The cancellation reaches order `q⁴`.
Used in the four-term `λ` bound. -/
theorem modularLambda_four_term_t_bound (q r₂' r₃' : ℂ) (rq : ℝ)
    (hq_norm : ‖q‖ = rq) (hrq_pos : 0 < rq) (hrq_lt : rq < 1 / 16)
    (hr2_loose : ‖r₂'‖ ≤ rq ^ 4) (hr3_loose : ‖r₃'‖ ≤ rq ^ 4)
    (hD_norm : (1 / 2 : ℝ) ≤ ‖(1 + 2 * q + 2 * q ^ 4 + 2 * q ^ 9 + r₃' : ℂ)‖) :
    ‖((1 + q^2 + q^6 + q^12 + r₂') / (1 + 2*q + 2*q^4 + 2*q^9 + r₃') - 1) +
        2*q - 5*q^2 + 10*q^3‖ ≤ 100 * rq^4 := by
  have hrq_nn : 0 ≤ rq := hrq_pos.le
  have hrq_le_one : rq ≤ 1 := by linarith
  have hrq4_pos : 0 < rq^4 := by positivity
  have hrq4_nn : 0 ≤ rq^4 := hrq4_pos.le
  have hD_pos : 0 < ‖(1 + 2*q + 2*q^4 + 2*q^9 + r₃' : ℂ)‖ := by linarith
  have hD_ne : (1 + 2*q + 2*q^4 + 2*q^9 + r₃' : ℂ) ≠ 0 := norm_ne_zero_iff.mp hD_pos.ne'
  -- t·D = 18q⁴ + 4q⁵ - 9q⁶ + 20q⁷ - 2q⁹ + 4q¹⁰ - 10q¹¹ + 21q¹² + r₂' + (-1 + 2q - 5q² + 10q³)·r₃'.
  have h_t_eq : ((1 + q^2 + q^6 + q^12 + r₂') / (1 + 2*q + 2*q^4 + 2*q^9 + r₃') - 1) +
      2*q - 5*q^2 + 10*q^3 =
      (18*q^4 + 4*q^5 - 9*q^6 + 20*q^7 - 2*q^9 + 4*q^10 - 10*q^11 + 21*q^12 + r₂' +
        (-1 + 2*q - 5*q^2 + 10*q^3) * r₃') / (1 + 2*q + 2*q^4 + 2*q^9 + r₃') := by
    have h_lhs_mul : (((1 + q^2 + q^6 + q^12 + r₂') / (1 + 2*q + 2*q^4 + 2*q^9 + r₃') - 1) +
        2*q - 5*q^2 + 10*q^3) * (1 + 2*q + 2*q^4 + 2*q^9 + r₃') =
        (18*q^4 + 4*q^5 - 9*q^6 + 20*q^7 - 2*q^9 + 4*q^10 - 10*q^11 + 21*q^12 + r₂' +
          (-1 + 2*q - 5*q^2 + 10*q^3) * r₃') := by
      have h_div_mul : (1 + q^2 + q^6 + q^12 + r₂') / (1 + 2*q + 2*q^4 + 2*q^9 + r₃') *
          (1 + 2*q + 2*q^4 + 2*q^9 + r₃') = 1 + q^2 + q^6 + q^12 + r₂' := div_mul_cancel₀ _ hD_ne
      have h_expand : (((1 + q^2 + q^6 + q^12 + r₂') / (1 + 2*q + 2*q^4 + 2*q^9 + r₃') - 1) +
          2*q - 5*q^2 + 10*q^3) * (1 + 2*q + 2*q^4 + 2*q^9 + r₃') =
          (1 + q^2 + q^6 + q^12 + r₂') / (1 + 2*q + 2*q^4 + 2*q^9 + r₃') *
            (1 + 2*q + 2*q^4 + 2*q^9 + r₃') -
            (1 + 2*q + 2*q^4 + 2*q^9 + r₃') + 2*q * (1 + 2*q + 2*q^4 + 2*q^9 + r₃') -
            5*q^2 * (1 + 2*q + 2*q^4 + 2*q^9 + r₃') +
            10*q^3 * (1 + 2*q + 2*q^4 + 2*q^9 + r₃') := by ring
      rw [h_expand, h_div_mul]
      ring
    rw [eq_div_iff hD_ne]
    exact h_lhs_mul
  rw [h_t_eq, norm_div]
  rw [div_le_iff₀ hD_pos]
  -- Goal: ‖num‖ ≤ 100 rq⁴ · ‖D‖.
  have h_q2_norm : ‖q^2‖ = rq^2 := by rw [norm_pow, hq_norm]
  have h_q3_norm : ‖q^3‖ = rq^3 := by rw [norm_pow, hq_norm]
  have h_q4_norm : ‖q^4‖ = rq^4 := by rw [norm_pow, hq_norm]
  have h_q5_norm : ‖q^5‖ = rq^5 := by rw [norm_pow, hq_norm]
  have h_q6_norm : ‖q^6‖ = rq^6 := by rw [norm_pow, hq_norm]
  have h_q7_norm : ‖q^7‖ = rq^7 := by rw [norm_pow, hq_norm]
  have h_q9_norm : ‖q^9‖ = rq^9 := by rw [norm_pow, hq_norm]
  have h_q10_norm : ‖q^10‖ = rq^10 := by rw [norm_pow, hq_norm]
  have h_q11_norm : ‖q^11‖ = rq^11 := by rw [norm_pow, hq_norm]
  have h_q12_norm : ‖q^12‖ = rq^12 := by rw [norm_pow, hq_norm]
  have h_const_norm (n : ℕ) (k : ℕ) :
      ‖((n : ℂ) * q^k)‖ = n * rq^k := by
    rw [show ((n : ℂ) * q^k) = (((n : ℝ) : ℂ)) * q^k from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, norm_pow, hq_norm]
    simp
  have h_18q4_norm : ‖((18 : ℂ) * q^4)‖ = 18 * rq^4 := h_const_norm 18 4
  have h_4q5_norm : ‖((4 : ℂ) * q^5)‖ = 4 * rq^5 := h_const_norm 4 5
  have h_9q6_norm : ‖((9 : ℂ) * q^6)‖ = 9 * rq^6 := h_const_norm 9 6
  have h_20q7_norm : ‖((20 : ℂ) * q^7)‖ = 20 * rq^7 := h_const_norm 20 7
  have h_2q9_norm : ‖((2 : ℂ) * q^9)‖ = 2 * rq^9 := h_const_norm 2 9
  have h_4q10_norm : ‖((4 : ℂ) * q^10)‖ = 4 * rq^10 := h_const_norm 4 10
  have h_10q11_norm : ‖((10 : ℂ) * q^11)‖ = 10 * rq^11 := h_const_norm 10 11
  have h_21q12_norm : ‖((21 : ℂ) * q^12)‖ = 21 * rq^12 := h_const_norm 21 12
  -- ‖-1 + 2q - 5q² + 10q³‖ ≤ 2.
  have h_factor_norm_le : ‖((-1 : ℂ) + 2*q - 5*q^2 + 10*q^3)‖ ≤ 2 := by
    have h_2q_norm : ‖((2 : ℂ) * q)‖ = 2 * rq := by
      rw [show ((2 * q : ℂ)) = (((2 : ℝ) : ℂ)) * q from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, hq_norm]; simp
    have h_5q2_norm : ‖((5 : ℂ) * q^2)‖ = 5 * rq^2 := h_const_norm 5 2
    have h_10q3_norm : ‖((10 : ℂ) * q^3)‖ = 10 * rq^3 := h_const_norm 10 3
    have h_neg1_norm : ‖(-1 : ℂ)‖ = 1 := by simp
    have h_add1 := norm_add_le ((-1 : ℂ) + 2*q - 5*q^2) (10*q^3)
    have h_sub1 := norm_sub_le ((-1 : ℂ) + 2*q) (5*q^2)
    have h_add2 := norm_add_le ((-1 : ℂ)) (2*q)
    have h_2rq : 2 * rq ≤ 1/8 := by linarith
    have h_5rq2 : 5 * rq^2 ≤ 1/8 := by
      have h_rq2 : rq^2 ≤ rq * (1/16) := by
        have h_eq : rq^2 = rq * rq := by ring
        rw [h_eq]; exact mul_le_mul_of_nonneg_left hrq_lt.le hrq_nn
      have h_rq2_le_256 : rq^2 ≤ 1/256 := by
        have : rq * (1/16 : ℝ) ≤ (1/16) * (1/16) := by
          apply mul_le_mul_of_nonneg_right hrq_lt.le; norm_num
        linarith [this]
      linarith
    have h_10rq3 : 10 * rq^3 ≤ 1/8 := by
      have h_rq3 : rq^3 ≤ (1/16)^3 := pow_le_pow_left₀ hrq_nn hrq_lt.le 3
      have : ((1/16 : ℝ))^3 = 1/4096 := by norm_num
      have h_rq3_le : rq^3 ≤ 1/4096 := h_rq3.trans (le_of_eq this)
      linarith
    linarith [h_add1, h_sub1, h_add2, h_neg1_norm, h_2q_norm, h_5q2_norm, h_10q3_norm]
  -- ‖(-1 + 2q - 5q² + 10q³) · r₃'‖ ≤ 2 · rq^4.
  have h_factor_mul_le : ‖((-1 : ℂ) + 2*q - 5*q^2 + 10*q^3) * r₃'‖ ≤ 2 * rq^4 := by
    rw [norm_mul]
    have h : ‖((-1 : ℂ) + 2*q - 5*q^2 + 10*q^3)‖ * ‖r₃'‖ ≤ 2 * rq^4 :=
      mul_le_mul h_factor_norm_le hr3_loose (norm_nonneg _) (by norm_num)
    linarith
  -- Triangle inequality on the numerator.
  have h_num_eq :
      18*q^4 + 4*q^5 - 9*q^6 + 20*q^7 - 2*q^9 + 4*q^10 - 10*q^11 + 21*q^12 + r₂' +
        (-1 + 2*q - 5*q^2 + 10*q^3) * r₃' =
      ((((((((18*q^4 + 4*q^5) - 9*q^6) + 20*q^7) - 2*q^9) + 4*q^10) - 10*q^11) + 21*q^12) + r₂') +
        (-1 + 2*q - 5*q^2 + 10*q^3) * r₃' := by ring
  rw [h_num_eq]
  have h_t1 := norm_add_le (((((((((18*q^4 + 4*q^5) - 9*q^6) + 20*q^7) - 2*q^9) + 4*q^10) -
    10*q^11) + 21*q^12) + r₂')) (((-1 : ℂ) + 2*q - 5*q^2 + 10*q^3) * r₃')
  have h_t2 := norm_add_le ((((((((18*q^4 + 4*q^5) - 9*q^6) + 20*q^7) - 2*q^9) + 4*q^10) -
    10*q^11) + 21*q^12)) r₂'
  have h_t3 := norm_add_le (((((((18*q^4 + 4*q^5) - 9*q^6) + 20*q^7) - 2*q^9) + 4*q^10) -
    10*q^11)) (21*q^12)
  have h_t4 := norm_sub_le ((((((18*q^4 + 4*q^5) - 9*q^6) + 20*q^7) - 2*q^9) + 4*q^10))
    (10*q^11)
  have h_t5 := norm_add_le (((((18*q^4 + 4*q^5) - 9*q^6) + 20*q^7) - 2*q^9)) (4*q^10)
  have h_t6 := norm_sub_le ((((18*q^4 + 4*q^5) - 9*q^6) + 20*q^7)) (2*q^9)
  have h_t7 := norm_add_le (((18*q^4 + 4*q^5) - 9*q^6)) (20*q^7)
  have h_t8 := norm_sub_le ((18*q^4 + 4*q^5)) (9*q^6)
  have h_t9 := norm_add_le (18*q^4) (4*q^5)
  -- Power ladder: rq^k ≤ rq^4 for k ≥ 4.
  have h_rq5_le : rq^5 ≤ rq^4 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq6_le : rq^6 ≤ rq^4 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq7_le : rq^7 ≤ rq^4 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq9_le : rq^9 ≤ rq^4 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq10_le : rq^10 ≤ rq^4 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq11_le : rq^11 ≤ rq^4 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  have h_rq12_le : rq^12 ≤ rq^4 := pow_le_pow_of_le_one hrq_nn hrq_le_one (by omega)
  -- Numerator bound: 18+4+9+20+2+4+10+21+1+2 = 91 rq^4 ≤ 50 rq^4 actually need tighter.
  -- Actually: 18 + small + 1 + 2 = 21 dominant. With loose ≤ 4: 91.
  -- Use 100·rq⁴·(1/2) = 50·rq⁴ available budget.
  -- So we need ‖num‖ ≤ 50 rq^4. With 91 we exceed. Need tighter bounds.
  -- Better: use rq^k ≤ rq^4 · rq^(k-4) ≤ rq^4 · (1/16)^(k-4) for k ≥ 4.
  -- Higher powers ARE much smaller. Let me use that.
  have h_rq5_tight : rq^5 ≤ rq^4 / 16 := by
    have h_eq : rq^5 = rq^4 * rq := by ring
    rw [h_eq]
    calc rq^4 * rq ≤ rq^4 * (1/16) := mul_le_mul_of_nonneg_left hrq_lt.le hrq4_nn
      _ = rq^4 / 16 := by ring
  have h_rq6_tight : rq^6 ≤ rq^4 / 256 := by
    have h_eq : rq^6 = rq^4 * (rq * rq) := by ring
    rw [h_eq]
    have h_rq_rq_le : rq * rq ≤ (1/16) * (1/16) :=
      mul_le_mul hrq_lt.le hrq_lt.le hrq_nn (by norm_num)
    calc rq^4 * (rq * rq) ≤ rq^4 * ((1/16) * (1/16)) :=
          mul_le_mul_of_nonneg_left h_rq_rq_le hrq4_nn
      _ = rq^4 / 256 := by ring
  -- For higher powers, use rq^k ≤ rq^4/256 (very loose for k ≥ 7).
  have h_rq7_tight : rq^7 ≤ rq^4 / 256 := by
    have h_eq : rq^7 = rq^6 * rq := by ring
    rw [h_eq]
    have h_rq6_pos : 0 ≤ rq^6 := by positivity
    calc rq^6 * rq ≤ rq^6 * 1 := mul_le_mul_of_nonneg_left hrq_le_one h_rq6_pos
      _ = rq^6 := mul_one _
      _ ≤ rq^4 / 256 := h_rq6_tight
  have h_rq_high_tight : ∀ k : ℕ, k ≥ 6 → rq^k ≤ rq^4 / 256 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact h_rq6_tight
    | succ n hn ih =>
      have hrqn_nn : 0 ≤ rq^n := by positivity
      have h_eq : rq^(n+1) = rq^n * rq := by ring
      rw [h_eq]
      calc rq^n * rq ≤ rq^n * 1 := mul_le_mul_of_nonneg_left hrq_le_one hrqn_nn
        _ = rq^n := mul_one _
        _ ≤ rq^4 / 256 := ih
  have h_rq9_tight : rq^9 ≤ rq^4 / 256 := h_rq_high_tight 9 (by omega)
  have h_rq10_tight : rq^10 ≤ rq^4 / 256 := h_rq_high_tight 10 (by omega)
  have h_rq11_tight : rq^11 ≤ rq^4 / 256 := h_rq_high_tight 11 (by omega)
  have h_rq12_tight : rq^12 ≤ rq^4 / 256 := h_rq_high_tight 12 (by omega)
  -- Numerator bound:
  -- 18 rq^4 + 4 rq^5 + 9 rq^6 + 20 rq^7 + 2 rq^9 + 4 rq^10 + 10 rq^11 + 21 rq^12 + rq^4 + 2 rq^4
  -- ≤ 18 rq^4 + 4/16 rq^4 + 9/256 rq^4 + (20+2+4+10+21)/256 rq^4 + rq^4 + 2 rq^4
  -- ≤ 21 rq^4 + 0.25 rq^4 + 0.035 rq^4 + 57/256 rq^4
  -- ≤ 21.51 rq^4 ≤ 50 rq^4 (with margin).
  have h_num_le : ‖((((((((18*q^4 + 4*q^5) - 9*q^6) + 20*q^7) - 2*q^9) + 4*q^10) -
      10*q^11) + 21*q^12) + r₂') + (-1 + 2*q - 5*q^2 + 10*q^3) * r₃'‖ ≤ 50 * rq^4 := by
    linarith [h_t1, h_t2, h_t3, h_t4, h_t5, h_t6, h_t7, h_t8, h_t9,
              h_18q4_norm.le, h_4q5_norm.le, h_9q6_norm.le, h_20q7_norm.le,
              h_2q9_norm.le, h_4q10_norm.le, h_10q11_norm.le, h_21q12_norm.le,
              hr2_loose, h_factor_mul_le, h_rq5_tight, h_rq6_tight, h_rq7_tight,
              h_rq9_tight, h_rq10_tight, h_rq11_tight, h_rq12_tight, hrq4_nn]
  -- 100 rq⁴ · ‖D‖ ≥ 100 rq⁴ · 1/2 = 50 rq⁴.
  have h_rhs_ge : 50 * rq^4 ≤ 100 * rq^4 * ‖(1 + 2*q + 2*q^4 + 2*q^9 + r₃' : ℂ)‖ := by
    have h_step : 100 * rq^4 * (1/2 : ℝ) ≤ 100 * rq^4 * ‖(1 + 2*q + 2*q^4 + 2*q^9 + r₃' : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hD_norm (by positivity)
    linarith
  linarith

/-- **Three-term leading bound for `λ`.** For `τ.im ≥ 1`,
`‖λ(τ) − 16·exp(πi τ) + 128·exp(2πi τ) − 704·exp(3πi τ)‖
   ≤ 32768·exp(−4π·τ.im)`. Combines the three-term `θ₂` and `θ₃` bounds
via the algebraic identity `(1 + v)⁴ − 1 + 8q − 44q² = −120q³ +
(4 − 24q + 60q²)·s + 6s² + 150q⁴ + 4v³ + v⁴` where `s := v + 2q − 5q²`
captures the next-order correction beyond the two-term bound. -/
theorem modularLambdaH_norm_sub_three_term_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ) +
        128 * Complex.exp (2 * Real.pi * Complex.I * τ) -
        704 * Complex.exp (3 * Real.pi * Complex.I * τ)‖ ≤
      32768 * Real.exp (-4 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  set q : ℂ := Complex.exp (Real.pi * Complex.I * τ) with hq_def
  set Q2 : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ) with hQ2_def
  set Q3 : ℂ := Complex.exp (3 * Real.pi * Complex.I * τ) with hQ3_def
  set Q4 : ℂ := Complex.exp (4 * Real.pi * Complex.I * τ) with hQ4_def
  set Q6 : ℂ := Complex.exp (6 * Real.pi * Complex.I * τ) with hQ6_def
  set rq : ℝ := Real.exp (-Real.pi * τ.im) with hrq_def
  have hrq_pos : 0 < rq := Real.exp_pos _
  have hrq_nn : 0 ≤ rq := hrq_pos.le
  have hq_norm : ‖q‖ = rq := by
    rw [hq_def, Complex.norm_exp, hrq_def]
    congr 1
    have h_eq : (Real.pi * Complex.I * τ : ℂ) = ((Real.pi : ℝ) : ℂ) * (Complex.I * τ) := by
      ring
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
  -- exp(π) > 16, so rq < 1/16.
  have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_exp3_gt_16 : (16 : ℝ) < Real.exp 3 := by
    have h_eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
    rw [h_eq]; nlinarith [h_e_gt, Real.exp_pos (1 : ℝ)]
  have h_exp_pi_gt_16 : (16 : ℝ) < Real.exp Real.pi :=
    h_exp3_gt_16.trans_le (Real.exp_le_exp.mpr Real.pi_gt_three.le)
  have hrq_le_eneg : rq ≤ Real.exp (-Real.pi) := by
    rw [hrq_def]; apply Real.exp_le_exp.mpr; nlinarith
  have h_exp_neg_pi_lt : Real.exp (-Real.pi) < 1/16 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/16),
        show (1/16 : ℝ)⁻¹ = 16 from by norm_num]
    exact h_exp_pi_gt_16
  have hrq_lt : rq < 1/16 := lt_of_le_of_lt hrq_le_eneg h_exp_neg_pi_lt
  have hrq_lt_one : rq < 1 := by linarith
  have hrq_le_one : rq ≤ 1 := hrq_lt_one.le
  have hrq2_pos : 0 < rq^2 := by positivity
  have hrq3_pos : 0 < rq^3 := by positivity
  have hrq3_nn : 0 ≤ rq^3 := hrq3_pos.le
  have hrq4_pos : 0 < rq^4 := by positivity
  have hrq4_eq : rq^4 = Real.exp (-4 * Real.pi * τ.im) := by
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
  -- r₂', r₃' bounds.
  set r₂' : ℂ := (theta2 τ - A * (1 + Q2 + Q6)) / A with hr2_def
  set r₃' : ℂ := theta3 τ - 1 - 2 * q - 2 * Q4 with hr3_def
  have hr2_bound : ‖r₂'‖ ≤ 4 * rq^12 := by
    rw [hr2_def, norm_div, hA_norm]
    have h_denom_pos : 0 < 2 * Real.exp (-(Real.pi * τ.im / 4)) := by positivity
    rw [div_le_iff₀ h_denom_pos]
    have hrq12_eq : rq^12 = Real.exp (-(12 * Real.pi * τ.im)) := by
      rw [hrq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h_target_eq : 4 * rq^12 * (2 * Real.exp (-(Real.pi * τ.im / 4))) =
        8 * Real.exp (-(49 * Real.pi * τ.im / 4)) := by
      rw [hrq12_eq]
      rw [show (4 * Real.exp (-(12 * Real.pi * τ.im)) *
          (2 * Real.exp (-(Real.pi * τ.im / 4))) : ℝ) =
          8 * (Real.exp (-(12 * Real.pi * τ.im)) *
            Real.exp (-(Real.pi * τ.im / 4))) from by ring]
      rw [← Real.exp_add]
      exact congr_arg (fun x => 8 * Real.exp x) (by ring)
    rw [h_target_eq]
    have h_eq_A : A * (1 + Q2 + Q6) =
        2 * Complex.exp (Real.pi * Complex.I * τ / 4) *
          (1 + Complex.exp (2 * Real.pi * Complex.I * τ) +
            Complex.exp (6 * Real.pi * Complex.I * τ)) := by
      rw [hA_def, hQ2_def, hQ6_def]
    rw [h_eq_A]
    exact theta2_norm_sub_three_term_le_of_im_ge_one hτ
  have hr3_bound : ‖r₃'‖ ≤ 4 * rq^9 := by
    rw [hr3_def, hq_def, hQ4_def]
    have hrq9_eq : rq^9 = Real.exp (-9 * Real.pi * τ.im) := by
      rw [hrq_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hrq9_eq]
    exact theta3_sub_one_minus_2q_minus_2q4_norm_le_of_im_ge_one hτ
  have hr2_loose : ‖r₂'‖ ≤ rq^3 := by
    refine hr2_bound.trans ?_
    have h_4rq9_le : (4 : ℝ) * rq^9 ≤ 1 := by
      have h1 : rq^9 ≤ (1/16 : ℝ)^9 := pow_le_pow_left₀ hrq_nn hrq_lt.le _
      have h2 : ((1/16:ℝ))^9 ≤ 1/4 := by norm_num
      linarith
    have h_eq : (4 : ℝ) * rq^12 = (4 * rq^9) * rq^3 := by ring
    rw [h_eq]
    calc (4 * rq^9) * rq^3 ≤ 1 * rq^3 := mul_le_mul_of_nonneg_right h_4rq9_le hrq3_nn
      _ = rq^3 := one_mul _
  have hr3_loose : ‖r₃'‖ ≤ rq^3 := by
    refine hr3_bound.trans ?_
    have h_4rq6_le : (4 : ℝ) * rq^6 ≤ 1 := by
      have h1 : rq^6 ≤ (1/16 : ℝ)^6 := pow_le_pow_left₀ hrq_nn hrq_lt.le _
      have h2 : ((1/16:ℝ))^6 ≤ 1/4 := by norm_num
      linarith
    have h_eq : (4 : ℝ) * rq^9 = (4 * rq^6) * rq^3 := by ring
    rw [h_eq]
    calc (4 * rq^6) * rq^3 ≤ 1 * rq^3 := mul_le_mul_of_nonneg_right h_4rq6_le hrq3_nn
      _ = rq^3 := one_mul _
  -- θ₂ = A(1+Q2+Q6+r₂'); θ₃ = 1+2q+2Q4+r₃'.
  have h_th2_eq : theta2 τ = A * (1 + Q2 + Q6 + r₂') := by
    rw [hr2_def]; field_simp
    ring
  have h_th3_eq : theta3 τ = 1 + 2 * q + 2 * Q4 + r₃' := by rw [hr3_def]; ring
  -- ‖D‖ ≥ 1/2 (using θ₃ norm bound).
  have h_th3_norm_ge := theta3_norm_ge_half_of_im_ge_one hτ
  have h_th3_norm_ge' : (1/2 : ℝ) ≤ ‖(1 + 2*q + 2*Q4 + r₃' : ℂ)‖ := by
    rw [← h_th3_eq]; exact h_th3_norm_ge
  have h_th3_pos : 0 < ‖(1 + 2*q + 2*Q4 + r₃' : ℂ)‖ :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) h_th3_norm_ge'
  have h_th3_ne : (1 + 2*q + 2*Q4 + r₃' : ℂ) ≠ 0 := norm_ne_zero_iff.mp h_th3_pos.ne'
  -- λ formula.
  have h_lambda_eq : modularLambdaH τ =
      A^4 * ((1 + Q2 + Q6 + r₂') / (1 + 2*q + 2*Q4 + r₃'))^4 := by
    unfold modularLambdaH
    rw [h_th2_eq, h_th3_eq, mul_pow, div_pow]; ring
  rw [h_lambda_eq]
  -- Substitute 16q = A^4, 128 Q2 = 8q A⁴, 704 Q3 = 44q² A⁴.
  rw [show (16 * Complex.exp (Real.pi * Complex.I * τ) : ℂ) = A^4 from hA_pow.symm]
  rw [show (128 * Complex.exp (2 * Real.pi * Complex.I * τ) : ℂ) = 8 * q * A^4 from by
    rw [show Complex.exp (2 * Real.pi * Complex.I * τ) = Q2 from rfl]
    rw [hA_pow, hQ2_eq]; ring]
  rw [show (704 * Complex.exp (3 * Real.pi * Complex.I * τ) : ℂ) = 44 * q^2 * A^4 from by
    rw [show Complex.exp (3 * Real.pi * Complex.I * τ) = Q3 from rfl]
    rw [hA_pow, hQ3_eq]; ring]
  -- Factor out A^4.
  rw [show (A^4 * ((1 + Q2 + Q6 + r₂') / (1 + 2*q + 2*Q4 + r₃'))^4 - A^4 +
      8 * q * A^4 - 44 * q^2 * A^4 : ℂ) =
      A^4 * (((1 + Q2 + Q6 + r₂') / (1 + 2*q + 2*Q4 + r₃'))^4 - 1 + 8 * q - 44 * q^2) from
        by ring]
  rw [norm_mul, hA_pow_norm]
  -- Convert Q^k to q^k in the bracket.
  rw [hQ2_eq, hQ4_eq, hQ6_eq]
  -- ‖D‖ ≥ 1/2 in q^4 form.
  have hD_norm_q : (1/2 : ℝ) ≤ ‖(1 + 2*q + 2*q^4 + r₃' : ℂ)‖ := by
    rw [show (1 + 2*q + 2*q^4 + r₃' : ℂ) = 1 + 2*q + 2*Q4 + r₃' from by rw [hQ4_eq]]
    exact h_th3_norm_ge'
  -- Set v.
  set v : ℂ := (1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃') - 1 with hv_def
  rw [show ((1 + q^2 + q^6 + r₂') / (1 + 2*q + 2*q^4 + r₃')) = 1 + v from by
    rw [hv_def]; ring]
  -- Apply algebraic identity.
  rw [modularLambda_three_term_bracket_identity v q]
  -- Apply helpers.
  have hv_bound : ‖v‖ ≤ 6 * rq :=
    modularLambda_three_term_v_bound q r₂' r₃' rq hq_norm hrq_pos hrq_lt
      hr2_loose hr3_loose hD_norm_q
  have hs_bound : ‖v + 2*q - 5*q^2‖ ≤ 64 * rq^3 :=
    modularLambda_three_term_s_bound q r₂' r₃' rq hq_norm hrq_pos hrq_lt
      hr2_loose hr3_loose hD_norm_q
  -- Bound each bracket term.
  have h_q2_norm : ‖q^2‖ = rq^2 := by rw [norm_pow, hq_norm]
  have h_q3_norm : ‖q^3‖ = rq^3 := by rw [norm_pow, hq_norm]
  have h_q4_norm : ‖q^4‖ = rq^4 := by rw [norm_pow, hq_norm]
  -- ‖-120 q^3‖ = 120 rq^3.
  have h_120q3_norm : ‖(-120 * q^3 : ℂ)‖ = 120 * rq^3 := by
    rw [show ((-120 * q^3 : ℂ)) = (((-120 : ℝ) : ℂ)) * q^3 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q3_norm]; simp
  -- ‖(4 − 24q + 60q²)‖ ≤ 6.
  have h_coeff_norm_le : ‖((4 : ℂ) - 24*q + 60*q^2)‖ ≤ 6 := by
    have h_24q : ‖((24 : ℂ) * q)‖ = 24 * rq := by
      rw [show ((24 * q : ℂ)) = (((24 : ℝ) : ℂ)) * q from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, hq_norm]; simp
    have h_60q2 : ‖((60 : ℂ) * q^2)‖ = 60 * rq^2 := by
      rw [show ((60 * q^2 : ℂ)) = (((60 : ℝ) : ℂ)) * q^2 from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, h_q2_norm]; simp
    have h_4_norm : ‖(4 : ℂ)‖ = 4 := by simp
    have h_24rq : 24 * rq ≤ 24/16 := by linarith
    have h_60rq2 : 60 * rq^2 ≤ 60/256 := by
      have h_rq2 : rq^2 ≤ 1/256 := by
        have h_step : rq^2 = rq * rq := by ring
        rw [h_step]
        calc rq * rq ≤ (1/16) * (1/16 : ℝ) :=
              mul_le_mul hrq_lt.le hrq_lt.le hrq_nn (by norm_num)
          _ = 1/256 := by norm_num
      linarith
    have h_add := norm_add_le ((4 : ℂ) - 24*q) (60*q^2)
    have h_sub := norm_sub_le ((4 : ℂ)) (24*q)
    linarith [h_add, h_sub, h_24q, h_60q2, h_4_norm, h_24rq, h_60rq2]
  -- ‖(4 − 24q + 60q²)·s‖ ≤ 6 · 64 rq³ = 384 rq³.
  have h_coeff_s_le : ‖((4 : ℂ) - 24*q + 60*q^2) * (v + 2*q - 5*q^2)‖ ≤ 384 * rq^3 := by
    rw [norm_mul]
    have h_step : ‖((4 : ℂ) - 24*q + 60*q^2)‖ * ‖v + 2*q - 5*q^2‖ ≤ 6 * (64 * rq^3) :=
      mul_le_mul h_coeff_norm_le hs_bound (norm_nonneg _) (by norm_num)
    linarith
  -- ‖6 s²‖ ≤ 6 · (64 rq³)² = 24576 rq⁶ ≤ 6 rq³.
  have h_6s2_le : ‖(6 : ℂ) * (v + 2*q - 5*q^2)^2‖ ≤ 6 * rq^3 := by
    rw [norm_mul, norm_pow]
    have h_step1 : ‖v + 2*q - 5*q^2‖^2 ≤ (64 * rq^3)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hs_bound 2
    have h_simp : ((64 : ℝ) * rq^3)^2 = 4096 * rq^6 := by ring
    have h_6 : ‖((6 : ℂ))‖ = 6 := by simp
    rw [h_6]
    have h_chain : (6 : ℝ) * ‖v + 2*q - 5*q^2‖^2 ≤ 6 * (4096 * rq^6) := by
      calc (6 : ℝ) * ‖v + 2*q - 5*q^2‖^2 ≤ 6 * (64 * rq^3)^2 :=
            mul_le_mul_of_nonneg_left h_step1 (by norm_num)
        _ = 6 * (4096 * rq^6) := by rw [h_simp]
    -- 6 · 4096 · rq⁶ ≤ 6 · rq³? 4096 rq⁶ ≤ rq³ iff 4096 rq³ ≤ 1.
    -- rq³ ≤ 1/16³ = 1/4096. So 4096 rq³ ≤ 1. ✓
    have h_4096rq3 : (4096 : ℝ) * rq^3 ≤ 1 := by
      have h_rq3 : rq^3 ≤ (1/16 : ℝ)^3 := pow_le_pow_left₀ hrq_nn hrq_lt.le _
      have hh : ((1/16:ℝ))^3 = 1/4096 := by norm_num
      linarith
    have h_4096_rq6_le_rq3 : (4096 : ℝ) * rq^6 ≤ rq^3 := by
      have h_eq : (4096 : ℝ) * rq^6 = (4096 * rq^3) * rq^3 := by ring
      rw [h_eq]
      calc (4096 * rq^3) * rq^3 ≤ 1 * rq^3 :=
            mul_le_mul_of_nonneg_right h_4096rq3 hrq3_nn
        _ = rq^3 := one_mul _
    linarith
  -- ‖150 q⁴‖ ≤ 10 rq³.
  have h_150q4_le : ‖((150 : ℂ) * q^4)‖ ≤ 10 * rq^3 := by
    rw [show ((150 * q^4 : ℂ)) = (((150 : ℝ) : ℂ)) * q^4 from by push_cast; ring]
    rw [norm_mul, Complex.norm_real, h_q4_norm]
    simp only [Real.norm_ofNat]
    have h_step : (150 : ℝ) * rq^4 = (150 * rq) * rq^3 := by ring
    have h_150rq : (150 : ℝ) * rq ≤ 10 := by linarith
    rw [h_step]
    exact mul_le_mul_of_nonneg_right h_150rq hrq3_nn
  -- ‖4 v³‖ ≤ 4 · (6 rq)³ = 864 rq³.
  have h_4v3_le : ‖((4 : ℂ) * v^3)‖ ≤ 864 * rq^3 := by
    rw [norm_mul, norm_pow]
    have h_step1 : ‖v‖^3 ≤ (6 * rq)^3 := pow_le_pow_left₀ (norm_nonneg _) hv_bound 3
    have h_simp : (6 * rq)^3 = 216 * rq^3 := by ring
    have h_4 : ‖((4 : ℂ))‖ = 4 := by simp
    rw [h_4]
    have h_chain : (4 : ℝ) * ‖v‖^3 ≤ 864 * rq^3 := by
      have h_a : (4 : ℝ) * ‖v‖^3 ≤ 4 * (6 * rq)^3 :=
        mul_le_mul_of_nonneg_left h_step1 (by norm_num)
      have h_b : (4 : ℝ) * (6 * rq)^3 = 864 * rq^3 := by rw [h_simp]; ring
      linarith
    exact h_chain
  -- ‖v⁴‖ ≤ 1296 rq⁴ ≤ 81 rq³.
  have h_v4_le : ‖v^4‖ ≤ 81 * rq^3 := by
    rw [norm_pow]
    have h_step1 : ‖v‖^4 ≤ (6 * rq)^4 := pow_le_pow_left₀ (norm_nonneg _) hv_bound 4
    have h_simp : (6 * rq)^4 = 1296 * rq^4 := by ring
    -- 1296 rq^4 ≤ 81 rq^3 iff 1296 rq ≤ 81 iff rq ≤ 81/1296 = 1/16. ✓
    have h_1296rq : (1296 : ℝ) * rq ≤ 81 := by linarith
    have h_chain : (1296 : ℝ) * rq^4 ≤ 81 * rq^3 := by
      have h_eq : (1296 : ℝ) * rq^4 = (1296 * rq) * rq^3 := by ring
      rw [h_eq]
      exact mul_le_mul_of_nonneg_right h_1296rq hrq3_nn
    linarith [h_step1, h_simp.le, h_chain]
  -- Combine: bracket ≤ 120 + 384 + 6 + 10 + 864 + 81 = 1465 rq³.
  have h_bracket_bound : ‖(-120 * q^3 + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2) +
      6 * (v + 2*q - 5*q^2)^2 + 150 * q^4 + 4 * v^3 + v^4 : ℂ)‖ ≤ 1465 * rq^3 := by
    have h_eq : (-120 * q^3 + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2) +
        6 * (v + 2*q - 5*q^2)^2 + 150 * q^4 + 4 * v^3 + v^4 : ℂ) =
        ((((((-120 * q^3) + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2)) +
            6 * (v + 2*q - 5*q^2)^2) + 150 * q^4) + 4 * v^3) + v^4) := by ring
    rw [h_eq]
    have h1 := norm_add_le (((((-120 * q^3) + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2)) +
        6 * (v + 2*q - 5*q^2)^2) + 150 * q^4) + 4 * v^3) (v^4)
    have h2 := norm_add_le ((((-120 * q^3) + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2)) +
        6 * (v + 2*q - 5*q^2)^2) + 150 * q^4) (4 * v^3)
    have h3 := norm_add_le (((-120 * q^3) + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2)) +
        6 * (v + 2*q - 5*q^2)^2) (150 * q^4)
    have h4 := norm_add_le ((-120 * q^3) + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2))
        (6 * (v + 2*q - 5*q^2)^2)
    have h5 := norm_add_le (-120 * q^3) ((4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2))
    linarith [h1, h2, h3, h4, h5, h_120q3_norm.le, h_coeff_s_le, h_6s2_le,
              h_150q4_le, h_4v3_le, h_v4_le]
  -- 16 rq · ‖bracket‖ ≤ 16 rq · 1465 rq³ = 23440 rq⁴ ≤ 32768 rq⁴.
  have h_step : (16 * rq) * ‖(-120 * q^3 + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2) +
      6 * (v + 2*q - 5*q^2)^2 + 150 * q^4 + 4 * v^3 + v^4 : ℂ)‖ ≤ 23440 * rq^4 := by
    have h_mul : (16 * rq) * ‖(-120 * q^3 + (4 - 24*q + 60*q^2) * (v + 2*q - 5*q^2) +
        6 * (v + 2*q - 5*q^2)^2 + 150 * q^4 + 4 * v^3 + v^4 : ℂ)‖ ≤
        (16 * rq) * (1465 * rq^3) :=
      mul_le_mul_of_nonneg_left h_bracket_bound (by positivity)
    have h_eq : (16 : ℝ) * rq * (1465 * rq^3) = 23440 * rq^4 := by ring
    linarith
  have h_final : 23440 * rq^4 ≤ 32768 * Real.exp (-4 * Real.pi * τ.im) := by
    rw [← hrq4_eq]
    have h_pos : 0 ≤ rq^4 := by positivity
    linarith
  linarith [h_step, h_final]

end NoWanderingDomains
