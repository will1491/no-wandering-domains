/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.ModularFunction.FourTermBounds.Lambda

/-! # Jacobi’s identity, theta non-vanishing, and the cusp function

Jacobi's identity `θ₂⁴ + θ₄⁴ = θ₃⁴` on `ℍ`, proved by the weight-4 cusp-form vanishing
principle applied to the squared Jacobi difference together with its cusp decay bound.
Non-vanishing of all three theta nullwerte on the full upper half-plane via
`SL(2, ℤ)`-reduction of the easy regime `τ.im ≥ 1/2`, and differentiability of `λ` on
`ℍ`. The cusp function `modularLambdaH_cusp : ℂ → ℂ` of the period-2 function `λ`, its
analyticity on the unit `q`-disk, the q-coordinate truncation bounds, the Cauchy
derivative estimates, and the Taylor data `cusp 0 = 0`, `deriv cusp 0 = 16`,
`iteratedDeriv 2 cusp 0 = −256`, `iteratedDeriv 3 cusp 0 = 4224`.
-/

namespace NoWanderingDomains
open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped ModularForm Manifold MatrixGroups

/-- `‖θ₃(τ) − θ₄(τ)‖ ≤ 100 · exp(−π·τ.im)` for `τ.im ≥ 1`. The
constant terms `1` in `θ₃` and `θ₄` cancel, leaving the leading-`q¹`
piece `4q + O(q⁹)`; this gives full `exp(−π·τ.im)` decay. -/
theorem theta3_sub_theta4_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta3 τ - theta4 τ‖ ≤ 100 * Real.exp (-Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  have hτ1_im : (τ + 1).im = τ.im := by simp [Complex.add_im]
  have hτ1_im_pos : 0 < (τ + 1).im := by rw [hτ1_im]; exact hτim_pos
  -- Mathlib bound at τ and at τ + 1.
  have h_at_τ : ‖jacobiTheta τ - 1‖ ≤
      2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) :=
    norm_jacobiTheta_sub_one_le hτim_pos
  have h_at_τ1 : ‖jacobiTheta (τ + 1) - 1‖ ≤
      2 / (1 - Real.exp (-Real.pi * (τ + 1).im)) * Real.exp (-Real.pi * (τ + 1).im) :=
    norm_jacobiTheta_sub_one_le hτ1_im_pos
  rw [hτ1_im] at h_at_τ1
  -- exp(-π·τ.im) ≤ exp(-π) < 1/2; hence (1 - exp(-π·τ.im)) ≥ 1/2.
  have h_exp_at_one : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have h_exp_neg_pi_lt_half : Real.exp (-Real.pi) < 1/2 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/2),
        show (1/2 : ℝ)⁻¹ = 2 from by norm_num]
    have h1 : (1 : ℝ) + 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp 1 < Real.exp Real.pi :=
      Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_three])
    linarith
  have h_exp_lt_half : Real.exp (-Real.pi * τ.im) < 1/2 :=
    lt_of_le_of_lt h_exp_at_one h_exp_neg_pi_lt_half
  have h_one_sub_ge : 1/2 ≤ 1 - Real.exp (-Real.pi * τ.im) := by linarith
  have h_one_sub_pos : 0 < 1 - Real.exp (-Real.pi * τ.im) := by linarith
  have h_quot_le : 2 / (1 - Real.exp (-Real.pi * τ.im)) ≤ 4 := by
    rw [div_le_iff₀ h_one_sub_pos]; linarith
  -- Each ‖θᵢ - 1‖ ≤ 4 · exp(-π·τ.im).
  have h_exp_pos : 0 < Real.exp (-Real.pi * τ.im) := Real.exp_pos _
  have h_th3_sub_one : ‖jacobiTheta τ - 1‖ ≤ 4 * Real.exp (-Real.pi * τ.im) :=
    h_at_τ.trans (mul_le_mul_of_nonneg_right h_quot_le h_exp_pos.le)
  have h_th4_sub_one : ‖jacobiTheta (τ + 1) - 1‖ ≤ 4 * Real.exp (-Real.pi * τ.im) :=
    h_at_τ1.trans (mul_le_mul_of_nonneg_right h_quot_le h_exp_pos.le)
  -- θ₃ - θ₄ = (θ₃ - 1) - (θ₄ - 1) = (jacobiTheta τ - 1) - (jacobiTheta(τ+1) - 1).
  unfold theta3 theta4
  calc ‖jacobiTheta τ - jacobiTheta (τ + 1)‖
      = ‖(jacobiTheta τ - 1) - (jacobiTheta (τ + 1) - 1)‖ := by congr 1; ring
    _ ≤ ‖jacobiTheta τ - 1‖ + ‖jacobiTheta (τ + 1) - 1‖ := norm_sub_le _ _
    _ ≤ 4 * Real.exp (-Real.pi * τ.im) + 4 * Real.exp (-Real.pi * τ.im) := by
        linarith
    _ ≤ 100 * Real.exp (-Real.pi * τ.im) := by nlinarith

/-- **Jacobi-difference cusp bound.** The squared Jacobi difference
`f² = (θ₂⁴ + θ₄⁴ − θ₃⁴)²` decays exponentially at the cusp `+i∞`.
The proof chains the four norm bounds: `‖θ₂⁴‖ ≤ 10⁴·exp(−π·τ.im)`
from `theta2_norm_le_of_im_ge_one`, and
`‖θ₃⁴ − θ₄⁴‖ ≤ 4·10⁵·exp(−π·τ.im)` from the factorisation
`θ₃⁴ − θ₄⁴ = (θ₃ − θ₄)(θ₃³ + θ₃²θ₄ + θ₃θ₄² + θ₄³)` together with
`theta3_sub_theta4_norm_le_of_im_ge_one` and the `θ₃/θ₄` bounds. -/
theorem jacobi_diff_sq_cusp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℂ, 1 ≤ τ.im →
      ‖(theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4) ^ 2‖
        ≤ C * Real.exp (-Real.pi * τ.im) := by
  refine ⟨10 ^ 12, by norm_num, ?_⟩
  intro τ hτim
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτim
  have hπ_pos := Real.pi_pos
  have h_exp_pos : 0 < Real.exp (-Real.pi * τ.im) := Real.exp_pos _
  have h_exp_nn : 0 ≤ Real.exp (-Real.pi * τ.im) := h_exp_pos.le
  have h_exp_le_one : Real.exp (-Real.pi * τ.im) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  -- Apply the four helpers.
  have h2 := theta2_norm_le_of_im_ge_one hτim
  have h3 := theta3_norm_le_of_im_ge_one hτim
  have h4 := theta4_norm_le_of_im_ge_one hτim
  have h34 := theta3_sub_theta4_norm_le_of_im_ge_one hτim
  -- `‖θ₂⁴‖ ≤ 10000 · exp(−π·τ.im)`.
  have h2_pow4 : ‖theta2 τ ^ 4‖ ≤ 10000 * Real.exp (-Real.pi * τ.im) := by
    rw [norm_pow]
    have h_pow_le : ‖theta2 τ‖ ^ 4 ≤ (10 * Real.exp (-Real.pi * τ.im / 4)) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 4
    refine h_pow_le.trans (le_of_eq ?_)
    rw [mul_pow]
    have h_exp_pow : (Real.exp (-Real.pi * τ.im / 4)) ^ 4 = Real.exp (-Real.pi * τ.im) := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [h_exp_pow]
    norm_num
  -- `‖θᵢ‖ ^ k ≤ 10 ^ k` for k = 1, 2, 3.
  have hn3 : (0 : ℝ) ≤ ‖theta3 τ‖ := norm_nonneg _
  have hn4 : (0 : ℝ) ≤ ‖theta4 τ‖ := norm_nonneg _
  have h3_pow3 : ‖theta3 τ‖ ^ 3 ≤ 1000 := by
    calc ‖theta3 τ‖ ^ 3 ≤ (10 : ℝ) ^ 3 := pow_le_pow_left₀ hn3 h3 3
      _ = 1000 := by norm_num
  have h3_pow2 : ‖theta3 τ‖ ^ 2 ≤ 100 := by
    calc ‖theta3 τ‖ ^ 2 ≤ (10 : ℝ) ^ 2 := pow_le_pow_left₀ hn3 h3 2
      _ = 100 := by norm_num
  have h4_pow3 : ‖theta4 τ‖ ^ 3 ≤ 1000 := by
    calc ‖theta4 τ‖ ^ 3 ≤ (10 : ℝ) ^ 3 := pow_le_pow_left₀ hn4 h4 3
      _ = 1000 := by norm_num
  have h4_pow2 : ‖theta4 τ‖ ^ 2 ≤ 100 := by
    calc ‖theta4 τ‖ ^ 2 ≤ (10 : ℝ) ^ 2 := pow_le_pow_left₀ hn4 h4 2
      _ = 100 := by norm_num
  -- `‖θ₃³ + θ₃²θ₄ + θ₃θ₄² + θ₄³‖ ≤ 4000`.
  have h_quart_norm :
      ‖theta3 τ ^ 3 + theta3 τ ^ 2 * theta4 τ + theta3 τ * theta4 τ ^ 2 + theta4 τ ^ 3‖
        ≤ 4000 := by
    have h_a : ‖theta3 τ ^ 3‖ ≤ 1000 := by rw [norm_pow]; exact h3_pow3
    have h_b : ‖theta3 τ ^ 2 * theta4 τ‖ ≤ 1000 := by
      rw [norm_mul, norm_pow]
      have := mul_le_mul h3_pow2 h4 hn4 (by norm_num : (0:ℝ) ≤ 100)
      linarith
    have h_c : ‖theta3 τ * theta4 τ ^ 2‖ ≤ 1000 := by
      rw [norm_mul, norm_pow]
      have := mul_le_mul h3 h4_pow2 (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 10)
      linarith
    have h_d : ‖theta4 τ ^ 3‖ ≤ 1000 := by rw [norm_pow]; exact h4_pow3
    have h_add1 :
        ‖theta3 τ ^ 3 + theta3 τ ^ 2 * theta4 τ + theta3 τ * theta4 τ ^ 2 + theta4 τ ^ 3‖
          ≤ ‖theta3 τ ^ 3 + theta3 τ ^ 2 * theta4 τ + theta3 τ * theta4 τ ^ 2‖
              + ‖theta4 τ ^ 3‖ := norm_add_le _ _
    have h_add2 :
        ‖theta3 τ ^ 3 + theta3 τ ^ 2 * theta4 τ + theta3 τ * theta4 τ ^ 2‖
          ≤ ‖theta3 τ ^ 3 + theta3 τ ^ 2 * theta4 τ‖ + ‖theta3 τ * theta4 τ ^ 2‖ :=
      norm_add_le _ _
    have h_add3 :
        ‖theta3 τ ^ 3 + theta3 τ ^ 2 * theta4 τ‖
          ≤ ‖theta3 τ ^ 3‖ + ‖theta3 τ ^ 2 * theta4 τ‖ := norm_add_le _ _
    linarith
  -- `‖θ₃⁴ − θ₄⁴‖ = ‖(θ₃ − θ₄)·(θ₃³ + θ₃²θ₄ + θ₃θ₄² + θ₄³)‖ ≤ 100·exp(−π·τ.im)·4000`.
  have h_diff_eq : theta3 τ ^ 4 - theta4 τ ^ 4
      = (theta3 τ - theta4 τ)
        * (theta3 τ ^ 3 + theta3 τ ^ 2 * theta4 τ
            + theta3 τ * theta4 τ ^ 2 + theta4 τ ^ 3) := by ring
  have h_diff_norm :
      ‖theta3 τ ^ 4 - theta4 τ ^ 4‖
        ≤ 100 * Real.exp (-Real.pi * τ.im) * 4000 := by
    rw [h_diff_eq, norm_mul]
    exact mul_le_mul h34 h_quart_norm (norm_nonneg _)
      (by positivity)
  -- `‖f‖ ≤ ‖θ₂⁴‖ + ‖θ₃⁴ − θ₄⁴‖ ≤ 410000·exp(−π·τ.im)`.
  have h_f_decomp : theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4
      = theta2 τ ^ 4 - (theta3 τ ^ 4 - theta4 τ ^ 4) := by ring
  have h_f_norm :
      ‖theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4‖
        ≤ 410000 * Real.exp (-Real.pi * τ.im) := by
    rw [h_f_decomp]
    have h_step : ‖theta2 τ ^ 4 - (theta3 τ ^ 4 - theta4 τ ^ 4)‖
        ≤ ‖theta2 τ ^ 4‖ + ‖theta3 τ ^ 4 - theta4 τ ^ 4‖ := norm_sub_le _ _
    have h_sum :
        10000 * Real.exp (-Real.pi * τ.im) + 100 * Real.exp (-Real.pi * τ.im) * 4000
          = 410000 * Real.exp (-Real.pi * τ.im) := by ring
    linarith
  -- `‖f²‖ = ‖f‖² ≤ (410000)²·exp(−2π·τ.im) ≤ 10¹²·exp(−π·τ.im)`.
  rw [norm_pow]
  have h_sq_le : ‖theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4‖ ^ 2
      ≤ (410000 * Real.exp (-Real.pi * τ.im)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h_f_norm 2
  refine h_sq_le.trans ?_
  rw [mul_pow]
  -- `exp(−π·τ.im)^2 = exp(−π·τ.im) · exp(−π·τ.im) ≤ exp(−π·τ.im) · 1`.
  have h_exp_sq : (Real.exp (-Real.pi * τ.im)) ^ 2
      ≤ Real.exp (-Real.pi * τ.im) := by
    rw [sq]
    nlinarith
  have h_410k_sq_pos : (0 : ℝ) ≤ (410000 : ℝ) ^ 2 := by positivity
  have h_step1 :
      (410000 : ℝ) ^ 2 * (Real.exp (-Real.pi * τ.im)) ^ 2
        ≤ (410000 : ℝ) ^ 2 * Real.exp (-Real.pi * τ.im) :=
    mul_le_mul_of_nonneg_left h_exp_sq h_410k_sq_pos
  refine h_step1.trans ?_
  -- `(410000)² ≤ 10¹²`.
  have h_const_le : (410000 : ℝ) ^ 2 ≤ 10 ^ 12 := by norm_num
  exact mul_le_mul_of_nonneg_right h_const_le h_exp_nn

/-- **Weight-4 cusp form vanishing principle** (architectural). A
holomorphic function `g` on the upper half-plane that is
`T`-invariant (`g(τ + 1) = g(τ)`), transforms under `S` with
weight 4 (`g(−1/τ) = τ⁴ · g(τ)`), and decays exponentially at the
cusp `+i∞` must be identically zero on `ℍ`.

**Mathematical content.** The space `S_4(SL(2, ℤ))` of weight-4
cusp forms for the full modular group is zero-dimensional.
A concrete proof uses the `Δ`-division route: given a weight-4
cusp form `g`, the quotient `g² / Δ` is a weight `8 − 12 = −4`
modular form (since `g²` has weight 8, vanishes to order ≥ 2 at
the cusp, while `Δ` has weight 12 and vanishes to order exactly 1
at the cusp; the quotient is holomorphic on `ℍ` because Mathlib's
`delta_ne_zero` holds, and bounded at the cusp because `2 − 1 ≥ 1`).
By Mathlib's `levelOne_neg_weight_eq_zero` (a negative-weight
modular form for `SL(2, ℤ)` is identically zero), `g² / Δ = 0`,
hence `g = 0`.

**Mathlib bridges used to close this lemma.**
1. Bridging the bare `ℂ → ℂ` hypotheses to a Mathlib
   `CuspForm Γ(1) 4`. The `T` and `S` invariance hypotheses give
   slash invariance on the two generators; the full
   `SlashInvariantForm Γ(1) 4` slash invariance is obtained via
   `SpecialLinearGroup.SL2Z_generators` + `Subgroup.closure_induction`
   (the pattern used in Mathlib's `EisensteinSeries.E2.Transform`).
2. Bridging Mathlib's `delta : ℍ → ℂ` to a packaged `CuspForm Γ(1) 12`.
   Mathlib has `delta_T_invariant`, `delta_S_invariant`,
   `delta_ne_zero`, which assemble into the bundled cusp-form
   instance.
3. Constructing the quotient `g² / Δ` as a `ModularForm Γ(1) (−4)`
   from the two packaged forms via a custom modular-form division
   construction (no off-the-shelf Mathlib API).
4. The endpoint `levelOne_neg_weight_eq_zero` from Mathlib applies
   once the quotient is packaged. -/
theorem holomorphic_weight4_modform_cusp_vanishes
    {g : ℂ → ℂ}
    (h_holo : DifferentiableOn ℂ g { τ : ℂ | 0 < τ.im })
    (h_T : ∀ τ : ℂ, 0 < τ.im → g (τ + 1) = g τ)
    (h_S : ∀ τ : ℂ, 0 < τ.im → g (-1 / τ) = τ ^ 4 * g τ)
    (h_cusp : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℂ, 1 ≤ τ.im →
        ‖g τ‖ ≤ C * Real.exp (-Real.pi * τ.im))
    {τ : ℂ} (hτ : 0 < τ.im) :
    g τ = 0 := by
  -- The bridge constructs a `CuspForm Γ(1) 4` from the bare hypotheses
  -- and applies the weight-4 vanishing principle. Concretely:
  -- (a) `g_H := fun σ : ℍ => g σ` is `T`-, `S`-, and SL(2,ℤ)-slash-invariant
  --     of weight 4 (via the bridge `slash_T_eq_of_T_invariant`,
  --     `slash_S_eq_of_S_weight_k`, and `slashInvariant_via_S_T_in_SL2Z`);
  -- (b) `g_H` is `MDiff` (via `mdiff_of_differentiableOn_upperHalfPlane`);
  -- (c) `g_H` vanishes at `+i∞` (via `isZeroAtImInfty_of_exp_decay`);
  --     by `OnePoint.isZeroAt_iff_forall_SL2Z`, this extends to all cusps
  --     using slash invariance.
  -- Then `CuspForm.mk g_H ... : CuspForm Γ(1) 4`, and
  -- `weight4_levelOne_cuspForm_vanishes` gives `g_H = 0`, hence `g τ = 0`.
  set g_H : UpperHalfPlane → ℂ := fun σ => g (↑σ : ℂ) with hg_H_def
  -- Slash invariance under T, S, and the full SL(2, ℤ).
  have h_T_slash : g_H ∣[(4 : ℤ)] ModularGroup.T = g_H :=
    slash_T_eq_of_T_invariant h_T
  have h_S_slash : g_H ∣[(4 : ℤ)] ModularGroup.S = g_H :=
    slash_S_eq_of_S_weight_k h_S
  have h_slash_SL : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      g_H ∣[(4 : ℤ)] γ = g_H := fun γ =>
    slashInvariant_via_S_T_in_SL2Z h_S_slash h_T_slash γ
  -- Manifold differentiability and cusp vanishing.
  have h_mdiff : MDiff g_H := mdiff_of_differentiableOn_upperHalfPlane h_holo
  have h_zero : IsZeroAtImInfty g_H := isZeroAtImInfty_of_exp_decay h_cusp
  -- Bundle as a CuspForm Γ(1) 4.
  let F : CuspForm Γ(1) 4 :=
  { toFun := g_H
    slash_action_eq' := by
      intro γ_GL hγ_GL
      obtain ⟨g_SL, _hg_SL_mem, h_eq⟩ := hγ_GL
      have h := h_slash_SL g_SL
      rw [ModularForm.SL_slash] at h
      rw [← h_eq]
      exact h
    holo' := h_mdiff
    zero_at_cusps' := by
      intro c hc
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
      rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
      intro γ _hγ
      rw [h_slash_SL γ]
      exact h_zero }
  -- Apply the bridge's `weight4_levelOne_cuspForm_vanishes`.
  have h_F_zero : F ⟨τ, hτ⟩ = 0 := weight4_levelOne_cuspForm_vanishes F ⟨τ, hτ⟩
  -- `F ⟨τ, hτ⟩ = g_H ⟨τ, hτ⟩ = g τ` by definition.
  exact h_F_zero

/-- **Jacobi's identity**: `θ₂(τ)⁴ + θ₄(τ)⁴ = θ₃(τ)⁴` on the upper
half-plane. Setting `g(τ) := (θ₂(τ)⁴ + θ₄(τ)⁴ − θ₃(τ)⁴)²`, the
proven transformations `jacobi_diff_sq_T_smul` and
`jacobi_diff_sq_S_smul` show `g` is a holomorphic, weight-4 modular
form for `SL(2, ℤ)`. The cusp bound `jacobi_diff_sq_cusp_bound`
shows `g` vanishes at `+i∞`. By the weight-4 cusp form vanishing
principle (`holomorphic_weight4_modform_cusp_vanishes`),
`g ≡ 0`; hence `f ≡ 0` and Jacobi's identity follows. -/
theorem jacobi_identity {τ : ℂ} (hτ : 0 < τ.im) :
    theta2 τ ^ 4 + theta4 τ ^ 4 = theta3 τ ^ 4 := by
  have h_zero : (theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4) ^ 2 = 0 :=
    holomorphic_weight4_modform_cusp_vanishes
      (g := fun σ => (theta2 σ ^ 4 + theta4 σ ^ 4 - theta3 σ ^ 4) ^ 2)
      jacobi_diff_sq_differentiableOn
      (fun σ _ => jacobi_diff_sq_T_smul σ)
      (fun σ hσ => jacobi_diff_sq_S_smul hσ)
      jacobi_diff_sq_cusp_bound
      hτ
  have h_diff_zero : theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4 = 0 :=
    (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h_zero
  linear_combination h_diff_zero

/-! ## Non-vanishing of `θ₂`, `θ₃`, `θ₄` on `ℍ`

The full-ℍ non-vanishing theorems `theta2_ne_zero`, `theta3_ne_zero`,
`theta4_ne_zero` are proved later in this file (after the half-regime
lemmas and the SL(2,ℤ)-reduction infrastructure). They are obtained by
combining the easy-regime non-vanishing (`theta_i_ne_zero_of_im_ge_half`)
with the SL(2,ℤ)-invariance of the predicate `all_theta_ne_zero`. -/

/-- For `τ` with imaginary part at least one, the bound
`‖jacobiTheta τ − 1‖ ≤ 2·exp(−π·τ.im)/(1 − exp(−π·τ.im))` is strictly less
than one (since `exp(−π) < 1/3`), so `jacobiTheta τ ≠ 0`. This is the
easy regime of the general non-vanishing claim. -/
theorem theta3_ne_zero_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    theta3 τ ≠ 0 := by
  unfold theta3
  have hτ_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have h_bound : ‖jacobiTheta τ - 1‖ ≤
      2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) :=
    norm_jacobiTheta_sub_one_le hτ_pos
  -- Let x = exp(-π · τ.im); show x < 1/3, hence 2x/(1-x) < 1.
  set x := Real.exp (-Real.pi * τ.im) with hx_def
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have h_x_pos : 0 < x := Real.exp_pos _
  have h_x_le : x ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h_exp_neg_pi : Real.exp (-Real.pi) < 1 / 3 := by
    have h_pi : 3 < Real.pi := Real.pi_gt_three
    have h_exp_3 : (3 : ℝ) < Real.exp 3 := by
      have h1 : (3 : ℝ) + 1 ≤ Real.exp 3 := Real.add_one_le_exp 3
      linarith
    have h_exp_pi : Real.exp 3 < Real.exp Real.pi := Real.exp_lt_exp.mpr h_pi
    have h3_lt_exp_pi : (3 : ℝ) < Real.exp Real.pi := lt_trans h_exp_3 h_exp_pi
    have h_exp_pi_pos : 0 < Real.exp Real.pi := Real.exp_pos _
    rw [Real.exp_neg, inv_lt_comm₀ h_exp_pi_pos (by norm_num : (0 : ℝ) < 1 / 3)]
    rw [show (1 / 3 : ℝ)⁻¹ = 3 from by norm_num]
    exact h3_lt_exp_pi
  have h_x_lt_third : x < 1 / 3 := lt_of_le_of_lt h_x_le h_exp_neg_pi
  have h_one_sub_x_pos : 0 < 1 - x := by linarith
  have h_bound_lt_one : 2 / (1 - x) * x < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one h_one_sub_x_pos]
    linarith
  have h_norm_lt : ‖jacobiTheta τ - 1‖ < 1 := lt_of_le_of_lt h_bound h_bound_lt_one
  intro h_zero
  rw [h_zero, zero_sub, norm_neg, norm_one] at h_norm_lt
  exact lt_irrefl 1 h_norm_lt

/-- Easy-regime non-vanishing for `θ₄`. Reduces to
`theta3_ne_zero_of_im_ge_one` via `θ₄ τ = θ₃ (τ + 1)` and the fact that
`Im(τ + 1) = Im τ`. -/
theorem theta4_ne_zero_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    theta4 τ ≠ 0 := by
  rw [show theta4 τ = theta3 (τ + 1) from (theta3_add_one τ).symm]
  apply theta3_ne_zero_of_im_ge_one
  simp [Complex.add_im, hτ]

/-- **Easy-regime non-vanishing for `θ₂`.** For `τ.im ≥ 1`,
`θ₂(τ) = exp(πiτ/4) · jacobiTheta₂(τ/2, τ)`, where the leading two
terms of `jacobiTheta₂(τ/2, τ)` at `n = 0, −1` both equal `1`, giving
`jacobiTheta₂(τ/2, τ) = 2 + r(τ)`. The remainder is bounded by the
geometric series `2·s/(1 − s) ≤ 1` where `s = exp(−2π·τ.im) ≤ 1/3`
(via `Real.add_one_le_exp 2 ⇒ exp(2π) ≥ 3`), so
`‖jacobiTheta₂(τ/2, τ)‖ ≥ 2 − 1 = 1 > 0` and `θ₂ ≠ 0` since
`exp(πiτ/4) ≠ 0`. -/
theorem theta2_ne_zero_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    theta2 τ ≠ 0 := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- `s = exp(−2π·τ.im) ≤ 1/3` for τ.im ≥ 1.
  set s : ℝ := Real.exp (-2 * Real.pi * τ.im) with hs_def
  have hs_pos : 0 < s := Real.exp_pos _
  have hs_le_third : s ≤ 1/3 := by
    rw [hs_def, show (-2 * Real.pi * τ.im : ℝ) = -(2 * Real.pi * τ.im) from by ring,
        Real.exp_neg,
        inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/3),
        show (1/3 : ℝ)⁻¹ = 3 from by norm_num]
    have h_3_le_exp_2 : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ); linarith
    have h_2_le_2piτ : (2 : ℝ) ≤ 2 * Real.pi * τ.im := by
      have h_pi_3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
      have h_2pi_pos : 0 < 2 * Real.pi := by positivity
      nlinarith
    linarith [Real.exp_le_exp.mpr h_2_le_2piτ]
  have hs_lt_one : s < 1 := by linarith
  have h_one_sub_s_pos : 0 < 1 - s := by linarith
  -- 2·((1-s)⁻¹ - 1) ≤ 1.
  have h_int_sum_le_one : (1 - s)⁻¹ - 1 + ((1 - s)⁻¹ - 1) ≤ 1 := by
    have h_inv_eq : (1 - s)⁻¹ - 1 = s / (1 - s) := by
      field_simp; ring
    rw [h_inv_eq]
    rw [show s/(1-s) + s/(1-s) = 2*s/(1-s) from by ring]
    rw [div_le_one h_one_sub_s_pos]; linarith
  -- HasSum for the (skipped) geometric series.
  have h_geo : HasSum (fun m : ℕ => s ^ m) ((1 - s)⁻¹) :=
    hasSum_geometric_of_lt_one hs_pos.le hs_lt_one
  have h_skip_geo : HasSum (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m)
                          ((1 - s)⁻¹ - 1) := by
    have h_step := hasSum_ite_sub_hasSum h_geo 0
    simp only [pow_zero] at h_step
    exact h_step
  -- Sum over ℤ via Int.rec.
  have h_int_rec : HasSum
      (fun n : ℤ => Int.rec (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m)
                            (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m) n)
      ((1 - s)⁻¹ - 1 + ((1 - s)⁻¹ - 1)) :=
    HasSum.int_rec h_skip_geo h_skip_geo
  -- HasSum for jacobiTheta₂ - 2, by skipping terms at n=0 and n=-1.
  have h_jt_hasSum := hasSum_jacobiTheta₂_term (τ / 2) hτim_pos
  have h_zim : (τ / 2 : ℂ).im = τ.im / 2 := by simp
  -- Show term_0 = 1 and term_{-1} = 1.
  have h_term_0 : jacobiTheta₂_term 0 (τ / 2) τ = 1 := by
    simp [jacobiTheta₂_term]
  have h_term_neg1 : jacobiTheta₂_term (-1) (τ / 2) τ = 1 := by
    rw [jacobiTheta₂_term]
    have h_zero : 2 * (Real.pi : ℂ) * Complex.I * ((-1 : ℤ) : ℂ) * (τ/2)
        + (Real.pi : ℂ) * Complex.I * (((-1 : ℤ) : ℂ)) ^ 2 * τ = 0 := by
      push_cast; ring
    rw [h_zero]; exact Complex.exp_zero
  -- Skip n=0 from jacobiTheta₂.
  have h_skip_0 : HasSum
      (fun n : ℤ => if n = 0 then (0 : ℂ) else jacobiTheta₂_term n (τ / 2) τ)
      (jacobiTheta₂ (τ / 2) τ - 1) := by
    have h_step := hasSum_ite_sub_hasSum h_jt_hasSum 0
    rw [h_term_0] at h_step
    exact h_step
  -- Skip n=-1 from the result.
  have h_skip_both : HasSum
      (fun n : ℤ => if n = -1 then (0 : ℂ)
                    else if n = 0 then (0 : ℂ) else jacobiTheta₂_term n (τ / 2) τ)
      (jacobiTheta₂ (τ / 2) τ - 1 - 1) := by
    have h_step := hasSum_ite_sub_hasSum h_skip_0 (-1)
    have h_at_neg1 :
        (if ((-1 : ℤ)) = 0 then (0 : ℂ) else jacobiTheta₂_term (-1) (τ / 2) τ) = 1 := by
      simp [h_term_neg1]
    rw [h_at_neg1] at h_step
    exact h_step
  -- Per-term norm bound.
  have h_term_bound : ∀ n : ℤ,
      ‖(if n = -1 then (0 : ℂ)
        else if n = 0 then (0 : ℂ) else jacobiTheta₂_term n (τ / 2) τ)‖
        ≤ Int.rec (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m)
                  (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m) n := by
    intro n
    cases n with
    | ofNat m =>
      by_cases hm : m = 0
      · subst hm; simp
      · have hn_ne_neg1 : (Int.ofNat m : ℤ) ≠ -1 := by
          have h_nn : (0 : ℤ) ≤ Int.ofNat m := Int.natCast_nonneg m
          omega
        have hn_ne_0 : (Int.ofNat m : ℤ) ≠ 0 := by
          change ((m : ℕ) : ℤ) ≠ 0
          exact_mod_cast hm
        rw [if_neg hn_ne_neg1, if_neg hn_ne_0]
        change ‖jacobiTheta₂_term (Int.ofNat m) (τ/2) τ‖ ≤
               (if m = 0 then (0 : ℝ) else s ^ m)
        rw [if_neg hm, norm_jacobiTheta₂_term, h_zim,
            hs_def, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have h_cast : ((Int.ofNat m : ℤ) : ℝ) = (m : ℝ) := by simp
        rw [h_cast]
        have h_m_pos : 1 ≤ (m : ℝ) := by
          have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
          exact_mod_cast this
        -- Goal: -π·m²·τ.im - 2π·m·(τ.im/2) ≤ m·(-2π·τ.im)
        -- ⟺ π·m·τ.im·(m - 1) ≥ 0.
        have h_key : 0 ≤ Real.pi * (m : ℝ) * τ.im * ((m : ℝ) - 1) := by
          have h_m_nn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
          have h_m_sub_nn : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
          exact mul_nonneg (mul_nonneg (mul_nonneg hπ_pos.le h_m_nn) hτim_pos.le) h_m_sub_nn
        nlinarith [h_key]
    | negSucc m =>
      by_cases hm : m = 0
      · subst hm; simp
      · have hn_ne_neg1 : (Int.negSucc m : ℤ) ≠ -1 := by
          intro h
          have : Int.negSucc m = -↑(m + 1) := rfl
          rw [this] at h; omega
        have hn_ne_0 : (Int.negSucc m : ℤ) ≠ 0 := by
          intro h
          have : Int.negSucc m = -↑(m + 1) := rfl
          rw [this] at h; omega
        rw [if_neg hn_ne_neg1, if_neg hn_ne_0]
        change ‖jacobiTheta₂_term (Int.negSucc m) (τ/2) τ‖ ≤
               (if m = 0 then (0 : ℝ) else s ^ m)
        rw [if_neg hm, norm_jacobiTheta₂_term, h_zim,
            hs_def, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have h_cast : ((Int.negSucc m : ℤ) : ℝ) = -((m : ℝ) + 1) := by
          rw [Int.cast_negSucc]; push_cast; ring
        rw [h_cast]
        have h_m_pos : 1 ≤ (m : ℝ) := by
          have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
          exact_mod_cast this
        -- After substituting, LHS = -π·τ.im·(m+1)·m, RHS = -2π·τ.im·m.
        -- Need: -π·τ.im·m·(m+1) ≤ -2π·τ.im·m ⟺ m+1 ≥ 2 ⟺ m ≥ 1.
        have h_key : 0 ≤ Real.pi * (m : ℝ) * τ.im * ((m : ℝ) - 1) := by
          have h_m_nn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
          have h_m_sub_nn : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
          exact mul_nonneg (mul_nonneg (mul_nonneg hπ_pos.le h_m_nn) hτim_pos.le) h_m_sub_nn
        nlinarith [h_key]
  -- Apply tsum_of_norm_bounded.
  have h_norm_le : ‖jacobiTheta₂ (τ / 2) τ - 1 - 1‖
      ≤ (1 - s)⁻¹ - 1 + ((1 - s)⁻¹ - 1) := by
    rw [← h_skip_both.tsum_eq]
    exact tsum_of_norm_bounded h_int_rec h_term_bound
  have h_norm_diff_le_one : ‖jacobiTheta₂ (τ / 2) τ - 2‖ ≤ 1 := by
    have h_eq : jacobiTheta₂ (τ / 2) τ - 2 = jacobiTheta₂ (τ / 2) τ - 1 - 1 := by ring
    rw [h_eq]; linarith
  -- ‖jacobiTheta₂‖ ≥ 1 via reverse triangle.
  have h_jt_norm_ge : (1 : ℝ) ≤ ‖jacobiTheta₂ (τ / 2) τ‖ := by
    have h_rev : ‖(2 : ℂ)‖ - ‖(2 : ℂ) - jacobiTheta₂ (τ / 2) τ‖
        ≤ ‖(2 : ℂ) - ((2 : ℂ) - jacobiTheta₂ (τ / 2) τ)‖ :=
      norm_sub_norm_le (2 : ℂ) ((2 : ℂ) - jacobiTheta₂ (τ / 2) τ)
    have h_simp : (2 : ℂ) - ((2 : ℂ) - jacobiTheta₂ (τ / 2) τ) = jacobiTheta₂ (τ / 2) τ := by ring
    rw [h_simp] at h_rev
    have h_two_norm : ‖(2 : ℂ)‖ = 2 := by simp
    have h_eq_neg : (2 : ℂ) - jacobiTheta₂ (τ / 2) τ = -(jacobiTheta₂ (τ / 2) τ - 2) := by ring
    rw [h_two_norm, h_eq_neg, norm_neg] at h_rev
    linarith
  -- Conclude theta2 ≠ 0.
  intro h_zero
  unfold theta2 at h_zero
  have h_exp_ne : Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4) ≠ 0 :=
    Complex.exp_ne_zero _
  rcases mul_eq_zero.mp h_zero with h | h
  · exact h_exp_ne h
  · rw [h, norm_zero] at h_jt_norm_ge
    linarith

/-- **Extended-regime non-vanishing for `θ₃`** (`im ≥ 1/2`). Same
proof shape as `theta3_ne_zero_of_im_ge_one`, but the numeric bound
`exp(−π/2) < 1/3` uses `Real.quadratic_le_exp_of_nonneg` at `π/2`
to get `exp(π/2) ≥ 1 + π/2 + (π/2)²/2 > 3` from `π > 3`. The lower
threshold `1/2` is compatible with `SL(2,ℤ)`-reduction
(`ModularGroup.exists_one_half_le_im_smul`) and is needed for
bridging to the full upper half-plane via the modular action. -/
theorem theta3_ne_zero_of_im_ge_half {τ : ℂ} (hτ : 1 / 2 ≤ τ.im) :
    theta3 τ ≠ 0 := by
  unfold theta3
  have hτ_pos : 0 < τ.im := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) hτ
  have h_bound : ‖jacobiTheta τ - 1‖ ≤
      2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) :=
    norm_jacobiTheta_sub_one_le hτ_pos
  set x := Real.exp (-Real.pi * τ.im) with hx_def
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have h_x_pos : 0 < x := Real.exp_pos _
  have h_x_le : x ≤ Real.exp (-Real.pi / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h_exp_neg_pi_half : Real.exp (-Real.pi / 2) < 1 / 3 := by
    have h_pi_gt_3 : 3 < Real.pi := Real.pi_gt_three
    have h_pi_half_nn : (0 : ℝ) ≤ Real.pi / 2 := by linarith
    have h_quad : 1 + Real.pi/2 + (Real.pi/2)^2 / 2 ≤ Real.exp (Real.pi/2) :=
      Real.quadratic_le_exp_of_nonneg h_pi_half_nn
    have h_3_lt_quad : (3 : ℝ) < 1 + Real.pi/2 + (Real.pi/2)^2 / 2 := by nlinarith
    have h_3_lt_exp_pi_half : (3 : ℝ) < Real.exp (Real.pi/2) :=
      lt_of_lt_of_le h_3_lt_quad h_quad
    have h_exp_pi_half_pos : 0 < Real.exp (Real.pi/2) := Real.exp_pos _
    rw [show (-Real.pi / 2 : ℝ) = -(Real.pi/2) from by ring, Real.exp_neg,
        inv_lt_comm₀ h_exp_pi_half_pos (by norm_num : (0 : ℝ) < 1 / 3),
        show (1 / 3 : ℝ)⁻¹ = 3 from by norm_num]
    exact h_3_lt_exp_pi_half
  have h_x_lt_third : x < 1 / 3 := lt_of_le_of_lt h_x_le h_exp_neg_pi_half
  have h_one_sub_x_pos : 0 < 1 - x := by linarith
  have h_bound_lt_one : 2 / (1 - x) * x < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one h_one_sub_x_pos]; linarith
  have h_norm_lt : ‖jacobiTheta τ - 1‖ < 1 := lt_of_le_of_lt h_bound h_bound_lt_one
  intro h_zero
  rw [h_zero, zero_sub, norm_neg, norm_one] at h_norm_lt
  exact lt_irrefl 1 h_norm_lt

/-- Extended-regime non-vanishing for `θ₄`. Reduces to
`theta3_ne_zero_of_im_ge_half` via `θ₄ τ = θ₃ (τ + 1)`. -/
theorem theta4_ne_zero_of_im_ge_half {τ : ℂ} (hτ : 1 / 2 ≤ τ.im) :
    theta4 τ ≠ 0 := by
  rw [show theta4 τ = theta3 (τ + 1) from (theta3_add_one τ).symm]
  apply theta3_ne_zero_of_im_ge_half
  rw [Complex.add_im]; simp; linarith

/-- **Extended-regime non-vanishing for `θ₂`** (`im ≥ 1/2`). Same
series-decomposition proof as `theta2_ne_zero_of_im_ge_one`, but the
numeric bound `s ≤ 1/3` (where `s = exp(−2π·τ.im)`) uses the simpler
`Real.add_one_le_exp π` (giving `exp(π) ≥ 1 + π ≥ 4 > 3`) — for
`τ.im ≥ 1/2`, `s ≤ exp(−π) ≤ 1/3`. -/
theorem theta2_ne_zero_of_im_ge_half {τ : ℂ} (hτ : 1 / 2 ≤ τ.im) :
    theta2 τ ≠ 0 := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) hτ
  have hπ_pos := Real.pi_pos
  set s : ℝ := Real.exp (-2 * Real.pi * τ.im) with hs_def
  have hs_pos : 0 < s := Real.exp_pos _
  have hs_le_third : s ≤ 1/3 := by
    rw [hs_def, show (-2 * Real.pi * τ.im : ℝ) = -(2 * Real.pi * τ.im) from by ring,
        Real.exp_neg,
        inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/3),
        show (1/3 : ℝ)⁻¹ = 3 from by norm_num]
    have h_pi_gt_3 : 3 < Real.pi := Real.pi_gt_three
    have h_pi_le_2pi_tau : Real.pi ≤ 2 * Real.pi * τ.im := by nlinarith
    have h_exp_le : Real.exp Real.pi ≤ Real.exp (2 * Real.pi * τ.im) :=
      Real.exp_le_exp.mpr h_pi_le_2pi_tau
    have h_3_le_exp_pi : (3 : ℝ) ≤ Real.exp Real.pi := by
      have := Real.add_one_le_exp Real.pi; linarith
    linarith
  have hs_lt_one : s < 1 := by linarith
  have h_one_sub_s_pos : 0 < 1 - s := by linarith
  have h_int_sum_le_one : (1 - s)⁻¹ - 1 + ((1 - s)⁻¹ - 1) ≤ 1 := by
    have h_inv_eq : (1 - s)⁻¹ - 1 = s / (1 - s) := by field_simp; ring
    rw [h_inv_eq]
    rw [show s/(1-s) + s/(1-s) = 2*s/(1-s) from by ring]
    rw [div_le_one h_one_sub_s_pos]; linarith
  have h_geo : HasSum (fun m : ℕ => s ^ m) ((1 - s)⁻¹) :=
    hasSum_geometric_of_lt_one hs_pos.le hs_lt_one
  have h_skip_geo : HasSum (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m)
                          ((1 - s)⁻¹ - 1) := by
    have h_step := hasSum_ite_sub_hasSum h_geo 0
    simp only [pow_zero] at h_step
    exact h_step
  have h_int_rec : HasSum
      (fun n : ℤ => Int.rec (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m)
                            (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m) n)
      ((1 - s)⁻¹ - 1 + ((1 - s)⁻¹ - 1)) :=
    HasSum.int_rec h_skip_geo h_skip_geo
  have h_jt_hasSum := hasSum_jacobiTheta₂_term (τ / 2) hτim_pos
  have h_zim : (τ / 2 : ℂ).im = τ.im / 2 := by simp
  have h_term_0 : jacobiTheta₂_term 0 (τ / 2) τ = 1 := by
    simp [jacobiTheta₂_term]
  have h_term_neg1 : jacobiTheta₂_term (-1) (τ / 2) τ = 1 := by
    rw [jacobiTheta₂_term]
    have h_zero : 2 * (Real.pi : ℂ) * Complex.I * ((-1 : ℤ) : ℂ) * (τ/2)
        + (Real.pi : ℂ) * Complex.I * (((-1 : ℤ) : ℂ)) ^ 2 * τ = 0 := by
      push_cast; ring
    rw [h_zero]; exact Complex.exp_zero
  have h_skip_0 : HasSum
      (fun n : ℤ => if n = 0 then (0 : ℂ) else jacobiTheta₂_term n (τ / 2) τ)
      (jacobiTheta₂ (τ / 2) τ - 1) := by
    have h_step := hasSum_ite_sub_hasSum h_jt_hasSum 0
    rw [h_term_0] at h_step
    exact h_step
  have h_skip_both : HasSum
      (fun n : ℤ => if n = -1 then (0 : ℂ)
                    else if n = 0 then (0 : ℂ) else jacobiTheta₂_term n (τ / 2) τ)
      (jacobiTheta₂ (τ / 2) τ - 1 - 1) := by
    have h_step := hasSum_ite_sub_hasSum h_skip_0 (-1)
    have h_at_neg1 :
        (if ((-1 : ℤ)) = 0 then (0 : ℂ) else jacobiTheta₂_term (-1) (τ / 2) τ) = 1 := by
      simp [h_term_neg1]
    rw [h_at_neg1] at h_step
    exact h_step
  have h_term_bound : ∀ n : ℤ,
      ‖(if n = -1 then (0 : ℂ)
        else if n = 0 then (0 : ℂ) else jacobiTheta₂_term n (τ / 2) τ)‖
        ≤ Int.rec (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m)
                  (fun m : ℕ => if m = 0 then (0 : ℝ) else s ^ m) n := by
    intro n
    cases n with
    | ofNat m =>
      by_cases hm : m = 0
      · subst hm; simp
      · have hn_ne_neg1 : (Int.ofNat m : ℤ) ≠ -1 := by
          have h_nn : (0 : ℤ) ≤ Int.ofNat m := Int.natCast_nonneg m
          omega
        have hn_ne_0 : (Int.ofNat m : ℤ) ≠ 0 := by
          change ((m : ℕ) : ℤ) ≠ 0
          exact_mod_cast hm
        rw [if_neg hn_ne_neg1, if_neg hn_ne_0]
        change ‖jacobiTheta₂_term (Int.ofNat m) (τ/2) τ‖ ≤
               (if m = 0 then (0 : ℝ) else s ^ m)
        rw [if_neg hm, norm_jacobiTheta₂_term, h_zim,
            hs_def, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have h_cast : ((Int.ofNat m : ℤ) : ℝ) = (m : ℝ) := by simp
        rw [h_cast]
        have h_m_pos : 1 ≤ (m : ℝ) := by
          have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
          exact_mod_cast this
        have h_key : 0 ≤ Real.pi * (m : ℝ) * τ.im * ((m : ℝ) - 1) := by
          have h_m_nn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
          have h_m_sub_nn : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
          exact mul_nonneg (mul_nonneg (mul_nonneg hπ_pos.le h_m_nn) hτim_pos.le) h_m_sub_nn
        nlinarith [h_key]
    | negSucc m =>
      by_cases hm : m = 0
      · subst hm; simp
      · have hn_ne_neg1 : (Int.negSucc m : ℤ) ≠ -1 := by
          intro h
          have : Int.negSucc m = -↑(m + 1) := rfl
          rw [this] at h; omega
        have hn_ne_0 : (Int.negSucc m : ℤ) ≠ 0 := by
          intro h
          have : Int.negSucc m = -↑(m + 1) := rfl
          rw [this] at h; omega
        rw [if_neg hn_ne_neg1, if_neg hn_ne_0]
        change ‖jacobiTheta₂_term (Int.negSucc m) (τ/2) τ‖ ≤
               (if m = 0 then (0 : ℝ) else s ^ m)
        rw [if_neg hm, norm_jacobiTheta₂_term, h_zim,
            hs_def, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have h_cast : ((Int.negSucc m : ℤ) : ℝ) = -((m : ℝ) + 1) := by
          rw [Int.cast_negSucc]; push_cast; ring
        rw [h_cast]
        have h_m_pos : 1 ≤ (m : ℝ) := by
          have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
          exact_mod_cast this
        have h_key : 0 ≤ Real.pi * (m : ℝ) * τ.im * ((m : ℝ) - 1) := by
          have h_m_nn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
          have h_m_sub_nn : (0 : ℝ) ≤ (m : ℝ) - 1 := by linarith
          exact mul_nonneg (mul_nonneg (mul_nonneg hπ_pos.le h_m_nn) hτim_pos.le) h_m_sub_nn
        nlinarith [h_key]
  have h_norm_le : ‖jacobiTheta₂ (τ / 2) τ - 1 - 1‖
      ≤ (1 - s)⁻¹ - 1 + ((1 - s)⁻¹ - 1) := by
    rw [← h_skip_both.tsum_eq]
    exact tsum_of_norm_bounded h_int_rec h_term_bound
  have h_norm_diff_le_one : ‖jacobiTheta₂ (τ / 2) τ - 2‖ ≤ 1 := by
    have h_eq : jacobiTheta₂ (τ / 2) τ - 2 = jacobiTheta₂ (τ / 2) τ - 1 - 1 := by ring
    rw [h_eq]; linarith
  have h_jt_norm_ge : (1 : ℝ) ≤ ‖jacobiTheta₂ (τ / 2) τ‖ := by
    have h_rev : ‖(2 : ℂ)‖ - ‖(2 : ℂ) - jacobiTheta₂ (τ / 2) τ‖
        ≤ ‖(2 : ℂ) - ((2 : ℂ) - jacobiTheta₂ (τ / 2) τ)‖ :=
      norm_sub_norm_le (2 : ℂ) ((2 : ℂ) - jacobiTheta₂ (τ / 2) τ)
    have h_simp : (2 : ℂ) - ((2 : ℂ) - jacobiTheta₂ (τ / 2) τ) = jacobiTheta₂ (τ / 2) τ := by ring
    rw [h_simp] at h_rev
    have h_two_norm : ‖(2 : ℂ)‖ = 2 := by simp
    have h_eq_neg : (2 : ℂ) - jacobiTheta₂ (τ / 2) τ = -(jacobiTheta₂ (τ / 2) τ - 2) := by ring
    rw [h_two_norm, h_eq_neg, norm_neg] at h_rev
    linarith
  intro h_zero
  unfold theta2 at h_zero
  have h_exp_ne : Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4) ≠ 0 :=
    Complex.exp_ne_zero _
  rcases mul_eq_zero.mp h_zero with h | h
  · exact h_exp_ne h
  · rw [h, norm_zero] at h_jt_norm_ge
    linarith

/-! ### `SL(2,ℤ)`-reduction: extending non-vanishing to all of `ℍ` -/

/-- All three theta nullwerte are simultaneously nonzero at `τ`.
This is the orbit-invariant predicate under the `SL(2,ℤ)`-action,
since `SL(2,ℤ)` permutes `{θ₂, θ₃, θ₄}` modulo nonzero factors. -/
def all_theta_ne_zero (τ : ℂ) : Prop :=
  theta2 τ ≠ 0 ∧ theta3 τ ≠ 0 ∧ theta4 τ ≠ 0

/-- Easy-regime version of `all_theta_ne_zero` for `τ.im ≥ 1/2`. -/
theorem all_theta_ne_zero_of_im_ge_half {τ : ℂ} (hτ : 1 / 2 ≤ τ.im) :
    all_theta_ne_zero τ :=
  ⟨theta2_ne_zero_of_im_ge_half hτ,
   theta3_ne_zero_of_im_ge_half hτ,
   theta4_ne_zero_of_im_ge_half hτ⟩

/-- T-invariance: `all_theta_ne_zero (τ + 1) ↔ all_theta_ne_zero τ`.
Uses `theta2_add_one`, `theta3_add_one`, `theta4_add_one`; the T-shift
permutes `θ₃ ↔ θ₄` and rescales `θ₂` by the nonzero `exp(πi/4)`. -/
theorem all_theta_ne_zero_T_iff (τ : ℂ) :
    all_theta_ne_zero (τ + 1) ↔ all_theta_ne_zero τ := by
  unfold all_theta_ne_zero
  rw [theta2_add_one, theta3_add_one, theta4_add_one]
  have h_exp_ne : Complex.exp ((Real.pi : ℂ) * Complex.I / 4) ≠ 0 :=
    Complex.exp_ne_zero _
  constructor
  · rintro ⟨h2, h3, h4⟩
    exact ⟨(mul_ne_zero_iff.mp h2).2, h4, h3⟩
  · rintro ⟨h2, h3, h4⟩
    exact ⟨mul_ne_zero h_exp_ne h2, h4, h3⟩

/-- S-invariance: `all_theta_ne_zero (-1/τ) ↔ all_theta_ne_zero τ`
for `τ ∈ ℍ`. Uses `theta2_S_smul`, `theta3_S_smul`, `theta4_S_smul`;
the S-action permutes `θ₂ ↔ θ₄` (fixing `θ₃`) and rescales by the
nonzero `(−iτ)^{1/2}`. -/
theorem all_theta_ne_zero_S_iff {τ : ℂ} (hτ : 0 < τ.im) :
    all_theta_ne_zero (-1 / τ) ↔ all_theta_ne_zero τ := by
  unfold all_theta_ne_zero
  rw [theta2_S_smul hτ, theta3_S_smul hτ, theta4_S_smul hτ]
  have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hτ
  have h_mIτ_ne : -Complex.I * τ ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ_ne
  have h_factor_ne : (-Complex.I * τ) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl h_mIτ_ne)
  constructor
  · rintro ⟨h2, h3, h4⟩
    refine ⟨(mul_ne_zero_iff.mp h4).2, (mul_ne_zero_iff.mp h3).2, (mul_ne_zero_iff.mp h2).2⟩
  · rintro ⟨h2, h3, h4⟩
    exact ⟨mul_ne_zero h_factor_ne h4, mul_ne_zero h_factor_ne h3, mul_ne_zero h_factor_ne h2⟩

/-- **Main SL(2,ℤ)-invariance of `all_theta_ne_zero`.** For any
`γ ∈ SL(2,ℤ)` and any `τ ∈ ℍ`,
`all_theta_ne_zero ((γ • τ) : ℂ) ↔ all_theta_ne_zero (τ : ℂ)`. Proved
by `Subgroup.closure_induction` on `SpecialLinearGroup.SL2Z_generators`,
using `all_theta_ne_zero_T_iff` and `all_theta_ne_zero_S_iff` on the
generators. -/
theorem all_theta_ne_zero_smul_iff_SL2Z (γ : SL(2, ℤ)) :
    ∀ τ : UpperHalfPlane,
      all_theta_ne_zero ((γ • τ : UpperHalfPlane) : ℂ) ↔ all_theta_ne_zero (τ : ℂ) := by
  have hmem : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | one =>
    intro τ; rw [one_smul]
  | mem g hg =>
    intro τ
    rcases hg with h | h
    · -- g = S
      subst h
      rw [UpperHalfPlane.modular_S_smul]
      change all_theta_ne_zero ((-(τ : ℂ))⁻¹) ↔ _
      rw [show (-(τ : ℂ))⁻¹ = -1 / (τ : ℂ) from by field_simp]
      exact all_theta_ne_zero_S_iff τ.2
    · -- g = T
      subst h
      rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
      rw [show (((1 : ℝ) : ℂ) + (τ : ℂ)) = (τ : ℂ) + 1 from by push_cast; ring]
      exact all_theta_ne_zero_T_iff (τ : ℂ)
  | mul g h _ _ ig ih =>
    intro τ
    rw [mul_smul]
    exact (ig (h • τ)).trans (ih τ)
  | inv g _ ig =>
    intro τ
    have h_id : g • (g⁻¹ • τ : UpperHalfPlane) = τ := by
      rw [← mul_smul, mul_inv_cancel, one_smul]
    have h := ig (g⁻¹ • τ)
    rw [h_id] at h
    exact h.symm

/-- **Full-`ℍ` theta non-vanishing.** For any `τ ∈ ℍ`, all three theta
nullwerte are nonzero. Applies `SL(2,ℤ)`-reduction (Mathlib's
`ModularGroup.exists_one_half_le_im_smul`) to land in the easy regime
`im ≥ 1/2`, then transports the easy-regime non-vanishing back via
`all_theta_ne_zero_smul_iff_SL2Z`. -/
theorem all_theta_ne_zero_on_H {τ : ℂ} (hτ : 0 < τ.im) :
    all_theta_ne_zero τ := by
  set τH : UpperHalfPlane := ⟨τ, hτ⟩
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_one_half_le_im_smul τH
  have h_at_γτ : all_theta_ne_zero (((γ • τH : UpperHalfPlane)) : ℂ) :=
    all_theta_ne_zero_of_im_ge_half hγ
  exact (all_theta_ne_zero_smul_iff_SL2Z γ τH).mp h_at_γτ

/-- `θ₂` does not vanish on the upper half-plane. -/
theorem theta2_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : theta2 τ ≠ 0 :=
  (all_theta_ne_zero_on_H hτ).1

/-- `θ₃ = jacobiTheta` does not vanish on the upper half-plane. -/
theorem theta3_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : theta3 τ ≠ 0 :=
  (all_theta_ne_zero_on_H hτ).2.1

/-- `θ₄` does not vanish on the upper half-plane. -/
theorem theta4_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : theta4 τ ≠ 0 :=
  (all_theta_ne_zero_on_H hτ).2.2

/-- **Easy-regime differentiability of `λ`.** For `τ` with `1 ≤ τ.im`,
`modularLambdaH` is differentiable at `τ` (since `θ₃(τ) ≠ 0` and both
`θ₂`, `θ₃` are differentiable). -/
theorem modularLambdaH_differentiableAt_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    DifferentiableAt ℂ modularLambdaH τ := by
  have hτ_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have h3_ne : theta3 τ ≠ 0 := theta3_ne_zero_of_im_ge_one hτ
  have h3_pow_ne : theta3 τ ^ 4 ≠ 0 := pow_ne_zero 4 h3_ne
  unfold modularLambdaH
  refine DifferentiableAt.div ?_ ?_ h3_pow_ne
  · exact (theta2_differentiableAt hτ_pos).pow 4
  · exact (theta3_differentiableAt hτ_pos).pow 4

/-! ## q-expansion cusp infrastructure for `λ`

The level-2 modular function `λ` is periodic with period 2, so via
Mathlib's `Function.Periodic.cuspFunction`, we lift it to a function
on the unit `q`-disk where `q := exp(πi τ)`. The cusp function is
analytic on the open unit disk, providing the foundation for the
q-expansion power series of `λ`. The Cauchy estimate on this disk
closes the three-term derivative bound
`modularLambdaH_deriv_norm_sub_three_term_le_of_im_ge_one`
(in `Gamma2FundamentalDomain/CuspAsymptotics.lean`). -/

/-- **`λ` is differentiable at every `τ` with `0 < τ.im`.**
Generalization of `modularLambdaH_differentiableAt_of_im_ge_one`. -/
theorem modularLambdaH_differentiableAt_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ modularLambdaH τ := by
  have h3_ne : theta3 τ ≠ 0 := theta3_ne_zero hτ
  have h3_pow_ne : theta3 τ ^ 4 ≠ 0 := pow_ne_zero 4 h3_ne
  unfold modularLambdaH
  refine DifferentiableAt.div ?_ ?_ h3_pow_ne
  · exact (theta2_differentiableAt hτ).pow 4
  · exact (theta3_differentiableAt hτ).pow 4

/-- **`λ` is periodic with period 2.** Direct lift of
`modularLambdaH_two_add` to `Function.Periodic`. -/
theorem modularLambdaH_periodic :
    Function.Periodic modularLambdaH ((2 : ℝ) : ℂ) := by
  intro τ
  have h := modularLambdaH_two_add τ
  have h_cast : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_cast
  rw [h_cast]
  exact h

/-- **`λ → 0` as `τ.im → ∞`.** Direct consequence of
`modularLambdaH_norm_le_exp_of_im_ge_one`: the norm decays at least
as fast as `exp(−π·τ.im)`. -/
theorem modularLambdaH_zeroAtImInfty :
    Filter.ZeroAtFilter (Filter.comap Complex.im Filter.atTop) modularLambdaH := by
  unfold Filter.ZeroAtFilter
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- We need ‖λ τ‖ < ε eventually as τ.im → ∞.
  -- Use ‖λ τ‖ ≤ 160000 * exp(-π τ.im) for τ.im ≥ 1.
  -- Find N such that 160000 * exp(-π N) < ε.
  have h_g_tendsto : Filter.Tendsto (fun y : ℝ => 160000 * Real.exp (-Real.pi * y))
      Filter.atTop (nhds 0) := by
    have h_neg : Filter.Tendsto (fun y : ℝ => -Real.pi * y) Filter.atTop Filter.atBot := by
      have hπ_neg : -Real.pi < 0 := by linarith
      exact Filter.tendsto_id.const_mul_atTop_of_neg hπ_neg
    have h_exp := Real.tendsto_exp_atBot.comp h_neg
    have : Filter.Tendsto (fun y : ℝ => Real.exp (-Real.pi * y)) Filter.atTop (nhds 0) := h_exp
    simpa using this.const_mul 160000
  -- Get N such that for y ≥ N: 160000 * exp(-π y) < ε.
  obtain ⟨N, hN⟩ := (Metric.tendsto_nhds.mp h_g_tendsto ε hε).exists_forall_of_atTop
  -- Eventually τ.im > max(1, N).
  rw [Filter.eventually_comap]
  refine Filter.eventually_atTop.mpr ⟨max 1 N, fun y hy τ hτ_eq => ?_⟩
  have hy_ge_one : (1 : ℝ) ≤ y := le_trans (le_max_left 1 N) hy
  have hy_ge_N : N ≤ y := le_trans (le_max_right 1 N) hy
  have h_norm_bd : ‖modularLambdaH τ‖ ≤ 160000 * Real.exp (-Real.pi * τ.im) :=
    modularLambdaH_norm_le_exp_of_im_ge_one (hτ_eq ▸ hy_ge_one)
  have h_dist_bd : dist (160000 * Real.exp (-Real.pi * y)) 0 < ε := hN y hy_ge_N
  rw [Real.dist_eq, sub_zero] at h_dist_bd
  have h_pos : 0 < 160000 * Real.exp (-Real.pi * y) := by
    apply mul_pos; · norm_num
    exact Real.exp_pos _
  rw [abs_of_pos h_pos] at h_dist_bd
  rw [dist_zero_right]
  calc ‖modularLambdaH τ‖
      ≤ 160000 * Real.exp (-Real.pi * τ.im) := h_norm_bd
    _ = 160000 * Real.exp (-Real.pi * y) := by rw [hτ_eq]
    _ < ε := h_dist_bd

/-- **The cusp function of `λ` at `q = 0`.** Defined via Mathlib's
`Function.Periodic.cuspFunction` for period-2 functions: for `q ≠ 0`,
`modularLambdaH_cusp q = modularLambdaH τ` where `q = exp(πi τ)`;
at `q = 0`, it equals the limit value `0`. -/
noncomputable def modularLambdaH_cusp : ℂ → ℂ :=
  Function.Periodic.cuspFunction 2 modularLambdaH

/-- **Cusp-function equation.** `modularLambdaH_cusp (exp(πi τ)) = λ(τ)`
for any `τ ∈ ℂ`. -/
theorem modularLambdaH_cusp_qParam (τ : ℂ) :
    modularLambdaH_cusp (Function.Periodic.qParam 2 τ) = modularLambdaH τ :=
  Function.Periodic.eq_cuspFunction (by norm_num : (2 : ℝ) ≠ 0)
    modularLambdaH_periodic τ

/-- **Value at the cusp `∞`.** `modularLambdaH_cusp 0 = 0`, since `λ → 0`
as `τ.im → ∞`. -/
theorem modularLambdaH_cusp_zero : modularLambdaH_cusp 0 = 0 :=
  Function.Periodic.cuspFunction_zero_of_zero_at_inf
    (by norm_num : (0 : ℝ) < 2) modularLambdaH_zeroAtImInfty

/-- **Differentiability at `q = 0`.** `modularLambdaH_cusp` is
differentiable at the cusp `q = 0`. -/
theorem modularLambdaH_cusp_differentiableAt_zero :
    DifferentiableAt ℂ modularLambdaH_cusp 0 := by
  apply Function.Periodic.differentiableAt_cuspFunction_zero
    (by norm_num : (0 : ℝ) < 2) modularLambdaH_periodic
  · -- Eventually differentiable at τ with τ.im → ∞.
    rw [Filter.eventually_comap]
    refine Filter.eventually_atTop.mpr ⟨1, fun y hy τ hτ_eq => ?_⟩
    have : (0 : ℝ) < τ.im := by rw [hτ_eq]; linarith
    exact modularLambdaH_differentiableAt_of_im_pos this
  · -- BoundedAtFilter follows from ZeroAtFilter.
    exact modularLambdaH_zeroAtImInfty.boundedAtFilter

/-- **Differentiability on the open punctured unit `q`-disk.** For
`q ≠ 0` with `|q| < 1`, `modularLambdaH_cusp` is differentiable at `q`. -/
theorem modularLambdaH_cusp_differentiableAt_of_norm_lt_one {q : ℂ}
    (hq_ne : q ≠ 0) (hq_lt : ‖q‖ < 1) :
    DifferentiableAt ℂ modularLambdaH_cusp q := by
  -- q = qParam 2 (invQParam 2 q) since q ≠ 0.
  have hh_ne : (2 : ℝ) ≠ 0 := by norm_num
  have h_eq : Function.Periodic.qParam 2 (Function.Periodic.invQParam 2 q) = q :=
    Function.Periodic.qParam_right_inv hh_ne hq_ne
  -- invQParam q has positive imaginary part since |q| < 1.
  have h_im_pos : 0 < (Function.Periodic.invQParam 2 q).im := by
    rw [Function.Periodic.im_invQParam]
    have h_log_neg : Real.log ‖q‖ < 0 :=
      Real.log_neg (norm_pos_iff.mpr hq_ne) hq_lt
    have h_factor : -((2 : ℝ) / (2 * Real.pi)) < 0 := by
      have hπ := Real.pi_pos
      have h_pos : 0 < (2 : ℝ) / (2 * Real.pi) := by positivity
      linarith
    have h_prod_pos : 0 < -((2 : ℝ) / (2 * Real.pi)) * Real.log ‖q‖ :=
      mul_pos_of_neg_of_neg h_factor h_log_neg
    convert h_prod_pos using 1
    ring
  have h_diff_lambda : DifferentiableAt ℂ modularLambdaH (Function.Periodic.invQParam 2 q) :=
    modularLambdaH_differentiableAt_of_im_pos h_im_pos
  have h_diff_cusp : DifferentiableAt ℂ modularLambdaH_cusp
      (Function.Periodic.qParam 2 (Function.Periodic.invQParam 2 q)) :=
    Function.Periodic.differentiableAt_cuspFunction hh_ne modularLambdaH_periodic
      h_diff_lambda
  rw [h_eq] at h_diff_cusp
  exact h_diff_cusp

/-- **`modularLambdaH_cusp` is differentiable on the open unit
`q`-disk.** Combines `differentiableAt_zero` with the punctured-disk
result. -/
theorem modularLambdaH_cusp_differentiableOn_unitBall :
    DifferentiableOn ℂ modularLambdaH_cusp (Metric.ball (0 : ℂ) 1) := by
  intro q hq
  rw [Metric.mem_ball, dist_zero_right] at hq
  by_cases hq_eq : q = 0
  · rw [hq_eq]
    exact modularLambdaH_cusp_differentiableAt_zero.differentiableWithinAt
  · exact (modularLambdaH_cusp_differentiableAt_of_norm_lt_one hq_eq hq).differentiableWithinAt

/-- **`modularLambdaH_cusp` is analytic on the open unit `q`-disk.**
Follows from differentiability on the open ball via Mathlib's
`DifferentiableOn.analyticOnNhd` (a holomorphic function on an open
subset of `ℂ` is analytic). This is the foundation for the q-expansion
power series of `λ` at the cusp `∞`. -/
theorem modularLambdaH_cusp_analyticOn :
    AnalyticOn ℂ modularLambdaH_cusp (Metric.ball (0 : ℂ) 1) :=
  modularLambdaH_cusp_differentiableOn_unitBall.analyticOn Metric.isOpen_ball

/-- **One-term q-expansion bound for `modularLambdaH_cusp`.** For `y ≠ 0`
with `‖y‖ ≤ exp(−π)`, `‖cusp y − 16 y‖ ≤ 4096 · ‖y‖²`. This is the
direct translation of `modularLambdaH_norm_sub_lead_le_of_im_ge_one`
into the `q`-coordinate `y = exp(πi τ)`. -/
theorem modularLambdaH_cusp_norm_sub_lead_le {y : ℂ} (hy : ‖y‖ ≤ Real.exp (-Real.pi))
    (hy_ne : y ≠ 0) :
    ‖modularLambdaH_cusp y - 16 * y‖ ≤ 4096 * ‖y‖^2 := by
  set τ := Function.Periodic.invQParam 2 y with hτ_def
  have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy_ne
  have hπ : 0 < Real.pi := Real.pi_pos
  have h_qParam : Function.Periodic.qParam 2 τ = y :=
    Function.Periodic.qParam_right_inv (by norm_num : (2 : ℝ) ≠ 0) hy_ne
  have h_cusp : modularLambdaH_cusp y = modularLambdaH τ := by
    rw [← h_qParam]; exact modularLambdaH_cusp_qParam τ
  -- τ.im = -log ‖y‖ / π.
  have hτ_im_eq : τ.im = -Real.log ‖y‖ / Real.pi := by
    rw [hτ_def, Function.Periodic.im_invQParam]
    ring
  have hτ_im_ge : 1 ≤ τ.im := by
    rw [hτ_im_eq, le_div_iff₀ hπ, one_mul]
    have h_log_le : Real.log ‖y‖ ≤ -Real.pi := by
      have := Real.log_le_log hy_norm_pos hy
      rwa [Real.log_exp] at this
    linarith
  -- exp(πi τ) = qParam 2 τ = y.
  have h_exp_eq : Complex.exp (Real.pi * Complex.I * τ) = y := by
    rw [← h_qParam, Function.Periodic.qParam]
    congr 1
    push_cast; ring
  -- exp(-2π·τ.im) = ‖y‖².
  have h_exp_sq_eq : Real.exp (-2 * Real.pi * τ.im) = ‖y‖^2 := by
    have h_re_eq : (-2 * Real.pi * τ.im : ℝ) = 2 * Real.log ‖y‖ := by
      rw [hτ_im_eq]; field_simp
    rw [h_re_eq, show (2 * Real.log ‖y‖ : ℝ) = Real.log ‖y‖ + Real.log ‖y‖ from by ring,
      Real.exp_add, Real.exp_log hy_norm_pos]
    ring
  rw [h_cusp]
  have h_bound := modularLambdaH_norm_sub_lead_le_of_im_ge_one hτ_im_ge
  rw [h_exp_eq] at h_bound
  rw [h_exp_sq_eq] at h_bound
  exact h_bound

/-- **`modularLambdaH_cusp` has derivative `16` at the cusp `q = 0`.**
This is the first Taylor coefficient `c₁ = 16` of `λ`'s q-expansion,
extracted from the one-term function bound via the standard
`HasDerivAt` characterization. -/
theorem modularLambdaH_cusp_hasDerivAt_zero :
    HasDerivAt modularLambdaH_cusp 16 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have h_exp_pi_pos : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  set δ := min (Real.exp (-Real.pi)) (ε / 4096) with hδ_def
  have hδ_pos : 0 < δ := lt_min h_exp_pi_pos (div_pos hε (by norm_num))
  refine ⟨δ, hδ_pos, fun y hy_mem hy_dist => ?_⟩
  have hy_ne : y ≠ 0 := hy_mem
  rw [dist_zero_right] at hy_dist
  have hy_norm_lt : ‖y‖ < δ := hy_dist
  have hy_norm_le_exp : ‖y‖ ≤ Real.exp (-Real.pi) :=
    le_of_lt (lt_of_lt_of_le hy_norm_lt (min_le_left _ _))
  have hy_norm_lt_div : ‖y‖ < ε / 4096 := lt_of_lt_of_le hy_norm_lt (min_le_right _ _)
  -- slope cusp 0 y = (y - 0)⁻¹ • (cusp y - cusp 0) = y⁻¹ * (cusp y - 0) = cusp y / y.
  rw [slope_def_field, modularLambdaH_cusp_zero, sub_zero, sub_zero]
  -- Goal: dist (cusp y / y) 16 < ε.
  -- Rewrite cusp y / y - 16 = (cusp y - 16 y) / y.
  have h_norm_eq : ‖modularLambdaH_cusp y / y - 16‖ = ‖modularLambdaH_cusp y - 16 * y‖ / ‖y‖ := by
    have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy_ne
    have h_factor : modularLambdaH_cusp y / y - 16 = (modularLambdaH_cusp y - 16 * y) / y := by
      field_simp
    rw [h_factor, norm_div]
  rw [Complex.dist_eq, h_norm_eq]
  -- Now use the bound: ‖cusp y - 16 y‖ ≤ 4096 · ‖y‖².
  have h_bound := modularLambdaH_cusp_norm_sub_lead_le hy_norm_le_exp hy_ne
  have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy_ne
  calc ‖modularLambdaH_cusp y - 16 * y‖ / ‖y‖
      ≤ (4096 * ‖y‖^2) / ‖y‖ := by
        apply div_le_div_of_nonneg_right h_bound hy_norm_pos.le
    _ = 4096 * ‖y‖ := by
        rw [sq]; field_simp
    _ < 4096 * (ε / 4096) := by
        apply mul_lt_mul_of_pos_left hy_norm_lt_div (by norm_num : (0 : ℝ) < 4096)
    _ = ε := by ring

/-- **First Taylor coefficient of `modularLambdaH_cusp` at `0`.** The
classical q-expansion coefficient `c₁ = 16` of `λ`. -/
theorem modularLambdaH_cusp_deriv_zero : deriv modularLambdaH_cusp 0 = 16 :=
  modularLambdaH_cusp_hasDerivAt_zero.deriv

/-- **Two-term q-expansion bound for `modularLambdaH_cusp`.** For `y ≠ 0`
with `‖y‖ ≤ exp(−π)`, `‖cusp y − 16 y + 128 y²‖ ≤ 8192 · ‖y‖³`. Direct
translation of `modularLambdaH_norm_sub_two_term_le_of_im_ge_one` into
the `q`-coordinate. -/
theorem modularLambdaH_cusp_norm_sub_two_term_le {y : ℂ} (hy : ‖y‖ ≤ Real.exp (-Real.pi))
    (hy_ne : y ≠ 0) :
    ‖modularLambdaH_cusp y - 16 * y + 128 * y^2‖ ≤ 8192 * ‖y‖^3 := by
  set τ := Function.Periodic.invQParam 2 y with hτ_def
  have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy_ne
  have hπ : 0 < Real.pi := Real.pi_pos
  have h_qParam : Function.Periodic.qParam 2 τ = y :=
    Function.Periodic.qParam_right_inv (by norm_num : (2 : ℝ) ≠ 0) hy_ne
  have h_cusp : modularLambdaH_cusp y = modularLambdaH τ := by
    rw [← h_qParam]; exact modularLambdaH_cusp_qParam τ
  have hτ_im_eq : τ.im = -Real.log ‖y‖ / Real.pi := by
    rw [hτ_def, Function.Periodic.im_invQParam]
    ring
  have hτ_im_ge : 1 ≤ τ.im := by
    rw [hτ_im_eq, le_div_iff₀ hπ, one_mul]
    have h_log_le : Real.log ‖y‖ ≤ -Real.pi := by
      have := Real.log_le_log hy_norm_pos hy
      rwa [Real.log_exp] at this
    linarith
  have h_exp_eq : Complex.exp (Real.pi * Complex.I * τ) = y := by
    rw [← h_qParam, Function.Periodic.qParam]
    congr 1
    push_cast; ring
  have h_exp_sq_eq : Complex.exp (2 * Real.pi * Complex.I * τ) = y^2 := by
    have h_sum : (2 * Real.pi * Complex.I * τ : ℂ) =
        (Real.pi * Complex.I * τ) + (Real.pi * Complex.I * τ) := by ring
    rw [h_sum, Complex.exp_add, h_exp_eq, sq]
  have h_exp_cube_eq : Real.exp (-3 * Real.pi * τ.im) = ‖y‖^3 := by
    have h_re_eq : (-3 * Real.pi * τ.im : ℝ) = 3 * Real.log ‖y‖ := by
      rw [hτ_im_eq]; field_simp
    rw [h_re_eq, show (3 * Real.log ‖y‖ : ℝ) =
      Real.log ‖y‖ + Real.log ‖y‖ + Real.log ‖y‖ from by ring,
      Real.exp_add, Real.exp_add, Real.exp_log hy_norm_pos]
    ring
  rw [h_cusp]
  have h_bound := modularLambdaH_norm_sub_two_term_le_of_im_ge_one hτ_im_ge
  rw [h_exp_eq, h_exp_sq_eq] at h_bound
  rw [h_exp_cube_eq] at h_bound
  exact h_bound

/-- **Three-term q-expansion bound for `modularLambdaH_cusp`.** For `y ≠ 0`
with `‖y‖ ≤ exp(−π)`, `‖cusp y − 16 y + 128 y² − 704 y³‖ ≤ 32768 · ‖y‖⁴`.
Direct translation of `modularLambdaH_norm_sub_three_term_le_of_im_ge_one`
into the `q`-coordinate. -/
theorem modularLambdaH_cusp_norm_sub_three_term_le {y : ℂ}
    (hy : ‖y‖ ≤ Real.exp (-Real.pi)) (hy_ne : y ≠ 0) :
    ‖modularLambdaH_cusp y - 16 * y + 128 * y^2 - 704 * y^3‖ ≤ 32768 * ‖y‖^4 := by
  set τ := Function.Periodic.invQParam 2 y with hτ_def
  have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy_ne
  have hπ : 0 < Real.pi := Real.pi_pos
  have h_qParam : Function.Periodic.qParam 2 τ = y :=
    Function.Periodic.qParam_right_inv (by norm_num : (2 : ℝ) ≠ 0) hy_ne
  have h_cusp : modularLambdaH_cusp y = modularLambdaH τ := by
    rw [← h_qParam]; exact modularLambdaH_cusp_qParam τ
  have hτ_im_eq : τ.im = -Real.log ‖y‖ / Real.pi := by
    rw [hτ_def, Function.Periodic.im_invQParam]
    ring
  have hτ_im_ge : 1 ≤ τ.im := by
    rw [hτ_im_eq, le_div_iff₀ hπ, one_mul]
    have h_log_le : Real.log ‖y‖ ≤ -Real.pi := by
      have := Real.log_le_log hy_norm_pos hy
      rwa [Real.log_exp] at this
    linarith
  have h_exp_eq : Complex.exp (Real.pi * Complex.I * τ) = y := by
    rw [← h_qParam, Function.Periodic.qParam]
    congr 1
    push_cast; ring
  have h_exp_sq_eq : Complex.exp (2 * Real.pi * Complex.I * τ) = y^2 := by
    have h_sum : (2 * Real.pi * Complex.I * τ : ℂ) =
        (Real.pi * Complex.I * τ) + (Real.pi * Complex.I * τ) := by ring
    rw [h_sum, Complex.exp_add, h_exp_eq, sq]
  have h_exp_cube_eq_c : Complex.exp (3 * Real.pi * Complex.I * τ) = y^3 := by
    rw [show (3 * Real.pi * Complex.I * τ : ℂ) =
      (2 * Real.pi * Complex.I * τ) + (Real.pi * Complex.I * τ) from by ring,
      Complex.exp_add, h_exp_eq, h_exp_sq_eq]
    ring
  have h_exp_quad_eq : Real.exp (-4 * Real.pi * τ.im) = ‖y‖^4 := by
    have h_re_eq : (-4 * Real.pi * τ.im : ℝ) = 4 * Real.log ‖y‖ := by
      rw [hτ_im_eq]; field_simp
    rw [h_re_eq, show (4 * Real.log ‖y‖ : ℝ) =
      Real.log ‖y‖ + Real.log ‖y‖ + Real.log ‖y‖ + Real.log ‖y‖ from by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hy_norm_pos]
    ring
  rw [h_cusp]
  have h_bound := modularLambdaH_norm_sub_three_term_le_of_im_ge_one hτ_im_ge
  rw [h_exp_eq, h_exp_sq_eq, h_exp_cube_eq_c] at h_bound
  rw [h_exp_quad_eq] at h_bound
  exact h_bound

/-- **Widened four-term q-coord function bound.** For `y ≠ 0` with
`‖y‖ ≤ exp(−9π/10)`,
`‖cusp(y) − 16 y + 128 y² − 704 y³ + 3072 y⁴‖ ≤ 35000 · ‖y‖⁵`.
Translation of `modularLambdaH_norm_sub_four_term_le_of_im_ge_nine_tenths`
into the `q`-coordinate `y = exp(πi τ)`. The widened disk
`‖y‖ ≤ exp(−9π/10)` strictly contains the disk `‖y‖ ≤ exp(−π)`
corresponding to `τ.im ≥ 1`, which is the input to the Cauchy step
that closes
`modularLambdaH_deriv_norm_sub_three_term_le_of_im_ge_one`. -/
theorem modularLambdaH_cusp_norm_sub_four_term_le_widened {y : ℂ}
    (hy : ‖y‖ ≤ Real.exp (-(9 * Real.pi / 10))) (hy_ne : y ≠ 0) :
    ‖modularLambdaH_cusp y - 16 * y + 128 * y^2 - 704 * y^3 + 3072 * y^4‖ ≤
      35000 * ‖y‖^5 := by
  set τ := Function.Periodic.invQParam 2 y with hτ_def
  have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy_ne
  have hπ : 0 < Real.pi := Real.pi_pos
  have h_qParam : Function.Periodic.qParam 2 τ = y :=
    Function.Periodic.qParam_right_inv (by norm_num : (2 : ℝ) ≠ 0) hy_ne
  have h_cusp : modularLambdaH_cusp y = modularLambdaH τ := by
    rw [← h_qParam]; exact modularLambdaH_cusp_qParam τ
  have hτ_im_eq : τ.im = -Real.log ‖y‖ / Real.pi := by
    rw [hτ_def, Function.Periodic.im_invQParam]
    ring
  have hτ_im_ge : (9 : ℝ) / 10 ≤ τ.im := by
    rw [hτ_im_eq, le_div_iff₀ hπ]
    have h_log_le : Real.log ‖y‖ ≤ -(9 * Real.pi / 10) := by
      have := Real.log_le_log hy_norm_pos hy
      rwa [Real.log_exp] at this
    nlinarith
  have h_exp_eq : Complex.exp (Real.pi * Complex.I * τ) = y := by
    rw [← h_qParam, Function.Periodic.qParam]
    congr 1
    push_cast; ring
  have h_exp_sq_eq : Complex.exp (2 * Real.pi * Complex.I * τ) = y^2 := by
    have h_sum : (2 * Real.pi * Complex.I * τ : ℂ) =
        (Real.pi * Complex.I * τ) + (Real.pi * Complex.I * τ) := by ring
    rw [h_sum, Complex.exp_add, h_exp_eq, sq]
  have h_exp_cube_eq_c : Complex.exp (3 * Real.pi * Complex.I * τ) = y^3 := by
    rw [show (3 * Real.pi * Complex.I * τ : ℂ) =
      (2 * Real.pi * Complex.I * τ) + (Real.pi * Complex.I * τ) from by ring,
      Complex.exp_add, h_exp_eq, h_exp_sq_eq]
    ring
  have h_exp_quart_eq_c : Complex.exp (4 * Real.pi * Complex.I * τ) = y^4 := by
    rw [show (4 * Real.pi * Complex.I * τ : ℂ) =
      (3 * Real.pi * Complex.I * τ) + (Real.pi * Complex.I * τ) from by ring,
      Complex.exp_add, h_exp_eq, h_exp_cube_eq_c]
    ring
  have h_exp_quint_eq : Real.exp (-5 * Real.pi * τ.im) = ‖y‖^5 := by
    have h_re_eq : (-5 * Real.pi * τ.im : ℝ) = 5 * Real.log ‖y‖ := by
      rw [hτ_im_eq]; field_simp
    rw [h_re_eq, show (5 * Real.log ‖y‖ : ℝ) =
      Real.log ‖y‖ + Real.log ‖y‖ + Real.log ‖y‖ + Real.log ‖y‖ + Real.log ‖y‖ from by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hy_norm_pos]
    ring
  rw [h_cusp]
  have h_bound := modularLambdaH_norm_sub_four_term_le_of_im_ge_nine_tenths hτ_im_ge
  rw [h_exp_eq, h_exp_sq_eq, h_exp_cube_eq_c, h_exp_quart_eq_c] at h_bound
  rw [h_exp_quint_eq] at h_bound
  exact h_bound

/-- **Cauchy bound on `deriv cusp q − 16 + 256 q − 2112 q²` at the
full boundary disk `‖q‖ ≤ exp(−π)`.** For `q ≠ 0` with
`‖q‖ ≤ exp(−π)`,
`‖deriv cusp q − 16 + 256 q − 2112 q²‖ ≤ 31000 · ‖q‖³`.
The constant `31000` is calibrated so that the chain-rule
multiplication by `π · ‖q‖` lands inside the target constant
`100000 · exp(−4π·τ.im)` of
`modularLambdaH_deriv_norm_sub_three_term_le_of_im_ge_one`:
`π · 31000 ≈ 97389 ≤ 100000` (a 2.6% closure margin).

The proof applies Cauchy's estimate to
`H₄(z) := cusp(z) − 16 z + 128 z² − 704 z³ + 3072 z⁴` on the disk
`B(q, ‖q‖/4)`. The sphere stays inside `‖z‖ ≤ 5‖q‖/4 ≤ exp(−9π/10)`
(using `(5/4)·exp(−π) ≤ exp(−9π/10)`), so the widened four-term cusp
function bound applies; the Cauchy estimate gives
`‖deriv H₄(q)‖ ≤ 35000·(5/4)⁵·4·‖q‖⁴ ≈ 427 350·‖q‖⁴`. Combining
`‖deriv H₄(q)‖ ≤ 427 350·‖q‖⁴` with `‖12288 q³‖ = 12288 ‖q‖³`,
and using `‖q‖ ≤ exp(−π)` to convert `427 350·‖q‖⁴ ≤ 18 462·‖q‖³`,
yields `(18 462 + 12288)·‖q‖³ ≤ 31000·‖q‖³` (with slack). Extends
the existing `modularLambdaH_cusp_deriv_sub_two_term_le` (which
requires `‖q‖ ≤ exp(−π)/2`) to the full boundary disk
`‖q‖ ≤ exp(−π)`. -/
theorem modularLambdaH_cusp_deriv_sub_two_term_le_widened {q : ℂ}
    (hq : ‖q‖ ≤ Real.exp (-Real.pi)) (hq_ne : q ≠ 0) :
    ‖deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2‖ ≤ 31000 * ‖q‖^3 := by
  set f : ℂ → ℂ := fun z => modularLambdaH_cusp z - 16 * z + 128 * z^2 - 704 * z^3 + 3072 * z^4
    with hf_def
  have hq_norm_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq_ne
  have h_exp_pi_pos : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  set ρ : ℝ := ‖q‖ / 4 with hρ_def
  have hρ_pos : 0 < ρ := by positivity
  have h_exp_neg_pi_lt_1 : Real.exp (-Real.pi) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hq_norm_lt_1 : ‖q‖ < 1 := lt_of_le_of_lt hq h_exp_neg_pi_lt_1
  -- 5/4 ≤ exp(π/10).
  have h_pi10_ne : Real.pi / 10 ≠ 0 := by positivity
  have h_add1_lt_pi10 := Real.add_one_lt_exp h_pi10_ne
  have h_pi_gt_d2 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h_5_4_le_exp_pi10 : (5 : ℝ) / 4 ≤ Real.exp (Real.pi / 10) := by
    nlinarith [h_add1_lt_pi10, h_pi_gt_d2]
  have h_5_4_exp_neg_pi : (5 : ℝ) / 4 * Real.exp (-Real.pi) ≤ Real.exp (-(9 * Real.pi / 10)) := by
    have h_mul : (5 : ℝ) / 4 * Real.exp (-Real.pi) ≤
        Real.exp (Real.pi / 10) * Real.exp (-Real.pi) :=
      mul_le_mul_of_nonneg_right h_5_4_le_exp_pi10 h_exp_pi_pos.le
    have h_exp_sum : Real.exp (Real.pi / 10) * Real.exp (-Real.pi) =
        Real.exp (-(9 * Real.pi / 10)) := by
      rw [← Real.exp_add]; congr 1; ring
    linarith
  -- For z ∈ closedBall q ρ: ‖z‖ ≤ 5‖q‖/4 ≤ exp(-9π/10) < 1.
  have hz_norm_le (z : ℂ) (hz : z ∈ Metric.closedBall q ρ) : ‖z‖ ≤ 5 * ‖q‖ / 4 := by
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz
    calc ‖z‖ = ‖(z - q) + q‖ := by congr 1; ring
      _ ≤ ‖z - q‖ + ‖q‖ := norm_add_le _ _
      _ ≤ ρ + ‖q‖ := by linarith
      _ = ‖q‖ / 4 + ‖q‖ := rfl
      _ = 5 * ‖q‖ / 4 := by ring
  have hz_norm_le_exp (z : ℂ) (hz : z ∈ Metric.closedBall q ρ) :
      ‖z‖ ≤ Real.exp (-(9 * Real.pi / 10)) := by
    have h := hz_norm_le z hz
    have h_5q4_le : 5 * ‖q‖ / 4 ≤ 5 / 4 * Real.exp (-Real.pi) := by
      have h_mul : (5 : ℝ) / 4 * ‖q‖ ≤ (5 : ℝ) / 4 * Real.exp (-Real.pi) :=
        mul_le_mul_of_nonneg_left hq (by norm_num)
      linarith
    linarith
  have h_exp_9pi10_lt_1 : Real.exp (-(9 * Real.pi / 10)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith
  have hz_norm_lt_1 (z : ℂ) (hz : z ∈ Metric.closedBall q ρ) : ‖z‖ < 1 := by
    have h := hz_norm_le_exp z hz
    linarith
  -- Differentiability of f on a 1-ball around q.
  have h_diff_cusp_at (z : ℂ) (hz_norm : ‖z‖ < 1) :
      DifferentiableAt ℂ modularLambdaH_cusp z := by
    by_cases hz_eq : z = 0
    · rw [hz_eq]; exact modularLambdaH_cusp_differentiableAt_zero
    · exact modularLambdaH_cusp_differentiableAt_of_norm_lt_one hz_eq hz_norm
  have h_f_diff_at (z : ℂ) (hz_norm : ‖z‖ < 1) : DifferentiableAt ℂ f z := by
    apply DifferentiableAt.add
    · apply DifferentiableAt.sub
      · apply DifferentiableAt.add
        · exact (h_diff_cusp_at z hz_norm).sub
            ((differentiableAt_const 16).mul differentiableAt_id)
        · exact (differentiableAt_const 128).mul (differentiableAt_id.pow 2)
      · exact (differentiableAt_const 704).mul (differentiableAt_id.pow 3)
    · exact (differentiableAt_const 3072).mul (differentiableAt_id.pow 4)
  have h_f_diff : DifferentiableOn ℂ f (Metric.ball q ρ) := fun z hz =>
    (h_f_diff_at z (hz_norm_lt_1 z (Metric.ball_subset_closedBall hz))).differentiableWithinAt
  have h_f_cont_cl : ContinuousOn f (Metric.closedBall q ρ) := fun z hz =>
    (h_f_diff_at z (hz_norm_lt_1 z hz)).continuousAt.continuousWithinAt
  have h_diff_cont : DiffContOnCl ℂ f (Metric.ball q ρ) :=
    ⟨h_f_diff, by rwa [closure_ball _ hρ_pos.ne']⟩
  -- Sphere bound: ‖f z‖ ≤ M · ‖q‖^5 where M = 35000 · (5/4)^5 = 109375000/1024.
  set M : ℝ := 109375000 / 1024 with hM_def
  have h_sphere_bound : ∀ z ∈ Metric.sphere q ρ, ‖f z‖ ≤ M * ‖q‖^5 := by
    intro z hz
    have hz_cl : z ∈ Metric.closedBall q ρ := Metric.sphere_subset_closedBall hz
    have h_z_le : ‖z‖ ≤ 5 * ‖q‖ / 4 := hz_norm_le z hz_cl
    have h_z_le_exp : ‖z‖ ≤ Real.exp (-(9 * Real.pi / 10)) := hz_norm_le_exp z hz_cl
    have h_M_q5_nn : 0 ≤ M * ‖q‖^5 := by positivity
    by_cases hz_eq : z = 0
    · have h_f_zero : f z = 0 := by
        rw [hz_eq, hf_def]
        change modularLambdaH_cusp 0 - 16 * 0 + 128 * 0^2 - 704 * 0^3 + 3072 * 0^4 = 0
        rw [modularLambdaH_cusp_zero]; ring
      rw [h_f_zero, norm_zero]
      exact h_M_q5_nn
    · have h_four_term :=
        modularLambdaH_cusp_norm_sub_four_term_le_widened h_z_le_exp hz_eq
      calc ‖f z‖ ≤ 35000 * ‖z‖^5 := h_four_term
        _ ≤ 35000 * (5 * ‖q‖ / 4)^5 := by
            apply mul_le_mul_of_nonneg_left
            · exact pow_le_pow_left₀ (norm_nonneg z) h_z_le 5
            · norm_num
        _ = M * ‖q‖^5 := by
            change (35000 : ℝ) * (5 * ‖q‖ / 4)^5 = 109375000 / 1024 * ‖q‖^5
            ring
  -- Apply Cauchy's estimate: ‖deriv f q‖ ≤ M · ‖q‖^5 / ρ.
  have h_cauchy :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ_pos h_diff_cont h_sphere_bound
  -- Compute deriv f q via HasDerivAt route.
  have h_cusp_hasDeriv : HasDerivAt modularLambdaH_cusp (deriv modularLambdaH_cusp q) q :=
    (h_diff_cusp_at q hq_norm_lt_1).hasDerivAt
  have h_lin_hasDeriv : HasDerivAt (fun z : ℂ => 16 * z) 16 q := by
    simpa using (hasDerivAt_id q).const_mul (16 : ℂ)
  have h_quad_hasDeriv : HasDerivAt (fun z : ℂ => 128 * z^2) (256 * q) q := by
    have h_pow : HasDerivAt (fun z : ℂ => z^2) (2 * q) q := by
      simpa using hasDerivAt_pow 2 q
    have := h_pow.const_mul (128 : ℂ)
    convert! this using 1; ring
  have h_cube_hasDeriv : HasDerivAt (fun z : ℂ => 704 * z^3) (2112 * q^2) q := by
    have h_pow : HasDerivAt (fun z : ℂ => z^3) (3 * q^2) q := by
      simpa using hasDerivAt_pow 3 q
    have := h_pow.const_mul (704 : ℂ)
    convert! this using 1; ring
  have h_quart_hasDeriv : HasDerivAt (fun z : ℂ => 3072 * z^4) (12288 * q^3) q := by
    have h_pow : HasDerivAt (fun z : ℂ => z^4) (4 * q^3) q := by
      simpa using hasDerivAt_pow 4 q
    have := h_pow.const_mul (3072 : ℂ)
    convert! this using 1; ring
  have h_f_hasDeriv : HasDerivAt f
      (deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2 + 12288 * q^3) q := by
    have h1 : HasDerivAt (fun z : ℂ => modularLambdaH_cusp z - 16 * z)
        (deriv modularLambdaH_cusp q - 16) q :=
      h_cusp_hasDeriv.sub h_lin_hasDeriv
    have h2 : HasDerivAt (fun z : ℂ => modularLambdaH_cusp z - 16 * z + 128 * z^2)
        (deriv modularLambdaH_cusp q - 16 + 256 * q) q :=
      h1.add h_quad_hasDeriv
    have h3 : HasDerivAt (fun z : ℂ => modularLambdaH_cusp z - 16 * z + 128 * z^2 - 704 * z^3)
        (deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2) q :=
      h2.sub h_cube_hasDeriv
    exact h3.add h_quart_hasDeriv
  have h_deriv_f_eq : deriv f q =
      deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2 + 12288 * q^3 :=
    h_f_hasDeriv.deriv
  rw [h_deriv_f_eq] at h_cauchy
  -- Now bound ‖deriv cusp q - 16 + 256 q - 2112 q²‖ via triangle.
  have h_eq : deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2 =
      (deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2 + 12288 * q^3) - 12288 * q^3 := by
    ring
  rw [h_eq]
  -- M · ‖q‖^5 / ρ = M · ‖q‖^5 · (4/‖q‖) = 4M · ‖q‖^4.
  have h_quotient_simplify : M * ‖q‖^5 / ρ = 4 * M * ‖q‖^4 := by
    rw [hρ_def]
    rw [show ‖q‖^5 = ‖q‖^4 * ‖q‖ from by ring]
    field_simp
  rw [h_quotient_simplify] at h_cauchy
  -- exp(π) > 22.9.
  have h_exp_pi_gt_22_9 : (22.9 : ℝ) < Real.exp Real.pi := by
    have h_e : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h_2718_lt : (2.718 : ℝ) < Real.exp 1 := by linarith
    have h_2718_pos : (0 : ℝ) < 2.718 := by norm_num
    have h_pow3 : (2.718 : ℝ)^3 < (Real.exp 1)^3 :=
      pow_lt_pow_left₀ h_2718_lt h_2718_pos.le (by norm_num)
    have h_exp3_eq : (Real.exp 1)^3 = Real.exp 3 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
      ring
    have h_2718_cube_num : (2.718 : ℝ)^3 > 20.07 := by norm_num
    have h_exp3_gt : (20.07 : ℝ) < Real.exp 3 := by
      rw [← h_exp3_eq]; linarith
    have h_pi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
    have h_pi3_ne : Real.pi - 3 ≠ 0 := by intro h; linarith
    have h_add_lt := Real.add_one_lt_exp h_pi3_ne
    have h_pi3_pos : (0 : ℝ) < Real.pi - 3 := by linarith
    have h_exp_pi_eq : Real.exp Real.pi = Real.exp 3 * Real.exp (Real.pi - 3) := by
      rw [← Real.exp_add]; congr 1; ring
    have h_exp_pi3_gt : Real.exp (Real.pi - 3) > Real.pi - 2 := by linarith
    have h_exp3_pos : (0 : ℝ) < Real.exp 3 := Real.exp_pos _
    have h_pi_m2_gt : (1.1415 : ℝ) < Real.pi - 2 := by linarith
    have h_pi_m2_pos : (0 : ℝ) < Real.pi - 2 := by linarith
    rw [h_exp_pi_eq]
    calc (22.9 : ℝ) < 20.07 * 1.1415 := by norm_num
      _ < 20.07 * (Real.pi - 2) :=
          mul_lt_mul_of_pos_left h_pi_m2_gt (by norm_num)
      _ < Real.exp 3 * (Real.pi - 2) :=
          mul_lt_mul_of_pos_right h_exp3_gt h_pi_m2_pos
      _ < Real.exp 3 * Real.exp (Real.pi - 3) :=
          mul_lt_mul_of_pos_left h_exp_pi3_gt h_exp3_pos
  -- ‖q‖ ≤ exp(-π) < 1/22.9.
  have h_exp_pi_pos_real : 0 < Real.exp Real.pi := Real.exp_pos _
  have h_exp_neg_lt : Real.exp (-Real.pi) < 1 / 22.9 := by
    rw [Real.exp_neg, show (Real.exp Real.pi)⁻¹ = 1 / Real.exp Real.pi from (one_div _).symm]
    exact one_div_lt_one_div_of_lt (by norm_num : (0:ℝ) < 22.9) h_exp_pi_gt_22_9
  have hq_lt : ‖q‖ < 1 / 22.9 := lt_of_le_of_lt hq h_exp_neg_lt
  -- 4M · ‖q‖ ≤ 4M / 22.9 = (437500000/1024)/22.9 < 18700.
  have h_4M_pos : 0 < 4 * M := by change (0 : ℝ) < 4 * (109375000 / 1024); norm_num
  have h_4M_q : 4 * M * ‖q‖ < 4 * M * (1 / 22.9) :=
    mul_lt_mul_of_pos_left hq_lt h_4M_pos
  have h_4M_q_le : 4 * M * ‖q‖ ≤ 18700 := by
    have h_calc : (4 : ℝ) * M * (1 / 22.9) ≤ 18700 := by
      change (4 : ℝ) * (109375000 / 1024) * (1 / 22.9) ≤ 18700
      norm_num
    exact le_trans h_4M_q.le h_calc
  have hq3_nn : 0 ≤ ‖q‖^3 := by positivity
  have h_4M_q4 : 4 * M * ‖q‖^4 ≤ 18700 * ‖q‖^3 := by
    have h_pow_eq : ‖q‖^4 = ‖q‖^3 * ‖q‖ := by ring
    rw [h_pow_eq]
    have h_assoc : 4 * M * (‖q‖^3 * ‖q‖) = (4 * M * ‖q‖) * ‖q‖^3 := by ring
    rw [h_assoc]
    exact mul_le_mul_of_nonneg_right h_4M_q_le hq3_nn
  -- Triangle inequality + final arithmetic.
  have h_norm_12288 : ‖(12288 : ℂ) * q^3‖ = 12288 * ‖q‖^3 := by
    rw [norm_mul, norm_pow]
    have : ‖(12288 : ℂ)‖ = 12288 := by
      rw [show (12288 : ℂ) = ((12288 : ℝ) : ℂ) from by norm_num, Complex.norm_real]
      simp
    rw [this]
  calc ‖(deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2 + 12288 * q^3) - 12288 * q^3‖
      ≤ ‖deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2 + 12288 * q^3‖
          + ‖(12288 : ℂ) * q^3‖ := norm_sub_le _ _
    _ ≤ 4 * M * ‖q‖^4 + 12288 * ‖q‖^3 := by linarith [h_norm_12288.le]
    _ ≤ 18700 * ‖q‖^3 + 12288 * ‖q‖^3 := by linarith
    _ ≤ 31000 * ‖q‖^3 := by linarith

/-- **Cauchy bound on `deriv cusp q − 16 + 256 q` near `0`.** For `q ≠ 0`
with `‖q‖ ≤ exp(−π)/2`, `‖deriv cusp q − 16 + 256 q‖ ≤ 65536 · ‖q‖²`.
This is the Cauchy estimate applied to `H₂(z) := cusp(z) − 16 z + 128 z²`
on the disk `B(q, ‖q‖)`, using the two-term q-coordinate function bound
on the boundary sphere. Used to prove `iteratedDeriv 2 cusp 0 = −256`. -/
theorem modularLambdaH_cusp_deriv_sub_lead_le {q : ℂ}
    (hq : ‖q‖ ≤ Real.exp (-Real.pi) / 2) (hq_ne : q ≠ 0) :
    ‖deriv modularLambdaH_cusp q - 16 + 256 * q‖ ≤ 65536 * ‖q‖^2 := by
  set f : ℂ → ℂ := fun z => modularLambdaH_cusp z - 16 * z + 128 * z^2 with hf_def
  have hq_norm_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq_ne
  have h_exp_pi_pos : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  have hq_2 : 2 * ‖q‖ ≤ Real.exp (-Real.pi) := by linarith
  have h_exp_lt_1 : Real.exp (-Real.pi) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith [Real.pi_pos]
  have hq_2_lt_1 : 2 * ‖q‖ < 1 := by linarith
  -- For z ∈ ball q ‖q‖: ‖z‖ < 2‖q‖ ≤ exp(-π) < 1.
  have hz_norm_lt (z : ℂ) (hz : z ∈ Metric.ball q ‖q‖) : ‖z‖ < 2 * ‖q‖ := by
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    calc ‖z‖ = ‖(z - q) + q‖ := by congr 1; ring
      _ ≤ ‖z - q‖ + ‖q‖ := norm_add_le _ _
      _ < ‖q‖ + ‖q‖ := by linarith
      _ = 2 * ‖q‖ := by ring
  -- Differentiability of f on ball(q, ‖q‖) and continuity on its closure.
  have h_diff_cusp_at (z : ℂ) (hz_norm : ‖z‖ < 1) :
      DifferentiableAt ℂ modularLambdaH_cusp z := by
    by_cases hz_eq : z = 0
    · rw [hz_eq]; exact modularLambdaH_cusp_differentiableAt_zero
    · exact modularLambdaH_cusp_differentiableAt_of_norm_lt_one hz_eq hz_norm
  have h_f_diff_at (z : ℂ) (hz_norm : ‖z‖ < 1) : DifferentiableAt ℂ f z := by
    apply DifferentiableAt.add
    · exact (h_diff_cusp_at z hz_norm).sub
        ((differentiableAt_const 16).mul differentiableAt_id)
    · exact (differentiableAt_const 128).mul (differentiableAt_id.pow 2)
  have h_f_diff : DifferentiableOn ℂ f (Metric.ball q ‖q‖) := fun z hz =>
    (h_f_diff_at z ((hz_norm_lt z hz).trans hq_2_lt_1)).differentiableWithinAt
  -- Continuity on closure: closedBall q ‖q‖ ⊆ ball 0 1.
  have h_f_cont_cl : ContinuousOn f (Metric.closedBall q ‖q‖) := by
    intro z hz
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz
    have hz_norm_le : ‖z‖ ≤ 2 * ‖q‖ := by
      calc ‖z‖ = ‖(z - q) + q‖ := by congr 1; ring
        _ ≤ ‖z - q‖ + ‖q‖ := norm_add_le _ _
        _ ≤ ‖q‖ + ‖q‖ := by linarith
        _ = 2 * ‖q‖ := by ring
    have hz_lt_1 : ‖z‖ < 1 := lt_of_le_of_lt hz_norm_le hq_2_lt_1
    exact (h_f_diff_at z hz_lt_1).continuousAt.continuousWithinAt
  have h_diff_cont : DiffContOnCl ℂ f (Metric.ball q ‖q‖) :=
    ⟨h_f_diff, by rwa [closure_ball _ hq_norm_pos.ne']⟩
  -- Sphere bound: ‖f z‖ ≤ 65536 · ‖q‖³ on z ∈ sphere q ‖q‖.
  have h_sphere_bound : ∀ z ∈ Metric.sphere q ‖q‖, ‖f z‖ ≤ 65536 * ‖q‖^3 := by
    intro z hz
    rw [Metric.mem_sphere, Complex.dist_eq] at hz
    have hz_norm_eq : ‖z‖ ≤ 2 * ‖q‖ := by
      calc ‖z‖ = ‖(z - q) + q‖ := by congr 1; ring
        _ ≤ ‖z - q‖ + ‖q‖ := norm_add_le _ _
        _ = ‖q‖ + ‖q‖ := by rw [hz]
        _ = 2 * ‖q‖ := by ring
    have hz_norm_le_exp : ‖z‖ ≤ Real.exp (-Real.pi) := le_trans hz_norm_eq hq_2
    have hq_cube_nn : (0 : ℝ) ≤ 65536 * ‖q‖^3 := by positivity
    by_cases hz_eq : z = 0
    · have h_f_zero : f z = 0 := by
        rw [hz_eq, hf_def]
        change modularLambdaH_cusp 0 - 16 * 0 + 128 * 0^2 = 0
        rw [modularLambdaH_cusp_zero]; ring
      rw [h_f_zero, norm_zero]
      exact hq_cube_nn
    · have h_two_term :=
        modularLambdaH_cusp_norm_sub_two_term_le hz_norm_le_exp hz_eq
      calc ‖f z‖ ≤ 8192 * ‖z‖^3 := h_two_term
        _ ≤ 8192 * (2 * ‖q‖)^3 := by
            apply mul_le_mul_of_nonneg_left
            · apply pow_le_pow_left₀ (norm_nonneg z) hz_norm_eq
            · norm_num
        _ = 65536 * ‖q‖^3 := by ring
  -- Apply Cauchy's estimate.
  have h_cauchy :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hq_norm_pos h_diff_cont h_sphere_bound
  -- deriv f q = deriv cusp q - 16 + 256 q via HasDerivAt route.
  have h_q_norm_lt_1 : ‖q‖ < 1 := lt_of_le_of_lt hq (by linarith)
  have h_cusp_hasDeriv : HasDerivAt modularLambdaH_cusp (deriv modularLambdaH_cusp q) q :=
    (h_diff_cusp_at q h_q_norm_lt_1).hasDerivAt
  have h_lin_hasDeriv : HasDerivAt (fun z : ℂ => 16 * z) 16 q := by
    simpa using (hasDerivAt_id q).const_mul (16 : ℂ)
  have h_quad_hasDeriv : HasDerivAt (fun z : ℂ => 128 * z^2) (256 * q) q := by
    have h_pow : HasDerivAt (fun z : ℂ => z^2) (2 * q) q := by
      simpa using hasDerivAt_pow 2 q
    have := h_pow.const_mul (128 : ℂ)
    convert! this using 1; ring
  have h_f_hasDeriv : HasDerivAt f (deriv modularLambdaH_cusp q - 16 + 256 * q) q := by
    have h_sub : HasDerivAt (fun z : ℂ => modularLambdaH_cusp z - 16 * z)
        (deriv modularLambdaH_cusp q - 16) q :=
      h_cusp_hasDeriv.sub h_lin_hasDeriv
    have h_add : HasDerivAt (fun z : ℂ => modularLambdaH_cusp z - 16 * z + 128 * z^2)
        (deriv modularLambdaH_cusp q - 16 + 256 * q) q :=
      h_sub.add h_quad_hasDeriv
    exact h_add
  have h_deriv_f_eq : deriv f q = deriv modularLambdaH_cusp q - 16 + 256 * q :=
    h_f_hasDeriv.deriv
  rw [h_deriv_f_eq] at h_cauchy
  calc ‖deriv modularLambdaH_cusp q - 16 + 256 * q‖
      ≤ 65536 * ‖q‖^3 / ‖q‖ := h_cauchy
    _ = 65536 * ‖q‖^2 := by
        rw [show (‖q‖^3 : ℝ) = ‖q‖^2 * ‖q‖ from by ring]
        field_simp

/-- **Cauchy bound on `deriv cusp q − 16 + 256 q − 2112 q²` near `0`.**
For `q ≠ 0` with `‖q‖ ≤ exp(−π)/2`,
`‖deriv cusp q − 16 + 256 q − 2112 q²‖ ≤ 524288 · ‖q‖³`. This is the
Cauchy estimate applied to `H₃(z) := cusp(z) − 16 z + 128 z² − 704 z³`
on the disk `B(q, ‖q‖)`, using the three-term q-coordinate function
bound on the boundary sphere. Used to prove
`iteratedDeriv 3 cusp 0 = 4224`. -/
theorem modularLambdaH_cusp_deriv_sub_two_term_le {q : ℂ}
    (hq : ‖q‖ ≤ Real.exp (-Real.pi) / 2) (hq_ne : q ≠ 0) :
    ‖deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2‖ ≤ 524288 * ‖q‖^3 := by
  set f : ℂ → ℂ := fun z => modularLambdaH_cusp z - 16 * z + 128 * z^2 - 704 * z^3 with hf_def
  have hq_norm_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq_ne
  have h_exp_pi_pos : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  have hq_2 : 2 * ‖q‖ ≤ Real.exp (-Real.pi) := by linarith
  have h_exp_lt_1 : Real.exp (-Real.pi) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith [Real.pi_pos]
  have hq_2_lt_1 : 2 * ‖q‖ < 1 := by linarith
  have hz_norm_lt (z : ℂ) (hz : z ∈ Metric.ball q ‖q‖) : ‖z‖ < 2 * ‖q‖ := by
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    calc ‖z‖ = ‖(z - q) + q‖ := by congr 1; ring
      _ ≤ ‖z - q‖ + ‖q‖ := norm_add_le _ _
      _ < ‖q‖ + ‖q‖ := by linarith
      _ = 2 * ‖q‖ := by ring
  have h_diff_cusp_at (z : ℂ) (hz_norm : ‖z‖ < 1) :
      DifferentiableAt ℂ modularLambdaH_cusp z := by
    by_cases hz_eq : z = 0
    · rw [hz_eq]; exact modularLambdaH_cusp_differentiableAt_zero
    · exact modularLambdaH_cusp_differentiableAt_of_norm_lt_one hz_eq hz_norm
  have h_f_diff_at (z : ℂ) (hz_norm : ‖z‖ < 1) : DifferentiableAt ℂ f z := by
    apply DifferentiableAt.sub
    · apply DifferentiableAt.add
      · exact (h_diff_cusp_at z hz_norm).sub
          ((differentiableAt_const 16).mul differentiableAt_id)
      · exact (differentiableAt_const 128).mul (differentiableAt_id.pow 2)
    · exact (differentiableAt_const 704).mul (differentiableAt_id.pow 3)
  have h_f_diff : DifferentiableOn ℂ f (Metric.ball q ‖q‖) := fun z hz =>
    (h_f_diff_at z ((hz_norm_lt z hz).trans hq_2_lt_1)).differentiableWithinAt
  have h_f_cont_cl : ContinuousOn f (Metric.closedBall q ‖q‖) := by
    intro z hz
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz
    have hz_norm_le : ‖z‖ ≤ 2 * ‖q‖ := by
      calc ‖z‖ = ‖(z - q) + q‖ := by congr 1; ring
        _ ≤ ‖z - q‖ + ‖q‖ := norm_add_le _ _
        _ ≤ ‖q‖ + ‖q‖ := by linarith
        _ = 2 * ‖q‖ := by ring
    exact (h_f_diff_at z (lt_of_le_of_lt hz_norm_le hq_2_lt_1)).continuousAt.continuousWithinAt
  have h_diff_cont : DiffContOnCl ℂ f (Metric.ball q ‖q‖) :=
    ⟨h_f_diff, by rwa [closure_ball _ hq_norm_pos.ne']⟩
  have h_sphere_bound : ∀ z ∈ Metric.sphere q ‖q‖, ‖f z‖ ≤ 524288 * ‖q‖^4 := by
    intro z hz
    rw [Metric.mem_sphere, Complex.dist_eq] at hz
    have hz_norm_eq : ‖z‖ ≤ 2 * ‖q‖ := by
      calc ‖z‖ = ‖(z - q) + q‖ := by congr 1; ring
        _ ≤ ‖z - q‖ + ‖q‖ := norm_add_le _ _
        _ = ‖q‖ + ‖q‖ := by rw [hz]
        _ = 2 * ‖q‖ := by ring
    have hz_norm_le_exp : ‖z‖ ≤ Real.exp (-Real.pi) := le_trans hz_norm_eq hq_2
    have hq_pow_nn : (0 : ℝ) ≤ 524288 * ‖q‖^4 := by positivity
    by_cases hz_eq : z = 0
    · have h_f_zero : f z = 0 := by
        rw [hz_eq, hf_def]
        change modularLambdaH_cusp 0 - 16 * 0 + 128 * 0^2 - 704 * 0^3 = 0
        rw [modularLambdaH_cusp_zero]; ring
      rw [h_f_zero, norm_zero]
      exact hq_pow_nn
    · have h_three_term :=
        modularLambdaH_cusp_norm_sub_three_term_le hz_norm_le_exp hz_eq
      calc ‖f z‖ ≤ 32768 * ‖z‖^4 := h_three_term
        _ ≤ 32768 * (2 * ‖q‖)^4 := by
            apply mul_le_mul_of_nonneg_left
            · apply pow_le_pow_left₀ (norm_nonneg z) hz_norm_eq
            · norm_num
        _ = 524288 * ‖q‖^4 := by ring
  have h_cauchy :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hq_norm_pos h_diff_cont h_sphere_bound
  have h_q_norm_lt_1 : ‖q‖ < 1 := lt_of_le_of_lt hq (by linarith)
  have h_cusp_hasDeriv : HasDerivAt modularLambdaH_cusp (deriv modularLambdaH_cusp q) q :=
    (h_diff_cusp_at q h_q_norm_lt_1).hasDerivAt
  have h_lin_hasDeriv : HasDerivAt (fun z : ℂ => 16 * z) 16 q := by
    simpa using (hasDerivAt_id q).const_mul (16 : ℂ)
  have h_quad_hasDeriv : HasDerivAt (fun z : ℂ => 128 * z^2) (256 * q) q := by
    have h_pow : HasDerivAt (fun z : ℂ => z^2) (2 * q) q := by
      simpa using hasDerivAt_pow 2 q
    have := h_pow.const_mul (128 : ℂ)
    convert! this using 1; ring
  have h_cube_hasDeriv : HasDerivAt (fun z : ℂ => 704 * z^3) (2112 * q^2) q := by
    have h_pow : HasDerivAt (fun z : ℂ => z^3) (3 * q^2) q := by
      simpa using hasDerivAt_pow 3 q
    have := h_pow.const_mul (704 : ℂ)
    convert! this using 1; ring
  have h_f_hasDeriv : HasDerivAt f
      (deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2) q := by
    have h_sub1 : HasDerivAt (fun z : ℂ => modularLambdaH_cusp z - 16 * z)
        (deriv modularLambdaH_cusp q - 16) q :=
      h_cusp_hasDeriv.sub h_lin_hasDeriv
    have h_add : HasDerivAt (fun z : ℂ => modularLambdaH_cusp z - 16 * z + 128 * z^2)
        (deriv modularLambdaH_cusp q - 16 + 256 * q) q :=
      h_sub1.add h_quad_hasDeriv
    have h_sub2 : HasDerivAt (fun z : ℂ => modularLambdaH_cusp z - 16 * z + 128 * z^2 - 704 * z^3)
        (deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2) q :=
      h_add.sub h_cube_hasDeriv
    exact h_sub2
  have h_deriv_f_eq : deriv f q =
      deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2 :=
    h_f_hasDeriv.deriv
  rw [h_deriv_f_eq] at h_cauchy
  calc ‖deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2‖
      ≤ 524288 * ‖q‖^4 / ‖q‖ := h_cauchy
    _ = 524288 * ‖q‖^3 := by
        rw [show (‖q‖^4 : ℝ) = ‖q‖^3 * ‖q‖ from by ring]
        field_simp

/-- **Second Taylor coefficient of `modularLambdaH_cusp` at `0`.**
`iteratedDeriv 2 cusp 0 = −256` (so `c₂ = −128`). The classical
q-expansion coefficient. -/
theorem modularLambdaH_cusp_iteratedDeriv_two_zero :
    iteratedDeriv 2 modularLambdaH_cusp 0 = -256 := by
  -- iteratedDeriv 2 cusp 0 = deriv (deriv cusp) 0.
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  -- Now goal: deriv (deriv cusp) 0 = -256.
  -- Show HasDerivAt (deriv cusp) (-256) 0.
  have h_hasDeriv : HasDerivAt (deriv modularLambdaH_cusp) (-256) 0 := by
    rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have h_exp_pi_pos : 0 < Real.exp (-Real.pi) := Real.exp_pos _
    have h_exp_half_pos : 0 < Real.exp (-Real.pi) / 2 := by positivity
    set δ := min (Real.exp (-Real.pi) / 2) (ε / 65536) with hδ_def
    have hδ_pos : 0 < δ := lt_min h_exp_half_pos (div_pos hε (by norm_num))
    refine ⟨δ, hδ_pos, fun q hq_mem hq_dist => ?_⟩
    have hq_ne : q ≠ 0 := hq_mem
    rw [dist_zero_right] at hq_dist
    have hq_norm_lt : ‖q‖ < δ := hq_dist
    have hq_norm_le_exp_half : ‖q‖ ≤ Real.exp (-Real.pi) / 2 :=
      le_of_lt (lt_of_lt_of_le hq_norm_lt (min_le_left _ _))
    have hq_norm_lt_div : ‖q‖ < ε / 65536 :=
      lt_of_lt_of_le hq_norm_lt (min_le_right _ _)
    -- slope (deriv cusp) 0 q = (deriv cusp q - deriv cusp 0)/q = (deriv cusp q - 16)/q.
    rw [slope_def_field, modularLambdaH_cusp_deriv_zero, sub_zero]
    -- Goal: dist ((deriv cusp q - 16)/q) (-256) < ε.
    have hq_norm_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq_ne
    -- ((deriv cusp q - 16)/q) - (-256) = (deriv cusp q - 16 + 256 q)/q.
    have h_factor : (deriv modularLambdaH_cusp q - 16) / q - (-256) =
        (deriv modularLambdaH_cusp q - 16 + 256 * q) / q := by
      field_simp
      ring
    rw [Complex.dist_eq, h_factor, norm_div]
    have h_bound :=
      modularLambdaH_cusp_deriv_sub_lead_le hq_norm_le_exp_half hq_ne
    calc ‖deriv modularLambdaH_cusp q - 16 + 256 * q‖ / ‖q‖
        ≤ 65536 * ‖q‖^2 / ‖q‖ := div_le_div_of_nonneg_right h_bound hq_norm_pos.le
      _ = 65536 * ‖q‖ := by rw [sq]; field_simp
      _ < 65536 * (ε / 65536) := by
          apply mul_lt_mul_of_pos_left hq_norm_lt_div (by norm_num : (0 : ℝ) < 65536)
      _ = ε := by ring
  exact h_hasDeriv.deriv

/-- **Third Taylor coefficient of `modularLambdaH_cusp` at `0`.**
`iteratedDeriv 3 cusp 0 = 4224` (so `c₃ = 704`). The classical
q-expansion coefficient. -/
theorem modularLambdaH_cusp_iteratedDeriv_three_zero :
    iteratedDeriv 3 modularLambdaH_cusp 0 = 4224 := by
  -- iteratedDeriv 3 cusp 0 = deriv (iteratedDeriv 2 cusp) 0.
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
  -- Now goal: deriv (iteratedDeriv 2 cusp) 0 = 4224.
  -- iteratedDeriv 2 cusp = deriv (deriv cusp).
  rw [show (iteratedDeriv 2 modularLambdaH_cusp) = (deriv (deriv modularLambdaH_cusp)) from by
    funext z; rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]]
  -- Show HasDerivAt (deriv (deriv cusp)) 4224 0.
  -- We need a bound: |deriv (deriv cusp) q + 256 - 4224 q| ≤ 4194304 · ‖q‖²
  -- for q near 0 nonzero, via Cauchy on g(z) := deriv cusp z - 16 + 256z - 2112z².
  have h_hasDeriv : HasDerivAt (deriv (deriv modularLambdaH_cusp)) 4224 0 := by
    rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have h_exp_pi_pos : 0 < Real.exp (-Real.pi) := Real.exp_pos _
    have h_exp_quarter_pos : 0 < Real.exp (-Real.pi) / 4 := by positivity
    set δ := min (Real.exp (-Real.pi) / 4) (ε / 4194304) with hδ_def
    have hδ_pos : 0 < δ := lt_min h_exp_quarter_pos (div_pos hε (by norm_num))
    refine ⟨δ, hδ_pos, fun q hq_mem hq_dist => ?_⟩
    have hq_ne : q ≠ 0 := hq_mem
    rw [dist_zero_right] at hq_dist
    have hq_norm_lt : ‖q‖ < δ := hq_dist
    have hq_norm_le_exp_qtr : ‖q‖ ≤ Real.exp (-Real.pi) / 4 :=
      le_of_lt (lt_of_lt_of_le hq_norm_lt (min_le_left _ _))
    have hq_norm_lt_div : ‖q‖ < ε / 4194304 :=
      lt_of_lt_of_le hq_norm_lt (min_le_right _ _)
    -- Setup: g(z) := deriv cusp z - 16 + 256·z - 2112·z².
    set g : ℂ → ℂ := fun z => deriv modularLambdaH_cusp z - 16 + 256 * z - 2112 * z^2 with hg_def
    have hq_norm_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq_ne
    have hq_2 : 2 * ‖q‖ ≤ Real.exp (-Real.pi) / 2 := by linarith
    have h_exp_half : Real.exp (-Real.pi) / 2 < Real.exp (-Real.pi) := by
      have := h_exp_pi_pos; linarith
    have h_exp_lt_1 : Real.exp (-Real.pi) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith [Real.pi_pos]
    have hq_2_lt_1 : 2 * ‖q‖ < 1 :=
      lt_of_le_of_lt (le_trans hq_2 (le_of_lt h_exp_half)) h_exp_lt_1
    have hz_norm_lt (z : ℂ) (hz : z ∈ Metric.ball q ‖q‖) : ‖z‖ < 2 * ‖q‖ := by
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      calc ‖z‖ = ‖(z - q) + q‖ := by congr 1; ring
        _ ≤ ‖z - q‖ + ‖q‖ := norm_add_le _ _
        _ < ‖q‖ + ‖q‖ := by linarith
        _ = 2 * ‖q‖ := by ring
    -- Differentiability of deriv cusp on ball(0, 1).
    have h_dderiv_on :
        DifferentiableOn ℂ (deriv modularLambdaH_cusp) (Metric.ball (0 : ℂ) 1) :=
      modularLambdaH_cusp_differentiableOn_unitBall.deriv Metric.isOpen_ball
    have h_dderiv_at (z : ℂ) (hz_norm : ‖z‖ < 1) :
        DifferentiableAt ℂ (deriv modularLambdaH_cusp) z := by
      apply (h_dderiv_on.differentiableAt)
      apply Metric.isOpen_ball.mem_nhds
      rw [Metric.mem_ball, dist_zero_right]; exact hz_norm
    -- g is differentiable on ball(0, 1).
    have h_g_diff_at (z : ℂ) (hz_norm : ‖z‖ < 1) : DifferentiableAt ℂ g z := by
      apply DifferentiableAt.sub
      · apply DifferentiableAt.add
        · exact (h_dderiv_at z hz_norm).sub (differentiableAt_const 16)
        · exact (differentiableAt_const 256).mul differentiableAt_id
      · exact (differentiableAt_const 2112).mul (differentiableAt_id.pow 2)
    have h_g_diff : DifferentiableOn ℂ g (Metric.ball q ‖q‖) := fun z hz =>
      (h_g_diff_at z ((hz_norm_lt z hz).trans hq_2_lt_1)).differentiableWithinAt
    have h_g_cont_cl : ContinuousOn g (Metric.closedBall q ‖q‖) := by
      intro z hz
      rw [Metric.mem_closedBall, Complex.dist_eq] at hz
      have hz_norm_le : ‖z‖ ≤ 2 * ‖q‖ := by
        calc ‖z‖ = ‖(z - q) + q‖ := by congr 1; ring
          _ ≤ ‖z - q‖ + ‖q‖ := norm_add_le _ _
          _ ≤ ‖q‖ + ‖q‖ := by linarith
          _ = 2 * ‖q‖ := by ring
      exact (h_g_diff_at z (lt_of_le_of_lt hz_norm_le hq_2_lt_1)).continuousAt.continuousWithinAt
    have h_diff_cont : DiffContOnCl ℂ g (Metric.ball q ‖q‖) :=
      ⟨h_g_diff, by rwa [closure_ball _ hq_norm_pos.ne']⟩
    -- Sphere bound: ‖g z‖ ≤ 4194304 · ‖q‖³ on z ∈ sphere q ‖q‖.
    have h_sphere_bound : ∀ z ∈ Metric.sphere q ‖q‖, ‖g z‖ ≤ 4194304 * ‖q‖^3 := by
      intro z hz
      rw [Metric.mem_sphere, Complex.dist_eq] at hz
      have hz_norm_eq : ‖z‖ ≤ 2 * ‖q‖ := by
        calc ‖z‖ = ‖(z - q) + q‖ := by congr 1; ring
          _ ≤ ‖z - q‖ + ‖q‖ := norm_add_le _ _
          _ = ‖q‖ + ‖q‖ := by rw [hz]
          _ = 2 * ‖q‖ := by ring
      have hz_norm_le_exp_half : ‖z‖ ≤ Real.exp (-Real.pi) / 2 := le_trans hz_norm_eq hq_2
      have hq_pow_nn : (0 : ℝ) ≤ 4194304 * ‖q‖^3 := by positivity
      by_cases hz_eq : z = 0
      · have h_g_zero : g z = 0 := by
          rw [hz_eq, hg_def]
          change deriv modularLambdaH_cusp 0 - 16 + 256 * 0 - 2112 * 0^2 = 0
          rw [modularLambdaH_cusp_deriv_zero]; ring
        rw [h_g_zero, norm_zero]
        exact hq_pow_nn
      · have h_three_term :=
          modularLambdaH_cusp_deriv_sub_two_term_le hz_norm_le_exp_half hz_eq
        calc ‖g z‖ ≤ 524288 * ‖z‖^3 := h_three_term
          _ ≤ 524288 * (2 * ‖q‖)^3 := by
              apply mul_le_mul_of_nonneg_left
              · apply pow_le_pow_left₀ (norm_nonneg z) hz_norm_eq
              · norm_num
          _ = 4194304 * ‖q‖^3 := by ring
    -- Apply Cauchy.
    have h_cauchy :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hq_norm_pos h_diff_cont h_sphere_bound
    -- deriv g q = deriv (deriv cusp) q + 256 - 4224·q.
    have h_q_norm_lt_1 : ‖q‖ < 1 := lt_of_le_of_lt hq_norm_le_exp_qtr (by linarith)
    have h_dderiv_hasDeriv :
        HasDerivAt (deriv modularLambdaH_cusp) (deriv (deriv modularLambdaH_cusp) q) q :=
      (h_dderiv_at q h_q_norm_lt_1).hasDerivAt
    have h_const_hasDeriv : HasDerivAt (fun _ : ℂ => (16 : ℂ)) 0 q := hasDerivAt_const q 16
    have h_lin_hasDeriv : HasDerivAt (fun z : ℂ => 256 * z) 256 q := by
      simpa using (hasDerivAt_id q).const_mul (256 : ℂ)
    have h_quad_hasDeriv : HasDerivAt (fun z : ℂ => 2112 * z^2) (4224 * q) q := by
      have h_pow : HasDerivAt (fun z : ℂ => z^2) (2 * q) q := by
        simpa using hasDerivAt_pow 2 q
      have := h_pow.const_mul (2112 : ℂ)
      convert! this using 1; ring
    have h_g_hasDeriv : HasDerivAt g
        (deriv (deriv modularLambdaH_cusp) q + 256 - 4224 * q) q := by
      have h_sub1 : HasDerivAt (fun z : ℂ => deriv modularLambdaH_cusp z - 16)
          (deriv (deriv modularLambdaH_cusp) q) q := by
        simpa using h_dderiv_hasDeriv.fun_sub h_const_hasDeriv
      have h_add : HasDerivAt (fun z : ℂ => deriv modularLambdaH_cusp z - 16 + 256 * z)
          (deriv (deriv modularLambdaH_cusp) q + 256) q := h_sub1.add h_lin_hasDeriv
      have h_sub2 : HasDerivAt
          (fun z : ℂ => deriv modularLambdaH_cusp z - 16 + 256 * z - 2112 * z^2)
          (deriv (deriv modularLambdaH_cusp) q + 256 - 4224 * q) q :=
        h_add.sub h_quad_hasDeriv
      exact h_sub2
    have h_deriv_g_eq : deriv g q =
        deriv (deriv modularLambdaH_cusp) q + 256 - 4224 * q :=
      h_g_hasDeriv.deriv
    rw [h_deriv_g_eq] at h_cauchy
    have h_g_at_q_bound : ‖deriv (deriv modularLambdaH_cusp) q + 256 - 4224 * q‖
        ≤ 4194304 * ‖q‖^2 := by
      calc ‖deriv (deriv modularLambdaH_cusp) q + 256 - 4224 * q‖
          ≤ 4194304 * ‖q‖^3 / ‖q‖ := h_cauchy
        _ = 4194304 * ‖q‖^2 := by
            rw [show (‖q‖^3 : ℝ) = ‖q‖^2 * ‖q‖ from by ring]
            field_simp
    -- slope (deriv (deriv cusp)) 0 q = (deriv (deriv cusp) q - (-256))/q.
    -- deriv (deriv cusp) 0 = iteratedDeriv 2 cusp 0 = -256.
    have h_dderiv_at_zero : deriv (deriv modularLambdaH_cusp) 0 = -256 := by
      have := modularLambdaH_cusp_iteratedDeriv_two_zero
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at this
      exact this
    rw [slope_def_field, h_dderiv_at_zero, sub_neg_eq_add, sub_zero]
    -- Goal: dist ((deriv (deriv cusp) q + 256)/q) 4224 < ε.
    have h_factor : (deriv (deriv modularLambdaH_cusp) q + 256) / q - 4224 =
        (deriv (deriv modularLambdaH_cusp) q + 256 - 4224 * q) / q := by
      field_simp
    rw [Complex.dist_eq, h_factor, norm_div]
    calc ‖deriv (deriv modularLambdaH_cusp) q + 256 - 4224 * q‖ / ‖q‖
        ≤ 4194304 * ‖q‖^2 / ‖q‖ :=
          div_le_div_of_nonneg_right h_g_at_q_bound hq_norm_pos.le
      _ = 4194304 * ‖q‖ := by rw [sq]; field_simp
      _ < 4194304 * (ε / 4194304) :=
          mul_lt_mul_of_pos_left hq_norm_lt_div (by norm_num : (0 : ℝ) < 4194304)
      _ = ε := by ring
  exact h_hasDeriv.deriv

end NoWanderingDomains
