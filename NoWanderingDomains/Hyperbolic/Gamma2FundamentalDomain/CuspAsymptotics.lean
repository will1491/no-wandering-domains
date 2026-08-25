/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.Gamma2FundamentalDomain.BoundaryRealArcs

/-! # Cusp asymptotics and the strip bounds

Cusp asymptotics and q-expansion estimates for `λ` inside the open fundamental domain
`F°`. Contains the witness `Im λ((1 + 4i)/2) > 0` and the path-connectedness of `F°`,
the cusp-0 limit `λ(τ) → 1` and the cusp-1 norm blow-up `‖λ(τ)‖ → ∞` along arbitrary
paths in `F°`, and the three-term q-expansion bounds for `λ` and `λ′`. These give
`Im λ ≥ 0` on the interior band `{Re ∈ [1/8, 7/8], Im ≥ 1}` directly, and on the left
and right edge strips via positivity of `Im λ′`, the fundamental theorem of calculus,
and the T-shift plus conjugation symmetry.
-/

namespace NoWanderingDomains
open Complex Filter Topology Set

/-! ## Biholomorphism of `λ` on `F^o`

The modular function `λ` restricted to the open fundamental domain
`F^o` maps onto the open upper half of `ℂ`. The proof is topological,
with three steps:

* `modularLambdaH_F_im_pos` (Step A): `λ(F^o) ⊆ {Im w > 0}` (the image
  lies entirely in the upper half-plane).
* `modularLambdaH_F_image_isOpen` (Step B): `λ(F^o)` is open in `ℂ`
  (open-mapping theorem for non-constant analytic functions on a
  connected open set).
* `modularLambdaH_F_image_isClosed_in_upperHalf` (Step C): `λ(F^o)` is
  closed when viewed inside the upper half-plane (properness: as
  `τ → ∂F^o`, `λ(τ) → ℝ ∪ {∞}` by the four cusp asymptotic theorems
  and the three boundary-real arc theorems).
* `modularLambdaH_image_fundamentalDomainInterior` (Step D): combining
  the above with connectedness of the upper half-plane and
  non-emptiness of `F^o`. -/

/-- **Witness for Step A.** The specific point `(1+4i)/2 ∈ F^o` has
`Im(λ((1+4i)/2)) > 0`. At `τ = 1/2 + 2i`, `Re(πi·τ) = -2π` and
`Im(πi·τ) = π/2`, so `exp(πi·τ) = i · exp(-2π)` and
`16·exp(πi·τ) = 16i·exp(-2π)` has `Im = 16·exp(-2π) ≈ 0.030`.
By `modularLambdaH_norm_sub_lead_le_of_im_ge_one`, the error is
bounded by `4096·exp(-4π) ≈ 0.014`. Hence `Im(λ) ≥ 0.030 - 0.014 > 0`. -/
theorem modularLambdaH_im_pos_at_witness :
    0 < (modularLambdaH ((1 + 4 * Complex.I) / 2)).im := by
  set τ : ℂ := (1 + 4 * Complex.I) / 2 with hτ_def
  -- τ.re = 1/2, τ.im = 2.
  have hτ_re : τ.re = 1/2 := by
    rw [hτ_def]
    simp [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re]
  have hτ_im : τ.im = 2 := by
    rw [hτ_def]
    simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re]
    norm_num
  have hτ_im_ge_one : 1 ≤ τ.im := by rw [hτ_im]; norm_num
  -- (πi · τ).re = -2π, (πi · τ).im = π/2.
  have h_arg_re : (Real.pi * Complex.I * τ).re = -(2 * Real.pi) := by
    rw [show ((Real.pi : ℂ) * Complex.I * τ : ℂ) =
        ((Real.pi : ℝ) : ℂ) * (Complex.I * τ) from by ring]
    rw [Complex.mul_re, Complex.mul_re, Complex.mul_im]
    simp [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hτ_re, hτ_im]
    ring
  have h_arg_im : (Real.pi * Complex.I * τ).im = Real.pi / 2 := by
    rw [show ((Real.pi : ℂ) * Complex.I * τ : ℂ) =
        ((Real.pi : ℝ) : ℂ) * (Complex.I * τ) from by ring]
    rw [Complex.mul_im, Complex.mul_re, Complex.mul_im]
    simp [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hτ_re, hτ_im]
    ring
  -- (exp(πi · τ)).im = exp(-2π) · sin(π/2) = exp(-2π).
  have h_exp_im_compute :
      (Complex.exp (Real.pi * Complex.I * τ)).im = Real.exp (-(2 * Real.pi)) := by
    rw [Complex.exp_im, h_arg_re, h_arg_im, Real.sin_pi_div_two, mul_one]
  -- 16 · exp(πi · τ) has Im = 16 · exp(-2π).
  have h_16exp_im :
      ((16 : ℂ) * Complex.exp (Real.pi * Complex.I * τ)).im =
        16 * Real.exp (-2 * Real.pi) := by
    rw [Complex.mul_im]
    simp [h_exp_im_compute]
  -- Apply leading-term bound.
  have h_bound := modularLambdaH_norm_sub_lead_le_of_im_ge_one hτ_im_ge_one
  -- |Im(λ - 16 exp)| ≤ ‖λ - 16 exp‖ ≤ 4096 exp(-4π) (since τ.im = 2).
  have h_im_le_norm :
      |(modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ)).im| ≤
        ‖modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ)‖ :=
    Complex.abs_im_le_norm _
  have h_im_ge_neg_bound :
      -(4096 * Real.exp (-2 * Real.pi * τ.im)) ≤
        (modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ)).im := by
    have := abs_le.mp h_im_le_norm
    linarith [this.1, h_bound]
  -- τ.im = 2, so exp(-2π · τ.im) = exp(-4π).
  have hτ_im_eq : (-2 * Real.pi * τ.im : ℝ) = -4 * Real.pi := by rw [hτ_im]; ring
  rw [hτ_im_eq] at h_im_ge_neg_bound
  -- Im(λ) = Im(λ - 16 exp) + Im(16 exp).
  have h_lambda_im_decomp :
      (modularLambdaH τ).im =
        (modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ)).im +
        ((16 : ℂ) * Complex.exp (Real.pi * Complex.I * τ)).im := by
    rw [Complex.sub_im]; ring
  rw [h_lambda_im_decomp, h_16exp_im]
  -- Im(λ) ≥ -(4096 exp(-4π)) + 16 exp(-2π).
  -- Show 16 exp(-2π) > 4096 exp(-4π), i.e., exp(2π) > 256 = exp(π)² > 16².
  have h_exp_pi_gt_16 : (16 : ℝ) < Real.exp Real.pi := by
    have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h_exp3_gt_16 : (16 : ℝ) < Real.exp 3 := by
      have h_eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
      rw [h_eq]
      nlinarith [h_e_gt, Real.exp_pos (1 : ℝ)]
    exact h_exp3_gt_16.trans_le (Real.exp_le_exp.mpr Real.pi_gt_three.le)
  have h_exp_2pi_gt_256 : (256 : ℝ) < Real.exp (2 * Real.pi) := by
    have h_eq : Real.exp (2 * Real.pi) = Real.exp Real.pi * Real.exp Real.pi := by
      rw [show (2 * Real.pi : ℝ) = Real.pi + Real.pi from by ring, Real.exp_add]
    rw [h_eq]
    nlinarith [h_exp_pi_gt_16, Real.exp_pos Real.pi]
  -- 4096 exp(-4π) = (4096 / exp(2π)) · exp(-2π) < 16 · exp(-2π).
  have h_exp_neg_4pi : Real.exp (-4 * Real.pi) =
      Real.exp (-2 * Real.pi) * Real.exp (-2 * Real.pi) := by
    rw [show (-4 * Real.pi : ℝ) = (-2 * Real.pi) + (-2 * Real.pi) from by ring, Real.exp_add]
  have h_exp_neg_2pi_lt : Real.exp (-2 * Real.pi) < 1 / 256 := by
    have h_eq : Real.exp (-2 * Real.pi) = (Real.exp (2 * Real.pi))⁻¹ := by
      rw [show (-2 * Real.pi : ℝ) = -(2 * Real.pi) from by ring, Real.exp_neg]
    rw [h_eq, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/256),
      show (1/256 : ℝ)⁻¹ = 256 from by norm_num]
    exact h_exp_2pi_gt_256
  have h_exp_2pi_pos : 0 < Real.exp (-2 * Real.pi) := Real.exp_pos _
  -- Combine.
  have h_4096_lt : 4096 * Real.exp (-4 * Real.pi) < 16 * Real.exp (-2 * Real.pi) := by
    rw [h_exp_neg_4pi]
    -- 4096 * exp(-2π) * exp(-2π) < 16 * exp(-2π) iff 4096 * exp(-2π) < 16
    -- iff exp(-2π) < 16/4096 = 1/256.
    have h_step : 4096 * Real.exp (-2 * Real.pi) < 16 := by
      have : (4096 : ℝ) * (1/256) = 16 := by norm_num
      calc 4096 * Real.exp (-2 * Real.pi)
          < 4096 * (1/256 : ℝ) := by
            apply mul_lt_mul_of_pos_left h_exp_neg_2pi_lt
            norm_num
        _ = 16 := this
    calc 4096 * (Real.exp (-2 * Real.pi) * Real.exp (-2 * Real.pi))
        = (4096 * Real.exp (-2 * Real.pi)) * Real.exp (-2 * Real.pi) := by ring
      _ < 16 * Real.exp (-2 * Real.pi) :=
          mul_lt_mul_of_pos_right h_step h_exp_2pi_pos
  linarith

/-- **Sub-lemma for Step A: F^o is preconnected.** The open fundamental
domain is connected as a topological subspace of `ℂ`. Geometrically,
F^o is the open strip `0 < Re τ < 1, Im τ > 0` with the closed
semi-disk `|2τ − 1| ≤ 1` (which touches the strip's boundary tangentially)
removed. This is path-connected: any two points can be joined via
the "high cap" `{τ : Im τ ≥ 2}` which is convex (hence path-connected).

**Proof outline:**
* The "top" `T := {z : 0 < Re z < 1, 1 < Im z}` is convex (intersection
  of three open half-planes), hence path-connected.
* `T ⊆ F^o` because for `Im z > 1`, `|2z − 1|² ≥ (2 Im z)² > 4 > 1`.
* For any `τ ∈ F^o`, the vertical line from `τ` to `τ + 2i` stays in
  `F^o` (since `Re` is constant in `(0,1)`, `Im` increases, and
  `|2(τ + 2ti) − 1|² ≥ |2τ − 1|² > 1` because the imaginary part of
  `2(τ + 2ti) − 1 = 2τ − 1 + 4ti` is shifted up by `4t ≥ 0`, increasing
  the absolute value).
* `τ + 2i` lies in `T` (with `Im (τ + 2i) = Im τ + 2 ≥ 2 > 1`).
* Hence every `τ ∈ F^o` can be joined to `τ + 2i ∈ T` by a vertical
  line in `F^o`, and `T` is convex/path-connected.
* `JoinedIn.trans` chains these segments to give path-connectedness. -/
theorem Gamma2FundamentalDomainInterior_isPreconnected :
    IsPreconnected Gamma2FundamentalDomainInterior := by
  suffices h : IsPathConnected Gamma2FundamentalDomainInterior from
    h.isConnected.isPreconnected
  -- Base point: τ₀ = (1+4i)/2 = 1/2 + 2i.
  set τ₀ : ℂ := (1 + 4 * Complex.I) / 2 with hτ₀_def
  have hτ₀_im : τ₀.im = 2 := by
    rw [hτ₀_def]
    simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re]
    norm_num
  have hτ₀_re : τ₀.re = 1/2 := by
    rw [hτ₀_def]
    simp [Complex.add_re, Complex.mul_re, Complex.I_im, Complex.I_re]
  -- τ₀ ∈ F^o.
  have hτ₀_in_F : τ₀ ∈ Gamma2FundamentalDomainInterior := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hτ₀_im]; norm_num
    · rw [hτ₀_re]; norm_num
    · rw [hτ₀_re]; norm_num
    · -- |2τ₀ - 1| = |1 + 4i - 1| = |4i| = 4 > 1.
      have heq : 2 * τ₀ - 1 = 4 * Complex.I := by rw [hτ₀_def]; ring
      rw [heq]
      simp
  refine ⟨τ₀, hτ₀_in_F, ?_⟩
  intro τ hτ
  -- Construct JoinedIn F^o τ₀ τ.
  -- Step 1: vertical line from τ₀ to (1/2 + i(Im τ + 3)) - stays in F^o.
  -- Step 2: horizontal line from (1/2 + i(Im τ + 3)) to (Re τ + i(Im τ + 3)) - stays in F^o.
  -- Step 3: vertical line from (Re τ + i(Im τ + 3)) to τ - stays in F^o.
  set M : ℝ := τ.im + 3 with hM_def
  have hM_ge_2 : (2 : ℝ) ≤ M := by rw [hM_def]; linarith [hτ.1]
  -- Top half-strip T := {z : 0 < Re z < 1, 1 < Im z}.
  set T : Set ℂ := { z : ℂ | 0 < z.re ∧ z.re < 1 ∧ 1 < z.im } with hT_def
  -- T ⊆ F^o.
  have hT_sub_F : T ⊆ Gamma2FundamentalDomainInterior := by
    intro z hz
    refine ⟨?_, hz.1, hz.2.1, ?_⟩
    · linarith [hz.2.2]
    · -- |2z - 1| > 1: (2 Re - 1)² + (2 Im)² > 1, since (2 Im)² > 4.
      have h_norm_sq : ‖2 * z - 1‖^2 = (2 * z.re - 1)^2 + (2 * z.im)^2 := by
        rw [Complex.sq_norm]
        simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
          Complex.mul_im]
        ring
      have h_im_sq : 4 < (2 * z.im)^2 := by nlinarith [hz.2.2]
      have h_sum : 1 < (2 * z.re - 1)^2 + (2 * z.im)^2 := by nlinarith [sq_nonneg (2 * z.re - 1)]
      have h_norm_pos : 0 < ‖2 * z - 1‖ := by
        rcases lt_or_eq_of_le (norm_nonneg (2 * z - 1)) with h | h
        · exact h
        · exfalso
          rw [← h] at h_norm_sq
          nlinarith
      nlinarith [sq_nonneg (‖2 * z - 1‖ - 1)]
  -- T is convex.
  have hT_convex : Convex ℝ T := by
    intro z₁ hz₁ z₂ hz₂ s t hs ht hst
    rcases hz₁ with ⟨hz₁_re_pos, hz₁_re_lt, hz₁_im⟩
    rcases hz₂ with ⟨hz₂_re_pos, hz₂_re_lt, hz₂_im⟩
    refine ⟨?_, ?_, ?_⟩
    · change 0 < (s • z₁ + t • z₂).re
      rw [Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
      rcases lt_or_eq_of_le hs with hs_pos | hs_zero
      · nlinarith
      · have ht_pos : 0 < t := by linarith
        nlinarith
    · change (s • z₁ + t • z₂).re < 1
      rw [Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
      rcases lt_or_eq_of_le hs with hs_pos | hs_zero
      · have h1 : s * z₁.re < s * 1 := mul_lt_mul_of_pos_left hz₁_re_lt hs_pos
        have h2 : t * z₂.re ≤ t * 1 := mul_le_mul_of_nonneg_left hz₂_re_lt.le ht
        linarith
      · have ht_pos : 0 < t := by linarith
        have h1 : s * z₁.re ≤ s * 1 := mul_le_mul_of_nonneg_left hz₁_re_lt.le hs
        have h2 : t * z₂.re < t * 1 := mul_lt_mul_of_pos_left hz₂_re_lt ht_pos
        linarith
    · change 1 < (s • z₁ + t • z₂).im
      rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
      rcases lt_or_eq_of_le hs with hs_pos | hs_zero
      · nlinarith
      · have ht_pos : 0 < t := by linarith
        nlinarith
  -- T is nonempty (contains τ₀).
  have hτ₀_in_T : τ₀ ∈ T := ⟨by rw [hτ₀_re]; norm_num,
    by rw [hτ₀_re]; norm_num, by rw [hτ₀_im]; norm_num⟩
  -- T is path-connected.
  have hT_pc : IsPathConnected T := hT_convex.isPathConnected ⟨τ₀, hτ₀_in_T⟩
  -- Build intermediate points.
  set p₁ : ℂ := ⟨(1 : ℝ)/2, M⟩ with hp₁_def
  set p₂ : ℂ := ⟨τ.re, M⟩ with hp₂_def
  have hp₁_re : p₁.re = 1/2 := rfl
  have hp₁_im : p₁.im = M := rfl
  have hp₂_re : p₂.re = τ.re := rfl
  have hp₂_im : p₂.im = M := rfl
  -- p₁ ∈ T.
  have hp₁_in_T : p₁ ∈ T := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hp₁_re]; norm_num
    · rw [hp₁_re]; norm_num
    · rw [hp₁_im]; linarith
  -- p₂ ∈ T.
  have hp₂_in_T : p₂ ∈ T := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hp₂_re]; exact hτ.2.1
    · rw [hp₂_re]; exact hτ.2.2.1
    · rw [hp₂_im]; linarith
  -- Step 1: JoinedIn T τ₀ p₁.
  have h_joined_τ₀_p₁ : JoinedIn T τ₀ p₁ := hT_pc.joinedIn _ hτ₀_in_T _ hp₁_in_T
  -- Step 2: JoinedIn T p₁ p₂.
  have h_joined_p₁_p₂ : JoinedIn T p₁ p₂ := hT_pc.joinedIn _ hp₁_in_T _ hp₂_in_T
  -- Step 3: JoinedIn F^o p₂ τ via vertical line at Re = τ.re.
  -- Use Convex.isPathConnected on segment ℝ p₂ τ.
  have h_joined_p₂_τ : JoinedIn Gamma2FundamentalDomainInterior p₂ τ := by
    have h_seg_convex : Convex ℝ (segment ℝ p₂ τ) := convex_segment p₂ τ
    have h_seg_nonempty : (segment ℝ p₂ τ).Nonempty := ⟨p₂, left_mem_segment ℝ p₂ τ⟩
    have h_seg_pc : IsPathConnected (segment ℝ p₂ τ) :=
      h_seg_convex.isPathConnected h_seg_nonempty
    have h_p₂_mem : p₂ ∈ segment ℝ p₂ τ := left_mem_segment ℝ p₂ τ
    have h_τ_mem : τ ∈ segment ℝ p₂ τ := right_mem_segment ℝ p₂ τ
    have h_joined_seg : JoinedIn (segment ℝ p₂ τ) p₂ τ :=
      h_seg_pc.joinedIn _ h_p₂_mem _ h_τ_mem
    -- Show segment ⊆ F^o.
    have h_seg_sub_F : segment ℝ p₂ τ ⊆ Gamma2FundamentalDomainInterior := by
      intro z hz
      rcases hz with ⟨a, b, ha, hb, hab, h_eq⟩
      -- z = a • p₂ + b • τ.
      -- z.re = a · τ.re + b · τ.re = τ.re (since p₂.re = τ.re).
      have hz_re : z.re = τ.re := by
        rw [← h_eq, Complex.add_re, Complex.smul_re, Complex.smul_re,
          smul_eq_mul, smul_eq_mul, hp₂_re]
        linear_combination τ.re * hab
      -- z.im = a · M + b · τ.im.
      have hz_im : z.im = a * M + b * τ.im := by
        rw [← h_eq, Complex.add_im, Complex.smul_im, Complex.smul_im,
          smul_eq_mul, smul_eq_mul, hp₂_im]
      -- z.im ≥ τ.im.
      have hz_im_ge : τ.im ≤ z.im := by
        rw [hz_im, hM_def]
        nlinarith [hτ.1]
      refine ⟨?_, ?_, ?_, ?_⟩
      · linarith [hτ.1]
      · rw [hz_re]; exact hτ.2.1
      · rw [hz_re]; exact hτ.2.2.1
      · -- |2z - 1|² ≥ |2τ - 1|² > 1.
        have h_norm_sq_z : ‖2 * z - 1‖^2 = (2 * z.re - 1)^2 + (2 * z.im)^2 := by
          rw [Complex.sq_norm]
          simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
            Complex.mul_im]
          ring
        have h_norm_sq_τ : ‖2 * τ - 1‖^2 = (2 * τ.re - 1)^2 + (2 * τ.im)^2 := by
          rw [Complex.sq_norm]
          simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
            Complex.mul_im]
          ring
        have h_norm_τ_gt : 1 < ‖2 * τ - 1‖ := hτ.2.2.2
        have h_im_sq_ge : (2 * τ.im)^2 ≤ (2 * z.im)^2 := by
          have h_im_nn : 0 ≤ τ.im := hτ.1.le
          have h_z_im_nn : 0 ≤ z.im := h_im_nn.trans hz_im_ge
          nlinarith
        have h_re_eq : (2 * z.re - 1)^2 = (2 * τ.re - 1)^2 := by rw [hz_re]
        have h_norm_sq_ge : ‖2 * τ - 1‖^2 ≤ ‖2 * z - 1‖^2 := by
          rw [h_norm_sq_z, h_norm_sq_τ, h_re_eq]
          linarith
        have h_norm_pos_τ : 0 ≤ ‖2 * τ - 1‖ := norm_nonneg _
        have h_norm_pos_z : 0 ≤ ‖2 * z - 1‖ := norm_nonneg _
        have h_z_ge_τ : ‖2 * τ - 1‖ ≤ ‖2 * z - 1‖ := by
          have h1 := sq_nonneg (‖2 * τ - 1‖ - ‖2 * z - 1‖)
          nlinarith
        linarith
    exact h_joined_seg.mono h_seg_sub_F
  -- Combine.
  have h_joined_τ₀_p₂ : JoinedIn Gamma2FundamentalDomainInterior τ₀ p₂ := by
    apply JoinedIn.trans
    · exact (h_joined_τ₀_p₁.mono hT_sub_F)
    · exact (h_joined_p₁_p₂.mono hT_sub_F)
  exact h_joined_τ₀_p₂.trans h_joined_p₂_τ

/-! ## Cusp asymptotics for `λ` inside `F^o`

Two cusp asymptotics needed for the Phragmén–Lindelöf-style closure of
Step A. These are stronger than the existing left-edge-only limits
(`modularLambdaH_iy_tendsto_*`) because the `F^o` constraint
`‖2τ − 1‖ > 1` forces every approach to `0` (resp. `1`) inside `F^o`
to satisfy `Im(−1/(τ − 1)) → ∞` (resp. the q'-expansion gives
`Im λ > 0` for `τ` near `1`). -/

/-- **Cusp 0 limit inside `F^o`.** As `τ → 0` along any path in `F^o`,
`λ(τ) → 1`. This is stronger than `modularLambdaH_iy_tendsto_one_atZeroPos`
(which gives the limit only along the imaginary axis): in `F^o`, the
constraint `‖2τ − 1‖ > 1` (equivalently `(Re τ)² + (Im τ)² > Re τ`)
forces `Re τ < (Im τ)²` near `0`, so `Im(−1/τ) = Im τ / |τ|² → ∞` as
`τ → 0` in `F^o`, and the S-shift identity
`λ(τ) = 1 − λ(−1/τ)` combined with the cusp `i∞` uniform bound
`modularLambdaH_norm_le_exp_of_im_ge_one` gives `λ(τ) → 1`. -/
theorem modularLambdaH_cusp_zero_tendsto_one_in_F :
    Filter.Tendsto modularLambdaH
      (nhdsWithin (0 : ℂ) Gamma2FundamentalDomainInterior) (𝓝 1) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε_pos
  have hπ_pos := Real.pi_pos
  -- Set K := max 1 (log(160000/ε)/π + 1), δ := 1/(3·K).
  set K : ℝ := max 1 (Real.log (160000 / ε) / Real.pi + 1) with hK_def
  have hK_ge_one : 1 ≤ K := le_max_left _ _
  have hK_pos : 0 < K := by linarith
  have hK_ge_log : Real.log (160000 / ε) / Real.pi + 1 ≤ K := le_max_right _ _
  set δ : ℝ := 1 / (3 * K) with hδ_def
  have h_3K_pos : 0 < 3 * K := by linarith
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  refine ⟨δ, hδ_pos, ?_⟩
  intro τ hτ_F hτ_dist
  rw [dist_zero_right] at hτ_dist
  obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ := hτ_F
  -- Standard bounds.
  have hτ_im_le_norm : τ.im ≤ ‖τ‖ := by
    have h_sq : τ.im ^ 2 ≤ ‖τ‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg τ.re]
    have h_norm_nn : 0 ≤ ‖τ‖ := norm_nonneg _
    nlinarith [hτ_im_pos.le, sq_nonneg (τ.im - ‖τ‖)]
  have hτ_re_le_norm : τ.re ≤ ‖τ‖ := by
    have h_sq : τ.re ^ 2 ≤ ‖τ‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg τ.im]
    have h_norm_nn : 0 ≤ ‖τ‖ := norm_nonneg _
    nlinarith [hτ_re_pos.le, sq_nonneg (τ.re - ‖τ‖)]
  have hτ_im_lt_δ : τ.im < δ := lt_of_le_of_lt hτ_im_le_norm hτ_dist
  have hτ_re_lt_δ : τ.re < δ := lt_of_le_of_lt hτ_re_le_norm hτ_dist
  -- δ ≤ 1/3 since K ≥ 1.
  have hδ_le_third : δ ≤ 1/3 := by
    rw [hδ_def]
    rw [div_le_div_iff₀ h_3K_pos (by norm_num : (0:ℝ) < 3)]
    linarith
  have hτ_im_lt_third : τ.im < 1/3 := lt_of_lt_of_le hτ_im_lt_δ hδ_le_third
  have hτ_re_lt_third : τ.re < 1/3 := lt_of_lt_of_le hτ_re_lt_δ hδ_le_third
  -- |τ|² > Re τ (from F^o constraint ‖2τ-1‖ > 1).
  have hτ_normSq_gt_re : τ.re ^ 2 + τ.im ^ 2 > τ.re := by
    have h_sq_lt : 1 < ‖2 * τ - 1‖ ^ 2 := by
      have h_norm_nn : 0 ≤ ‖2 * τ - 1‖ := norm_nonneg _
      nlinarith
    have h_norm_sq_eq : ‖2 * τ - 1‖ ^ 2 = (2 * τ.re - 1) ^ 2 + (2 * τ.im) ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im]
      ring
    rw [h_norm_sq_eq] at h_sq_lt
    nlinarith
  -- Hence Im²τ > Re·(1-Re) ≥ Re·(2/3) for Re < 1/3.
  have h_im_sq_gt : τ.im ^ 2 > τ.re * (2/3) := by
    have h_one_sub : 2/3 < 1 - τ.re := by linarith
    nlinarith [hτ_re_pos.le, hτ_normSq_gt_re]
  -- Hence Re < (3/2)·Im²τ.
  have h_re_lt_3_2_im : τ.re < (3/2) * τ.im ^ 2 := by linarith
  -- |τ|² = Re² + Im² ≤ Re·(1/3) + Im² (since Re < 1/3, Re² ≤ Re·(1/3)).
  -- Re² ≤ Re · Re ≤ Re · (1/3).
  have h_re_sq_le : τ.re ^ 2 ≤ τ.re * (1/3) := by
    have := mul_le_mul_of_nonneg_left hτ_re_lt_third.le hτ_re_pos.le
    nlinarith [sq_nonneg τ.re]
  -- |τ|² ≤ Re·(1/3) + Im²τ ≤ (3/2·Im²τ)·(1/3) + Im²τ = (1/2)·Im²τ + Im²τ = (3/2)·Im²τ.
  -- So |τ|² ≤ (3/2)·Im²τ, hence 1/|τ|² ≥ 2/(3·Im²τ).
  -- Wait actually we want a stronger ratio. Let me redo.
  -- |τ|² = Re² + Im² ≤ (Re·1/3) + Im² ≤ ((3/2·Im²)·1/3) + Im² = (1/2)·Im² + Im² = (3/2)·Im².
  have h_normSq_le : τ.re ^ 2 + τ.im ^ 2 ≤ (3/2) * τ.im ^ 2 := by
    have h_re_sq_bound : τ.re ^ 2 ≤ (1/2) * τ.im ^ 2 := by
      calc τ.re ^ 2 ≤ τ.re * (1/3) := h_re_sq_le
        _ ≤ ((3/2) * τ.im ^ 2) * (1/3) :=
            mul_le_mul_of_nonneg_right h_re_lt_3_2_im.le (by norm_num)
        _ = (1/2) * τ.im ^ 2 := by ring
    linarith
  -- |τ|² ≤ (3/2)·Im²τ. So Im(-1/τ) = Im τ / |τ|² ≥ Im τ / ((3/2)·Im²τ) = 2/(3·Im τ).
  -- For Im τ < 1/3: 2/(3·Im τ) > 2 > 1.
  have hτ_normSq_pos : 0 < τ.re ^ 2 + τ.im ^ 2 := by positivity
  have hτ_normSq_eq : Complex.normSq τ = τ.re ^ 2 + τ.im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have h_inv_im : (-1 / τ).im = τ.im / Complex.normSq τ := by
    rw [show (-1 / τ : ℂ) = -(τ⁻¹) from by ring]
    rw [Complex.neg_im, Complex.inv_im]
    ring
  have h_inv_im_lower : 2 / (3 * τ.im) ≤ (-1 / τ).im := by
    rw [h_inv_im, hτ_normSq_eq]
    have h_3im_pos : 0 < 3 * τ.im := by linarith
    rw [div_le_div_iff₀ h_3im_pos hτ_normSq_pos]
    have : 2 * (τ.re ^ 2 + τ.im ^ 2) ≤ 2 * ((3/2) * τ.im ^ 2) :=
      mul_le_mul_of_nonneg_left h_normSq_le (by norm_num)
    have h_simp : 2 * ((3/2) * τ.im ^ 2) = τ.im * (3 * τ.im) := by ring
    linarith
  -- 2/(3·Im τ) ≥ 2·K when Im τ ≤ 1/(3·K).
  have h_inv_im_ge_2K : 2 * K ≤ (-1 / τ).im := by
    have h_2_K : 2 / (3 * τ.im) ≥ 2 * K := by
      rw [ge_iff_le]
      have h_3im_pos : 0 < 3 * τ.im := by linarith
      rw [le_div_iff₀ h_3im_pos]
      have h_imK : τ.im < 1 / (3 * K) := hτ_im_lt_δ
      have h_mul_lt : 2 * K * (3 * τ.im) < 2 * K * (1 / (3 * K) * 3) := by
        have : 2 * K * (3 * τ.im) < 2 * K * (3 * (1/(3*K))) := by
          have h_im_lt : 3 * τ.im < 3 * (1/(3*K)) :=
            mul_lt_mul_of_pos_left h_imK (by norm_num)
          exact mul_lt_mul_of_pos_left h_im_lt (by linarith : (0:ℝ) < 2 * K)
        linarith
      have h_simp : 2 * K * (1 / (3 * K) * 3) = 2 := by
        field_simp
      linarith
    linarith
  -- Apply cusp ∞ bound at -1/τ.
  have h_inv_im_ge_one : 1 ≤ (-1 / τ).im := le_trans (by linarith) h_inv_im_ge_2K
  have h_lam_bound : ‖modularLambdaH (-1 / τ)‖ ≤
      160000 * Real.exp (-Real.pi * (-1 / τ).im) :=
    modularLambdaH_norm_le_exp_of_im_ge_one h_inv_im_ge_one
  -- S-shift.
  have h_S := modularLambdaH_add_S_smul_eq_one hτ_im_pos
  have h_lam_sub : modularLambdaH τ - 1 = -(modularLambdaH (-1 / τ)) := by
    linear_combination h_S
  rw [dist_eq_norm, h_lam_sub, norm_neg]
  -- We have ‖λ(-1/τ)‖ ≤ 160000·exp(-π·Im(-1/τ)) ≤ 160000·exp(-π·2K) ≤ 160000·exp(-2π·K).
  have h_exp_le : Real.exp (-Real.pi * (-1 / τ).im) ≤ Real.exp (-Real.pi * (2 * K)) := by
    apply Real.exp_le_exp.mpr
    have : -Real.pi * (-1 / τ).im ≤ -Real.pi * (2 * K) := by
      have h := h_inv_im_ge_2K
      nlinarith [Real.pi_pos]
    exact this
  -- 160000·exp(-π·2K) ≤ 160000·exp(-π·(log(160000/ε)/π + 1)·1)
  --                 ≤ 160000·exp(-(log(160000/ε) + π))
  --                 = 160000·(ε/160000)·exp(-π)
  --                 = ε·exp(-π) < ε.
  have h_K_ge : 2 * K ≥ Real.log (160000 / ε) / Real.pi + 1 := by
    have h1 : K ≥ Real.log (160000 / ε) / Real.pi + 1 := hK_ge_log
    linarith
  have h_pi_2K : -Real.pi * (2 * K) ≤ -(Real.log (160000 / ε) + Real.pi) := by
    have h_lhs_eq : -Real.pi * (2 * K) = -(Real.pi * (2 * K)) := by ring
    have h_rhs : Real.pi * (Real.log (160000 / ε) / Real.pi + 1) =
        Real.log (160000 / ε) + Real.pi := by
      field_simp
    have h_step : Real.pi * (Real.log (160000 / ε) / Real.pi + 1) ≤ Real.pi * (2 * K) :=
      mul_le_mul_of_nonneg_left h_K_ge hπ_pos.le
    rw [h_rhs] at h_step
    linarith
  have h_exp_neg_le : Real.exp (-Real.pi * (2 * K)) ≤
      ε / 160000 * Real.exp (-Real.pi) := by
    have h_exp_le' : Real.exp (-Real.pi * (2 * K)) ≤
        Real.exp (-(Real.log (160000 / ε) + Real.pi)) :=
      Real.exp_le_exp.mpr h_pi_2K
    have h_eq : Real.exp (-(Real.log (160000 / ε) + Real.pi)) =
        ε / 160000 * Real.exp (-Real.pi) := by
      rw [show (-(Real.log (160000 / ε) + Real.pi) : ℝ) =
          -Real.log (160000 / ε) + -Real.pi from by ring]
      rw [Real.exp_add]
      have h_160_div_pos : 0 < 160000 / ε := by positivity
      rw [show -Real.log (160000 / ε) = Real.log (160000 / ε)⁻¹ from
          (Real.log_inv _).symm]
      rw [Real.exp_log (by positivity : (0:ℝ) < (160000/ε)⁻¹)]
      rw [show ((160000 / ε)⁻¹ : ℝ) = ε / 160000 from by
        rw [inv_div]]
    linarith [h_exp_le', h_eq.le]
  -- exp(-π) < 1.
  have h_exp_neg_pi_lt : Real.exp (-Real.pi) < 1 := by
    rw [show (-Real.pi : ℝ) = -(Real.pi) from rfl]
    rw [Real.exp_neg]
    have h_exp_pi_gt : 1 < Real.exp Real.pi := by
      have h1 : (0:ℝ) < Real.pi := hπ_pos
      have h := Real.add_one_le_exp Real.pi
      linarith
    have h_inv_lt : (Real.exp Real.pi)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      right; exact h_exp_pi_gt
    exact h_inv_lt
  calc ‖modularLambdaH (-1 / τ)‖
      ≤ 160000 * Real.exp (-Real.pi * (-1 / τ).im) := h_lam_bound
    _ ≤ 160000 * Real.exp (-Real.pi * (2 * K)) :=
        mul_le_mul_of_nonneg_left h_exp_le (by norm_num)
    _ ≤ 160000 * (ε / 160000 * Real.exp (-Real.pi)) :=
        mul_le_mul_of_nonneg_left h_exp_neg_le (by norm_num)
    _ = ε * Real.exp (-Real.pi) := by field_simp
    _ < ε * 1 := mul_lt_mul_of_pos_left h_exp_neg_pi_lt hε_pos
    _ = ε := by ring

/-- Helper for `modularLambdaH_im_nonneg_strip_interior_band`: `exp π > 22`.
Used to derive `r := exp(−πY) < 1/22` when `Y ≥ 1`. -/
theorem exp_pi_gt_22 : (22 : ℝ) < Real.exp Real.pi := by
  have he1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he3_pow : (2.7 : ℝ)^3 < (Real.exp 1)^3 :=
    pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
  have he3_eq : (Real.exp 1)^3 = Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 from by ring, Real.exp_add, Real.exp_add]
    ring
  have he3 : (19.683 : ℝ) < Real.exp 3 := by
    rw [← he3_eq]
    have : (2.7 : ℝ)^3 = 19.683 := by norm_num
    linarith
  have he014 : (1.14 : ℝ) < Real.exp 0.14 := by
    have h_add : (0.14 : ℝ) ≠ 0 := by norm_num
    have h := Real.add_one_lt_exp h_add
    linarith
  have he314_eq : Real.exp 3.14 = Real.exp 3 * Real.exp 0.14 := by
    rw [← Real.exp_add]; congr 1; norm_num
  have he314 : (22 : ℝ) < Real.exp 3.14 := by
    rw [he314_eq]
    have hpos3 : 0 < Real.exp 3 := Real.exp_pos _
    have h_prod : (19.683 : ℝ) * 1.14 ≤ Real.exp 3 * Real.exp 0.14 := by
      apply mul_le_mul he3.le he014.le (by norm_num) hpos3.le
    have h_lt : (22 : ℝ) < 19.683 * 1.14 := by norm_num
    linarith
  have h_pi : (3.14 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
  exact lt_of_lt_of_le he314 (Real.exp_le_exp.mpr h_pi.le)

/-- Helper: `√2 < 1.42`. -/
theorem sqrt_two_lt_142 : Real.sqrt 2 < 1.42 := by
  have h1 : Real.sqrt 2 < Real.sqrt ((1.42 : ℝ)^2) := by
    apply Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 2)
    norm_num
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.42)] at h1

/-- Helper: `1.41 < √2`. -/
theorem sqrt_two_gt_141 : (1.41 : ℝ) < Real.sqrt 2 := by
  have h1 : Real.sqrt ((1.41 : ℝ)^2) < Real.sqrt 2 := by
    apply Real.sqrt_lt_sqrt (by positivity : (0:ℝ) ≤ (1.41 : ℝ)^2)
    norm_num
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.41)] at h1

/-- Helper: `cos(π/8) < 0.926`. Uses `cos(π/8) = √(2 + √2)/2` and `√2 < 1.42`. -/
theorem cos_pi_div_eight_lt_926 : Real.cos (Real.pi / 8) < 0.926 := by
  rw [Real.cos_pi_div_eight]
  have h_inner_nn : (0 : ℝ) ≤ 2 + Real.sqrt 2 := by
    have := Real.sqrt_nonneg 2; linarith
  have h_1852_sq : ((1.852 : ℝ))^2 = 3.429904 := by norm_num
  have h_inner_lt_pow : (2 : ℝ) + Real.sqrt 2 < (1.852 : ℝ)^2 := by
    rw [h_1852_sq]; linarith [sqrt_two_lt_142]
  have h_step : Real.sqrt (2 + Real.sqrt 2) < Real.sqrt ((1.852 : ℝ)^2) :=
    Real.sqrt_lt_sqrt h_inner_nn h_inner_lt_pow
  rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.852)] at h_step
  linarith

/-- Helper: `sin(π/8) > 0.38`. Uses `sin(π/8) = √(2 − √2)/2` and `√2 < 1.42`. -/
theorem sin_pi_div_eight_gt_38 : (0.38 : ℝ) < Real.sin (Real.pi / 8) := by
  rw [Real.sin_pi_div_eight]
  have h_inner_nn : (0 : ℝ) ≤ 2 - Real.sqrt 2 := by linarith [sqrt_two_lt_142]
  have h_076_sq : ((0.76 : ℝ))^2 = 0.5776 := by norm_num
  have h_inner_gt_pow : ((0.76 : ℝ))^2 < 2 - Real.sqrt 2 := by
    rw [h_076_sq]; linarith [sqrt_two_lt_142]
  have h_step : Real.sqrt ((0.76 : ℝ)^2) < Real.sqrt (2 - Real.sqrt 2) :=
    Real.sqrt_lt_sqrt (by positivity : (0:ℝ) ≤ (0.76 : ℝ)^2) h_inner_gt_pow
  rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 0.76)] at h_step
  linarith

/-- Helper: bracket lower bound for `modularLambdaH_im_nonneg_strip_interior_band`.
For `c ≤ cπ8`, `0 < cπ8 ≤ 1`, and `r ∈ (0, 1/22)`, the bracket
`B(c, r) := 16r − 256 r² c + 704 r³ (4c² − 1)` satisfies
`B(c, r) ≥ B(cπ8, r)`.
Proof via the algebraic identity
`B(c, r) − B(cπ8, r) = 256 r² (cπ8 − c)·(1 − 11r(c + cπ8))`. -/
theorem interior_band_bracket_lower_bound (r c cπ8 : ℝ)
    (hr_pos : 0 < r) (hr_lt : r < 1 / 22)
    (hcπ8_pos : 0 < cπ8) (hcπ8_le_one : cπ8 ≤ 1)
    (h_cos_ub : c ≤ cπ8) :
    16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1) ≥
      16 * r - 256 * r^2 * cπ8 + 704 * r^3 * (4 * cπ8^2 - 1) := by
  have h_cπ8_minus_c : 0 ≤ cπ8 - c := by linarith
  have h_sum_le : c + cπ8 ≤ 2 * cπ8 := by linarith
  have h_one_minus_pos : 0 ≤ 1 - 11 * r * (c + cπ8) := by
    have h_step1 : 11 * r * (c + cπ8) ≤ 11 * r * (2 * cπ8) := by
      have h_11r_pos : 0 ≤ 11 * r := by linarith
      exact mul_le_mul_of_nonneg_left h_sum_le h_11r_pos
    have h_step2 : 11 * r * (2 * cπ8) = 22 * r * cπ8 := by ring
    have h_step3 : 22 * r * cπ8 < 1 * cπ8 := by
      apply mul_lt_mul_of_pos_right _ hcπ8_pos
      linarith
    have h_step4 : 1 * cπ8 ≤ 1 := by linarith
    linarith
  have h_r_sq_pos : 0 ≤ 256 * r^2 := by positivity
  have h_diff_nn : 0 ≤ 256 * r^2 * (cπ8 - c) * (1 - 11 * r * (c + cπ8)) := by
    apply mul_nonneg
    · apply mul_nonneg h_r_sq_pos h_cπ8_minus_c
    · exact h_one_minus_pos
  have h_identity :
      (16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1)) -
      (16 * r - 256 * r^2 * cπ8 + 704 * r^3 * (4 * cπ8^2 - 1)) =
      256 * r^2 * (cπ8 - c) * (1 - 11 * r * (c + cπ8)) := by
    ring
  linarith [h_diff_nn, h_identity]

/-- Helper polynomial inequality for `modularLambdaH_im_nonneg_strip_interior_band`.
For `r ∈ (0, 1/22)`,
`0.38 · (16r − 237.056 r² + 1696.64 r³) ≥ 32768 r⁴`.
Proof via Horner factorization `r · g(r)` where
`g(r) := 6.08 − 90.08128 r + 644.7232 r² − 32768 r³ ≥ 0.23`. -/
theorem interior_band_polynomial_inequality (r : ℝ)
    (hr_pos : 0 < r) (hr_lt : r < 1 / 22) :
    0.38 * (16 * r - 237.056 * r^2 + 1696.64 * r^3) ≥ 32768 * r^4 := by
  have hr_le : r ≤ 1/22 := le_of_lt hr_lt
  have h_r2_le : r^2 ≤ 1/484 := by
    have h_step1 : r * r ≤ r * (1/22) :=
      mul_le_mul_of_nonneg_left hr_le (le_of_lt hr_pos)
    have h_step2 : r * (1/22 : ℝ) ≤ (1/22) * (1/22) :=
      mul_le_mul_of_nonneg_right hr_le (by norm_num)
    have h_eq_sq : r^2 = r * r := sq r
    have h_eq_const : (1/22 : ℝ) * (1/22) = 1/484 := by norm_num
    linarith
  have h_inner_lb : (644.7232 : ℝ) - 32768 * r ≥ -845 := by
    have h_le : 32768 * r ≤ 32768 * (1/22 : ℝ) :=
      mul_le_mul_of_nonneg_left hr_le (by norm_num)
    have h_val : (32768 : ℝ) * (1/22) ≤ 1489.7232 := by norm_num
    linarith
  have h_90r : 90.08128 * r ≤ 4.1 := by
    have h_le : 90.08128 * r ≤ 90.08128 * (1/22 : ℝ) :=
      mul_le_mul_of_nonneg_left hr_le (by norm_num)
    have h_val : (90.08128 : ℝ) * (1/22) ≤ 4.1 := by norm_num
    linarith
  have h_845r2 : 845 * r^2 ≤ 1.75 := by
    have h_le : 845 * r^2 ≤ 845 * (1/484 : ℝ) :=
      mul_le_mul_of_nonneg_left h_r2_le (by norm_num)
    have h_val : (845 : ℝ) * (1/484) ≤ 1.75 := by norm_num
    linarith
  have h_horner_eq : (6.08 : ℝ) - 90.08128 * r + 644.7232 * r^2 - 32768 * r^3 =
      6.08 + r * (-90.08128 + r * (644.7232 - 32768 * r)) := by ring
  have h_outer_eq : r * (-90.08128 - 845 * r) = -(90.08128 * r) - 845 * r^2 := by ring
  have h_middle : -90.08128 + r * (644.7232 - 32768 * r) ≥ -90.08128 - 845 * r := by
    have h_mul : r * (644.7232 - 32768 * r) ≥ r * (-845) :=
      mul_le_mul_of_nonneg_left h_inner_lb (le_of_lt hr_pos)
    have h_eq : r * (-845 : ℝ) = -(845 * r) := by ring
    linarith
  have h_outer : r * (-90.08128 + r * (644.7232 - 32768 * r)) ≥
      r * (-90.08128 - 845 * r) :=
    mul_le_mul_of_nonneg_left h_middle (le_of_lt hr_pos)
  have h_g_lb : (6.08 : ℝ) - 90.08128 * r + 644.7232 * r^2 - 32768 * r^3 ≥ 0.23 := by
    linarith
  have h_f_eq : (0.38 : ℝ) * (16 * r - 237.056 * r^2 + 1696.64 * r^3) - 32768 * r^4 =
      r * (6.08 - 90.08128 * r + 644.7232 * r^2 - 32768 * r^3) := by ring
  have h_f_ge : r * (6.08 - 90.08128 * r + 644.7232 * r^2 - 32768 * r^3) ≥ r * 0.23 :=
    mul_le_mul_of_nonneg_left h_g_lb (le_of_lt hr_pos)
  have h_r023_nn : (0 : ℝ) ≤ r * 0.23 :=
    mul_nonneg (le_of_lt hr_pos) (by norm_num)
  linarith

/-- **Interior band of the strip claim: `Im λ ≥ 0` on
`{Re ∈ [1/8, 7/8], Im ≥ 1}`.**

The three-term q-expansion
`‖λ(w) − 16q + 128q² − 704q³‖ ≤ 32768 exp(−4π·Im w)` combined with the
algebraic identity `Im(16q − 128q² + 704q³) = sin(πX)·B(Y, X)` where
`B(Y, X) := 16 exp(−πY) − 256 exp(−2πY)·cos(πX) +
704 exp(−3πY)·(4cos²(πX) − 1)`.

At the worst case `Y = 1, X = 1/8` (or `X = 7/8` by symmetry):
* `sin(π/8) = √(2 − √2)/2 > 0.382`
* `cos(π/8) = √(2 + √2)/2 < 0.925`
* `B(1, 1/8) > 0.387` (computed via `Real.pi_lt_d6`, `Real.exp_one_gt_d9`).
* `Im(leading) > 0.382 · 0.387 ≈ 0.148`.
* Error `32768 · exp(−4π) < 0.117`.
* Margin `≈ 0.030`, formalizable via Mathlib's tight bounds.

For larger `Y`, the margin grows since the error decays as `exp(−4πY)`
while the leading decays only as `exp(−πY)`. -/
theorem modularLambdaH_im_nonneg_strip_interior_band (w : ℂ)
    (hw_re_lo : (1 : ℝ) / 8 ≤ w.re) (hw_re_hi : w.re ≤ 7 / 8)
    (hw_im_ge : 1 ≤ w.im) :
    0 ≤ (modularLambdaH w).im := by
  -- Strategy: apply three-term q-expansion bound, then verify
  -- Im(16q − 128q² + 704q³) − error ≥ 0 via tight numerical bounds.
  set Y := w.im with hY_def
  set X := w.re with hX_def
  have hY_pos : 0 < Y := by linarith
  have hY_one : 1 ≤ Y := hw_im_ge
  -- The argument of `q := exp(πi·w)` decomposes as
  -- `exp(πi·w) = exp(−π·Y) · exp(πi·X)`.
  -- Hence `q.re = exp(−πY)·cos(πX)` and `q.im = exp(−πY)·sin(πX)`.
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  -- Set q := exp(π·I·w), then compute real/imaginary parts.
  set q : ℂ := Complex.exp (Real.pi * Complex.I * w) with hq_def
  have h_argq : (Real.pi * Complex.I * w).re = -Real.pi * Y := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hY_def, Complex.ofReal_re,
      Complex.ofReal_im]
  have h_argq_im : (Real.pi * Complex.I * w).im = Real.pi * X := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hX_def, Complex.ofReal_re,
      Complex.ofReal_im]
  -- |q| = exp(-πY).
  have hq_norm : ‖q‖ = Real.exp (-Real.pi * Y) := by
    rw [hq_def, Complex.norm_exp, h_argq]
  -- Apply three-term q-expansion bound.
  set Q2 : ℂ := Complex.exp (2 * Real.pi * Complex.I * w) with hQ2_def
  set Q3 : ℂ := Complex.exp (3 * Real.pi * Complex.I * w) with hQ3_def
  have h_three_term : ‖modularLambdaH w - 16 * q + 128 * Q2 - 704 * Q3‖ ≤
      32768 * Real.exp (-4 * Real.pi * Y) := by
    have := modularLambdaH_norm_sub_three_term_le_of_im_ge_one (τ := w) hY_one
    rwa [← hq_def, ← hQ2_def, ← hQ3_def] at this
  -- Q2 = q^2, Q3 = q^3.
  have hQ2_eq : Q2 = q^2 := by
    rw [hQ2_def, hq_def, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hQ3_eq : Q3 = q^3 := by
    rw [hQ3_def, hq_def, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  -- Set r := exp(-πY) and the trig values.
  set r : ℝ := Real.exp (-Real.pi * Y) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  -- q.re = r·cos(πX), q.im = r·sin(πX).
  -- The decomposition `π·I·w = (−π·Y) + (π·X)·I` (real/imag parts).
  have h_decomp : Real.pi * Complex.I * w =
      ((-Real.pi * Y : ℝ) : ℂ) + ((Real.pi * X : ℝ) : ℂ) * Complex.I := by
    have hw_decomp : w = (X : ℂ) + (Y : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, hX_def]
      · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, hY_def]
    rw [hw_decomp]
    push_cast
    have hI_sq : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (Real.pi * Y) * hI_sq
  have hq_re_eq : q.re = r * Real.cos (Real.pi * X) := by
    rw [hq_def, h_decomp, Complex.exp_add, Complex.exp_ofReal_mul_I,
      Complex.mul_re, Complex.exp_ofReal_re, Complex.exp_ofReal_im]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [show r = Real.exp (-Real.pi * Y) from hr_def]
    ring
  have hq_im_eq : q.im = r * Real.sin (Real.pi * X) := by
    rw [hq_def, h_decomp, Complex.exp_add, Complex.exp_ofReal_mul_I,
      Complex.mul_im, Complex.exp_ofReal_re, Complex.exp_ofReal_im]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [show r = Real.exp (-Real.pi * Y) from hr_def]
    ring
  -- Q2.im = r² · sin(2πX) = 2 r² sin(πX) cos(πX).
  -- Q3.im = r³ · sin(3πX) = r³ sin(πX) (4cos²(πX) − 1).
  -- These follow from Q2 = q² and Q3 = q³.
  have hQ2_re_eq : Q2.re = r^2 * (Real.cos (Real.pi * X))^2 -
      r^2 * (Real.sin (Real.pi * X))^2 := by
    rw [hQ2_eq, sq, Complex.mul_re, hq_re_eq, hq_im_eq]; ring
  have hQ2_im_eq : Q2.im = 2 * r^2 * Real.cos (Real.pi * X) * Real.sin (Real.pi * X) := by
    rw [hQ2_eq, sq, Complex.mul_im, hq_re_eq, hq_im_eq]; ring
  have hQ3_im_eq : Q3.im = r^3 * Real.sin (Real.pi * X) *
      (4 * (Real.cos (Real.pi * X))^2 - 1) := by
    rw [hQ3_eq, show q^3 = q^2 * q from by ring, Complex.mul_im, ← hQ2_eq,
      hQ2_re_eq, hQ2_im_eq, hq_re_eq, hq_im_eq]
    have h_pyth : (Real.sin (Real.pi * X))^2 + (Real.cos (Real.pi * X))^2 = 1 :=
      Real.sin_sq_add_cos_sq (Real.pi * X)
    linear_combination -r^3 * Real.sin (Real.pi * X) * h_pyth
  -- The imaginary part of `16q − 128 Q2 + 704 Q3` factors as
  -- `sin(πX) · Bracket(Y, X)` with explicit bracket.
  set s : ℝ := Real.sin (Real.pi * X) with hs_def
  set c : ℝ := Real.cos (Real.pi * X) with hc_def
  have h_lead_im : (16 * q - 128 * Q2 + 704 * Q3).im =
      s * (16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1)) := by
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im]
    simp only [show (16 : ℂ).re = 16 from rfl, show (16 : ℂ).im = 0 from rfl,
      show (128 : ℂ).re = 128 from rfl, show (128 : ℂ).im = 0 from rfl,
      show (704 : ℂ).re = 704 from rfl, show (704 : ℂ).im = 0 from rfl]
    rw [hq_re_eq, hq_im_eq, hQ2_re_eq, hQ2_im_eq, hQ3_im_eq]
    ring
  -- Lower bound on `s = sin(πX)` for `X ∈ [1/8, 7/8]`.
  -- We have πX ∈ [π/8, 7π/8], and sin attains its min on this interval at the
  -- endpoints, both equal to sin(π/8).
  have h_piX_lo : Real.pi / 8 ≤ Real.pi * X := by
    have hX_lo : (1 : ℝ) / 8 ≤ X := hw_re_lo
    have h_div : Real.pi / 8 = Real.pi * (1 / 8) := by ring
    rw [h_div]
    exact mul_le_mul_of_nonneg_left hX_lo hπ_pos.le
  have h_piX_hi : Real.pi * X ≤ 7 * Real.pi / 8 := by
    have hX_hi : X ≤ 7 / 8 := hw_re_hi
    have h_div : 7 * Real.pi / 8 = Real.pi * (7 / 8) := by ring
    rw [h_div]
    exact mul_le_mul_of_nonneg_left hX_hi hπ_pos.le
  have h_piX_pos : 0 < Real.pi * X := by
    have : 0 < Real.pi / 8 := by positivity
    linarith
  have h_piX_lt_pi : Real.pi * X < Real.pi := by
    have : 7 * Real.pi / 8 < Real.pi := by linarith
    linarith
  -- sin(πX) ≥ sin(π/8) using `Real.sin_pos_of_pos_of_lt_pi` and monotonicity on
  -- the two halves of [0, π].
  have h_sin_pos : 0 < s := by
    rw [hs_def]
    exact Real.sin_pos_of_pos_of_lt_pi h_piX_pos h_piX_lt_pi
  have h_sin_lb : Real.sin (Real.pi / 8) ≤ s := by
    rw [hs_def]
    have h_neg_pi_div_two : -(Real.pi / 2) ≤ Real.pi / 8 := by
      have : 0 < Real.pi / 2 := by positivity
      have : 0 ≤ Real.pi / 8 := by positivity
      linarith
    by_cases h_X_le_half : X ≤ 1 / 2
    · -- Case X ∈ [1/8, 1/2]: πX ∈ [π/8, π/2]. sin monotone increasing.
      have h_piX_le_half : Real.pi * X ≤ Real.pi / 2 := by
        have h_div : Real.pi / 2 = Real.pi * (1 / 2) := by ring
        rw [h_div]
        exact mul_le_mul_of_nonneg_left h_X_le_half hπ_pos.le
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        h_neg_pi_div_two h_piX_le_half h_piX_lo
    · -- Case X ∈ (1/2, 7/8]: πX ∈ (π/2, 7π/8]. Use symmetry sin(πX) = sin(π − πX).
      push Not at h_X_le_half
      have h_piX_gt_half : Real.pi / 2 < Real.pi * X := by
        have h_div : Real.pi / 2 = Real.pi * (1 / 2) := by ring
        rw [h_div]
        exact mul_lt_mul_of_pos_left h_X_le_half hπ_pos
      -- sin(πX) = sin(π − πX); π − πX ∈ [π/8, π/2).
      have h_sin_sym : Real.sin (Real.pi * X) = Real.sin (Real.pi - Real.pi * X) := by
        rw [Real.sin_pi_sub]
      rw [h_sin_sym]
      have h_pi_sub_lo : Real.pi / 8 ≤ Real.pi - Real.pi * X := by linarith
      have h_pi_sub_hi : Real.pi - Real.pi * X ≤ Real.pi / 2 := by linarith
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        h_neg_pi_div_two h_pi_sub_hi h_pi_sub_lo
  -- Upper bound on `|c| = |cos(πX)|` by `cos(π/8)` for `X ∈ [1/8, 7/8]`.
  -- cos is monotone decreasing on `[0, π]`, so cos(πX) ≤ cos(π/8) (using X ≥ 1/8)
  -- and cos(πX) ≥ cos(7π/8) = -cos(π/8) (using X ≤ 7/8).
  have h_cos_ub : c ≤ Real.cos (Real.pi / 8) := by
    rw [hc_def]
    have h_X_pos : 0 < Real.pi * X := h_piX_pos
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (le_of_lt h_piX_lt_pi) h_piX_lo
  have h_cos_lb : -Real.cos (Real.pi / 8) ≤ c := by
    rw [hc_def]
    -- cos(πX) ≥ cos(7π/8) = -cos(π/8) for πX ≤ 7π/8.
    have h_cos_at_7_pi_8 : Real.cos (7 * Real.pi / 8) = -Real.cos (Real.pi / 8) := by
      have h_eq : 7 * Real.pi / 8 = Real.pi - Real.pi / 8 := by ring
      rw [h_eq, Real.cos_pi_sub]
    rw [← h_cos_at_7_pi_8]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (by linarith [Real.pi_pos] : 7 * Real.pi / 8 ≤ Real.pi) h_piX_hi
  -- Bound on r: r = exp(−πY) ≤ exp(−π) for Y ≥ 1.
  have hr_le : r ≤ Real.exp (-Real.pi) := by
    rw [hr_def]
    apply Real.exp_le_exp.mpr
    nlinarith [hπ_pos]
  -- Hence r < 1/22, using `exp(π) > 22` (helper lemma).
  have hr_lt_22 : r < 1 / 22 := by
    have h_exp_neg : Real.exp (-Real.pi) < 1 / 22 := by
      rw [Real.exp_neg]
      rw [show (Real.exp Real.pi)⁻¹ = 1 / Real.exp Real.pi from by rw [inv_eq_one_div]]
      exact one_div_lt_one_div_of_lt (by norm_num) exp_pi_gt_22
    linarith
  -- Bracket lower bound: B(c, r) ≥ B(cos(π/8), r).
  -- We use the identity B(c, r) - B(cπ8, r) = 256 r² (cπ8 - c) · (1 - 11 r (c + cπ8))
  -- and show RHS ≥ 0 for c ≤ cπ8 and r < 1/22 with cπ8 ≤ 1.
  set cπ8 : ℝ := Real.cos (Real.pi / 8) with hcπ8_def
  have hcπ8_pos : 0 < cπ8 := by
    rw [hcπ8_def]
    have : 0 < Real.pi / 8 := by positivity
    have h_lt_half : Real.pi / 8 < Real.pi / 2 := by linarith
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, h_lt_half⟩
  have hcπ8_le_one : cπ8 ≤ 1 := by
    rw [hcπ8_def]; exact Real.cos_le_one _
  have h_bracket_lb : 16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1) ≥
      16 * r - 256 * r^2 * cπ8 + 704 * r^3 * (4 * cπ8^2 - 1) :=
    interior_band_bracket_lower_bound r c cπ8 hr_pos hr_lt_22 hcπ8_pos
      hcπ8_le_one h_cos_ub
  -- Numerical bounds (from helper lemmas).
  have h_sqrt2_gt : (1.41 : ℝ) < Real.sqrt 2 := sqrt_two_gt_141
  have h_cπ8_lt : cπ8 < 0.926 := by rw [hcπ8_def]; exact cos_pi_div_eight_lt_926
  have h_sπ8_gt : (0.38 : ℝ) < Real.sin (Real.pi / 8) := sin_pi_div_eight_gt_38
  -- r^4 = exp(-4πY).
  have hr4_eq : r^4 = Real.exp (-4 * Real.pi * Y) := by
    have h_cast : (-4 * Real.pi * Y : ℝ) = ((4 : ℕ) : ℝ) * (-Real.pi * Y) := by
      push_cast; ring
    rw [hr_def, h_cast]
    exact (Real.exp_nat_mul _ _).symm
  -- Decompose Im λ = err.im + lead.im where lead := 16q - 128Q2 + 704Q3.
  have h_im_split : (modularLambdaH w).im =
      (modularLambdaH w - 16 * q + 128 * Q2 - 704 * Q3).im +
        (16 * q - 128 * Q2 + 704 * Q3).im := by
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im]
    ring
  -- |err.im| ≤ ‖err‖ ≤ 32768 · r^4.
  have h_err_abs : |(modularLambdaH w - 16 * q + 128 * Q2 - 704 * Q3).im| ≤
      32768 * r^4 := by
    rw [hr4_eq]
    exact le_trans (Complex.abs_im_le_norm _) h_three_term
  -- Hence err.im ≥ -32768 · r^4.
  have h_err_lb : -(32768 * r^4) ≤
      (modularLambdaH w - 16 * q + 128 * Q2 - 704 * Q3).im :=
    neg_le_of_abs_le h_err_abs
  -- 4 cπ8² - 1 = 1 + √2 (from cos²(π/8) = (2 + √2)/4).
  have h_4cπ8_sq : 4 * cπ8^2 - 1 = 1 + Real.sqrt 2 := by
    rw [hcπ8_def, Real.cos_pi_div_eight]
    have h_sqrt_nn : (0 : ℝ) ≤ 2 + Real.sqrt 2 := by
      have := Real.sqrt_nonneg 2; linarith
    have h_div_sq : (Real.sqrt (2 + Real.sqrt 2) / 2)^2 =
        (Real.sqrt (2 + Real.sqrt 2))^2 / 4 := by ring
    rw [h_div_sq, Real.sq_sqrt h_sqrt_nn]
    ring
  -- Hence 4 cπ8² - 1 > 2.41.
  have h_4cπ8_sq_gt : (2.41 : ℝ) < 4 * cπ8^2 - 1 := by
    rw [h_4cπ8_sq]; linarith
  -- Positivity of r^2, r^3.
  have hr2_pos : 0 < r^2 := pow_pos hr_pos 2
  have hr3_pos : 0 < r^3 := pow_pos hr_pos 3
  have hr4_pos : 0 < r^4 := pow_pos hr_pos 4
  -- B(cπ8, r) > 16r - 237.056 r² + 1696.64 r³ (using cπ8 < 0.926, 4cπ8²-1 > 2.41).
  have h_B_cπ8_lb :
      16 * r - 256 * r^2 * cπ8 + 704 * r^3 * (4 * cπ8^2 - 1) >
        16 * r - 237.056 * r^2 + 1696.64 * r^3 := by
    have h_term2 : -(256 * r^2 * cπ8) > -(256 * r^2 * 0.926) := by
      have h_pos : 0 < 256 * r^2 := by linarith
      have h_mul_lt : 256 * r^2 * cπ8 < 256 * r^2 * 0.926 :=
        mul_lt_mul_of_pos_left h_cπ8_lt h_pos
      linarith
    have h_term3 : 704 * r^3 * (4 * cπ8^2 - 1) > 704 * r^3 * 2.41 := by
      have h_pos : 0 < 704 * r^3 := by linarith
      exact mul_lt_mul_of_pos_left h_4cπ8_sq_gt h_pos
    have h_eq1 : (256 : ℝ) * r^2 * 0.926 = 237.056 * r^2 := by ring
    have h_eq2 : (704 : ℝ) * r^3 * 2.41 = 1696.64 * r^3 := by ring
    linarith
  -- B(c, r) ≥ B(cπ8, r) > 16r - 237.056 r² + 1696.64 r³.
  have h_B_lb_full :
      16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1) >
        16 * r - 237.056 * r^2 + 1696.64 * r^3 := by
    linarith [h_bracket_lb, h_B_cπ8_lb]
  -- B(c, r) ≥ 0.
  -- For r ≤ 1/22, 16r - 237.056 r² > 0 (since r · (16 - 237.056/22) > 0).
  have h_poly_lb_pos : 0 < 16 * r - 237.056 * r^2 + 1696.64 * r^3 := by
    have h_1 : (16 : ℝ) - 237.056 * r > 0 := by
      have : (237.056 : ℝ) * r < 237.056 * (1/22) := by
        exact mul_lt_mul_of_pos_left hr_lt_22 (by norm_num)
      linarith
    have h_2 : 16 * r - 237.056 * r^2 > 0 := by
      have h_factor : 16 * r - 237.056 * r^2 = r * (16 - 237.056 * r) := by ring
      rw [h_factor]; exact mul_pos hr_pos h_1
    linarith [mul_pos (by linarith : (0:ℝ) < 1696.64) hr3_pos]
  have h_B_pos : 0 < 16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1) := by
    linarith
  -- lead.im = s · B(c, r) ≥ 0.38 · B(c, r) ≥ 0.38 · (16r - 237.056 r² + 1696.64 r³).
  have h_s_lb : (0.38 : ℝ) < s := lt_of_lt_of_le h_sπ8_gt h_sin_lb
  have h_lead_im_lb :
      (16 * q - 128 * Q2 + 704 * Q3).im >
        0.38 * (16 * r - 237.056 * r^2 + 1696.64 * r^3) := by
    rw [h_lead_im]
    have h_step1 : (0.38 : ℝ) * (16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1)) <
        s * (16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1)) :=
      mul_lt_mul_of_pos_right h_s_lb h_B_pos
    have h_step2 : (0.38 : ℝ) * (16 * r - 237.056 * r^2 + 1696.64 * r^3) <
        0.38 * (16 * r - 256 * r^2 * c + 704 * r^3 * (4 * c^2 - 1)) :=
      mul_lt_mul_of_pos_left h_B_lb_full (by norm_num)
    linarith
  -- Polynomial inequality: 0.38·(16r - 237.056r² + 1696.64r³) ≥ 32768 r^4 for r ∈ (0, 1/22).
  -- Expand: 6.08 r - 90.08128 r² + 644.7232 r³ ≥ 32768 r^4.
  -- Divide by r > 0: 6.08 - 90.08128 r + 644.7232 r² ≥ 32768 r^3.
  -- For r ≤ 1/22: 90.08128/22 ≈ 4.0946, 32768/22^3 ≈ 3.0779, gap ≈ 2 with r² term help.
  have h_poly_ineq : 0.38 * (16 * r - 237.056 * r^2 + 1696.64 * r^3) ≥ 32768 * r^4 :=
    interior_band_polynomial_inequality r hr_pos hr_lt_22
  -- Now combine: lead.im > 0.38 · (...) ≥ 32768 r^4 ≥ -err.im, so lead.im + err.im > 0.
  rw [h_im_split]
  linarith

/-- **General T-shift form for `λ`.** For `τ ∈ ℍ`,
`λ(τ + 1) = λ(τ)/(λ(τ) − 1)`.
Derived from `modularLambdaH_T_smul` (`λ(τ + 1) = −θ₂(τ)⁴/θ₄(τ)⁴`)
and the Jacobi identity `θ₂⁴ + θ₄⁴ = θ₃⁴`. -/
theorem modularLambdaH_add_one_eq_div_sub_one {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH (τ + 1) = modularLambdaH τ / (modularLambdaH τ - 1) := by
  have h_jacobi : theta2 τ ^ 4 + theta4 τ ^ 4 = theta3 τ ^ 4 := jacobi_identity hτ
  have hne3 : theta3 τ ≠ 0 := theta3_ne_zero hτ
  have hne4 : theta4 τ ≠ 0 := theta4_ne_zero hτ
  have h_lam_sub_ne : modularLambdaH τ - 1 ≠ 0 :=
    sub_ne_zero.mpr (modularLambdaH_ne_one hτ)
  rw [modularLambdaH_T_smul, eq_div_iff h_lam_sub_ne]
  unfold modularLambdaH
  field_simp
  linear_combination -(theta2 τ ^ 4) * h_jacobi

/-- **Cusp 1 norm limit inside `F^o`.** As `τ → 1` along any path in
`F^o`, `‖λ(τ)‖ → ∞`. Proof: `σ := τ − 1 → 0` with `Re σ < 0` and
`Im σ > 0`. Set `w := −1/σ`. Then `|w|² = 1/|σ|² → ∞`; the F^o
constraint `‖2τ − 1‖ > 1` gives `Re w < 1`, hence
`Im²w ≥ |w|² − 1 → ∞`. The cusp-∞ bound
`modularLambdaH_norm_le_exp_of_im_ge_one` then gives `λ(w) → 0`, and the
T-shift identity `λ(τ) = 1 − 1/λ(w)` yields `‖λ(τ)‖ → ∞`. -/
theorem modularLambdaH_cusp_one_tendsto_norm_atTop_in_F :
    Filter.Tendsto (fun τ => ‖modularLambdaH τ‖)
      (nhdsWithin (1 : ℂ) Gamma2FundamentalDomainInterior) Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro N
  have hπ_pos : (0:ℝ) < Real.pi := Real.pi_pos
  set M : ℝ := |N| + 2 with hM_def
  have hM_pos : 0 < M := by rw [hM_def]; have := abs_nonneg N; linarith
  have hM_minus_one_ge_N : N ≤ M - 1 := by
    rw [hM_def]; have := le_abs_self N; linarith
  set K : ℝ := max 1 (Real.log (160000 * M) / Real.pi) with hK_def
  have hK_ge_one : 1 ≤ K := le_max_left _ _
  have hK_pos : 0 < K := by linarith
  have h_K_ge_log : Real.log (160000 * M) / Real.pi ≤ K := le_max_right _ _
  have h_log_pos : 0 < 160000 * M := by positivity
  have h_exp_K_pos : 0 < Real.exp (Real.pi * K) := Real.exp_pos _
  have h_exp_K_ge : 160000 * M ≤ Real.exp (Real.pi * K) := by
    have h_step : Real.log (160000 * M) ≤ Real.pi * K := by
      rw [div_le_iff₀ hπ_pos] at h_K_ge_log; linarith
    have := Real.exp_le_exp.mpr h_step
    rwa [Real.exp_log h_log_pos] at this
  have h_exp_neg_K : 160000 * Real.exp (-Real.pi * K) ≤ 1 / M := by
    rw [show -Real.pi * K = -(Real.pi * K) from by ring, Real.exp_neg, le_div_iff₀ hM_pos]
    rw [show (160000 * (Real.exp (Real.pi * K))⁻¹ * M : ℝ) =
      (160000 * M) / Real.exp (Real.pi * K) from by field_simp]
    rw [div_le_one h_exp_K_pos]
    exact h_exp_K_ge
  set δ : ℝ := 1 / (K + 1) with hδ_def
  have hK_p1_pos : 0 < K + 1 := by linarith
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨Metric.ball (1 : ℂ) δ ∩ Gamma2FundamentalDomainInterior, ?_, ?_⟩
  · rw [mem_nhdsWithin]
    refine ⟨Metric.ball (1 : ℂ) δ, Metric.isOpen_ball, Metric.mem_ball_self hδ_pos, ?_⟩
    intro y hy; exact hy
  · intro τ ⟨hτ_ball, hτ_F⟩
    obtain ⟨hτ_im_pos, hτ_re_pos, hτ_re_lt_one, hτ_semicircle⟩ := hτ_F
    rw [Metric.mem_ball, Complex.dist_eq] at hτ_ball
    set σ := τ - 1 with hσ_def
    have hσ_norm_lt : ‖σ‖ < δ := hτ_ball
    have hσ_im_pos : 0 < σ.im := by
      change 0 < (τ - 1).im
      simp only [Complex.sub_im, Complex.one_im, sub_zero]; exact hτ_im_pos
    have hσ_re_neg : σ.re < 0 := by
      change (τ - 1).re < 0
      simp only [Complex.sub_re, Complex.one_re]; linarith
    have hσ_ne : σ ≠ 0 := fun h => by rw [h] at hσ_im_pos; simp at hσ_im_pos
    have hσ_norm_pos : 0 < ‖σ‖ := norm_pos_iff.mpr hσ_ne
    have hσ_normSq_eq : Complex.normSq σ = ‖σ‖^2 := by rw [← Complex.sq_norm]
    have hσ_normSq_pos : 0 < Complex.normSq σ := Complex.normSq_pos.mpr hσ_ne
    have hτ_F_constraint : -σ.re < Complex.normSq σ := by
      have h_sq_lt : 1 < ‖2 * τ - 1‖^2 := by
        have h_norm_nn : 0 ≤ ‖2 * τ - 1‖ := norm_nonneg _
        nlinarith
      have h_eq : 2 * τ - 1 = 2 * σ + 1 := by rw [hσ_def]; ring
      have h_normSq_eq : Complex.normSq (2 * τ - 1) > 1 := by
        rw [← Complex.sq_norm]; exact h_sq_lt
      rw [h_eq] at h_normSq_eq
      have h_expand : Complex.normSq (2 * σ + 1) = 4 * Complex.normSq σ + 4 * σ.re + 1 := by
        simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.one_re, Complex.one_im]; ring
      rw [h_expand] at h_normSq_eq
      linarith
    set w := -1 / σ with hw_def
    have hw_eq_neg_inv : w = -σ⁻¹ := by rw [hw_def, neg_div, one_div]
    have hw_re : w.re = -σ.re / Complex.normSq σ := by
      rw [hw_eq_neg_inv, Complex.neg_re, Complex.inv_re]; ring
    have hw_im : w.im = σ.im / Complex.normSq σ := by
      rw [hw_eq_neg_inv, Complex.neg_im, Complex.inv_im]; ring
    have hw_im_pos : 0 < w.im := by
      rw [hw_im]; exact div_pos hσ_im_pos hσ_normSq_pos
    have hw_re_pos : 0 < w.re := by
      rw [hw_re]; apply div_pos _ hσ_normSq_pos; linarith
    have hw_re_lt_one : w.re < 1 := by
      rw [hw_re]; rw [div_lt_one hσ_normSq_pos]
      linarith
    have hw_normSq_eq : Complex.normSq w = 1 / Complex.normSq σ := by
      have h1 : ‖w‖^2 = Complex.normSq w := Complex.sq_norm _
      have h2 : ‖σ‖^2 = Complex.normSq σ := Complex.sq_norm _
      have h3 : ‖w‖ = ‖σ‖⁻¹ := by rw [hw_eq_neg_inv, norm_neg, norm_inv]
      rw [← h1, h3, inv_pow, h2, one_div]
    have h_normSq_σ_lt : Complex.normSq σ < δ^2 := by
      rw [hσ_normSq_eq]
      apply sq_lt_sq' (by linarith [norm_nonneg σ]) hσ_norm_lt
    have hw_normSq_gt : Complex.normSq w > (K + 1)^2 := by
      rw [hw_normSq_eq]
      rw [gt_iff_lt, lt_div_iff₀ hσ_normSq_pos]
      have h_pos_sq : 0 < (K + 1)^2 := by positivity
      have h_step : (K + 1)^2 * Complex.normSq σ < (K + 1)^2 * δ^2 :=
        mul_lt_mul_of_pos_left h_normSq_σ_lt h_pos_sq
      have h_δsq_inv : δ^2 = 1 / (K + 1)^2 := by
        rw [hδ_def, div_pow, one_pow]
      have h_eq : (K + 1)^2 * δ^2 = 1 := by
        rw [h_δsq_inv]; field_simp
      linarith
    have hw_re_sq_lt : w.re^2 < 1 := by nlinarith [hw_re_pos, hw_re_lt_one]
    have hw_im_sq_gt : w.im^2 > K^2 := by
      have h_normSq : Complex.normSq w = w.re^2 + w.im^2 := by
        simp [Complex.normSq_apply]; ring
      have h_sum : w.re^2 + w.im^2 > (K + 1)^2 := h_normSq ▸ hw_normSq_gt
      nlinarith
    have hw_im_gt_K : K < w.im := by
      have h_sq : K^2 < w.im^2 := hw_im_sq_gt
      nlinarith [hw_im_pos]
    have hw_im_ge_one : 1 ≤ w.im := by linarith
    have h_lamw_bound : ‖modularLambdaH w‖ ≤ 160000 * Real.exp (-Real.pi * w.im) :=
      modularLambdaH_norm_le_exp_of_im_ge_one hw_im_ge_one
    have h_exp_mono : Real.exp (-Real.pi * w.im) ≤ Real.exp (-Real.pi * K) := by
      apply Real.exp_le_exp.mpr
      have h_mul : Real.pi * K ≤ Real.pi * w.im :=
        mul_le_mul_of_nonneg_left hw_im_gt_K.le hπ_pos.le
      linarith
    have h_lamw_le : ‖modularLambdaH w‖ ≤ 1 / M := by
      calc ‖modularLambdaH w‖
          ≤ 160000 * Real.exp (-Real.pi * w.im) := h_lamw_bound
        _ ≤ 160000 * Real.exp (-Real.pi * K) :=
            mul_le_mul_of_nonneg_left h_exp_mono (by norm_num)
        _ ≤ 1 / M := h_exp_neg_K
    have hlamw_ne_zero : modularLambdaH w ≠ 0 := modularLambdaH_ne_zero hw_im_pos
    have hlamw_norm_pos : 0 < ‖modularLambdaH w‖ := norm_pos_iff.mpr hlamw_ne_zero
    have h_S : modularLambdaH σ + modularLambdaH w = 1 := by
      have := modularLambdaH_add_S_smul_eq_one hσ_im_pos
      rw [hw_def]; exact this
    have hlamσ_eq : modularLambdaH σ = 1 - modularLambdaH w := by linear_combination h_S
    have hστ_eq : σ + 1 = τ := by rw [hσ_def]; ring
    have h_T : modularLambdaH τ = modularLambdaH σ / (modularLambdaH σ - 1) := by
      rw [← hστ_eq]
      exact modularLambdaH_add_one_eq_div_sub_one hσ_im_pos
    have hlamτ_check_eq : modularLambdaH τ = 1 - 1 / modularLambdaH w := by
      rw [h_T, hlamσ_eq]
      have h_denom_eq : (1 - modularLambdaH w) - 1 = -modularLambdaH w := by ring
      rw [h_denom_eq]
      field_simp; ring
    rw [hlamτ_check_eq]
    have h_inv_norm : ‖(1 : ℂ) / modularLambdaH w‖ = 1 / ‖modularLambdaH w‖ := by
      rw [norm_div, norm_one]
    have h_inv_lower : M ≤ ‖(1 : ℂ) / modularLambdaH w‖ := by
      rw [h_inv_norm, le_div_iff₀ hlamw_norm_pos]
      have h_step : ‖modularLambdaH w‖ * M ≤ (1 / M) * M :=
        mul_le_mul_of_nonneg_right h_lamw_le hM_pos.le
      rw [div_mul_cancel₀ 1 (ne_of_gt hM_pos)] at h_step
      linarith
    have h_tri : ‖(1 : ℂ) / modularLambdaH w‖ - ‖(1 : ℂ)‖ ≤
        ‖(1 : ℂ) / modularLambdaH w - 1‖ :=
      norm_sub_norm_le _ _
    have h_one_norm : ‖(1 : ℂ)‖ = 1 := norm_one
    have h_eq_neg : (1 : ℂ) / modularLambdaH w - 1 = -((1 : ℂ) - 1 / modularLambdaH w) := by
      ring
    rw [h_eq_neg, norm_neg] at h_tri
    linarith

/-- **Direct three-term q-expansion bound on `λ'` at `τ.im ≥ 1`.**
For `τ ∈ ℍ` with `τ.im ≥ 1`,
`‖deriv λ τ − 16πi q + 256πi q² − 2112πi q³‖ ≤ 100000 · exp(−4π·τ.im)`
where `q := exp(πi τ)`. The bound is derived from the q-expansion
power series of `λ'` directly. The tight asymptotic value of the
constant is `π · ∑_{n≥4} n |c_n| · exp(−π(n−4)) ≈ 47995`, evaluated
at the boundary `τ.im = 1` (the supremum). The chosen constant
`100000` provides a `≈ 108%` margin over this asymptotic value and
remains compatible with the closure constraint `K · r^3 < 3π` for
`r ≤ exp(−π) < 1/22` required by
`modularLambdaH_deriv_im_nonneg_on_left_edge` (since
`100000/10648 ≈ 9.391 < 3π ≈ 9.425`).

The closure path goes through the widened four-term cusp-function
infrastructure in `ModularFunction/JacobiIdentity.lean`: at the boundary `τ.im = 1`,
`|q| = exp(−π)`, and Cauchy on the standard disk `|z| ≤ exp(−π)`
collapses to zero radius. The widened bound
`modularLambdaH_cusp_norm_sub_four_term_le_widened` extends the
four-term function bound to the strictly larger disk
`|z| ≤ exp(−9π/10)`, allowing Cauchy at radius
`ρ = ‖q‖/4` (sphere stays inside `|z| ≤ 5‖q‖/4 ≤ exp(−9π/10)`).
This yields `modularLambdaH_cusp_deriv_sub_two_term_le_widened`
on the full disk `‖q‖ ≤ exp(−π)`, which combines with the chain
rule `deriv λ τ = πi · q · deriv cusp(q)` to give the stated
derivative bound on `τ.im ≥ 1`. -/
theorem modularLambdaH_deriv_norm_sub_three_term_le_of_im_ge_one
    {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖deriv modularLambdaH τ -
        16 * (Real.pi : ℂ) * Complex.I * Complex.exp (Real.pi * Complex.I * τ) +
        256 * (Real.pi : ℂ) * Complex.I *
          Complex.exp (2 * Real.pi * Complex.I * τ) -
        2112 * (Real.pi : ℂ) * Complex.I *
          Complex.exp (3 * Real.pi * Complex.I * τ)‖ ≤
      100000 * Real.exp (-4 * Real.pi * τ.im) := by
  set q : ℂ := Complex.exp (Real.pi * Complex.I * τ) with hq_def
  have hq_ne : q ≠ 0 := Complex.exp_ne_zero _
  have hτ_im_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  -- ‖q‖ = exp(-π τ.im).
  have h_q_norm_eq : ‖q‖ = Real.exp (-Real.pi * τ.im) := by
    rw [hq_def, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_q_norm_pos : 0 < ‖q‖ := by rw [h_q_norm_eq]; exact Real.exp_pos _
  -- ‖q‖ ≤ exp(-π).
  have h_q_norm_le : ‖q‖ ≤ Real.exp (-Real.pi) := by
    rw [h_q_norm_eq]
    apply Real.exp_le_exp.mpr
    nlinarith
  -- ‖q‖ < 1 from τ.im ≥ 1.
  have h_q_lt_1 : ‖q‖ < 1 := by
    rw [h_q_norm_eq, Real.exp_lt_one_iff]
    nlinarith
  -- ‖q‖^4 = exp(-4π τ.im).
  have h_q_norm_pow4 : ‖q‖^4 = Real.exp (-4 * Real.pi * τ.im) := by
    rw [h_q_norm_eq]
    rw [show (-4 * Real.pi * τ.im : ℝ) =
      (-Real.pi * τ.im) + (-Real.pi * τ.im) + (-Real.pi * τ.im) + (-Real.pi * τ.im) from by ring,
      Real.exp_add, Real.exp_add, Real.exp_add]
    ring
  -- Widened cusp deriv bound at q.
  have h_widened := modularLambdaH_cusp_deriv_sub_two_term_le_widened h_q_norm_le hq_ne
  -- Chain rule for q(τ) = exp(πi τ): deriv q τ = πi · q.
  have h_lin_hasDeriv : HasDerivAt (fun z : ℂ => Real.pi * Complex.I * z)
      (Real.pi * Complex.I) τ := by
    simpa using (hasDerivAt_id τ).const_mul (Real.pi * Complex.I : ℂ)
  have h_q_fn_hasDeriv : HasDerivAt (fun z : ℂ => Complex.exp (Real.pi * Complex.I * z))
      ((Real.pi * Complex.I) * q) τ := by
    have h_comp := (Complex.hasDerivAt_exp (Real.pi * Complex.I * τ)).comp τ h_lin_hasDeriv
    -- h_comp : HasDerivAt (exp ∘ (πi·)) (exp(πi τ) * πi) τ
    convert! h_comp using 1
    rw [hq_def]; ring
  -- Cusp differentiable at q.
  have h_cusp_diff_at_q : DifferentiableAt ℂ modularLambdaH_cusp q :=
    modularLambdaH_cusp_differentiableAt_of_norm_lt_one hq_ne h_q_lt_1
  have h_cusp_hasDeriv : HasDerivAt modularLambdaH_cusp (deriv modularLambdaH_cusp q) q :=
    h_cusp_diff_at_q.hasDerivAt
  -- Composition.
  have h_comp_hasDeriv : HasDerivAt
      (modularLambdaH_cusp ∘ (fun z : ℂ => Complex.exp (Real.pi * Complex.I * z)))
      (deriv modularLambdaH_cusp q * ((Real.pi * Complex.I) * q)) τ :=
    h_cusp_hasDeriv.comp τ h_q_fn_hasDeriv
  -- λ = cusp ∘ (z ↦ exp(πi z)).
  have h_funeq : (modularLambdaH_cusp ∘ (fun z : ℂ => Complex.exp (Real.pi * Complex.I * z))) =
      modularLambdaH := by
    funext τ'
    change modularLambdaH_cusp (Complex.exp (Real.pi * Complex.I * τ')) = modularLambdaH τ'
    have h_qParam_eq : Function.Periodic.qParam 2 τ' = Complex.exp (Real.pi * Complex.I * τ') := by
      unfold Function.Periodic.qParam
      congr 1
      push_cast; ring
    rw [← h_qParam_eq]
    exact modularLambdaH_cusp_qParam τ'
  rw [h_funeq] at h_comp_hasDeriv
  have h_deriv_lam_eq : deriv modularLambdaH τ =
      deriv modularLambdaH_cusp q * ((Real.pi * Complex.I) * q) := h_comp_hasDeriv.deriv
  -- Identities exp(2πi τ) = q², exp(3πi τ) = q³.
  have h_qsq : Complex.exp (2 * Real.pi * Complex.I * τ) = q^2 := by
    rw [show (2 * Real.pi * Complex.I * τ : ℂ) =
      (Real.pi * Complex.I * τ) + (Real.pi * Complex.I * τ) from by ring,
      Complex.exp_add, ← hq_def, sq]
  have h_qcube : Complex.exp (3 * Real.pi * Complex.I * τ) = q^3 := by
    rw [show (3 * Real.pi * Complex.I * τ : ℂ) =
      (2 * Real.pi * Complex.I * τ) + (Real.pi * Complex.I * τ) from by ring,
      Complex.exp_add, h_qsq, ← hq_def]
    ring
  rw [h_qsq, h_qcube, h_deriv_lam_eq]
  -- Algebraic factoring.
  have h_factor :
      deriv modularLambdaH_cusp q * (Real.pi * Complex.I * q) -
        16 * (Real.pi : ℂ) * Complex.I * q +
        256 * (Real.pi : ℂ) * Complex.I * q^2 -
        2112 * (Real.pi : ℂ) * Complex.I * q^3 =
      (Real.pi : ℂ) * Complex.I * q *
        (deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2) := by
    ring
  rw [h_factor]
  -- Norm computation.
  have h_norm_factor :
      ‖(Real.pi : ℂ) * Complex.I * q *
          (deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2)‖ =
      Real.pi * ‖q‖ * ‖deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hπ_pos]
  rw [h_norm_factor]
  -- Bound chain.
  have h_pi_q_nn : (0 : ℝ) ≤ Real.pi * ‖q‖ := by positivity
  have h_exp_nn : (0 : ℝ) ≤ Real.exp (-4 * Real.pi * τ.im) := (Real.exp_pos _).le
  calc Real.pi * ‖q‖ * ‖deriv modularLambdaH_cusp q - 16 + 256 * q - 2112 * q^2‖
      ≤ Real.pi * ‖q‖ * (31000 * ‖q‖^3) :=
        mul_le_mul_of_nonneg_left h_widened h_pi_q_nn
    _ = 31000 * Real.pi * ‖q‖^4 := by ring
    _ = 31000 * Real.pi * Real.exp (-4 * Real.pi * τ.im) := by rw [h_q_norm_pow4]
    _ ≤ 100000 * Real.exp (-4 * Real.pi * τ.im) := by
        have h_pi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
        have h_31000_pi_le : 31000 * Real.pi ≤ 100000 := by nlinarith
        exact mul_le_mul_of_nonneg_right h_31000_pi_le h_exp_nn

set_option maxHeartbeats 400000 in
-- The proof accumulates many local hypotheses (q, Q2, Q3 components,
-- bracket bounds, exp bounds, numerical bounds on √2, cos(π/8)) that
-- exceed the default 200000-heartbeat ceiling. Raising to 400000
-- (the project-wide allowed maximum) is the minimal accommodation.
/-- **Positivity of `Im λ'` on the closed left-edge strip.** For `w`
with `0 ≤ Re w ≤ 1/8` and `Im w ≥ 1`, `Im (deriv λ w) ≥ 0`.

The proof uses the direct three-term derivative bound
`modularLambdaH_deriv_norm_sub_three_term_le_of_im_ge_one`:
`λ' = πi (16q − 256q² + 2112q³) + R` with `|R| ≤ 100000·exp(−4π·Im w)`.
Taking imaginary parts and using `cos(πx)`-bounds:
`Im λ'(w) = π·(16 cos(πx) e^{−πy} − 256 cos(2πx) e^{−2πy} +
2112 cos(3πx) e^{−3πy}) + Im R`.
For `x ∈ [0, 1/8]`, the leading bracket is bounded below by
`14.72 e^{−πy} − 256 e^{−2πy} + (nonneg) ≥ 3·e^{−πy}` when
`r = e^{−πy} ≤ 1/22` (using `cos(π/8) > 0.92`). So
`Im L = π · (bracket) ≥ 3π · r`. The error contributes
`|Im R| ≤ 100000 · r^4`. Closure: `3π · r − 100000 · r^4 = r · (3π − 100000 · r³) ≥ 0`
when `100000 · r³ ≤ 100000/10648 ≈ 9.391 < 3π ≈ 9.425`. -/
theorem modularLambdaH_deriv_im_nonneg_on_left_edge (w : ℂ)
    (hw_re_nn : 0 ≤ w.re) (hw_re_le : w.re ≤ 1 / 8) (hw_im_ge : 1 ≤ w.im) :
    0 ≤ (deriv modularLambdaH w).im := by
  set y := w.im with hy_def
  set x := w.re with hx_def
  have hy_pos : (0 : ℝ) < y := lt_of_lt_of_le one_pos hw_im_ge
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Setup q, Q2, Q3.
  set q : ℂ := Complex.exp (Real.pi * Complex.I * w) with hq_def
  set Q2 : ℂ := Complex.exp (2 * Real.pi * Complex.I * w) with hQ2_def
  set Q3 : ℂ := Complex.exp (3 * Real.pi * Complex.I * w) with hQ3_def
  -- Get derivative bound.
  have h_deriv_bound := modularLambdaH_deriv_norm_sub_three_term_le_of_im_ge_one
    (τ := w) hw_im_ge
  rw [← hq_def, ← hQ2_def, ← hQ3_def] at h_deriv_bound
  -- Compute real/imag parts of q, Q2, Q3.
  have h_argq_re : (Real.pi * Complex.I * w).re = -Real.pi * y := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hy_def,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_argq_im : (Real.pi * Complex.I * w).im = Real.pi * x := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hx_def,
      Complex.ofReal_re, Complex.ofReal_im]
  set r : ℝ := Real.exp (-Real.pi * y) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have h_decomp : Real.pi * Complex.I * w =
      ((-Real.pi * y : ℝ) : ℂ) + ((Real.pi * x : ℝ) : ℂ) * Complex.I := by
    have hw_decomp : w = (x : ℂ) + (y : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, hx_def]
      · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, hy_def]
    rw [hw_decomp]
    push_cast
    have hI_sq : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (Real.pi * y) * hI_sq
  have hq_re_eq : q.re = r * Real.cos (Real.pi * x) := by
    rw [hq_def, h_decomp, Complex.exp_add, Complex.exp_ofReal_mul_I,
      Complex.mul_re, Complex.exp_ofReal_re, Complex.exp_ofReal_im]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [show r = Real.exp (-Real.pi * y) from hr_def]
    ring
  have hq_im_eq : q.im = r * Real.sin (Real.pi * x) := by
    rw [hq_def, h_decomp, Complex.exp_add, Complex.exp_ofReal_mul_I,
      Complex.mul_im, Complex.exp_ofReal_re, Complex.exp_ofReal_im]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [show r = Real.exp (-Real.pi * y) from hr_def]
    ring
  have hQ2_eq : Q2 = q^2 := by
    rw [hQ2_def, hq_def, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hQ3_eq : Q3 = q^3 := by
    rw [hQ3_def, hq_def, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  set s : ℝ := Real.sin (Real.pi * x) with hs_def
  set c : ℝ := Real.cos (Real.pi * x) with hc_def
  have h_pyth : s^2 + c^2 = 1 := Real.sin_sq_add_cos_sq (Real.pi * x)
  have hQ2_re : Q2.re = r^2 * (c^2 - s^2) := by
    rw [hQ2_eq, sq, Complex.mul_re, hq_re_eq, hq_im_eq]; ring
  have hQ2_im : Q2.im = r^2 * (2 * c * s) := by
    rw [hQ2_eq, sq, Complex.mul_im, hq_re_eq, hq_im_eq]; ring
  have hQ3_re : Q3.re = r^3 * (c * (c^2 - 3 * s^2)) := by
    rw [hQ3_eq, show q^3 = q^2 * q from by ring, Complex.mul_re, ← hQ2_eq,
      hQ2_re, hQ2_im, hq_re_eq, hq_im_eq]
    ring
  -- Compute Im(πi(16q - 256 Q2 + 2112 Q3)) = π·(16 c r - 256 r²(c² - s²) + 2112 r³ c (c² - 3s²)).
  -- That is: π·(16 c r - 256(2c² - 1) r² + 2112 c(4c² - 3) r³) using s² + c² = 1.
  set L : ℂ := 16 * (Real.pi : ℂ) * Complex.I * q -
    256 * (Real.pi : ℂ) * Complex.I * Q2 +
    2112 * (Real.pi : ℂ) * Complex.I * Q3 with hL_def
  set E : ℂ := deriv modularLambdaH w - L with hE_def
  have hE_norm : ‖E‖ ≤ 100000 * Real.exp (-4 * Real.pi * y) := by
    have h_eq : E = deriv modularLambdaH w -
        16 * (Real.pi : ℂ) * Complex.I * q +
        256 * (Real.pi : ℂ) * Complex.I * Q2 -
        2112 * (Real.pi : ℂ) * Complex.I * Q3 := by
      rw [hE_def, hL_def]; ring
    rw [h_eq]; exact h_deriv_bound
  -- Im λ' = L.im + E.im.
  have h_split : (deriv modularLambdaH w).im = L.im + E.im := by
    have : deriv modularLambdaH w = L + E := by rw [hE_def]; ring
    rw [this, Complex.add_im]
  -- L.im = π · (16 c r - 256 r² (c²-s²) + 2112 r³ c (c²-3s²)).
  have hL_im : L.im = Real.pi * (16 * c * r - 256 * r^2 * (c^2 - s^2) +
      2112 * r^3 * (c * (c^2 - 3 * s^2))) := by
    -- L = π I (16 q - 256 Q2 + 2112 Q3). Im(π I · z) = π · Re(z).
    have hL_factor : L = (Real.pi : ℂ) * Complex.I *
        (16 * q - 256 * Q2 + 2112 * Q3) := by rw [hL_def]; ring
    rw [hL_factor]
    -- Now compute Im(π I · X) where X := 16 q - 256 Q2 + 2112 Q3.
    set X : ℂ := 16 * q - 256 * Q2 + 2112 * Q3 with hX_def
    have h_im : ((Real.pi : ℂ) * Complex.I * X).im = Real.pi * X.re := by
      rw [show ((Real.pi : ℂ) * Complex.I * X : ℂ) =
          ((Real.pi : ℝ) : ℂ) * (Complex.I * X) from by ring]
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
    rw [h_im]
    -- Now: X.re = 16 q.re - 256 Q2.re + 2112 Q3.re.
    have hX_re : X.re = 16 * (r * c) - 256 * (r^2 * (c^2 - s^2)) +
        2112 * (r^3 * (c * (c^2 - 3 * s^2))) := by
      simp only [hX_def, Complex.add_re, Complex.sub_re, Complex.mul_re,
        show (16 : ℂ).re = 16 from rfl, show (16 : ℂ).im = 0 from rfl,
        show (256 : ℂ).re = 256 from rfl, show (256 : ℂ).im = 0 from rfl,
        show (2112 : ℂ).re = 2112 from rfl, show (2112 : ℂ).im = 0 from rfl,
        zero_mul, sub_zero]
      rw [hq_re_eq, hQ2_re, hQ3_re]
    rw [hX_re]; ring
  -- Bounds on c: c ∈ [cos(π/8), 1] for x ∈ [0, 1/8].
  have h_piX_nn : 0 ≤ Real.pi * x := by
    have : 0 ≤ x := hw_re_nn
    positivity
  have h_piX_le : Real.pi * x ≤ Real.pi / 8 := by
    have hx_le : x ≤ 1 / 8 := hw_re_le
    have h_div : Real.pi / 8 = Real.pi * (1 / 8) := by ring
    rw [h_div]
    exact mul_le_mul_of_nonneg_left hx_le hπ_pos.le
  have h_piX_lt_half : Real.pi * x < Real.pi / 2 := by
    have : Real.pi / 8 < Real.pi / 2 := by linarith
    linarith
  have hc_ge_cπ8 : Real.cos (Real.pi / 8) ≤ c := by
    rw [hc_def]
    exact Real.cos_le_cos_of_nonneg_of_le_pi h_piX_nn (by linarith) h_piX_le
  have hc_le_one : c ≤ 1 := by rw [hc_def]; exact Real.cos_le_one _
  have hc_pos : 0 < c := by
    rw [hc_def]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, h_piX_lt_half⟩
  -- cos(π/8) < 0.926, so c < 0.926. And cos(π/8) > 0.924 needed; we have > 0.38 via helper.
  -- For our bound: c ≥ 0.92 (need cos(π/8) ≥ 0.92).
  -- We have cos_pi_div_eight_lt_926 : cos(π/8) < 0.926. NOT a lower bound!
  -- We need cos(π/8) ≥ some value. Let me derive.
  -- cos(π/8) = √(2 + √2)/2. With √2 > 1.41: 2 + √2 > 3.41, so √(3.41) > 1.847, cos(π/8) > 0.923.
  have h_cπ8_gt_92 : (0.92 : ℝ) < Real.cos (Real.pi / 8) := by
    rw [Real.cos_pi_div_eight]
    -- √(2 + √2)/2 > 0.92 ⟺ √(2 + √2) > 1.84 ⟺ 2 + √2 > 1.84² = 3.3856.
    have h_184_sq : ((1.84 : ℝ))^2 = 3.3856 := by norm_num
    have h_sqrt2_gt : (1.41 : ℝ) < Real.sqrt 2 := sqrt_two_gt_141
    have h_inner_gt : ((1.84 : ℝ))^2 < 2 + Real.sqrt 2 := by
      rw [h_184_sq]; linarith
    have h_inner_nn : (0 : ℝ) ≤ (1.84 : ℝ)^2 := by positivity
    have h_step : Real.sqrt ((1.84 : ℝ)^2) < Real.sqrt (2 + Real.sqrt 2) :=
      Real.sqrt_lt_sqrt h_inner_nn h_inner_gt
    rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.84)] at h_step
    linarith
  have hc_gt_92 : (0.92 : ℝ) < c := lt_of_lt_of_le h_cπ8_gt_92 hc_ge_cπ8
  have hc_sq_ge : (0.8464 : ℝ) ≤ c^2 := by
    have h1 : (0.92 : ℝ)^2 ≤ c^2 := by
      apply pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 0.92)
      linarith
    have h2 : (0.92 : ℝ)^2 = 0.8464 := by norm_num
    linarith
  -- r ≤ exp(-π) < 1/22.
  have hr_le : r ≤ Real.exp (-Real.pi) := by
    rw [hr_def]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hr_lt_22 : r < 1 / 22 := by
    have h_exp_neg : Real.exp (-Real.pi) < 1 / 22 := by
      rw [Real.exp_neg]
      rw [show (Real.exp Real.pi)⁻¹ = 1 / Real.exp Real.pi from by rw [inv_eq_one_div]]
      exact one_div_lt_one_div_of_lt (by norm_num) exp_pi_gt_22
    linarith
  -- Use 2c² - 1 ≤ 1 (max) and 4c² - 3 ≥ 4·0.8464 - 3 = 0.3856 (min).
  have h_2c_sq_minus_1_le : 2 * c^2 - 1 ≤ 1 := by nlinarith [h_pyth, sq_nonneg c]
  have h_4c_sq_minus_3_ge : (0.3856 : ℝ) ≤ 4 * c^2 - 3 := by linarith [hc_sq_ge]
  have h_c2_minus_s2_eq : c^2 - s^2 = 2 * c^2 - 1 := by linarith [h_pyth]
  have h_c2_minus_3s2_eq : c^2 - 3 * s^2 = 4 * c^2 - 3 := by linarith [h_pyth]
  -- Bound the bracket: B := 16 c r - 256 r² (c²-s²) + 2112 r³ c (c²-3s²).
  -- B = 16 c r - 256 (2c²-1) r² + 2112 c (4c²-3) r³.
  -- ≥ 16·0.92·r - 256·1·r² + 2112·0.92·0.3856·r³ = 14.72 r - 256 r² + 749.4 r³.
  have h_bracket : 16 * c * r - 256 * r^2 * (c^2 - s^2) +
      2112 * r^3 * (c * (c^2 - 3 * s^2)) ≥
      14.72 * r - 256 * r^2 := by
    have hr_sq_pos : 0 < r^2 := by positivity
    have hr_cube_pos : 0 < r^3 := by positivity
    -- 16 c r ≥ 16 · 0.92 · r = 14.72 r.
    have h_t1 : 14.72 * r ≤ 16 * c * r := by
      have : 14.72 * r ≤ 16 * c * r := by
        have h_step : 14.72 ≤ 16 * c := by linarith
        nlinarith [hr_pos]
      exact this
    -- -256 r² (c² - s²) ≥ -256 r² (since c² - s² ≤ 1).
    have h_t2 : -(256 * r^2 * (c^2 - s^2)) ≥ -(256 * r^2) := by
      rw [h_c2_minus_s2_eq]
      have h_step : 256 * r^2 * (2 * c^2 - 1) ≤ 256 * r^2 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      linarith
    -- 2112 r³ c (c² - 3s²) ≥ 2112 r³ · 0.92 · 0.3856 = 749.4 r³ ≥ 0.
    have h_t3 : 0 ≤ 2112 * r^3 * (c * (c^2 - 3 * s^2)) := by
      rw [h_c2_minus_3s2_eq]
      have h_c_nn : 0 < c := hc_pos
      have h_4c_sq_minus_3_pos : 0 < 4 * c^2 - 3 := by linarith
      positivity
    linarith
  -- For r ≤ 1/22: 14.72 r - 256 r² ≥ 14.72 r - 256 r/22 = (14.72 - 256/22) r ≈ 3.09 r.
  have h_bracket_lb : 14.72 * r - 256 * r^2 ≥ 3 * r := by
    have h_r_sq_le : 256 * r^2 ≤ 256 * r / 22 := by
      have : 256 * r^2 = 256 * r * r := by ring
      have h_step : 256 * r * r ≤ 256 * r * (1/22) := by
        apply mul_le_mul_of_nonneg_left (le_of_lt hr_lt_22)
        positivity
      have h_eq : 256 * r * (1/22 : ℝ) = 256 * r / 22 := by ring
      linarith
    have h_step2 : 256 * r / 22 ≤ 11.64 * r := by
      have h_div : (256 : ℝ) / 22 ≤ 11.64 := by norm_num
      have : 256 * r / 22 = (256/22) * r := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right h_div (le_of_lt hr_pos)
    linarith
  -- Combine: L.im = π · bracket ≥ π · 3r.
  have h_L_im_lb : L.im ≥ 3 * Real.pi * r := by
    rw [hL_im]
    have h_step1 : 16 * c * r - 256 * r^2 * (c^2 - s^2) +
        2112 * r^3 * (c * (c^2 - 3 * s^2)) ≥ 3 * r := by
      linarith
    have h_step2 : Real.pi * (16 * c * r - 256 * r^2 * (c^2 - s^2) +
        2112 * r^3 * (c * (c^2 - 3 * s^2))) ≥ Real.pi * (3 * r) :=
      mul_le_mul_of_nonneg_left h_step1 hπ_pos.le
    have h_eq : Real.pi * (3 * r) = 3 * Real.pi * r := by ring
    linarith
  -- Error: |E.im| ≤ ‖E‖ ≤ 100000 · exp(-4π y).
  have hr4_eq : r^4 = Real.exp (-4 * Real.pi * y) := by
    have h_cast : (-4 * Real.pi * y : ℝ) = ((4 : ℕ) : ℝ) * (-Real.pi * y) := by
      push_cast; ring
    rw [hr_def, h_cast]
    exact (Real.exp_nat_mul _ _).symm
  have hE_im_abs : |E.im| ≤ 100000 * r^4 := by
    rw [hr4_eq]
    exact le_trans (Complex.abs_im_le_norm _) hE_norm
  have hE_im_lb : E.im ≥ -(100000 * r^4) := neg_le_of_abs_le hE_im_abs
  -- Im λ' ≥ L.im + E.im ≥ 3π r - 100000 r^4. Need ≥ 0.
  -- 3π r - 100000 r^4 = r · (3π - 100000 r^3). Inner ≥ 3π - 100000/10648 ≈ 9.42 - 6.16 > 0.
  rw [h_split]
  have h_r3_le : r^3 ≤ (1/22 : ℝ)^3 :=
    pow_le_pow_left₀ (le_of_lt hr_pos) (le_of_lt hr_lt_22) 3
  have h_22_cube : ((1/22 : ℝ))^3 = 1/10648 := by norm_num
  have h_K_r3_le : 100000 * r^3 ≤ 100000 * ((1/22 : ℝ)^3) :=
    mul_le_mul_of_nonneg_left h_r3_le (by norm_num)
  -- 100000 · (1/22)^3 = 100000/10648 ≈ 9.391 < 9.4 < 9.42 < 3π (since π > 3.14).
  have h_K_22_le : 100000 * ((1/22 : ℝ)^3) < 9.4 := by
    rw [h_22_cube]; norm_num
  have h_inner_nn : 0 ≤ 3 * Real.pi - 100000 * r^3 := by
    have h_lt94 : 100000 * r^3 < 9.4 := lt_of_le_of_lt h_K_r3_le h_K_22_le
    have h_3pi_gt_94 : (9.4 : ℝ) < 3 * Real.pi := by
      have h_pi_gt_d2 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
      linarith
    linarith
  have h_main : 3 * Real.pi * r - 100000 * r^4 ≥ 0 := by
    have h_factor : 3 * Real.pi * r - 100000 * r^4 = r * (3 * Real.pi - 100000 * r^3) := by
      ring
    rw [h_factor]
    exact mul_nonneg (le_of_lt hr_pos) h_inner_nn
  linarith

/-- **Strip left edge: `Im λ ≥ 0` on `{Re ∈ (0, 1/8), Im ≥ 1}`.**

The proof linearizes `λ` along horizontal lines `{t + i · y : t ∈ [0, x]}`
using the fundamental theorem of calculus:
`λ(x + iy) − λ(iy) = ∫_0^x λ'(t + iy) dt`.
Since `λ(iy)` is real (`modularLambdaH_pure_imag_real`), taking imaginary
parts gives
`Im λ(x + iy) = ∫_0^x Im(λ'(t + iy)) dt`.
The integrand is nonneg by
`modularLambdaH_deriv_im_nonneg_on_left_edge`, so the integral is nonneg. -/
theorem modularLambdaH_im_nonneg_strip_left_edge (w : ℂ)
    (hw_re_pos : 0 < w.re) (hw_re_lt : w.re < 1 / 8) (hw_im_ge : 1 ≤ w.im) :
    0 ≤ (modularLambdaH w).im := by
  set x := w.re with hx_def
  set y := w.im with hy_def
  have hy_pos : (0 : ℝ) < y := lt_of_lt_of_le one_pos hw_im_ge
  have hx_pos : 0 < x := hw_re_pos
  have hx_lt : x < 1 / 8 := hw_re_lt
  -- Rewrite w = ↑x + ↑y * I.
  have hw_eq : w = (↑x : ℂ) + (↑y : ℂ) * Complex.I := by
    rw [hx_def, hy_def, Complex.re_add_im]
  -- Define the curve f(t) := λ(↑t + ↑y · I).
  -- Show f has derivative `deriv λ (↑t + ↑y · I)` at each t ∈ uIcc 0 x.
  have hf_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt (fun s : ℝ => modularLambdaH ((↑s : ℂ) + (↑y : ℂ) * Complex.I))
        (deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I)) t := by
    intro t ht
    -- (↑t + ↑y · I).im = y > 0, so λ is differentiable there.
    have h_im_pos : 0 < ((↑t : ℂ) + (↑y : ℂ) * Complex.I).im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add]
      exact hy_pos
    have h_lam_diff : DifferentiableAt ℂ modularLambdaH
        ((↑t : ℂ) + (↑y : ℂ) * Complex.I) := by
      apply (modularLambdaH_differentiableOn _ h_im_pos).differentiableAt
      exact (isOpen_lt continuous_const Complex.continuous_im).mem_nhds h_im_pos
    have h_lam_hda : HasDerivAt modularLambdaH
        (deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I))
        ((↑t : ℂ) + (↑y : ℂ) * Complex.I) := h_lam_diff.hasDerivAt
    -- Inner: HasDerivAt (fun s => ↑s + ↑y * I) 1 t.
    have h_inner : HasDerivAt (fun s : ℝ => (↑s : ℂ) + (↑y : ℂ) * Complex.I) 1 t := by
      have := Complex.ofRealCLM.hasDerivAt (x := t)
      simpa using this.add_const ((↑y : ℂ) * Complex.I)
    -- Chain rule via scomp (explicit IsScalarTower).
    have hst : IsScalarTower ℝ ℂ ℂ := IsScalarTower.right
    have h_chain := @HasDerivAt.scomp ℝ _ ℂ _ _ t ℂ _ _ _ hst _ _ _ _ h_lam_hda h_inner
    simpa using! h_chain
  -- Continuity of the integrand on uIcc.
  have h_int_cont : ContinuousOn
      (fun t : ℝ => deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I))
      (Set.uIcc 0 x) := by
    have h_inner_cont :
        ContinuousOn (fun t : ℝ => ((↑t : ℂ) + (↑y : ℂ) * Complex.I))
          (Set.uIcc 0 x) :=
      (Complex.continuous_ofReal.add continuous_const).continuousOn
    have h_inner_maps :
        Set.MapsTo (fun t : ℝ => ((↑t : ℂ) + (↑y : ℂ) * Complex.I))
          (Set.uIcc 0 x) { z : ℂ | 0 < z.im } := by
      intro t _
      simp only [Set.mem_ofPred_eq, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add]
      exact hy_pos
    have h_deriv_cont :
        ContinuousOn (deriv modularLambdaH) { z : ℂ | 0 < z.im } := by
      have h_diff_on : DifferentiableOn ℂ modularLambdaH { z : ℂ | 0 < z.im } :=
        modularLambdaH_differentiableOn
      exact (h_diff_on.analyticOnNhd
        (isOpen_lt continuous_const Complex.continuous_im)).deriv.continuousOn
    exact h_deriv_cont.comp h_inner_cont h_inner_maps
  have h_int_integrable : IntervalIntegrable
      (fun t : ℝ => deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I))
      MeasureTheory.volume 0 x :=
    h_int_cont.intervalIntegrable
  -- FTC.
  have h_ftc :
      ∫ t in (0 : ℝ)..x, deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I) =
      modularLambdaH ((↑x : ℂ) + (↑y : ℂ) * Complex.I) -
        modularLambdaH ((↑(0 : ℝ) : ℂ) + (↑y : ℂ) * Complex.I) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hf_deriv h_int_integrable
  -- λ(iy) is real (Im = 0).
  have h_lam_iy_im : (modularLambdaH ((↑(0 : ℝ) : ℂ) + (↑y : ℂ) * Complex.I)).im = 0 := by
    have h_iy_eq : ((↑(0 : ℝ) : ℂ) + (↑y : ℂ) * Complex.I) = Complex.I * (↑y : ℂ) := by
      push_cast; ring
    rw [h_iy_eq]
    exact modularLambdaH_pure_imag_real hy_pos
  -- Express Im λ(w) via the integral.
  have h_lam_w_im_eq : (modularLambdaH w).im =
      (∫ t in (0 : ℝ)..x, deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I)).im := by
    have h_ftc_im : (modularLambdaH ((↑x : ℂ) + (↑y : ℂ) * Complex.I)).im -
        (modularLambdaH ((↑(0 : ℝ) : ℂ) + (↑y : ℂ) * Complex.I)).im =
        (∫ t in (0 : ℝ)..x, deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I)).im := by
      rw [← Complex.sub_im, ← h_ftc]
    have h_w_eq_im : (modularLambdaH w).im =
        (modularLambdaH ((↑x : ℂ) + (↑y : ℂ) * Complex.I)).im := by
      rw [← hw_eq]
    rw [h_w_eq_im, ← h_ftc_im, h_lam_iy_im, sub_zero]
  -- Commute Im with the integral.
  have h_im_commute :
      (∫ t in (0 : ℝ)..x, deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I)).im =
      ∫ t in (0 : ℝ)..x,
        (deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I)).im :=
    (Complex.imCLM.intervalIntegral_comp_comm h_int_integrable).symm
  -- Integrand ≥ 0 by helper.
  have h_integrand_nonneg : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      0 ≤ (deriv modularLambdaH ((↑t : ℂ) + (↑y : ℂ) * Complex.I)).im := by
    intro t ht
    apply modularLambdaH_deriv_im_nonneg_on_left_edge
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      rcases (Set.mem_uIcc.mp ht) with ⟨h1, _⟩ | ⟨h1, _⟩
      · linarith
      · linarith [hx_pos]
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      rcases (Set.mem_uIcc.mp ht) with ⟨_, h2⟩ | ⟨_, h2⟩
      · linarith
      · linarith [hx_lt]
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add]
      exact hw_im_ge
  -- Integral of nonneg function is nonneg.
  rw [h_lam_w_im_eq, h_im_commute]
  -- Use intervalIntegral.integral_nonneg.
  have hx_le : (0 : ℝ) ≤ x := le_of_lt hx_pos
  apply intervalIntegral.integral_nonneg hx_le
  intro t ht
  apply h_integrand_nonneg
  rcases ht with ⟨h1, h2⟩
  exact Set.mem_uIcc.mpr (Or.inl ⟨h1, h2⟩)

/-- **Strip right edge: `Im λ ≥ 0` on `{Re ∈ (7/8, 1), Im ≥ 1}`.**

Reduces to the left edge via the T-shift identity
`λ(τ + 1) = λ(τ)/(λ(τ) − 1)` and the conjugation symmetry
`λ(−conj τ) = conj(λ τ)`.
Concretely: for `w` with `w.re ∈ (7/8, 1)`, define
`w_left := (1 − w.re) + i·w.im`, which has `Re w_left ∈ (0, 1/8)` and
`Im w_left = w.im ≥ 1`. The chain
`λ(w_left) = λ(−conj(w − 1)) = conj(λ(w − 1))`
combined with the T-shift `λ(w) = λ(w − 1)/(λ(w − 1) − 1)` gives
`λ(w) = conj(λ w_left)/(conj(λ w_left) − 1)`.
A direct computation yields
`Im λ(w) = (Im λ(w_left)) / |λ(w_left) − 1|²`,
which is nonneg since `Im λ(w_left) ≥ 0` (left edge) and
`λ(w_left) ≠ 1` on `ℍ`. -/
theorem modularLambdaH_im_nonneg_strip_right_edge (w : ℂ)
    (hw_re_gt : 7 / 8 < w.re) (hw_re_lt : w.re < 1) (hw_im_ge : 1 ≤ w.im) :
    0 ≤ (modularLambdaH w).im := by
  -- Build w_left := (1 - w.re) + i · w.im.
  set w_left : ℂ := ⟨1 - w.re, w.im⟩ with hw_left_def
  have hw_left_re : w_left.re = 1 - w.re := rfl
  have hw_left_im : w_left.im = w.im := rfl
  have hw_left_re_pos : 0 < w_left.re := by rw [hw_left_re]; linarith
  have hw_left_re_lt : w_left.re < 1 / 8 := by rw [hw_left_re]; linarith
  have hw_left_im_ge : 1 ≤ w_left.im := by rw [hw_left_im]; exact hw_im_ge
  have hw_left_im_pos : 0 < w_left.im := lt_of_lt_of_le one_pos hw_left_im_ge
  -- Apply left edge.
  have h_left_im : 0 ≤ (modularLambdaH w_left).im :=
    modularLambdaH_im_nonneg_strip_left_edge w_left hw_left_re_pos hw_left_re_lt
      hw_left_im_ge
  -- σ := w - 1, with Im σ = w.im ≥ 1 > 0.
  have hσ_im_pos : 0 < (w - 1).im := by
    rw [Complex.sub_im, Complex.one_im, sub_zero]; linarith
  -- Show -conj(w - 1) = w_left.
  have h_neg_conj_eq : -(starRingEnd ℂ (w - 1)) = w_left := by
    apply Complex.ext
    · simp only [Complex.neg_re, Complex.conj_re, Complex.sub_re, Complex.one_re,
        hw_left_re]
      ring
    · simp only [Complex.neg_im, Complex.conj_im, Complex.sub_im, Complex.one_im,
        sub_zero, neg_neg, hw_left_im]
  -- Conjugation symmetry: λ(-conj(w-1)) = conj(λ(w-1)).
  have h_conj_sym :
      modularLambdaH (-(starRingEnd ℂ (w - 1))) =
        starRingEnd ℂ (modularLambdaH (w - 1)) :=
    modularLambdaH_conj_symmetry hσ_im_pos
  -- So λ(w_left) = conj(λ(w-1)), hence λ(w-1) = conj(λ(w_left)).
  rw [h_neg_conj_eq] at h_conj_sym
  have h_lam_w_sub_1 :
      modularLambdaH (w - 1) = starRingEnd ℂ (modularLambdaH w_left) := by
    have h := congrArg (starRingEnd ℂ) h_conj_sym
    rw [Complex.conj_conj] at h
    exact h.symm
  -- T-shift: λ(w) = λ((w-1) + 1) = λ(w-1)/(λ(w-1) - 1).
  have h_w_eq : w = (w - 1) + 1 := by ring
  have h_lam_w :
      modularLambdaH w = modularLambdaH (w - 1) / (modularLambdaH (w - 1) - 1) := by
    conv_lhs => rw [h_w_eq]
    exact modularLambdaH_add_one_eq_div_sub_one hσ_im_pos
  -- Substitute to get λ(w) in terms of conj(λ(w_left)).
  rw [h_lam_w, h_lam_w_sub_1]
  set α := modularLambdaH w_left with hα_def
  -- α - 1 ≠ 0 (since λ ≠ 1 on ℍ).
  have hα_minus_one_ne : α - 1 ≠ 0 :=
    sub_ne_zero.mpr (modularLambdaH_ne_one hw_left_im_pos)
  -- Im(conj α / (conj α - 1)) = α.im / |α - 1|²: use conj-div, then div_im.
  have h_conj_div :
      starRingEnd ℂ α / (starRingEnd ℂ α - 1) =
        starRingEnd ℂ (α / (α - 1)) := by
    rw [map_div₀, map_sub, map_one]
  rw [h_conj_div]
  -- Goal: 0 ≤ (conj(α/(α-1))).im. Im(conj z) = -Im z.
  rw [Complex.conj_im]
  -- Goal: 0 ≤ -(α/(α-1)).im.
  rw [neg_nonneg]
  -- Compute (α/(α - 1)).im ≤ 0 using `Complex.div_im` and `← sub_div`.
  rw [Complex.div_im]
  have h_normSq_pos : 0 < Complex.normSq (α - 1) :=
    Complex.normSq_pos.mpr hα_minus_one_ne
  -- Simplify (α - 1).re and (α - 1).im.
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
  -- Combine the two division terms.
  rw [← sub_div]
  -- Numerator algebraic identity.
  have h_num_eq : α.im * (α.re - 1) - α.re * α.im = -α.im := by ring
  rw [h_num_eq]
  -- Goal: -α.im / Complex.normSq (α - 1) ≤ 0.
  rw [neg_div, neg_nonpos]
  exact div_nonneg h_left_im h_normSq_pos.le

end NoWanderingDomains
