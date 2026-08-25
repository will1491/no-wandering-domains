/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.ModularCoveringMap.DegreeArgument

/-! # Winding number one and injectivity of `λ`

The image curve `λ ∘ ∂F_Y` winds exactly once around `w`: the contour integral equals
`2πi`, the argument-principle index is `1`, and two distinct zeros would force a count
`≥ 2`. This yields existence and uniqueness of the `λ`-preimage in `F°`, injectivity of
`λ` on `F°`, on the three boundary arcs (ranges `(0, 1)`, `(−∞, 0)`, `(1, ∞)` and
monotonicity), and on the closed `F`; the upper branch of Pillar 4 follows, together
with the local multiplicity theorem: a nonconstant analytic map with vanishing
derivative is locally at least two-to-one.
-/

namespace NoWanderingDomains
open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-! ## The winding number of the image curve -/

/-- **Topological-winding result: image-curve contour integral equals 2πi.**
For `w ∈ ℍ` with a `λ`-preimage `τ₀ ∈ F°` located inside the truncated
region (above the bottom edge, below the top edge, outside the excised
arc-ball), and valid F_Y parameters satisfying the cusp-excision bounds
`δ ≤ 1/4` and `√(1/4 − δ²) < R₀`, with `λ ≠ w` on each boundary piece:
the contour integral of `(z − w)⁻¹` along the image curve
`λ ∘ F_Y_boundary_parameterization δ Y R₀` over `[0, 6]` equals exactly
`2πi`.

The hypothesis set is the minimal one making the statement true:

* Without `hR₀_lo`, the region F_Y reaches into the cusp at `1/2`,
  where the Γ(2)-orbit of `τ₀` clusters just above the bottom edge,
  making the winding integer exceed `1`.
* Without the preimage-location data (`hτ₀_im_lo`, `hτ₀_im_hi`,
  `hτ₀_arc`), `w` may have no preimage in F_Y at all (e.g. when the
  unique `F°`-preimage lies below the bottom edge `Im τ = δ`), making
  the winding integer `0`.
* By `F_Y_point_in_gamma2_semicircle_exterior`, the arc bound places
  the interior of F_Y inside `F°`, so the zeros of `λ − w` in F_Y are
  exactly its `F°`-preimages there — `τ₀` is one of them (simple,
  since `λ' ≠ 0` on `{Im λ > 0}`), and the winding-1 claim is
  equivalent to `τ₀` being the only one.

Proof route: by `image_curve_lambda_F_Y_homotopic_to_circle` the image
curve is continuously homotopic to a parameterized CCW circle around
`w` with angular speed `π/3`. Applying
`_pathContourIntegral_eq_circle_via_homotopy` equates the two contour
integrals. The circle integral computes directly via chain rule:
`d/dt(circleMap w ε (t π/3)) = (π/3) · ε · exp(I(t π/3)) · I`, so the
integrand `(circleMap - w)⁻¹ · deriv = (ε exp(I t π/3))⁻¹ ·
(π ε I / 3) · exp(I t π/3) = I π / 3` is constant, giving
`∫₀⁶ I π / 3 dt = 2πI`. -/
theorem modularLambdaH_F_Y_image_curve_pathContourIntegral_eq_two_pi_I
    {w : ℂ} (hw : 0 < w.im) {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (_hδ_le : δ ≤ 1 / 4) (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0)
    (τ₀ : ℂ) (hτ₀_in : τ₀ ∈ Gamma2FundamentalDomainInterior)
    (hτ₀_eq : modularLambdaH τ₀ = w)
    (hτ₀_im_lo : δ < τ₀.im) (hτ₀_im_hi : τ₀.im < Y)
    (hτ₀_arc : R₀ < ‖τ₀ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖) :
    Complex.pathContourIntegral
      (fun t => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
      0 6 (fun z => (z - w)⁻¹) = 2 * Real.pi * Complex.I := by
  -- Extract the homotopy from image_curve_lambda_F_Y_homotopic_to_circle —
  -- now exposing the 1D log lift `L` and the explicit log-space form of `H`.
  obtain ⟨ε, L, H, hε_pos, hL_cont, hL_exp, hH_form, hH_cont, hH_0, hH_1, hH_avoid⟩ :=
    image_curve_lambda_F_Y_homotopic_to_circle hw hδ hδY hR₀_pos hR₀_lt h_δR_lt_Y
      hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
  -- Architectural setup for `hH_closed`:
  -- (1) The F_Y boundary curve closes at the corners: `γ(0) = γ(6) = δ·i`.
  -- (2) Hence the log lift `L` satisfies `exp(L 0) = exp(L 6)`, so by
  --     `winding_lift_integer_coeff` there is `K : ℤ` with
  --     `L 6 − L 0 = K · 2πi` (the topological winding integer).
  -- (3) For the explicit `H s t = w + exp((1−s)·L t + s·t·π/3·i)`,
  --     `H s 0 = H s 6` reduces algebraically to the integer-valuedness of
  --     the affine real map `s ↦ K + s·(1 − K)` on `[0, 1]`.
  -- (4) `K_eq_one_of_affine_int_valued_on_unit_interval` then forces `K = 1`,
  --     and `H_explicit_closed_of_K_eq_one` recovers `hH_closed`.
  -- The remaining input — the affine integer-valuedness on `[0, 1]` — is the
  -- deep topological fact equivalent to `hH_closed`; it is proved below via
  -- the degree-argument bootstrap.
  have hγ_closed : F_Y_boundary_parameterization δ Y R₀ 0 =
      F_Y_boundary_parameterization δ Y R₀ 6 := by
    unfold F_Y_boundary_parameterization
    have h0_le_1 : (0 : ℝ) ≤ 1 := by norm_num
    have h6_not_le_1 : ¬((6 : ℝ) ≤ 1) := by norm_num
    have h6_not_le_2 : ¬((6 : ℝ) ≤ 2) := by norm_num
    have h6_not_le_3 : ¬((6 : ℝ) ≤ 3) := by norm_num
    have h6_not_le_4 : ¬((6 : ℝ) ≤ 4) := by norm_num
    have h6_not_le_5 : ¬((6 : ℝ) ≤ 5) := by norm_num
    have h6_le_6 : (6 : ℝ) ≤ 6 := by norm_num
    rw [if_pos h0_le_1, if_neg h6_not_le_1, if_neg h6_not_le_2,
        if_neg h6_not_le_3, if_neg h6_not_le_4, if_neg h6_not_le_5, if_pos h6_le_6]
    push_cast; ring
  have hL_lift_closed : Complex.exp (L 0) = Complex.exp (L 6) := by
    have h0 : Complex.exp (L 0) =
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ 0) - w :=
      hL_exp 0 ⟨by norm_num, by norm_num⟩
    have h6 : Complex.exp (L 6) =
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ 6) - w :=
      hL_exp 6 ⟨by norm_num, by norm_num⟩
    rw [h0, h6, hγ_closed]
  obtain ⟨K, hK_eq⟩ := winding_lift_integer_coeff L hL_lift_closed
  -- Deep topological fact: the affine real map `s ↦ K + s·(1 − K)` is
  -- integer-valued at every `s ∈ [0, 1]` — equivalent (via
  -- `K_eq_one_of_affine_int_valued_on_unit_interval`) to the winding
  -- integer `K` being `1`. The hypothesis set is exactly what makes
  -- this true: by `F_Y_point_in_gamma2_semicircle_exterior` (using
  -- `hR₀_lo`), the interior of F_Y lies in `F°`, so `K` equals the
  -- number of `F°`-preimages of `w` inside F_Y counted with
  -- multiplicity; `τ₀` is one such preimage (`hτ₀_im_lo`/`hτ₀_im_hi`/
  -- `hτ₀_arc` place it inside, and it is a simple zero since `λ' ≠ 0`
  -- on `{Im λ > 0}`). `K = 1` is therefore equivalent to `τ₀` being
  -- the unique `F°`-preimage of `w` in F_Y — provable either by the
  -- direct boundary-tracking argument (total argument variation of
  -- `λ − w` along the six near-real boundary pieces equals `2π`) or
  -- by the Γ(2) orbit-uniqueness property of the fundamental domain.
  -- Proved here by the degree argument: `K` equals the divisor sum `N` of
  -- `λ − w` on the truncated region (FTC + AP chain), and `N = 1` since
  -- `τ₀` is its unique simple zero there (degree-argument bootstrap
  -- `modularLambdaH_F_interior_preimage_unique` / `_deriv_ne_zero`).
  have h_tau_int_valued : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∃ n : ℤ, (K : ℝ) + s * (1 - K) = n := by
    -- (a) The image curve avoids zero on `[0, 6]`.
    have hγ_ne : ∀ t ∈ Set.Icc (0 : ℝ) 6,
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w ≠ 0 :=
      F_Y_image_curve_ne_zero hR₀_pos hR₀_lt hδY.le
        hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
    -- (b) FTC along the log lift: the contour integral is `L 6 − L 0`.
    have h_ftc := pathContourIntegral_inv_eq_log_lift_diff_F_Y_image_curve
      hδ hδY hR₀_pos hR₀_lt hγ_ne L hL_cont hL_exp
    -- (c) Bridge: six-term boundary expression = path contour integral.
    have h_lhs := modularLambdaH_F_Y_image_curve_LHS_eq_pathContourIntegral
      hδ hδY hR₀_pos hR₀_lt h_δR_lt_Y
      hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
    -- (d) Argument principle: normalized expression = divisor sum `N`.
    have h_div := modularLambdaH_F_Y_AP_integral_eq_divisor_sum
      hδ hδY hR₀_pos hR₀_lt h_δR_lt_Y
      hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
    -- (e) Combine (b)–(d) with `hK_eq`: `(K : ℂ) = (N : ℂ)`.
    rw [h_lhs, h_ftc, hK_eq] at h_div
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have h_cancel : (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ((K : ℂ) * (2 * Real.pi * Complex.I)) = (K : ℂ) := by
      rw [mul_comm ((K : ℂ)) (2 * Real.pi * Complex.I), ← mul_assoc,
        inv_mul_cancel₀ hpi, one_mul]
    rw [h_cancel] at h_div
    -- Coordinates of the excised-ball center.
    have he_re : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).re = 1 / 2 := by
      rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      have h_half_re : ((1 : ℂ) / 2).re = 1 / 2 := by rw [Complex.div_re]; simp
      rw [h_half_re]; ring
    have he_im : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im = δ := by
      rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
      rw [h_half_im]; ring
    obtain ⟨hτ₀_im_pos, hτ₀_re_lo, hτ₀_re_hi, hτ₀_semi⟩ := id hτ₀_in
    have hτ₀_zero : (fun τ => modularLambdaH τ - w) τ₀ = 0 := by
      change modularLambdaH τ₀ - w = 0
      rw [hτ₀_eq, sub_self]
    -- (f) Lower bound: `τ₀` is a zero in the region, so `1 ≤ N`.
    have h_one_le : 1 ≤ (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat := by
      have hτ₀_mem : τ₀ ∈ (Set.Icc (0 : ℝ) 1 ×ℂ
          Set.Icc (((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im) Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ := by
        rw [he_im]
        refine ⟨?_, ?_⟩
        · rw [Complex.mem_reProdIm]
          exact ⟨Set.mem_Icc.mpr ⟨hτ₀_re_lo.le, hτ₀_re_hi.le⟩,
            Set.mem_Icc.mpr ⟨hτ₀_im_lo.le, hτ₀_im_hi.le⟩⟩
        · simp only [Metric.mem_ball, Complex.dist_eq, not_lt]
          exact hτ₀_arc.le
      have key := Complex.one_le_divisor_sum_toNat_of_zero_on_rectMinusUpperHalfDisk
        (fun τ => modularLambdaH τ - w) 0 1 Y ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
        (by norm_num) hR₀_pos
        (by rw [he_re]; linarith)
        (by rw [he_re]; linarith)
        (by rw [he_im]; exact h_δR_lt_Y)
        (by rw [he_im]; exact modularLambdaH_F_Y_analytic w hδ hδY hR₀_pos)
        (by
          rw [he_im]
          intro h0
          have h0' : modularLambdaH (((0 : ℝ) : ℂ) + (δ : ℂ) * Complex.I) - w = 0 := h0
          rw [Complex.ofReal_zero] at h0'
          exact hg_left δ (Set.mem_Icc.mpr ⟨le_refl δ, hδY.le⟩) h0')
        hτ₀_mem hτ₀_zero
      rw [he_im] at key
      exact key
    -- (g) Upper bound: `τ₀` is the unique simple zero, so `N ≤ 1`.
    have h_unique_δ : ∀ z ∈ (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀,
        (fun τ => modularLambdaH τ - w) z = 0 → z = τ₀ := by
      intro z hz h_gz0
      have h_gz : modularLambdaH z - w = 0 := h_gz0
      have h_lam_eq : modularLambdaH z = w := sub_eq_zero.mp h_gz
      obtain ⟨hz_box, hz_ball⟩ := hz
      rw [Complex.mem_reProdIm] at hz_box
      obtain ⟨hz_re, hz_im⟩ := hz_box
      have hz_dist : R₀ ≤ ‖z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖ := by
        simp only [Metric.mem_ball, Complex.dist_eq, not_lt] at hz_ball
        exact hz_ball
      -- Left edge excluded.
      by_cases h_re_0 : z.re = 0
      · exfalso
        have h_z_eq : z = (0 : ℂ) + (z.im : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, h_re_0]
          · simp [Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
        exact hg_left z.im hz_im (by rw [← h_z_eq]; exact h_gz)
      -- Right edge excluded.
      by_cases h_re_1 : z.re = 1
      · exfalso
        have h_z_eq : z = (1 : ℂ) + (z.im : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, h_re_1]
          · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
        exact hg_right z.im hz_im (by rw [← h_z_eq]; exact h_gz)
      -- Top edge excluded.
      by_cases h_im_Y : z.im = Y
      · exfalso
        have h_z_eq : z = (z.re : ℂ) + (Y : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
          · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, h_im_Y]
        exact hg_top z.re hz_re (by rw [← h_z_eq]; exact h_gz)
      -- Bottom edge excluded.
      by_cases h_im_δ : z.im = δ
      · exfalso
        have h_z_sub : z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)
            = ((z.re - 1 / 2 : ℝ) : ℂ) := by
          apply Complex.ext
          · rw [Complex.sub_re, he_re, Complex.ofReal_re]
          · rw [Complex.sub_im, he_im, Complex.ofReal_im, h_im_δ, sub_self]
        rw [h_z_sub, Complex.norm_real, Real.norm_eq_abs] at hz_dist
        have h_z_eq : z = (z.re : ℂ) + (δ : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
          · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, h_im_δ]
        rcases abs_cases (z.re - 1 / 2) with ⟨h_abs_eq, _⟩ | ⟨h_abs_eq, _⟩
        · rw [h_abs_eq] at hz_dist
          exact hg_bot_right z.re (Set.mem_Icc.mpr ⟨by linarith, hz_re.2⟩)
            (by rw [← h_z_eq]; exact h_gz)
        · rw [h_abs_eq] at hz_dist
          exact hg_bot_left z.re (Set.mem_Icc.mpr ⟨hz_re.1, by linarith⟩)
            (by rw [← h_z_eq]; exact h_gz)
      -- Arc excluded, or interior point.
      rcases eq_or_lt_of_le hz_dist with h_norm_eq | h_arc_gt
      · exfalso
        have h_polar := Complex.norm_mul_exp_arg_mul_I
          (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I))
        have hζ_im_nonneg : 0 ≤ (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).im := by
          rw [Complex.sub_im, he_im]
          linarith [hz_im.1]
        have hθ_nonneg : 0 ≤ (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg :=
          Complex.arg_nonneg_iff.mpr hζ_im_nonneg
        have hθ_le_pi : (z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg ≤ Real.pi :=
          Complex.arg_le_pi _
        have h_z_eq : z = _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
            ((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg) := by
          have h_cm : _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
              ((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg) =
              ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) + (R₀ : ℂ) *
                Complex.exp (((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg : ℂ) *
                  Complex.I) := rfl
          rw [h_cm, h_norm_eq, h_polar]
          ring
        exact hg_arc ((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg)
          (Set.mem_Icc.mpr ⟨hθ_nonneg, hθ_le_pi⟩) (by rw [← h_z_eq]; exact h_gz)
      · -- Strictly interior: `z ∈ F°`, so `z = τ₀` by the bootstrap uniqueness.
        have h_im_gt : δ < z.im := lt_of_le_of_ne hz_im.1 (Ne.symm h_im_δ)
        have h_re_gt : 0 < z.re := lt_of_le_of_ne hz_re.1 (Ne.symm h_re_0)
        have h_re_lt : z.re < 1 := lt_of_le_of_ne hz_re.2 h_re_1
        have h_semi : 1 < ‖2 * z - 1‖ :=
          F_Y_point_in_gamma2_semicircle_exterior hδ hR₀_lo h_im_gt h_arc_gt
        exact modularLambdaH_F_interior_preimage_unique hw
          ⟨lt_trans hδ h_im_gt, h_re_gt, h_re_lt, h_semi⟩ hτ₀_in h_lam_eq hτ₀_eq
    have h_simple : (fun τ => modularLambdaH τ - w) τ₀ = 0 →
        deriv (fun τ => modularLambdaH τ - w) τ₀ ≠ 0 := by
      intro _
      have h_d : deriv (fun τ => modularLambdaH τ - w) τ₀
          = deriv modularLambdaH τ₀ := deriv_sub_const w
      rw [h_d]
      exact modularLambdaH_F_interior_preimage_deriv_ne_zero hw hτ₀_in hτ₀_eq
    have h_le_one : (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat ≤ 1 := by
      have key := Complex.divisor_sum_toNat_le_one_of_unique_simple_zero_on_rectMinusUpperHalfDisk
        (fun τ => modularLambdaH τ - w) 0 1 Y ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
        (by rw [he_im]; exact modularLambdaH_F_Y_analytic w hδ hδY hR₀_pos)
        (by rw [he_im]; exact h_unique_δ)
        h_simple
      rw [he_im] at key
      exact key
    -- (h) `N = 1`, hence `K = 1`, hence the affine map is constantly `1`.
    have hN_eq : (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat = 1 :=
      le_antisymm h_le_one h_one_le
    rw [hN_eq] at h_div
    have hK_one : K = 1 := by exact_mod_cast h_div
    exact fun s _ => ⟨1, by rw [hK_one]; push_cast; ring⟩
  have hK_one : K = 1 :=
    K_eq_one_of_affine_int_valued_on_unit_interval h_tau_int_valued
  have hL_eq : L 6 - L 0 = (2 * Real.pi * Complex.I : ℂ) := by
    rw [hK_eq, hK_one]; push_cast; ring
  have hH_explicit_closed := H_explicit_closed_of_K_eq_one w L hL_eq
  have hH_closed : ∀ s ∈ Set.Icc (0 : ℝ) 1, H s 0 = H s 6 := by
    intro s hs
    rw [hH_form s 0, hH_form s 6]
    exact hH_explicit_closed s hs
  -- Apply continuous-homotopy invariance to equate image and circle integrals.
  rw [modularLambdaH_F_Y_image_curve_pathContourIntegral_eq_circle_via_homotopy
    hδ hδY hR₀_pos hR₀_lt ε hε_pos H hH_cont hH_0 hH_1 hH_avoid hH_closed]
  -- Compute the circle integral directly.
  unfold Complex.pathContourIntegral
  -- Goal: ∫ t in 0..6, (circleMap w ε (t * π / 3) - w)⁻¹ * deriv (.) t = 2πi.
  have h_integrand : ∀ t : ℝ,
      (fun z => (z - w)⁻¹) (_root_.circleMap w ε (t * Real.pi / 3)) *
        deriv (fun t : ℝ => _root_.circleMap w ε (t * Real.pi / 3)) t =
      Complex.I * (Real.pi / 3) := by
    intro t
    -- Compute deriv via chain rule.
    have h_inner : HasDerivAt (fun s : ℝ => s * Real.pi / 3) (Real.pi / 3) t := by
      have h1 : HasDerivAt (fun y : ℝ => id y * Real.pi) (1 * Real.pi) t :=
        (hasDerivAt_id t).mul_const Real.pi
      simp only [id, one_mul] at h1
      exact h1.div_const 3
    have h_outer := hasDerivAt_circleMap w ε (t * Real.pi / 3)
    have h_comp := h_outer.scomp t h_inner
    have h_deriv_eq : deriv (fun t : ℝ => _root_.circleMap w ε (t * Real.pi / 3)) t =
        (Real.pi / 3 : ℝ) • (_root_.circleMap 0 ε (t * Real.pi / 3) * Complex.I) :=
      h_comp.deriv
    rw [h_deriv_eq]
    -- circleMap w ε θ - w = circleMap 0 ε θ.
    have h_sub : _root_.circleMap w ε (t * Real.pi / 3) - w =
        _root_.circleMap 0 ε (t * Real.pi / 3) := by
      unfold _root_.circleMap; ring
    change (_root_.circleMap w ε (t * Real.pi / 3) - w)⁻¹ * _ = _
    rw [h_sub]
    -- circleMap 0 ε θ ≠ 0.
    have h_circ_ne : _root_.circleMap 0 ε (t * Real.pi / 3) ≠ 0 := by
      unfold _root_.circleMap
      simp only [zero_add]
      refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
      exact_mod_cast ne_of_gt hε_pos
    -- Simplify.
    rw [Complex.real_smul]
    field_simp
    push_cast
    ring
  -- Use the constant integrand to evaluate the integral.
  rw [intervalIntegral.integral_congr (g := fun _ => Complex.I * (Real.pi / 3))
    (fun t _ => h_integrand t)]
  rw [intervalIntegral.integral_const]
  change ((6 - 0 : ℝ) : ℂ) * (Complex.I * (Real.pi / 3)) = 2 * Real.pi * Complex.I
  push_cast
  ring

/-- **Image curve winding index is 1.**
The load-bearing topological/geometric core sub-helper for B2. For any
`n : ℕ` satisfying the AP-derived identity, `n` equals the winding
index of the image curve `λ ∘ ∂F_Y` around `w`, which is `1`.

Proof: bridge the 6-term boundary integral expression to
`pathContourIntegral (λ ∘ F_Y_boundary_parameterization) 0 6 ((z − w)⁻¹)`
via `_LHS_eq_pathContourIntegral`, then apply
`_pathContourIntegral_eq_two_pi_I` (the topological winding result).
Combining with the AP-derived hypothesis `(2πi)⁻¹ · expression = (n : ℂ)`
gives `(n : ℂ) = 1`, hence `n = 1`. -/
theorem modularLambdaH_F_Y_image_curve_winding_index_eq_one
    {w : ℂ} (hw : 0 < w.im) {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (hδ_le : δ ≤ 1 / 4) (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0)
    (τ₀ : ℂ) (hτ₀_in : τ₀ ∈ Gamma2FundamentalDomainInterior)
    (hτ₀_eq : modularLambdaH τ₀ = w)
    (hτ₀_im_lo : δ < τ₀.im) (hτ₀_im_hi : τ₀.im < Y)
    (hτ₀_arc : R₀ < ‖τ₀ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖)
    {n : ℕ}
    (hn : (2 * Real.pi * Complex.I)⁻¹ * ((∫ x in (0 : ℝ)..(1 / 2 - R₀),
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      (∫ x in (1 / 2 + R₀ : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ x in (0 : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) -
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ θ in (0 : ℝ)..Real.pi,
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
        (modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = (n : ℂ)) :
    n = 1 := by
  -- Bridge LHS to pathContourIntegral via the chain-rule sub-helper.
  have h_bridge := modularLambdaH_F_Y_image_curve_LHS_eq_pathContourIntegral
    hδ hδY hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
  -- Topological winding via homotopy + circle.
  have h_topo := modularLambdaH_F_Y_image_curve_pathContourIntegral_eq_two_pi_I
    hw hδ hδY hR₀_pos hR₀_lt hδ_le hR₀_lo h_δR_lt_Y
    hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
    τ₀ hτ₀_in hτ₀_eq hτ₀_im_lo hτ₀_im_hi hτ₀_arc
  -- Combine: (2πi)⁻¹ · 2πi = 1 = (n : ℂ).
  rw [h_bridge, h_topo] at hn
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  rw [inv_mul_cancel₀ hpi] at hn
  exact_mod_cast hn.symm

/-- **F_Y boundary integral of `λ'/(λ − w)` equals `2πi`.**

For `w ∈ ℍ` and valid F_Y parameters with `λ ≠ w` on each of the six
boundary pieces, the closed-boundary integral of `λ'/(λ − w)` around
`∂F_Y` (CCW, region on the left) equals exactly `2πi`. Equivalently,
the image curve `λ ∘ ∂F_Y` has winding number `1` around `w`.

Proof: combine `modularLambdaH_F_Y_AP_integral_eq_nat_form` (returning
`(2πi)⁻¹ · integral = n` for some `n : ℕ`) with
`modularLambdaH_F_Y_image_curve_winding_index_eq_one` (`n = 1`), then
multiply by `2πi`. -/
theorem modularLambdaH_F_Y_boundary_integral_eq_two_pi_I
    {w : ℂ} (hw : 0 < w.im) {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (hδ_le : δ ≤ 1 / 4) (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0)
    (τ₀ : ℂ) (hτ₀_in : τ₀ ∈ Gamma2FundamentalDomainInterior)
    (hτ₀_eq : modularLambdaH τ₀ = w)
    (hτ₀_im_lo : δ < τ₀.im) (hτ₀_im_hi : τ₀.im < Y)
    (hτ₀_arc : R₀ < ‖τ₀ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖) :
    (∫ x in (0 : ℝ)..(1 / 2 - R₀),
      deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
      (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
    (∫ x in (1 / 2 + R₀ : ℝ)..1,
      deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
      (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
    Complex.I * (∫ y in (δ : ℝ)..Y,
      deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
      (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) -
    (∫ x in (0 : ℝ)..1,
      deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
      (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) -
    Complex.I * (∫ y in (δ : ℝ)..Y,
      deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
      (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) -
    (∫ θ in (0 : ℝ)..Real.pi,
      deriv modularLambdaH
        (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
      (modularLambdaH
        (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
    2 * Real.pi * Complex.I := by
  obtain ⟨n, hn⟩ := modularLambdaH_F_Y_AP_integral_eq_nat_form hδ hδY hR₀_pos hR₀_lt
    h_δR_lt_Y hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
  have h_n_one : n = 1 :=
    modularLambdaH_F_Y_image_curve_winding_index_eq_one hw hδ hδY hR₀_pos hR₀_lt
    hδ_le hR₀_lo h_δR_lt_Y hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
    τ₀ hτ₀_in hτ₀_eq hτ₀_im_lo hτ₀_im_hi hτ₀_arc hn
  rw [h_n_one, Nat.cast_one] at hn
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  have h_mul : (2 * Real.pi * Complex.I) * ((2 * Real.pi * Complex.I)⁻¹ * _) =
      (2 * Real.pi * Complex.I) * 1 := congrArg _ hn
  rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul, mul_one] at h_mul
  exact h_mul

/-- **Two distinct zeros force AP count `≥ 2`.**
A refinement of the F_Y argument principle exposing the natural-number
count as the divisor sum. For `g(τ) = λ(τ) − w` with two distinct zeros
`τ₁, τ₂` in the **open** F_Y interior, the natural number `n` returned
by the AP existential (`(2πi)⁻¹ · integral = (n : ℂ)`) satisfies `n ≥ 2`.

Combined with `_image_curve_winding_index_eq_one` (giving `n = 1` from
`(2πi)⁻¹ · integral = (n : ℂ)`), this yields a contradiction, proving
uniqueness of preimages
in F_Y interior.

Proof strategy: factor `g = r · h` via `MeromorphicOn.extract_zeros_poles`
on the F_Y region. The natural number `n` from `cIntegralLogDeriv_isNat`
equals the divisor sum of `g` over `F_Y` (this requires either reaching
inside the AP theorem's existing proof or restating with the explicit
divisor sum). Each zero `τᵢ` contributes at least `1` to the divisor
sum (multiplicity ≥ 1 since `g τᵢ = 0` and `g` analytic, distinct from
the analyticOrder-defined `0` value). Two distinct zeros ⟹ sum ≥ 2. -/
theorem modularLambdaH_F_Y_AP_count_ge_two_of_two_distinct_zeros
    {w : ℂ} {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (h_δR_lt_Y : δ + R₀ < Y)
    (hg_bot_left : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0)
    {τ₁ τ₂ : ℂ}
    (hτ₁_re_lo : 0 < τ₁.re) (hτ₁_re_hi : τ₁.re < 1)
    (hτ₁_im_lo : δ < τ₁.im) (hτ₁_im_hi : τ₁.im < Y)
    (hτ₁_outside : R₀ < ‖τ₁ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖)
    (hτ₂_re_lo : 0 < τ₂.re) (hτ₂_re_hi : τ₂.re < 1)
    (hτ₂_im_lo : δ < τ₂.im) (hτ₂_im_hi : τ₂.im < Y)
    (hτ₂_outside : R₀ < ‖τ₂ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖)
    (hτ_ne : τ₁ ≠ τ₂)
    (hlam_τ₁ : modularLambdaH τ₁ = w) (hlam_τ₂ : modularLambdaH τ₂ = w)
    {n : ℕ}
    (hn : (2 * Real.pi * Complex.I)⁻¹ * ((∫ x in (0 : ℝ)..(1 / 2 - R₀),
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      (∫ x in (1 / 2 + R₀ : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w)) +
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ x in (0 : ℝ)..1,
        deriv modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) /
        (modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w)) -
      Complex.I * (∫ y in (δ : ℝ)..Y,
        deriv modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) /
        (modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w)) -
      (∫ θ in (0 : ℝ)..Real.pi,
        deriv modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) /
        (modularLambdaH
          (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = (n : ℂ)) :
    2 ≤ n := by
  -- (1) Argument principle: the normalized boundary expression equals the
  -- divisor sum `N` of `λ − w` on the truncated region.
  have h_div := modularLambdaH_F_Y_AP_integral_eq_divisor_sum
    hδ hδY hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
  -- (2) Identify `n` with the divisor sum.
  have h_cast := hn.symm.trans h_div
  have h_n_eq : n = (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat := by
    exact_mod_cast h_cast
  -- Coordinates of the excised-ball center.
  have he_re : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).re = 1 / 2 := by
    rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_re : ((1 : ℂ) / 2).re = 1 / 2 := by rw [Complex.div_re]; simp
    rw [h_half_re]; ring
  have he_im : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im = δ := by
    rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have h_half_im : ((1 : ℂ) / 2).im = 0 := by rw [Complex.div_im]; simp
    rw [h_half_im]; ring
  -- (3) `τ₁`, `τ₂` are two distinct zeros of `λ − w` in the region.
  have hτ₁_zero : (fun τ => modularLambdaH τ - w) τ₁ = 0 := by
    change modularLambdaH τ₁ - w = 0
    rw [hlam_τ₁, sub_self]
  have hτ₂_zero : (fun τ => modularLambdaH τ - w) τ₂ = 0 := by
    change modularLambdaH τ₂ - w = 0
    rw [hlam_τ₂, sub_self]
  have hτ₁_mem : τ₁ ∈ (Set.Icc (0 : ℝ) 1 ×ℂ
      Set.Icc (((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im) Y) \
      Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ := by
    rw [he_im]
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      exact ⟨Set.mem_Icc.mpr ⟨hτ₁_re_lo.le, hτ₁_re_hi.le⟩,
        Set.mem_Icc.mpr ⟨hτ₁_im_lo.le, hτ₁_im_hi.le⟩⟩
    · simp only [Metric.mem_ball, Complex.dist_eq, not_lt]
      exact hτ₁_outside.le
  have hτ₂_mem : τ₂ ∈ (Set.Icc (0 : ℝ) 1 ×ℂ
      Set.Icc (((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im) Y) \
      Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ := by
    rw [he_im]
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      exact ⟨Set.mem_Icc.mpr ⟨hτ₂_re_lo.le, hτ₂_re_hi.le⟩,
        Set.mem_Icc.mpr ⟨hτ₂_im_lo.le, hτ₂_im_hi.le⟩⟩
    · simp only [Metric.mem_ball, Complex.dist_eq, not_lt]
      exact hτ₂_outside.le
  -- (4) Two distinct zeros force the divisor sum to be at least 2.
  have key := Complex.two_le_divisor_sum_toNat_of_two_zeros_on_rectMinusUpperHalfDisk
    (fun τ => modularLambdaH τ - w) 0 1 Y ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
    (by norm_num) hR₀_pos
    (by rw [he_re]; linarith)
    (by rw [he_re]; linarith)
    (by rw [he_im]; exact h_δR_lt_Y)
    (by rw [he_im]; exact modularLambdaH_F_Y_analytic w hδ hδY hR₀_pos)
    (by
      rw [he_im]
      intro h0
      have h0' : modularLambdaH (((0 : ℝ) : ℂ) + (δ : ℂ) * Complex.I) - w = 0 := h0
      rw [Complex.ofReal_zero] at h0'
      exact hg_left δ (Set.mem_Icc.mpr ⟨le_refl δ, hδY.le⟩) h0')
    hτ_ne hτ₁_mem hτ₁_zero hτ₂_mem hτ₂_zero
  rw [he_im] at key
  omega

/-! ## Existence, uniqueness, and injectivity of `λ` on `F` -/

/-- **Existence and uniqueness of `λ`-preimage in `F^o`.** For each
`w` with `Im w > 0`, there is a unique `τ ∈ F^o` with `λ(τ) = w`.

Existence: directly from `modularLambdaH_image_F_supset_upperHalf`
(the surjectivity half of Step D).

Uniqueness: via `modularLambdaH_F_interior_preimage_unique` (the
degree-argument bootstrap), which transports the F_Y zero count of
`g(τ) := λ(τ) − w` along a `w`-segment avoided by the boundary image
to the deep-cusp reference value, where the fibre is a provably
unique simple point. -/
theorem modularLambdaH_existsUnique_in_F_interior_of_im_pos
    {w : ℂ} (hw : 0 < w.im) :
    ∃! τ : ℂ, τ ∈ Gamma2FundamentalDomainInterior ∧ modularLambdaH τ = w := by
  obtain ⟨τ_ex, hτ_ex_in, hτ_ex_eq⟩ :=
    modularLambdaH_image_F_supset_upperHalf hw
  refine ⟨τ_ex, ⟨hτ_ex_in, hτ_ex_eq⟩, ?_⟩
  rintro τ' ⟨hτ'_in, hτ'_eq⟩
  exact modularLambdaH_F_interior_preimage_unique hw hτ'_in hτ_ex_in hτ'_eq hτ_ex_eq

/-- **Injectivity of `λ` on the open interior `F^o`.** Combined
with the surjectivity from Step D
`modularLambdaH_image_fundamentalDomainInterior`, this yields the
biholomorphism `λ : F^o ≅ {Im w > 0}`. Direct consequence of
`modularLambdaH_existsUnique_in_F_interior_of_im_pos`: the unique
preimage of `λ τ₁` in `F^o` is both `τ₁` and `τ₂`. -/
theorem modularLambdaH_injOn_F_interior :
    Set.InjOn modularLambdaH Gamma2FundamentalDomainInterior := by
  intro τ₁ h₁ τ₂ h₂ h_eq
  have hw : 0 < (modularLambdaH τ₁).im := modularLambdaH_F_im_pos τ₁ h₁
  obtain ⟨τ, _, hτ_unique⟩ :=
    modularLambdaH_existsUnique_in_F_interior_of_im_pos hw
  have h_τ₁ : τ₁ = τ := hτ_unique τ₁ ⟨h₁, rfl⟩
  have h_τ₂ : τ₂ = τ := hτ_unique τ₂ ⟨h₂, h_eq.symm⟩
  rw [h_τ₁, h_τ₂]

/-! ### Boundary-arc analysis: ranges and monotonicity -/

/-- **`T`-translation in `λ`-form.** `λ(τ + 1) = λ(τ)/(λ(τ) − 1)`
on `ℍ`: combine `modularLambdaH_T_smul` (`λ(τ+1) = −θ₂⁴/θ₄⁴`) with
the Jacobi identity `θ₂⁴ + θ₄⁴ = θ₃⁴` and nonvanishing of `θ₃, θ₄`. -/
theorem modularLambdaH_T_smul_div {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH (τ + 1) = modularLambdaH τ / (modularLambdaH τ - 1) := by
  have h3 : theta3 τ ≠ 0 := theta3_ne_zero hτ
  have h4 : theta4 τ ≠ 0 := theta4_ne_zero hτ
  have h3' : (theta3 τ) ^ 4 ≠ 0 := pow_ne_zero 4 h3
  have h4' : (theta4 τ) ^ 4 ≠ 0 := pow_ne_zero 4 h4
  have hjac : theta2 τ ^ 4 + theta4 τ ^ 4 = theta3 τ ^ 4 := jacobi_identity hτ
  have hne : modularLambdaH τ - 1 ≠ 0 := sub_ne_zero.mpr (modularLambdaH_ne_one hτ)
  rw [modularLambdaH_T_smul, eq_div_iff hne]
  unfold modularLambdaH
  field_simp
  linear_combination (-(theta2 τ ^ 4)) * hjac

/-- **Range of `λ` on the imaginary axis.** For `y > 0`, the real
value `λ(iy)` lies strictly between `0` and `1`: strict antitonicity
(`modularLambdaH_iy_strictAntitone`) pinches it between the cusp
limits `λ(iy) → 1` as `y → 0⁺` and `λ(iy) → 0` as `y → ∞`
(`modularLambdaH_iy_tendsto_one_atZeroPos`,
`modularLambdaH_iy_tendsto_zero_atTop`). -/
theorem modularLambdaH_iy_re_mem_Ioo {y : ℝ} (hy : 0 < y) :
    (modularLambdaH (Complex.I * y)).re ∈ Set.Ioo (0 : ℝ) 1 := by
  -- real-part limits
  have h0 : Filter.Tendsto (fun t : ℝ => (modularLambdaH (Complex.I * (t : ℂ))).re)
      Filter.atTop (nhds (0 : ℝ)) := by
    have := (Complex.continuous_re.tendsto (0 : ℂ)).comp modularLambdaH_iy_tendsto_zero_atTop
    simpa using! this
  have h1 : Filter.Tendsto (fun t : ℝ => (modularLambdaH (Complex.I * (t : ℂ))).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 : ℝ)) := by
    have := (Complex.continuous_re.tendsto (1 : ℂ)).comp modularLambdaH_iy_tendsto_one_atZeroPos
    simpa using! this
  -- membership facts
  have hy_mem : y ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr hy
  have hy2_mem : y / 2 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have h2y_mem : 2 * y ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  -- strict antitonicity comparisons
  have hab : (modularLambdaH (Complex.I * (y : ℂ))).re
      < (modularLambdaH (Complex.I * ((y / 2 : ℝ) : ℂ))).re :=
    modularLambdaH_iy_strictAntitone hy2_mem hy_mem (by linarith)
  have hca : (modularLambdaH (Complex.I * ((2 * y : ℝ) : ℂ))).re
      < (modularLambdaH (Complex.I * (y : ℂ))).re :=
    modularLambdaH_iy_strictAntitone hy_mem h2y_mem (by linarith)
  -- upper bound: L (y/2) ≤ 1
  have hb1 : (modularLambdaH (Complex.I * ((y / 2 : ℝ) : ℂ))).re ≤ 1 := by
    apply ge_of_tendsto h1
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < y / 2 by linarith)] with t ht
    exact (modularLambdaH_iy_strictAntitone (Set.mem_Ioi.mpr ht.1) hy2_mem ht.2).le
  -- lower bound: 0 ≤ L (2*y)
  have hc0 : (0 : ℝ) ≤ (modularLambdaH (Complex.I * ((2 * y : ℝ) : ℂ))).re := by
    apply le_of_tendsto h0
    filter_upwards [Filter.eventually_gt_atTop (2 * y)] with t ht
    exact (modularLambdaH_iy_strictAntitone h2y_mem
      (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < t)) ht).le
  refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
  · linarith [hc0, hca]
  · linarith [hab, hb1]

/-- **Range of `λ` on the right edge.** For `y > 0`,
`λ(1 + iy) = u/(u − 1)` with `u = λ(iy) ∈ (0, 1)` real, so the value
is real and strictly negative. -/
theorem modularLambdaH_one_add_iy_re_neg {y : ℝ} (hy : 0 < y) :
    (modularLambdaH (1 + Complex.I * y)).re < 0 := by
  have h_im_pos : 0 < (Complex.I * (y : ℂ)).im := by
    have : (Complex.I * (y : ℂ)).im = y := by
      simp [Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [this]; exact hy
  have hu_im : (modularLambdaH (Complex.I * (y : ℂ))).im = 0 := modularLambdaH_pure_imag_real hy
  have hu_mem := modularLambdaH_iy_re_mem_Ioo hy
  obtain ⟨hpos, hlt⟩ := Set.mem_Ioo.mp hu_mem
  have h_div := modularLambdaH_T_smul_div h_im_pos
  have hcomm : (1 : ℂ) + Complex.I * (y : ℂ) = Complex.I * (y : ℂ) + 1 := by ring
  rw [hcomm, h_div]
  set u := modularLambdaH (Complex.I * (y : ℂ)) with hu_def
  have hu_eq : u = (u.re : ℂ) := by
    apply Complex.ext <;> simp [hu_im]
  have hden : (u.re : ℝ) - 1 < 0 := by linarith
  rw [hu_eq]
  rw [show (u.re : ℂ) - 1 = ((u.re - 1 : ℝ) : ℂ) from by push_cast; ring]
  rw [← Complex.ofReal_div, Complex.ofReal_re]
  exact div_neg_of_pos_of_neg hpos hden

/-- **Injectivity of `λ` along the right edge.** The Möbius map
`u ↦ u/(u − 1)` is injective away from `u = 1`, and `y ↦ λ(iy)` is
injective by strict antitonicity of the real part together with
`λ(iy)` being real. -/
theorem modularLambdaH_one_add_iy_injOn {y₁ y₂ : ℝ}
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂)
    (h_eq : modularLambdaH (1 + Complex.I * y₁) =
      modularLambdaH (1 + Complex.I * y₂)) :
    y₁ = y₂ := by
  have him1 : 0 < (Complex.I * (y₁ : ℂ)).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
    exact hy₁
  have him2 : 0 < (Complex.I * (y₂ : ℂ)).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
    exact hy₂
  have e1 : (1 + Complex.I * (y₁ : ℂ)) = Complex.I * (y₁ : ℂ) + 1 := by ring
  have e2 : (1 + Complex.I * (y₂ : ℂ)) = Complex.I * (y₂ : ℂ) + 1 := by ring
  rw [e1, e2, modularLambdaH_T_smul_div him1, modularLambdaH_T_smul_div him2] at h_eq
  have hne1 : modularLambdaH (Complex.I * (y₁ : ℂ)) - 1 ≠ 0 :=
    sub_ne_zero.mpr (modularLambdaH_ne_one him1)
  have hne2 : modularLambdaH (Complex.I * (y₂ : ℂ)) - 1 ≠ 0 :=
    sub_ne_zero.mpr (modularLambdaH_ne_one him2)
  rw [div_eq_div_iff hne1 hne2] at h_eq
  have hu_eq : modularLambdaH (Complex.I * (y₁ : ℂ)) =
      modularLambdaH (Complex.I * (y₂ : ℂ)) := by
    linear_combination -h_eq
  have hre : (modularLambdaH (Complex.I * (y₁ : ℂ))).re =
      (modularLambdaH (Complex.I * (y₂ : ℂ))).re :=
    congrArg Complex.re hu_eq
  exact modularLambdaH_iy_strictAntitone.injOn (Set.mem_Ioi.mpr hy₁) (Set.mem_Ioi.mpr hy₂) hre

/-- **Semicircle reduction to the right edge.** For `τ` on the open
upper semicircle `‖2τ − 1‖ = 1`, `Im τ > 0`, the circle equation
gives `|τ|² = Re τ > 0`, hence `−1/τ = −1 + i·(Im τ/Re τ)`; combining
`modularLambdaH_add_S_smul_eq_one` with the `2`-periodicity of `λ`
yields `λ(τ) = 1 − λ(1 + i·(Im τ/Re τ))`. -/
theorem modularLambdaH_semicircle_eq {τ : ℂ} (hτ_im : 0 < τ.im)
    (h_circle : ‖2 * τ - 1‖ = 1) :
    modularLambdaH τ =
      1 - modularLambdaH (1 + Complex.I * (τ.im / τ.re)) := by
  -- Step a: normSq τ = τ.re
  have h_nsq : Complex.normSq (2 * τ - 1) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h_circle]; norm_num
  have h_re : Complex.normSq τ = τ.re := by
    have hns := h_nsq
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat] at hns
    simp only [Complex.normSq_apply]
    linear_combination hns / 4
  -- Step b: τ.re > 0
  have hτ_ne : τ ≠ 0 := by
    intro h; rw [h] at hτ_im; simp at hτ_im
  have hre_pos : 0 < τ.re := by
    rw [← h_re]; exact Complex.normSq_pos.mpr hτ_ne
  have hre_ne : τ.re ≠ 0 := ne_of_gt hre_pos
  -- Step c: -1/τ = -1 + I * (τ.im / τ.re)
  have hq : ((τ.im : ℂ) / (τ.re : ℂ)) = ((τ.im / τ.re : ℝ) : ℂ) := by push_cast; ring
  have h_inv : -1 / τ = -1 + Complex.I * (τ.im / τ.re) := by
    rw [hq]
    apply Complex.ext
    · simp only [Complex.div_re, Complex.add_re, Complex.neg_re, Complex.one_re,
        Complex.neg_im, Complex.one_im, neg_zero, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
        sub_zero, add_zero, h_re]
      field_simp
      ring
    · simp only [Complex.div_im, Complex.add_im, Complex.neg_re, Complex.one_re,
        Complex.neg_im, Complex.one_im, neg_zero, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
        zero_add, h_re]
      ring
  -- Step d: λ τ = 1 - λ(-1/τ)
  have h_S := modularLambdaH_add_S_smul_eq_one hτ_im
  rw [h_inv] at h_S
  -- Step e: periodicity moves -1 to 1
  have h_per := modularLambdaH_periodic (-1 + Complex.I * (τ.im / τ.re))
  have harg : (-1 + Complex.I * (τ.im / τ.re)) + ((2 : ℝ) : ℂ)
      = 1 + Complex.I * (τ.im / τ.re) := by push_cast; ring
  rw [harg] at h_per
  rw [← h_per] at h_S
  linear_combination h_S

/-- **Range of `λ` on the semicircle.** For `τ` on the open upper
semicircle, `λ(τ) = 1 − λ(1 + i·s)` with `λ(1 + i·s)` real negative,
so `Re λ(τ) > 1`. -/
theorem modularLambdaH_semicircle_re_gt_one {τ : ℂ} (hτ_im : 0 < τ.im)
    (h_circle : ‖2 * τ - 1‖ = 1) :
    1 < (modularLambdaH τ).re := by
  have h_nsq : Complex.normSq (2 * τ - 1) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h_circle]; norm_num
  have h_re : Complex.normSq τ = τ.re := by
    have hns := h_nsq
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat] at hns
    simp only [Complex.normSq_apply]
    linear_combination hns / 4
  have hτ_ne : τ ≠ 0 := by
    intro h; rw [h] at hτ_im; simp at hτ_im
  have hre_pos : 0 < τ.re := by
    rw [← h_re]; exact Complex.normSq_pos.mpr hτ_ne
  have hs_pos : 0 < τ.im / τ.re := div_pos hτ_im hre_pos
  have hbridge : ((τ.im : ℂ) / (τ.re : ℂ)) = ((τ.im / τ.re : ℝ) : ℂ) := by push_cast; ring
  rw [modularLambdaH_semicircle_eq hτ_im h_circle, Complex.sub_re, Complex.one_re, hbridge]
  have hneg := modularLambdaH_one_add_iy_re_neg hs_pos
  linarith

/-- **Semicircle points are determined by the slope `Im τ/Re τ`.**
On `‖2τ − 1‖ = 1`, `Im τ > 0`, the circle equation `|τ|² = Re τ`
forces `Re τ = 1/(1 + s²)` and `Im τ = s/(1 + s²)` for
`s = Im τ/Re τ`, so equal slopes give equal points. -/
theorem semicircle_eq_of_im_div_re_eq {τ₁ τ₂ : ℂ}
    (h₁_im : 0 < τ₁.im) (h₁_circle : ‖2 * τ₁ - 1‖ = 1)
    (h₂_im : 0 < τ₂.im) (h₂_circle : ‖2 * τ₂ - 1‖ = 1)
    (h_ratio : τ₁.im / τ₁.re = τ₂.im / τ₂.re) :
    τ₁ = τ₂ := by
  -- normSq facts and re positivity for both points
  have h1_re : Complex.normSq τ₁ = τ₁.re := by
    have hns : Complex.normSq (2 * τ₁ - 1) = 1 := by
      rw [Complex.normSq_eq_norm_sq, h₁_circle]; norm_num
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat] at hns
    simp only [Complex.normSq_apply]
    linear_combination hns / 4
  have h2_re : Complex.normSq τ₂ = τ₂.re := by
    have hns : Complex.normSq (2 * τ₂ - 1) = 1 := by
      rw [Complex.normSq_eq_norm_sq, h₂_circle]; norm_num
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat] at hns
    simp only [Complex.normSq_apply]
    linear_combination hns / 4
  have h1ne : τ₁ ≠ 0 := by intro h; rw [h] at h₁_im; simp at h₁_im
  have h2ne : τ₂ ≠ 0 := by intro h; rw [h] at h₂_im; simp at h₂_im
  have h1re_pos : 0 < τ₁.re := by rw [← h1_re]; exact Complex.normSq_pos.mpr h1ne
  have h2re_pos : 0 < τ₂.re := by rw [← h2_re]; exact Complex.normSq_pos.mpr h2ne
  have h1re_ne : τ₁.re ≠ 0 := ne_of_gt h1re_pos
  have h2re_ne : τ₂.re ≠ 0 := ne_of_gt h2re_pos
  -- re² + im² = re from normSq
  have e1 : τ₁.re * τ₁.re + τ₁.im * τ₁.im = τ₁.re := by
    rw [← Complex.normSq_apply]; exact h1_re
  have e2 : τ₂.re * τ₂.re + τ₂.im * τ₂.im = τ₂.re := by
    rw [← Complex.normSq_apply]; exact h2_re
  -- common slope s, im = s * re
  set s := τ₁.im / τ₁.re with hs
  have him1 : τ₁.im = s * τ₁.re := by rw [hs]; field_simp
  have him2 : τ₂.im = s * τ₂.re := by rw [h_ratio]; field_simp
  -- re * (1 + s²) = 1
  have hf1 : τ₁.re * (1 + s ^ 2) = 1 := by
    have h := e1; rw [him1] at h
    have key : τ₁.re * (τ₁.re * (1 + s ^ 2)) = τ₁.re * 1 := by linear_combination h
    exact mul_left_cancel₀ h1re_ne key
  have hf2 : τ₂.re * (1 + s ^ 2) = 1 := by
    have h := e2; rw [him2] at h
    have key : τ₂.re * (τ₂.re * (1 + s ^ 2)) = τ₂.re * 1 := by linear_combination h
    exact mul_left_cancel₀ h2re_ne key
  have hsq_pos : 0 < 1 + s ^ 2 := by positivity
  have hre_eq : τ₁.re = τ₂.re :=
    mul_right_cancel₀ (ne_of_gt hsq_pos) (by rw [hf1, hf2])
  have him_eq : τ₁.im = τ₂.im := by rw [him1, him2, hre_eq]
  exact Complex.ext hre_eq him_eq

/-- **Injectivity of `λ` on the boundary `∂F`.** For two boundary
points `τ₁, τ₂ ∈ F \ F^o` with `λ(τ₁) = λ(τ₂)`, we have `τ₁ = τ₂`.
The proof case-splits on which of the three boundary arcs each `τᵢ`
lies on (left edge `Re τ = 0`, right edge `Re τ = 1`, upper
semicircle `‖2τ − 1‖ = 1`). Same arc ⟹ same point by strict
monotonicity (left edge: `modularLambdaH_iy_strictAntitone`;
right edge: `modularLambdaH_one_add_iy_injOn`; semicircle:
`modularLambdaH_semicircle_eq` + right-edge injectivity +
`semicircle_eq_of_im_div_re_eq`). Different arcs ⟹ the disjoint
ranges `(0, 1)`, `(−∞, 0)`, `(1, +∞)` (lemmas
`modularLambdaH_iy_re_mem_Ioo`, `modularLambdaH_one_add_iy_re_neg`,
`modularLambdaH_semicircle_re_gt_one`) contradict `λ`-equality. -/
theorem modularLambdaH_injOn_F_boundary
    {τ₁ τ₂ : ℂ}
    (h₁ : τ₁ ∈ Gamma2FundamentalDomain)
    (h₁_not_int : τ₁ ∉ Gamma2FundamentalDomainInterior)
    (h₂ : τ₂ ∈ Gamma2FundamentalDomain)
    (h₂_not_int : τ₂ ∉ Gamma2FundamentalDomainInterior)
    (h_eq : modularLambdaH τ₁ = modularLambdaH τ₂) :
    τ₁ = τ₂ := by
  obtain ⟨hτ₁_im, hτ₁_re_nn, hτ₁_re_le, hτ₁_semi⟩ := h₁
  obtain ⟨hτ₂_im, hτ₂_re_nn, hτ₂_re_le, hτ₂_semi⟩ := h₂
  -- Arc trichotomy for each point: at least one boundary equation holds.
  have h_arc1 : τ₁.re = 0 ∨ τ₁.re = 1 ∨ ‖2 * τ₁ - 1‖ = 1 := by
    by_contra h
    push Not at h
    obtain ⟨hne0, hne1, hnec⟩ := h
    exact h₁_not_int ⟨hτ₁_im, lt_of_le_of_ne hτ₁_re_nn (Ne.symm hne0),
      lt_of_le_of_ne hτ₁_re_le hne1, lt_of_le_of_ne hτ₁_semi (Ne.symm hnec)⟩
  have h_arc2 : τ₂.re = 0 ∨ τ₂.re = 1 ∨ ‖2 * τ₂ - 1‖ = 1 := by
    by_contra h
    push Not at h
    obtain ⟨hne0, hne1, hnec⟩ := h
    exact h₂_not_int ⟨hτ₂_im, lt_of_le_of_ne hτ₂_re_nn (Ne.symm hne0),
      lt_of_le_of_ne hτ₂_re_le hne1, lt_of_le_of_ne hτ₂_semi (Ne.symm hnec)⟩
  -- Real-part equality from λ-equality.
  have h_re_eq : (modularLambdaH τ₁).re = (modularLambdaH τ₂).re := by rw [h_eq]
  rcases h_arc1 with hre1 | hre1 | hcirc1
  · -- τ₁ on left edge (re = 0).
    have h_τ₁_eq : τ₁ = Complex.I * τ₁.im := by
      apply Complex.ext
      · simp [Complex.mul_re, Complex.I_re, Complex.I_im, hre1]
      · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
    have hL1 : (modularLambdaH τ₁).re ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [h_τ₁_eq]; exact modularLambdaH_iy_re_mem_Ioo hτ₁_im
    rcases h_arc2 with hre2 | hre2 | hcirc2
    · -- L-L: strict antitonicity.
      have h_τ₂_eq : τ₂ = Complex.I * τ₂.im := by
        apply Complex.ext
        · simp [Complex.mul_re, Complex.I_re, Complex.I_im, hre2]
        · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
      have key : (modularLambdaH (Complex.I * (τ₁.im : ℂ))).re =
          (modularLambdaH (Complex.I * (τ₂.im : ℂ))).re := by
        rw [← h_τ₁_eq, ← h_τ₂_eq, h_eq]
      have him_eq : τ₁.im = τ₂.im :=
        modularLambdaH_iy_strictAntitone.injOn (Set.mem_Ioi.mpr hτ₁_im)
          (Set.mem_Ioi.mpr hτ₂_im) key
      calc τ₁ = Complex.I * (τ₁.im : ℂ) := h_τ₁_eq
        _ = Complex.I * (τ₂.im : ℂ) := by rw [him_eq]
        _ = τ₂ := h_τ₂_eq.symm
    · -- L-R: cross, contradiction.
      exfalso
      have h_τ₂_eq : τ₂ = 1 + Complex.I * τ₂.im := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, hre2]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
      have hR2 : (modularLambdaH τ₂).re < 0 := by
        rw [h_τ₂_eq]; exact modularLambdaH_one_add_iy_re_neg hτ₂_im
      have := hL1.1
      linarith [h_re_eq]
    · -- L-C: cross, contradiction.
      exfalso
      have hC2 : 1 < (modularLambdaH τ₂).re :=
        modularLambdaH_semicircle_re_gt_one hτ₂_im hcirc2
      have := hL1.2
      linarith [h_re_eq]
  · -- τ₁ on right edge (re = 1).
    have h_τ₁_eq : τ₁ = 1 + Complex.I * τ₁.im := by
      apply Complex.ext
      · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, hre1]
      · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    have hR1 : (modularLambdaH τ₁).re < 0 := by
      rw [h_τ₁_eq]; exact modularLambdaH_one_add_iy_re_neg hτ₁_im
    rcases h_arc2 with hre2 | hre2 | hcirc2
    · -- R-L: cross, contradiction.
      exfalso
      have h_τ₂_eq : τ₂ = Complex.I * τ₂.im := by
        apply Complex.ext
        · simp [Complex.mul_re, Complex.I_re, Complex.I_im, hre2]
        · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
      have hL2 : (modularLambdaH τ₂).re ∈ Set.Ioo (0 : ℝ) 1 := by
        rw [h_τ₂_eq]; exact modularLambdaH_iy_re_mem_Ioo hτ₂_im
      have := hL2.1
      linarith [h_re_eq]
    · -- R-R: Möbius injectivity along the right edge.
      have h_τ₂_eq : τ₂ = 1 + Complex.I * τ₂.im := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, hre2]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
      have h_eq' : modularLambdaH (1 + Complex.I * (τ₁.im : ℂ)) =
          modularLambdaH (1 + Complex.I * (τ₂.im : ℂ)) := by
        rw [← h_τ₁_eq, ← h_τ₂_eq, h_eq]
      have him_eq : τ₁.im = τ₂.im :=
        modularLambdaH_one_add_iy_injOn hτ₁_im hτ₂_im h_eq'
      calc τ₁ = 1 + Complex.I * (τ₁.im : ℂ) := h_τ₁_eq
        _ = 1 + Complex.I * (τ₂.im : ℂ) := by rw [him_eq]
        _ = τ₂ := h_τ₂_eq.symm
    · -- R-C: cross, contradiction.
      exfalso
      have hC2 : 1 < (modularLambdaH τ₂).re :=
        modularLambdaH_semicircle_re_gt_one hτ₂_im hcirc2
      linarith [h_re_eq]
  · -- τ₁ on semicircle.
    have hC1 : 1 < (modularLambdaH τ₁).re :=
      modularLambdaH_semicircle_re_gt_one hτ₁_im hcirc1
    rcases h_arc2 with hre2 | hre2 | hcirc2
    · -- C-L: cross, contradiction.
      exfalso
      have h_τ₂_eq : τ₂ = Complex.I * τ₂.im := by
        apply Complex.ext
        · simp [Complex.mul_re, Complex.I_re, Complex.I_im, hre2]
        · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
      have hL2 : (modularLambdaH τ₂).re ∈ Set.Ioo (0 : ℝ) 1 := by
        rw [h_τ₂_eq]; exact modularLambdaH_iy_re_mem_Ioo hτ₂_im
      have := hL2.2
      linarith [h_re_eq]
    · -- C-R: cross, contradiction.
      exfalso
      have h_τ₂_eq : τ₂ = 1 + Complex.I * τ₂.im := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, hre2]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
      have hR2 : (modularLambdaH τ₂).re < 0 := by
        rw [h_τ₂_eq]; exact modularLambdaH_one_add_iy_re_neg hτ₂_im
      linarith [h_re_eq]
    · -- C-C: semicircle reduction + right-edge injectivity + slope determinacy.
      have hτ₁_ne : τ₁ ≠ 0 := fun h => by simp [h] at hτ₁_im
      have hτ₂_ne : τ₂ ≠ 0 := fun h => by simp [h] at hτ₂_im
      have hre₁_pos : 0 < τ₁.re := by
        have h_normSq : Complex.normSq τ₁ = τ₁.re :=
          Gamma2FundamentalDomain_semicircle_normSq_eq_re hcirc1
        rw [← h_normSq]; exact Complex.normSq_pos.mpr hτ₁_ne
      have hre₂_pos : 0 < τ₂.re := by
        have h_normSq : Complex.normSq τ₂ = τ₂.re :=
          Gamma2FundamentalDomain_semicircle_normSq_eq_re hcirc2
        rw [← h_normSq]; exact Complex.normSq_pos.mpr hτ₂_ne
      have hs₁_pos : 0 < τ₁.im / τ₁.re := div_pos hτ₁_im hre₁_pos
      have hs₂_pos : 0 < τ₂.im / τ₂.re := div_pos hτ₂_im hre₂_pos
      rw [modularLambdaH_semicircle_eq hτ₁_im hcirc1,
          modularLambdaH_semicircle_eq hτ₂_im hcirc2] at h_eq
      have h_eq' := sub_right_inj.mp h_eq
      rw [← Complex.ofReal_div, ← Complex.ofReal_div] at h_eq'
      have him_eq : τ₁.im / τ₁.re = τ₂.im / τ₂.re :=
        modularLambdaH_one_add_iy_injOn hs₁_pos hs₂_pos h_eq'
      exact semicircle_eq_of_im_div_re_eq hτ₁_im hcirc1 hτ₂_im hcirc2 him_eq

/-- **Injectivity of `λ` on the closed half-fundamental domain `F`.**
Case split on `F^o` vs `∂F` for each of `τ₁`, `τ₂`:

* **Both `F^o`**: `modularLambdaH_injOn_F_interior`.
* **Both `∂F`**: `modularLambdaH_injOn_F_boundary`.
* **Mixed (one `F^o`, one `∂F`)**: `Im λ > 0` on `F^o` (Step A,
  `modularLambdaH_F_im_pos`) versus `Im λ = 0` on `∂F` (from one of
  the three boundary real-value lemmas
  `modularLambdaH_pure_imag_real` / `_one_add_imag_real` /
  `_semicircle_real`) — contradicts `λ`-equality. -/
theorem modularLambdaH_injOn_F_closed :
    Set.InjOn modularLambdaH Gamma2FundamentalDomain := by
  intro τ₁ h₁ τ₂ h₂ h_eq
  obtain ⟨hτ₁_im, hτ₁_re_nn, hτ₁_re_le, hτ₁_semi⟩ := h₁
  obtain ⟨hτ₂_im, hτ₂_re_nn, hτ₂_re_le, hτ₂_semi⟩ := h₂
  -- Helper: `Im(λ τ) = 0` for `τ ∈ ∂F`.
  have h_im_zero_on_boundary : ∀ {τ : ℂ}, τ ∈ Gamma2FundamentalDomain →
      τ ∉ Gamma2FundamentalDomainInterior → (modularLambdaH τ).im = 0 := by
    intro τ hτ_F hτ_not_int
    obtain ⟨hτ_im, hτ_re_nn, hτ_re_le, hτ_semi⟩ := hτ_F
    by_cases h_re_zero : τ.re = 0
    · have h_τ_eq : τ = Complex.I * τ.im := by
        apply Complex.ext
        · simp [Complex.mul_re, Complex.I_re, Complex.I_im, h_re_zero]
        · simp [Complex.mul_im, Complex.I_re, Complex.I_im]
      rw [h_τ_eq]; exact modularLambdaH_pure_imag_real hτ_im
    · by_cases h_re_one : τ.re = 1
      · have h_τ_eq : τ = 1 + Complex.I * τ.im := by
          apply Complex.ext
          · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, h_re_one]
          · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
        rw [h_τ_eq]; exact modularLambdaH_one_add_imag_real hτ_im
      · by_cases h_semi_eq : ‖2 * τ - 1‖ = 1
        · exact modularLambdaH_semicircle_real hτ_im h_semi_eq
        · -- All three boundary inequalities strict ⟹ τ ∈ F^o, contradicts.
          exfalso
          apply hτ_not_int
          refine ⟨hτ_im, ?_, ?_, ?_⟩
          · rcases lt_or_eq_of_le hτ_re_nn with h | h
            · exact h
            · exact absurd h.symm h_re_zero
          · rcases lt_or_eq_of_le hτ_re_le with h | h
            · exact h
            · exact absurd h h_re_one
          · rcases lt_or_eq_of_le hτ_semi with h | h
            · exact h
            · exact absurd h.symm h_semi_eq
  by_cases h₁_int : τ₁ ∈ Gamma2FundamentalDomainInterior
  · by_cases h₂_int : τ₂ ∈ Gamma2FundamentalDomainInterior
    · -- Both interior.
      exact modularLambdaH_injOn_F_interior h₁_int h₂_int h_eq
    · -- τ₁ interior, τ₂ boundary: contradicts via Im λ.
      exfalso
      have h_im_1 : 0 < (modularLambdaH τ₁).im := modularLambdaH_F_im_pos _ h₁_int
      have h_im_2 : (modularLambdaH τ₂).im = 0 :=
        h_im_zero_on_boundary ⟨hτ₂_im, hτ₂_re_nn, hτ₂_re_le, hτ₂_semi⟩ h₂_int
      rw [h_eq] at h_im_1
      linarith
  · by_cases h₂_int : τ₂ ∈ Gamma2FundamentalDomainInterior
    · -- τ₁ boundary, τ₂ interior: contradicts via Im λ.
      exfalso
      have h_im_2 : 0 < (modularLambdaH τ₂).im := modularLambdaH_F_im_pos _ h₂_int
      have h_im_1 : (modularLambdaH τ₁).im = 0 :=
        h_im_zero_on_boundary ⟨hτ₁_im, hτ₁_re_nn, hτ₁_re_le, hτ₁_semi⟩ h₁_int
      rw [← h_eq] at h_im_2
      linarith
    · -- Both boundary.
      exact modularLambdaH_injOn_F_boundary
        ⟨hτ₁_im, hτ₁_re_nn, hτ₁_re_le, hτ₁_semi⟩ h₁_int
        ⟨hτ₂_im, hτ₂_re_nn, hτ₂_re_le, hτ₂_semi⟩ h₂_int h_eq

/-! ## Pillar 4, upper branch: `Im λ > 0` -/

/-- **Injectivity of `λ` on `F` modulo `Γ(2)`.** For
`τ₁, τ₂ ∈ F ⊂ ℍ` with `λ(τ₁) = λ(τ₂)`, there is `γ ∈ Γ(2)` taking
`τ₁` to `τ₂`. Direct consequence of `modularLambdaH_injOn_F_closed`:
`λ` injective on `F` gives `τ₁ = τ₂` in `ℂ`, hence `τ₁ = τ₂` in `ℍ`
(by `UpperHalfPlane.ext`), and `γ = 1 ∈ Γ(2)` does the job. -/
theorem modularLambdaH_injOn_F_mod_gamma2
    {τ₁ τ₂ : UpperHalfPlane}
    (h₁ : (τ₁ : ℂ) ∈ Gamma2FundamentalDomain)
    (h₂ : (τ₂ : ℂ) ∈ Gamma2FundamentalDomain)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  have h_eq_c : (τ₁ : ℂ) = (τ₂ : ℂ) :=
    modularLambdaH_injOn_F_closed h₁ h₂ h_eq
  have h_eq_h : τ₁ = τ₂ := UpperHalfPlane.ext h_eq_c
  refine ⟨1, (CongruenceSubgroup.Gamma 2).one_mem, ?_⟩
  rw [h_eq_h]; exact one_smul _ _

/-- **Pillar-4 upper branch.** For `τ₁, τ₂ ∈ ℍ` with
`Im(λ τ₁) > 0` and `λ(τ₁) = λ(τ₂)`, there is `γ ∈ Γ(2)` taking
`τ₁` to `τ₂`. Reduce both `τ₁`, `τ₂` to `F` via
`gamma2_orbit_meets_F_when_im_lambda_pos`, apply
`modularLambdaH_injOn_F_mod_gamma2`, transport via the
`Γ(2)`-action. -/
theorem gamma2_lambda_eq_implies_orbit_when_im_lambda_pos
    {τ₁ τ₂ : UpperHalfPlane}
    (h_im_pos : 0 < (modularLambdaH (τ₁ : ℂ)).im)
    (h_eq : modularLambdaH (τ₁ : ℂ) = modularLambdaH (τ₂ : ℂ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ₁ = τ₂ := by
  have h_im_pos_2 : 0 < (modularLambdaH (τ₂ : ℂ)).im := by rw [← h_eq]; exact h_im_pos
  obtain ⟨γ₁, hγ₁_in, hγ₁τ₁_F⟩ :=
    gamma2_orbit_meets_F_when_im_lambda_pos τ₁ h_im_pos
  obtain ⟨γ₂, hγ₂_in, hγ₂τ₂_F⟩ :=
    gamma2_orbit_meets_F_when_im_lambda_pos τ₂ h_im_pos_2
  have h_eq_γ : modularLambdaH ((γ₁ • τ₁ : UpperHalfPlane) : ℂ)
      = modularLambdaH ((γ₂ • τ₂ : UpperHalfPlane) : ℂ) := by
    rw [modularLambdaH_gamma2_invariant γ₁ hγ₁_in τ₁,
      modularLambdaH_gamma2_invariant γ₂ hγ₂_in τ₂]
    exact h_eq
  obtain ⟨γ, hγ_in, hγ_eq⟩ :=
    modularLambdaH_injOn_F_mod_gamma2 hγ₁τ₁_F hγ₂τ₂_F h_eq_γ
  refine ⟨γ₂⁻¹ * γ * γ₁, ?_, ?_⟩
  · exact (CongruenceSubgroup.Gamma 2).mul_mem
      ((CongruenceSubgroup.Gamma 2).mul_mem
        ((CongruenceSubgroup.Gamma 2).inv_mem hγ₂_in) hγ_in) hγ₁_in
  · rw [mul_smul, mul_smul, hγ_eq, ← mul_smul, inv_mul_cancel, one_smul]

/-! ## Local multiplicity of analytic maps -/

set_option maxHeartbeats 400000 in
-- Composes the multiplicity factorization with an analytic n-th root
-- (`Complex.log` + `Complex.exp`) and the inverse function theorem; the
-- combined elaboration pressure exceeds the default heartbeat limit.
/-- **Analytic local openness with multiplicity.** If `f : ℂ → ℂ`
is analytic at `z₀`, not eventually constant near `z₀`, and
`deriv f z₀ = 0`, then in any neighbourhood `U` of `z₀` and for any
value `w` sufficiently close (but unequal) to `f z₀`, there exist
two distinct points `z₁, z₂ ∈ U` with `f z₁ = f z₂ = w`. This is
the classical "open mapping with multiplicity ≥ 2" statement: the
factorization `f(z) - f(z₀) = (z - z₀)^n · g(z)` with `n ≥ 2`,
`g(z₀) ≠ 0`, combined with the existence of an analytic `n`-th root
of `g` near `z₀` (via `Complex.exp ∘ ((1/n) * Complex.log ∘ h)`),
yields `n` distinct preimages for each `w` in a small punctured
neighbourhood of `f(z₀)`. -/
theorem analyticAt_localOpen_with_multiplicity
    {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀)
    (h_nc : ¬ ∀ᶠ z in nhds z₀, f z = f z₀)
    (h_dz : deriv f z₀ = 0)
    (U : Set ℂ) (hU : U ∈ nhds z₀) :
    ∃ V ∈ nhds (f z₀), ∀ w ∈ V, w ≠ f z₀ →
      ∃ z₁ ∈ U, ∃ z₂ ∈ U, z₁ ≠ z₂ ∧ f z₁ = w ∧ f z₂ = w := by
  -- Abbreviate f₀(z) := f(z) - f(z₀). Analytic at z₀ with f₀(z₀) = 0.
  set f₀ : ℂ → ℂ := fun z => f z - f z₀ with hf₀_def
  have hf₀_at : AnalyticAt ℂ f₀ z₀ := hf.sub analyticAt_const
  -- Order of f₀ is not ⊤ (else f₀ ≡ 0 near z₀, i.e. f eventually constant).
  have h_order_ne_top : analyticOrderAt f₀ z₀ ≠ ⊤ := by
    intro h_top
    rw [analyticOrderAt_eq_top] at h_top
    apply h_nc
    filter_upwards [h_top] with z hz
    exact sub_eq_zero.mp hz
  -- Use analyticOrderAt_deriv_add_one to obtain n ≥ 2.
  have h_order_chain :
      analyticOrderAt (deriv f) z₀ + 1 = analyticOrderAt f₀ z₀ := by
    have h := hf.analyticOrderAt_deriv_add_one
    -- h : order(deriv f) + 1 = order (fun x_1 => f x_1 - f z₀) = order f₀.
    exact h
  -- deriv f is analytic at z₀ (from f analytic at z₀).
  have h_deriv_at : AnalyticAt ℂ (deriv f) z₀ := hf.deriv
  -- (deriv f)(z₀) = 0, and deriv f is analytic, so analyticOrderAt (deriv f) z₀ ≥ 1.
  -- Specifically: if order = 0, then (deriv f)(z₀) ≠ 0 by definition.
  have h_deriv_order_ge_one : 1 ≤ analyticOrderAt (deriv f) z₀ := by
    rw [Order.one_le_iff_ne_zero]
    intro h_eq
    rw [h_deriv_at.analyticOrderAt_eq_zero] at h_eq
    exact h_eq h_dz
  -- Hence order(f₀) ≥ 2.
  have h_order_f₀_ge_two : 2 ≤ analyticOrderAt f₀ z₀ := by
    rw [← h_order_chain]
    calc (2 : ℕ∞) = 1 + 1 := by rfl
      _ ≤ analyticOrderAt (deriv f) z₀ + 1 := by
        gcongr
  -- Convert order to natural number n.
  obtain ⟨n, hn_coe⟩ := ENat.ne_top_iff_exists.mp h_order_ne_top
  have hn_eq : analyticOrderAt f₀ z₀ = (n : ℕ∞) := hn_coe.symm
  have hn_ge_two : 2 ≤ n := by
    have : ((2 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by rw [← hn_eq]; exact_mod_cast h_order_f₀_ge_two
    exact_mod_cast this
  have hn_pos : 0 < n := by linarith
  have hn_ne_zero : n ≠ 0 := by linarith
  -- Get the factorization.
  obtain ⟨g, hg_at, hg_ne, hg_eq⟩ :=
    (hf₀_at.analyticOrderAt_eq_natCast).mp hn_eq
  -- hg_eq : ∀ᶠ z in nhds z₀, f₀ z = (z - z₀) ^ n • g z
  -- Define c := g z₀, and h(z) := g(z) / c.
  set c : ℂ := g z₀ with hc_def
  have hc_ne : c ≠ 0 := hg_ne
  set h : ℂ → ℂ := fun z => g z / c with hh_def
  have hh_at : AnalyticAt ℂ h z₀ := (hg_at.div_const : AnalyticAt ℂ (fun z => g z / c) z₀)
  have hh_z₀_one : h z₀ = 1 := by
    change g z₀ / c = 1
    exact div_self hc_ne
  have hh_in_slit : h z₀ ∈ Complex.slitPlane := by
    rw [hh_z₀_one]; exact Complex.one_mem_slitPlane
  -- Eventually h(z) ∈ slitPlane (since slitPlane is open + h continuous).
  have h_h_slit_evt : ∀ᶠ z in nhds z₀, h z ∈ Complex.slitPlane :=
    hh_at.continuousAt.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hh_in_slit)
  -- log analytic at h(z₀) = 1.
  have h_log_at : AnalyticAt ℂ Complex.log (h z₀) := by
    apply DifferentiableOn.analyticAt _ (Complex.isOpen_slitPlane.mem_nhds hh_in_slit)
    intro z hz
    exact (Complex.differentiableAt_log hz).differentiableWithinAt
  -- log ∘ h analytic at z₀.
  have h_log_h_at : AnalyticAt ℂ (Complex.log ∘ h) z₀ := h_log_at.comp hh_at
  -- Define ρ(z) := exp ((1/n) * log(h z)).
  set ρ : ℂ → ℂ := fun z => Complex.exp ((n : ℂ)⁻¹ * Complex.log (h z)) with hρ_def
  -- ρ analytic at z₀.
  have hρ_at : AnalyticAt ℂ ρ z₀ := by
    have h_mul : AnalyticAt ℂ (fun z => (n : ℂ)⁻¹ * Complex.log (h z)) z₀ :=
      (analyticAt_const).mul h_log_h_at
    exact h_mul.cexp
  -- ρ(z₀) = 1.
  have hρ_z₀ : ρ z₀ = 1 := by
    change Complex.exp ((n : ℂ)⁻¹ * Complex.log (h z₀)) = 1
    rw [hh_z₀_one, Complex.log_one, mul_zero, Complex.exp_zero]
  -- Eventually ρ(z)^n = h(z).
  have h_nC_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn_ne_zero
  have h_ρ_pow_eq : ∀ᶠ z in nhds z₀, ρ z ^ n = h z := by
    filter_upwards [h_h_slit_evt] with z hz_slit
    change Complex.exp ((n : ℂ)⁻¹ * Complex.log (h z)) ^ n = h z
    rw [← Complex.exp_nat_mul]
    have h_h_ne : h z ≠ 0 := Complex.slitPlane_ne_zero hz_slit
    have h_simp : (n : ℂ) * ((n : ℂ)⁻¹ * Complex.log (h z)) = Complex.log (h z) := by
      field_simp
    rw [h_simp]
    exact Complex.exp_log h_h_ne
  -- Define φ(z) := (z - z₀) · ρ(z).
  set φ : ℂ → ℂ := fun z => (z - z₀) * ρ z with hφ_def
  have hφ_at : AnalyticAt ℂ φ z₀ :=
    (analyticAt_id.sub analyticAt_const).mul hρ_at
  have hφ_z₀ : φ z₀ = 0 := by change (z₀ - z₀) * _ = 0; ring
  -- HasDerivAt φ 1 z₀.
  have hφ_hasDeriv : HasDerivAt φ 1 z₀ := by
    have h_a : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ := by
      simpa using (hasDerivAt_id z₀).sub_const z₀
    have h_b : HasDerivAt ρ (deriv ρ z₀) z₀ := hρ_at.differentiableAt.hasDerivAt
    have h_mul := h_a.mul h_b
    have h_simpl : (1 : ℂ) * ρ z₀ + (z₀ - z₀) * deriv ρ z₀ = 1 := by
      rw [hρ_z₀]; ring
    rw [← h_simpl]
    exact h_mul
  have hφ_deriv_eq : deriv φ z₀ = 1 := hφ_hasDeriv.deriv
  -- HasStrictDerivAt φ 1 z₀.
  have hφ_strict : HasStrictDerivAt φ 1 z₀ := by
    have := hφ_at.hasStrictDerivAt
    rw [hφ_deriv_eq] at this
    exact this
  -- Local inverse ψ.
  set ψ : ℂ → ℂ := hφ_strict.localInverse φ 1 z₀ one_ne_zero with hψ_def
  -- ψ(0) = z₀ via eventually_left_inverse at z₀.
  have hψ_0 : ψ 0 = z₀ := by
    have h_ev := hφ_strict.eventually_left_inverse one_ne_zero
    have h_at_z₀ : ψ (φ z₀) = z₀ := h_ev.self_of_nhds
    rwa [hφ_z₀] at h_at_z₀
  -- ψ continuous at 0 via HasStrictFDerivAt.localInverse_continuousAt.
  have hψ_cont : ContinuousAt ψ 0 := by
    have h_cont_at : ContinuousAt ψ (φ z₀) :=
      (hφ_strict.hasStrictFDerivAt_equiv one_ne_zero).localInverse_continuousAt
    rwa [hφ_z₀] at h_cont_at
  -- Eventually φ(ψ y) = y near 0 (right inverse).
  have h_right_inv : ∀ᶠ y in nhds 0, φ (ψ y) = y := by
    have h_ev := hφ_strict.eventually_right_inverse one_ne_zero
    rwa [hφ_z₀] at h_ev
  -- Eventually f(z) = f(z₀) + c · φ(z)^n.
  have h_factor_eq : ∀ᶠ z in nhds z₀, f z = f z₀ + c * φ z ^ n := by
    filter_upwards [hg_eq, h_ρ_pow_eq] with z h_fact h_pow
    -- h_fact : f z - f z₀ = (z - z₀)^n • g z
    -- h_pow : ρ z ^ n = h z = g z / c
    change f z = f z₀ + c * ((z - z₀) * ρ z) ^ n
    have h_sub : f z - f z₀ = (z - z₀)^n • g z := h_fact
    have h_smul : (z - z₀)^n • g z = (z - z₀)^n * g z := by rw [smul_eq_mul]
    rw [h_smul] at h_sub
    have h_g_eq : g z = c * h z := by
      change g z = c * (g z / c)
      field_simp
    rw [h_g_eq] at h_sub
    have h_pow_expand : ((z - z₀) * ρ z) ^ n = (z - z₀)^n * ρ z ^ n := by
      rw [mul_pow]
    rw [h_pow_expand, h_pow]
    linear_combination h_sub
  -- Collect all eventually-conditions into a single open ball around z₀:
  -- ∃ ε > 0, ∀ z ∈ B(z₀, ε), ψ z ∈ U ∧ f(ψ z + extra) etc.
  -- Use that ψ(0) = z₀ ∈ U (since U ∈ nhds z₀).
  -- Build the witness V around f(z₀) such that w ∈ V → ζ = (w - f(z₀))/c is small enough
  -- that both ζ_0 = exp((1/n) log ζ) and ζ_1 = ζ_0 * exp(2πi/n) are in nhds 0 with all
  -- needed properties.
  -- Combine eventually facts: ψ(0) = z₀ ∈ U, ψ continuous, etc.
  -- Get a single radius δ that handles everything.
  have h_all_nhd_0 : ∀ᶠ y in nhds 0, φ (ψ y) = y ∧ ψ y ∈ U ∧ f (ψ y) = f z₀ + c * φ (ψ y) ^ n := by
    have h_ψU : ∀ᶠ y in nhds 0, ψ y ∈ U := by
      have h_ψU_filter : Filter.Tendsto ψ (nhds 0) (nhds (ψ 0)) := hψ_cont
      rw [hψ_0] at h_ψU_filter
      exact h_ψU_filter hU
    have h_fac_ψ : ∀ᶠ y in nhds 0, f (ψ y) = f z₀ + c * φ (ψ y) ^ n := by
      have h_ψ_to_z₀ : Filter.Tendsto ψ (nhds 0) (nhds z₀) := by
        rw [← hψ_0]; exact hψ_cont
      exact h_ψ_to_z₀ h_factor_eq
    filter_upwards [h_right_inv, h_ψU, h_fac_ψ] with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- Extract ε > 0 such that B(0, ε) is in the eventually set.
  rcases Metric.eventually_nhds_iff.mp h_all_nhd_0 with ⟨δ, hδ_pos, hδ_prop⟩
  -- Define V = B(f z₀, |c| · δ^n).
  set η : ℝ := ‖c‖ * δ^n with hη_def
  have hη_pos : 0 < η := by
    have hδ_pow_pos : 0 < δ^n := pow_pos hδ_pos n
    have hc_norm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc_ne
    positivity
  refine ⟨Metric.ball (f z₀) η, Metric.ball_mem_nhds _ hη_pos, ?_⟩
  intro w hw_in_V hw_ne
  -- w ∈ B(f z₀, η), w ≠ f z₀.
  -- Define ζ = (w - f z₀) / c.
  set ζ : ℂ := (w - f z₀) / c with hζ_def
  have hζ_ne : ζ ≠ 0 := by
    intro hζ_zero
    apply hw_ne
    have h_sub_zero : w - f z₀ = 0 := by
      have h1 : (w - f z₀) / c = 0 := hζ_zero
      have h_mul : (w - f z₀) / c * c = 0 * c := by rw [h1]
      rw [div_mul_cancel₀ _ hc_ne, zero_mul] at h_mul
      exact h_mul
    linear_combination h_sub_zero
  -- Define ζ_0 = exp((1/n) * log ζ), ζ_1 = ζ_0 * exp(2πi/n).
  set ζ_0 : ℂ := Complex.exp ((n : ℂ)⁻¹ * Complex.log ζ) with hζ_0_def
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hω_def
  set ζ_1 : ℂ := ζ_0 * ω with hζ_1_def
  -- ζ_0 ^ n = ζ.
  have hζ_0_pow : ζ_0 ^ n = ζ := by
    change Complex.exp ((n : ℂ)⁻¹ * Complex.log ζ) ^ n = ζ
    rw [← Complex.exp_nat_mul]
    have h_simp : (n : ℂ) * ((n : ℂ)⁻¹ * Complex.log ζ) = Complex.log ζ := by field_simp
    rw [h_simp]
    exact Complex.exp_log hζ_ne
  -- ω ^ n = 1.
  have hω_pow : ω ^ n = 1 := by
    change Complex.exp (2 * Real.pi * Complex.I / n) ^ n = 1
    rw [← Complex.exp_nat_mul]
    have h_simp : (n : ℂ) * (2 * Real.pi * Complex.I / n) = 2 * Real.pi * Complex.I := by
      field_simp
    rw [h_simp]
    exact Complex.exp_two_pi_mul_I
  -- ζ_1 ^ n = ζ.
  have hζ_1_pow : ζ_1 ^ n = ζ := by
    change (ζ_0 * ω) ^ n = ζ
    rw [mul_pow, hω_pow, mul_one, hζ_0_pow]
  -- ω ≠ 1 (since n ≥ 2).
  have hω_ne_one : ω ≠ 1 := by
    intro hω_one
    -- ω = 1 means exp(2πi/n) = 1, so 2πi/n = 2πi·k for some k ∈ ℤ.
    -- This means 1/n = k, so n | 1, so n = 1, contradicting n ≥ 2.
    have h_log_eq : Complex.log ω = 0 := by rw [hω_one]; exact Complex.log_one
    -- log(exp(z)) = z when -π < z.im ≤ π.
    have h_2pi_div_n_im : ((2 * Real.pi * Complex.I / n : ℂ)).im = 2 * Real.pi / n := by
      have h_n_re : (n : ℂ).re = n := by simp
      have h_n_im : (n : ℂ).im = 0 := by simp
      have h_n_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
      simp [Complex.div_im, Complex.mul_im, Complex.mul_re,
        Complex.I_im, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im, h_n_im]
      field_simp
    have h_2pi_div_n_lt : (2 * Real.pi * Complex.I / n : ℂ).im ≤ Real.pi := by
      rw [h_2pi_div_n_im]
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn_ge_two
      have h_pi_pos : 0 < Real.pi := Real.pi_pos
      have : 2 * Real.pi / n ≤ Real.pi := by
        rw [div_le_iff₀ (by exact_mod_cast hn_pos : (0 : ℝ) < (n : ℝ))]
        nlinarith
      exact this
    have h_2pi_div_n_gt : -Real.pi < (2 * Real.pi * Complex.I / n : ℂ).im := by
      rw [h_2pi_div_n_im]
      have h_pi_pos : 0 < Real.pi := Real.pi_pos
      have h_n_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
      have : 0 < 2 * Real.pi / n := by positivity
      linarith
    have h_log_omega : Complex.log ω = 2 * Real.pi * Complex.I / n := by
      change Complex.log (Complex.exp (2 * Real.pi * Complex.I / n)) = 2 * Real.pi * Complex.I / n
      exact Complex.log_exp h_2pi_div_n_gt h_2pi_div_n_lt
    rw [h_log_omega] at h_log_eq
    -- h_log_eq : 2πi/n = 0, but 2πi/n ≠ 0.
    have h_im : (2 * Real.pi * Complex.I / n : ℂ).im = 0 := by rw [h_log_eq]; simp
    rw [h_2pi_div_n_im] at h_im
    have h_pos : 0 < 2 * Real.pi / n := by
      have h_n_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
      have : 0 < Real.pi := Real.pi_pos
      positivity
    linarith
  -- ζ_1 ≠ ζ_0.
  have hζ_ne_distinct : ζ_0 ≠ ζ_1 := by
    intro h_eq
    have h_ζ₀_ne : ζ_0 ≠ 0 := by
      intro h_ζ₀_zero
      have : ζ_0 ^ n = 0 := by rw [h_ζ₀_zero]; exact zero_pow hn_ne_zero
      rw [hζ_0_pow] at this
      exact hζ_ne this
    have : ω = 1 := by
      have h_eq' : ζ_0 * ω = ζ_0 * 1 := by rw [mul_one]; exact h_eq.symm
      exact mul_left_cancel₀ h_ζ₀_ne h_eq'
    exact hω_ne_one this
  -- |ζ| < δ^n.
  have h_ζ_norm : ‖ζ‖ < δ^n := by
    change ‖(w - f z₀) / c‖ < δ^n
    rw [norm_div]
    rw [Metric.mem_ball, dist_eq_norm] at hw_in_V
    have h_num_lt : ‖w - f z₀‖ < η := hw_in_V
    have h_c_norm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc_ne
    rw [div_lt_iff₀ h_c_norm_pos]
    have h_η_def : η = ‖c‖ * δ^n := hη_def
    nlinarith
  -- ‖ζ_0‖ = |ζ|^(1/n) < δ.
  have h_ζ₀_norm_eq : ‖ζ_0‖ = ‖ζ‖^((n : ℝ)⁻¹) := by
    change ‖Complex.exp ((n : ℂ)⁻¹ * Complex.log ζ)‖ = ‖ζ‖^((n : ℝ)⁻¹)
    rw [Complex.norm_exp]
    -- Re((n : ℂ)⁻¹ * log ζ) = (1/n) * Re(log ζ) = (1/n) * log ‖ζ‖
    have h_n_re : ((n : ℂ)⁻¹).re = (n : ℝ)⁻¹ := by
      have : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
      rw [this, ← Complex.ofReal_inv]
      simp
    have h_n_im : ((n : ℂ)⁻¹).im = 0 := by
      have : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
      rw [this, ← Complex.ofReal_inv]
      simp
    rw [Complex.mul_re, h_n_re, h_n_im, zero_mul, sub_zero]
    rw [Complex.log_re]
    have h_norm_pos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ_ne
    rw [show (n : ℝ)⁻¹ * Real.log ‖ζ‖ = Real.log ‖ζ‖ * (n : ℝ)⁻¹ from by ring]
    exact (Real.rpow_def_of_pos h_norm_pos _).symm
  have h_ζ₀_norm_lt : ‖ζ_0‖ < δ := by
    rw [h_ζ₀_norm_eq]
    have h_pos_zeta : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ_ne
    have h_n_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have h_n_real_ne : (n : ℝ) ≠ 0 := ne_of_gt h_n_real_pos
    have h_n_inv_pos : 0 < ((n : ℝ))⁻¹ := inv_pos.mpr h_n_real_pos
    -- We need ‖ζ‖^(1/n) < δ.
    -- We have ‖ζ‖ < δ^n (= h_ζ_norm).
    -- Apply rpow with positive 1/n: (‖ζ‖)^(1/n) < (δ^n)^(1/n) = δ.
    have h_δ_pos : 0 < δ := hδ_pos
    have h_step1 : ‖ζ‖ ^ ((n : ℝ)⁻¹) < (δ^n) ^ ((n : ℝ)⁻¹) := by
      exact Real.rpow_lt_rpow h_pos_zeta.le h_ζ_norm h_n_inv_pos
    have h_step2 : (δ^n) ^ ((n : ℝ)⁻¹) = δ := by
      rw [show δ^n = δ ^ ((n : ℕ) : ℝ) from (Real.rpow_natCast δ n).symm]
      rw [← Real.rpow_mul h_δ_pos.le]
      rw [mul_inv_cancel₀ h_n_real_ne]
      exact Real.rpow_one _
    linarith
  -- ‖ζ_1‖ = ‖ζ_0‖ < δ.
  have h_ζ₁_norm_lt : ‖ζ_1‖ < δ := by
    change ‖ζ_0 * ω‖ < δ
    rw [norm_mul]
    have h_omega_norm : ‖ω‖ = 1 := by
      change ‖Complex.exp (2 * Real.pi * Complex.I / n)‖ = 1
      rw [Complex.norm_exp]
      -- Re(2πi/n) = 0
      have h_re_zero : ((2 * Real.pi * Complex.I / n : ℂ)).re = 0 := by
        simp [Complex.div_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [h_re_zero, Real.exp_zero]
    rw [h_omega_norm, mul_one]
    exact h_ζ₀_norm_lt
  -- ζ_0, ζ_1 ∈ B(0, δ).
  have h_ζ₀_in_ball : ζ_0 ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_zero_right]; exact h_ζ₀_norm_lt
  have h_ζ₁_in_ball : ζ_1 ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_zero_right]; exact h_ζ₁_norm_lt
  -- Convert to membership in nhds 0 (for hδ_prop).
  have hδ_at_ball : ∀ y ∈ Metric.ball (0 : ℂ) δ,
      φ (ψ y) = y ∧ ψ y ∈ U ∧ f (ψ y) = f z₀ + c * φ (ψ y) ^ n := by
    intro y hy
    have : dist y 0 < δ := Metric.mem_ball.mp hy
    exact hδ_prop this
  obtain ⟨h_φψ_ζ₀, hψ_ζ₀_U, h_f_ψ_ζ₀⟩ := hδ_at_ball ζ_0 h_ζ₀_in_ball
  obtain ⟨h_φψ_ζ₁, hψ_ζ₁_U, h_f_ψ_ζ₁⟩ := hδ_at_ball ζ_1 h_ζ₁_in_ball
  -- f(ψ ζ_i) = w.
  have h_f_ψ_ζ₀_eq_w : f (ψ ζ_0) = w := by
    rw [h_f_ψ_ζ₀, h_φψ_ζ₀, hζ_0_pow]
    change f z₀ + c * ((w - f z₀) / c) = w
    rw [mul_div_cancel₀ _ hc_ne]; ring
  have h_f_ψ_ζ₁_eq_w : f (ψ ζ_1) = w := by
    rw [h_f_ψ_ζ₁, h_φψ_ζ₁, hζ_1_pow]
    change f z₀ + c * ((w - f z₀) / c) = w
    rw [mul_div_cancel₀ _ hc_ne]; ring
  -- ψ ζ_0 ≠ ψ ζ_1.
  have hψ_ne : ψ ζ_0 ≠ ψ ζ_1 := by
    intro h_eq
    -- ψ injective on its image (since ψ is local inverse).
    have h_eq' : φ (ψ ζ_0) = φ (ψ ζ_1) := by rw [h_eq]
    rw [h_φψ_ζ₀, h_φψ_ζ₁] at h_eq'
    exact hζ_ne_distinct h_eq'
  -- Wrap up.
  exact ⟨ψ ζ_0, hψ_ζ₀_U, ψ ζ_1, hψ_ζ₁_U, hψ_ne, h_f_ψ_ζ₀_eq_w, h_f_ψ_ζ₁_eq_w⟩

end NoWanderingDomains
