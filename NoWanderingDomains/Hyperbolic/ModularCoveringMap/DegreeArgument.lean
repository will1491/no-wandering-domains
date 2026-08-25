/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.ModularCoveringMap.ArgumentPrincipleBridge

/-! # Segment transport and the degree bootstrap

Segment transport and the degree-argument bootstrap. The `F_Y` interior lies inside
`F°` (the arc bound forces `‖2τ − 1‖ > 1`), the boundary contour integral is invariant
along a `w`-segment avoided by the image curve, and uniform boundary clearance bounds
hold for the top edge, the bottom strips, and the arc, with thresholds depending only
on bounds for `w`. Transporting the `F_Y` zero count to the deep-cusp reference value
proves that the `F°`-preimage of each `w` with `Im w > 0` is unique and that `λ′` does
not vanish there.
-/

namespace NoWanderingDomains
open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-! ## Segment transport and uniform boundary clearance -/

/-- **The truncated region avoids the unit semicircle.** Under the arc
bound `√(1/4 − δ²) < R₀`, every point `τ` with `δ < Im τ` lying outside
the closed ball `B(1/2 + δi, R₀)` satisfies `1 < ‖2τ − 1‖`.

Together with the strip bounds `0 < Re τ < 1` this places the interior
of the truncated region F_Y inside the open fundamental domain `F°`:
the algebra `‖τ − (1/2 + δi)‖² = ‖τ − 1/2‖² − 2δ·Im τ + δ²` combined
with `‖τ − (1/2 + δi)‖² > R₀² > 1/4 − δ²` and `Im τ > δ > 0` yields
`‖τ − 1/2‖² > 1/4 + 2δ(Im τ − δ) > 1/4`. Consequently the zeros of
`λ − w` counted by the F_Y argument principle are exactly the
`F°`-preimages of `w` lying in F_Y. -/
theorem F_Y_point_in_gamma2_semicircle_exterior
    {δ R₀ : ℝ} (hδ : 0 < δ) (hR₀_lo : Real.sqrt (1 / 4 - δ ^ 2) < R₀)
    {τ : ℂ} (h_im : δ < τ.im)
    (h_arc : R₀ < ‖τ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖) :
    1 < ‖2 * τ - 1‖ := by
  have hR₀_pos : 0 < R₀ := lt_of_le_of_lt (Real.sqrt_nonneg _) hR₀_lo
  -- Square the arc bound: 1/4 − δ² < R₀².
  have h_sq_lo : 1 / 4 - δ ^ 2 < R₀ ^ 2 := (Real.sqrt_lt' hR₀_pos).mp hR₀_lo
  -- Square the distance bound: R₀² < ‖τ − (1/2 + δi)‖².
  have h_sq_arc : R₀ ^ 2 < ‖τ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖ ^ 2 := by
    have h := mul_self_lt_mul_self hR₀_pos.le h_arc
    nlinarith [h]
  -- Coordinates.
  have h_norm_arc : ‖τ - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)‖ ^ 2 =
      (τ.re - 1 / 2) ^ 2 + (τ.im - δ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h_norm_semi : ‖2 * τ - 1‖ ^ 2 = (2 * τ.re - 1) ^ 2 + (2 * τ.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    ring
  -- Conclude via the squares.
  have h_one_lt_sq : 1 < ‖2 * τ - 1‖ ^ 2 := by
    rw [h_norm_semi]
    rw [h_norm_arc] at h_sq_arc
    nlinarith [h_sq_lo, h_sq_arc, h_im, hδ]
  by_contra h_le
  push Not at h_le
  nlinarith [norm_nonneg (2 * τ - 1), h_le, h_one_lt_sq]

/-- **Contour-integral invariance along a `w`-segment avoided by the
image curve.** If the image curve `λ ∘ ∂F_Y` avoids every point of the
segment `[w₀, w₁]`, the contour integrals of `(z − w₀)⁻¹` and
`(z − w₁)⁻¹` along it coincide.

Proof: the moving difference `u(s, t) := λ(γ(t)) − ((1 − s)w₀ + s·w₁)`
admits a jointly continuous log lift `L` over `[0, 1] × [0, 6]`
(`continuous_log_lift_param_of_continuous_ne_zero`); the cross-section
boundary difference `τ(s) := L s 6 − L s 0` is continuous and lies in
`2πi·ℤ` (the curve closes up), so by the intermediate value theorem
`τ(0) = τ(1)`; the piecewise FTC bridge identifies the two contour
integrals with `τ(0)` and `τ(1)`. -/
theorem modularLambdaH_F_Y_pathContourIntegral_eq_of_segment_avoids
    {δ Y R₀ : ℝ} (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    {w₀ w₁ : ℂ}
    (h_avoid : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) ≠
        (1 - (s : ℂ)) * w₀ + (s : ℂ) * w₁) :
    Complex.pathContourIntegral
      (fun t => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
      0 6 (fun z => (z - w₀)⁻¹) =
    Complex.pathContourIntegral
      (fun t => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
      0 6 (fun z => (z - w₁)⁻¹) := by
  -- The moving difference u(s, t) := λ(γ t) − w(s) along the segment
  -- w(s) := (1 − s)·w₀ + s·w₁ is jointly continuous and nonvanishing.
  have h_image_cont : ContinuousOn
      (fun t : ℝ => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
      (Set.Icc (0 : ℝ) 6) := by
    have h := F_Y_image_curve_continuousOn w₀ hδ hδY hR₀_pos hR₀_lt
    have h_eq : (fun t : ℝ =>
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t)) =
        fun t => (modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w₀) + w₀ := by
      funext t; ring
    rw [h_eq]
    exact h.add continuousOn_const
  have h_u_cont : ContinuousOn
      (Function.uncurry (fun (s : ℝ) (t : ℝ) =>
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) -
          ((1 - (s : ℂ)) * w₀ + (s : ℂ) * w₁)))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 6) := by
    have h1 : ContinuousOn
        (fun p : ℝ × ℝ =>
          modularLambdaH (F_Y_boundary_parameterization δ Y R₀ p.2))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 6) := by
      refine ContinuousOn.comp h_image_cont continuousOn_snd ?_
      intro p hp
      exact hp.2
    have h2 : Continuous (fun p : ℝ × ℝ =>
        (1 - ((p.1 : ℝ) : ℂ)) * w₀ + ((p.1 : ℝ) : ℂ) * w₁) := by
      fun_prop
    exact h1.sub h2.continuousOn
  obtain ⟨L, hL_cont, hL_exp₀⟩ :=
    continuous_log_lift_param_of_continuous_ne_zero
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 6)
      (fun (s : ℝ) (t : ℝ) =>
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) -
        ((1 - (s : ℂ)) * w₀ + (s : ℂ) * w₁)) h_u_cont
      (fun s hs t ht => sub_ne_zero.mpr (h_avoid s hs t ht))
  have hL_exp : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 6,
      Complex.exp (L s t) =
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) -
          ((1 - (s : ℂ)) * w₀ + (s : ℂ) * w₁) := hL_exp₀
  have h0_mem6 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 6 := by norm_num
  have h6_mem6 : (6 : ℝ) ∈ Set.Icc (0 : ℝ) 6 := by norm_num
  have h0_mem1 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have h1_mem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  -- The F_Y boundary curve closes up.
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
  -- Cross-section boundary difference: continuous, valued in 2πi·ℤ.
  have h_τ_cont : Continuous (fun s => L s 6 - L s 0) := by
    have h6 : Continuous (fun s => L s 6) :=
      hL_cont.comp (continuous_id.prodMk continuous_const)
    have h0 : Continuous (fun s => L s 0) :=
      hL_cont.comp (continuous_id.prodMk continuous_const)
    exact h6.sub h0
  have h_τ_int : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∃ n : ℤ, L s 6 - L s 0 = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    intro s hs
    have h_exp_eq : Complex.exp (L s 6 - L s 0) = 1 := by
      rw [Complex.exp_sub, hL_exp s hs 6 h6_mem6, hL_exp s hs 0 h0_mem6,
        hγ_closed]
      exact div_self (sub_ne_zero.mpr (by rw [← hγ_closed]; exact h_avoid s hs 0 h0_mem6))
    exact Complex.exp_eq_one_iff.mp h_exp_eq
  have h_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hψ_int : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∃ n : ℤ, (L s 6 - L s 0).im / (2 * Real.pi) = (n : ℝ) := by
    intro s hs
    obtain ⟨n, hn⟩ := h_τ_int s hs
    refine ⟨n, ?_⟩
    have h_im : (L s 6 - L s 0).im = (n : ℝ) * (2 * Real.pi) := by
      rw [hn]
      simp [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    rw [h_im]
    field_simp
  have hψ_re : ∀ s ∈ Set.Icc (0 : ℝ) 1, (L s 6 - L s 0).re = 0 := by
    intro s hs
    obtain ⟨n, hn⟩ := h_τ_int s hs
    rw [hn]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  have h_τ_eq : L 0 6 - L 0 0 = L 1 6 - L 1 0 := by
    have hψ_cont : Continuous (fun s => (L s 6 - L s 0).im / (2 * Real.pi)) :=
      (Complex.continuous_im.comp h_τ_cont).div_const _
    obtain ⟨n₀, hn₀⟩ := hψ_int 0 h0_mem1
    obtain ⟨n₁, hn₁⟩ := hψ_int 1 h1_mem1
    have h_n_eq : n₀ = n₁ := by
      by_contra h_ne
      rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
      · have h_le : (n₀ : ℝ) + 1 ≤ n₁ := by exact_mod_cast h_lt
        have h_mem : ((n₀ : ℝ) + 1 / 2) ∈ Set.Icc
            ((L (0 : ℝ) 6 - L 0 0).im / (2 * Real.pi))
            ((L (1 : ℝ) 6 - L 1 0).im / (2 * Real.pi)) := by
          rw [hn₀, hn₁]
          constructor <;> linarith
        obtain ⟨s, hs_mem, hs_val⟩ :=
          intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
            hψ_cont.continuousOn h_mem
        have hs_val' : (L s 6 - L s 0).im / (2 * Real.pi) = (n₀ : ℝ) + 1 / 2 := hs_val
        obtain ⟨m, hm⟩ := hψ_int s hs_mem
        have h_m_val : (m : ℝ) = (n₀ : ℝ) + 1 / 2 := by rw [← hm]; exact hs_val'
        have h_cast : ((2 * m : ℤ) : ℝ) = ((2 * n₀ + 1 : ℤ) : ℝ) := by
          push_cast; linarith
        have h2m : (2 * m : ℤ) = 2 * n₀ + 1 := by exact_mod_cast h_cast
        omega
      · have h_le : (n₁ : ℝ) + 1 ≤ n₀ := by exact_mod_cast h_gt
        have h_mem : ((n₁ : ℝ) + 1 / 2) ∈ Set.Icc
            ((L (1 : ℝ) 6 - L 1 0).im / (2 * Real.pi))
            ((L (0 : ℝ) 6 - L 0 0).im / (2 * Real.pi)) := by
          rw [hn₀, hn₁]
          constructor <;> linarith
        obtain ⟨s, hs_mem, hs_val⟩ :=
          intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
            hψ_cont.continuousOn h_mem
        have hs_val' : (L s 6 - L s 0).im / (2 * Real.pi) = (n₁ : ℝ) + 1 / 2 := hs_val
        obtain ⟨m, hm⟩ := hψ_int s hs_mem
        have h_m_val : (m : ℝ) = (n₁ : ℝ) + 1 / 2 := by rw [← hm]; exact hs_val'
        have h_cast : ((2 * m : ℤ) : ℝ) = ((2 * n₁ + 1 : ℤ) : ℝ) := by
          push_cast; linarith
        have h2m : (2 * m : ℤ) = 2 * n₁ + 1 := by exact_mod_cast h_cast
        omega
    have h_im0 : (L (0 : ℝ) 6 - L 0 0).im = (n₀ : ℝ) * (2 * Real.pi) := by
      have h := hn₀
      field_simp at h
      linarith
    have h_im1 : (L (1 : ℝ) 6 - L 1 0).im = (n₁ : ℝ) * (2 * Real.pi) := by
      have h := hn₁
      field_simp at h
      linarith
    refine Complex.ext ?_ ?_
    · rw [hψ_re 0 h0_mem1, hψ_re 1 h1_mem1]
    · rw [h_im0, h_im1, h_n_eq]
  -- FTC at the two endpoints of the segment.
  have h_γ_ne₀ : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w₀ ≠ 0 := by
    intro t ht
    have h := h_avoid 0 h0_mem1 t ht
    rw [show (1 - ((0 : ℝ) : ℂ)) * w₀ + ((0 : ℝ) : ℂ) * w₁ = w₀ by push_cast; ring] at h
    exact sub_ne_zero.mpr h
  have h_γ_ne₁ : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w₁ ≠ 0 := by
    intro t ht
    have h := h_avoid 1 h1_mem1 t ht
    rw [show (1 - ((1 : ℝ) : ℂ)) * w₀ + ((1 : ℝ) : ℂ) * w₁ = w₁ by push_cast; ring] at h
    exact sub_ne_zero.mpr h
  have h_L0_cont : Continuous (fun t => L 0 t) :=
    hL_cont.comp (continuous_const.prodMk continuous_id)
  have h_L1_cont : Continuous (fun t => L 1 t) :=
    hL_cont.comp (continuous_const.prodMk continuous_id)
  have h_L0_exp : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      Complex.exp (L 0 t) =
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w₀ := by
    intro t ht
    rw [hL_exp 0 h0_mem1 t ht]
    rw [show (1 - ((0 : ℝ) : ℂ)) * w₀ + ((0 : ℝ) : ℂ) * w₁ = w₀ by push_cast; ring]
  have h_L1_exp : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      Complex.exp (L 1 t) =
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w₁ := by
    intro t ht
    rw [hL_exp 1 h1_mem1 t ht]
    rw [show (1 - ((1 : ℝ) : ℂ)) * w₀ + ((1 : ℝ) : ℂ) * w₁ = w₁ by push_cast; ring]
  have h_left := pathContourIntegral_inv_eq_log_lift_diff_F_Y_image_curve
    hδ hδY hR₀_pos hR₀_lt h_γ_ne₀ (fun t => L 0 t) h_L0_cont h_L0_exp
  have h_right := pathContourIntegral_inv_eq_log_lift_diff_F_Y_image_curve
    hδ hδY hR₀_pos hR₀_lt h_γ_ne₁ (fun t => L 1 t) h_L1_cont h_L1_exp
  rw [h_left, h_right]
  exact h_τ_eq


/-- **Uniform smallness of `λ` on high horizontal edges.** For any
`ν > 0` there is a height `Y₀ ≥ 1` beyond which `‖λ‖ < ν` on the whole
horizontal segment `[0, 1] × {Y}`. Quantitative form of the cusp-`∞`
decay, from `modularLambdaH_norm_le_exp_of_im_ge_one`. -/
theorem modularLambdaH_top_edge_norm_lt_uniform {ν : ℝ} (hν : 0 < ν) :
    ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y → ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      ‖modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I)‖ < ν := by
  -- Choose Y₀ with 160000·exp(−π·Y₀) < ν.
  set Y₀ : ℝ := max 1 (Real.log (320000 / ν) / Real.pi) with hY₀_def
  refine ⟨Y₀, le_max_left _ _, ?_⟩
  intro Y hY x hx_nn hx_le
  have hY_ge_one : 1 ≤ Y := le_trans (le_max_left _ _) hY
  set τ : ℂ := (x : ℂ) + (Y : ℂ) * Complex.I with hτ_def
  have hτ_im : τ.im = Y := by
    simp [hτ_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_decay := modularLambdaH_norm_le_exp_of_im_ge_one (τ := τ) (by rw [hτ_im]; exact hY_ge_one)
  rw [hτ_im] at h_decay
  refine lt_of_le_of_lt h_decay ?_
  -- 160000·exp(−π·Y) < ν since Y ≥ log(320000/ν)/π.
  have h_log_le : Real.log (320000 / ν) / Real.pi ≤ Y :=
    le_trans (le_max_right _ _) hY
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_log_le' : Real.log (320000 / ν) ≤ Real.pi * Y := by
    rw [div_le_iff₀ h_pi_pos] at h_log_le
    linarith
  have h_ratio_pos : (0 : ℝ) < 320000 / ν := by positivity
  have h_exp_bound : 320000 / ν ≤ Real.exp (Real.pi * Y) := by
    calc 320000 / ν = Real.exp (Real.log (320000 / ν)) := (Real.exp_log h_ratio_pos).symm
      _ ≤ Real.exp (Real.pi * Y) := Real.exp_le_exp.mpr h_log_le'
  have h_exp_pos : (0 : ℝ) < Real.exp (Real.pi * Y) := Real.exp_pos _
  have h_neg_exp : Real.exp (-Real.pi * Y) = (Real.exp (Real.pi * Y))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [h_neg_exp]
  rw [show (160000 : ℝ) * (Real.exp (Real.pi * Y))⁻¹ =
    160000 / Real.exp (Real.pi * Y) from by ring]
  rw [div_lt_iff₀ h_exp_pos]
  have h_from_bound : 320000 / ν * ν ≤ Real.exp (Real.pi * Y) * ν := by
    exact mul_le_mul_of_nonneg_right h_exp_bound hν.le
  rw [div_mul_cancel₀ (320000 : ℝ) (ne_of_gt hν)] at h_from_bound
  linarith


/-- **Segment-uniform bottom-left strip bound.** Quantitative variant
of `modularLambdaH_F_Y_bot_left_strip_ne`: a single strip width works
simultaneously for every `w'` at distance at least `ρ` from `1`
(near the cusp `0` the boundary values approach `1`). -/
theorem modularLambdaH_F_Y_bot_left_strip_ne_uniform {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ_u : ℝ, 0 < δ_u ∧ δ_u < 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ_u → ∀ x : ℝ, 0 ≤ x → x ≤ δ →
      ∀ w' : ℂ, ρ ≤ ‖w' - 1‖ →
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w' ≠ 0 := by
  set L : ℝ := Real.log (160000 / ρ) with hL_def
  set M : ℝ := max L 1 with hM_def
  have hM_ge_one : 1 ≤ M := le_max_right _ _
  have hM_pos : 0 < M := by linarith
  have hL_le_M : L ≤ M := le_max_left _ _
  set δ_w : ℝ := min (1/4) (1/(2*M)) with hδ_w_def
  have h_2M_pos : 0 < 2 * M := by linarith
  have hδ_w_pos : 0 < δ_w := lt_min (by norm_num) (by positivity)
  have hδ_w_lt_half : δ_w < 1/2 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨δ_w, hδ_w_pos, hδ_w_lt_half, ?_⟩
  intro δ hδ_pos hδ_le x hx_nn hx_le w' hw'_ρ h_eq
  set τ : ℂ := (x : ℂ) + (δ : ℂ) * Complex.I with hτ_def
  have h_lam_eq : modularLambdaH τ = w' := by linear_combination h_eq
  have hτ_re : τ.re = x := by
    simp [hτ_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im : τ.im = δ := by
    simp [hτ_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im_pos : 0 < τ.im := hτ_im ▸ hδ_pos
  have hδ_le_quarter : δ ≤ 1/4 := le_trans hδ_le (min_le_left _ _)
  have hδ_le_inv_2M : δ ≤ 1/(2*M) := le_trans hδ_le (min_le_right _ _)
  have h_2δ_pos : 0 < 2 * δ := by linarith
  have h_x_sq_le_δ_sq : x^2 ≤ δ^2 := by nlinarith
  have h_x_sq_plus_δ_sq_pos : 0 < x^2 + δ^2 := by nlinarith
  have h_normSq : Complex.normSq τ = x^2 + δ^2 := by
    rw [Complex.normSq_apply, hτ_re, hτ_im]; ring
  -- Im(-1/τ) = δ/(x² + δ²).
  have h_im_inv : (-(τ : ℂ)⁻¹).im = δ / (x^2 + δ^2) := by
    rw [Complex.neg_im, Complex.inv_im, hτ_im, h_normSq]; ring
  -- 1/(2δ) ≤ Im(-1/τ): equivalent to x² + δ² ≤ 2δ² (i.e., x² ≤ δ²).
  have h_im_inv_ge : 1/(2*δ) ≤ (-(τ : ℂ)⁻¹).im := by
    rw [h_im_inv, div_le_div_iff₀ h_2δ_pos h_x_sq_plus_δ_sq_pos]
    nlinarith
  -- 1/(2δ) ≥ 2 (since δ ≤ 1/4).
  have h_inv_2δ_ge_two : 2 ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]; linarith
  have h_inv_im_ge_one : 1 ≤ (-(τ : ℂ)⁻¹).im := by linarith
  -- Apply norm bound to -1/τ.
  have h_norm_lam_inv : ‖modularLambdaH (-(τ : ℂ)⁻¹)‖ ≤
      160000 * Real.exp (-Real.pi * (-(τ : ℂ)⁻¹).im) :=
    modularLambdaH_norm_le_exp_of_im_ge_one h_inv_im_ge_one
  -- Apply S-action identity: λ(τ) + λ(-1/τ) = 1.
  have h_S : modularLambdaH τ + modularLambdaH (-1/τ) = 1 :=
    modularLambdaH_add_S_smul_eq_one hτ_im_pos
  have h_neg_eq : -1/τ = -τ⁻¹ := by field_simp
  rw [h_neg_eq] at h_S
  -- ‖λ(τ) - 1‖ = ‖λ(-τ⁻¹)‖.
  have h_diff_eq : modularLambdaH τ - 1 = -modularLambdaH (-(τ : ℂ)⁻¹) := by
    linear_combination h_S
  have h_norm_diff : ‖modularLambdaH τ - 1‖ = ‖modularLambdaH (-(τ : ℂ)⁻¹)‖ := by
    rw [h_diff_eq, norm_neg]
  -- ‖λ(τ) - 1‖ ≤ 160000 · exp(-π · 1/(2δ)).
  have h_exp_mono : Real.exp (-Real.pi * (-(τ : ℂ)⁻¹).im) ≤
      Real.exp (-Real.pi * (1/(2*δ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, h_im_inv_ge]
  have h_bound : ‖modularLambdaH τ - 1‖ ≤ 160000 * Real.exp (-Real.pi * (1/(2*δ))) := by
    rw [h_norm_diff]
    refine le_trans h_norm_lam_inv ?_
    exact mul_le_mul_of_nonneg_left h_exp_mono (by norm_num)
  -- M ≤ 1/(2δ): δ ≤ 1/(2M) means 2δM ≤ 1.
  have h_M_le_inv_2δ : M ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]
    have h_step : δ * (2 * M) ≤ (1/(2*M)) * (2 * M) :=
      mul_le_mul_of_nonneg_right hδ_le_inv_2M (le_of_lt h_2M_pos)
    rw [div_mul_cancel₀ _ (ne_of_gt h_2M_pos)] at h_step
    linarith
  -- π * (1/(2δ)) > L since π > 1 and M ≥ L: π · M > M ≥ L, and π/(2δ) ≥ π·M.
  have h_pi_gt_one : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have h_pi_M_ge_pi_M : Real.pi * M ≤ Real.pi * (1/(2*δ)) :=
    mul_le_mul_of_nonneg_left h_M_le_inv_2δ (le_of_lt Real.pi_pos)
  have h_L_lt_pi_M : L < Real.pi * M := by
    calc L ≤ M := hL_le_M
      _ = 1 * M := by ring
      _ < Real.pi * M := by exact mul_lt_mul_of_pos_right h_pi_gt_one hM_pos
  have h_L_lt_pi_inv_2δ : L < Real.pi * (1/(2*δ)) :=
    lt_of_lt_of_le h_L_lt_pi_M h_pi_M_ge_pi_M
  -- exp(-π·(1/(2δ))) < exp(-L) = ρ/160000.
  have h_exp_lt : Real.exp (-Real.pi * (1/(2*δ))) < Real.exp (-L) := by
    apply Real.exp_lt_exp.mpr
    linarith
  have h_quot_pos : (0 : ℝ) < 160000 / ρ := by positivity
  have h_exp_neg_L : Real.exp (-L) = ρ / 160000 := by
    rw [hL_def]
    rw [show -Real.log (160000 / ρ) = Real.log ((160000 / ρ)⁻¹) from
      (Real.log_inv _).symm]
    rw [Real.exp_log (by positivity : (0:ℝ) < (160000 / ρ)⁻¹)]
    rw [inv_div]
  have h_final_bound : 160000 * Real.exp (-Real.pi * (1/(2*δ))) < ρ := by
    calc 160000 * Real.exp (-Real.pi * (1/(2*δ)))
        < 160000 * Real.exp (-L) := by
          exact mul_lt_mul_of_pos_left h_exp_lt (by norm_num)
      _ = 160000 * (ρ / 160000) := by rw [h_exp_neg_L]
      _ = ρ := by field_simp
  have h_strict : ‖modularLambdaH τ - 1‖ < ρ := lt_of_le_of_lt h_bound h_final_bound
  have h_strict' : ‖modularLambdaH τ - 1‖ < ‖w' - 1‖ := lt_of_lt_of_le h_strict hw'_ρ
  rw [h_lam_eq] at h_strict'
  exact lt_irrefl _ h_strict'

/-- Segment-uniform variant of `modularLambdaH_F_Y_bot_right_strip_ne`:
the threshold `δ_u` depends only on an upper bound `‖w'‖ ≤ B`. -/
theorem modularLambdaH_F_Y_bot_right_strip_ne_uniform {B : ℝ} (hB : 0 < B) :
    ∃ δ_u : ℝ, 0 < δ_u ∧ δ_u < 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ_u → ∀ x : ℝ, 1 - δ ≤ x → x ≤ 1 →
      ∀ w' : ℂ, ‖w'‖ ≤ B →
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w' ≠ 0 := by
  -- Target: ‖λ(τ - 1) - 1‖ < 1/(B + 2). Then |λ(τ)| ≥ ‖w'‖ + 1 > ‖w'‖, so λ(τ) ≠ w'.
  set L : ℝ := Real.log (160000 * (B + 2)) with hL_def
  set M : ℝ := max L 1 with hM_def
  have hM_ge_one : 1 ≤ M := le_max_right _ _
  have hM_pos : 0 < M := by linarith
  have hL_le_M : L ≤ M := le_max_left _ _
  set δ_w : ℝ := min (1/4) (1/(2*M)) with hδ_w_def
  have h_2M_pos : 0 < 2 * M := by linarith
  have hδ_w_pos : 0 < δ_w := lt_min (by norm_num) (by positivity)
  have hδ_w_lt_half : δ_w < 1/2 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨δ_w, hδ_w_pos, hδ_w_lt_half, ?_⟩
  intro δ hδ_pos hδ_le x hx_ge hx_le w' hw'_B h_eq
  set τ : ℂ := (x : ℂ) + (δ : ℂ) * Complex.I with hτ_def
  have h_lam_eq : modularLambdaH τ = w' := by linear_combination h_eq
  have hτ_re : τ.re = x := by
    simp [hτ_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im : τ.im = δ := by
    simp [hτ_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ_im_pos : 0 < τ.im := hτ_im ▸ hδ_pos
  have hδ_le_quarter : δ ≤ 1/4 := le_trans hδ_le (min_le_left _ _)
  have hδ_le_inv_2M : δ ≤ 1/(2*M) := le_trans hδ_le (min_le_right _ _)
  have h_2δ_pos : 0 < 2 * δ := by linarith
  -- Define τ' := (1 - x) + δi (in bot_left strip).
  set τ' : ℂ := ((1 - x : ℝ) : ℂ) + (δ : ℂ) * Complex.I with hτ'_def
  have hτ'_re : τ'.re = 1 - x := by
    simp [hτ'_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ'_im : τ'.im = δ := by
    simp [hτ'_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hτ'_im_pos : 0 < τ'.im := hτ'_im ▸ hδ_pos
  have hτ'_re_nn : 0 ≤ τ'.re := by rw [hτ'_re]; linarith
  have hτ'_re_le_δ : τ'.re ≤ δ := by rw [hτ'_re]; linarith
  -- σ := τ - 1.
  set σ : ℂ := τ - 1 with hσ_def
  have hσ_im : σ.im = δ := by simp [hσ_def, hτ_im]
  have hσ_im_pos : 0 < σ.im := hσ_im ▸ hδ_pos
  -- -conj σ = τ', so λ(τ') = conj(λ(σ)).
  have h_neg_conj_σ : -(starRingEnd ℂ σ) = τ' := by
    apply Complex.ext
    · simp [hσ_def, hτ_def, hτ'_def, Complex.neg_re,
        Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    · simp [hσ_def, hτ_def, hτ'_def, Complex.neg_im,
        Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
  have h_conj_lam : modularLambdaH τ' = starRingEnd ℂ (modularLambdaH σ) := by
    rw [← h_neg_conj_σ]
    exact modularLambdaH_conj_symmetry hσ_im_pos
  -- Cusp-0 bound on τ' (in bot_left strip):
  -- For τ' = (1-x) + δi with (1-x) ∈ [0, δ] and δ ∈ (0, 1/4]:
  -- Compute Im(-1/τ'), apply norm bound, apply S-action identity.
  have h_x_sq_le_δ_sq : (1 - x)^2 ≤ δ^2 := by nlinarith
  have h_x_sq_plus_δ_sq_pos : 0 < (1 - x)^2 + δ^2 := by nlinarith
  have h_normSq_τ' : Complex.normSq τ' = (1 - x)^2 + δ^2 := by
    rw [Complex.normSq_apply, hτ'_re, hτ'_im]; ring
  have h_im_inv_τ' : (-(τ' : ℂ)⁻¹).im = δ / ((1 - x)^2 + δ^2) := by
    rw [Complex.neg_im, Complex.inv_im, hτ'_im, h_normSq_τ']; ring
  have h_im_inv_τ'_ge : 1/(2*δ) ≤ (-(τ' : ℂ)⁻¹).im := by
    rw [h_im_inv_τ', div_le_div_iff₀ h_2δ_pos h_x_sq_plus_δ_sq_pos]
    nlinarith
  have h_inv_2δ_ge_two : 2 ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]; linarith
  have h_inv_im_τ'_ge_one : 1 ≤ (-(τ' : ℂ)⁻¹).im := by linarith
  have h_norm_lam_inv_τ' : ‖modularLambdaH (-(τ' : ℂ)⁻¹)‖ ≤
      160000 * Real.exp (-Real.pi * (-(τ' : ℂ)⁻¹).im) :=
    modularLambdaH_norm_le_exp_of_im_ge_one h_inv_im_τ'_ge_one
  have h_S_τ' : modularLambdaH τ' + modularLambdaH (-1/τ') = 1 :=
    modularLambdaH_add_S_smul_eq_one hτ'_im_pos
  have h_neg_eq_τ' : -1/τ' = -τ'⁻¹ := by field_simp
  rw [h_neg_eq_τ'] at h_S_τ'
  have h_diff_τ' : modularLambdaH τ' - 1 = -modularLambdaH (-(τ' : ℂ)⁻¹) := by
    linear_combination h_S_τ'
  have h_norm_diff_τ' : ‖modularLambdaH τ' - 1‖ = ‖modularLambdaH (-(τ' : ℂ)⁻¹)‖ := by
    rw [h_diff_τ', norm_neg]
  have h_exp_mono_τ' : Real.exp (-Real.pi * (-(τ' : ℂ)⁻¹).im) ≤
      Real.exp (-Real.pi * (1/(2*δ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, h_im_inv_τ'_ge]
  have h_bound_τ' : ‖modularLambdaH τ' - 1‖ ≤ 160000 * Real.exp (-Real.pi * (1/(2*δ))) := by
    rw [h_norm_diff_τ']
    exact le_trans h_norm_lam_inv_τ' (mul_le_mul_of_nonneg_left h_exp_mono_τ' (by norm_num))
  -- M ≤ 1/(2δ), so π·M ≤ π/(2δ).
  have h_M_le_inv_2δ : M ≤ 1/(2*δ) := by
    rw [le_div_iff₀ h_2δ_pos]
    have h_step : δ * (2 * M) ≤ (1/(2*M)) * (2 * M) :=
      mul_le_mul_of_nonneg_right hδ_le_inv_2M (le_of_lt h_2M_pos)
    rw [div_mul_cancel₀ _ (ne_of_gt h_2M_pos)] at h_step
    linarith
  have h_pi_gt_one : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have h_pi_inv_2δ_ge_pi_M : Real.pi * M ≤ Real.pi * (1/(2*δ)) :=
    mul_le_mul_of_nonneg_left h_M_le_inv_2δ (le_of_lt Real.pi_pos)
  have h_L_lt_pi_M : L < Real.pi * M := by
    calc L ≤ M := hL_le_M
      _ = 1 * M := by ring
      _ < Real.pi * M := mul_lt_mul_of_pos_right h_pi_gt_one hM_pos
  have h_L_lt_pi_inv_2δ : L < Real.pi * (1/(2*δ)) :=
    lt_of_lt_of_le h_L_lt_pi_M h_pi_inv_2δ_ge_pi_M
  have h_exp_lt : Real.exp (-Real.pi * (1/(2*δ))) < Real.exp (-L) := by
    apply Real.exp_lt_exp.mpr; linarith
  have h_B_plus_two_pos : (0 : ℝ) < B + 2 := by linarith
  have h_exp_neg_L : Real.exp (-L) = 1 / (160000 * (B + 2)) := by
    rw [hL_def]
    rw [show -Real.log (160000 * (B + 2)) = Real.log ((160000 * (B + 2))⁻¹) from
      (Real.log_inv _).symm]
    rw [Real.exp_log (by positivity : (0:ℝ) < (160000 * (B + 2))⁻¹)]
    rw [one_div]
  have h_final_bound : 160000 * Real.exp (-Real.pi * (1/(2*δ))) < 1 / (B + 2) := by
    calc 160000 * Real.exp (-Real.pi * (1/(2*δ)))
        < 160000 * Real.exp (-L) := mul_lt_mul_of_pos_left h_exp_lt (by norm_num)
      _ = 160000 * (1 / (160000 * (B + 2))) := by rw [h_exp_neg_L]
      _ = 1 / (B + 2) := by field_simp
  have h_strict_τ' : ‖modularLambdaH τ' - 1‖ < 1 / (B + 2) :=
    lt_of_le_of_lt h_bound_τ' h_final_bound
  -- Transfer to σ via conjugation.
  have h_norm_diff_σ : ‖modularLambdaH σ - 1‖ = ‖modularLambdaH τ' - 1‖ := by
    rw [h_conj_lam]
    rw [show starRingEnd ℂ (modularLambdaH σ) - 1 = starRingEnd ℂ (modularLambdaH σ - 1) by
      rw [map_sub, map_one]]
    rw [norm_conj]
  have h_strict_σ : ‖modularLambdaH σ - 1‖ < 1 / (B + 2) := by
    rw [h_norm_diff_σ]; exact h_strict_τ'
  -- T-action: λ(τ) = λ(σ + 1) = λ(σ)/(λ(σ) - 1).
  have h_T : modularLambdaH (σ + 1) = modularLambdaH σ / (modularLambdaH σ - 1) :=
    modularLambdaH_add_one_eq_div_sub_one hσ_im_pos
  have h_σ_plus_one : σ + 1 = τ := by simp [hσ_def]
  rw [h_σ_plus_one] at h_T
  -- λ(σ) - 1 ≠ 0 from λ(σ) ≠ 1.
  have h_lam_σ_sub_one_ne : modularLambdaH σ - 1 ≠ 0 :=
    sub_ne_zero.mpr (modularLambdaH_ne_one hσ_im_pos)
  -- |λ(σ)| ≥ 1 - ‖λ(σ) - 1‖.
  have h_lam_σ_norm_ge : 1 - ‖modularLambdaH σ - 1‖ ≤ ‖modularLambdaH σ‖ := by
    have h_rtri : ‖(1 : ℂ)‖ - ‖modularLambdaH σ‖ ≤ ‖(1 : ℂ) - modularLambdaH σ‖ :=
      norm_sub_norm_le (1 : ℂ) (modularLambdaH σ)
    have h_simp : (1 : ℂ) - modularLambdaH σ = -(modularLambdaH σ - 1) := by ring
    rw [norm_one, h_simp, norm_neg] at h_rtri
    linarith
  -- Now: |λ(τ)| = |λ(σ)| / |λ(σ) - 1|.
  have h_norm_lam_τ : ‖modularLambdaH τ‖ = ‖modularLambdaH σ‖ / ‖modularLambdaH σ - 1‖ := by
    rw [h_T, norm_div]
  -- We want |λ(τ)| > ‖w'‖.
  -- |λ(σ)| ≥ 1 - c, |λ(σ) - 1| < 1/(‖w'‖ + 2) where c = ‖λ(σ) - 1‖.
  -- |λ(σ)| / |λ(σ) - 1| ≥ (1 - c)/c > ‖w'‖ + 1 > ‖w'‖.
  set c : ℝ := ‖modularLambdaH σ - 1‖ with hc_def
  have hc_lt_B : c < 1 / (B + 2) := h_strict_σ
  have h_w'_plus_two_pos : (0 : ℝ) < ‖w'‖ + 2 := by
    have : (0 : ℝ) ≤ ‖w'‖ := norm_nonneg _
    linarith
  have h_div_le : 1 / (B + 2) ≤ 1 / (‖w'‖ + 2) :=
    one_div_le_one_div_of_le h_w'_plus_two_pos (by linarith)
  have hc_lt : c < 1 / (‖w'‖ + 2) := lt_of_lt_of_le hc_lt_B h_div_le
  have hc_pos : 0 < c := by
    rw [hc_def, norm_pos_iff]; exact h_lam_σ_sub_one_ne
  have h_one_minus_c_pos : 0 < 1 - c := by
    have : c < 1 := by
      have h_inv_pos : (0 : ℝ) < 1 / (‖w'‖ + 2) := by positivity
      have h_inv_lt_one : 1 / (‖w'‖ + 2) ≤ 1 := by
        rw [div_le_iff₀ h_w'_plus_two_pos]; linarith [norm_nonneg w']
      linarith
    linarith
  have h_lam_σ_norm_pos : 0 < ‖modularLambdaH σ‖ := by linarith [h_lam_σ_norm_ge]
  -- (1 - c)/c > ‖w'‖: equiv to (1 - c) > c·‖w'‖, i.e., 1 > c·(‖w'‖ + 1), i.e., c < 1/(‖w'‖ + 1).
  have h_w_plus_one_pos : (0 : ℝ) < ‖w'‖ + 1 := by linarith [norm_nonneg w']
  have hc_lt_inv : c < 1 / (‖w'‖ + 1) := by
    calc c < 1 / (‖w'‖ + 2) := hc_lt
      _ ≤ 1 / (‖w'‖ + 1) := by
        apply one_div_le_one_div_of_le h_w_plus_one_pos
        linarith
  have h_c_w_plus_one_lt_one : c * (‖w'‖ + 1) < 1 := by
    have := hc_lt_inv
    rw [lt_div_iff₀ h_w_plus_one_pos] at this
    linarith
  have h_norm_lam_τ_gt : ‖w'‖ < ‖modularLambdaH τ‖ := by
    rw [h_norm_lam_τ]
    rw [lt_div_iff₀ hc_pos]
    calc ‖w'‖ * c = c * ‖w'‖ := by ring
      _ < c * ‖w'‖ + (1 - c * (‖w'‖ + 1)) := by linarith [h_c_w_plus_one_lt_one]
      _ = 1 - c := by ring
      _ ≤ ‖modularLambdaH σ‖ := h_lam_σ_norm_ge
  -- λ(τ) = w' would give ‖λ(τ)‖ = ‖w'‖. Contradiction.
  rw [h_lam_eq] at h_norm_lam_τ_gt
  exact lt_irrefl _ h_norm_lam_τ_gt

set_option maxHeartbeats 400000 in
-- Cusp-1 case of the three-case arc nonvanishing (uniform version): the
-- reflection/conjugation machinery plus T-action elaborate slowly.
/-- Cusp-1 branch of `modularLambdaH_F_Y_arc_ne_uniform`: for `θ` near `0`
(below the returned threshold `θ_c`), conjugation symmetry plus the
`T`-action give `‖λ(arc)‖ > B ≥ ‖w'‖`. Thresholds depend only on `B`. -/
theorem modularLambdaH_F_Y_arc_ne_uniform_cusp_one_case {B : ℝ} (hB : 0 < B) :
    ∃ δ_c θ_c : ℝ, 0 < δ_c ∧ 0 < θ_c ∧ θ_c ≤ Real.pi / 4 ∧
    ∀ δ R₀ : ℝ, 0 < δ → δ ≤ δ_c → Real.sqrt (1 / 4 - δ ^ 2) < R₀ → R₀ < 1 / 2 →
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ θ_c → θ ≤ Real.pi →
      ∀ w' : ℂ, ‖w'‖ ≤ B →
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w' ≠ 0 := by
  -- K_1 for cusp 1: 160000·exp(-π·K_1) < 1/(B + 2).
  set L_1 : ℝ := Real.log (160000 * (B + 2)) with hL_1_def
  set K_1 : ℝ := max L_1 1 + 1 with hK_1_def
  have hK_1_pos : 0 < K_1 := by
    rw [hK_1_def]; have : 1 ≤ max L_1 1 := le_max_right _ _; linarith
  have hK_1_ge_one : 1 ≤ K_1 := by
    rw [hK_1_def]; have : 1 ≤ max L_1 1 := le_max_right _ _; linarith
  obtain ⟨δ_K_1, θ_K_1, hδ_K_1_pos, _hδ_K_1_le_quarter, hθ_K_1_pos, hθ_K_1_le_pi_4,
    h_cusp_1_bound⟩ :=
    modularLambdaH_F_Y_arc_im_inv_lower_cusp_0 K_1 hK_1_pos
  refine ⟨δ_K_1, θ_K_1, hδ_K_1_pos, hθ_K_1_pos, hθ_K_1_le_pi_4, ?_⟩
  intro δ R₀ hδ_pos hδ_le_δ_K_1 hR₀_lo hR₀_lt θ hθ_lo hθ_le hθ_hi w' hw'_B
  have hR₀_pos : 0 < R₀ := by have := Real.sqrt_nonneg (1/4 - δ^2); linarith
  set arc : ℂ := _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ
    with harc_def
  -- Assume λ(arc) = w' for contradiction.
  intro h_lam_eq_w
  have h_lam_arc_eq : modularLambdaH arc = w' := by
    linear_combination h_lam_eq_w
  have harc_im_pos : 0 < arc.im :=
    modularLambdaH_F_Y_arc_im_pos hδ_pos hR₀_pos.le hθ_lo hθ_hi
  -- arc(π - θ) is in [π - θ_K_1, π] (cusp 0 of arc).
  have hπθ_le : Real.pi - θ ≤ Real.pi := by linarith [hθ_lo]
  have hπθ_ge_θ_K_1 : Real.pi - θ_K_1 ≤ Real.pi - θ := by
    linarith [hθ_le]
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
  -- ‖λ(arc(π-θ)) - 1‖ ≤ 160000 · exp(-π · K_1) < 1/(B + 2).
  have h_exp_mono_πθ : Real.exp (-Real.pi * (-(arcπθ : ℂ)⁻¹).im) ≤
      Real.exp (-Real.pi * K_1) := by
    apply Real.exp_le_exp.mpr
    have := h_im_inv_πθ_ge
    rw [harcπθ_def] at this
    nlinarith [Real.pi_pos, this]
  have h_bound_πθ : ‖modularLambdaH arcπθ - 1‖ ≤ 160000 * Real.exp (-Real.pi * K_1) := by
    rw [h_norm_diff_πθ]
    exact le_trans h_norm_lam_inv_πθ (mul_le_mul_of_nonneg_left h_exp_mono_πθ (by norm_num))
  have h_B_plus_two_pos : (0 : ℝ) < B + 2 := by linarith
  have h_inv_pos : (0 : ℝ) < 1 / (B + 2) := by positivity
  -- 160000 · exp(-π K_1) < 1/(B+2) via exp_bound helper.
  have h_final_πθ : 160000 * Real.exp (-Real.pi * K_1) < 1 / (B + 2) := by
    have h_helper := modularLambdaH_F_Y_arc_ne_exp_bound_mul (B + 2) h_B_plus_two_pos
    have hK_1_eq : K_1 = max (Real.log (160000 * (B + 2))) 1 + 1 := by
      rw [hK_1_def, hL_1_def]
    rw [hK_1_eq]; exact h_helper
  have h_strict_πθ : ‖modularLambdaH arcπθ - 1‖ < 1 / (B + 2) :=
    lt_of_le_of_lt h_bound_πθ h_final_πθ
  -- Transfer to σ via conjugation.
  have h_norm_diff_σ : ‖modularLambdaH σ - 1‖ = ‖modularLambdaH arcπθ - 1‖ := by
    rw [h_conj_lam]
    rw [show starRingEnd ℂ (modularLambdaH σ) - 1 = starRingEnd ℂ (modularLambdaH σ - 1) by
      rw [map_sub, map_one]]
    rw [norm_conj]
  have h_strict_σ : ‖modularLambdaH σ - 1‖ < 1 / (B + 2) := by
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
  -- Show |λ(arc)| > ‖w'‖.
  set c : ℝ := ‖modularLambdaH σ - 1‖ with hc_def
  have hc_lt_B : c < 1 / (B + 2) := h_strict_σ
  have hc_pos : 0 < c := by
    rw [hc_def, norm_pos_iff]; exact h_lam_σ_sub_one_ne
  have h_w'_plus_two_pos : (0 : ℝ) < ‖w'‖ + 2 := by
    have : (0 : ℝ) ≤ ‖w'‖ := norm_nonneg _
    linarith
  have h_div_le : 1 / (B + 2) ≤ 1 / (‖w'‖ + 2) :=
    one_div_le_one_div_of_le h_w'_plus_two_pos (by linarith)
  have hc_lt : c < 1 / (‖w'‖ + 2) := lt_of_lt_of_le hc_lt_B h_div_le
  have h_lam_σ_ge : 1 - c ≤ ‖modularLambdaH σ‖ := by
    rw [hc_def]; exact h_lam_σ_norm_ge
  have h_norm_lam_arc_gt : ‖w'‖ < ‖modularLambdaH arc‖ := by
    rw [h_norm_lam_arc]
    exact modularLambdaH_F_Y_arc_cusp_1_norm_bound (norm_nonneg w') hc_pos hc_lt h_lam_σ_ge
  rw [h_lam_arc_eq] at h_norm_lam_arc_gt
  exact lt_irrefl _ h_norm_lam_arc_gt

set_option maxHeartbeats 400000 in
-- Cusp-0 case of the three-case arc nonvanishing (uniform version): the
-- S-action and exponential norm bounds elaborate slowly.
/-- Cusp-0 branch of `modularLambdaH_F_Y_arc_ne_uniform`: for `θ` near `π`
(above `π` minus the returned threshold `θ_c`), the `S`-action gives
`‖λ(arc) - 1‖ < ρ ≤ ‖w' - 1‖`. Thresholds depend only on `ρ`. -/
theorem modularLambdaH_F_Y_arc_ne_uniform_cusp_zero_case {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ_c θ_c : ℝ, 0 < δ_c ∧ 0 < θ_c ∧ θ_c ≤ Real.pi / 4 ∧
    ∀ δ R₀ : ℝ, 0 < δ → δ ≤ δ_c → Real.sqrt (1 / 4 - δ ^ 2) < R₀ → R₀ < 1 / 2 →
    ∀ θ : ℝ, 0 ≤ θ → Real.pi - θ_c ≤ θ → θ ≤ Real.pi →
      ∀ w' : ℂ, ρ ≤ ‖w' - 1‖ →
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w' ≠ 0 := by
  -- K_0 for cusp 0: 160000·exp(-π·K_0) < ρ.
  set L_0 : ℝ := Real.log (160000 / ρ) with hL_0_def
  set K_0 : ℝ := max L_0 1 + 1 with hK_0_def
  have hK_0_pos : 0 < K_0 := by
    rw [hK_0_def]
    have : 1 ≤ max L_0 1 := le_max_right _ _
    linarith
  have hK_0_ge_one : 1 ≤ K_0 := by
    rw [hK_0_def]
    have : 1 ≤ max L_0 1 := le_max_right _ _
    linarith
  obtain ⟨δ_K_0, θ_K_0, hδ_K_0_pos, _hδ_K_0_le_quarter, hθ_K_0_pos, hθ_K_0_le_pi_4,
    h_cusp_0_bound⟩ :=
    modularLambdaH_F_Y_arc_im_inv_lower_cusp_0 K_0 hK_0_pos
  refine ⟨δ_K_0, θ_K_0, hδ_K_0_pos, hθ_K_0_pos, hθ_K_0_le_pi_4, ?_⟩
  intro δ R₀ hδ_pos hδ_le_δ_K_0 hR₀_lo hR₀_lt θ hθ_lo hθ_in_cusp_0 hθ_hi w' hw'_ρ
  have hR₀_pos : 0 < R₀ := by have := Real.sqrt_nonneg (1/4 - δ^2); linarith
  set arc : ℂ := _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ
    with harc_def
  -- Assume λ(arc) = w' for contradiction.
  intro h_lam_eq_w
  have h_lam_arc_eq : modularLambdaH arc = w' := by
    linear_combination h_lam_eq_w
  have harc_im_pos : 0 < arc.im :=
    modularLambdaH_F_Y_arc_im_pos hδ_pos hR₀_pos.le hθ_lo hθ_hi
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
  -- 160000 · exp(-π · K_0) < ρ via exp_bound helper.
  have h_final_bound : 160000 * Real.exp (-Real.pi * K_0) < ρ := by
    have h_helper := modularLambdaH_F_Y_arc_ne_exp_bound_div ρ hρ
    have hK_0_eq : K_0 = max (Real.log (160000 / ρ)) 1 + 1 := by
      rw [hK_0_def, hL_0_def]
    rw [hK_0_eq]; exact h_helper
  have h_strict : ‖modularLambdaH arc - 1‖ < ρ :=
    lt_of_le_of_lt h_bound h_final_bound
  have h_strict' : ‖modularLambdaH arc - 1‖ < ‖w' - 1‖ :=
    lt_of_lt_of_le h_strict hw'_ρ
  rw [h_lam_arc_eq] at h_strict'
  exact lt_irrefl _ h_strict'

set_option maxHeartbeats 400000 in
-- Middle case of the three-case arc nonvanishing (uniform version): the
-- Lipschitz-ball extraction and semicircle computations elaborate slowly.
/-- Middle branch of `modularLambdaH_F_Y_arc_ne_uniform`: for
`θ ∈ [θ_0, π - θ_0]`, the Lipschitz bound for `Im λ` near the unit
semicircle forces `|Im λ(arc)| < μ ≤ w'.im`. The threshold
`δ_mid ≤ 1/4` depends only on `μ` and `θ_0`. -/
theorem modularLambdaH_F_Y_arc_ne_uniform_middle_case {μ θ_0 : ℝ} (hμ : 0 < μ)
    (hθ_0_pos : 0 < θ_0) (hθ_0_lt_pi_2 : θ_0 < Real.pi / 2) :
    ∃ δ_mid : ℝ, 0 < δ_mid ∧ δ_mid ≤ 1 / 4 ∧
    ∀ δ R₀ : ℝ, 0 < δ → δ ≤ δ_mid → Real.sqrt (1 / 4 - δ ^ 2) < R₀ → R₀ < 1 / 2 →
    ∀ θ : ℝ, θ_0 ≤ θ → θ ≤ Real.pi - θ_0 →
      ∀ w' : ℂ, μ ≤ w'.im →
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w' ≠ 0 := by
  have hθ_0_lt_pi : θ_0 < Real.pi := by linarith [Real.pi_pos]
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
  set δ_M : ℝ := μ / (4 * M) with hδ_M_def
  have hδ_M_pos : 0 < δ_M := by rw [hδ_M_def]; positivity
  refine ⟨min (Real.sin θ_0 / 4) (min δ_M (1/4)),
    lt_min (by positivity) (lt_min hδ_M_pos (by norm_num)),
    le_trans (min_le_right _ _) (min_le_right _ _), ?_⟩
  intro δ R₀ hδ_pos hδ_le hR₀_lo hR₀_lt θ hθ_in_middle_lo hθ_in_middle_hi w' hw'_im
  -- Extract individual constraints on δ.
  have hδ_le_sin_θ_0_quarter : δ ≤ Real.sin θ_0 / 4 :=
    le_trans hδ_le (min_le_left _ _)
  have hδ_le_δ_M : δ ≤ δ_M :=
    le_trans hδ_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ_le_quarter : δ ≤ 1/4 :=
    le_trans hδ_le (le_trans (min_le_right _ _) (min_le_right _ _))
  have hR₀_pos : 0 < R₀ := by have := Real.sqrt_nonneg (1/4 - δ^2); linarith
  set arc : ℂ := _root_.circleMap ((1/2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ
    with harc_def
  -- Assume λ(arc) = w' for contradiction.
  intro h_lam_eq_w
  have h_lam_arc_eq : modularLambdaH arc = w' := by
    linear_combination h_lam_eq_w
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
  -- δ ≤ μ/(4M) (from hδ_le_δ_M and δ_M definition).
  have hδ_le_wim_4M : δ ≤ μ / (4*M) := by
    have h_δ_M_eq : δ_M = μ / (4*M) := hδ_M_def
    linarith [hδ_le_δ_M, h_δ_M_eq]
  -- Apply the pure polynomial helper.
  have h_M_bound : M * (δ + (1/2 - R₀)) < μ :=
    modularLambdaH_F_Y_arc_middle_poly_bound hM_pos hδ_pos hδ_le_quarter
      hδ_le_wim_4M h_half_minus_R₀ hμ
  -- λ(arc) = w' gives Im λ(arc) = w'.im. |Im λ(arc)| = w'.im (since w'.im ≥ μ > 0).
  -- But |Im λ(arc)| ≤ M · (δ + 1/2 - R₀) < μ ≤ w'.im. Contradiction.
  rw [h_lam_arc_eq] at h_im_bound
  have h_w'_im_pos : 0 < w'.im := lt_of_lt_of_le hμ hw'_im
  have h_abs_w_im : |w'.im| = w'.im := abs_of_pos h_w'_im_pos
  rw [h_abs_w_im] at h_im_bound
  linarith [h_M_bound, h_im_bound, hw'_im]

-- Three-case arc nonvanishing (middle Lipschitz + cusp-0 + cusp-1 conjugation),
-- segment-uniform version: thresholds depend only on (μ, B, ρ).
/-- Segment-uniform variant of `modularLambdaH_F_Y_arc_ne`: the threshold
`δ_u` depends only on `μ ≤ w'.im`, `‖w'‖ ≤ B`, and `ρ ≤ ‖w' - 1‖`. -/
theorem modularLambdaH_F_Y_arc_ne_uniform {μ B ρ : ℝ} (hμ : 0 < μ) (hB : 0 < B) (hρ : 0 < ρ) :
    ∃ δ_u : ℝ, 0 < δ_u ∧ δ_u < 1 / 2 ∧
    ∀ δ R₀ : ℝ, 0 < δ → δ ≤ δ_u → Real.sqrt (1 / 4 - δ ^ 2) < R₀ → R₀ < 1 / 2 →
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
      ∀ w' : ℂ, μ ≤ w'.im → ‖w'‖ ≤ B → ρ ≤ ‖w' - 1‖ →
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w' ≠ 0 := by
  -- Three-case proof, assembled from the three case helpers above:
  -- (a) Middle θ ∈ [θ_0, π - θ_0]: Helper 8.3-style bound on |Im λ|.
  -- (b) Cusp 0 θ ∈ (π - θ_K_0, π]: S-action + norm bound; ‖λ - 1‖ < ρ ≤ ‖w' - 1‖.
  -- (c) Cusp 1 θ ∈ [0, θ_K_1): conjugation + T; |λ| > B ≥ ‖w'‖.
  -- The three pieces of `δ_u` come from these three regimes.
  obtain ⟨δ_K_0, θ_K_0, hδ_K_0_pos, hθ_K_0_pos, hθ_K_0_le_pi_4, h_cusp_0⟩ :=
    modularLambdaH_F_Y_arc_ne_uniform_cusp_zero_case hρ
  obtain ⟨δ_K_1, θ_K_1, hδ_K_1_pos, hθ_K_1_pos, _hθ_K_1_le_pi_4, h_cusp_1⟩ :=
    modularLambdaH_F_Y_arc_ne_uniform_cusp_one_case hB
  -- θ_0 := min(θ_K_0, θ_K_1).
  set θ_0 : ℝ := min θ_K_0 θ_K_1
  have hθ_0_pos : 0 < θ_0 := lt_min hθ_K_0_pos hθ_K_1_pos
  have hθ_0_le_θ_K_0 : θ_0 ≤ θ_K_0 := min_le_left _ _
  have hθ_0_le_θ_K_1 : θ_0 ≤ θ_K_1 := min_le_right _ _
  have hθ_0_lt_pi_2 : θ_0 < Real.pi / 2 := by
    have h1 : θ_0 ≤ Real.pi / 4 := le_trans hθ_0_le_θ_K_0 hθ_K_0_le_pi_4
    linarith [Real.pi_pos]
  obtain ⟨δ_mid, hδ_mid_pos, hδ_mid_le_quarter, h_middle⟩ :=
    modularLambdaH_F_Y_arc_ne_uniform_middle_case hμ hθ_0_pos hθ_0_lt_pi_2
  refine ⟨min (min δ_K_0 δ_K_1) δ_mid,
    lt_min (lt_min hδ_K_0_pos hδ_K_1_pos) hδ_mid_pos, ?_, ?_⟩
  · have h1 : min (min δ_K_0 δ_K_1) δ_mid ≤ δ_mid := min_le_right _ _
    linarith
  intro δ R₀ hδ_pos hδ_le hR₀_lo hR₀_lt θ hθ_lo hθ_hi w' hw'_im hw'_B hw'_ρ
  -- Extract individual constraints on δ.
  have hδ_le_δ_K_0 : δ ≤ δ_K_0 :=
    le_trans hδ_le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ_le_δ_K_1 : δ ≤ δ_K_1 :=
    le_trans hδ_le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ_le_δ_mid : δ ≤ δ_mid := le_trans hδ_le (min_le_right _ _)
  -- Case split on θ position.
  by_cases h_θ_le_θ_0 : θ ≤ θ_0
  · -- Cusp 1 case: θ ∈ [0, θ_0] ⊆ [0, θ_K_1].
    exact h_cusp_1 δ R₀ hδ_pos hδ_le_δ_K_1 hR₀_lo hR₀_lt θ hθ_lo
      (le_trans h_θ_le_θ_0 hθ_0_le_θ_K_1) hθ_hi w' hw'_B
  · push Not at h_θ_le_θ_0
    -- θ > θ_0. Check if θ ≥ π - θ_0.
    by_cases h_θ_ge : Real.pi - θ_0 ≤ θ
    · -- Cusp 0 case: θ ∈ [π - θ_0, π] ⊆ [π - θ_K_0, π].
      exact h_cusp_0 δ R₀ hδ_pos hδ_le_δ_K_0 hR₀_lo hR₀_lt θ hθ_lo
        (by linarith [hθ_0_le_θ_K_0]) hθ_hi w' hw'_ρ
    · -- Middle case: θ ∈ (θ_0, π - θ_0).
      push Not at h_θ_ge
      exact h_middle δ R₀ hδ_pos hδ_le_δ_mid hR₀_lo hR₀_lt θ
        (le_of_lt h_θ_le_θ_0) (le_of_lt h_θ_ge) w' hw'_im


/-! ## Fibre uniqueness on `F^o`: the degree argument -/

set_option maxHeartbeats 400000 in
-- Long single-declaration assembly of the degree argument (many large integral terms).
/-- **Uniqueness of the `F°`-preimage (degree-argument bootstrap).** Proved by
transporting the F_Y zero count along a `w`-segment to the deep-cusp reference
value, where the fibre is a provably unique simple point. -/
theorem modularLambdaH_F_interior_preimage_unique
    {w : ℂ} (hw : 0 < w.im) {τ₁ τ₂ : ℂ}
    (h₁_in : τ₁ ∈ Gamma2FundamentalDomainInterior)
    (h₂_in : τ₂ ∈ Gamma2FundamentalDomainInterior)
    (h₁_eq : modularLambdaH τ₁ = w) (h₂_eq : modularLambdaH τ₂ = w) :
    τ₁ = τ₂ := by
  by_contra h_τ_ne
  -- ================== A. deep-cusp reference value ==================
  obtain ⟨w_ref, τ_ref, hw_ref_im, _hτ_ref_in, _hτ_ref_eq, hτ_ref_deriv, hτ_ref_unique⟩ :=
    modularLambdaH_cusp_reference_value
  -- ================== B. segment bounds ==================
  obtain ⟨μ, hμ_pos, hμ_le_w_im, hμ_le_wref_im⟩ :
      ∃ m : ℝ, 0 < m ∧ m ≤ w.im ∧ m ≤ w_ref.im :=
    ⟨min w.im w_ref.im, lt_min hw hw_ref_im, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨B, hB_pos, hB_ge_w, hB_ge_wref⟩ :
      ∃ b : ℝ, 0 < b ∧ ‖w‖ ≤ b ∧ ‖w_ref‖ ≤ b :=
    ⟨max ‖w‖ ‖w_ref‖,
      lt_of_lt_of_le (lt_of_lt_of_le hw (Complex.im_le_norm w)) (le_max_left _ _),
      le_max_left _ _, le_max_right _ _⟩
  -- `Im z ≥ μ` forces `‖z − 1‖ ≥ μ`.
  have h_im_to_sub_one : ∀ z : ℂ, μ ≤ z.im → μ ≤ ‖z - 1‖ := by
    intro z hz
    have h1 : (z - 1).im = z.im := by rw [Complex.sub_im, Complex.one_im, sub_zero]
    calc μ ≤ (z - 1).im := by rw [h1]; exact hz
      _ ≤ ‖z - 1‖ := Complex.im_le_norm _
  have hw_sub_one : μ ≤ ‖w - 1‖ := h_im_to_sub_one w hμ_le_w_im
  have hw_ref_sub_one : μ ≤ ‖w_ref - 1‖ := h_im_to_sub_one w_ref hμ_le_wref_im
  -- Segment-point bounds (i): imaginary part.
  have h_seg_im : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      μ ≤ ((1 - (s : ℂ)) * w + (s : ℂ) * w_ref).im := by
    intro s hs
    have h_im : ((1 - (s : ℂ)) * w + (s : ℂ) * w_ref).im
        = (1 - s) * w.im + s * w_ref.im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h_im]
    have hP : 0 ≤ (1 - s) * (w.im - μ) :=
      mul_nonneg (by linarith [hs.2]) (by linarith [hμ_le_w_im])
    have hQ : 0 ≤ s * (w_ref.im - μ) :=
      mul_nonneg hs.1 (by linarith [hμ_le_wref_im])
    nlinarith [hP, hQ]
  -- Segment-point bounds (ii): norm.
  have h_seg_norm : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 - (s : ℂ)) * w + (s : ℂ) * w_ref‖ ≤ B := by
    intro s hs
    have h_tri := norm_add_le ((1 - (s : ℂ)) * w) ((s : ℂ) * w_ref)
    have h1 : ‖(1 - (s : ℂ)) * w‖ = (1 - s) * ‖w‖ := by
      rw [norm_mul]
      congr 1
      rw [show (1 : ℂ) - (s : ℂ) = ((1 - s : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
    have h2 : ‖(s : ℂ) * w_ref‖ = s * ‖w_ref‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    rw [h1, h2] at h_tri
    have hA := mul_le_mul_of_nonneg_left hB_ge_w (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s)
    have hC := mul_le_mul_of_nonneg_left hB_ge_wref hs.1
    calc ‖(1 - (s : ℂ)) * w + (s : ℂ) * w_ref‖
        ≤ (1 - s) * ‖w‖ + s * ‖w_ref‖ := h_tri
      _ ≤ (1 - s) * B + s * B := add_le_add hA hC
      _ = B := by ring
  -- Segment-point bounds (iii): distance to `1`.
  have h_seg_sub_one : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      μ ≤ ‖(1 - (s : ℂ)) * w + (s : ℂ) * w_ref - 1‖ :=
    fun s hs => h_im_to_sub_one _ (h_seg_im s hs)
  -- ================== C. thresholds and region parameters ==================
  obtain ⟨δ_bl, hδ_bl_pos, _hδ_bl_lt, h_bl_prop⟩ :=
    modularLambdaH_F_Y_bot_left_strip_ne_uniform hμ_pos
  obtain ⟨δ_br, hδ_br_pos, _hδ_br_lt, h_br_prop⟩ :=
    modularLambdaH_F_Y_bot_right_strip_ne_uniform hB_pos
  obtain ⟨δ_arc, hδ_arc_pos, _hδ_arc_lt, h_arc_prop⟩ :=
    modularLambdaH_F_Y_arc_ne_uniform hμ_pos hB_pos hμ_pos
  obtain ⟨Y₀, _hY₀_ge_one, hY₀_prop⟩ := modularLambdaH_top_edge_norm_lt_uniform hμ_pos
  obtain ⟨δ_max, hδ_max_pos, hδ_max_le_quarter, hδ_max_le_bl, hδ_max_le_br, hδ_max_le_arc⟩ :
      ∃ δ_m : ℝ, 0 < δ_m ∧ δ_m ≤ 1 / 4 ∧ δ_m ≤ δ_bl ∧ δ_m ≤ δ_br ∧ δ_m ≤ δ_arc :=
    ⟨min (min δ_bl δ_br) (min δ_arc (1 / 4)),
      lt_min (lt_min hδ_bl_pos hδ_br_pos) (lt_min hδ_arc_pos (by norm_num)),
      le_trans (min_le_right _ _) (min_le_right _ _),
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _),
      le_trans (min_le_right _ _) (min_le_left _ _)⟩
  obtain ⟨δ, Y_base, R₀, hδ_pos, hδ_le_δ_max, hδ_lt_τ₁_im, hδ_lt_τ₂_im,
    hδ_lt_Y_base, hτ₁_im_lt_Y_base, hτ₂_im_lt_Y_base,
    hR₀_pos, hR₀_lt, h_δR_lt_Y_base, hR₀_lo, hτ₁_norm_gt, hτ₂_norm_gt⟩ :=
    modularLambdaH_F_Y_params_exist_arc hw h₁_in h₂_in hδ_max_pos hδ_max_le_quarter
  obtain ⟨Y, hY_ge_base, hY_ge_Y₀⟩ : ∃ Y : ℝ, Y_base ≤ Y ∧ Y₀ ≤ Y :=
    ⟨max Y_base Y₀, le_max_left _ _, le_max_right _ _⟩
  have hδ_lt_Y : δ < Y := lt_of_lt_of_le hδ_lt_Y_base hY_ge_base
  have hτ₁_im_lt_Y : τ₁.im < Y := lt_of_lt_of_le hτ₁_im_lt_Y_base hY_ge_base
  have hτ₂_im_lt_Y : τ₂.im < Y := lt_of_lt_of_le hτ₂_im_lt_Y_base hY_ge_base
  have h_δR_lt_Y : δ + R₀ < Y := lt_of_lt_of_le h_δR_lt_Y_base hY_ge_base
  have hδ_le_δ_bl : δ ≤ δ_bl := le_trans hδ_le_δ_max hδ_max_le_bl
  have hδ_le_δ_br : δ ≤ δ_br := le_trans hδ_le_δ_max hδ_max_le_br
  have hδ_le_δ_arc : δ ≤ δ_arc := le_trans hδ_le_δ_max hδ_max_le_arc
  have hδ_le_quarter : δ ≤ 1 / 4 := le_trans hδ_le_δ_max hδ_max_le_quarter
  -- Coverage trick: the bottom edge intervals lie inside the cascade strips.
  have h_half_minus_R₀ : 1 / 2 - R₀ ≤ 2 * δ ^ 2 :=
    modularLambdaH_F_Y_arc_half_minus_R₀_bound hδ_pos hδ_le_quarter hR₀_lo hR₀_lt hR₀_pos
  have h_2δ_sq_le_δ : 2 * δ ^ 2 ≤ δ := by nlinarith [hδ_pos.le, hδ_le_quarter]
  have h_half_minus_R₀_le_δ : 1 / 2 - R₀ ≤ δ := le_trans h_half_minus_R₀ h_2δ_sq_le_δ
  -- ================== D. segment-uniform boundary facts ==================
  have hg_bot_left_u : ∀ w' : ℂ, μ ≤ ‖w' - 1‖ → ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w' ≠ 0 := by
    intro w' hw' x hx
    exact h_bl_prop δ hδ_pos hδ_le_δ_bl x hx.1 (le_trans hx.2 h_half_minus_R₀_le_δ) w' hw'
  have hg_bot_right_u : ∀ w' : ℂ, ‖w'‖ ≤ B → ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w' ≠ 0 := by
    intro w' hw' x hx
    refine h_br_prop δ hδ_pos hδ_le_δ_br x ?_ hx.2 w' hw'
    linarith [hx.1, h_half_minus_R₀_le_δ]
  have hg_top_u : ∀ w' : ℂ, μ ≤ w'.im → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w' ≠ 0 := by
    intro w' hw'_im x hx h_eq0
    have h_norm_lt : ‖modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I)‖ < μ :=
      hY₀_prop Y hY_ge_Y₀ x hx.1 hx.2
    have h_lam_eq : modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) = w' := by
      linear_combination h_eq0
    rw [h_lam_eq] at h_norm_lt
    linarith [Complex.im_le_norm w', hw'_im]
  have hg_right_u : ∀ w' : ℂ, 0 < w'.im → ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w' ≠ 0 := fun _ hw' _ hy =>
    modularLambdaH_F_Y_right_edge_ne hw' (lt_of_lt_of_le hδ_pos hy.1)
  have hg_left_u : ∀ w' : ℂ, 0 < w'.im → ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w' ≠ 0 := fun _ hw' _ hy =>
    modularLambdaH_F_Y_left_edge_ne hw' (lt_of_lt_of_le hδ_pos hy.1)
  have hg_arc_u : ∀ w' : ℂ, μ ≤ w'.im → ‖w'‖ ≤ B → μ ≤ ‖w' - 1‖ →
      ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w' ≠ 0 := by
    intro w' h1 h2 h3 θ hθ
    exact h_arc_prop δ R₀ hδ_pos hδ_le_δ_arc hR₀_lo hR₀_lt θ hθ.1 hθ.2 w' h1 h2 h3
  -- The six boundary facts at `w`.
  have hg_bot_left_w := hg_bot_left_u w hw_sub_one
  have hg_bot_right_w := hg_bot_right_u w hB_ge_w
  have hg_top_w := hg_top_u w hμ_le_w_im
  have hg_right_w := hg_right_u w hw
  have hg_left_w := hg_left_u w hw
  have hg_arc_w := hg_arc_u w hμ_le_w_im hB_ge_w hw_sub_one
  -- The six boundary facts at `w_ref`.
  have hg_bot_left_wr := hg_bot_left_u w_ref hw_ref_sub_one
  have hg_bot_right_wr := hg_bot_right_u w_ref hB_ge_wref
  have hg_top_wr := hg_top_u w_ref hμ_le_wref_im
  have hg_right_wr := hg_right_u w_ref hw_ref_im
  have hg_left_wr := hg_left_u w_ref hw_ref_im
  have hg_arc_wr := hg_arc_u w_ref hμ_le_wref_im hB_ge_wref hw_ref_sub_one
  -- Transport hypothesis: the image curve avoids the whole segment.
  have h_avoid : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) ≠
        (1 - (s : ℂ)) * w + (s : ℂ) * w_ref := by
    intro s hs t ht
    have h_ne := F_Y_image_curve_ne_zero (w := (1 - (s : ℂ)) * w + (s : ℂ) * w_ref)
      hR₀_pos hR₀_lt hδ_lt_Y.le
      (hg_bot_left_u _ (h_seg_sub_one s hs))
      (hg_bot_right_u _ (h_seg_norm s hs))
      (hg_top_u _ (h_seg_im s hs))
      (hg_right_u _ (lt_of_lt_of_le hμ_pos (h_seg_im s hs)))
      (hg_left_u _ (lt_of_lt_of_le hμ_pos (h_seg_im s hs)))
      (hg_arc_u _ (h_seg_im s hs) (h_seg_norm s hs) (h_seg_sub_one s hs))
      t ht
    exact sub_ne_zero.mp h_ne
  -- ================== F. identity chain N(w) = N(w_ref) ==================
  have h_div_w := modularLambdaH_F_Y_AP_integral_eq_divisor_sum
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_w hg_bot_right_w hg_top_w hg_right_w hg_left_w hg_arc_w
  have h_div_wr := modularLambdaH_F_Y_AP_integral_eq_divisor_sum
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_wr hg_bot_right_wr hg_top_wr hg_right_wr hg_left_wr hg_arc_wr
  have h_LHS_w := modularLambdaH_F_Y_image_curve_LHS_eq_pathContourIntegral
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_w hg_bot_right_w hg_top_w hg_right_w hg_left_w hg_arc_w
  have h_LHS_wr := modularLambdaH_F_Y_image_curve_LHS_eq_pathContourIntegral
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_wr hg_bot_right_wr hg_top_wr hg_right_wr hg_left_wr hg_arc_wr
  have h_transport := modularLambdaH_F_Y_pathContourIntegral_eq_of_segment_avoids
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_avoid
  have h_count_cast :
      ((∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat : ℂ) =
      ((∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w_ref)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat : ℂ) := by
    rw [← h_div_w, ← h_div_wr, h_LHS_w, h_LHS_wr, h_transport]
  have h_count_eq :
      (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat =
      (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w_ref)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat := by
    exact_mod_cast h_count_cast
  -- ================== G. count at w_ref is at most one ==================
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
  -- Any zero of `λ − w_ref` in the truncated region is `τ_ref`.
  have h_unique_δ : ∀ z ∈ (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
      Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀,
      (fun τ => modularLambdaH τ - w_ref) z = 0 → z = τ_ref := by
    intro z hz h_gz0
    have h_gz : modularLambdaH z - w_ref = 0 := h_gz0
    have h_lam_eq : modularLambdaH z = w_ref := sub_eq_zero.mp h_gz
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
      exact hg_left_wr z.im hz_im (by rw [← h_z_eq]; exact h_gz)
    -- Right edge excluded.
    by_cases h_re_1 : z.re = 1
    · exfalso
      have h_z_eq : z = (1 : ℂ) + (z.im : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, h_re_1]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
      exact hg_right_wr z.im hz_im (by rw [← h_z_eq]; exact h_gz)
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
        exact hg_bot_right_wr z.re (Set.mem_Icc.mpr ⟨by linarith, hz_re.2⟩)
          (by rw [← h_z_eq]; exact h_gz)
      · rw [h_abs_eq] at hz_dist
        exact hg_bot_left_wr z.re (Set.mem_Icc.mpr ⟨hz_re.1, by linarith⟩)
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
      exact hg_arc_wr ((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg)
        (Set.mem_Icc.mpr ⟨hθ_nonneg, hθ_le_pi⟩) (by rw [← h_z_eq]; exact h_gz)
    · -- Strictly interior: `z ∈ F°`, so `z = τ_ref` by the reference uniqueness.
      have h_im_gt : δ < z.im := lt_of_le_of_ne hz_im.1 (Ne.symm h_im_δ)
      have h_re_gt : 0 < z.re := lt_of_le_of_ne hz_re.1 (Ne.symm h_re_0)
      have h_re_lt : z.re < 1 := lt_of_le_of_ne hz_re.2 h_re_1
      have h_semi : 1 < ‖2 * z - 1‖ :=
        F_Y_point_in_gamma2_semicircle_exterior hδ_pos hR₀_lo h_im_gt h_arc_gt
      exact hτ_ref_unique z ⟨lt_trans hδ_pos h_im_gt, h_re_gt, h_re_lt, h_semi⟩ h_lam_eq
  have h_simple : (fun τ => modularLambdaH τ - w_ref) τ_ref = 0 →
      deriv (fun τ => modularLambdaH τ - w_ref) τ_ref ≠ 0 := by
    intro _
    have h_d : deriv (fun τ => modularLambdaH τ - w_ref) τ_ref
        = deriv modularLambdaH τ_ref := deriv_sub_const w_ref
    rw [h_d]
    exact hτ_ref_deriv
  have h_le_one : (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w_ref)
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat ≤ 1 := by
    have key := Complex.divisor_sum_toNat_le_one_of_unique_simple_zero_on_rectMinusUpperHalfDisk
      (fun τ => modularLambdaH τ - w_ref) 0 1 Y ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (by rw [he_im]; exact modularLambdaH_F_Y_analytic w_ref hδ_pos hδ_lt_Y hR₀_pos)
      (by rw [he_im]; exact h_unique_δ)
      h_simple
    rw [he_im] at key
    exact key
  -- ================== H. count at w is at least two ==================
  obtain ⟨_h₁_im_pos, h₁_re_lo, h₁_re_hi, _h₁_semi⟩ := h₁_in
  obtain ⟨_h₂_im_pos, h₂_re_lo, h₂_re_hi, _h₂_semi⟩ := h₂_in
  have hτ₁_mem : τ₁ ∈ (Set.Icc (0 : ℝ) 1 ×ℂ
      Set.Icc (((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im) Y) \
      Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ := by
    rw [he_im]
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      exact ⟨Set.mem_Icc.mpr ⟨h₁_re_lo.le, h₁_re_hi.le⟩,
        Set.mem_Icc.mpr ⟨hδ_lt_τ₁_im.le, hτ₁_im_lt_Y.le⟩⟩
    · simp only [Metric.mem_ball, Complex.dist_eq, not_lt]
      exact hτ₁_norm_gt.le
  have hτ₂_mem : τ₂ ∈ (Set.Icc (0 : ℝ) 1 ×ℂ
      Set.Icc (((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im) Y) \
      Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ := by
    rw [he_im]
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      exact ⟨Set.mem_Icc.mpr ⟨h₂_re_lo.le, h₂_re_hi.le⟩,
        Set.mem_Icc.mpr ⟨hδ_lt_τ₂_im.le, hτ₂_im_lt_Y.le⟩⟩
    · simp only [Metric.mem_ball, Complex.dist_eq, not_lt]
      exact hτ₂_norm_gt.le
  have hτ₁_zero : (fun τ => modularLambdaH τ - w) τ₁ = 0 := by
    change modularLambdaH τ₁ - w = 0
    rw [h₁_eq, sub_self]
  have hτ₂_zero : (fun τ => modularLambdaH τ - w) τ₂ = 0 := by
    change modularLambdaH τ₂ - w = 0
    rw [h₂_eq, sub_self]
  have h_two_le : 2 ≤ (∑ᶠ u, MeromorphicOn.divisor (fun τ => modularLambdaH τ - w)
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat := by
    have key := Complex.two_le_divisor_sum_toNat_of_two_zeros_on_rectMinusUpperHalfDisk
      (fun τ => modularLambdaH τ - w) 0 1 Y ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (by norm_num) hR₀_pos
      (by rw [he_re]; linarith)
      (by rw [he_re]; linarith)
      (by rw [he_im]; exact h_δR_lt_Y)
      (by rw [he_im]; exact modularLambdaH_F_Y_analytic w hδ_pos hδ_lt_Y hR₀_pos)
      (by
        rw [he_im]
        intro h0
        have h0' : modularLambdaH (((0 : ℝ) : ℂ) + (δ : ℂ) * Complex.I) - w = 0 := h0
        rw [Complex.ofReal_zero] at h0'
        exact hg_left_w δ (Set.mem_Icc.mpr ⟨le_refl δ, hδ_lt_Y.le⟩) h0')
      h_τ_ne hτ₁_mem hτ₁_zero hτ₂_mem hτ₂_zero
    rw [he_im] at key
    exact key
  omega

set_option maxHeartbeats 400000 in
-- Long single-declaration assembly of the degree argument (many large integral terms).
/-- **Nonvanishing of `λ'` at `F°`-preimages (degree-argument bootstrap).** A
vanishing derivative would make the preimage a double zero of `λ − w`, forcing
the F_Y zero count to be at least two; transporting the count along a
`w`-segment to the deep-cusp reference value caps it at one. -/
theorem modularLambdaH_F_interior_preimage_deriv_ne_zero
    {w : ℂ} (hw : 0 < w.im) {τ : ℂ}
    (h_in : τ ∈ Gamma2FundamentalDomainInterior)
    (h_eq : modularLambdaH τ = w) :
    deriv modularLambdaH τ ≠ 0 := by
  intro h_deriv_eq
  -- ================== A. deep-cusp reference value ==================
  obtain ⟨w_ref, τ_ref, hw_ref_im, _hτ_ref_in, _hτ_ref_eq, hτ_ref_deriv, hτ_ref_unique⟩ :=
    modularLambdaH_cusp_reference_value
  -- ================== B. segment bounds ==================
  obtain ⟨μ, hμ_pos, hμ_le_w_im, hμ_le_wref_im⟩ :
      ∃ m : ℝ, 0 < m ∧ m ≤ w.im ∧ m ≤ w_ref.im :=
    ⟨min w.im w_ref.im, lt_min hw hw_ref_im, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨B, hB_pos, hB_ge_w, hB_ge_wref⟩ :
      ∃ b : ℝ, 0 < b ∧ ‖w‖ ≤ b ∧ ‖w_ref‖ ≤ b :=
    ⟨max ‖w‖ ‖w_ref‖,
      lt_of_lt_of_le (lt_of_lt_of_le hw (Complex.im_le_norm w)) (le_max_left _ _),
      le_max_left _ _, le_max_right _ _⟩
  -- `Im z ≥ μ` forces `‖z − 1‖ ≥ μ`.
  have h_im_to_sub_one : ∀ z : ℂ, μ ≤ z.im → μ ≤ ‖z - 1‖ := by
    intro z hz
    have h1 : (z - 1).im = z.im := by rw [Complex.sub_im, Complex.one_im, sub_zero]
    calc μ ≤ (z - 1).im := by rw [h1]; exact hz
      _ ≤ ‖z - 1‖ := Complex.im_le_norm _
  have hw_sub_one : μ ≤ ‖w - 1‖ := h_im_to_sub_one w hμ_le_w_im
  have hw_ref_sub_one : μ ≤ ‖w_ref - 1‖ := h_im_to_sub_one w_ref hμ_le_wref_im
  -- Segment-point bounds (i): imaginary part.
  have h_seg_im : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      μ ≤ ((1 - (s : ℂ)) * w + (s : ℂ) * w_ref).im := by
    intro s hs
    have h_im : ((1 - (s : ℂ)) * w + (s : ℂ) * w_ref).im
        = (1 - s) * w.im + s * w_ref.im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h_im]
    have hP : 0 ≤ (1 - s) * (w.im - μ) :=
      mul_nonneg (by linarith [hs.2]) (by linarith [hμ_le_w_im])
    have hQ : 0 ≤ s * (w_ref.im - μ) :=
      mul_nonneg hs.1 (by linarith [hμ_le_wref_im])
    nlinarith [hP, hQ]
  -- Segment-point bounds (ii): norm.
  have h_seg_norm : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 - (s : ℂ)) * w + (s : ℂ) * w_ref‖ ≤ B := by
    intro s hs
    have h_tri := norm_add_le ((1 - (s : ℂ)) * w) ((s : ℂ) * w_ref)
    have h1 : ‖(1 - (s : ℂ)) * w‖ = (1 - s) * ‖w‖ := by
      rw [norm_mul]
      congr 1
      rw [show (1 : ℂ) - (s : ℂ) = ((1 - s : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
    have h2 : ‖(s : ℂ) * w_ref‖ = s * ‖w_ref‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    rw [h1, h2] at h_tri
    have hA := mul_le_mul_of_nonneg_left hB_ge_w (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s)
    have hC := mul_le_mul_of_nonneg_left hB_ge_wref hs.1
    calc ‖(1 - (s : ℂ)) * w + (s : ℂ) * w_ref‖
        ≤ (1 - s) * ‖w‖ + s * ‖w_ref‖ := h_tri
      _ ≤ (1 - s) * B + s * B := add_le_add hA hC
      _ = B := by ring
  -- Segment-point bounds (iii): distance to `1`.
  have h_seg_sub_one : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      μ ≤ ‖(1 - (s : ℂ)) * w + (s : ℂ) * w_ref - 1‖ :=
    fun s hs => h_im_to_sub_one _ (h_seg_im s hs)
  -- ================== C. thresholds and region parameters ==================
  obtain ⟨δ_bl, hδ_bl_pos, _hδ_bl_lt, h_bl_prop⟩ :=
    modularLambdaH_F_Y_bot_left_strip_ne_uniform hμ_pos
  obtain ⟨δ_br, hδ_br_pos, _hδ_br_lt, h_br_prop⟩ :=
    modularLambdaH_F_Y_bot_right_strip_ne_uniform hB_pos
  obtain ⟨δ_arc, hδ_arc_pos, _hδ_arc_lt, h_arc_prop⟩ :=
    modularLambdaH_F_Y_arc_ne_uniform hμ_pos hB_pos hμ_pos
  obtain ⟨Y₀, _hY₀_ge_one, hY₀_prop⟩ := modularLambdaH_top_edge_norm_lt_uniform hμ_pos
  obtain ⟨δ_max, hδ_max_pos, hδ_max_le_quarter, hδ_max_le_bl, hδ_max_le_br, hδ_max_le_arc⟩ :
      ∃ δ_m : ℝ, 0 < δ_m ∧ δ_m ≤ 1 / 4 ∧ δ_m ≤ δ_bl ∧ δ_m ≤ δ_br ∧ δ_m ≤ δ_arc :=
    ⟨min (min δ_bl δ_br) (min δ_arc (1 / 4)),
      lt_min (lt_min hδ_bl_pos hδ_br_pos) (lt_min hδ_arc_pos (by norm_num)),
      le_trans (min_le_right _ _) (min_le_right _ _),
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _),
      le_trans (min_le_right _ _) (min_le_left _ _)⟩
  obtain ⟨δ, Y_base, R₀, hδ_pos, hδ_le_δ_max, hδ_lt_τ_im, _hδ_lt_τ_im',
    hδ_lt_Y_base, hτ_im_lt_Y_base, _hτ_im_lt_Y_base',
    hR₀_pos, hR₀_lt, h_δR_lt_Y_base, hR₀_lo, hτ_norm_gt, _hτ_norm_gt'⟩ :=
    modularLambdaH_F_Y_params_exist_arc hw h_in h_in hδ_max_pos hδ_max_le_quarter
  obtain ⟨Y, hY_ge_base, hY_ge_Y₀⟩ : ∃ Y : ℝ, Y_base ≤ Y ∧ Y₀ ≤ Y :=
    ⟨max Y_base Y₀, le_max_left _ _, le_max_right _ _⟩
  have hδ_lt_Y : δ < Y := lt_of_lt_of_le hδ_lt_Y_base hY_ge_base
  have hτ_im_lt_Y : τ.im < Y := lt_of_lt_of_le hτ_im_lt_Y_base hY_ge_base
  have h_δR_lt_Y : δ + R₀ < Y := lt_of_lt_of_le h_δR_lt_Y_base hY_ge_base
  have hδ_le_δ_bl : δ ≤ δ_bl := le_trans hδ_le_δ_max hδ_max_le_bl
  have hδ_le_δ_br : δ ≤ δ_br := le_trans hδ_le_δ_max hδ_max_le_br
  have hδ_le_δ_arc : δ ≤ δ_arc := le_trans hδ_le_δ_max hδ_max_le_arc
  have hδ_le_quarter : δ ≤ 1 / 4 := le_trans hδ_le_δ_max hδ_max_le_quarter
  -- Coverage trick: the bottom edge intervals lie inside the cascade strips.
  have h_half_minus_R₀ : 1 / 2 - R₀ ≤ 2 * δ ^ 2 :=
    modularLambdaH_F_Y_arc_half_minus_R₀_bound hδ_pos hδ_le_quarter hR₀_lo hR₀_lt hR₀_pos
  have h_2δ_sq_le_δ : 2 * δ ^ 2 ≤ δ := by nlinarith [hδ_pos.le, hδ_le_quarter]
  have h_half_minus_R₀_le_δ : 1 / 2 - R₀ ≤ δ := le_trans h_half_minus_R₀ h_2δ_sq_le_δ
  -- ================== D. segment-uniform boundary facts ==================
  have hg_bot_left_u : ∀ w' : ℂ, μ ≤ ‖w' - 1‖ → ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2 - R₀),
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w' ≠ 0 := by
    intro w' hw' x hx
    exact h_bl_prop δ hδ_pos hδ_le_δ_bl x hx.1 (le_trans hx.2 h_half_minus_R₀_le_δ) w' hw'
  have hg_bot_right_u : ∀ w' : ℂ, ‖w'‖ ≤ B → ∀ x ∈ Set.Icc (1 / 2 + R₀ : ℝ) 1,
      modularLambdaH ((x : ℂ) + (δ : ℂ) * Complex.I) - w' ≠ 0 := by
    intro w' hw' x hx
    refine h_br_prop δ hδ_pos hδ_le_δ_br x ?_ hx.2 w' hw'
    linarith [hx.1, h_half_minus_R₀_le_δ]
  have hg_top_u : ∀ w' : ℂ, μ ≤ w'.im → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) - w' ≠ 0 := by
    intro w' hw'_im x hx h_eq0
    have h_norm_lt : ‖modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I)‖ < μ :=
      hY₀_prop Y hY_ge_Y₀ x hx.1 hx.2
    have h_lam_eq : modularLambdaH ((x : ℂ) + (Y : ℂ) * Complex.I) = w' := by
      linear_combination h_eq0
    rw [h_lam_eq] at h_norm_lt
    linarith [Complex.im_le_norm w', hw'_im]
  have hg_right_u : ∀ w' : ℂ, 0 < w'.im → ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((1 : ℂ) + (y : ℂ) * Complex.I) - w' ≠ 0 := fun _ hw' _ hy =>
    modularLambdaH_F_Y_right_edge_ne hw' (lt_of_lt_of_le hδ_pos hy.1)
  have hg_left_u : ∀ w' : ℂ, 0 < w'.im → ∀ y ∈ Set.Icc δ Y,
      modularLambdaH ((0 : ℂ) + (y : ℂ) * Complex.I) - w' ≠ 0 := fun _ hw' _ hy =>
    modularLambdaH_F_Y_left_edge_ne hw' (lt_of_lt_of_le hδ_pos hy.1)
  have hg_arc_u : ∀ w' : ℂ, μ ≤ w'.im → ‖w'‖ ≤ B → μ ≤ ‖w' - 1‖ →
      ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w' ≠ 0 := by
    intro w' h1 h2 h3 θ hθ
    exact h_arc_prop δ R₀ hδ_pos hδ_le_δ_arc hR₀_lo hR₀_lt θ hθ.1 hθ.2 w' h1 h2 h3
  -- The six boundary facts at `w`.
  have hg_bot_left_w := hg_bot_left_u w hw_sub_one
  have hg_bot_right_w := hg_bot_right_u w hB_ge_w
  have hg_top_w := hg_top_u w hμ_le_w_im
  have hg_right_w := hg_right_u w hw
  have hg_left_w := hg_left_u w hw
  have hg_arc_w := hg_arc_u w hμ_le_w_im hB_ge_w hw_sub_one
  -- The six boundary facts at `w_ref`.
  have hg_bot_left_wr := hg_bot_left_u w_ref hw_ref_sub_one
  have hg_bot_right_wr := hg_bot_right_u w_ref hB_ge_wref
  have hg_top_wr := hg_top_u w_ref hμ_le_wref_im
  have hg_right_wr := hg_right_u w_ref hw_ref_im
  have hg_left_wr := hg_left_u w_ref hw_ref_im
  have hg_arc_wr := hg_arc_u w_ref hμ_le_wref_im hB_ge_wref hw_ref_sub_one
  -- Transport hypothesis: the image curve avoids the whole segment.
  have h_avoid : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) ≠
        (1 - (s : ℂ)) * w + (s : ℂ) * w_ref := by
    intro s hs t ht
    have h_ne := F_Y_image_curve_ne_zero (w := (1 - (s : ℂ)) * w + (s : ℂ) * w_ref)
      hR₀_pos hR₀_lt hδ_lt_Y.le
      (hg_bot_left_u _ (h_seg_sub_one s hs))
      (hg_bot_right_u _ (h_seg_norm s hs))
      (hg_top_u _ (h_seg_im s hs))
      (hg_right_u _ (lt_of_lt_of_le hμ_pos (h_seg_im s hs)))
      (hg_left_u _ (lt_of_lt_of_le hμ_pos (h_seg_im s hs)))
      (hg_arc_u _ (h_seg_im s hs) (h_seg_norm s hs) (h_seg_sub_one s hs))
      t ht
    exact sub_ne_zero.mp h_ne
  -- ================== F. identity chain N(w) = N(w_ref) ==================
  have h_div_w := modularLambdaH_F_Y_AP_integral_eq_divisor_sum
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_w hg_bot_right_w hg_top_w hg_right_w hg_left_w hg_arc_w
  have h_div_wr := modularLambdaH_F_Y_AP_integral_eq_divisor_sum
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_wr hg_bot_right_wr hg_top_wr hg_right_wr hg_left_wr hg_arc_wr
  have h_LHS_w := modularLambdaH_F_Y_image_curve_LHS_eq_pathContourIntegral
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_w hg_bot_right_w hg_top_w hg_right_w hg_left_w hg_arc_w
  have h_LHS_wr := modularLambdaH_F_Y_image_curve_LHS_eq_pathContourIntegral
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_δR_lt_Y
    hg_bot_left_wr hg_bot_right_wr hg_top_wr hg_right_wr hg_left_wr hg_arc_wr
  have h_transport := modularLambdaH_F_Y_pathContourIntegral_eq_of_segment_avoids
    hδ_pos hδ_lt_Y hR₀_pos hR₀_lt h_avoid
  have h_count_cast :
      ((∑ᶠ u, MeromorphicOn.divisor (fun τ' => modularLambdaH τ' - w)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat : ℂ) =
      ((∑ᶠ u, MeromorphicOn.divisor (fun τ' => modularLambdaH τ' - w_ref)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat : ℂ) := by
    rw [← h_div_w, ← h_div_wr, h_LHS_w, h_LHS_wr, h_transport]
  have h_count_eq :
      (∑ᶠ u, MeromorphicOn.divisor (fun τ' => modularLambdaH τ' - w)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat =
      (∑ᶠ u, MeromorphicOn.divisor (fun τ' => modularLambdaH τ' - w_ref)
        ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
          Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat := by
    exact_mod_cast h_count_cast
  -- ================== G. count at w_ref is at most one ==================
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
  -- Any zero of `λ − w_ref` in the truncated region is `τ_ref`.
  have h_unique_δ : ∀ z ∈ (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
      Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀,
      (fun τ' => modularLambdaH τ' - w_ref) z = 0 → z = τ_ref := by
    intro z hz h_gz0
    have h_gz : modularLambdaH z - w_ref = 0 := h_gz0
    have h_lam_eq : modularLambdaH z = w_ref := sub_eq_zero.mp h_gz
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
      exact hg_left_wr z.im hz_im (by rw [← h_z_eq]; exact h_gz)
    -- Right edge excluded.
    by_cases h_re_1 : z.re = 1
    · exfalso
      have h_z_eq : z = (1 : ℂ) + (z.im : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, h_re_1]
        · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
      exact hg_right_wr z.im hz_im (by rw [← h_z_eq]; exact h_gz)
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
        exact hg_bot_right_wr z.re (Set.mem_Icc.mpr ⟨by linarith, hz_re.2⟩)
          (by rw [← h_z_eq]; exact h_gz)
      · rw [h_abs_eq] at hz_dist
        exact hg_bot_left_wr z.re (Set.mem_Icc.mpr ⟨hz_re.1, by linarith⟩)
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
      exact hg_arc_wr ((z - ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I)).arg)
        (Set.mem_Icc.mpr ⟨hθ_nonneg, hθ_le_pi⟩) (by rw [← h_z_eq]; exact h_gz)
    · -- Strictly interior: `z ∈ F°`, so `z = τ_ref` by the reference uniqueness.
      have h_im_gt : δ < z.im := lt_of_le_of_ne hz_im.1 (Ne.symm h_im_δ)
      have h_re_gt : 0 < z.re := lt_of_le_of_ne hz_re.1 (Ne.symm h_re_0)
      have h_re_lt : z.re < 1 := lt_of_le_of_ne hz_re.2 h_re_1
      have h_semi : 1 < ‖2 * z - 1‖ :=
        F_Y_point_in_gamma2_semicircle_exterior hδ_pos hR₀_lo h_im_gt h_arc_gt
      exact hτ_ref_unique z ⟨lt_trans hδ_pos h_im_gt, h_re_gt, h_re_lt, h_semi⟩ h_lam_eq
  have h_simple : (fun τ' => modularLambdaH τ' - w_ref) τ_ref = 0 →
      deriv (fun τ' => modularLambdaH τ' - w_ref) τ_ref ≠ 0 := by
    intro _
    have h_d : deriv (fun τ' => modularLambdaH τ' - w_ref) τ_ref
        = deriv modularLambdaH τ_ref := deriv_sub_const w_ref
    rw [h_d]
    exact hτ_ref_deriv
  have h_le_one : (∑ᶠ u, MeromorphicOn.divisor (fun τ' => modularLambdaH τ' - w_ref)
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat ≤ 1 := by
    have key := Complex.divisor_sum_toNat_le_one_of_unique_simple_zero_on_rectMinusUpperHalfDisk
      (fun τ' => modularLambdaH τ' - w_ref) 0 1 Y ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (by rw [he_im]; exact modularLambdaH_F_Y_analytic w_ref hδ_pos hδ_lt_Y hR₀_pos)
      (by rw [he_im]; exact h_unique_δ)
      h_simple
    rw [he_im] at key
    exact key
  -- ================== H. count at w is at least two (double zero) ==================
  obtain ⟨_h_im_pos, h_re_lo, h_re_hi, _h_semi⟩ := h_in
  have hτ_mem : τ ∈ (Set.Icc (0 : ℝ) 1 ×ℂ
      Set.Icc (((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im) Y) \
      Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ := by
    rw [he_im]
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      exact ⟨Set.mem_Icc.mpr ⟨h_re_lo.le, h_re_hi.le⟩,
        Set.mem_Icc.mpr ⟨hδ_lt_τ_im.le, hτ_im_lt_Y.le⟩⟩
    · simp only [Metric.mem_ball, Complex.dist_eq, not_lt]
      exact hτ_norm_gt.le
  have hτ_zero : (fun τ' => modularLambdaH τ' - w) τ = 0 := by
    change modularLambdaH τ - w = 0
    rw [h_eq, sub_self]
  have hτ_deriv_zero : deriv (fun τ' => modularLambdaH τ' - w) τ = 0 := by
    have h_d : deriv (fun τ' => modularLambdaH τ' - w) τ
        = deriv modularLambdaH τ := deriv_sub_const w
    rw [h_d]
    exact h_deriv_eq
  have h_two_le : 2 ≤ (∑ᶠ u, MeromorphicOn.divisor (fun τ' => modularLambdaH τ' - w)
      ((Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc δ Y) \
        Metric.ball ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀) u).toNat := by
    have key := Complex.two_le_divisor_sum_toNat_of_double_zero_on_rectMinusUpperHalfDisk
      (fun τ' => modularLambdaH τ' - w) 0 1 Y ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (by norm_num) hR₀_pos
      (by rw [he_re]; linarith)
      (by rw [he_re]; linarith)
      (by rw [he_im]; exact h_δR_lt_Y)
      (by rw [he_im]; exact modularLambdaH_F_Y_analytic w hδ_pos hδ_lt_Y hR₀_pos)
      (by
        rw [he_im]
        intro h0
        have h0' : modularLambdaH (((0 : ℝ) : ℂ) + (δ : ℂ) * Complex.I) - w = 0 := h0
        rw [Complex.ofReal_zero] at h0'
        exact hg_left_w δ (Set.mem_Icc.mpr ⟨le_refl δ, hδ_lt_Y.le⟩) h0')
      hτ_mem hτ_zero hτ_deriv_zero
    rw [he_im] at key
    exact key
  omega

end NoWanderingDomains
