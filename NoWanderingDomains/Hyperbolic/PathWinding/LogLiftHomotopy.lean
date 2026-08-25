/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.PathWinding.WindingInvariance
import NoWanderingDomains.Hyperbolic.ModularFunction.GammaTwoInvariance

/-! # Log lifts and the homotopy of the image curve to a circle

Continuous logarithmic lifts for the universal cover `z ↦ exp z` of `ℂ \\ {0}` and the
homotopy of the `F_Y` image curve to a circle. Contains the FTC bridge for the
piecewise-C¹ image curve `λ ∘ ∂F_Y` (telescoping the six smooth boundary pieces), the
1D log lift on a closed real interval and its jointly continuous 2D-parametric
extension over a rectangle, and the explicit log-space homotopy taking `λ ∘ ∂F_Y` to a
small counterclockwise circle around any `w ∈ ℍ`. Concludes with the winding-integer
extraction lemmas: a closed lift differs by `K · 2πi`, an integer-valued affine
function on `[0, 1]` forces `K = 1` (via irrationality of `1/π`), and the explicit
homotopy closes at every intermediate `s` when `K = 1`.
-/

namespace NoWanderingDomains
open Complex MeasureTheory intervalIntegral

/-- **FTC bridge for the F_Y image curve (piecewise C¹).** For
`γ := λ ∘ F_Y_boundary_parameterization δ Y R₀`, which is piecewise C¹
on `Icc 0 6` (with corners at `t = 1, 2, 3, 4, 5`), the path contour
integral equals the log-lift boundary difference:
`Complex.pathContourIntegral γ 0 6 ((z − w)⁻¹) = L 6 − L 0`.

Proof outline: split `Icc 0 6` into the six smooth pieces; on each
piece `[i, i+1]`, the piece formula maps to `ℍ` on an open neighborhood
where `λ ∘ formula_i` is `ContDiffOn ℝ 1`; apply the `ContDiffOn` FTC
bridge per piece and telescope. -/
theorem pathContourIntegral_inv_eq_log_lift_diff_F_Y_image_curve
    {δ Y R₀ : ℝ} (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    {w : ℂ}
    (hγ_ne : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w ≠ 0)
    (L : ℝ → ℂ) (hL_cont : Continuous L)
    (hL_exp : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      Complex.exp (L t) =
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w) :
    Complex.pathContourIntegral
      (fun t => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t))
      0 6 (fun z => (z - w)⁻¹) = L 6 - L 0 := by
  -- The γ_full integrand.
  set u : ℝ → ℂ := fun t =>
    (modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w)⁻¹ *
      deriv (fun s => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ s)) t with hu_def
  -- λ facts on ℍ.
  have hH_open : IsOpen {τ : ℂ | 0 < τ.im} :=
    Complex.continuous_im.isOpen_preimage _ isOpen_Ioi
  have h_lam_deriv_cont : ContinuousOn (deriv modularLambdaH) {τ : ℂ | 0 < τ.im} :=
    (modularLambdaH_differentiableOn.analyticOnNhd hH_open).deriv.continuousOn
  have hst : IsScalarTower ℝ ℂ ℂ := IsScalarTower.right
  -- Per-piece engine: a globally differentiable formula matching the boundary
  -- parameterization on `[a, b]` and mapping `[a, b]` into `ℍ` yields the
  -- log-lift identity for the piece, plus interval-integrability of the
  -- γ_full integrand on the piece.
  have h_piece : ∀ (a b : ℝ) (formula formula' : ℝ → ℂ),
      (0 : ℝ) ≤ a → a ≤ b → b ≤ 6 →
      (∀ t : ℝ, HasDerivAt formula (formula' t) t) →
      Continuous formula' →
      (∀ t ∈ Set.Icc a b, 0 < (formula t).im) →
      (∀ t ∈ Set.Icc a b, F_Y_boundary_parameterization δ Y R₀ t = formula t) →
      (∫ t in a..b, u t) = L b - L a ∧
        IntervalIntegrable u MeasureTheory.volume a b := by
    intro a b formula formula' ha_lb hab hb_ub h_form_d h_form'_cont h_im_pos h_F_eq
    have h_form_cont : Continuous formula :=
      continuous_iff_continuousAt.mpr fun t => (h_form_d t).continuousAt
    set V : Set ℝ := {t : ℝ | 0 < (formula t).im} with hV_def
    have hV_open : IsOpen V :=
      (Complex.continuous_im.comp h_form_cont).isOpen_preimage _ isOpen_Ioi
    have h_Icc_V : Set.Icc a b ⊆ V := h_im_pos
    -- Chain rule on V via scomp with explicit scalar-tower instance.
    have h_chain : ∀ t ∈ V, HasDerivAt (fun s => modularLambdaH (formula s))
        (formula' t • deriv modularLambdaH (formula t)) t := by
      intro t ht
      have h_im : 0 < (formula t).im := ht
      have h_lam_d : HasDerivAt modularLambdaH
          (deriv modularLambdaH (formula t)) (formula t) :=
        (modularLambdaH_differentiableAt_of_im_pos h_im).hasDerivAt
      exact @HasDerivAt.scomp ℝ _ ℂ _ _ t ℂ _ _ _ hst _ _ _ _ h_lam_d (h_form_d t)
    have h_g_cont : ContinuousOn
        (fun t => formula' t • deriv modularLambdaH (formula t)) V := by
      refine ContinuousOn.smul h_form'_cont.continuousOn ?_
      refine h_lam_deriv_cont.comp h_form_cont.continuousOn ?_
      intro t ht; exact ht
    have h_diff_on : DifferentiableOn ℝ (fun s => modularLambdaH (formula s)) V :=
      fun t ht => (h_chain t ht).differentiableAt.differentiableWithinAt
    have h_deriv_eqOn : Set.EqOn (deriv (fun s => modularLambdaH (formula s)))
        (fun t => formula' t • deriv modularLambdaH (formula t)) V :=
      fun t ht => (h_chain t ht).deriv
    have h_deriv_cont : ContinuousOn
        (deriv (fun s => modularLambdaH (formula s))) V :=
      h_g_cont.congr h_deriv_eqOn
    have h_comp_cdiff : ContDiffOn ℝ 1 (fun s => modularLambdaH (formula s)) V := by
      rw [show (1 : WithTop ℕ∞) = 0 + 1 from (zero_add 1).symm,
        contDiffOn_succ_iff_deriv_of_isOpen hV_open]
      refine ⟨h_diff_on, ?_, ?_⟩
      · intro h_absurd; exact absurd h_absurd (by simp)
      · rw [contDiffOn_zero]; exact h_deriv_cont
    -- Nonvanishing and log-lift transfer for the formula curve.
    have h_piece_ne : ∀ t ∈ Set.Icc a b, modularLambdaH (formula t) ≠ w := by
      intro t ht h_eq_w
      have h_ht_06 : t ∈ Set.Icc (0 : ℝ) 6 :=
        ⟨le_trans ha_lb ht.1, le_trans ht.2 hb_ub⟩
      apply hγ_ne t h_ht_06
      rw [h_F_eq t ht, h_eq_w, sub_self]
    have h_piece_exp : ∀ t ∈ Set.Icc a b,
        Complex.exp (L t) = modularLambdaH (formula t) - w := by
      intro t ht
      have h_ht_06 : t ∈ Set.Icc (0 : ℝ) 6 :=
        ⟨le_trans ha_lb ht.1, le_trans ht.2 hb_ub⟩
      rw [hL_exp t h_ht_06, h_F_eq t ht]
    -- FTC for the formula curve.
    have h_FTC := pathContourIntegral_inv_eq_log_lift_diff_of_contDiffOn
      hab (fun t => modularLambdaH (formula t)) hV_open h_Icc_V h_comp_cdiff
      h_piece_ne L hL_cont h_piece_exp
    -- The formula integrand.
    set v : ℝ → ℂ := fun t =>
      (modularLambdaH (formula t) - w)⁻¹ *
        deriv (fun s => modularLambdaH (formula s)) t with hv_def
    have h_FTC_v : (∫ t in a..b, v t) = L b - L a := by
      rw [← h_FTC]
      unfold Complex.pathContourIntegral
      rfl
    -- v is continuous on the closed piece, hence interval-integrable.
    have h_v_cont : ContinuousOn v (Set.Icc a b) := by
      intro t ht
      have htV : t ∈ V := h_Icc_V ht
      refine ContinuousAt.continuousWithinAt ?_
      have h1 : ContinuousAt (fun s => modularLambdaH (formula s)) t :=
        (h_chain t htV).continuousAt
      have h2 : ContinuousAt (deriv (fun s => modularLambdaH (formula s))) t :=
        h_deriv_cont.continuousAt (hV_open.mem_nhds htV)
      refine ContinuousAt.mul ?_ h2
      refine ContinuousAt.inv₀ (h1.sub continuousAt_const) ?_
      exact sub_ne_zero.mpr (h_piece_ne t ht)
    have h_v_ii : IntervalIntegrable v MeasureTheory.volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hab]; exact h_v_cont
    -- u = v a.e. on uIoc a b: they can differ only at the corner b.
    have h_ae_imp : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        x ∈ Set.uIoc a b → u x = v x := by
      rw [MeasureTheory.ae_iff]
      refine MeasureTheory.measure_mono_null (t := {b}) ?_
        (MeasureTheory.measure_singleton b)
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      push Not at hx
      obtain ⟨hx_ioc, hx_ne⟩ := hx
      rw [Set.uIoc_of_le hab] at hx_ioc
      rw [Set.mem_singleton_iff]
      by_contra h_xb
      apply hx_ne
      have hx_oo : x ∈ Set.Ioo a b := ⟨hx_ioc.1, lt_of_le_of_ne hx_ioc.2 h_xb⟩
      have hx_icc : x ∈ Set.Icc a b := ⟨le_of_lt hx_oo.1, le_of_lt hx_oo.2⟩
      have h_eq_nbhd :
          (fun s => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ s)) =ᶠ[nhds x]
          (fun s => modularLambdaH (formula s)) := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        refine ⟨Set.Ioo a b, isOpen_Ioo.mem_nhds hx_oo, fun y hy => ?_⟩
        change modularLambdaH (F_Y_boundary_parameterization δ Y R₀ y) =
          modularLambdaH (formula y)
        rw [h_F_eq y ⟨le_of_lt hy.1, le_of_lt hy.2⟩]
      have h_deriv_eq :
          deriv (fun s => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ s)) x =
          deriv (fun s => modularLambdaH (formula s)) x := h_eq_nbhd.deriv_eq
      change (modularLambdaH (F_Y_boundary_parameterization δ Y R₀ x) - w)⁻¹ *
          deriv (fun s => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ s)) x =
        (modularLambdaH (formula x) - w)⁻¹ *
          deriv (fun s => modularLambdaH (formula s)) x
      rw [h_F_eq x hx_icc, h_deriv_eq]
    have h_int_eq : (∫ t in a..b, u t) = ∫ t in a..b, v t :=
      intervalIntegral.integral_congr_ae h_ae_imp
    have h_uv_ae : u =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] v :=
      (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr h_ae_imp
    have h_u_ii : IntervalIntegrable u MeasureTheory.volume a b :=
      h_v_ii.congr_ae h_uv_ae.symm
    exact ⟨h_int_eq.trans h_FTC_v, h_u_ii⟩
  -- Piece 0: bottom-left edge.
  have h0_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => (t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I)
      ((1 / 2 - R₀ : ℂ)) t := by
    intro t
    have h1 := Complex.ofRealCLM.hasDerivAt (x := t)
    simpa using (h1.mul_const ((1 / 2 - R₀ : ℂ))).add_const ((δ : ℂ) * Complex.I)
  have h0_im : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < ((t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I).im := by
    intro t _
    simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re] using hδ
  have h0_eq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      F_Y_boundary_parameterization δ Y R₀ t =
      (t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I := by
    intro t ht
    unfold F_Y_boundary_parameterization
    rw [if_pos ht.2]
  obtain ⟨hI0, hII0⟩ := h_piece 0 1
    (fun t : ℝ => (t * (1 / 2 - R₀) : ℂ) + (δ : ℂ) * Complex.I)
    (fun _ : ℝ => (1 / 2 - R₀ : ℂ))
    (le_refl 0) (by norm_num) (by norm_num)
    h0_d continuous_const h0_im h0_eq
  -- Piece 1: semicircular arc.
  have h1_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
        (Real.pi * (2 - t)))
      ((Real.pi * -1 : ℝ) •
        (_root_.circleMap 0 R₀ (Real.pi * (2 - t)) * Complex.I)) t := by
    intro t
    have h_inner : HasDerivAt (fun s : ℝ => Real.pi * (2 - s)) (Real.pi * -1) t := by
      have h := ((hasDerivAt_id t).const_sub (2 : ℝ)).const_mul Real.pi
      simpa using h
    have h_outer := hasDerivAt_circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (Real.pi * (2 - t))
    have h_comp := h_outer.scomp t h_inner
    simpa [Function.comp_def] using! h_comp
  have h1_cont : Continuous (fun t : ℝ => (Real.pi * -1 : ℝ) •
      (_root_.circleMap 0 R₀ (Real.pi * (2 - t)) * Complex.I)) := by
    refine Continuous.fun_const_smul ?_ _
    refine Continuous.mul ?_ continuous_const
    exact (continuous_circleMap 0 R₀).comp (by fun_prop)
  have h1_im : ∀ t ∈ Set.Icc (1 : ℝ) 2,
      0 < (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
        (Real.pi * (2 - t))).im := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have h_cm_im : ∀ (c : ℂ) (R θ : ℝ),
        (_root_.circleMap c R θ).im = c.im + R * Real.sin θ := by
      intro c R θ
      unfold _root_.circleMap
      rw [Complex.exp_mul_I]
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im]
    rw [h_cm_im]
    have h_c_im : ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I).im = δ := by
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]
    rw [h_c_im]
    have h_sin_nn : 0 ≤ Real.sin (Real.pi * (2 - t)) := by
      refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
      · have h2t : (0 : ℝ) ≤ 2 - t := by linarith
        positivity
      · nlinarith [Real.pi_pos]
    nlinarith [mul_nonneg hR₀_pos.le h_sin_nn]
  have h1_eq : ∀ t ∈ Set.Icc (1 : ℝ) 2,
      F_Y_boundary_parameterization δ Y R₀ t =
      _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ (Real.pi * (2 - t)) := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    unfold F_Y_boundary_parameterization
    rcases eq_or_lt_of_le ht1 with h_eq | h_lt
    · -- t = 1: junction with piece 0.
      rw [← h_eq]
      rw [if_pos (le_refl 1)]
      unfold _root_.circleMap
      have h_angle : ((Real.pi * (2 - 1) : ℝ) : ℂ) * Complex.I =
          (Real.pi : ℂ) * Complex.I := by push_cast; ring
      rw [h_angle, Complex.exp_pi_mul_I]
      push_cast; ring
    · rw [if_neg (not_le.mpr h_lt), if_pos ht2]
  obtain ⟨hI1, hII1⟩ := h_piece 1 2
    (fun t : ℝ => _root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀
      (Real.pi * (2 - t)))
    (fun t : ℝ => (Real.pi * -1 : ℝ) •
      (_root_.circleMap 0 R₀ (Real.pi * (2 - t)) * Complex.I))
    (by norm_num) (by norm_num) (by norm_num)
    h1_d h1_cont h1_im h1_eq
  -- Piece 2: bottom-right edge.
  have h2_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => (((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I)
      ((1 / 2 - R₀ : ℂ)) t := by
    intro t
    have h1 := Complex.ofRealCLM.hasDerivAt (x := t)
    have h2 := (((h1.sub_const (2 : ℂ)).mul_const ((1 / 2 - R₀ : ℂ))).const_add
      ((1 / 2 + R₀ : ℂ))).add_const ((δ : ℂ) * Complex.I)
    simpa using h2
  have h2_im : ∀ t ∈ Set.Icc (2 : ℝ) 3,
      0 < ((((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I).im := by
    intro t _
    simpa [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.sub_re, Complex.I_im, Complex.I_re] using hδ
  have h2_eq : ∀ t ∈ Set.Icc (2 : ℝ) 3,
      F_Y_boundary_parameterization δ Y R₀ t =
      (((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I := by
    intro t ht
    obtain ⟨ht2, ht3⟩ := ht
    unfold F_Y_boundary_parameterization
    have h_not1 : ¬ t ≤ 1 := by linarith
    rcases eq_or_lt_of_le ht2 with h_eq | h_lt
    · -- t = 2: junction with the arc piece.
      rw [← h_eq]
      rw [if_neg (by norm_num : ¬ (2 : ℝ) ≤ 1), if_pos (le_refl (2 : ℝ))]
      unfold _root_.circleMap
      have h_angle : ((Real.pi * (2 - 2) : ℝ) : ℂ) * Complex.I = 0 := by
        push_cast; ring
      rw [h_angle, Complex.exp_zero]
      push_cast; ring
    · rw [if_neg h_not1, if_neg (not_le.mpr h_lt), if_pos ht3]
  obtain ⟨hI2, hII2⟩ := h_piece 2 3
    (fun t : ℝ => (((1 / 2 + R₀) + (t - 2) * (1 / 2 - R₀)) : ℂ) + (δ : ℂ) * Complex.I)
    (fun _ : ℝ => (1 / 2 - R₀ : ℂ))
    (by norm_num) (by norm_num) (by norm_num)
    h2_d continuous_const h2_im h2_eq
  -- Piece 3: right edge.
  have h3_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => (1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I)
      (((Y - δ : ℂ)) * Complex.I) t := by
    intro t
    have h1 := Complex.ofRealCLM.hasDerivAt (x := t)
    have h2 := ((((h1.sub_const (3 : ℂ)).mul_const ((Y - δ : ℂ))).const_add
      ((δ : ℂ))).mul_const Complex.I).const_add (1 : ℂ)
    simpa using h2
  have h3_im : ∀ t ∈ Set.Icc (3 : ℝ) 4,
      0 < ((1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I).im := by
    intro t ht
    obtain ⟨ht3, ht4⟩ := ht
    simp [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.sub_re, Complex.I_im, Complex.I_re]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ t - 3) (by linarith : (0:ℝ) ≤ Y - δ)]
  have h3_eq : ∀ t ∈ Set.Icc (3 : ℝ) 4,
      F_Y_boundary_parameterization δ Y R₀ t =
      (1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I := by
    intro t ht
    obtain ⟨ht3, ht4⟩ := ht
    unfold F_Y_boundary_parameterization
    have h_not1 : ¬ t ≤ 1 := by linarith
    have h_not2 : ¬ t ≤ 2 := by linarith
    rcases eq_or_lt_of_le ht3 with h_eq | h_lt
    · -- t = 3: junction with the bottom-right edge.
      rw [← h_eq]
      rw [if_neg (by norm_num : ¬ (3 : ℝ) ≤ 1), if_neg (by norm_num : ¬ (3 : ℝ) ≤ 2),
        if_pos (le_refl (3 : ℝ))]
      push_cast; ring
    · rw [if_neg h_not1, if_neg h_not2, if_neg (not_le.mpr h_lt), if_pos ht4]
  obtain ⟨hI3, hII3⟩ := h_piece 3 4
    (fun t : ℝ => (1 : ℂ) + ((δ + (t - 3) * (Y - δ)) : ℂ) * Complex.I)
    (fun _ : ℝ => ((Y - δ : ℂ)) * Complex.I)
    (by norm_num) (by norm_num) (by norm_num)
    h3_d continuous_const h3_im h3_eq
  -- Piece 4: top edge.
  have h4_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => ((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I)
      (((-1 : ℝ) : ℂ)) t := by
    intro t
    have h_inner : HasDerivAt (fun s : ℝ => 5 - s) (-1) t :=
      (hasDerivAt_id t).const_sub 5
    exact (h_inner.ofReal_comp).add_const ((Y : ℂ) * Complex.I)
  have hY_pos : 0 < Y := lt_trans hδ hδY
  have h4_im : ∀ t ∈ Set.Icc (4 : ℝ) 5,
      0 < (((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I).im := by
    intro t _
    simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re] using hY_pos
  have h4_eq : ∀ t ∈ Set.Icc (4 : ℝ) 5,
      F_Y_boundary_parameterization δ Y R₀ t =
      ((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I := by
    intro t ht
    obtain ⟨ht4, ht5⟩ := ht
    unfold F_Y_boundary_parameterization
    have h_not1 : ¬ t ≤ 1 := by linarith
    have h_not2 : ¬ t ≤ 2 := by linarith
    have h_not3 : ¬ t ≤ 3 := by linarith
    rcases eq_or_lt_of_le ht4 with h_eq | h_lt
    · -- t = 4: junction with the right edge.
      rw [← h_eq]
      rw [if_neg (by norm_num : ¬ (4 : ℝ) ≤ 1), if_neg (by norm_num : ¬ (4 : ℝ) ≤ 2),
        if_neg (by norm_num : ¬ (4 : ℝ) ≤ 3), if_pos (le_refl (4 : ℝ))]
      push_cast; ring
    · rw [if_neg h_not1, if_neg h_not2, if_neg h_not3, if_neg (not_le.mpr h_lt),
        if_pos ht5]
  obtain ⟨hI4, hII4⟩ := h_piece 4 5
    (fun t : ℝ => ((5 - t : ℝ) : ℂ) + (Y : ℂ) * Complex.I)
    (fun _ : ℝ => ((-1 : ℝ) : ℂ))
    (by norm_num) (by norm_num) (by norm_num)
    h4_d continuous_const h4_im h4_eq
  -- Piece 5: left edge.
  have h5_d : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I)
      (((-(Y - δ) : ℝ) : ℂ) * Complex.I) t := by
    intro t
    have h_inner : HasDerivAt (fun s : ℝ => Y - (s - 5) * (Y - δ)) (-(Y - δ)) t := by
      have h := (((hasDerivAt_id t).sub_const (5 : ℝ)).mul_const (Y - δ)).const_sub Y
      simpa using h
    exact (h_inner.ofReal_comp).mul_const Complex.I
  have h5_im : ∀ t ∈ Set.Icc (5 : ℝ) 6,
      0 < (((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I).im := by
    intro t ht
    obtain ⟨ht5, ht6⟩ := ht
    simp [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re]
    have h_le_one : t - 5 ≤ 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h_le_one (by linarith : (0:ℝ) ≤ Y - δ)]
  have h5_eq : ∀ t ∈ Set.Icc (5 : ℝ) 6,
      F_Y_boundary_parameterization δ Y R₀ t =
      ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I := by
    intro t ht
    obtain ⟨ht5, ht6⟩ := ht
    unfold F_Y_boundary_parameterization
    have h_not1 : ¬ t ≤ 1 := by linarith
    have h_not2 : ¬ t ≤ 2 := by linarith
    have h_not3 : ¬ t ≤ 3 := by linarith
    have h_not4 : ¬ t ≤ 4 := by linarith
    rcases eq_or_lt_of_le ht5 with h_eq | h_lt
    · -- t = 5: junction with the top edge.
      rw [← h_eq]
      rw [if_neg (by norm_num : ¬ (5 : ℝ) ≤ 1), if_neg (by norm_num : ¬ (5 : ℝ) ≤ 2),
        if_neg (by norm_num : ¬ (5 : ℝ) ≤ 3), if_neg (by norm_num : ¬ (5 : ℝ) ≤ 4),
        if_pos (le_refl (5 : ℝ))]
      push_cast; ring
    · rw [if_neg h_not1, if_neg h_not2, if_neg h_not3, if_neg h_not4,
        if_neg (not_le.mpr h_lt), if_pos ht6]
  obtain ⟨hI5, hII5⟩ := h_piece 5 6
    (fun t : ℝ => ((Y - (t - 5) * (Y - δ) : ℝ) : ℂ) * Complex.I)
    (fun _ : ℝ => ((-(Y - δ) : ℝ) : ℂ) * Complex.I)
    (by norm_num) (by norm_num) (le_refl 6)
    h5_d continuous_const h5_im h5_eq
  -- Telescope the six pieces.
  have e01 := intervalIntegral.integral_add_adjacent_intervals hII0 hII1
  have hII02 := hII0.trans hII1
  have e02 := intervalIntegral.integral_add_adjacent_intervals hII02 hII2
  have hII03 := hII02.trans hII2
  have e03 := intervalIntegral.integral_add_adjacent_intervals hII03 hII3
  have hII04 := hII03.trans hII3
  have e04 := intervalIntegral.integral_add_adjacent_intervals hII04 hII4
  have hII05 := hII04.trans hII4
  have e05 := intervalIntegral.integral_add_adjacent_intervals hII05 hII5
  unfold Complex.pathContourIntegral
  change (∫ t in (0:ℝ)..6, u t) = L 6 - L 0
  rw [← e05, ← e04, ← e03, ← e02, ← e01, hI0, hI1, hI2, hI3, hI4, hI5]
  ring


/-- **Continuous logarithmic lift on a closed real interval.**
For a continuous function `u : ℝ → ℂ` nonzero on `Icc a b`, there
exists a globally continuous function `L : ℝ → ℂ` such that
`Complex.exp (L t) = u t` for all `t ∈ Icc a b`.

This is the analytic core of path-lifting in the universal cover
`ℂ → ℂ \ {0}` of the punctured plane (via `z ↦ exp z`), restricted
to the simply-connected interval `[a, b]`. The lift is unique up to
addition of `2π i · k` for `k ∈ ℤ`.

Construction: pick `ε > 0` lower bound on `‖u‖` (compactness) and a
uniform-continuity modulus `δ > 0` for target `ε`. Subdivide `Icc a b`
into `N` equal segments with mesh `h = (b-a)/N < δ`, so on each
segment `u(t)/u(tt j) ∈ Metric.ball 1 1 ⊆ Complex.slitPlane`. Define
`L(t) := Complex.log(u(a)) + ∑ j ∈ range N, Complex.log(u(σ j t)/u(tt j))`
with `σ j t := min (max t (tt j)) (tt (j+1))`. The sum telescopes
through `Complex.exp` to give `u(t)` on `Icc a b`. -/
theorem continuous_log_lift_of_continuous_ne_zero_Icc
    {a b : ℝ} (hab : a ≤ b) (u : ℝ → ℂ)
    (hu_cont : ContinuousOn u (Set.Icc a b))
    (hu_ne : ∀ t ∈ Set.Icc a b, u t ≠ 0) :
    ∃ L : ℝ → ℂ, Continuous L ∧
      ∀ t ∈ Set.Icc a b, Complex.exp (L t) = u t := by
  -- Degenerate case a = b.
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · refine ⟨fun _ => Complex.log (u a), continuous_const, ?_⟩
    intro t ht
    have ht_eq : t = a := le_antisymm (ht.2.trans hab_eq.symm.le) ht.1
    rw [ht_eq]
    exact Complex.exp_log (hu_ne a ⟨le_refl _, hab⟩)
  -- Main case: a < b. Pick ε > 0 lower bound on ‖u‖.
  have h_nonempty : (Set.Icc a b).Nonempty := ⟨a, Set.left_mem_Icc.mpr hab⟩
  obtain ⟨t_min, ht_min_mem, ht_min_minOn⟩ :=
    isCompact_Icc.exists_isMinOn h_nonempty hu_cont.norm
  set ε : ℝ := ‖u t_min‖
  have hε_pos : 0 < ε := norm_pos_iff.mpr (hu_ne t_min ht_min_mem)
  have hε_lb : ∀ t ∈ Set.Icc a b, ε ≤ ‖u t‖ := fun t ht => ht_min_minOn ht
  -- Uniform-continuity modulus δ for target ε.
  have h_unif : UniformContinuousOn u (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hu_cont
  rw [Metric.uniformContinuousOn_iff] at h_unif
  obtain ⟨δ, hδ_pos, hδ_lt⟩ := h_unif ε hε_pos
  -- Choose N large enough.
  set N : ℕ := ⌈(b - a) / δ⌉₊ + 1 with hN_def
  have hN_pos : 0 < N := Nat.succ_pos _
  have hN_real_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
  set h₀ : ℝ := (b - a) / N with hh_def
  have h₀_pos : 0 < h₀ := div_pos (by linarith) hN_real_pos
  have h₀_lt_δ : h₀ < δ := by
    have h_ceil : (b - a) / δ ≤ (⌈(b - a) / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h_lt_N : (⌈(b - a) / δ⌉₊ : ℝ) < (N : ℝ) := by
      rw [hN_def]; push_cast; linarith
    have h_combined : (b - a) / δ < N := lt_of_le_of_lt h_ceil h_lt_N
    rw [hh_def, div_lt_iff₀ hN_real_pos]
    rw [div_lt_iff₀ hδ_pos] at h_combined
    linarith
  -- Partition points tt j := a + j * h₀.
  set tt : ℕ → ℝ := fun j => a + (j : ℝ) * h₀ with htt_def
  have htt0 : tt 0 = a := by simp [tt]
  have httN : tt N = b := by
    simp only [tt]; rw [hh_def]; field_simp; ring
  have htt_succ_eq : ∀ j, tt (j + 1) = tt j + h₀ := by
    intro j
    simp only [tt]
    push_cast; ring
  have htt_le_succ : ∀ j, tt j ≤ tt (j + 1) := fun j => by
    rw [htt_succ_eq]; linarith
  have htt_mono : ∀ {j k : ℕ}, j ≤ k → tt j ≤ tt k := by
    intro j k hjk
    simp only [tt]
    have h_cast : (j : ℝ) ≤ k := by exact_mod_cast hjk
    have h_mul : (j : ℝ) * h₀ ≤ k * h₀ := mul_le_mul_of_nonneg_right h_cast h₀_pos.le
    linarith
  have htt_mem : ∀ j ≤ N, tt j ∈ Set.Icc a b := by
    intro j hj
    refine ⟨?_, ?_⟩
    · rw [← htt0]; exact htt_mono (Nat.zero_le j)
    · rw [← httN]; exact htt_mono hj
  -- Metric.ball 1 1 ⊆ slitPlane.
  have h_ball_slit : Metric.ball (1 : ℂ) 1 ⊆ Complex.slitPlane := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    refine Or.inl ?_
    have h_re_le : (z - 1).re ≤ ‖z - 1‖ := Complex.re_le_norm _
    have h_neg_re_le : -(z - 1).re ≤ ‖z - 1‖ := by
      have h := Complex.re_le_norm (-(z - 1))
      rw [Complex.neg_re, norm_neg] at h
      exact h
    have h_z_re : z.re = (z - 1).re + 1 := by simp [Complex.sub_re]
    rw [h_z_re]; linarith
  -- For s ∈ [tt j, tt (j+1)], u s / u (tt j) ∈ ball 1 1.
  have h_quot_in_ball : ∀ j, j < N → ∀ s ∈ Set.Icc (tt j) (tt (j + 1)),
      u s / u (tt j) ∈ Metric.ball (1 : ℂ) 1 := by
    intro j hj_lt s hs
    have htt_j_mem : tt j ∈ Set.Icc a b :=
      htt_mem j (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hj_lt))
    have htt_succ_mem : tt (j + 1) ∈ Set.Icc a b := htt_mem (j + 1) hj_lt
    have hs_mem : s ∈ Set.Icc a b :=
      ⟨le_trans htt_j_mem.1 hs.1, le_trans hs.2 htt_succ_mem.2⟩
    have h_u_tt_ne : u (tt j) ≠ 0 := hu_ne _ htt_j_mem
    have h_u_tt_norm : ε ≤ ‖u (tt j)‖ := hε_lb _ htt_j_mem
    have h_dist_st : dist s (tt j) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
      have hb : s - tt j ≤ tt (j + 1) - tt j := sub_le_sub_right hs.2 _
      rw [htt_succ_eq] at hb
      have h_eq : tt j + h₀ - tt j = h₀ := by ring
      rw [h_eq] at hb
      linarith
    have h_u_dist : dist (u s) (u (tt j)) < ε := hδ_lt s hs_mem (tt j) htt_j_mem h_dist_st
    rw [Metric.mem_ball, dist_eq_norm]
    have h_div_eq : u s / u (tt j) - 1 = (u s - u (tt j)) / u (tt j) := by
      field_simp
    rw [h_div_eq, norm_div]
    rw [div_lt_one (norm_pos_iff.mpr h_u_tt_ne)]
    have h1 : ‖u s - u (tt j)‖ < ε := by rwa [dist_eq_norm] at h_u_dist
    linarith
  -- σ j t := min (max t (tt j)) (tt (j+1)), always in [tt j, tt (j+1)] ⊆ [a, b].
  set σ : ℕ → ℝ → ℝ := fun j t => min (max t (tt j)) (tt (j + 1))
  have hσ_mem : ∀ j, j < N → ∀ t, σ j t ∈ Set.Icc (tt j) (tt (j + 1)) := by
    intro j _ t
    refine ⟨le_min (le_max_right _ _) (htt_le_succ j), min_le_right _ _⟩
  have hσ_mem_ab : ∀ j, j < N → ∀ t, σ j t ∈ Set.Icc a b := by
    intro j hj_lt t
    have h1 := hσ_mem j hj_lt t
    have h2 := htt_mem j (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hj_lt))
    have h3 := htt_mem (j + 1) hj_lt
    exact ⟨le_trans h2.1 h1.1, le_trans h1.2 h3.2⟩
  have hσ_cont : ∀ j, Continuous (σ j) := fun j => by
    change Continuous (fun t => min (max t (tt j)) (tt (j + 1))); fun_prop
  -- Define L.
  set L : ℝ → ℂ := fun t => Complex.log (u a) +
    ∑ j ∈ Finset.range N, Complex.log (u (σ j t) / u (tt j)) with hL_def
  -- Complex.log continuous on slitPlane.
  have h_log_contOn : ContinuousOn Complex.log Complex.slitPlane := fun z hz =>
    (Complex.differentiableAt_log hz).continuousAt.continuousWithinAt
  refine ⟨L, ?_, ?_⟩
  · -- Continuity of L.
    refine continuous_const.add ?_
    refine continuous_finsetSum _ ?_
    intro j hj
    have hj_lt : j < N := Finset.mem_range.mp hj
    have h_u_σ_cont : Continuous (fun t => u (σ j t)) :=
      hu_cont.comp_continuous (hσ_cont j) (fun t => hσ_mem_ab j hj_lt t)
    have h_quot_cont : Continuous (fun t => u (σ j t) / u (tt j)) :=
      h_u_σ_cont.div_const _
    refine h_log_contOn.comp_continuous h_quot_cont (fun t => h_ball_slit ?_)
    exact h_quot_in_ball j hj_lt _ (hσ_mem j hj_lt t)
  · -- exp(L t) = u t for t ∈ Icc a b.
    intro t ht
    obtain ⟨ht_lb, ht_ub⟩ := ht
    -- Find smallest k with t ≤ tt (k+1).
    have h_exists : ∃ j, j < N ∧ t ≤ tt (j + 1) := by
      refine ⟨N - 1, Nat.sub_lt hN_pos Nat.one_pos, ?_⟩
      have h_succ : N - 1 + 1 = N := Nat.sub_add_cancel hN_pos
      rw [h_succ, httN]; exact ht_ub
    let k : ℕ := Nat.find h_exists
    have hk_spec := Nat.find_spec h_exists
    have hk_lt : k < N := hk_spec.1
    have ht_le : t ≤ tt (k + 1) := hk_spec.2
    have hk_le_N : k ≤ N := le_of_lt hk_lt
    have hk_le_t : tt k ≤ t := by
      by_cases hk_zero : k = 0
      · rw [hk_zero, htt0]; exact ht_lb
      · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_zero
        have h_pred_lt : k - 1 < k := Nat.sub_lt hk_pos Nat.one_pos
        have h_not := Nat.find_min h_exists h_pred_lt
        simp only [not_and, not_le] at h_not
        have h_pred_lt_N : k - 1 < N := lt_trans h_pred_lt hk_lt
        have h_lt := h_not h_pred_lt_N
        have h_pred_succ : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
        rw [h_pred_succ] at h_lt
        exact le_of_lt h_lt
    -- σ j t formulas: j < k → σ = tt (j+1); j = k → σ = t; j > k → σ = tt j.
    have hσ_lt_k : ∀ j, j < k → σ j t = tt (j + 1) := by
      intro j hjk
      change min (max t (tt j)) (tt (j + 1)) = tt (j + 1)
      have h_succ_le : tt (j + 1) ≤ tt k := htt_mono hjk
      have h_succ_le_t : tt (j + 1) ≤ t := le_trans h_succ_le hk_le_t
      have h_j_le_t : tt j ≤ t := le_trans (htt_le_succ j) h_succ_le_t
      rw [max_eq_left h_j_le_t, min_eq_right h_succ_le_t]
    have hσ_eq_k : σ k t = t := by
      change min (max t (tt k)) (tt (k + 1)) = t
      rw [max_eq_left hk_le_t, min_eq_left ht_le]
    have hσ_gt_k : ∀ j, k < j → σ j t = tt j := by
      intro j hjk
      change min (max t (tt j)) (tt (j + 1)) = tt j
      have h_succ_le_j : tt (k + 1) ≤ tt j := htt_mono hjk
      have h_t_le_j : t ≤ tt j := le_trans ht_le h_succ_le_j
      rw [max_eq_right h_t_le_j, min_eq_left (htt_le_succ j)]
    -- exp(L t) = exp(log(u a)) · ∏_j exp(log(u(σ j t)/u(tt j)))
    --        = u(a) · ∏_j (u(σ j t)/u(tt j)).
    have h_u_a_ne : u a ≠ 0 := hu_ne a ⟨le_refl _, hab⟩
    have h_log_quot : ∀ j ∈ Finset.range N,
        Complex.exp (Complex.log (u (σ j t) / u (tt j))) = u (σ j t) / u (tt j) := by
      intro j hj
      have hj_lt : j < N := Finset.mem_range.mp hj
      have h_u_tt_ne : u (tt j) ≠ 0 :=
        hu_ne _ (htt_mem j (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hj_lt)))
      have h_u_σ_ne : u (σ j t) ≠ 0 := hu_ne _ (hσ_mem_ab j hj_lt t)
      exact Complex.exp_log (div_ne_zero h_u_σ_ne h_u_tt_ne)
    change Complex.exp (Complex.log (u a) +
      ∑ j ∈ Finset.range N, Complex.log (u (σ j t) / u (tt j))) = u t
    rw [Complex.exp_add, Complex.exp_log h_u_a_ne, Complex.exp_sum,
        Finset.prod_congr rfl h_log_quot]
    -- Split range N at k: range k ∪ {k} ∪ Ico (k+1) N.
    have h_split : Finset.range N =
        Finset.range k ∪ {k} ∪ Finset.Ico (k + 1) N := by
      ext j
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton, Finset.mem_Ico]
      constructor
      · intro hj
        rcases lt_trichotomy j k with hlt | heq | hgt
        · exact Or.inl (Or.inl hlt)
        · exact Or.inl (Or.inr heq)
        · exact Or.inr ⟨hgt, hj⟩
      · rintro ((hlt | heq) | ⟨hgt, hlt⟩)
        · exact lt_of_lt_of_le hlt hk_le_N
        · rw [heq]; exact hk_lt
        · exact hlt
    have h_disj_left : Disjoint (Finset.range k) ({k} : Finset ℕ) := by
      rw [Finset.disjoint_singleton_right]; exact Finset.notMem_range_self
    have h_disj_right : Disjoint (Finset.range k ∪ {k}) (Finset.Ico (k + 1) N) := by
      rw [Finset.disjoint_left]
      intro j hj hj_Ico
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton] at hj
      rw [Finset.mem_Ico] at hj_Ico
      omega
    rw [h_split, Finset.prod_union h_disj_right, Finset.prod_union h_disj_left,
        Finset.prod_singleton, hσ_eq_k]
    -- ∏ on range k: u(tt(j+1))/u(tt j) → telescope to u(tt k)/u(a).
    have h_telescope : ∀ k' ≤ N,
        ∏ j ∈ Finset.range k', u (tt (j + 1)) / u (tt j) = u (tt k') / u (tt 0) := by
      intro k' hk'
      induction k' with
      | zero =>
        have h_u_a_ne : u (tt 0) ≠ 0 := hu_ne _ (htt_mem 0 (Nat.zero_le _))
        simp [div_self h_u_a_ne]
      | succ m ih =>
        have hm_le : m ≤ N := Nat.le_of_succ_le hk'
        rw [Finset.prod_range_succ, ih hm_le]
        have h_u_tt_m_ne : u (tt m) ≠ 0 := hu_ne _ (htt_mem m hm_le)
        field_simp
    have h_prod_range_k : ∏ j ∈ Finset.range k, u (σ j t) / u (tt j) =
        u (tt k) / u (tt 0) := by
      have h_eq : ∀ j ∈ Finset.range k, u (σ j t) / u (tt j) = u (tt (j + 1)) / u (tt j) := by
        intro j hj
        rw [hσ_lt_k j (Finset.mem_range.mp hj)]
      rw [Finset.prod_congr rfl h_eq, h_telescope k hk_le_N]
    -- ∏ on Ico (k+1) N: 1.
    have h_prod_Ico : ∏ j ∈ Finset.Ico (k + 1) N, u (σ j t) / u (tt j) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      rw [Finset.mem_Ico] at hj
      rw [hσ_gt_k j hj.1, div_self (hu_ne _ (htt_mem j (le_of_lt hj.2)))]
    rw [h_prod_range_k, h_prod_Ico, htt0, mul_one]
    have h_u_tt_k_ne : u (tt k) ≠ 0 := hu_ne _ (htt_mem k hk_le_N)
    field_simp

/-- **Parametric continuous logarithmic lift.** For a jointly continuous
function `u : ℝ × ℝ → ℂ` nonzero on `Icc a b × Icc c d`, there exists a
jointly continuous function `L : ℝ × ℝ → ℂ` such that
`Complex.exp (L (s, t)) = u (s, t)` for all `(s, t) ∈ Icc a b × Icc c d`.

The 2D-parametric extension of `continuous_log_lift_of_continuous_ne_zero_Icc`.
Construction analogous: by joint compactness, get `ε > 0` lower bound on
`‖u‖` and a joint uniform-continuity modulus `δ`. Subdivide the rectangle
into a grid of cells with mesh `< δ` (in both directions), so that on each
cell `u(s, t) / u(sᵢ, tⱼ) ∈ Metric.ball 1 1 ⊆ Complex.slitPlane`. Define
the lift via a 2D telescoping sum of `Complex.log` evaluations on the
clipped projections to each cell. -/
theorem continuous_log_lift_param_of_continuous_ne_zero
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (u : ℝ → ℝ → ℂ)
    (hu_cont : ContinuousOn (Function.uncurry u) (Set.Icc a b ×ˢ Set.Icc c d))
    (hu_ne : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, u s t ≠ 0) :
    ∃ L : ℝ → ℝ → ℂ, Continuous (Function.uncurry L) ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc c d, Complex.exp (L s t) = u s t := by
  have ha_mem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hc_mem : c ∈ Set.Icc c d := Set.left_mem_Icc.mpr hcd
  -- Degenerate case a = b: the rectangle is {a} × [c, d]; use the 1D lift in t.
  rcases hab.eq_or_lt with hab_eq | hab_lt
  · have h_ua_cont : ContinuousOn (u a) (Set.Icc c d) := by
      have h_pair_cont : ContinuousOn (fun t : ℝ => ((a, t) : ℝ × ℝ)) (Set.Icc c d) :=
        (continuous_const.prodMk continuous_id).continuousOn
      exact hu_cont.comp h_pair_cont (fun t ht => Set.mk_mem_prod ha_mem ht)
    obtain ⟨L₁, hL₁_cont, hL₁_exp⟩ :=
      continuous_log_lift_of_continuous_ne_zero_Icc hcd (u a) h_ua_cont
        (fun t ht => hu_ne a ha_mem t ht)
    refine ⟨fun _ t => L₁ t, ?_, ?_⟩
    · change Continuous fun p : ℝ × ℝ => L₁ p.2
      exact hL₁_cont.comp continuous_snd
    · intro s hs t ht
      have hs_eq : s = a := le_antisymm (hs.2.trans hab_eq.symm.le) hs.1
      rw [hs_eq]
      exact hL₁_exp t ht
  -- Degenerate case c = d: the rectangle is [a, b] × {c}; use the 1D lift in s.
  rcases hcd.eq_or_lt with hcd_eq | hcd_lt
  · have h_uc_cont : ContinuousOn (fun x : ℝ => u x c) (Set.Icc a b) := by
      have h_pair_cont : ContinuousOn (fun x : ℝ => ((x, c) : ℝ × ℝ)) (Set.Icc a b) :=
        (continuous_id.prodMk continuous_const).continuousOn
      exact hu_cont.comp h_pair_cont (fun x hx => Set.mk_mem_prod hx hc_mem)
    obtain ⟨L₁, hL₁_cont, hL₁_exp⟩ :=
      continuous_log_lift_of_continuous_ne_zero_Icc hab (fun x => u x c) h_uc_cont
        (fun x hx => hu_ne x hx c hc_mem)
    refine ⟨fun s _ => L₁ s, ?_, ?_⟩
    · change Continuous fun p : ℝ × ℝ => L₁ p.1
      exact hL₁_cont.comp continuous_fst
    · intro s hs t ht
      have ht_eq : t = c := le_antisymm (ht.2.trans hcd_eq.symm.le) ht.1
      rw [ht_eq]
      exact hL₁_exp s hs
  -- Main case: a < b and c < d. Pick ε > 0 lower bound on ‖u‖ by joint compactness.
  have hK_compact : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) :=
    isCompact_Icc.prod isCompact_Icc
  have hK_nonempty : (Set.Icc a b ×ˢ Set.Icc c d).Nonempty :=
    ⟨(a, c), Set.mk_mem_prod ha_mem hc_mem⟩
  obtain ⟨p_min, hp_min_mem, hp_min_minOn⟩ :=
    hK_compact.exists_isMinOn hK_nonempty hu_cont.norm
  rw [Set.mem_prod] at hp_min_mem
  set ε : ℝ := ‖Function.uncurry u p_min‖
  have hε_pos : 0 < ε :=
    norm_pos_iff.mpr (hu_ne p_min.1 hp_min_mem.1 p_min.2 hp_min_mem.2)
  have hε_lb : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, ε ≤ ‖u x y‖ := by
    intro x hx y hy
    exact hp_min_minOn (Set.mk_mem_prod hx hy)
  -- Joint uniform-continuity modulus δ for target ε.
  have h_unif : UniformContinuousOn (Function.uncurry u) (Set.Icc a b ×ˢ Set.Icc c d) :=
    hK_compact.uniformContinuousOn_of_continuous hu_cont
  rw [Metric.uniformContinuousOn_iff] at h_unif
  obtain ⟨δ, hδ_pos, hδ_lt⟩ := h_unif ε hε_pos
  -- Choose N (s-direction grid size) large enough.
  set N : ℕ := ⌈(b - a) / δ⌉₊ + 1 with hN_def
  have hN_pos : 0 < N := Nat.succ_pos _
  have hN_real_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
  set sStep : ℝ := (b - a) / N with hsStep_def
  have hsStep_pos : 0 < sStep := div_pos (by linarith) hN_real_pos
  have hsStep_lt_δ : sStep < δ := by
    have h_ceil : (b - a) / δ ≤ (⌈(b - a) / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h_lt_N : (⌈(b - a) / δ⌉₊ : ℝ) < (N : ℝ) := by
      rw [hN_def]; push_cast; linarith
    have h_combined : (b - a) / δ < N := lt_of_le_of_lt h_ceil h_lt_N
    rw [hsStep_def, div_lt_iff₀ hN_real_pos]
    rw [div_lt_iff₀ hδ_pos] at h_combined
    linarith
  -- Choose M (t-direction grid size) large enough.
  set M : ℕ := ⌈(d - c) / δ⌉₊ + 1 with hM_def
  have hM_pos : 0 < M := Nat.succ_pos _
  have hM_real_pos : (0 : ℝ) < M := Nat.cast_pos.mpr hM_pos
  set tStep : ℝ := (d - c) / M with htStep_def
  have htStep_pos : 0 < tStep := div_pos (by linarith) hM_real_pos
  have htStep_lt_δ : tStep < δ := by
    have h_ceil : (d - c) / δ ≤ (⌈(d - c) / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h_lt_M : (⌈(d - c) / δ⌉₊ : ℝ) < (M : ℝ) := by
      rw [hM_def]; push_cast; linarith
    have h_combined : (d - c) / δ < M := lt_of_le_of_lt h_ceil h_lt_M
    rw [htStep_def, div_lt_iff₀ hM_real_pos]
    rw [div_lt_iff₀ hδ_pos] at h_combined
    linarith
  -- s-direction partition points ss i := a + i * sStep.
  set ss : ℕ → ℝ := fun i => a + (i : ℝ) * sStep
  have hss0 : ss 0 = a := by simp [ss]
  have hssN : ss N = b := by
    simp only [ss]; rw [hsStep_def]; field_simp; ring
  have hss_succ_eq : ∀ i, ss (i + 1) = ss i + sStep := by
    intro i
    simp only [ss]
    push_cast; ring
  have hss_le_succ : ∀ i, ss i ≤ ss (i + 1) := fun i => by
    rw [hss_succ_eq]; linarith
  have hss_mono : ∀ {i k : ℕ}, i ≤ k → ss i ≤ ss k := by
    intro i k hik
    simp only [ss]
    have h_cast : (i : ℝ) ≤ k := by exact_mod_cast hik
    have h_mul : (i : ℝ) * sStep ≤ k * sStep :=
      mul_le_mul_of_nonneg_right h_cast hsStep_pos.le
    linarith
  have hss_mem : ∀ i ≤ N, ss i ∈ Set.Icc a b := by
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [← hss0]; exact hss_mono (Nat.zero_le i)
    · rw [← hssN]; exact hss_mono hi
  -- t-direction partition points tt j := c + j * tStep.
  set tt : ℕ → ℝ := fun j => c + (j : ℝ) * tStep
  have htt0 : tt 0 = c := by simp [tt]
  have httM : tt M = d := by
    simp only [tt]; rw [htStep_def]; field_simp; ring
  have htt_succ_eq : ∀ j, tt (j + 1) = tt j + tStep := by
    intro j
    simp only [tt]
    push_cast; ring
  have htt_le_succ : ∀ j, tt j ≤ tt (j + 1) := fun j => by
    rw [htt_succ_eq]; linarith
  have htt_mono : ∀ {j k : ℕ}, j ≤ k → tt j ≤ tt k := by
    intro j k hjk
    simp only [tt]
    have h_cast : (j : ℝ) ≤ k := by exact_mod_cast hjk
    have h_mul : (j : ℝ) * tStep ≤ k * tStep :=
      mul_le_mul_of_nonneg_right h_cast htStep_pos.le
    linarith
  have htt_mem : ∀ j ≤ M, tt j ∈ Set.Icc c d := by
    intro j hj
    refine ⟨?_, ?_⟩
    · rw [← htt0]; exact htt_mono (Nat.zero_le j)
    · rw [← httM]; exact htt_mono hj
  -- Metric.ball 1 1 ⊆ slitPlane.
  have h_ball_slit : Metric.ball (1 : ℂ) 1 ⊆ Complex.slitPlane := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    refine Or.inl ?_
    have h_re_le : (z - 1).re ≤ ‖z - 1‖ := Complex.re_le_norm _
    have h_neg_re_le : -(z - 1).re ≤ ‖z - 1‖ := by
      have h := Complex.re_le_norm (-(z - 1))
      rw [Complex.neg_re, norm_neg] at h
      exact h
    have h_z_re : z.re = (z - 1).re + 1 := by simp [Complex.sub_re]
    rw [h_z_re]; linarith
  -- For x ∈ [ss i, ss (i+1)], u x c / u (ss i) c ∈ ball 1 1
  -- (second coordinates both equal to c, so the product distance is the s-distance).
  have h_quot_s_in_ball : ∀ i, i < N → ∀ x ∈ Set.Icc (ss i) (ss (i + 1)),
      u x c / u (ss i) c ∈ Metric.ball (1 : ℂ) 1 := by
    intro i hi_lt x hx
    have hss_i_mem : ss i ∈ Set.Icc a b := hss_mem i (le_of_lt hi_lt)
    have hss_succ_mem : ss (i + 1) ∈ Set.Icc a b := hss_mem (i + 1) hi_lt
    have hx_mem : x ∈ Set.Icc a b :=
      ⟨le_trans hss_i_mem.1 hx.1, le_trans hx.2 hss_succ_mem.2⟩
    have h_u_ne : u (ss i) c ≠ 0 := hu_ne _ hss_i_mem c hc_mem
    have h_u_norm : ε ≤ ‖u (ss i) c‖ := hε_lb _ hss_i_mem c hc_mem
    have h_dist_x : dist x (ss i) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
      have hb' : x - ss i ≤ ss (i + 1) - ss i := sub_le_sub_right hx.2 _
      rw [hss_succ_eq] at hb'
      have h_eq : ss i + sStep - ss i = sStep := by ring
      rw [h_eq] at hb'
      linarith
    have h_dist_pair : dist ((x, c) : ℝ × ℝ) ((ss i, c) : ℝ × ℝ) < δ := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · exact h_dist_x
      · simpa using hδ_pos
    have h_u_dist : dist (u x c) (u (ss i) c) < ε :=
      hδ_lt (x, c) (Set.mk_mem_prod hx_mem hc_mem) (ss i, c)
        (Set.mk_mem_prod hss_i_mem hc_mem) h_dist_pair
    rw [Metric.mem_ball, dist_eq_norm]
    have h_div_eq : u x c / u (ss i) c - 1 = (u x c - u (ss i) c) / u (ss i) c := by
      field_simp
    rw [h_div_eq, norm_div]
    rw [div_lt_one (norm_pos_iff.mpr h_u_ne)]
    have h1 : ‖u x c - u (ss i) c‖ < ε := by rwa [dist_eq_norm] at h_u_dist
    linarith
  -- For x ∈ [a, b] and y ∈ [tt j, tt (j+1)], u x y / u x (tt j) ∈ ball 1 1
  -- (first coordinates both equal to x, so the product distance is the t-distance).
  have h_quot_t_in_ball : ∀ x ∈ Set.Icc a b, ∀ j, j < M →
      ∀ y ∈ Set.Icc (tt j) (tt (j + 1)),
      u x y / u x (tt j) ∈ Metric.ball (1 : ℂ) 1 := by
    intro x hx_mem j hj_lt y hy
    have htt_j_mem : tt j ∈ Set.Icc c d := htt_mem j (le_of_lt hj_lt)
    have htt_succ_mem : tt (j + 1) ∈ Set.Icc c d := htt_mem (j + 1) hj_lt
    have hy_mem : y ∈ Set.Icc c d :=
      ⟨le_trans htt_j_mem.1 hy.1, le_trans hy.2 htt_succ_mem.2⟩
    have h_u_ne : u x (tt j) ≠ 0 := hu_ne x hx_mem _ htt_j_mem
    have h_u_norm : ε ≤ ‖u x (tt j)‖ := hε_lb x hx_mem _ htt_j_mem
    have h_dist_y : dist y (tt j) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy.1)]
      have hb' : y - tt j ≤ tt (j + 1) - tt j := sub_le_sub_right hy.2 _
      rw [htt_succ_eq] at hb'
      have h_eq : tt j + tStep - tt j = tStep := by ring
      rw [h_eq] at hb'
      linarith
    have h_dist_pair : dist ((x, y) : ℝ × ℝ) ((x, tt j) : ℝ × ℝ) < δ := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · simpa using hδ_pos
      · exact h_dist_y
    have h_u_dist : dist (u x y) (u x (tt j)) < ε :=
      hδ_lt (x, y) (Set.mk_mem_prod hx_mem hy_mem) (x, tt j)
        (Set.mk_mem_prod hx_mem htt_j_mem) h_dist_pair
    rw [Metric.mem_ball, dist_eq_norm]
    have h_div_eq : u x y / u x (tt j) - 1 = (u x y - u x (tt j)) / u x (tt j) := by
      field_simp
    rw [h_div_eq, norm_div]
    rw [div_lt_one (norm_pos_iff.mpr h_u_ne)]
    have h1 : ‖u x y - u x (tt j)‖ < ε := by rwa [dist_eq_norm] at h_u_dist
    linarith
  -- Clamps: σs i x ∈ [ss i, ss (i+1)], σt j y ∈ [tt j, tt (j+1)], ρ x ∈ [a, b].
  set σs : ℕ → ℝ → ℝ := fun i x => min (max x (ss i)) (ss (i + 1))
  have hσs_mem : ∀ i, i < N → ∀ x : ℝ, σs i x ∈ Set.Icc (ss i) (ss (i + 1)) := by
    intro i _ x
    exact ⟨le_min (le_max_right _ _) (hss_le_succ i), min_le_right _ _⟩
  have hσs_mem_ab : ∀ i, i < N → ∀ x : ℝ, σs i x ∈ Set.Icc a b := by
    intro i hi_lt x
    have h1 := hσs_mem i hi_lt x
    have h2 := hss_mem i (le_of_lt hi_lt)
    have h3 := hss_mem (i + 1) hi_lt
    exact ⟨le_trans h2.1 h1.1, le_trans h1.2 h3.2⟩
  have hσs_cont : ∀ i, Continuous (σs i) := fun i => by
    change Continuous (fun x : ℝ => min (max x (ss i)) (ss (i + 1))); fun_prop
  set σt : ℕ → ℝ → ℝ := fun j y => min (max y (tt j)) (tt (j + 1))
  have hσt_mem : ∀ j, j < M → ∀ y : ℝ, σt j y ∈ Set.Icc (tt j) (tt (j + 1)) := by
    intro j _ y
    exact ⟨le_min (le_max_right _ _) (htt_le_succ j), min_le_right _ _⟩
  have hσt_mem_cd : ∀ j, j < M → ∀ y : ℝ, σt j y ∈ Set.Icc c d := by
    intro j hj_lt y
    have h1 := hσt_mem j hj_lt y
    have h2 := htt_mem j (le_of_lt hj_lt)
    have h3 := htt_mem (j + 1) hj_lt
    exact ⟨le_trans h2.1 h1.1, le_trans h1.2 h3.2⟩
  have hσt_cont : ∀ j, Continuous (σt j) := fun j => by
    change Continuous (fun y : ℝ => min (max y (tt j)) (tt (j + 1))); fun_prop
  set ρ : ℝ → ℝ := fun x => min (max x a) b
  have hρ_mem : ∀ x : ℝ, ρ x ∈ Set.Icc a b := by
    intro x
    exact ⟨le_min (le_max_right _ _) hab, min_le_right _ _⟩
  have hρ_eq_self : ∀ x ∈ Set.Icc a b, ρ x = x := by
    intro x hx
    change min (max x a) b = x
    rw [max_eq_left hx.1, min_eq_left hx.2]
  have hρ_cont : Continuous ρ := by
    change Continuous (fun x : ℝ => min (max x a) b); fun_prop
  -- Joint continuity of p ↦ u (f p) (g p) for continuous f, g into the rectangle.
  have h_comp_cont : ∀ f g : ℝ × ℝ → ℝ, Continuous f → Continuous g →
      (∀ p, f p ∈ Set.Icc a b) → (∀ p, g p ∈ Set.Icc c d) →
      Continuous fun p : ℝ × ℝ => u (f p) (g p) := by
    intro f g hf hg hf_mem hg_mem
    exact hu_cont.comp_continuous (hf.prodMk hg)
      (fun p => Set.mk_mem_prod (hf_mem p) (hg_mem p))
  -- Complex.log continuous on slitPlane.
  have h_log_contOn : ContinuousOn Complex.log Complex.slitPlane := fun z hz =>
    (Complex.differentiableAt_log hz).continuousAt.continuousWithinAt
  -- Define L.
  set L : ℝ → ℝ → ℂ := fun x y => Complex.log (u a c)
    + ∑ i ∈ Finset.range N, Complex.log (u (σs i x) c / u (ss i) c)
    + ∑ j ∈ Finset.range M, Complex.log (u (ρ x) (σt j y) / u (ρ x) (tt j))
  refine ⟨L, ?_, ?_⟩
  · -- Joint continuity of uncurry L.
    change Continuous fun p : ℝ × ℝ =>
      Complex.log (u a c)
      + ∑ i ∈ Finset.range N, Complex.log (u (σs i p.1) c / u (ss i) c)
      + ∑ j ∈ Finset.range M, Complex.log (u (ρ p.1) (σt j p.2) / u (ρ p.1) (tt j))
    refine Continuous.add (Continuous.add continuous_const ?_) ?_
    · -- s-direction sum: each term depends only on p.1.
      refine continuous_finsetSum _ ?_
      intro i hi
      have hi_lt : i < N := Finset.mem_range.mp hi
      have h_num_cont : Continuous (fun p : ℝ × ℝ => u (σs i p.1) c) :=
        h_comp_cont _ _ ((hσs_cont i).comp continuous_fst) continuous_const
          (fun p => hσs_mem_ab i hi_lt p.1) (fun _ => hc_mem)
      have h_quot_cont : Continuous (fun p : ℝ × ℝ => u (σs i p.1) c / u (ss i) c) :=
        h_num_cont.div_const _
      refine h_log_contOn.comp_continuous h_quot_cont (fun p => h_ball_slit ?_)
      exact h_quot_s_in_ball i hi_lt _ (hσs_mem i hi_lt p.1)
    · -- t-direction sum: jointly continuous via the clamps ρ and σt.
      refine continuous_finsetSum _ ?_
      intro j hj
      have hj_lt : j < M := Finset.mem_range.mp hj
      have h_num_cont : Continuous (fun p : ℝ × ℝ => u (ρ p.1) (σt j p.2)) :=
        h_comp_cont _ _ (hρ_cont.comp continuous_fst) ((hσt_cont j).comp continuous_snd)
          (fun p => hρ_mem p.1) (fun p => hσt_mem_cd j hj_lt p.2)
      have h_den_cont : Continuous (fun p : ℝ × ℝ => u (ρ p.1) (tt j)) :=
        h_comp_cont _ _ (hρ_cont.comp continuous_fst) continuous_const
          (fun p => hρ_mem p.1) (fun _ => htt_mem j (le_of_lt hj_lt))
      have h_quot_cont : Continuous
          (fun p : ℝ × ℝ => u (ρ p.1) (σt j p.2) / u (ρ p.1) (tt j)) :=
        h_num_cont.div h_den_cont
          (fun p => hu_ne _ (hρ_mem p.1) _ (htt_mem j (le_of_lt hj_lt)))
      refine h_log_contOn.comp_continuous h_quot_cont (fun p => h_ball_slit ?_)
      exact h_quot_t_in_ball (ρ p.1) (hρ_mem p.1) j hj_lt _ (hσt_mem j hj_lt p.2)
  · -- exp(L s t) = u s t for (s, t) in the rectangle.
    intro s hs_ab t ht_cd
    have h_ne_ac : u a c ≠ 0 := hu_ne a ha_mem c hc_mem
    have h_ne_sc : u s c ≠ 0 := hu_ne s hs_ab c hc_mem
    have h_ne_st : u s t ≠ 0 := hu_ne s hs_ab t ht_cd
    have h_log_quot_s : ∀ i ∈ Finset.range N,
        Complex.exp (Complex.log (u (σs i s) c / u (ss i) c)) =
          u (σs i s) c / u (ss i) c := by
      intro i hi
      have hi_lt : i < N := Finset.mem_range.mp hi
      have h_ne_den : u (ss i) c ≠ 0 := hu_ne _ (hss_mem i (le_of_lt hi_lt)) c hc_mem
      have h_ne_num : u (σs i s) c ≠ 0 := hu_ne _ (hσs_mem_ab i hi_lt s) c hc_mem
      exact Complex.exp_log (div_ne_zero h_ne_num h_ne_den)
    have h_log_quot_t : ∀ j ∈ Finset.range M,
        Complex.exp (Complex.log (u s (σt j t) / u s (tt j))) =
          u s (σt j t) / u s (tt j) := by
      intro j hj
      have hj_lt : j < M := Finset.mem_range.mp hj
      have h_ne_den : u s (tt j) ≠ 0 := hu_ne s hs_ab _ (htt_mem j (le_of_lt hj_lt))
      have h_ne_num : u s (σt j t) ≠ 0 := hu_ne s hs_ab _ (hσt_mem_cd j hj_lt t)
      exact Complex.exp_log (div_ne_zero h_ne_num h_ne_den)
    -- s-direction telescoping: the s-product evaluates to u s c / u a c.
    have h_prod_s_eval :
        ∏ i ∈ Finset.range N, (u (σs i s) c / u (ss i) c) = u s c / u a c := by
      have h_exists_s : ∃ i, i < N ∧ s ≤ ss (i + 1) := by
        refine ⟨N - 1, Nat.sub_lt hN_pos Nat.one_pos, ?_⟩
        have h_succ : N - 1 + 1 = N := Nat.sub_add_cancel hN_pos
        rw [h_succ, hssN]; exact hs_ab.2
      let k : ℕ := Nat.find h_exists_s
      have hk_spec := Nat.find_spec h_exists_s
      have hk_lt : k < N := hk_spec.1
      have hs_le : s ≤ ss (k + 1) := hk_spec.2
      have hk_le_N : k ≤ N := le_of_lt hk_lt
      have hk_le_s : ss k ≤ s := by
        by_cases hk_zero : k = 0
        · rw [hk_zero, hss0]; exact hs_ab.1
        · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_zero
          have h_pred_lt : k - 1 < k := Nat.sub_lt hk_pos Nat.one_pos
          have h_not := Nat.find_min h_exists_s h_pred_lt
          simp only [not_and, not_le] at h_not
          have h_pred_lt_N : k - 1 < N := lt_trans h_pred_lt hk_lt
          have h_lt := h_not h_pred_lt_N
          have h_pred_succ : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
          rw [h_pred_succ] at h_lt
          exact le_of_lt h_lt
      have hσs_lt_k : ∀ i, i < k → σs i s = ss (i + 1) := by
        intro i hik
        change min (max s (ss i)) (ss (i + 1)) = ss (i + 1)
        have h_succ_le : ss (i + 1) ≤ ss k := hss_mono hik
        have h_succ_le_s : ss (i + 1) ≤ s := le_trans h_succ_le hk_le_s
        have h_i_le_s : ss i ≤ s := le_trans (hss_le_succ i) h_succ_le_s
        rw [max_eq_left h_i_le_s, min_eq_right h_succ_le_s]
      have hσs_eq_k : σs k s = s := by
        change min (max s (ss k)) (ss (k + 1)) = s
        rw [max_eq_left hk_le_s, min_eq_left hs_le]
      have hσs_gt_k : ∀ i, k < i → σs i s = ss i := by
        intro i hik
        change min (max s (ss i)) (ss (i + 1)) = ss i
        have h_succ_le_i : ss (k + 1) ≤ ss i := hss_mono hik
        have h_s_le_i : s ≤ ss i := le_trans hs_le h_succ_le_i
        rw [max_eq_right h_s_le_i, min_eq_left (hss_le_succ i)]
      have h_split : Finset.range N =
          Finset.range k ∪ {k} ∪ Finset.Ico (k + 1) N := by
        ext i
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton, Finset.mem_Ico]
        constructor
        · intro hi
          rcases lt_trichotomy i k with hlt | heq | hgt
          · exact Or.inl (Or.inl hlt)
          · exact Or.inl (Or.inr heq)
          · exact Or.inr ⟨hgt, hi⟩
        · rintro ((hlt | heq) | ⟨hgt, hlt⟩)
          · exact lt_of_lt_of_le hlt hk_le_N
          · rw [heq]; exact hk_lt
          · exact hlt
      have h_disj_left : Disjoint (Finset.range k) ({k} : Finset ℕ) := by
        rw [Finset.disjoint_singleton_right]; exact Finset.notMem_range_self
      have h_disj_right : Disjoint (Finset.range k ∪ {k}) (Finset.Ico (k + 1) N) := by
        rw [Finset.disjoint_left]
        intro i hi hi_Ico
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton] at hi
        rw [Finset.mem_Ico] at hi_Ico
        omega
      rw [h_split, Finset.prod_union h_disj_right, Finset.prod_union h_disj_left,
          Finset.prod_singleton, hσs_eq_k]
      have h_telescope : ∀ k' ≤ N,
          ∏ i ∈ Finset.range k', u (ss (i + 1)) c / u (ss i) c =
            u (ss k') c / u (ss 0) c := by
        intro k' hk'
        induction k' with
        | zero =>
          have h_ne : u (ss 0) c ≠ 0 := hu_ne _ (hss_mem 0 (Nat.zero_le _)) c hc_mem
          simp [div_self h_ne]
        | succ n ih =>
          have hn_le : n ≤ N := Nat.le_of_succ_le hk'
          rw [Finset.prod_range_succ, ih hn_le]
          have h_ne_n : u (ss n) c ≠ 0 := hu_ne _ (hss_mem n hn_le) c hc_mem
          field_simp
      have h_prod_range_k : ∏ i ∈ Finset.range k, u (σs i s) c / u (ss i) c =
          u (ss k) c / u (ss 0) c := by
        have h_eq' : ∀ i ∈ Finset.range k,
            u (σs i s) c / u (ss i) c = u (ss (i + 1)) c / u (ss i) c := by
          intro i hi
          rw [hσs_lt_k i (Finset.mem_range.mp hi)]
        rw [Finset.prod_congr rfl h_eq', h_telescope k hk_le_N]
      have h_prod_Ico : ∏ i ∈ Finset.Ico (k + 1) N, u (σs i s) c / u (ss i) c = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        rw [Finset.mem_Ico] at hi
        rw [hσs_gt_k i hi.1, div_self (hu_ne _ (hss_mem i (le_of_lt hi.2)) c hc_mem)]
      rw [h_prod_range_k, h_prod_Ico, hss0, mul_one]
      have h_ne_k : u (ss k) c ≠ 0 := hu_ne _ (hss_mem k hk_le_N) c hc_mem
      field_simp
    -- t-direction telescoping (fixed first coordinate s): evaluates to u s t / u s c.
    have h_prod_t_eval :
        ∏ j ∈ Finset.range M, (u s (σt j t) / u s (tt j)) = u s t / u s c := by
      have h_exists_t : ∃ j, j < M ∧ t ≤ tt (j + 1) := by
        refine ⟨M - 1, Nat.sub_lt hM_pos Nat.one_pos, ?_⟩
        have h_succ : M - 1 + 1 = M := Nat.sub_add_cancel hM_pos
        rw [h_succ, httM]; exact ht_cd.2
      let m : ℕ := Nat.find h_exists_t
      have hm_spec := Nat.find_spec h_exists_t
      have hm_lt : m < M := hm_spec.1
      have ht_le : t ≤ tt (m + 1) := hm_spec.2
      have hm_le_M : m ≤ M := le_of_lt hm_lt
      have hm_le_t : tt m ≤ t := by
        by_cases hm_zero : m = 0
        · rw [hm_zero, htt0]; exact ht_cd.1
        · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_zero
          have h_pred_lt : m - 1 < m := Nat.sub_lt hm_pos Nat.one_pos
          have h_not := Nat.find_min h_exists_t h_pred_lt
          simp only [not_and, not_le] at h_not
          have h_pred_lt_M : m - 1 < M := lt_trans h_pred_lt hm_lt
          have h_lt := h_not h_pred_lt_M
          have h_pred_succ : m - 1 + 1 = m := Nat.sub_add_cancel hm_pos
          rw [h_pred_succ] at h_lt
          exact le_of_lt h_lt
      have hσt_lt_m : ∀ j, j < m → σt j t = tt (j + 1) := by
        intro j hjm
        change min (max t (tt j)) (tt (j + 1)) = tt (j + 1)
        have h_succ_le : tt (j + 1) ≤ tt m := htt_mono hjm
        have h_succ_le_t : tt (j + 1) ≤ t := le_trans h_succ_le hm_le_t
        have h_j_le_t : tt j ≤ t := le_trans (htt_le_succ j) h_succ_le_t
        rw [max_eq_left h_j_le_t, min_eq_right h_succ_le_t]
      have hσt_eq_m : σt m t = t := by
        change min (max t (tt m)) (tt (m + 1)) = t
        rw [max_eq_left hm_le_t, min_eq_left ht_le]
      have hσt_gt_m : ∀ j, m < j → σt j t = tt j := by
        intro j hjm
        change min (max t (tt j)) (tt (j + 1)) = tt j
        have h_succ_le_j : tt (m + 1) ≤ tt j := htt_mono hjm
        have h_t_le_j : t ≤ tt j := le_trans ht_le h_succ_le_j
        rw [max_eq_right h_t_le_j, min_eq_left (htt_le_succ j)]
      have h_split : Finset.range M =
          Finset.range m ∪ {m} ∪ Finset.Ico (m + 1) M := by
        ext j
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton, Finset.mem_Ico]
        constructor
        · intro hj
          rcases lt_trichotomy j m with hlt | heq | hgt
          · exact Or.inl (Or.inl hlt)
          · exact Or.inl (Or.inr heq)
          · exact Or.inr ⟨hgt, hj⟩
        · rintro ((hlt | heq) | ⟨hgt, hlt⟩)
          · exact lt_of_lt_of_le hlt hm_le_M
          · rw [heq]; exact hm_lt
          · exact hlt
      have h_disj_left : Disjoint (Finset.range m) ({m} : Finset ℕ) := by
        rw [Finset.disjoint_singleton_right]; exact Finset.notMem_range_self
      have h_disj_right : Disjoint (Finset.range m ∪ {m}) (Finset.Ico (m + 1) M) := by
        rw [Finset.disjoint_left]
        intro j hj hj_Ico
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton] at hj
        rw [Finset.mem_Ico] at hj_Ico
        omega
      rw [h_split, Finset.prod_union h_disj_right, Finset.prod_union h_disj_left,
          Finset.prod_singleton, hσt_eq_m]
      have h_telescope : ∀ m' ≤ M,
          ∏ j ∈ Finset.range m', u s (tt (j + 1)) / u s (tt j) =
            u s (tt m') / u s (tt 0) := by
        intro m' hm'
        induction m' with
        | zero =>
          have h_ne : u s (tt 0) ≠ 0 := hu_ne s hs_ab _ (htt_mem 0 (Nat.zero_le _))
          simp [div_self h_ne]
        | succ n ih =>
          have hn_le : n ≤ M := Nat.le_of_succ_le hm'
          rw [Finset.prod_range_succ, ih hn_le]
          have h_ne_n : u s (tt n) ≠ 0 := hu_ne s hs_ab _ (htt_mem n hn_le)
          field_simp
      have h_prod_range_m : ∏ j ∈ Finset.range m, u s (σt j t) / u s (tt j) =
          u s (tt m) / u s (tt 0) := by
        have h_eq' : ∀ j ∈ Finset.range m,
            u s (σt j t) / u s (tt j) = u s (tt (j + 1)) / u s (tt j) := by
          intro j hj
          rw [hσt_lt_m j (Finset.mem_range.mp hj)]
        rw [Finset.prod_congr rfl h_eq', h_telescope m hm_le_M]
      have h_prod_Ico : ∏ j ∈ Finset.Ico (m + 1) M, u s (σt j t) / u s (tt j) = 1 := by
        apply Finset.prod_eq_one
        intro j hj
        rw [Finset.mem_Ico] at hj
        rw [hσt_gt_m j hj.1, div_self (hu_ne s hs_ab _ (htt_mem j (le_of_lt hj.2)))]
      rw [h_prod_range_m, h_prod_Ico, htt0, mul_one]
      have h_ne_m : u s (tt m) ≠ 0 := hu_ne s hs_ab _ (htt_mem m hm_le_M)
      field_simp
    -- Assemble: exp(L s t) = u a c · (u s c / u a c) · (u s t / u s c) = u s t.
    change Complex.exp (Complex.log (u a c)
      + ∑ i ∈ Finset.range N, Complex.log (u (σs i s) c / u (ss i) c)
      + ∑ j ∈ Finset.range M, Complex.log (u (ρ s) (σt j t) / u (ρ s) (tt j))) = u s t
    rw [hρ_eq_self s hs_ab]
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_log h_ne_ac,
        Complex.exp_sum, Complex.exp_sum,
        Finset.prod_congr rfl h_log_quot_s, Finset.prod_congr rfl h_log_quot_t,
        h_prod_s_eval, h_prod_t_eval]
    field_simp


/-- **F_Y image-curve homotopy to a small CCW circle (with explicit
log-lift exposure).** For `w ∈ ℍ` and valid F_Y parameters with
`λ ≠ w` on each of the six boundary pieces, the composite image curve
`λ ∘ F_Y_boundary_parameterization` is homotopic in `ℂ \ {w}` to a
CCW unit circle around `w` (parameterized over the same `[0, 6]`
range, going once around with angular speed `π/3`).

The statement exposes the 1D continuous log lift `L` of `γ_image - w`
and the explicit log-space form
`H s t = w + exp((1 - s) · L t + s · i · t · π/3)`. Downstream code
uses the explicit form to translate the homotopy's intermediate-`s`
closure into a linear-algebra constraint on the winding integer.

Construction (log-space homotopy): let `u(t) := λ(γ(t)) - w` be the
shifted image curve (continuous on `Icc 0 6` and nonzero by the F_Y
boundary helpers, via `F_Y_image_curve_continuousOn` and
`F_Y_image_curve_ne_zero`). Apply
`continuous_log_lift_of_continuous_ne_zero_Icc` to obtain a continuous
`L : ℝ → ℂ` with `exp(L t) = u t` on `Icc 0 6`. Define
`H s t := w + exp((1 - s) · L t + s · i · t · π/3)`. At `s = 0`:
`H = w + exp(L t) = w + u(t) = λ(γ(t))`. At `s = 1`:
`H = w + exp(i · t · π/3) = circleMap w 1 (t · π/3)`. Avoidance is
automatic because `exp ≠ 0` everywhere. Continuity follows from
joint continuity of the exponential and the continuous lift. -/
theorem image_curve_lambda_F_Y_homotopic_to_circle
    {w : ℂ} (_hw : 0 < w.im) {δ Y R₀ : ℝ}
    (hδ : 0 < δ) (hδY : δ < Y) (hR₀_pos : 0 < R₀) (hR₀_lt : R₀ < 1 / 2)
    (_h_δR_lt_Y : δ + R₀ < Y)
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
      modularLambdaH (_root_.circleMap ((1 / 2 : ℂ) + (δ : ℂ) * Complex.I) R₀ θ) - w ≠ 0) :
    ∃ (ε : ℝ) (L : ℝ → ℂ) (H : ℝ → ℝ → ℂ),
      0 < ε ∧
      Continuous L ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 6,
        Complex.exp (L t) =
        modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w) ∧
      (∀ s t : ℝ, H s t = w +
        Complex.exp ((1 - (s : ℂ)) * L t + (s : ℂ) *
          (((t * Real.pi / 3 : ℝ) : ℂ) * Complex.I))) ∧
      ContinuousOn (Function.uncurry H)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 6) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 6,
        H 0 t = modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 6,
        H 1 t = _root_.circleMap w ε (t * Real.pi / 3)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 6, H s t ≠ w) := by
  -- Image curve is continuous on Icc 0 6.
  have h_u_cont : ContinuousOn
      (fun t : ℝ => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w)
      (Set.Icc (0 : ℝ) 6) :=
    F_Y_image_curve_continuousOn w hδ hδY hR₀_pos hR₀_lt
  -- Image curve is nonzero on Icc 0 6.
  have h_u_ne : ∀ t ∈ Set.Icc (0 : ℝ) 6,
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w ≠ 0 :=
    F_Y_image_curve_ne_zero hR₀_pos hR₀_lt hδY.le
      hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc
  -- Continuous log lift.
  obtain ⟨L, hL_cont, hL_exp⟩ :=
    continuous_log_lift_of_continuous_ne_zero_Icc
      (by norm_num : (0 : ℝ) ≤ 6)
      (fun t => modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t) - w)
      h_u_cont h_u_ne
  -- Construct the homotopy.
  refine ⟨1, L,
    fun s t => w +
      Complex.exp ((1 - (s : ℂ)) * L t + (s : ℂ) *
        (((t * Real.pi / 3 : ℝ) : ℂ) * Complex.I)),
    zero_lt_one, hL_cont, hL_exp, ?_, ?_, ?_, ?_, ?_⟩
  · -- H s t equals the explicit form.
    intro s t
    rfl
  · -- ContinuousOn (uncurry H) (Icc 0 1 ×ˢ Icc 0 6).
    refine Continuous.continuousOn ?_
    refine continuous_const.add ?_
    refine Complex.continuous_exp.comp ?_
    refine Continuous.add ?_ ?_
    · refine Continuous.mul ?_ (hL_cont.comp continuous_snd)
      exact continuous_const.sub (Complex.continuous_ofReal.comp continuous_fst)
    · refine Continuous.mul (Complex.continuous_ofReal.comp continuous_fst) ?_
      refine Continuous.mul ?_ continuous_const
      refine Complex.continuous_ofReal.comp ?_
      refine Continuous.div_const ?_ 3
      exact continuous_snd.mul continuous_const
  · -- H 0 t = λ(γ(t)).
    intro t ht
    have h_exp := hL_exp t ht
    change w + Complex.exp ((1 - ((0:ℝ) : ℂ)) * L t + ((0:ℝ) : ℂ) *
      (((t * Real.pi / 3 : ℝ) : ℂ) * Complex.I)) =
      modularLambdaH (F_Y_boundary_parameterization δ Y R₀ t)
    push_cast
    rw [show (1 - 0 : ℂ) = 1 from by ring, one_mul, zero_mul, add_zero, h_exp]
    ring
  · -- H 1 t = circleMap w 1 (t * π / 3).
    intro t _
    change w + Complex.exp ((1 - ((1:ℝ) : ℂ)) * L t + ((1:ℝ) : ℂ) *
      (((t * Real.pi / 3 : ℝ) : ℂ) * Complex.I)) =
      _root_.circleMap w 1 (t * Real.pi / 3)
    push_cast
    rw [show (1 - 1 : ℂ) = 0 from by ring, zero_mul, zero_add, one_mul]
    unfold _root_.circleMap
    push_cast; ring
  · -- H s t ≠ w (since exp ≠ 0).
    intro s _ t _ h_eq
    have h_exp_ne : Complex.exp ((1 - (s : ℂ)) * L t + (s : ℂ) *
      (((t * Real.pi / 3 : ℝ) : ℂ) * Complex.I)) ≠ 0 := Complex.exp_ne_zero _
    apply h_exp_ne
    linear_combination h_eq

/-- **Winding-integer extraction from a closed continuous log lift.**
For a continuous `L : ℝ → ℂ` with `exp(L a) = exp(L b)`, there is an
integer `K` such that `L b - L a = K · 2πi`.

This packages `Complex.exp_eq_one_iff`: a complex number with `exp = 1`
is `n · 2πi` for some `n : ℤ`. -/
theorem winding_lift_integer_coeff
    (L : ℝ → ℂ) {a b : ℝ} (hL_closed : Complex.exp (L a) = Complex.exp (L b)) :
    ∃ K : ℤ, L b - L a = (K : ℂ) * (2 * Real.pi * Complex.I) := by
  have h_exp_eq_one : Complex.exp (L b - L a) = 1 := by
    rw [Complex.exp_sub, hL_closed, div_self (Complex.exp_ne_zero _)]
  rw [Complex.exp_eq_one_iff] at h_exp_eq_one
  obtain ⟨n, hn⟩ := h_exp_eq_one
  exact ⟨n, hn⟩

/-- **Linear-algebra core: integer-valued affine function on `[0, 1]`
forces slope zero.** For `K : ℤ`, if the affine real function
`s ↦ K + s · (1 - K)` takes integer values at every `s ∈ [0, 1]`,
then `K = 1` (which makes the slope `1 - K = 0`).

Proof: apply the hypothesis at the irrational `s₀ := 1 / π ∈ (0, 1)`
(since `π > 3`). From `K + s₀ · (1 - K) = n` for some `n ∈ ℤ`, isolate
`s₀ · (1 - K) = n - K`. If `K ≠ 1`, the slope `1 - K` is a nonzero
integer; dividing yields `s₀ = (n - K) / (1 - K) ∈ ℚ`, contradicting
the irrationality of `1 / π` (Mathlib's `irrational_pi.inv`).

This is the load-bearing topological → algebraic translation: in the
hH_closed proof chain, the input "the H closure relation
`(L 6 − L 0) · (1 − s) + s · 2πi ∈ 2πi · ℤ` holds at every `s ∈ [0,1]`"
becomes "the affine map `s ↦ K + s(1 − K)` is integer-valued at every
`s`", and this lemma collapses it to `K = 1`. -/
theorem K_eq_one_of_affine_int_valued_on_unit_interval
    {K : ℤ}
    (h : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ n : ℤ, (K : ℝ) + s * (1 - K) = n) :
    K = 1 := by
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ_gt_3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπ_ne : Real.pi ≠ 0 := ne_of_gt hπ_pos
  have hπ_inv_mem : (1 / Real.pi : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · positivity
    · rw [div_le_one hπ_pos]; linarith
  obtain ⟨n, hn⟩ := h (1 / Real.pi) hπ_inv_mem
  by_contra hK_ne_one
  -- Multiply through by π: K · π + (1 − K) = n · π,
  -- i.e., π · (n − K) = 1 − K.
  have h_mul : Real.pi * ((n : ℝ) - K) = 1 - K := by
    have h_step : (Real.pi : ℝ) * ((K : ℝ) + 1 / Real.pi * (1 - (K : ℝ))) =
        Real.pi * ((n : ℝ)) := by
      rw [hn]
    field_simp at h_step
    linarith
  have h1K_ne : (1 - (K : ℝ)) ≠ 0 := by
    intro habs
    apply hK_ne_one
    have hK_eq : (K : ℝ) = 1 := by linarith
    exact_mod_cast hK_eq
  have hnK_ne : ((n : ℝ) - K) ≠ 0 := by
    intro habs
    rw [habs, mul_zero] at h_mul
    exact h1K_ne h_mul.symm
  -- So π = (1 − K)/(n − K), a rational.
  have h_pi_eq : Real.pi = ((1 - (K : ℝ))) / ((n : ℝ) - K) := by
    rw [eq_div_iff hnK_ne]; linarith
  have h_pi_rat : Real.pi = ((((1 - K : ℤ) : ℚ) / ((n - K : ℤ) : ℚ) : ℚ) : ℝ) := by
    rw [h_pi_eq]
    push_cast
    ring
  exact Irrational.ne_rat irrational_pi _ h_pi_rat

/-- **H closes at intermediate `s` when the winding integer is `K = 1`.**
Given a continuous log lift `L : ℝ → ℂ` with `L 6 − L 0 = 2πi`
(i.e., the winding integer of the image curve is `K = 1`), the
explicit log-space homotopy
`H s t = w + exp((1 − s) · L t + s · t · π/3 · i)` from
`image_curve_lambda_F_Y_homotopic_to_circle` is closed at every
intermediate `s`:
`∀ s ∈ [0, 1], H s 0 = H s 6`.

Direct algebra: at `t = 0`, the exponent is `(1 − s) · L 0`; at `t = 6`,
the exponent is `(1 − s) · L 6 + s · 2πi = (1 − s) · L 0 + 2πi` (using
`L 6 = L 0 + 2πi`). Since `exp(z + 2πi) = exp z`, the values agree. -/
theorem H_explicit_closed_of_K_eq_one
    (w : ℂ) (L : ℝ → ℂ)
    (hL_eq : L 6 - L 0 = (2 * Real.pi * Complex.I : ℂ)) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1,
      w + Complex.exp ((1 - (s : ℂ)) * L 0 + (s : ℂ) *
        (((0 * Real.pi / 3 : ℝ) : ℂ) * Complex.I)) =
      w + Complex.exp ((1 - (s : ℂ)) * L 6 + (s : ℂ) *
        (((6 * Real.pi / 3 : ℝ) : ℂ) * Complex.I)) := by
  intro s _
  congr 1
  -- L 6 = L 0 + 2πi.
  have hL6 : L 6 = L 0 + (2 * Real.pi * Complex.I : ℂ) := by linear_combination hL_eq
  -- Normalize the real coercions.
  have h0 : ((0 * Real.pi / 3 : ℝ) : ℂ) = 0 := by push_cast; ring
  have h6 : ((6 * Real.pi / 3 : ℝ) : ℂ) = 2 * Real.pi := by push_cast; ring
  rw [h0, h6, hL6]
  -- LHS exponent: A := (1 - s) * L 0 + s * (0 * I).
  -- RHS exponent: (1 - s) * (L 0 + 2πi) + s * (2π * I) = A + 2πi.
  -- exp(A + 2πi) = exp(A) by periodicity.
  rw [show (1 - (s : ℂ)) * (L 0 + (2 * Real.pi * Complex.I : ℂ)) +
       (s : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) =
       ((1 - (s : ℂ)) * L 0 + (s : ℂ) * (0 * Complex.I)) +
         (2 * Real.pi * Complex.I : ℂ) from by ring]
  exact (Complex.exp_periodic _).symm

end NoWanderingDomains
