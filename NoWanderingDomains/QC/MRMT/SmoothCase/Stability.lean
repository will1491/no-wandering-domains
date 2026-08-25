/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.MRMT.SmoothCase.Inverse

/-!
# The Ahlfors–Bers stability endgame

The uniform potential and image bounds, the resolvent stability of the
fixed-point field, locally uniform convergence of principal solutions under
almost-everywhere convergence of coefficients, the two-sided Hölder inequality
with constants uniform over the smooth family, and mollification of a Beltrami
coefficient.

* `cauchyTransform_sub_le_holder_uniform`, `isPrincipalSolution_uniform_image_bound`
  — the uniform estimates.
* `lp_fixedPoint_beltrami_stability` — resolvent stability.
* `isPrincipalSolution_tendstoUniformly_of_ae_tendsto` — convergence of solutions.
* `isPrincipalSolution_two_sided_holder` — the two-sided Hölder inequality.
* `exists_contDiff_mollification_beltrami` — mollification.
-/

open MeasureTheory Complex Filter
open scoped ContDiff ENNReal NNReal Topology

namespace NoWanderingDomains

/-! ## Uniform potential estimates -/

/-- **Uniform Hölder bound for the Cauchy transform** — the family-uniform form
of the proved `cauchyTransform_sub_le_holder`: a constant `C = C(p, R)` with

`‖P h z₁ − P h z₂‖ ≤ C·‖h‖ₚ·‖z₁ − z₂‖^(1−2/p)`
for **every** field `h ∈ Lᵖ` (`p > 2`) vanishing outside the ball of radius
`R`. The difference kernel scales: `∫ |1/(ζ−z₁) − 1/(ζ−z₂)|^q dA =
c(q)·‖z₁ − z₂‖^(2−q)`, so the constant depends only on the exponent data. -/
theorem cauchyTransform_sub_le_holder_uniform {p : ℝ≥0∞} {R : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℂ → ℂ, MemLp h p volume →
      (∀ z : ℂ, R < ‖z‖ → h z = 0) →
      ∀ z₁ z₂ : ℂ, ‖cauchyTransform h z₁ - cauchyTransform h z₂‖
        ≤ C * (eLpNorm h p volume).toReal * ‖z₁ - z₂‖ ^ (1 - 2 / p.toReal) := by
  -- ===== Exponent bookkeeping: `pr > 2`, conjugate `qr ∈ (1,2)`, `α ∈ (0,1)` =====
  set pr : ℝ := p.toReal with hpr_def
  have hp0 : p ≠ 0 := (lt_trans (by norm_num : (0:ℝ≥0∞) < 2) hp).ne'
  have hpr2 : 2 < pr := by
    have h2 := (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hp').mpr hp
    simpa [← hpr_def] using h2
  have hpr0 : 0 < pr := lt_trans two_pos hpr2
  set qr : ℝ := (1 - pr⁻¹)⁻¹ with hqr_def
  have hainv0 : 0 < pr⁻¹ := inv_pos.mpr hpr0
  have hainv : pr⁻¹ < 2⁻¹ := by
    have hmul : pr * pr⁻¹ = 1 := mul_inv_cancel₀ hpr0.ne'
    nlinarith [hainv0, hpr2, hmul]
  have hb0 : 0 < 1 - pr⁻¹ := by
    have h12 : (2 : ℝ)⁻¹ < 1 := by norm_num
    linarith
  have hbinv0 : 0 < (1 - pr⁻¹)⁻¹ := inv_pos.mpr hb0
  have hbmul : (1 - pr⁻¹) * (1 - pr⁻¹)⁻¹ = 1 := mul_inv_cancel₀ hb0.ne'
  have hqr1 : 1 < qr := by
    rw [hqr_def]
    nlinarith [hbmul, mul_pos hainv0 hbinv0, hbinv0]
  have hqr2 : qr < 2 := by
    rw [hqr_def]
    nlinarith [hbmul, hainv, hbinv0]
  have hqr0 : 0 < qr := lt_trans one_pos hqr1
  have hpq : pr.HolderConjugate qr := by
    refine ⟨?_, hpr0, hqr0⟩
    rw [hqr_def, inv_inv, inv_one]
    ring
  set α : ℝ := 1 - 2 / pr with hα_def
  have hα0 : 0 < α := by
    rw [hα_def]
    have hlt : 2 / pr < 1 := (div_lt_one hpr0).mpr hpr2
    linarith
  have hαqr : (2 - qr) / qr = α := by
    have h1qr : qr⁻¹ = 1 - pr⁻¹ := by rw [hqr_def, inv_inv]
    rw [hα_def, div_eq_mul_inv, sub_mul, mul_inv_cancel₀ hqr0.ne', h1qr]
    ring
  -- ===== Global constants (independent of the field `h`) =====
  set κ₁ : ℝ := (2 * Real.pi / (2 - qr)) ^ (1/qr) with hκ₁_def
  set κ₂ : ℝ := (2 * Real.pi / (2*qr - 2)) ^ (1/qr) with hκ₂_def
  have hκ₁0 : 0 ≤ κ₁ := Real.rpow_nonneg (div_nonneg (by positivity) (by linarith)) _
  have hκ₂0 : 0 ≤ κ₂ := Real.rpow_nonneg (div_nonneg (by positivity) (by linarith)) _
  set κ : ℝ := κ₁ * 2 ^ α + κ₁ * 3 ^ α + κ₂ * 2 ^ α with hκ_def
  have h2α : (0:ℝ) ≤ 2 ^ α := Real.rpow_nonneg (by norm_num) _
  have h3α : (0:ℝ) ≤ 3 ^ α := Real.rpow_nonneg (by norm_num) _
  have hκ0 : 0 ≤ κ := by
    rw [hκ_def]
    have := mul_nonneg hκ₁0 h2α
    have := mul_nonneg hκ₁0 h3α
    have := mul_nonneg hκ₂0 h2α
    linarith
  -- ===== Radial kernel integrals =====
  -- pointwise: `‖w⁻¹‖ₑ ^ qr = ofReal (‖w‖ ^ (-qr))`
  have hpt : ∀ w : ℂ, ‖w⁻¹‖ₑ ^ qr = ENNReal.ofReal (‖w‖ ^ (-qr)) := fun w => by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hqr0.le,
      norm_inv, Real.inv_rpow (norm_nonneg w), ← Real.rpow_neg (norm_nonneg w)]
  -- `‖·‖^(-qr)` is integrable on balls (dimension 2, `qr < 2`)
  have hnegpow_int : ∀ r : ℝ, 0 < r →
      IntegrableOn (fun w : ℂ => ‖w‖ ^ (-qr)) (Metric.ball (0:ℂ) r) volume := by
    intro r hr
    rw [← integrable_indicator_iff measurableSet_ball]
    set F : ℝ → ℝ := fun t : ℝ => if t < r then t ^ (-qr) else 0 with hF
    have heq : (Metric.ball (0:ℂ) r).indicator (fun w : ℂ => ‖w‖ ^ (-qr))
        = fun w : ℂ => F ‖w‖ := by
      funext w
      simp only [Set.indicator, hF]
      by_cases hw : w ∈ Metric.ball (0:ℂ) r
      · rw [if_pos hw]
        have hwr : ‖w‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        rw [if_pos hwr]
      · rw [if_neg hw]
        have hwr : ¬ ‖w‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        rw [if_neg hwr]
    rw [heq]
    rw [show (fun w : ℂ => F ‖w‖) = (F ‖·‖) from rfl]
    rw [integrable_fun_norm_addHaar volume]
    rw [Complex.finrank_real_complex]
    have hbase : IntegrableOn
        ((Set.Ioo (0 : ℝ) r).indicator fun y : ℝ => y ^ (1 - qr)) (Set.Ioi 0) volume := by
      rw [integrableOn_indicator_iff measurableSet_Ioo]
      have hsub : Set.Ioo (0 : ℝ) r ∩ Set.Ioi 0 = Set.Ioo (0 : ℝ) r :=
        Set.inter_eq_left.mpr fun y hy => hy.1
      rw [hsub, intervalIntegral.integrableOn_Ioo_rpow_iff hr]
      linarith
    apply hbase.congr_fun _ measurableSet_Ioi
    intro y hy
    simp only [Set.mem_Ioi] at hy
    simp only [hF, smul_eq_mul, Set.indicator]
    by_cases hyR : y < r
    · rw [if_pos ⟨hy, hyR⟩, if_pos hyR,
        show (1 - qr) = (1 : ℝ) + (-qr) by ring, Real.rpow_add hy, Real.rpow_one]
      norm_num
    · rw [if_neg fun hc => hyR hc.2, if_neg hyR, mul_zero]
  -- explicit value bound on the ball
  have hball_val : ∀ r : ℝ, 0 < r →
      ∫ w in Metric.ball (0:ℂ) r, ‖w‖ ^ (-qr) ≤ 2 * Real.pi / (2 - qr) * r ^ (2 - qr) := by
    intro r hr
    set f : ℝ → ℝ := fun t => if t < r then t ^ (-qr) else 0 with hf
    have hconv : ∫ w in Metric.ball (0:ℂ) r, ‖w‖ ^ (-qr) = ∫ x : ℂ, f ‖x‖ := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hx : x ∈ Metric.ball (0:ℂ) r
      · rw [Set.indicator_of_mem hx]
        simp only [hf]
        rw [Metric.mem_ball, dist_zero_right] at hx
        rw [if_pos hx]
      · rw [Set.indicator_of_notMem hx]
        simp only [hf]
        rw [Metric.mem_ball, dist_zero_right] at hx
        rw [if_neg hx]
    rw [hconv]
    rw [integral_fun_norm_addHaar volume f, Complex.finrank_real_complex]
    have hvol : volume.real (Metric.ball (0:ℂ) 1) = Real.pi := by
      rw [Measure.real, Complex.volume_ball]; simp
    rw [hvol]
    have hinner : ∫ y in Set.Ioi (0:ℝ), y ^ (2 - 1) • f y = r ^ (2 - qr) / (2 - qr) := by
      have hsub' : ∫ y in Set.Ioi (0:ℝ), y ^ (2 - 1) • f y
          = ∫ y in Set.Ioo (0:ℝ) r, y ^ (2 - 1) • f y := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        · intro x hx
          simp only [Set.mem_Ioo, Set.mem_Ioi] at *
          exact hx.1
        · intro x hx
          simp only [Set.mem_Ioi, Set.mem_Ioo, Set.mem_sdiff, not_and, not_lt] at hx
          obtain ⟨hx0, hxR⟩ := hx
          have hnlt : ¬ (x < r) := not_lt.mpr (hxR hx0)
          rw [hf]; simp only [if_neg hnlt, smul_zero]
      rw [hsub']
      have hcongr : ∫ y in Set.Ioo (0:ℝ) r, y ^ (2 - 1) • f y
          = ∫ y in Set.Ioo (0:ℝ) r, y ^ (1 - qr) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro y hy
        simp only [Set.mem_Ioo] at hy
        rw [hf]
        simp only [if_pos hy.2]
        rw [pow_one, smul_eq_mul]
        rw [show y * y ^ (-qr) = y ^ (1:ℝ) * y ^ (-qr) by rw [Real.rpow_one]]
        rw [← Real.rpow_add hy.1]
        ring_nf
      rw [hcongr]
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
      rw [integral_rpow (Or.inl (by linarith))]
      have h1 : (1 : ℝ) - qr + 1 = 2 - qr := by ring
      rw [h1, Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < 2 - qr))]
      ring
    rw [hinner]
    rw [le_iff_lt_or_eq]; right
    rw [nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
  -- translation of set-lintegrals to the origin
  have htransl : ∀ S₀ : Set ℂ, MeasurableSet S₀ → ∀ (g : ℂ → ℝ≥0∞) (y : ℂ),
      ∫⁻ ζ in {ζ : ℂ | ζ - y ∈ S₀}, g (ζ - y) = ∫⁻ w in S₀, g w := by
    intro S₀ hS₀ g y
    have hpre : MeasurableSet {ζ : ℂ | ζ - y ∈ S₀} := (measurable_id.sub_const y) hS₀
    calc ∫⁻ ζ in {ζ : ℂ | ζ - y ∈ S₀}, g (ζ - y)
        = ∫⁻ ζ, ({ζ : ℂ | ζ - y ∈ S₀}).indicator (fun ζ => g (ζ - y)) ζ := by
          rw [lintegral_indicator hpre]
      _ = ∫⁻ ζ, S₀.indicator g (ζ - y) := by
          apply lintegral_congr
          intro ζ
          unfold Set.indicator
          by_cases hζ : ζ - y ∈ S₀
          · rw [if_pos hζ, if_pos (by exact hζ)]
          · rw [if_neg hζ, if_neg (by exact hζ)]
      _ = ∫⁻ ζ, S₀.indicator g ζ := lintegral_sub_right_eq_self _ y
      _ = ∫⁻ w in S₀, g w := by rw [lintegral_indicator hS₀]
  -- ball kernel bound (single pole)
  have hballE : ∀ (y : ℂ) (r : ℝ), 0 < r →
      ∫⁻ ζ in Metric.ball y r, ‖(ζ - y)⁻¹‖ₑ ^ qr
        ≤ ENNReal.ofReal (2 * Real.pi / (2 - qr) * r ^ (2 - qr)) := by
    intro y r hr
    have hset : Metric.ball y r = {ζ : ℂ | ζ - y ∈ Metric.ball (0:ℂ) r} := by
      ext ζ
      simp [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc ∫⁻ ζ in Metric.ball y r, ‖(ζ - y)⁻¹‖ₑ ^ qr
        = ∫⁻ w in Metric.ball (0:ℂ) r, ‖w⁻¹‖ₑ ^ qr := by
          rw [hset]
          exact htransl _ measurableSet_ball (fun w => ‖w⁻¹‖ₑ ^ qr) y
      _ = ∫⁻ w in Metric.ball (0:ℂ) r, ENNReal.ofReal (‖w‖ ^ (-qr)) := lintegral_congr hpt
      _ = ENNReal.ofReal (∫ w in Metric.ball (0:ℂ) r, ‖w‖ ^ (-qr)) :=
          (ofReal_integral_eq_lintegral_ofReal (hnegpow_int r hr)
            (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (norm_nonneg w) _)).symm
      _ ≤ ENNReal.ofReal (2 * Real.pi / (2 - qr) * r ^ (2 - qr)) :=
          ENNReal.ofReal_le_ofReal (hball_val r hr)
  -- annulus integrability (exponent `2qr > 2` at infinity)
  have hann_int : ∀ r : ℝ, 0 < r →
      IntegrableOn (fun w : ℂ => ‖w‖ ^ (-(2*qr))) {w : ℂ | r ≤ ‖w‖} volume := by
    intro r hr
    have hSmeas : MeasurableSet {w : ℂ | r ≤ ‖w‖} :=
      measurableSet_le measurable_const measurable_norm
    rw [← integrable_indicator_iff hSmeas]
    set F : ℝ → ℝ := fun t : ℝ => if r ≤ t then t ^ (-(2*qr)) else 0 with hF
    have heq : ({w : ℂ | r ≤ ‖w‖}).indicator (fun w : ℂ => ‖w‖ ^ (-(2*qr)))
        = fun w : ℂ => F ‖w‖ := by
      funext w
      simp only [Set.indicator, hF]
      by_cases hw : w ∈ {w : ℂ | r ≤ ‖w‖}
      · rw [if_pos hw, if_pos (by exact hw)]
      · rw [if_neg hw, if_neg (by exact hw)]
    rw [heq]
    rw [show (fun w : ℂ => F ‖w‖) = (F ‖·‖) from rfl]
    rw [integrable_fun_norm_addHaar volume]
    rw [Complex.finrank_real_complex]
    have hbase : IntegrableOn
        ((Set.Ici r).indicator fun y : ℝ => y ^ (1 - 2*qr)) (Set.Ioi 0) volume := by
      rw [integrableOn_indicator_iff measurableSet_Ici]
      have hsub : Set.Ici r ∩ Set.Ioi 0 = Set.Ici r :=
        Set.inter_eq_left.mpr fun y hy => lt_of_lt_of_le hr hy
      rw [hsub, integrableOn_Ici_iff_integrableOn_Ioi, integrableOn_Ioi_rpow_iff hr]
      linarith
    apply hbase.congr_fun _ measurableSet_Ioi
    intro y hy
    simp only [Set.mem_Ioi] at hy
    simp only [hF, smul_eq_mul, Set.indicator, Set.mem_Ici]
    by_cases hyr : r ≤ y
    · rw [if_pos hyr, if_pos hyr,
        show (1 - 2*qr) = (1 : ℝ) + (-(2*qr)) by ring, Real.rpow_add hy, Real.rpow_one]
      norm_num
    · rw [if_neg hyr, if_neg hyr, mul_zero]
  -- explicit value bound on the annulus
  have hann_val : ∀ r : ℝ, 0 < r →
      ∫ w in {w : ℂ | r ≤ ‖w‖}, ‖w‖ ^ (-(2*qr))
        ≤ 2 * Real.pi / (2*qr - 2) * r ^ (2 - 2*qr) := by
    intro r hr
    set F : ℝ → ℝ := fun t : ℝ => if r ≤ t then t ^ (-(2*qr)) else 0 with hF
    have hSmeas : MeasurableSet {w : ℂ | r ≤ ‖w‖} :=
      measurableSet_le measurable_const measurable_norm
    have hconv : ∫ w in {w : ℂ | r ≤ ‖w‖}, ‖w‖ ^ (-(2*qr)) = ∫ x : ℂ, F ‖x‖ := by
      rw [← integral_indicator hSmeas]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hx : x ∈ {w : ℂ | r ≤ ‖w‖}
      · rw [Set.indicator_of_mem hx]
        simp only [hF]
        rw [if_pos (by exact hx)]
      · rw [Set.indicator_of_notMem hx]
        simp only [hF]
        rw [if_neg (by exact hx)]
    rw [hconv]
    rw [integral_fun_norm_addHaar volume F, Complex.finrank_real_complex]
    have hvol : volume.real (Metric.ball (0:ℂ) 1) = Real.pi := by
      rw [Measure.real, Complex.volume_ball]; simp
    rw [hvol]
    have hinner : ∫ y in Set.Ioi (0:ℝ), y ^ (2 - 1) • F y = r ^ (2 - 2*qr) / (2*qr - 2) := by
      have hsub' : ∫ y in Set.Ioi (0:ℝ), y ^ (2 - 1) • F y
          = ∫ y in Set.Ici r, y ^ (2 - 1) • F y := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        · intro y hy
          exact lt_of_lt_of_le hr hy
        · intro y hy
          simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_Ici, not_le] at hy
          rw [hF]
          simp only [if_neg (not_le.mpr hy.2), smul_zero]
      rw [hsub']
      have hcongr : ∫ y in Set.Ici r, y ^ (2 - 1) • F y
          = ∫ y in Set.Ici r, y ^ (1 - 2*qr) := by
        apply setIntegral_congr_fun measurableSet_Ici
        intro y hy
        simp only [Set.mem_Ici] at hy
        have hy0 : 0 < y := lt_of_lt_of_le hr hy
        rw [hF]
        simp only [if_pos hy]
        rw [pow_one, smul_eq_mul]
        rw [show y * y ^ (-(2*qr)) = y ^ (1:ℝ) * y ^ (-(2*qr)) by rw [Real.rpow_one]]
        rw [← Real.rpow_add hy0]
        ring_nf
      rw [hcongr, integral_Ici_eq_integral_Ioi,
        integral_Ioi_rpow_of_lt (by linarith : (1:ℝ) - 2*qr < -1) hr]
      rw [show (1:ℝ) - 2*qr + 1 = 2 - 2*qr from by ring]
      rw [neg_div, ← div_neg, show -(2 - 2*qr) = 2*qr - 2 from by ring]
    rw [hinner]
    rw [le_iff_lt_or_eq]; right
    rw [nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
  -- annulus kernel bound (single pole)
  have hannE : ∀ (y : ℂ) (r : ℝ), 0 < r →
      ∫⁻ ζ in {ζ : ℂ | r ≤ ‖ζ - y‖}, ENNReal.ofReal (‖ζ - y‖ ^ (-(2*qr)))
        ≤ ENNReal.ofReal (2 * Real.pi / (2*qr - 2) * r ^ (2 - 2*qr)) := by
    intro y r hr
    have hSmeas : MeasurableSet {w : ℂ | r ≤ ‖w‖} :=
      measurableSet_le measurable_const measurable_norm
    have hset : {ζ : ℂ | r ≤ ‖ζ - y‖} = {ζ : ℂ | ζ - y ∈ {w : ℂ | r ≤ ‖w‖}} := rfl
    calc ∫⁻ ζ in {ζ : ℂ | r ≤ ‖ζ - y‖}, ENNReal.ofReal (‖ζ - y‖ ^ (-(2*qr)))
        = ∫⁻ w in {w : ℂ | r ≤ ‖w‖}, ENNReal.ofReal (‖w‖ ^ (-(2*qr))) := by
          rw [hset]
          exact htransl _ hSmeas (fun w => ENNReal.ofReal (‖w‖ ^ (-(2*qr)))) y
      _ = ENNReal.ofReal (∫ w in {w : ℂ | r ≤ ‖w‖}, ‖w‖ ^ (-(2*qr))) :=
          (ofReal_integral_eq_lintegral_ofReal (hann_int r hr)
            (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (norm_nonneg w) _)).symm
      _ ≤ ENNReal.ofReal (2 * Real.pi / (2*qr - 2) * r ^ (2 - 2*qr)) :=
          ENNReal.ofReal_le_ofReal (hann_val r hr)
  -- ===== Hölder machinery (field-free parts) =====
  have htri : ∀ a b : ℂ, ‖a - b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := fun a b => by
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_sub_le a b)
  have hscale : ∀ c r : ℝ, 0 ≤ c → 0 < r →
      ENNReal.ofReal (c * r ^ (2 - qr)) ^ (1/qr)
        = ENNReal.ofReal (c ^ (1/qr) * r ^ α) := by
    intro c r hc hr
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hc (Real.rpow_nonneg hr.le _))
        (le_of_lt (one_div_pos.mpr hqr0)),
      Real.mul_rpow hc (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le,
      mul_one_div, hαqr]
  -- ===== Exhibit the uniform constant, then quantify over the field =====
  refine ⟨1 / Real.pi * κ, mul_nonneg (by positivity) hκ0, ?_⟩
  intro h hh hsupp
  have hint : ∀ z : ℂ, Integrable (fun ζ => h ζ / (ζ - z)) volume := fun z =>
    integrable_div_sub_of_memLp_of_support hp hp' hh hsupp z
  set N : ℝ≥0∞ := eLpNorm h p volume with hN_def
  have hN_ne : N ≠ ⊤ := hh.2.ne
  have hNle : ∀ S : Set ℂ, (∫⁻ ζ in S, ‖h ζ‖ₑ ^ pr) ^ (1/pr) ≤ N := by
    intro S
    rw [hN_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp']
    exact ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _)
      (le_of_lt (one_div_pos.mpr hpr0))
  have hHolder : ∀ (S : Set ℂ) (k : ℂ → ℝ≥0∞), AEMeasurable k (volume.restrict S) →
      ∫⁻ ζ in S, ‖h ζ‖ₑ * k ζ ≤ N * (∫⁻ ζ in S, k ζ ^ qr) ^ (1/qr) := by
    intro S k hk
    calc ∫⁻ ζ in S, ‖h ζ‖ₑ * k ζ
        ≤ (∫⁻ ζ in S, ‖h ζ‖ₑ ^ pr) ^ (1/pr) * (∫⁻ ζ in S, k ζ ^ qr) ^ (1/qr) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq (hh.1.restrict.enorm) hk
      _ ≤ N * (∫⁻ ζ in S, k ζ ^ qr) ^ (1/qr) := mul_le_mul' (hNle S) le_rfl
  -- ===== Conclusion =====
  intro z₁ z₂
  by_cases hz : z₁ = z₂
  · rw [hz]
    simp [Real.zero_rpow hα0.ne']
  · set d : ℝ := ‖z₁ - z₂‖ with hd_def
    have hd : 0 < d := by
      rw [hd_def, norm_pos_iff]
      exact sub_ne_zero_of_ne hz
    set G : ℂ → ℂ := fun ζ => (ζ - z₁)⁻¹ - (ζ - z₂)⁻¹ with hG_def
    have hGmeas : Measurable G :=
      ((measurable_id.sub_const z₁).inv).sub ((measurable_id.sub_const z₂).inv)
    set A : Set ℂ := Metric.ball z₁ (2*d) with hA_def
    have hAmeas : MeasurableSet A := by rw [hA_def]; exact measurableSet_ball
    have hAc : Aᶜ = {ζ : ℂ | 2*d ≤ ‖ζ - z₁‖} := by
      rw [hA_def]
      ext ζ
      simp [Metric.mem_ball, dist_eq_norm, not_lt]
    have hA_sub : A ⊆ Metric.ball z₂ (3*d) := by
      intro ζ hζ
      rw [hA_def, Metric.mem_ball, dist_eq_norm] at hζ
      rw [Metric.mem_ball, dist_eq_norm]
      have hstep : ‖ζ - z₂‖ ≤ ‖ζ - z₁‖ + d := by
        calc ‖ζ - z₂‖ = ‖(ζ - z₁) + (z₁ - z₂)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖ζ - z₁‖ + ‖z₁ - z₂‖ := norm_add_le _ _
          _ = ‖ζ - z₁‖ + d := by rw [← hd_def]
      linarith
    -- pointwise off-ball bound
    have hGoff : ∀ ζ : ℂ, 2*d ≤ ‖ζ - z₁‖ →
        ‖G ζ‖ₑ ^ qr ≤ ENNReal.ofReal ((2*d) ^ qr)
          * ENNReal.ofReal (‖ζ - z₁‖ ^ (-(2*qr))) := by
      intro ζ hζ
      have ha0 : 0 < ‖ζ - z₁‖ := lt_of_lt_of_le (by positivity) hζ
      have hane : ζ - z₁ ≠ 0 := norm_pos_iff.mp ha0
      have hcge : ‖ζ - z₁‖ - d ≤ ‖ζ - z₂‖ := by
        have h1 : ‖ζ - z₁‖ - ‖z₂ - z₁‖ ≤ ‖(ζ - z₁) - (z₂ - z₁)‖ := norm_sub_norm_le _ _
        have h2 : (ζ - z₁) - (z₂ - z₁) = ζ - z₂ := by ring
        have h3 : ‖z₂ - z₁‖ = d := by rw [hd_def, norm_sub_rev]
        rw [h2, h3] at h1
        exact h1
      have hc0 : 0 < ‖ζ - z₂‖ := by linarith
      have hcne : ζ - z₂ ≠ 0 := norm_pos_iff.mp hc0
      have hbc : ‖ζ - z₁‖ ≤ 2 * ‖ζ - z₂‖ := by linarith
      have hGval : ‖G ζ‖ = d / (‖ζ - z₁‖ * ‖ζ - z₂‖) := by
        have hid : G ζ = (z₁ - z₂) / ((ζ - z₁) * (ζ - z₂)) := by
          simp only [hG_def]
          rw [inv_sub_inv hane hcne]
          congr 1
          ring
        rw [hid, norm_div, norm_mul]
      have hGle : ‖G ζ‖ ≤ 2*d / (‖ζ - z₁‖ * ‖ζ - z₁‖) := by
        rw [hGval, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hbc (mul_nonneg hd.le ha0.le)]
      have hsq : ‖ζ - z₁‖ ^ (2:ℝ) = ‖ζ - z₁‖ * ‖ζ - z₁‖ := by
        rw [show ((2:ℝ)) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast, pow_two]
      have hkey : (2*d / (‖ζ - z₁‖ * ‖ζ - z₁‖)) ^ qr
          = (2*d) ^ qr * ‖ζ - z₁‖ ^ (-(2*qr)) := by
        rw [Real.div_rpow (by positivity) (by positivity), ← hsq,
          ← Real.rpow_mul (norm_nonneg _), div_eq_mul_inv,
          ← Real.rpow_neg (norm_nonneg _)]
      calc ‖G ζ‖ₑ ^ qr
          ≤ ENNReal.ofReal (2*d / (‖ζ - z₁‖ * ‖ζ - z₁‖)) ^ qr := by
            refine ENNReal.rpow_le_rpow ?_ hqr0.le
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal hGle
        _ = ENNReal.ofReal ((2*d / (‖ζ - z₁‖ * ‖ζ - z₁‖)) ^ qr) :=
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hqr0.le
        _ = ENNReal.ofReal ((2*d) ^ qr * ‖ζ - z₁‖ ^ (-(2*qr))) := by rw [hkey]
        _ = ENNReal.ofReal ((2*d) ^ qr) * ENNReal.ofReal (‖ζ - z₁‖ ^ (-(2*qr))) :=
            ENNReal.ofReal_mul (by positivity)
    -- the three kernel-piece bounds
    have hE₁ : (∫⁻ ζ in A, ‖(ζ - z₁)⁻¹‖ₑ ^ qr) ^ (1/qr)
        ≤ ENNReal.ofReal (κ₁ * (2 ^ α * d ^ α)) := by
      calc (∫⁻ ζ in A, ‖(ζ - z₁)⁻¹‖ₑ ^ qr) ^ (1/qr)
          ≤ ENNReal.ofReal (2 * Real.pi / (2 - qr) * (2*d) ^ (2 - qr)) ^ (1/qr) :=
            ENNReal.rpow_le_rpow (hballE z₁ (2*d) (by positivity))
              (le_of_lt (one_div_pos.mpr hqr0))
        _ = ENNReal.ofReal ((2 * Real.pi / (2 - qr)) ^ (1/qr) * (2*d) ^ α) :=
            hscale _ _ (div_nonneg (by positivity) (by linarith)) (by positivity)
        _ = ENNReal.ofReal (κ₁ * (2 ^ α * d ^ α)) := by
            rw [hκ₁_def]
            congr 1
            rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hd.le]
    have hE₂ : (∫⁻ ζ in A, ‖(ζ - z₂)⁻¹‖ₑ ^ qr) ^ (1/qr)
        ≤ ENNReal.ofReal (κ₁ * (3 ^ α * d ^ α)) := by
      have hmono : ∫⁻ ζ in A, ‖(ζ - z₂)⁻¹‖ₑ ^ qr
          ≤ ∫⁻ ζ in Metric.ball z₂ (3*d), ‖(ζ - z₂)⁻¹‖ₑ ^ qr :=
        lintegral_mono_set hA_sub
      calc (∫⁻ ζ in A, ‖(ζ - z₂)⁻¹‖ₑ ^ qr) ^ (1/qr)
          ≤ ENNReal.ofReal (2 * Real.pi / (2 - qr) * (3*d) ^ (2 - qr)) ^ (1/qr) :=
            ENNReal.rpow_le_rpow
              (le_trans hmono (hballE z₂ (3*d) (by positivity)))
              (le_of_lt (one_div_pos.mpr hqr0))
        _ = ENNReal.ofReal ((2 * Real.pi / (2 - qr)) ^ (1/qr) * (3*d) ^ α) :=
            hscale _ _ (div_nonneg (by positivity) (by linarith)) (by positivity)
        _ = ENNReal.ofReal (κ₁ * (3 ^ α * d ^ α)) := by
            rw [hκ₁_def]
            congr 1
            rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hd.le]
    have hE₃ : (∫⁻ ζ in Aᶜ, ‖G ζ‖ₑ ^ qr) ^ (1/qr)
        ≤ ENNReal.ofReal (κ₂ * (2 ^ α * d ^ α)) := by
      have hstep : ∫⁻ ζ in Aᶜ, ‖G ζ‖ₑ ^ qr
          ≤ ENNReal.ofReal (2 * Real.pi / (2*qr - 2) * (2*d) ^ (2 - qr)) := by
        have h1 : ∫⁻ ζ in Aᶜ, ‖G ζ‖ₑ ^ qr
            ≤ ∫⁻ ζ in Aᶜ, ENNReal.ofReal ((2*d) ^ qr)
                * ENNReal.ofReal (‖ζ - z₁‖ ^ (-(2*qr))) := by
          refine setLIntegral_mono
            (measurable_const.mul
              ((?_ : Measurable fun ζ : ℂ => ‖ζ - z₁‖ ^ (-(2*qr))).ennreal_ofReal)) ?_
          · fun_prop
          · intro ζ hζ
            refine hGoff ζ ?_
            rw [hAc] at hζ
            exact hζ
        have h2 : ∫⁻ ζ in Aᶜ, ENNReal.ofReal ((2*d) ^ qr)
              * ENNReal.ofReal (‖ζ - z₁‖ ^ (-(2*qr)))
            = ENNReal.ofReal ((2*d) ^ qr)
              * ∫⁻ ζ in Aᶜ, ENNReal.ofReal (‖ζ - z₁‖ ^ (-(2*qr))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        have h3 : ∫⁻ ζ in Aᶜ, ENNReal.ofReal (‖ζ - z₁‖ ^ (-(2*qr)))
            ≤ ENNReal.ofReal (2 * Real.pi / (2*qr - 2) * (2*d) ^ (2 - 2*qr)) := by
          rw [hAc]
          exact hannE z₁ (2*d) (by positivity)
        calc ∫⁻ ζ in Aᶜ, ‖G ζ‖ₑ ^ qr
            ≤ ENNReal.ofReal ((2*d) ^ qr)
                * ∫⁻ ζ in Aᶜ, ENNReal.ofReal (‖ζ - z₁‖ ^ (-(2*qr))) := by
              rw [← h2]
              exact h1
          _ ≤ ENNReal.ofReal ((2*d) ^ qr)
                * ENNReal.ofReal (2 * Real.pi / (2*qr - 2) * (2*d) ^ (2 - 2*qr)) :=
              mul_le_mul' le_rfl h3
          _ = ENNReal.ofReal ((2*d) ^ qr
                * (2 * Real.pi / (2*qr - 2) * (2*d) ^ (2 - 2*qr))) :=
              (ENNReal.ofReal_mul (by positivity)).symm
          _ = ENNReal.ofReal (2 * Real.pi / (2*qr - 2) * (2*d) ^ (2 - qr)) := by
              congr 1
              rw [show (2*d) ^ qr * (2 * Real.pi / (2*qr - 2) * (2*d) ^ (2 - 2*qr))
                  = 2 * Real.pi / (2*qr - 2) * ((2*d) ^ qr * (2*d) ^ (2 - 2*qr)) from by ring,
                ← Real.rpow_add (by positivity : (0:ℝ) < 2*d)]
              rw [show qr + (2 - 2*qr) = 2 - qr from by ring]
      calc (∫⁻ ζ in Aᶜ, ‖G ζ‖ₑ ^ qr) ^ (1/qr)
          ≤ ENNReal.ofReal (2 * Real.pi / (2*qr - 2) * (2*d) ^ (2 - qr)) ^ (1/qr) :=
            ENNReal.rpow_le_rpow hstep (le_of_lt (one_div_pos.mpr hqr0))
        _ = ENNReal.ofReal ((2 * Real.pi / (2*qr - 2)) ^ (1/qr) * (2*d) ^ α) :=
            hscale _ _ (div_nonneg (by positivity) (by linarith)) (by positivity)
        _ = ENNReal.ofReal (κ₂ * (2 ^ α * d ^ α)) := by
            rw [hκ₂_def]
            congr 1
            rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hd.le]
    -- collect the constants
    have hsum : ENNReal.ofReal (κ₁ * (2 ^ α * d ^ α)) + ENNReal.ofReal (κ₁ * (3 ^ α * d ^ α))
          + ENNReal.ofReal (κ₂ * (2 ^ α * d ^ α))
        = ENNReal.ofReal (κ * d ^ α) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      rw [hκ_def]
      ring
    -- main estimate at the level of the integrals
    have hmain : ‖(∫ ζ, h ζ / (ζ - z₁)) - ∫ ζ, h ζ / (ζ - z₂)‖ₑ
        ≤ ENNReal.ofReal (N.toReal * (κ * d ^ α)) := by
      rw [← integral_sub (hint z₁) (hint z₂)]
      have hptG : (fun ζ => h ζ / (ζ - z₁) - h ζ / (ζ - z₂))
          =ᵐ[volume] fun ζ => h ζ * G ζ := by
        apply Filter.Eventually.of_forall
        intro ζ
        simp only [hG_def]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      calc ‖∫ ζ, (h ζ / (ζ - z₁) - h ζ / (ζ - z₂))‖ₑ
          = ‖∫ ζ, h ζ * G ζ‖ₑ := by rw [integral_congr_ae hptG]
        _ ≤ ∫⁻ ζ, ‖h ζ * G ζ‖ₑ := enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ ζ, ‖h ζ‖ₑ * ‖G ζ‖ₑ := lintegral_congr fun ζ => enorm_mul _ _
        _ = (∫⁻ ζ in A, ‖h ζ‖ₑ * ‖G ζ‖ₑ) + ∫⁻ ζ in Aᶜ, ‖h ζ‖ₑ * ‖G ζ‖ₑ :=
            (lintegral_add_compl _ hAmeas).symm
        _ ≤ (N * (∫⁻ ζ in A, ‖(ζ - z₁)⁻¹‖ₑ ^ qr) ^ (1/qr)
              + N * (∫⁻ ζ in A, ‖(ζ - z₂)⁻¹‖ₑ ^ qr) ^ (1/qr))
            + N * (∫⁻ ζ in Aᶜ, ‖G ζ‖ₑ ^ qr) ^ (1/qr) := by
            refine add_le_add ?_ (hHolder Aᶜ _ (hGmeas.enorm.aemeasurable.restrict))
            calc ∫⁻ ζ in A, ‖h ζ‖ₑ * ‖G ζ‖ₑ
                ≤ ∫⁻ ζ in A, (‖h ζ‖ₑ * ‖(ζ - z₁)⁻¹‖ₑ + ‖h ζ‖ₑ * ‖(ζ - z₂)⁻¹‖ₑ) := by
                  apply lintegral_mono
                  intro ζ
                  change ‖h ζ‖ₑ * ‖G ζ‖ₑ
                    ≤ ‖h ζ‖ₑ * ‖(ζ - z₁)⁻¹‖ₑ + ‖h ζ‖ₑ * ‖(ζ - z₂)⁻¹‖ₑ
                  rw [← mul_add]
                  exact mul_le_mul' le_rfl (htri _ _)
              _ = (∫⁻ ζ in A, ‖h ζ‖ₑ * ‖(ζ - z₁)⁻¹‖ₑ)
                    + ∫⁻ ζ in A, ‖h ζ‖ₑ * ‖(ζ - z₂)⁻¹‖ₑ :=
                  lintegral_add_left'
                    ((hh.1.restrict.enorm).mul
                      (((measurable_id.sub_const z₁).inv).enorm.aemeasurable.restrict)) _
              _ ≤ N * (∫⁻ ζ in A, ‖(ζ - z₁)⁻¹‖ₑ ^ qr) ^ (1/qr)
                    + N * (∫⁻ ζ in A, ‖(ζ - z₂)⁻¹‖ₑ ^ qr) ^ (1/qr) :=
                  add_le_add
                    (hHolder A _ (((measurable_id.sub_const z₁).inv).enorm.aemeasurable.restrict))
                    (hHolder A _ (((measurable_id.sub_const z₂).inv).enorm.aemeasurable.restrict))
        _ ≤ (N * ENNReal.ofReal (κ₁ * (2 ^ α * d ^ α))
              + N * ENNReal.ofReal (κ₁ * (3 ^ α * d ^ α)))
            + N * ENNReal.ofReal (κ₂ * (2 ^ α * d ^ α)) :=
            add_le_add (add_le_add (mul_le_mul' le_rfl hE₁) (mul_le_mul' le_rfl hE₂))
              (mul_le_mul' le_rfl hE₃)
        _ = N * (ENNReal.ofReal (κ₁ * (2 ^ α * d ^ α))
              + ENNReal.ofReal (κ₁ * (3 ^ α * d ^ α))
              + ENNReal.ofReal (κ₂ * (2 ^ α * d ^ α))) := by ring
        _ = N * ENNReal.ofReal (κ * d ^ α) := by rw [hsum]
        _ = ENNReal.ofReal (N.toReal * (κ * d ^ α)) := by
            rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hN_ne]
    -- pass to the real inequality and unfold the Cauchy transform
    have hnn : (0:ℝ) ≤ N.toReal * (κ * d ^ α) :=
      mul_nonneg ENNReal.toReal_nonneg (mul_nonneg hκ0 (Real.rpow_nonneg hd.le _))
    have hX : ‖(∫ ζ, h ζ / (ζ - z₁)) - ∫ ζ, h ζ / (ζ - z₂)‖ ≤ N.toReal * (κ * d ^ α) := by
      have h2 := hmain
      rw [← ofReal_norm] at h2
      exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h2
    have hPdiff : cauchyTransform h z₁ - cauchyTransform h z₂
        = -(1/(Real.pi:ℂ)) * ((∫ ζ, h ζ / (ζ - z₁)) - ∫ ζ, h ζ / (ζ - z₂)) := by
      rw [cauchyTransform, cauchyTransform, mul_sub]
    have hconst : ‖-(1/(Real.pi:ℂ))‖ = 1/Real.pi := by
      rw [norm_neg, norm_div, norm_one, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
    rw [hPdiff, norm_mul, hconst]
    calc 1/Real.pi * ‖(∫ ζ, h ζ / (ζ - z₁)) - ∫ ζ, h ζ / (ζ - z₂)‖
        ≤ 1/Real.pi * (N.toReal * (κ * d ^ α)) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = 1 / Real.pi * κ * N.toReal * d ^ α := by ring

/-- **Uniform image bound for principal solutions.** Over all coefficients of
dilatation at most `k < 1` supported in the ball of radius `R`, the principal
solutions displace points by a bounded amount: there is `R' = R'(k, R)` with
`‖f z‖ ≤ R'` whenever `‖z‖ ≤ R`. Choose `p = p(k) > 2` with the Neumann
contraction (`exists_p_gt_two_beurling_contraction`); the canonical field has
`‖h‖ₚ ≤ (1 − kC)⁻¹·‖μ‖ₚ ≤ (1 − kC)⁻¹·k·|B_R|^{1/p}`, and
`norm_cauchyTransform_le_of_memLp_support` bounds the displacement `‖P h‖_∞`.
Needed to place the supports of the inverse coefficients
(`IsPrincipalSolution.inverse_principalSolution_of_contDiff`) in a uniform
ball. -/
theorem isPrincipalSolution_uniform_image_bound {k R : ℝ}
    (hk0 : 0 ≤ k) (hk : k < 1) :
    ∃ R' : ℝ, R ≤ R' ∧ ∀ (b : BeltramiCoeff) (f : ℂ → ℂ),
      eLpNormEssSup b.μ volume ≤ ENNReal.ofReal k →
      (∀ z : ℂ, R < ‖z‖ → b.μ z = 0) →
      IsPrincipalSolution b f →
      ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ R' := by
  classical
  -- ===== Uniform exponent data: `p₀ > 2`, CZ bound `C₀` with `k·C₀ < 1`. =====
  set ε : ℝ := (1 - k) / 2 with hε_def
  have hεpos : 0 < ε := by rw [hε_def]; linarith
  obtain ⟨p₀, hp2, hptop, C₀, hClt, hCb⟩ := beurling_opNorm_continuous ε hεpos
  have hC0 : 0 ≤ C₀ := hCb.1
  have hkC : k * C₀ < 1 := by
    have h1 : k * C₀ ≤ k * (1 + ε) := mul_le_mul_of_nonneg_left hClt.le hk0
    have h2 : k * (1 + ε) < 1 := by rw [hε_def]; nlinarith
    linarith
  have h1pos : 0 < 1 - k * C₀ := by linarith
  -- ===== The uniform `Lᵖ⁰` bound for the coefficients: `M = |B|^{1/p₀}·k`. =====
  set m : ℝ := max R 0 with hm_def
  set B : Set ℂ := Metric.closedBall (0 : ℂ) m with hB_def
  have hBmeas : MeasurableSet B := by rw [hB_def]; exact measurableSet_closedBall
  have hBfin : volume B ≠ ⊤ := by
    rw [hB_def]; exact (isCompact_closedBall _ _).measure_lt_top.ne
  set M : ℝ≥0∞ := volume B ^ p₀.toReal⁻¹ * ENNReal.ofReal k with hM_def
  have hMfin : M ≠ ⊤ := by
    rw [hM_def]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hBfin)
      ENNReal.ofReal_ne_top
  -- ===== The uniform sup-norm constant for the Cauchy transform at `(p₀, R)`. =====
  obtain ⟨C₉, hC90, hC9⟩ := norm_cauchyTransform_le_of_memLp_support (R := R) hp2 hptop
  -- ===== The uniform displacement bound `D = (1 − kC₀)⁻¹·M`. =====
  set D : ℝ := (1 - k * C₀)⁻¹ * M.toReal with hD_def
  have hD0 : 0 ≤ D := by
    rw [hD_def]
    exact mul_nonneg (inv_nonneg.2 h1pos.le) ENNReal.toReal_nonneg
  refine ⟨R + C₉ * D, by linarith [mul_nonneg hC90 hD0], ?_⟩
  intro b f hkb hsupp hf
  -- The coefficient's essential bound is finite.
  have hμfin : eLpNormEssSup b.μ volume ≠ ⊤ :=
    (lt_of_le_of_lt hkb ENNReal.ofReal_lt_top).ne
  -- `b.μ ∈ Lᵖ⁰` with the quantitative bound `‖b.μ‖ₚ₀ ≤ M`.
  have hμLp : MemLp b.μ p₀ volume :=
    memLp_of_eLpNormEssSup_ne_top_of_support hptop b.measurable hμfin hsupp
  have hind : b.μ = B.indicator b.μ := by
    funext ζ
    by_cases hζ : ζ ∈ B
    · rw [Set.indicator_of_mem hζ]
    · rw [Set.indicator_of_notMem hζ]
      refine hsupp ζ ?_
      have hmζ : m < ‖ζ‖ := by
        simpa [hB_def, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
      exact lt_of_le_of_lt (le_max_left R 0) hmζ
  have hae_k : ∀ᵐ z ∂volume, ‖b.μ z‖ ≤ k := by
    filter_upwards [ae_le_eLpNormEssSup (f := b.μ) (μ := volume)] with z hz
    have h1 : ‖b.μ z‖ₑ ≤ ENNReal.ofReal k := le_trans hz hkb
    rwa [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hk0] at h1
  have hμM : eLpNorm b.μ p₀ volume ≤ M := by
    calc eLpNorm b.μ p₀ volume = eLpNorm (B.indicator b.μ) p₀ volume := by rw [← hind]
      _ = eLpNorm b.μ p₀ (volume.restrict B) :=
          eLpNorm_indicator_eq_eLpNorm_restrict hBmeas
      _ ≤ (volume.restrict B) Set.univ ^ p₀.toReal⁻¹ * ENNReal.ofReal k :=
          eLpNorm_le_of_ae_bound (ae_restrict_of_ae hae_k)
      _ = M := by rw [Measure.restrict_apply_univ, hM_def]
  -- Contraction at `b`'s essential bound.
  have ht : (eLpNormEssSup b.μ volume).toReal ≤ k :=
    ENNReal.toReal_le_of_le_ofReal hk0 hkb
  have hcontr : (eLpNormEssSup b.μ volume).toReal * C₀ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right ht hC0) hkC
  -- Solve the fixed-point equation with datum `b.μ`.
  obtain ⟨h, hLp, haeeq, hbound⟩ :=
    exists_lp_fixedPoint_beltrami hp2 hptop b.measurable hμfin hCb hcontr hμLp
  -- The everywhere-defined representative, vanishing pointwise outside the ball.
  set h' : ℂ → ℂ := fun z => b.μ z * beurling h z + b.μ z with hh'_def
  have hh'ae : h' =ᵐ[volume] h := haeeq.symm
  have hh'Lp : MemLp h' p₀ volume := hLp.ae_eq haeeq
  have hh'supp : ∀ z : ℂ, R < ‖z‖ → h' z = 0 := by
    intro z hz
    simp only [hh'_def]
    rw [hsupp z hz, zero_mul, zero_add]
  -- `L²` memberships (finite-measure embedding on the support ball).
  have hL2h' : MemLp h' 2 volume := by
    have : IsFiniteMeasure (volume.restrict B) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact lt_top_iff_ne_top.2 hBfin⟩
    have hind' : h' = B.indicator h' := by
      funext ζ
      by_cases hζ : ζ ∈ B
      · rw [Set.indicator_of_mem hζ]
      · rw [Set.indicator_of_notMem hζ]
        refine hh'supp ζ ?_
        have hmζ : m < ‖ζ‖ := by
          simpa [hB_def, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
        exact lt_of_le_of_lt (le_max_left R 0) hmζ
    rw [hind']
    exact (memLp_indicator_iff_restrict hBmeas).2 ((hh'Lp.restrict B).mono_exponent hp2.le)
  have hL2h : MemLp h 2 volume := hL2h'.ae_eq hh'ae
  -- The fixed-point equation transfers to `h'`.
  have hSeq : beurling h =ᵐ[volume] beurling h' := beurling_congr_ae hL2h hL2h' haeeq
  have heq' : h' =ᵐ[volume] (fun z => b.μ z * beurling h' z + b.μ z) := by
    filter_upwards [hSeq] with z hz
    rw [← hz]
  -- `f = id + P h'` by uniqueness of the principal solution.
  have hf0 : IsPrincipalSolution b (fun z => z + cauchyTransform h' z) :=
    ⟨p₀, h', R, hp2, hptop, hh'Lp, hh'supp, heq', fun z => rfl⟩
  have hfeq : f = fun z => z + cauchyTransform h' z := isPrincipalSolution_unique hf hf0
  -- The uniform norm bound on the field: `‖h'‖ₚ₀ ≤ (1 − kC₀)⁻¹·M`.
  have hnorm' : eLpNorm h' p₀ volume = eLpNorm h p₀ volume := eLpNorm_congr_ae hh'ae
  have hinv : (1 - (eLpNormEssSup b.μ volume).toReal * C₀)⁻¹ ≤ (1 - k * C₀)⁻¹ := by
    rw [← one_div, ← one_div]
    refine one_div_le_one_div_of_le h1pos ?_
    have := mul_le_mul_of_nonneg_right ht hC0
    linarith
  have hchain : eLpNorm h p₀ volume ≤ ENNReal.ofReal ((1 - k * C₀)⁻¹) * M :=
    le_trans hbound (mul_le_mul' (ENNReal.ofReal_le_ofReal hinv) hμM)
  have htoReal : (eLpNorm h' p₀ volume).toReal ≤ D := by
    rw [hnorm']
    have h1 : (eLpNorm h p₀ volume).toReal
        ≤ (ENNReal.ofReal ((1 - k * C₀)⁻¹) * M).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMfin) hchain
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 h1pos.le)] at h1
    rw [hD_def]
    exact h1
  -- Assemble: for `‖z‖ ≤ R`, `‖f z‖ ≤ ‖z‖ + ‖P h' z‖ ≤ R + C₉·D`.
  intro z hz
  have hPz : ‖cauchyTransform h' z‖ ≤ C₉ * (eLpNorm h' p₀ volume).toReal :=
    hC9 h' hh'Lp hh'supp z
  have hfz : f z = z + cauchyTransform h' z := by rw [hfeq]
  calc ‖f z‖ = ‖z + cauchyTransform h' z‖ := by rw [hfz]
    _ ≤ ‖z‖ + ‖cauchyTransform h' z‖ := norm_add_le _ _
    _ ≤ R + C₉ * D :=
        add_le_add hz (le_trans hPz (mul_le_mul_of_nonneg_left htoReal hC90))

/-! ## The Ahlfors–Bers endgame: stability, convergence, injectivity -/

/-- **Resolvent stability of the Beltrami fixed point** (AIM Lemma 5.3.1). Two
fixed points `hᵢ = μᵢ·S hᵢ + μᵢ` with common contraction data satisfy the
resolvent identity `h₁ − h₂ = μ₁·S(h₁ − h₂) + (μ₁ − μ₂)·(1 + S h₂)`, so the
Neumann bound controls their distance by the coefficient difference:

`‖h₁ − h₂‖ₚ ≤ (1 − kC)⁻¹·‖(μ₁ − μ₂)·(1 + S h₂)‖ₚ`.

With `μₙ → μ` a.e., uniformly bounded and commonly supported, dominated
convergence sends the right side to `0` — the quantitative engine of the
mollification limit. -/
theorem lp_fixedPoint_beltrami_stability {μ₁ μ₂ h₁ h₂ : ℂ → ℂ}
    {p : ℝ≥0∞} {C k : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤)
    (hμ₁ : Measurable μ₁) (hμ₂ : Measurable μ₂)
    (hk₁ : eLpNormEssSup μ₁ volume ≤ ENNReal.ofReal k)
    (_hk₂ : eLpNormEssSup μ₂ volume ≤ ENNReal.ofReal k)
    (hCb : IsCalderonZygmundBound beurling p C)
    (hk0 : 0 ≤ k) (hcontr : k * C < 1)
    (hh₁ : MemLp h₁ p volume) (hh₂ : MemLp h₂ p volume)
    (heq₁ : h₁ =ᵐ[volume] fun z => μ₁ z * beurling h₁ z + μ₁ z)
    (heq₂ : h₂ =ᵐ[volume] fun z => μ₂ z * beurling h₂ z + μ₂ z) :
    eLpNorm (fun z => h₁ z - h₂ z) p volume
      ≤ ENNReal.ofReal ((1 - k * C)⁻¹)
        * eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume := by
  classical
  have hp1 : (1 : ℝ≥0∞) ≤ p := le_of_lt (lt_trans (by norm_num : (1 : ℝ≥0∞) < 2) hp)
  obtain ⟨hC0, hCbound⟩ := hCb
  have hkC0 : 0 ≤ k * C := mul_nonneg hk0 hC0
  have h1pos : 0 < 1 - k * C := by linarith
  -- The difference field is in `Lᵖ`.
  have hd : MemLp (fun z => h₁ z - h₂ z) p volume := hh₁.sub hh₂
  -- Beurling sends `Lᵖ` to `Lᵖ`.
  have hbeurLp : ∀ {u : ℂ → ℂ}, MemLp u p volume → MemLp (beurling u) p volume :=
    fun {u} hu => memLp_beurling_of_memLp hp hp' hu
  -- Beurling subtractivity a.e. on `Lᵖ` (corollary of `beurling_add_ae_lp`).
  have hbsub : beurling (fun w => h₁ w - h₂ w) =ᵐ[volume] beurling h₁ - beurling h₂ := by
    have hadd := beurling_add_ae_lp hp hp' hh₂
      (show MemLp (fun w => h₁ w - h₂ w) p volume from hd)
    have hvuv : (h₂ + fun w => h₁ w - h₂ w) = h₁ := by funext w; simp
    rw [hvuv] at hadd
    filter_upwards [hadd] with z hz
    simp only [Pi.add_apply, Pi.sub_apply] at hz ⊢
    rw [hz]; ring
  -- The resolvent identity a.e.:
  -- `h₁ − h₂ = μ₁·S(h₁ − h₂) + (μ₁ − μ₂)·(1 + S h₂)`.
  have hres : (fun z => h₁ z - h₂ z) =ᵐ[volume]
      fun z => μ₁ z * beurling (fun w => h₁ w - h₂ w) z
        + (μ₁ z - μ₂ z) * (1 + beurling h₂ z) := by
    filter_upwards [heq₁, heq₂, hbsub] with z e₁ e₂ eb
    have e₁' : h₁ z = μ₁ z * beurling h₁ z + μ₁ z := e₁
    have e₂' : h₂ z = μ₂ z * beurling h₂ z + μ₂ z := e₂
    have eb' : beurling (fun w => h₁ w - h₂ w) z = beurling h₁ z - beurling h₂ z := eb
    change h₁ z - h₂ z
      = μ₁ z * beurling (fun w => h₁ w - h₂ w) z + (μ₁ z - μ₂ z) * (1 + beurling h₂ z)
    rw [e₁', e₂', eb']
    ring
  -- Measurability of the two resolvent terms.
  have hT1m : AEStronglyMeasurable
      (fun z => μ₁ z * beurling (fun w => h₁ w - h₂ w) z) volume :=
    hμ₁.aestronglyMeasurable.mul (hbeurLp hd).aestronglyMeasurable
  have hT2m : AEStronglyMeasurable
      (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) volume :=
    (hμ₁.sub hμ₂).aestronglyMeasurable.mul
      (aestronglyMeasurable_const.add (hbeurLp hh₂).aestronglyMeasurable)
  -- The contraction bound on the first term:
  -- `‖μ₁·S(h₁−h₂)‖ₚ ≤ (k·C)·‖h₁−h₂‖ₚ`.
  have hT1bound : eLpNorm (fun z => μ₁ z * beurling (fun w => h₁ w - h₂ w) z) p volume
      ≤ ENNReal.ofReal (k * C) * eLpNorm (fun z => h₁ z - h₂ z) p volume := by
    calc eLpNorm (fun z => μ₁ z * beurling (fun w => h₁ w - h₂ w) z) p volume
        ≤ eLpNormEssSup μ₁ volume
            * eLpNorm (beurling (fun w => h₁ w - h₂ w)) p volume :=
          eLpNorm_mul_le_essSup_mul hμ₁.aestronglyMeasurable (hbeurLp hd)
      _ ≤ ENNReal.ofReal k
            * (ENNReal.ofReal C * eLpNorm (fun z => h₁ z - h₂ z) p volume) :=
          mul_le_mul' hk₁ (hCbound (fun z => h₁ z - h₂ z) hd)
      _ = ENNReal.ofReal (k * C) * eLpNorm (fun z => h₁ z - h₂ z) p volume := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hk0]
  -- Triangle inequality: `A ≤ (k·C)·A + B`.
  have hE_le : eLpNorm (fun z => h₁ z - h₂ z) p volume
      ≤ ENNReal.ofReal (k * C) * eLpNorm (fun z => h₁ z - h₂ z) p volume
        + eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume := by
    calc eLpNorm (fun z => h₁ z - h₂ z) p volume
        = eLpNorm (fun z => μ₁ z * beurling (fun w => h₁ w - h₂ w) z
            + (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume := eLpNorm_congr_ae hres
      _ ≤ eLpNorm (fun z => μ₁ z * beurling (fun w => h₁ w - h₂ w) z) p volume
            + eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume :=
          eLpNorm_add_le hT1m hT2m hp1
      _ ≤ ENNReal.ofReal (k * C) * eLpNorm (fun z => h₁ z - h₂ z) p volume
            + eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume :=
          add_le_add hT1bound le_rfl
  -- Rearrange. If the right side is infinite the bound is trivial.
  have hAfin : eLpNorm (fun z => h₁ z - h₂ z) p volume ≠ ⊤ := hd.2.ne
  by_cases hBtop :
      eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume = ⊤
  · rw [hBtop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (inv_pos.mpr h1pos)).ne']
    exact le_top
  -- Otherwise pass to real numbers, rearrange, and return to `ℝ≥0∞`.
  · have hmul_ne : ENNReal.ofReal (k * C)
        * eLpNorm (fun z => h₁ z - h₂ z) p volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin
    have hreal : (eLpNorm (fun z => h₁ z - h₂ z) p volume).toReal
        ≤ k * C * (eLpNorm (fun z => h₁ z - h₂ z) p volume).toReal
          + (eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume).toReal := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hmul_ne, hBtop⟩) hE_le
      rwa [ENNReal.toReal_add hmul_ne hBtop, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hkC0] at this
    have hreal2 : (eLpNorm (fun z => h₁ z - h₂ z) p volume).toReal
        ≤ (1 - k * C)⁻¹
          * (eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume).toReal := by
      rw [inv_mul_eq_div, le_div_iff₀ h1pos]
      nlinarith [hreal]
    calc eLpNorm (fun z => h₁ z - h₂ z) p volume
        = ENNReal.ofReal (eLpNorm (fun z => h₁ z - h₂ z) p volume).toReal :=
          (ENNReal.ofReal_toReal hAfin).symm
      _ ≤ ENNReal.ofReal ((1 - k * C)⁻¹
            * (eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume).toReal) :=
          ENNReal.ofReal_le_ofReal hreal2
      _ = ENNReal.ofReal ((1 - k * C)⁻¹)
            * ENNReal.ofReal
              (eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume).toReal :=
          ENNReal.ofReal_mul (inv_nonneg.2 h1pos.le)
      _ = ENNReal.ofReal ((1 - k * C)⁻¹)
            * eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume := by
          rw [ENNReal.ofReal_toReal hBtop]

/-- **Principal solutions converge uniformly under a.e. convergence of the
coefficients** (AIM Theorem 5.3.2, convergence half). For coefficients of
dilatation at most `k < 1` supported in a common ball, a.e. convergence
`μₙ → μ` forces the principal solutions to converge uniformly on all of `ℂ`:
the fixed-point fields converge in `Lᵖ` (`lp_fixedPoint_beltrami_stability` +
dominated convergence), and `fₙ − f = P(hₙ − h)` is controlled in sup norm by
`norm_cauchyTransform_le_of_memLp_support`. -/
theorem isPrincipalSolution_tendstoUniformly_of_ae_tendsto
    {bs : ℕ → BeltramiCoeff} {b : BeltramiCoeff}
    {fs : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {k R : ℝ}
    (hk0 : 0 ≤ k) (hk : k < 1)
    (hbound : ∀ n, eLpNormEssSup (bs n).μ volume ≤ ENNReal.ofReal k)
    (hbound' : eLpNormEssSup b.μ volume ≤ ENNReal.ofReal k)
    (hsupp : ∀ n, ∀ z : ℂ, R < ‖z‖ → (bs n).μ z = 0)
    (hsupp' : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0)
    (htend : ∀ᵐ z, Tendsto (fun n => (bs n).μ z) atTop (𝓝 (b.μ z)))
    (hfs : ∀ n, IsPrincipalSolution (bs n) (fs n))
    (hf : IsPrincipalSolution b f) :
    TendstoUniformly fs f atTop := by
  classical
  -- ===== Step 0: contraction data `(p₀, C₀)` at the common dilatation bound `k`. =====
  have hkenorm : ‖(k : ℂ)‖ₑ = ENNReal.ofReal k := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk0]
  have hkonec : eLpNormEssSup (fun _ : ℂ => (k : ℂ)) volume < 1 := by
    rw [eLpNormEssSup_const _ (NeZero.ne volume), hkenorm]
    exact ENNReal.ofReal_lt_one.2 hk
  obtain ⟨p0, hp2, hptop, C0, hCb, hcontr0⟩ :=
    exists_p_gt_two_beurling_contraction
      (measurable_const : Measurable fun _ : ℂ => (k : ℂ)) hkonec
  have hC00 : 0 ≤ C0 := hCb.1
  have hcontr : k * C0 < 1 := by
    rwa [eLpNormEssSup_const _ (NeZero.ne volume), hkenorm,
      ENNReal.toReal_ofReal hk0] at hcontr0
  have hp00 : p0 ≠ 0 := by
    intro h0
    rw [h0] at hp2
    exact absurd hp2 (by simp)
  have hp0rpos : 0 < p0.toReal := ENNReal.toReal_pos hp00 hptop
  -- ===== Step 1: canonical fixed-point fields at exponent `p₀`. =====
  have key : ∀ (bb : BeltramiCoeff) (ff : ℂ → ℂ),
      eLpNormEssSup bb.μ volume ≤ ENNReal.ofReal k →
      (∀ z : ℂ, R < ‖z‖ → bb.μ z = 0) →
      IsPrincipalSolution bb ff →
      ∃ hh : ℂ → ℂ, MemLp hh p0 volume ∧
        (∀ z : ℂ, R < ‖z‖ → hh z = 0) ∧
        (hh =ᵐ[volume] fun z => bb.μ z * beurling hh z + bb.μ z) ∧
        ∀ z : ℂ, ff z = z + cauchyTransform hh z := by
    intro bb ff hbb hsuppbb hffsol
    have hμfin : eLpNormEssSup bb.μ volume ≠ ⊤ :=
      (lt_of_le_of_lt hbb ENNReal.ofReal_lt_top).ne
    have hμLp : MemLp bb.μ p0 volume :=
      memLp_of_eLpNormEssSup_ne_top_of_support hptop bb.measurable hμfin hsuppbb
    have hbbk : (eLpNormEssSup bb.μ volume).toReal ≤ k := by
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbb
      rwa [ENNReal.toReal_ofReal hk0] at h1
    have hcontrbb : (eLpNormEssSup bb.μ volume).toReal * C0 < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbbk hC00) hcontr
    obtain ⟨h0, hLp, haeeq, _⟩ :=
      exists_lp_fixedPoint_beltrami hp2 hptop bb.measurable hμfin hCb hcontrbb hμLp
    -- The everywhere-defined representative, vanishing pointwise outside the ball.
    set h' : ℂ → ℂ := fun z => bb.μ z * beurling h0 z + bb.μ z with hh'_def
    have hh'ae : h' =ᵐ[volume] h0 := haeeq.symm
    have hh'Lp : MemLp h' p0 volume := hLp.ae_eq haeeq
    have hh'supp : ∀ z : ℂ, R < ‖z‖ → h' z = 0 := by
      intro z hz
      simp only [hh'_def]
      rw [hsuppbb z hz, zero_mul, zero_add]
    -- `L²` memberships (finite-measure embedding on the support ball).
    have hL2h' : MemLp h' 2 volume := by
      set m : ℝ := max R 0 with hm_def
      set Bm : Set ℂ := Metric.closedBall (0 : ℂ) m with hBm_def
      have hBmmeas : MeasurableSet Bm := by rw [hBm_def]; exact measurableSet_closedBall
      have : IsFiniteMeasure (volume.restrict Bm) :=
        ⟨by
          rw [Measure.restrict_apply_univ]
          exact (isCompact_closedBall _ _).measure_lt_top⟩
      have hind : h' = Bm.indicator h' := by
        funext ζ
        by_cases hζ : ζ ∈ Bm
        · rw [Set.indicator_of_mem hζ]
        · rw [Set.indicator_of_notMem hζ]
          refine hh'supp ζ ?_
          have hm : m < ‖ζ‖ := by
            simpa [hBm_def, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
          exact lt_of_le_of_lt (le_max_left R 0) hm
      rw [hind]
      exact (memLp_indicator_iff_restrict hBmmeas).2
        ((hh'Lp.restrict Bm).mono_exponent hp2.le)
    have hL2h0 : MemLp h0 2 volume := hL2h'.ae_eq hh'ae
    -- The fixed-point equation transfers to `h'`.
    have hSeq : beurling h0 =ᵐ[volume] beurling h' := beurling_congr_ae hL2h0 hL2h' haeeq
    have heq' : h' =ᵐ[volume] (fun z => bb.μ z * beurling h' z + bb.μ z) := by
      filter_upwards [hSeq] with z hz
      rw [← hz]
    -- Identification with the given principal solution.
    have hsol' : IsPrincipalSolution bb (fun z => z + cauchyTransform h' z) :=
      ⟨p0, h', R, hp2, hptop, hh'Lp, hh'supp, heq', fun z => rfl⟩
    have hffeq := isPrincipalSolution_unique hffsol hsol'
    exact ⟨h', hh'Lp, hh'supp, heq', fun z => by rw [hffeq]⟩
  choose hs hsmem hssupp hseq hsrepr using
    fun n => key (bs n) (fs n) (hbound n) (hsupp n) (hfs n)
  obtain ⟨h, hhmem, hhsupp, hheq, hhrepr⟩ := key b f hbound' hsupp' hf
  -- ===== Step 2: resolvent stability bounds the field differences. =====
  have hstab : ∀ n, eLpNorm (fun z => hs n z - h z) p0 volume
      ≤ ENNReal.ofReal ((1 - k * C0)⁻¹)
        * eLpNorm (fun z => ((bs n).μ z - b.μ z) * (1 + beurling h z)) p0 volume :=
    fun n => lp_fixedPoint_beltrami_stability hp2 hptop (bs n).measurable b.measurable
      (hbound n) hbound' hCb hk0 hcontr (hsmem n) hhmem (hseq n) hheq
  -- ===== Step 3: the stability majorant tends to `0` (dominated convergence). =====
  have hSh : MemLp (beurling h) p0 volume := memLp_beurling_of_memLp hp2 hptop hhmem
  have hShm : AEStronglyMeasurable (fun z => 1 + beurling h z) volume :=
    aestronglyMeasurable_const.add hSh.1
  set B : Set ℂ := Metric.closedBall (0 : ℂ) R with hB_def
  have hBmeas : MeasurableSet B := by rw [hB_def]; exact measurableSet_closedBall
  have : IsFiniteMeasure (volume.restrict B) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isCompact_closedBall _ _).measure_lt_top⟩
  -- The dominator: `(2k·|1 + S h|)^{p₀}` cut off to the support ball.
  set D : ℂ → ℝ≥0∞ := fun z =>
    B.indicator (fun w => (ENNReal.ofReal (2 * k) * ‖1 + beurling h w‖ₑ) ^ p0.toReal) z
    with hD_def
  have hconst_ne : ENNReal.ofReal (2 * k) ^ p0.toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp0rpos.le ENNReal.ofReal_ne_top
  have honeB : MemLp (fun _ : ℂ => (1 : ℂ)) p0 (volume.restrict B) := memLp_const _
  have hSB : MemLp (beurling h) p0 (volume.restrict B) := hSh.restrict B
  have hgB : MemLp (fun z => 1 + beurling h z) p0 (volume.restrict B) := honeB.add hSB
  have hDint : ∫⁻ z in B, ‖1 + beurling h z‖ₑ ^ p0.toReal ∂volume ≠ ⊤ :=
    ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp00 hptop).1 hgB.2).ne
  have hDfin : ∫⁻ z, D z ∂volume ≠ ⊤ := by
    have heq1 : ∫⁻ z, D z ∂volume
        = ENNReal.ofReal (2 * k) ^ p0.toReal
          * ∫⁻ z in B, ‖1 + beurling h z‖ₑ ^ p0.toReal ∂volume := by
      calc ∫⁻ z, D z ∂volume
          = ∫⁻ z in B, (ENNReal.ofReal (2 * k) * ‖1 + beurling h z‖ₑ) ^ p0.toReal ∂volume := by
            simp only [hD_def]
            exact lintegral_indicator hBmeas _
        _ = ∫⁻ z in B, ENNReal.ofReal (2 * k) ^ p0.toReal
              * ‖1 + beurling h z‖ₑ ^ p0.toReal ∂volume :=
            lintegral_congr fun z => ENNReal.mul_rpow_of_nonneg _ _ hp0rpos.le
        _ = ENNReal.ofReal (2 * k) ^ p0.toReal
              * ∫⁻ z in B, ‖1 + beurling h z‖ₑ ^ p0.toReal ∂volume :=
            lintegral_const_mul' _ _ hconst_ne
    rw [heq1]
    exact ENNReal.mul_ne_top hconst_ne hDint
  -- a.e. dilatation bounds.
  have hkn : ∀ n, ∀ᵐ z ∂volume, ‖(bs n).μ z‖ₑ ≤ ENNReal.ofReal k := fun n =>
    (enorm_ae_le_eLpNormEssSup ((bs n).μ) volume).mono fun z hz => hz.trans (hbound n)
  have hkb : ∀ᵐ z ∂volume, ‖b.μ z‖ₑ ≤ ENNReal.ofReal k :=
    (enorm_ae_le_eLpNormEssSup (b.μ) volume).mono fun z hz => hz.trans hbound'
  -- Dominated convergence for the `p₀`-th powers.
  have hDCT : Tendsto
      (fun n => ∫⁻ z, ‖((bs n).μ z - b.μ z) * (1 + beurling h z)‖ₑ ^ p0.toReal ∂volume)
      atTop (𝓝 0) := by
    have hlim := tendsto_lintegral_of_dominated_convergence' (μ := volume)
      (F := fun n z => ‖((bs n).μ z - b.μ z) * (1 + beurling h z)‖ₑ ^ p0.toReal)
      (f := fun _ => (0 : ℝ≥0∞)) D
      (fun n => by
        have h1 : AEStronglyMeasurable
            (fun z => ((bs n).μ z - b.μ z) * (1 + beurling h z)) volume :=
          (((bs n).measurable.sub b.measurable).aestronglyMeasurable).mul hShm
        exact (ENNReal.continuous_rpow_const.measurable).comp_aemeasurable h1.enorm)
      (fun n => by
        filter_upwards [hkn n, hkb] with z hzn hzb
        by_cases hzB : z ∈ B
        · simp only [hD_def, Set.indicator_of_mem hzB]
          refine ENNReal.rpow_le_rpow ?_ hp0rpos.le
          rw [enorm_mul]
          gcongr
          refine le_trans enorm_sub_le ?_
          calc ‖(bs n).μ z‖ₑ + ‖b.μ z‖ₑ
              ≤ ENNReal.ofReal k + ENNReal.ofReal k := add_le_add hzn hzb
            _ = ENNReal.ofReal (2 * k) := by
                rw [← ENNReal.ofReal_add hk0 hk0, two_mul]
        · simp only [hD_def, Set.indicator_of_notMem hzB]
          have hzR : R < ‖z‖ := by
            simpa [hB_def, Metric.mem_closedBall, dist_zero_right, not_le] using hzB
          rw [hsupp n z hzR, hsupp' z hzR, sub_zero, zero_mul]
          simp [ENNReal.zero_rpow_of_pos hp0rpos])
      hDfin
      (by
        filter_upwards [htend] with z hz
        have h1 : Tendsto (fun n => ((bs n).μ z - b.μ z) * (1 + beurling h z))
            atTop (𝓝 0) := by
          have h2 := (hz.sub_const (b.μ z)).mul_const (1 + beurling h z)
          rwa [sub_self, zero_mul] at h2
        have h3 : Tendsto (fun n => ‖((bs n).μ z - b.μ z) * (1 + beurling h z)‖ₑ)
            atTop (𝓝 (‖(0 : ℂ)‖ₑ)) := (continuous_enorm.tendsto (0 : ℂ)).comp h1
        rw [enorm_zero] at h3
        have h5 : Tendsto (fun n => ‖((bs n).μ z - b.μ z) * (1 + beurling h z)‖ₑ ^ p0.toReal)
            atTop (𝓝 ((0 : ℝ≥0∞) ^ p0.toReal)) :=
          ((ENNReal.continuous_rpow_const (y := p0.toReal)).tendsto (0 : ℝ≥0∞)).comp h3
        rwa [ENNReal.zero_rpow_of_pos hp0rpos] at h5)
    simpa using hlim
  -- The `eLpNorm` of the majorant tends to `0`.
  have hG0 : Tendsto
      (fun n => eLpNorm (fun z => ((bs n).μ z - b.μ z) * (1 + beurling h z)) p0 volume)
      atTop (𝓝 0) := by
    have hrw : ∀ n, eLpNorm (fun z => ((bs n).μ z - b.μ z) * (1 + beurling h z)) p0 volume
        = (∫⁻ z, ‖((bs n).μ z - b.μ z) * (1 + beurling h z)‖ₑ ^ p0.toReal ∂volume)
            ^ (1 / p0.toReal) :=
      fun n => eLpNorm_eq_lintegral_rpow_enorm_toReal hp00 hptop
    simp only [hrw]
    have h5 : Tendsto
        (fun n => (∫⁻ z, ‖((bs n).μ z - b.μ z) * (1 + beurling h z)‖ₑ ^ p0.toReal ∂volume)
          ^ (1 / p0.toReal))
        atTop (𝓝 ((0 : ℝ≥0∞) ^ (1 / p0.toReal))) :=
      ((ENNReal.continuous_rpow_const (y := 1 / p0.toReal)).tendsto (0 : ℝ≥0∞)).comp hDCT
    rwa [ENNReal.zero_rpow_of_pos (one_div_pos.2 hp0rpos)] at h5
  -- The field differences tend to `0` in `L^{p₀}` (squeeze).
  have hfield0 : Tendsto (fun n => eLpNorm (fun z => hs n z - h z) p0 volume)
      atTop (𝓝 0) := by
    have hupper : Tendsto (fun n => ENNReal.ofReal ((1 - k * C0)⁻¹)
        * eLpNorm (fun z => ((bs n).μ z - b.μ z) * (1 + beurling h z)) p0 volume)
        atTop (𝓝 0) := by
      have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ((1 - k * C0)⁻¹)) hG0
        (Or.inr ENNReal.ofReal_ne_top)
      rwa [mul_zero] at h1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => zero_le) (fun n => hstab n)
  -- ===== Step 4: the uniform sup bound converts `Lᵖ` convergence to uniform. =====
  obtain ⟨CR, hCR0, hCR⟩ := norm_cauchyTransform_le_of_memLp_support (R := R) hp2 hptop
  have hdmem : ∀ n, MemLp (fun w => hs n w - h w) p0 volume :=
    fun n => (hsmem n).sub hhmem
  have hdsupp : ∀ n, ∀ w : ℂ, R < ‖w‖ → hs n w - h w = 0 := fun n w hw => by
    rw [hssupp n w hw, hhsupp w hw, sub_zero]
  -- Cauchy-transform subtractivity from integral linearity.
  have hPsub : ∀ n, ∀ z : ℂ, cauchyTransform (fun w => hs n w - h w) z
      = cauchyTransform (hs n) z - cauchyTransform h z := by
    intro n z
    have h1 := integrable_div_sub_of_memLp_of_support hp2 hptop (hsmem n) (hssupp n) z
    have h2 := integrable_div_sub_of_memLp_of_support hp2 hptop hhmem hhsupp z
    simp only [cauchyTransform]
    rw [← mul_sub, ← integral_sub h1 h2]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun ζ => sub_div _ _ _)
  have hdiffz : ∀ n, ∀ z : ℂ, fs n z - f z = cauchyTransform (fun w => hs n w - h w) z := by
    intro n z
    rw [hsrepr n z, hhrepr z, hPsub n z]
    ring
  -- Assemble the uniform convergence.
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have htoReal : Tendsto (fun n => (eLpNorm (fun z => hs n z - h z) p0 volume).toReal)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (eLpNorm (fun z => hs n z - h z) p0 volume).toReal)
        atTop (𝓝 ((0 : ℝ≥0∞).toReal)) :=
      (ENNReal.tendsto_toReal (by simp)).comp hfield0
    simpa using h1
  have hCRtend : Tendsto
      (fun n => CR * (eLpNorm (fun z => hs n z - h z) p0 volume).toReal) atTop (𝓝 0) := by
    have h1 := htoReal.const_mul CR
    rwa [mul_zero] at h1
  filter_upwards [hCRtend.eventually_lt_const hε] with n hn z
  have h1 : ‖cauchyTransform (fun w => hs n w - h w) z‖
      ≤ CR * (eLpNorm (fun w => hs n w - h w) p0 volume).toReal :=
    hCR _ (hdmem n) (hdsupp n) z
  have h2 : dist (f z) (fs n z) = ‖cauchyTransform (fun w => hs n w - h w) z‖ := by
    rw [dist_comm, dist_eq_norm, hdiffz n z]
  rw [h2]
  exact lt_of_le_of_lt h1 hn

/-- **The two-sided Hölder inequality, uniformly over the smooth family**
(Ahlfors–Bers Lemma 8). For every dilatation bound `k < 1` and support radius
`R` there are constants `c` and `α > 0` such that **every** principal solution
of a smooth compactly supported coefficient within those bounds satisfies

`‖z₁ − z₂‖ ≤ ‖f z₁ − f z₂‖ + c·‖f z₁ − f z₂‖^α` for all `z₁ z₂`.

Apply the inverse-solution package
(`IsPrincipalSolution.inverse_principalSolution_of_contDiff`): the inverse
`g = id + P h'` has field norm `‖h'‖ₚ` bounded by `k`, the uniform image ball
(`isPrincipalSolution_uniform_image_bound`), and the Neumann bound, so the
uniform Hölder estimate `cauchyTransform_sub_le_holder_uniform` at
`wᵢ = f zᵢ` gives `‖z₁ − z₂‖ − ‖w₁ − w₂‖ ≤ ‖P h' w₁ − P h' w₂‖ ≤
c·‖w₁ − w₂‖^α`. Since the constants survive the mollification limit, this
inequality is what forces the measurable-case principal solution to be
injective. -/
theorem isPrincipalSolution_two_sided_holder {k R : ℝ}
    (hk0 : 0 ≤ k) (hk : k < 1) :
    ∃ c α : ℝ, 0 ≤ c ∧ 0 < α ∧ ∀ (b : BeltramiCoeff) (f : ℂ → ℂ),
      ContDiff ℝ ∞ b.μ → HasCompactSupport b.μ →
      eLpNormEssSup b.μ volume ≤ ENNReal.ofReal k →
      (∀ z : ℂ, R < ‖z‖ → b.μ z = 0) →
      IsPrincipalSolution b f →
      ∀ z₁ z₂ : ℂ, ‖z₁ - z₂‖ ≤ ‖f z₁ - f z₂‖ + c * ‖f z₁ - f z₂‖ ^ α := by
  classical
  -- ===== Step 0: all constants are chosen before the family. =====
  -- Contraction exponent data at the numeric dilatation bound `k`.
  set ε : ℝ := (1 - k) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨p₀, hp₀2, hp₀top, C₀, hC₀lt, hCZ⟩ := beurling_opNorm_continuous ε hεpos
  have hC₀0 : 0 ≤ C₀ := hCZ.1
  have hkC : k * C₀ < 1 := by
    have h1 : k * C₀ ≤ k * (1 + ε) := mul_le_mul_of_nonneg_left hC₀lt.le hk0
    have h2 : k * (1 + ε) < 1 := by rw [hε]; nlinarith [hk0, hk]
    linarith
  have h1kC : 0 < 1 - k * C₀ := by linarith
  -- The Hölder exponent `α = 1 − 2/p₀ > 0`.
  have hp₀R : 2 < p₀.toReal := by
    have h1 : ((2 : ℝ≥0∞)).toReal < p₀.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) hp₀top).2 hp₀2
    simpa using h1
  have hα : 0 < 1 - 2 / p₀.toReal := by
    have h2 : 2 / p₀.toReal < 1 := (div_lt_one (by linarith)).2 hp₀R
    linarith
  -- The uniform image radius `R'` and the uniform Hölder constant at `(p₀, R')`.
  obtain ⟨R', hRR', himg⟩ := isPrincipalSolution_uniform_image_bound (k := k) (R := R) hk0 hk
  obtain ⟨C₁₀, hC₁₀0, hHold⟩ :=
    cauchyTransform_sub_le_holder_uniform (p := p₀) (R := R') hp₀2 hp₀top
  -- The uniform bound on the `Lᵖ⁰` norms of the inverse fields.
  set B : Set ℂ := Metric.closedBall (0 : ℂ) R' with hB
  have hBmeas : MeasurableSet B := measurableSet_closedBall
  have hBfin : volume B ≠ ⊤ := (isCompact_closedBall _ _).measure_lt_top.ne
  set Hb : ℝ≥0∞ :=
    ENNReal.ofReal ((1 - k * C₀)⁻¹) * (volume B ^ p₀.toReal⁻¹ * ENNReal.ofReal k) with hHb
  have hHbfin : Hb ≠ ⊤ := by
    rw [hHb]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) hBfin)
        ENNReal.ofReal_ne_top)
  refine ⟨C₁₀ * Hb.toReal, 1 - 2 / p₀.toReal,
    mul_nonneg hC₁₀0 ENNReal.toReal_nonneg, hα, ?_⟩
  -- ===== The family. =====
  intro b f hbs hbc hbk hbsupp hpf
  -- Step 1: `f` is the `C¹` nondegenerate principal solution, hence a homeomorphism.
  obtain ⟨F, hFps, hF1, hFdet, _hFdz⟩ := exists_contDiffOne_principalSolution b hbs hbc
  obtain rfl : f = F := isPrincipalSolution_unique hpf hFps
  have hhom : IsHomeomorph f := isHomeomorph_of_contDiffOne_principalSolution hpf hF1 hFdet
  -- Step 2: the inverse-solution package.
  obtain ⟨ν, _hνformula, hνbound, _hνcs, hνimg, hνps⟩ :=
    hpf.inverse_principalSolution_of_contDiff hbs hbc hF1 hFdet hhom
  -- Step 3: `ν` is bounded by `k` and supported in the ball of radius `R'`.
  have hνk : eLpNormEssSup ν.μ volume ≤ ENNReal.ofReal k := hνbound.trans hbk
  have hνfin : eLpNormEssSup ν.μ volume ≠ ⊤ :=
    (lt_of_le_of_lt hνk ENNReal.ofReal_lt_top).ne
  have hνtoReal : (eLpNormEssSup ν.μ volume).toReal ≤ k := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hνk
    rwa [ENNReal.toReal_ofReal hk0] at h1
  have htsupp : tsupport b.μ ⊆ Metric.closedBall 0 R := by
    have hsub : Function.support b.μ ⊆ Metric.closedBall 0 R := by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hcon
      rw [not_le] at hcon
      exact hz (hbsupp z hcon)
    exact closure_minimal hsub Metric.isClosed_closedBall
  have hνvan : ∀ w : ℂ, R' < ‖w‖ → ν.μ w = 0 := by
    intro w hw
    by_contra hne
    obtain ⟨z, hz, hzw⟩ := hνimg w hne
    have h1 : ‖z‖ ≤ R := by
      have h2 := htsupp hz
      rwa [Metric.mem_closedBall, dist_zero_right] at h2
    have h3 : ‖f z‖ ≤ R' := himg b f hbk hbsupp hpf z h1
    rw [hzw] at h3
    exact absurd h3 (not_le.mpr hw)
  -- Step 4: the canonical field of the inverse at the exponent `p₀`.
  have hνLp : MemLp ν.μ p₀ volume :=
    memLp_of_eLpNormEssSup_ne_top_of_support hp₀top ν.measurable hνfin hνvan
  have hνcontr : (eLpNormEssSup ν.μ volume).toReal * C₀ < 1 := by
    have h1 : (eLpNormEssSup ν.μ volume).toReal * C₀ ≤ k * C₀ :=
      mul_le_mul_of_nonneg_right hνtoReal hC₀0
    linarith
  obtain ⟨h₀, hh₀mem, hh₀eq, hh₀norm⟩ :=
    exists_lp_fixedPoint_beltrami hp₀2 hp₀top ν.measurable hνfin hCZ hνcontr hνLp
  -- The everywhere-defined representative, vanishing pointwise outside the ball.
  set u : ℂ → ℂ := fun z => ν.μ z * beurling h₀ z + ν.μ z with hu_def
  have hh₀u : h₀ =ᵐ[volume] u := hh₀eq
  have humem : MemLp u p₀ volume := hh₀mem.ae_eq hh₀u
  have husupp : ∀ z : ℂ, R' < ‖z‖ → u z = 0 := by
    intro z hz
    simp only [hu_def]
    rw [hνvan z hz, zero_mul, zero_add]
  -- `L²` memberships for the Beurling congruence.
  have huL2 : MemLp u 2 volume := by
    set m : ℝ := max R' 0 with hm_def
    set B₂ : Set ℂ := Metric.closedBall (0 : ℂ) m with hB₂_def
    have hB₂meas : MeasurableSet B₂ := by rw [hB₂_def]; exact measurableSet_closedBall
    have : IsFiniteMeasure (volume.restrict B₂) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (isCompact_closedBall _ _).measure_lt_top⟩
    have hind : u = B₂.indicator u := by
      funext ζ
      by_cases hζ : ζ ∈ B₂
      · rw [Set.indicator_of_mem hζ]
      · rw [Set.indicator_of_notMem hζ]
        refine husupp ζ ?_
        have hm : m < ‖ζ‖ := by
          simpa [hB₂_def, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
        exact lt_of_le_of_lt (le_max_left R' 0) hm
    rw [hind]
    exact (memLp_indicator_iff_restrict hB₂meas).2 ((humem.restrict B₂).mono_exponent hp₀2.le)
  have hh₀L2 : MemLp h₀ 2 volume := huL2.ae_eq hh₀u.symm
  have hSeq : beurling h₀ =ᵐ[volume] beurling u := beurling_congr_ae hh₀L2 huL2 hh₀u
  have hueq : u =ᵐ[volume] (fun z => ν.μ z * beurling u z + ν.μ z) := by
    filter_upwards [hSeq] with z hz
    rw [← hz]
  -- `id + P u` is a principal solution of `ν`, hence equal to the inverse of `f`.
  have hg'ps : IsPrincipalSolution ν (fun w => w + cauchyTransform u w) :=
    ⟨p₀, u, R', hp₀2, hp₀top, humem, husupp, hueq, fun z => rfl⟩
  have hgg' : (fun w => w + cauchyTransform u w) = ⇑(hhom.homeomorph f).symm :=
    isPrincipalSolution_unique hg'ps hνps
  -- The uniform field-norm bound `‖u‖ₚ₀ ≤ Hb`.
  have hunorm : eLpNorm u p₀ volume ≤ Hb := by
    have hcalc : eLpNorm ν.μ p₀ volume ≤ volume B ^ p₀.toReal⁻¹ * ENNReal.ofReal k := by
      have hband : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν.μ z‖ ≤ k := by
        filter_upwards [ae_le_eLpNormEssSup (f := ν.μ) (μ := volume)] with z hz
        have h2 : ‖ν.μ z‖ₑ ≤ ENNReal.ofReal k := le_trans hz hνk
        rw [← ofReal_norm] at h2
        exact (ENNReal.ofReal_le_ofReal_iff hk0).1 h2
      have hind : ν.μ = B.indicator ν.μ := by
        funext ζ
        by_cases hζ : ζ ∈ B
        · rw [Set.indicator_of_mem hζ]
        · rw [Set.indicator_of_notMem hζ]
          refine hνvan ζ ?_
          simpa [hB, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
      calc eLpNorm ν.μ p₀ volume
          = eLpNorm (B.indicator ν.μ) p₀ volume :=
            eLpNorm_congr_ae (Filter.EventuallyEq.of_eq hind)
        _ = eLpNorm ν.μ p₀ (volume.restrict B) :=
            eLpNorm_indicator_eq_eLpNorm_restrict hBmeas
        _ ≤ (volume.restrict B) Set.univ ^ p₀.toReal⁻¹ * ENNReal.ofReal k :=
            eLpNorm_le_of_ae_bound (ae_restrict_of_ae hband)
        _ = volume B ^ p₀.toReal⁻¹ * ENNReal.ofReal k := by
            rw [Measure.restrict_apply_univ]
    have hinv : (1 - (eLpNormEssSup ν.μ volume).toReal * C₀)⁻¹ ≤ (1 - k * C₀)⁻¹ := by
      have h1 : 1 - k * C₀ ≤ 1 - (eLpNormEssSup ν.μ volume).toReal * C₀ := by
        have h2 : (eLpNormEssSup ν.μ volume).toReal * C₀ ≤ k * C₀ :=
          mul_le_mul_of_nonneg_right hνtoReal hC₀0
        linarith
      gcongr
    calc eLpNorm u p₀ volume = eLpNorm h₀ p₀ volume := eLpNorm_congr_ae hh₀u.symm
      _ ≤ ENNReal.ofReal ((1 - (eLpNormEssSup ν.μ volume).toReal * C₀)⁻¹)
          * eLpNorm ν.μ p₀ volume := hh₀norm
      _ ≤ ENNReal.ofReal ((1 - k * C₀)⁻¹)
          * (volume B ^ p₀.toReal⁻¹ * ENNReal.ofReal k) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hinv) hcalc
      _ = Hb := hHb.symm
  have huD : (eLpNorm u p₀ volume).toReal ≤ Hb.toReal := ENNReal.toReal_mono hHbfin hunorm
  -- ===== Step 5: the two-sided inequality. =====
  intro z₁ z₂
  have hrep : ∀ z : ℂ, z = f z + cauchyTransform u (f z) := by
    intro z
    have h1 : (hhom.homeomorph f).symm (f z) = z := Homeomorph.symm_apply_apply _ z
    calc z = (hhom.homeomorph f).symm (f z) := h1.symm
      _ = f z + cauchyTransform u (f z) := by rw [← hgg']
  have hdiff : z₁ - z₂
      = (f z₁ - f z₂) + (cauchyTransform u (f z₁) - cauchyTransform u (f z₂)) := by
    calc z₁ - z₂
        = (f z₁ + cauchyTransform u (f z₁)) - (f z₂ + cauchyTransform u (f z₂)) := by
          rw [← hrep z₁, ← hrep z₂]
      _ = (f z₁ - f z₂) + (cauchyTransform u (f z₁) - cauchyTransform u (f z₂)) := by
          ring
  calc ‖z₁ - z₂‖
      = ‖(f z₁ - f z₂) + (cauchyTransform u (f z₁) - cauchyTransform u (f z₂))‖ := by
        rw [hdiff]
    _ ≤ ‖f z₁ - f z₂‖ + ‖cauchyTransform u (f z₁) - cauchyTransform u (f z₂)‖ :=
        norm_add_le _ _
    _ ≤ ‖f z₁ - f z₂‖
        + C₁₀ * (eLpNorm u p₀ volume).toReal * ‖f z₁ - f z₂‖ ^ (1 - 2 / p₀.toReal) := by
        have h1 := hHold u humem husupp (f z₁) (f z₂)
        linarith
    _ ≤ ‖f z₁ - f z₂‖ + C₁₀ * Hb.toReal * ‖f z₁ - f z₂‖ ^ (1 - 2 / p₀.toReal) := by
        have hX : (0:ℝ) ≤ ‖f z₁ - f z₂‖ ^ (1 - 2 / p₀.toReal) :=
          Real.rpow_nonneg (norm_nonneg _) _
        have h2 : C₁₀ * (eLpNorm u p₀ volume).toReal ≤ C₁₀ * Hb.toReal :=
          mul_le_mul_of_nonneg_left huD hC₁₀0
        have h3 := mul_le_mul_of_nonneg_right h2 hX
        linarith

/-- **Mollification of a Beltrami coefficient.** Every compactly vanishing
Beltrami coefficient is the a.e. limit of smooth compactly supported
coefficients of no larger dilatation, supported in a slightly larger ball:
convolve with a mollifier at scales `εₙ → 0` — the convolution is smooth, its
modulus is bounded by the essential supremum of `|μ|` everywhere, its support
lies in `supp μ + B(εₙ)`, and it converges at every Lebesgue point of `μ`. -/
theorem exists_contDiff_mollification_beltrami (b : BeltramiCoeff) {R : ℝ}
    (hsupp : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0) :
    ∃ bs : ℕ → BeltramiCoeff,
      (∀ n, ContDiff ℝ ∞ (bs n).μ) ∧ (∀ n, HasCompactSupport (bs n).μ) ∧
      (∀ n, eLpNormEssSup (bs n).μ volume ≤ eLpNormEssSup b.μ volume) ∧
      (∀ n, ∀ z : ℂ, R + 1 < ‖z‖ → (bs n).μ z = 0) ∧
      ∀ᵐ z, Tendsto (fun n => (bs n).μ z) atTop (𝓝 (b.μ z)) := by
  classical
  -- ===== The `L∞` bound `k` of `b.μ` and its basic properties. =====
  have hfin : eLpNormEssSup b.μ volume ≠ ⊤ := (b.bound.trans ENNReal.one_lt_top).ne
  set k : ℝ := (eLpNormEssSup b.μ volume).toReal with hkdef
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  -- The pointwise a.e. bound `‖b.μ w‖ ≤ k`.
  have hbae : ∀ᵐ w : ℂ, ‖b.μ w‖ ≤ k := by
    filter_upwards [MeasureTheory.enorm_ae_le_eLpNormEssSup b.μ volume] with w hw
    have h1 := ENNReal.toReal_mono hfin hw
    rwa [toReal_enorm] at h1
  -- ===== The truncation `ν` of `b.μ` at level `k`. =====
  -- It is bounded by `k` *everywhere*, a.e. equal to `b.μ`, measurable, and
  -- vanishes wherever `b.μ` does.
  set ν : ℂ → ℂ := fun w => if ‖b.μ w‖ ≤ k then b.μ w else 0 with hνdef
  have hν_meas : Measurable ν :=
    Measurable.ite (measurableSet_le b.measurable.norm measurable_const)
      b.measurable measurable_const
  have hν_bdd : ∀ w, ‖ν w‖ ≤ k := by
    intro w
    by_cases hw : ‖b.μ w‖ ≤ k
    · simp [hνdef, hw]
    · simp [hνdef, hw, hk0]
  have hν_ae : ν =ᵐ[volume] b.μ := by
    filter_upwards [hbae] with w hw
    simp [hνdef, hw]
  have hν_supp : ∀ w : ℂ, R < ‖w‖ → ν w = 0 := by
    intro w hw
    simp [hνdef, hsupp w hw]
  -- `ν` is integrable (bounded, measurable, supported in `closedBall 0 R`),
  -- hence locally integrable.
  have hν_int : Integrable ν volume := by
    refine Integrable.mono' (g := (Metric.closedBall (0 : ℂ) R).indicator fun _ => k) ?_
      hν_meas.aestronglyMeasurable ?_
    · exact (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    · refine Eventually.of_forall fun w => ?_
      by_cases hw : w ∈ Metric.closedBall (0 : ℂ) R
      · rw [Set.indicator_of_mem hw]
        exact hν_bdd w
      · rw [Set.indicator_of_notMem hw]
        have hRw : R < ‖w‖ := by
          simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hw
        simp [hν_supp w hRw]
  have hν_li : LocallyIntegrable ν volume := hν_int.locallyIntegrable
  -- ===== The mollifier bumps at scales `1/(n+1)` with `rOut = 2 · rIn`. =====
  set φb : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    { rIn := 1 / (2 * ((n : ℝ) + 1)), rOut := 1 / ((n : ℝ) + 1),
      rIn_pos := by positivity,
      rIn_lt_rOut := by
        refine div_lt_div_of_pos_left one_pos (by positivity) ?_
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith } with hφbdef
  have hrIn : ∀ n : ℕ, (φb n).rIn = 1 / (2 * ((n : ℝ) + 1)) := fun n => rfl
  have hrOut : ∀ n : ℕ, (φb n).rOut = 1 / ((n : ℝ) + 1) := fun n => rfl
  set ρ : ℕ → ℂ → ℝ := fun n => (φb n).normed volume with hρdef
  have hρ_int : ∀ n, ∫ t : ℂ, ρ n t ∂volume = 1 := fun n => (φb n).integral_normed
  have hρ_nonneg : ∀ n t, 0 ≤ ρ n t := fun n t => (φb n).nonneg_normed t
  have hρ_integrable : ∀ n, Integrable (ρ n) volume := fun n => (φb n).integrable_normed
  have hρ_supp_eq : ∀ n, Function.support (ρ n) = Metric.ball (0 : ℂ) (φb n).rOut :=
    fun n => (φb n).support_normed_eq
  -- ===== The mollified coefficients `mol n = ρ n ⋆ ν`. =====
  set mol : ℕ → ℂ → ℂ := fun n =>
    MeasureTheory.convolution (ρ n) ν (ContinuousLinearMap.lsmul ℝ ℝ) volume with hmoldef
  have hmol_eq : ∀ n z, mol n z
      = ∫ t : ℂ, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ n t) (ν (z - t)) ∂volume := by
    intro n z
    simp only [hmoldef, MeasureTheory.convolution_def]
  -- (a) Smoothness: convolution of the smooth compactly supported bump with the
  -- locally integrable `ν`.
  have hsmooth : ∀ n, ContDiff ℝ ∞ (mol n) := fun n =>
    ((φb n).hasCompactSupport_normed).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) ((φb n).contDiff_normed (n := ⊤)) hν_li
  have hmol_meas : ∀ n, Measurable (mol n) := fun n => (hsmooth n).continuous.measurable
  -- (b) Everywhere pointwise bound `‖mol n z‖ ≤ k`.
  have hmol_bdd : ∀ n z, ‖mol n z‖ ≤ k := by
    intro n z
    rw [hmol_eq n z]
    calc ‖∫ t : ℂ, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ n t) (ν (z - t)) ∂volume‖
        ≤ ∫ t : ℂ, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ n t) (ν (z - t))‖ ∂volume :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℂ, ρ n t * k ∂volume := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
            ((hρ_integrable n).mul_const k)
          refine Eventually.of_forall fun t => ?_
          simp only [ContinuousLinearMap.lsmul_apply, norm_smul,
            Real.norm_of_nonneg (hρ_nonneg n t)]
          exact mul_le_mul_of_nonneg_left (hν_bdd _) (hρ_nonneg n t)
      _ = (∫ t : ℂ, ρ n t ∂volume) * k := integral_mul_const k _
      _ = k := by rw [hρ_int n, one_mul]
  -- The `L∞` bound conjunct.
  have hmol_esssup : ∀ n, eLpNormEssSup (mol n) volume ≤ eLpNormEssSup b.μ volume := by
    intro n
    have h1 : eLpNormEssSup (mol n) volume ≤ ENNReal.ofReal k :=
      eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun z => hmol_bdd n z)
    rwa [hkdef, ENNReal.ofReal_toReal hfin] at h1
  have hmol_lt : ∀ n, eLpNormEssSup (mol n) volume < 1 :=
    fun n => lt_of_le_of_lt (hmol_esssup n) b.bound
  -- (c) Vanishing outside `closedBall 0 (R + 1)`: for `‖z‖ > R + 1` the integrand
  -- vanishes identically (either the bump or the translated `ν` is zero).
  have hmol_vanish : ∀ n, ∀ z : ℂ, R + 1 < ‖z‖ → mol n z = 0 := by
    intro n z hz
    rw [hmol_eq n z]
    have hzero : ∀ t : ℂ, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ n t) (ν (z - t)) = 0 := by
      intro t
      by_cases ht : ‖t‖ < (φb n).rOut
      · -- inside the bump: `‖t‖ < rOut ≤ 1`, so `‖z - t‖ > R` and `ν (z - t) = 0`.
        have hrOut_le : (φb n).rOut ≤ 1 := by
          rw [hrOut n, div_le_one (by positivity)]
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        have h2 : ‖z‖ - ‖t‖ ≤ ‖z - t‖ := norm_sub_norm_le z t
        have h3 : ‖t‖ < 1 := lt_of_lt_of_le ht hrOut_le
        have h1 : R < ‖z - t‖ := by linarith
        rw [hν_supp _ h1]
        exact map_zero _
      · -- outside the bump support: `ρ n t = 0`.
        have hρ0 : ρ n t = 0 := by
          apply Function.notMem_support.mp
          rw [hρ_supp_eq n]
          simpa [Metric.mem_ball, dist_zero_right] using ht
        rw [hρ0]
        simp
    simp only [hzero, integral_zero]
  -- Compact support.
  have hmol_cs : ∀ n, HasCompactSupport (mol n) := by
    intro n
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + 1)) fun z hz => ?_
    have hz1 : R + 1 < ‖z‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hz
    exact hmol_vanish n z hz1
  -- (d) a.e. convergence `mol n z → ν z = b.μ z` (Lebesgue differentiation:
  -- Mathlib's a.e. bump-convolution convergence for locally integrable functions,
  -- with bounded ratio `rOut ≤ 2 · rIn`).
  have hφ_rout : Tendsto (fun n => (φb n).rOut) atTop (𝓝 0) := by
    simp only [hrOut]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hφ_ratio : ∀ n : ℕ, (φb n).rOut ≤ 2 * (φb n).rIn := by
    intro n
    have h2 : 2 * (1 / (2 * ((n : ℝ) + 1))) = 1 / ((n : ℝ) + 1) := by
      have hx : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [hrOut n, hrIn n, h2]
  have htends : ∀ᵐ z : ℂ, Tendsto (fun n => mol n z) atTop (𝓝 (ν z)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K := 2)
      hφ_rout (Eventually.of_forall hφ_ratio) hν_li
  -- ===== Assemble the Beltrami coefficients and the five conjuncts. =====
  refine ⟨fun n => ⟨mol n, hmol_meas n, hmol_lt n⟩, fun n => hsmooth n, fun n => hmol_cs n,
    fun n => hmol_esssup n, fun n z hz => hmol_vanish n z hz, ?_⟩
  filter_upwards [htends, hν_ae] with z hz hze
  rw [← hze]
  exact hz

end NoWanderingDomains
