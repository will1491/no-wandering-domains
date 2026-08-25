/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.SingularIntegral.Beurling.Beltrami
import NoWanderingDomains.Analysis.SingularIntegral.Cauchy
import NoWanderingDomains.Analysis.WeakLimits.WeakL2Limit

/-!
# The Cauchy transform of a compactly vanishing `Lᵖ` field

For an exponent `2 < p`, `p ≠ ⊤`, and a field `h ∈ Lᵖ(ℂ)` vanishing outside a ball
(`∀ z, R < ‖z‖ → h z = 0`), this file develops the pointwise theory of the Cauchy transform
`P h z = -(1/π) ∫ h ζ / (ζ - z) dA ζ` (`cauchyTransform`, from `Analysis/SingularIntegral/Cauchy`):
the defining integral converges at every `z`, `P h` is globally Hölder continuous of exponent
`1 - 2/p`, and `P h z → 0` as `z → ∞`. No continuity or smoothness of `h` is used — only `MemLp`
and the vanishing condition. The companion file `QC/MRMT/NeumannSeries/PrincipalSolution.lean`
consumes these estimates: it computes the weak gradient of `P h` (coordinate components
`S h + h` and `i·(S h - h)`, `S` the Beurling transform), solves `h = μ·S h + μ` by a Banach
fixed point, and assembles the principal solution `f = id + P h` of `∂̄f = μ·∂f`. The estimates
are also used directly in `QC/MRMT/SmoothCase/`, `QC/MRMT/AnalyticDependence.lean` and
`Dynamics/Deformation/SphereVectorField/`.

## Main results

* `NoWanderingDomains.memLp_of_eLpNormEssSup_ne_top_of_support` — a measurable `μ` with
  `eLpNormEssSup μ volume ≠ ⊤` that vanishes outside `‖z‖ ≤ R` is in `Lᵖ(ℂ)` for every
  exponent `p ≠ ⊤`. This is what puts a Beltrami coefficient, the inhomogeneity of the
  singular integral equation, into `Lᵖ`.
* `NoWanderingDomains.integrable_div_sub_of_memLp_of_support` — for `2 < p`, `p ≠ ⊤`,
  `MemLp h p volume` and `h` vanishing outside `‖z‖ ≤ R`, the map `ζ ↦ h ζ / (ζ - z)` is
  integrable for every `z`, so `cauchyTransform h` is defined pointwise. `2 < p` is
  load-bearing: it puts the Hölder-conjugate exponent `q = (1 - p⁻¹)⁻¹` in `(1, 2)`, the range
  where `|ζ - z|^(-q)` is integrable on balls of the plane.
* `NoWanderingDomains.cauchyTransform_sub_le_holder` — under the same four hypotheses there is a
  constant `C ≥ 0`, uniform in the two points, with
  `‖P h z₁ - P h z₂‖ ≤ C * ‖z₁ - z₂‖ ^ (1 - 2 / p.toReal)` for all `z₁ z₂ : ℂ`: a global
  Hölder bound of exponent `1 - 2/p.toReal ∈ (0, 1)`. The proof splits the kernel difference
  into three pieces at scale `‖z₁ - z₂‖` and estimates each by Hölder against `‖h‖ₚ`.
* `NoWanderingDomains.continuous_cauchyTransform_of_memLp_of_support` — the same hypotheses give
  `Continuous (cauchyTransform h)`; the qualitative reading of the Hölder bound, and the form
  nearly all call sites use.
* `NoWanderingDomains.cauchyTransform_tendsto_cocompact` — under the same hypotheses
  `cauchyTransform h` tends to `0` along `cocompact ℂ`. Off the ball `‖ζ‖ ≤ max R 0` carrying
  `h` the integrand vanishes, and on it the kernel is bounded by `(‖z‖ - max R 0)⁻¹`, giving
  `‖P h z‖ ≤ (1/π) · (∫ ζ in ball, ‖h ζ‖) · (‖z‖ - max R 0)⁻¹` once `max R 0 + 1 ≤ ‖z‖`.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **An `L∞` coefficient vanishing outside a ball is in every `Lᵖ`, `p ≠ ∞`.** The
membership feeding the fixed-point equation: the Beltrami coefficient itself is the
inhomogeneity of the singular integral equation, and its essential boundedness
together with compact vanishing puts it in `Lᵖ(ℂ)`. -/
theorem memLp_of_eLpNormEssSup_ne_top_of_support {μ : ℂ → ℂ} {p : ℝ≥0∞} {R : ℝ}
    (_hp : p ≠ ⊤) (hμmeas : Measurable μ) (hμfin : eLpNormEssSup μ volume ≠ ⊤)
    (hsupp : ∀ z : ℂ, R < ‖z‖ → μ z = 0) :
    MemLp μ p volume := by
  -- `μ` coincides with its indicator on the closed ball of radius `R`.
  have hEq : μ = (Metric.closedBall (0 : ℂ) R).indicator μ := by
    funext z
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) R
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      refine hsupp z ?_
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hz
  -- The restriction of `volume` to the closed ball is a finite measure.
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) R)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isCompact_closedBall _ _).measure_lt_top⟩
  -- `μ` is `L^∞` for the restricted measure, hence `L^p` there by finiteness.
  have htop : MemLp μ ⊤ (volume.restrict (Metric.closedBall (0 : ℂ) R)) := by
    refine ⟨hμmeas.aestronglyMeasurable.restrict, ?_⟩
    rw [eLpNorm_exponent_top]
    exact lt_of_le_of_lt
      (eLpNormEssSup_mono_measure μ
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self))
      hμfin.lt_top
  rw [hEq]
  exact (memLp_indicator_iff_restrict measurableSet_closedBall).2
    (htop.mono_exponent le_top)

/-- **The Cauchy kernel pairs integrably with a compactly vanishing `Lᵖ` field**
(`p > 2`): for every `z`, `ζ ↦ h ζ / (ζ - z)` is integrable, since the kernel is
`L^{p'}` (`p' < 2`) on the ball carrying `h`. This is what makes `cauchyTransform h`
well-defined pointwise. -/
theorem integrable_div_sub_of_memLp_of_support {h : ℂ → ℂ} {p : ℝ≥0∞} {R : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤) (hh : MemLp h p volume)
    (hsupp : ∀ z : ℂ, R < ‖z‖ → h z = 0) (z : ℂ) :
    Integrable (fun ζ => h ζ / (ζ - z)) volume := by
  -- The Hölder-conjugate exponent `q = (1 - p⁻¹)⁻¹` of `p`.
  have hp1 : (1 : ℝ≥0∞) ≤ p := le_of_lt (lt_trans ENNReal.one_lt_two hp)
  set q : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hq_def
  have hpq : ENNReal.HolderConjugate p q := by
    rw [hq_def, ENNReal.holderConjugate_iff, inv_inv, add_comm,
      tsub_add_cancel_of_le (ENNReal.inv_le_one.mpr hp1)]
  have hq0 : q ≠ 0 := by
    rw [hq_def]
    exact ENNReal.inv_ne_zero.mpr (tsub_le_self.trans_lt ENNReal.one_lt_top).ne
  have hqtop : q ≠ ⊤ := by
    rw [hq_def]
    refine ENNReal.inv_ne_top.mpr fun h0 => ?_
    exact absurd (tsub_eq_zero_iff_le.mp h0)
      (not_le.mpr (ENNReal.inv_lt_one.mpr (lt_trans ENNReal.one_lt_two hp)))
  -- Real form of the conjugate exponent: `q.toReal = (1 - p.toReal⁻¹)⁻¹ ∈ (1, 2)`.
  have hpr2 : 2 < p.toReal := by
    have h2 := (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hp').mpr hp
    simpa using h2
  have hpr0 : 0 < p.toReal := lt_trans two_pos hpr2
  have hqtoReal : q.toReal = (1 - p.toReal⁻¹)⁻¹ := by
    rw [hq_def, ENNReal.toReal_inv,
      ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr hp1) ENNReal.one_ne_top,
      ENNReal.toReal_inv, ENNReal.toReal_one]
  have hainv0 : 0 < p.toReal⁻¹ := inv_pos.mpr hpr0
  have hainv : p.toReal⁻¹ < 2⁻¹ := by
    have hmul : p.toReal * p.toReal⁻¹ = 1 := mul_inv_cancel₀ hpr0.ne'
    nlinarith [hainv0, hpr2, hmul]
  have hb0 : 0 < 1 - p.toReal⁻¹ := by
    have h12 : (2 : ℝ)⁻¹ < 1 := by norm_num
    linarith
  have hbinv0 : 0 < (1 - p.toReal⁻¹)⁻¹ := inv_pos.mpr hb0
  have hbmul : (1 - p.toReal⁻¹) * (1 - p.toReal⁻¹)⁻¹ = 1 := mul_inv_cancel₀ hb0.ne'
  have hs1 : 1 < q.toReal := by
    rw [hqtoReal]
    nlinarith [hbmul, mul_pos hainv0 hbinv0, hbinv0]
  have hs2 : q.toReal < 2 := by
    rw [hqtoReal]
    nlinarith [hbmul, hainv, hbinv0]
  have hs0 : 0 < q.toReal := lt_trans one_pos hs1
  -- A `z`-centered ball containing the support ball `closedBall 0 R`.
  set r' : ℝ := max R 0 + ‖z‖ + 1 with hr'_def
  have hr' : 0 < r' := by rw [hr'_def]; positivity
  have hBsub : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball z r' := by
    intro ζ hζ
    rw [Metric.mem_closedBall, dist_zero_right] at hζ
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖ζ - z‖ ≤ ‖ζ‖ + ‖z‖ := norm_sub_le ζ z
      _ ≤ max R 0 + ‖z‖ := by
          have hRmax : R ≤ max R 0 := le_max_left R 0
          linarith
      _ < r' := by rw [hr'_def]; linarith
  -- Pointwise identification of the kernel's enorm power with a real negative power.
  have hpt : ∀ w : ℂ, ‖w⁻¹‖ₑ ^ q.toReal = ‖‖w‖ ^ (-q.toReal)‖ₑ := fun w => by
    rw [← ofReal_norm, ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs0.le,
      norm_inv, Real.inv_rpow (norm_nonneg w), ← Real.rpow_neg (norm_nonneg w),
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg w) _)]
  -- Integrability of `‖·‖^(-q.toReal)` on `ball 0 r'` (dimension 2, exponent < 2).
  have hnegpow : IntegrableOn (fun w : ℂ => ‖w‖ ^ (-q.toReal))
      (Metric.ball (0 : ℂ) r') volume := by
    rw [← integrable_indicator_iff measurableSet_ball]
    set F : ℝ → ℝ := fun t : ℝ => if t < r' then t ^ (-q.toReal) else 0 with hF
    have heq : (Metric.ball (0 : ℂ) r').indicator (fun w : ℂ => ‖w‖ ^ (-q.toReal))
        = fun w : ℂ => F ‖w‖ := by
      funext w
      simp only [Set.indicator, hF]
      by_cases hw : w ∈ Metric.ball (0 : ℂ) r'
      · rw [if_pos hw]
        have hwr : ‖w‖ < r' := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        rw [if_pos hwr]
      · rw [if_neg hw]
        have hwr : ¬ ‖w‖ < r' := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        rw [if_neg hwr]
    rw [heq]
    rw [show (fun w : ℂ => F ‖w‖) = (F ‖·‖) from rfl]
    rw [integrable_fun_norm_addHaar volume]
    rw [Complex.finrank_real_complex]
    have hbase : IntegrableOn
        ((Set.Ioo (0 : ℝ) r').indicator fun y : ℝ => y ^ (1 - q.toReal))
        (Set.Ioi 0) volume := by
      rw [integrableOn_indicator_iff measurableSet_Ioo]
      have hsub : Set.Ioo (0 : ℝ) r' ∩ Set.Ioi 0 = Set.Ioo (0 : ℝ) r' :=
        Set.inter_eq_left.mpr fun y hy => hy.1
      rw [hsub, intervalIntegral.integrableOn_Ioo_rpow_iff hr']
      linarith
    apply hbase.congr_fun _ measurableSet_Ioi
    intro y hy
    simp only [Set.mem_Ioi] at hy
    simp only [hF, smul_eq_mul, Set.indicator]
    by_cases hyR : y < r'
    · rw [if_pos ⟨hy, hyR⟩, if_pos hyR,
        show (1 - q.toReal) = (1 : ℝ) + (-q.toReal) by ring, Real.rpow_add hy,
        Real.rpow_one]
      norm_num
    · rw [if_neg fun hc => hyR hc.2, if_neg hyR, mul_zero]
  -- Translation: center the kernel lintegral at the origin.
  have htransl : ∫⁻ ζ in Metric.ball z r', ‖(ζ - z)⁻¹‖ₑ ^ q.toReal
      = ∫⁻ w in Metric.ball (0 : ℂ) r', ‖w⁻¹‖ₑ ^ q.toReal := by
    have hmem : ∀ ζ : ℂ, ζ ∈ Metric.ball z r' ↔ ζ - z ∈ Metric.ball (0 : ℂ) r' := by
      intro ζ
      simp only [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc ∫⁻ ζ in Metric.ball z r', ‖(ζ - z)⁻¹‖ₑ ^ q.toReal
        = ∫⁻ ζ, (Metric.ball z r').indicator (fun ζ => ‖(ζ - z)⁻¹‖ₑ ^ q.toReal) ζ := by
          rw [lintegral_indicator measurableSet_ball]
      _ = ∫⁻ ζ, (Metric.ball (0 : ℂ) r').indicator
            (fun w => ‖w⁻¹‖ₑ ^ q.toReal) (ζ - z) := by
          apply lintegral_congr
          intro ζ
          unfold Set.indicator
          by_cases hζ : ζ ∈ Metric.ball z r'
          · rw [if_pos hζ, if_pos ((hmem ζ).mp hζ)]
          · rw [if_neg hζ, if_neg fun hc => hζ ((hmem ζ).mpr hc)]
      _ = ∫⁻ ζ, (Metric.ball (0 : ℂ) r').indicator (fun w => ‖w⁻¹‖ₑ ^ q.toReal) ζ :=
          lintegral_sub_right_eq_self _ z
      _ = ∫⁻ w in Metric.ball (0 : ℂ) r', ‖w⁻¹‖ₑ ^ q.toReal := by
          rw [lintegral_indicator measurableSet_ball]
  -- Finiteness of the kernel mass at exponent `q.toReal` on the origin ball.
  have hfin : ∫⁻ w in Metric.ball (0 : ℂ) r', ‖w⁻¹‖ₑ ^ q.toReal < ⊤ := by
    have h2 := hnegpow.2
    rw [hasFiniteIntegral_iff_enorm] at h2
    calc ∫⁻ w in Metric.ball (0 : ℂ) r', ‖w⁻¹‖ₑ ^ q.toReal
        = ∫⁻ w in Metric.ball (0 : ℂ) r', ‖‖w‖ ^ (-q.toReal)‖ₑ := lintegral_congr hpt
      _ < ⊤ := h2
  -- The Cauchy kernel is `L^q` on the support ball.
  have hker : MemLp (fun ζ : ℂ => (ζ - z)⁻¹) q
      (volume.restrict (Metric.closedBall (0 : ℂ) R)) := by
    refine ⟨((measurable_id.sub_const z).inv).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0 hqtop]
    calc ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ‖(ζ - z)⁻¹‖ₑ ^ q.toReal
        ≤ ∫⁻ ζ in Metric.ball z r', ‖(ζ - z)⁻¹‖ₑ ^ q.toReal := lintegral_mono_set hBsub
      _ = ∫⁻ w in Metric.ball (0 : ℂ) r', ‖w⁻¹‖ₑ ^ q.toReal := htransl
      _ < ⊤ := hfin
  -- Hölder pairing on the support ball.
  have hhB : MemLp h p (volume.restrict (Metric.closedBall (0 : ℂ) R)) := hh.restrict _
  have hprod : Integrable (h * fun ζ : ℂ => (ζ - z)⁻¹)
      (volume.restrict (Metric.closedBall (0 : ℂ) R)) := hhB.integrable_mul hker
  -- The integrand vanishes off the support ball; conclude.
  have hsuppsub : Function.support (fun ζ : ℂ => h ζ / (ζ - z))
      ⊆ Metric.closedBall (0 : ℂ) R := by
    rw [Function.support_subset_iff']
    intro ζ hζ
    have hζR : R < ‖ζ‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hζ
    rw [hsupp ζ hζR, zero_div]
  rw [← integrableOn_iff_integrable_of_support_subset hsuppsub]
  exact hprod.congr (Filter.Eventually.of_forall fun ζ => by
    simp only [Pi.mul_apply]
    rw [div_eq_mul_inv])

/-- **Global Hölder continuity of the Cauchy transform of a compactly vanishing `Lᵖ`
field** (`p > 2`), with exponent `1 - 2/p`: there is a constant `C` (depending on
`p`, `R`, and `‖h‖ₚ`) with

`‖P h z₁ − P h z₂‖ ≤ C · ‖z₁ − z₂‖^(1−2/p)` for all `z₁ z₂`.

The difference of kernels `1/(ζ−z₁) − 1/(ζ−z₂)` is estimated against `‖h‖ₚ` by
Hölder's inequality, splitting at scale `‖z₁ − z₂‖`. -/
theorem cauchyTransform_sub_le_holder {h : ℂ → ℂ} {p : ℝ≥0∞} {R : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤) (hh : MemLp h p volume)
    (hsupp : ∀ z : ℂ, R < ‖z‖ → h z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z₁ z₂ : ℂ,
      ‖cauchyTransform h z₁ - cauchyTransform h z₂‖
        ≤ C * ‖z₁ - z₂‖ ^ (1 - 2 / p.toReal) := by
  have hint : ∀ z : ℂ, Integrable (fun ζ => h ζ / (ζ - z)) volume := fun z =>
    integrable_div_sub_of_memLp_of_support hp hp' hh hsupp z
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
  -- ===== Global constants =====
  set N : ℝ≥0∞ := eLpNorm h p volume with hN_def
  have hN_ne : N ≠ ⊤ := hh.2.ne
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
  -- ===== Hölder machinery =====
  have htri : ∀ a b : ℂ, ‖a - b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := fun a b => by
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_sub_le a b)
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
  have hscale : ∀ c r : ℝ, 0 ≤ c → 0 < r →
      ENNReal.ofReal (c * r ^ (2 - qr)) ^ (1/qr)
        = ENNReal.ofReal (c ^ (1/qr) * r ^ α) := by
    intro c r hc hr
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hc (Real.rpow_nonneg hr.le _))
        (le_of_lt (one_div_pos.mpr hqr0)),
      Real.mul_rpow hc (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le,
      mul_one_div, hαqr]
  -- ===== Conclusion =====
  refine ⟨1 / Real.pi * (N.toReal * κ), by positivity, ?_⟩
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
      _ = 1/Real.pi * (N.toReal * κ) * d ^ α := by ring

/-- **Continuity of the Cauchy transform of a compactly vanishing `Lᵖ` field**
(`p > 2`) — the qualitative consequence of the global Hölder bound. -/
theorem continuous_cauchyTransform_of_memLp_of_support {h : ℂ → ℂ} {p : ℝ≥0∞} {R : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤) (hh : MemLp h p volume)
    (hsupp : ∀ z : ℂ, R < ‖z‖ → h z = 0) :
    Continuous (cauchyTransform h) := by
  obtain ⟨C, hC0, hHolder⟩ := cauchyTransform_sub_le_holder hp hp' hh hsupp
  have hpr2 : 2 < p.toReal := by
    have h2 := (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hp').mpr hp
    simpa using h2
  have hα0 : 0 < 1 - 2 / p.toReal := by
    have hpr0 : 0 < p.toReal := lt_trans two_pos hpr2
    have hlt : 2 / p.toReal < 1 := (div_lt_one hpr0).mpr hpr2
    linarith
  rw [continuous_iff_continuousAt]
  intro z₀
  have hbound : ∀ z : ℂ, dist (cauchyTransform h z) (cauchyTransform h z₀)
      ≤ C * ‖z - z₀‖ ^ (1 - 2 / p.toReal) := fun z => by
    rw [dist_eq_norm]
    exact hHolder z z₀
  have htends : Filter.Tendsto (fun z : ℂ => C * ‖z - z₀‖ ^ (1 - 2 / p.toReal))
      (𝓝 z₀) (𝓝 0) := by
    have h1 : Filter.Tendsto (fun z : ℂ => ‖z - z₀‖) (𝓝 z₀) (𝓝 0) := by
      have h1' : Continuous fun z : ℂ => ‖z - z₀‖ :=
        (continuous_id.sub continuous_const).norm
      have h1'' := h1'.tendsto z₀
      simpa using h1''
    have h2 : ContinuousAt (fun t : ℝ => t ^ (1 - 2 / p.toReal)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr hα0.le)
    have h3 : Filter.Tendsto (fun z : ℂ => ‖z - z₀‖ ^ (1 - 2 / p.toReal))
        (𝓝 z₀) (𝓝 0) := by
      have h3' := Filter.Tendsto.comp h2 h1
      simpa [Function.comp, Real.zero_rpow hα0.ne'] using! h3'
    have h4 := h3.const_mul C
    simpa using h4
  exact tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero (fun z => dist_nonneg) hbound htends)

/-- **The Cauchy transform of a compactly vanishing `Lᵖ` field vanishes at infinity**
(`p > 2`): `P h (z) → 0` as `z → ∞`. Far from the ball carrying `h` the kernel is
uniformly small, and Hölder's inequality on the ball gives the decay. This is the
principal normalization `f(z) − z → 0`. -/
theorem cauchyTransform_tendsto_cocompact {h : ℂ → ℂ} {p : ℝ≥0∞} {R : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤) (hh : MemLp h p volume)
    (hsupp : ∀ z : ℂ, R < ‖z‖ → h z = 0) :
    Tendsto (cauchyTransform h) (Filter.cocompact ℂ) (𝓝 0) := by
  have hint : ∀ z : ℂ, Integrable (fun ζ => h ζ / (ζ - z)) volume := fun z =>
    integrable_div_sub_of_memLp_of_support hp hp' hh hsupp z
  -- support ball and the L¹ mass of `h`
  set m : ℝ := max R 0 with hm_def
  set B : Set ℂ := Metric.closedBall (0:ℂ) m with hB_def
  have : IsFiniteMeasure (volume.restrict B) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hp1 : (1 : ℝ≥0∞) ≤ p := le_of_lt (lt_trans ENNReal.one_lt_two hp)
  have hh1 : MemLp h 1 (volume.restrict B) := (hh.restrict B).mono_exponent hp1
  have hint1 : IntegrableOn h B volume := memLp_one_iff_integrable.mp hh1
  set I₀ : ℝ := ∫ ζ in B, ‖h ζ‖ with hI₀_def
  have hI₀0 : 0 ≤ I₀ := integral_nonneg fun ζ => norm_nonneg _
  have hconst : ‖-(1/(Real.pi:ℂ))‖ = 1/Real.pi := by
    rw [norm_neg, norm_div, norm_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  -- the far-field pointwise bound
  have hkey : ∀ z : ℂ, m + 1 ≤ ‖z‖ →
      ‖cauchyTransform h z‖ ≤ 1/Real.pi * I₀ * (‖z‖ - m)⁻¹ := by
    intro z hz
    have hzm : 0 < ‖z‖ - m := by linarith
    -- the integrand vanishes off `B`
    have hsuppz : ∀ ζ : ℂ, ζ ∉ B → h ζ / (ζ - z) = 0 := by
      intro ζ hζ
      have hζm : m < ‖ζ‖ := by
        simpa [hB_def, Metric.mem_closedBall, dist_zero_right, not_le] using hζ
      have hζR : R < ‖ζ‖ := lt_of_le_of_lt (le_max_left R 0) hζm
      rw [hsupp ζ hζR, zero_div]
    have hres : ∫ ζ, h ζ / (ζ - z) = ∫ ζ in B, h ζ / (ζ - z) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hsuppz).symm
    rw [cauchyTransform, norm_mul, hconst, hres]
    have hbound : ‖∫ ζ in B, h ζ / (ζ - z)‖ ≤ ∫ ζ in B, ‖h ζ‖ * (‖z‖ - m)⁻¹ := by
      refine le_trans (norm_integral_le_integral_norm _) ?_
      refine setIntegral_mono_on ?_ ?_ measurableSet_closedBall ?_
      · exact ((hint z).integrableOn).norm
      · exact hint1.norm.mul_const _
      · intro ζ hζ
        have hζm : ‖ζ‖ ≤ m := by
          simpa [hB_def, Metric.mem_closedBall, dist_zero_right] using hζ
        have hζz : ‖z‖ - m ≤ ‖ζ - z‖ := by
          have h1 : ‖z‖ - ‖ζ‖ ≤ ‖z - ζ‖ := norm_sub_norm_le z ζ
          rw [norm_sub_rev] at h1
          linarith
        rw [norm_div, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ hzm hζz) (norm_nonneg _)
    calc 1/Real.pi * ‖∫ ζ in B, h ζ / (ζ - z)‖
        ≤ 1/Real.pi * ∫ ζ in B, ‖h ζ‖ * (‖z‖ - m)⁻¹ :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 1/Real.pi * (I₀ * (‖z‖ - m)⁻¹) := by rw [integral_mul_const]
      _ = 1/Real.pi * I₀ * (‖z‖ - m)⁻¹ := by ring
  -- filter plumbing: squeeze along `cocompact`
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (Filter.cocompact ℂ) atTop :=
    tendsto_norm_cocompact_atTop
  have hmaj : Tendsto (fun z : ℂ => 1/Real.pi * I₀ * (‖z‖ - m)⁻¹)
      (Filter.cocompact ℂ) (𝓝 0) := by
    have haux : Tendsto (fun t : ℝ => t - m) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (-m) tendsto_id).congr
        fun t => (sub_eq_add_neg t m).symm
    have hinv : Tendsto (fun t : ℝ => (t - m)⁻¹) atTop (𝓝 0) :=
      haux.inv_tendsto_atTop
    have hcomp := hinv.comp hnorm
    have hfinal := hcomp.const_mul (1/Real.pi * I₀)
    simpa [Function.comp] using hfinal
  have hev : ∀ᶠ z : ℂ in Filter.cocompact ℂ,
      ‖cauchyTransform h z‖ ≤ 1/Real.pi * I₀ * (‖z‖ - m)⁻¹ := by
    filter_upwards [hnorm.eventually_ge_atTop (m + 1)] with z hz
    exact hkey z hz
  have h0 : ∀ᶠ z : ℂ in Filter.cocompact ℂ, 0 ≤ ‖cauchyTransform h z‖ :=
    Filter.Eventually.of_forall fun z => norm_nonneg _
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' h0 hev hmaj)

end NoWanderingDomains
