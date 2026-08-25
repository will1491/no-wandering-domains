/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.SingularIntegral.Beurling.DirichletIsometry

/-!
# The Beurling transform — Convolution

The truncated Beurling operator as a convolution, Young's inequality
(`eLpNorm_convolution_le`), the convolution bounded-linear map `convCLM` and its
adjoint, and the dyadic pieces with their mean-zero (Cotlar–Stein) integrals.

Part of the `Beurling` development (overview in `Beurling/Kernel.lean`). -/

open MeasureTheory Complex Filter Topology
open scoped Real ENNReal NNReal Convolution InnerProductSpace

namespace NoWanderingDomains

variable {μ : ℂ → ℂ} {z : ℂ} {p : ℝ≥0∞}

/-- The **truncated Beurling convolution kernel** `k_r(u) = u⁻² · 1_{‖u‖ ≥ r}`.

This is the translation-invariant kernel of the truncated Beurling operator:
`czOperator beurlingKernel r f = k_r ⋆ f` (`czOperator_beurling_eq_convolution`).
Truncating below `r` removes the non-integrable singularity at `0`; the remaining
`|u|⁻²` tail is square-integrable on `ℂ = ℝ²` (`‖k_r‖₂² = π r⁻²`) but *not*
integrable (the `2D` tail `∫_{|u|>r} |u|⁻² = 2π ∫_r^∞ ρ⁻¹ dρ` diverges
logarithmically), so the operator is a genuine principal-value singular integral,
not a Young-type `L¹⋆L²` convolution.

The set `{u | r ≤ ‖u‖}` (closed) is chosen to match `(ball x r)ᶜ` exactly, so the
identification with `czOperator` is a strict equality (no `a.e.` slack). -/
noncomputable def truncBeurlingKernel (r : ℝ) (u : ℂ) : ℂ :=
  Set.indicator {u : ℂ | r ≤ ‖u‖} (fun u => u ^ (-2 : ℤ)) u

/-- **The truncated Beurling operator is convolution against `truncBeurlingKernel`.**
`czOperator beurlingKernel r f x = ∫_{‖y-x‖≥r} (x-y)⁻² f y dy = (k_r ⋆ f)(x)`, with
`k_r(u) = u⁻²·1_{‖u‖≥r}`. The substitution `t = x - y` turns the `(ball x r)ᶜ`
integral over `y` into the convolution integral `∫ t, k_r t · f(x-t)`; left
invariance of Lebesgue measure (`integral_sub_left_eq_self`) supplies the change of
variables, and the truncation sets match on the nose because `(ball x r)ᶜ =
{y | r ≤ ‖y-x‖}` corresponds under `t = x-y` to `{t | r ≤ ‖t‖}`. -/
lemma czOperator_beurling_eq_convolution (r : ℝ) (f : ℂ → ℂ) :
    czOperator beurlingKernel r f
      = MeasureTheory.convolution (truncBeurlingKernel r) f
          (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext x
  rw [MeasureTheory.convolution_mul]
  change (∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * f y)
      = ∫ t, truncBeurlingKernel r t * f (x - t)
  rw [← integral_indicator measurableSet_ball.compl]
  rw [show (fun t => truncBeurlingKernel r t * f (x - t))
        = (fun t => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y * f y) (x - t))
        from ?_]
  · rw [MeasureTheory.integral_sub_left_eq_self
        (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y * f y) y) volume x]
  · funext t
    have hmem : (x - t ∈ (Metric.ball x r)ᶜ) ↔ (t ∈ {u : ℂ | r ≤ ‖u‖}) := by
      simp only [Set.mem_compl_iff, Metric.mem_ball, Set.mem_ofPred_eq, not_lt, dist_eq_norm,
        show x - t - x = -t by ring, norm_neg]
    by_cases h : t ∈ {u : ℂ | r ≤ ‖u‖}
    · have h2 : (x - t) ∈ (Metric.ball x r)ᶜ := hmem.mpr h
      rw [truncBeurlingKernel, Set.indicator_of_mem h, Set.indicator_of_mem h2, beurlingKernel,
        show x - (x - t) = t by ring]
    · have h2 : (x - t) ∉ (Metric.ball x r)ᶜ := fun hc => h (hmem.mp hc)
      rw [truncBeurlingKernel, Set.indicator_of_notMem h, Set.indicator_of_notMem h2, zero_mul]

/-- **Young's convolution inequality `L¹ ⋆ L² → L²`.** For `g ∈ L¹(ℂ)` and
`f ∈ L²(ℂ)` the convolution `g ⋆ f` lies in `L²(ℂ)` with `‖g ⋆ f‖₂ ≤ ‖g‖₁ ‖f‖₂`.

Mathlib has *no* `Lᵖ` Young inequality (an explicit "To do" in
`Mathlib/Analysis/Convolution.lean`), so we build it here from the continuous
Minkowski integral inequality (`MeasureTheory.lintegral_lintegral_pow_swap`,
supplied by the Carleson `RealInterpolation.Minkowski` file): writing
`‖(g ⋆ f)(x)‖ₑ ≤ ∫ ‖g(t)‖ ‖f(x-t)‖ dt` (triangle inequality for the Bochner
integral) and applying Minkowski with exponent `2` reduces to the translation
invariance `‖f(·-t)‖₂ = ‖f‖₂`, which factors out the `t`-integral of `‖g‖`. -/
lemma eLpNorm_convolution_le {g f : ℂ → ℂ}
    (hg : MemLp g 1 volume) (hf : MemLp f 2 volume) :
    eLpNorm (MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume) 2 volume
      ≤ eLpNorm g 1 volume * eLpNorm f 2 volume := by
  set G : ℂ → ℂ → ℝ≥0∞ := fun x t => ‖g t‖ₑ * ‖f (x - t)‖ₑ with hG
  have hgm : AEMeasurable (fun t => ‖g t‖ₑ) volume := hg.1.enorm
  have hfm : AEStronglyMeasurable f volume := hf.1
  -- Step 1: pointwise enorm bound on the convolution integral
  have hpt : ∀ x, ‖MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume x‖ₑ
      ≤ ∫⁻ t, G x t ∂volume := by
    intro x
    rw [MeasureTheory.convolution_mul]
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    apply lintegral_mono
    intro t
    simp only [hG, enorm_mul, le_refl]
  -- Step 2: rewrite `eLpNorm 2` as a lintegral and monotone-bound
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [show (2:ℝ≥0∞).toReal = (2:ℝ) by norm_num]
  have hmono :
      (∫⁻ x, ‖MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume x‖ₑ ^ (2:ℝ)
          ∂volume) ^ (1 / (2:ℝ))
        ≤ (∫⁻ x, (∫⁻ t, G x t ∂volume) ^ (2:ℝ) ∂volume) ^ (1 / (2:ℝ)) := by
    gcongr with x
    exact hpt x
  refine le_trans hmono ?_
  -- Step 3: Minkowski's integral inequality (p = 2)
  have hGmeas : AEMeasurable (Function.uncurry G) (volume.prod volume) := by
    apply AEMeasurable.fun_mul
    · exact hgm.comp_snd
    · have hsub : AEStronglyMeasurable (fun p : ℂ × ℂ => f (p.1 - p.2)) (volume.prod volume) :=
        hfm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant volume volume)
      exact hsub.enorm
  have hMink := MeasureTheory.lintegral_lintegral_pow_swap (p := (2:ℝ)) (by norm_num)
    (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ)) (f := G) hGmeas
  rw [show (1 / (2:ℝ)) = (2:ℝ)⁻¹ by norm_num]
  refine le_trans hMink ?_
  -- Step 4: evaluate the inner lintegral via translation invariance
  have hinner : ∀ t, (∫⁻ x, (G x t) ^ (2:ℝ) ∂volume) ^ (2:ℝ)⁻¹
      = ‖g t‖ₑ * eLpNorm f 2 volume := by
    intro t
    simp only [hG]
    have hsplit : (fun x => (‖g t‖ₑ * ‖f (x - t)‖ₑ) ^ (2:ℝ))
        = (fun x => ‖g t‖ₑ ^ (2:ℝ) * ‖f (x - t)‖ₑ ^ (2:ℝ)) := by
      funext x; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    rw [hsplit, lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by simp))]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    rw [← ENNReal.rpow_mul]
    rw [show (2:ℝ) * (2:ℝ)⁻¹ = 1 by norm_num, ENNReal.rpow_one]
    have htrans : eLpNorm (fun x => f (x - t)) 2 volume = eLpNorm f 2 volume :=
      eLpNorm_comp_measurePreserving hfm (measurePreserving_sub_right volume t)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at htrans
    simp only [show (2:ℝ≥0∞).toReal = (2:ℝ) by norm_num] at htrans
    rw [one_div] at htrans
    rw [htrans]
  rw [lintegral_congr hinner]
  rw [lintegral_mul_const'' _ hgm]
  rw [← eLpNorm_one_eq_lintegral_enorm]

/-- **Dyadic piece of the (truncated) Beurling kernel.** The annular restriction
`ψ_j(u) = u⁻²·1_{2ʲr ≤ ‖u‖ < 2ʲ⁺¹r}` of the singular kernel `u⁻²`. The truncated
Beurling kernel `k_r = u⁻²·1_{‖u‖≥r}` is the (a.e.) sum `∑_j ψ_j` of these dyadic
pieces, each of which is genuinely `L¹` (the divergence is only in summing over
`j`). These are the building blocks of the dyadic almost-orthogonality
decomposition. -/
noncomputable def dyadicBeurling (r : ℝ) (j : ℕ) (u : ℂ) : ℂ :=
  Set.indicator {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r}
    (fun u => u ^ (-2 : ℤ)) u

/-- The dyadic annulus `{2ʲr ≤ ‖u‖ < 2ʲ⁺¹r}` is measurable. -/
lemma measurableSet_dyadicAnnulus (r : ℝ) (j : ℕ) :
    MeasurableSet {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r} := by
  apply MeasurableSet.inter
  · exact measurableSet_le measurable_const measurable_norm
  · exact measurableSet_lt measurable_norm measurable_const

/-- The `enorm` of a dyadic piece is the annular indicator of `‖u⁻²‖ₑ`. -/
lemma enorm_dyadicBeurling (r : ℝ) (j : ℕ) (u : ℂ) :
    ‖dyadicBeurling r j u‖ₑ
      = Set.indicator {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r}
          (fun u => ‖(u ^ (-2:ℤ) : ℂ)‖ₑ) u := by
  rw [dyadicBeurling]
  by_cases h : u ∈ {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    simp

/-- **The `L¹` norm of every dyadic piece is `2π log 2`,** uniform in `j` and `r`.
This is the key uniform bound: each annular piece has the same `L¹` mass, the
logarithmic divergence of `‖k_r‖₁` arising purely from the (infinitely many)
dyadic scales `∑_j 2π log 2 = ∞`. Computed via `annulus_lintegral` with the
endpoints `a = 2ʲr`, `b = 2ʲ⁺¹r`, where `log(b/a) = log 2`. -/
lemma eLpNorm_dyadicBeurling (r : ℝ) (hr : 0 < r) (j : ℕ) :
    eLpNorm (dyadicBeurling r j) 1 volume = ENNReal.ofReal (2 * Real.pi * Real.log 2) := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hpt : (fun u => ‖dyadicBeurling r j u‖ₑ)
      = Set.indicator {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r}
          (fun u => ‖(u ^ (-2:ℤ) : ℂ)‖ₑ) := by
    funext u; exact enorm_dyadicBeurling r j u
  rw [hpt]
  rw [lintegral_indicator (measurableSet_dyadicAnnulus r j)]
  have ha : 0 < (2:ℝ)^j * r := by positivity
  have hab : (2:ℝ)^j * r < (2:ℝ)^(j+1) * r := by
    apply mul_lt_mul_of_pos_right _ hr
    apply pow_lt_pow_right₀ (by norm_num) (by omega)
  rw [SingularIntegral.annulus_lintegral _ _ ha hab]
  have heq : (2:ℝ)^(j+1) * r / ((2:ℝ)^j * r) = 2 := by
    rw [pow_succ]
    have h2j : (2:ℝ)^j ≠ 0 := by positivity
    field_simp
  rw [heq]

/-- **Each dyadic piece lies in `L¹`.** Immediate from
`eLpNorm_dyadicBeurling` (finite `L¹` mass) plus measurability of the annular
indicator of `u ↦ u⁻²`. -/
lemma memLp_dyadicBeurling (r : ℝ) (hr : 0 < r) (j : ℕ) :
    MemLp (dyadicBeurling r j) 1 volume := by
  constructor
  · apply AEStronglyMeasurable.indicator _ (measurableSet_dyadicAnnulus r j)
    apply Measurable.aestronglyMeasurable
    have : (fun u : ℂ => u ^ (-2 : ℤ)) = (fun u : ℂ => (u * u)⁻¹) := by
      funext u; rw [zpow_neg, zpow_two]
    rw [this]
    exact (measurable_id.mul measurable_id).inv
  · rw [eLpNorm_dyadicBeurling r hr j]
    exact ENNReal.ofReal_lt_top

/-- **`L¹ ⋆ L² ⊆ L²`.** For `g ∈ L¹(ℂ)` and `f ∈ L²(ℂ)` the convolution `g ⋆ f`
again lies in `L²(ℂ)`. The `eLpNorm < ∞` half is the Young inequality
`eLpNorm_convolution_le`; the `AEStronglyMeasurable` half is measurability of the
parametrized integral `x ↦ ∫ t, g t · f (x - t)` via
`AEStronglyMeasurable.integral_prod_right'`. This packages a convolution against a
fixed `L¹` kernel as a self-map of `L²`, the analytic substrate of the
Cotlar–Stein dyadic operators. -/
lemma memLp_convolution_two {g : ℂ → ℂ} (hg : MemLp g 1 volume) {f : ℂ → ℂ}
    (hf : MemLp f 2 volume) :
    MemLp (MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume) 2 volume := by
  constructor
  · have hint : AEStronglyMeasurable
        (Function.uncurry fun x t => g t * f (x - t)) (volume.prod volume) := by
      apply AEStronglyMeasurable.mul
      · exact hg.1.comp_snd
      · exact hf.1.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant volume volume)
    have hmeas := hint.integral_prod_right' (ν := (volume : Measure ℂ))
    simp only [Function.uncurry] at hmeas
    have hconv : (MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume)
        = (fun x => ∫ t, g t * f (x - t) ∂volume) := by
      funext x; rw [MeasureTheory.convolution_mul]
    rw [hconv]
    exact hmeas
  · exact lt_of_le_of_lt (eLpNorm_convolution_le hg hf)
      (ENNReal.mul_lt_top hg.2 hf.2)

/-- For `g ∈ L¹` and `f ∈ L²`, the convolution integrand `t ↦ g t * f (x - t)` is
integrable for a.e. `x`. This is the a.e. existence of the L¹⋆L² convolution. -/
lemma ae_convolutionExistsAt {g : ℂ → ℂ} (hg : MemLp g 1 volume) {f : ℂ → ℂ}
    (hf : MemLp f 2 volume) :
    ∀ᵐ x ∂volume, ConvolutionExistsAt g f x (ContinuousLinearMap.mul ℂ ℂ) volume := by
  -- enorm integrand as a lintegral; finiteness for a.e. x from Young.
  set G : ℂ → ℂ → ℝ≥0∞ := fun x t => ‖g t‖ₑ * ‖f (x - t)‖ₑ with hG
  have hgm : AEMeasurable (fun t => ‖g t‖ₑ) volume := hg.1.enorm
  have hfm : AEStronglyMeasurable f volume := hf.1
  have hGmeas : AEMeasurable (Function.uncurry G) (volume.prod volume) := by
    apply AEMeasurable.fun_mul
    · exact hgm.comp_snd
    · have hsub : AEStronglyMeasurable (fun p : ℂ × ℂ => f (p.1 - p.2)) (volume.prod volume) :=
        hfm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant volume volume)
      exact hsub.enorm
  have hMink := MeasureTheory.lintegral_lintegral_pow_swap (p := (2:ℝ)) (by norm_num)
    (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ)) (f := G) hGmeas
  have hinner : ∀ t, (∫⁻ x, (G x t) ^ (2:ℝ) ∂volume) ^ (2:ℝ)⁻¹
      = ‖g t‖ₑ * eLpNorm f 2 volume := by
    intro t
    simp only [hG]
    have hsplit : (fun x => (‖g t‖ₑ * ‖f (x - t)‖ₑ) ^ (2:ℝ))
        = (fun x => ‖g t‖ₑ ^ (2:ℝ) * ‖f (x - t)‖ₑ ^ (2:ℝ)) := by
      funext x; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    rw [hsplit, lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by simp))]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    rw [← ENNReal.rpow_mul]
    rw [show (2:ℝ) * (2:ℝ)⁻¹ = 1 by norm_num, ENNReal.rpow_one]
    have htrans : eLpNorm (fun x => f (x - t)) 2 volume = eLpNorm f 2 volume :=
      eLpNorm_comp_measurePreserving hfm (measurePreserving_sub_right volume t)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at htrans
    simp only [show (2:ℝ≥0∞).toReal = (2:ℝ) by norm_num] at htrans
    rw [one_div] at htrans
    rw [htrans]
  have hRHS : (∫⁻ t, (∫⁻ x, (G x t) ^ (2:ℝ) ∂volume) ^ (2:ℝ)⁻¹ ∂volume)
      = eLpNorm g 1 volume * eLpNorm f 2 volume := by
    rw [lintegral_congr hinner, lintegral_mul_const'' _ hgm, ← eLpNorm_one_eq_lintegral_enorm]
  have hRHS_lt : (∫⁻ t, (∫⁻ x, (G x t) ^ (2:ℝ) ∂volume) ^ (2:ℝ)⁻¹ ∂volume) < ⊤ := by
    rw [hRHS]; exact ENNReal.mul_lt_top hg.2 hf.2
  have hLHS_lt : (∫⁻ x, (∫⁻ t, G x t ∂volume) ^ (2:ℝ) ∂volume) ^ (2:ℝ)⁻¹ < ⊤ :=
    lt_of_le_of_lt hMink hRHS_lt
  have hdouble_lt : (∫⁻ x, (∫⁻ t, G x t ∂volume) ^ (2:ℝ) ∂volume) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [h] at hLHS_lt
    simp only [ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < (2:ℝ)⁻¹)] at hLHS_lt
    exact (lt_irrefl _ hLHS_lt)
  have hae_pow : ∀ᵐ x ∂volume, (∫⁻ t, G x t ∂volume) ^ (2:ℝ) < ⊤ :=
    ae_lt_top' (by
      apply AEMeasurable.pow_const
      exact hGmeas.lintegral_prod_right') hdouble_lt.ne
  have hae_inner : ∀ᵐ x ∂volume, (∫⁻ t, G x t ∂volume) < ⊤ := by
    filter_upwards [hae_pow] with x hx
    rw [lt_top_iff_ne_top]
    intro h
    rw [h] at hx
    simp only [ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < (2:ℝ))] at hx
    exact (lt_irrefl _ hx)
  filter_upwards [hae_inner] with x hx
  refine ⟨?_, ?_⟩
  · apply hg.1.mul
    exact hfm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure ℂ) x)
  · rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt ?_ hx
    apply lintegral_mono
    intro t
    simp only [hG, ContinuousLinearMap.mul_apply', enorm_mul, le_refl]

/-- The convolution `g ⋆ F` of an `L¹` kernel `g` with the `L²` representative of
`F`, packaged back into `L²`. -/
noncomputable def convToLp (g : ℂ → ℂ) (hg : MemLp g 1 volume)
    (F : Lp ℂ 2 (volume : Measure ℂ)) :
    Lp ℂ 2 (volume : Measure ℂ) :=
  (memLp_convolution_two hg (Lp.memLp F)).toLp
    (MeasureTheory.convolution g (F : ℂ → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume)

/-- Convolution by `g` is additive (a.e.) in the second argument, for `g ∈ L¹` and
`F₁, F₂ ∈ L²`. -/
lemma convolution_ae_add {g : ℂ → ℂ} (hg : MemLp g 1 volume)
    {f₁ f₂ : ℂ → ℂ} (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume) :
    MeasureTheory.convolution g (f₁ + f₂) (ContinuousLinearMap.mul ℂ ℂ) volume
      =ᵐ[volume]
        MeasureTheory.convolution g f₁ (ContinuousLinearMap.mul ℂ ℂ) volume
          + MeasureTheory.convolution g f₂ (ContinuousLinearMap.mul ℂ ℂ) volume := by
  filter_upwards [ae_convolutionExistsAt hg hf₁, ae_convolutionExistsAt hg hf₂] with x h₁ h₂
  exact h₁.distrib_add h₂

/-- The underlying linear map `F ↦ g ⋆ F` on `L²`. -/
noncomputable def convLM (g : ℂ → ℂ) (hg : MemLp g 1 volume) :
    (Lp ℂ 2 (volume : Measure ℂ)) →ₗ[ℂ] (Lp ℂ 2 (volume : Measure ℂ)) where
  toFun F := convToLp g hg F
  map_add' F₁ F₂ := by
    have hF₁ : MemLp (F₁ : ℂ → ℂ) 2 volume := Lp.memLp F₁
    have hF₂ : MemLp (F₂ : ℂ → ℂ) 2 volume := Lp.memLp F₂
    apply Lp.ext
    have hadd : (↑(F₁ + F₂) : ℂ → ℂ) =ᵐ[volume] (F₁ : ℂ → ℂ) + (F₂ : ℂ → ℂ) :=
      Lp.coeFn_add F₁ F₂
    have hL : (convToLp g hg (F₁ + F₂) : ℂ → ℂ)
        =ᵐ[volume] MeasureTheory.convolution g (↑(F₁ + F₂))
          (ContinuousLinearMap.mul ℂ ℂ) volume :=
      MemLp.coeFn_toLp _
    have hR : ((convToLp g hg F₁ + convToLp g hg F₂ : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
        =ᵐ[volume]
          MeasureTheory.convolution g (F₁ : ℂ → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume
            + MeasureTheory.convolution g (F₂ : ℂ → ℂ)
              (ContinuousLinearMap.mul ℂ ℂ) volume := by
      filter_upwards [Lp.coeFn_add (convToLp g hg F₁) (convToLp g hg F₂),
        (MemLp.coeFn_toLp (memLp_convolution_two hg hF₁)),
        (MemLp.coeFn_toLp (memLp_convolution_two hg hF₂))] with x hx h1 h2
      rw [hx]
      simp only [Pi.add_apply, convToLp]
      rw [h1, h2]
    have hconveq : MeasureTheory.convolution g (↑(F₁ + F₂))
          (ContinuousLinearMap.mul ℂ ℂ) volume
        = MeasureTheory.convolution g ((F₁ : ℂ → ℂ) + (F₂ : ℂ → ℂ))
          (ContinuousLinearMap.mul ℂ ℂ) volume :=
      MeasureTheory.convolution_congr (L := ContinuousLinearMap.mul ℂ ℂ)
        (μ := (volume : Measure ℂ)) (Filter.EventuallyEq.refl _ g) hadd
    have hsplit := convolution_ae_add hg hF₁ hF₂
    rw [hconveq] at hL
    exact hL.trans (hsplit.trans hR.symm)
  map_smul' c F := by
    have hF : MemLp (F : ℂ → ℂ) 2 volume := Lp.memLp F
    apply Lp.ext
    simp only [RingHom.id_apply]
    have hL : (convToLp g hg (c • F) : ℂ → ℂ)
        =ᵐ[volume] MeasureTheory.convolution g (↑(c • F))
          (ContinuousLinearMap.mul ℂ ℂ) volume :=
      MemLp.coeFn_toLp _
    have hsmul : (↑(c • F) : ℂ → ℂ) =ᵐ[volume] c • (F : ℂ → ℂ) := Lp.coeFn_smul c F
    have hconveq : MeasureTheory.convolution g (↑(c • F))
          (ContinuousLinearMap.mul ℂ ℂ) volume
        = MeasureTheory.convolution g (c • (F : ℂ → ℂ))
          (ContinuousLinearMap.mul ℂ ℂ) volume :=
      MeasureTheory.convolution_congr (L := ContinuousLinearMap.mul ℂ ℂ)
        (μ := (volume : Measure ℂ)) (Filter.EventuallyEq.refl _ g) hsmul
    have hpull : MeasureTheory.convolution g (c • (F : ℂ → ℂ))
          (ContinuousLinearMap.mul ℂ ℂ) volume
        = c • MeasureTheory.convolution g (F : ℂ → ℂ)
          (ContinuousLinearMap.mul ℂ ℂ) volume :=
      MeasureTheory.convolution_smul
    have hR : ((c • convToLp g hg F : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
        =ᵐ[volume] c • MeasureTheory.convolution g (F : ℂ → ℂ)
          (ContinuousLinearMap.mul ℂ ℂ) volume := by
      filter_upwards [Lp.coeFn_smul c (convToLp g hg F),
        MemLp.coeFn_toLp (memLp_convolution_two hg hF)] with x hx h1
      rw [hx]
      simp only [Pi.smul_apply, convToLp]
      rw [h1]
    rw [hconveq, hpull] at hL
    exact hL.trans hR.symm

/-- The operator "convolve by `g`" as a continuous linear self-map of `L²(ℂ)`,
for `g ∈ L¹`, with operator-norm bound `(eLpNorm g 1 volume).toReal` from Young's
inequality. This is the dyadic Cotlar–Stein operator `T_j = convCLM (ψ_j)`. -/
noncomputable def convCLM (g : ℂ → ℂ) (hg : MemLp g 1 volume) :
    (Lp ℂ 2 (volume : Measure ℂ)) →L[ℂ] (Lp ℂ 2 (volume : Measure ℂ)) :=
  LinearMap.mkContinuous (convLM g hg) (eLpNorm g 1 volume).toReal (by
    intro F
    have hF : MemLp (F : ℂ → ℂ) 2 volume := Lp.memLp F
    change ‖convToLp g hg F‖ ≤ _
    rw [convToLp, Lp.norm_toLp, Lp.norm_def]
    have hYoung := eLpNorm_convolution_le hg hF
    rw [← ENNReal.toReal_mul]
    exact (ENNReal.toReal_le_toReal (memLp_convolution_two hg hF).2.ne
      (ENNReal.mul_ne_top hg.2.ne (Lp.eLpNorm_ne_top F))).mpr hYoung)

/-- The action of `convCLM g hg` on a representative: `(convCLM g hg F) =ᵐ g ⋆ F`. -/
theorem convCLM_apply_coeFn (g : ℂ → ℂ) (hg : MemLp g 1 volume)
    (F : Lp ℂ 2 (volume : Measure ℂ)) :
    (convCLM g hg F : ℂ → ℂ)
      =ᵐ[volume] MeasureTheory.convolution g (F : ℂ → ℂ)
        (ContinuousLinearMap.mul ℂ ℂ) volume :=
  MemLp.coeFn_toLp (memLp_convolution_two hg (Lp.memLp F))

/-- The operator-norm bound from Young's inequality:
`‖convCLM g hg‖ ≤ (eLpNorm g 1 volume).toReal`. -/
theorem convCLM_opNorm_le (g : ℂ → ℂ) (hg : MemLp g 1 volume) :
    ‖convCLM g hg‖ ≤ (eLpNorm g 1 volume).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

/-- The **adjoint kernel** `g̃ u = conj (g (-u))`. The Hilbert adjoint on `L²` of
convolution-by-`g` is convolution-by-`g̃` (`adjoint_convCLM`). -/
noncomputable def convKernelStar (g : ℂ → ℂ) : ℂ → ℂ := fun u => starRingEnd ℂ (g (-u))

/-- The `L¹` norm of `g̃ u = conj (g (-u))` equals that of `g`: conjugation preserves
the pointwise norm and `u ↦ -u` is measure preserving. -/
theorem eLpNorm_convKernelStar (g : ℂ → ℂ) (hg : AEStronglyMeasurable g volume) :
    eLpNorm (convKernelStar g) 1 volume = eLpNorm g 1 volume := by
  have hconj : eLpNorm (convKernelStar g) 1 volume = eLpNorm (fun u => g (-u)) 1 volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards with u
    exact Complex.norm_conj (g (-u))
  rw [hconj, show (fun u : ℂ => g (-u)) = g ∘ (fun u : ℂ => -u) from rfl]
  exact eLpNorm_comp_measurePreserving hg (Measure.measurePreserving_neg volume)

/-- `g̃ ∈ L¹` whenever `g ∈ L¹`. -/
theorem memLp_convKernelStar {g : ℂ → ℂ} (hg : MemLp g 1 volume) :
    MemLp (convKernelStar g) 1 volume := by
  refine ⟨?_, ?_⟩
  · apply Complex.continuous_conj.comp_aestronglyMeasurable
    exact hg.1.comp_quasiMeasurePreserving
      (Measure.measurePreserving_neg volume).quasiMeasurePreserving
  · rw [eLpNorm_convKernelStar g hg.1]
    exact hg.2

/-- `(∫ ‖f‖²)^(1/2)` equals `(‖f‖₂).toReal` for `f ∈ L²`. -/
theorem rpow_half_eq (f : ℂ → ℂ) (hf : MemLp f 2 volume) :
    (∫ a, ‖f a‖ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) = (eLpNorm f 2 volume).toReal := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hf]
  rw [ENNReal.toReal_ofReal (by positivity)]; norm_num

/-- Uniform Cauchy–Schwarz bound (translate on the left factor):
`∫ x, ‖F (x-t)‖·‖H x‖ ≤ ‖F‖₂·‖H‖₂`, independent of `t`. -/
theorem cs_unif (F H : ℂ → ℂ) (hF : MemLp F 2 volume) (hH : MemLp H 2 volume) (t : ℂ) :
    ∫ x, ‖F (x - t)‖ * ‖H x‖ ∂volume
      ≤ (eLpNorm F 2 volume).toReal * (eLpNorm H 2 volume).toReal := by
  have hFt : MemLp (fun x => F (x - t)) 2 volume :=
    hF.comp_measurePreserving (measurePreserving_sub_right volume t)
  have heq : eLpNorm (fun x => F (x - t)) 2 volume = eLpNorm F 2 volume :=
    eLpNorm_comp_measurePreserving (p := 2) hF.1 (measurePreserving_sub_right volume t)
  have hCS := integral_mul_norm_le_Lp_mul_Lq (μ := volume)
    (p := 2) (q := 2) (Real.HolderConjugate.two_two) (by simpa using hFt) (by simpa using hH)
  refine hCS.trans ?_
  rw [rpow_half_eq _ hFt, rpow_half_eq _ hH, heq]

/-- Uniform Cauchy–Schwarz bound (translate on the right factor):
`∫ y, ‖F y‖·‖H (y-t)‖ ≤ ‖F‖₂·‖H‖₂`, independent of `t`. -/
theorem cs_unif2 (F H : ℂ → ℂ) (hF : MemLp F 2 volume) (hH : MemLp H 2 volume) (t : ℂ) :
    ∫ y, ‖F y‖ * ‖H (y - t)‖ ∂volume
      ≤ (eLpNorm F 2 volume).toReal * (eLpNorm H 2 volume).toReal := by
  have hHt : MemLp (fun y => H (y - t)) 2 volume :=
    hH.comp_measurePreserving (measurePreserving_sub_right volume t)
  have heq : eLpNorm (fun y => H (y - t)) 2 volume = eLpNorm H 2 volume :=
    eLpNorm_comp_measurePreserving (p := 2) hH.1 (measurePreserving_sub_right volume t)
  have hCS := integral_mul_norm_le_Lp_mul_Lq (μ := volume)
    (p := 2) (q := 2) (Real.HolderConjugate.two_two) (by simpa using hF) (by simpa using hHt)
  refine hCS.trans ?_
  rw [rpow_half_eq _ hF, rpow_half_eq _ hHt, heq]

private theorem qmp_sub21 : Measure.QuasiMeasurePreserving (fun p : ℂ × ℂ => p.2 - p.1)
    (volume.prod volume) volume := by
  have h1 : Measure.QuasiMeasurePreserving (fun p : ℂ × ℂ => p.1 - p.2)
      (volume.prod volume) volume := quasiMeasurePreserving_sub_of_right_invariant volume volume
  simpa [Function.comp_def, Prod.swap] using
    h1.comp (Measure.measurePreserving_swap).quasiMeasurePreserving

private theorem qmp_sub12 : Measure.QuasiMeasurePreserving (fun p : ℂ × ℂ => p.1 - p.2)
    (volume.prod volume) volume := quasiMeasurePreserving_sub_of_right_invariant volume volume

/-- Joint integrability of the LHS bilinear integrand
`(t, x) ↦ conj(g t)·(conj(F(x-t))·H x)` (coordinates `p.1 = t`, `p.2 = x`). -/
theorem joint_int (g F H : ℂ → ℂ) (hg : MemLp g 1 volume)
    (hF : MemLp F 2 volume) (hH : MemLp H 2 volume) :
    Integrable (fun p : ℂ × ℂ =>
      starRingEnd ℂ (g p.1) * (starRingEnd ℂ (F (p.2 - p.1)) * H p.2))
      (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℂ × ℂ => starRingEnd ℂ (g p.1) * (starRingEnd ℂ (F (p.2 - p.1)) * H p.2))
      (volume.prod volume) := by
    apply AEStronglyMeasurable.mul
    · exact (Complex.continuous_conj.comp_aestronglyMeasurable hg.1).comp_fst
    · apply AEStronglyMeasurable.mul
      · exact Complex.continuous_conj.comp_aestronglyMeasurable
          (hF.1.comp_quasiMeasurePreserving qmp_sub21)
      · exact hH.1.comp_snd
  rw [integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards with t
    have hFt : MemLp (fun x => F (x - t)) 2 volume :=
      hF.comp_measurePreserving (measurePreserving_sub_right volume t)
    have hconjFt : MemLp (fun x => starRingEnd ℂ (F (x - t))) 2 volume := by
      have heqn : eLpNorm (fun x => starRingEnd ℂ (F (x - t))) 2 volume
          = eLpNorm (fun x => F (x - t)) 2 volume := by
        apply eLpNorm_congr_norm_ae; filter_upwards with x; exact Complex.norm_conj _
      exact ⟨Complex.continuous_conj.comp_aestronglyMeasurable hFt.1, by rw [heqn]; exact hFt.2⟩
    exact (MemLp.integrable_mul (p := 2) (q := 2) hconjFt hH).const_mul (starRingEnd ℂ (g t))
  · have hgn : Integrable (fun a => ‖g a‖) volume := (memLp_one_iff_integrable.mp hg).norm
    have hdom : Integrable
        (fun t => ‖g t‖ * ((eLpNorm F 2 volume).toReal * (eLpNorm H 2 volume).toReal)) volume :=
      Integrable.mul_const hgn _
    refine Integrable.mono' hdom hmeas.norm.integral_prod_right' ?_
    filter_upwards with t
    have hnn : (0 : ℝ) ≤ ∫ x, ‖starRingEnd ℂ (g t) * (starRingEnd ℂ (F (x - t)) * H x)‖ ∂volume :=
      integral_nonneg (fun x => norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    have heq2 : (fun x => ‖starRingEnd ℂ (g t) * (starRingEnd ℂ (F (x - t)) * H x)‖)
        = (fun x => ‖g t‖ * (‖F (x - t)‖ * ‖H x‖)) := by
      funext x; rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    rw [heq2, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (cs_unif F H hF hH t) (norm_nonneg _)

/-- Joint integrability of the RHS bilinear integrand
`(y, t) ↦ conj(F y)·(conj(g(-t))·H(y-t))` (coordinates `p.1 = y`, `p.2 = t`). -/
theorem joint_int2 (g F H : ℂ → ℂ) (hg : MemLp g 1 volume)
    (hF : MemLp F 2 volume) (hH : MemLp H 2 volume) :
    Integrable (fun p : ℂ × ℂ =>
      starRingEnd ℂ (F p.1) * (starRingEnd ℂ (g (-p.2)) * H (p.1 - p.2)))
      (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℂ × ℂ => starRingEnd ℂ (F p.1) * (starRingEnd ℂ (g (-p.2)) * H (p.1 - p.2)))
      (volume.prod volume) := by
    apply AEStronglyMeasurable.mul
    · exact (Complex.continuous_conj.comp_aestronglyMeasurable hF.1).comp_fst
    · apply AEStronglyMeasurable.mul
      · apply Complex.continuous_conj.comp_aestronglyMeasurable
        exact (hg.1.comp_quasiMeasurePreserving
          ((Measure.measurePreserving_neg volume).quasiMeasurePreserving)).comp_snd
      · exact hH.1.comp_quasiMeasurePreserving qmp_sub12
  rw [integrable_prod_iff' hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards with t
    have hHt : MemLp (fun y => H (y - t)) 2 volume :=
      hH.comp_measurePreserving (measurePreserving_sub_right volume t)
    have hconjF : MemLp (fun y => starRingEnd ℂ (F y)) 2 volume := by
      have heqn : eLpNorm (fun y => starRingEnd ℂ (F y)) 2 volume = eLpNorm F 2 volume := by
        apply eLpNorm_congr_norm_ae; filter_upwards with y; exact Complex.norm_conj _
      exact ⟨Complex.continuous_conj.comp_aestronglyMeasurable hF.1, by rw [heqn]; exact hF.2⟩
    have hprod : Integrable (fun y => starRingEnd ℂ (F y) * H (y - t)) volume :=
      MemLp.integrable_mul (p := 2) (q := 2) hconjF hHt
    have hc := hprod.const_mul (starRingEnd ℂ (g (-t)))
    apply hc.congr; filter_upwards with y; ring
  · have hgn : Integrable (fun a => ‖g (-a)‖) volume :=
      ((memLp_one_iff_integrable.mp hg).comp_neg).norm
    have hdom : Integrable
        (fun t => ‖g (-t)‖ * ((eLpNorm F 2 volume).toReal * (eLpNorm H 2 volume).toReal)) volume :=
      Integrable.mul_const hgn _
    have hmeasL : AEStronglyMeasurable
        (fun t => ∫ y, ‖starRingEnd ℂ (F y) * (starRingEnd ℂ (g (-t)) * H (y - t))‖ ∂volume)
        volume := by
      have hsw : AEStronglyMeasurable
          (fun p : ℂ × ℂ => ‖starRingEnd ℂ (F p.2) * (starRingEnd ℂ (g (-p.1)) * H (p.2 - p.1))‖)
          (volume.prod volume) := by
        have := hmeas.norm.comp_measurePreserving
          (Measure.measurePreserving_swap (μ := (volume : Measure ℂ)) (ν := volume))
        simpa [Function.comp_def, Prod.swap] using this
      exact hsw.integral_prod_right'
    refine Integrable.mono' hdom hmeasL ?_
    filter_upwards with t
    have hnn : (0 : ℝ)
        ≤ ∫ y, ‖starRingEnd ℂ (F y) * (starRingEnd ℂ (g (-t)) * H (y - t))‖ ∂volume :=
      integral_nonneg (fun y => norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    have heq2 : (fun y => ‖starRingEnd ℂ (F y) * (starRingEnd ℂ (g (-t)) * H (y - t))‖)
        = (fun y => ‖g (-t)‖ * (‖F y‖ * ‖H (y - t)‖)) := by
      funext y; rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]; ring
    rw [heq2, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (cs_unif2 F H hF hH t) (norm_nonneg _)

/-- The left inner product `⟪g ⋆ F, H⟫` as an iterated integral. -/
theorem lhs_eq (g : ℂ → ℂ) (hg : MemLp g 1 volume)
    (F H : Lp ℂ 2 (volume : Measure ℂ)) :
    (inner ℂ (convCLM g hg F) H : ℂ)
      = ∫ x, ∫ t, starRingEnd ℂ (g t) *
          (starRingEnd ℂ ((F : ℂ → ℂ) (x - t)) * (H : ℂ → ℂ) x) ∂volume ∂volume := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [convCLM_apply_coeFn g hg F] with x hx
  rw [RCLike.inner_apply', hx, MeasureTheory.convolution_mul]
  calc (starRingEnd ℂ) (∫ (t : ℂ), g t * (F : ℂ → ℂ) (x - t)) * (H : ℂ → ℂ) x
      = (∫ t, starRingEnd ℂ (g t) * starRingEnd ℂ ((F : ℂ → ℂ) (x - t)) ∂volume)
          * (H : ℂ → ℂ) x := by
        congr 1
        rw [show (starRingEnd ℂ) (∫ (t : ℂ), g t * (F : ℂ → ℂ) (x - t))
            = ∫ t, (starRingEnd ℂ) (g t * (F : ℂ → ℂ) (x - t)) from (integral_conj).symm]
        apply integral_congr_ae; filter_upwards with t; rw [map_mul]
    _ = ∫ t, (starRingEnd ℂ (g t) * starRingEnd ℂ ((F : ℂ → ℂ) (x - t))) * (H : ℂ → ℂ) x
          ∂volume :=
        (integral_mul_const ((H : ℂ → ℂ) x) _).symm
    _ = ∫ t, starRingEnd ℂ (g t)
          * (starRingEnd ℂ ((F : ℂ → ℂ) (x - t)) * (H : ℂ → ℂ) x) ∂volume := by
        apply integral_congr_ae; filter_upwards with t; ring

/-- The right inner product `⟪F, g̃ ⋆ H⟫` as an iterated integral. -/
theorem rhs_eq (g : ℂ → ℂ) (hg : MemLp g 1 volume)
    (F H : Lp ℂ 2 (volume : Measure ℂ)) :
    (inner ℂ F (convCLM (convKernelStar g) (memLp_convKernelStar hg) H) : ℂ)
      = ∫ y, ∫ t, starRingEnd ℂ ((F : ℂ → ℂ) y) *
          (starRingEnd ℂ (g (-t)) * (H : ℂ → ℂ) (y - t)) ∂volume ∂volume := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [convCLM_apply_coeFn (convKernelStar g) (memLp_convKernelStar hg) H] with y hy
  rw [RCLike.inner_apply', hy, MeasureTheory.convolution_mul]
  have hstep : (∫ (t : ℂ), convKernelStar g t * (H : ℂ → ℂ) (y - t) ∂volume)
      = ∫ t, starRingEnd ℂ (g (-t)) * (H : ℂ → ℂ) (y - t) ∂volume := by
    apply integral_congr_ae; filter_upwards with t; simp only [convKernelStar]
  rw [hstep]
  exact (integral_const_mul ((starRingEnd ℂ) ((F : ℂ → ℂ) y)) _).symm

/-- `D_L` after Fubini (swap `x ↔ t`) and the substitution `x ↦ x + t`. -/
theorem dL_eq (g F H : ℂ → ℂ) (hg : MemLp g 1 volume)
    (hF : MemLp F 2 volume) (hH : MemLp H 2 volume) :
    (∫ x, ∫ t, starRingEnd ℂ (g t) * (starRingEnd ℂ (F (x - t)) * H x) ∂volume ∂volume)
      = ∫ t, ∫ x, starRingEnd ℂ (g t) * (starRingEnd ℂ (F x) * H (x + t)) ∂volume ∂volume := by
  have hLint : Integrable (Function.uncurry
      (fun x t => starRingEnd ℂ (g t) * (starRingEnd ℂ (F (x - t)) * H x)))
      (volume.prod volume) := by
    have := (joint_int g F H hg hF hH).swap
    simpa [Function.uncurry_def, Function.comp_def, Prod.swap] using this
  rw [integral_integral_swap hLint]
  apply integral_congr_ae; filter_upwards with t
  rw [← integral_add_right_eq_self
      (fun x => starRingEnd ℂ (g t) * (starRingEnd ℂ (F (x - t)) * H x)) t]
  apply integral_congr_ae; filter_upwards with x
  rw [show x + t - t = x by ring]

/-- `D_R` after Fubini (swap `y ↔ t`) and the substitution `t ↦ -t`. -/
theorem dR_eq (g F H : ℂ → ℂ) (hg : MemLp g 1 volume)
    (hF : MemLp F 2 volume) (hH : MemLp H 2 volume) :
    (∫ y, ∫ t, starRingEnd ℂ (F y) * (starRingEnd ℂ (g (-t)) * H (y - t)) ∂volume ∂volume)
      = ∫ t, ∫ x, starRingEnd ℂ (g t) * (starRingEnd ℂ (F x) * H (x + t)) ∂volume ∂volume := by
  have hRint : Integrable (Function.uncurry
      (fun y t => starRingEnd ℂ (F y) * (starRingEnd ℂ (g (-t)) * H (y - t))))
      (volume.prod volume) := by
    simpa [Function.uncurry_def] using (joint_int2 g F H hg hF hH)
  rw [integral_integral_swap hRint]
  rw [← integral_neg_eq_self
      (fun t => ∫ y, starRingEnd ℂ (F y) * (starRingEnd ℂ (g (-t)) * H (y - t)) ∂volume)]
  apply integral_congr_ae; filter_upwards with t
  apply integral_congr_ae; filter_upwards with y
  rw [neg_neg, sub_neg_eq_add]; ring

/-- **The Hilbert adjoint of convolution-by-`g` is convolution-by-`g̃`,** where
`g̃ u = conj (g (-u))`. This identifies `(T_i)* T_j` as convolution by
`ψ̃_i ⋆ ψ_j`, the kernel whose `L¹` cancellation drives almost-orthogonality. -/
theorem adjoint_convCLM (g : ℂ → ℂ) (hg : MemLp g 1 volume) :
    ContinuousLinearMap.adjoint (convCLM g hg)
      = convCLM (convKernelStar g) (memLp_convKernelStar hg) := by
  have key : ∀ (F H : Lp ℂ 2 (volume : Measure ℂ)),
      inner ℂ (convCLM g hg F) H
        = inner ℂ F (convCLM (convKernelStar g) (memLp_convKernelStar hg) H) := by
    intro F H
    rw [lhs_eq g hg F H, rhs_eq g hg F H,
      (dL_eq g (F : ℂ → ℂ) (H : ℂ → ℂ) hg (Lp.memLp F) (Lp.memLp H)).trans
        (dR_eq g (F : ℂ → ℂ) (H : ℂ → ℂ) hg (Lp.memLp F) (Lp.memLp H)).symm]
  have hA : convCLM g hg
      = ContinuousLinearMap.adjoint (convCLM (convKernelStar g) (memLp_convKernelStar hg)) :=
    (ContinuousLinearMap.eq_adjoint_iff _ _).mpr key
  rw [← ContinuousLinearMap.adjoint_adjoint
        (convCLM (convKernelStar g) (memLp_convKernelStar hg))]
  exact congrArg ContinuousLinearMap.adjoint hA

/-! ### Dyadic almost-orthogonality assembly (Cotlar–Stein) -/

/-- The coercion `u ↦ (‖a u‖ : ℂ)` of a pointwise norm preserves membership in `Lᵖ`. -/
lemma memLp_coe_norm {a : ℂ → ℂ} {p : ℝ≥0∞} (ha : MemLp a p volume) :
    MemLp (fun u => (‖a u‖ : ℂ)) p volume := by
  refine ⟨Complex.continuous_ofReal.comp_aestronglyMeasurable ha.1.norm, ?_⟩
  have : eLpNorm (fun u => ((‖a u‖ : ℝ) : ℂ)) p volume = eLpNorm a p volume := by
    apply eLpNorm_congr_norm_ae; filter_upwards with u; simp
  rw [this]; exact ha.2

/-- The real-valued convolution `‖b‖ ⋆ ‖F‖` exists at `x` whenever the complex one does. -/
lemma convExists_norm_of_complex {b F : ℂ → ℂ} {x : ℂ}
    (h : ConvolutionExistsAt b F x (ContinuousLinearMap.mul ℂ ℂ) volume) :
    ConvolutionExistsAt (fun u => ‖b u‖) (fun u => ‖F u‖) x
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
  have hnorm : Integrable (fun t => ‖(ContinuousLinearMap.mul ℂ ℂ) (b t) (F (x - t))‖) volume :=
    h.norm
  simp only [ContinuousLinearMap.mul_apply', norm_mul] at hnorm
  change Integrable (fun t => (ContinuousLinearMap.mul ℝ ℝ) (‖b t‖) (‖F (x - t)‖)) volume
  simpa only [ContinuousLinearMap.mul_apply'] using hnorm

/-- The ℂ-convolution of the coerced norms equals the coercion of the real convolution. -/
lemma conv_coe_norm_eq {b F : ℂ → ℂ} (y : ℂ) :
    MeasureTheory.convolution (fun u => (‖b u‖:ℂ)) (fun u => (‖F u‖:ℂ))
        (ContinuousLinearMap.mul ℂ ℂ) volume y
      = ((MeasureTheory.convolution (fun u => ‖b u‖) (fun u => ‖F u‖)
          (ContinuousLinearMap.mul ℝ ℝ) volume y : ℝ) : ℂ) := by
  rw [MeasureTheory.convolution_mul, MeasureTheory.convolution_mul]
  simp only [← Complex.ofReal_mul]; exact integral_ofReal

/-- The real convolution of two pointwise norms is nonnegative. -/
lemma conv_norm_nonneg {b F : ℂ → ℂ} (y : ℂ) :
    0 ≤ MeasureTheory.convolution (fun u => ‖b u‖) (fun u => ‖F u‖)
        (ContinuousLinearMap.mul ℝ ℝ) volume y := by
  rw [MeasureTheory.convolution_mul]; apply integral_nonneg; intro t; positivity

set_option maxHeartbeats 400000 in
-- The proof discharges the three integrability side conditions of `convolution_assoc`
-- through the `L¹/L²` substrate, which involves several nested `MemLp`/`Integrable`
-- elaborations that exceed the default heartbeat budget.
/-- **Almost-everywhere associativity of convolution** for two `L¹` kernels and an `L²`
function: `(a ⋆ b) ⋆ F =ᵐ a ⋆ (b ⋆ F)`. Discharges the three integrability conditions of
`MeasureTheory.convolution_assoc` via the `L¹/L²` substrate. -/
lemma ae_convolution_assoc {a b : ℂ → ℂ} (ha : MemLp a 1 volume) (hb : MemLp b 1 volume)
    {F : ℂ → ℂ} (hF : MemLp F 2 volume) :
    MeasureTheory.convolution (MeasureTheory.convolution a b (ContinuousLinearMap.mul ℂ ℂ) volume)
        F (ContinuousLinearMap.mul ℂ ℂ) volume
      =ᵐ[volume]
        MeasureTheory.convolution a
          (MeasureTheory.convolution b F (ContinuousLinearMap.mul ℂ ℂ) volume)
          (ContinuousLinearMap.mul ℂ ℂ) volume := by
  have hia : Integrable a volume := (memLp_one_iff_integrable).mp ha
  have hib : Integrable b volume := (memLp_one_iff_integrable).mp hb
  have hfg : ∀ᵐ y ∂volume, ConvolutionExistsAt a b y (ContinuousLinearMap.mul ℂ ℂ) volume :=
    hia.ae_convolution_exists _ hib
  have hgk : ∀ᵐ x ∂volume, ConvolutionExistsAt (fun u => ‖b u‖) (fun u => ‖F u‖) x
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
    filter_upwards [ae_convolutionExistsAt hb hF] with x hx
    exact convExists_norm_of_complex hx
  have hA : MemLp (fun u => (‖a u‖:ℂ)) 1 volume := memLp_coe_norm ha
  have hB : MemLp (fun u => (‖b u‖:ℂ)) 1 volume := memLp_coe_norm hb
  have hΦ : MemLp (fun u => (‖F u‖:ℂ)) 2 volume := memLp_coe_norm hF
  have hBΦ : MemLp (MeasureTheory.convolution (fun u => (‖b u‖:ℂ)) (fun u => (‖F u‖:ℂ))
      (ContinuousLinearMap.mul ℂ ℂ) volume) 2 volume := memLp_convolution_two hB hΦ
  have hfgk_C : ∀ᵐ x ∂volume, ConvolutionExistsAt (fun u => (‖a u‖:ℂ))
      (MeasureTheory.convolution (fun u => (‖b u‖:ℂ)) (fun u => (‖F u‖:ℂ))
          (ContinuousLinearMap.mul ℂ ℂ) volume) x (ContinuousLinearMap.mul ℂ ℂ) volume :=
    ae_convolutionExistsAt hA hBΦ
  have hfgk : ∀ᵐ x ∂volume, ConvolutionExistsAt (fun u => ‖a u‖)
      (MeasureTheory.convolution (fun u => ‖b u‖) (fun u => ‖F u‖)
          (ContinuousLinearMap.mul ℝ ℝ) volume) x (ContinuousLinearMap.mul ℝ ℝ) volume := by
    filter_upwards [hfgk_C] with x hx
    have hxn := hx.norm
    simp only [ContinuousLinearMap.mul_apply', norm_mul, Complex.norm_real,
      conv_coe_norm_eq] at hxn
    change Integrable (fun t => (ContinuousLinearMap.mul ℝ ℝ) (‖a t‖)
      (MeasureTheory.convolution (fun u => ‖b u‖) (fun u => ‖F u‖)
        (ContinuousLinearMap.mul ℝ ℝ) volume (x-t))) volume
    simp only [ContinuousLinearMap.mul_apply']
    refine hxn.congr ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_norm, Real.norm_eq_abs, abs_of_nonneg (conv_norm_nonneg _)]
  filter_upwards [hfgk] with x₀ hx_fgk
  exact MeasureTheory.convolution_assoc (ContinuousLinearMap.mul ℂ ℂ)
    (ContinuousLinearMap.mul ℂ ℂ) (ContinuousLinearMap.mul ℂ ℂ) (ContinuousLinearMap.mul ℂ ℂ)
    (fun x y z => by simp [mul_assoc]) ha.1 hb.1 hF.1 hfg hgk hx_fgk

/-- **`L¹ ⋆ L¹ ⊆ L¹`** (Young at exponent one): the convolution of two `L¹` functions is `L¹`. -/
lemma memLp_convolution_one {a b : ℂ → ℂ} (ha : MemLp a 1 volume) (hb : MemLp b 1 volume) :
    MemLp (MeasureTheory.convolution a b (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume := by
  have hia : Integrable a volume := (memLp_one_iff_integrable).mp ha
  have hib : Integrable b volume := (memLp_one_iff_integrable).mp hb
  exact (memLp_one_iff_integrable).mpr (hia.integrable_convolution _ hib)

/-- **Composition of convolution operators.** On `L²`, convolving by `a ∈ L¹` then by `b ∈ L¹`
equals convolving by `a ⋆ b`. -/
lemma convCLM_comp {a b : ℂ → ℂ} (ha : MemLp a 1 volume) (hb : MemLp b 1 volume) :
    (convCLM a ha) ∘L (convCLM b hb)
      = convCLM (MeasureTheory.convolution a b (ContinuousLinearMap.mul ℂ ℂ) volume)
          (memLp_convolution_one ha hb) := by
  apply ContinuousLinearMap.ext
  intro F
  apply Lp.ext
  have hF : MemLp (F : ℂ → ℂ) 2 volume := Lp.memLp F
  have hL1 : ((convCLM a ha) ((convCLM b hb) F) : ℂ → ℂ)
      =ᵐ[volume] MeasureTheory.convolution a (((convCLM b hb) F : ℂ → ℂ))
        (ContinuousLinearMap.mul ℂ ℂ) volume :=
    convCLM_apply_coeFn a ha _
  have hbF : ((convCLM b hb) F : ℂ → ℂ)
      =ᵐ[volume] MeasureTheory.convolution b (F : ℂ → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume :=
    convCLM_apply_coeFn b hb F
  have hL2 : MeasureTheory.convolution a (((convCLM b hb) F : ℂ → ℂ))
        (ContinuousLinearMap.mul ℂ ℂ) volume
      = MeasureTheory.convolution a
        (MeasureTheory.convolution b (F : ℂ → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume)
        (ContinuousLinearMap.mul ℂ ℂ) volume :=
    MeasureTheory.convolution_congr (L := ContinuousLinearMap.mul ℂ ℂ)
      (Filter.EventuallyEq.refl _ a) hbF
  have hR1 : ((convCLM (MeasureTheory.convolution a b (ContinuousLinearMap.mul ℂ ℂ) volume)
        (memLp_convolution_one ha hb) F) : ℂ → ℂ)
      =ᵐ[volume] MeasureTheory.convolution
        (MeasureTheory.convolution a b (ContinuousLinearMap.mul ℂ ℂ) volume) (F : ℂ → ℂ)
        (ContinuousLinearMap.mul ℂ ℂ) volume :=
    convCLM_apply_coeFn _ _ F
  have hLHS : ((((convCLM a ha) ∘L (convCLM b hb)) F) : ℂ → ℂ)
      =ᵐ[volume] MeasureTheory.convolution a
        (MeasureTheory.convolution b (F : ℂ → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume)
        (ContinuousLinearMap.mul ℂ ℂ) volume :=
    (show ((((convCLM a ha) ∘L (convCLM b hb)) F) : ℂ → ℂ)
        =ᵐ[volume] MeasureTheory.convolution a (((convCLM b hb) F : ℂ → ℂ))
          (ContinuousLinearMap.mul ℂ ℂ) volume from hL1).trans (hL2 ▸ Filter.EventuallyEq.rfl)
  refine hLHS.trans ?_
  exact (ae_convolution_assoc ha hb hF).symm.trans hR1.symm

/-- **Young's convolution inequality `L¹ ⋆ L¹ → L¹`.** For `g, f ∈ L¹(ℂ)`,
`‖g ⋆ f‖₁ ≤ ‖g‖₁ ‖f‖₁`. Proved via Tonelli and translation invariance. -/
lemma eLpNorm_convolution_one_le {g f : ℂ → ℂ}
    (hg : MemLp g 1 volume) (hf : MemLp f 1 volume) :
    eLpNorm (MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume
      ≤ eLpNorm g 1 volume * eLpNorm f 1 volume := by
  have hgm : AEMeasurable (fun t => ‖g t‖ₑ) volume := hg.1.enorm
  have hfm : AEStronglyMeasurable f volume := hf.1
  have hpt : ∀ x, ‖MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume x‖ₑ
      ≤ ∫⁻ t, ‖g t‖ₑ * ‖f (x - t)‖ₑ ∂volume := by
    intro x
    rw [MeasureTheory.convolution_mul]
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    apply lintegral_mono
    intro t
    simp only [enorm_mul, le_refl]
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hmono :
      (∫⁻ x, ‖MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume x‖ₑ ∂volume)
        ≤ ∫⁻ x, (∫⁻ t, ‖g t‖ₑ * ‖f (x - t)‖ₑ ∂volume) ∂volume := by
    apply lintegral_mono
    exact hpt
  refine le_trans hmono ?_
  have hGmeas : AEMeasurable (Function.uncurry fun x t => ‖g t‖ₑ * ‖f (x - t)‖ₑ)
      (volume.prod volume) := by
    apply AEMeasurable.fun_mul
    · exact hgm.comp_snd
    · have hsub : AEStronglyMeasurable (fun p : ℂ × ℂ => f (p.1 - p.2)) (volume.prod volume) :=
        hfm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant volume volume)
      exact hsub.enorm
  rw [lintegral_lintegral_swap hGmeas]
  have hinner : ∀ t, (∫⁻ x, ‖g t‖ₑ * ‖f (x - t)‖ₑ ∂volume) = ‖g t‖ₑ * eLpNorm f 1 volume := by
    intro t
    rw [lintegral_const_mul'' _ (by
      have hsub : AEStronglyMeasurable (fun x : ℂ => f (x - t)) volume :=
        hfm.comp_quasiMeasurePreserving
          (measurePreserving_sub_right volume t).quasiMeasurePreserving
      exact hsub.enorm)]
    have htrans : eLpNorm (fun x => f (x - t)) 1 volume = eLpNorm f 1 volume :=
      eLpNorm_comp_measurePreserving hfm (measurePreserving_sub_right volume t)
    rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm] at htrans
    rw [eLpNorm_one_eq_lintegral_enorm]
    rw [htrans]
  rw [lintegral_congr hinner, lintegral_mul_const'' _ hgm, ← eLpNorm_one_eq_lintegral_enorm]

/-- **Trivial Young `L¹` bound for the cross-convolution.** Both `ψ̃_i ⋆ ψ_j` and
`ψ_i ⋆ ψ̃_j` have `L¹` mass at most `(2π log 2)²`, the product of the (equal) `L¹` masses of
the two factors. The universal, no-cancellation bound. -/
lemma eLpNorm_cross_le_sq (r : ℝ) (hr : 0 < r) (i j : ℕ) :
    eLpNorm (MeasureTheory.convolution (convKernelStar (dyadicBeurling r i)) (dyadicBeurling r j)
        (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume
        ≤ ENNReal.ofReal ((2 * Real.pi * Real.log 2) ^ 2)
      ∧ eLpNorm (MeasureTheory.convolution (dyadicBeurling r i)
          (convKernelStar (dyadicBeurling r j))
          (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume
        ≤ ENNReal.ofReal ((2 * Real.pi * Real.log 2) ^ 2) := by
  have hψi := memLp_dyadicBeurling r hr i
  have hψj := memLp_dyadicBeurling r hr j
  have hgi := memLp_convKernelStar hψi
  have hgj := memLp_convKernelStar hψj
  have hni : eLpNorm (convKernelStar (dyadicBeurling r i)) 1 volume
      = ENNReal.ofReal (2 * Real.pi * Real.log 2) := by
    rw [eLpNorm_convKernelStar _ hψi.1, eLpNorm_dyadicBeurling r hr i]
  have hnj : eLpNorm (convKernelStar (dyadicBeurling r j)) 1 volume
      = ENNReal.ofReal (2 * Real.pi * Real.log 2) := by
    rw [eLpNorm_convKernelStar _ hψj.1, eLpNorm_dyadicBeurling r hr j]
  have hpos : (0:ℝ) ≤ 2 * Real.pi * Real.log 2 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    positivity
  refine ⟨?_, ?_⟩
  · refine (eLpNorm_convolution_one_le hgi hψj).trans ?_
    rw [hni, eLpNorm_dyadicBeurling r hr j, ← ENNReal.ofReal_mul hpos, ← sq]
  · refine (eLpNorm_convolution_one_le hψi hgj).trans ?_
    rw [hnj, eLpNorm_dyadicBeurling r hr i, ← ENNReal.ofReal_mul hpos, ← sq]

/-- The numeric comparison powering the small-separation case: `(2π log 2)² ≤ 4096·(1/2)^d`
whenever `d ≤ 7`. Indeed `(2π log 2)² ≤ 64` and `4096·(1/2)^7 = 32`, but `(2π log 2)² ≤ 32`
fails the trivial nlinarith bound, so we use the sharper `(2π log 2)² ≤ 64` only and require
`64 ≤ 4096·(1/2)^d`, i.e. `(1/2)^d ≥ 1/64`, i.e. `d ≤ 6`. We therefore split at `d ≤ 6`. -/
lemma sq_logmass_le (d : ℕ) (hd : d ≤ 6) :
    (2 * Real.pi * Real.log 2) ^ 2 ≤ 4096 * ((1:ℝ)/2) ^ d := by
  have hπ : Real.pi ≤ 4 := Real.pi_le_four
  have hlog2 : Real.log 2 ≤ 1 := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply le_of_lt
    apply Real.log_lt_log (by norm_num)
    have := Real.add_one_lt_exp (x := 1) (by norm_num)
    linarith
  have hπpos : (0:ℝ) ≤ Real.pi := Real.pi_pos.le
  have hlogpos : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hLHS : (2 * Real.pi * Real.log 2) ^ 2 ≤ 64 := by
    have hbase : 2 * Real.pi * Real.log 2 ≤ 8 := by
      nlinarith [hπpos, hlogpos, hπ, hlog2]
    have hbase_nn : (0:ℝ) ≤ 2 * Real.pi * Real.log 2 :=
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hπpos) hlogpos
    nlinarith [hbase, hbase_nn]
  have hRHS : (64:ℝ) ≤ 4096 * ((1:ℝ)/2) ^ d := by
    have hmono : ((1:ℝ)/2) ^ 6 ≤ ((1:ℝ)/2) ^ d :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
    have heq : (4096:ℝ) * ((1:ℝ)/2) ^ 6 = 64 := by norm_num
    nlinarith [hmono]
  linarith

/-- The unit-circle parametrization `e θ = cos θ + i sin θ`. -/
noncomputable def eCirc (θ : ℝ) : ℂ := (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I

lemma eCirc_norm (θ : ℝ) : ‖eCirc θ‖ = 1 := by
  rw [eCirc, Complex.norm_add_mul_I,
    show Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 by rw [add_comm]; exact Real.sin_sq_add_cos_sq θ]
  simp

lemma eCirc_ne_zero (θ : ℝ) : eCirc θ ≠ 0 := by
  rw [← norm_ne_zero_iff, eCirc_norm]; norm_num

/-- `e θ · conj (e θ) = 1`, so `(e θ)⁻¹ = conj (e θ)`. -/
lemma eCirc_mul_conj (θ : ℝ) : eCirc θ * (starRingEnd ℂ) (eCirc θ) = 1 := by
  have h : ‖eCirc θ‖ ^ 2 = 1 := by rw [eCirc_norm]; norm_num
  rw [Complex.mul_conj]
  rw [← Complex.normSq_eq_norm_sq] at h
  rw [show ((Complex.normSq (eCirc θ) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) by rw [h]]; norm_num

lemma eCirc_inv (θ : ℝ) : (eCirc θ)⁻¹ = (starRingEnd ℂ) (eCirc θ) :=
  inv_eq_of_mul_eq_one_right (eCirc_mul_conj θ)

/-- The derivative of `e θ = cos θ + sin θ I` is `I · e θ`. -/
lemma eCirc_hasDerivAt (θ : ℝ) : HasDerivAt eCirc (I * eCirc θ) θ := by
  have hcos : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ)) ((-Real.sin θ : ℝ) : ℂ) θ :=
    (Real.hasDerivAt_cos θ).ofReal_comp
  have hsin : HasDerivAt (fun s : ℝ => (Real.sin s : ℂ)) ((Real.cos θ : ℝ) : ℂ) θ :=
    (Real.hasDerivAt_sin θ).ofReal_comp
  have hd : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ) + (Real.sin s : ℂ) * I)
      ((((-Real.sin θ : ℝ)) : ℂ) + (((Real.cos θ : ℝ)) : ℂ) * I) θ :=
    hcos.add (hsin.mul_const I)
  have hev : (((-Real.sin θ : ℝ)) : ℂ) + (((Real.cos θ : ℝ)) : ℂ) * I = I * eCirc θ := by
    rw [eCirc, Complex.ofReal_neg]
    linear_combination (-(Real.sin θ : ℂ)) * Complex.I_mul_I
  have : HasDerivAt eCirc ((((-Real.sin θ : ℝ)) : ℂ) + (((Real.cos θ : ℝ)) : ℂ) * I) θ := hd
  rwa [hev] at this

/-- The conjugate has derivative `-I · conj (e θ)`. -/
lemma eCirc_conj_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (eCirc t)) (-I * (starRingEnd ℂ) (eCirc θ)) θ := by
  have hconj_eq : (fun t : ℝ => (starRingEnd ℂ) (eCirc t))
      = fun t : ℝ => (Real.cos t : ℂ) - (Real.sin t : ℂ) * I := by
    funext t; rw [eCirc]
    simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [hconj_eq]
  have hcos : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) ((-Real.sin θ : ℝ) : ℂ) θ :=
    (Real.hasDerivAt_cos θ).ofReal_comp
  have hsin : HasDerivAt (fun t : ℝ => (Real.sin t : ℂ)) ((Real.cos θ : ℝ) : ℂ) θ :=
    (Real.hasDerivAt_sin θ).ofReal_comp
  have hd := hcos.sub (hsin.mul_const I)
  convert! hd using 1
  rw [eCirc]
  simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  linear_combination (Real.sin θ : ℂ) * Complex.I_mul_I

/-- **The angular integral vanishes:** `∫_{-π}^{π} (conj (e θ))² dθ = 0`. The integrand has
the `2π`-periodic primitive `(I/2)(conj (e θ))²`, and `e π = e (-π) = -1`. -/
lemma angular_integral_eq_zero :
    (∫ θ in Set.Ioo (-π : ℝ) π, ((starRingEnd ℂ) (eCirc θ)) ^ 2) = 0 := by
  have hper : ∀ s : ℝ, HasDerivAt (fun t : ℝ => (I / 2) * ((starRingEnd ℂ) (eCirc t)) ^ 2)
      (((starRingEnd ℂ) (eCirc s)) ^ 2) s := by
    intro s
    have h2 := ((eCirc_conj_hasDerivAt s).pow 2).const_mul (I / 2)
    convert! h2 using 1
    have hps : (2:ℕ) - 1 = 1 := rfl
    rw [hps, pow_one]
    have hI2 : (I:ℂ) ^ 2 = -1 := by rw [pow_two]; exact Complex.I_mul_I
    field_simp
    rw [hI2]; ring
  have hπle : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hπle]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hper θ)]
  · have hπ : eCirc π = (-1 : ℂ) := by rw [eCirc]; simp [Real.cos_pi, Real.sin_pi]
    have hmπ : eCirc (-π) = (-1 : ℂ) := by rw [eCirc]; simp [Real.cos_pi, Real.sin_pi]
    rw [hπ, hmπ]; simp
  · apply Continuous.intervalIntegrable
    have hcont_e : Continuous eCirc := by unfold eCirc; fun_prop
    exact ((Complex.continuous_conj.comp hcont_e)).pow 2

/-- **General angular integral of a nonzero power of `e θ` vanishes:** for `n ≥ 1`,
`∫_{-π}^{π} (e θ)^n dθ = 0`. The primitive is `(e θ)^n / (n·I)` (since `(e θ)^n` has
derivative `n·I·(e θ)^n`), and `e π = e (-π) = -1` makes the boundary terms cancel. -/
lemma angular_integral_pow_eq_zero (n : ℕ) (hn : 1 ≤ n) :
    (∫ θ in Set.Ioo (-π : ℝ) π, (eCirc θ) ^ n) = 0 := by
  have hnne : (n : ℂ) ≠ 0 := by
    have : (0:ℕ) < n := hn
    exact_mod_cast this.ne'
  have hni : (n : ℂ) * I ≠ 0 := mul_ne_zero hnne Complex.I_ne_zero
  -- Primitive `F θ = (e θ)^n / (n·I)` has derivative `(e θ)^n`.
  have hper : ∀ s : ℝ, HasDerivAt (fun t : ℝ => (eCirc t) ^ n / ((n : ℂ) * I))
      ((eCirc s) ^ n) s := by
    intro s
    have hd : HasDerivAt (fun t : ℝ => (eCirc t) ^ n)
        ((n : ℂ) * (eCirc s) ^ (n - 1) * (I * eCirc s)) s :=
      (eCirc_hasDerivAt s).pow n
    have hd2 := hd.div_const ((n : ℂ) * I)
    convert! hd2 using 1
    rw [eq_div_iff hni]
    have hns : (eCirc s) ^ (n - 1) * eCirc s = (eCirc s) ^ n := by
      rw [← pow_succ]; congr 1; omega
    have : (n : ℂ) * (eCirc s) ^ (n - 1) * (I * eCirc s)
        = (n : ℂ) * I * ((eCirc s) ^ (n - 1) * eCirc s) := by ring
    rw [this, hns]; ring
  have hπle : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hπle]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hper θ)]
  · have hπ : eCirc π = (-1 : ℂ) := by rw [eCirc]; simp [Real.cos_pi, Real.sin_pi]
    have hmπ : eCirc (-π) = (-1 : ℂ) := by rw [eCirc]; simp [Real.cos_pi, Real.sin_pi]
    rw [hπ, hmπ]; simp
  · apply Continuous.intervalIntegrable
    have hcont_e : Continuous eCirc := by unfold eCirc; fun_prop
    exact hcont_e.pow n

/-- `polarCoord.symm p = p.1 • eCirc p.2` (the complex form of the polar symm map). -/
lemma polarCoord_symm_eq (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * eCirc p.2 := by
  rw [Complex.polarCoord_symm_apply, eCirc]

/-- **Mean-zero of the dyadic Beurling piece.** `∫_ℂ ψ_i = 0`. In polar coordinates the
integrand factors into a radial part (`ρ⁻¹`, integrable over `[2ⁱr, 2ⁱ⁺¹r)`) times the angular
part `(conj (e θ))²`, whose integral over a full turn vanishes. -/
lemma integral_dyadicBeurling_eq_zero (r : ℝ) (hr : 0 < r) (i : ℕ) :
    ∫ u, dyadicBeurling r i u ∂volume = 0 := by
  classical
  set a := (2:ℝ)^i * r with ha_def
  set b := (2:ℝ)^(i+1) * r with hb_def
  have ha : 0 < a := by rw [ha_def]; positivity
  have hab : a < b := by
    rw [ha_def, hb_def]
    apply mul_lt_mul_of_pos_right _ hr
    apply pow_lt_pow_right₀ (by norm_num) (by omega)
  have hb : 0 < b := ha.trans hab
  have htarget : (polarCoord.target : Set (ℝ × ℝ)) = Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π := rfl
  rw [← Complex.integral_comp_polarCoord_symm (fun u => dyadicBeurling r i u)]
  set F : ℝ × ℝ → ℂ := fun p =>
    (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ)⁻¹)) p.1 * ((starRingEnd ℂ) (eCirc p.2)) ^ 2
    with hF_def
  have hcongr : ∀ p ∈ (polarCoord.target : Set (ℝ × ℝ)),
      p.1 • dyadicBeurling r i (Complex.polarCoord.symm p) = F p := by
    intro p hp
    rw [htarget, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
    obtain ⟨hp1, _⟩ := hp
    simp only [hF_def]
    rw [dyadicBeurling]
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    by_cases hmem : Complex.polarCoord.symm p ∈
        {u : ℂ | (2:ℝ)^i * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(i+1) * r}
    · rw [Set.indicator_of_mem hmem]
      simp only [Set.mem_ofPred_eq, hnorm, ← ha_def, ← hb_def] at hmem
      rw [Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hmem.1, hmem.2⟩)]
      rw [polarCoord_symm_eq]
      have hp1ne : (p.1 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp1
      have heinv : (eCirc p.2)⁻¹ = (starRingEnd ℂ) (eCirc p.2) := eCirc_inv p.2
      rw [zpow_neg, zpow_two, mul_inv, ← heinv]
      rw [real_smul]
      field_simp
    · rw [Set.indicator_of_notMem hmem]
      simp only [Set.mem_ofPred_eq, hnorm, ← ha_def, ← hb_def] at hmem
      rw [Set.indicator_of_notMem (by
        simp only [Set.mem_Ico, not_and, not_lt]
        intro h1; by_contra h2; exact hmem ⟨h1, not_le.mp h2⟩)]
      simp
  refine (setIntegral_congr_fun
    (by rw [htarget]; exact measurableSet_Ioi.prod measurableSet_Ioo) hcongr).trans ?_
  rw [htarget]
  have hfubini := MeasureTheory.setIntegral_prod_mul
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ)⁻¹)))
    (g := fun θ : ℝ => ((starRingEnd ℂ) (eCirc θ)) ^ 2)
    (Set.Ioi (0:ℝ)) (Set.Ioo (-π) π)
  have hang : (∫ θ in Set.Ioo (-π:ℝ) π, ((starRingEnd ℂ) (eCirc θ)) ^ 2) = 0 :=
    angular_integral_eq_zero
  calc (∫ p in Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π, F p)
      = ∫ p in Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π,
          (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ)⁻¹)) p.1
            * ((starRingEnd ℂ) (eCirc p.2)) ^ 2 ∂(volume.prod volume) := by
            rw [Measure.volume_eq_prod ℝ ℝ]
    _ = (∫ x in Set.Ioi (0:ℝ), (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ)⁻¹)) x)
          * ∫ y in Set.Ioo (-π:ℝ) π, ((starRingEnd ℂ) (eCirc y)) ^ 2 := hfubini
    _ = 0 := by rw [hang, mul_zero]

/-- The reflected/conjugated kernel `ψ̃_i = conj (ψ_i (-·))` is also mean-zero. -/
lemma integral_convKernelStar_dyadicBeurling_eq_zero (r : ℝ) (hr : 0 < r) (i : ℕ) :
    ∫ u, convKernelStar (dyadicBeurling r i) u ∂volume = 0 := by
  unfold convKernelStar
  rw [show (∫ (u : ℂ), (starRingEnd ℂ) (dyadicBeurling r i (-u)) ∂volume)
      = (starRingEnd ℂ) (∫ (u : ℂ), dyadicBeurling r i (-u) ∂volume) from integral_conj]
  rw [integral_neg_eq_self (fun u => dyadicBeurling r i u) volume]
  rw [integral_dyadicBeurling_eq_zero r hr i, map_zero]

/-- **Polar separation of a radially-`ρ`-power × angular integral over an annulus.**
If a function `H : ℂ → ℂ` agrees on the annulus `{a ≤ ‖u‖ < b}` (and vanishes off it) with the
polar product `ρ^k · A(θ)` (i.e. `H (ρ • eCirc θ) = (ρ:ℂ)^k * A θ` on the target), then its
integral is `(∫_{[a,b)} ρ^{k+1} dρ) · (∫_{(-π,π)} A)`. When the angular integral `∫ A` vanishes,
so does `∫ H`. This is the abstract engine behind all the moment computations. -/
lemma integral_annulus_polar_factor (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (k : ℤ) (A : ℝ → ℂ)
    (H : ℂ → ℂ)
    (hzero : ∀ u : ℂ, ¬ (a ≤ ‖u‖ ∧ ‖u‖ < b) → H u = 0)
    (hpolar : ∀ ρ : ℝ, 0 < ρ → a ≤ ρ → ρ < b → ∀ θ : ℝ,
      H ((ρ : ℂ) * eCirc θ) = (ρ : ℂ) ^ k * A θ)
    (hAzero : (∫ θ in Set.Ioo (-π : ℝ) π, A θ) = 0) :
    ∫ u, H u ∂volume = 0 := by
  classical
  have hb : 0 < b := ha.trans hab
  have htarget : (polarCoord.target : Set (ℝ × ℝ)) = Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π := rfl
  rw [← Complex.integral_comp_polarCoord_symm H]
  set F : ℝ × ℝ → ℂ := fun p =>
    (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ) ^ (k + 1))) p.1 * A p.2 with hF_def
  have hcongr : ∀ p ∈ (polarCoord.target : Set (ℝ × ℝ)),
      p.1 • H (Complex.polarCoord.symm p) = F p := by
    intro p hp
    rw [htarget, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
    obtain ⟨hp1, _⟩ := hp
    simp only [hF_def]
    rw [polarCoord_symm_eq]
    have hnorm : ‖(p.1 : ℂ) * eCirc p.2‖ = p.1 := by
      rw [norm_mul, eCirc_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg hp1.le]
    by_cases hmem : a ≤ p.1 ∧ p.1 < b
    · rw [hpolar p.1 hp1 hmem.1 hmem.2 p.2]
      rw [Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hmem.1, hmem.2⟩)]
      rw [Complex.real_smul]
      rw [zpow_add_one₀ (by exact_mod_cast ne_of_gt hp1)]
      ring
    · rw [hzero _ (by rw [hnorm]; exact hmem)]
      rw [Set.indicator_of_notMem (by
        simp only [Set.mem_Ico, not_and, not_lt]
        intro h1; by_contra h2; exact hmem ⟨h1, not_le.mp h2⟩)]
      simp
  refine (setIntegral_congr_fun
    (by rw [htarget]; exact measurableSet_Ioi.prod measurableSet_Ioo) hcongr).trans ?_
  rw [htarget]
  have hfubini := MeasureTheory.setIntegral_prod_mul
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ) ^ (k + 1))))
    (g := A) (Set.Ioi (0:ℝ)) (Set.Ioo (-π) π)
  calc (∫ p in Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π, F p)
      = ∫ p in Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π,
          (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ) ^ (k + 1))) p.1
            * A p.2 ∂(volume.prod volume) := by rw [Measure.volume_eq_prod ℝ ℝ]
    _ = (∫ x in Set.Ioi (0:ℝ), (Set.Ico a b).indicator (fun ρ : ℝ => ((ρ : ℂ) ^ (k + 1))) x)
          * ∫ y in Set.Ioo (-π:ℝ) π, A y := hfubini
    _ = 0 := by rw [hAzero, mul_zero]

/-- The polar value of `u·ψ_j` on the annulus is `ρ⁻¹·conj(e θ)`: helper computation. -/
lemma polar_value_id_mul (ρ : ℝ) (hρ : 0 < ρ) (θ : ℝ) :
    ((ρ : ℂ) * eCirc θ) * ((ρ : ℂ) * eCirc θ) ^ (-2 : ℤ)
      = (ρ : ℂ) ^ (-1 : ℤ) * (starRingEnd ℂ) (eCirc θ) := by
  have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  have heθ : eCirc θ ≠ 0 := eCirc_ne_zero θ
  rw [zpow_neg, zpow_two, mul_inv]
  rw [show ((ρ : ℂ) * eCirc θ) * (((ρ:ℂ)*eCirc θ)⁻¹ * ((ρ:ℂ)*eCirc θ)⁻¹)
      = (((ρ:ℂ)*eCirc θ) * ((ρ:ℂ)*eCirc θ)⁻¹) * ((ρ:ℂ)*eCirc θ)⁻¹ by ring]
  rw [mul_inv_cancel₀ (mul_ne_zero hρne heθ), one_mul, mul_inv, eCirc_inv]
  rw [zpow_neg, zpow_one]

/-- **First moment of the dyadic Beurling piece vanishes (holomorphic component):**
`∫ u · ψ_j(u) du = 0`. In polar the integrand is `ρ⁻¹ · conj(e θ)`, so the radial profile is
`ρ⁰ = 1` and the angular part `conj(e θ)` integrates to `conj(∫ e θ) = 0`
(`angular_integral_pow_eq_zero 1`). -/
lemma integral_id_mul_dyadicBeurling_eq_zero (r : ℝ) (hr : 0 < r) (j : ℕ) :
    ∫ u, u * dyadicBeurling r j u ∂volume = 0 := by
  refine integral_annulus_polar_factor ((2:ℝ)^j * r) ((2:ℝ)^(j+1) * r) (by positivity)
    (by apply mul_lt_mul_of_pos_right _ hr; exact pow_lt_pow_right₀ (by norm_num) (by omega))
    (-1) (fun θ => (starRingEnd ℂ) (eCirc θ)) (fun u => u * dyadicBeurling r j u) ?_ ?_ ?_
  · -- vanishes off the annulus
    intro u hu
    have hu' : u ∉ {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r} := hu
    simp only [dyadicBeurling, Set.indicator_of_notMem hu', mul_zero]
  · -- polar value on the annulus
    intro ρ hρ hρa hρb θ
    simp only [dyadicBeurling]
    have hmem : (ρ : ℂ) * eCirc θ ∈
        {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r} := by
      have hnorm : ‖(ρ : ℂ) * eCirc θ‖ = ρ := by
        rw [norm_mul, eCirc_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ.le]
      simp only [Set.mem_ofPred_eq, hnorm]; exact ⟨hρa, hρb⟩
    rw [Set.indicator_of_mem hmem]
    exact polar_value_id_mul ρ hρ θ
  · -- angular integral vanishes: ∫ conj(e θ) = conj(∫ e θ) = conj(∫ (e θ)^1) = 0
    have hconj : (∫ θ in Set.Ioo (-π : ℝ) π, (starRingEnd ℂ) (eCirc θ))
        = (starRingEnd ℂ) (∫ θ in Set.Ioo (-π : ℝ) π, eCirc θ) :=
      integral_conj
    rw [hconj]
    have he1 : (∫ θ in Set.Ioo (-π : ℝ) π, eCirc θ)
        = ∫ θ in Set.Ioo (-π : ℝ) π, (eCirc θ) ^ 1 := by simp
    rw [he1, angular_integral_pow_eq_zero 1 (le_refl 1), map_zero]

/-- The polar value of `ū·ψ_j` on the annulus is `ρ⁻¹·conj((e θ)³)`: helper computation.
Here `ū = ρ·conj(e θ)` and `ψ_j = (ρ e θ)⁻²`, so the product is `ρ⁻¹·conj(e θ)·(e θ)⁻²
= ρ⁻¹·conj(e θ)³`. -/
lemma polar_value_conj_mul (ρ : ℝ) (hρ : 0 < ρ) (θ : ℝ) :
    (starRingEnd ℂ) ((ρ : ℂ) * eCirc θ) * ((ρ : ℂ) * eCirc θ) ^ (-2 : ℤ)
      = (ρ : ℂ) ^ (-1 : ℤ) * ((starRingEnd ℂ) (eCirc θ)) ^ 3 := by
  have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  have heθ : eCirc θ ≠ 0 := eCirc_ne_zero θ
  have hconjρ : (starRingEnd ℂ) (ρ : ℂ) = (ρ : ℂ) := Complex.conj_ofReal ρ
  have heinv : (eCirc θ)⁻¹ = (starRingEnd ℂ) (eCirc θ) := eCirc_inv θ
  rw [map_mul, hconjρ, zpow_neg, zpow_two, mul_inv, mul_inv, zpow_neg, zpow_one]
  rw [show ((ρ : ℂ) * (starRingEnd ℂ) (eCirc θ))
        * (((ρ:ℂ)⁻¹ * (eCirc θ)⁻¹) * ((ρ:ℂ)⁻¹ * (eCirc θ)⁻¹))
      = ((ρ:ℂ) * (ρ:ℂ)⁻¹) * (ρ:ℂ)⁻¹
        * ((starRingEnd ℂ) (eCirc θ) * (eCirc θ)⁻¹ * (eCirc θ)⁻¹) by ring]
  rw [mul_inv_cancel₀ hρne, one_mul, heinv]
  ring

/-- **First moment of the dyadic Beurling piece vanishes (anti-holomorphic component):**
`∫ ū · ψ_j(u) du = 0`. In polar the integrand is `ρ⁻¹ · conj((e θ)³)`, radial profile `ρ⁰=1`,
angular `conj((e θ)³)` integrates to `conj(∫ (e θ)³) = 0` (`angular_integral_pow_eq_zero 3`). -/
lemma integral_conj_mul_dyadicBeurling_eq_zero (r : ℝ) (hr : 0 < r) (j : ℕ) :
    ∫ u, (starRingEnd ℂ) u * dyadicBeurling r j u ∂volume = 0 := by
  refine integral_annulus_polar_factor ((2:ℝ)^j * r) ((2:ℝ)^(j+1) * r) (by positivity)
    (by apply mul_lt_mul_of_pos_right _ hr; exact pow_lt_pow_right₀ (by norm_num) (by omega))
    (-1) (fun θ => ((starRingEnd ℂ) (eCirc θ)) ^ 3)
    (fun u => (starRingEnd ℂ) u * dyadicBeurling r j u) ?_ ?_ ?_
  · -- vanishes off the annulus
    intro u hu
    have hu' : u ∉ {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r} := hu
    simp only [dyadicBeurling, Set.indicator_of_notMem hu', mul_zero]
  · -- polar value on the annulus
    intro ρ hρ hρa hρb θ
    simp only [dyadicBeurling]
    have hmem : (ρ : ℂ) * eCirc θ ∈
        {u : ℂ | (2:ℝ)^j * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j+1) * r} := by
      have hnorm : ‖(ρ : ℂ) * eCirc θ‖ = ρ := by
        rw [norm_mul, eCirc_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ.le]
      simp only [Set.mem_ofPred_eq, hnorm]; exact ⟨hρa, hρb⟩
    rw [Set.indicator_of_mem hmem]
    exact polar_value_conj_mul ρ hρ θ
  · -- angular integral vanishes
    rw [show (∫ θ in Set.Ioo (-π : ℝ) π, ((starRingEnd ℂ) (eCirc θ)) ^ 3)
        = ∫ θ in Set.Ioo (-π : ℝ) π, (starRingEnd ℂ) ((eCirc θ) ^ 3) by
          simp only [map_pow]]
    have hconj : (∫ θ in Set.Ioo (-π : ℝ) π, (starRingEnd ℂ) ((eCirc θ) ^ 3))
        = (starRingEnd ℂ) (∫ θ in Set.Ioo (-π : ℝ) π, (eCirc θ) ^ 3) :=
      integral_conj
    rw [hconj, angular_integral_pow_eq_zero 3 (by norm_num), map_zero]

/-- **First moment of the reflected kernel `ψ̃_i = conj(ψ_i(-·))` vanishes (holomorphic
component):** `∫ t · ψ̃_i(t) dt = 0`. Reduces to the anti-holomorphic first moment of `ψ_i`
via the reflection `t ↦ -t` (measure preserving) and `conj`. -/
lemma integral_id_mul_convKernelStar_eq_zero (r : ℝ) (hr : 0 < r) (i : ℕ) :
    ∫ t, t * convKernelStar (dyadicBeurling r i) t ∂volume = 0 := by
  unfold convKernelStar
  -- ∫ t·conj(ψ_i(-t)) = ∫ (-t)·conj(ψ_i t) (sub t↦-t) = -∫ conj(conj t · ψ_i t) = -conj 0 = 0
  rw [← integral_neg_eq_self (fun t => t * (starRingEnd ℂ) (dyadicBeurling r i (-t))) volume]
  have hcongr : (fun t => (fun s => s * (starRingEnd ℂ) (dyadicBeurling r i (-s))) (-t))
      = fun t => (starRingEnd ℂ) (-((starRingEnd ℂ) t * dyadicBeurling r i t)) := by
    funext t; simp only [neg_neg, map_neg, map_mul, Complex.conj_conj]; ring
  rw [hcongr]
  have hci : (∫ t, (starRingEnd ℂ) (-((starRingEnd ℂ) t * dyadicBeurling r i t)) ∂volume)
      = (starRingEnd ℂ) (∫ t, -((starRingEnd ℂ) t * dyadicBeurling r i t) ∂volume) :=
    integral_conj
  rw [hci, integral_neg, integral_conj_mul_dyadicBeurling_eq_zero r hr i, neg_zero, map_zero]

/-- **First moment of the reflected kernel `ψ̃_i` vanishes (anti-holomorphic component):**
`∫ conj(t) · ψ̃_i(t) dt = 0`. Reduces to the holomorphic first moment of `ψ_i`. -/
lemma integral_conj_mul_convKernelStar_eq_zero (r : ℝ) (hr : 0 < r) (i : ℕ) :
    ∫ t, (starRingEnd ℂ) t * convKernelStar (dyadicBeurling r i) t ∂volume = 0 := by
  unfold convKernelStar
  rw [← integral_neg_eq_self
    (fun t => (starRingEnd ℂ) t * (starRingEnd ℂ) (dyadicBeurling r i (-t))) volume]
  have hcongr : (fun t => (fun s => (starRingEnd ℂ) s * (starRingEnd ℂ) (dyadicBeurling r i (-s)))
      (-t)) = fun t => (starRingEnd ℂ) (-(t * dyadicBeurling r i t)) := by
    funext t; simp only [neg_neg, map_neg, map_mul]; ring
  rw [hcongr]
  have hci : (∫ t, (starRingEnd ℂ) (-(t * dyadicBeurling r i t)) ∂volume)
      = (starRingEnd ℂ) (∫ t, -(t * dyadicBeurling r i t) ∂volume) :=
    integral_conj
  rw [hci, integral_neg, integral_id_mul_dyadicBeurling_eq_zero r hr i, neg_zero, map_zero]

/-- **Mean-zero reduces convolution to a difference.** If the kernel `g ∈ L¹` has integral zero
and the convolution `(g ⋆ f)(x)` exists at `x`, then `(g ⋆ f)(x) = ∫ g(t)·(f(x - t) - f(x)) dt`.
This is the entry point of the MVT cancellation: the inserted `-g(t)·f(x)` integrates to
`-f(x)·∫ g = 0`. -/
lemma convolution_apply_eq_of_integral_zero {g f : ℂ → ℂ} (hg : MemLp g 1 volume)
    (hgz : ∫ t, g t ∂volume = 0) (x : ℂ)
    (hex : ConvolutionExistsAt g f x (ContinuousLinearMap.mul ℂ ℂ) volume) :
    MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume x
      = ∫ t, g t * (f (x - t) - f x) ∂volume := by
  rw [MeasureTheory.convolution_mul]
  have hgint : Integrable g volume := (memLp_one_iff_integrable).mp hg
  have hint1 : Integrable (fun t => g t * f (x - t)) volume := by
    have := hex
    rw [ConvolutionExistsAt] at this
    simpa [ContinuousLinearMap.mul_apply'] using this
  have hint2 : Integrable (fun t => g t * f x) volume := hgint.mul_const _
  have hsub : (fun t => g t * (f (x - t) - f x)) = (fun t => g t * f (x - t) - g t * f x) := by
    funext t; ring
  have hzero2 : (∫ t, g t * f x ∂volume) = 0 := by
    have h2 : (∫ t, g t * f x ∂volume) = (∫ t, g t ∂volume) * f x :=
      integral_mul_const (f x) g
    rw [h2, hgz, zero_mul]
  rw [hsub, integral_sub hint1 hint2, hzero2, sub_zero]

/-- **Modulus-of-continuity Fubini reduction.** For a mean-zero `L¹` kernel `g` and `L¹`
function `f`, the `L¹` mass of `g ⋆ f` is controlled by the `g`-weighted integral of the
first-order modulus of continuity `ω_f(t) = ∫ ‖f(·-t) - f‖`. This is the entry point that
converts cancellation (mean-zero) into geometric decay. -/
lemma eLpNorm_convolution_meanZero_le {g f : ℂ → ℂ}
    (hg : MemLp g 1 volume) (hf : MemLp f 1 volume) (hgz : ∫ t, g t ∂volume = 0) :
    eLpNorm (MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume
      ≤ ∫⁻ t, ‖g t‖ₑ * (∫⁻ x, ‖f (x - t) - f x‖ₑ ∂volume) ∂volume := by
  have hgm : AEMeasurable (fun t => ‖g t‖ₑ) volume := hg.1.enorm
  have hfm : AEStronglyMeasurable f volume := hf.1
  have hgint : Integrable g volume := (memLp_one_iff_integrable).mp hg
  have hfint : Integrable f volume := (memLp_one_iff_integrable).mp hf
  -- a.e. existence of the convolution (L¹ ⋆ L¹).
  have hex : ∀ᵐ x ∂volume,
      ConvolutionExistsAt g f x (ContinuousLinearMap.mul ℂ ℂ) volume :=
    hgint.ae_convolution_exists (L := ContinuousLinearMap.mul ℂ ℂ) hfint
  -- pointwise a.e. bound on the convolution enorm.
  have hpt : ∀ᵐ x ∂volume,
      ‖MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume x‖ₑ
        ≤ ∫⁻ t, ‖g t‖ₑ * ‖f (x - t) - f x‖ₑ ∂volume := by
    filter_upwards [hex] with x hxe
    rw [convolution_apply_eq_of_integral_zero hg hgz x hxe]
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    apply lintegral_mono
    intro t
    simp only [enorm_mul, le_refl]
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hmono :
      (∫⁻ x, ‖MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume x‖ₑ ∂volume)
        ≤ ∫⁻ x, (∫⁻ t, ‖g t‖ₑ * ‖f (x - t) - f x‖ₑ ∂volume) ∂volume :=
    lintegral_mono_ae hpt
  refine le_trans hmono ?_
  -- Fubini swap.
  have hGmeas : AEMeasurable
      (Function.uncurry fun x t => ‖g t‖ₑ * ‖f (x - t) - f x‖ₑ) (volume.prod volume) := by
    apply AEMeasurable.fun_mul
    · exact hgm.comp_snd
    · have hsub1 : AEStronglyMeasurable (fun p : ℂ × ℂ => f (p.1 - p.2)) (volume.prod volume) :=
        hfm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub_of_right_invariant volume volume)
      have hsub2 : AEStronglyMeasurable (fun p : ℂ × ℂ => f p.1) (volume.prod volume) :=
        hfm.comp_fst
      exact (hsub1.sub hsub2).enorm
  rw [lintegral_lintegral_swap hGmeas]
  apply lintegral_mono
  intro t
  simp only
  rw [lintegral_const_mul'' _ (by
    have hsub1 : AEStronglyMeasurable (fun x : ℂ => f (x - t)) volume :=
      hfm.comp_quasiMeasurePreserving
        (measurePreserving_sub_right volume t).quasiMeasurePreserving
    exact (hsub1.sub hfm).enorm)]

end NoWanderingDomains
