/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.SingularIntegral.Beurling.L2Core

/-!
# The Beurling transform — LpLow

`Lᵖ` boundedness for `1 < p < 2`: uniform-in-`r` truncation bounds (Marcinkiewicz),
the maximal operator on `Lᵖ`, a.e. convergence, and the passage to `beurling`
(`eLpNorm_beurling_Lp_le`); plus the kernel symmetry `beurlingKernel_symm`.

Part of the `Beurling` development (overview in `Beurling/Kernel.lean`). -/

open MeasureTheory Complex Filter Topology
open scoped Real ENNReal NNReal Convolution InnerProductSpace

namespace NoWanderingDomains

variable {μ : ℂ → ℂ} {z : ℂ} {p : ℝ≥0∞}

/-! ## `Lᵖ` boundedness: uniform bounds on the truncations

For `1 < p < 2` the truncated Beurling operator `czOperator beurlingKernel r` is
bounded `Lᵖ → Lᵖ` with a constant independent of `r`, by Marcinkiewicz
interpolation between its weak-(1,1) bound (`czOperator_weak_1_1`, upgraded from
`BoundedFiniteSupport` to all of `L¹`) and its strong-(2,2) bound
(`eLpNorm_czOperator_beurling_L2`). Passing `r → 0⁺` (a.e. convergence + Fatou)
then transfers the bound to the Beurling transform itself. -/

/-- Integrability of the truncated Beurling integrand against an `L¹` function:
on `(ball x r)ᶜ` the kernel is bounded by `r⁻²`, so `K(x,·)·f` is integrable for
`f ∈ L¹`. -/
lemma integrableOn_beurlingKernel_mul_L1 {r : ℝ} (hr : 0 < r) (x : ℂ) {f : ℂ → ℂ}
    (hf : MemLp f 1 volume) :
    IntegrableOn (fun y => beurlingKernel x y * f y) (Metric.ball x r)ᶜ volume := by
  -- `f` is integrable; restrict to `(ball x r)ᶜ`.
  have hfint : Integrable f volume := memLp_one_iff_integrable.mp hf
  rw [IntegrableOn]
  -- The kernel `beurlingKernel x ·` is `AEStronglyMeasurable`.
  have hker_meas : AEStronglyMeasurable (fun y => beurlingKernel x y)
      (volume.restrict (Metric.ball x r)ᶜ) := by
    apply Measurable.aestronglyMeasurable
    unfold beurlingKernel; fun_prop
  -- On `(ball x r)ᶜ` the kernel is bounded by `r⁻²`.
  have hbound : ∀ᵐ y ∂(volume.restrict (Metric.ball x r)ᶜ),
      ‖beurlingKernel x y‖ ≤ (r : ℝ) ^ (-2 : ℤ) := by
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with y hy
    -- `y ∉ ball x r ⇒ r ≤ dist x y = ‖x - y‖`.
    have hr_le : r ≤ ‖x - y‖ := by
      rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, dist_comm] at hy
      rw [Complex.dist_eq] at hy; exact hy
    have hxy_pos : 0 < ‖x - y‖ := lt_of_lt_of_le hr hr_le
    have hnorm : ‖beurlingKernel x y‖ = ‖x - y‖ ^ (-2 : ℤ) := by
      rw [beurlingKernel, norm_zpow]
    rw [hnorm, zpow_neg, zpow_neg, zpow_two, zpow_two]
    -- `(‖x-y‖ * ‖x-y‖)⁻¹ ≤ (r * r)⁻¹`.
    apply inv_anti₀ (by positivity)
    exact mul_le_mul hr_le hr_le hr.le hxy_pos.le
  -- Apply `Integrable.bdd_mul` with bounded factor the kernel.
  exact Integrable.bdd_mul (hfint.restrict) hker_meas hbound

/-- Integrability of the truncated Beurling integrand against an `Lᵖ` function,
`1 < p < ∞`: the kernel section lies in `Lᵖ'` (since `∫_{|u|≥r} |u|^{-2p'} < ∞`
for `p' < ∞`), so the product is in `L¹` by Hölder. -/
lemma integrableOn_beurlingKernel_mul_Lp {r : ℝ} (hr : 0 < r) (x : ℂ) {p p' : ℝ≥0∞}
    (hp1 : 1 < p) (hp_top : p ≠ ⊤) [ENNReal.HolderConjugate p p'] {f : ℂ → ℂ}
    (hf : MemLp f p volume) :
    IntegrableOn (fun y => beurlingKernel x y * f y) (Metric.ball x r)ᶜ volume := by
  -- The conjugate exponent `p'` is finite and `> 1`.
  have : ENNReal.HolderConjugate p' p := ENNReal.HolderConjugate.symm
  have hp'_top : p' ≠ ⊤ := by
    have : p' < ⊤ := (ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mpr hp1
    exact this.ne
  have hp'1 : 1 < p' := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p').mp
    (lt_of_le_of_ne le_top hp_top)
  set q' : ℝ := p'.toReal with hq'_def
  have hp'0 : p' ≠ 0 := by
    rintro rfl; exact absurd hp'1 (by simp)
  have hq'1 : 1 < q' := by
    rw [hq'_def, show (1:ℝ) = (1 : ℝ≥0∞).toReal from rfl]
    exact ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp'_top |>.mpr hp'1
  have hq'0 : 0 < q' := lt_trans one_pos hq'1
  -- **Finite mass of the truncated kernel section at exponent `q'`.**
  -- `∫_{‖u‖≥r} ((‖u‖ₑ^2)⁻¹)^q' < ∞` via polar coordinates, `∫_r^∞ ρ^{1-2q'} dρ < ∞`.
  have hlint : ∫⁻ u : ℂ in {u : ℂ | r ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ q' < ⊤ := by
    rw [← lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable),
      ← Complex.lintegral_comp_polarCoord_symm]
    set box : ℝ × ℝ → ENNReal := fun p =>
      (Set.Ici r ×ˢ Set.Ioo (-π) π).indicator
        (fun p => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) p with hbox
    have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) := by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.mul measurable_fst
      exact (Real.continuous_rpow_const hq'0.le).measurable.comp ((measurable_fst.pow_const 2).inv)
    have hbound : ∀ p ∈ polarCoord.target,
        ENNReal.ofReal p.1 • {u : ℂ | r ≤ ‖u‖}.indicator
          (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (Complex.polarCoord.symm p) ≤ box p := by
      intro p hp
      rw [polarCoord_target, Set.mem_prod] at hp
      obtain ⟨hp1', hp2⟩ := hp
      simp only [Set.mem_Ioi] at hp1'
      simp only [hbox]
      have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp1']
      by_cases hmem : Complex.polarCoord.symm p ∈ {u : ℂ | r ≤ ‖u‖}
      · have hpR : r ≤ p.1 := by rw [Set.mem_ofPred_eq, hnorm] at hmem; exact hmem
        rw [Set.indicator_of_mem hmem,
          Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hpR, hp2⟩)]
        have henorm : ‖Complex.polarCoord.symm p‖ₑ = ENNReal.ofReal p.1 := by
          rw [← ofReal_norm, hnorm]
        rw [henorm, smul_eq_mul,
          show ((ENNReal.ofReal p.1 ^ 2)⁻¹) ^ q' = ENNReal.ofReal (((p.1^2)⁻¹)^q') by
            rw [← ENNReal.ofReal_pow hp1'.le, ← ENNReal.ofReal_inv_of_pos (by positivity),
              ENNReal.ofReal_rpow_of_pos (by positivity)],
          ← ENNReal.ofReal_mul hp1'.le]
      · rw [Set.indicator_of_notMem hmem, smul_zero]; exact zero_le
    refine lt_of_le_of_lt (setLIntegral_mono
      (hmeas_polar.indicator (measurableSet_Ici.prod measurableSet_Ioo)) hbound) ?_
    calc ∫⁻ p in polarCoord.target, box p
        ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
      _ = ∫⁻ p in (Set.Ici r ×ˢ Set.Ioo (-π) π), ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q') := by
            rw [hbox, lintegral_indicator (measurableSet_Ici.prod measurableSet_Ioo)]
      _ < ⊤ := by
            rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hmeas_polar.aemeasurable]
            simp only [setLIntegral_const]
            rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
            apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
            have hint : IntegrableOn (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q') (Set.Ici r) volume := by
              have heq : (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q')
                  =ᶠ[ae (volume.restrict (Set.Ici r))]
                  (fun ρ : ℝ => ρ^(1 - 2 * q')) := by
                filter_upwards [ae_restrict_mem measurableSet_Ici] with ρ hρ
                simp only [Set.mem_Ici] at hρ
                have hρpos : 0 < ρ := lt_of_lt_of_le hr hρ
                have hbase : (ρ^2)⁻¹ = ρ^(-2 : ℝ) := by
                  rw [Real.rpow_neg hρpos.le, ← Real.rpow_natCast ρ 2]; norm_num
                have h1 : ((ρ^2)⁻¹)^q' = ρ^(-2 * q') := by
                  rw [hbase, ← Real.rpow_mul hρpos.le]
                have h2 : ρ * ρ^(-2 * q') = ρ^(1 - 2 * q') := by
                  nth_rewrite 1 [← Real.rpow_one ρ]
                  rw [← Real.rpow_add hρpos]; congr 1; ring
                rw [h1, h2]
              rw [integrableOn_congr_fun_ae heq, integrableOn_Ici_iff_integrableOn_Ioi,
                integrableOn_Ioi_rpow_iff hr]
              -- `1 - 2 q' < -1 ↔ q' > 1`.
              nlinarith [hq'1]
            have hfin := hint.2
            rw [hasFiniteIntegral_iff_enorm] at hfin
            refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y hy => ?_)) hfin
            · refine (measurable_id.mul ?_).enorm
              exact (Real.continuous_rpow_const hq'0.le).measurable.comp
                ((measurable_id.pow_const 2).inv)
            · simp only [Set.mem_Ici] at hy
              have hypos : 0 < y := lt_of_lt_of_le hr hy
              rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- **Kernel section ∈ Lᵖ'.**
  have hker : MemLp (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) p'
      volume := by
    have hmeas : AEStronglyMeasurable
        (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) volume := by
      apply AEStronglyMeasurable.indicator _ measurableSet_ball.compl
      apply Measurable.aestronglyMeasurable
      unfold beurlingKernel; fun_prop
    refine ⟨hmeas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp'0 hp'_top]
    rw [← hq'_def]
    have hpt : ∀ y, ‖(Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y‖ₑ ^ q'
        = (Metric.ball x r)ᶜ.indicator (fun y => ‖beurlingKernel x y‖ₑ ^ q') y := by
      intro y
      by_cases h : y ∈ (Metric.ball x r)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero,
          ENNReal.zero_rpow_of_pos hq'0]
    refine lt_of_eq_of_lt (lintegral_congr hpt) ?_
    rw [lintegral_indicator measurableSet_ball.compl]
    have hkb : ∀ y, ‖beurlingKernel x y‖ₑ ^ q' ≤ ((‖x - y‖ₑ ^ 2)⁻¹) ^ q' := by
      intro y
      apply ENNReal.rpow_le_rpow _ hq'0.le
      by_cases h : x = y
      · subst h; simp [beurlingKernel]
      · have hne : x - y ≠ 0 := sub_ne_zero.mpr h
        have he : beurlingKernel x y = ((x-y) * (x-y))⁻¹ := by
          rw [beurlingKernel, zpow_neg, zpow_two]
        rw [he, enorm_inv (mul_ne_zero hne hne), enorm_mul, sq]
    refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y _ => hkb y)) ?_
    · exact ENNReal.continuous_rpow_const.measurable.comp
        ((((measurable_const.sub measurable_id).enorm).pow_const 2).inv)
    rw [← lintegral_indicator measurableSet_ball.compl]
    have hsub : (fun y => (Metric.ball x r)ᶜ.indicator (fun y => ((‖x - y‖ₑ ^ 2)⁻¹) ^ q') y)
        = (fun y => {u : ℂ | r ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (x - y)) := by
      funext y
      have hiff : (y ∈ (Metric.ball x r)ᶜ) ↔ (x - y ∈ {u : ℂ | r ≤ ‖u‖}) := by
        rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, Set.mem_ofPred_eq, dist_comm,
          Complex.dist_eq]
      by_cases h : y ∈ (Metric.ball x r)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]
    rw [hsub, lintegral_sub_left_eq_self
      (fun u => {u : ℂ | r ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') u) x]
    rw [lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable)]
    exact hlint
  rw [IntegrableOn]
  have h1 : MemLp (fun y => beurlingKernel x y) p' (volume.restrict (Metric.ball x r)ᶜ) := by
    apply MemLp.ae_eq _ (hker.restrict (Metric.ball x r)ᶜ)
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with y hy
    rw [Set.indicator_of_mem hy]
  exact h1.integrable_mul (hf.restrict _)

/-- The truncations are `AEStronglyMeasurable` for any measurable `f`. -/
lemma aestronglyMeasurable_czOperator_beurling' {r : ℝ} {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (czOperator beurlingKernel r f) volume :=
  czOperator_aestronglyMeasurable hf

/-- The truncated Beurling operator is weak-(1,1) on all of `L¹` (not just
`BoundedFiniteSupport`): the Carleson bound `czOperator_weak_1_1` extends by
`L¹` density and `wnorm` lower semicontinuity (the truncations converge uniformly
since the kernel is bounded by `r⁻²` on `(ball x r)ᶜ`). -/
lemma hasWeakType_czOperator_beurling_one {r : ℝ} (hr : 0 < r) :
    HasWeakType (czOperator beurlingKernel r) 1 1 volume volume (C10_0_3 4) := by
  intro f hf
  refine ⟨aestronglyMeasurable_czOperator_beurling' hf.aestronglyMeasurable, ?_⟩
  -- Carleson weak-(1,1) on `BoundedFiniteSupport`.
  have hBWT : HasBoundedWeakType (czOperator beurlingKernel r) 1 1 volume volume (C10_0_3 4) :=
    czOperator_weak_1_1 (show (4:ℕ) ≤ 4 by norm_num) hr (czOperator_beurling_strongType_L2 hr)
  -- The enorm of the truncated kernel on `(ball x r)ᶜ` is `≤ ofReal (r⁻²)`.
  have hkernelEnorm : ∀ (x y : ℂ), y ∈ (Metric.ball x r)ᶜ →
      ‖beurlingKernel x y‖ₑ ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) := by
    intro x y hy
    have hr_le : r ≤ ‖x - y‖ := by
      rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, dist_comm] at hy
      rw [Complex.dist_eq] at hy; exact hy
    have hxy_pos : 0 < ‖x - y‖ := lt_of_lt_of_le hr hr_le
    have hnorm : ‖beurlingKernel x y‖ = ‖x - y‖ ^ (-2 : ℤ) := by
      rw [beurlingKernel, norm_zpow]
    have hle : ‖beurlingKernel x y‖ ≤ (r : ℝ) ^ (-2 : ℤ) := by
      rw [hnorm, zpow_neg, zpow_neg, zpow_two, zpow_two]
      apply inv_anti₀ (by positivity)
      exact mul_le_mul hr_le hr_le hr.le hxy_pos.le
    calc ‖beurlingKernel x y‖ₑ = ENNReal.ofReal ‖beurlingKernel x y‖ :=
          (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) := ENNReal.ofReal_le_ofReal hle
  -- The `L¹` operator bound: `‖czOp h x‖ₑ ≤ ofReal(r⁻²) · ‖h‖₁`.
  have hOpBound : ∀ (h : ℂ → ℂ) (x : ℂ),
      ‖czOperator beurlingKernel r h x‖ₑ
        ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * eLpNorm h 1 volume := by
    intro h x
    have hczeq : czOperator beurlingKernel r h x
        = ∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * h y := rfl
    rw [hczeq]
    calc ‖∫ y in (Metric.ball x r)ᶜ, beurlingKernel x y * h y‖ₑ
        ≤ ∫⁻ y in (Metric.ball x r)ᶜ, ‖beurlingKernel x y * h y‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y in (Metric.ball x r)ᶜ, ‖beurlingKernel x y‖ₑ * ‖h y‖ₑ := by simp_rw [enorm_mul]
      _ ≤ ∫⁻ y in (Metric.ball x r)ᶜ, ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * ‖h y‖ₑ := by
          refine setLIntegral_mono' measurableSet_ball.compl (fun y hy => ?_)
          exact mul_le_mul' (hkernelEnorm x y hy) le_rfl
      _ = ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ))
            * ∫⁻ y in (Metric.ball x r)ᶜ, ‖h y‖ₑ := by rw [lintegral_const_mul']; finiteness
      _ ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * ∫⁻ y, ‖h y‖ₑ := by
          exact mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
      _ = ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * eLpNorm h 1 volume := by
          rw [eLpNorm_one_eq_lintegral_enorm]
  -- An approximating sequence of simple functions, `‖f - gₖ‖₁ → 0`, each `BoundedFiniteSupport`.
  have hεne : ∀ k : ℕ, (((k : ℝ≥0∞) + 1))⁻¹ ≠ 0 := by
    intro k; exact ENNReal.inv_ne_zero.mpr (by finiteness)
  choose g hgle hgmem using fun k : ℕ =>
    hf.exists_simpleFunc_eLpNorm_sub_lt (by simp) (hεne k)
  -- Each `gₖ` (as a function) is `BoundedFiniteSupport`.
  have hgBFS : ∀ k, BoundedFiniteSupport (⇑(g k)) volume := by
    intro k
    refine ⟨(g k).memLp_top volume, ?_⟩
    exact (g k).measure_support_lt_top_of_memLp (hgmem k) one_ne_zero ENNReal.one_ne_top
  -- `‖f - gₖ‖₁ → 0`.
  have htend0 : Tendsto (fun k => eLpNorm (f - ⇑(g k)) 1 volume) atTop (𝓝 0) := by
    have hinv0 : Tendsto (fun k : ℕ => (((k : ℝ≥0∞) + 1))⁻¹) atTop (𝓝 0) := by
      have hcomp : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
        ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      refine hcomp.congr (fun k => ?_)
      push_cast; ring_nf
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv0
      (fun k => zero_le) (fun k => (hgle k).le)
  -- Each `gₖ ∈ L¹`.
  have hgL1 : ∀ k, MemLp (⇑(g k)) 1 volume := fun k => (hgBFS k).memLp 1
  -- Pointwise convergence of the truncations.
  have hconv : ∀ x : ℂ, Tendsto (fun k => czOperator beurlingKernel r (⇑(g k)) x) atTop
      (𝓝 (czOperator beurlingKernel r f x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    -- `czOp gₖ x - czOp f x = czOp (gₖ - f) x` (linearity from integrability).
    have hdiff : ∀ k, czOperator beurlingKernel r (⇑(g k)) x - czOperator beurlingKernel r f x
        = czOperator beurlingKernel r (⇑(g k) - f) x := by
      intro k
      have h1 := integrableOn_beurlingKernel_mul_L1 hr x (hgL1 k)
      have h2 := integrableOn_beurlingKernel_mul_L1 hr x hf
      unfold czOperator
      rw [← integral_sub h1 h2]
      refine setIntegral_congr_fun measurableSet_ball.compl (fun y _ => ?_)
      simp only [Pi.sub_apply]; ring
    -- The enorm bound `‖czOp gₖ x − czOp f x‖ₑ ≤ ofReal(r⁻²)·‖gₖ − f‖₁`.
    have hbdE : ∀ k, ‖czOperator beurlingKernel r (⇑(g k)) x - czOperator beurlingKernel r f x‖ₑ
        ≤ ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * eLpNorm (⇑(g k) - f) 1 volume := by
      intro k; rw [hdiff k]; exact hOpBound (⇑(g k) - f) x
    -- The RHS tends to `0` in `ℝ≥0∞`.
    have hRHS0 : Tendsto
        (fun k => ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) * eLpNorm (⇑(g k) - f) 1 volume) atTop
        (𝓝 0) := by
      have heq : ∀ k, eLpNorm (⇑(g k) - f) 1 volume = eLpNorm (f - ⇑(g k)) 1 volume := by
        intro k; rw [← eLpNorm_neg]; congr 1; funext y; simp
      have : Tendsto (fun k => ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ))
          * eLpNorm (f - ⇑(g k)) 1 volume) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul htend0
          (Or.inr (by simp : ENNReal.ofReal ((r : ℝ) ^ (-2 : ℤ)) ≠ ⊤))
        simpa using this
      exact this.congr (fun k => by rw [heq k])
    -- The enorm of the difference tends to `0`, hence so does the norm.
    have henorm0 : Tendsto
        (fun k => ‖czOperator beurlingKernel r (⇑(g k)) x - czOperator beurlingKernel r f x‖ₑ)
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRHS0
        (fun k => zero_le) hbdE
    -- Convert `‖·‖ₑ → 0` to `‖·‖ → 0`.
    have := (ENNReal.tendsto_toReal (by simp)).comp henorm0
    simpa [Function.comp_def, toReal_enorm] using this
  -- Apply the `wnorm` Fatou lemma via the `ε`-route.
  -- `‖gₖ‖₁ → ‖f‖₁` (reverse triangle inequality, `ℝ≥0∞` squeeze).
  have hgnorm : Tendsto (fun k => eLpNorm (⇑(g k)) 1 volume) atTop (𝓝 (eLpNorm f 1 volume)) := by
    set L := eLpNorm f 1 volume with hL
    set d := fun k => eLpNorm (f - ⇑(g k)) 1 volume with hd
    have hupper : ∀ k, eLpNorm (⇑(g k)) 1 volume ≤ L + d k := by
      intro k
      have h : eLpNorm (⇑(g k)) 1 volume
          ≤ eLpNorm f 1 volume + eLpNorm (⇑(g k) - f) 1 volume := by
        calc eLpNorm (⇑(g k)) 1 volume = eLpNorm (f + (⇑(g k) - f)) 1 volume := by
              congr 1; funext y; simp
          _ ≤ eLpNorm f 1 volume + eLpNorm (⇑(g k) - f) 1 volume :=
              eLpNorm_add_le hf.aestronglyMeasurable ((hgL1 k).sub hf).aestronglyMeasurable le_rfl
      rw [hL, hd]
      rwa [show eLpNorm (⇑(g k) - f) 1 volume = eLpNorm (f - ⇑(g k)) 1 volume from by
        rw [← eLpNorm_neg]; congr 1; funext y; simp] at h
    have hlower : ∀ k, L - d k ≤ eLpNorm (⇑(g k)) 1 volume := by
      intro k
      rw [tsub_le_iff_right]
      calc L = eLpNorm ((⇑(g k)) + (f - ⇑(g k))) 1 volume := by rw [hL]; congr 1; funext y; simp
        _ ≤ eLpNorm (⇑(g k)) 1 volume + eLpNorm (f - ⇑(g k)) 1 volume :=
            eLpNorm_add_le (hgL1 k).aestronglyMeasurable
              (hf.sub (hgL1 k)).aestronglyMeasurable le_rfl
    have hupper' : Tendsto (fun k => L + d k) atTop (𝓝 L) := by
      simpa using tendsto_const_nhds.add htend0
    have hlower' : Tendsto (fun k => L - d k) atTop (𝓝 L) := by
      simpa using (ENNReal.Tendsto.sub (a := L) (b := 0) tendsto_const_nhds htend0
        (Or.inr (by simp)))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower' hupper' hlower hupper
  -- `C10_0_3 4 · ‖gₖ‖₁ → C10_0_3 4 · ‖f‖₁`.
  have hCgnorm : Tendsto (fun k => (C10_0_3 4 : ℝ≥0∞) * eLpNorm (⇑(g k)) 1 volume) atTop
      (𝓝 ((C10_0_3 4 : ℝ≥0∞) * eLpNorm f 1 volume)) :=
    ENNReal.Tendsto.const_mul hgnorm (Or.inr (by finiteness))
  -- Finite-ness of the target product.
  have hbfin : (C10_0_3 4 : ℝ≥0∞) * eLpNorm f 1 volume < ⊤ :=
    ENNReal.mul_lt_top (by finiteness) hf.2
  -- Now the `ε`-route.
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  set L := (C10_0_3 4 : ℝ≥0∞) * eLpNorm f 1 volume with hLdef
  have hLlt : L < L + (ε : ℝ≥0∞) :=
    ENNReal.lt_add_right hbfin.ne (by exact_mod_cast hε.ne')
  -- Eventually `C10_0_3 4 · ‖gₖ‖₁ ≤ L + ε`.
  have hbound : ∀ᶠ k in atTop,
      wnorm (czOperator beurlingKernel r (⇑(g k))) 1 volume ≤ L + (ε : ℝ≥0∞) := by
    have hev := hCgnorm.eventually_le_const hLlt
    filter_upwards [hev] with k hk
    exact le_trans (hBWT (⇑(g k)) (hgBFS k)).2 hk
  -- Conclude by the `wnorm` Fatou lemma.
  exact wnorm_le_of_ae_tendsto hbound
    (fun k => aestronglyMeasurable_czOperator_beurling' (hgL1 k).aestronglyMeasurable)
    (Filter.Eventually.of_forall hconv)

/-- The truncated Beurling operator is strong-(2,2) on all of `L²`
(`eLpNorm_czOperator_beurling_L2`). -/
lemma hasStrongType_czOperator_beurling_two {r : ℝ} (hr : 0 < r) :
    HasStrongType (czOperator beurlingKernel r) 2 2 volume volume (C10_1_6 4) := by
  intro f hf
  exact ⟨aestronglyMeasurable_czOperator_beurling hf, eLpNorm_czOperator_beurling_L2 hr hf⟩

/-- The truncated Beurling operator is subadditive (in fact linear) on the
union class `L¹ ∪ L²`. -/
lemma aesubadditiveOn_czOperator_beurling {r : ℝ} (hr : 0 < r) :
    AESubadditiveOn (czOperator beurlingKernel r)
      (fun f : ℂ → ℂ => MemLp f 1 volume ∨ MemLp f 2 volume) 1 volume := by
  intro f g hf hg
  -- From the `L¹ ∪ L²` membership, get integrability of the kernel product on `(ball x r)ᶜ`.
  have hf_int : ∀ x : ℂ,
      IntegrableOn (fun y => beurlingKernel x y * f y) (Metric.ball x r)ᶜ volume := by
    intro x
    rcases hf with hf1 | hf2
    · exact integrableOn_beurlingKernel_mul_L1 hr x hf1
    · exact integrableOn_beurlingKernel_mul hr x hf2
  have hg_int : ∀ x : ℂ,
      IntegrableOn (fun y => beurlingKernel x y * g y) (Metric.ball x r)ᶜ volume := by
    intro x
    rcases hg with hg1 | hg1
    · exact integrableOn_beurlingKernel_mul_L1 hr x hg1
    · exact integrableOn_beurlingKernel_mul hr x hg1
  -- The operator is additive, so the bound holds pointwise (for all `x`).
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [czOperator_beurling_add (hf_int x) (hg_int x), one_mul]
  exact enorm_add_le _ _

/-- The interpolation constant for the truncated Beurling operator on `Lᵖ`,
`1 < p < 2`: independent of `r`. -/
noncomputable def beurlingTruncLpConst (p : ℝ≥0∞) : ℝ≥0 :=
  C_realInterpolation 1 2 1 2 p (C10_0_3 4) (C10_1_6 4) 1 (2 * (1 - p⁻¹))

/-- **Uniform-in-`r` `Lᵖ` bound for the truncations**, `1 < p < 2`, by
Marcinkiewicz interpolation. The constant `beurlingTruncLpConst p` does not depend
on `r`. -/
lemma eLpNorm_czOperator_beurling_Lp {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2) {r : ℝ} (hr : 0 < r)
    {f : ℂ → ℂ} (hf : MemLp f p volume) :
    eLpNorm (czOperator beurlingKernel r f) p volume
      ≤ (beurlingTruncLpConst p : ℝ≥0∞) * eLpNorm f p volume := by
  -- interpolation parameter (verbatim arithmetic from `isCalderonZygmundBound_of_hasWeakType`)
  set t : ℝ≥0∞ := 2 * (1 - p⁻¹) with ht_def
  have hp0 : p ≠ 0 := by rintro rfl; exact absurd hp1 (by simp)
  have hpinv_lt1 : p⁻¹ < 1 := by rw [ENNReal.inv_lt_one]; exact hp1
  have hhalf_lt : (2:ℝ≥0∞)⁻¹ < p⁻¹ := by rw [ENNReal.inv_lt_inv]; exact hp2
  have hpinv_ne_top : p⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hp0
  have h2mulinv : (2:ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have h2 : (1:ℝ≥0∞) - p⁻¹ < 2⁻¹ := by
    have htwo_inv_ne : (2:ℝ≥0∞)⁻¹ ≠ ∞ := by simp
    have hadd : (1:ℝ≥0∞) - p⁻¹ + p⁻¹ < 2⁻¹ + p⁻¹ := by
      rw [tsub_add_cancel_of_le hpinv_lt1.le]
      calc (1:ℝ≥0∞) = 2⁻¹ + 2⁻¹ := (ENNReal.inv_two_add_inv_two).symm
        _ < 2⁻¹ + p⁻¹ := by
          rw [ENNReal.add_lt_add_iff_left htwo_inv_ne]; exact hhalf_lt
    exact lt_of_add_lt_add_right hadd
  have ht : t ∈ Set.Ioo (0:ℝ≥0∞) 1 := by
    constructor
    · have : 0 < 1 - p⁻¹ := tsub_pos_of_lt hpinv_lt1
      rw [ht_def]; positivity
    · rw [ht_def]
      calc 2 * (1 - p⁻¹) < 2 * 2⁻¹ := by gcongr; simp
        _ = 1 := h2mulinv
  have h2pinv : (1:ℝ≥0∞) ≤ 2 * p⁻¹ := by
    calc (1:ℝ≥0∞) = 2 * 2⁻¹ := h2mulinv.symm
      _ ≤ 2 * p⁻¹ := by gcongr
  have hp : p⁻¹ = (1 - t) / 1 + t / 2 := by
    rw [ht_def, div_one]
    have htle1 : 2 * (1 - p⁻¹) ≤ 1 := ht.2.le
    lift p⁻¹ to ℝ≥0 using hpinv_ne_top with y
    have hy1 : y ≤ 1 := by exact_mod_cast hpinv_lt1.le
    have hone_sub : (1:ℝ≥0∞) - (y : ℝ≥0∞) = ((1 - y : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_one, ← ENNReal.coe_sub]
    rw [hone_sub, show (2:ℝ≥0∞) = ((2:ℝ≥0):ℝ≥0∞) by simp, ← ENNReal.coe_mul] at htle1 ⊢
    have htle1' : 2 * (1 - y) ≤ 1 := by exact_mod_cast htle1
    rw [show (1:ℝ≥0∞) = ((1:ℝ≥0):ℝ≥0∞) by simp, ← ENNReal.coe_sub,
      ← ENNReal.coe_div (by simp), ← ENNReal.coe_add, ENNReal.coe_inj]
    rw [NNReal.eq_iff]
    push_cast [NNReal.coe_sub, NNReal.coe_div, htle1', hy1]
    ring
  have hp0' : (1:ℝ≥0∞) ∈ Set.Ioc 0 1 := by constructor <;> simp
  have hp1' : (2:ℝ≥0∞) ∈ Set.Ioc 0 2 := by constructor <;> simp
  have hq0q1 : (1:ℝ≥0∞) ≠ 2 := by norm_num
  -- endpoint hypotheses for the truncated Beurling operator
  have hmeas : ∀ g : ℂ → ℂ, MemLp g p volume →
      AEStronglyMeasurable (czOperator beurlingKernel r g) volume :=
    fun g hg => aestronglyMeasurable_czOperator_beurling' hg.aestronglyMeasurable
  have hsub : AESubadditiveOn (czOperator beurlingKernel r)
      (fun g : ℂ → ℂ => MemLp g 1 volume ∨ MemLp g 2 volume) 1 volume :=
    aesubadditiveOn_czOperator_beurling hr
  have hweak₁ : HasWeakType (czOperator beurlingKernel r) 1 1 volume volume (C10_0_3 4) :=
    hasWeakType_czOperator_beurling_one hr
  have hweak₂ : HasWeakType (czOperator beurlingKernel r) 2 2 volume volume (C10_1_6 4) :=
    (hasStrongType_czOperator_beurling_two hr).hasWeakType (by norm_num)
  have hA : (1 : ℝ≥0) ≤ 1 := le_refl _
  have hC₁ : (0 : ℝ≥0) < C10_0_3 4 := by rw [C10_0_3]; positivity
  have hC₂ : (0 : ℝ≥0) < C10_1_6 4 := by rw [C10_1_6]; positivity
  -- apply the Carleson real-interpolation theorem
  have hST : HasStrongType (czOperator beurlingKernel r) p p volume volume
      (C_realInterpolation 1 2 1 2 p (C10_0_3 4) (C10_1_6 4) 1 t) :=
    exists_hasStrongType_real_interpolation hp0' hp1' hq0q1 hA ht hC₁ hC₂ hp hp
      hmeas hsub hweak₁ hweak₂
  have hbound := (hST f hf).2
  -- match the constant with `beurlingTruncLpConst p`
  rw [beurlingTruncLpConst]
  exact hbound

/-! ## `Lᵖ` bounds for the maximal truncated operator (`1 < p < 2`)

The `L²` maximal-operator development, replicated at exponent `p`: the maximal
operator `simpleNontangentialOperator beurlingKernel 0` is bounded `Lᵖ → Lᵖ`
(Cotlar's pointwise estimate `cotlar_estimate` + the Hardy–Littlewood maximal
`Lᵖ` bound `hasStrongType_maximalFunction` + the truncation `Lᵖ` bound
`eLpNorm_czOperator_beurling_Lp`), which yields a.e. convergence of the
truncations on `Lᵖ`. The constants are immaterial here (only finiteness matters),
so the maximal bound is stated with an existential constant. -/

/-- `Lᵖ`-linearity of the truncated Beurling operator (`1 < p < ∞`): both kernel
products are integrable (`integrableOn_beurlingKernel_mul_Lp`), so the truncated
integral is additive. -/
lemma czOperator_beurling_sub_Lp {p : ℝ≥0∞} (hp1 : 1 < p) (hp_top : p ≠ ⊤) {r : ℝ} (hr : 0 < r)
    (x : ℂ) {f g : ℂ → ℂ} (hf : MemLp f p volume) (hg : MemLp g p volume) :
    czOperator beurlingKernel r (f - g) x
      = czOperator beurlingKernel r f x - czOperator beurlingKernel r g x := by
  -- Construct the conjugate exponent `p' = (1 - p⁻¹)⁻¹` and its `HolderConjugate` instance.
  have hpinv_le_one : p⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]; exact hp1.le
  have hHC : ENNReal.HolderConjugate p ((1 - p⁻¹)⁻¹) := by
    rw [ENNReal.holderConjugate_iff, inv_inv, add_tsub_cancel_of_le hpinv_le_one]
  have h1 := integrableOn_beurlingKernel_mul_Lp (p' := (1 - p⁻¹)⁻¹) hr x hp1 hp_top hf
  have h2 := integrableOn_beurlingKernel_mul_Lp (p' := (1 - p⁻¹)⁻¹) hr x hp1 hp_top hg
  unfold czOperator
  rw [← integral_sub h1 h2]
  refine setIntegral_congr_fun measurableSet_ball.compl (fun y _ => ?_)
  simp only [Pi.sub_apply]; ring

/-- **Maximal-operator `Lᵖ` bound** (`1 < p < 2`): a finite constant `C` with
`‖simpleNontangentialOperator beurlingKernel 0 g‖_p ≤ C ‖g‖_p` for every `g ∈ Lᵖ`.
Proved by replicating `simple_nontangential_operator` at exponent `p` (Cotlar +
HL-maximal-`Lᵖ` + `eLpNorm_czOperator_beurling_Lp`) on `BoundedFiniteSupport`,
then extending to all of `Lᵖ` by lower semicontinuity + Fatou. -/
lemma exists_eLpNorm_simpleNontangential_beurling_Lp {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ≥0, ∀ g : ℂ → ℂ, MemLp g p volume →
      eLpNorm (simpleNontangentialOperator beurlingKernel 0 g) p volume
        ≤ (C : ℝ≥0∞) * eLpNorm g p volume := by
  have hp_top : p ≠ ⊤ := (lt_trans hp2 (by norm_num : (2:ℝ≥0∞) < ⊤)).ne_top
  have hp1' : (1 : ℝ≥0∞) ≤ p := hp1.le
  -- `p` as an `ℝ≥0`, with `1 < pnn`.
  set pnn : ℝ≥0 := p.toNNReal with hpnn_def
  have hpnn_coe : (pnn : ℝ≥0∞) = p := by rw [hpnn_def, ENNReal.coe_toNNReal hp_top]
  have hpnn1 : 1 < pnn := by
    have : (1 : ℝ≥0∞) < (pnn : ℝ≥0∞) := by rw [hpnn_coe]; exact hp1
    exact_mod_cast this
  -- The HL maximal `Lᵖ` strong-type bound (constant `Cgmf`).
  -- Use the `defaultA 4` doubling structure (the one carried by the Carleson lemmas).
  have hA4 : (volume : Measure ℂ).IsDoubling ((defaultA 4 : ℕ) : ℝ≥0) :=
    doublingMeasure_complex_defaultA4.toIsDoubling
  set Cgmf : ℝ≥0 := C2_0_6 ((defaultA 4 : ℕ) : ℝ≥0) 1 pnn with hCgmf_def
  have hgmf : HasStrongType
      (globalMaximalFunction (X := ℂ) (ε := ℂ) volume 1)
      (pnn : ℝ≥0∞) (pnn : ℝ≥0∞) volume volume Cgmf := by
    have h := hasStrongType_maximalFunction (X := ℂ) (ε' := ℂ) (μ := volume)
      (A := ((defaultA 4 : ℕ) : ℝ≥0)) (𝓑 := Set.univ (α := ℂ × ℝ)) (c := (·.fst))
      (r := (·.snd)) (p₁ := 1) (p₂ := pnn) zero_lt_one hpnn1
    norm_cast at h
  -- Abbreviations for the truncation constant.
  set Ctr : ℝ≥0 := beurlingTruncLpConst p with hCtr_def
  -- **Part (a): the BFS bound at a positive scale `r`.**
  set C₀ : ℝ≥0 := 4 * Cgmf * Ctr + (C10_1_5 4 + C10_1_2 4) * Cgmf with hC₀_def
  have hBFSscale : ∀ {r : ℝ}, 0 < r → ∀ g : ℂ → ℂ, BoundedFiniteSupport g volume →
      eLpNorm (simpleNontangentialOperator beurlingKernel r g) p volume
        ≤ (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
    intro r hr g hg
    -- The strong-type input for Cotlar's estimate (`L²` truncation bound).
    have hT : ∀ s > 0, HasBoundedStrongType (czOperator beurlingKernel s) 2 2 volume volume
        (C_Ts 4 : ℝ≥0∞) := fun s hs => czOperator_beurling_strongType_L2 hs
    -- The pointwise dominating function (Cotlar + x-shift), exponent-free.
    set pointwise : ℂ → ℝ≥0∞ :=
      4 * globalMaximalFunction volume 1 (czOperator beurlingKernel r g)
        + C10_1_5 4 • globalMaximalFunction volume 1 g
        + C10_1_2 4 • globalMaximalFunction volume 1 g with hpw_def
    -- Pointwise domination (verbatim from `simple_nontangential_operator`).
    have hdom : ∀ x, simpleNontangentialOperator beurlingKernel r g x ≤ pointwise x := by
      simp_rw [hpw_def, simpleNontangentialOperator, iSup_le_iff]
      intro x R hR x' hx'
      rw [Metric.mem_ball, dist_comm] at hx'
      trans ‖czOperator beurlingKernel R g x‖ₑ
          + C10_1_2 4 * globalMaximalFunction volume 1 g x
      · calc ‖czOperator beurlingKernel R g x'‖ₑ
            = ‖czOperator beurlingKernel R g x
              + (czOperator beurlingKernel R g x' - czOperator beurlingKernel R g x)‖ₑ := by
              congr 1; ring
          _ ≤ ‖czOperator beurlingKernel R g x‖ₑ
              + ‖czOperator beurlingKernel R g x'
                - czOperator beurlingKernel R g x‖ₑ := enorm_add_le _ _
          _ ≤ ‖czOperator beurlingKernel R g x‖ₑ
              + C10_1_2 4 * globalMaximalFunction volume 1 g x := by
              gcongr
              rw [← edist_eq_enorm_sub, edist_comm]
              exact estimate_x_shift (K := beurlingKernel) (by norm_num) hg
                (hr.trans hR.lt) hx'.le
      · refine add_le_add (cotlar_estimate (K := beurlingKernel) (r := r) (R := R)
          (by norm_num) hT hg ?_) (by rfl) |>.trans ?_
        · rw [Set.mem_Ioc]; exact ⟨hr, hR.le⟩
        · apply le_of_eq
          simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, ENNReal.smul_def, smul_eq_mul,
            Pi.ofNat_apply, add_assoc]
    -- Take `eLpNorm _ p` and use the additivity + maximal `Lᵖ` + truncation `Lᵖ` bounds.
    refine (eLpNorm_mono_enorm (g := pointwise) (fun x => by
      simp only [enorm_eq_self]; exact hdom x)).trans ?_
    -- `czOperator r g ∈ Lᵖ` and `g ∈ Lᵖ` (from `BoundedFiniteSupport`).
    have hgLp : MemLp g p volume := hg.memLp p
    have hczLp : MemLp (czOperator beurlingKernel r g) p volume := by
      refine ⟨aestronglyMeasurable_czOperator_beurling' hgLp.aestronglyMeasurable, ?_⟩
      exact lt_of_le_of_lt (eLpNorm_czOperator_beurling_Lp hp1 hp2 hr hgLp)
        (ENNReal.mul_lt_top ENNReal.coe_lt_top hgLp.2)
    -- Strong-type bounds for the maximal functions.
    have hgmf_g := (hgmf g (by rw [hpnn_coe]; exact hgLp)).2
    have hgmf_czg := (hgmf (czOperator beurlingKernel r g) (by rw [hpnn_coe]; exact hczLp)).2
    rw [hpnn_coe] at hgmf_g hgmf_czg
    -- Measurability for `eLpNorm_add_le`.
    have hm_czg : AEStronglyMeasurable
        (globalMaximalFunction volume 1 (czOperator beurlingKernel r g)) volume :=
      measurable_maximalFunction.aestronglyMeasurable
    have hm_g : AEStronglyMeasurable (globalMaximalFunction volume 1 g) volume :=
      measurable_maximalFunction.aestronglyMeasurable
    rw [hpw_def, show (4 : ℂ → ℝ≥0∞)
          * globalMaximalFunction volume 1 (czOperator beurlingKernel r g)
        = (4 : ℝ≥0) • globalMaximalFunction volume 1 (czOperator beurlingKernel r g) by
      ext y; simp [ENNReal.smul_def]]
    -- Split the eLpNorm of the sum.
    refine (eLpNorm_add_le (by fun_prop) (by fun_prop) hp1').trans ?_
    refine (add_le_add (eLpNorm_add_le (by fun_prop) (by fun_prop) hp1') (le_refl _)).trans ?_
    rw [show eLpNorm ((4 : ℝ≥0) • globalMaximalFunction volume 1
          (czOperator beurlingKernel r g)) p volume
        = ‖(4 : ℝ≥0)‖ₑ * eLpNorm (globalMaximalFunction volume 1
          (czOperator beurlingKernel r g)) p volume from eLpNorm_const_smul',
      show eLpNorm (C10_1_5 4 • globalMaximalFunction volume 1 g) p volume
        = ‖C10_1_5 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
        from eLpNorm_const_smul',
      show eLpNorm (C10_1_2 4 • globalMaximalFunction volume 1 g) p volume
        = ‖C10_1_2 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
        from eLpNorm_const_smul']
    -- Apply the maximal `Lᵖ` bound and then the truncation `Lᵖ` bound.
    have hkey : ‖(4 : ℝ≥0)‖ₑ * eLpNorm (globalMaximalFunction volume 1
          (czOperator beurlingKernel r g)) p volume
        + (‖C10_1_5 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
          + ‖C10_1_2 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume)
        ≤ (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
      have hb1 : eLpNorm (globalMaximalFunction volume 1 (czOperator beurlingKernel r g)) p volume
          ≤ (Cgmf : ℝ≥0∞) * ((Ctr : ℝ≥0∞) * eLpNorm g p volume) := by
        refine hgmf_czg.trans ?_
        rw [hCtr_def]
        exact mul_le_mul' (le_refl _) (eLpNorm_czOperator_beurling_Lp hp1 hp2 hr hgLp)
      have hb2 : eLpNorm (globalMaximalFunction volume 1 g) p volume
          ≤ (Cgmf : ℝ≥0∞) * eLpNorm g p volume := hgmf_g
      calc ‖(4 : ℝ≥0)‖ₑ * eLpNorm (globalMaximalFunction volume 1
              (czOperator beurlingKernel r g)) p volume
            + (‖C10_1_5 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume
              + ‖C10_1_2 4‖ₑ * eLpNorm (globalMaximalFunction volume 1 g) p volume)
          ≤ ‖(4 : ℝ≥0)‖ₑ * ((Cgmf : ℝ≥0∞) * ((Ctr : ℝ≥0∞) * eLpNorm g p volume))
              + (‖C10_1_5 4‖ₑ * ((Cgmf : ℝ≥0∞) * eLpNorm g p volume)
                + ‖C10_1_2 4‖ₑ * ((Cgmf : ℝ≥0∞) * eLpNorm g p volume)) := by
            gcongr
        _ = (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
            rw [hC₀_def]
            push_cast [enorm_NNReal]
            ring
    rw [add_assoc]; exact hkey
  -- **Scale-0 BFS bound** (monotone convergence over `r = (n+1)⁻¹`).
  have hBFS0 : ∀ g : ℂ → ℂ, BoundedFiniteSupport g volume →
      eLpNorm (simpleNontangentialOperator beurlingKernel 0 g) p volume
        ≤ (C₀ : ℝ≥0∞) * eLpNorm g p volume := by
    intro g hg
    set fseq : ℕ → ℂ → ℝ≥0∞ :=
      fun n => simpleNontangentialOperator beurlingKernel (n + 1 : ℝ)⁻¹ g with hfseq_def
    have f_mon : ∀ x : ℂ, Monotone fun n => fseq n x := by
      intro x m n hmn
      simp only [hfseq_def, simpleNontangentialOperator]
      gcongr with R
      apply iSup_const_mono (lt_of_le_of_lt _)
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      simp only [add_le_add_iff_right]
      exact_mod_cast hmn
    have snt0 : ⨆ (n : ℕ), fseq n = simpleNontangentialOperator beurlingKernel 0 g := by
      ext x
      simp only [hfseq_def]
      simp_rw [iSup_apply, simpleNontangentialOperator, gt_iff_lt]
      rw [iSup_comm]
      congr 1; ext R
      apply le_antisymm (iSup_le <| fun n => iSup_const_mono (lt_trans (by positivity)))
        (iSup_le _)
      intro hR
      set n := Nat.ceil R⁻¹ with hn_def
      have hn : (n + 1 : ℝ)⁻¹ < R :=
        inv_lt_of_inv_lt₀ hR <| (Nat.le_ceil R⁻¹).trans_lt (by exact_mod_cast lt_add_one _)
      refine le_iSup_of_le n ?_
      rw [iSup_pos hn]
    have mct := eLpNorm_iSup' (p := p) (f := fseq) (μ := volume)
      (fun n => aestronglyMeasurable_simpleNontangentialOperator.aemeasurable)
      (by filter_upwards; exact f_mon)
    rw [← snt0, show (⨆ n, fseq n) = fun x => ⨆ n, fseq n x from funext fun x => iSup_apply,
      mct]
    apply iSup_le
    intro n
    exact hBFSscale (r := (n + 1 : ℝ)⁻¹) (by positivity) g hg
  -- **Part (b): extend the scale-0 bound from `BoundedFiniteSupport` to all of `Lᵖ`.**
  -- The conjugate exponent and the kernel-section `Lᵖ'` membership.
  set p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hp'_def
  have hpinv_le_one : p⁻¹ ≤ 1 := by rw [ENNReal.inv_le_one]; exact hp1.le
  have hHC : ENNReal.HolderConjugate p p' := by
    rw [hp'_def, ENNReal.holderConjugate_iff, inv_inv, add_tsub_cancel_of_le hpinv_le_one]
  -- Per-point Hölder bound for the truncation against an `Lᵖ` function.
  have hHolderPt : ∀ (R : ℝ), 0 < R → ∀ (x' : ℂ) {h : ℂ → ℂ}, MemLp h p volume →
      ‖czOperator beurlingKernel R h x'‖ₑ
        ≤ eLpNorm (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p'
            volume * eLpNorm h p volume := by
    intro R hR x' h hh
    unfold czOperator
    have hcs : ∫⁻ y in (Metric.ball x' R)ᶜ, ‖beurlingKernel x' y‖ₑ * ‖h y‖ₑ
        ≤ eLpNorm (fun y => beurlingKernel x' y) p' (volume.restrict (Metric.ball x' R)ᶜ)
          * eLpNorm h p (volume.restrict (Metric.ball x' R)ᶜ) := by
      have := ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm
        (μ := volume.restrict (Metric.ball x' R)ᶜ) (p := p') (q := p)
        (ENNReal.HolderConjugate.symm)
        (f := fun y => ‖beurlingKernel x' y‖ₑ) (g := fun y => ‖h y‖ₑ)
        (by unfold beurlingKernel; fun_prop) hh.aestronglyMeasurable.enorm.restrict
      simpa [eLpNorm_enorm] using this
    calc ‖∫ y in (Metric.ball x' R)ᶜ, beurlingKernel x' y * h y‖ₑ
        ≤ ∫⁻ y in (Metric.ball x' R)ᶜ, ‖beurlingKernel x' y * h y‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y in (Metric.ball x' R)ᶜ, ‖beurlingKernel x' y‖ₑ * ‖h y‖ₑ := by simp_rw [enorm_mul]
      _ ≤ eLpNorm (fun y => beurlingKernel x' y) p' (volume.restrict (Metric.ball x' R)ᶜ)
            * eLpNorm h p (volume.restrict (Metric.ball x' R)ᶜ) := hcs
      _ ≤ eLpNorm (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p'
              volume * eLpNorm h p volume := by
          refine mul_le_mul' ?_ ?_
          · exact le_of_eq (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.compl).symm
          · exact eLpNorm_restrict_le h p volume _
  -- Kernel-section `Lᵖ'` membership (so the per-point constant is finite).
  have hkermem : ∀ (x' : ℂ) (R : ℝ), 0 < R →
      MemLp (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p'
          volume := by
    intro x' R hR
    -- The membership via the `Lᵖ'` lintegral finiteness.
    have : ENNReal.HolderConjugate p' p := ENNReal.HolderConjugate.symm
    have hp'_top : p' ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mpr hp1).ne
    have hp'1 : 1 < p' :=
      (ENNReal.HolderConjugate.lt_top_iff_one_lt p p').mp (lt_of_le_of_ne le_top hp_top)
    set q' : ℝ := p'.toReal with hq'_def
    have hp'0 : p' ≠ 0 := ne_of_gt (lt_trans one_pos hp'1)
    have hq'1 : 1 < q' := by
      rw [hq'_def, show (1:ℝ) = (1 : ℝ≥0∞).toReal from rfl]
      exact ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp'_top |>.mpr hp'1
    have hq'0 : 0 < q' := lt_trans one_pos hq'1
    have hlint : ∫⁻ u : ℂ in {u : ℂ | R ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ q' < ⊤ := by
      rw [← lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable),
        ← Complex.lintegral_comp_polarCoord_symm]
      set box : ℝ × ℝ → ENNReal := fun p =>
        (Set.Ici R ×ˢ Set.Ioo (-π) π).indicator
          (fun p => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) p with hbox
      have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * ((p.1^2)⁻¹)^q')) := by
        apply ENNReal.measurable_ofReal.comp
        apply Measurable.mul measurable_fst
        exact (Real.continuous_rpow_const hq'0.le).measurable.comp
          ((measurable_fst.pow_const 2).inv)
      have hbound : ∀ pp ∈ polarCoord.target,
          ENNReal.ofReal pp.1 • {u : ℂ | R ≤ ‖u‖}.indicator
            (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (Complex.polarCoord.symm pp) ≤ box pp := by
        intro pp hpp
        rw [polarCoord_target, Set.mem_prod] at hpp
        obtain ⟨hpp1, hpp2⟩ := hpp
        simp only [Set.mem_Ioi] at hpp1
        simp only [hbox]
        have hnorm : ‖Complex.polarCoord.symm pp‖ = pp.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hpp1]
        by_cases hmem : Complex.polarCoord.symm pp ∈ {u : ℂ | R ≤ ‖u‖}
        · have hpR : R ≤ pp.1 := by rw [Set.mem_ofPred_eq, hnorm] at hmem; exact hmem
          rw [Set.indicator_of_mem hmem,
            Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hpR, hpp2⟩)]
          have henorm : ‖Complex.polarCoord.symm pp‖ₑ = ENNReal.ofReal pp.1 := by
            rw [← ofReal_norm, hnorm]
          rw [henorm, smul_eq_mul,
            show ((ENNReal.ofReal pp.1 ^ 2)⁻¹) ^ q' = ENNReal.ofReal (((pp.1^2)⁻¹)^q') by
              rw [← ENNReal.ofReal_pow hpp1.le, ← ENNReal.ofReal_inv_of_pos (by positivity),
                ENNReal.ofReal_rpow_of_pos (by positivity)],
            ← ENNReal.ofReal_mul hpp1.le]
        · rw [Set.indicator_of_notMem hmem, smul_zero]; exact zero_le
      refine lt_of_le_of_lt (setLIntegral_mono
        (hmeas_polar.indicator (measurableSet_Ici.prod measurableSet_Ioo)) hbound) ?_
      calc ∫⁻ pp in polarCoord.target, box pp
          ≤ ∫⁻ pp, box pp := setLIntegral_le_lintegral _ _
        _ = ∫⁻ pp in (Set.Ici R ×ˢ Set.Ioo (-π) π),
              ENNReal.ofReal (pp.1 * ((pp.1^2)⁻¹)^q') := by
              rw [hbox, lintegral_indicator (measurableSet_Ici.prod measurableSet_Ioo)]
        _ < ⊤ := by
              rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hmeas_polar.aemeasurable]
              simp only [setLIntegral_const]
              rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
              apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
              have hint2 : IntegrableOn (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q') (Set.Ici R) volume := by
                have heq : (fun ρ : ℝ => ρ * ((ρ^2)⁻¹)^q')
                    =ᶠ[ae (volume.restrict (Set.Ici R))]
                    (fun ρ : ℝ => ρ^(1 - 2 * q')) := by
                  filter_upwards [ae_restrict_mem measurableSet_Ici] with ρ hρ
                  simp only [Set.mem_Ici] at hρ
                  have hρpos : 0 < ρ := lt_of_lt_of_le hR hρ
                  have hbase : (ρ^2)⁻¹ = ρ^(-2 : ℝ) := by
                    rw [Real.rpow_neg hρpos.le, ← Real.rpow_natCast ρ 2]; norm_num
                  have hh1 : ((ρ^2)⁻¹)^q' = ρ^(-2 * q') := by
                    rw [hbase, ← Real.rpow_mul hρpos.le]
                  have hh2 : ρ * ρ^(-2 * q') = ρ^(1 - 2 * q') := by
                    nth_rewrite 1 [← Real.rpow_one ρ]
                    rw [← Real.rpow_add hρpos]; congr 1; ring
                  rw [hh1, hh2]
                rw [integrableOn_congr_fun_ae heq, integrableOn_Ici_iff_integrableOn_Ioi,
                  integrableOn_Ioi_rpow_iff hR]
                nlinarith [hq'1]
              have hfin := hint2.2
              rw [hasFiniteIntegral_iff_enorm] at hfin
              refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y hy => ?_)) hfin
              · refine (measurable_id.mul ?_).enorm
                exact (Real.continuous_rpow_const hq'0.le).measurable.comp
                  ((measurable_id.pow_const 2).inv)
              · simp only [Set.mem_Ici] at hy
                have hypos : 0 < y := lt_of_lt_of_le hR hy
                rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hmeas : AEStronglyMeasurable
        (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) volume := by
      apply AEStronglyMeasurable.indicator _ measurableSet_ball.compl
      apply Measurable.aestronglyMeasurable
      unfold beurlingKernel; fun_prop
    refine ⟨hmeas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp'0 hp'_top, ← hq'_def]
    have hpt : ∀ y, ‖(Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y‖ₑ ^ q'
        = (Metric.ball x' R)ᶜ.indicator (fun y => ‖beurlingKernel x' y‖ₑ ^ q') y := by
      intro y
      by_cases h : y ∈ (Metric.ball x' R)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero,
          ENNReal.zero_rpow_of_pos hq'0]
    refine lt_of_eq_of_lt (lintegral_congr hpt) ?_
    rw [lintegral_indicator measurableSet_ball.compl]
    have hkb : ∀ y, ‖beurlingKernel x' y‖ₑ ^ q' ≤ ((‖x' - y‖ₑ ^ 2)⁻¹) ^ q' := by
      intro y
      apply ENNReal.rpow_le_rpow _ hq'0.le
      by_cases h : x' = y
      · subst h; simp [beurlingKernel]
      · have hne : x' - y ≠ 0 := sub_ne_zero.mpr h
        have he : beurlingKernel x' y = ((x'-y) * (x'-y))⁻¹ := by
          rw [beurlingKernel, zpow_neg, zpow_two]
        rw [he, enorm_inv (mul_ne_zero hne hne), enorm_mul, sq]
    refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y _ => hkb y)) ?_
    · exact ENNReal.continuous_rpow_const.measurable.comp
        ((((measurable_const.sub measurable_id).enorm).pow_const 2).inv)
    rw [← lintegral_indicator measurableSet_ball.compl]
    have hsub : (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => ((‖x' - y‖ₑ ^ 2)⁻¹) ^ q') y)
        = (fun y => {u : ℂ | R ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') (x' - y)) := by
      funext y
      have hiff : (y ∈ (Metric.ball x' R)ᶜ) ↔ (x' - y ∈ {u : ℂ | R ≤ ‖u‖}) := by
        rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, Set.mem_ofPred_eq, dist_comm,
          Complex.dist_eq]
      by_cases h : y ∈ (Metric.ball x' R)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]
    rw [hsub, lintegral_sub_left_eq_self
      (fun u => {u : ℂ | R ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ q') u) x']
    rw [lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable)]
    exact hlint
  -- Per-point liminf bound (Hölder `Lᵖ`-continuity in the function argument).
  have hLiminfPt : ∀ (R : ℝ), 0 < R → ∀ (x' : ℂ) {f : ℂ → ℂ} {gg : ℕ → ℂ → ℂ},
      MemLp f p volume → (∀ n, MemLp (gg n) p volume) →
      Tendsto (fun n => eLpNorm (f - gg n) p volume) atTop (𝓝 0) →
      ‖czOperator beurlingKernel R f x'‖ₑ
        ≤ liminf (fun n => ‖czOperator beurlingKernel R (gg n) x'‖ₑ) atTop := by
    intro R hR x' f gg hf hgmem htend
    set C := eLpNorm
      (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) p' volume with hCdef
    have hbd : ∀ n, ‖czOperator beurlingKernel R f x'‖ₑ
        ≤ ‖czOperator beurlingKernel R (gg n) x'‖ₑ + C * eLpNorm (f - gg n) p volume := by
      intro n
      have hsub : ‖czOperator beurlingKernel R f x' - czOperator beurlingKernel R (gg n) x'‖ₑ
          ≤ C * eLpNorm (f - gg n) p volume := by
        rw [← czOperator_beurling_sub_Lp hp1 hp_top hR x' hf (hgmem n)]
        exact hHolderPt R hR x' (hf.sub (hgmem n))
      calc ‖czOperator beurlingKernel R f x'‖ₑ
          ≤ ‖czOperator beurlingKernel R (gg n) x'‖ₑ
            + ‖czOperator beurlingKernel R f x' - czOperator beurlingKernel R (gg n) x'‖ₑ := by
              rw [add_comm]
              exact le_trans (by rw [sub_add_cancel]) (enorm_add_le _ _)
        _ ≤ _ := by gcongr
    have hCne : C ≠ ⊤ := by rw [hCdef]; exact (hkermem x' R hR).2.ne
    have hC0 : Tendsto (fun n => C * eLpNorm (f - gg n) p volume) atTop (𝓝 0) := by
      simpa using (ENNReal.Tendsto.const_mul htend (Or.inr hCne))
    calc ‖czOperator beurlingKernel R f x'‖ₑ
        ≤ liminf (fun n => ‖czOperator beurlingKernel R (gg n) x'‖ₑ
            + C * eLpNorm (f - gg n) p volume) atTop :=
          le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall hbd)
      _ = liminf (fun n => ‖czOperator beurlingKernel R (gg n) x'‖ₑ) atTop :=
          ENNReal.liminf_add_of_right_tendsto_zero hC0 _
  refine ⟨C₀, fun g hg => ?_⟩
  -- Smooth compactly-supported `Lᵖ`-approximating sequence `gₙ → g`.
  have hp_top' : p ≠ ⊤ := hp_top
  choose gg hggc hggsmooth hggle using fun n : ℕ =>
    hg.exist_eLpNorm_sub_le hp_top' hp1' (ε := 1/(n+1)) (by positivity)
  have hggmem : ∀ n, MemLp (gg n) p volume := fun n =>
    (hggsmooth n).continuous.memLp_of_hasCompactSupport (hggc n)
  have hggBFS : ∀ n, BoundedFiniteSupport (gg n) volume := fun n =>
    boundedFiniteSupport_of_contDiff (hggsmooth n) (hggc n)
  have htend : Tendsto (fun n => eLpNorm (g - gg n) p volume) atTop (𝓝 0) := by
    have hto0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1))) atTop (𝓝 0) := by
      rw [show (0:ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      refine ENNReal.tendsto_ofReal (Tendsto.div_atTop tendsto_const_nhds ?_)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto0
      (fun n => zero_le) hggle
  -- Per-point: `simpleNTO 0 g x ≤ liminf (simpleNTO 0 gₙ x)`.
  have hsup : ∀ x, simpleNontangentialOperator beurlingKernel 0 g x
      ≤ liminf (fun n => simpleNontangentialOperator beurlingKernel 0 (gg n) x) atTop := by
    intro x
    unfold simpleNontangentialOperator
    refine iSup_le (fun R => iSup_le (fun hR => iSup_le (fun x' => iSup_le (fun hx' => ?_))))
    refine le_trans (hLiminfPt R hR x' hg hggmem htend) ?_
    refine liminf_le_liminf (Eventually.of_forall (fun n => ?_))
    exact le_iSup_of_le R (le_iSup_of_le hR (le_iSup_of_le x' (le_iSup_of_le hx' (le_refl _))))
  -- BFS bound on each `gₙ`.
  have hggbd : ∀ n, eLpNorm (simpleNontangentialOperator beurlingKernel 0 (gg n)) p volume
      ≤ (C₀ : ℝ≥0∞) * eLpNorm (gg n) p volume := fun n => hBFS0 (gg n) (hggBFS n)
  -- `‖gₙ‖_p → ‖g‖_p`.
  have htnorm : Tendsto (fun n => (C₀ : ℝ≥0∞) * eLpNorm (gg n) p volume) atTop
      (𝓝 ((C₀ : ℝ≥0∞) * eLpNorm g p volume)) := by
    have hgnorm : Tendsto (fun n => eLpNorm (gg n) p volume) atTop (𝓝 (eLpNorm g p volume)) := by
      set L := eLpNorm g p volume with hL
      set d := fun n => eLpNorm (g - gg n) p volume with hd
      have hupper : ∀ n, eLpNorm (gg n) p volume ≤ L + d n := by
        intro n
        have h : eLpNorm (gg n) p volume ≤ eLpNorm g p volume + eLpNorm (gg n - g) p volume := by
          calc eLpNorm (gg n) p volume = eLpNorm (g + (gg n - g)) p volume := by
                congr 1; funext y; simp
            _ ≤ eLpNorm g p volume + eLpNorm (gg n - g) p volume :=
                eLpNorm_add_le hg.aestronglyMeasurable ((hggmem n).sub hg).aestronglyMeasurable hp1'
        rw [hL, hd]
        rwa [show eLpNorm (gg n - g) p volume = eLpNorm (g - gg n) p volume from by
          rw [← eLpNorm_neg]; congr 1; funext y; simp] at h
      have hlower : ∀ n, L - d n ≤ eLpNorm (gg n) p volume := by
        intro n
        rw [tsub_le_iff_right]
        calc L = eLpNorm ((gg n) + (g - gg n)) p volume := by rw [hL]; congr 1; funext y; simp
          _ ≤ eLpNorm (gg n) p volume + eLpNorm (g - gg n) p volume :=
              eLpNorm_add_le (hggmem n).aestronglyMeasurable
                (hg.sub (hggmem n)).aestronglyMeasurable hp1'
      have hupper' : Tendsto (fun n => L + d n) atTop (𝓝 L) := by
        simpa using tendsto_const_nhds.add htend
      have hlower' : Tendsto (fun n => L - d n) atTop (𝓝 L) := by
        simpa using (ENNReal.Tendsto.sub (a := L) (b := 0) tendsto_const_nhds htend
          (Or.inr (by simp)))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower' hupper' hlower hupper
    refine ENNReal.Tendsto.const_mul hgnorm ?_
    right; exact ENNReal.coe_ne_top
  -- Fatou on the `Lᵖ` lintegral.
  have hp_pos : (0:ℝ) < p.toReal :=
    ENNReal.toReal_pos (by rintro rfl; exact absurd hp1 (by simp)) hp_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by rintro rfl; exact absurd hp1 (by simp)) hp_top]
  simp only [one_div]
  have hmono : ∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 g x‖ₑ ^ p.toReal
      ≤ liminf (fun n => ∫⁻ x,
        ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal) atTop := by
    have hpowliminf : ∀ (u : ℕ → ℝ≥0∞),
        liminf (fun n => (u n) ^ p.toReal) atTop = (liminf u atTop) ^ p.toReal := by
      intro u
      have hmono' : Monotone (fun x : ℝ≥0∞ => x ^ p.toReal) :=
        fun a b h => ENNReal.rpow_le_rpow h hp_pos.le
      exact (hmono'.map_liminf_of_continuousAt u (ENNReal.continuous_rpow_const).continuousAt).symm
    have hle : ∀ x, ‖simpleNontangentialOperator beurlingKernel 0 g x‖ₑ ^ p.toReal
        ≤ liminf (fun n =>
          ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal) atTop := by
      intro x
      simp_rw [enorm_eq_self]
      rw [hpowliminf]
      gcongr
      exact hsup x
    refine le_trans (lintegral_mono hle) ?_
    refine lintegral_liminf_le (fun n => ?_)
    exact (lowerSemicontinuous_simpleNontangentialOperator.measurable).enorm.pow_const _
  calc (∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 g x‖ₑ ^ p.toReal) ^ (p.toReal)⁻¹
      ≤ (liminf (fun n => ∫⁻ x,
          ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal) atTop)
            ^ (p.toReal)⁻¹ := by gcongr
    _ = liminf (fun n => (∫⁻ x,
          ‖simpleNontangentialOperator beurlingKernel 0 (gg n) x‖ₑ ^ p.toReal)
            ^ (p.toReal)⁻¹) atTop := by
        have hmono2 : Monotone (fun x : ℝ≥0∞ => x ^ (p.toReal)⁻¹) :=
          fun a b h => ENNReal.rpow_le_rpow h (by positivity)
        exact hmono2.map_liminf_of_continuousAt _ (ENNReal.continuous_rpow_const).continuousAt
    _ = liminf (fun n => eLpNorm (simpleNontangentialOperator beurlingKernel 0 (gg n)) p volume)
          atTop := by
        congr 1; funext n
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by rintro rfl; exact absurd hp1 (by simp))
          hp_top]
        simp only [one_div]
    _ ≤ liminf (fun n => (C₀ : ℝ≥0∞) * eLpNorm (gg n) p volume) atTop :=
        liminf_le_liminf (Eventually.of_forall hggbd)
    _ = (C₀ : ℝ≥0∞) * eLpNorm g p volume := htnorm.liminf_eq

/-- **A.e. existence of the principal-value limit on `Lᵖ`** (`1 < p < 2`): for
`f ∈ Lᵖ` the truncations `czOperator beurlingKernel r f z` converge as `r → 0⁺`
for a.e. `z`. The oscillation argument (smooth `Lᵖ` density `MemLp.exist_eLpNorm_sub_le`
+ the maximal-`Lᵖ` bound via Markov–Chebyshev) replicates the `L²` proof. -/
lemma czOperator_beurling_ae_tendsto_Lp {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2)
    {f : ℂ → ℂ} (hf : MemLp f p volume) :
    ∀ᵐ z ∂volume, ∃ L, Filter.Tendsto (fun r => czOperator beurlingKernel r f z)
      (𝓝[>] (0:ℝ)) (𝓝 L) := by
  have hp_top : p ≠ ⊤ := (lt_trans hp2 (by norm_num : (2:ℝ≥0∞) < ⊤)).ne_top
  have hp1' : (1 : ℝ≥0∞) ≤ p := hp1.le
  have hp_pos : p ≠ 0 := by rintro rfl; exact absurd hp1 (by simp)
  -- Inline helper: oscillation control by the maximal operator (the `Lᵖ` version of
  -- `edist_czOperator_oscillation`, using `czOperator_beurling_sub_Lp`).
  have edist_osc : ∀ {ν : ℂ → ℂ}, MemLp ν p volume → ∀ (z : ℂ) {r₁ r₂ : ℝ}, 0 < r₁ → 0 < r₂ →
      edist (czOperator beurlingKernel r₁ f z) (czOperator beurlingKernel r₂ f z)
        ≤ edist (czOperator beurlingKernel r₁ ν z) (czOperator beurlingKernel r₂ ν z)
          + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
    intro ν hν z r₁ r₂ hr₁ hr₂
    have hd1 : czOperator beurlingKernel r₁ f z - czOperator beurlingKernel r₁ ν z
        = czOperator beurlingKernel r₁ (f - ν) z :=
      (czOperator_beurling_sub_Lp hp1 hp_top hr₁ z hf hν).symm
    have hd2 : czOperator beurlingKernel r₂ f z - czOperator beurlingKernel r₂ ν z
        = czOperator beurlingKernel r₂ (f - ν) z :=
      (czOperator_beurling_sub_Lp hp1 hp_top hr₂ z hf hν).symm
    set Sf1 := czOperator beurlingKernel r₁ f z
    set Sf2 := czOperator beurlingKernel r₂ f z
    set Sn1 := czOperator beurlingKernel r₁ ν z
    set Sn2 := czOperator beurlingKernel r₂ ν z
    have hb1 : edist Sf1 Sn1 ≤ simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
      rw [edist_eq_enorm_sub, hd1]; exact enorm_czOperator_le_simpleNontangential hr₁ (f - ν) z
    have hb2 : edist Sn2 Sf2 ≤ simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
      rw [edist_comm, edist_eq_enorm_sub, hd2]
      exact enorm_czOperator_le_simpleNontangential hr₂ (f - ν) z
    calc edist Sf1 Sf2 ≤ edist Sf1 Sn1 + edist Sn1 Sn2 + edist Sn2 Sf2 := by
          refine le_trans (edist_triangle Sf1 Sn2 Sf2) ?_
          gcongr
          exact edist_triangle Sf1 Sn1 Sn2
      _ = edist Sn1 Sn2 + (edist Sf1 Sn1 + edist Sn2 Sf2) := by ring
      _ ≤ edist Sn1 Sn2 + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
          gcongr; rw [two_mul]; gcongr
  -- Inline helper: per-point Cauchy from smooth convergence + small maximal value
  -- (the `Lᵖ` version of `eventually_edist_lt_of_smooth_conv`).
  have edist_lt_of_conv : ∀ {ν : ℂ → ℂ}, MemLp ν p volume → ∀ (z : ℂ) {a : ℝ≥0∞}, 0 < a →
      (∃ L, Tendsto (fun r => czOperator beurlingKernel r ν z) (𝓝[>] (0:ℝ)) (𝓝 L)) →
      2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z < a / 2 →
      ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel p.1 f z) (czOperator beurlingKernel p.2 f z) < a := by
    intro ν hν z a ha hconv hsmall
    obtain ⟨L, hL⟩ := hconv
    have hνcauchy : ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel q.1 ν z) (czOperator beurlingKernel q.2 ν z) < a / 2 := by
      have hmap : Tendsto (fun q : ℝ × ℝ =>
          (czOperator beurlingKernel q.1 ν z, czOperator beurlingKernel q.2 ν z))
          ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) (𝓝 (L, L)) :=
        (hL.comp tendsto_fst).prodMk_nhds (hL.comp tendsto_snd)
      have ht : Tendsto (fun q : ℝ × ℝ =>
          edist (czOperator beurlingKernel q.1 ν z) (czOperator beurlingKernel q.2 ν z))
          ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) (𝓝 (edist L L)) :=
        (continuous_edist.tendsto _).comp hmap
      rw [edist_self] at ht
      exact ht (Iio_mem_nhds (ENNReal.half_pos (ne_of_gt ha)))
    have hpos : ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)), 0 < q.1 ∧ 0 < q.2 := by
      rw [eventually_prod_iff]
      refine ⟨fun r => 0 < r, ?_, fun r => 0 < r, ?_, fun {r₁} h1 {r₂} h2 => ⟨h1, h2⟩⟩
      · exact eventually_mem_of_tendsto_nhdsWithin tendsto_id |>.mono (fun x hx => hx)
      · exact eventually_mem_of_tendsto_nhdsWithin tendsto_id |>.mono (fun x hx => hx)
    filter_upwards [hνcauchy, hpos] with q hq hqpos
    obtain ⟨hq1, hq2⟩ := hqpos
    calc edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z)
        ≤ edist (czOperator beurlingKernel q.1 ν z) (czOperator beurlingKernel q.2 ν z)
          + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z :=
          edist_osc hν z hq1 hq2
      _ < a / 2 + a / 2 := ENNReal.add_lt_add hq hsmall
      _ = a := ENNReal.add_halves a
  -- The smooth `Lᵖ`-dense sequence (inline version of `exists_contDiff_seq_tendsto_L2`).
  choose g hgc hgsmooth hgle using fun n : ℕ =>
    hf.exist_eLpNorm_sub_le hp_top hp1' (ε := 1/(n+1)) (by positivity)
  have hg : ∀ n, MemLp (g n) p volume := fun n =>
    (hgsmooth n).continuous.memLp_of_hasCompactSupport (hgc n)
  have htend : Tendsto (fun n => eLpNorm (f - g n) p volume) atTop (𝓝 0) := by
    have hto0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1))) atTop (𝓝 0) := by
      rw [show (0:ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      refine ENNReal.tendsto_ofReal (Tendsto.div_atTop tendsto_const_nhds ?_)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto0
      (fun n => zero_le) hgle
  -- The maximal-`Lᵖ` Chebyshev bound (inline version of `volume_simpleNontangential_ge_le`).
  obtain ⟨C, hC⟩ := exists_eLpNorm_simpleNontangential_beurling_Lp hp1 hp2
  have vol_ge : ∀ {h : ℂ → ℂ}, MemLp h p volume → ∀ {a : ℝ≥0∞}, a ≠ 0 → a ≠ ⊤ →
      volume {z | a ≤ simpleNontangentialOperator beurlingKernel 0 h z}
        ≤ a⁻¹ ^ p.toReal * ((C : ℝ≥0∞) * eLpNorm h p volume) ^ p.toReal := by
    intro h hh a hane hatop
    have hcheb := meas_ge_le_mul_pow_eLpNorm_enorm volume hp_pos hp_top
      (f := simpleNontangentialOperator beurlingKernel 0 h)
      aestronglyMeasurable_simpleNontangentialOperator (ε := a) hane (fun heq => absurd heq hatop)
    refine le_trans hcheb (mul_le_mul' (le_refl (a⁻¹ ^ p.toReal)) ?_)
    exact ENNReal.rpow_le_rpow (hC h hh) (by positivity)
  -- Inline version of `volume_oscillation_set_eq_zero`.
  have osc_null : ∀ {a : ℝ≥0∞}, 0 < a → a ≠ ⊤ →
      volume {z | ¬ ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z) < a} = 0 := by
    intro a ha ha'
    set b := a / 4 with hbdef
    have hbpos : 0 < b := ENNReal.div_pos (ne_of_gt ha) (by norm_num)
    have hbne : b ≠ 0 := ne_of_gt hbpos
    have hbtop : b ≠ ⊤ := (ENNReal.div_lt_top ha' (by norm_num)).ne
    set B := {z | ¬ ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
        edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z) < a}
      with hBdef
    have hsubset : ∀ n, B ⊆ {z | b ≤ simpleNontangentialOperator beurlingKernel 0 (f - g n) z} := by
      intro n z hz
      by_contra hlt
      rw [Set.mem_ofPred_eq, not_le] at hlt
      apply hz
      refine edist_lt_of_conv (hg n) z ha
        ⟨_, czOperator_beurling_tendsto_neg_pi ((hgsmooth n).of_le (by exact_mod_cast le_top))
          (hgc n) z⟩ ?_
      rw [hbdef] at hlt
      calc 2 * simpleNontangentialOperator beurlingKernel 0 (f - g n) z
          < 2 * (a / 4) := by gcongr; exact (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
        _ = a / 2 := by
            rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, mul_comm (2:ℝ≥0∞) a, mul_assoc]
            congr 1
            rw [show (4:ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
              ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    have hmeas : ∀ n, volume B
        ≤ b⁻¹ ^ p.toReal * ((C : ℝ≥0∞) * eLpNorm (f - g n) p volume) ^ p.toReal :=
      fun n => le_trans (measure_mono (hsubset n)) (vol_ge (hf.sub (hg n)) hbne hbtop)
    have hto0 : Tendsto
        (fun n => b⁻¹ ^ p.toReal * ((C : ℝ≥0∞) * eLpNorm (f - g n) p volume) ^ p.toReal)
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => (C : ℝ≥0∞) * eLpNorm (f - g n) p volume) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul htend (Or.inr ENNReal.coe_ne_top)
      have h2 : Tendsto (fun n => ((C : ℝ≥0∞) * eLpNorm (f - g n) p volume) ^ p.toReal) atTop
          (𝓝 0) := by
        have h := (ENNReal.continuous_rpow_const (y := p.toReal)).continuousAt.tendsto.comp h1
        rw [show ((0:ℝ≥0∞) ^ p.toReal) = 0 by
          rw [ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_pos hp_top)]] at h
        exact h
      have hbinv : b⁻¹ ^ p.toReal ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.inv_ne_top.mpr hbne)
      have h3 := ENNReal.Tendsto.const_mul (a := b⁻¹ ^ p.toReal) h2 (Or.inr hbinv)
      rw [mul_zero] at h3
      exact h3
    exact le_antisymm (ge_of_tendsto hto0 (Eventually.of_forall hmeas)) (zero_le)
  -- Assemble: union over the levels `1/(k+1)`, then `tendsto_of_cauchy_edist`.
  set Bk := fun k : ℕ => {z | ¬ ∀ᶠ q in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
      edist (czOperator beurlingKernel q.1 f z) (czOperator beurlingKernel q.2 f z)
        < 1/((k:ℝ≥0∞)+1)} with hBk
  have hBknull : ∀ k, volume (Bk k) = 0 := by
    intro k
    apply osc_null
    · apply ENNReal.div_pos one_ne_zero
      exact (ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top k, ENNReal.one_lt_top⟩).ne
    · apply ENNReal.div_ne_top ENNReal.one_ne_top
      have hkp : (0:ℝ≥0∞) < (k:ℝ≥0∞)+1 := by positivity
      exact hkp.ne'
  have hunionnull : volume (⋃ k, Bk k) = 0 := measure_iUnion_null hBknull
  rw [ae_iff]
  refine measure_mono_null ?_ hunionnull
  intro z hz
  rw [Set.mem_ofPred_eq] at hz
  rw [Set.mem_iUnion]
  by_contra hnot
  push Not at hnot
  apply hz
  apply tendsto_of_cauchy_edist
  intro ε hε
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hε)
  have hmem := hnot k
  simp only [hBk, Set.mem_ofPred_eq, not_not] at hmem
  refine hmem.mono (fun q hq => lt_of_lt_of_le hq ?_)
  rw [one_div]
  calc ((k:ℝ≥0∞)+1)⁻¹ ≤ ((k:ℝ≥0∞))⁻¹ := ENNReal.inv_le_inv.mpr le_self_add
    _ ≤ ε := le_of_lt hk

/-! ## `Lᵖ` boundedness: passage to the Beurling transform

A.e. convergence of the truncations on `Lᵖ` (`1 < p < 2`), then Fatou, transfers
the uniform truncation bound to `beurling`. The `p = 2` case is the isometry; the
`p > 2` case is duality (the Beurling kernel is symmetric). -/

/-- **A.e. convergence of the truncations on `Lᵖ`**, `1 < p < 2`: the truncated
Beurling integrals converge a.e. as `r → 0⁺` to `-π · beurling f`. Extends the
`L²` result (`czOperator_beurling_ae_tendsto_neg_pi`) via the maximal-operator
weak-(1,1) bound and the `L¹ + L²` decomposition of `Lᵖ`. -/
lemma czOperator_beurling_ae_tendsto_neg_pi_Lp {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2)
    {f : ℂ → ℂ} (hf : MemLp f p volume) :
    ∀ᵐ z ∂volume, Filter.Tendsto (fun r => czOperator beurlingKernel r f z) (𝓝[>] (0:ℝ))
      (𝓝 (-(π : ℂ) * beurling f z)) := by
  filter_upwards [czOperator_beurling_ae_tendsto_Lp hp1 hp2 hf] with z hz
  obtain ⟨L, hL⟩ := hz
  have hlim : limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r f z) = L := by
    apply Filter.Tendsto.limUnder_eq
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r f z
        = czOperator beurlingKernel r f z := fun r => rfl
    simpa only [hcz] using hL
  have hb : beurling f z = -(1 / (π : ℂ)) * L := by rw [beurling, hlim]
  have hval : -(π:ℂ) * beurling f z = L := by
    rw [hb]; have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [hval]; exact hL

/-- **`Lᵖ` bound for the Beurling transform, `1 < p < 2`.** The uniform-in-`r`
truncation bound (`eLpNorm_czOperator_beurling_Lp`) passes to the limit by Fatou
(`eLpNorm_le_of_ae_tendsto` along `r → 0⁺`), using the a.e. convergence
`czOperator_beurling_ae_tendsto_neg_pi_Lp`. -/
lemma eLpNorm_beurling_Lp_le {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2) {f : ℂ → ℂ}
    (hf : MemLp f p volume) :
    eLpNorm (beurling f) p volume
      ≤ (ENNReal.ofReal (1 / π) * (beurlingTruncLpConst p : ℝ≥0∞)) * eLpNorm f p volume := by
  have hπpos : (0:ℝ) < 1 / π := by positivity
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set C : ℝ≥0∞ := (ENNReal.ofReal (1 / π) * (beurlingTruncLpConst p : ℝ≥0∞)) * eLpNorm f p volume
    with hCdef
  -- The scaled family `F r = (-(1/π)) • czOperator beurlingKernel r f`.
  set F : ℝ → ℂ → ℂ := fun r => (-(1 / π : ℂ)) • czOperator beurlingKernel r f with hFdef
  -- Bound `eLpNorm (F r) p ≤ C` for `r > 0`.
  have hbound : ∀ᶠ r in 𝓝[>] (0:ℝ), eLpNorm (F r) p volume ≤ C := by
    refine eventually_nhdsWithin_of_forall (fun r hr => ?_)
    rw [Set.mem_Ioi] at hr
    rw [hFdef, eLpNorm_const_smul]
    have hnorm : ‖(-(1 / π : ℂ))‖ₑ = ENNReal.ofReal (1 / π) := by
      rw [← ofReal_norm, norm_neg]
      congr 1
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hnorm, hCdef, mul_assoc]
    exact mul_le_mul' (le_refl _) (eLpNorm_czOperator_beurling_Lp hp1 hp2 hr hf)
  -- Measurability of each `F r`.
  have hmeas : ∀ r, AEStronglyMeasurable (F r) volume := by
    intro r
    rw [hFdef]
    exact (aestronglyMeasurable_czOperator_beurling' hf.aestronglyMeasurable).const_smul _
  -- a.e. tendsto: scale the a.e. limit by `-(1/π)`.
  have hae : ∀ᵐ z ∂volume, Tendsto (fun r => F r z) (𝓝[>] (0:ℝ)) (𝓝 (beurling f z)) := by
    filter_upwards [czOperator_beurling_ae_tendsto_neg_pi_Lp hp1 hp2 hf] with z hz
    have hscaled := hz.const_mul (-(1 / π : ℂ))
    have heq : -(1 / π : ℂ) * (-(π : ℂ) * beurling f z) = beurling f z := by
      field_simp
    rw [heq] at hscaled
    have hFz : (fun r => F r z) = fun r => -(1 / π : ℂ) * czOperator beurlingKernel r f z := by
      funext r; rw [hFdef]; simp [Pi.smul_apply, smul_eq_mul]
    rw [hFz]; exact hscaled
  exact Lp.eLpNorm_le_of_ae_tendsto hbound hmeas hae

/-- The Beurling kernel is symmetric: `K(z, ζ) = K(ζ, z)` (an even power of
`z - ζ`). This is the algebraic input that makes the Beurling transform its own
transpose, used for the `p > 2` range by duality. -/
lemma beurlingKernel_symm (z ζ : ℂ) : beurlingKernel z ζ = beurlingKernel ζ z := by
  unfold beurlingKernel
  rw [zpow_neg, zpow_neg, zpow_two, zpow_two,
    show (z - ζ) * (z - ζ) = (ζ - z) * (ζ - z) by ring]

end NoWanderingDomains
