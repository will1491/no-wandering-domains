/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.MRMT.NeumannSeries.PrincipalSolution
import NoWanderingDomains.QC.LengthArea.Mollification

/-!
# Smooth Calderón–Zygmund calculus and the `C¹` criterion

On `C∞₀` data the Beurling transform is `S u = P(∂u)` and both `P` and `S`
preserve smoothness; a continuous function with continuous weak gradient is
genuinely `C¹`; and the Cauchy transform of an `Lᵖ` function supported in a ball
obeys the uniform potential bound.

* `beurling_eq_cauchyTransform_dz`, `contDiff_cauchyTransform`,
  `contDiff_beurling` — the smooth Calderón–Zygmund calculus.
* `contDiffOne_of_continuous_hasWeakGradient` — the `C¹` criterion.
* `norm_cauchyTransform_le_of_memLp_support` — the uniform potential bound.
-/

open MeasureTheory Complex Filter
open scoped ContDiff ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **`S = P ∘ ∂` on smooth data.** For a smooth compactly supported `u` the
Beurling transform is the Cauchy transform of the holomorphic Wirtinger
derivative: `S u = P(∂u)`. Companion of the proved bridge
`beurling_eq_dz_cauchyTransform` (`S u = ∂(P u)`): both sides are continuous,
vanish at infinity, and have the same `∂̄` (namely `∂u`, by Cauchy–Pompeiu and
the commutation of `∂̄` with `P`), so the difference is entire and vanishes by
Liouville. -/
theorem beurling_eq_cauchyTransform_dz {u : ℂ → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (z : ℂ) :
    beurling u z = cauchyTransform (fun ζ => dz u ζ) z := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by exact_mod_cast le_top)
  -- Both sides are `-(1/π)` times an integral: the Beurling side is the
  -- principal-value limit of the truncated singular integrals, and the
  -- extracted Tendsto `czOperator_beurling_tendsto_smooth` identifies that
  -- limit with the Cauchy-transform integral of `∂u`.
  rw [beurling, cauchyTransform]
  congr 1
  refine Filter.Tendsto.limUnder_eq ?_
  have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r u z
      = czOperator beurlingKernel r u z := fun r => rfl
  simpa only [hcz] using czOperator_beurling_tendsto_smooth hu1 huc z

/-- **The Cauchy transform preserves smoothness.** For smooth compactly
supported `u` the potential `P u` is smooth: `P u` is the convolution of `u`
with the locally integrable kernel `-1/(π·)`, so all derivatives fall on `u`
(`HasCompactSupport.hasFDerivAt_convolution_left`, iterated). -/
theorem contDiff_cauchyTransform {u : ℂ → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    ContDiff ℝ ∞ (cauchyTransform u) := by
  set L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ with hL
  set k : ℂ → ℂ := fun w => -w⁻¹ with hk
  -- The kernel `-w⁻¹` is locally integrable: in polar coordinates the Jacobian
  -- factor `r` cancels the singularity `r⁻¹`, leaving a finite box integral.
  have hk_loc : LocallyIntegrable k volume := by
    rw [hk]
    apply LocallyIntegrable.neg
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
    apply MeasureTheory.IntegrableOn.mono_set _ hR₀
    rw [IntegrableOn]
    refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
      ← Complex.lintegral_comp_polarCoord_symm]
    set box : ℝ × ℝ → ENNReal :=
      (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
        (fun _ => (1 : ENNReal)) with hbox
    have hbound : ∀ q ∈ polarCoord.target,
        ENNReal.ofReal q.1 • (Metric.closedBall (0 : ℂ) R₀).indicator
          (fun w : ℂ => ‖w⁻¹‖ₑ) (Complex.polarCoord.symm q) ≤ box q := by
      intro q hq
      simp only [hbox]
      rw [polarCoord_target, Set.mem_prod] at hq
      obtain ⟨hq1, hq2⟩ := hq
      simp only [Set.mem_Ioi] at hq1
      by_cases hmem : Complex.polarCoord.symm q ∈ Metric.closedBall (0 : ℂ) R₀
      · rw [Set.indicator_of_mem hmem]
        have hnorm : ‖Complex.polarCoord.symm q‖ = q.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hq1]
        have hsymm_ne : Complex.polarCoord.symm q ≠ 0 := by
          rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hq1
        rw [enorm_inv hsymm_ne]
        have henorm : ‖Complex.polarCoord.symm q‖ₑ = ENNReal.ofReal q.1 := by
          rw [← ofReal_norm, hnorm]
        rw [henorm, smul_eq_mul,
          ENNReal.mul_inv_cancel
            (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq1)
            ENNReal.ofReal_lt_top.ne]
        have hqR : q.1 ≤ R₀ := by
          rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem; exact hmem
        rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hq1, hqR⟩, hq2⟩)]
      · rw [Set.indicator_of_notMem hmem]; simp
    calc
      ∫⁻ q in polarCoord.target, ENNReal.ofReal q.1 •
          (Metric.closedBall (0 : ℂ) R₀).indicator
            (fun w : ℂ => ‖w⁻¹‖ₑ) (Complex.polarCoord.symm q)
          ≤ ∫⁻ q in polarCoord.target, box q :=
            setLIntegral_mono (measurable_const.indicator
              (measurableSet_Ioc.prod measurableSet_Ioo)) hbound
      _ ≤ ∫⁻ q, box q := setLIntegral_le_lintegral _ _
      _ = volume (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
            rw [hbox, lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]
            simp
      _ < ⊤ := by
            rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc,
              Real.volume_Ioo]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  -- `P u` is `-(1/π)` times the convolution of `u` with the kernel.
  have hCT : cauchyTransform u
      = fun w => (-(1 / (Real.pi : ℂ))) • (MeasureTheory.convolution u k L volume) w := by
    funext w
    rw [cauchyTransform, MeasureTheory.convolution_def, smul_eq_mul]
    congr 1
    apply integral_congr_ae (ae_of_all _ fun ζ => ?_)
    rw [hL, ContinuousLinearMap.mul_apply']
    change u ζ / (ζ - w) = u ζ * -(w - ζ)⁻¹
    have hflip : -(w - ζ)⁻¹ = (ζ - w)⁻¹ := by rw [← neg_sub ζ w, inv_neg, neg_neg]
    rw [hflip, div_eq_mul_inv]
  rw [hCT]
  exact (huc.contDiff_convolution_left L hu hk_loc).const_smul _

/-- **The Beurling transform preserves smoothness.** For smooth compactly
supported `u` the singular integral `S u` is smooth: by
`beurling_eq_cauchyTransform_dz`, `S u = P(∂u)` with `∂u` smooth and compactly
supported, and `P` preserves smoothness (`contDiff_cauchyTransform`). -/
theorem contDiff_beurling {u : ℂ → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    ContDiff ℝ ∞ (beurling u) := by
  -- `S u = P(∂u)` pointwise.
  have hbeq : beurling u = cauchyTransform (fun ζ => dz u ζ) := by
    funext z; exact beurling_eq_cauchyTransform_dz hu huc z
  -- `∂u` is a fixed continuous-linear expression in `fderiv ℝ u`.
  have hcomp : (fun ζ => dz u ζ)
      = (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
        ∘ (fun ζ => fderiv ℝ u ζ) := by
    funext ζ; rfl
  -- Smoothness of `∂u`.
  have hfderiv_cinf : ContDiff ℝ ∞ (fun ζ => fderiv ℝ u ζ) :=
    hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hΦ_cd : ContDiff ℝ ∞
      (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I)) := by
    have hΦ_lin : (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
        = (fun D : ℂ →L[ℝ] ℂ =>
            (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) D
              - Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I D)) := by
      funext D; simp [ContinuousLinearMap.apply_apply, smul_eq_mul]
    rw [hΦ_lin]
    exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff).sub
      ((ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff.const_smul Complex.I)).const_smul _
  have hdzu_cinf : ContDiff ℝ ∞ (fun ζ => dz u ζ) := by
    rw [hcomp]; exact hΦ_cd.comp hfderiv_cinf
  -- Compact support of `∂u`.
  have hdzu_cs : HasCompactSupport (fun ζ => dz u ζ) := by
    have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ u ζ) := huc.fderiv (𝕜 := ℝ)
    rw [hcomp]; exact hfderiv_cs.comp_left (by simp)
  -- Conclude via the smoothness of the Cauchy transform.
  rw [hbeq]
  exact contDiff_cauchyTransform hdzu_cinf hdzu_cs

/-! ## The `C¹` criterion from continuous weak gradients -/

/-- **Continuous weak gradient ⇒ `C¹`.** A continuous function on `ℂ` whose
weak gradient components are continuous is continuously differentiable, and the
weak partials are the genuine directional derivatives everywhere. Classical
mollification argument: `f ∗ φ_ε → f` locally uniformly and
`∂(f ∗ φ_ε) = gx ∗ φ_ε → gx` locally uniformly, so the limit `f` is `C¹` with
the asserted differential. -/
theorem contDiffOne_of_continuous_hasWeakGradient {f gx gy : ℂ → ℂ}
    (hf : Continuous f) (hgrad : HasWeakGradient gx gy f Set.univ)
    (hgx : Continuous gx) (hgy : Continuous gy) :
    ContDiff ℝ 1 f ∧
      ∀ z : ℂ, (fderiv ℝ f z) 1 = gx z ∧ (fderiv ℝ f z) Complex.I = gy z := by
  classical
  obtain ⟨hwgx, hwgy⟩ := hgrad
  have hfloc : LocallyIntegrable f := hf.locallyIntegrable
  have hgxLI : LocallyIntegrable gx := hgx.locallyIntegrable
  have hgyLI : LocallyIntegrable gy := hgy.locallyIntegrable
  -- ===== Mollifier sequence `φ n` with `rOut → 0`. =====
  set φ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    { rIn := 1 / (n + 2), rOut := 2 / (n + 2),
      rIn_pos := by positivity,
      rIn_lt_rOut := by
        rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num } with hφdef
  have hφrout : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [hφdef] using this
  -- The normed bumps and the three mollifications.
  set ρ : ℕ → ℂ → ℝ := fun n => (φ n).normed volume with hρ
  have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
    (φ n).contDiff_normed (n := ⊤)
  have hρsupp : ∀ n, HasCompactSupport (ρ n) := fun n => (φ n).hasCompactSupport_normed
  set fn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) f
    (ContinuousLinearMap.lsmul ℝ ℝ) volume with hfn
  set cx : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) gx
    (ContinuousLinearMap.lsmul ℝ ℝ) volume with hcx
  set cy : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) gy
    (ContinuousLinearMap.lsmul ℝ ℝ) volume with hcy
  -- Directional derivatives of the mollification are the mollified weak partials.
  have hA1x : ∀ n z, (fderiv ℝ (fn n) z) (1 : ℂ) = cx n z := fun n z =>
    fderiv_convolution_normed_apply_eq hwgx hfloc hgxLI (hρsm n) (hρsupp n) z
  have hA1y : ∀ n z, (fderiv ℝ (fn n) z) Complex.I = cy n z := fun n z =>
    fderiv_convolution_normed_apply_eq hwgy hfloc hgyLI (hρsm n) (hρsupp n) z
  -- Each mollification is smooth.
  have hfn_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fn n) := fun n =>
    (hρsupp n).contDiff_convolution_left _ (hρsm n) hfloc
  -- Two `ℝ`-linear CLMs on `ℂ` agreeing at `1` and `I` are equal.
  have hCLMext : ∀ T S : ℂ →L[ℝ] ℂ, T 1 = S 1 → T Complex.I = S Complex.I → T = S := by
    intro T S h1 hI
    ext w
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
    rw [hw]
    simp only [map_add, map_smul, h1, hI]
  -- Basis values of the assembled derivative candidates.
  have hA_apply : ∀ a b : ℂ,
      (Complex.reCLM.smulRight a + Complex.imCLM.smulRight b) (1 : ℂ) = a
      ∧ (Complex.reCLM.smulRight a + Complex.imCLM.smulRight b) Complex.I = b := by
    intro a b
    constructor
    · simp [ContinuousLinearMap.smulRight_apply]
    · simp [ContinuousLinearMap.smulRight_apply]
  -- Each mollification has the assembled derivative everywhere.
  have hfnFD : ∀ n z, HasFDerivAt (fn n)
      (Complex.reCLM.smulRight (cx n z) + Complex.imCLM.smulRight (cy n z)) z := by
    intro n z
    have hd : DifferentiableAt ℝ (fn n) z :=
      ((hfn_smooth n).differentiable (by simp)).differentiableAt
    have hEq : fderiv ℝ (fn n) z
        = Complex.reCLM.smulRight (cx n z) + Complex.imCLM.smulRight (cy n z) := by
      refine hCLMext _ _ ?_ ?_
      · rw [hA1x n z, (hA_apply (cx n z) (cy n z)).1]
      · rw [hA1y n z, (hA_apply (cx n z) (cy n z)).2]
    exact hEq ▸ hd.hasFDerivAt
  -- ===== Mollifications of a continuous map converge locally uniformly. =====
  have hconvTLU : ∀ (g : ℂ → ℂ), Continuous g →
      TendstoLocallyUniformly (fun n => MeasureTheory.convolution (ρ n) g
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) g atTop := by
    intro g hgcont
    refine tendstoLocallyUniformly_of_forall_exists_nhds (fun x => ?_)
    refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
    have hUC : UniformContinuousOn g (Metric.closedBall x 2) :=
      (isCompact_closedBall x 2).uniformContinuousOn_of_continuous hgcont.continuousOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by positivity
    obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) hε2
    have hev : ∀ᶠ n in atTop, (φ n).rOut < min δ 1 := by
      have := hφrout.eventually (eventually_lt_nhds (show (0 : ℝ) < min δ 1 by positivity))
      filter_upwards [this] with n hn using hn
    filter_upwards [hev] with n hn z hz
    have hrout_le_one : (φ n).rOut ≤ 1 := (lt_of_lt_of_le hn (min_le_right δ 1)).le
    have hrout_le_δ : (φ n).rOut ≤ δ := (lt_of_lt_of_le hn (min_le_left δ 1)).le
    have hsupp : Function.support (ρ n) ⊆ Metric.ball (0 : ℂ) (φ n).rOut := by
      rw [hρ, (φ n).support_normed_eq]
    have hnf : ∀ y, 0 ≤ ρ n y := fun y => (φ n).nonneg_normed y
    have hintf : ∫ y, ρ n y ∂volume = 1 := (φ n).integral_normed
    have hclose : ∀ y ∈ Metric.ball z (φ n).rOut, dist (g y) (g z) ≤ ε / 2 := by
      intro y hy
      have hzmem : z ∈ Metric.closedBall x 2 :=
        Metric.closedBall_subset_closedBall (by norm_num) hz
      rw [Metric.mem_ball] at hy
      have hymem : y ∈ Metric.closedBall x 2 := by
        rw [Metric.mem_closedBall] at hz ⊢
        calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
          _ ≤ (φ n).rOut + 1 := by gcongr
          _ ≤ 1 + 1 := by gcongr
          _ = 2 := by norm_num
      exact (hδ y hymem z hzmem (hy.trans_le hrout_le_δ)).le
    calc dist (g z) (MeasureTheory.convolution (ρ n) g (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
        = dist (MeasureTheory.convolution (ρ n) g (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
            (g z) := dist_comm _ _
      _ ≤ ε / 2 := dist_convolution_le hε2.le hsupp hnf hintf
            hgcont.aestronglyMeasurable hclose
      _ < ε := by linarith
  have hcxTLU : TendstoLocallyUniformly cx gx atTop := by
    have := hconvTLU gx hgx; rwa [← hcx] at this
  have hcyTLU : TendstoLocallyUniformly cy gy atTop := by
    have := hconvTLU gy hgy; rwa [← hcy] at this
  -- ===== The assembled derivatives converge locally uniformly. =====
  have hTLU : TendstoLocallyUniformlyOn
      (fun n z => Complex.reCLM.smulRight (cx n z) + Complex.imCLM.smulRight (cy n z))
      (fun z => Complex.reCLM.smulRight (gx z) + Complex.imCLM.smulRight (gy z))
      atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    have hx := tendstoLocallyUniformly_iff_forall_isCompact.mp hcxTLU K hK
    have hy := tendstoLocallyUniformly_iff_forall_isCompact.mp hcyTLU K hK
    rw [Metric.tendstoUniformlyOn_iff] at hx hy ⊢
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by positivity
    filter_upwards [hx (ε / 2) hε2, hy (ε / 2) hε2] with n hnx hny z hz
    have h1 := hnx z hz
    have h2 := hny z hz
    rw [dist_eq_norm] at h1 h2
    change dist (Complex.reCLM.smulRight (gx z) + Complex.imCLM.smulRight (gy z))
      (Complex.reCLM.smulRight (cx n z) + Complex.imCLM.smulRight (cy n z)) < ε
    rw [dist_eq_norm]
    have hdiff : (Complex.reCLM.smulRight (gx z) + Complex.imCLM.smulRight (gy z))
        - (Complex.reCLM.smulRight (cx n z) + Complex.imCLM.smulRight (cy n z))
        = Complex.reCLM.smulRight (gx z - cx n z)
          + Complex.imCLM.smulRight (gy z - cy n z) := by
      ext w
      simp only [sub_apply, add_apply,
        ContinuousLinearMap.smulRight_apply, smul_sub]
      abel
    rw [hdiff]
    have hbound : ‖Complex.reCLM.smulRight (gx z - cx n z)
          + Complex.imCLM.smulRight (gy z - cy n z)‖
        ≤ ‖gx z - cx n z‖ + ‖gy z - cy n z‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
      simp only [add_apply, ContinuousLinearMap.smulRight_apply,
        Complex.reCLM_apply, Complex.imCLM_apply]
      calc ‖w.re • (gx z - cx n z) + w.im • (gy z - cy n z)‖
          ≤ ‖w.re • (gx z - cx n z)‖ + ‖w.im • (gy z - cy n z)‖ := norm_add_le _ _
        _ = |w.re| * ‖gx z - cx n z‖ + |w.im| * ‖gy z - cy n z‖ := by
            rw [Complex.real_smul, Complex.real_smul, norm_mul, norm_mul,
              Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ ‖w‖ * ‖gx z - cx n z‖ + ‖w‖ * ‖gy z - cy n z‖ := by
            gcongr
            · exact Complex.abs_re_le_norm w
            · exact Complex.abs_im_le_norm w
        _ = (‖gx z - cx n z‖ + ‖gy z - cy n z‖) * ‖w‖ := by ring
    calc ‖Complex.reCLM.smulRight (gx z - cx n z)
          + Complex.imCLM.smulRight (gy z - cy n z)‖
        ≤ ‖gx z - cx n z‖ + ‖gy z - cy n z‖ := hbound
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := by ring
  -- ===== Pointwise convergence of the mollifications. =====
  have hptw : ∀ x : ℂ, Tendsto (fun n => fn n x) atTop (𝓝 (f x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous hφrout hf x
  -- ===== The uniform-limit theorem: `f` has the assembled derivative everywhere. =====
  have hFD : ∀ z : ℂ, HasFDerivAt f
      (Complex.reCLM.smulRight (gx z) + Complex.imCLM.smulRight (gy z)) z := fun z =>
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hTLU
      (fun n x _ => hfnFD n x) (fun x _ => hptw x) (Set.mem_univ z)
  have hfeq : ∀ z : ℂ, fderiv ℝ f z
      = Complex.reCLM.smulRight (gx z) + Complex.imCLM.smulRight (gy z) := fun z =>
    (hFD z).fderiv
  -- ===== Assembly. =====
  have hLcont : Continuous (fun z : ℂ =>
      Complex.reCLM.smulRight (gx z) + Complex.imCLM.smulRight (gy z)) := by
    have h1 : Continuous (fun z : ℂ => Complex.reCLM.smulRight (gx z)) :=
      (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM).continuous.comp hgx
    have h2 : Continuous (fun z : ℂ => Complex.imCLM.smulRight (gy z)) :=
      (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).continuous.comp hgy
    exact h1.add h2
  constructor
  · rw [contDiff_one_iff_fderiv]
    refine ⟨fun z => (hFD z).differentiableAt, ?_⟩
    have heq : fderiv ℝ f = fun z =>
        Complex.reCLM.smulRight (gx z) + Complex.imCLM.smulRight (gy z) := funext hfeq
    rw [heq]
    exact hLcont
  · intro z
    rw [hfeq z]
    exact ⟨(hA_apply (gx z) (gy z)).1, (hA_apply (gx z) (gy z)).2⟩

/-- **Uniform sup bound for the Cauchy transform of compactly vanishing `Lᵖ`
fields** (`p > 2`): a constant `C = C(p, R)` with
`‖P h‖_∞ ≤ C·‖h‖ₚ` for every field `h ∈ Lᵖ` vanishing outside the ball of
radius `R`. Hölder's inequality against the kernel: the conjugate exponent
satisfies `q < 2`, so `sup_z ∫_{B_R} |ζ − z|^{-q} dA < ∞`. The constant is
uniform over the family — the source of every uniformity in the
Ahlfors–Bers limit argument. -/
theorem norm_cauchyTransform_le_of_memLp_support {p : ℝ≥0∞} {R : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℂ → ℂ, MemLp h p volume →
      (∀ z : ℂ, R < ‖z‖ → h z = 0) →
      ∀ z : ℂ, ‖cauchyTransform h z‖ ≤ C * (eLpNorm h p volume).toReal := by
  -- ===== Exponent bookkeeping: `pr > 2`, conjugate `qr ∈ (1,2)` =====
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
  -- ===== The uniform (in the pole) kernel constant over the support ball =====
  set B : Set ℂ := Metric.closedBall (0:ℂ) R with hB_def
  have hBmeas : MeasurableSet B := measurableSet_closedBall
  set K₀ : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi / (2 - qr) * 1 ^ (2 - qr)) + volume B
    with hK₀_def
  have hK₀top : K₀ ≠ ⊤ := by
    rw [hK₀_def]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ?_⟩
    rw [hB_def]
    exact ((isCompact_closedBall _ _).measure_lt_top).ne
  -- pointwise domination of the shifted kernel: near the pole use the ball kernel,
  -- away from it the kernel is bounded by `1`
  have hptw : ∀ z ζ : ℂ, ‖(ζ - z)⁻¹‖ₑ ^ qr
      ≤ (Metric.ball z 1).indicator (fun ξ => ‖(ξ - z)⁻¹‖ₑ ^ qr) ζ + 1 := by
    intro z ζ
    by_cases hζ : ζ ∈ Metric.ball z 1
    · rw [Set.indicator_of_mem hζ]
      exact le_self_add
    · rw [Set.indicator_of_notMem hζ, zero_add]
      have h1 : (1:ℝ) ≤ ‖ζ - z‖ := by
        rw [Metric.mem_ball, dist_eq_norm, not_lt] at hζ
        exact hζ
      have hle : ‖(ζ - z)⁻¹‖ₑ ≤ 1 := by
        rw [← ofReal_norm, norm_inv]
        exact ENNReal.ofReal_le_one.mpr (inv_le_one_of_one_le₀ h1)
      calc ‖(ζ - z)⁻¹‖ₑ ^ qr ≤ 1 ^ qr := ENNReal.rpow_le_rpow hle hqr0.le
        _ = 1 := ENNReal.one_rpow _
  -- the uniform kernel mass bound over the support ball
  have hker : ∀ z : ℂ, ∫⁻ ζ in B, ‖(ζ - z)⁻¹‖ₑ ^ qr ≤ K₀ := by
    intro z
    calc ∫⁻ ζ in B, ‖(ζ - z)⁻¹‖ₑ ^ qr
        ≤ ∫⁻ ζ in B, ((Metric.ball z 1).indicator (fun ξ => ‖(ξ - z)⁻¹‖ₑ ^ qr) ζ + 1) :=
          lintegral_mono fun ζ => hptw z ζ
      _ = (∫⁻ ζ in B, (Metric.ball z 1).indicator (fun ξ => ‖(ξ - z)⁻¹‖ₑ ^ qr) ζ)
            + ∫⁻ _ in B, 1 :=
          lintegral_add_right' _ aemeasurable_const
      _ = (∫⁻ ζ in Metric.ball z 1 ∩ B, ‖(ζ - z)⁻¹‖ₑ ^ qr) + volume B := by
          rw [lintegral_indicator measurableSet_ball,
            Measure.restrict_restrict measurableSet_ball, setLIntegral_one]
      _ ≤ (∫⁻ ζ in Metric.ball z 1, ‖(ζ - z)⁻¹‖ₑ ^ qr) + volume B :=
          add_le_add (lintegral_mono_set Set.inter_subset_left) le_rfl
      _ ≤ ENNReal.ofReal (2 * Real.pi / (2 - qr) * 1 ^ (2 - qr)) + volume B :=
          add_le_add (hballE z 1 one_pos) le_rfl
      _ = K₀ := hK₀_def.symm
  set Kc : ℝ≥0∞ := K₀ ^ (1/qr) with hKc_def
  have hKctop : Kc ≠ ⊤ := by
    rw [hKc_def]
    exact ENNReal.rpow_ne_top_of_nonneg (le_of_lt (one_div_pos.mpr hqr0)) hK₀top
  -- ===== Conclusion =====
  refine ⟨1 / Real.pi * Kc.toReal,
    mul_nonneg (by positivity) ENNReal.toReal_nonneg, ?_⟩
  intro h hh hsupp z
  set N : ℝ≥0∞ := eLpNorm h p volume with hN_def
  have hN_ne : N ≠ ⊤ := hh.2.ne
  -- the integrand vanishes off the support ball
  have hrestrict : ∫⁻ ζ, ‖h ζ / (ζ - z)‖ₑ = ∫⁻ ζ in B, ‖h ζ / (ζ - z)‖ₑ := by
    rw [← lintegral_indicator hBmeas]
    apply lintegral_congr
    intro ζ
    by_cases hζ : ζ ∈ B
    · rw [Set.indicator_of_mem hζ]
    · rw [Set.indicator_of_notMem hζ]
      have hζR : R < ‖ζ‖ := by
        rw [hB_def] at hζ
        simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hζ
      rw [hsupp ζ hζR, zero_div]
      simp
  -- Hölder pairing against the kernel on the support ball
  have hHolder : ∫⁻ ζ in B, ‖h ζ‖ₑ * ‖(ζ - z)⁻¹‖ₑ ≤ N * Kc := by
    have hNle : (∫⁻ ζ in B, ‖h ζ‖ₑ ^ pr) ^ (1/pr) ≤ N := by
      rw [hN_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp']
      exact ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _)
        (le_of_lt (one_div_pos.mpr hpr0))
    calc ∫⁻ ζ in B, ‖h ζ‖ₑ * ‖(ζ - z)⁻¹‖ₑ
        ≤ (∫⁻ ζ in B, ‖h ζ‖ₑ ^ pr) ^ (1/pr)
            * (∫⁻ ζ in B, ‖(ζ - z)⁻¹‖ₑ ^ qr) ^ (1/qr) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq (hh.1.restrict.enorm)
            (((measurable_id.sub_const z).inv).enorm.aemeasurable.restrict)
      _ ≤ N * Kc := by
          refine mul_le_mul' hNle ?_
          rw [hKc_def]
          exact ENNReal.rpow_le_rpow (hker z) (le_of_lt (one_div_pos.mpr hqr0))
  -- main estimate at the level of the integral
  have hmain : ‖∫ ζ, h ζ / (ζ - z)‖ₑ ≤ N * Kc := by
    calc ‖∫ ζ, h ζ / (ζ - z)‖ₑ
        ≤ ∫⁻ ζ, ‖h ζ / (ζ - z)‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ ζ in B, ‖h ζ / (ζ - z)‖ₑ := hrestrict
      _ = ∫⁻ ζ in B, ‖h ζ‖ₑ * ‖(ζ - z)⁻¹‖ₑ := lintegral_congr fun ζ => by
          rw [div_eq_mul_inv, enorm_mul]
      _ ≤ N * Kc := hHolder
  -- pass to the real inequality
  have hnn : (0:ℝ) ≤ N.toReal * Kc.toReal :=
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hX : ‖∫ ζ, h ζ / (ζ - z)‖ ≤ N.toReal * Kc.toReal := by
    have h2 := hmain
    rw [show N * Kc = ENNReal.ofReal (N.toReal * Kc.toReal) by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hN_ne,
          ENNReal.ofReal_toReal hKctop],
      ← ofReal_norm] at h2
    exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h2
  -- unfold the Cauchy transform and conclude
  have hCT : ‖cauchyTransform h z‖ = 1/Real.pi * ‖∫ ζ, h ζ / (ζ - z)‖ := by
    rw [cauchyTransform, norm_mul]
    congr 1
    rw [norm_neg, norm_div, norm_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hCT]
  calc 1/Real.pi * ‖∫ ζ, h ζ / (ζ - z)‖
      ≤ 1/Real.pi * (N.toReal * Kc.toReal) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = 1 / Real.pi * Kc.toReal * N.toReal := by ring

end NoWanderingDomains
