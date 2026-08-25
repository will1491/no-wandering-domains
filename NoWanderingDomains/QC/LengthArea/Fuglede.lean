/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.LengthArea.Mollification

/-!
# Length–area: the Fuglede chain rule and the exceptional-modulus theorem

Continues `LengthArea.Mollification`. The `GoodCurve` predicate, the mollified upper-gradient
inequality along curves, the Fuglede chain rule for a.e.-good curves (`chainRule_good_of_finite`),
and the conclusion that the exceptional (non-good / non-AC-image) curves form a zero-modulus
family (`IsQCAnalytic.chainRule_exceptional_modulus_zero`).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace NoWanderingDomains

/-- A curve `γ` is **good** for `f` when some sequence of normed `ContDiffBump`
mollifiers with outer radius tending to `0` makes the arc-length line integral along
`γ` of the difference between the differential of the mollification and the
differential of `f` tend to `0`. By the quasiconformal Fuglede theorem
(`IsQCAnalytic.curveModulus_notGoodCurve_zero`) the non-good curves of any family form
a zero-modulus subfamily, so the upper-gradient inequality (which holds for good
curves) holds modulus-almost-everywhere. -/
def GoodCurve (f : ℂ → ℂ) (γ : ℝ → ℂ) : Prop :=
  ∃ φ : ℕ → ContDiffBump (0 : ℂ),
    Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => arcLengthLineIntegral
      (fun z => (‖fderiv ℝ (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) f
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) z - fderiv ℝ f z‖₊ : ℝ≥0∞)) γ)
      Filter.atTop (nhds 0)

/-- **(Mollified-differential trace convergence along a good curve.)**
For a curve `γ` along which the mollified differential converges in arc-length to the
differential of `f` (`hgood_φ`), the mollified arc-length density integral is
eventually within `ε` of the target `∫ fdNormMulDeriv f γ`:
`∫_{uIoc x y} ‖fderiv ℝ f_n (γ t)‖ ‖deriv γ t‖ ≤ ∫ fdNormMulDeriv f γ + ε` eventually.

Proof: the reverse triangle inequality bounds the excess by the arc-length integral of
the differential difference `‖fderiv ℝ f_n − fderiv ℝ f‖`, which tends to `0` by
`hgood_φ`.

De-gated: only continuity of `f` is consumed (the mollification of a continuous locally
integrable map is `C¹`, and the trace convergence is the hypothesis `hgood_φ` itself). -/
theorem fderiv_mollified_lineIntegral_le {f : ℂ → ℂ}
    (hfcont : Continuous f) {γ : ℝ → ℂ} (hγcont : Continuous γ)
    (_hγac : AbsolutelyContinuousOnInterval γ 0 1)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (x y : ℝ) (hxy : Set.uIcc x y ⊆ Set.Icc (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) (φ : ℕ → ContDiffBump (0 : ℂ))
    (_hφrout : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0))
    (hgood_φ : Filter.Tendsto (fun n => arcLengthLineIntegral
      (fun z => (‖fderiv ℝ (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) f
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) z - fderiv ℝ f z‖₊ : ℝ≥0∞)) γ)
      Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop,
      (∫ t in Set.uIoc x y,
          ‖fderiv ℝ (MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) f
            (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) (γ t)‖ * ‖deriv γ t‖) ≤
        (∫ t in Set.uIoc x y, fdNormMulDeriv f γ t) + ε := by
  -- Abbreviations: `fn n := ρ_n ⋆ f` the mollifications,
  -- `dn n t := fderiv (fn n) (γ t) − fderiv f (γ t)`.
  set fn : ℕ → ℂ → ℂ :=
    fun n => MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) f
      (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume with hfndef
  have hfloc : MeasureTheory.LocallyIntegrable f := hfcont.locallyIntegrable
  -- Each `fn n` is `C¹`, hence `fderiv ℝ (fn n)` is continuous.
  have hfn_contDiff : ∀ n, ContDiff ℝ 1 (fn n) := fun n =>
    ((φ n).hasCompactSupport_normed).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (n := 1) (φ n).contDiff_normed hfloc
  have hfn_fderiv_cont : ∀ n, Continuous (fun z => fderiv ℝ (fn n) z) := fun n =>
    (hfn_contDiff n).continuous_fderiv (by norm_num)
  -- Abbreviation: the `ℝ≥0∞` arc-length integral of the differential difference along `γ`.
  set A : ℕ → ℝ≥0∞ := fun n => arcLengthLineIntegral
      (fun z => (‖fderiv ℝ (fn n) z - fderiv ℝ f z‖₊ : ℝ≥0∞)) γ with hA
  -- The `.toReal` of these tend to `0`, since they tend to `0` in `ℝ≥0∞`.
  have hA_to_zero : Filter.Tendsto (fun n => (A n).toReal) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto A Filter.atTop (nhds 0) := hgood_φ
    simpa using! (ENNReal.tendsto_toReal (by simp)).comp this
  -- Eventually `(A n).toReal ≤ ε`.
  have hAev : ∀ᶠ n in Filter.atTop, (A n).toReal ≤ ε :=
    hA_to_zero.eventually (ge_mem_nhds hε)
  -- Eventually `A n ≠ ∞` (since `A → 0` in `ℝ≥0∞`, `A n` is eventually `< 1`).
  have hAne : ∀ᶠ n in Filter.atTop, A n ≠ ∞ := by
    have hlt : ∀ᶠ n in Filter.atTop, A n < 1 :=
      (hgood_φ : Filter.Tendsto A Filter.atTop (nhds 0)).eventually
        (eventually_lt_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
    filter_upwards [hlt] with n hn using ne_top_of_lt (hn.trans_le le_top)
  filter_upwards [hAev, hAne] with n hAn hAnetop
  -- `g t := ‖fderiv (fn n) (γ t)‖ * ‖deriv γ t‖` and `h t := fdNormMulDeriv f γ t`.
  -- `deriv γ` is measurable; `‖deriv γ ·‖` measurable.
  have hderiv_meas : Measurable (fun t => ‖deriv γ t‖) := (measurable_deriv γ).norm
  -- The `fderiv f` piece is integrable on `uIcc x y ⊇ uIoc x y`.
  have hh_int_uIcc : IntegrableOn (fdNormMulDeriv f γ) (Set.uIcc x y) := by
    have hmeas : Measurable (fdNormMulDeriv f γ) := by
      have h1 : Measurable (fun t => ‖fderiv ℝ f (γ t)‖) :=
        ((measurable_fderiv ℝ f).norm).comp hγcont.measurable
      simpa only [fdNormMulDeriv] using! h1.mul hderiv_meas
    refine IntegrableOn.mono_set ?_ hxy
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lt_top_iff_ne_top]
    have hptf : ∀ t, ‖fdNormMulDeriv f γ t‖ₑ
        = (‖fderiv ℝ f (γ t)‖₊ : ℝ≥0∞) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
      intro t
      simp only [fdNormMulDeriv, enorm_eq_nnnorm, nnnorm_mul, nnnorm_norm, ENNReal.coe_mul]
    calc ∫⁻ t in Set.Icc (0:ℝ) 1, ‖fdNormMulDeriv f γ t‖ₑ
        = ∫⁻ t in Set.Icc (0:ℝ) 1,
            (‖fderiv ℝ f (γ t)‖₊ : ℝ≥0∞) * (‖deriv γ t‖₊ : ℝ≥0∞) := by simp_rw [hptf]
      _ = arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ := by
            rw [arcLengthLineIntegral]
      _ ≠ ∞ := hfin
  have hh_int : IntegrableOn (fdNormMulDeriv f γ) (Set.uIoc x y) :=
    hh_int_uIcc.mono_set Set.Ioc_subset_Icc_self
  -- The mollified piece is continuous, hence measurable.
  have hfn_density_meas : Measurable
      (fun t => ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖) :=
    (((hfn_fderiv_cont n).comp hγcont).norm.measurable).mul hderiv_meas
  -- The differential-difference density `dterm t := ‖dn t‖ * ‖γ' t‖`.
  have hdmeas : Measurable
      (fun t => ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖) := by
    have hfn_meas : Measurable (fun t => fderiv ℝ (fn n) (γ t)) :=
      ((hfn_fderiv_cont n).measurable).comp hγcont.measurable
    have hf_meas : Measurable (fun t => fderiv ℝ f (γ t)) :=
      (measurable_fderiv ℝ f).comp hγcont.measurable
    have h1 : Measurable (fun t => ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖) :=
      (hfn_meas.sub hf_meas).norm
    exact h1.mul hderiv_meas
  -- Its enorm at `t` equals the `ℝ≥0∞`-density factor.
  have hpt : ∀ t,
      ‖‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖‖ₑ
        = (‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖₊ : ℝ≥0∞) *
          (‖deriv γ t‖₊ : ℝ≥0∞) := by
    intro t
    rw [enorm_eq_nnnorm, nnnorm_mul, ENNReal.coe_mul, nnnorm_norm, nnnorm_norm]
  -- The lower integral of its enorm over `uIoc x y` is `≤ A n`.
  have hAeq : A n = ∫⁻ t in Set.Icc (0:ℝ) 1,
      (‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖₊ : ℝ≥0∞) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
    simp only [hA, arcLengthLineIntegral]
  have hle : (∫⁻ t in Set.uIoc x y,
      ‖‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖‖ₑ) ≤ A n := by
    simp_rw [hpt]
    rw [hAeq]
    exact MeasureTheory.lintegral_mono_set (Set.Ioc_subset_Icc_self.trans hxy)
  -- The excess density is integrable on `uIoc x y` (finite enorm integral `≤ A n < ∞`).
  have hdterm_int : IntegrableOn
      (fun t => ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖)
      (Set.uIoc x y) := by
    refine ⟨hdmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lt_top_iff_ne_top]
    exact ne_top_of_le_ne_top hAnetop hle
  -- The reverse-triangle pointwise bound `g ≤ h + dterm`.
  have hbound : ∀ t, ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖ ≤
      fdNormMulDeriv f γ t +
        ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖ := by
    intro t
    have htri : ‖fderiv ℝ (fn n) (γ t)‖ ≤
        ‖fderiv ℝ f (γ t)‖ + ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ := by
      have := norm_le_norm_add_norm_sub' (fderiv ℝ (fn n) (γ t)) (fderiv ℝ f (γ t))
      simpa [norm_sub_rev] using this
    have hnn : (0 : ℝ) ≤ ‖deriv γ t‖ := norm_nonneg _
    calc ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖
        ≤ (‖fderiv ℝ f (γ t)‖ +
            ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖) * ‖deriv γ t‖ :=
          mul_le_mul_of_nonneg_right htri hnn
      _ = fdNormMulDeriv f γ t +
            ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖ := by
          rw [fdNormMulDeriv, add_mul]
  -- The mollified density is integrable, dominated by `h + dterm`.
  have hg_int : IntegrableOn
      (fun t => ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖) (Set.uIoc x y) := by
    refine Integrable.mono' (hh_int.add hdterm_int) hfn_density_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hbound t
  -- The arc-length excess term `Rₙ := ∫ ‖dn‖‖γ'‖`.
  set R : ℝ := ∫ t in Set.uIoc x y,
      ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖ with hR
  -- Bound `R ≤ (A n).toReal`.
  have hR_le : R ≤ (A n).toReal := by
    rw [hR]
    -- For nonneg integrand, `∫ ≤ (∫⁻ ‖·‖ₑ).toReal`.
    have hnn : 0 ≤ᵐ[volume.restrict (Set.uIoc x y)]
        (fun t => ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖) :=
      Filter.Eventually.of_forall (fun t => by positivity)
    have hstep : (∫ t in Set.uIoc x y,
        ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖) ≤
        (∫⁻ t in Set.uIoc x y,
          ‖‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖‖ₑ).toReal := by
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn
        hdterm_int.aestronglyMeasurable]
      apply ENNReal.toReal_mono (by
        rw [← lt_top_iff_ne_top]; exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hAnetop))
      refine MeasureTheory.lintegral_mono (fun t => ?_)
      rw [← ofReal_norm, Real.norm_of_nonneg (by positivity)]
    refine hstep.trans ?_
    exact ENNReal.toReal_mono hAnetop hle
  -- Finally: `∫ ‖fderiv (fn n)(γ)‖‖γ'‖ ≤ ∫ fdNormMulDeriv f γ + R ≤ ∫ fdNormMulDeriv f γ + ε`.
  have hmain : (∫ t in Set.uIoc x y, ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖) ≤
      (∫ t in Set.uIoc x y, fdNormMulDeriv f γ t) + R := by
    rw [hR, ← MeasureTheory.integral_add hh_int hdterm_int]
    refine MeasureTheory.integral_mono hg_int (hh_int.add hdterm_int) (fun t => ?_)
    have htri : ‖fderiv ℝ (fn n) (γ t)‖ ≤
        ‖fderiv ℝ f (γ t)‖ + ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ := by
      have := norm_le_norm_add_norm_sub' (fderiv ℝ (fn n) (γ t)) (fderiv ℝ f (γ t))
      simpa [norm_sub_rev] using this
    have hnn : (0 : ℝ) ≤ ‖deriv γ t‖ := norm_nonneg _
    calc ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖
        ≤ (‖fderiv ℝ f (γ t)‖ +
            ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖) * ‖deriv γ t‖ :=
          mul_le_mul_of_nonneg_right htri hnn
      _ = fdNormMulDeriv f γ t +
            ‖fderiv ℝ (fn n) (γ t) - fderiv ℝ f (γ t)‖ * ‖deriv γ t‖ := by
          rw [fdNormMulDeriv, add_mul]
  calc (∫ t in Set.uIoc x y, ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖)
      ≤ (∫ t in Set.uIoc x y, fdNormMulDeriv f γ t) + R := hmain
    _ ≤ (∫ t in Set.uIoc x y, fdNormMulDeriv f γ t) + ε := by
        have := hR_le.trans hAn
        linarith

/-- **(Smooth approximant along the curve.)** For a quasiconformal `f`, an absolutely
continuous curve `γ` with finite gradient line integral, and any tolerance `ε > 0`,
there is a `C¹` function `g` that (i) approximates `f` at the two endpoints `γ x`,
`γ y` to within `ε`, and (ii) whose arc-length density integral along `γ` over
`uIoc x y` is within `ε` of the target `∫ fdNormMulDeriv f γ`.

The proof uses the mollification glue and `fderiv_mollified_lineIntegral_le`:
take `g = f_n = ρ_n ⋆ f` (`ρ_n` a normed `ContDiffBump` with `rOut → 0`); `f_n`
is `C¹` (`HasCompactSupport.contDiff_convolution_left`), part (i) is the pointwise
convergence `f_n (z) → f (z)`
(`ContDiffBump.convolution_tendsto_right_of_continuous`, `f` continuous), and part
(ii) is `fderiv_mollified_lineIntegral_le`. De-gated: only continuity of `f` is consumed. -/
theorem exists_contDiff_approx_along_curve {f : ℂ → ℂ}
    (hfcont : Continuous f) {γ : ℝ → ℂ} (hγcont : Continuous γ)
    (hγac : AbsolutelyContinuousOnInterval γ 0 1)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (x y : ℝ) (hxy : Set.uIcc x y ⊆ Set.Icc (0 : ℝ) 1) (hgood : GoodCurve f γ) :
    ∀ ε > (0 : ℝ), ∃ g : ℂ → ℂ, ContDiff ℝ 1 g ∧
      dist (f (γ x)) (g (γ x)) ≤ ε ∧ dist (f (γ y)) (g (γ y)) ≤ ε ∧
      (∫ t in Set.uIoc x y, ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖) ≤
        (∫ t in Set.uIoc x y, fdNormMulDeriv f γ t) + ε := by
  intro ε hε
  -- `f` is continuous and locally integrable.
  have hfloc : MeasureTheory.LocallyIntegrable f := hfcont.locallyIntegrable
  -- The good-curve mollifier sequence `φ n` of normed bumps with `rOut → 0`.
  obtain ⟨φ, hφrout, hgood_φ⟩ := hgood
  -- The mollified functions `f_n := (φ n).normed volume ⋆ f`, each `C^∞` hence `C¹`.
  set fn : ℕ → ℂ → ℂ :=
    fun n => MeasureTheory.convolution ((φ n).normed MeasureTheory.volume) f
      (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume with hfndef
  have hfn_contDiff : ∀ n, ContDiff ℝ 1 (fn n) := fun n =>
    ((φ n).hasCompactSupport_normed).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (n := 1) (φ n).contDiff_normed hfloc
  -- (i) Pointwise convergence `f_n (z) → f (z)` at any point, from continuity of `f`.
  have hfn_tendsto : ∀ z : ℂ, Filter.Tendsto (fun n => fn n z) Filter.atTop (nhds (f z)) :=
    fun z => ContDiffBump.convolution_tendsto_right_of_continuous hφrout hfcont z
  -- Pick `N` large enough that `f_N` is within `ε` of `f` at both endpoints, AND the
  -- density-integral bound holds within `ε`.  The density bound is the Fuglede core.
  have hfn_density : ∀ᶠ n in Filter.atTop,
      (∫ t in Set.uIoc x y, ‖fderiv ℝ (fn n) (γ t)‖ * ‖deriv γ t‖) ≤
        (∫ t in Set.uIoc x y, fdNormMulDeriv f γ t) + ε :=
    fderiv_mollified_lineIntegral_le hfcont hγcont hγac hfin x y hxy hε φ hφrout hgood_φ
  -- The endpoint convergences give eventual `ε`-closeness.
  have hev_close : ∀ z : ℂ, ∀ᶠ n in Filter.atTop, dist (f z) (fn n z) ≤ ε := by
    intro z
    have hd : Filter.Tendsto (fun n => dist (f z) (fn n z)) Filter.atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := f z)).dist (hfn_tendsto z)
      simpa using this
    have := (hd.eventually (ge_mem_nhds (show (0 : ℝ) < ε from hε)))
    filter_upwards [this] with n hn using hn
  have hxev := hev_close (γ x)
  have hyev := hev_close (γ y)
  -- Combine the three eventual conditions and extract a witness `N`.
  obtain ⟨N, hN⟩ := (hfn_density.and (hxev.and hyev)).exists
  exact ⟨fn N, hfn_contDiff N, hN.2.1, hN.2.2, hN.1⟩

/-- **(Fuglede upper-gradient inequality.)** For a quasiconformal `f` and an absolutely
continuous curve `γ` whose gradient line integral over `[0,1]` is finite, the distance
moved by `f ∘ γ` across a subinterval `uIoc x y ⊆ [0,1]` is bounded by the arc-length
integral of `‖fderiv ℝ f‖` over that subinterval.

The proof is the elementary `ε`-limit glue over the smooth approximant
`exists_contDiff_approx_along_curve`: applying the smooth upper-gradient bound
`dist_comp_le_setIntegral_of_contDiff` to the `C¹` approximant `g` and inserting it via
the triangle inequality
`dist (f (γ x)) (f (γ y)) ≤ dist (f (γ x)) (g (γ x)) + dist (g (γ x)) (g (γ y))
  + dist (g (γ y)) (f (γ y))`
bounds the LHS by `∫ fdNormMulDeriv f γ + 3ε` for every `ε > 0`; letting `ε → 0`
closes the inequality. The mollification setup, smooth chain-rule/FTC bound, and
ℂ-valued density integrability are supplied by the helpers above; the
trace-convergence core is `exists_contDiff_approx_along_curve`.

De-gated core: only continuity of `f` is consumed — the finite gradient line integral and the
mollified trace convergence are the hypotheses `hfin` and `hgood`. The `IsQCAnalytic` wrapper
is `fugledeUpperGradient` below. -/
theorem fugledeUpperGradient_of_continuous {f : ℂ → ℂ}
    (hfcont : Continuous f) {γ : ℝ → ℂ} (hγcont : Continuous γ)
    (hγac : AbsolutelyContinuousOnInterval γ 0 1)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (x y : ℝ) (hxy : Set.uIcc x y ⊆ Set.Icc (0 : ℝ) 1) (hgood : GoodCurve f γ) :
    dist ((f ∘ γ) x) ((f ∘ γ) y) ≤ ∫ t in Set.uIoc x y, fdNormMulDeriv f γ t := by
  -- It suffices to show `dist ≤ target + 3ε` for every `ε > 0`.
  rw [show (f ∘ γ) x = f (γ x) from rfl, show (f ∘ γ) y = f (γ y) from rfl]
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  -- Obtain the `C¹` approximant `g` for tolerance `ε / 3`.
  obtain ⟨g, hg_smooth, hgx, hgy, hg_int⟩ :=
    exists_contDiff_approx_along_curve hfcont hγcont hγac hfin x y hxy hgood (ε / 3)
      (by positivity)
  -- The proven smooth upper-gradient bound for `g`.
  have hsmooth := dist_comp_le_setIntegral_of_contDiff hg_smooth hγcont hγac x y hxy
  -- Triangle inequality: insert `g (γ x)`, `g (γ y)` between the `f`-endpoints.
  have htri : dist (f (γ x)) (f (γ y)) ≤
      dist (f (γ x)) (g (γ x)) + dist (g (γ x)) (g (γ y)) + dist (g (γ y)) (f (γ y)) := by
    have h1 : dist (f (γ x)) (f (γ y))
        ≤ dist (f (γ x)) (g (γ y)) + dist (g (γ y)) (f (γ y)) := dist_triangle _ _ _
    have h2 : dist (f (γ x)) (g (γ y))
        ≤ dist (f (γ x)) (g (γ x)) + dist (g (γ x)) (g (γ y)) := dist_triangle _ _ _
    linarith
  -- Chain the bounds: `dist (g (γ x)) (g (γ y)) ≤ ∫ density g`, then `hg_int`.
  have hgy' : dist (g (γ y)) (f (γ y)) ≤ ε / 3 := by rw [dist_comm]; exact hgy
  -- Combine all bounds linearly.
  have : (∫ t in Set.uIoc x y, ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖) ≤
      (∫ t in Set.uIoc x y, fdNormMulDeriv f γ t) + ε / 3 := hg_int
  linarith [htri, hgx, hgy', hsmooth, this]

/-- **(Fuglede upper-gradient inequality.)** `IsQCAnalytic` wrapper of
`fugledeUpperGradient_of_continuous` (only continuity of `f` is consumed). -/
theorem fugledeUpperGradient {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) {γ : ℝ → ℂ} (hγcont : Continuous γ)
    (hγac : AbsolutelyContinuousOnInterval γ 0 1)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (x y : ℝ) (hxy : Set.uIcc x y ⊆ Set.Icc (0 : ℝ) 1) (hgood : GoodCurve f γ) :
    dist ((f ∘ γ) x) ((f ∘ γ) y) ≤ ∫ t in Set.uIoc x y, fdNormMulDeriv f γ t :=
  fugledeUpperGradient_of_continuous hf.1.1.continuous hγcont hγac hfin x y hxy hgood

/-- **(Fuglede upper-gradient inequality, statement-fixed `[0,1]`-restricted form.)**
The distance moved by `f ∘ γ` across a subinterval `uIoc x y ⊆ [0,1]` is bounded by
the arc-length integral of `‖fderiv ℝ f‖` over that subinterval. The `[0,1]` guard
`hxy : uIcc x y ⊆ Icc 0 1` is essential and consumable: `hfin` only controls the
gradient line integral over `[0,1]`, and the downstream length–area assembly only
ever integrates along `[0,1]`. A thin wrapper over `fugledeUpperGradient_of_continuous`. -/
theorem dist_le_setIntegral_fderiv_norm_mul_deriv {f : ℂ → ℂ}
    (hfcont : Continuous f) {γ : ℝ → ℂ} (hγcont : Continuous γ)
    (hγac : AbsolutelyContinuousOnInterval γ 0 1)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (x y : ℝ) (hxy : Set.uIcc x y ⊆ Set.Icc (0 : ℝ) 1) (hgood : GoodCurve f γ) :
    dist ((f ∘ γ) x) ((f ∘ γ) y) ≤ ∫ t in Set.uIoc x y, fdNormMulDeriv f γ t :=
  fugledeUpperGradient_of_continuous hfcont hγcont hγac hfin x y hxy hgood

/-- **(Interval integrability of the density.)** The real
arc-length integrand `g t := ‖fderiv ℝ f (γ t)‖ · ‖deriv γ t‖` is integrable on
every compact interval `uIcc a c ⊆ [0,1]`.

With the `[0,1]` guard this is exactly the `ℝ`-valued content of `hfin`: `γ` is
continuous (it is AC on every interval), so `g` is measurable, and the lower
integral of its enorm over `[0,1]` equals
`arcLengthLineIntegral ‖fderiv ℝ f‖ γ`, which is finite by `hfin`. A nonnegative
measurable function with finite lower integral is integrable, and
`IntegrableOn.mono_set` restricts from `[0,1]` to `uIcc a c`. No hypothesis on `f`
beyond the finiteness `hfin` is consumed. -/
theorem integrableOn_fdNormMulDeriv_uIcc {f : ℂ → ℂ} {γ : ℝ → ℂ} (hγcont : Continuous γ)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (a c : ℝ) (huIcc : Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1) :
    IntegrableOn (fdNormMulDeriv f γ) (Set.uIcc a c) := by
  -- Measurability of the integrand.
  have hmeas : Measurable (fdNormMulDeriv f γ) := by
    have h1 : Measurable (fun t => ‖fderiv ℝ f (γ t)‖) :=
      ((measurable_fderiv ℝ f).norm).comp hγcont.measurable
    have h2 : Measurable (fun t => ‖deriv γ t‖) := (measurable_deriv γ).norm
    simpa only [fdNormMulDeriv] using! h1.mul h2
  -- Reduce `uIcc a c` to `Icc 0 1`.
  refine IntegrableOn.mono_set ?_ huIcc
  -- Build `Integrable` from AEStronglyMeasurable + HasFiniteIntegral.
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lt_top_iff_ne_top]
  -- The lintegral of the enorm equals the arc-length line integral of `hfin`.
  have hpt : ∀ t, ‖fdNormMulDeriv f γ t‖ₑ
      = (‖fderiv ℝ f (γ t)‖₊ : ℝ≥0∞) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
    intro t
    simp only [fdNormMulDeriv, enorm_eq_nnnorm, nnnorm_mul, nnnorm_norm,
      ENNReal.coe_mul]
  calc ∫⁻ t in Set.Icc (0:ℝ) 1, ‖fdNormMulDeriv f γ t‖ₑ
      = ∫⁻ t in Set.Icc (0:ℝ) 1,
          (‖fderiv ℝ f (γ t)‖₊ : ℝ≥0∞) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
        simp_rw [hpt]
    _ = arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ := by
        rw [arcLengthLineIntegral]
    _ ≠ ∞ := hfin

/-- **(Interval integrability of the density.)** `IsQCAnalytic`-flavoured wrapper of
`integrableOn_fdNormMulDeriv_uIcc`, kept for the pre-existing consumers; the quasiconformal
hypothesis is not consumed. -/
theorem integrableOn_fderiv_norm_mul_deriv_uIcc {f : ℂ → ℂ} {b : BeltramiCoeff}
    (_hf : IsQCAnalytic f b) {γ : ℝ → ℂ} (hγcont : Continuous γ)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (a c : ℝ) (huIcc : Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1) :
    IntegrableOn (fdNormMulDeriv f γ) (Set.uIcc a c) :=
  integrableOn_fdNormMulDeriv_uIcc hγcont hfin a c huIcc

/-- **(Fuglede length–area content.)** Absolute continuity of `f ∘ γ` on every
interval, given that the gradient line integral
`∫₀¹ ‖fderiv ℝ f (γ t)‖ ‖γ' t‖ dt` is finite and the curve `γ` is itself
absolutely continuous.

The genuine analytic core rests on two ingredients:
`dist_le_setIntegral_fderiv_norm_mul_deriv` (the upper-gradient inequality along
the curve — the mollification / `L¹`-trace step) and
`integrableOn_fdNormMulDeriv_uIcc` (interval integrability of the density).
On top of those, this proof is the elementary `ε`-`δ` glue: it mirrors Mathlib's
`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`, bounding the
distance-sum over a disjoint interval family by the set-integral of the density
over their union and using that the integral over a small-measure set is small
(`Integrable.tendsto_setIntegral_nhds_zero`). De-gated: only continuity of `f` is
consumed. -/
theorem absolutelyContinuous_comp_of_finite_lineIntegral {f : ℂ → ℂ}
    (hfcont : Continuous f) {γ : ℝ → ℂ} (hγcont : Continuous γ)
    (hγac : AbsolutelyContinuousOnInterval γ 0 1)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (hgood : GoodCurve f γ) :
    ∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
      AbsolutelyContinuousOnInterval (f ∘ γ) a c := by
  intro a c huIcc
  -- The density `g` and its integrability on `uIcc a c`.
  set g : ℝ → ℝ := fdNormMulDeriv f γ with hg
  have hgint : IntegrableOn g (Set.uIcc a c) :=
    integrableOn_fdNormMulDeriv_uIcc hγcont hfin a c huIcc
  -- `g` is nonnegative.
  have hgnonneg : ∀ t, 0 ≤ g t := fun t => by
    rw [hg, fdNormMulDeriv]; positivity
  -- Abbreviation for the union of the disjoint subintervals of a family `E`.
  set s : ℕ × (ℕ → ℝ × ℝ) → Set ℝ :=
    fun E => ⋃ i ∈ Finset.range E.1, Set.uIoc (E.2 i).1 (E.2 i).2 with hs
  -- The set-integrals of `g` over `s E`, restricted to `uIoc a c`, tend to `0`
  -- as the total length of `E` tends to `0` along `disjWithin a c`.
  have hgint' : Integrable g (volume.restrict (Set.uIoc a c)) := by
    have : IntegrableOn g (Set.uIoc a c) :=
      hgint.mono_set Set.Ioc_subset_Icc_self
    exact this
  have htend : Filter.Tendsto
      (fun E => ∫ t in s E, g t ∂(volume.restrict (Set.uIoc a c)))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a c)) (nhds 0) :=
    hgint'.tendsto_setIntegral_nhds_zero
      (AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero
        a c)
  -- Reduce to the `ε`-`δ` form via the `disjWithin` filter, mirroring Mathlib's
  -- `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`.
  rw [AbsolutelyContinuousOnInterval]
  refine squeeze_zero' (g := fun E =>
      ∫ t in s E, g t ∂(volume.restrict (Set.uIoc a c))) ?_ ?_ htend
  · -- The distance-sum is nonnegative.
    filter_upwards with E
    exact Finset.sum_nonneg (fun _ _ => dist_nonneg)
  · -- The distance-sum is bounded by the set-integral of `g`.
    have hmem : ∀ᶠ (E : ℕ × (ℕ → ℝ × ℝ)) in
        (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
          Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a c)),
        E ∈ AbsolutelyContinuousOnInterval.disjWithin a c :=
      Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall fun _ h => h)
    filter_upwards [hmem] with E hE
    obtain ⟨n, I⟩ := E
    -- Each subinterval `uIoc (I i).1 (I i).2 ⊆ uIoc a c`.
    have hsub : ∀ i ∈ Finset.range n,
        Set.uIoc (I i).1 (I i).2 ⊆ Set.uIoc a c :=
      fun i hi => AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hE
        (Finset.mem_range.mp hi)
    -- Each subinterval's *closed* hull `uIcc (I i).1 (I i).2 ⊆ Icc 0 1`: its endpoints
    -- lie in `uIcc a c ⊆ Icc 0 1` (from `disjWithin a c` membership and `huIcc`).
    have hsub01 : ∀ i ∈ Finset.range n,
        Set.uIcc (I i).1 (I i).2 ⊆ Set.Icc (0 : ℝ) 1 := by
      intro i hi
      obtain ⟨hp1, hp2⟩ := hE.1 i hi
      exact Set.uIcc_subset_Icc (huIcc hp1) (huIcc hp2)
    -- `g` is integrable on each subinterval (restricted to `uIoc a c`).
    have hgint_i : ∀ i ∈ Finset.range n,
        IntegrableOn g (Set.uIoc (I i).1 (I i).2) (volume.restrict (Set.uIoc a c)) := by
      intro i hi
      rw [IntegrableOn, Measure.restrict_restrict_of_subset (hsub i hi)]
      exact hgint.mono_set
        ((hsub i hi).trans Set.Ioc_subset_Icc_self)
    -- The disjointness of the subintervals (within `uIoc`).
    have hdisj : (↑(Finset.range n) : Set ℕ).PairwiseDisjoint
        (fun i => Set.uIoc (I i).1 (I i).2) := hE.2
    -- Measurability of each subinterval.
    have hmeas : ∀ i ∈ Finset.range n, MeasurableSet (Set.uIoc (I i).1 (I i).2) :=
      fun i _ => measurableSet_uIoc
    -- Bound each distance by the per-subinterval integral, then sum.
    calc ∑ i ∈ Finset.range n, dist ((f ∘ γ) (I i).1) ((f ∘ γ) (I i).2)
        ≤ ∑ i ∈ Finset.range n,
            ∫ t in Set.uIoc (I i).1 (I i).2, g t ∂(volume.restrict (Set.uIoc a c)) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          rw [Measure.restrict_restrict_of_subset (hsub i hi)]
          exact dist_le_setIntegral_fderiv_norm_mul_deriv hfcont hγcont hγac hfin (I i).1 (I i).2
            (hsub01 i hi) hgood
      _ = ∫ t in s (n, I), g t ∂(volume.restrict (Set.uIoc a c)) := by
          rw [hs]
          exact (integral_biUnion_finset (Finset.range n) hmeas (hdisj : Set.Pairwise _ _)
            hgint_i).symm

/-- **(Chain-rule clause.)** For a.e. `t ∈ [0,1]` with `deriv γ t ≠ 0`, the
composite `f ∘ γ` has derivative `(fderiv ℝ f (γ t)) (deriv γ t)` at `t`.

The single-point identity is `HasFDerivAt.comp_hasDerivAt`, which needs both
`HasFDerivAt f (fderiv ℝ f (γ t)) (γ t)` and `HasDerivAt γ (deriv γ t) t`. The
second factor comes from the absolute continuity of `γ` (`hγac`): an AC curve has
bounded variation on `[0,1]`, hence is differentiable a.e.
(`BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`), so `HasDerivAt γ
(deriv γ t) t` holds a.e. The first factor comes from `hmeet`: the arc length of
the contact between `γ` and the degeneracy set
`N := {z | ¬(DifferentiableAt ℝ f z ∧ 0 < det (fderiv ℝ f z))}` is negligible,
which forces the parameter footprint `{t ∈ [0,1] | deriv γ t ≠ 0 ∧ γ t ∈ N}` to
be Lebesgue-null; off it, `deriv γ t ≠ 0` implies `DifferentiableAt ℝ f (γ t)`.
Combining the two a.e. facts gives the chain rule a.e. on `[0,1]`. -/
theorem chainRule_hasDerivAt_of_finite {f : ℂ → ℂ} {γ : ℝ → ℂ} (hγcont : Continuous γ)
    (hγac : AbsolutelyContinuousOnInterval γ 0 1)
    (_hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (hmeet : ¬ 1 ≤ arcLengthLineIntegral
      ({z | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)}.indicator
        (fun _ => ∞)) γ) :
    ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
      HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t := by
  classical
  -- The degeneracy set `N` (where `f` is not differentiable with positive Jacobian).
  set N : Set ℂ := {z | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)} with hN
  have hNmeas : MeasurableSet N := by
    have hd : MeasurableSet {z : ℂ | DifferentiableAt ℝ f z} :=
      measurableSet_of_differentiableAt ℝ f
    have hdet : MeasurableSet {z : ℂ | 0 < (fderiv ℝ f z).det} :=
      measurableSet_lt measurable_const
        ((ContinuousLinearMap.continuous_det).measurable.comp (measurable_fderiv ℝ f))
    have : N = ({z : ℂ | DifferentiableAt ℝ f z} ∩ {z : ℂ | 0 < (fderiv ℝ f z).det})ᶜ := by
      ext z; simp [hN, Set.mem_compl_iff, not_and]
    rw [this]; exact (hd.inter hdet).compl
  -- The bad parameter set: where `deriv γ t ≠ 0` and `γ t` lands in the degeneracy set.
  set B : Set ℝ := {t | deriv γ t ≠ 0 ∧ γ t ∈ N} with hB
  have hBmeas : MeasurableSet B := by
    have hd : MeasurableSet {t : ℝ | deriv γ t ≠ 0} :=
      (measurableSet_singleton (0 : ℂ)).preimage (measurable_deriv γ) |>.compl
    have hpre : MeasurableSet {t : ℝ | γ t ∈ N} := hNmeas.preimage hγcont.measurable
    have : B = {t : ℝ | deriv γ t ≠ 0} ∩ {t : ℝ | γ t ∈ N} := by
      ext t; simp [hB, Set.mem_inter_iff]
    rw [this]; exact hd.inter hpre
  -- The `∞·𝟙_N`-line-integrand equals `∞` exactly on `B`, else `0`.
  have hintegrand : ∀ t, (N.indicator (fun _ => (∞ : ℝ≥0∞)) (γ t)) *
      (‖deriv γ t‖₊ : ℝ≥0∞) = B.indicator (fun _ => (∞ : ℝ≥0∞)) t := by
    intro t
    by_cases hd : deriv γ t = 0
    · have htB : t ∉ B := fun h => h.1 hd
      rw [Set.indicator_of_notMem htB]
      simp [hd]
    · by_cases hγN : γ t ∈ N
      · have htB : t ∈ B := ⟨hd, hγN⟩
        have hnz : (‖deriv γ t‖₊ : ℝ≥0∞) ≠ 0 := by
          simp only [ne_eq, ENNReal.coe_eq_zero, nnnorm_eq_zero]
          exact hd
        rw [Set.indicator_of_mem hγN, Set.indicator_of_mem htB, ENNReal.top_mul hnz]
      · have htB : t ∉ B := fun h => hγN h.2
        rw [Set.indicator_of_notMem hγN, Set.indicator_of_notMem htB, zero_mul]
  have hLI : arcLengthLineIntegral (N.indicator (fun _ => (∞ : ℝ≥0∞))) γ
      = (∞ : ℝ≥0∞) * volume (B ∩ Set.Icc (0 : ℝ) 1) := by
    unfold arcLengthLineIntegral
    rw [show (fun t => (N.indicator (fun _ => (∞ : ℝ≥0∞)) (γ t)) *
        (‖deriv γ t‖₊ : ℝ≥0∞)) = B.indicator (fun _ => (∞ : ℝ≥0∞)) from
      funext hintegrand]
    rw [lintegral_indicator hBmeas, setLIntegral_const,
      Measure.restrict_apply hBmeas, Set.inter_comm]
  -- From `hmeet`: the parameter footprint of `B` on `[0,1]` is Lebesgue-null.
  have hBnull : volume (B ∩ Set.Icc (0 : ℝ) 1) = 0 := by
    by_contra hpos
    apply hmeet
    rw [hLI, ENNReal.top_mul hpos]
    exact le_top
  -- Hence a.e.-`t` on `[0,1]`: `deriv γ t ≠ 0 → DifferentiableAt ℝ f (γ t)`.
  have hdifff : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      deriv γ t ≠ 0 → DifferentiableAt ℝ f (γ t) := by
    rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
    apply measure_mono_null _ hBnull
    intro t ht
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at ht
    obtain ⟨hmem, hd, hndf⟩ := ht
    refine ⟨⟨hd, ?_⟩, hmem⟩
    -- `¬ DifferentiableAt ℝ f (γ t)` ⟹ `γ t ∈ N`.
    simp only [hN, Set.mem_ofPred_eq, not_and]
    exact fun hdf => absurd hdf hndf
  -- A.e.-`t` on `[0,1]`: `γ` is differentiable (hence `HasDerivAt γ (deriv γ t) t`).
  have hdiffγ : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      DifferentiableAt ℝ γ t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have hbv : BoundedVariationOn γ (Set.uIcc (0 : ℝ) 1) := hγac.boundedVariationOn
    filter_upwards [hbv.ae_differentiableAt_of_mem_uIcc] with t ht htmem
    exact ht (by rw [Set.uIcc_of_le (by norm_num)]; exact htmem)
  -- Combine the three a.e. facts and compose via `HasFDerivAt.comp_hasDerivAt`.
  filter_upwards [hdifff, hdiffγ] with t hdiffft hdiffγt hd0
  have hfd : HasFDerivAt f (fderiv ℝ f (γ t)) (γ t) := (hdiffft hd0).hasFDerivAt
  have hγd : HasDerivAt γ (deriv γ t) t := hdiffγt.hasDerivAt
  exact hfd.comp_hasDerivAt t hγd

/-- **(F3) Good curves obey the chain rule.** A curve `γ` whose gradient line
integral `∫₀¹ ‖fderiv ℝ f (γ t)‖ ‖γ' t‖ dt` is *finite* and which meets the
degeneracy set `N := {z | ¬(DifferentiableAt ℝ f z ∧ 0 < det (fderiv ℝ f z))}`
only on an arc-length-negligible set (`¬ 1 ≤ ∫₀¹ (∞·𝟙_N)(γ t)‖γ' t‖ dt`) satisfies
all three good clauses: `f ∘ γ` is absolutely continuous on every interval; the
Jacobian determinant `det (fderiv ℝ f (γ t))` is positive for a.e.-`t`; and the
chain rule `HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t))(deriv γ t)) t` holds for
a.e.-`t`.

**Domain of the a.e.-clauses.** The arc-length line integral lives on the
parameter interval `[0,1]`, and the hypotheses (`hfin`, `hmeet`) constrain `γ`
*only* there; nothing is known about `γ` outside `[0,1]`. Accordingly clauses 2
and 3 are stated for `∀ᵐ t ∂(volume.restrict (Set.Icc 0 1))` — exactly the
strength the length–area transfer consumes (its integrand
`ρ(γ t)‖deriv (f∘γ) t‖` is integrated over `[0,1]`, and the `deriv γ t = 0`
points contribute `0`). With the global `∀ᵐ t : ℝ` the clauses would be
genuinely unprovable, the parametrisation outside `[0,1]` being arbitrary.

**The three clauses.** Clause 2 (the guarded determinant positivity): from
`hmeet`, the contact set `{t ∈ [0,1] | γ t ∈ N ∧ deriv γ t ≠ 0}` carries an
`∞`-valued integrand, so it must be Lebesgue-null (else the integral is `∞ ≥ 1`),
giving `γ t ∉ N`, i.e. `0 < det`, for a.e. such `t`. The two remaining clauses are
the genuine Fuglede/chain-rule content:
  * `clause 3` (the chain rule `HasDerivAt (f∘γ) ((Df)(γ t)·γ' t) t`) needs
    `DifferentiableAt ℝ γ t` (via `HasFDerivAt.comp_hasDerivAt`, since
    `deriv γ t` is the junk derivative unless `γ` is differentiable). The curve
    family carries no rectifiability/AC of `γ`, so this is *not* dischargeable
    from `hfin`/`hmeet` alone — it is `chainRule_hasDerivAt_of_finite`.
  * `clause 1` (absolute continuity of `f∘γ`) is the length–area estimate
    `‖f(γ t)−f(γ s)‖ ≤ ∫ₛᵗ ‖Df(γ)‖‖γ'‖`. The ACL theory is for coordinate
    lines, not general curves, so this is
    `absolutelyContinuous_comp_of_finite_lineIntegral`. -/
theorem chainRule_good_of_finite {f : ℂ → ℂ}
    (hfcont : Continuous f) {γ : ℝ → ℂ} (hγcont : Continuous γ)
    (hγac : AbsolutelyContinuousOnInterval γ 0 1)
    (hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞)) γ ≠ ∞)
    (hmeet : ¬ 1 ≤ arcLengthLineIntegral
      ({z | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)}.indicator
        (fun _ => ∞)) γ) (hgood : GoodCurve f γ) :
    (∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
        AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
      (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
        HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t := by
  -- The degeneracy set and the operator-norm density.
  set N : Set ℂ := {z | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)} with hN
  -- `N` is measurable (same computation as in the modulus reduction).
  have hNmeas : MeasurableSet N := by
    have hd : MeasurableSet {z : ℂ | DifferentiableAt ℝ f z} :=
      measurableSet_of_differentiableAt ℝ f
    have hdet : MeasurableSet {z : ℂ | 0 < (fderiv ℝ f z).det} :=
      measurableSet_lt measurable_const
        ((ContinuousLinearMap.continuous_det).measurable.comp (measurable_fderiv ℝ f))
    have : N = ({z : ℂ | DifferentiableAt ℝ f z} ∩ {z : ℂ | 0 < (fderiv ℝ f z).det})ᶜ := by
      ext z; simp [hN, Set.mem_compl_iff, not_and]
    rw [this]; exact (hd.inter hdet).compl
  -- ===================================================================
  -- CLAUSE 2 (proven): the guarded determinant positivity on `[0,1]`.
  -- From `hmeet`, the contact set has a Lebesgue-null parameter footprint.
  -- ===================================================================
  -- The bad parameter set for clause 2, sitting inside the contact set.
  set B : Set ℝ := {t | deriv γ t ≠ 0 ∧ γ t ∈ N} with hB
  -- `B` is measurable: `γ` is continuous (hence measurable), `N` measurable,
  -- and `deriv γ` is always measurable.
  have hBmeas : MeasurableSet B := by
    have hd : MeasurableSet {t : ℝ | deriv γ t ≠ 0} :=
      (measurableSet_singleton (0 : ℂ)).preimage
        (measurable_deriv γ) |>.compl
    have hpre : MeasurableSet {t : ℝ | γ t ∈ N} :=
      hNmeas.preimage hγcont.measurable
    have : B = {t : ℝ | deriv γ t ≠ 0} ∩ {t : ℝ | γ t ∈ N} := by
      ext t; simp [hB, Set.mem_inter_iff]
    rw [this]; exact hd.inter hpre
  -- The `∞·𝟙_N`-line-integrand: equals `∞` exactly on `B`, else `0`.
  have hintegrand : ∀ t, (N.indicator (fun _ => (∞ : ℝ≥0∞)) (γ t)) *
      (‖deriv γ t‖₊ : ℝ≥0∞) = B.indicator (fun _ => (∞ : ℝ≥0∞)) t := by
    intro t
    by_cases hd : deriv γ t = 0
    · -- `‖0‖₊ = 0` kills the product; and `t ∉ B`.
      have htB : t ∉ B := fun h => h.1 hd
      rw [Set.indicator_of_notMem htB]
      simp [hd]
    · by_cases hγN : γ t ∈ N
      · have htB : t ∈ B := ⟨hd, hγN⟩
        have hnz : (‖deriv γ t‖₊ : ℝ≥0∞) ≠ 0 := by
          simp only [ne_eq, ENNReal.coe_eq_zero, nnnorm_eq_zero]
          exact hd
        rw [Set.indicator_of_mem hγN, Set.indicator_of_mem htB, ENNReal.top_mul hnz]
      · have htB : t ∉ B := fun h => hγN h.2
        rw [Set.indicator_of_notMem hγN, Set.indicator_of_notMem htB, zero_mul]
  -- The line integral of `∞·𝟙_N` equals `∞ * volume (B ∩ [0,1])`.
  have hLI : arcLengthLineIntegral (N.indicator (fun _ => (∞ : ℝ≥0∞))) γ
      = (∞ : ℝ≥0∞) * volume (B ∩ Set.Icc (0 : ℝ) 1) := by
    unfold arcLengthLineIntegral
    rw [show (fun t => (N.indicator (fun _ => (∞ : ℝ≥0∞)) (γ t)) *
        (‖deriv γ t‖₊ : ℝ≥0∞)) = B.indicator (fun _ => (∞ : ℝ≥0∞)) from
      funext hintegrand]
    rw [lintegral_indicator hBmeas, setLIntegral_const,
      Measure.restrict_apply hBmeas, Set.inter_comm]
  -- From `hmeet`: that integral is `< 1 < ∞`, so the measure must be `0`.
  have hBnull : volume (B ∩ Set.Icc (0 : ℝ) 1) = 0 := by
    by_contra hpos
    apply hmeet
    rw [hLI, ENNReal.top_mul hpos]
    exact le_top
  -- Hence `∀ᵐ t ∂(restrict [0,1])`, `deriv γ t ≠ 0 → γ t ∉ N`, i.e. `0 < det`.
  have hclause2 : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det := by
    rw [ae_restrict_iff' measurableSet_Icc]
    rw [ae_iff]
    -- The exceptional set is contained in `B`, intersected with `[0,1]`.
    apply measure_mono_null _ hBnull
    intro t ht
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at ht
    obtain ⟨hmem, hd, hdet⟩ := ht
    refine ⟨⟨hd, ?_⟩, hmem⟩
    -- `¬ 0 < det` ⟹ `γ t ∈ N` (since `N` includes the `¬ 0 < det` half).
    simp only [hN, Set.mem_ofPred_eq, not_and, not_lt]
    exact fun _ => not_lt.mp hdet
  -- ===================================================================
  -- CLAUSES 1 and 3: the genuine Fuglede / chain-rule content.
  -- ===================================================================
  refine ⟨absolutelyContinuous_comp_of_finite_lineIntegral hfcont hγcont hγac hfin hgood,
    hclause2, ?_⟩
  exact chainRule_hasDerivAt_of_finite hγcont hγac hfin hmeet

/-- **Fuglede: the non-good curves of a family have zero modulus.** Assembled from
the mollified-gradient `L²` energy decay
(`mollified_fderiv_ball_energy_tendsto_zero_of_memW12loc`)
and the Fuglede line-integral sweep (`curveModulus_lineIntegral_not_tendsto_zero`) via
a ball exhaustion of the (continuous) curves.

De-gated form: stated over the explicit hypothesis triple (continuity + a.e.
differentiability + `MemW12loc`); the `IsQCAnalytic` wrapper is
`IsQCAnalytic.curveModulus_notGoodCurve_zero` below. -/
theorem curveModulus_notGoodCurve_zero_of_memW12loc {f : ℂ → ℂ}
    (hfcont : Continuous f) (hdiff : ∀ᵐ z, DifferentiableAt ℝ f z) (hW12 : MemW12loc f)
    (Γ : Set (ℝ → ℂ)) (hcont : ∀ γ ∈ Γ, Continuous γ) :
    curveModulus {γ ∈ Γ | ¬ GoodCurve f γ} = 0 := by
  classical
  -- ===================================================================
  -- Ball exhaustion: split the non-good family by where the curve lives.
  -- ===================================================================
  set E : Set (ℝ → ℂ) := {γ ∈ Γ | ¬ GoodCurve f γ} with hE
  set Em : ℕ → Set (ℝ → ℂ) := fun m => {γ ∈ Γ | ¬ GoodCurve f γ ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Metric.closedBall (0 : ℂ) m)} with hEm
  -- `E = ⋃ m, Em m`.
  have hEunion : E = ⋃ m, Em m := by
    apply Set.eq_of_subset_of_subset
    · rintro γ ⟨hγΓ, hγbad⟩
      -- `γ '' Icc 0 1` is compact, hence bounded, hence in some `closedBall 0 m`.
      have hcomp : IsCompact (γ '' Set.Icc 0 1) :=
        isCompact_Icc.image (hcont γ hγΓ)
      obtain ⟨r, hr⟩ := hcomp.isBounded.subset_closedBall (0 : ℂ)
      obtain ⟨m, hm⟩ := exists_nat_ge r
      refine Set.mem_iUnion.mpr ⟨m, hγΓ, hγbad, fun t ht => ?_⟩
      have : γ t ∈ Metric.closedBall (0 : ℂ) r := hr (Set.mem_image_of_mem γ ht)
      exact Metric.closedBall_subset_closedBall hm this
    · refine Set.iUnion_subset (fun m γ hγ => ?_)
      obtain ⟨hγΓ, hγbad, _⟩ := hγ
      exact ⟨hγΓ, hγbad⟩
  rw [hEunion]
  -- Reduce to: each `Em m` has zero modulus.
  refine curveModulus_iUnion_zero (fun m => ?_)
  -- ===================================================================
  -- Per-ball sweep.  Fix `m`; work on the ball of radius `R = m + 1`.
  -- ===================================================================
  set R : ℝ := (m : ℝ) + 1 with hR
  -- A canonical mollifier sequence with `rOut = 2/(n+2) → 0`.
  set φ₀ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ₀
  have hφ₀rout : Filter.Tendsto (fun n => (φ₀ n).rOut) Filter.atTop (nhds 0) := by
    have : (fun n : ℕ => (φ₀ n).rOut) = fun n : ℕ => (2 : ℝ) / (n + 2) := rfl
    rw [this]
    exact Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  -- The mollified-differential difference density and its ball-energy.
  set D : ℕ → ℂ → ℝ≥0∞ := fun n z =>
    (‖fderiv ℝ (MeasureTheory.convolution ((φ₀ n).normed MeasureTheory.volume) f
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) z - fderiv ℝ f z‖₊ : ℝ≥0∞)
    with hD
  -- `D n` is measurable.
  have hDmeas : ∀ n, Measurable (D n) := by
    intro n
    have h1 : Measurable (fderiv ℝ (MeasureTheory.convolution
        ((φ₀ n).normed MeasureTheory.volume) f (ContinuousLinearMap.lsmul ℝ ℝ)
        MeasureTheory.volume)) := measurable_fderiv ℝ _
    have h2 : Measurable (fderiv ℝ f) := measurable_fderiv ℝ f
    exact ((h1.sub h2).nnnorm).coe_nnreal_ennreal
  set a : ℕ → ℝ≥0∞ := fun n => ∫⁻ z in Metric.ball (0 : ℂ) R, (D n z) ^ 2 with ha
  -- Pillar A: the ball-energy of the differential difference tends to `0`.
  have haTendsto : Filter.Tendsto a Filter.atTop (nhds 0) :=
    mollified_fderiv_ball_energy_tendsto_zero_of_memW12loc hfcont hdiff hW12 R φ₀ hφ₀rout
  -- ===================================================================
  -- Extract a subsequence `σ` whose root-energies are geometrically small.
  -- ===================================================================
  have hkey : ∀ (c : ℝ≥0∞), c ≠ 0 → ∀ N : ℕ, ∃ n, N < n ∧ a n ≤ c := by
    intro c hc N
    have hev : ∀ᶠ n in Filter.atTop, a n ≤ c :=
      (ENNReal.tendsto_nhds_zero.mp haTendsto) c (pos_iff_ne_zero.mpr hc)
    obtain ⟨n, hn, hnc⟩ := (hev.and (Filter.eventually_gt_atTop N)).exists
    exact ⟨n, hnc, hn⟩
  -- The geometric threshold (squared so its root dominates `(1/2)^k`).
  have hthresh : ∀ k : ℕ, ((ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) ^ 2) ≠ 0 := by
    intro k
    apply pow_ne_zero
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  choose g hg1 hg2 using hkey
  set σ : ℕ → ℕ := fun k => Nat.rec
    (g ((ENNReal.ofReal ((1 / 2 : ℝ) ^ 0)) ^ 2) (hthresh 0) 0)
    (fun k prev => g ((ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1))) ^ 2) (hthresh (k + 1)) prev) k
    with hσ
  have hσmono : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact hg1 ((ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1))) ^ 2) (hthresh (k + 1)) (σ k)
  have hσbound : ∀ k, a (σ k) ≤ (ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) ^ 2 := by
    intro k
    cases k with
    | zero => exact hg2 _ _ 0
    | succ n => exact hg2 _ _ (σ n)
  -- ===================================================================
  -- The truncated densities `G k` and their summable root-energies.
  -- ===================================================================
  set G : ℕ → ℂ → ℝ≥0∞ := fun k =>
    (Metric.ball (0 : ℂ) R).indicator (fun z => D (σ k) z) with hG
  have hGmeas : ∀ k, Measurable (G k) := fun k =>
    (hDmeas (σ k)).indicator measurableSet_ball
  -- `∫⁻ (G k)² = a (σ k)`.
  have hGenergy : ∀ k, (∫⁻ z, (G k z) ^ 2) = a (σ k) := by
    intro k
    have h1 : (fun z => (G k z) ^ 2)
        = (Metric.ball (0 : ℂ) R).indicator (fun z => (D (σ k) z) ^ 2) := by
      funext z
      by_cases hz : z ∈ Metric.ball (0 : ℂ) R
      · simp only [hG, Set.indicator_of_mem hz]
      · simp only [hG, Set.indicator_of_notMem hz]; ring
    rw [h1, lintegral_indicator measurableSet_ball]
  -- Root-energy bound: `(∫⁻ (G k)²)^{1/2} ≤ ofReal ((1/2)^k)`.
  have hGroot : ∀ k, (∫⁻ z, (G k z) ^ 2) ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro k
    rw [hGenergy k]
    calc a (σ k) ^ ((1 : ℝ) / 2)
        ≤ ((ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) ^ 2) ^ ((1 : ℝ) / 2) := by
          gcongr; exact hσbound k
      _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
          rw [← ENNReal.rpow_natCast (ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) 2,
            ← ENNReal.rpow_mul]; norm_num
  -- The sum of root-energies is finite (dominated by `∑ (1/2)^k = 2`).
  have hsum : ∑' k, (∫⁻ z, (G k z) ^ 2) ^ ((1 : ℝ) / 2) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hGroot)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  -- ===================================================================
  -- Pillar B: the curves where the truncated line integrals fail to
  -- vanish form a zero-modulus family.
  -- ===================================================================
  have hEmcont : ∀ γ ∈ Em m, Continuous γ := fun γ hγ => hcont γ hγ.1
  have hBzero : curveModulus {γ ∈ Em m | ¬ Filter.Tendsto
      (fun k => arcLengthLineIntegral (G k) γ) Filter.atTop (nhds 0)} = 0 :=
    curveModulus_lineIntegral_not_tendsto_zero hGmeas hsum hEmcont
  -- ===================================================================
  -- Containment: every curve of `Em m` fails the truncated convergence.
  -- ===================================================================
  refine le_antisymm ?_ (zero_le)
  rw [← hBzero]
  refine curveModulus_mono ?_
  rintro γ ⟨hγΓ, hγbad, hγball⟩
  refine ⟨⟨hγΓ, hγbad, hγball⟩, ?_⟩
  -- For curves inside the ball, the truncated line integral equals the full one.
  have hLIeq : ∀ k, arcLengthLineIntegral (G k) γ
      = arcLengthLineIntegral (fun z => D (σ k) z) γ := by
    intro k
    unfold arcLengthLineIntegral
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    simp only [hG]
    have hin : γ t ∈ Metric.ball (0 : ℂ) R := by
      have hcb : γ t ∈ Metric.closedBall (0 : ℂ) m := hγball t ht
      exact Metric.closedBall_subset_ball (by rw [hR]; linarith) hcb
    rw [Set.indicator_of_mem hin]
  -- Suppose the truncated line integrals tended to `0`; then `γ` would be good.
  intro hTend
  apply hγbad
  have hTend' : Filter.Tendsto (fun k => arcLengthLineIntegral (fun z => D (σ k) z) γ)
      Filter.atTop (nhds 0) := by
    have : (fun k => arcLengthLineIntegral (G k) γ)
        = fun k => arcLengthLineIntegral (fun z => D (σ k) z) γ := by
      funext k; exact hLIeq k
    rw [← this]; exact hTend
  -- The witness `φ := fun k => φ₀ (σ k)`.
  refine ⟨fun k => φ₀ (σ k), ?_, ?_⟩
  · exact hφ₀rout.comp hσmono.tendsto_atTop
  · exact hTend'

/-- **Fuglede: the non-good curves of a family have zero modulus.** `IsQCAnalytic` wrapper
of `curveModulus_notGoodCurve_zero_of_memW12loc`. -/
theorem IsQCAnalytic.curveModulus_notGoodCurve_zero {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (Γ : Set (ℝ → ℂ)) (hcont : ∀ γ ∈ Γ, Continuous γ) :
    curveModulus {γ ∈ Γ | ¬ GoodCurve f γ} = 0 :=
  curveModulus_notGoodCurve_zero_of_memW12loc hf.1.1.continuous
    (IsQCAnalytic.ae_differentiableAt hf) hf.2.1 Γ hcont

/-- **Fuglede's theorem (quasiconformal case).** For a quasiconformal map `f`, the
curves `γ` of a family along which the chain rule for `f` fails — either `f ∘ γ` is
not absolutely continuous, or its derivative does not agree almost everywhere with
`(D f)(γ) · γ'` — form a subfamily of zero modulus. This is exactly the strength the
length–area density transfer needs: on the complementary (full-modulus) subfamily,
the arc-length integral of a transferred density is governed by the differential of
`f` along the curve. (The bare absolute-continuity statement is strictly weaker:
absolute continuity of `f ∘ γ` does not by itself give the chain-rule identity,
because `f`'s plane-a.e. differentiability need not hold at a.e. point of a fixed
curve.)

The proof assembles three modulus-zero exceptional families.  Writing
`G z := ‖fderiv ℝ f z‖₊` and `N := {z | ¬(DifferentiableAt ℝ f z ∧
0 < det (fderiv ℝ f z))}` (a Lebesgue-null set), the exceptional family `E` is
contained in `F1 ∪ F2`, where `F1` is the infinite-`G`-line-integral family
(`curveModulus_lineIntegral_top_zero`) and `F2` is the family meeting `N` with
positive arc length (`curveModulus_meetsNullSet_zero`, since `N` is null).  The
inclusion `E ⊆ F1 ∪ F2` is the contrapositive of `chainRule_good_of_finite`.
Monotonicity (`curveModulus_mono`) and subadditivity for null families
(`curveModulus_union_zero`) finish. -/
theorem IsQCAnalytic.chainRule_exceptional_modulus_zero {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (Γ : Set (ℝ → ℂ)) (hcont : ∀ γ ∈ Γ, Continuous γ)
    (hac : ∀ γ ∈ Γ, AbsolutelyContinuousOnInterval γ 0 1) :
    curveModulus {γ ∈ Γ | ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
        AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
      (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
        HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t)} = 0 := by
  classical
  -- The operator-norm density `G` of the differential, and the degeneracy set `N`.
  set G : ℂ → ℝ≥0∞ := fun z => (‖fderiv ℝ f z‖₊ : ℝ≥0∞) with hG
  set N : Set ℂ := {z | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)} with hN
  -- `N` is measurable.
  have hNmeas : MeasurableSet N := by
    have hd : MeasurableSet {z : ℂ | DifferentiableAt ℝ f z} :=
      measurableSet_of_differentiableAt ℝ f
    have hdet : MeasurableSet {z : ℂ | 0 < (fderiv ℝ f z).det} :=
      measurableSet_lt measurable_const
        ((ContinuousLinearMap.continuous_det).measurable.comp (measurable_fderiv ℝ f))
    rw [hN]
    have : {z : ℂ | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)}
        = ({z : ℂ | DifferentiableAt ℝ f z} ∩ {z : ℂ | 0 < (fderiv ℝ f z).det})ᶜ := by
      ext z; simp [Set.mem_compl_iff, not_and]
    rw [this]
    exact (hd.inter hdet).compl
  -- `N` is Lebesgue-null: a.e. `z` is differentiable with positive determinant.
  have hNnull : volume N = 0 := by
    rw [hN, ← ae_iff]
    filter_upwards [hf.1.2, IsQCAnalytic.ae_differentiableAt hf] with z hz hzd
    exact ⟨hzd, hz⟩
  -- The three exceptional families.
  set F1 : Set (ℝ → ℂ) := {γ ∈ Γ | arcLengthLineIntegral G γ = ∞} with hF1
  set F2 : Set (ℝ → ℂ) :=
    {γ ∈ Γ | 1 ≤ arcLengthLineIntegral (N.indicator (fun _ => ∞)) γ} with hF2
  set F3 : Set (ℝ → ℂ) := {γ ∈ Γ | ¬ GoodCurve f γ} with hF3
  -- All three have zero modulus.
  have hF1zero : curveModulus F1 = 0 := curveModulus_lineIntegral_top_zero hf Γ hcont
  have hF2zero : curveModulus F2 = 0 := curveModulus_meetsNullSet_zero hNmeas hNnull Γ
  have hF3zero : curveModulus F3 = 0 :=
    IsQCAnalytic.curveModulus_notGoodCurve_zero hf Γ hcont
  -- The union has zero modulus by subadditivity.
  have hUnionZero : curveModulus (F1 ∪ F2 ∪ F3) = 0 :=
    curveModulus_union_zero (curveModulus_union_zero hF1zero hF2zero) hF3zero
  -- The exceptional family is contained in `F1 ∪ F2 ∪ F3`.
  refine le_antisymm ?_ (zero_le)
  rw [← hUnionZero]
  refine curveModulus_mono ?_
  rintro γ ⟨hγΓ, hbad⟩
  -- Contrapositive of `chainRule_good_of_finite`: a curve outside `F1 ∪ F2 ∪ F3` is
  -- finite-gradient, meets `N` negligibly, and is good.
  by_contra hnotin
  rw [Set.mem_union, Set.mem_union, not_or, not_or] at hnotin
  obtain ⟨⟨hnF1, hnF2⟩, hnF3⟩ := hnotin
  -- Outside `F1`: the gradient line integral is finite.
  have hfin : arcLengthLineIntegral G γ ≠ ∞ := by
    intro htop; exact hnF1 ⟨hγΓ, htop⟩
  -- Outside `F2`: the contact with `N` has negligible arc length.
  have hmeet : ¬ 1 ≤ arcLengthLineIntegral (N.indicator (fun _ => ∞)) γ := by
    intro hge; exact hnF2 ⟨hγΓ, hge⟩
  -- Outside `F3`: `γ` is a good curve.
  have hgood : GoodCurve f γ := by
    by_contra hng; exact hnF3 ⟨hγΓ, hng⟩
  -- Then all three good clauses hold, contradicting `hbad`.
  exact hbad
    (chainRule_good_of_finite hf.1.1.continuous (hcont γ hγΓ) (hac γ hγΓ) hfin hmeet hgood)

end NoWanderingDomains
