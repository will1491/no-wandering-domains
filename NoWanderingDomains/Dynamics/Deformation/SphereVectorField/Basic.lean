/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.MRMT.NeumannSeries.PrincipalSolution
import NoWanderingDomains.QC.Calculus.WeylLocal
import NoWanderingDomains.QC.LengthArea.CurveModulus

/-!
# Sphere vector fields and the canonical `∂̄`-solver

Continuous vector fields on the sphere in the finite chart, the weak
`∂̄`-derivative class with locally square-integrable gradient, and the
canonical solver `dbarSolver μ = P(1_𝔻 μ) + inversion-chart correction`, a
sphere vector field linear in the coefficient.

* `HasL2WeakDzbar`, `IsSphereVectorField` — the classes.
* `ballTruncation`, `inftyChartCoeff`, `dbarSolver` — the solver data.
* `dbarSolver_add`, `dbarSolver_smul`, `isSphereVectorField_dbarSolver` — its
  algebra and sphere-field property.
-/

open MeasureTheory Complex Metric Filter Topology
open scoped ENNReal NNReal ContDiff

namespace NoWanderingDomains

def HasL2WeakDzbar (v μ : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  ∃ gx gy : ℂ → ℂ, HasWeakGradient gx gy v Ω ∧
    MemLpLocOn gx 2 Ω ∧ MemLpLocOn gy 2 Ω ∧
    (∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω →
      gx z + Complex.I * gy z = 2 * μ z)

/-- A **sphere vector field** in finite-chart reading: `v : ℂ → ℂ` is
continuous, and the infinity-chart reading `w ↦ w²·v(1/w)` extends
continuously at `w = 0` — i.e. it has a limit `L` along the punctured
neighborhoods of `0`. This is the concrete, two-chart formulation of a
continuous vector field on the Riemann sphere. (The geometric infinity-chart
reading is `−w²·v(1/w)`; the sign does not affect the extension property and
is omitted.) -/
def IsSphereVectorField (v : ℂ → ℂ) : Prop :=
  Continuous v ∧ ∃ L : ℂ,
    Tendsto (fun w : ℂ => w ^ 2 * v w⁻¹) (nhdsWithin 0 {0}ᶜ) (nhds L)

/-- The truncation of a coefficient to the closed unit disk — the *near piece*
of the canonical splitting. -/
noncomputable def ballTruncation (μ : ℂ → ℂ) : ℂ → ℂ := fun z =>
  open Classical in
  if z ∈ Metric.closedBall (0 : ℂ) 1 then μ z else 0

/-- The infinity-chart transport of the *far piece* of a coefficient: the
Beltrami transformation law under `z = 1/w` applied to `μ·1_{|z|>1}`, giving
`ν(w) = (w²/w̄²)·μ(1/w)` carried by the punctured open unit disk. The factor
`w²/w̄²` is unimodular, so `|ν(w)| = |μ(1/w)|` and essential bounds are
preserved. -/
noncomputable def inftyChartCoeff (μ : ℂ → ℂ) : ℂ → ℂ := fun w =>
  open Classical in
  if w ∈ Metric.ball (0 : ℂ) 1 ∧ w ≠ 0
    then w ^ 2 / (starRingEnd ℂ w) ^ 2 * μ w⁻¹ else 0

/-- The **canonical `∂̄`-solver**: a totally defined, pointwise formula
producing a continuous sphere vector field with weak `∂̄` equal to `μ`. The
near piece is the Cauchy transform of the disk truncation; the far piece is
solved in the infinity chart and transported back as a vector field (the
finite-chart reading of a field whose infinity-chart reading is `u` is
`z ↦ −z²·u(1/z)`; at `z = 0` the junk value `0⁻¹ = 0` is harmless since the
prefactor `−z²` vanishes). -/
noncomputable def dbarSolver (μ : ℂ → ℂ) : ℂ → ℂ := fun z =>
  cauchyTransform (ballTruncation μ) z
    - z ^ 2 * cauchyTransform (inftyChartCoeff μ) z⁻¹

/-- **Additivity of the solver.** The truncation and transport operations are
pointwise linear; the Cauchy transform is additive on integrable integrands,
which the measurability and essential boundedness of the two coefficients
provide. -/
theorem dbarSolver_add {μ σ : ℂ → ℂ}
    (hμ : AEMeasurable μ volume) (hσ : AEMeasurable σ volume)
    (hμb : eLpNormEssSup μ volume < ⊤) (hσb : eLpNormEssSup σ volume < ⊤) :
    dbarSolver (fun z => μ z + σ z)
      = fun z => dbarSolver μ z + dbarSolver σ z := by
  -- pointwise additivity of the truncation and the transport
  have hball : ballTruncation (fun z => μ z + σ z)
      = fun z => ballTruncation μ z + ballTruncation σ z := by
    funext z
    simp only [ballTruncation]
    split_ifs <;> simp
  have hinfty : inftyChartCoeff (fun z => μ z + σ z)
      = fun w => inftyChartCoeff μ w + inftyChartCoeff σ w := by
    funext w
    simp only [inftyChartCoeff]
    split_ifs with h
    · ring
    · simp
  -- the inversion `z ↦ z⁻¹` maps null sets to null sets (differentiable off `0`)
  have hinv_image_null : ∀ N : Set ℂ, volume N = 0 →
      volume ((fun z : ℂ => z⁻¹) '' N) = 0 := by
    intro N hN
    have hsub : (fun z : ℂ => z⁻¹) '' N
        ⊆ ((fun z : ℂ => z⁻¹) '' (N \ {0})) ∪ {0} := by
      rintro _ ⟨z, hz, rfl⟩
      by_cases h0 : z = 0
      · exact Or.inr (by simp [h0])
      · exact Or.inl ⟨z, ⟨hz, h0⟩, rfl⟩
    refine measure_mono_null hsub (measure_union_null ?_ (measure_singleton 0))
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ?_ (measure_mono_null Set.sdiff_subset hN)
    intro z hz
    exact (differentiableAt_inv (𝕜 := ℝ) (by simpa using hz.2)).differentiableWithinAt
  -- hence it is quasi-measure-preserving (it is a measurable involution)
  have hqmp : Measure.QuasiMeasurePreserving (fun z : ℂ => z⁻¹)
      (volume : Measure ℂ) volume := by
    refine ⟨measurable_inv, Measure.AbsolutelyContinuous.mk fun N hNm hN => ?_⟩
    rw [Measure.map_apply measurable_inv hNm]
    have hpre : (fun z : ℂ => z⁻¹) ⁻¹' N = (fun z : ℂ => z⁻¹) '' N := by
      ext w
      constructor
      · intro hw
        exact ⟨w⁻¹, hw, inv_inv w⟩
      · rintro ⟨v, hv, rfl⟩
        simpa [Set.mem_preimage, inv_inv] using hv
    rw [hpre]
    exact hinv_image_null N hN
  -- both truncated pieces of an admissible coefficient pair integrably
  -- against the Cauchy kernel
  have key : ∀ ν : ℂ → ℂ, AEMeasurable ν volume → eLpNormEssSup ν volume < ⊤ →
      (∀ w : ℂ, Integrable (fun ζ => ballTruncation ν ζ / (ζ - w)) volume) ∧
      (∀ w : ℂ, Integrable (fun ζ => inftyChartCoeff ν ζ / (ζ - w)) volume) := by
    intro ν hν hνb
    -- the near piece is an indicator of an essentially bounded function
    have hball_eq : ballTruncation ν = (Metric.closedBall (0:ℂ) 1).indicator ν := by
      funext w
      by_cases hw : w ∈ Metric.closedBall (0:ℂ) 1
      · rw [Set.indicator_of_mem hw]
        simp only [ballTruncation]
        rw [if_pos hw]
      · rw [Set.indicator_of_notMem hw]
        simp only [ballTruncation]
        rw [if_neg hw]
    have hfin1 : IsFiniteMeasure (volume.restrict (Metric.closedBall (0:ℂ) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]
          exact (isCompact_closedBall _ _).measure_lt_top⟩
    have hballmem : MemLp (ballTruncation ν) 4 volume := by
      rw [hball_eq, memLp_indicator_iff_restrict measurableSet_closedBall]
      have htop : MemLp ν ⊤ (volume.restrict (Metric.closedBall (0:ℂ) 1)) := by
        refine ⟨hν.aestronglyMeasurable.restrict, ?_⟩
        rw [eLpNorm_exponent_top]
        exact lt_of_le_of_lt
          (eLpNormEssSup_mono_measure ν
            (Measure.absolutelyContinuous_of_le Measure.restrict_le_self))
          hνb
      exact htop.mono_exponent le_top
    have hballsupp : ∀ w : ℂ, (1:ℝ) < ‖w‖ → ballTruncation ν w = 0 := by
      intro w hw
      simp only [ballTruncation]
      have hmem : w ∉ Metric.closedBall (0:ℂ) 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hw
      rw [if_neg hmem]
    have hinftysupp : ∀ w : ℂ, (1:ℝ) < ‖w‖ → inftyChartCoeff ν w = 0 := by
      intro w hw
      simp only [inftyChartCoeff]
      have hmem : ¬ (w ∈ Metric.ball (0:ℂ) 1 ∧ w ≠ 0) := by
        rintro ⟨hw1, -⟩
        rw [Metric.mem_ball, dist_zero_right] at hw1
        linarith
      rw [if_neg hmem]
    -- the far piece: measurable through the quasi-measure-preserving inversion
    have hg_aem : AEMeasurable
        (fun w : ℂ => w ^ 2 / (starRingEnd ℂ w) ^ 2 * ν w⁻¹) volume := by
      have h1 : Measurable fun w : ℂ => w ^ 2 / (starRingEnd ℂ w) ^ 2 := by
        simp only [div_eq_mul_inv]
        exact (measurable_id.pow_const 2).mul
          ((Complex.continuous_conj.measurable.pow_const 2).inv)
      have h2 : AEMeasurable (fun w : ℂ => ν w⁻¹) volume :=
        hν.comp_quasiMeasurePreserving hqmp
      exact h1.aemeasurable.mul h2
    have hinfty_eq : inftyChartCoeff ν
        = (Metric.ball (0:ℂ) 1 \ {0}).indicator
            (fun w : ℂ => w ^ 2 / (starRingEnd ℂ w) ^ 2 * ν w⁻¹) := by
      funext w
      by_cases hw : w ∈ Metric.ball (0:ℂ) 1 ∧ w ≠ 0
      · rw [Set.indicator_of_mem ((Set.mem_sdiff w).mpr ⟨hw.1, by simpa using hw.2⟩)]
        simp only [inftyChartCoeff]
        rw [if_pos hw]
      · rw [Set.indicator_of_notMem
          (fun hmem => hw ⟨hmem.1, by simpa using hmem.2⟩)]
        simp only [inftyChartCoeff]
        rw [if_neg hw]
    have hfin2 : IsFiniteMeasure (volume.restrict (Metric.ball (0:ℂ) 1 \ {0})) :=
      ⟨by rw [Measure.restrict_apply_univ]
          exact lt_of_le_of_lt (measure_mono Set.sdiff_subset) measure_ball_lt_top⟩
    have hinftymem : MemLp (inftyChartCoeff ν) 4 volume := by
      rw [hinfty_eq, memLp_indicator_iff_restrict
        (measurableSet_ball.diff (measurableSet_singleton 0))]
      refine MemLp.of_bound hg_aem.aestronglyMeasurable.restrict
        (eLpNormEssSup ν volume).toReal ?_
      have hCae : ∀ᵐ w ∂(volume : Measure ℂ),
          ‖ν w⁻¹‖ₑ ≤ eLpNormEssSup ν volume := by
        have h0 := enorm_ae_le_eLpNormEssSup ν (volume : Measure ℂ)
        rw [ae_iff] at h0 ⊢
        exact hqmp.preimage_null h0
      filter_upwards [ae_restrict_of_ae hCae] with w hw
      have hfac : ‖w ^ 2 / (starRingEnd ℂ w) ^ 2‖ ≤ 1 := by
        rcases eq_or_ne w 0 with rfl | hw0
        · simp
        · have hnz : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
          have h1 : ‖w ^ 2 / (starRingEnd ℂ w) ^ 2‖ = 1 := by
            rw [norm_div, norm_pow, norm_pow, Complex.norm_conj,
              div_self (pow_ne_zero 2 hnz)]
          exact h1.le
      calc ‖w ^ 2 / (starRingEnd ℂ w) ^ 2 * ν w⁻¹‖
          ≤ ‖ν w⁻¹‖ := by
            rw [norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _) hfac
        _ ≤ (eLpNormEssSup ν volume).toReal := by
            rw [← ofReal_norm] at hw
            exact (ENNReal.ofReal_le_iff_le_toReal hνb.ne).mp hw
    exact ⟨fun w => integrable_div_sub_of_memLp_of_support
        (by norm_num : (2:ℝ≥0∞) < 4) (by norm_num) hballmem hballsupp w,
      fun w => integrable_div_sub_of_memLp_of_support
        (by norm_num : (2:ℝ≥0∞) < 4) (by norm_num) hinftymem hinftysupp w⟩
  obtain ⟨hIμball, hIμinfty⟩ := key μ hμ hμb
  obtain ⟨hIσball, hIσinfty⟩ := key σ hσ hσb
  -- the Cauchy transform is additive on kernel-integrable inputs
  have hPadd : ∀ (f g : ℂ → ℂ),
      (∀ w : ℂ, Integrable (fun ζ => f ζ / (ζ - w)) volume) →
      (∀ w : ℂ, Integrable (fun ζ => g ζ / (ζ - w)) volume) → ∀ w : ℂ,
      cauchyTransform (fun ζ => f ζ + g ζ) w
        = cauchyTransform f w + cauchyTransform g w := by
    intro f g hf hg w
    have h1 : ∫ (ζ : ℂ), (f ζ + g ζ) / (ζ - w)
        = (∫ (ζ : ℂ), f ζ / (ζ - w)) + ∫ (ζ : ℂ), g ζ / (ζ - w) := by
      rw [show (fun ζ : ℂ => (f ζ + g ζ) / (ζ - w))
          = fun ζ : ℂ => f ζ / (ζ - w) + g ζ / (ζ - w) from
        funext fun ζ => add_div (f ζ) (g ζ) (ζ - w)]
      exact integral_add (hf w) (hg w)
    change -(1 / (Real.pi : ℂ)) * ∫ ζ, (f ζ + g ζ) / (ζ - w)
        = -(1 / (Real.pi : ℂ)) * (∫ ζ, f ζ / (ζ - w))
          + -(1 / (Real.pi : ℂ)) * ∫ ζ, g ζ / (ζ - w)
    rw [h1]
    ring
  funext z
  simp only [dbarSolver, hball, hinfty]
  rw [hPadd _ _ hIμball hIσball z, hPadd _ _ hIμinfty hIσinfty z⁻¹]
  ring

/-- **Homogeneity of the solver.** Scalar multiples pass through the
truncation, the transport, and the (Bochner) integral unconditionally. -/
theorem dbarSolver_smul (c : ℂ) (μ : ℂ → ℂ) :
    dbarSolver (fun z => c * μ z) = fun z => c * dbarSolver μ z := by
  -- the truncation is pointwise linear
  have hball : ballTruncation (fun z => c * μ z) = fun z => c * ballTruncation μ z := by
    funext z
    simp only [ballTruncation]
    split_ifs <;> simp
  -- the infinity-chart transport is pointwise linear
  have hinfty : inftyChartCoeff (fun z => c * μ z) = fun w => c * inftyChartCoeff μ w := by
    funext w
    simp only [inftyChartCoeff]
    split_ifs with h
    · ring
    · exact (mul_zero c).symm
  -- the Cauchy transform pulls out scalars (unconditionally)
  have hP : ∀ (h : ℂ → ℂ) (z : ℂ),
      cauchyTransform (fun ζ => c * h ζ) z = c * cauchyTransform h z := by
    intro h z
    change -(1 / (Real.pi : ℂ)) * ∫ ζ, c * h ζ / (ζ - z)
        = c * (-(1 / (Real.pi : ℂ)) * ∫ ζ, h ζ / (ζ - z))
    have h1 : ∫ (ζ : ℂ), c * (h ζ / (ζ - z)) = c * ∫ (ζ : ℂ), h ζ / (ζ - z) :=
      integral_const_mul c (fun ζ : ℂ => h ζ / (ζ - z))
    rw [show (fun ζ : ℂ => c * h ζ / (ζ - z)) = fun ζ : ℂ => c * (h ζ / (ζ - z)) from
      funext fun ζ => mul_div_assoc c (h ζ) (ζ - z), h1]
    ring
  funext z
  simp only [dbarSolver, hball, hinfty, hP]
  ring

/-- The canonical solution of `∂̄v = μ` for a measurable, essentially bounded
coefficient is a sphere vector field: it is continuous on `ℂ` (Hölder
continuity of the Cauchy transform of a bounded compactly supported density,
in each chart), and its infinity-chart reading extends continuously at `0`
(the near piece decays at infinity; the far piece's reading near `0` *is* the
Cauchy transform in the `w`-chart, continuous there). -/
theorem isSphereVectorField_dbarSolver {μ : ℂ → ℂ}
    (hμ : AEMeasurable μ volume) (hb : eLpNormEssSup μ volume < ⊤) :
    IsSphereVectorField (dbarSolver μ) := by
  -- ===== the coefficient pieces are `L⁴` and compactly vanishing =====
  have hinv_image_null : ∀ N : Set ℂ, volume N = 0 →
      volume ((fun z : ℂ => z⁻¹) '' N) = 0 := by
    intro N hN
    have hsub : (fun z : ℂ => z⁻¹) '' N
        ⊆ ((fun z : ℂ => z⁻¹) '' (N \ {0})) ∪ {0} := by
      rintro _ ⟨z, hz, rfl⟩
      by_cases h0 : z = 0
      · exact Or.inr (by simp [h0])
      · exact Or.inl ⟨z, ⟨hz, h0⟩, rfl⟩
    refine measure_mono_null hsub (measure_union_null ?_ (measure_singleton 0))
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ?_ (measure_mono_null Set.sdiff_subset hN)
    intro z hz
    exact (differentiableAt_inv (𝕜 := ℝ) (by simpa using hz.2)).differentiableWithinAt
  have hqmp : Measure.QuasiMeasurePreserving (fun z : ℂ => z⁻¹)
      (volume : Measure ℂ) volume := by
    refine ⟨measurable_inv, Measure.AbsolutelyContinuous.mk fun N hNm hN => ?_⟩
    rw [Measure.map_apply measurable_inv hNm]
    have hpre : (fun z : ℂ => z⁻¹) ⁻¹' N = (fun z : ℂ => z⁻¹) '' N := by
      ext w
      constructor
      · intro hw
        exact ⟨w⁻¹, hw, inv_inv w⟩
      · rintro ⟨v, hv, rfl⟩
        simpa [Set.mem_preimage, inv_inv] using hv
    rw [hpre]
    exact hinv_image_null N hN
  have hball_eq : ballTruncation μ = (Metric.closedBall (0:ℂ) 1).indicator μ := by
    funext w
    by_cases hw : w ∈ Metric.closedBall (0:ℂ) 1
    · rw [Set.indicator_of_mem hw]
      simp only [ballTruncation]
      rw [if_pos hw]
    · rw [Set.indicator_of_notMem hw]
      simp only [ballTruncation]
      rw [if_neg hw]
  have hfin1 : IsFiniteMeasure (volume.restrict (Metric.closedBall (0:ℂ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hballmem : MemLp (ballTruncation μ) 4 volume := by
    rw [hball_eq, memLp_indicator_iff_restrict measurableSet_closedBall]
    have htop : MemLp μ ⊤ (volume.restrict (Metric.closedBall (0:ℂ) 1)) := by
      refine ⟨hμ.aestronglyMeasurable.restrict, ?_⟩
      rw [eLpNorm_exponent_top]
      exact lt_of_le_of_lt
        (eLpNormEssSup_mono_measure μ
          (Measure.absolutelyContinuous_of_le Measure.restrict_le_self))
        hb
    exact htop.mono_exponent le_top
  have hballsupp : ∀ w : ℂ, (1:ℝ) < ‖w‖ → ballTruncation μ w = 0 := by
    intro w hw
    simp only [ballTruncation]
    have hmem : w ∉ Metric.closedBall (0:ℂ) 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hw
    rw [if_neg hmem]
  have hinftysupp : ∀ w : ℂ, (1:ℝ) < ‖w‖ → inftyChartCoeff μ w = 0 := by
    intro w hw
    simp only [inftyChartCoeff]
    have hmem : ¬ (w ∈ Metric.ball (0:ℂ) 1 ∧ w ≠ 0) := by
      rintro ⟨hw1, -⟩
      rw [Metric.mem_ball, dist_zero_right] at hw1
      linarith
    rw [if_neg hmem]
  have hg_aem : AEMeasurable
      (fun w : ℂ => w ^ 2 / (starRingEnd ℂ w) ^ 2 * μ w⁻¹) volume := by
    have h1 : Measurable fun w : ℂ => w ^ 2 / (starRingEnd ℂ w) ^ 2 := by
      simp only [div_eq_mul_inv]
      exact (measurable_id.pow_const 2).mul
        ((Complex.continuous_conj.measurable.pow_const 2).inv)
    have h2 : AEMeasurable (fun w : ℂ => μ w⁻¹) volume :=
      hμ.comp_quasiMeasurePreserving hqmp
    exact h1.aemeasurable.mul h2
  have hinfty_eq : inftyChartCoeff μ
      = (Metric.ball (0:ℂ) 1 \ {0}).indicator
          (fun w : ℂ => w ^ 2 / (starRingEnd ℂ w) ^ 2 * μ w⁻¹) := by
    funext w
    by_cases hw : w ∈ Metric.ball (0:ℂ) 1 ∧ w ≠ 0
    · rw [Set.indicator_of_mem ((Set.mem_sdiff w).mpr ⟨hw.1, by simpa using hw.2⟩)]
      simp only [inftyChartCoeff]
      rw [if_pos hw]
    · rw [Set.indicator_of_notMem
        (fun hmem => hw ⟨hmem.1, by simpa using hmem.2⟩)]
      simp only [inftyChartCoeff]
      rw [if_neg hw]
  have hfin2 : IsFiniteMeasure (volume.restrict (Metric.ball (0:ℂ) 1 \ {0})) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_lt (measure_mono Set.sdiff_subset) measure_ball_lt_top⟩
  have hinftymem : MemLp (inftyChartCoeff μ) 4 volume := by
    rw [hinfty_eq, memLp_indicator_iff_restrict
      (measurableSet_ball.diff (measurableSet_singleton 0))]
    refine MemLp.of_bound hg_aem.aestronglyMeasurable.restrict
      (eLpNormEssSup μ volume).toReal ?_
    have hCae : ∀ᵐ w ∂(volume : Measure ℂ),
        ‖μ w⁻¹‖ₑ ≤ eLpNormEssSup μ volume := by
      have h0 := enorm_ae_le_eLpNormEssSup μ (volume : Measure ℂ)
      rw [ae_iff] at h0 ⊢
      exact hqmp.preimage_null h0
    filter_upwards [ae_restrict_of_ae hCae] with w hw
    have hfac : ‖w ^ 2 / (starRingEnd ℂ w) ^ 2‖ ≤ 1 := by
      rcases eq_or_ne w 0 with rfl | hw0
      · simp
      · have hnz : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
        have h1 : ‖w ^ 2 / (starRingEnd ℂ w) ^ 2‖ = 1 := by
          rw [norm_div, norm_pow, norm_pow, Complex.norm_conj,
            div_self (pow_ne_zero 2 hnz)]
        exact h1.le
    calc ‖w ^ 2 / (starRingEnd ℂ w) ^ 2 * μ w⁻¹‖
        ≤ ‖μ w⁻¹‖ := by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) hfac
      _ ≤ (eLpNormEssSup μ volume).toReal := by
          rw [← ofReal_norm] at hw
          exact (ENNReal.ofReal_le_iff_le_toReal hb.ne).mp hw
  -- ===== the Cauchy-transform calculus for the two pieces =====
  have h24 : (2:ℝ≥0∞) < 4 := by norm_num
  have h4top : (4:ℝ≥0∞) ≠ ⊤ := by norm_num
  have hP1cont : Continuous (cauchyTransform (ballTruncation μ)) :=
    continuous_cauchyTransform_of_memLp_of_support h24 h4top hballmem hballsupp
  have hP2cont : Continuous (cauchyTransform (inftyChartCoeff μ)) :=
    continuous_cauchyTransform_of_memLp_of_support h24 h4top hinftymem hinftysupp
  have hP1co : Tendsto (cauchyTransform (ballTruncation μ))
      (Filter.cocompact ℂ) (𝓝 0) :=
    cauchyTransform_tendsto_cocompact h24 h4top hballmem hballsupp
  have hP2co : Tendsto (cauchyTransform (inftyChartCoeff μ))
      (Filter.cocompact ℂ) (𝓝 0) :=
    cauchyTransform_tendsto_cocompact h24 h4top hinftymem hinftysupp
  -- ===== filter tools at the puncture =====
  have hinvT : Tendsto (fun z : ℂ => z⁻¹) (𝓝[≠] (0:ℂ)) (Filter.cocompact ℂ) := by
    rw [← cobounded_eq_cocompact]
    exact tendsto_inv₀_nhdsNE_zero
  have hsq : Tendsto (fun w : ℂ => w ^ 2) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
    have h : Tendsto (fun w : ℂ => w ^ 2) (𝓝 (0:ℂ)) (𝓝 0) := by
      simpa using (continuous_pow 2).tendsto (0:ℂ)
    exact h.mono_left nhdsWithin_le_nhds
  have hvanish : ∀ q : ℂ → ℂ, Tendsto q (Filter.cocompact ℂ) (𝓝 0) →
      Tendsto (fun w : ℂ => w ^ 2 * q w⁻¹) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
    intro q hq
    have h := hsq.mul (hq.comp hinvT)
    simpa [Function.comp] using h
  constructor
  · -- ===== continuity of the solver =====
    have hGcont : Continuous
        (fun z : ℂ => z ^ 2 * cauchyTransform (inftyChartCoeff μ) z⁻¹) := by
      rw [continuous_iff_continuousAt]
      intro z₀
      rcases eq_or_ne z₀ 0 with rfl | hz₀
      · -- at the origin the vanishing prefactor forces the limit `0 = value`
        have hpunc := hvanish _ hP2co
        have hpure : Tendsto
            (fun z : ℂ => z ^ 2 * cauchyTransform (inftyChartCoeff μ) z⁻¹)
            (pure (0:ℂ)) (𝓝 0) := by
          rw [Filter.tendsto_pure_left]
          intro s hs
          simpa using mem_of_mem_nhds hs
        have hdecomp : (𝓝 (0:ℂ)) = pure (0:ℂ) ⊔ 𝓝[≠] (0:ℂ) := by
          rw [← nhdsWithin_univ, ← Set.union_compl_self ({(0:ℂ)} : Set ℂ),
            nhdsWithin_union, nhdsWithin_singleton]
        have hgoal : Tendsto
            (fun z : ℂ => z ^ 2 * cauchyTransform (inftyChartCoeff μ) z⁻¹)
            (𝓝 (0:ℂ)) (𝓝 0) := by
          nth_rewrite 1 [hdecomp]
          exact Filter.tendsto_sup.mpr ⟨hpure, hpunc⟩
        have hv0 : (0:ℂ) ^ 2 * cauchyTransform (inftyChartCoeff μ) (0:ℂ)⁻¹ = 0 := by
          simp
        change Tendsto (fun z : ℂ => z ^ 2 * cauchyTransform (inftyChartCoeff μ) z⁻¹)
          (𝓝 (0:ℂ)) (𝓝 ((0:ℂ) ^ 2 * cauchyTransform (inftyChartCoeff μ) (0:ℂ)⁻¹))
        rw [hv0]
        exact hgoal
      · exact ((continuous_pow 2).continuousAt).mul
          (hP2cont.continuousAt.comp (continuousAt_inv₀ hz₀))
    exact hP1cont.sub hGcont
  · -- ===== the infinity-chart limit =====
    refine ⟨-cauchyTransform (inftyChartCoeff μ) 0, ?_⟩
    -- for `w ≠ 0` the reading simplifies: `w²·(w⁻¹)² = 1` and `(w⁻¹)⁻¹ = w`
    have hEq : ∀ w : ℂ, w ≠ 0 →
        w ^ 2 * cauchyTransform (ballTruncation μ) w⁻¹
          - cauchyTransform (inftyChartCoeff μ) w
          = w ^ 2 * dbarSolver μ w⁻¹ := by
      intro w hw
      simp only [dbarSolver, inv_inv]
      have h1 : w ^ 2 * (w⁻¹) ^ 2 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]
      linear_combination cauchyTransform (inftyChartCoeff μ) w * h1
    have hT1 := hvanish _ hP1co
    have hT2 : Tendsto (cauchyTransform (inftyChartCoeff μ)) (𝓝[≠] (0:ℂ))
        (𝓝 (cauchyTransform (inftyChartCoeff μ) 0)) :=
      (hP2cont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hsub := hT1.sub hT2
    rw [zero_sub] at hsub
    refine Filter.Tendsto.congr' ?_ hsub
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hEq w hw

end NoWanderingDomains
