/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Sobolev.WeakDeriv
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Order.Zorn

/-!
# Morrey oscillation bound for super-critical Sobolev functions on `ℂ`

For `p > 2` a continuous function `f : ℂ → ℂ` with weak gradient `(gx, gy) ∈ Lᵖ_loc`
satisfies the quantitative Morrey oscillation estimate: on every ball the oscillation
of `f` is controlled by `r ^ (1 - 2/p)` times the local `Lᵖ` energy of the gradient.
This is the `C¹`-Morrey estimate transported to the weak-gradient setting via
mollification and the `δ → 0` limit.

The Lusin (N) consequence is built on top of this estimate in
`Analysis/Sobolev/Morrey/LusinN.lean`.
-/

open MeasureTheory Complex Metric Set Function
open scoped ContDiff ENNReal NNReal Convolution Topology

namespace NoWanderingDomains

set_option maxHeartbeats 400000 in
-- This proof inlines the entire `C¹` Morrey estimate, the mollifier `Lᵖ`-bound,
-- and the weak-derivative/mollifier bridge as nested `have`s, then performs the
-- `δ → 0` mollification limit; the resulting elaboration needs the raised budget.
theorem exists_morrey_oscillation_bound {p : ℝ} (hp : 2 < p) {f gx gy : ℂ → ℂ}
    (hf : Continuous f) (hgrad : HasWeakGradient gx gy f Set.univ)
    (hgx : MemLpLocOn gx (ENNReal.ofReal p) Set.univ)
    (hgy : MemLpLocOn gy (ENNReal.ofReal p) Set.univ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℂ) (r : ℝ), 0 < r → ∀ y ∈ Metric.closedBall x r,
      ‖f y - f x‖ ≤ C * r ^ (1 - 2 / p) *
        (∫ z in Metric.ball x (2 * r), ‖gx z‖ ^ p + ‖gy z‖ ^ p) ^ (1 / p) := by
  -- Basic numerology for `p`.
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  -- The conjugate exponent `p' = p/(p-1)`, which satisfies `p' < 2` since `p > 2`.
  set p' : ℝ := p / (p - 1) with hp'def
  have hpm1 : (0 : ℝ) < p - 1 := by linarith
  have hp'pos : 0 < p' := by rw [hp'def]; positivity
  have hp'lt2 : p' < 2 := by
    rw [hp'def, div_lt_iff₀ hpm1]; linarith
  -- `gx`, `gy` are locally integrable: on any compact `K`, `MemLp` at `ofReal p ≥ 1` gives `L¹`.
  have hp_ne_top : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hp1.le
  have hgxloc : LocallyIntegrable gx (volume : Measure ℂ) := by
    rw [locallyIntegrable_iff]
    intro K hK
    have hmemlp : MemLp gx (ENNReal.ofReal p) (volume.restrict K) := hgx K (Set.subset_univ _) hK
    have : IsFiniteMeasure (volume.restrict K) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top
    exact hmemlp.integrable hp_one_le
  have hgyloc : LocallyIntegrable gy (volume : Measure ℂ) := by
    rw [locallyIntegrable_iff]
    intro K hK
    have hmemlp : MemLp gy (ENNReal.ofReal p) (volume.restrict K) := hgy K (Set.subset_univ _) hK
    have : IsFiniteMeasure (volume.restrict K) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top
    exact hmemlp.integrable hp_one_le
  have hfloc : LocallyIntegrable f (volume : Measure ℂ) := hf.locallyIntegrable
  -- INLINED PILLAR 3 (bridge)
  have bridge : ∀ {v : ℂ} {f g : ℂ → ℂ}
    (hf : Continuous f) (hgloc : MeasureTheory.LocallyIntegrable g (volume : Measure ℂ))
    (hweak : ∀ ψ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
       ∫ z, ((fderiv ℝ ψ z) v) • f z = - ∫ z, ψ z • g z)
    {φ : ℂ → ℝ} (hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφsupp : HasCompactSupport φ) (z : ℂ),
      (fderiv ℝ (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] f) z) v
      = (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] g) z := by
    intro v f g hf hgloc hweak φ hφsmooth hφsupp z
    -- `f` is locally integrable, and `φ` is `C¹`
    have hfloc : LocallyIntegrable f (volume : Measure ℂ) := hf.locallyIntegrable
    have h1 : ContDiff ℝ 1 φ := hφsmooth.of_le (by exact_mod_cast le_top)
    -- continuity/compact-support of `fderiv φ`
    have hcontderiv : Continuous (fderiv ℝ φ) := h1.continuous_fderiv (by norm_num)
    have hcompactderiv : HasCompactSupport (fderiv ℝ φ) := hφsupp.fderiv ℝ
    -- step 2: total derivative of the convolution (convolution differentiated on the left)
    have hfderiv :
        HasFDerivAt (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] f)
          ((fderiv ℝ φ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ,
              (volume : Measure ℂ)] f) z) z :=
      hφsupp.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) h1 hfloc z
    rw [hfderiv.fderiv]
    -- step 2': push the evaluation `· v` inside the convolution integral.
    -- We establish integrability of the (CLM-valued) integrand by hand from its
    -- continuity and compact support, avoiding the (very slow) `precompL`
    -- instance search inside `convolutionExists_left`.
    have hfcomp : Continuous (fun t => f (z - t)) :=
      hf.comp (continuous_const.sub continuous_id)
    have hcontCLM :
        Continuous (fun t => (((ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ)
          (fderiv ℝ φ t)) (f (z - t))) :=
      (((ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ).continuous.comp hcontderiv).clm_apply hfcomp
    have hsubCLM :
        Function.support (fun t => (((ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ)
          (fderiv ℝ φ t)) (f (z - t)))
          ⊆ Function.support (fderiv ℝ φ) := by
      intro t ht
      simp only [Function.mem_support] at ht ⊢
      intro hzero
      apply ht
      rw [hzero]
      simp
    have hcsCLM :
        HasCompactSupport (fun t => (((ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ)
          (fderiv ℝ φ t)) (f (z - t))) :=
      hcompactderiv.mono hsubCLM
    have hintCLM :
        Integrable (fun t => (((ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ)
          (fderiv ℝ φ t)) (f (z - t))) (volume : Measure ℂ) :=
      hcontCLM.integrable_of_hasCompactSupport hcsCLM
    have hstep2 :
        ((fderiv ℝ φ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ,
            (volume : Measure ℂ)] f) z) v
          = ∫ t, ((fderiv ℝ φ t) v) • f (z - t) ∂(volume : Measure ℂ) := by
      rw [convolution_def, ContinuousLinearMap.integral_apply hintCLM]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
    rw [hstep2]
    -- step 3: substitute s = z - t  (volume is neg- and left-invariant)
    have hsubst :
        ∫ t, ((fderiv ℝ φ t) v) • f (z - t) ∂(volume : Measure ℂ)
          = ∫ s, ((fderiv ℝ φ (z - s)) v) • f s ∂(volume : Measure ℂ) := by
      have key := integral_sub_left_eq_self
        (fun s : ℂ => ((fderiv ℝ φ (z - s)) v) • f s) (volume : Measure ℂ) z
      simp only [sub_sub_cancel] at key
      exact key
    rw [hsubst]
    -- step 4: apply the weak-derivative hypothesis to the test function ψ s := φ (z - s)
    set ψ : ℂ → ℝ := fun s => φ (z - s) with hψdef
    have hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
      hφsmooth.comp (contDiff_const.sub contDiff_id)
    have hψsupp : HasCompactSupport ψ := by
      have hrw : ψ = φ ∘ (Homeomorph.subLeft z) := by
        ext s; simp [hψdef, Homeomorph.subLeft]
      rw [hrw]
      exact hφsupp.comp_homeomorph (Homeomorph.subLeft z)
    -- chain rule: (fderiv ψ s) v = - (fderiv φ (z - s)) v
    have hchain : ∀ s : ℂ, (fderiv ℝ ψ s) v = -((fderiv ℝ φ (z - s)) v) := by
      intro s
      have hm : HasFDerivAt (fun s : ℂ => z - s) (-ContinuousLinearMap.id ℝ ℂ) s :=
        (hasFDerivAt_id s).const_sub z
      have hφd : HasFDerivAt φ (fderiv ℝ φ (z - s)) (z - s) :=
        (h1.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have hcomp : HasFDerivAt ψ
          ((fderiv ℝ φ (z - s)).comp (-ContinuousLinearMap.id ℝ ℂ)) s := hφd.comp s hm
      rw [hcomp.fderiv]
      simp
    -- weak-derivative identity for ψ
    have hweakψ := hweak ψ hψsmooth hψsupp
    -- rewrite the LHS of hweakψ using the chain rule
    have hLHS : ∫ s, ((fderiv ℝ ψ s) v) • f s ∂(volume : Measure ℂ)
        = - ∫ s, ((fderiv ℝ φ (z - s)) v) • f s ∂(volume : Measure ℂ) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only []
      rw [hchain s]
      exact neg_smul ((fderiv ℝ φ (z - s)) v) (f s)
    rw [hLHS] at hweakψ
    -- now hweakψ : - ∫ s, (fderiv φ (z-s)) v • f s = - ∫ s, ψ s • g s
    have hfinal : ∫ s, ((fderiv ℝ φ (z - s)) v) • f s ∂(volume : Measure ℂ)
        = ∫ s, ψ s • g s ∂(volume : Measure ℂ) := neg_injective hweakψ
    rw [hfinal]
    -- step 5: RHS = (φ ⋆ g) z  via convolution_lsmul_swap
    rw [convolution_lsmul_swap]
  -- INLINED PILLAR 2 (molli_bound)
  have molli_bound : ∀ {p : ℝ} (hp : 1 ≤ p) {φ : ℂ → ℝ}
    (hφnonneg : ∀ w, 0 ≤ φ w) (hφint : ∫ w, φ w = 1)
    (hφcont : Continuous φ) (hφsupp : HasCompactSupport φ) {δ : ℝ} (hδ : 0 < δ)
    (hφsupp' : Function.support φ ⊆ Metric.ball (0 : ℂ) δ)
    {g : ℂ → ℂ} (hgmeas : AEStronglyMeasurable g (volume : Measure ℂ))
    (hgsupp : HasCompactSupport g)
    (hgLp : MemLp g (ENNReal.ofReal p) (volume : Measure ℂ))
    (x : ℂ) {ρ : ℝ} (hρ : 0 < ρ), ∫ z in Metric.ball x ρ,
        ‖(φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] g) z‖ ^ p
      ≤ ∫ z in Metric.ball x (ρ + δ), ‖g z‖ ^ p := by
    intro p hp φ hφnonneg hφint hφcont hφsupp δ hδ hφsupp' g hgmeas hgsupp hgLp x ρ hρ
    have hp0 : p ≠ 0 := by linarith
    have hp_pos : 0 < p := by linarith
    -- `ENNReal.ofReal p` facts
    have hp_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]; exact ENNReal.ofReal_le_ofReal hp
    have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
    have hp_toReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp_pos.le
    -- volume on ℂ is invariant under negation
    have hneg : (volume : Measure ℂ).IsNegInvariant := by infer_instance
    -- abbreviations
    set G : ℂ → ℝ := fun u => ‖g u‖ ^ p with hG
    have hGnonneg : ∀ u, 0 ≤ G u := fun u => by positivity
    -- `‖g‖ ^ p` is integrable from MemLp at exponent `ofReal p`
    have hGint : Integrable G (volume : Measure ℂ) := by
      have := hgLp.integrable_norm_rpow hp_ne_zero ENNReal.ofReal_ne_top
      rwa [hp_toReal] at this
    -- `g` is locally integrable from MemLp at exponent `≥ 1`
    have hgloc : LocallyIntegrable g (volume : Measure ℂ) := hgLp.locallyIntegrable hp_le
    have hφintegrable : Integrable φ (volume : Measure ℂ) :=
      hφcont.integrable_of_hasCompactSupport hφsupp
    ------------------------------------------------------------------
    -- STEP 1 : pointwise Jensen
    --   ‖(φ ⋆ g) z‖ ^ p ≤ ∫ w, φ w * ‖g (z - w)‖ ^ p
    ------------------------------------------------------------------
    have jensen : ∀ z : ℂ,
        ‖(φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] g) z‖ ^ p
          ≤ ∫ w, φ w * ‖g (z - w)‖ ^ p := by
      intro z
      -- probability density measure μφ
      set d : ℂ → NNReal := fun w => (φ w).toNNReal with hd
      have hdmeas : Measurable d := measurable_real_toNNReal.comp hφcont.measurable
      have hdcoe : ∀ w, (d w : ℝ) = φ w := fun w => Real.coe_toNNReal _ (hφnonneg w)
      set μφ : Measure ℂ := (volume : Measure ℂ).withDensity (fun w => (d w : ℝ≥0∞)) with hμφ
      have hprob : IsProbabilityMeasure μφ := by
        constructor
        rw [hμφ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        have h1 : ∫⁻ w, (d w : ℝ≥0∞) ∂(volume : Measure ℂ)
            = ENNReal.ofReal (∫ w, (d w : ℝ) ∂volume) :=
          lintegral_coe_eq_integral d (by simpa only [hdcoe] using hφintegrable)
        rw [h1]
        have h2 : (∫ w, (d w : ℝ) ∂(volume : Measure ℂ)) = 1 := by
          simp_rw [hdcoe]; exact hφint
        rw [h2]; simp
      -- abbreviation `h := ‖g (z - ·)‖`
      set h : ℂ → ℝ := fun w => ‖g (z - w)‖ with hh
      have hh_nonneg : ∀ w, 0 ≤ h w := fun w => norm_nonneg _
      -- `w ↦ ‖g (z - w)‖ ^ p` is integrable over volume (translation of `G`)
      have hGtrans : Integrable (fun w => ‖g (z - w)‖ ^ p) (volume : Measure ℂ) :=
        hGint.comp_sub_left z
      -- `w ↦ g (z - w)` is `AEStronglyMeasurable`
      have hgz_aesm : AEStronglyMeasurable (fun w => g (z - w)) (volume : Measure ℂ) :=
        hgmeas.comp_quasiMeasurePreserving
          (Measure.measurePreserving_sub_left volume z).quasiMeasurePreserving
      have hh_aesm : AEStronglyMeasurable h (volume : Measure ℂ) := hgz_aesm.norm
      -- `w ↦ g (z - w)` is locally integrable
      have hgz_loc : LocallyIntegrable (fun w => g (z - w)) (volume : Measure ℂ) := by
        rw [locallyIntegrable_iff]
        intro K hK
        have hemb : MeasurableEmbedding (fun w : ℂ => z - w) :=
          (Homeomorph.subLeft z).measurableEmbedding
        have hmp : MeasurePreserving (fun w : ℂ => z - w)
            (volume : Measure ℂ) (volume : Measure ℂ) :=
          Measure.measurePreserving_sub_left volume z
        exact (hmp.integrableOn_image hemb (f := g) (s := K)).mp
          (hgloc.integrableOn_isCompact (hK.image (by fun_prop)))
      -- `h = ‖g (z - ·)‖` is locally integrable
      have hh_loc : LocallyIntegrable h (volume : Measure ℂ) := by
        rw [locallyIntegrable_iff]
        intro K hK
        exact (hgz_loc.integrableOn_isCompact hK).norm
      -- `φ · h ^ p` integrable over volume
      have hφhp_int : Integrable (fun w => φ w * (h w ^ p)) (volume : Measure ℂ) := by
        have := hGtrans.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
          (g := φ) hφcont hφsupp
        simpa [smul_eq_mul] using this
      -- `φ · h` integrable over volume
      have hφh_int : Integrable (fun w => φ w * (h w)) (volume : Measure ℂ) := by
        have := hh_loc.integrable_smul_left_of_hasCompactSupport (g := φ) hφcont hφsupp
        simpa [smul_eq_mul] using this
      -- transfer integrabilities to `μφ`
      have hh_int : Integrable h μφ := by
        rw [hμφ, integrable_withDensity_iff_integrable_smul hdmeas]
        apply hφh_int.congr
        filter_upwards with w
        rw [NNReal.smul_def, smul_eq_mul, hdcoe w]
      have hhp_int : Integrable (fun w => h w ^ p) μφ := by
        rw [hμφ, integrable_withDensity_iff_integrable_smul hdmeas]
        apply hφhp_int.congr
        filter_upwards with w
        rw [NNReal.smul_def, smul_eq_mul, hdcoe w]
      -- convolution = ∫ g(z - ·) ∂μφ
      have hconv_eq : (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] g) z
          = ∫ w, g (z - w) ∂μφ := by
        rw [convolution_def, hμφ, integral_withDensity_eq_integral_smul hdmeas]
        apply integral_congr_ae
        filter_upwards with w
        rw [ContinuousLinearMap.lsmul_apply]
        congr 1
        exact (hdcoe w).symm
      -- norm of integral ≤ integral of norm
      have hstepB : ‖∫ w, g (z - w) ∂μφ‖ ≤ ∫ w, h w ∂μφ :=
        norm_integral_le_integral_norm _
      -- Jensen for rpow under the probability measure μφ
      have hstepC : (∫ w, h w ∂μφ) ^ p ≤ ∫ w, h w ^ p ∂μφ := by
        have := (convexOn_rpow hp).map_integral_le (f := h) (μ := μφ)
          (continuousOn_id.rpow_const (fun _ _ => Or.inr (by linarith)))
          isClosed_Ici
          (Filter.Eventually.of_forall fun w => hh_nonneg w)
          hh_int hhp_int
        simpa using this
      -- convert ∫ h ^ p ∂μφ = ∫ φ w * ‖g (z - w)‖ ^ p
      have hstepD : (∫ w, h w ^ p ∂μφ) = ∫ w, φ w * ‖g (z - w)‖ ^ p := by
        rw [hμφ, integral_withDensity_eq_integral_smul hdmeas]
        apply integral_congr_ae
        filter_upwards with w
        rw [NNReal.smul_def, smul_eq_mul, hdcoe w]
      -- combine
      rw [hconv_eq]
      calc ‖∫ w, g (z - w) ∂μφ‖ ^ p
          ≤ (∫ w, h w ∂μφ) ^ p :=
            Real.rpow_le_rpow (norm_nonneg _) hstepB (by linarith)
        _ ≤ ∫ w, h w ^ p ∂μφ := hstepC
        _ = ∫ w, φ w * ‖g (z - w)‖ ^ p := hstepD
    ------------------------------------------------------------------
    -- STEP 2 : integrate the pointwise bound over ball x ρ
    ------------------------------------------------------------------
    -- the convolution `z ↦ ‖(φ ⋆ g) z‖ ^ p` is integrable on the ball
    have hconv_cont : Continuous (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] g) :=
      hφsupp.continuous_convolution_left _ hφcont hgloc
    have hLHS_cont : Continuous
        (fun z => ‖(φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] g) z‖ ^ p) :=
      hconv_cont.norm.rpow_const (fun _ => Or.inr (by linarith))
    have hLHS_intOn : IntegrableOn
        (fun z => ‖(φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] g) z‖ ^ p)
        (ball x ρ) (volume : Measure ℂ) :=
      (hLHS_cont.locallyIntegrable.integrableOn_isCompact
        (isCompact_closedBall x ρ)).mono_set ball_subset_closedBall
    -- joint integrability on the restricted product (for Fubini)
    have hAESM : AEStronglyMeasurable (uncurry (fun z w => φ w * ‖g (z - w)‖ ^ p))
        (((volume : Measure ℂ).restrict (ball x ρ)).prod (volume : Measure ℂ)) := by
      have hqmp : Measure.QuasiMeasurePreserving (fun pp : ℂ × ℂ => pp.1 - pp.2)
          (((volume : Measure ℂ).restrict (ball x ρ)).prod (volume : Measure ℂ))
          (volume : Measure ℂ) := by
        refine QuasiMeasurePreserving.prod_of_left (measurable_fst.sub measurable_snd) ?_
        filter_upwards with w
        refine Measure.QuasiMeasurePreserving.mono_left ?_
          Measure.restrict_le_self.absolutelyContinuous
        exact (measurePreserving_sub_right (volume : Measure ℂ) w).quasiMeasurePreserving
      have hg_comp : AEStronglyMeasurable (fun pp : ℂ × ℂ => g (pp.1 - pp.2))
          (((volume : Measure ℂ).restrict (ball x ρ)).prod (volume : Measure ℂ)) :=
        hgmeas.comp_quasiMeasurePreserving hqmp
      apply AEStronglyMeasurable.mul
      · exact hφcont.comp_aestronglyMeasurable (continuous_snd.aestronglyMeasurable)
      · apply Continuous.comp_aestronglyMeasurable (g := fun t : ℝ => t ^ p) ?_ hg_comp.norm
        exact continuous_id.rpow_const (fun _ => Or.inr (by linarith))
    have hF_prod_int : Integrable (uncurry (fun z w => φ w * ‖g (z - w)‖ ^ p))
        (((volume : Measure ℂ).restrict (ball x ρ)).prod (volume : Measure ℂ)) := by
      rw [integrable_prod_iff' hAESM]
      refine ⟨?_, ?_⟩
      · filter_upwards with w
        exact (hGint.comp_sub_right w).integrableOn.const_mul (φ w)
      · set C0 : ℝ := ∫ z, ‖g z‖ ^ p with hC0
        have hbound : ∀ w, (∫ z in ball x ρ,
              ‖uncurry (fun z w => φ w * ‖g (z - w)‖ ^ p) (z, w)‖) ≤ |φ w| * C0 := by
          intro w
          have hGtrans : Integrable (fun z => ‖g (z - w)‖ ^ p) (volume : Measure ℂ) :=
            hGint.comp_sub_right w
          have heq : (fun z => ‖uncurry (fun z w => φ w * ‖g (z - w)‖ ^ p) (z, w)‖)
              = fun z => |φ w| * ‖g (z - w)‖ ^ p := by
            funext z
            simp only [uncurry]
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hGnonneg _)]
          rw [heq, integral_const_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc (∫ z in ball x ρ, ‖g (z - w)‖ ^ p) ≤ ∫ z, ‖g (z - w)‖ ^ p :=
                setIntegral_le_integral hGtrans
                  (Filter.Eventually.of_forall (fun z => hGnonneg _))
            _ = C0 := integral_sub_right_eq_self (fun z => ‖g z‖ ^ p) w
        apply MeasureTheory.Integrable.mono' (g := fun w => |φ w| * C0)
        · exact ((hφcont.integrable_of_hasCompactSupport hφsupp).abs).mul_const C0
        · have hswap : AEStronglyMeasurable
              (fun pp => (uncurry (fun z w => φ w * ‖g (z - w)‖ ^ p)) pp.swap)
              ((volume : Measure ℂ).prod ((volume : Measure ℂ).restrict (ball x ρ))) :=
            hAESM.prod_swap
          have hres := hswap.norm.integral_prod_right'
          convert hres using 2
          simp
        · filter_upwards with w
          rw [Real.norm_eq_abs, abs_of_nonneg]
          · exact hbound w
          · apply integral_nonneg
            intro z
            simp only [uncurry, Pi.zero_apply]
            positivity
    -- integrability of the inner-integral function on the ball
    have hRHS_intOn : IntegrableOn (fun z => ∫ w, φ w * ‖g (z - w)‖ ^ p)
        (ball x ρ) (volume : Measure ℂ) :=
      hF_prod_int.integral_prod_left
    -- mono : LHS ≤ ∫ z in ball, (RHS pointwise)
    have step2 :
        ∫ z in ball x ρ, ‖(φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] g) z‖ ^ p
          ≤ ∫ z in ball x ρ, ∫ w, φ w * ‖g (z - w)‖ ^ p :=
      setIntegral_mono_on hLHS_intOn hRHS_intOn measurableSet_ball (fun z _ => jensen z)
    ------------------------------------------------------------------
    -- STEP 3 : Fubini swap
    ------------------------------------------------------------------
    have step3 : (∫ z in ball x ρ, ∫ w, φ w * ‖g (z - w)‖ ^ p)
        = ∫ w, ∫ z in ball x ρ, φ w * ‖g (z - w)‖ ^ p :=
      integral_integral_swap hF_prod_int
    ------------------------------------------------------------------
    -- STEP 4 : inner substitution + ball inclusion, bound by larger ball
    ------------------------------------------------------------------
    set C : ℝ := ∫ z in ball x (ρ + δ), ‖g z‖ ^ p with hC
    -- inner substitution lemma
    have inner_sub : ∀ w : ℂ,
        (∫ z in ball x ρ, ‖g (z - w)‖ ^ p) = ∫ u in ball (x - w) ρ, ‖g u‖ ^ p := by
      intro w
      rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
      have key : (fun z => (ball x ρ).indicator (fun z => ‖g (z - w)‖ ^ p) z)
            = (fun z => ((ball (x - w) ρ).indicator (fun u => ‖g u‖ ^ p)) (z - w)) := by
        ext z
        have hmem : z ∈ ball x ρ ↔ z - w ∈ ball (x - w) ρ := by
          simp only [mem_ball, dist_eq_norm, sub_sub_sub_cancel_right]
        by_cases hz : z ∈ ball x ρ
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hmem.mp hz)]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun hh => hz (hmem.mpr hh))]
      rw [key]
      exact integral_sub_right_eq_self _ w
    -- for each w, φ w * (inner integral) ≤ φ w * C
    have ptwise_bound : ∀ w : ℂ,
        φ w * (∫ z in ball x ρ, ‖g (z - w)‖ ^ p) ≤ φ w * C := by
      intro w
      rcases eq_or_ne (φ w) 0 with hφ0 | hφ0
      · simp [hφ0]
      · apply mul_le_mul_of_nonneg_left _ (hφnonneg w)
        rw [inner_sub w]
        have hwsupp : w ∈ Function.support φ := hφ0
        have hwball : w ∈ ball (0 : ℂ) δ := hφsupp' hwsupp
        have hwnorm : ‖w‖ < δ := by simpa [mem_ball, dist_eq_norm] using hwball
        have hsub : ball (x - w) ρ ⊆ ball x (ρ + δ) := by
          intro y hy
          simp only [mem_ball] at hy ⊢
          have htri : dist y x ≤ dist y (x - w) + dist (x - w) x := dist_triangle _ _ _
          have hd2 : dist (x - w) x = ‖w‖ := by rw [dist_eq_norm]; simp [norm_neg]
          calc dist y x ≤ dist y (x - w) + dist (x - w) x := htri
            _ < ρ + δ := by rw [hd2]; linarith
        have hCint : IntegrableOn (fun u => ‖g u‖ ^ p) (ball x (ρ + δ)) (volume : Measure ℂ) :=
          hGint.integrableOn
        exact setIntegral_mono_set hCint
          (Filter.Eventually.of_forall fun u => hGnonneg u)
          (Filter.Eventually.of_forall (fun y hy => hsub hy))
    ------------------------------------------------------------------
    -- STEP 5 : assemble
    ------------------------------------------------------------------
    have hInner_int : Integrable (fun w => φ w * ∫ z in ball x ρ, ‖g (z - w)‖ ^ p)
        (volume : Measure ℂ) := by
      have hpr := hF_prod_int.integral_prod_right
      simp only [uncurry] at hpr
      have hcongr : (fun w => ∫ z in ball x ρ, φ w * ‖g (z - w)‖ ^ p)
          = (fun w => φ w * ∫ z in ball x ρ, ‖g (z - w)‖ ^ p) := by
        funext w; rw [integral_const_mul]
      rw [hcongr] at hpr
      exact hpr
    have hConst_int : Integrable (fun w => φ w * C) (volume : Measure ℂ) :=
      hφintegrable.mul_const C
    calc
      ∫ z in ball x ρ, ‖(φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] g) z‖ ^ p
          ≤ ∫ z in ball x ρ, ∫ w, φ w * ‖g (z - w)‖ ^ p := step2
      _ = ∫ w, ∫ z in ball x ρ, φ w * ‖g (z - w)‖ ^ p := step3
      _ = ∫ w, φ w * ∫ z in ball x ρ, ‖g (z - w)‖ ^ p := by
            apply integral_congr_ae
            filter_upwards with w
            rw [integral_const_mul]
      _ ≤ ∫ w, φ w * C := integral_mono hInner_int hConst_int ptwise_bound
      _ = (∫ w, φ w) * C := integral_mul_const C φ ▸ by rw [integral_mul_const]
      _ = C := by rw [hφint, one_mul]
  -- INLINED PILLAR 1 (morrey_C1, with all nested helpers + C₀ + morrey_C1_bound)
  have negpow_ball_integral : ∀ (q : ℝ) (hq0 : 0 ≤ q) (hq2 : q < 2) (R : ℝ) (hR : 0 < R),
      ∫ w in Metric.ball (0 : ℂ) R, ‖w‖ ^ (-q) ≤ (2 * Real.pi / (2 - q)) * R ^ (2 - q) := by
    intro q hq0 hq2 R hR
    set f : ℝ → ℝ := fun t => if t < R then t ^ (-q) else 0 with hf
    -- Step 1: setIntegral over ball = full integral of f ‖·‖
    have hconv : ∫ w in Metric.ball (0 : ℂ) R, ‖w‖ ^ (-q) = ∫ x : ℂ, f ‖x‖ := by
      rw [← MeasureTheory.integral_indicator measurableSet_ball]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hx : x ∈ ball (0:ℂ) R
      · rw [Set.indicator_of_mem hx]
        simp only [hf]
        rw [mem_ball_zero_iff] at hx
        rw [if_pos hx]
      · rw [Set.indicator_of_notMem hx]
        simp only [hf]
        rw [mem_ball_zero_iff] at hx
        rw [if_neg hx]
    rw [hconv]
    -- Step 2: HaarToSphere reduction
    rw [integral_fun_norm_addHaar volume f, Complex.finrank_real_complex]
    -- Step 3: volume.real (ball 0 1) = π
    have hvol : volume.real (Metric.ball (0:ℂ) 1) = Real.pi := by
      rw [Measure.real, Complex.volume_ball]; simp
    rw [hvol]
    -- Step 4: compute the inner integral = R^(2-q)/(2-q)
    have hinner : ∫ (y : ℝ) in Ioi (0:ℝ), y ^ (2 - 1) • f y = R ^ (2 - q) / (2 - q) := by
      have hsub : ∫ (y : ℝ) in Ioi (0:ℝ), y ^ (2 - 1) • f y
                = ∫ (y : ℝ) in Ioo (0:ℝ) R, y ^ (2 - 1) • f y := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        · intro x hx
          simp only [mem_Ioo, mem_Ioi] at *
          exact hx.1
        · intro x hx
          simp only [mem_Ioi, mem_Ioo, mem_sdiff, not_and, not_lt] at hx
          obtain ⟨hx0, hxR⟩ := hx
          have hnlt : ¬ (x < R) := not_lt.mpr (hxR hx0)
          rw [hf]; simp only [if_neg hnlt, smul_zero]
      rw [hsub]
      have hcongr : ∫ (y : ℝ) in Ioo (0:ℝ) R, y ^ (2 - 1) • f y
                  = ∫ (y : ℝ) in Ioo (0:ℝ) R, y ^ (1 - q) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro y hy
        simp only [mem_Ioo] at hy
        rw [hf]
        simp only [if_pos hy.2]
        rw [pow_one, smul_eq_mul]
        rw [show y * y ^ (-q) = y ^ (1:ℝ) * y ^ (-q) by rw [Real.rpow_one]]
        rw [← Real.rpow_add hy.1]
        ring_nf
      rw [hcongr]
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le]
      rw [integral_rpow (Or.inl (by linarith))]
      have h1 : (1 : ℝ) - q + 1 = 2 - q := by ring
      rw [h1, Real.zero_rpow (by linarith)]
      ring
    rw [hinner]
    -- Step 5: final equality 2 • π • (R^(2-q)/(2-q)) = (2π/(2-q)) R^(2-q)
    rw [le_iff_lt_or_eq]; right
    rw [nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
  have ball_transl : ∀ (R : ℝ) (y : ℂ) (h : ℂ → ENNReal),
      ∫⁻ z in Metric.ball y R, h (z - y) = ∫⁻ w in Metric.ball (0:ℂ) R, h w := by
    intro R y h
    have hmem : ∀ z : ℂ, (z ∈ Metric.ball y R) ↔ (z - y ∈ Metric.ball (0:ℂ) R) := by
      intro z; simp only [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc ∫⁻ z in Metric.ball y R, h (z - y)
        = ∫⁻ z, (Metric.ball y R).indicator (fun z => h (z - y)) z := by
          rw [lintegral_indicator measurableSet_ball]
      _ = ∫⁻ z, (Metric.ball (0:ℂ) R).indicator h (z - y) := by
          apply lintegral_congr; intro z; unfold Set.indicator
          by_cases hz : z ∈ Metric.ball y R
          · rw [if_pos hz, if_pos ((hmem z).mp hz)]
          · rw [if_neg hz, if_neg (fun hc => hz ((hmem z).mpr hc))]
      _ = ∫⁻ z, (Metric.ball (0:ℂ) R).indicator h z := lintegral_sub_right_eq_self _ y
      _ = ∫⁻ w in Metric.ball (0:ℂ) R, h w := by rw [lintegral_indicator measurableSet_ball]
  -- Integrability of ‖·‖^(-pp) on ball 0 R for pp < 2 in ℂ.
  have negpow_integrableOn_ball : ∀ (pp : ℝ) (hpp0 : 0 < pp) (hpp2 : pp < 2) (R : ℝ) (hR : 0 < R),
      IntegrableOn (fun w : ℂ => ‖w‖ ^ (-pp)) (Metric.ball (0:ℂ) R) volume := by
    intro pp hpp0 hpp2 R hR
    rw [← integrable_indicator_iff measurableSet_ball]
    set F : ℝ → ℝ := fun t : ℝ => if t < R then t ^ (-pp) else 0 with hF
    have heq : (Metric.ball (0:ℂ) R).indicator (fun w : ℂ => ‖w‖ ^ (-pp))
        = (fun w : ℂ => F ‖w‖) := by
      funext w
      simp only [Set.indicator, hF]
      by_cases hw : w ∈ Metric.ball (0:ℂ) R
      · rw [if_pos hw]
        have : ‖w‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        rw [if_pos this]
      · rw [if_neg hw]
        have : ¬ ‖w‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        rw [if_neg this]
    rw [heq]
    rw [show (fun w : ℂ => F ‖w‖) = (F ‖·‖) from rfl]
    rw [integrable_fun_norm_addHaar volume]
    rw [Complex.finrank_real_complex]
    have hbase : IntegrableOn ((Ioo (0:ℝ) R).indicator (fun y : ℝ => y ^ (1 - pp)))
        (Ioi 0) volume := by
      rw [integrableOn_indicator_iff measurableSet_Ioo]
      have hsub : Ioo (0:ℝ) R ∩ Ioi 0 = Ioo (0:ℝ) R := by
        apply Set.inter_eq_left.mpr
        intro y hy; exact hy.1
      rw [hsub, intervalIntegral.integrableOn_Ioo_rpow_iff hR]
      linarith
    apply hbase.congr_fun _ measurableSet_Ioi
    intro y hy
    simp only [Set.mem_Ioi] at hy
    simp only [hF, smul_eq_mul, Set.indicator]
    by_cases hyR : y < R
    · rw [if_pos ⟨hy, hyR⟩, if_pos hyR]
      rw [show (1 - pp) = (1 : ℝ) + (-pp) by ring, Real.rpow_add hy, Real.rpow_one]
      norm_num
    · rw [if_neg (fun h => hyR h.2), if_neg hyR, mul_zero]
  have kernel_bound : ∀ (pp : ℝ) (hpp0 : 0 < pp) (hpp2 : pp < 2) (x : ℂ) (r : ℝ) (hr : 0 < r)
    (y : ℂ) (hy : y ∈ Metric.closedBall x r),
      ∫⁻ z in Metric.ball x (2*r), (ENNReal.ofReal ‖z - y‖⁻¹) ^ pp ≤
      ENNReal.ofReal ((2 * Real.pi / (2 - pp)) * (3*r) ^ (2 - pp)) := by
    intro pp hpp0 hpp2 x r hr y hy
    -- Step 1: subset ball x 2r ⊆ ball y 3r
    have hsub : Metric.ball x (2*r) ⊆ Metric.ball y (3*r) := by
      intro z hz
      simp only [Metric.mem_ball, dist_eq_norm] at hz ⊢
      simp only [Metric.mem_closedBall, dist_eq_norm] at hy
      calc ‖z - y‖ = ‖(z - x) + (x - y)‖ := by ring_nf
        _ ≤ ‖z - x‖ + ‖x - y‖ := norm_add_le _ _
        _ < 2*r + r := by rw [show ‖x - y‖ = ‖y - x‖ from norm_sub_rev x y]; linarith
        _ = 3*r := by ring
    -- abbreviation for the kernel
    set K : ℂ → ENNReal := fun z => (ENNReal.ofReal ‖z - y‖⁻¹) ^ pp with hK
    -- Step 2: monotone over larger set
    have h3r : (0:ℝ) < 3*r := by positivity
    calc ∫⁻ z in Metric.ball x (2*r), K z
        ≤ ∫⁻ z in Metric.ball y (3*r), K z := lintegral_mono_set hsub
      -- Step 3: translate to origin
      _ = ∫⁻ w in Metric.ball (0:ℂ) (3*r), (ENNReal.ofReal ‖w‖⁻¹) ^ pp := by
          have := ball_transl (3*r) y (fun w => (ENNReal.ofReal ‖w‖⁻¹) ^ pp)
          simpa [hK] using this
      -- Step 4: pointwise rpow identity
      _ = ∫⁻ w in Metric.ball (0:ℂ) (3*r), ENNReal.ofReal (‖w‖ ^ (-pp)) := by
          apply lintegral_congr
          intro w
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hpp0.le]
          congr 1
          rw [Real.rpow_neg (norm_nonneg _), ← Real.inv_rpow (norm_nonneg _)]
      -- Step 5: lintegral = ofReal Bochner
      _ = ENNReal.ofReal (∫ w in Metric.ball (0:ℂ) (3*r), ‖w‖ ^ (-pp)) := by
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
          · exact negpow_integrableOn_ball pp hpp0 hpp2 (3*r) h3r
          · filter_upwards with w using Real.rpow_nonneg (norm_nonneg _) _
      -- Step 6: apply helper
      _ ≤ ENNReal.ofReal ((2 * Real.pi / (2 - pp)) * (3*r) ^ (2 - pp)) := by
          apply ENNReal.ofReal_le_ofReal
          exact negpow_ball_integral pp hpp0.le hpp2 (3*r) h3r
  have morrey_slice : ∀ (g : ℂ → ENNReal) (x y : ℂ) (r : ℝ) (hr : 0 < r)
    (s : ℝ) (hs : 0 < s),
      (∫⁻ a in Metric.ball x r, g (y + (s:ℂ) • (a - y)) * ENNReal.ofReal ‖a - y‖)
    = ∫⁻ z in Metric.ball (y + (s:ℂ) • (x - y)) (s * r),
        g z * ENNReal.ofReal ‖z - y‖ * ENNReal.ofReal (s^3)⁻¹ := by
    intro g x y r hr s hs
    have hsc : (s:ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hderiv : ∀ a ∈ Metric.ball x r,
        HasFDerivWithinAt (fun a => y + (s:ℂ) • (a - y))
          ((s:ℝ) • (ContinuousLinearMap.id ℝ ℂ)) (Metric.ball x r) a := by
      intro a _
      have hfun : (fun a : ℂ => y + (s:ℂ) • (a - y))
          = (fun a : ℂ => (s:ℝ) • a + (y - (s:ℝ) • y)) := by
        funext z; simp [Complex.real_smul]; ring
      rw [hfun]
      have hbase : HasFDerivAt (fun a : ℂ => (s:ℝ) • a)
          ((s:ℝ) • ContinuousLinearMap.id ℝ ℂ) a := by
        have := ContinuousLinearMap.hasFDerivAt ((s:ℝ) • ContinuousLinearMap.id ℝ ℂ) (x := a)
        convert this using 1
        ext z
        simp
      have hall : HasFDerivAt (fun a : ℂ => (s:ℝ) • a + (y - (s:ℝ) • y))
          ((s:ℝ) • ContinuousLinearMap.id ℝ ℂ) a :=
        (hasFDerivAt_add_const_iff (y - (s:ℝ) • y)).mpr hbase
      exact hall.hasFDerivWithinAt
    have hinj : Set.InjOn (fun a => y + (s:ℂ) • (a - y)) (Metric.ball x r) := by
      intro a _ b _ hab
      simp only at hab
      have h1 : (s:ℂ) • (a - y) = (s:ℂ) • (b - y) := add_left_cancel hab
      have h2 : a - y = b - y := smul_right_injective ℂ hsc h1
      exact sub_left_inj.mp h2
    have hdet : ((s:ℝ) • (ContinuousLinearMap.id ℝ ℂ)).det = s^2 := by
      rw [ContinuousLinearMap.det]
      simp only [ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.coe_id]
      rw [LinearMap.det_smul]
      simp [Complex.finrank_real_complex, sq]
    have himg : (fun a => y + (s:ℂ) • (a - y)) '' (Metric.ball x r)
        = Metric.ball (y + (s:ℂ) • (x - y)) (s * r) := by
      ext z
      simp only [Set.mem_image, Metric.mem_ball]
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [Complex.dist_eq]
        have hsub : y + (s:ℂ) • (a - y) - (y + (s:ℂ) • (x - y)) = (s:ℂ) • (a - x) := by
          simp only [smul_sub]; ring
        rw [hsub, norm_smul]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
        rw [Complex.dist_eq] at ha
        exact mul_lt_mul_of_pos_left ha hs
      · intro hz
        refine ⟨y + (s:ℂ)⁻¹ • (z - y), ?_, ?_⟩
        · rw [Complex.dist_eq]
          have heq : y + (s:ℂ)⁻¹ • (z - y) - x = (s:ℂ)⁻¹ • (z - (y + (s:ℂ) • (x - y))) := by
            simp only [smul_eq_mul]; field_simp; ring
          rw [heq, norm_smul]
          simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
          rw [Complex.dist_eq] at hz
          rw [inv_mul_lt_iff₀ hs]
          linarith [hz]
        · rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hsc, one_smul]
          abel
    have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure ℂ)
      (measurableSet_ball) hderiv hinj
      (fun z => g z * ENNReal.ofReal ‖z - y‖ * ENNReal.ofReal (s^3)⁻¹)
    rw [himg] at hcov
    rw [hcov]
    apply setLIntegral_congr_fun measurableSet_ball
    intro a _
    rw [hdet]
    simp only []
    have hnorm : ‖y + (s:ℂ) • (a - y) - y‖ = s * ‖a - y‖ := by
      rw [add_sub_cancel_left, norm_smul]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    rw [hnorm]
    rw [abs_of_pos (by positivity : (0:ℝ) < s^2)]
    rw [show ENNReal.ofReal (s * ‖a - y‖) = ENNReal.ofReal s * ENNReal.ofReal ‖a - y‖ from
      (ENNReal.ofReal_mul hs.le)]
    have hscalar : ENNReal.ofReal (s^2) * ENNReal.ofReal s * ENNReal.ofReal (s^3)⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      rw [show s^2 * s * (s^3)⁻¹ = 1 by field_simp]
      simp
    rw [show ENNReal.ofReal (s ^ 2) *
          (g (y + (s:ℂ) • (a - y)) * (ENNReal.ofReal s * ENNReal.ofReal ‖a - y‖)
            * ENNReal.ofReal (s ^ 3)⁻¹)
        = (ENNReal.ofReal (s^2) * ENNReal.ofReal s * ENNReal.ofReal (s^3)⁻¹)
          * (g (y + (s:ℂ) • (a - y)) * ENNReal.ofReal ‖a - y‖) by ring]
    rw [hscalar, one_mul]
  have morrey_ball_subset : ∀ (x y : ℂ) (r s : ℝ) (hr : 0 < r) (hs0 : 0 < s) (hs1 : s < 1)
    (hxy : ‖x - y‖ ≤ r), Metric.ball (y + (s:ℂ) • (x - y)) (s * r) ⊆ Metric.ball x (2 * r) := by
    intro x y r s hr hs0 hs1 hxy z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz ⊢
    have heq : z - x = (z - (y + (s:ℂ) • (x - y))) + ((1:ℂ) - (s:ℂ)) • (y - x) := by
      simp only [smul_eq_mul]; ring
    rw [heq]
    calc ‖(z - (y + (s:ℂ) • (x - y))) + ((1:ℂ) - (s:ℂ)) • (y - x)‖
        ≤ ‖z - (y + (s:ℂ) • (x - y))‖ + ‖((1:ℂ) - (s:ℂ)) • (y - x)‖ := norm_add_le _ _
      _ < (s * r) + (1 - s) * r := by
          apply add_lt_add_of_lt_of_le hz
          rw [norm_smul]
          have h1s : ‖(1:ℂ) - (s:ℂ)‖ = 1 - s := by
            rw [show (1:ℂ) - (s:ℂ) = ((1 - s : ℝ) : ℂ) by push_cast; ring]
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
          rw [h1s, norm_sub_rev]
          exact mul_le_mul_of_nonneg_left hxy (by linarith)
      _ = r := by ring
      _ < 2 * r := by linarith
  have morrey_inner_bound : ∀ (x y z : ℂ) (r : ℝ) (hr : 0 < r) (hxy : ‖x - y‖ ≤ r)
    (hzy : 0 < ‖z - y‖),
      (∫⁻ s in Ioo (0:ℝ) 1,
        Set.indicator {s : ℝ | z ∈ Metric.ball (y + (s:ℂ) • (x - y)) (s * r)}
        (fun s => ENNReal.ofReal ((s^3)⁻¹)) s)
    ≤ ENNReal.ofReal (2 * r^2 / ‖z - y‖^2) := by
    intro x y z r hr hxy hzy
    set t0 := ‖z - y‖ / (2 * r) with ht0def
    have ht0pos : 0 < t0 := by rw [ht0def]; positivity
    have hstep1 : (∫⁻ s in Ioo (0:ℝ) 1,
        Set.indicator {s : ℝ | z ∈ Metric.ball (y + (s:ℂ) • (x - y)) (s * r)}
          (fun s => ENNReal.ofReal ((s^3)⁻¹)) s)
        ≤ ∫⁻ s in Ioi t0, ENNReal.ofReal ((s^3)⁻¹) := by
      rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioi]
      apply lintegral_mono
      intro s
      by_cases hs1 : s ∈ Ioo (0:ℝ) 1
      · rw [Set.indicator_of_mem hs1]
        by_cases hcond : z ∈ Metric.ball (y + (s:ℂ) • (x - y)) (s * r)
        · rw [Set.indicator_of_mem (Set.mem_ofPred_eq ▸ hcond)]
          have hspos : 0 < s := hs1.1
          have hlt : ‖z - y‖ < 2 * s * r := by
            rw [Metric.mem_ball, Complex.dist_eq] at hcond
            have h1 : z - y = (z - (y + (s:ℂ) • (x - y))) + (s:ℂ) • (x - y) := by ring
            calc ‖z - y‖ = ‖(z - (y + (s:ℂ) • (x - y))) + (s:ℂ) • (x - y)‖ := by rw [← h1]
              _ ≤ ‖z - (y + (s:ℂ) • (x - y))‖ + ‖(s:ℂ) • (x - y)‖ := norm_add_le _ _
              _ < (s * r) + s * r := by
                  apply add_lt_add_of_lt_of_le hcond
                  rw [norm_smul]; simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos]
                  exact mul_le_mul_of_nonneg_left hxy hspos.le
              _ = 2 * s * r := by ring
          have hsmem : s ∈ Ioi t0 := by
            rw [mem_Ioi, ht0def, div_lt_iff₀ (by positivity : (0:ℝ) < 2*r)]; linarith [hlt]
          rw [Set.indicator_of_mem hsmem]
        · rw [Set.indicator_of_notMem (by rw [Set.mem_ofPred_eq]; exact hcond)]; exact zero_le
      · rw [Set.indicator_of_notMem hs1]; exact zero_le
    refine hstep1.trans ?_
    have hint : (∫⁻ s in Ioi t0, ENNReal.ofReal ((s^3)⁻¹)) = ENNReal.ofReal (1 / (2 * t0^2)) := by
      have hcongr : ∀ s ∈ Ioi t0, ENNReal.ofReal ((s^3)⁻¹) = ENNReal.ofReal (s^(-3:ℝ)) := by
        intro s hs
        have hsp : 0 < s := ht0pos.trans hs
        congr 1
        rw [show (-3:ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg, zpow_ofNat]
      rw [setLIntegral_congr_fun measurableSet_Ioi hcongr]
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · rw [integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) ht0pos]
        congr 1
        rw [show (-3:ℝ)+1 = ((-2:ℤ):ℝ) by norm_num, Real.rpow_intCast, zpow_neg, zpow_ofNat]
        field_simp; ring
      · exact integrableOn_Ioi_rpow_of_lt (by norm_num) ht0pos
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hsp : 0 < s := ht0pos.trans hs; positivity
    rw [hint]
    apply le_of_eq
    congr 1
    rw [ht0def, div_pow]
    field_simp
  have morrey_cov : ∀ (g : ℂ → ENNReal) (hg : Measurable g)
    (x : ℂ) (r : ℝ) (hr : 0 < r) (y : ℂ) (hy : y ∈ Metric.closedBall x r),
      (∫⁻ a in Metric.ball x r, ∫⁻ s in Set.Ioo (0:ℝ) 1,
        g (y + (s:ℂ) • (a - y)) * ENNReal.ofReal ‖a - y‖) ≤
      ENNReal.ofReal (2 * r ^ 2) *
        ∫⁻ z in Metric.ball x (2 * r), g z * ENNReal.ofReal ‖z - y‖⁻¹ := by
    intro g hg x r hr y hy
    have hxy : ‖x - y‖ ≤ r := by
      rw [Metric.mem_closedBall, Complex.dist_eq] at hy
      rwa [norm_sub_rev]
    -- Step 1: Tonelli swap (a,s) → (s,a)
    have hmeas1 : Measurable (Function.uncurry (fun (a : ℂ) (s : ℝ) =>
        g (y + (s:ℂ) • (a - y)) * ENNReal.ofReal ‖a - y‖)) :=
      Measurable.mul (hg.comp (by fun_prop)) ((measurable_fst.sub_const y).norm.ennreal_ofReal)
    rw [lintegral_lintegral_swap hmeas1.aemeasurable]
    -- Step 2: rewrite each inner a-integral via slice COV + extend to ball x (2r)
    have hslice : ∀ s ∈ Ioo (0:ℝ) 1,
        (∫⁻ a in Metric.ball x r, g (y + (s:ℂ) • (a - y)) * ENNReal.ofReal ‖a - y‖)
        = ∫⁻ z in Metric.ball x (2 * r),
            Set.indicator (Metric.ball (y + (s:ℂ) • (x - y)) (s * r))
              (fun z => g z * ENNReal.ofReal ‖z - y‖ * ENNReal.ofReal ((s^3)⁻¹)) z := by
      intro s hs
      rw [morrey_slice g x y r hr s hs.1]
      rw [setLIntegral_indicator (measurableSet_ball)]
      rw [Set.inter_eq_left.mpr (morrey_ball_subset x y r s hr hs.1 hs.2 hxy)]
    rw [setLIntegral_congr_fun measurableSet_Ioo hslice]
    -- Step 3: Tonelli swap (s,z) → (z,s)
    have hmeas2 : Measurable (Function.uncurry (fun (z : ℂ) (s : ℝ) =>
        Set.indicator (Metric.ball (y + (s:ℂ) • (x - y)) (s * r))
          (fun z => g z * ENNReal.ofReal ‖z - y‖ * ENNReal.ofReal ((s^3)⁻¹)) z)) := by
      have hset : MeasurableSet
          {p : ℂ × ℝ | p.1 ∈ Metric.ball (y + (p.2:ℂ) • (x - y)) (p.2 * r)} := by
        have heq : {p : ℂ × ℝ | p.1 ∈ Metric.ball (y + (p.2:ℂ) • (x - y)) (p.2 * r)}
            = {p : ℂ × ℝ | dist p.1 (y + (p.2:ℂ) • (x - y)) < p.2 * r} := by
          ext p; simp [Metric.mem_ball]
        rw [heq]; exact measurableSet_lt (by fun_prop) (by fun_prop)
      have hfun : (Function.uncurry (fun (z : ℂ) (s : ℝ) =>
          Set.indicator (Metric.ball (y + (s:ℂ) • (x - y)) (s * r))
            (fun z => g z * ENNReal.ofReal ‖z - y‖ * ENNReal.ofReal ((s^3)⁻¹)) z))
          = {p : ℂ × ℝ | p.1 ∈ Metric.ball (y + (p.2:ℂ) • (x - y)) (p.2 * r)}.indicator
            (fun p => g p.1 * ENNReal.ofReal ‖p.1 - y‖ * ENNReal.ofReal ((p.2^3)⁻¹)) := by
        funext p
        obtain ⟨z, s⟩ := p
        simp only [Function.uncurry]
        by_cases hc : z ∈ Metric.ball (y + (s:ℂ) • (x - y)) (s * r)
        · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (show (z,s) ∈ _ from hc)]
        · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (show (z,s) ∉ _ from hc)]
      rw [hfun]
      exact Measurable.indicator
        (((hg.comp measurable_fst).mul ((measurable_fst.sub_const y).norm.ennreal_ofReal)).mul
          (by fun_prop)) hset
    rw [← lintegral_lintegral_swap (μ := (volume : Measure ℂ).restrict (Metric.ball x (2 * r)))
      (ν := (volume : Measure ℝ).restrict (Ioo (0:ℝ) 1)) hmeas2.aemeasurable]
    -- Step 4+5+6: bound the z-integral pointwise and pull out ofReal(2r²)
    conv_rhs => rw [← lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
    apply setLIntegral_mono_ae' measurableSet_ball
    apply Filter.Eventually.of_forall
    intro z _
    -- inner: ∫⁻ s in Ioo 0 1, 1_{z∈ball(...)}·(g z·ofReal‖z-y‖·ofReal((s³)⁻¹))
    -- pull out g z · ofReal‖z-y‖, converting the z-indicator to the slice-set form
    have hpull : (∫⁻ s in Ioo (0:ℝ) 1, Set.indicator (Metric.ball (y + (s:ℂ) • (x - y)) (s * r))
          (fun z => g z * ENNReal.ofReal ‖z - y‖ * ENNReal.ofReal ((s^3)⁻¹)) z)
        = (g z * ENNReal.ofReal ‖z - y‖) *
          ∫⁻ s in Ioo (0:ℝ) 1, Set.indicator {s : ℝ | z ∈ Metric.ball (y + (s:ℂ) • (x - y)) (s * r)}
            (fun s => ENNReal.ofReal ((s^3)⁻¹)) s := by
      have hmeasf : Measurable (fun s : ℝ =>
          Set.indicator {s : ℝ | z ∈ Metric.ball (y + (s:ℂ) • (x - y)) (s * r)}
          (fun s => ENNReal.ofReal ((s^3)⁻¹)) s) := by
        apply Measurable.indicator (by fun_prop)
        have heq : {s : ℝ | z ∈ Metric.ball (y + (s:ℂ) • (x - y)) (s * r)}
            = {s : ℝ | dist z (y + (s:ℂ) • (x - y)) < s * r} := by ext s; simp [Metric.mem_ball]
        rw [heq]; exact measurableSet_lt (by fun_prop) (by fun_prop)
      rw [← lintegral_const_mul _ hmeasf]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro s _
      simp only []
      by_cases hc : z ∈ Metric.ball (y + (s:ℂ) • (x - y)) (s * r)
      · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (Set.mem_ofPred_eq ▸ hc)]
      · rw [Set.indicator_of_notMem hc,
          Set.indicator_of_notMem (by rw [Set.mem_ofPred_eq]; exact hc),
          mul_zero]
    rw [hpull]
    by_cases hzy : 0 < ‖z - y‖
    · -- nonzero case: use inner bound
      calc (g z * ENNReal.ofReal ‖z - y‖) *
            ∫⁻ s in Ioo (0:ℝ) 1,
              Set.indicator {s : ℝ | z ∈ Metric.ball (y + (s:ℂ) • (x - y)) (s * r)}
              (fun s => ENNReal.ofReal ((s^3)⁻¹)) s
          ≤ (g z * ENNReal.ofReal ‖z - y‖) * ENNReal.ofReal (2 * r^2 / ‖z - y‖^2) := by
            exact mul_le_mul_of_nonneg_left (morrey_inner_bound x y z r hr hxy hzy) (zero_le)
        _ = ENNReal.ofReal (2 * r ^ 2) * (g z * ENNReal.ofReal ‖z - y‖⁻¹) := by
            have hkey : ENNReal.ofReal ‖z - y‖ * ENNReal.ofReal (2 * r^2 / ‖z - y‖^2)
                = ENNReal.ofReal (2 * r ^ 2) * ENNReal.ofReal ‖z - y‖⁻¹ := by
              rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [eq_comm]
              field_simp
            calc g z * ENNReal.ofReal ‖z - y‖ * ENNReal.ofReal (2 * r^2 / ‖z - y‖^2)
                = ENNReal.ofReal ‖z - y‖ * ENNReal.ofReal (2 * r^2 / ‖z - y‖^2) * g z := by ring
              _ = ENNReal.ofReal (2 * r ^ 2) * ENNReal.ofReal ‖z - y‖⁻¹ * g z := by rw [hkey]
              _ = ENNReal.ofReal (2 * r ^ 2) * (g z * ENNReal.ofReal ‖z - y‖⁻¹) := by ring
    · -- ‖z-y‖ = 0 case: LHS = 0
      rw [not_lt] at hzy
      have : ‖z - y‖ = 0 := le_antisymm hzy (norm_nonneg _)
      rw [this]
      simp
  have ptwise_bound : ∀ (u : ℂ → ℂ) (hu : ContDiff ℝ 1 u) (y a : ℂ),
      ‖u y - u a‖ ≤ ∫ s in (0:ℝ)..1, ‖fderiv ℝ u (y + s • (a - y))‖ * ‖a - y‖ := by
    intro u hu y a
    set γ : ℝ → ℂ := fun s => y + s • (a - y) with hγ
    have hγ' : ∀ s : ℝ, HasDerivAt γ (a - y) s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => s • (a - y)) (a - y) s := by
        simpa using (hasDerivAt_id s).smul_const (a - y)
      simpa [hγ] using h1.const_add y
    have hγcont : Continuous γ := continuous_iff_continuousAt.2 (fun s => (hγ' s).continuousAt)
    have hdiff : Differentiable ℝ u := hu.differentiable (by norm_num)
    have hcfd : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
    have key : ∀ s ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (u ∘ γ) ((fderiv ℝ u (γ s)) (a - y)) s :=
      fun s _ => (hdiff (γ s)).hasFDerivAt.comp_hasDerivAt s (hγ' s)
    have hcont : Continuous (fun s : ℝ => (fderiv ℝ u (γ s)) (a - y)) :=
      (hcfd.comp hγcont).clm_apply continuous_const
    have hint : IntervalIntegrable (fun s : ℝ => (fderiv ℝ u (γ s)) (a - y))
        MeasureTheory.volume 0 1 := hcont.intervalIntegrable 0 1
    have heq : u a - u y = ∫ s in (0:ℝ)..1, (fderiv ℝ u (γ s)) (a - y) := by
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt key hint
      simpa [Function.comp, hγ] using this.symm
    have hne : u y - u a = -(u a - u y) := by ring
    rw [hne, norm_neg, heq]
    calc ‖∫ s in (0:ℝ)..1, (fderiv ℝ u (γ s)) (a - y)‖
        ≤ ∫ s in (0:ℝ)..1, ‖(fderiv ℝ u (γ s)) (a - y)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ s in (0:ℝ)..1, ‖fderiv ℝ u (γ s)‖ * ‖a - y‖ := by
          apply intervalIntegral.integral_mono_on (by norm_num)
          · exact (hcont.norm).intervalIntegrable 0 1
          · exact ((hcfd.comp hγcont).norm.mul continuous_const).intervalIntegrable 0 1
          · intro s _; exact (fderiv ℝ u (γ s)).le_opNorm (a - y)
  have inner_bridge : ∀ (u : ℂ → ℂ) (hu : ContDiff ℝ 1 u) (y a : ℂ), ENNReal.ofReal ‖u y - u a‖ ≤
      ∫⁻ s in Set.Ioo (0:ℝ) 1,
        ENNReal.ofReal ‖fderiv ℝ u (y + (s:ℝ) • (a - y))‖ * ENNReal.ofReal ‖a - y‖ := by
    intro u hu y a
    have hpt := ptwise_bound u hu y a
    have hcfd : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
    have hγcont : Continuous (fun s : ℝ => y + s • (a - y)) := by
      have hγ' : ∀ s : ℝ, HasDerivAt (fun s : ℝ => y + s • (a - y)) (a - y) s := by
        intro s
        have h1 : HasDerivAt (fun s : ℝ => s • (a - y)) (a - y) s := by
          simpa using (hasDerivAt_id s).smul_const (a - y)
        simpa using h1.const_add y
      exact continuous_iff_continuousAt.2 (fun s => (hγ' s).continuousAt)
    set F : ℝ → ℝ := fun s => ‖fderiv ℝ u (y + s • (a - y))‖ * ‖a - y‖ with hF
    have hFcont : Continuous F := (hcfd.comp hγcont).norm.mul continuous_const
    have hFnn : ∀ s, 0 ≤ F s := fun s => by positivity
    have e1 : (∫ s in (0:ℝ)..1, F s) = ∫ s in Set.Ioc (0:ℝ) 1, F s :=
      intervalIntegral.integral_of_le (by norm_num)
    have e2 : (∫ s in Set.Ioc (0:ℝ) 1, F s) = ∫ s in Set.Ioo (0:ℝ) 1, F s :=
      integral_Ioc_eq_integral_Ioo
    have hintIoo : IntegrableOn F (Set.Ioo (0:ℝ) 1) volume :=
      (hFcont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have e3 : ENNReal.ofReal (∫ s in Set.Ioo (0:ℝ) 1, F s)
        = ∫⁻ s in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (F s) :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintIoo
        (Filter.Eventually.of_forall (fun s => hFnn s))
    calc ENNReal.ofReal ‖u y - u a‖
        ≤ ENNReal.ofReal (∫ s in (0:ℝ)..1, F s) := ENNReal.ofReal_le_ofReal hpt
      _ = ENNReal.ofReal (∫ s in Set.Ioo (0:ℝ) 1, F s) := by rw [e1, e2]
      _ = ∫⁻ s in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (F s) := e3
      _ = ∫⁻ s in Set.Ioo (0:ℝ) 1,
            ENNReal.ofReal ‖fderiv ℝ u (y + (s:ℝ) • (a - y))‖ * ENNReal.ofReal ‖a - y‖ := by
          apply lintegral_congr; intro s
          rw [hF, ENNReal.ofReal_mul (norm_nonneg _)]
  have single_point_bound : ∀ {p : ℝ} (hp : 2 < p) (pp : ℝ) (hpq : p.HolderConjugate pp)
    (hpp0 : 0 < pp) (hpp2 : pp < 2)
    {u : ℂ → ℂ} (hu : ContDiff ℝ 1 u) (x : ℂ) {r : ℝ} (hr : 0 < r)
    (y : ℂ) (hy : y ∈ Metric.closedBall x r),
      ‖u y - ((volume (Metric.ball x r)).toReal)⁻¹ • ∫ a in Metric.ball x r, u a‖ ≤
      ((volume (Metric.ball x r)).toReal)⁻¹ *
        ((2 * r ^ 2) *
          ((∫ z in Metric.ball x (2*r), ‖fderiv ℝ u z‖ ^ p) ^ (1/p) *
           ((2 * Real.pi / (2 - pp)) * (3*r) ^ (2 - pp)) ^ (1/pp))) := by
    intro p hp pp hpq hpp0 hpp2 u hu x r hr y hy
    set B := Metric.ball x r with hB
    set B2 := Metric.ball x (2*r) with hB2
    set vt := (volume B).toReal with hvt
    set g : ℂ → ENNReal := fun z => ENNReal.ofReal ‖fderiv ℝ u z‖ with hg
    have hgmeas : Measurable g :=
      ENNReal.measurable_ofReal.comp ((hu.continuous_fderiv (by norm_num)).norm.measurable)
    -- measure facts
    have hvB_pos : 0 < volume B := by
      rw [hB, Complex.volume_ball]; apply ENNReal.mul_pos
      · exact pow_ne_zero 2 (by simp [ENNReal.ofReal_eq_zero]; linarith)
      · exact_mod_cast NNReal.pi_pos.ne'
    have hvB_ne_top : volume B ≠ ⊤ := by rw [hB, Complex.volume_ball]; finiteness
    have hvt_pos : 0 < vt := ENNReal.toReal_pos hvB_pos.ne' hvB_ne_top
    -- STEP 1: ‖u y - f̄‖ ≤ vt⁻¹ * ∫_B ‖u y - u a‖
    have hu_int : IntegrableOn u B volume :=
      (hu.continuous.continuousOn.integrableOn_compact (isCompact_closedBall x r)).mono_set
        Metric.ball_subset_closedBall
    have hconst_int : IntegrableOn (fun _ => u y) B volume :=
      integrableOn_const (C := u y) hvB_ne_top (by finiteness)
    have hconst : ∫ _a in B, (u y) ∂volume = vt • u y := by rw [setIntegral_const]; rfl
    have hstep1 : ‖u y - vt⁻¹ • ∫ a in B, u a‖ ≤ vt⁻¹ * ∫ a in B, ‖u y - u a‖ := by
      have hrw : u y - vt⁻¹ • ∫ a in B, u a = vt⁻¹ • ∫ a in B, (u y - u a) := by
        rw [integral_sub hconst_int hu_int, hconst]
        have hv : vt ≠ 0 := hvt_pos.ne'
        match_scalars <;> field_simp
      rw [hrw, show ‖vt⁻¹ • ∫ a in B, (u y - u a)‖ = vt⁻¹ * ‖∫ a in B, (u y - u a)‖ from
        norm_smul_of_nonneg (by positivity) _]
      gcongr
      exact norm_integral_le_integral_norm _
    -- STEP 2: ∫_B ‖u y - u a‖ = (∫⁻_B ofReal ‖u y - u a‖).toReal
    have hAEsm : AEStronglyMeasurable (fun a => ‖u y - u a‖) (volume.restrict B) :=
      (continuous_const.sub (hu.continuous.comp continuous_id)).norm.aestronglyMeasurable
    have hstep2 : ∫ a in B, ‖u y - u a‖
        = (∫⁻ a in B, ENNReal.ofReal ‖u y - u a‖).toReal := by
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun a => norm_nonneg _)) hAEsm]
    -- STEP 3: the ENNReal chain.  ∫⁻_B ofReal‖uy-ua‖ ≤ Lcov ≤ ... ≤ final
    set Gp : ENNReal := ∫⁻ z in B2, g z ^ p with hGp
    set Kp : ENNReal := ∫⁻ z in B2, (ENNReal.ofReal ‖z - y‖⁻¹) ^ pp with hKp
    set Kc : ℝ := (2 * Real.pi / (2 - pp)) * (3*r) ^ (2 - pp) with hKc
    have hKc0 : 0 ≤ Kc := by
      rw [hKc]; apply mul_nonneg
      · apply div_nonneg (by positivity); linarith
      · positivity
    set Final : ENNReal :=
      ENNReal.ofReal (2 * r ^ 2) * (Gp ^ (1/p) * (ENNReal.ofReal Kc) ^ (1/pp)) with hFinal
    -- (a) hLHS_le : ∫⁻_B ofReal‖uy-ua‖ ≤ Lcov
    have hLHS_le : (∫⁻ a in B, ENNReal.ofReal ‖u y - u a‖) ≤
        ∫⁻ a in B, ∫⁻ s in Set.Ioo (0:ℝ) 1,
          g (y + (s:ℝ) • (a - y)) * ENNReal.ofReal ‖a - y‖ := by
      apply lintegral_mono
      intro a
      simpa [hg] using inner_bridge u hu y a
    -- (b) CoV
    have hcov := morrey_cov g hgmeas x r hr y hy
    -- (c) Hölder
    have hG_ae : AEMeasurable (fun z => g z) (volume.restrict B2) := hgmeas.aemeasurable
    have hK_ae : AEMeasurable (fun z => ENNReal.ofReal ‖z - y‖⁻¹) (volume.restrict B2) :=
      (ENNReal.measurable_ofReal.comp ((measurable_id.sub measurable_const).norm.inv)).aemeasurable
    have hholder : (∫⁻ z in B2, g z * ENNReal.ofReal ‖z - y‖⁻¹) ≤ Gp ^ (1/p) * Kp ^ (1/pp) := by
      have := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict B2) hpq hG_ae hK_ae
      simpa [Pi.mul_apply, hGp, hKp] using this
    -- (d) kernel
    have hkernel : Kp ≤ ENNReal.ofReal Kc := kernel_bound pp hpp0 hpp2 x r hr y hy
    -- assemble ENNReal chain
    have hpp_nn : (0:ℝ) ≤ 1/pp := by positivity
    have hchain : (∫⁻ a in B, ENNReal.ofReal ‖u y - u a‖) ≤ Final := by
      calc (∫⁻ a in B, ENNReal.ofReal ‖u y - u a‖)
          ≤ ∫⁻ a in B, ∫⁻ s in Set.Ioo (0:ℝ) 1,
              g (y + (s:ℝ) • (a - y)) * ENNReal.ofReal ‖a - y‖ := hLHS_le
        _ ≤ ENNReal.ofReal (2 * r ^ 2) * (∫⁻ z in B2, g z * ENNReal.ofReal ‖z - y‖⁻¹) := hcov
        _ ≤ ENNReal.ofReal (2 * r ^ 2) * (Gp ^ (1/p) * Kp ^ (1/pp)) := by gcongr
        _ ≤ Final := by rw [hFinal]; gcongr
    -- STEP 4: convert to reals
    have hp0 : 0 < p := by linarith
    have hG_eq : Gp = ENNReal.ofReal (∫ z in B2, ‖fderiv ℝ u z‖ ^ p) := by
      have hpt : ∀ z, (ENNReal.ofReal ‖fderiv ℝ u z‖) ^ p = ENNReal.ofReal (‖fderiv ℝ u z‖ ^ p) :=
        fun z => ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le
      have hintegr : IntegrableOn (fun z => ‖fderiv ℝ u z‖ ^ p) B2 volume := by
        have hc : Continuous (fun z => ‖fderiv ℝ u z‖ ^ p) :=
          (hu.continuous_fderiv (by norm_num)).norm.rpow_const (fun _ => Or.inr hp0.le)
        exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall x (2*r))).mono_set
          Metric.ball_subset_closedBall
      calc Gp = ∫⁻ z in B2, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ p) := by
                rw [hGp]; apply lintegral_congr; intro z; rw [hg]; rw [hpt]
        _ = ENNReal.ofReal (∫ z in B2, ‖fderiv ℝ u z‖ ^ p) := by
            rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintegr
              (Filter.Eventually.of_forall (fun z => by positivity))]
    have hFinal_ne_top : Final ≠ ⊤ := by rw [hFinal, hG_eq]; finiteness
    -- final real bound
    have hkey : (∫⁻ a in B, ENNReal.ofReal ‖u y - u a‖).toReal ≤ Final.toReal :=
      ENNReal.toReal_mono hFinal_ne_top hchain
    have hFinal_toReal : Final.toReal
        = (2 * r ^ 2) *
            ((∫ z in B2, ‖fderiv ℝ u z‖ ^ p) ^ (1/p) * Kc ^ (1/pp)) := by
      rw [hFinal, hG_eq]
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ENNReal.ofReal_rpow_of_nonneg hKc0 (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      rw [ENNReal.toReal_ofReal (by positivity)]
    calc ‖u y - vt⁻¹ • ∫ a in B, u a‖
        ≤ vt⁻¹ * ∫ a in B, ‖u y - u a‖ := hstep1
      _ = vt⁻¹ * (∫⁻ a in B, ENNReal.ofReal ‖u y - u a‖).toReal := by rw [hstep2]
      _ ≤ vt⁻¹ * Final.toReal := by
            have : (0:ℝ) ≤ vt⁻¹ := by positivity
            gcongr
      _ = vt⁻¹ * ((2 * r ^ 2) *
            ((∫ z in B2, ‖fderiv ℝ u z‖ ^ p) ^ (1/p) * Kc ^ (1/pp))) := by rw [hFinal_toReal]
  let C₀ : ℝ → ℝ := fun p =>
    (2 / Real.pi) * 3 ^ (1 - 2 / p) * (2 * Real.pi / (2 - p / (p - 1))) ^ (1 / (p / (p - 1)))
  have single_point_bound' : ∀ {p : ℝ} (hp : 2 < p)
    {u : ℂ → ℂ} (hu : ContDiff ℝ 1 u) (x : ℂ) {r : ℝ} (hr : 0 < r)
    (y : ℂ) (hy : y ∈ Metric.closedBall x r),
      ‖u y - ((volume (Metric.ball x r)).toReal)⁻¹ • ∫ a in Metric.ball x r, u a‖ ≤
      C₀ p * r ^ (1 - 2 / p) *
        (∫ z in Metric.ball x (2 * r), ‖fderiv ℝ u z‖ ^ p) ^ (1 / p) := by
    intro p hp u hu x r hr y hy
    set pp : ℝ := p / (p - 1) with hpp
    have hp_pos : 0 < p := by linarith
    have hsub : 0 < p - 1 := by linarith
    have hpq : p.HolderConjugate pp := by
      rw [hpp, Real.holderConjugate_iff]; refine ⟨by linarith, ?_⟩; field_simp; ring
    have hpp0 : 0 < pp := div_pos hp_pos (by linarith)
    have hpp2 : pp < 2 := by rw [hpp, div_lt_iff₀ (by linarith)]; linarith
    have hG : 0 ≤ ∫ z in Metric.ball x (2 * r), ‖fderiv ℝ u z‖ ^ p := by
      apply MeasureTheory.integral_nonneg; intro z; positivity
    have hvt : (volume (Metric.ball x r)).toReal = Real.pi * r ^ 2 := by
      rw [Complex.volume_ball, ENNReal.toReal_mul,
        show (ENNReal.ofReal r ^ 2 : ENNReal) = ENNReal.ofReal (r ^ 2) by
          rw [ENNReal.ofReal_pow hr.le],
        ENNReal.toReal_ofReal (by positivity)]
      simp [mul_comm]
    have hbd := single_point_bound hp pp hpq hpp0 hpp2 hu x hr y hy
    refine hbd.trans (le_of_eq ?_)
    -- constant extraction
    set G := ∫ z in Metric.ball x (2 * r), ‖fderiv ℝ u z‖ ^ p with hGdef
    rw [hvt]
    have hexp : (2 - pp) * (1 / pp) = 1 - 2 / p := by
      have hinv : p⁻¹ + pp⁻¹ = 1 := hpq.inv_add_inv_eq_one
      have hpp_eq : pp = p / (p - 1) := hpp
      rw [hpp_eq]; field_simp; ring
    have hKpos : 0 ≤ 2 * Real.pi / (2 - pp) := div_nonneg (by positivity) (by linarith)
    simp only [C₀]
    rw [← hpp]
    rw [Real.mul_rpow (by norm_num) hr.le]
    rw [show (2 * Real.pi / (2 - pp)) * (3 ^ (2 - pp) * r ^ (2 - pp))
          = ((2 * Real.pi / (2 - pp)) * 3 ^ (2 - pp)) * r ^ (2 - pp) by ring]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [Real.mul_rpow hKpos (by positivity)]
    rw [← Real.rpow_mul hr.le, hexp]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3), hexp]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hr2 : r ^ 2 ≠ 0 := by positivity
    field_simp
  have morrey_C1_bound : ∀ {p : ℝ} (hp : 2 < p), ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : ℂ → ℂ}, ContDiff ℝ 1 u →
      ∀ (x : ℂ) {r : ℝ}, 0 < r →
      ∀ y ∈ Metric.closedBall x r,
      ‖u y - u x‖ ≤ C * r ^ (1 - 2 / p) *
        (∫ z in Metric.ball x (2 * r), ‖fderiv ℝ u z‖ ^ p) ^ (1 / p) := by
    intro p hp
    refine ⟨2 * C₀ p, ?_, ?_⟩
    · -- 0 ≤ 2 * C₀ p
      have hp_pos : 0 < p := by linarith
      have hsub : 0 < p - 1 := by linarith
      have hKbase : (0:ℝ) ≤ 2 * Real.pi / (2 - p / (p - 1)) := by
        apply div_nonneg (by positivity)
        rw [show (2 : ℝ) - p / (p - 1) = (p - 2) / (p - 1) by field_simp; ring]
        exact div_nonneg (by linarith) (by linarith)
      have hC0 : (0:ℝ) ≤ C₀ p := by
        simp only [C₀]
        apply mul_nonneg (mul_nonneg (by positivity) (by positivity))
        exact Real.rpow_nonneg hKbase _
      linarith
    · intro u hu x r hr y hy
      have hx : x ∈ Metric.closedBall x r := by simp [Metric.mem_closedBall]; linarith
      set fbar : ℂ := ((volume (Metric.ball x r)).toReal)⁻¹ • ∫ a in Metric.ball x r, u a with hfbar
      set R := r ^ (1 - 2 / p) *
          (∫ z in Metric.ball x (2 * r), ‖fderiv ℝ u z‖ ^ p) ^ (1 / p) with hR
      have hby : ‖u y - fbar‖ ≤ C₀ p * R := by
        have := single_point_bound' hp hu x hr y hy
        rw [hR]; rw [← mul_assoc]; exact this
      have hbx : ‖u x - fbar‖ ≤ C₀ p * R := by
        have := single_point_bound' hp hu x hr x hx
        rw [hR]; rw [← mul_assoc]; exact this
      calc ‖u y - u x‖
          = ‖(u y - fbar) - (u x - fbar)‖ := by congr 1; abel
        _ ≤ ‖u y - fbar‖ + ‖u x - fbar‖ := norm_sub_le _ _
        _ ≤ C₀ p * R + C₀ p * R := add_le_add hby hbx
        _ = 2 * C₀ p * r ^ (1 - 2 / p) *
              (∫ z in Metric.ball x (2 * r), ‖fderiv ℝ u z‖ ^ p) ^ (1 / p) := by rw [hR]; ring
  -- obtain the Morrey constant for the outer p
  obtain ⟨Cm, hCm0, hMorrey⟩ := morrey_C1_bound hp
  refine ⟨Cm * 2, by positivity, ?_⟩
  intro x r hr y hy
  -- The RHS gradient-energy integrand h := ‖gx‖^p + ‖gy‖^p, integrable on closedBall x (2r+1).
  set h : ℂ → ℝ := fun z => ‖gx z‖ ^ p + ‖gy z‖ ^ p with hh
  have hhnonneg : ∀ z, 0 ≤ h z := fun z => by positivity
  have hr2 : (0:ℝ) < 2 * r := by linarith
  -- gx', gy' truncations to closedBall x (2r+1)
  set S : Set ℂ := Metric.closedBall x (2 * r + 1) with hS
  have hSmeas : MeasurableSet S := measurableSet_closedBall
  set gx' : ℂ → ℂ := S.indicator gx with hgx'
  set gy' : ℂ → ℂ := S.indicator gy with hgy'
  -- MemLp of gx', gy' over global volume (from MemLpLocOn on the compact ball)
  have hgxS : MemLp gx (ENNReal.ofReal p) (volume.restrict S) :=
    hgx S (Set.subset_univ _) (isCompact_closedBall x (2 * r + 1))
  have hgyS : MemLp gy (ENNReal.ofReal p) (volume.restrict S) :=
    hgy S (Set.subset_univ _) (isCompact_closedBall x (2 * r + 1))
  have hgx'Lp : MemLp gx' (ENNReal.ofReal p) volume :=
    (memLp_indicator_iff_restrict hSmeas).mpr hgxS
  have hgy'Lp : MemLp gy' (ENNReal.ofReal p) volume :=
    (memLp_indicator_iff_restrict hSmeas).mpr hgyS
  have hgx'meas : AEStronglyMeasurable gx' volume := hgx'Lp.aestronglyMeasurable
  have hgy'meas : AEStronglyMeasurable gy' volume := hgy'Lp.aestronglyMeasurable
  have hgx'cs : HasCompactSupport gx' := by
    apply HasCompactSupport.intro (isCompact_closedBall x (2 * r + 1))
    intro z hz; rw [hgx', Set.indicator_of_notMem hz]
  have hgy'cs : HasCompactSupport gy' := by
    apply HasCompactSupport.intro (isCompact_closedBall x (2 * r + 1))
    intro z hz; rw [hgy', Set.indicator_of_notMem hz]
  -- operator-norm bound ‖T‖ ≤ ‖T 1‖ + ‖T I‖ for T : ℂ →L[ℝ] ℂ
  have opnorm_bound : ∀ T : ℂ →L[ℝ] ℂ, ‖T‖ ≤ ‖T 1‖ + ‖T Complex.I‖ := by
    intro T
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    have hw : w = w.re • (1:ℂ) + w.im • Complex.I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one]
      exact (Complex.re_add_im w).symm
    calc ‖T w‖ = ‖T (w.re • (1:ℂ) + w.im • Complex.I)‖ := by rw [← hw]
      _ = ‖w.re • T 1 + w.im • T Complex.I‖ := by rw [map_add, map_smul, map_smul]
      _ ≤ ‖w.re • T 1‖ + ‖w.im • T Complex.I‖ := norm_add_le _ _
      _ = |w.re| * ‖T 1‖ + |w.im| * ‖T Complex.I‖ := by simp [Real.norm_eq_abs]
      _ ≤ ‖w‖ * ‖T 1‖ + ‖w‖ * ‖T Complex.I‖ := by
          gcongr
          · exact Complex.abs_re_le_norm w
          · exact Complex.abs_im_le_norm w
      _ = (‖T 1‖ + ‖T Complex.I‖) * ‖w‖ := by ring
  -- power-mean: (a+b)^p ≤ 2^p (a^p + b^p) for a,b ≥ 0
  have powmean : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) ^ p ≤ 2 ^ p * (a ^ p + b ^ p) := by
    intro a b ha hb
    have hmax : a + b ≤ 2 * max a b := by
      rcases le_total a b with hab | hab
      · simp [max_eq_right hab]; linarith [le_max_right a b, le_max_left a b]
      · simp [max_eq_left hab]; linarith [le_max_right a b, le_max_left a b]
    have habnn : 0 ≤ a + b := by linarith
    calc (a + b) ^ p ≤ (2 * max a b) ^ p := Real.rpow_le_rpow habnn hmax hp0.le
      _ = 2 ^ p * (max a b) ^ p := by rw [Real.mul_rpow (by norm_num) (le_max_of_le_left ha)]
      _ ≤ 2 ^ p * (a ^ p + b ^ p) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rcases le_total a b with hab | hab
          · rw [max_eq_right hab]; have := Real.rpow_nonneg ha p; linarith
          · rw [max_eq_left hab]; have := Real.rpow_nonneg hb p; linarith
  -- weak-derivative hypotheses for the bridge (specialized to gx, gy)
  have hweakx : ∀ ψ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ z, ((fderiv ℝ ψ z) (1:ℂ)) • f z = - ∫ z, ψ z • gx z := by
    intro ψ hψ hψc; exact hgrad.1 ψ (by exact_mod_cast hψ) hψc (Set.subset_univ _)
  have hweaky : ∀ ψ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ z, ((fderiv ℝ ψ z) Complex.I) • f z = - ∫ z, ψ z • gy z := by
    intro ψ hψ hψc; exact hgrad.2 ψ (by exact_mod_cast hψ) hψc (Set.subset_univ _)
  -- The bump sequence with rOut = 1/(n+1)
  have hcast : ∀ n : ℕ, (0:ℝ) ≤ (n:ℝ) := fun n => Nat.cast_nonneg n
  set bn : ℕ → ContDiffBump (0:ℂ) :=
    fun n => ⟨1/(2*((n:ℝ)+1)), 1/((n:ℝ)+1), by positivity, by
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      gcongr; linarith⟩ with hbn
  -- per-n inequality
  have per_n : ∀ n : ℕ,
      ‖(((bn n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] f) y
        - (((bn n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] f) x‖
      ≤ Cm * r ^ (1 - 2 / p) *
        (2 ^ p * ∫ z in Metric.ball x (2 * r + 1/((n:ℝ)+1)), h z) ^ (1 / p) := by
    intro n
    set φn : ℂ → ℝ := (bn n).normed volume with hφn
    set δn : ℝ := 1/((n:ℝ)+1) with hδn
    have hδnpos : 0 < δn := by rw [hδn]; positivity
    have hδnle : δn ≤ 1 := by
      rw [hδn]; rw [div_le_one (by positivity)]; have := hcast n; linarith
    have hφnsmooth : ContDiff ℝ (⊤ : ℕ∞) φn := (bn n).contDiff_normed
    have hφnnonneg : ∀ w, 0 ≤ φn w := (bn n).nonneg_normed
    have hφnint : ∫ w, φn w = 1 := (bn n).integral_normed
    have hφncs : HasCompactSupport φn := (bn n).hasCompactSupport_normed
    have hφnsupp : Function.support φn = Metric.ball (0:ℂ) δn := by
      rw [hφn]; exact (bn n).support_normed_eq
    have hφncont : Continuous φn := hφnsmooth.continuous
    have hφn1 : ContDiff ℝ (1 : ℕ∞) φn := hφnsmooth.of_le (by exact_mod_cast le_top)
    set Fn : ℂ → ℂ := (φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] f) with hFn
    have hFnC1 : ContDiff ℝ 1 Fn := by
      rw [hFn]; exact hφncs.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hφn1 hfloc
    -- bridge: directional derivatives of Fn are convolutions of φn with gx, gy
    have hbridgex : ∀ z, (fderiv ℝ Fn z) (1:ℂ)
        = (φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx) z := by
      intro z; rw [hFn]; exact bridge hf hgxloc hweakx hφnsmooth hφncs z
    have hbridgey : ∀ z, (fderiv ℝ Fn z) Complex.I
        = (φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy) z := by
      intro z; rw [hFn]; exact bridge hf hgyloc hweaky hφnsmooth hφncs z
    -- truncation: on ball x (2r), convolution with gx equals convolution with gx'
    have htruncx : ∀ z ∈ Metric.ball x (2 * r),
        (φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx) z
          = (φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z := by
      intro z hz
      rw [convolution_def, convolution_def]
      apply integral_congr_ae
      filter_upwards with t
      simp only [ContinuousLinearMap.lsmul_apply]
      by_cases ht : t ∈ Function.support φn
      · have htball : t ∈ Metric.ball (0:ℂ) δn := by rw [← hφnsupp]; exact ht
        have htnorm : ‖t‖ < δn := by simpa [Metric.mem_ball, dist_eq_norm] using htball
        have hmemS : z - t ∈ S := by
          rw [hS, Metric.mem_closedBall, dist_eq_norm]
          rw [Metric.mem_ball, dist_eq_norm] at hz
          calc ‖z - t - x‖ = ‖(z - x) - t‖ := by ring_nf
            _ ≤ ‖z - x‖ + ‖t‖ := norm_sub_le _ _
            _ ≤ 2 * r + 1 := by linarith
        rw [hgx', Set.indicator_of_mem hmemS]
      · simp only [Function.mem_support, not_not] at ht
        rw [ht]; simp
    have htruncy : ∀ z ∈ Metric.ball x (2 * r),
        (φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy) z
          = (φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z := by
      intro z hz
      rw [convolution_def, convolution_def]
      apply integral_congr_ae
      filter_upwards with t
      simp only [ContinuousLinearMap.lsmul_apply]
      by_cases ht : t ∈ Function.support φn
      · have htball : t ∈ Metric.ball (0:ℂ) δn := by rw [← hφnsupp]; exact ht
        have htnorm : ‖t‖ < δn := by simpa [Metric.mem_ball, dist_eq_norm] using htball
        have hmemS : z - t ∈ S := by
          rw [hS, Metric.mem_closedBall, dist_eq_norm]
          rw [Metric.mem_ball, dist_eq_norm] at hz
          calc ‖z - t - x‖ = ‖(z - x) - t‖ := by ring_nf
            _ ≤ ‖z - x‖ + ‖t‖ := norm_sub_le _ _
            _ ≤ 2 * r + 1 := by linarith
        rw [hgy', Set.indicator_of_mem hmemS]
      · simp only [Function.mem_support, not_not] at ht
        rw [ht]; simp
    -- Morrey applied to Fn
    have hMor := hMorrey hFnC1 x hr y hy
    -- Convolution functions and their continuity (for integrability)
    have hCgx_cont : Continuous (φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') :=
      hφncs.continuous_convolution_left _ hφncont (hgx'Lp.locallyIntegrable hp_one_le)
    have hCgy_cont : Continuous (φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') :=
      hφncs.continuous_convolution_left _ hφncont (hgy'Lp.locallyIntegrable hp_one_le)
    -- Pointwise gradient bound on ball x (2r)
    have hgradptw : ∀ z ∈ Metric.ball x (2 * r),
        ‖fderiv ℝ Fn z‖ ^ p ≤ 2 ^ p *
          (‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z‖ ^ p
            + ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z‖ ^ p) := by
      intro z hz
      have hb1 := hbridgex z
      have hb2 := hbridgey z
      have htx := htruncx z hz
      have hty := htruncy z hz
      have hle : ‖fderiv ℝ Fn z‖
          ≤ ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z‖
            + ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z‖ := by
        calc ‖fderiv ℝ Fn z‖ ≤ ‖(fderiv ℝ Fn z) 1‖ + ‖(fderiv ℝ Fn z) Complex.I‖ :=
              opnorm_bound _
          _ = ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z‖
              + ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z‖ := by
              rw [hb1, hb2, htx, hty]
      calc ‖fderiv ℝ Fn z‖ ^ p
          ≤ (‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z‖
              + ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z‖) ^ p :=
            Real.rpow_le_rpow (norm_nonneg _) hle hp0.le
        _ ≤ 2 ^ p * (‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z‖ ^ p
              + ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z‖ ^ p) :=
            powmean _ _ (norm_nonneg _) (norm_nonneg _)
    -- integrability on ball x (2r) of the relevant ^p functions
    have hgradInt : IntegrableOn (fun z => ‖fderiv ℝ Fn z‖ ^ p) (Metric.ball x (2 * r)) volume := by
      have hc : Continuous (fun z => ‖fderiv ℝ Fn z‖ ^ p) :=
        (hFnC1.continuous_fderiv (by norm_num)).norm.rpow_const (fun _ => Or.inr hp0.le)
      exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall x (2 * r))).mono_set
        Metric.ball_subset_closedBall
    have hCgxInt : IntegrableOn
        (fun z => ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z‖ ^ p)
        (Metric.ball x (2 * r)) volume := by
      have hc : Continuous
          (fun z => ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z‖ ^ p) :=
        hCgx_cont.norm.rpow_const (fun _ => Or.inr hp0.le)
      exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall x (2 * r))).mono_set
        Metric.ball_subset_closedBall
    have hCgyInt : IntegrableOn
        (fun z => ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z‖ ^ p)
        (Metric.ball x (2 * r)) volume := by
      have hc : Continuous
          (fun z => ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z‖ ^ p) :=
        hCgy_cont.norm.rpow_const (fun _ => Or.inr hp0.le)
      exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall x (2 * r))).mono_set
        Metric.ball_subset_closedBall
    -- integrate the pointwise gradient bound
    have hgradIntBound : ∫ z in Metric.ball x (2 * r), ‖fderiv ℝ Fn z‖ ^ p
        ≤ 2 ^ p * ((∫ z in Metric.ball x (2 * r),
            ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z‖ ^ p)
          + ∫ z in Metric.ball x (2 * r),
            ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z‖ ^ p) := by
      have hsum_int : IntegrableOn (fun z => 2 ^ p *
          (‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z‖ ^ p
            + ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z‖ ^ p))
          (Metric.ball x (2 * r)) volume :=
        (hCgxInt.add hCgyInt).const_mul (2 ^ p)
      calc ∫ z in Metric.ball x (2 * r), ‖fderiv ℝ Fn z‖ ^ p
          ≤ ∫ z in Metric.ball x (2 * r), 2 ^ p *
              (‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z‖ ^ p
                + ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z‖ ^ p) :=
            setIntegral_mono_on hgradInt hsum_int measurableSet_ball hgradptw
        _ = 2 ^ p * ((∫ z in Metric.ball x (2 * r),
              ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z‖ ^ p)
            + ∫ z in Metric.ball x (2 * r),
              ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z‖ ^ p) := by
            rw [integral_const_mul, integral_add hCgxInt hCgyInt]
    -- molli_bound applied to gx', gy' at ρ = 2r, δ = δn
    have hφnsupp' : Function.support φn ⊆ Metric.ball (0:ℂ) δn := by rw [hφnsupp]
    have hmollix := molli_bound (p := p) hp1.le hφnnonneg hφnint hφncont hφncs hδnpos hφnsupp'
      hgx'meas hgx'cs hgx'Lp x hr2
    have hmolliy := molli_bound (p := p) hp1.le hφnnonneg hφnint hφncont hφncs hδnpos hφnsupp'
      hgy'meas hgy'cs hgy'Lp x hr2
    -- on ball x (2r+δn) ⊆ S, gx' = gx and gy' = gy, so ‖gx'‖^p + ‖gy'‖^p = h
    have hballsubS : Metric.ball x (2 * r + δn) ⊆ S := by
      rw [hS]; intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rw [Metric.mem_closedBall, dist_eq_norm]; linarith
    have hgx'eq : ∀ z ∈ Metric.ball x (2 * r + δn), ‖gx' z‖ ^ p = ‖gx z‖ ^ p := by
      intro z hz; rw [hgx', Set.indicator_of_mem (hballsubS hz)]
    have hgy'eq : ∀ z ∈ Metric.ball x (2 * r + δn), ‖gy' z‖ ^ p = ‖gy z‖ ^ p := by
      intro z hz; rw [hgy', Set.indicator_of_mem (hballsubS hz)]
    -- integrability of ‖gx'‖^p, ‖gy'‖^p, h on the ball
    have hGxInt : IntegrableOn (fun z => ‖gx z‖ ^ p) (Metric.ball x (2 * r + δn)) volume := by
      have : MemLp gx (ENNReal.ofReal p) (volume.restrict S) := hgxS
      have hb : IntegrableOn (fun z => ‖gx z‖ ^ p) S volume := by
        have hi := hgxS.integrable_norm_rpow (by simp [ENNReal.ofReal_eq_zero]; linarith)
          ENNReal.ofReal_ne_top
        rw [ENNReal.toReal_ofReal hp0.le] at hi
        exact hi
      exact hb.mono_set hballsubS
    have hGyInt : IntegrableOn (fun z => ‖gy z‖ ^ p) (Metric.ball x (2 * r + δn)) volume := by
      have hb : IntegrableOn (fun z => ‖gy z‖ ^ p) S volume := by
        have hi := hgyS.integrable_norm_rpow (by simp [ENNReal.ofReal_eq_zero]; linarith)
          ENNReal.ofReal_ne_top
        rw [ENNReal.toReal_ofReal hp0.le] at hi
        exact hi
      exact hb.mono_set hballsubS
    have hgx'IntBall : IntegrableOn (fun z => ‖gx' z‖ ^ p) (Metric.ball x (2 * r + δn)) volume :=
      hGxInt.congr_fun (fun z hz => (hgx'eq z hz).symm) measurableSet_ball
    have hgy'IntBall : IntegrableOn (fun z => ‖gy' z‖ ^ p) (Metric.ball x (2 * r + δn)) volume :=
      hGyInt.congr_fun (fun z hz => (hgy'eq z hz).symm) measurableSet_ball
    -- combine molli bounds into a bound by ∫ h
    have hcombine :
        (∫ z in Metric.ball x (2 * r),
            ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z‖ ^ p)
          + ∫ z in Metric.ball x (2 * r),
            ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z‖ ^ p
          ≤ ∫ z in Metric.ball x (2 * r + δn), h z := by
      have hadd : (∫ z in Metric.ball x (2 * r + δn), ‖gx' z‖ ^ p)
          + ∫ z in Metric.ball x (2 * r + δn), ‖gy' z‖ ^ p
          = ∫ z in Metric.ball x (2 * r + δn), h z := by
        rw [← integral_add hgx'IntBall hgy'IntBall]
        apply setIntegral_congr_fun measurableSet_ball
        intro z hz
        simp only [hh, hgx'eq z hz, hgy'eq z hz]
      calc (∫ z in Metric.ball x (2 * r),
              ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z‖ ^ p)
            + ∫ z in Metric.ball x (2 * r),
              ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z‖ ^ p
          ≤ (∫ z in Metric.ball x (2 * r + δn), ‖gx' z‖ ^ p)
              + ∫ z in Metric.ball x (2 * r + δn), ‖gy' z‖ ^ p := add_le_add hmollix hmolliy
        _ = ∫ z in Metric.ball x (2 * r + δn), h z := hadd
    -- assemble per_n
    set Cgx_int := ∫ z in Metric.ball x (2 * r),
      ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gx') z‖ ^ p with hCgx_int
    set Cgy_int := ∫ z in Metric.ball x (2 * r),
      ‖(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] gy') z‖ ^ p with hCgy_int
    set gradFn_int := ∫ z in Metric.ball x (2 * r), ‖fderiv ℝ Fn z‖ ^ p with hgradFn_int
    have hgradFn_nonneg : 0 ≤ gradFn_int := by
      rw [hgradFn_int]; apply integral_nonneg; intro z; positivity
    have hh_int_nonneg : 0 ≤ ∫ z in Metric.ball x (2 * r + δn), h z := by
      apply integral_nonneg; intro z; exact hhnonneg z
    have hcoef_nonneg : 0 ≤ Cm * r ^ (1 - 2 / p) := by positivity
    have hstep_a : gradFn_int ≤ 2 ^ p * ∫ z in Metric.ball x (2 * r + δn), h z := by
      calc gradFn_int ≤ 2 ^ p * (Cgx_int + Cgy_int) := hgradIntBound
        _ ≤ 2 ^ p * ∫ z in Metric.ball x (2 * r + δn), h z := by
            apply mul_le_mul_of_nonneg_left hcombine (by positivity)
    have hrpow_mono :
        gradFn_int ^ (1/p) ≤ (2 ^ p * ∫ z in Metric.ball x (2 * r + δn), h z) ^ (1/p) :=
      Real.rpow_le_rpow hgradFn_nonneg hstep_a (by positivity)
    calc ‖Fn y - Fn x‖ ≤ Cm * r ^ (1 - 2 / p) * gradFn_int ^ (1/p) := hMor
      _ ≤ Cm * r ^ (1 - 2 / p) *
          (2 ^ p * ∫ z in Metric.ball x (2 * r + δn), h z) ^ (1/p) := by
          apply mul_le_mul_of_nonneg_left hrpow_mono hcoef_nonneg
  -- Take the limit n → ∞.
  set δseq : ℕ → ℝ := fun n => 1/((n:ℝ)+1) with hδseq
  -- (1) Fn y → f y, Fn x → f x
  have hrout : Filter.Tendsto (fun n => (bn n).rOut) Filter.atTop (nhds 0) := by
    simp only [hbn]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hlimy : Filter.Tendsto
      (fun n => (((bn n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] f) y)
      Filter.atTop (nhds (f y)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous hrout hf y
  have hlimx : Filter.Tendsto
      (fun n => (((bn n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] f) x)
      Filter.atTop (nhds (f x)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous hrout hf x
  have hlimLHS : Filter.Tendsto
      (fun n => ‖(((bn n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] f) y
        - (((bn n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure ℂ)] f) x‖)
      Filter.atTop (nhds (‖f y - f x‖)) :=
    (hlimy.sub hlimx).norm
  -- (2) the integral limit ∫_{ball x (2r+δseq n)} h → ∫_{ball x 2r} h
  have hSseq_meas : ∀ n : ℕ, MeasurableSet (Metric.ball x (2 * r + δseq n)) :=
    fun n => measurableSet_ball
  have hSseq_anti : Antitone (fun n => Metric.ball x (2 * r + δseq n)) := by
    intro m n hmn
    apply Metric.ball_subset_ball
    have hmn' : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
    have hmn1 : (m:ℝ) + 1 ≤ (n:ℝ) + 1 := by linarith
    rw [hδseq]
    have : (1:ℝ)/((n:ℝ)+1) ≤ 1/((m:ℝ)+1) := by
      apply one_div_le_one_div_of_le (by positivity) hmn1
    simp only; linarith
  have hInter : (⋂ n, Metric.ball x (2 * r + δseq n)) = Metric.closedBall x (2 * r) := by
    apply subset_antisymm
    · intro z hz
      simp only [Set.mem_iInter, Metric.mem_ball] at hz
      rw [Metric.mem_closedBall]
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hcon)
      have h2 := hz n
      rw [hδseq] at h2; simp only at h2
      linarith
    · intro z hz
      simp only [Set.mem_iInter, Metric.mem_ball]
      rw [Metric.mem_closedBall] at hz
      intro n
      have hpos : (0:ℝ) < δseq n := by rw [hδseq]; positivity
      linarith
  have hh_int_S : IntegrableOn h (Metric.ball x (2 * r + δseq 0)) volume := by
    have hb : IntegrableOn h S volume := by
      have hgxb : IntegrableOn (fun z => ‖gx z‖ ^ p) S volume := by
        have hi := hgxS.integrable_norm_rpow (by simp [ENNReal.ofReal_eq_zero]; linarith)
          ENNReal.ofReal_ne_top
        rw [ENNReal.toReal_ofReal hp0.le] at hi
        exact hi
      have hgyb : IntegrableOn (fun z => ‖gy z‖ ^ p) S volume := by
        have hi := hgyS.integrable_norm_rpow (by simp [ENNReal.ofReal_eq_zero]; linarith)
          ENNReal.ofReal_ne_top
        rw [ENNReal.toReal_ofReal hp0.le] at hi
        exact hi
      exact hgxb.add hgyb
    apply hb.mono_set
    rw [hS]; intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : δseq 0 = 1 := by rw [hδseq]; norm_num
    rw [this] at hz; linarith
  have hsphere : volume (Metric.sphere x (2 * r)) = 0 := Measure.addHaar_sphere volume x (2 * r)
  have hclosed_eq :
      ∫ z in Metric.closedBall x (2 * r), h z = ∫ z in Metric.ball x (2 * r), h z := by
    apply setIntegral_congr_set
    rw [Filter.eventuallyEq_set]
    have hsub : Metric.ball x (2 * r) ⊆ Metric.closedBall x (2 * r) := Metric.ball_subset_closedBall
    have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ Metric.sphere x (2 * r) := by
      have hcompl := hsphere
      rw [← compl_mem_ae_iff] at hcompl
      filter_upwards [hcompl] with z hz; exact hz
    filter_upwards [hae] with z hz
    constructor
    · intro hzc
      rw [Metric.mem_closedBall] at hzc
      rw [Metric.mem_ball]
      rcases lt_or_eq_of_le hzc with hlt | heq
      · exact hlt
      · exact absurd (Metric.mem_sphere.mpr heq) hz
    · intro hzb; exact hsub hzb
  have hlimInt : Filter.Tendsto (fun n => ∫ z in Metric.ball x (2 * r + δseq n), h z)
      Filter.atTop (nhds (∫ z in Metric.ball x (2 * r), h z)) := by
    have := tendsto_setIntegral_of_antitone hSseq_meas hSseq_anti ⟨0, hh_int_S⟩
    rw [hInter, hclosed_eq] at this
    exact this
  -- (3) RHS limit
  set E : ℝ := ∫ z in Metric.ball x (2 * r), h z with hE
  have hE_nonneg : 0 ≤ E := by rw [hE]; apply integral_nonneg; intro z; exact hhnonneg z
  -- continuity of z ↦ Cm * r^(1-2/p) * (2^p * z)^(1/p) at points ≥ 0 (use rpow continuity)
  have hcont_rhs : Continuous (fun z : ℝ => Cm * r ^ (1 - 2 / p) * (2 ^ p * z) ^ (1 / p)) := by
    apply Continuous.mul continuous_const
    apply Continuous.rpow_const
    · fun_prop
    · intro z; right; positivity
  have hlimRHS : Filter.Tendsto
      (fun n => Cm * r ^ (1 - 2 / p) *
        (2 ^ p * ∫ z in Metric.ball x (2 * r + δseq n), h z) ^ (1 / p))
      Filter.atTop (nhds (Cm * r ^ (1 - 2 / p) * (2 ^ p * E) ^ (1 / p))) := by
    have hcomp : Filter.Tendsto
        (fun n => (fun z : ℝ => Cm * r ^ (1 - 2 / p) * (2 ^ p * z) ^ (1 / p))
          (∫ z in Metric.ball x (2 * r + δseq n), h z))
        Filter.atTop (nhds ((fun z : ℝ => Cm * r ^ (1 - 2 / p) * (2 ^ p * z) ^ (1 / p)) E)) :=
      (hcont_rhs.continuousAt.tendsto).comp (by rw [hE] at hlimInt ⊢; exact hlimInt)
    exact hcomp
  -- the limit inequality
  have hfinal_le : ‖f y - f x‖ ≤ Cm * r ^ (1 - 2 / p) * (2 ^ p * E) ^ (1 / p) := by
    apply le_of_tendsto_of_tendsto' hlimLHS hlimRHS
    intro n
    have hpn := per_n n
    rw [hδseq]
    exact hpn
  -- (2^p * E)^(1/p) = 2 * E^(1/p)
  have hpow : (2 ^ p * E) ^ (1 / p) = 2 * E ^ (1 / p) := by
    rw [Real.mul_rpow (by positivity) hE_nonneg]
    congr 1
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [mul_one_div, div_self hp0.ne']
    exact Real.rpow_one 2
  -- conclude with C = Cm * 2
  have hbound : ‖f y - f x‖ ≤ Cm * 2 * r ^ (1 - 2 / p) * E ^ (1 / p) := by
    rw [hpow] at hfinal_le
    calc ‖f y - f x‖ ≤ Cm * r ^ (1 - 2 / p) * (2 * E ^ (1 / p)) := hfinal_le
      _ = Cm * 2 * r ^ (1 - 2 / p) * E ^ (1 / p) := by ring
  rw [hE] at hbound
  convert hbound using 2

end NoWanderingDomains
