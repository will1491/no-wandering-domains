/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Defs.Analytic
import NoWanderingDomains.QC.LengthArea.Mollification
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Quasiconformal calculus: Weyl's lemma

A `1`-quasiconformal map is conformal. In the analytic formulation: an `IsQCAnalytic` map whose
Beltrami coefficient vanishes (`b.μ = 0`) is holomorphic. The Beltrami equation `∂̄f = b.μ · ∂f`
then reads `∂̄f = 0` almost everywhere, and a `W^{1,2}_loc` solution of `∂̄f = 0` is holomorphic —
this is **Weyl's lemma** (hypoellipticity of the Cauchy–Riemann operator `∂̄`).
-/

open MeasureTheory

namespace NoWanderingDomains

/-- **Weyl's lemma (`1`-quasiconformal ⇒ conformal).** An analytic-quasiconformal map with
vanishing Beltrami coefficient is holomorphic. With `b.μ = 0` the Beltrami equation gives
`∂̄f = 0` almost everywhere; the `W^{1,2}_loc` regularity of `f` then upgrades this weak equation
to genuine holomorphy. The argument mollifies `f`: each mollification is `C^∞` with `∂̄ = 0`
(the weak derivative `∂̄f = 0` convolves to a pointwise zero), hence holomorphic, and the
mollifications converge to `f` locally uniformly, so the limit `f` is holomorphic. -/
theorem weyl_lemma {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b) (hμ : b.μ = 0) :
    Differentiable ℂ f := by
  classical
  -- ===== Basic data from `IsQCAnalytic f b`. =====
  have hfcont : Continuous f := hf.1.1.continuous
  have hfloc : MeasureTheory.LocallyIntegrable f := hfcont.locallyIntegrable
  have hdiff : ∀ᵐ z, DifferentiableAt ℝ f z := IsQCAnalytic.ae_differentiableAt hf
  -- The weak gradient `(gx, gy)` of `f` from `MemW12loc f`, both `L²_loc`.
  obtain ⟨_hLp, gx, gy, ⟨hwgx, hwgy⟩, hmgx, hmgy⟩ := hf.2.1
  have hLpgx : MemLpLocOn gx 2 Set.univ := hmgx
  have hLpgy : MemLpLocOn gy 2 Set.univ := hmgy
  -- `L²_loc ⟹ L¹_loc ⟹ LocallyIntegrable`.
  have memLpLoc_to_loc : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
      MeasureTheory.LocallyIntegrable g := by
    intro g hg
    rw [← locallyIntegrableOn_univ, locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro k hk
    have : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict k) :=
      ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    have hmem1 : MeasureTheory.MemLp g 1 (MeasureTheory.volume.restrict k) :=
      (hg k (Set.subset_univ _) hk).mono_exponent (by norm_num)
    exact MeasureTheory.memLp_one_iff_integrable.mp hmem1
  have hgxLI : MeasureTheory.LocallyIntegrable gx := memLpLoc_to_loc hLpgx
  have hgyLI : MeasureTheory.LocallyIntegrable gy := memLpLoc_to_loc hLpgy
  have hgxloc : MeasureTheory.LocallyIntegrableOn gx Set.univ :=
    locallyIntegrableOn_univ.mpr hgxLI
  have hgyloc : MeasureTheory.LocallyIntegrableOn gy Set.univ :=
    locallyIntegrableOn_univ.mpr hgyLI
  -- ===== The Beltrami equation with `b.μ = 0`: `∂̄f = 0` a.e. =====
  have hbel : ∀ᵐ z, dzbar f z = 0 := by
    filter_upwards [hf.2.2] with z hz
    rw [hz, hμ]; simp
  -- a.e.: `(fderiv f z) 1 = gx z`, `(fderiv f z) I = gy z`.
  have haex : ∀ᵐ z, (fderiv ℝ f z) (1 : ℂ) = gx z :=
    fderiv_ae_eq_weakDirDeriv hwgx hgxloc hdiff (Or.inl rfl) hfloc
  have haey : ∀ᵐ z, (fderiv ℝ f z) Complex.I = gy z :=
    fderiv_ae_eq_weakDirDeriv hwgy hgyloc hdiff (Or.inr rfl) hfloc
  -- a.e.: `gx z + I • gy z = 0` (the weak `∂̄f = 0` rewritten through the partials).
  have hcomb : ∀ᵐ z, gx z + Complex.I * gy z = 0 := by
    filter_upwards [hbel, haex, haey] with z hz hx hy
    have : dzbar f z = (1 / 2 : ℂ) * (gx z + Complex.I * gy z) := by
      rw [dzbar, hx, hy]
    rw [this] at hz
    have h2 : (1 / 2 : ℂ) ≠ 0 := by norm_num
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h h2
    · exact h
  -- ===== Mollifier sequence `φ n` with `rOut → 0`. =====
  set φ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    { rIn := 1 / (n + 2), rOut := 2 / (n + 2),
      rIn_pos := by positivity,
      rIn_lt_rOut := by
        rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num } with hφdef
  have hφrout : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [hφdef] using this
  -- The normed bumps and the mollifications.
  set ρ : ℕ → ℂ → ℝ := fun n => (φ n).normed MeasureTheory.volume with hρ
  set fn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) f
    (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume with hfn
  have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
    (φ n).contDiff_normed (n := ⊤)
  have hρsupp : ∀ n, HasCompactSupport (ρ n) := fun n => (φ n).hasCompactSupport_normed
  have hρcont : ∀ n, Continuous (ρ n) := fun n => (hρsm n).continuous
  -- ===== Each `fn n` is holomorphic on `univ`. =====
  -- Directional derivatives of `fn n` are the mollifications of the weak partials.
  have hA1x : ∀ n z, (fderiv ℝ (fn n) z) (1 : ℂ)
      = MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ)
          MeasureTheory.volume z := fun n z =>
    fderiv_convolution_normed_apply_eq hwgx hfloc hgxLI (hρsm n) (hρsupp n) z
  have hA1y : ∀ n z, (fderiv ℝ (fn n) z) Complex.I
      = MeasureTheory.convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ)
          MeasureTheory.volume z := fun n z =>
    fderiv_convolution_normed_apply_eq hwgy hfloc hgyLI (hρsm n) (hρsupp n) z
  -- The two convolutions exist everywhere (`ρ n` smooth, compact support; `gx`, `gy` loc. int.).
  have hexx : ∀ n, MeasureTheory.ConvolutionExists (ρ n) gx
      (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := fun n =>
    (hρsupp n).convolutionExists_left _ (hρcont n) hgxLI
  have hexy : ∀ n, MeasureTheory.ConvolutionExists (ρ n) gy
      (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := fun n =>
    (hρsupp n).convolutionExists_left _ (hρcont n) hgyLI
  -- `∂̄ (fn n) = 0` everywhere, hence each `fn n` is holomorphic.
  have hfn_holo : ∀ n, DifferentiableOn ℂ (fn n) Set.univ := by
    intro n
    -- `fn n` is `C^∞` (mollification by a smooth compactly supported bump).
    have hfn_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fn n) :=
      (hρsupp n).contDiff_convolution_left _ (hρsm n) hfloc
    have hfn_diffR : ∀ z, DifferentiableAt ℝ (fn n) z := fun z =>
      (hfn_smooth.differentiable (by simp)).differentiableAt
    -- `∂̄ (fn n) z = ½ ((ρ_n ⋆ gx) z + I·(ρ_n ⋆ gy) z) = 0`.
    have hdzbar0 : ∀ z, dzbar (fn n) z = 0 := by
      intro z
      have hval : dzbar (fn n) z
          = (1 / 2 : ℂ) *
            (MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ)
                MeasureTheory.volume z
              + Complex.I * MeasureTheory.convolution (ρ n) gy
                (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume z) := by
        rw [dzbar, hA1x n z, hA1y n z]
      -- The combination of mollified partials is the mollification of the combination = `0`.
      have hzero : MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ)
            MeasureTheory.volume z
          + Complex.I * MeasureTheory.convolution (ρ n) gy
            (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume z = 0 := by
        -- Abbreviations for the two convolution integrands.
        set Fx : ℂ → ℂ := fun t => (ContinuousLinearMap.lsmul ℝ ℝ (ρ n t)) (gx (z - t)) with hFx
        set Fy : ℂ → ℂ := fun t => (ContinuousLinearMap.lsmul ℝ ℝ (ρ n t)) (gy (z - t)) with hFy
        have hcx : MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ)
            MeasureTheory.volume z = ∫ t, Fx t := rfl
        have hcy : MeasureTheory.convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ)
            MeasureTheory.volume z = ∫ t, Fy t := rfl
        rw [hcx, hcy]
        -- Pull the constant `I` into the second integral.
        have hIint : Complex.I * ∫ t, Fy t = ∫ t, Complex.I * Fy t :=
          (MeasureTheory.integral_const_mul Complex.I Fy).symm
        rw [hIint]
        -- Add the integrals (both integrands integrable).
        have hix : MeasureTheory.Integrable Fx MeasureTheory.volume := (hexx n z)
        have hiy : MeasureTheory.Integrable (fun t => Complex.I * Fy t) MeasureTheory.volume :=
          (hexy n z).const_mul Complex.I
        rw [← MeasureTheory.integral_add hix hiy]
        -- The integrand is a.e. zero: `gx (z-t) + I·gy (z-t) = 0` for a.e. `t`.
        refine MeasureTheory.integral_eq_zero_of_ae ?_
        -- Translate the a.e.-zero combination `hcomb` by `t ↦ z - t`.
        have hshift : ∀ᵐ t, gx (z - t) + Complex.I * gy (z - t) = 0 := by
          have hmp : MeasureTheory.MeasurePreserving (fun t : ℂ => z - t)
              (MeasureTheory.volume : MeasureTheory.Measure ℂ) MeasureTheory.volume :=
            (MeasureTheory.volume : MeasureTheory.Measure ℂ).measurePreserving_sub_left z
          exact hmp.quasiMeasurePreserving.ae hcomb
        filter_upwards [hshift] with t ht
        simp only [hFx, hFy, ContinuousLinearMap.lsmul_apply, Pi.zero_apply]
        -- `ρ_n t • gx(z-t) + I·(ρ_n t • gy(z-t)) = ρ_n t • (gx(z-t) + I·gy(z-t)) = ρ_n t • 0 = 0`.
        rw [mul_smul_comm, ← smul_add, ht, smul_zero]
      rw [hval, hzero, mul_zero]
    -- Holomorphic characterization on the open set `univ`.
    refine (differentiableOn_iff_dzbar_eq_zero isOpen_univ ?_).mpr (fun z _ => hdzbar0 z)
    exact fun z _ => (hfn_diffR z).differentiableWithinAt
  -- ===== `fn n → f` locally uniformly on `univ`. =====
  have hTLU : TendstoLocallyUniformlyOn fn f Filter.atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_univ]
    refine tendstoLocallyUniformly_of_forall_exists_nhds (fun x => ?_)
    -- A compact neighborhood `closedBall x 1`, with uniform-continuity modulus on `closedBall x 2`.
    refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
    -- `f` is uniformly continuous on the compact `closedBall x 2`.
    have hUC : UniformContinuousOn f (Metric.closedBall x 2) :=
      (isCompact_closedBall x 2).uniformContinuousOn_of_continuous hfcont.continuousOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by positivity
    obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) hε2
    -- For `rOut < min δ 1`, the convolution estimate `dist_convolution_le` applies.
    have hev : ∀ᶠ n in Filter.atTop, (φ n).rOut < min δ 1 := by
      have := hφrout.eventually (eventually_lt_nhds (show (0 : ℝ) < min δ 1 by positivity))
      filter_upwards [this] with n hn using hn
    filter_upwards [hev] with n hn z hz
    -- `(φ n).rOut ≤ 1` and `(φ n).rOut ≤ δ`.
    have hrout_le_one : (φ n).rOut ≤ 1 := (lt_of_lt_of_le hn (min_le_right δ 1)).le
    have hrout_le_δ : (φ n).rOut ≤ δ := (lt_of_lt_of_le hn (min_le_left δ 1)).le
    -- Apply `dist_convolution_le` with `R = (φ n).rOut`, `z₀ = f z`.
    have hsupp : Function.support (ρ n) ⊆ Metric.ball (0 : ℂ) (φ n).rOut := by
      rw [hρ, (φ n).support_normed_eq]
    have hnf : ∀ y, 0 ≤ ρ n y := fun y => (φ n).nonneg_normed y
    have hintf : ∫ y, ρ n y ∂MeasureTheory.volume = 1 := (φ n).integral_normed
    have hclose : ∀ y ∈ Metric.ball z (φ n).rOut, dist (f y) (f z) ≤ ε / 2 := by
      intro y hy
      -- `z ∈ closedBall x 1`, `y ∈ ball z rOut ⊆ ball z 1`, so both in `closedBall x 2`.
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
    -- `dist (f z) ((ρ n ⋆ f) z) ≤ ε/2 < ε`.
    calc dist (f z) (fn n z)
        = dist (fn n z) (f z) := dist_comm _ _
      _ ≤ ε / 2 := dist_convolution_le hε2.le hsupp hnf hintf
            hfcont.aestronglyMeasurable hclose
      _ < ε := by linarith
  -- ===== Conclusion: locally uniform limit of holomorphic functions is holomorphic. =====
  have hdiffOn : DifferentiableOn ℂ f Set.univ :=
    hTLU.differentiableOn (Filter.Eventually.of_forall hfn_holo) isOpen_univ
  rw [← differentiableOn_univ]
  exact hdiffOn

end NoWanderingDomains
