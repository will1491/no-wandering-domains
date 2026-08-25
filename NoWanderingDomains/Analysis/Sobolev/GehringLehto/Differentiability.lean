/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Sobolev.GehringLehto.CourantLebesgue

/-!
# Gehring–Lehto: smooth approximation, the small-energy circle, and a.e. differentiability

Continues `GehringLehto.CourantLebesgue`. The local `W^{1,2}` mollification with `L²`-gradient
convergence (`exists_smooth_approx_L2grad_local`), the boundary-circle oscillation estimates
(`continuousOn_diam_image_sphere`, `courantLebesgue_smallEnergyCircle`), and the assembly into
the finite metric upper derivative a.e. (`ae_finiteMetricDerivative_of_W12loc_homeomorph`) and
hence, via the Stepanov engine, the main theorem `ae_differentiableAt_of_W12loc_homeomorph`.
-/

open Metric Set MeasureTheory Filter
open scoped Topology ENNReal NNReal Pointwise

namespace NoWanderingDomains.GehringLehto

/-- **Local W^{1,2} mollification with L²-gradient convergence (CL-C1).**

A continuous `f` with weak gradient `(gx, gy) ∈ L²_loc` admits, for every disc `closedBall x R` and
tolerance `ε > 0`, a `C¹` map `g` that is uniformly `ε`-close to `f` on the disc and whose classical
gradient is `L²`-close to `(gx, gy)` there (the energy of the gradient difference is `≤ ε`).

This is the mollification step `g = η_δ ⋆ (χ·f)` with a cutoff `χ`: the weak derivative commutes
with the convolution (`fderiv (η_δ ⋆ u) v = η_δ ⋆ (∂_v u)`), and `η_δ ⋆ h → h` in `L²` for `h ∈ L²`;
the cutoff localizes the only-`L²_loc` data to a genuine `L²` function. -/
theorem exists_smooth_approx_L2grad_local {f gx gy : ℂ → ℂ}
    (hfcont : Continuous f) (hwg : HasWeakGradient gx gy f Set.univ)
    (hgx : MemLpLocOn gx 2 Set.univ) (hgy : MemLpLocOn gy 2 Set.univ)
    (x : ℂ) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, ContDiff ℝ 1 g ∧
      (∀ z ∈ Metric.closedBall x R, ‖g z - f z‖ ≤ ε) ∧
      (∫⁻ z in Metric.closedBall x R,
          energyDensity (fun w => (fderiv ℝ g w) 1 - gx w)
            (fun w => (fderiv ℝ g w) Complex.I - gy w) z) ≤ ENNReal.ofReal ε := by
  classical
  obtain ⟨hgxw, hgyw⟩ := hwg
  -- ====================================================================
  -- Degenerate radii: `R < 0` gives an empty ball; `R = 0` a null set.
  -- ====================================================================
  rcases lt_or_ge 0 R with hRpos | hR0
  case inr =>
    -- `closedBall x R` is either empty (`R < 0`) or a single point (`R = 0`): take the constant
    -- map `f x`, whose `C¹`-ness and closeness are immediate, and whose energy integral is over a
    -- null set.
    refine ⟨fun _ => f x, contDiff_const, ?_, ?_⟩
    · intro z hz
      rcases lt_or_eq_of_le hR0 with hRneg | hR0'
      · simp only [Metric.closedBall_eq_empty.mpr hRneg, Set.mem_empty_iff_false] at hz
      · rw [Metric.mem_closedBall, hR0', dist_le_zero] at hz
        subst hz; simp [le_of_lt hε]
    · have hnull : volume (Metric.closedBall x R) = 0 := by
        rcases lt_or_eq_of_le hR0 with hRneg | hR0'
        · rw [Metric.closedBall_eq_empty.mpr hRneg]; simp
        · rw [hR0', Metric.closedBall_zero]; simp
      rw [setLIntegral_measure_zero _ _ hnull]; exact zero_le
  -- ====================================================================
  -- The genuine case `R > 0`.
  -- ====================================================================
  -- (Cut) A smooth cutoff `χ` adapted to `ball x (R+1) ⊇ closedBall x R`, with compact support.
  obtain ⟨χ, hχ_cd, hχ_cs, hχ_nonneg, hχ_le1, hχ_one, hχ_supp, -⟩ :=
    exists_cutoff_ball x (R + 1) (by positivity)
  have hχ_cont : Continuous χ := hχ_cd.continuous
  -- The localized function `u = χ • f` and its weak partials `Gx`, `Gy`.
  set u : ℂ → ℂ := fun z => (χ z : ℝ) • f z with hu_def
  set Gx : ℂ → ℂ := fun z => (χ z : ℝ) • gx z + ((fderiv ℝ χ z) 1) • f z with hGx_def
  set Gy : ℂ → ℂ := fun z => (χ z : ℝ) • gy z + ((fderiv ℝ χ z) Complex.I) • f z with hGy_def
  -- Local integrability of `f`, `gx`, `gy` on `univ`.
  have hfloc : LocallyIntegrableOn f Set.univ := by
    rw [locallyIntegrableOn_univ]; exact hfcont.locallyIntegrable
  have hlocOfMemLp : ∀ {h : ℂ → ℂ}, MemLpLocOn h 2 Set.univ → LocallyIntegrableOn h Set.univ := by
    intro h hmem
    rw [locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro k hk
    have : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hmem k (Set.subset_univ _) hk).mono_exponent (by norm_num))
  have hgxloc : LocallyIntegrableOn gx Set.univ := hlocOfMemLp hgx
  have hgyloc : LocallyIntegrableOn gy Set.univ := hlocOfMemLp hgy
  -- (Leibniz) `Gx`, `Gy` are the weak partials of `u` on `univ`.
  have hGxw : HasWeakDirDeriv 1 Gx u Set.univ :=
    hgxw.smul_smooth hχ_cd hfloc hgxloc
  have hGyw : HasWeakDirDeriv Complex.I Gy u Set.univ :=
    hgyw.smul_smooth hχ_cd hfloc hgyloc
  -- The compact set `K = tsupport χ` carrying the supports of `u`, `Gx`, `Gy`.
  set K : Set ℂ := tsupport χ with hK_def
  have hK_compact : IsCompact K := hχ_cs
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  -- Global a.e.-measurability of `gx`, `gy` (patched over the cover by closed balls).
  have haem_of_loc : ∀ {h : ℂ → ℂ}, MemLpLocOn h 2 Set.univ → AEMeasurable h volume := by
    intro h hmem
    have hcover : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n) = Set.univ := iUnion_closedBall_nat 0
    have hh : AEMeasurable h (volume.restrict (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n)) := by
      refine AEMeasurable.iUnion (fun n => ?_)
      exact ((hmem (Metric.closedBall 0 n) (Set.subset_univ _)
        (isCompact_closedBall 0 n)).aestronglyMeasurable).aemeasurable
    rwa [hcover, Measure.restrict_univ] at hh
  have hgx_aem : AEMeasurable gx volume := haem_of_loc hgx
  have hgy_aem : AEMeasurable gy volume := haem_of_loc hgy
  -- The fderiv of `χ` is continuous (smoothness `≥ 1`) and vanishes off `K`.
  have hdχ_cont : Continuous (fderiv ℝ χ) := hχ_cd.continuous_fderiv (by simp)
  have hdχ1_cont : Continuous (fun z => (fderiv ℝ χ z) 1) := hdχ_cont.clm_apply continuous_const
  have hdχI_cont : Continuous (fun z => (fderiv ℝ χ z) Complex.I) :=
    hdχ_cont.clm_apply continuous_const
  have hχ_off : ∀ z, z ∉ K → χ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (by rwa [← hK_def])
  have hdχ_off : ∀ z, z ∉ K → fderiv ℝ χ z = 0 := fun z hz =>
    fderiv_of_notMem_tsupport (𝕜 := ℝ) (by rwa [← hK_def])
  -- Supports of `u`, `Gx`, `Gy` are inside `K`.
  have hu_supp : Function.support u ⊆ K := by
    intro z hz
    by_contra hzK
    refine hz ?_
    simp [hu_def, hχ_off z hzK]
  have hGx_supp : Function.support Gx ⊆ K := by
    intro z hz
    by_contra hzK
    refine hz ?_
    simp [hGx_def, hχ_off z hzK, hdχ_off z hzK]
  have hGy_supp : Function.support Gy ⊆ K := by
    intro z hz
    by_contra hzK
    refine hz ?_
    simp [hGy_def, hχ_off z hzK, hdχ_off z hzK]
  -- `u` is continuous; `Gx`, `Gy` are a.e.-strongly measurable.  Real-smul = multiplication.
  have hu_cont : Continuous u := by
    have heq : u = fun z => (χ z : ℂ) * f z := by
      funext z; simp only [hu_def, Complex.real_smul]
    rw [heq]; exact (Complex.continuous_ofReal.comp hχ_cont).mul hfcont
  have hu_aesm : AEStronglyMeasurable u volume := hu_cont.aestronglyMeasurable
  have hGx_aesm : AEStronglyMeasurable Gx volume := by
    have heq : Gx = fun z => (χ z : ℂ) * gx z + ((fderiv ℝ χ z) 1 : ℂ) * f z := by
      funext z; simp only [hGx_def, Complex.real_smul]
    rw [heq]
    refine (((Complex.continuous_ofReal.comp hχ_cont).aemeasurable.mul hgx_aem).add
      (((Complex.continuous_ofReal.comp hdχ1_cont).aemeasurable).mul
        hfcont.aemeasurable)).aestronglyMeasurable
  have hGy_aesm : AEStronglyMeasurable Gy volume := by
    have heq : Gy = fun z => (χ z : ℂ) * gy z + ((fderiv ℝ χ z) Complex.I : ℂ) * f z := by
      funext z; simp only [hGy_def, Complex.real_smul]
    rw [heq]
    refine (((Complex.continuous_ofReal.comp hχ_cont).aemeasurable.mul hgy_aem).add
      (((Complex.continuous_ofReal.comp hdχI_cont).aemeasurable).mul
        hfcont.aemeasurable)).aestronglyMeasurable
  -- Compact support of `u`, `Gx`, `Gy`.
  have hu_cs : HasCompactSupport u :=
    HasCompactSupport.of_support_subset_isCompact hK_compact hu_supp
  have hGx_cs : HasCompactSupport Gx :=
    HasCompactSupport.of_support_subset_isCompact hK_compact hGx_supp
  have hGy_cs : HasCompactSupport Gy :=
    HasCompactSupport.of_support_subset_isCompact hK_compact hGy_supp
  -- Finite measure of the restriction to the compact `K`.
  have hKfin : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK_compact.measure_lt_top⟩
  -- `gx`, `gy` are `L²` on the compact `K`.
  have hgxK : MemLp gx 2 (volume.restrict K) := hgx K (Set.subset_univ _) hK_compact
  have hgyK : MemLp gy 2 (volume.restrict K) := hgy K (Set.subset_univ _) hK_compact
  -- Continuous functions are bounded on the compact `K`: `f` and the two partials of `χ`.
  obtain ⟨Mf, hMf⟩ := hK_compact.exists_bound_of_continuousOn hfcont.continuousOn
  obtain ⟨Mχ1, hMχ1⟩ := hK_compact.exists_bound_of_continuousOn hdχ1_cont.continuousOn
  obtain ⟨MχI, hMχI⟩ := hK_compact.exists_bound_of_continuousOn hdχI_cont.continuousOn
  -- `u`, `Gx`, `Gy` are globally `L²`.
  have hu2 : MemLp u 2 volume := hu_cont.memLp_of_hasCompactSupport hu_cs
  -- Helper: a function supported in `K` and `L²` on `restrict K` is globally `L²`.
  have memLp_of_restrict : ∀ {h : ℂ → ℂ}, AEStronglyMeasurable h volume →
      Function.support h ⊆ K → MemLp h 2 (volume.restrict K) → MemLp h 2 volume := by
    intro h haesm hsupp hmemK
    refine ⟨haesm, ?_⟩
    rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
    exact hmemK.2
  -- a.e.-strong-measurability of the four `ℝ • ℂ` pieces, via the multiplication form.
  have aesm_smul : ∀ {a : ℂ → ℝ} {b : ℂ → ℂ}, Continuous a → AEMeasurable b volume →
      AEStronglyMeasurable (fun z => a z • b z) (volume.restrict K) := by
    intro a b ha hb
    have heq : (fun z => a z • b z) = fun z => (a z : ℂ) * b z := by
      funext z; rw [Complex.real_smul]
    rw [heq]
    exact (((Complex.continuous_ofReal.comp ha).aemeasurable).mul hb).aestronglyMeasurable.restrict
  have hGx2 : MemLp Gx 2 volume := by
    refine memLp_of_restrict hGx_aesm hGx_supp ?_
    -- On `K`: `Gx = χ•gx + ∂₁χ•f`, the first dominated by `gx`, the second bounded.
    refine MemLp.add ?_ ?_
    · refine MemLp.of_le hgxK (aesm_smul hχ_cont hgx_aem) ?_
      refine Filter.Eventually.of_forall (fun z => ?_)
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have : |χ z| ≤ 1 := abs_le.mpr ⟨by linarith [hχ_nonneg z], hχ_le1 z⟩
      nlinarith [norm_nonneg (gx z), this]
    · refine MemLp.of_bound (aesm_smul hdχ1_cont hfcont.aemeasurable) (Mχ1 * Mf) ?_
      rw [ae_restrict_iff' hK_meas]
      refine Filter.Eventually.of_forall (fun z hz => ?_)
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |(fderiv ℝ χ z) 1| ≤ Mχ1 := by
        have := hMχ1 z hz; rwa [Real.norm_eq_abs] at this
      have h2 : ‖f z‖ ≤ Mf := hMf z hz
      have hM10 : 0 ≤ Mχ1 := le_trans (abs_nonneg _) h1
      exact mul_le_mul h1 h2 (norm_nonneg _) hM10
  have hGy2 : MemLp Gy 2 volume := by
    refine memLp_of_restrict hGy_aesm hGy_supp ?_
    refine MemLp.add ?_ ?_
    · refine MemLp.of_le hgyK (aesm_smul hχ_cont hgy_aem) ?_
      refine Filter.Eventually.of_forall (fun z => ?_)
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have : |χ z| ≤ 1 := abs_le.mpr ⟨by linarith [hχ_nonneg z], hχ_le1 z⟩
      nlinarith [norm_nonneg (gy z), this]
    · refine MemLp.of_bound (aesm_smul hdχI_cont hfcont.aemeasurable) (MχI * Mf) ?_
      rw [ae_restrict_iff' hK_meas]
      refine Filter.Eventually.of_forall (fun z hz => ?_)
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |(fderiv ℝ χ z) Complex.I| ≤ MχI := by
        have := hMχI z hz; rwa [Real.norm_eq_abs] at this
      have h2 : ‖f z‖ ≤ Mf := hMf z hz
      have hM10 : 0 ≤ MχI := le_trans (abs_nonneg _) h1
      exact mul_le_mul h1 h2 (norm_nonneg _) hM10
  -- Local integrability of `u`, `Gx`, `Gy` (consumed by the convolution-derivative lemma).
  have hu_li : MeasureTheory.LocallyIntegrable u := hu2.locallyIntegrable (by norm_num)
  have hGx_li : MeasureTheory.LocallyIntegrable Gx := hGx2.locallyIntegrable (by norm_num)
  have hGy_li : MeasureTheory.LocallyIntegrable Gy := hGy2.locallyIntegrable (by norm_num)
  -- ====================================================================
  -- (F) Mollification commutes with the weak directional derivative:
  --   `(fderiv (ρ ⋆ G) z) v = (ρ ⋆ ∂ᵥG) z`.
  -- ====================================================================
  have fderiv_conv : ∀ {F gv : ℂ → ℂ} {v : ℂ},
      HasWeakDirDeriv v gv F Set.univ →
      MeasureTheory.LocallyIntegrable F → MeasureTheory.LocallyIntegrable gv →
      ∀ {ρ : ℂ → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ →
      HasCompactSupport ρ → ∀ (z : ℂ),
        (fderiv ℝ (MeasureTheory.convolution ρ F
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) z) v
          = MeasureTheory.convolution ρ gv (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
    intro F gv v hv hF hgv ρ hρ_smooth hρ_supp z
    have _hgv := hgv
    set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
    have hρ_one : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) ρ := hρ_smooth.of_le (by exact_mod_cast le_top)
    have hρ_diff : Differentiable ℝ ρ :=
      hρ_one.differentiable (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
    have hdρ_supp : HasCompactSupport (fderiv ℝ ρ) := hρ_supp.fderiv ℝ
    have hderiv :
        HasFDerivAt (MeasureTheory.convolution ρ F L volume)
          (MeasureTheory.convolution (fderiv ℝ ρ) F (L.precompL ℂ) volume z) z :=
      HasCompactSupport.hasFDerivAt_convolution_left L hρ_supp hρ_one hF z
    rw [hderiv.fderiv]
    have hconvexists :
        MeasureTheory.ConvolutionExistsAt (fderiv ℝ ρ) F z (L.precompL ℂ) volume :=
      (hdρ_supp.convolutionExists_left (L.precompL ℂ)
        (hρ_one.continuous_fderiv (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))) hF) z
    rw [MeasureTheory.convolution_def,
        ContinuousLinearMap.integral_apply hconvexists.integrable]
    simp only [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.lsmul_apply]
    have hcv :
        (∫ t, ((fderiv ℝ ρ t) v) • F (z - t) ∂volume)
          = ∫ w, ((fderiv ℝ ρ (z - w)) v) • F w ∂volume := by
      have hself := MeasureTheory.integral_sub_left_eq_self
        (fun t => ((fderiv ℝ ρ t) v) • F (z - t)) volume z
      simp only [sub_sub_cancel] at hself
      exact hself.symm
    refine hcv.trans ?_
    set φz : ℂ → ℝ := fun w => ρ (z - w) with hφz
    have hφz_fderiv : ∀ w, (fderiv ℝ φz w) v = -((fderiv ℝ ρ (z - w)) v) := by
      intro w
      have hsub : HasFDerivAt (fun w : ℂ => z - w) (-ContinuousLinearMap.id ℝ ℂ) w := by
        simpa using (hasFDerivAt_id w).const_sub z
      have hcomp : HasFDerivAt φz
          ((fderiv ℝ ρ (z - w)).comp (-ContinuousLinearMap.id ℝ ℂ)) w :=
        (hρ_diff (z - w)).hasFDerivAt.comp w hsub
      rw [hcomp.fderiv]
      simp only [ContinuousLinearMap.comp_apply, neg_apply,
        ContinuousLinearMap.id_apply, map_neg]
    have hint_eq :
        (∫ w, ((fderiv ℝ ρ (z - w)) v) • F w ∂volume)
          = -∫ w, ((fderiv ℝ φz w) v) • F w ∂volume := by
      rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
      change ((fderiv ℝ ρ (z - w)) v) • F w = -(((fderiv ℝ φz w) v) • F w)
      rw [hφz_fderiv w]
      rw [show (-(fderiv ℝ ρ (z - w)) v) • F w = -(((fderiv ℝ ρ (z - w)) v) • F w)
        from neg_smul _ _, neg_neg]
    rw [hint_eq]
    have hφz_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φz :=
      hρ_smooth.comp (contDiff_const.sub contDiff_id)
    have hφz_supp : HasCompactSupport φz :=
      hρ_supp.comp_homeomorph (Homeomorph.subLeft z)
    have hwd := hv φz hφz_smooth hφz_supp (Set.subset_univ _)
    rw [hwd, neg_neg]
    rw [MeasureTheory.convolution_def, ← MeasureTheory.integral_sub_left_eq_self
        (fun t => (L (ρ t)) (gv (z - t))) volume z]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    simp only [hφz, sub_sub_cancel, hL, ContinuousLinearMap.lsmul_apply]
  -- ====================================================================
  -- (C) `L²` mollification convergence `‖ρ_n ⋆ G - G‖₂ → 0` for `G ∈ L²`.
  -- ====================================================================
  have conv_tendsto : ∀ {G : ℂ → ℂ},
      MemLp G 2 volume → ∀ (φ : ℕ → ContDiffBump (0 : ℂ)),
      Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => eLpNorm
          (MeasureTheory.convolution ((φ n).normed volume) G
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - G) 2 volume)
        Filter.atTop (nhds 0) := by
    intro G hG φ hφrout
    set Cg : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed volume)
      G (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCg
    have hP3 : ∀ (h : ℂ → ℂ), HasCompactSupport h → ContDiff ℝ (⊤ : ℕ∞) h →
        Filter.Tendsto (fun n => eLpNorm
          (MeasureTheory.convolution ((φ n).normed volume) h
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - h) 2 volume)
          Filter.atTop (nhds 0) := by
      intro h hh_supp hh_smooth
      obtain ⟨M, hM⟩ := hh_smooth.continuous.bounded_above_of_compact_support hh_supp
      have hM0 : 0 ≤ M := le_trans (norm_nonneg (h 0)) (hM 0)
      set Kset : Set ℂ := Metric.cthickening 1 (tsupport h) with hKdef
      have hKcompact : IsCompact Kset := hh_supp.isCompact.cthickening
      have hKmeas : MeasurableSet Kset := hKcompact.measurableSet
      have hKfin' : volume Kset < ⊤ := hKcompact.measure_lt_top
      have htsupp_sub : tsupport h ⊆ Kset := Metric.self_subset_cthickening _
      set Cn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed volume)
        h (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCn
      have hCn_cont : ∀ n, Continuous (Cn n) := fun n =>
        HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
      have hptwise : ∀ x, Filter.Tendsto (fun n => Cn n x) Filter.atTop (nhds (h x)) := fun x =>
        ContDiffBump.convolution_tendsto_right_of_continuous hφrout hh_smooth.continuous x
      have hCnbd : ∀ n x, ‖Cn n x‖ ≤ M := by
        intro n x
        set ρ := (φ n).normed volume with hρ
        have hρnn : ∀ t, 0 ≤ ρ t := (φ n).nonneg_normed
        rw [hCn]; simp only; rw [MeasureTheory.convolution_def]
        calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t)) ∂volume‖
            ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t))‖ ∂volume :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ t, ρ t * M ∂volume := by
              have hint : Integrable ρ volume :=
                ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
                  ((φ n).hasCompactSupport_normed)
              apply integral_mono_of_nonneg
                (Filter.Eventually.of_forall (fun t => norm_nonneg _)) (hint.mul_const M)
              refine Filter.Eventually.of_forall (fun t => ?_)
              simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hρnn t)]
              exact mul_le_mul_of_nonneg_left (hM _) (hρnn t)
          _ = (∫ t, ρ t ∂volume) * M := by rw [integral_mul_const]
          _ = M := by rw [(φ n).integral_normed]; ring
      have hMh : ∀ y, ‖h y‖ ≤ M := hM
      have hsupp_in_K : ∀ᶠ n in Filter.atTop, Function.support (Cn n) ⊆ Kset := by
        have hev : ∀ᶠ n in Filter.atTop, (φ n).rOut ≤ 1 := by
          have := hφrout.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
          filter_upwards [this] with n hn using hn
        filter_upwards [hev] with n hrout1
        have haddsub : Metric.closedBall (0 : ℂ) (φ n).rOut + tsupport h ⊆ Kset := by
          intro z hz
          obtain ⟨a, ha, b, hb, rfl⟩ := hz
          rw [Metric.mem_closedBall, dist_zero_right] at ha
          refine Metric.mem_cthickening_of_dist_le (a + b) b 1 (tsupport h) hb ?_
          rw [dist_eq_norm]; simp only [add_sub_cancel_right]; exact le_trans ha hrout1
        have hsub := MeasureTheory.support_convolution_subset (μ := volume)
          (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
          (f := (φ n).normed volume) (g := h)
        refine hsub.trans (le_trans ?_ haddsub)
        apply Set.add_subset_add _ (subset_tsupport h)
        intro z hz
        have h1 : z ∈ tsupport ((φ n).normed volume) := subset_tsupport _ hz
        rwa [(φ n).tsupport_normed_eq] at h1
      have : MeasureTheory.IsFiniteMeasure (volume.restrict Kset) := by
        constructor; rw [MeasureTheory.Measure.restrict_apply_univ]; exact hKfin'
      set D : ℕ → ℂ → ℂ := fun n => Cn n - h with hD
      have hrestrict : ∀ᶠ n in Filter.atTop,
          eLpNorm (D n) 2 volume = eLpNorm (D n) 2 (volume.restrict Kset) := by
        filter_upwards [hsupp_in_K] with n hn
        have hDsupp : Function.support (D n) ⊆ Kset := by
          intro x hx
          simp only [hD, Pi.sub_apply, Function.mem_support, ne_eq] at hx
          by_contra hxK
          have h1 : Cn n x = 0 := Function.notMem_support.mp (fun hc => hxK (hn hc))
          have h2 : h x = 0 := Function.notMem_support.mp
            (fun hc => hxK (htsupp_sub (subset_tsupport h hc)))
          rw [h1, h2, sub_zero] at hx; exact hx rfl
        rw [← eLpNorm_indicator_eq_eLpNorm_restrict hKmeas, Set.indicator_eq_self.mpr hDsupp]
      have hgoal : Filter.Tendsto (fun n => eLpNorm (D n) 2 (volume.restrict Kset))
          Filter.atTop (nhds 0) := by
        have hui : MeasureTheory.UnifIntegrable Cn 2 (volume.restrict Kset) := by
          refine MeasureTheory.unifIntegrable_of (by norm_num) (by norm_num)
            (fun n => (hCn_cont n).aestronglyMeasurable) (fun ε hε => ?_)
          refine ⟨(M.toNNReal + 1), fun n => ?_⟩
          have hempty : {x | (M.toNNReal + 1 : ℝ≥0) ≤ ‖Cn n x‖₊} = (∅ : Set ℂ) := by
            ext x
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
            have hb' : ‖Cn n x‖₊ ≤ M.toNNReal := by
              rw [← NNReal.coe_le_coe, Real.coe_toNNReal M hM0]; exact hCnbd n x
            exact lt_of_le_of_lt hb' (by simp)
          rw [hempty, Set.indicator_empty]; simp
        have hhmem : MemLp h 2 (volume.restrict Kset) :=
          MemLp.of_bound hh_smooth.continuous.aestronglyMeasurable M
            (Filter.Eventually.of_forall hMh)
        exact MeasureTheory.tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
          (fun n => (hCn_cont n).aestronglyMeasurable) hhmem hui
          (Filter.Eventually.of_forall hptwise)
      exact Filter.Tendsto.congr' (hrestrict.mono (fun n hn => hn.symm)) hgoal
    have hP2 : ∀ (w : ℂ → ℂ), MemLp w 2 volume → ∀ (ε : ℝ),
        eLpNorm w 2 volume ≤ ENNReal.ofReal ε → ∀ n,
          eLpNorm (MeasureTheory.convolution ((φ n).normed volume) w
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume ≤ ENNReal.ofReal ε := by
      intro w hw ε hclose n
      set ρc : ℂ → ℂ := fun z => (((φ n).normed volume z : ℝ) : ℂ) with hρc
      have hconv_eq : MeasureTheory.convolution ((φ n).normed volume) w
            (ContinuousLinearMap.lsmul ℝ ℝ) volume
          = MeasureTheory.convolution ρc w (ContinuousLinearMap.mul ℂ ℂ) volume := by
        funext xx
        rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        simp only [hρc, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply]
        exact (Complex.real_smul).symm
      rw [hconv_eq]
      have hρc_memLp : MemLp ρc 1 volume := by
        have hcont : Continuous ρc :=
          Complex.continuous_ofReal.comp ((φ n).contDiff_normed (n := 0)).continuous
        have hsupp : HasCompactSupport ρc :=
          ((φ n).hasCompactSupport_normed).comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
        exact hcont.memLp_of_hasCompactSupport hsupp
      have hρc_norm : eLpNorm ρc 1 volume = 1 := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        have hint : Integrable ((φ n).normed volume) volume :=
          ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
            ((φ n).hasCompactSupport_normed)
        have hnn : 0 ≤ᵐ[volume] (φ n).normed volume :=
          Filter.Eventually.of_forall (fun z => (φ n).nonneg_normed z)
        calc ∫⁻ z, ‖ρc z‖ₑ ∂volume
            = ∫⁻ z, ENNReal.ofReal ((φ n).normed volume z) ∂volume := by
              refine lintegral_congr (fun z => ?_)
              rw [hρc,
                show ‖(((φ n).normed volume z : ℝ) : ℂ)‖ₑ
                    = ‖(φ n).normed volume z‖ₑ from by
                  rw [← enorm_norm, Complex.norm_real, enorm_norm],
                Real.enorm_of_nonneg ((φ n).nonneg_normed z)]
          _ = ENNReal.ofReal (∫ z, (φ n).normed volume z ∂volume) :=
              (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
          _ = 1 := by rw [(φ n).integral_normed]; simp
      calc eLpNorm (MeasureTheory.convolution ρc w (ContinuousLinearMap.mul ℂ ℂ)
              volume) 2 volume
          ≤ eLpNorm ρc 1 volume * eLpNorm w 2 volume :=
            eLpNorm_convolution_le hρc_memLp hw
        _ = eLpNorm w 2 volume := by rw [hρc_norm, one_mul]
        _ ≤ ENNReal.ofReal ε := hclose
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε'
    by_cases htop : ε = ⊤
    · refine Filter.Eventually.of_forall (fun n => ?_)
      rw [htop]; exact le_top
    set δ : ℝ := ε.toReal with hδ
    have hδpos : 0 < δ := ENNReal.toReal_pos hε'.ne' htop
    have hδle : ENNReal.ofReal δ = ε := ENNReal.ofReal_toReal htop
    obtain ⟨hh, hh_supp, hh_smooth, hh_close⟩ := hG.exist_eLpNorm_sub_le
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (ε := δ / 3) (by positivity)
    have hh_memLp : MemLp hh 2 volume :=
      hh_smooth.continuous.memLp_of_hasCompactSupport hh_supp
    have hgh_memLp : MemLp (G - hh) 2 volume := hG.sub hh_memLp
    have hP2gh : ∀ n, eLpNorm (MeasureTheory.convolution ((φ n).normed volume)
          (G - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume
          ≤ ENNReal.ofReal (δ / 3) :=
      hP2 (G - hh) hgh_memLp (δ / 3) hh_close
    have hP3ev : ∀ᶠ n in Filter.atTop,
        eLpNorm (MeasureTheory.convolution ((φ n).normed volume) hh
          (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) 2 volume
          ≤ ENNReal.ofReal (δ / 3) :=
      (ENNReal.tendsto_nhds_zero.mp (hP3 hh hh_supp hh_smooth) (ENNReal.ofReal (δ / 3))
        (ENNReal.ofReal_pos.mpr (by positivity)))
    have hdecomp : ∀ n, Cg n - G = MeasureTheory.convolution ((φ n).normed volume)
          (G - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
        + (MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - G) := by
      intro n
      have hce1 : MeasureTheory.ConvolutionExists ((φ n).normed volume) (G - hh)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        refine HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous ?_
        exact (hG.locallyIntegrable (by norm_num)).sub hh_smooth.continuous.locallyIntegrable
      have hce2 : MeasureTheory.ConvolutionExists ((φ n).normed volume) hh
          (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
        HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
      have hsplit : Cg n = MeasureTheory.convolution ((φ n).normed volume)
            (G - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
          + MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        rw [hCg]; simp only
        rw [← MeasureTheory.ConvolutionExists.distrib_add hce1 hce2]
        congr 1; abel
      rw [hsplit]; abel
    filter_upwards [hP3ev] with n hn3
    rw [hdecomp n]
    have hm1 : AEStronglyMeasurable (MeasureTheory.convolution
        ((φ n).normed volume) (G - hh) (ContinuousLinearMap.lsmul ℝ ℝ)
        volume) volume :=
      (HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous
        ((hG.locallyIntegrable (by norm_num)).sub
          hh_smooth.continuous.locallyIntegrable)).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (MeasureTheory.convolution
        ((φ n).normed volume) hh (ContinuousLinearMap.lsmul ℝ ℝ)
        volume - hh) volume :=
      ((HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous
        hh_smooth.continuous.locallyIntegrable).sub hh_smooth.continuous).aestronglyMeasurable
    have hm3 : AEStronglyMeasurable (hh - G) volume :=
      (hh_memLp.sub hG).1
    have hkey : eLpNorm (MeasureTheory.convolution ((φ n).normed volume)
          (G - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
        + (MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - G)) 2
          volume
        ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) := by
      refine le_trans (eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)) ?_
      refine add_le_add (le_trans (eLpNorm_add_le hm1 hm2 (by norm_num)) ?_) ?_
      · exact add_le_add (hP2gh n) hn3
      · rw [eLpNorm_sub_comm]; exact hh_close
    refine le_trans hkey ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← hδle]
    apply le_of_eq; congr 1; ring
  -- ====================================================================
  -- On the closed ball `B = closedBall x R` the cutoff is identically `1`, hence `u = f`,
  -- `Gx = gx` and `Gy = gy` there.
  -- ====================================================================
  set B : Set ℂ := Metric.closedBall x R with hB_def
  have hB_sub : B ⊆ Metric.ball x (R + 1) := by
    refine Metric.closedBall_subset_ball ?_; linarith
  have hχ1_on_ball : Set.EqOn χ (fun _ => (1 : ℝ)) (Metric.ball x (R + 1)) :=
    fun z hz => hχ_one z hz
  -- On the open ball `χ` is locally constant `1`, so its Fréchet derivative vanishes there.
  have hdχ_zero_on_ball : ∀ z ∈ Metric.ball x (R + 1), fderiv ℝ χ z = 0 := by
    intro z hz
    have heqf : χ =ᶠ[nhds z] (fun _ => (1 : ℝ)) :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz) hχ1_on_ball
    rw [heqf.fderiv_eq]; simp
  -- `Gx = gx` and `Gy = gy` on `B`.
  have hGx_on_B : ∀ z ∈ B, Gx z = gx z := by
    intro z hz
    have hzb := hB_sub hz
    simp [hGx_def, hχ_one z hzb, hdχ_zero_on_ball z hzb]
  have hGy_on_B : ∀ z ∈ B, Gy z = gy z := by
    intro z hz
    have hzb := hB_sub hz
    simp [hGy_def, hχ_one z hzb, hdχ_zero_on_ball z hzb]
  have hu_on_B : ∀ z ∈ B, u z = f z := by
    intro z hz
    simp [hu_def, hχ_one z (hB_sub hz)]
  -- ====================================================================
  -- Choose the mollifier radius.  Sequence `φ₀ n` with `rOut = 2/(n+2) → 0`.
  -- ====================================================================
  set φ₀ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ₀
  have hφ₀rout : Filter.Tendsto (fun n => (φ₀ n).rOut) Filter.atTop (nhds 0) := by
    have heq : (fun n : ℕ => (φ₀ n).rOut) = fun n : ℕ => (2 : ℝ) / (n + 2) := rfl
    rw [heq]
    exact Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  -- `u` is uniformly continuous (continuous with compact support), so the mollified family is
  -- uniformly `ε`-close once the support radius is small.
  have hu_uc : UniformContinuous u := hu_cs.uniformContinuous_of_continuous hu_cont
  obtain ⟨δu, hδu_pos, hδu⟩ : ∃ δ > 0, ∀ z z' : ℂ, dist z z' < δ → dist (u z) (u z') ≤ ε := by
    rw [Metric.uniformContinuous_iff] at hu_uc
    obtain ⟨δ, hδpos, hδ⟩ := hu_uc ε hε
    exact ⟨δ, hδpos, fun z z' hzz' => (hδ hzz').le⟩
  -- (Uniform) For every mollifier of `rOut < δu`, the mollification is `ε`-close to `u` everywhere.
  have hclose_of_rout : ∀ n, (φ₀ n).rOut < δu →
      ∀ z, ‖(MeasureTheory.convolution ((φ₀ n).normed volume) u
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) z - u z‖ ≤ ε := by
    intro n hn z
    have hsupp_ball : Function.support ((φ₀ n).normed volume) ⊆ Metric.ball (0 : ℂ) δu := by
      rw [(φ₀ n).support_normed_eq]
      exact Metric.ball_subset_ball hn.le
    have hgz : ∀ y ∈ Metric.ball z δu, dist (u y) (u z) ≤ ε := by
      intro y hy
      rw [Metric.mem_ball] at hy
      exact hδu y z hy
    have := dist_convolution_le (le_of_lt hε) hsupp_ball ((φ₀ n).nonneg_normed)
      ((φ₀ n).integral_normed) hu_cont.aestronglyMeasurable hgz
    rwa [dist_eq_norm] at this
  -- (L²) The gradient mollifications converge to `Gx`, `Gy` in `L²`.
  have hconvGx := conv_tendsto hGx2 φ₀ hφ₀rout
  have hconvGy := conv_tendsto hGy2 φ₀ hφ₀rout
  -- Pick a threshold `δ` for the `L²` gradient differences with `2 δ² ≤ ε`.
  set δ : ℝ := Real.sqrt (ε / 2) with hδ_def
  have hδ_pos : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδ_sq : δ ^ 2 = ε / 2 := Real.sq_sqrt (by positivity)
  -- Eventually-small `L²` gradient differences and small `rOut`.
  have hevGx : ∀ᶠ n in Filter.atTop, eLpNorm
      (MeasureTheory.convolution ((φ₀ n).normed volume) Gx
        (ContinuousLinearMap.lsmul ℝ ℝ) volume - Gx) 2 volume ≤ ENNReal.ofReal δ :=
    ENNReal.tendsto_nhds_zero.mp hconvGx (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ_pos)
  have hevGy : ∀ᶠ n in Filter.atTop, eLpNorm
      (MeasureTheory.convolution ((φ₀ n).normed volume) Gy
        (ContinuousLinearMap.lsmul ℝ ℝ) volume - Gy) 2 volume ≤ ENNReal.ofReal δ :=
    ENNReal.tendsto_nhds_zero.mp hconvGy (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ_pos)
  have hevRout : ∀ᶠ n in Filter.atTop, (φ₀ n).rOut < δu :=
    hφ₀rout.eventually (eventually_lt_nhds hδu_pos)
  obtain ⟨N, hNGx, hNGy, hNrout⟩ := (hevGx.and (hevGy.and hevRout)).exists
  -- ====================================================================
  -- The output map `g = ρ_N ⋆ u`.
  -- ====================================================================
  set ρ : ℂ → ℝ := (φ₀ N).normed volume with hρdef
  set g : ℂ → ℂ := MeasureTheory.convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume with hgdef
  have hρ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ := (φ₀ N).contDiff_normed
  have hρ_cs : HasCompactSupport ρ := (φ₀ N).hasCompactSupport_normed
  -- `g` is `C¹`.
  have hg_contDiff : ContDiff ℝ 1 g := by
    refine HasCompactSupport.contDiff_convolution_left _ hρ_cs ?_ hu_li
    exact hρ_smooth.of_le (by exact_mod_cast le_top)
  -- The two directional derivatives of `g` are the mollifications of `Gx`, `Gy`.
  have hdx : (fun z => (fderiv ℝ g z) 1)
      = MeasureTheory.convolution ρ Gx (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext z; exact fderiv_conv hGxw hu_li hGx_li hρ_smooth hρ_cs z
  have hdy : (fun z => (fderiv ℝ g z) Complex.I)
      = MeasureTheory.convolution ρ Gy (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext z; exact fderiv_conv hGyw hu_li hGy_li hρ_smooth hρ_cs z
  refine ⟨g, hg_contDiff, ?_, ?_⟩
  · -- (Closeness) On `B = closedBall x R`, `g` is `ε`-close to `f` (via `u = f` there).
    intro z hz
    have h1 : ‖g z - u z‖ ≤ ε := hclose_of_rout N hNrout z
    rw [hu_on_B z hz] at h1
    exact h1
  · -- (Energy) The gradient energy of `g - (gx, gy)` over `B`.
    -- On `B`, `gx = Gx`, `gy = Gy`, so the integrand is `‖ρ⋆Gx - Gx‖² + ‖ρ⋆Gy - Gy‖²`.
    set Dx : ℂ → ℂ := fun w =>
      MeasureTheory.convolution ρ Gx (ContinuousLinearMap.lsmul ℝ ℝ) volume w - Gx w with hDx_def
    set Dy : ℂ → ℂ := fun w =>
      MeasureTheory.convolution ρ Gy (ContinuousLinearMap.lsmul ℝ ℝ) volume w - Gy w with hDy_def
    -- Pointwise rewrite of the integrand on `B`.
    have hpt : ∀ z ∈ B,
        energyDensity (fun w => (fderiv ℝ g w) 1 - gx w)
          (fun w => (fderiv ℝ g w) Complex.I - gy w) z
        = energyDensity Dx Dy z := by
      intro z hz
      simp only [energyDensity, hDx_def, hDy_def]
      rw [show (fderiv ℝ g z) 1 = MeasureTheory.convolution ρ Gx
            (ContinuousLinearMap.lsmul ℝ ℝ) volume z from congrFun hdx z,
          show (fderiv ℝ g z) Complex.I = MeasureTheory.convolution ρ Gy
            (ContinuousLinearMap.lsmul ℝ ℝ) volume z from congrFun hdy z,
          hGx_on_B z hz, hGy_on_B z hz]
    -- Rewrite the integral over `B`.
    rw [setLIntegral_congr_fun (measurableSet_closedBall) (fun z hz => hpt z hz)]
    -- `energyDensity Dx Dy = ‖Dx‖² + ‖Dy‖²`; split the integral.
    have hDx_aem : AEMeasurable (fun z => (‖Dx z‖₊ : ℝ≥0∞) ^ 2) volume := by
      have : AEStronglyMeasurable Dx volume := by
        refine (HasCompactSupport.continuous_convolution_left _ hρ_cs hρ_smooth.continuous
          hGx_li).aestronglyMeasurable.sub hGx_aesm
      exact (this.aemeasurable.enorm.pow_const 2).congr
        (by filter_upwards with z using by rw [enorm_eq_nnnorm])
    -- The energy splits and each summand is bounded by the `L²` norm of the difference, squared.
    have hsplit : (∫⁻ z in B, energyDensity Dx Dy z)
        = (∫⁻ z in B, (‖Dx z‖₊ : ℝ≥0∞) ^ 2) + ∫⁻ z in B, (‖Dy z‖₊ : ℝ≥0∞) ^ 2 := by
      simp only [energyDensity]
      exact lintegral_add_left' hDx_aem.restrict _
    rw [hsplit]
    -- Bound each restricted integral by the global `L²` norm squared.
    have hbound : ∀ (D : ℂ → ℂ), eLpNorm D 2 volume ≤ ENNReal.ofReal δ →
        (∫⁻ z in B, (‖D z‖₊ : ℝ≥0∞) ^ 2) ≤ (ENNReal.ofReal δ) ^ 2 := by
      intro D hD
      have hle : (∫⁻ z in B, (‖D z‖₊ : ℝ≥0∞) ^ 2) ≤ ∫⁻ z, (‖D z‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
        setLIntegral_le_lintegral _ _
      refine le_trans hle ?_
      have heq : (∫⁻ z, (‖D z‖₊ : ℝ≥0∞) ^ 2 ∂volume) = (eLpNorm D 2 volume) ^ 2 := by
        have hbase : (∫⁻ z, ‖D z‖ₑ ^ (2 : ℝ) ∂volume) = eLpNorm' D 2 volume ^ (2 : ℝ) :=
          lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num)
        have hlhs : (∫⁻ z, (‖D z‖₊ : ℝ≥0∞) ^ 2 ∂volume)
            = ∫⁻ z, ‖D z‖ₑ ^ (2 : ℝ) ∂volume := by
          refine lintegral_congr (fun z => ?_)
          rw [enorm_eq_nnnorm, ← ENNReal.rpow_natCast (‖D z‖₊ : ℝ≥0∞) 2]; norm_num
        rw [hlhs, hbase, eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num),
          ← ENNReal.rpow_natCast (eLpNorm' D (ENNReal.toReal 2) volume) 2]
        norm_num
      rw [heq]
      exact pow_le_pow_left' hD 2
    -- Assemble: each summand `≤ (ofReal δ)²`, and `2 δ² ≤ ε`.
    refine le_trans (add_le_add (hbound Dx hNGx) (hbound Dy hNGy)) ?_
    rw [← two_mul]
    rw [show (ENNReal.ofReal δ) ^ 2 = ENNReal.ofReal (δ ^ 2) by
      rw [← ENNReal.ofReal_pow hδ_pos.le]]
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp [ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hδ_sq]; ring_nf; linarith

/-- **Continuity of the image-circle diameter in the radius (CL-C2).**

For a continuous `f`, the map `ρ ↦ diam (f '' sphere x ρ)` is continuous on `ρ > 0`. (The sphere
varies continuously in the Hausdorff metric, `f` is uniformly continuous on compacts, and `diam` is
`1`-Lipschitz for the Hausdorff distance on compacta.) Used to pass the radius selected for the
mollified maps to the limit. -/
theorem continuousOn_diam_image_sphere {f : ℂ → ℂ} (hfcont : Continuous f) (x : ℂ) :
    ContinuousOn (fun ρ : ℝ => Metric.diam (f '' Metric.sphere x ρ)) (Set.Ioi 0) := by
  -- Parametrize the circle by the angle `θ ∈ [0, 2π]` via `circleMap`, write the diameter of the
  -- image as the supremum of pairwise distances `Ψ ρ p`, and conclude by the parametric-supremum
  -- continuity lemma `IsCompact.continuous_sSup`.
  set K : Set (ℝ × ℝ) := (Set.Icc 0 (2 * Real.pi)) ×ˢ (Set.Icc 0 (2 * Real.pi)) with hK_def
  -- `Ψ ρ p = dist (f (circleMap x ρ p.1)) (f (circleMap x ρ p.2))`.
  set Ψ : ℝ → ℝ × ℝ → ℝ :=
    fun ρ p => dist (f (circleMap x ρ p.1)) (f (circleMap x ρ p.2)) with hΨ_def
  -- `K` is compact and nonempty.
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hK_compact : IsCompact K := (isCompact_Icc).prod (isCompact_Icc)
  have hK_ne : K.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    exact ⟨Set.left_mem_Icc.mpr hpi, Set.left_mem_Icc.mpr hpi⟩
  -- Joint continuity of `↿Ψ : ℝ × (ℝ × ℝ) → ℝ`.  The map `(ρ, θ) ↦ x + ρ·exp(θ·I)` is continuous.
  have hcircle : Continuous (fun q : ℝ × ℝ => circleMap x q.1 q.2) := by
    simp only [circleMap]
    refine continuous_const.add ?_
    refine Continuous.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp continuous_fst
    · exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hΨ_cont : Continuous (Function.uncurry Ψ) := by
    -- `↿Ψ (ρ, p) = dist (f (circleMap x ρ p.1)) (f (circleMap x ρ p.2))`.
    have harg1 : Continuous (fun q : ℝ × ℝ × ℝ => (q.1, q.2.1)) :=
      continuous_fst.prodMk (continuous_snd.fst)
    have harg2 : Continuous (fun q : ℝ × ℝ × ℝ => (q.1, q.2.2)) :=
      continuous_fst.prodMk (continuous_snd.snd)
    have hfst : Continuous (fun q : ℝ × ℝ × ℝ => f (circleMap x q.1 q.2.1)) :=
      hfcont.comp (hcircle.comp harg1)
    have hsnd : Continuous (fun q : ℝ × ℝ × ℝ => f (circleMap x q.1 q.2.2)) :=
      hfcont.comp (hcircle.comp harg2)
    exact hfst.dist hsnd
  -- For each `ρ > 0`, the diameter of the image equals `sSup (Ψ ρ '' K)`.
  have hEq : Set.EqOn (fun ρ : ℝ => Metric.diam (f '' Metric.sphere x ρ))
      (fun ρ : ℝ => sSup (Ψ ρ '' K)) (Set.Ioi 0) := by
    intro ρ hρ
    simp only [Set.mem_Ioi] at hρ
    -- The sphere is the image of `[0, 2π]` under `circleMap x ρ`.
    have hsphere : Metric.sphere x ρ = circleMap x ρ '' Set.Icc 0 (2 * Real.pi) := by
      have hper := (periodic_circleMap x ρ).image_Icc
        (show (0 : ℝ) < 2 * Real.pi by positivity) 0
      rw [zero_add, range_circleMap, abs_of_pos hρ] at hper
      exact hper.symm
    -- Image of the sphere under `f` is the image of `[0, 2π]` under `θ ↦ f (circleMap x ρ θ)`.
    have himg : f '' Metric.sphere x ρ
        = (fun θ => f (circleMap x ρ θ)) '' Set.Icc 0 (2 * Real.pi) := by
      rw [hsphere, Set.image_image]
    -- `Ψ ρ` is continuous (a slice of `↿Ψ`).
    have hΨρ_cont : Continuous (Ψ ρ) := by
      have : (Ψ ρ) = (fun p : ℝ × ℝ => Function.uncurry Ψ (ρ, p)) := rfl
      rw [this]
      exact hΨ_cont.comp (continuous_const.prodMk continuous_id)
    -- `Ψ ρ '' K` is nonempty and bounded above (continuous image of a compact set).
    have hΨimg_ne : (Ψ ρ '' K).Nonempty := hK_ne.image _
    have hΨimg_bdd : BddAbove (Ψ ρ '' K) :=
      hK_compact.bddAbove_image hΨρ_cont.continuousOn
    -- The image of the sphere under `f` is bounded (continuous image of a compact set).
    have hsphere_compact : IsCompact (Metric.sphere x ρ) := isCompact_sphere x ρ
    have himg_bounded : Bornology.IsBounded (f '' Metric.sphere x ρ) :=
      (hsphere_compact.image hfcont).isBounded
    -- `sSup (Ψ ρ '' K) ≥ 0`.
    have hsup_nonneg : 0 ≤ sSup (Ψ ρ '' K) := by
      obtain ⟨a, p, hp, hav⟩ := hΨimg_ne
      have hmem : a ∈ Ψ ρ '' K := ⟨p, hp, hav⟩
      exact le_trans (by rw [← hav]; exact dist_nonneg) (le_csSup hΨimg_bdd hmem)
    refine le_antisymm ?_ ?_
    · -- `diam ≤ sSup (Ψ ρ '' K)`.
      refine Metric.diam_le_of_forall_dist_le hsup_nonneg ?_
      rw [himg]
      rintro u ⟨θ₁, hθ₁, rfl⟩ v ⟨θ₂, hθ₂, rfl⟩
      refine le_csSup hΨimg_bdd ?_
      exact ⟨(θ₁, θ₂), ⟨hθ₁, hθ₂⟩, rfl⟩
    · -- `sSup (Ψ ρ '' K) ≤ diam`.
      refine csSup_le hΨimg_ne ?_
      rintro w ⟨⟨θ₁, θ₂⟩, ⟨hθ₁, hθ₂⟩, rfl⟩
      simp only [hΨ_def]
      refine Metric.dist_le_diam_of_mem himg_bounded ?_ ?_
      · rw [himg]; exact ⟨θ₁, hθ₁, rfl⟩
      · rw [himg]; exact ⟨θ₂, hθ₂, rfl⟩
  -- Conclude: the parametric supremum is continuous, and it agrees with the diameter on `Ioi 0`.
  refine (IsCompact.continuous_sSup hK_compact hΨ_cont).continuousOn.congr hEq

/-- **Courant–Lebesgue small-energy circle (CL) — the analytic core.**

For a continuous `f` with weak gradient `(gx, gy) ∈ L²_loc`, there is a universal constant `C₀`
(value `π / (2 log 2)`) such that for every centre `x` and radius `r > 0` there is a radius
`ρ ∈ [r, 2r]` whose image circle is small in diameter relative to the Dirichlet energy of the
surrounding disc:
`diam (f '' sphere x ρ)² ≤ C₀ · ∫_{closedBall x (2r)} (‖gx‖² + ‖gy‖²)`.

Assembled from `courantLebesgue_smooth` (CL-smooth) applied to a sequence of mollified maps
(`exists_smooth_approx_L2grad_local`, CL-C1), passing the selected radius to the limit via
`continuousOn_diam_image_sphere` (CL-C2) and `L²`-convergence of the mollified energy. -/
theorem courantLebesgue_smallEnergyCircle {f gx gy : ℂ → ℂ}
    (hfcont : Continuous f) (hwg : HasWeakGradient gx gy f Set.univ)
    (hgx : MemLpLocOn gx 2 Set.univ) (hgy : MemLpLocOn gy 2 Set.univ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (x : ℂ) (r : ℝ), 0 < r →
      ∃ ρ ∈ Set.Icc r (2 * r),
        ENNReal.ofReal ((Metric.diam (f '' Metric.sphere x ρ)) ^ 2)
          ≤ ENNReal.ofReal C₀ * ∫⁻ z in Metric.closedBall x (2 * r), energyDensity gx gy z := by
  classical
  set C₀ : ℝ := Real.pi / (2 * Real.log 2) with hC₀_def
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC₀_nonneg : 0 ≤ C₀ := by
    rw [hC₀_def]; positivity
  refine ⟨C₀, hC₀_nonneg, ?_⟩
  intro x r hr
  set B : Set ℂ := Metric.closedBall x (2 * r) with hB_def
  have hB_compact : IsCompact B := by rw [hB_def]; exact isCompact_closedBall x (2 * r)
  -- The target energy and its `L²`-pieces.
  set E : ℝ≥0∞ := ∫⁻ z in B, energyDensity gx gy z with hE_def
  -- `gx, gy ∈ L²(B)` (compact ⊆ univ), giving finite `L²` norms and a.e.-strong measurability.
  have hgx_mem : MemLp gx 2 (volume.restrict B) :=
    hgx B (Set.subset_univ _) hB_compact
  have hgy_mem : MemLp gy 2 (volume.restrict B) :=
    hgy B (Set.subset_univ _) hB_compact
  -- ============================================================================================
  -- A universal helper: for any `h : ℂ → ℂ`, `∫⁻_B ‖h‖₊² = (eLpNorm h 2 (volume.restrict B))²`.
  -- ============================================================================================
  have hsq : ∀ h : ℂ → ℂ,
      (∫⁻ z in B, (‖h z‖₊ : ℝ≥0∞) ^ 2)
        = (eLpNorm h 2 (volume.restrict B)) ^ 2 := by
    intro h
    have hbase : (∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂(volume.restrict B))
        = eLpNorm' h 2 (volume.restrict B) ^ (2 : ℝ) :=
      lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num)
    have hlhs : (∫⁻ z, (‖h z‖₊ : ℝ≥0∞) ^ 2 ∂(volume.restrict B))
        = ∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂(volume.restrict B) := by
      refine lintegral_congr (fun z => ?_)
      rw [enorm_eq_nnnorm, ← ENNReal.rpow_natCast (‖h z‖₊ : ℝ≥0∞) 2]; norm_num
    rw [hlhs, hbase, eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num),
      ← ENNReal.rpow_natCast (eLpNorm' h (ENNReal.toReal 2) (volume.restrict B)) 2]
    norm_num
  -- `E` as a sum of squared `L²` norms.
  set Nx : ℝ≥0∞ := eLpNorm gx 2 (volume.restrict B) with hNx_def
  set Ny : ℝ≥0∞ := eLpNorm gy 2 (volume.restrict B) with hNy_def
  have hNx_lt : Nx < ⊤ := hgx_mem.eLpNorm_lt_top
  have hNy_lt : Ny < ⊤ := hgy_mem.eLpNorm_lt_top
  have hE_eq : E = Nx ^ 2 + Ny ^ 2 := by
    rw [hE_def]
    have hsplit : (∫⁻ z in B, energyDensity gx gy z)
        = (∫⁻ z in B, (‖gx z‖₊ : ℝ≥0∞) ^ 2) + ∫⁻ z in B, (‖gy z‖₊ : ℝ≥0∞) ^ 2 := by
      simp only [energyDensity]
      refine lintegral_add_left' ?_ _
      exact (hgx_mem.aestronglyMeasurable.aemeasurable.enorm.pow_const 2).congr
        (by filter_upwards with z using by rw [enorm_eq_nnnorm])
    rw [hsplit, hsq gx, hsq gy, hNx_def, hNy_def]
  -- ============================================================================================
  -- Build a sequence of `C¹` approximations `G n` with `L²`-gradient error `≤ 1/(n+1)`.
  -- ============================================================================================
  have hchoose : ∀ n : ℕ, ∃ g : ℂ → ℂ, ContDiff ℝ 1 g ∧
      (∀ z ∈ B, ‖g z - f z‖ ≤ 1 / (n + 1 : ℝ)) ∧
      (∫⁻ z in B, energyDensity (fun w => (fderiv ℝ g w) 1 - gx w)
          (fun w => (fderiv ℝ g w) Complex.I - gy w) z) ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    have hεpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    obtain ⟨g, hgcd, hgclose, hgen⟩ :=
      exists_smooth_approx_L2grad_local hfcont hwg hgx hgy x (2 * r) hεpos
    exact ⟨g, hgcd, hgclose, hgen⟩
  choose G hG_cd hG_close hG_energy using hchoose
  -- Partial derivatives of `G n`.
  set Px : ℕ → ℂ → ℂ := fun n w => (fderiv ℝ (G n) w) 1 with hPx_def
  set Py : ℕ → ℂ → ℂ := fun n w => (fderiv ℝ (G n) w) Complex.I with hPy_def
  -- Continuity of the partials (since each `G n` is `C¹`).
  have hPx_cont : ∀ n, Continuous (Px n) := by
    intro n
    exact (hG_cd n).continuous_fderiv one_ne_zero |>.clm_apply continuous_const
  have hPy_cont : ∀ n, Continuous (Py n) := by
    intro n
    exact (hG_cd n).continuous_fderiv one_ne_zero |>.clm_apply continuous_const
  -- `L²` norms of the partials and of the gradient errors on `B`.
  set Nxn : ℕ → ℝ≥0∞ := fun n => eLpNorm (Px n) 2 (volume.restrict B) with hNxn_def
  set Nyn : ℕ → ℝ≥0∞ := fun n => eLpNorm (Py n) 2 (volume.restrict B) with hNyn_def
  set Dxn : ℕ → ℝ≥0∞ :=
    fun n => eLpNorm (fun w => Px n w - gx w) 2 (volume.restrict B) with hDxn_def
  set Dyn : ℕ → ℝ≥0∞ :=
    fun n => eLpNorm (fun w => Py n w - gy w) 2 (volume.restrict B) with hDyn_def
  -- The smooth energy on `B`.
  set En : ℕ → ℝ≥0∞ :=
    fun n => ∫⁻ z in B, energyDensity (Px n) (Py n) z with hEn_def
  have hEn_eq : ∀ n, En n = Nxn n ^ 2 + Nyn n ^ 2 := by
    intro n
    simp only [hEn_def]
    have hsplit : (∫⁻ z in B, energyDensity (Px n) (Py n) z)
        = (∫⁻ z in B, (‖Px n z‖₊ : ℝ≥0∞) ^ 2) + ∫⁻ z in B, (‖Py n z‖₊ : ℝ≥0∞) ^ 2 := by
      simp only [energyDensity]
      refine lintegral_add_left' ?_ _
      exact ((hPx_cont n).aemeasurable.enorm.pow_const 2).congr
        (by filter_upwards with z using by rw [enorm_eq_nnnorm])
    rw [hsplit, hsq (Px n), hsq (Py n), hNxn_def, hNyn_def]
  -- The gradient-error energy on `B` bounds each squared error norm.
  have hDxy_bound : ∀ n, Dxn n ^ 2 ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧
      Dyn n ^ 2 ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    have hsplit : (∫⁻ z in B, energyDensity (fun w => Px n w - gx w)
          (fun w => Py n w - gy w) z)
        = Dxn n ^ 2 + Dyn n ^ 2 := by
      simp only [energyDensity, hDxn_def, hDyn_def]
      rw [← hsq (fun w => Px n w - gx w), ← hsq (fun w => Py n w - gy w)]
      refine lintegral_add_left' ?_ _
      exact (((hPx_cont n).aemeasurable.sub
        hgx_mem.aestronglyMeasurable.aemeasurable).enorm.pow_const 2).congr
        (by filter_upwards with z using by simp [enorm_eq_nnnorm])
    have htot : Dxn n ^ 2 + Dyn n ^ 2 ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
      rw [← hsplit]; exact hG_energy n
    exact ⟨le_trans (self_le_add_right _ _) htot, le_trans (self_le_add_left _ _) htot⟩
  -- ============================================================================================
  -- Apply CL-smooth to each `G n` to select a radius `ρ n ∈ [r, 2r]`.
  -- ============================================================================================
  have hCL : ∀ n, ∃ ρ ∈ Set.Icc r (2 * r),
      ENNReal.ofReal ((Metric.diam (G n '' Metric.sphere x ρ)) ^ 2)
        ≤ ENNReal.ofReal C₀ * En n := by
    intro n
    obtain ⟨ρ, hρmem, hρle⟩ := courantLebesgue_smooth (hG_cd n) x hr
    refine ⟨ρ, hρmem, ?_⟩
    change ENNReal.ofReal ((Metric.diam (G n '' Metric.sphere x ρ)) ^ 2)
        ≤ ENNReal.ofReal C₀ * (∫⁻ z in B, energyDensity (Px n) (Py n) z)
    rw [hC₀_def]
    exact hρle
  choose ρ hρ_mem hρ_le using hCL
  -- ============================================================================================
  -- Convergence of the smooth energy: `En n ≤ bound n` and `bound n → E`.
  -- ============================================================================================
  -- The error norms tend to `0`.
  have hofReal_tendsto : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  -- Taking square roots: `a = (a²)^(1/2)`, so `Dxn n → 0` from `Dxn n ² → 0`.
  have hroot : ∀ a : ℝ≥0∞, (a ^ 2) ^ (1 / 2 : ℝ) = a := by
    intro a
    rw [← ENNReal.rpow_natCast a 2, ← ENNReal.rpow_mul]
    norm_num
  have hDxn_zero : Tendsto Dxn atTop (𝓝 0) := by
    have hsq_zero : Tendsto (fun n => Dxn n ^ 2) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hofReal_tendsto
        (fun n => zero_le) (fun n => (hDxy_bound n).1)
    have := hsq_zero.ennrpow_const (1 / 2 : ℝ)
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1 / 2)] at this
    simpa only [hroot] using this
  have hDyn_zero : Tendsto Dyn atTop (𝓝 0) := by
    have hsq_zero : Tendsto (fun n => Dyn n ^ 2) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hofReal_tendsto
        (fun n => zero_le) (fun n => (hDxy_bound n).2)
    have := hsq_zero.ennrpow_const (1 / 2 : ℝ)
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1 / 2)] at this
    simpa only [hroot] using this
  -- ============================================================================================
  -- Triangle inequality: `Nxn n ≤ Nx + Dxn n` and `Nyn n ≤ Ny + Dyn n` (on `volume.restrict B`).
  -- ============================================================================================
  have hone_le : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hNxn_le : ∀ n, Nxn n ≤ Nx + Dxn n := by
    intro n
    have htri := eLpNorm_add_le (μ := volume.restrict B) (p := 2)
      hgx_mem.aestronglyMeasurable
      ((hPx_cont n).aestronglyMeasurable.sub hgx_mem.aestronglyMeasurable) hone_le
    have heq : (gx + (Px n - gx)) = Px n := by funext w; simp
    rw [heq] at htri
    simpa only [hNxn_def, hNx_def, hDxn_def] using! htri
  have hNyn_le : ∀ n, Nyn n ≤ Ny + Dyn n := by
    intro n
    have htri := eLpNorm_add_le (μ := volume.restrict B) (p := 2)
      hgy_mem.aestronglyMeasurable
      ((hPy_cont n).aestronglyMeasurable.sub hgy_mem.aestronglyMeasurable) hone_le
    have heq : (gy + (Py n - gy)) = Py n := by funext w; simp
    rw [heq] at htri
    simpa only [hNyn_def, hNy_def, hDyn_def] using! htri
  -- The dominating bound `bound n := (Nx + Dxn n)² + (Ny + Dyn n)²` satisfies `En n ≤ bound n`
  -- and `bound n → E`.
  set bound : ℕ → ℝ≥0∞ := fun n => (Nx + Dxn n) ^ 2 + (Ny + Dyn n) ^ 2 with hbound_def
  have hEn_le_bound : ∀ n, En n ≤ bound n := by
    intro n
    rw [hEn_eq n, hbound_def]
    exact add_le_add (pow_le_pow_left' (hNxn_le n) 2) (pow_le_pow_left' (hNyn_le n) 2)
  have hbound_tendsto : Tendsto bound atTop (𝓝 E) := by
    have h1 : Tendsto (fun n => Nx + Dxn n) atTop (𝓝 (Nx + 0)) :=
      tendsto_const_nhds.add hDxn_zero
    have h2 : Tendsto (fun n => Ny + Dyn n) atTop (𝓝 (Ny + 0)) :=
      tendsto_const_nhds.add hDyn_zero
    have h1sq : Tendsto (fun n => (Nx + Dxn n) ^ 2) atTop (𝓝 ((Nx + 0) ^ 2)) :=
      (ENNReal.continuous_pow 2).continuousAt.tendsto.comp h1
    have h2sq : Tendsto (fun n => (Ny + Dyn n) ^ 2) atTop (𝓝 ((Ny + 0) ^ 2)) :=
      (ENNReal.continuous_pow 2).continuousAt.tendsto.comp h2
    have hadd : Tendsto bound atTop (𝓝 ((Nx + 0) ^ 2 + (Ny + 0) ^ 2)) := h1sq.add h2sq
    rwa [add_zero, add_zero, ← hE_eq] at hadd
  -- ============================================================================================
  -- One-sided diameter stability under uniform displacement.
  -- ============================================================================================
  have hstable : ∀ (g₁ g₂ : ℂ → ℂ), Continuous g₁ → Continuous g₂ → ∀ S : Set ℂ, IsCompact S →
      ∀ δ : ℝ, 0 ≤ δ → (∀ z ∈ S, ‖g₁ z - g₂ z‖ ≤ δ) →
      Metric.diam (g₁ '' S) ≤ Metric.diam (g₂ '' S) + 2 * δ := by
    intro g₁ g₂ hg₁ hg₂ S hScpt δ hδ hbnd
    have hb₂ : Bornology.IsBounded (g₂ '' S) := (hScpt.image hg₂).isBounded
    refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    rintro u ⟨a, haS, rfl⟩ v ⟨b, hbS, rfl⟩
    have hd : dist (g₁ a) (g₁ b)
        ≤ dist (g₁ a) (g₂ a) + dist (g₂ a) (g₂ b) + dist (g₂ b) (g₁ b) :=
      dist_triangle4 (g₁ a) (g₂ a) (g₂ b) (g₁ b)
    have h1 : dist (g₁ a) (g₂ a) ≤ δ := by rw [dist_eq_norm]; exact hbnd a haS
    have h3 : dist (g₂ b) (g₁ b) ≤ δ := by
      rw [dist_eq_norm, norm_sub_rev]; exact hbnd b hbS
    have h2 : dist (g₂ a) (g₂ b) ≤ Metric.diam (g₂ '' S) :=
      Metric.dist_le_diam_of_mem hb₂ ⟨a, haS, rfl⟩ ⟨b, hbS, rfl⟩
    calc dist (g₁ a) (g₁ b) ≤ δ + Metric.diam (g₂ '' S) + δ := by
            exact le_trans hd (add_le_add (add_le_add h1 h2) h3)
      _ = Metric.diam (g₂ '' S) + 2 * δ := by ring
  -- ============================================================================================
  -- Select a subsequence of radii converging to `ρ* ∈ [r, 2r]`.
  -- ============================================================================================
  obtain ⟨ρstar, hρstar_mem, φ, hφ_mono, hφ_tendsto⟩ :=
    isCompact_Icc.tendsto_subseq hρ_mem
  have hρstar_pos : 0 < ρstar := lt_of_lt_of_le hr hρstar_mem.1
  -- Convergence helpers.
  have hφ_atTop : Tendsto φ atTop atTop := hφ_mono.tendsto_atTop
  have hc_tendsto : Tendsto (fun k => 2 * (1 / (φ k + 1 : ℝ))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hcomp := h0.comp hφ_atTop
    have := hcomp.const_mul (2 : ℝ)
    simpa using this
  -- `diam (f '' sphere x (ρ (φ k))) → diam (f '' sphere x ρ*)`.
  have hb_tendsto :
      Tendsto (fun k => Metric.diam (f '' Metric.sphere x (ρ (φ k)))) atTop
        (𝓝 (Metric.diam (f '' Metric.sphere x ρstar))) := by
    have hwithin : Tendsto (fun k => ρ (φ k)) atTop (𝓝[Set.Ioi 0] ρstar) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hφ_tendsto ?_
      refine Filter.Eventually.of_forall (fun k => ?_)
      exact lt_of_lt_of_le hr (hρ_mem (φ k)).1
    have hcwa := (continuousOn_diam_image_sphere hfcont x).continuousWithinAt
      (Set.mem_Ioi.mpr hρstar_pos)
    exact hcwa.tendsto.comp hwithin
  -- `diam (G (φ k) '' sphere x (ρ (φ k))) → diam (f '' sphere x ρ*)` by squeeze.
  have ha_tendsto :
      Tendsto (fun k => Metric.diam (G (φ k) '' Metric.sphere x (ρ (φ k)))) atTop
        (𝓝 (Metric.diam (f '' Metric.sphere x ρstar))) := by
    -- lower and upper bracket both tend to the limit.
    have hlow : Tendsto (fun k => Metric.diam (f '' Metric.sphere x (ρ (φ k)))
        - 2 * (1 / (φ k + 1 : ℝ))) atTop (𝓝 (Metric.diam (f '' Metric.sphere x ρstar))) := by
      have := hb_tendsto.sub hc_tendsto
      simpa using this
    have hupp : Tendsto (fun k => Metric.diam (f '' Metric.sphere x (ρ (φ k)))
        + 2 * (1 / (φ k + 1 : ℝ))) atTop (𝓝 (Metric.diam (f '' Metric.sphere x ρstar))) := by
      have := hb_tendsto.add hc_tendsto
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp ?_ ?_
    · -- lower bound: `diam(f''S) - 2δ ≤ diam(G''S)`
      intro k
      have hsph_cpt : IsCompact (Metric.sphere x (ρ (φ k))) := isCompact_sphere x (ρ (φ k))
      have hbnd : ∀ z ∈ Metric.sphere x (ρ (φ k)),
          ‖f z - G (φ k) z‖ ≤ 1 / (φ k + 1 : ℝ) := by
        intro z hz
        have hzB : z ∈ B := by
          rw [hB_def]
          have : ρ (φ k) ≤ 2 * r := (hρ_mem (φ k)).2
          rw [Metric.mem_sphere] at hz
          rw [Metric.mem_closedBall, hz]; exact this
        rw [norm_sub_rev]; exact hG_close (φ k) z hzB
      have hst := hstable f (G (φ k)) hfcont (hG_cd (φ k)).continuous
        (Metric.sphere x (ρ (φ k))) hsph_cpt (1 / (φ k + 1 : ℝ)) (by positivity) hbnd
      have : Metric.diam (f '' Metric.sphere x (ρ (φ k)))
          ≤ Metric.diam (G (φ k) '' Metric.sphere x (ρ (φ k))) + 2 * (1 / (φ k + 1 : ℝ)) := by
        simpa using hst
      linarith
    · -- upper bound: `diam(G''S) ≤ diam(f''S) + 2δ`
      intro k
      have hsph_cpt : IsCompact (Metric.sphere x (ρ (φ k))) := isCompact_sphere x (ρ (φ k))
      have hbnd : ∀ z ∈ Metric.sphere x (ρ (φ k)),
          ‖G (φ k) z - f z‖ ≤ 1 / (φ k + 1 : ℝ) := by
        intro z hz
        have hzB : z ∈ B := by
          rw [hB_def]
          have : ρ (φ k) ≤ 2 * r := (hρ_mem (φ k)).2
          rw [Metric.mem_sphere] at hz
          rw [Metric.mem_closedBall, hz]; exact this
        exact hG_close (φ k) z hzB
      have hst := hstable (G (φ k)) f (hG_cd (φ k)).continuous hfcont
        (Metric.sphere x (ρ (φ k))) hsph_cpt (1 / (φ k + 1 : ℝ)) (by positivity) hbnd
      simpa using hst
  -- ============================================================================================
  -- Pass to the limit in `ℝ≥0∞`.
  -- ============================================================================================
  -- LHS along the subsequence converges to `ofReal (diam (f '' sphere x ρ*)²)`.
  have hLHS_tendsto :
      Tendsto (fun k => ENNReal.ofReal
        ((Metric.diam (G (φ k) '' Metric.sphere x (ρ (φ k)))) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((Metric.diam (f '' Metric.sphere x ρstar)) ^ 2))) := by
    have hsq_t :
        Tendsto (fun k => (Metric.diam (G (φ k) '' Metric.sphere x (ρ (φ k)))) ^ 2) atTop
          (𝓝 ((Metric.diam (f '' Metric.sphere x ρstar)) ^ 2)) :=
      (continuous_pow 2).continuousAt.tendsto.comp ha_tendsto
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto).comp hsq_t
  -- RHS along the subsequence is `≤ ofReal C₀ * bound (φ k)`, which converges to `ofReal C₀ * E`.
  have hRHS_tendsto :
      Tendsto (fun k => ENNReal.ofReal C₀ * bound (φ k)) atTop
        (𝓝 (ENNReal.ofReal C₀ * E)) := by
    have hbsub : Tendsto (fun k => bound (φ k)) atTop (𝓝 E) := hbound_tendsto.comp hφ_atTop
    exact ENNReal.Tendsto.const_mul hbsub (Or.inr ENNReal.ofReal_ne_top)
  -- The pointwise inequality along the subsequence.
  have hpt_le : ∀ k,
      ENNReal.ofReal ((Metric.diam (G (φ k) '' Metric.sphere x (ρ (φ k)))) ^ 2)
        ≤ ENNReal.ofReal C₀ * bound (φ k) := by
    intro k
    refine le_trans (hρ_le (φ k)) ?_
    exact mul_le_mul' (le_refl _) (hEn_le_bound (φ k))
  -- Conclude.
  refine ⟨ρstar, hρstar_mem, ?_⟩
  have hfinal :
      ENNReal.ofReal ((Metric.diam (f '' Metric.sphere x ρstar)) ^ 2)
        ≤ ENNReal.ofReal C₀ * E :=
    le_of_tendsto_of_tendsto' hLHS_tendsto hRHS_tendsto hpt_le
  exact hfinal

/-- **Finite metric derivative a.e. (ASM) — assembly of CL + MON + ED.**

A homeomorphism `f` with weak gradient `(gx, gy) ∈ L²_loc` has a finite metric upper derivative at
almost every point — verbatim the hypothesis the proven Stepanov engine
`ae_differentiableAt_of_ae_limsup_slope_lt_top` consumes.

Proof (per a.e. good `x`, an energy Lebesgue point from `ED`): for any small `s`, `CL` with `r = s`
gives `ρ ∈ [s, 2s]` with `diam (f '' sphere x ρ)² ≤ C₀·∫_{B(x,2s)} φ`; `MON` upgrades this to
`diam (f '' closedBall x ρ)`; since `closedBall x s ⊆ closedBall x ρ`, monotonicity of diameter and
`ED`'s `∫_{B(x,2s)} φ ≤ A·s²` give `diam (f '' closedBall x s) ≤ √(C₀·A)·s`; finally every `y` near
`x` lies in `closedBall x ‖y − x‖`, so
`‖f y − f x‖ ≤ diam (f '' closedBall x ‖y−x‖) ≤ √(C₀·A)·‖y − x‖` — the finite metric upper
derivative, obtained from `CL + MON + ED` (no conformal-modulus roundness estimate). -/
theorem ae_finiteMetricDerivative_of_W12loc_homeomorph {f gx gy : ℂ → ℂ}
    (hhomeo : IsHomeomorph f) (hwg : HasWeakGradient gx gy f Set.univ)
    (hgx : MemLpLocOn gx 2 Set.univ) (hgy : MemLpLocOn gy 2 Set.univ) :
    ∀ᵐ x : ℂ, ∃ C : ℝ, ∀ᶠ y in 𝓝 x, ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  classical
  have hfcont : Continuous f := hhomeo.continuous
  -- Courant–Lebesgue: a uniform constant `C₀` with a small-energy circle at every scale.
  obtain ⟨C₀, hC₀, hCL⟩ := courantLebesgue_smallEnergyCircle hfcont hwg hgx hgy
  -- Work at almost every energy Lebesgue point `x`.
  filter_upwards [ae_energyDensity_lebesgue_point hgx hgy] with x hx
  obtain ⟨A, hA, hED⟩ := hx
  -- The Stepanov constant.
  refine ⟨Real.sqrt (C₀ * A), ?_⟩
  set C : ℝ := Real.sqrt (C₀ * A) with hC_def
  have hC_nonneg : 0 ≤ C := Real.sqrt_nonneg _
  -- A `diam` bound at every small radius `s`.
  have hradius : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Metric.diam (f '' Metric.closedBall x s) ≤ C * s := by
    filter_upwards [hED, self_mem_nhdsWithin] with s hs hspos
    have hspos' : (0 : ℝ) < s := hspos
    -- Courant–Lebesgue at radius `r = s`: a sphere radius `ρ ∈ [s, 2s]` with small image diameter.
    obtain ⟨ρ, hρmem, hρdiam⟩ := hCL x s hspos'
    have hρge : s ≤ ρ := hρmem.1
    have hρpos : 0 < ρ := lt_of_lt_of_le hspos' hρge
    -- Combine CL with ED to get `ofReal((diam sphere)²) ≤ ofReal (C₀·A·s²)`.
    have hchain_ennreal : ENNReal.ofReal ((Metric.diam (f '' Metric.sphere x ρ)) ^ 2)
        ≤ ENNReal.ofReal (C₀ * A * s ^ 2) := by
      calc ENNReal.ofReal ((Metric.diam (f '' Metric.sphere x ρ)) ^ 2)
          ≤ ENNReal.ofReal C₀ * ∫⁻ z in Metric.closedBall x (2 * s), energyDensity gx gy z :=
            hρdiam
        _ ≤ ENNReal.ofReal C₀ * ENNReal.ofReal (A * s ^ 2) := by gcongr
        _ = ENNReal.ofReal (C₀ * (A * s ^ 2)) := (ENNReal.ofReal_mul hC₀).symm
        _ = ENNReal.ofReal (C₀ * A * s ^ 2) := by rw [mul_assoc]
    -- Pass to real numbers (both sides nonneg).
    have hsphere_nonneg : 0 ≤ Metric.diam (f '' Metric.sphere x ρ) := Metric.diam_nonneg
    have hCAs_nonneg : 0 ≤ C₀ * A * s ^ 2 := by positivity
    have hchain_real : (Metric.diam (f '' Metric.sphere x ρ)) ^ 2 ≤ C₀ * A * s ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff hCAs_nonneg).mp hchain_ennreal
    -- Take square roots: `diam (sphere) ≤ √(C₀·A)·s = C·s`.
    have hCA_nonneg : 0 ≤ C₀ * A := by positivity
    have hsphere_le : Metric.diam (f '' Metric.sphere x ρ) ≤ C * s := by
      have hsqrt : Metric.diam (f '' Metric.sphere x ρ)
          ≤ Real.sqrt (C₀ * A * s ^ 2) := by
        calc Metric.diam (f '' Metric.sphere x ρ)
            = Real.sqrt ((Metric.diam (f '' Metric.sphere x ρ)) ^ 2) := by
              rw [Real.sqrt_sq hsphere_nonneg]
          _ ≤ Real.sqrt (C₀ * A * s ^ 2) := Real.sqrt_le_sqrt hchain_real
      calc Metric.diam (f '' Metric.sphere x ρ)
          ≤ Real.sqrt (C₀ * A * s ^ 2) := hsqrt
        _ = C * s := by
            rw [show C₀ * A * s ^ 2 = (C₀ * A) * s ^ 2 by ring, Real.sqrt_mul hCA_nonneg,
              Real.sqrt_sq hspos'.le, hC_def]
    -- MON: `diam (f '' closedBall x ρ) ≤ diam (f '' sphere x ρ)`.
    have hMON : Metric.diam (f '' Metric.closedBall x ρ)
        ≤ Metric.diam (f '' Metric.sphere x ρ) :=
      diam_image_closedBall_le_diam_image_sphere hhomeo x hρpos
    -- Monotonicity of diam in the radius: `closedBall x s ⊆ closedBall x ρ`.
    have hsub : Metric.closedBall x s ⊆ Metric.closedBall x ρ :=
      Metric.closedBall_subset_closedBall hρge
    have hball_bdd : Bornology.IsBounded (f '' Metric.closedBall x ρ) :=
      ((isCompact_closedBall x ρ).image hfcont).isBounded
    have hmono : Metric.diam (f '' Metric.closedBall x s)
        ≤ Metric.diam (f '' Metric.closedBall x ρ) :=
      Metric.diam_mono (Set.image_mono hsub) hball_bdd
    -- Assemble: `diam (f '' closedBall x s) ≤ C · s`.
    calc Metric.diam (f '' Metric.closedBall x s)
        ≤ Metric.diam (f '' Metric.closedBall x ρ) := hmono
      _ ≤ Metric.diam (f '' Metric.sphere x ρ) := hMON
      _ ≤ C * s := hsphere_le
  -- Translate the radius bound to the pointwise bound near `x`.
  rw [eventually_nhdsWithin_iff] at hradius
  rw [Metric.eventually_nhds_iff] at hradius ⊢
  obtain ⟨ε, hεpos, hε⟩ := hradius
  refine ⟨ε, hεpos, ?_⟩
  intro y hy
  rcases eq_or_ne y x with rfl | hyx
  · simp
  · -- `s = dist y x = ‖y - x‖ ∈ (0, ε)`.
    have hdist_pos : 0 < dist y x := dist_pos.2 hyx
    have hdist_lt : dist y x < ε := hy
    have hdist0 : dist (dist y x) 0 < ε := by
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
    have hbound := hε hdist0 (Set.mem_Ioi.2 hdist_pos)
    -- `y, x ∈ closedBall x (dist y x)`.
    have hymem : y ∈ Metric.closedBall x (dist y x) := Metric.mem_closedBall.2 le_rfl
    have hxmem : x ∈ Metric.closedBall x (dist y x) := by
      rw [Metric.mem_closedBall, dist_self]; exact dist_nonneg
    have hdiam_bd : dist (f y) (f x) ≤ Metric.diam (f '' Metric.closedBall x (dist y x)) :=
      Metric.dist_le_diam_of_mem ((isCompact_closedBall x (dist y x)).image hfcont).isBounded
        (Set.mem_image_of_mem f hymem) (Set.mem_image_of_mem f hxmem)
    calc ‖f y - f x‖ = dist (f y) (f x) := (dist_eq_norm _ _).symm
      _ ≤ Metric.diam (f '' Metric.closedBall x (dist y x)) := hdiam_bd
      _ ≤ C * dist y x := hbound
      _ = C * ‖y - x‖ := by rw [dist_eq_norm]

/-- **Gehring–Lehto: roundness-free a.e. differentiability.**

A homeomorphism `f : ℂ → ℂ` with weak gradient `(gx, gy) ∈ L²_loc` (i.e. `f ∈ W^{1,2}_loc`) is
differentiable almost everywhere. This is the pivot: it supplies the a.e.-differentiability of a
geometric quasiconformal map **without** the conformal-modulus roundness estimate, by composing the
finite-metric-derivative assembly `ASM` with the proven Stepanov engine. -/
theorem ae_differentiableAt_of_W12loc_homeomorph {f gx gy : ℂ → ℂ}
    (hhomeo : IsHomeomorph f) (hwg : HasWeakGradient gx gy f Set.univ)
    (hgx : MemLpLocOn gx 2 Set.univ) (hgy : MemLpLocOn gy 2 Set.univ) :
    ∀ᵐ x : ℂ, DifferentiableAt ℝ f x :=
  NoWanderingDomains.Stepanov.ae_differentiableAt_of_ae_limsup_slope_lt_top
    (ae_finiteMetricDerivative_of_W12loc_homeomorph hhomeo hwg hgx hgy)

end NoWanderingDomains.GehringLehto
