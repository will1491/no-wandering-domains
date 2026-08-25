/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Sobolev.WeakDeriv
import NoWanderingDomains.QC.LengthArea.Mollification
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Weyl's lemma on an open set

The local (open-set) form of Weyl's lemma: a continuous function on an open
set `V ⊆ ℂ` whose weak `∂̄`-derivative vanishes on `V` is holomorphic on `V`.

Two interchangeable formulations are provided, matching the two ways the rest
of the development produces the weak hypothesis:

* `weyl_lemma_on` — via explicit weak-gradient witnesses `gx`, `gy` on `V`
  (the shape produced by the Cauchy-transform calculus, e.g.
  `hasWeakGradient_cauchyTransform`), with the Wirtinger combination
  `gx + I·gy` vanishing almost everywhere on `V`;
* `weyl_lemma_on_of_test` — via the distributional formulation: the
  integral of `f` against `∂̄φ` vanishes for every smooth compactly
  supported complex test function `φ` with support in `V`.

The proof route (mollification) is the one inlined for `V = univ` in
`weyl_lemma` (`QC/Calculus/Weyl.lean`): convolve `f` with a shrinking bump
family; each mollification is smooth with vanishing `∂̄` on a shrunken set,
hence holomorphic there; the mollifications converge locally uniformly to `f`
on compact subsets of `V`, so `f` is holomorphic on `V` by Weierstrass
convergence. The only new ingredient relative to the global case is the
shrinking: mollification at scale `ε` is controlled only at points whose
`ε`-neighborhood lies in `V`, and `V` is exhausted by such points.
-/

open MeasureTheory Complex
open scoped ContDiff

namespace NoWanderingDomains

/-- **Weyl's lemma on an open set, weak-gradient form.** If `f` is continuous
on an open set `V ⊆ ℂ`, has weak partial derivatives `gx` (direction `1`) and
`gy` (direction `I`) on `V` that are locally integrable on `V`, and the weak
`∂̄`-combination `gx + I·gy` vanishes almost everywhere on `V`, then `f` is
holomorphic on `V`. -/
theorem weyl_lemma_on {V : Set ℂ} {f gx gy : ℂ → ℂ} (hV : IsOpen V)
    (hf : ContinuousOn f V)
    (hgrad : HasWeakGradient gx gy f V)
    (hgx : LocallyIntegrableOn gx V)
    (hgy : LocallyIntegrableOn gy V)
    (hcomb : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ V → gx z + Complex.I * gy z = 0) :
    DifferentiableOn ℂ f V := by
  classical
  intro z₀ hz₀
  -- ===== A ball around `z₀` inside `V`, and the working radius `r`. =====
  obtain ⟨R, hR0, hRV⟩ := Metric.isOpen_iff.mp hV z₀ hz₀
  set r : ℝ := R / 8 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  -- ===== Smooth cutoff `χ`: `1` on `closedBall z₀ 5r`, support in `closedBall z₀ 6r`. =====
  set χ : ContDiffBump z₀ :=
    { rIn := 5 * r, rOut := 6 * r,
      rIn_pos := by linarith,
      rIn_lt_rOut := by linarith } with hχdef
  have hrIn : χ.rIn = 5 * r := by rw [hχdef]
  have hrOut : χ.rOut = 6 * r := by rw [hχdef]
  have hcbV : Metric.closedBall z₀ (6 * r) ⊆ V := by
    intro w hw
    apply hRV
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    have h68 : 6 * r < R := by rw [hrdef]; linarith
    linarith
  have hballV : Metric.ball z₀ (5 * r) ⊆ V := by
    intro w hw
    apply hRV
    rw [Metric.mem_ball] at hw ⊢
    have h58 : 5 * r < R := by rw [hrdef]; linarith
    linarith
  -- ===== The globally continuous compactly supported localization `F` of `f`. =====
  set F : ℂ → ℂ := fun w => if w ∈ V then ((χ w : ℝ) : ℂ) * f w else 0 with hFdef
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro w
    by_cases hw : w ∈ V
    · have h1 : ContinuousOn (fun u => ((χ u : ℝ) : ℂ) * f u) V :=
        (Complex.continuous_ofReal.comp χ.continuous).continuousOn.mul hf
      refine (h1.continuousAt (hV.mem_nhds hw)).congr ?_
      filter_upwards [hV.mem_nhds hw] with u hu
      rw [hFdef]
      simp [hu]
    · have hwn : w ∉ tsupport (χ : ℂ → ℝ) := by
        rw [χ.tsupport_eq, hrOut]
        intro hmem
        exact hw (hcbV hmem)
      have hnhds : (tsupport (χ : ℂ → ℝ))ᶜ ∈ nhds w :=
        (isClosed_tsupport _).isOpen_compl.mem_nhds hwn
      refine ContinuousAt.congr (f := fun _ => (0 : ℂ)) continuousAt_const ?_
      filter_upwards [hnhds] with u hu
      have hχu : χ u = 0 := image_eq_zero_of_notMem_tsupport hu
      rw [hFdef]
      by_cases huV : u ∈ V
      · simp [huV, hχu]
      · simp [huV]
  have hFf : ∀ u ∈ Metric.ball z₀ (5 * r), F u = f u := by
    intro u hu
    have huV : u ∈ V := hballV hu
    have hχ1 : χ u = 1 := χ.one_of_mem_closedBall
      (show u ∈ Metric.closedBall z₀ χ.rIn by
        rw [hrIn]; exact Metric.ball_subset_closedBall hu)
    rw [hFdef]
    simp [huV, hχ1]
  have hFsupp : HasCompactSupport F := by
    refine HasCompactSupport.intro (isCompact_closedBall z₀ (6 * r)) (fun x hx => ?_)
    have hxn : x ∉ tsupport (χ : ℂ → ℝ) := by
      rw [χ.tsupport_eq, hrOut]
      exact hx
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hxn
    rw [hFdef]
    by_cases hxV : x ∈ V
    · simp [hxV, hχx]
    · simp [hxV]
  have hFloc : MeasureTheory.LocallyIntegrable F := hFcont.locallyIntegrable
  -- ===== Mollifier sequence with `rOut ≤ r` and `rOut → 0`. =====
  set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  set φB : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    { rIn := r / (n + 2), rOut := 2 * r / (n + 2),
      rIn_pos := by positivity,
      rIn_lt_rOut := by
        rw [div_lt_div_iff_of_pos_right (by positivity)]; linarith } with hφBdef
  have hφrout : Filter.Tendsto (fun n => (φB n).rOut) Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun n : ℕ => 2 * r / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [hφBdef] using h
  have hφle : ∀ n, (φB n).rOut ≤ r := by
    intro n
    simp only [hφBdef]
    rw [div_le_iff₀ (by positivity)]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  set ρ : ℕ → ℂ → ℝ := fun n => (φB n).normed MeasureTheory.volume with hρdef
  set fn : ℕ → ℂ → ℂ := fun n =>
    MeasureTheory.convolution (ρ n) F L MeasureTheory.volume with hfndef
  have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
    (φB n).contDiff_normed (n := ⊤)
  have hρsupp : ∀ n, HasCompactSupport (ρ n) := fun n => (φB n).hasCompactSupport_normed
  have hρ_one : ∀ n, ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
    (hρsm n).of_le (by exact_mod_cast le_top)
  have hρ_diff : ∀ n, Differentiable ℝ (ρ n) := fun n =>
    (hρ_one n).differentiable (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
  have hdρsupp : ∀ n, HasCompactSupport (fderiv ℝ (ρ n)) := fun n => (hρsupp n).fderiv ℝ
  have hdρcont : ∀ n, Continuous (fderiv ℝ (ρ n)) := fun n =>
    (hρ_one n).continuous_fderiv (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
  -- ===== Directional derivatives of the mollifications, as integrals against `F`. =====
  have hstep : ∀ (n : ℕ) (z v : ℂ), (fderiv ℝ (fn n) z) v
      = ∫ u, ((fderiv ℝ (ρ n) (z - u)) v) • F u := by
    intro n z v
    have hderiv : HasFDerivAt (fn n)
        (MeasureTheory.convolution (fderiv ℝ (ρ n)) F (L.precompL ℂ)
          MeasureTheory.volume z) z :=
      HasCompactSupport.hasFDerivAt_convolution_left L (hρsupp n) (hρ_one n) hFloc z
    rw [hderiv.fderiv]
    have hconvex : MeasureTheory.ConvolutionExistsAt (fderiv ℝ (ρ n)) F z (L.precompL ℂ)
        MeasureTheory.volume :=
      ((hdρsupp n).convolutionExists_left (L.precompL ℂ) (hdρcont n) hFloc) z
    rw [MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply hconvex.integrable]
    simp only [ContinuousLinearMap.precompL_apply, hLdef, ContinuousLinearMap.lsmul_apply]
    have hself := MeasureTheory.integral_sub_left_eq_self
      (fun t => ((fderiv ℝ (ρ n) t) v) • F (z - t)) MeasureTheory.volume z
    simp only [sub_sub_cancel] at hself
    exact hself.symm
  -- ===== Geometry: the mollification zone around points of `ball z₀ 4r`. =====
  have hcball : ∀ z ∈ Metric.ball z₀ (4 * r), ∀ n : ℕ,
      Metric.closedBall z ((φB n).rOut) ⊆ Metric.ball z₀ (5 * r) := by
    intro z hz n u hu
    rw [Metric.mem_ball] at hz ⊢
    rw [Metric.mem_closedBall] at hu
    have h1 : dist u z ≤ r := hu.trans (hφle n)
    calc dist u z₀ ≤ dist u z + dist z z₀ := dist_triangle _ _ _
      _ < 5 * r := by linarith
  -- ===== Key step: `∂̄ (fn n) = 0` on `ball z₀ 4r`, via the weak-gradient identity. =====
  have hkey : ∀ (n : ℕ), ∀ z ∈ Metric.ball z₀ (4 * r), dzbar (fn n) z = 0 := by
    intro n z hz
    -- The translated-bump real test function.
    set φt : ℂ → ℝ := fun u => ρ n (z - u) with hφtdef
    have hφt_smooth : ContDiff ℝ ∞ φt := (hρsm n).comp (contDiff_const.sub contDiff_id)
    have hφt_supp : HasCompactSupport φt :=
      (hρsupp n).comp_homeomorph (Homeomorph.subLeft z)
    have hφt_tsub : tsupport φt ⊆ Metric.closedBall z ((φB n).rOut) := by
      refine closure_minimal ?_ Metric.isClosed_closedBall
      intro u hu
      rw [Function.mem_support] at hu
      have h2 : z - u ∈ Function.support (ρ n) := Function.mem_support.mpr hu
      simp only [hρdef] at h2
      rw [(φB n).support_normed_eq] at h2
      rw [Metric.mem_ball, dist_zero_right] at h2
      rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
      exact h2.le
    have hφt_tsuppV : tsupport φt ⊆ V :=
      hφt_tsub.trans ((hcball z hz n).trans hballV)
    -- Chain rule for the translated bump.
    have hφt_fderiv : ∀ (u v : ℂ), (fderiv ℝ φt u) v = -((fderiv ℝ (ρ n) (z - u)) v) := by
      intro u v
      have hsub : HasFDerivAt (fun w : ℂ => z - w) (-ContinuousLinearMap.id ℝ ℂ) u := by
        simpa using (hasFDerivAt_id u).const_sub z
      have hcomp : HasFDerivAt φt
          ((fderiv ℝ (ρ n) (z - u)).comp (-ContinuousLinearMap.id ℝ ℂ)) u :=
        (hρ_diff n (z - u)).hasFDerivAt.comp u hsub
      rw [hcomp.fderiv]
      simp only [ContinuousLinearMap.comp_apply, neg_apply,
        ContinuousLinearMap.id_apply, map_neg]
    -- Under the derivative weight, `F` can be swapped for `f`.
    have hswap : ∀ (v u : ℂ),
        ((fderiv ℝ (ρ n) (z - u)) v) • F u = ((fderiv ℝ (ρ n) (z - u)) v) • f u := by
      intro v u
      by_cases hu : u ∈ Metric.closedBall z ((φB n).rOut)
      · rw [hFf u (hcball z hz n hu)]
      · have h1 : z - u ∉ tsupport (ρ n) := by
          simp only [hρdef]
          rw [(φB n).tsupport_normed_eq]
          intro hmem
          apply hu
          rw [Metric.mem_closedBall] at hmem ⊢
          rw [dist_zero_right] at hmem
          rw [dist_comm, dist_eq_norm]
          exact hmem
        have h2 : fderiv ℝ (ρ n) (z - u) = 0 := by
          by_contra h
          exact h1 (support_fderiv_subset ℝ (Function.mem_support.mpr h))
        rw [h2]
        simp
    -- The weak-derivative identity computes the directional derivatives of `fn n`.
    have hdir : ∀ (v : ℂ) (gv : ℂ → ℂ), HasWeakDirDeriv v gv f V →
        (fderiv ℝ (fn n) z) v = ∫ u, φt u • gv u := by
      intro v gv hw
      have e1 : ∫ u, ((fderiv ℝ (ρ n) (z - u)) v) • F u
          = ∫ u, ((fderiv ℝ (ρ n) (z - u)) v) • f u :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (hswap v))
      have e2 : ∫ u, ((fderiv ℝ (ρ n) (z - u)) v) • f u
          = - ∫ u, ((fderiv ℝ φt u) v) • f u := by
        rw [← MeasureTheory.integral_neg]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        change ((fderiv ℝ (ρ n) (z - u)) v) • f u = -(((fderiv ℝ φt u) v) • f u)
        rw [hφt_fderiv u v, Complex.real_smul, Complex.real_smul]
        push_cast
        ring
      have e3 := hw φt hφt_smooth hφt_supp hφt_tsuppV
      rw [hstep n z v, e1, e2, e3, neg_neg]
    obtain ⟨hwx, hwy⟩ := hgrad
    have hdx := hdir 1 gx hwx
    have hdy := hdir Complex.I gy hwy
    -- Integrability of the two weak-pairing integrands.
    have hint : ∀ {g : ℂ → ℂ}, LocallyIntegrableOn g V →
        Integrable (fun u => φt u • g u) volume := by
      intro g hg
      have hK : IsCompact (tsupport φt) := hφt_supp
      have hgon : IntegrableOn g (tsupport φt) volume :=
        hg.integrableOn_compact_subset hφt_tsuppV hK
      have hon : IntegrableOn (fun u => φt u • g u) (tsupport φt) volume :=
        hgon.continuousOn_smul hφt_smooth.continuous.continuousOn hK
      have hsupp3 : Function.support (fun u => φt u • g u) ⊆ tsupport φt := by
        intro u hu
        apply subset_tsupport φt
        simp only [Function.mem_support] at hu ⊢
        intro h0
        apply hu
        simp [h0]
      exact (MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp3).mp hon
    have hIx : Integrable (fun u => φt u • gx u) volume := hint hgx
    have hIy : Integrable (fun u => φt u • gy u) volume := hint hgy
    have hIy' : Integrable (fun u => Complex.I * (φt u • gy u)) volume := hIy.const_mul _
    have hIint : Complex.I * ∫ u, φt u • gy u = ∫ u, Complex.I * (φt u • gy u) :=
      (MeasureTheory.integral_const_mul Complex.I (fun u => φt u • gy u)).symm
    -- The combined integrand vanishes a.e. thanks to `hcomb`.
    have hzero : ∫ u, (φt u • gx u + Complex.I * (φt u • gy u)) = 0 := by
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      filter_upwards [hcomb] with u hu
      by_cases huT : u ∈ tsupport φt
      · have h5 := hu (hφt_tsuppV huT)
        change φt u • gx u + Complex.I * (φt u • gy u) = 0
        rw [Complex.real_smul, Complex.real_smul]
        calc ((φt u : ℝ) : ℂ) * gx u + Complex.I * (((φt u : ℝ) : ℂ) * gy u)
            = ((φt u : ℝ) : ℂ) * (gx u + Complex.I * gy u) := by ring
          _ = 0 := by rw [h5, mul_zero]
      · have h6 : φt u = 0 := image_eq_zero_of_notMem_tsupport huT
        change φt u • gx u + Complex.I * (φt u • gy u) = 0
        rw [h6]
        simp
    have hEq2 : (∫ u, φt u • gx u) + Complex.I * ∫ u, φt u • gy u = 0 := by
      rw [hIint, ← MeasureTheory.integral_add hIx hIy']
      exact hzero
    rw [dzbar, hdx, hdy, hEq2, mul_zero]
  -- ===== Each mollification is holomorphic on `ball z₀ 4r`. =====
  have hfn_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fn n) := fun n =>
    (hρsupp n).contDiff_convolution_left L (hρsm n) hFloc
  have hfn_holo : ∀ n, DifferentiableOn ℂ (fn n) (Metric.ball z₀ (4 * r)) := by
    intro n
    refine (differentiableOn_iff_dzbar_eq_zero Metric.isOpen_ball ?_).mpr
      (fun z hz => hkey n z hz)
    exact fun z _ =>
      (((hfn_smooth n).differentiable (by simp)).differentiableAt).differentiableWithinAt
  -- ===== `fn → F` locally uniformly. =====
  have hTLUg : TendstoLocallyUniformly (fun n => fn n) F Filter.atTop := by
    refine tendstoLocallyUniformly_of_forall_exists_nhds (fun x => ?_)
    refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
    have hUC : UniformContinuousOn F (Metric.closedBall x 2) :=
      (isCompact_closedBall x 2).uniformContinuousOn_of_continuous hFcont.continuousOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by positivity
    obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) hε2
    have hev : ∀ᶠ n in Filter.atTop, (φB n).rOut < min δ 1 := by
      have := hφrout.eventually (eventually_lt_nhds (show (0 : ℝ) < min δ 1 by positivity))
      filter_upwards [this] with n hn using hn
    filter_upwards [hev] with n hn z hz
    have hrout_le_one : (φB n).rOut ≤ 1 := (lt_of_lt_of_le hn (min_le_right δ 1)).le
    have hrout_le_δ : (φB n).rOut ≤ δ := (lt_of_lt_of_le hn (min_le_left δ 1)).le
    have hsupp2 : Function.support (ρ n) ⊆ Metric.ball (0 : ℂ) (φB n).rOut := by
      simp only [hρdef]
      rw [(φB n).support_normed_eq]
    have hnf : ∀ y, 0 ≤ ρ n y := fun y => (φB n).nonneg_normed y
    have hintf : ∫ y, ρ n y ∂MeasureTheory.volume = 1 := (φB n).integral_normed
    have hclose : ∀ y ∈ Metric.ball z ((φB n).rOut), dist (F y) (F z) ≤ ε / 2 := by
      intro y hy
      have hzmem : z ∈ Metric.closedBall x 2 :=
        Metric.closedBall_subset_closedBall (by norm_num) hz
      rw [Metric.mem_ball] at hy
      have hymem : y ∈ Metric.closedBall x 2 := by
        rw [Metric.mem_closedBall] at hz ⊢
        calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
          _ ≤ (φB n).rOut + 1 := by gcongr
          _ ≤ 1 + 1 := by gcongr
          _ = 2 := by norm_num
      exact (hδ y hymem z hzmem (hy.trans_le hrout_le_δ)).le
    calc dist (F z) (fn n z)
        = dist (fn n z) (F z) := dist_comm _ _
      _ ≤ ε / 2 := dist_convolution_le hε2.le hsupp2 hnf hintf
            hFcont.aestronglyMeasurable hclose
      _ < ε := by linarith
  -- ===== Conclusion at `z₀`. =====
  have hTLU : TendstoLocallyUniformlyOn (fun n => fn n) F Filter.atTop
      (Metric.ball z₀ (4 * r)) := hTLUg.tendstoLocallyUniformlyOn
  have hFdiff : DifferentiableOn ℂ F (Metric.ball z₀ (4 * r)) :=
    hTLU.differentiableOn (Filter.Eventually.of_forall hfn_holo) Metric.isOpen_ball
  have hfdiff : DifferentiableOn ℂ f (Metric.ball z₀ (4 * r)) := by
    refine hFdiff.congr (fun u hu => ?_)
    exact (hFf u (Metric.ball_subset_ball (by linarith) hu)).symm
  have hz₀mem : z₀ ∈ Metric.ball z₀ (4 * r) := Metric.mem_ball_self (by linarith)
  exact ((hfdiff z₀ hz₀mem).differentiableAt
    (Metric.isOpen_ball.mem_nhds hz₀mem)).differentiableWithinAt

/-- **Weyl's lemma on an open set, test-function form.** If `f` is continuous
on an open set `V ⊆ ℂ` and the distributional `∂̄`-derivative of `f` vanishes
on `V` — the integral of `f` against `∂̄φ` is zero for every smooth compactly
supported complex test function `φ` with support in `V` — then `f` is
holomorphic on `V`. -/
theorem weyl_lemma_on_of_test {V : Set ℂ} {f : ℂ → ℂ} (hV : IsOpen V)
    (hf : ContinuousOn f V)
    (htest : ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ V → ∫ z, dzbar φ z * f z = 0) :
    DifferentiableOn ℂ f V := by
  classical
  intro z₀ hz₀
  -- ===== A ball around `z₀` inside `V`, and the working radius `r`. =====
  obtain ⟨R, hR0, hRV⟩ := Metric.isOpen_iff.mp hV z₀ hz₀
  set r : ℝ := R / 8 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  -- ===== Smooth cutoff `χ`: `1` on `closedBall z₀ 5r`, support in `closedBall z₀ 6r`. =====
  set χ : ContDiffBump z₀ :=
    { rIn := 5 * r, rOut := 6 * r,
      rIn_pos := by linarith,
      rIn_lt_rOut := by linarith } with hχdef
  have hrIn : χ.rIn = 5 * r := by rw [hχdef]
  have hrOut : χ.rOut = 6 * r := by rw [hχdef]
  have hcbV : Metric.closedBall z₀ (6 * r) ⊆ V := by
    intro w hw
    apply hRV
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    have h68 : 6 * r < R := by rw [hrdef]; linarith
    linarith
  have hballV : Metric.ball z₀ (5 * r) ⊆ V := by
    intro w hw
    apply hRV
    rw [Metric.mem_ball] at hw ⊢
    have h58 : 5 * r < R := by rw [hrdef]; linarith
    linarith
  -- ===== The globally continuous compactly supported localization `F` of `f`. =====
  set F : ℂ → ℂ := fun w => if w ∈ V then ((χ w : ℝ) : ℂ) * f w else 0 with hFdef
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro w
    by_cases hw : w ∈ V
    · have h1 : ContinuousOn (fun u => ((χ u : ℝ) : ℂ) * f u) V :=
        (Complex.continuous_ofReal.comp χ.continuous).continuousOn.mul hf
      refine (h1.continuousAt (hV.mem_nhds hw)).congr ?_
      filter_upwards [hV.mem_nhds hw] with u hu
      rw [hFdef]
      simp [hu]
    · have hwn : w ∉ tsupport (χ : ℂ → ℝ) := by
        rw [χ.tsupport_eq, hrOut]
        intro hmem
        exact hw (hcbV hmem)
      have hnhds : (tsupport (χ : ℂ → ℝ))ᶜ ∈ nhds w :=
        (isClosed_tsupport _).isOpen_compl.mem_nhds hwn
      refine ContinuousAt.congr (f := fun _ => (0 : ℂ)) continuousAt_const ?_
      filter_upwards [hnhds] with u hu
      have hχu : χ u = 0 := image_eq_zero_of_notMem_tsupport hu
      rw [hFdef]
      by_cases huV : u ∈ V
      · simp [huV, hχu]
      · simp [huV]
  have hFf : ∀ u ∈ Metric.ball z₀ (5 * r), F u = f u := by
    intro u hu
    have huV : u ∈ V := hballV hu
    have hχ1 : χ u = 1 := χ.one_of_mem_closedBall
      (show u ∈ Metric.closedBall z₀ χ.rIn by
        rw [hrIn]; exact Metric.ball_subset_closedBall hu)
    rw [hFdef]
    simp [huV, hχ1]
  have hFsupp : HasCompactSupport F := by
    refine HasCompactSupport.intro (isCompact_closedBall z₀ (6 * r)) (fun x hx => ?_)
    have hxn : x ∉ tsupport (χ : ℂ → ℝ) := by
      rw [χ.tsupport_eq, hrOut]
      exact hx
    have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hxn
    rw [hFdef]
    by_cases hxV : x ∈ V
    · simp [hxV, hχx]
    · simp [hxV]
  have hFloc : MeasureTheory.LocallyIntegrable F := hFcont.locallyIntegrable
  -- ===== Mollifier sequence with `rOut ≤ r` and `rOut → 0`. =====
  set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  set φB : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    { rIn := r / (n + 2), rOut := 2 * r / (n + 2),
      rIn_pos := by positivity,
      rIn_lt_rOut := by
        rw [div_lt_div_iff_of_pos_right (by positivity)]; linarith } with hφBdef
  have hφrout : Filter.Tendsto (fun n => (φB n).rOut) Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun n : ℕ => 2 * r / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [hφBdef] using h
  have hφle : ∀ n, (φB n).rOut ≤ r := by
    intro n
    simp only [hφBdef]
    rw [div_le_iff₀ (by positivity)]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  set ρ : ℕ → ℂ → ℝ := fun n => (φB n).normed MeasureTheory.volume with hρdef
  set fn : ℕ → ℂ → ℂ := fun n =>
    MeasureTheory.convolution (ρ n) F L MeasureTheory.volume with hfndef
  have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
    (φB n).contDiff_normed (n := ⊤)
  have hρsupp : ∀ n, HasCompactSupport (ρ n) := fun n => (φB n).hasCompactSupport_normed
  have hρ_one : ∀ n, ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
    (hρsm n).of_le (by exact_mod_cast le_top)
  have hρ_diff : ∀ n, Differentiable ℝ (ρ n) := fun n =>
    (hρ_one n).differentiable (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
  have hdρsupp : ∀ n, HasCompactSupport (fderiv ℝ (ρ n)) := fun n => (hρsupp n).fderiv ℝ
  have hdρcont : ∀ n, Continuous (fderiv ℝ (ρ n)) := fun n =>
    (hρ_one n).continuous_fderiv (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
  -- ===== Directional derivatives of the mollifications, as integrals against `F`. =====
  have hstep : ∀ (n : ℕ) (z v : ℂ), (fderiv ℝ (fn n) z) v
      = ∫ u, ((fderiv ℝ (ρ n) (z - u)) v) • F u := by
    intro n z v
    have hderiv : HasFDerivAt (fn n)
        (MeasureTheory.convolution (fderiv ℝ (ρ n)) F (L.precompL ℂ)
          MeasureTheory.volume z) z :=
      HasCompactSupport.hasFDerivAt_convolution_left L (hρsupp n) (hρ_one n) hFloc z
    rw [hderiv.fderiv]
    have hconvex : MeasureTheory.ConvolutionExistsAt (fderiv ℝ (ρ n)) F z (L.precompL ℂ)
        MeasureTheory.volume :=
      ((hdρsupp n).convolutionExists_left (L.precompL ℂ) (hdρcont n) hFloc) z
    rw [MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply hconvex.integrable]
    simp only [ContinuousLinearMap.precompL_apply, hLdef, ContinuousLinearMap.lsmul_apply]
    have hself := MeasureTheory.integral_sub_left_eq_self
      (fun t => ((fderiv ℝ (ρ n) t) v) • F (z - t)) MeasureTheory.volume z
    simp only [sub_sub_cancel] at hself
    exact hself.symm
  -- ===== Geometry: the mollification zone around points of `ball z₀ 4r`. =====
  have hcball : ∀ z ∈ Metric.ball z₀ (4 * r), ∀ n : ℕ,
      Metric.closedBall z ((φB n).rOut) ⊆ Metric.ball z₀ (5 * r) := by
    intro z hz n u hu
    rw [Metric.mem_ball] at hz ⊢
    rw [Metric.mem_closedBall] at hu
    have h1 : dist u z ≤ r := hu.trans (hφle n)
    calc dist u z₀ ≤ dist u z + dist z z₀ := dist_triangle _ _ _
      _ < 5 * r := by linarith
  -- ===== Key step: `∂̄ (fn n) = 0` on `ball z₀ 4r`, via the test hypothesis. =====
  have hkey : ∀ (n : ℕ), ∀ z ∈ Metric.ball z₀ (4 * r), dzbar (fn n) z = 0 := by
    intro n z hz
    -- The translated-bump complex test function.
    set ψ : ℂ → ℂ := fun u => ((ρ n (z - u) : ℝ) : ℂ) with hψdef
    have hψ_smooth : ContDiff ℝ ∞ ψ :=
      Complex.ofRealCLM.contDiff.comp ((hρsm n).comp (contDiff_const.sub contDiff_id))
    have hψ_supp : HasCompactSupport ψ := by
      have h1 : HasCompactSupport (fun u => ρ n (z - u)) :=
        (hρsupp n).comp_homeomorph (Homeomorph.subLeft z)
      exact h1.comp_left Complex.ofReal_zero
    have hψ_tsub : tsupport ψ ⊆ Metric.closedBall z ((φB n).rOut) := by
      refine closure_minimal ?_ Metric.isClosed_closedBall
      intro u hu
      rw [Function.mem_support] at hu
      have h2 : z - u ∈ Function.support (ρ n) := by
        rw [Function.mem_support]
        intro h0
        apply hu
        change ((ρ n (z - u) : ℝ) : ℂ) = 0
        rw [h0, Complex.ofReal_zero]
      simp only [hρdef] at h2
      rw [(φB n).support_normed_eq] at h2
      rw [Metric.mem_ball, dist_zero_right] at h2
      rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
      exact h2.le
    have hψ_tsuppV : tsupport ψ ⊆ V := hψ_tsub.trans ((hcball z hz n).trans hballV)
    -- Chain rule: the Fréchet derivative of the translated coerced bump.
    have hψ_fderiv : ∀ (u v : ℂ), (fderiv ℝ ψ u) v
        = -(((fderiv ℝ (ρ n) (z - u)) v : ℝ) : ℂ) := by
      intro u v
      have hsub : HasFDerivAt (fun w : ℂ => z - w) (-ContinuousLinearMap.id ℝ ℂ) u := by
        simpa using (hasFDerivAt_id u).const_sub z
      have hcomp : HasFDerivAt (fun w : ℂ => ρ n (z - w))
          ((fderiv ℝ (ρ n) (z - u)).comp (-ContinuousLinearMap.id ℝ ℂ)) u :=
        (hρ_diff n (z - u)).hasFDerivAt.comp u hsub
      have hψd : HasFDerivAt ψ
          (Complex.ofRealCLM.comp
            ((fderiv ℝ (ρ n) (z - u)).comp (-ContinuousLinearMap.id ℝ ℂ))) u :=
        (Complex.ofRealCLM.hasFDerivAt).comp u hcomp
      rw [hψd.fderiv]
      simp
    have hψ_dzbar : ∀ u : ℂ, dzbar ψ u
        = -(1/2 : ℂ) * ((((fderiv ℝ (ρ n) (z - u)) 1 : ℝ) : ℂ)
            + Complex.I * (((fderiv ℝ (ρ n) (z - u)) Complex.I : ℝ) : ℂ)) := by
      intro u
      rw [dzbar, hψ_fderiv u 1, hψ_fderiv u Complex.I]
      ring
    -- The derivative of the bump vanishes off the mollification zone.
    have hoff : ∀ u : ℂ, u ∉ Metric.closedBall z ((φB n).rOut) →
        fderiv ℝ (ρ n) (z - u) = 0 := by
      intro u hu
      have h1 : z - u ∉ tsupport (ρ n) := by
        simp only [hρdef]
        rw [(φB n).tsupport_normed_eq]
        intro hmem
        apply hu
        rw [Metric.mem_closedBall] at hmem ⊢
        rw [dist_zero_right] at hmem
        rw [dist_comm, dist_eq_norm]
        exact hmem
      by_contra h
      exact h1 (support_fderiv_subset ℝ (Function.mem_support.mpr h))
    -- Pointwise bridge between the test integrand and the convolution integrands.
    have hbridge : ∀ u : ℂ, dzbar ψ u * f u
        = -(1/2 : ℂ) * (((fderiv ℝ (ρ n) (z - u)) 1) • F u
            + Complex.I * (((fderiv ℝ (ρ n) (z - u)) Complex.I) • F u)) := by
      intro u
      by_cases hu : u ∈ Metric.closedBall z ((φB n).rOut)
      · rw [hψ_dzbar u, hFf u (hcball z hz n hu), Complex.real_smul, Complex.real_smul]
        ring
      · rw [hψ_dzbar u, hoff u hu]
        simp
    -- Integrability of the convolution integrands.
    have hdcont : ∀ v : ℂ, Continuous fun u => (fderiv ℝ (ρ n) (z - u)) v := fun v =>
      ((hdρcont n).comp (continuous_const.sub continuous_id)).clm_apply continuous_const
    have hIsm : ∀ v : ℂ, Integrable (fun u => ((fderiv ℝ (ρ n) (z - u)) v) • F u) volume := by
      intro v
      have h1 : Integrable (fun u => (((fderiv ℝ (ρ n) (z - u)) v : ℝ) : ℂ) * F u) volume :=
        ((Complex.continuous_ofReal.comp (hdcont v)).mul
          hFcont).integrable_of_hasCompactSupport hFsupp.mul_left
      have h2 : (fun u => ((fderiv ℝ (ρ n) (z - u)) v) • F u)
          = fun u => (((fderiv ℝ (ρ n) (z - u)) v : ℝ) : ℂ) * F u := by
        funext u
        exact Complex.real_smul
      rw [h2]
      exact h1
    have hI1 := hIsm 1
    have hI2' : Integrable
        (fun u => Complex.I * (((fderiv ℝ (ρ n) (z - u)) Complex.I) • F u)) volume :=
      (hIsm Complex.I).const_mul _
    -- Split the test integral into the two convolution integrals.
    have hsplit : ∫ u, dzbar ψ u * f u
        = -(1/2 : ℂ) * ((∫ u, ((fderiv ℝ (ρ n) (z - u)) 1) • F u)
            + Complex.I * ∫ u, ((fderiv ℝ (ρ n) (z - u)) Complex.I) • F u) := by
      calc ∫ u, dzbar ψ u * f u
          = ∫ u, -(1/2 : ℂ) * (((fderiv ℝ (ρ n) (z - u)) 1) • F u
              + Complex.I * (((fderiv ℝ (ρ n) (z - u)) Complex.I) • F u)) :=
            MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hbridge)
        _ = -(1/2 : ℂ) * ∫ u, (((fderiv ℝ (ρ n) (z - u)) 1) • F u
              + Complex.I * (((fderiv ℝ (ρ n) (z - u)) Complex.I) • F u)) :=
            MeasureTheory.integral_const_mul _ _
        _ = -(1/2 : ℂ) * ((∫ u, ((fderiv ℝ (ρ n) (z - u)) 1) • F u)
              + ∫ u, Complex.I * (((fderiv ℝ (ρ n) (z - u)) Complex.I) • F u)) := by
            rw [MeasureTheory.integral_add hI1 hI2']
        _ = -(1/2 : ℂ) * ((∫ u, ((fderiv ℝ (ρ n) (z - u)) 1) • F u)
              + Complex.I * ∫ u, ((fderiv ℝ (ρ n) (z - u)) Complex.I) • F u) := by
            congr 1
            congr 1
            exact MeasureTheory.integral_const_mul Complex.I _
    have h0 := htest ψ hψ_smooth hψ_supp hψ_tsuppV
    have hsum : (∫ u, ((fderiv ℝ (ρ n) (z - u)) 1) • F u)
        + Complex.I * ∫ u, ((fderiv ℝ (ρ n) (z - u)) Complex.I) • F u = 0 := by
      have h3 : -(1/2 : ℂ) * ((∫ u, ((fderiv ℝ (ρ n) (z - u)) 1) • F u)
          + Complex.I * ∫ u, ((fderiv ℝ (ρ n) (z - u)) Complex.I) • F u) = 0 := by
        rw [← hsplit]
        exact h0
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 (by norm_num)
      · exact h4
    rw [dzbar, hstep n z 1, hstep n z Complex.I, hsum, mul_zero]
  -- ===== Each mollification is holomorphic on `ball z₀ 4r`. =====
  have hfn_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fn n) := fun n =>
    (hρsupp n).contDiff_convolution_left L (hρsm n) hFloc
  have hfn_holo : ∀ n, DifferentiableOn ℂ (fn n) (Metric.ball z₀ (4 * r)) := by
    intro n
    refine (differentiableOn_iff_dzbar_eq_zero Metric.isOpen_ball ?_).mpr
      (fun z hz => hkey n z hz)
    exact fun z _ =>
      (((hfn_smooth n).differentiable (by simp)).differentiableAt).differentiableWithinAt
  -- ===== `fn → F` locally uniformly. =====
  have hTLUg : TendstoLocallyUniformly (fun n => fn n) F Filter.atTop := by
    refine tendstoLocallyUniformly_of_forall_exists_nhds (fun x => ?_)
    refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
    have hUC : UniformContinuousOn F (Metric.closedBall x 2) :=
      (isCompact_closedBall x 2).uniformContinuousOn_of_continuous hFcont.continuousOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by positivity
    obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) hε2
    have hev : ∀ᶠ n in Filter.atTop, (φB n).rOut < min δ 1 := by
      have := hφrout.eventually (eventually_lt_nhds (show (0 : ℝ) < min δ 1 by positivity))
      filter_upwards [this] with n hn using hn
    filter_upwards [hev] with n hn z hz
    have hrout_le_one : (φB n).rOut ≤ 1 := (lt_of_lt_of_le hn (min_le_right δ 1)).le
    have hrout_le_δ : (φB n).rOut ≤ δ := (lt_of_lt_of_le hn (min_le_left δ 1)).le
    have hsupp2 : Function.support (ρ n) ⊆ Metric.ball (0 : ℂ) (φB n).rOut := by
      simp only [hρdef]
      rw [(φB n).support_normed_eq]
    have hnf : ∀ y, 0 ≤ ρ n y := fun y => (φB n).nonneg_normed y
    have hintf : ∫ y, ρ n y ∂MeasureTheory.volume = 1 := (φB n).integral_normed
    have hclose : ∀ y ∈ Metric.ball z ((φB n).rOut), dist (F y) (F z) ≤ ε / 2 := by
      intro y hy
      have hzmem : z ∈ Metric.closedBall x 2 :=
        Metric.closedBall_subset_closedBall (by norm_num) hz
      rw [Metric.mem_ball] at hy
      have hymem : y ∈ Metric.closedBall x 2 := by
        rw [Metric.mem_closedBall] at hz ⊢
        calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
          _ ≤ (φB n).rOut + 1 := by gcongr
          _ ≤ 1 + 1 := by gcongr
          _ = 2 := by norm_num
      exact (hδ y hymem z hzmem (hy.trans_le hrout_le_δ)).le
    calc dist (F z) (fn n z)
        = dist (fn n z) (F z) := dist_comm _ _
      _ ≤ ε / 2 := dist_convolution_le hε2.le hsupp2 hnf hintf
            hFcont.aestronglyMeasurable hclose
      _ < ε := by linarith
  -- ===== Conclusion at `z₀`. =====
  have hTLU : TendstoLocallyUniformlyOn (fun n => fn n) F Filter.atTop
      (Metric.ball z₀ (4 * r)) := hTLUg.tendstoLocallyUniformlyOn
  have hFdiff : DifferentiableOn ℂ F (Metric.ball z₀ (4 * r)) :=
    hTLU.differentiableOn (Filter.Eventually.of_forall hfn_holo) Metric.isOpen_ball
  have hfdiff : DifferentiableOn ℂ f (Metric.ball z₀ (4 * r)) := by
    refine hFdiff.congr (fun u hu => ?_)
    exact (hFf u (Metric.ball_subset_ball (by linarith) hu)).symm
  have hz₀mem : z₀ ∈ Metric.ball z₀ (4 * r) := Metric.mem_ball_self (by linarith)
  exact ((hfdiff z₀ hz₀mem).differentiableAt
    (Metric.isOpen_ball.mem_nhds hz₀mem)).differentiableWithinAt

end NoWanderingDomains
