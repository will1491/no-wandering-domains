/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.MRMT.SmoothCase.Solution

/-!
# The smooth-case solution as a homeomorphism, and its inverse

The `C¹` principal solution of a smooth compactly supported coefficient is a
homeomorphism of the plane, and its inverse is the principal solution of the
explicit coefficient `ν = −(μ∘g)·(∂f∘g)/conj(∂f∘g)`, of no larger dilatation
and compactly supported in the image of `supp μ`.

* `isHomeomorph_of_contDiffOne_principalSolution` — the homeomorphism.
* `IsPrincipalSolution.inverse_principalSolution_of_contDiff` — the inverse.
-/

open MeasureTheory Complex Filter
open scoped ContDiff ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **A nondegenerate `C¹` principal solution is a homeomorphism of the plane**
(AIM Theorem 5.2.4). Everywhere-positive Jacobian makes `f` a local
homeomorphism (inverse function theorem); the principal normalization makes it
proper (`f − id → 0` at infinity) and holomorphic and injective near infinity
(off the support ball of its field, `f = id + P h` is holomorphic with Laurent
expansion `z + O(1/z)`); the fiber-count function of a proper local
homeomorphism of the plane is locally constant, and it equals `1` near
infinity, so `f` is a global homeomorphism. -/
theorem isHomeomorph_of_contDiffOne_principalSolution {b : BeltramiCoeff}
    {f : ℂ → ℂ} (hf : IsPrincipalSolution b f) (hf1 : ContDiff ℝ 1 f)
    (hdet : ∀ z : ℂ, 0 < (fderiv ℝ f z).det) :
    IsHomeomorph f := by
  classical
  have hcont : Continuous f := hf1.continuous
  have hdecay : Tendsto (fun z => f z - z) (cocompact ℂ) (𝓝 0) :=
    hf.tendsto_sub_id_cocompact
  -- ===== 1. `f` is a local homeomorphism (inverse function theorem). =====
  have hlocal : IsLocalHomeomorph f := by
    intro z
    have hsd : HasStrictFDerivAt f (fderiv ℝ f z) z :=
      hf1.contDiffAt.hasStrictFDerivAt one_ne_zero
    have hAdet : LinearMap.det ((fderiv ℝ f z : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) ≠ 0 :=
      (hdet z).ne'
    set eqv : ℂ ≃L[ℝ] ℂ :=
      (LinearMap.equivOfDetNeZero ((fderiv ℝ f z : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)
        hAdet).toContinuousLinearEquiv with heqv
    have hcoe : (eqv : ℂ →L[ℝ] ℂ) = fderiv ℝ f z := by
      ext w
      simp [heqv]
    have hsd' : HasStrictFDerivAt f ((eqv : ℂ →L[ℝ] ℂ)) z := by
      rw [hcoe]; exact hsd
    exact ⟨hsd'.toOpenPartialHomeomorph f, hsd'.mem_toOpenPartialHomeomorph_source,
      (hsd'.toOpenPartialHomeomorph_coe).symm⟩
  have hopen : IsOpenMap f := hlocal.isOpenMap
  have hstack : ∀ z : ℂ, ∃ W : Set ℂ, IsOpen W ∧ z ∈ W ∧ Set.InjOn f W := by
    intro z
    obtain ⟨e, hz, hfe⟩ := hlocal z
    refine ⟨e.source, e.open_source, hz, ?_⟩
    rw [hfe]
    exact e.injOn
  -- ===== 2. `f` is proper, hence a closed map. =====
  have hnormf : Tendsto (fun z : ℂ => ‖f z‖) (cocompact ℂ) atTop := by
    have h1 : Tendsto (fun z : ℂ => ‖f z - z‖) (cocompact ℂ) (𝓝 0) := by
      simpa using hdecay.norm
    have hev : ∀ᶠ z : ℂ in cocompact ℂ, ‖f z - z‖ < 1 :=
      h1.eventually_lt_const one_pos
    have hz1 : Tendsto (fun z : ℂ => ‖z‖ - 1) (cocompact ℂ) atTop := by
      simpa [sub_eq_add_neg] using
        tendsto_atTop_add_const_right (cocompact ℂ) (-1 : ℝ) tendsto_norm_cocompact_atTop
    refine tendsto_atTop_mono' (cocompact ℂ) ?_ hz1
    filter_upwards [hev] with z hz
    have h2 : ‖z‖ ≤ ‖f z‖ + ‖f z - z‖ := by
      simpa [sub_sub_cancel] using norm_sub_le (f z) (f z - z)
    linarith
  have hcoc : Tendsto f (cocompact ℂ) (cocompact ℂ) := by
    rw [Filter.hasBasis_cocompact.tendsto_right_iff]
    intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    filter_upwards [hnormf.eventually (eventually_gt_atTop r)] with z hz
    exact fun hmem => absurd (mem_closedBall_zero_iff.mp (hr hmem)) (not_le.mpr hz)
  have hproper : IsProperMap f := isProperMap_iff_tendsto_cocompact.mpr ⟨hcont, hcoc⟩
  have hclosedmap : IsClosedMap f := hproper.isClosedMap
  -- ===== 3. `f` is surjective (open + closed range in the connected plane). =====
  have hrange_closed : IsClosed (Set.range f) := by
    have h1 := hclosedmap Set.univ isClosed_univ
    rwa [Set.image_univ] at h1
  have hsurj : Function.Surjective f := by
    rw [← Set.range_eq_univ]
    exact IsClopen.eq_univ ⟨hrange_closed, hopen.isOpen_range⟩ ⟨f 0, 0, rfl⟩
  -- ===== 4. far-region holomorphy and injectivity. =====
  obtain ⟨p, h, R, hp, hp', hmem, hsupp_h, _heq, hrepr⟩ := hf
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp.le
  have hgfun : (fun z => f z - z) = cauchyTransform h := by
    funext z; rw [hrepr z]; ring
  have hgC1 : ContDiff ℝ 1 (fun z => f z - z) := hf1.sub contDiff_id
  have hPhC1 : ContDiff ℝ 1 (cauchyTransform h) := by rw [← hgfun]; exact hgC1
  -- a.e. identification of `∂̄f` with the field `h` by weak-derivative uniqueness.
  have hwg := hasWeakGradient_cauchyTransform hp hp' hmem hsupp_h
  have hfdPh_cont : Continuous (fun z => fderiv ℝ (cauchyTransform h) z) :=
    (contDiff_one_iff_fderiv.mp hPhC1).2
  have hclx_cont : Continuous (fun z => (fderiv ℝ (cauchyTransform h) z) 1) :=
    ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous).comp hfdPh_cont
  have hcly_cont : Continuous (fun z => (fderiv ℝ (cauchyTransform h) z) Complex.I) :=
    ((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp hfdPh_cont
  have hSh_mem : MemLp (beurling h) p volume := memLp_beurling_of_memLp hp hp' hmem
  have haex := HasWeakDirDeriv.ae_eq isOpen_univ
    (HasWeakDirDeriv.of_contDiffOn isOpen_univ hPhC1.contDiffOn) hwg.1
    (locallyIntegrableOn_univ.mpr hclx_cont.locallyIntegrable)
    (locallyIntegrableOn_univ.mpr ((hSh_mem.add hmem).locallyIntegrable hp1))
  have haey := HasWeakDirDeriv.ae_eq isOpen_univ
    (HasWeakDirDeriv.of_contDiffOn isOpen_univ hPhC1.contDiffOn) hwg.2
    (locallyIntegrableOn_univ.mpr hcly_cont.locallyIntegrable)
    (locallyIntegrableOn_univ.mpr
      (((hSh_mem.sub hmem).const_mul Complex.I).locallyIntegrable hp1))
  have hff : f = fun w => w + cauchyTransform h w := funext hrepr
  have haedzbar : ∀ᵐ z ∂(volume : Measure ℂ), dzbar f z = h z := by
    filter_upwards [haex, haey] with z hx hy
    have hx' : (fderiv ℝ (cauchyTransform h) z) 1 = beurling h z + h z :=
      hx (Set.mem_univ z)
    have hy' : (fderiv ℝ (cauchyTransform h) z) Complex.I
        = Complex.I * (beurling h z - h z) := hy (Set.mem_univ z)
    have hidd : DifferentiableAt ℝ (fun w : ℂ => w) z := differentiable_id.differentiableAt
    have hPd : DifferentiableAt ℝ (cauchyTransform h) z :=
      (hPhC1.differentiable one_ne_zero).differentiableAt
    have hdzbarid : dzbar (fun w : ℂ => w) z = 0 := by
      rw [dzbar, fderiv_fun_id]
      simp only [ContinuousLinearMap.id_apply]
      linear_combination ((1 / 2 : ℂ)) * Complex.I_mul_I
    rw [hff, dzbar_add hidd hPd, hdzbarid, zero_add, dzbar, hx', hy']
    linear_combination ((1 / 2 : ℂ) * (beurling h z - h z)) * Complex.I_mul_I
  -- `∂̄f` is continuous and vanishes pointwise on the far region.
  have hdzbarf_cont : Continuous (fun z => dzbar f z) := by
    have h1 : Continuous (fun z => fderiv ℝ f z) := (contDiff_one_iff_fderiv.mp hf1).2
    have h2 : Continuous (fun z => (fderiv ℝ f z) 1) :=
      ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous).comp h1
    have h3 : Continuous (fun z => (fderiv ℝ f z) Complex.I) :=
      ((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp h1
    have h4 : (fun z => dzbar f z)
        = fun z => (1 / 2 : ℂ)
            * ((fderiv ℝ f z) 1 + Complex.I * (fderiv ℝ f z) Complex.I) := by
      funext z; rw [dzbar]
    rw [h4]
    exact continuous_const.mul (h2.add (continuous_const.mul h3))
  have hUfar_open : IsOpen {w : ℂ | R < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hdzbarf_far : ∀ z, R < ‖z‖ → dzbar f z = 0 := by
    intro z hz
    by_contra hne
    have hopen2 : IsOpen ({w : ℂ | R < ‖w‖} ∩ {w | dzbar f w ≠ 0}) :=
      hUfar_open.inter (isOpen_ne_fun hdzbarf_cont continuous_const)
    have hnull : volume ({w : ℂ | R < ‖w‖} ∩ {w | dzbar f w ≠ 0}) = 0 := by
      have h5 : ({w : ℂ | R < ‖w‖} ∩ {w | dzbar f w ≠ 0})
          ⊆ {w | ¬ dzbar f w = h w} := by
        rintro w ⟨hw1, hw2⟩ hcontra
        exact hw2 (by rw [hcontra, hsupp_h w hw1])
      exact measure_mono_null h5 (MeasureTheory.ae_iff.mp haedzbar)
    exact absurd hnull (hopen2.measure_pos volume ⟨z, hz, hne⟩).ne'
  have hholo_far : DifferentiableOn ℂ f {w : ℂ | R < ‖w‖} := by
    refine (differentiableOn_iff_dzbar_eq_zero hUfar_open ?_).mpr
      (fun z hz => hdzbarf_far z hz)
    exact fun z _ => ((hf1.differentiable one_ne_zero) z).differentiableWithinAt
  have hgholo : DifferentiableOn ℂ (fun z => f z - z) {w : ℂ | R < ‖w‖} :=
    hholo_far.sub differentiable_id.differentiableOn
  -- Far smallness of the displacement.
  have hev4 : ∀ᶠ z : ℂ in cocompact ℂ, ‖f z - z‖ ≤ 1 / 4 := by
    have h1 : Tendsto (fun z : ℂ => ‖f z - z‖) (cocompact ℂ) (𝓝 0) := by
      simpa using hdecay.norm
    exact h1.eventually (eventually_le_nhds (by norm_num))
  rw [Filter.eventually_iff, Filter.mem_cocompact] at hev4
  obtain ⟨K, hKc, hKsub⟩ := hev4
  obtain ⟨r, hr⟩ := hKc.isBounded.subset_closedBall 0
  set R₁ : ℝ := max r (R + 1) + 1 with hR₁def
  have hR₁r : r < R₁ := by
    have := le_max_left r (R + 1); rw [hR₁def]; linarith
  have hR₁R : R + 1 < R₁ := by
    have := le_max_right r (R + 1); rw [hR₁def]; linarith
  have hgsm : ∀ z : ℂ, R₁ ≤ ‖z‖ → ‖f z - z‖ ≤ 1 / 4 := by
    intro z hz
    refine hKsub ?_
    intro hzK
    have h6 := hr hzK
    rw [Metric.mem_closedBall, dist_zero_right] at h6
    linarith
  -- Cauchy estimate for the derivative of the displacement on the far region.
  have hderiv_bd : ∀ x : ℂ, R₁ + 1 < ‖x‖ → ‖deriv (fun z => f z - z) x‖ ≤ 1 / 4 := by
    intro x hx
    have hsub1 : Metric.closedBall x 1 ⊆ {w : ℂ | R < ‖w‖} := by
      intro w hw
      rw [Metric.mem_closedBall] at hw
      have h7 : ‖x‖ - ‖w‖ ≤ 1 := by
        calc ‖x‖ - ‖w‖ ≤ ‖x - w‖ := norm_sub_norm_le x w
          _ = dist w x := by rw [dist_comm, dist_eq_norm]
          _ ≤ 1 := hw
      simp only [Set.mem_ofPred_eq]
      linarith
    have hdiff : DifferentiableOn ℂ (fun z => f z - z) (closure (Metric.ball x 1)) := by
      rw [closure_ball x one_ne_zero]
      exact hgholo.mono hsub1
    have hdc : DiffContOnCl ℂ (fun z => f z - z) (Metric.ball x 1) :=
      hdiff.diffContOnCl
    have hsp : ∀ w ∈ Metric.sphere x 1, ‖f w - w‖ ≤ 1 / 4 := by
      intro w hw
      rw [Metric.mem_sphere] at hw
      refine hgsm w ?_
      have h8 : ‖x‖ - ‖w‖ ≤ 1 := by
        calc ‖x‖ - ‖w‖ ≤ ‖x - w‖ := norm_sub_norm_le x w
          _ = dist w x := by rw [dist_comm, dist_eq_norm]
          _ = 1 := hw
      linarith
    have h9 := norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hdc hsp
    simpa using h9
  -- Far injectivity.
  have hfar_inj : ∀ z₁ z₂ : ℂ, R₁ + 2 < ‖z₁‖ → R₁ + 2 < ‖z₂‖ → f z₁ = f z₂ → z₁ = z₂ := by
    intro z₁ z₂ h₁ h₂ hf12
    have hnormdiff : z₁ - z₂ = (f z₂ - z₂) - (f z₁ - z₁) := by rw [hf12]; ring
    have hsmall12 : ‖z₁ - z₂‖ ≤ 1 / 2 := by
      rw [hnormdiff]
      calc ‖(f z₂ - z₂) - (f z₁ - z₁)‖
          ≤ ‖f z₂ - z₂‖ + ‖f z₁ - z₁‖ := norm_sub_le _ _
        _ ≤ 1 / 4 + 1 / 4 :=
            add_le_add (hgsm z₂ (by linarith)) (hgsm z₁ (by linarith))
        _ = 1 / 2 := by norm_num
    have hballfar : ∀ x ∈ Metric.closedBall z₁ (1 : ℝ), R₁ + 1 < ‖x‖ := by
      intro x hx
      rw [Metric.mem_closedBall] at hx
      have h8 : ‖z₁‖ - ‖x‖ ≤ 1 := by
        calc ‖z₁‖ - ‖x‖ ≤ ‖z₁ - x‖ := norm_sub_norm_le z₁ x
          _ = dist x z₁ := by rw [dist_comm, dist_eq_norm]
          _ ≤ 1 := hx
      linarith
    have hreprL : ∀ (L : ℂ →L[ℝ] ℂ) (w : ℂ),
        L w = (1 / 2 : ℂ) * ((L 1) - I * (L I)) * w
          + (1 / 2 : ℂ) * ((L 1) + I * (L I)) * (starRingEnd ℂ) w := by
      intro L w
      have hLw : L w = (↑w.re : ℂ) * L 1 + (↑w.im : ℂ) * L I := by
        conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • I by
          rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
        rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
      have hcw : (starRingEnd ℂ) w = (↑w.re : ℂ) - ↑w.im * I := by
        conv_lhs => rw [← Complex.re_add_im w]
        simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
        ring
      have hw : w = (↑w.re : ℂ) + ↑w.im * I := (Complex.re_add_im w).symm
      rw [hLw, hcw]
      set a : ℂ := (↑w.re : ℂ) with ha
      set bb : ℂ := (↑w.im : ℂ) with hbb
      rw [hw]
      linear_combination (bb * L I) * Complex.I_mul_I
    have hdzbarg : ∀ x, R < ‖x‖ → dzbar (fun z => f z - z) x = 0 := by
      intro x hx
      have hd1' : DifferentiableAt ℝ f x := (hf1.differentiable one_ne_zero) x
      have hd2' : DifferentiableAt ℝ (fun w : ℂ => w) x := differentiable_id.differentiableAt
      have hfdsub : fderiv ℝ (fun z : ℂ => f z - z) x
          = fderiv ℝ f x - fderiv ℝ (fun w : ℂ => w) x := fderiv_fun_sub hd1' hd2'
      have h0 := hdzbarf_far x hx
      rw [dzbar] at h0
      rw [dzbar, hfdsub, fderiv_fun_id]
      simp only [sub_apply, ContinuousLinearMap.id_apply]
      linear_combination h0 + (-(1 / 2 : ℂ)) * Complex.I_mul_I
    have hderivsW : ∀ x ∈ Metric.closedBall z₁ (1 : ℝ),
        HasFDerivWithinAt (fun z => f z - z) (fderiv ℝ (fun z => f z - z) x)
          (Metric.closedBall z₁ 1) x := fun x _ =>
      ((hgC1.differentiable one_ne_zero x).hasFDerivAt).hasFDerivWithinAt
    have hbound : ∀ x ∈ Metric.closedBall z₁ (1 : ℝ),
        ‖fderiv ℝ (fun z => f z - z) x‖ ≤ 1 / 4 := by
      intro x hx
      have hxfar := hballfar x hx
      have hxR : R < ‖x‖ := by linarith [hR₁R]
      have hxU : {w : ℂ | R < ‖w‖} ∈ 𝓝 x := hUfar_open.mem_nhds hxR
      have hdC : DifferentiableAt ℂ (fun z => f z - z) x := hgholo.differentiableAt hxU
      have hdzg' := dz_eq_deriv_of_differentiableAt hdC
      rw [dz] at hdzg'
      have hdzbarg0' := hdzbarg x hxR
      rw [dzbar] at hdzbarg0'
      refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun v => ?_)
      have hval := hreprL (fderiv ℝ (fun z => f z - z) x) v
      rw [hdzg', hdzbarg0', zero_mul, add_zero] at hval
      rw [hval, norm_mul]
      exact mul_le_mul_of_nonneg_right (hderiv_bd x hxfar) (norm_nonneg v)
    have hz₂mem : z₂ ∈ Metric.closedBall z₁ (1 : ℝ) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖z₂ - z₁‖ = ‖z₁ - z₂‖ := norm_sub_rev _ _
        _ ≤ 1 / 2 := hsmall12
        _ ≤ 1 := by norm_num
    have hz₁mem : z₁ ∈ Metric.closedBall z₁ (1 : ℝ) :=
      Metric.mem_closedBall_self one_pos.le
    have hMVT := (convex_closedBall z₁ (1 : ℝ)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hderivsW hbound hz₁mem hz₂mem
    have h9 : ‖z₁ - z₂‖ ≤ 1 / 4 * ‖z₁ - z₂‖ := by
      calc ‖z₁ - z₂‖ = ‖(f z₂ - z₂) - (f z₁ - z₁)‖ := by rw [hnormdiff]
        _ ≤ 1 / 4 * ‖z₂ - z₁‖ := hMVT
        _ = 1 / 4 * ‖z₁ - z₂‖ := by rw [norm_sub_rev]
    have h10 : ‖z₁ - z₂‖ = 0 := by nlinarith [norm_nonneg (z₁ - z₂)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h10)
  -- A global displacement bound and a very far target point.
  obtain ⟨Mg, hMg0, hMg⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖f z - z‖ ≤ M := by
    obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) R₁).exists_bound_of_continuousOn
      (hgC1.continuous.continuousOn)
    refine ⟨max M₀ (1 / 4), le_trans (by norm_num) (le_max_right _ _), fun z => ?_⟩
    by_cases hz : R₁ ≤ ‖z‖
    · exact le_trans (hgsm z hz) (le_max_right _ _)
    · refine le_trans (hM₀ z ?_) (le_max_left _ _)
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
  set w₀ : ℂ := ((|R₁| + Mg + 4 : ℝ) : ℂ) with hw₀def
  have hw₀norm : ‖w₀‖ = |R₁| + Mg + 4 := by
    rw [hw₀def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [abs_nonneg R₁] : (0 : ℝ) ≤ |R₁| + Mg + 4)]
  have hfarfiber : ∀ z, f z = w₀ → R₁ + 2 < ‖z‖ := by
    intro z hz
    have h2 : ‖w₀‖ ≤ ‖z‖ + ‖f z - z‖ := by
      rw [← hz]
      calc ‖f z‖ = ‖z + (f z - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖f z - z‖ := norm_add_le _ _
    have h3 := hMg z
    rw [hw₀norm] at h2
    have habs : R₁ ≤ |R₁| := le_abs_self R₁
    linarith
  -- ===== 5. the set of subsingleton fibers is clopen, hence everything. =====
  set Good : Set ℂ := {w | Set.Subsingleton (f ⁻¹' {w})} with hGooddef
  have hGood_open : IsOpen Good := by
    rw [isOpen_iff_forall_mem_open]
    intro w₁ hw₁
    have hw₁' : (f ⁻¹' {w₁}).Subsingleton := hw₁
    obtain ⟨z₀, hz₀⟩ := hsurj w₁
    have hfib : ∀ c, f c = w₁ → c = z₀ := fun c hc =>
      hw₁' (show c ∈ f ⁻¹' {w₁} from hc) (show z₀ ∈ f ⁻¹' {w₁} from hz₀)
    obtain ⟨W, hWopen, hz₀W, hWinj⟩ := hstack z₀
    refine ⟨(f '' W) ∩ (f '' Wᶜ)ᶜ, ?_, ?_, ?_⟩
    · rintro w ⟨hw1, hw2⟩
      have hfibW : ∀ c, f c = w → c ∈ W := by
        intro c hc
        by_contra hcW
        exact hw2 ⟨c, hcW, hc⟩
      intro a ha c hc
      have ha' : f a = w := ha
      have hc' : f c = w := hc
      exact hWinj (hfibW a ha') (hfibW c hc') (ha'.trans hc'.symm)
    · exact (hopen W hWopen).inter (isOpen_compl_iff.mpr (hclosedmap Wᶜ hWopen.isClosed_compl))
    · constructor
      · exact ⟨z₀, hz₀W, hz₀⟩
      · rintro ⟨c, hcW, hc⟩
        exact hcW (hfib c hc ▸ hz₀W)
  have hGoodc_open : IsOpen Goodᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro w₁ hw₁
    have hw₁' : ¬ (f ⁻¹' {w₁}).Subsingleton := hw₁
    rw [Set.not_subsingleton_iff] at hw₁'
    obtain ⟨z₁, hz₁, z₂, hz₂, hne⟩ := hw₁'
    have hz₁' : f z₁ = w₁ := hz₁
    have hz₂' : f z₂ = w₁ := hz₂
    obtain ⟨W₁, hW₁o, hzW₁, hinj₁⟩ := hstack z₁
    obtain ⟨W₂, hW₂o, hzW₂, hinj₂⟩ := hstack z₂
    obtain ⟨U₁, U₂, hU₁o, hU₂o, hzU₁, hzU₂, hUdisj⟩ := t2_separation hne
    refine ⟨f '' (W₁ ∩ U₁) ∩ f '' (W₂ ∩ U₂), ?_, ?_, ?_⟩
    · rintro w ⟨⟨a, ⟨haW, haU⟩, ha⟩, ⟨c, ⟨hcW, hcU⟩, hc⟩⟩
      have hac : a ≠ c := by
        intro haceq
        rw [haceq] at haU
        exact (Set.disjoint_left.mp hUdisj haU) hcU
      intro hsub
      exact hac (hsub (show a ∈ f ⁻¹' {w} from ha) (show c ∈ f ⁻¹' {w} from hc))
    · exact (hopen _ (hW₁o.inter hU₁o)).inter (hopen _ (hW₂o.inter hU₂o))
    · exact ⟨⟨z₁, ⟨hzW₁, hzU₁⟩, hz₁'⟩, ⟨z₂, ⟨hzW₂, hzU₂⟩, hz₂'⟩⟩
  have hGood_w₀ : w₀ ∈ Good := by
    have h1 : (f ⁻¹' {w₀}).Subsingleton := by
      intro a ha c hc
      have ha' : f a = w₀ := ha
      have hc' : f c = w₀ := hc
      exact hfar_inj a c (hfarfiber a ha') (hfarfiber c hc') (ha'.trans hc'.symm)
    exact h1
  have hGood_univ : Good = Set.univ :=
    IsClopen.eq_univ ⟨isOpen_compl_iff.mp hGoodc_open, hGood_open⟩ ⟨w₀, hGood_w₀⟩
  have hinj : Function.Injective f := by
    intro a c hac
    have h1 : f c ∈ Good := by rw [hGood_univ]; exact Set.mem_univ _
    have h2 : (f ⁻¹' {f c}).Subsingleton := h1
    exact h2 (show a ∈ f ⁻¹' {f c} from hac) (show c ∈ f ⁻¹' {f c} from rfl)
  exact ⟨hcont, hopen, hinj, hsurj⟩

/-- **The inverse of the smooth-case principal solution is a principal
solution** (Ahlfors–Bers Lemma 11). If `f` is a `C¹` homeomorphic principal
solution for a smooth compactly supported coefficient, its inverse
`g = f⁻¹` is the principal solution of the explicit coefficient

`ν(w) = −μ(g w)·∂f(g w) / conj (∂f(g w))`

(chain rule for `C¹` diffeomorphisms: `∂g = conj(∂f)/J ∘ g`,
`∂̄g = −∂̄f/J ∘ g`). Since `|ν| = |μ ∘ g|` pointwise, the dilatation does not
grow, and `ν` is supported in the compact image `f '' supp μ` — the two
uniformities the measurable-case endgame consumes. -/
theorem IsPrincipalSolution.inverse_principalSolution_of_contDiff
    {b : BeltramiCoeff} {f : ℂ → ℂ} (hf : IsPrincipalSolution b f)
    (hμs : ContDiff ℝ ∞ b.μ) (hμc : HasCompactSupport b.μ)
    (hf1 : ContDiff ℝ 1 f) (hdet : ∀ z : ℂ, 0 < (fderiv ℝ f z).det)
    (hhom : IsHomeomorph f) :
    ∃ ν : BeltramiCoeff,
      (∀ w : ℂ, ν.μ w = -(b.μ ((hhom.homeomorph f).symm w)
          * dz f ((hhom.homeomorph f).symm w)
          / (starRingEnd ℂ) (dz f ((hhom.homeomorph f).symm w)))) ∧
      eLpNormEssSup ν.μ volume ≤ eLpNormEssSup b.μ volume ∧
      HasCompactSupport ν.μ ∧
      (∀ w : ℂ, ν.μ w ≠ 0 → w ∈ f '' tsupport b.μ) ∧
      IsPrincipalSolution ν ⇑(hhom.homeomorph f).symm := by
  classical
  -- ===== 0. homeomorphism bookkeeping =====
  set G := hhom.homeomorph f with hGdef
  set g : ℂ → ℂ := ⇑G.symm with hgdef
  have hGcoe : ⇑G = f := by
    funext a
    rw [hGdef]
    exact IsHomeomorph.homeomorph_apply f hhom a
  have hcont : Continuous f := hf1.continuous
  have hgc : Continuous g := by rw [hgdef]; exact G.symm.continuous
  have hfg : ∀ w, f (g w) = w := by
    intro w
    rw [hgdef, ← hGcoe]
    exact G.apply_symm_apply w
  have hgf : ∀ z, g (f z) = z := by
    intro z
    rw [hgdef, ← hGcoe]
    exact G.symm_apply_apply z
  have hinj : Function.Injective f := by
    intro a c hac
    have h1 := congrArg g hac
    rwa [hgf, hgf] at h1
  -- ===== 1. pointwise coefficient bound =====
  set k : ℝ := (eLpNormEssSup b.μ volume).toReal with hkdef
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hkfin : eLpNormEssSup b.μ volume ≠ ⊤ := (b.bound.trans_le le_top).ne
  have hk1 : k < 1 := by
    rw [hkdef, show (1 : ℝ) = (1 : ℝ≥0∞).toReal by simp]
    exact (ENNReal.toReal_lt_toReal hkfin ENNReal.one_ne_top).2 b.bound
  have hμ_ae : ∀ᵐ z ∂(volume : Measure ℂ), ‖b.μ z‖ ≤ k := by
    have h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖b.μ z‖ₑ ≤ eLpNormEssSup b.μ volume :=
      ae_le_eLpNormEssSup
    filter_upwards [h1] with z hz
    rw [← ofReal_norm] at hz
    have h3 := ENNReal.toReal_mono hkfin hz
    rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h3
  have hμpt : ∀ z, ‖b.μ z‖ ≤ k := by
    by_contra hcon
    obtain ⟨z₀, hz₀⟩ := not_forall.mp hcon
    rw [not_le] at hz₀
    have hopen : IsOpen {z : ℂ | k < ‖b.μ z‖} :=
      isOpen_lt continuous_const hμs.continuous.norm
    have hnull : volume {z : ℂ | k < ‖b.μ z‖} = 0 := by
      have h2 := hμ_ae
      rw [MeasureTheory.ae_iff] at h2
      have hset : {z : ℂ | ¬ ‖b.μ z‖ ≤ k} = {z : ℂ | k < ‖b.μ z‖} := by
        ext z; simp [not_le]
      rwa [hset] at h2
    exact absurd hnull (hopen.measure_pos volume ⟨z₀, hz₀⟩).ne'
  -- ===== 2. continuity toolkit for Wirtinger derivatives =====
  have hdifff : ∀ z, DifferentiableAt ℝ f z :=
    fun z => hf1.differentiable one_ne_zero z
  have happly_cont : ∀ F : ℂ → ℂ, Continuous (fun z => fderiv ℝ F z) →
      Continuous (fun z => dz F z) ∧ Continuous (fun z => dzbar F z) := by
    intro F hF
    have h2 : Continuous (fun z => (fderiv ℝ F z) 1) :=
      ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous).comp hF
    have h3 : Continuous (fun z => (fderiv ℝ F z) Complex.I) :=
      ((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp hF
    constructor
    · have h4 : (fun z => dz F z)
          = fun z => (1 / 2 : ℂ)
              * ((fderiv ℝ F z) 1 - Complex.I * (fderiv ℝ F z) Complex.I) := by
        funext z; rw [dz]
      rw [h4]
      exact continuous_const.mul (h2.sub (continuous_const.mul h3))
    · have h4 : (fun z => dzbar F z)
          = fun z => (1 / 2 : ℂ)
              * ((fderiv ℝ F z) 1 + Complex.I * (fderiv ℝ F z) Complex.I) := by
        funext z; rw [dzbar]
      rw [h4]
      exact continuous_const.mul (h2.add (continuous_const.mul h3))
  have hfd_cont : Continuous (fun z => fderiv ℝ f z) := (contDiff_one_iff_fderiv.mp hf1).2
  have hdzf_cont : Continuous (fun z => dz f z) := (happly_cont f hfd_cont).1
  have hdzbarf_cont : Continuous (fun z => dzbar f z) := (happly_cont f hfd_cont).2
  -- ===== 3. nonvanishing of `∂f` and the complex Jacobian =====
  have hdzf_ne : ∀ z, dz f z ≠ 0 := by
    intro z hz
    have h1 := hdet z
    rw [det_fderiv_eq_wirtinger, hz] at h1
    simp only [norm_zero] at h1
    nlinarith [sq_nonneg ‖dzbar f z‖]
  have hconj_ne : ∀ z, (starRingEnd ℂ) (dz f z) ≠ 0 := by
    intro z hz
    rw [starRingEnd_apply, star_eq_zero] at hz
    exact hdzf_ne z hz
  have hJC : ∀ z, dz f z * (starRingEnd ℂ) (dz f z)
      - dzbar f z * (starRingEnd ℂ) (dzbar f z) = ((fderiv ℝ f z).det : ℂ) := by
    intro z
    rw [Complex.mul_conj, Complex.mul_conj, det_fderiv_eq_wirtinger,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hDneC : ∀ z, ((fderiv ℝ f z).det : ℂ) ≠ 0 :=
    fun z => Complex.ofReal_ne_zero.mpr (hdet z).ne'
  -- ===== 4. the inverse is `C¹` =====
  have hg1 : ContDiff ℝ 1 g := by
    have hcle : ∀ a : ℂ, ∃ e : ℂ ≃L[ℝ] ℂ, (e : ℂ →L[ℝ] ℂ) = fderiv ℝ f a := by
      intro a
      have hAdet : LinearMap.det ((fderiv ℝ f a : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) ≠ 0 :=
        (hdet a).ne'
      refine ⟨(LinearMap.equivOfDetNeZero ((fderiv ℝ f a : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)
          hAdet).toContinuousLinearEquiv, ?_⟩
      ext v
      simp
    choose eqv heqv using hcle
    have hfd : ∀ a : ℂ, HasFDerivAt (⇑G) ((eqv a : ℂ →L[ℝ] ℂ)) a := by
      intro a
      rw [hGcoe, heqv a]
      exact (hf1.differentiable one_ne_zero a).hasFDerivAt
    have hGC1 : ContDiff ℝ 1 ⇑G := by rw [hGcoe]; exact hf1
    rw [hgdef]
    exact G.contDiff_symm hfd hGC1
  have hdiffg : ∀ w, DifferentiableAt ℝ g w :=
    fun w => hg1.differentiable one_ne_zero w
  have hgfd_cont : Continuous (fun w => fderiv ℝ g w) := (contDiff_one_iff_fderiv.mp hg1).2
  have hdzg_cont : Continuous (fun w => dz g w) := (happly_cont g hgfd_cont).1
  have hdzbarg_cont : Continuous (fun w => dzbar g w) := (happly_cont g hgfd_cont).2
  -- ===== 5. Wirtinger derivatives of the identity, and the dictionary =====
  have hdzid : ∀ z : ℂ, dz (fun w : ℂ => w) z = 1 ∧ dzbar (fun w : ℂ => w) z = 0 := by
    intro z
    have hfd : fderiv ℝ (fun w : ℂ => w) z = ContinuousLinearMap.id ℝ ℂ := fderiv_fun_id
    constructor
    · rw [dz, hfd]
      simp only [ContinuousLinearMap.id_apply]
      linear_combination (-(1 / 2 : ℂ)) * Complex.I_mul_I
    · rw [dzbar, hfd]
      simp only [ContinuousLinearMap.id_apply]
      linear_combination ((1 / 2 : ℂ)) * Complex.I_mul_I
  have hdict : ∀ (F : ℂ → ℂ) (z : ℂ), (fderiv ℝ F z) 1 = dz F z + dzbar F z ∧
      (fderiv ℝ F z) Complex.I = Complex.I * (dz F z - dzbar F z) := by
    intro F z
    constructor
    · rw [dz, dzbar]; ring
    · rw [dz, dzbar]
      linear_combination ((fderiv ℝ F z) Complex.I) * Complex.I_mul_I
  -- ===== 6. chain rule: the Wirtinger derivatives of the inverse =====
  have hcompid : (fun x : ℂ => f (g x)) = fun x : ℂ => x := funext hfg
  have hchain1 : ∀ w, dz f (g w) * dz g w
      + dzbar f (g w) * (starRingEnd ℂ) (dzbar g w) = 1 := by
    intro w
    have h0 := dz_comp (hdiffg w) (hdifff (g w))
    rw [hcompid, (hdzid w).1] at h0
    exact h0.symm
  have hchain2 : ∀ w, dz f (g w) * dzbar g w
      + dzbar f (g w) * (starRingEnd ℂ) (dz g w) = 0 := by
    intro w
    have h0 := dzbar_comp (hdiffg w) (hdifff (g w))
    rw [hcompid, (hdzid w).2] at h0
    exact h0.symm
  have hdzg : ∀ w, dz g w
      = (starRingEnd ℂ) (dz f (g w)) / ((fderiv ℝ f (g w)).det : ℂ) := by
    intro w
    have h1 := hchain1 w
    have h2 := hchain2 w
    have hD := hJC (g w)
    have hDne := hDneC (g w)
    have hconj2 : (starRingEnd ℂ) (dz f (g w)) * (starRingEnd ℂ) (dzbar g w)
        + (starRingEnd ℂ) (dzbar f (g w)) * dz g w = 0 := by
      have h3 := congrArg (starRingEnd ℂ) h2
      simpa [map_add, map_mul] using h3
    rw [eq_div_iff hDne]
    linear_combination (starRingEnd ℂ) (dz f (g w)) * h1
      - dzbar f (g w) * hconj2 - dz g w * hD
  have hdzbarg : ∀ w, dzbar g w
      = -(dzbar f (g w)) / ((fderiv ℝ f (g w)).det : ℂ) := by
    intro w
    have h1 := hchain1 w
    have h2 := hchain2 w
    have hD := hJC (g w)
    have hDne := hDneC (g w)
    have hconj1 : (starRingEnd ℂ) (dz f (g w)) * (starRingEnd ℂ) (dz g w)
        + (starRingEnd ℂ) (dzbar f (g w)) * dzbar g w = 1 := by
      have h3 := congrArg (starRingEnd ℂ) h1
      simpa [map_add, map_mul] using h3
    rw [eq_div_iff hDne]
    linear_combination (starRingEnd ℂ) (dz f (g w)) * h2
      - dzbar f (g w) * hconj1 - dzbar g w * hD
  -- ===== 7. pointwise Beltrami equation for `f` =====
  have hbelt : ∀ z, dzbar f z = b.μ z * dz f z := by
    obtain ⟨p₀, h₀, R₀, hp₀, hp₀', hmem₀, hsupp₀, heq₀, hrepr₀⟩ := hf
    have hp₀1 : (1 : ℝ≥0∞) ≤ p₀ := le_of_lt (lt_trans ENNReal.one_lt_two hp₀)
    have hPh₀fun : cauchyTransform h₀ = fun z => f z - z := by
      funext z; rw [hrepr₀ z]; ring
    have hPh₀C1 : ContDiff ℝ 1 (cauchyTransform h₀) := by
      rw [hPh₀fun]; exact hf1.sub contDiff_id
    have hwg₀ := hasWeakGradient_cauchyTransform hp₀ hp₀' hmem₀ hsupp₀
    have hSh₀mem : MemLp (beurling h₀) p₀ volume := memLp_beurling_of_memLp hp₀ hp₀' hmem₀
    have hfdPh₀_cont : Continuous (fun z => fderiv ℝ (cauchyTransform h₀) z) :=
      (contDiff_one_iff_fderiv.mp hPh₀C1).2
    have hclx_cont : Continuous (fun z => (fderiv ℝ (cauchyTransform h₀) z) 1) :=
      ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous).comp hfdPh₀_cont
    have hcly_cont : Continuous (fun z => (fderiv ℝ (cauchyTransform h₀) z) Complex.I) :=
      ((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp hfdPh₀_cont
    have haex := HasWeakDirDeriv.ae_eq isOpen_univ
      (HasWeakDirDeriv.of_contDiffOn isOpen_univ hPh₀C1.contDiffOn) hwg₀.1
      (locallyIntegrableOn_univ.mpr hclx_cont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr ((hSh₀mem.add hmem₀).locallyIntegrable hp₀1))
    have haey := HasWeakDirDeriv.ae_eq isOpen_univ
      (HasWeakDirDeriv.of_contDiffOn isOpen_univ hPh₀C1.contDiffOn) hwg₀.2
      (locallyIntegrableOn_univ.mpr hcly_cont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr
        (((hSh₀mem.sub hmem₀).const_mul Complex.I).locallyIntegrable hp₀1))
    have hff : f = fun w => w + cauchyTransform h₀ w := funext hrepr₀
    have haeBelt : (fun z => dzbar f z) =ᵐ[volume] (fun z => b.μ z * dz f z) := by
      filter_upwards [haex, haey, heq₀] with z hx hy heqz
      have hx' : (fderiv ℝ (cauchyTransform h₀) z) 1 = beurling h₀ z + h₀ z :=
        hx (Set.mem_univ z)
      have hy' : (fderiv ℝ (cauchyTransform h₀) z) Complex.I
          = Complex.I * (beurling h₀ z - h₀ z) := hy (Set.mem_univ z)
      have hidd : DifferentiableAt ℝ (fun w : ℂ => w) z := differentiable_id.differentiableAt
      have hPd : DifferentiableAt ℝ (cauchyTransform h₀) z :=
        hPh₀C1.differentiable one_ne_zero z
      have hdzbarfz : dzbar f z = h₀ z := by
        rw [hff, dzbar_add hidd hPd, (hdzid z).2, zero_add, dzbar, hx', hy']
        linear_combination ((1 / 2 : ℂ) * (beurling h₀ z - h₀ z)) * Complex.I_mul_I
      have hdzfz : dz f z = 1 + beurling h₀ z := by
        rw [hff, dz_add hidd hPd, (hdzid z).1, dz, hx', hy']
        linear_combination (-(1 / 2 : ℂ) * (beurling h₀ z - h₀ z)) * Complex.I_mul_I
      rw [hdzbarfz, hdzfz, heqz]
      ring
    have hEq := (Continuous.ae_eq_iff_eq volume hdzbarf_cont
      (hμs.continuous.mul hdzf_cont)).mp haeBelt
    intro z
    exact congrFun hEq z
  -- ===== 8. the inverse coefficient =====
  set μν : ℂ → ℂ :=
    fun w => -(b.μ (g w) * dz f (g w) / (starRingEnd ℂ) (dz f (g w))) with hμνdef
  have hμν_cont : Continuous μν := by
    rw [hμνdef]
    refine Continuous.neg (Continuous.div ?_ ?_ ?_)
    · exact (hμs.continuous.comp hgc).mul (hdzf_cont.comp hgc)
    · exact Complex.continuous_conj.comp (hdzf_cont.comp hgc)
    · intro w
      exact hconj_ne (g w)
  have hμν_norm : ∀ w, ‖μν w‖ = ‖b.μ (g w)‖ := by
    intro w
    rw [hμνdef]
    rw [norm_neg, norm_div, norm_mul, RCLike.norm_conj, mul_div_assoc,
      div_self (norm_ne_zero_iff.mpr (hdzf_ne (g w))), mul_one]
  have hμν_essSup : eLpNormEssSup μν volume ≤ eLpNormEssSup b.μ volume := by
    have h1 : ∀ᵐ w ∂(volume : Measure ℂ), ‖μν w‖ ≤ k :=
      Filter.Eventually.of_forall (fun w => (hμν_norm w) ▸ hμpt (g w))
    have h2 := eLpNormEssSup_le_of_ae_bound (μ := (volume : Measure ℂ)) h1
    rwa [hkdef, ENNReal.ofReal_toReal hkfin] at h2
  have himg_cpt : IsCompact (f '' tsupport b.μ) := hμc.isCompact.image hcont
  have hgw_supp : ∀ w, w ∉ f '' tsupport b.μ → b.μ (g w) = 0 := by
    intro w hw
    by_contra hne
    exact hw ⟨g w, subset_tsupport _ (Function.mem_support.mpr hne), hfg w⟩
  have hμν_zero : ∀ w, w ∉ f '' tsupport b.μ → μν w = 0 := by
    intro w hw
    rw [hμνdef]
    simp only [hgw_supp w hw, zero_mul, zero_div, neg_zero]
  refine ⟨⟨μν, hμν_cont.measurable, lt_of_le_of_lt hμν_essSup b.bound⟩,
    fun w => rfl, hμν_essSup, ?_, ?_, ?_⟩
  · exact HasCompactSupport.intro himg_cpt hμν_zero
  · intro w hw
    by_contra hmem
    exact hw (hμν_zero w hmem)
  · -- ===== 9. the inverse is the principal solution of `ν` =====
    -- The canonical field of the inverse: `h = ∂̄g`, continuous with compact
    -- support in the image of `supp μ`.
    have hbeltg : ∀ w, dzbar g w = μν w * dz g w := by
      intro w
      have hca := hconj_ne (g w)
      have hD := hDneC (g w)
      rw [hdzbarg w, hdzg w, hbelt (g w)]
      simp only [hμνdef]
      field_simp
    obtain ⟨R₂, hR₂⟩ : ∃ r : ℝ, f '' tsupport b.μ ⊆ Metric.closedBall 0 r :=
      himg_cpt.isBounded.subset_closedBall 0
    have hfar_notmem : ∀ w : ℂ, R₂ < ‖w‖ → w ∉ f '' tsupport b.μ := by
      intro w hw hmem
      have h2 := hR₂ hmem
      rw [Metric.mem_closedBall, dist_zero_right] at h2
      exact absurd h2 (not_le.mpr hw)
    have hg_van : ∀ w : ℂ, R₂ < ‖w‖ → dzbar g w = 0 := by
      intro w hw
      have h0 : b.μ (g w) = 0 := hgw_supp w (hfar_notmem w hw)
      rw [hdzbarg w, hbelt (g w), h0, zero_mul, neg_zero, zero_div]
    have hg_cs : HasCompactSupport (fun w => dzbar g w) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R₂) ?_
      intro w hw
      refine hg_van w ?_
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hw
      exact hw
    have hp4 : (2 : ℝ≥0∞) < 4 := by norm_num
    have hp4' : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have h14 : (1 : ℝ≥0∞) ≤ 4 := by norm_num
    have hg_mem : MemLp (fun w => dzbar g w) 4 volume :=
      hdzbarg_cont.memLp_of_hasCompactSupport hg_cs
    have hSg_mem : MemLp (beurling (fun w => dzbar g w)) 4 volume :=
      memLp_beurling_of_memLp hp4 hp4' hg_mem
    have hPg_cont : Continuous (cauchyTransform (fun w => dzbar g w)) :=
      continuous_cauchyTransform_of_memLp_of_support hp4 hp4' hg_mem hg_van
    have hwg_g := hasWeakGradient_cauchyTransform hp4 hp4' hg_mem hg_van
    have hweyl : ∀ (f gx gy : ℂ → ℂ), Continuous f →
        HasWeakDirDeriv 1 gx f Set.univ → HasWeakDirDeriv Complex.I gy f Set.univ →
        LocallyIntegrable gx → LocallyIntegrable gy →
        (∀ z, gx z + Complex.I * gy z = 0) →
        Differentiable ℂ f := by
      intro f gx gy hfcont hwgx hwgy hgxLI hgyLI hcombpt
      have hfloc : LocallyIntegrable f := hfcont.locallyIntegrable
      have hcomb : ∀ᵐ z ∂(volume : Measure ℂ), gx z + Complex.I * gy z = 0 :=
        Filter.Eventually.of_forall hcombpt
      set φb : ℕ → ContDiffBump (0 : ℂ) := fun n =>
        { rIn := 1 / (n + 2), rOut := 2 / (n + 2),
          rIn_pos := by positivity,
          rIn_lt_rOut := by
            rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num } with hφbdef
      have hφrout : Tendsto (fun n => (φb n).rOut) atTop (𝓝 0) := by
        have h2 : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
          apply Tendsto.div_atTop tendsto_const_nhds
          exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
        simpa [hφbdef] using h2
      set ρ : ℕ → ℂ → ℝ := fun n => (φb n).normed volume with hρdef
      set fn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution (ρ n) f
        (ContinuousLinearMap.lsmul ℝ ℝ) volume with hfndef
      have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
        (φb n).contDiff_normed (n := ⊤)
      have hρsupp : ∀ n, HasCompactSupport (ρ n) := fun n => (φb n).hasCompactSupport_normed
      have hρcont : ∀ n, Continuous (ρ n) := fun n => (hρsm n).continuous
      have hA1x : ∀ n z, (fderiv ℝ (fn n) z) (1 : ℂ)
          = MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z :=
        fun n z => fderiv_convolution_normed_apply_eq hwgx hfloc hgxLI (hρsm n) (hρsupp n) z
      have hA1y : ∀ n z, (fderiv ℝ (fn n) z) Complex.I
          = MeasureTheory.convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z :=
        fun n z => fderiv_convolution_normed_apply_eq hwgy hfloc hgyLI (hρsm n) (hρsupp n) z
      have hexx : ∀ n, MeasureTheory.ConvolutionExists (ρ n) gx
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := fun n =>
        (hρsupp n).convolutionExists_left _ (hρcont n) hgxLI
      have hexy : ∀ n, MeasureTheory.ConvolutionExists (ρ n) gy
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := fun n =>
        (hρsupp n).convolutionExists_left _ (hρcont n) hgyLI
      have hfn_holo : ∀ n, DifferentiableOn ℂ (fn n) Set.univ := by
        intro n
        have hfn_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fn n) :=
          (hρsupp n).contDiff_convolution_left _ (hρsm n) hfloc
        have hfn_diffR : ∀ z, DifferentiableAt ℝ (fn n) z := fun z =>
          (hfn_smooth.differentiable (by simp)).differentiableAt
        have hdzbar0 : ∀ z, dzbar (fn n) z = 0 := by
          intro z
          have hval : dzbar (fn n) z
              = (1 / 2 : ℂ) *
                (MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                  + Complex.I * MeasureTheory.convolution (ρ n) gy
                    (ContinuousLinearMap.lsmul ℝ ℝ) volume z) := by
            rw [dzbar, hA1x n z, hA1y n z]
          have hzero : MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ)
                volume z
              + Complex.I * MeasureTheory.convolution (ρ n) gy
                (ContinuousLinearMap.lsmul ℝ ℝ) volume z = 0 := by
            set Fx : ℂ → ℂ := fun t => (ContinuousLinearMap.lsmul ℝ ℝ (ρ n t)) (gx (z - t))
              with hFx
            set Fy : ℂ → ℂ := fun t => (ContinuousLinearMap.lsmul ℝ ℝ (ρ n t)) (gy (z - t))
              with hFy
            have hcx : MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ)
                volume z = ∫ t, Fx t := rfl
            have hcy : MeasureTheory.convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ)
                volume z = ∫ t, Fy t := rfl
            rw [hcx, hcy]
            have hIint : Complex.I * ∫ t, Fy t = ∫ t, Complex.I * Fy t :=
              (MeasureTheory.integral_const_mul Complex.I Fy).symm
            rw [hIint]
            have hix : MeasureTheory.Integrable Fx volume := (hexx n z)
            have hiy : MeasureTheory.Integrable (fun t => Complex.I * Fy t) volume :=
              (hexy n z).const_mul Complex.I
            rw [← MeasureTheory.integral_add hix hiy]
            refine MeasureTheory.integral_eq_zero_of_ae ?_
            have hshift : ∀ᵐ t ∂(volume : Measure ℂ),
                gx (z - t) + Complex.I * gy (z - t) = 0 := by
              have hmp : MeasureTheory.MeasurePreserving (fun t : ℂ => z - t)
                  (volume : Measure ℂ) volume :=
                (volume : Measure ℂ).measurePreserving_sub_left z
              exact hmp.quasiMeasurePreserving.ae hcomb
            filter_upwards [hshift] with t ht
            simp only [hFx, hFy, ContinuousLinearMap.lsmul_apply, Pi.zero_apply]
            rw [mul_smul_comm, ← smul_add, ht, smul_zero]
          rw [hval, hzero, mul_zero]
        refine (differentiableOn_iff_dzbar_eq_zero isOpen_univ ?_).mpr (fun z _ => hdzbar0 z)
        exact fun z _ => (hfn_diffR z).differentiableWithinAt
      have hTLU : TendstoLocallyUniformlyOn fn f atTop Set.univ := by
        rw [tendstoLocallyUniformlyOn_univ]
        refine tendstoLocallyUniformly_of_forall_exists_nhds (fun x => ?_)
        refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
        have hUC : UniformContinuousOn f (Metric.closedBall x 2) :=
          (isCompact_closedBall x 2).uniformContinuousOn_of_continuous hfcont.continuousOn
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        have hε2 : (0 : ℝ) < ε / 2 := by positivity
        obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hUC (ε / 2) hε2
        have hev : ∀ᶠ n in atTop, (φb n).rOut < min δ 1 := by
          have := hφrout.eventually (eventually_lt_nhds (show (0 : ℝ) < min δ 1 by positivity))
          filter_upwards [this] with n hn using hn
        filter_upwards [hev] with n hn z hz
        have hrout_le_one : (φb n).rOut ≤ 1 := (lt_of_lt_of_le hn (min_le_right δ 1)).le
        have hrout_le_δ : (φb n).rOut ≤ δ := (lt_of_lt_of_le hn (min_le_left δ 1)).le
        have hsupp2 : Function.support (ρ n) ⊆ Metric.ball (0 : ℂ) (φb n).rOut := by
          rw [hρdef, (φb n).support_normed_eq]
        have hnf : ∀ y, 0 ≤ ρ n y := fun y => (φb n).nonneg_normed y
        have hintf : ∫ y, ρ n y ∂volume = 1 := (φb n).integral_normed
        have hclose : ∀ y ∈ Metric.ball z (φb n).rOut, dist (f y) (f z) ≤ ε / 2 := by
          intro y hy
          have hzmem : z ∈ Metric.closedBall x 2 :=
            Metric.closedBall_subset_closedBall (by norm_num) hz
          rw [Metric.mem_ball] at hy
          have hymem : y ∈ Metric.closedBall x 2 := by
            rw [Metric.mem_closedBall] at hz ⊢
            calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
              _ ≤ (φb n).rOut + 1 := by gcongr
              _ ≤ 1 + 1 := by gcongr
              _ = 2 := by norm_num
          exact (hδ y hymem z hzmem (hy.trans_le hrout_le_δ)).le
        calc dist (f z) (fn n z) = dist (fn n z) (f z) := dist_comm _ _
          _ ≤ ε / 2 := dist_convolution_le hε2.le hsupp2 hnf hintf
                hfcont.aestronglyMeasurable hclose
          _ < ε := by linarith
      have hdiffOn : DifferentiableOn ℂ f Set.univ :=
        hTLU.differentiableOn (Filter.Eventually.of_forall hfn_holo) isOpen_univ
      rw [← differentiableOn_univ]
      exact hdiffOn
    -- ===== the comparison function `u = g − (id + P(∂̄g))` =====
    set u : ℂ → ℂ := fun w => g w - (w + cauchyTransform (fun x => dzbar g x) w)
      with hu_def
    have hu_cont : Continuous u := by
      rw [hu_def]
      exact hgc.sub (continuous_id.add hPg_cont)
    -- weak gradients
    have hwgx_g : HasWeakDirDeriv 1 (fun z => (fderiv ℝ g z) 1) g Set.univ :=
      HasWeakDirDeriv.of_contDiffOn isOpen_univ hg1.contDiffOn
    have hwgy_g : HasWeakDirDeriv Complex.I (fun z => (fderiv ℝ g z) Complex.I) g
        Set.univ :=
      HasWeakDirDeriv.of_contDiffOn isOpen_univ hg1.contDiffOn
    have hidC : ContDiffOn ℝ 1 (fun z : ℂ => z) Set.univ := contDiffOn_id
    have hid1 := HasWeakDirDeriv.of_contDiffOn (v := 1) isOpen_univ hidC
    have hidI := HasWeakDirDeriv.of_contDiffOn (v := Complex.I) isOpen_univ hidC
    have hfder1 : (fun z : ℂ => (fderiv ℝ (fun z : ℂ => z) z) 1) = fun _ : ℂ => (1:ℂ) := by
      funext z
      rw [fderiv_fun_id]
      rfl
    have hfderI : (fun z : ℂ => (fderiv ℝ (fun z : ℂ => z) z) Complex.I)
        = fun _ : ℂ => Complex.I := by
      funext z
      rw [fderiv_fun_id]
      rfl
    rw [hfder1] at hid1
    rw [hfderI] at hidI
    have hLIid : LocallyIntegrableOn (fun z : ℂ => z) Set.univ :=
      continuous_id.locallyIntegrable.locallyIntegrableOn _
    have hLIP : LocallyIntegrableOn (cauchyTransform (fun x => dzbar g x)) Set.univ :=
      hPg_cont.locallyIntegrable.locallyIntegrableOn _
    have hLI1 : LocallyIntegrableOn (fun _ : ℂ => (1:ℂ)) Set.univ :=
      continuous_const.locallyIntegrable.locallyIntegrableOn _
    have hLII : LocallyIntegrableOn (fun _ : ℂ => Complex.I) Set.univ :=
      continuous_const.locallyIntegrable.locallyIntegrableOn _
    have hLIgx : LocallyIntegrableOn
        (fun z => beurling (fun x => dzbar g x) z + dzbar g z) Set.univ :=
      ((hSg_mem.add hg_mem).locallyIntegrable h14).locallyIntegrableOn _
    have hLIgy : LocallyIntegrableOn
        (fun z => Complex.I * (beurling (fun x => dzbar g x) z - dzbar g z)) Set.univ :=
      (((hSg_mem.sub hg_mem).const_mul Complex.I).locallyIntegrable h14).locallyIntegrableOn _
    have hwF0x := HasWeakDirDeriv.add hid1 hwg_g.1 hLIid hLIP hLI1 hLIgx
    have hwF0y := HasWeakDirDeriv.add hidI hwg_g.2 hLIid hLIP hLII hLIgy
    have hLIg : LocallyIntegrableOn g Set.univ :=
      hgc.locallyIntegrable.locallyIntegrableOn _
    have hLIF0 : LocallyIntegrableOn
        (fun z : ℂ => z + cauchyTransform (fun x => dzbar g x) z) Set.univ :=
      (continuous_id.add hPg_cont).locallyIntegrable.locallyIntegrableOn _
    have hLIgx_g : LocallyIntegrableOn (fun z => (fderiv ℝ g z) 1) Set.univ :=
      ((((ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).continuous).comp
        hgfd_cont).locallyIntegrable).locallyIntegrableOn _
    have hLIgy_g : LocallyIntegrableOn (fun z => (fderiv ℝ g z) Complex.I) Set.univ :=
      ((((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp
        hgfd_cont).locallyIntegrable).locallyIntegrableOn _
    have hLIF0x : LocallyIntegrableOn
        (fun z => (1:ℂ) + (beurling (fun x => dzbar g x) z + dzbar g z)) Set.univ := by
      have h1 : LocallyIntegrable (fun _ : ℂ => (1:ℂ)) volume :=
        continuous_const.locallyIntegrable
      have h2 : LocallyIntegrable
          (fun z => beurling (fun x => dzbar g x) z + dzbar g z) volume :=
        (hSg_mem.add hg_mem).locallyIntegrable h14
      exact (h1.add h2).locallyIntegrableOn _
    have hLIF0y : LocallyIntegrableOn
        (fun z => Complex.I
          + Complex.I * (beurling (fun x => dzbar g x) z - dzbar g z)) Set.univ := by
      have h1 : LocallyIntegrable (fun _ : ℂ => Complex.I) volume :=
        continuous_const.locallyIntegrable
      have h2 : LocallyIntegrable
          (fun z => Complex.I * (beurling (fun x => dzbar g x) z - dzbar g z)) volume :=
        ((hSg_mem.sub hg_mem).const_mul Complex.I).locallyIntegrable h14
      exact (h1.add h2).locallyIntegrableOn _
    have hwux := HasWeakDirDeriv.sub hwgx_g hwF0x hLIg hLIF0 hLIgx_g hLIF0x
    have hwuy := HasWeakDirDeriv.sub hwgy_g hwF0y hLIg hLIF0 hLIgy_g hLIF0y
    have hLIux : LocallyIntegrable (fun z => (fderiv ℝ g z) 1
        - ((1:ℂ) + (beurling (fun x => dzbar g x) z + dzbar g z))) volume := by
      have h1 : LocallyIntegrable (fun z => (fderiv ℝ g z) 1) volume :=
        (((ContinuousLinearMap.apply ℝ ℂ (1:ℂ)).continuous).comp hgfd_cont).locallyIntegrable
      have h2 : LocallyIntegrable
          (fun z => (1:ℂ) + (beurling (fun x => dzbar g x) z + dzbar g z)) volume := by
        have h3 : LocallyIntegrable (fun _ : ℂ => (1:ℂ)) volume :=
          continuous_const.locallyIntegrable
        have h4 : LocallyIntegrable
            (fun z => beurling (fun x => dzbar g x) z + dzbar g z) volume :=
          (hSg_mem.add hg_mem).locallyIntegrable h14
        exact h3.add h4
      exact h1.sub h2
    have hLIuy : LocallyIntegrable (fun z => (fderiv ℝ g z) Complex.I
        - (Complex.I + Complex.I * (beurling (fun x => dzbar g x) z - dzbar g z)))
        volume := by
      have h1 : LocallyIntegrable (fun z => (fderiv ℝ g z) Complex.I) volume :=
        (((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp
          hgfd_cont).locallyIntegrable
      have h2 : LocallyIntegrable
          (fun z => Complex.I
            + Complex.I * (beurling (fun x => dzbar g x) z - dzbar g z)) volume := by
        have h3 : LocallyIntegrable (fun _ : ℂ => Complex.I) volume :=
          continuous_const.locallyIntegrable
        have h4 : LocallyIntegrable
            (fun z => Complex.I * (beurling (fun x => dzbar g x) z - dzbar g z)) volume :=
          ((hSg_mem.sub hg_mem).const_mul Complex.I).locallyIntegrable h14
        exact h3.add h4
      exact h1.sub h2
    have hcombpt : ∀ z, ((fderiv ℝ g z) 1
        - ((1:ℂ) + (beurling (fun x => dzbar g x) z + dzbar g z)))
        + Complex.I * ((fderiv ℝ g z) Complex.I
          - (Complex.I + Complex.I * (beurling (fun x => dzbar g x) z - dzbar g z)))
        = 0 := by
      intro z
      rw [(hdict g z).1, (hdict g z).2]
      linear_combination (dz g z - 1 - beurling (fun x => dzbar g x) z) * Complex.I_mul_I
    have hu_ent : Differentiable ℂ u :=
      hweyl u _ _ hu_cont hwux hwuy hLIux hLIuy hcombpt
    -- ===== `u → 0` cocompactly, hence `u ≡ 0` by Liouville =====
    have hdecay : Tendsto (fun z => f z - z) (cocompact ℂ) (𝓝 0) :=
      hf.tendsto_sub_id_cocompact
    have hgproper : Tendsto g (cocompact ℂ) (cocompact ℂ) := by
      have h1 : IsProperMap g := by
        rw [hgdef]
        exact G.symm.isProperMap
      exact (isProperMap_iff_tendsto_cocompact.mp h1).2
    have ht1 : Tendsto (fun w => g w - w) (cocompact ℂ) (𝓝 0) := by
      have h3 : Tendsto (fun z => -(f z - z)) (cocompact ℂ) (𝓝 0) := by
        have h4 := hdecay.neg
        rwa [neg_zero] at h4
      have h2 : Tendsto ((fun z => -(f z - z)) ∘ g) (cocompact ℂ) (𝓝 0) :=
        h3.comp hgproper
      refine h2.congr ?_
      intro w
      simp only [Function.comp_apply]
      rw [hfg w]
      ring
    have ht2 : Tendsto (cauchyTransform (fun x => dzbar g x)) (cocompact ℂ) (𝓝 0) :=
      cauchyTransform_tendsto_cocompact hp4 hp4' hg_mem hg_van
    have hu0 : Tendsto u (cocompact ℂ) (𝓝 0) := by
      have h2 := ht1.sub ht2
      rw [sub_zero] at h2
      refine h2.congr ?_
      intro w
      simp only [hu_def]
      ring
    have hubdd : Bornology.IsBounded (Set.range u) := by
      have h1 : ∀ᶠ z in Filter.cocompact ℂ, u z ∈ Metric.closedBall (0 : ℂ) 1 :=
        hu0 (Metric.closedBall_mem_nhds 0 one_pos)
      rw [Filter.eventually_iff, Filter.mem_cocompact] at h1
      obtain ⟨K, hKc, hKsub⟩ := h1
      have h2 : Set.range u ⊆ (u '' K) ∪ Metric.closedBall (0 : ℂ) 1 := by
        rintro _ ⟨z, rfl⟩
        by_cases hz : z ∈ K
        · exact Or.inl ⟨z, hz, rfl⟩
        · exact Or.inr (hKsub hz)
      exact (((hKc.image hu_cont).isBounded).union Metric.isBounded_closedBall).subset h2
    have hu_zero : ∀ z, u z = 0 := by
      intro z
      have hconst : ∀ w, u w = u z := fun w => hu_ent.apply_eq_apply_of_bounded hubdd w z
      have hc' : Tendsto u (Filter.cocompact ℂ) (𝓝 (u z)) := by
        have hfe : u = fun _ => u z := funext hconst
        rw [hfe]
        exact tendsto_const_nhds
      exact tendsto_nhds_unique hc' hu0
    have hrepr_g : ∀ w, g w = w + cauchyTransform (fun x => dzbar g x) w := by
      intro w
      have h0 := hu_zero w
      simp only [hu_def] at h0
      linear_combination h0
    -- ===== the a.e. fixed-point equation for the inverse field =====
    have hPgfun : cauchyTransform (fun x => dzbar g x) = fun w => g w - w := by
      funext w
      rw [hrepr_g w]
      ring
    have hPgC1 : ContDiff ℝ 1 (cauchyTransform (fun x => dzbar g x)) := by
      rw [hPgfun]
      exact hg1.sub contDiff_id
    have hfdPg_cont : Continuous
        (fun z => fderiv ℝ (cauchyTransform (fun x => dzbar g x)) z) :=
      (contDiff_one_iff_fderiv.mp hPgC1).2
    have hclxg_cont : Continuous
        (fun z => (fderiv ℝ (cauchyTransform (fun x => dzbar g x)) z) 1) :=
      ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous).comp hfdPg_cont
    have hclyg_cont : Continuous
        (fun z => (fderiv ℝ (cauchyTransform (fun x => dzbar g x)) z) Complex.I) :=
      ((ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous).comp hfdPg_cont
    have haex_g := HasWeakDirDeriv.ae_eq isOpen_univ
      (HasWeakDirDeriv.of_contDiffOn isOpen_univ hPgC1.contDiffOn) hwg_g.1
      (locallyIntegrableOn_univ.mpr hclxg_cont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr ((hSg_mem.add hg_mem).locallyIntegrable h14))
    have haey_g := HasWeakDirDeriv.ae_eq isOpen_univ
      (HasWeakDirDeriv.of_contDiffOn isOpen_univ hPgC1.contDiffOn) hwg_g.2
      (locallyIntegrableOn_univ.mpr hclyg_cont.locallyIntegrable)
      (locallyIntegrableOn_univ.mpr
        (((hSg_mem.sub hg_mem).const_mul Complex.I).locallyIntegrable h14))
    have heq_g : (fun w => dzbar g w) =ᵐ[volume]
        (fun w => μν w * beurling (fun x => dzbar g x) w + μν w) := by
      filter_upwards [haex_g, haey_g] with w hx hy
      have hx' : (fderiv ℝ (cauchyTransform (fun x => dzbar g x)) w) 1
          = beurling (fun x => dzbar g x) w + dzbar g w := hx (Set.mem_univ w)
      have hy' : (fderiv ℝ (cauchyTransform (fun x => dzbar g x)) w) Complex.I
          = Complex.I * (beurling (fun x => dzbar g x) w - dzbar g w) :=
        hy (Set.mem_univ w)
      have hgfun2 : g = fun x => x + cauchyTransform (fun y => dzbar g y) x :=
        funext hrepr_g
      have hidd : DifferentiableAt ℝ (fun x : ℂ => x) w := differentiable_id.differentiableAt
      have hPd : DifferentiableAt ℝ (cauchyTransform (fun x => dzbar g x)) w :=
        hPgC1.differentiable one_ne_zero w
      have hdzg_ae : dz g w = 1 + beurling (fun x => dzbar g x) w := by
        conv_lhs => rw [hgfun2]
        rw [dz_add hidd hPd, (hdzid w).1, dz, hx', hy']
        linear_combination (-(1 / 2 : ℂ)
          * (beurling (fun x => dzbar g x) w - dzbar g w)) * Complex.I_mul_I
      change dzbar g w = μν w * beurling (fun x => dzbar g x) w + μν w
      rw [hbeltg w, hdzg_ae]
      ring
    exact ⟨4, (fun w => dzbar g w), R₂, hp4, hp4', hg_mem, hg_van, heq_g, hrepr_g⟩

end NoWanderingDomains
