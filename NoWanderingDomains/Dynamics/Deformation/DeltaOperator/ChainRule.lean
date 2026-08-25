/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.Deformation.DeltaOperator.Basic

/-!
# Weak Wirtinger calculus: the chain rule

Precomposition with a holomorphic map transports a weak `∂̄`-derivative with
`L²_loc` gradient: the conformally invariant class `HasL2WeakDzbar` is stable
under holomorphic change of variables.

* `hasL2WeakDzbar_comp_holomorphic` — the chain rule.
-/

open MeasureTheory Complex Metric Filter Topology Polynomial OnePoint

namespace NoWanderingDomains

/-! ## Weak Wirtinger calculus: the chain rule -/

set_option maxHeartbeats 400000 in
-- The weak-Dzbar chain rule elaborates as one large declaration: many nested `have`
-- sub-lemmas (Wirtinger apply, Jacobian determinant, conformal L²_loc closure under
-- composition) exhaust the default heartbeat budget but finish within twice it.
open scoped ContDiff ENNReal in
/-- **Chain rule under a holomorphic map.** If `φ` is holomorphic on the open
set `Ω` and `v` is continuous with weak `∂̄`-derivative `μ` (and `L²_loc`
gradient) on all of `ℂ`, then `v ∘ φ` has weak `∂̄`-derivative
`(μ∘φ)·conj(φ′)` on `Ω`:

`∂̄(v∘φ) = (∂̄v)(φ)·conj(φ′)` a.e. on `Ω`

(the `(∂v)(φ)·∂̄φ` term vanishes since `φ` is holomorphic). The `L²_loc`
class survives composition by the conformal invariance of the Dirichlet
integral together with local boundedness of the covering multiplicity of a
holomorphic map; critical points of `φ` are isolated and are absorbed by the
a.e. formulation. -/
theorem hasL2WeakDzbar_comp_holomorphic {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {φ v μ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ Ω)
    (hv : Continuous v)
    (hgrad : HasL2WeakDzbar v μ Set.univ) :
    HasL2WeakDzbar (fun z => v (φ z))
      (fun z => μ (φ z) * starRingEnd ℂ (deriv φ z)) Ω := by
  have d1_locInt : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {g : ℂ → ℂ}
    (hg : MemLpLocOn g 2 Ω), LocallyIntegrableOn g Ω := by
    intro Ω hΩ g hg
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro k hk hkc
    have : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hkc.measure_lt_top⟩
    have h1le : (1 : ℝ≥0∞) ≤ 2 := by norm_num
    exact memLp_one_iff_integrable.mp ((hg k hk hkc).mono_exponent h1le)
  have d2_integ_real : ∀ {Ω : Set ℂ} (m : ℂ → ℝ) (hm : Continuous m)
    (hcsm : HasCompactSupport m) (htsuppm : tsupport m ⊆ Ω)
    {h : ℂ → ℂ} (hh : LocallyIntegrableOn h Ω), Integrable (fun z => m z • h z) volume := by
    intro Ω m hm hcsm htsuppm h hh
    have hK : IsCompact (tsupport m) := hcsm
    have hhon : IntegrableOn h (tsupport m) volume :=
      hh.integrableOn_compact_subset htsuppm hK
    have hon : IntegrableOn (fun z => m z • h z) (tsupport m) volume :=
      hhon.continuousOn_smul hm.continuousOn hK
    have hsupp : Function.support (fun z => m z • h z) ⊆ tsupport m := by
      intro z hz
      apply subset_tsupport m
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hon
  have e2_conj_eq : ∀ (ζ : ℂ), (starRingEnd ℂ) ζ = (ζ.re : ℂ) - (ζ.im : ℂ) * Complex.I := by
    intro ζ
    apply Complex.ext <;> simp
  have e1_wirtinger_apply : ∀ (L : ℂ →L[ℝ] ℂ) (ζ : ℂ),
      L ζ = (1 / 2 : ℂ) * (L 1 - Complex.I * L Complex.I) * ζ
        + (1 / 2 : ℂ) * (L 1 + Complex.I * L Complex.I) * ((starRingEnd ℂ) ζ) := by
    intro L ζ
    have hdec : ζ = ζ.re • (1 : ℂ) + ζ.im • Complex.I := by
      apply Complex.ext <;> simp [Complex.real_smul]
    have hLdec : L ζ = (ζ.re : ℂ) * L 1 + (ζ.im : ℂ) * L Complex.I := by
      conv_lhs => rw [hdec]
      rw [map_add, _root_.map_smul, _root_.map_smul]
      simp only [Complex.real_smul]
    have h1 : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
    have h2 := e2_conj_eq ζ
    linear_combination hLdec + (-(1 / 2 : ℂ) * (L 1 - Complex.I * L Complex.I)) * h1
      + (-(1 / 2 : ℂ) * (L 1 + Complex.I * L Complex.I)) * h2
      + ((ζ.im : ℂ) * L Complex.I) * Complex.I_mul_I
  have e3_det : ∀ (c : ℂ), (ContinuousLinearMap.mul ℝ ℂ c).det = Complex.normSq c := by
    intro c
    have h := LinearMap.det_toMatrix Complex.basisOneI
      ((ContinuousLinearMap.mul ℝ ℂ c : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)
    have hgoal : (ContinuousLinearMap.mul ℝ ℂ c).det
        = ((LinearMap.toMatrix Complex.basisOneI Complex.basisOneI)
            ((ContinuousLinearMap.mul ℝ ℂ c : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)).det := h.symm
    rw [hgoal, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply]
    rw [show Complex.basisOneI 0 = 1 by simp [Complex.coe_basisOneI],
      show Complex.basisOneI 1 = Complex.I by simp [Complex.coe_basisOneI]]
    simp only [Complex.coe_basisOneI_repr]
    change (c * 1).re * (c * Complex.I).im - (c * Complex.I).re * (c * 1).im
        = Complex.normSq c
    simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  have e4_inj_ball : ∀ {f : ℂ → ℂ} {a c : ℂ}
    (hf : HasStrictDerivAt f c a) (hc : c ≠ 0), ∃ r > 0, Set.InjOn f (Metric.ball a r) := by
    intro f a c hf hc
    have h := hf.eventually_left_inverse hc
    rw [Metric.eventually_nhds_iff_ball] at h
    obtain ⟨r, hr, hleft⟩ := h
    exact ⟨r, hr, fun x hx y hy hxy => by rw [← hleft x hx, ← hleft y hy, hxy]⟩
  have e5_fderiv_apply : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω), ∀ z ∈ Ω, ∀ e : ℂ, (fderiv ℝ φ z) e = deriv φ z * e := by
    intro Ω hΩ φ hφ z hz e
    have hdC : DifferentiableAt ℂ φ z := hφ.differentiableAt (hΩ.mem_nhds hz)
    obtain ⟨hr, hCR⟩ := differentiableAt_complex_iff_differentiableAt_real.mp hdC
    have h1 : (fderiv ℝ φ z) 1 = deriv φ z := by
      have hdz := dz_eq_deriv_of_differentiableAt hdC
      rw [dz, hCR, smul_eq_mul] at hdz
      linear_combination hdz + (1 / 2 : ℂ) * ((fderiv ℝ φ z) 1) * Complex.I_mul_I
    have hI : (fderiv ℝ φ z) Complex.I = Complex.I * deriv φ z := by
      rw [hCR, smul_eq_mul, h1]
    have hdec : e = e.re • (1 : ℂ) + e.im • Complex.I := by
      apply Complex.ext <;> simp [Complex.real_smul]
    calc (fderiv ℝ φ z) e
        = e.re • ((fderiv ℝ φ z) 1) + e.im • ((fderiv ℝ φ z) Complex.I) := by
          conv_lhs => rw [hdec]
          rw [map_add, _root_.map_smul, _root_.map_smul]
      _ = deriv φ z * e := by
          rw [h1, hI]
          simp only [Complex.real_smul]
          linear_combination (deriv φ z) * (Complex.re_add_im e)
  have e6_hasFDerivWithinAt : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω) {s : Set ℂ} (hs : s ⊆ Ω),
      ∀ z ∈ s, HasFDerivWithinAt φ (ContinuousLinearMap.mul ℝ ℂ (deriv φ z)) s z := by
    intro Ω hΩ φ hφ s hs z hz
    have hdC : DifferentiableAt ℂ φ z := hφ.differentiableAt (hΩ.mem_nhds (hs hz))
    have hdR : DifferentiableAt ℝ φ z :=
      (differentiableAt_complex_iff_differentiableAt_real.mp hdC).1
    have heq : fderiv ℝ φ z = ContinuousLinearMap.mul ℝ ℂ (deriv φ z) := by
      apply ContinuousLinearMap.ext
      intro w
      rw [e5_fderiv_apply hΩ hφ z (hs hz) w, ContinuousLinearMap.mul_apply']
    rw [← heq]
    exact hdR.hasFDerivAt.hasFDerivWithinAt
  have a_fiber_bound : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω) {p : ℂ} (hp : p ∈ Ω)
    (hnc : ¬ (∀ᶠ z in 𝓝 p, φ z = φ p)), ∃ r > 0, Metric.ball p r ⊆ Ω ∧ ∃ m : ℕ,
      ∀ w : ℂ, ({z ∈ Metric.ball p r | φ z = w}).Finite ∧
        ({z ∈ Metric.ball p r | φ z = w}).ncard ≤ m := by
    intro Ω hΩ φ hφ p hp hnc
    classical
    have hφa : AnalyticAt ℂ φ p := (hφ.analyticOnNhd hΩ) p hp
    have hg0a : AnalyticAt ℂ (fun z => φ z - φ p) p := hφa.sub analyticAt_const
    -- The order of vanishing of `φ - φ p` at `p` is a finite natural number.
    have hord_ne : analyticOrderAt (fun z => φ z - φ p) p ≠ ⊤ := by
      intro htop
      rw [analyticOrderAt_eq_top] at htop
      apply hnc
      filter_upwards [htop] with z hz
      exact sub_eq_zero.mp hz
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hord_ne
    obtain ⟨g, hga, hgp0, hfact⟩ :=
      (hg0a.analyticOrderAt_eq_natCast).mp hm.symm
    -- `m ≥ 1` because `φ p - φ p = 0` while `g p ≠ 0`.
    have hm1 : 1 ≤ m := by
      by_contra hm0
      have hm00 : m = 0 := by omega
      subst hm00
      have h0 := hfact.self_of_nhds
      simp at h0
      exact hgp0 h0.symm
    -- An `m`-th root `c` of `g p`.
    have hdeg : 0 < (Polynomial.X ^ m - Polynomial.C (g p) : Polynomial ℂ).degree := by
      rw [Polynomial.degree_X_pow_sub_C (by omega : 0 < m) (g p)]
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    obtain ⟨c, hcroot⟩ := Complex.exists_root hdeg
    have hcm : c ^ m = g p := by
      have := hcroot
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C] at this
      exact sub_eq_zero.mp this
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by omega)] at hcm
      exact hgp0 hcm.symm
    -- The analytic `m`-th root `h` of `g` near `p`.
    set h : ℂ → ℂ := fun z => c * Complex.exp (Complex.log (g z / g p) / m) with hhdef
    have hgp_slit : g p / g p ∈ Complex.slitPlane := by
      rw [div_self hgp0]
      exact Complex.one_mem_slitPlane
    have hgdiv : AnalyticAt ℂ (fun z => g z / g p) p := hga.div analyticAt_const hgp0
    have hlog : AnalyticAt ℂ (fun z => Complex.log (g z / g p)) p := by
      have hclog : AnalyticAt ℂ Complex.log ((fun z => g z / g p) p) :=
        analyticAt_clog hgp_slit
      have := AnalyticAt.comp (g := Complex.log) (f := fun z => g z / g p) (x := p)
        hclog hgdiv
      simpa [Function.comp] using! this
    have hm0C : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hh_a : AnalyticAt ℂ h p := by
      apply analyticAt_const.mul
      have hdivm : AnalyticAt ℂ (fun z => Complex.log (g z / g p) / m) p :=
        hlog.div analyticAt_const hm0C
      have := analyticAt_cexp.comp hdivm
      simpa [Function.comp] using! this
    have hhp : h p = c := by
      rw [hhdef]
      simp only []
      rw [div_self hgp0, Complex.log_one, zero_div, Complex.exp_zero, mul_one]
    -- `h ^ m = g` near `p`.
    have hpow_ev : ∀ᶠ z in 𝓝 p, h z ^ m = g z := by
      have h1 : ∀ᶠ z in 𝓝 p, g z / g p ∈ Complex.slitPlane := by
        have hcont : ContinuousAt (fun z => g z / g p) p := hgdiv.continuousAt
        exact hcont.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hgp_slit)
      have h2 : ∀ᶠ z in 𝓝 p, g z ≠ 0 := hga.continuousAt.eventually_ne hgp0
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hhdef]
      simp only []
      rw [mul_pow, hcm]
      have hexp : Complex.exp (Complex.log (g z / g p) / m) ^ m
          = Complex.exp (Complex.log (g z / g p)) := by
        rw [← Complex.exp_nat_mul]
        congr 1
        field_simp
      rw [hexp, Complex.exp_log (div_ne_zero hz2 hgp0)]
      field_simp
    -- The uniformizer `u = (z - p) · h` and its nonvanishing strict derivative.
    set u : ℂ → ℂ := fun z => (z - p) * h z with hudef
    have hu_a : AnalyticAt ℂ u p := (analyticAt_id.sub analyticAt_const).mul hh_a
    have hdu : HasDerivAt u (h p) p := by
      have hd1 : HasDerivAt (fun z : ℂ => z - p) 1 p := (hasDerivAt_id p).sub_const p
      have hd2 : HasDerivAt h (deriv h p) p := hh_a.differentiableAt.hasDerivAt
      have := hd1.mul hd2
      simpa using! this
    have hu_strict : HasStrictDerivAt u (h p) p := by
      have hs := hu_a.hasStrictDerivAt
      rwa [hdu.deriv] at hs
    obtain ⟨r₁, hr₁, hinj⟩ := e4_inj_ball hu_strict (by rw [hhp]; exact hc0)
    -- Choose a ball where everything holds simultaneously.
    have hall : ∀ᶠ z in 𝓝 p, (φ z - φ p = (z - p) ^ m • g z ∧ h z ^ m = g z) ∧ z ∈ Ω :=
      (hfact.and hpow_ev).and
        (Filter.eventually_of_mem (hΩ.mem_nhds hp) (fun z hz => hz))
    rw [Metric.eventually_nhds_iff_ball] at hall
    obtain ⟨r₂, hr₂, hball⟩ := hall
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_, m, ?_⟩
    · intro z hz
      exact (hball z (Metric.ball_subset_ball (min_le_right _ _) hz)).2
    intro w
    -- Fiber points solve `u z ^ m = w - φ p` and `u` is injective on the ball.
    set S : Set ℂ := {z ∈ Metric.ball p (min r₁ r₂) | φ z = w} with hSdef
    have hSsub : ∀ z ∈ S, u z ^ m = w - φ p := by
      rintro z ⟨hzball, hzw⟩
      have hz2 := hball z (Metric.ball_subset_ball (min_le_right _ _) hzball)
      have h1 : φ z - φ p = (z - p) ^ m * g z := by
        rw [hz2.1.1]; rw [smul_eq_mul]
      rw [hudef]
      simp only []
      rw [mul_pow, hz2.1.2, ← h1, hzw]
    -- The set of `m`-th roots of `w - φ p` has at most `m` elements.
    set R : Set ℂ := {ζ : ℂ | ζ ^ m = w - φ p} with hRdef
    have hpoly_ne : (Polynomial.X ^ m - Polynomial.C (w - φ p) : Polynomial ℂ) ≠ 0 :=
      Polynomial.X_pow_sub_C_ne_zero (by omega) _
    have hRsub : R ⊆ ((Polynomial.X ^ m - Polynomial.C (w - φ p) :
        Polynomial ℂ).roots.toFinset : Set ℂ) := by
      intro ζ hζ
      simp only [Multiset.mem_toFinset, Finset.mem_coe]
      rw [Polynomial.mem_roots hpoly_ne]
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      rw [hζ]
      ring
    have hRfin : R.Finite :=
      Set.Finite.subset (Set.finite_coe_iff.mp (by infer_instance)) hRsub
    have hRcard : R.ncard ≤ m := by
      calc R.ncard ≤ ((Polynomial.X ^ m - Polynomial.C (w - φ p) :
            Polynomial ℂ).roots.toFinset : Set ℂ).ncard :=
            Set.ncard_le_ncard hRsub (Set.toFinite _)
        _ = (Polynomial.X ^ m - Polynomial.C (w - φ p) :
            Polynomial ℂ).roots.toFinset.card := Set.ncard_coe_finset _
        _ ≤ Multiset.card (Polynomial.X ^ m - Polynomial.C (w - φ p) :
            Polynomial ℂ).roots := Multiset.toFinset_card_le _
        _ ≤ (Polynomial.X ^ m - Polynomial.C (w - φ p) : Polynomial ℂ).natDegree :=
            Polynomial.card_roots' _
        _ = m := by
            rw [Polynomial.natDegree_X_pow_sub_C]
    -- Conclude via injectivity of `u`.
    have hinj' : Set.InjOn u S :=
      hinj.mono (fun z hz => Metric.ball_subset_ball (min_le_left _ _) hz.1)
    have himg : u '' S ⊆ R := by
      rintro ζ ⟨z, hz, rfl⟩
      exact hSsub z hz
    have hSfin : S.Finite :=
      Set.Finite.of_finite_image (hRfin.subset himg) hinj'
    refine ⟨hSfin, ?_⟩
    calc S.ncard = (u '' S).ncard := (Set.InjOn.ncard_image hinj').symm
      _ ≤ R.ncard := Set.ncard_le_ncard himg hRfin
      _ ≤ m := hRcard
  have b00_ncard_biUnion_le : ∀ {ι : Type} [DecidableEq ι] (t : Finset ι)
    (S : ι → Set ℂ) (hfin : ∀ i, (S i).Finite),
      (⋃ i ∈ t, S i).Finite ∧ (⋃ i ∈ t, S i).ncard ≤ ∑ i ∈ t, (S i).ncard := by
    intro ι _inst t S hfin
    classical
    induction t using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.set_biUnion_insert]
        refine ⟨(hfin a).union ih.1, ?_⟩
        calc (S a ∪ ⋃ i ∈ s, S i).ncard
            ≤ (S a).ncard + (⋃ i ∈ s, S i).ncard :=
              Set.ncard_union_le _ _
          _ ≤ (S a).ncard + ∑ i ∈ s, (S i).ncard := Nat.add_le_add_left ih.2 _
          _ = ∑ i ∈ insert a s, (S i).ncard :=
              (Finset.sum_insert (f := fun i => (S i).ncard) ha).symm
  have b0_count : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω) {K : Set ℂ} (hKΩ : K ⊆ Ω) (hKc : IsCompact K), ∃ N : ℕ, ∀ w : ℂ,
      ({z ∈ K | deriv φ z ≠ 0 ∧ φ z = w}).Finite ∧
      ({z ∈ K | deriv φ z ≠ 0 ∧ φ z = w}).ncard ≤ N := by
    intro Ω hΩ φ hφ K hKΩ hKc
    classical
    -- The open set where `φ` is locally constant.
    set C : Set ℂ := {z : ℂ | ∀ᶠ w in 𝓝 z, φ w = φ z} with hCdef
    have hCopen : IsOpen C := by
      rw [isOpen_iff_mem_nhds]
      intro z hz
      have hz' : ∀ᶠ w in 𝓝 z, φ w = φ z := hz
      rw [Metric.eventually_nhds_iff_ball] at hz'
      obtain ⟨r, hr, hconst⟩ := hz'
      rw [Metric.mem_nhds_iff]
      refine ⟨r, hr, ?_⟩
      intro y hy
      change ∀ᶠ w in 𝓝 y, φ w = φ y
      rw [Metric.eventually_nhds_iff_ball]
      obtain ⟨r', hr', hsub⟩ : ∃ r' > 0, Metric.ball y r' ⊆ Metric.ball z r :=
        ⟨r - dist y z, by simp [Metric.mem_ball.mp hy],
          Metric.ball_subset_ball' (by linarith)⟩
      exact ⟨r', hr', fun x hx => by rw [hconst x (hsub hx), hconst y hy]⟩
    -- Its complement traps all points with nonvanishing derivative.
    have hUC : ∀ z, deriv φ z ≠ 0 → z ∉ C := by
      intro z hd hzC
      apply hd
      have : deriv φ z = deriv (fun _ => φ z) z := Filter.EventuallyEq.deriv_eq hzC
      rw [this, deriv_const]
    -- Compactness of `K ∖ C` and the finite subcover of fiber-bounded balls.
    set Kd : Set ℂ := K ∩ Cᶜ with hKddef
    have hKdc : IsCompact Kd := hKc.inter_right hCopen.isClosed_compl
    have hmem : ∀ z : ℂ, z ∈ Kd → ¬ (∀ᶠ w in 𝓝 z, φ w = φ z) := by
      intro z hz
      exact hz.2
    by_cases hKdemp : Kd = ∅
    · refine ⟨0, fun w => ?_⟩
      have hsub : {z ∈ K | deriv φ z ≠ 0 ∧ φ z = w} ⊆ Kd := by
        rintro z ⟨hzK, hzd, _⟩
        exact ⟨hzK, hUC z hzd⟩
      rw [hKdemp] at hsub
      have : {z ∈ K | deriv φ z ≠ 0 ∧ φ z = w} = ∅ := Set.subset_empty_iff.mp hsub
      simp [this]
    -- Choose fiber-bounded balls at every point of `Kd`.
    have hchoice : ∀ z : Kd, ∃ r > 0, Metric.ball (z : ℂ) r ⊆ Ω ∧ ∃ m : ℕ,
        ∀ w : ℂ, ({x ∈ Metric.ball (z : ℂ) r | φ x = w}).Finite ∧
          ({x ∈ Metric.ball (z : ℂ) r | φ x = w}).ncard ≤ m := by
      intro z
      exact a_fiber_bound hΩ hφ (hKΩ z.2.1) (hmem z z.2)
    choose r hr hballΩ m hm using hchoice
    obtain ⟨t, ht⟩ := hKdc.elim_finite_subcover
      (fun z : Kd => Metric.ball (z : ℂ) (r z)) (fun z => Metric.isOpen_ball)
      (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hr ⟨z, hz⟩)⟩)
    refine ⟨∑ i ∈ t, m i, fun w => ?_⟩
    set fiber : Set ℂ := {z ∈ K | deriv φ z ≠ 0 ∧ φ z = w} with hfiberdef
    have hfibsub : fiber ⊆ ⋃ i ∈ t, {x ∈ Metric.ball (i : ℂ) (r i) | φ x = w} := by
      rintro z ⟨hzK, hzd, hzw⟩
      have hzKd : z ∈ Kd := ⟨hzK, hUC z hzd⟩
      obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (ht hzKd)
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hzi, hzw⟩
    obtain ⟨hUfin, hUcard⟩ := b00_ncard_biUnion_le t
      (fun i => {x ∈ Metric.ball (i : ℂ) (r i) | φ x = w}) (fun i => (hm i w).1)
    refine ⟨hUfin.subset hfibsub, ?_⟩
    calc fiber.ncard ≤ (⋃ i ∈ t, {x ∈ Metric.ball (i : ℂ) (r i) | φ x = w}).ncard :=
          Set.ncard_le_ncard hfibsub hUfin
      _ ≤ ∑ i ∈ t, ({x ∈ Metric.ball (i : ℂ) (r i) | φ x = w}).ncard := hUcard
      _ ≤ ∑ i ∈ t, m i := Finset.sum_le_sum (fun i _ => (hm i w).2)
  have b_cv : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω) {K : Set ℂ} (hKΩ : K ⊆ Ω) (hKc : IsCompact K),
      ∃ N : ℕ, ∀ q : ℂ → ℂ, Measurable q →
      (∫⁻ z in K, ‖q (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume)
        ≤ N * ∫⁻ w in φ '' K, ‖q w‖ₑ ^ (2 : ℕ) ∂volume := by
    intro Ω hΩ φ hφ K hKΩ hKc
    classical
    obtain ⟨N, hN⟩ := b0_count hΩ hφ hKΩ hKc
    have hφa : AnalyticOnNhd ℂ φ Ω := hφ.analyticOnNhd hΩ
    have hd'cont : ContinuousOn (deriv φ) Ω := hφa.deriv.continuousOn
    have hφcont : ContinuousOn φ Ω := hφ.continuousOn
    refine ⟨N, fun q hq => ?_⟩
    set G : ℂ → ℝ≥0∞ := fun w => ‖q w‖ₑ ^ (2 : ℕ) with hGdef
    have hGmeas : Measurable G := hq.enorm.pow_const 2
    -- The open set of noncritical points.
    set U : Set ℂ := Ω ∩ (deriv φ) ⁻¹' {(0 : ℂ)}ᶜ with hUdef
    have hUopen : IsOpen U := hd'cont.isOpen_inter_preimage hΩ isOpen_compl_singleton
    have hUsub : U ⊆ Ω := Set.inter_subset_left
    have hUne' : ∀ z ∈ U, deriv φ z ≠ 0 := by
      intro z hz
      have := hz.2
      simpa using this
    -- Step 1: the integrand vanishes off `U`.
    have hzeroKU : ∀ z ∈ K \ U, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) = 0 := by
      intro z hz
      have hzΩ : z ∈ Ω := hKΩ hz.1
      have hd0 : deriv φ z = 0 := by
        by_contra hne
        exact hz.2 ⟨hzΩ, by simpa using hne⟩
      rw [hd0]
      simp
    have hsplit : (∫⁻ z in K, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume)
        = ∫⁻ z in K ∩ U, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume := by
      have hKeq : K = (K ∩ U) ∪ (K \ U) := (Set.inter_union_sdiff K U).symm
      conv_lhs => rw [hKeq]
      rw [lintegral_union (hKc.measurableSet.diff hUopen.measurableSet)
        (Set.disjoint_sdiff_right.mono_left Set.inter_subset_right)]
      have h0 : (∫⁻ z in K \ U, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume) = 0 := by
        rw [setLIntegral_congr_fun (hKc.measurableSet.diff hUopen.measurableSet)
          (fun z hz => hzeroKU z hz)]
        simp
      rw [h0, add_zero]
    rw [hsplit]
    -- Trivial case: `U` empty.
    rcases Set.eq_empty_or_nonempty U with hUemp | hUne
    · rw [hUemp]
      simp
    -- Injectivity balls inside `U` at every point of `U`.
    have hchoice : ∀ z : U, ∃ ρ > 0, Metric.ball (z : ℂ) ρ ⊆ U ∧
        Set.InjOn φ (Metric.ball (z : ℂ) ρ) := by
      intro z
      have hzU := z.2
      have hzΩ : (z : ℂ) ∈ Ω := hUsub hzU
      have hne : deriv φ (z : ℂ) ≠ 0 := hUne' _ hzU
      have hstrict : HasStrictDerivAt φ (deriv φ (z : ℂ)) (z : ℂ) :=
        (hφa _ hzΩ).hasStrictDerivAt
      obtain ⟨r₁, hr₁, hinj⟩ := e4_inj_ball hstrict hne
      obtain ⟨r₂, hr₂, hball⟩ := Metric.isOpen_iff.mp hUopen _ hzU
      exact ⟨min r₁ r₂, lt_min hr₁ hr₂,
        (Metric.ball_subset_ball (min_le_right _ _)).trans hball,
        hinj.mono (Metric.ball_subset_ball (min_le_left _ _))⟩
    choose ρ hρ hρU hρinj using hchoice
    -- Countable subcover of `U` by these balls.
    obtain ⟨T, hTcnt, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun z : U => Metric.ball (z : ℂ) (ρ z)) (fun z => Metric.isOpen_ball)
    have hUcover : U ⊆ ⋃ i ∈ T, Metric.ball ((i : U) : ℂ) (ρ i) := by
      intro z hz
      rw [hTeq]
      exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hρ _)⟩
    have hTne : T.Nonempty := by
      rcases hUne with ⟨z, hz⟩
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have := hUcover hz
      simp [hemp] at this
    obtain ⟨f, hf⟩ := hTcnt.exists_eq_range hTne
    set B : ℕ → Set ℂ := fun n => Metric.ball ((f n : U) : ℂ) (ρ (f n)) with hBdef
    have hBmeas : ∀ n, MeasurableSet (B n) := fun n => Metric.isOpen_ball.measurableSet
    have hBU : ∀ n, B n ⊆ U := fun n => hρU (f n)
    have hBinj : ∀ n, Set.InjOn φ (B n) := fun n => hρinj (f n)
    have hUB : U ⊆ ⋃ n, B n := by
      intro z hz
      obtain ⟨i, hiT, hzi⟩ := Set.mem_iUnion₂.mp (hUcover hz)
      have : i ∈ Set.range f := by rw [← hf]; exact hiT
      obtain ⟨n, rfl⟩ := this
      exact Set.mem_iUnion.mpr ⟨n, hzi⟩
    -- Disjointify.
    set D : ℕ → Set ℂ := disjointed B with hDdef
    have hDmeas : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed hBmeas
    have hDdisj : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed B
    have hDB : ∀ n, D n ⊆ B n := fun n => disjointed_subset B n
    set E : ℕ → Set ℂ := fun n => (K ∩ U) ∩ D n with hEdef
    have hEmeas : ∀ n, MeasurableSet (E n) := fun n =>
      (hKc.measurableSet.inter hUopen.measurableSet).inter (hDmeas n)
    have hEdisj : Pairwise (Function.onFun Disjoint E) := fun i j hij =>
      ((hDdisj hij).mono Set.inter_subset_right Set.inter_subset_right)
    have hEB : ∀ n, E n ⊆ B n := fun n => (Set.inter_subset_right).trans (hDB n)
    have hEK : ∀ n, E n ⊆ K := fun n => (Set.inter_subset_left).trans Set.inter_subset_left
    have hEU : ∀ n, E n ⊆ U := fun n => (Set.inter_subset_left).trans Set.inter_subset_right
    have hEΩ : ∀ n, E n ⊆ Ω := fun n => (hEU n).trans hUsub
    have hEinj : ∀ n, Set.InjOn φ (E n) := fun n => (hBinj n).mono (hEB n)
    have hEunion : (⋃ n, E n) = K ∩ U := by
      rw [hEdef]
      rw [← Set.inter_iUnion]
      rw [iUnion_disjointed]
      exact Set.inter_eq_left.mpr (fun z hz => hUB hz.2)
    -- Step 2: decompose the integral.
    have hstep2 : (∫⁻ z in K ∩ U, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume)
        = ∑' n, ∫⁻ z in E n, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume := by
      rw [← hEunion, lintegral_iUnion hEmeas hEdisj]
    -- Step 3: injective change of variables on each piece.
    have hstep3 : ∀ n, (∫⁻ z in E n, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume)
        = ∫⁻ w in φ '' E n, G w ∂volume := by
      intro n
      have hfd := e6_hasFDerivWithinAt hΩ hφ (hEΩ n)
      have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure ℂ)
        (hEmeas n) hfd (hEinj n) G
      rw [hcov]
      apply setLIntegral_congr_fun (hEmeas n)
      intro z _
      dsimp only
      rw [e3_det, abs_of_nonneg (Complex.normSq_nonneg _)]
      rw [show Complex.normSq (deriv φ z) = ‖deriv φ z‖ ^ 2 from Complex.normSq_eq_norm_sq _]
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      ring
    -- Step 4: sum the image integrals against the multiplicity bound.
    have hEimg_meas : ∀ n, MeasurableSet (φ '' E n) := fun n =>
      MeasurableSet.image_of_continuousOn_injOn (hEmeas n)
        (hφcont.mono (hEΩ n)) (hEinj n)
    have hKimg : IsCompact (φ '' K) := hKc.image_of_continuousOn (hφcont.mono hKΩ)
    have hind : ∀ n, (∫⁻ w in φ '' E n, G w ∂volume)
        = ∫⁻ w, (φ '' E n).indicator (fun _ => (1 : ℝ≥0∞)) w * G w ∂volume := by
      intro n
      rw [← lintegral_indicator (hEimg_meas n)]
      apply lintegral_congr
      intro w
      by_cases hw : w ∈ φ '' E n <;> simp [hw]
    -- Pointwise multiplicity bound.
    have hcount : ∀ w : ℂ, (∑' n, (φ '' E n).indicator (fun _ => (1 : ℝ≥0∞)) w)
        ≤ (N : ℝ≥0∞) * (φ '' K).indicator (fun _ => (1 : ℝ≥0∞)) w := by
      intro w
      by_cases hw : w ∈ φ '' K
      · rw [Set.indicator_of_mem hw, mul_one]
        rw [ENNReal.tsum_eq_iSup_sum]
        apply iSup_le
        intro s
        obtain ⟨hfibfin, hfibcard⟩ := hN w
        set fib : Set ℂ := {z ∈ K | deriv φ z ≠ 0 ∧ φ z = w} with hfibdef
        set s' : Finset ℕ := s.filter (fun n => w ∈ φ '' E n) with hs'def
        have hsum : (∑ n ∈ s, (φ '' E n).indicator (fun _ => (1 : ℝ≥0∞)) w)
            = (s'.card : ℝ≥0∞) := by
          rw [hs'def, Finset.card_filter]
          push_cast
          apply Finset.sum_congr rfl
          intro n _
          by_cases hn : w ∈ φ '' E n <;> simp [hn]
        rw [hsum]
        have hpick : ∀ n ∈ s', ∃ z, z ∈ E n ∧ φ z = w := by
          intro n hn
          obtain ⟨z, hz, hzw⟩ := (Finset.mem_filter.mp hn).2
          exact ⟨z, hz, hzw⟩
        choose pick hpick1 hpick2 using hpick
        have hmapsto : ∀ n (hn : n ∈ s'), pick n hn ∈ hfibfin.toFinset := by
          intro n hn
          rw [Set.Finite.mem_toFinset]
          have hzE := hpick1 n hn
          exact ⟨hEK n hzE, hUne' _ (hEU n hzE), hpick2 n hn⟩
        have hcardle : s'.card ≤ hfibfin.toFinset.card := by
          apply Finset.card_le_card_of_injOn (fun n => if hn : n ∈ s' then pick n hn else 0)
          · intro n hn
            dsimp only
            rw [dif_pos (Finset.mem_coe.mp hn)]
            exact hmapsto n (Finset.mem_coe.mp hn)
          · intro a ha b hb hab
            simp only [Finset.mem_coe] at ha hb
            dsimp only at hab
            rw [dif_pos ha, dif_pos hb] at hab
            by_contra hne
            have hdis := hEdisj hne
            have h1 := hpick1 a ha
            have h2 := hpick1 b hb
            rw [hab] at h1
            exact Set.disjoint_left.mp hdis h1 h2
        have hfibN : hfibfin.toFinset.card ≤ N := by
          rw [← Set.ncard_eq_toFinset_card fib hfibfin]
          exact hfibcard
        exact_mod_cast hcardle.trans hfibN
      · have hzero : ∀ n, (φ '' E n).indicator (fun _ => (1 : ℝ≥0∞)) w = 0 := by
          intro n
          apply Set.indicator_of_notMem
          intro hmem
          exact hw (Set.image_mono (hEK n) hmem)
        simp only [hzero]
        simp
    calc (∫⁻ z in K ∩ U, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume)
        = ∑' n, ∫⁻ z in E n, G (φ z) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume := hstep2
      _ = ∑' n, ∫⁻ w in φ '' E n, G w ∂volume := by
          apply tsum_congr
          intro n
          exact hstep3 n
      _ = ∑' n, ∫⁻ w, (φ '' E n).indicator (fun _ => (1 : ℝ≥0∞)) w * G w ∂volume := by
          apply tsum_congr
          intro n
          exact hind n
      _ = ∫⁻ w, ∑' n, (φ '' E n).indicator (fun _ => (1 : ℝ≥0∞)) w * G w ∂volume := by
          rw [← lintegral_tsum]
          intro n
          exact ((measurable_one.indicator (hEimg_meas n)).mul hGmeas).aemeasurable
      _ ≤ ∫⁻ w, ((N : ℝ≥0∞) * (φ '' K).indicator (fun _ => (1 : ℝ≥0∞)) w) * G w ∂volume := by
          apply lintegral_mono
          intro w
          dsimp only
          rw [ENNReal.tsum_mul_right]
          exact le_trans (mul_le_mul_left (hcount w) (G w)) (le_of_eq (by ring))
      _ = N * ∫⁻ w in φ '' K, G w ∂volume := by
          rw [← lintegral_indicator hKimg.measurableSet]
          rw [← lintegral_const_mul (N : ℝ≥0∞) (hGmeas.indicator hKimg.measurableSet)]
          apply lintegral_congr
          intro w
          by_cases hw : w ∈ φ '' K <;> simp [hw]
  have c_preimage_null : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω) {E : Set ℂ} (hE : volume E = 0),
      ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω → deriv φ z ≠ 0 → φ z ∉ E := by
    intro Ω hΩ φ hφ E hE
    classical
    obtain ⟨E', hEE', hE'meas, hE'null⟩ := exists_measurable_superset_of_null hE
    have hd'cont : ContinuousOn (deriv φ) Ω := (hφ.analyticOnNhd hΩ).deriv.continuousOn
    -- The compact exhaustion of `Ω`.
    set Kn : ℕ → Set ℂ := fun n =>
      Metric.closedBall 0 n ∩ ⋂ y ∈ Ωᶜ, {z : ℂ | 1 / (n + 1 : ℝ) ≤ dist z y} with hKndef
    have hKn_closed : ∀ n, IsClosed (Kn n) := by
      intro n
      apply (Metric.isClosed_closedBall).inter
      apply isClosed_biInter
      intro y _
      exact isClosed_le continuous_const (continuous_id.dist continuous_const)
    have hKn_compact : ∀ n, IsCompact (Kn n) := fun n =>
      (isCompact_closedBall (0 : ℂ) n).of_isClosed_subset (hKn_closed n)
        Set.inter_subset_left
    have hKn_sub : ∀ n, Kn n ⊆ Ω := by
      intro n z hz
      by_contra hzΩ
      have h1 := Set.mem_iInter₂.mp hz.2 z hzΩ
      simp only [Set.mem_ofPred_eq, dist_self] at h1
      have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      linarith
    have hKn_cover : ∀ z ∈ Ω, ∃ n, z ∈ Kn n := by
      intro z hz
      by_cases hcompl : Ωᶜ = ∅
      · obtain ⟨n, hn⟩ := exists_nat_ge (dist z 0)
        refine ⟨n, ⟨Metric.mem_closedBall.mpr hn, ?_⟩⟩
        rw [hcompl]
        simp
      · have hne : Ωᶜ.Nonempty := Set.nonempty_iff_ne_empty.mpr hcompl
        have hzpos : 0 < Metric.infDist z Ωᶜ := by
          rw [← hΩ.isClosed_compl.notMem_iff_infDist_pos hne]
          simpa using hz
        obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hzpos
        obtain ⟨n₂, hn₂⟩ := exists_nat_ge (dist z 0)
        have hn2' : dist z 0 ≤ ((max n₁ n₂ : ℕ) : ℝ) := by
          have hcast : ((n₂ : ℕ) : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by
            exact_mod_cast le_max_right n₁ n₂
          linarith
        refine ⟨max n₁ n₂, ⟨Metric.mem_closedBall.mpr hn2', ?_⟩⟩
        apply Set.mem_iInter₂.mpr
        intro y hy
        simp only [Set.mem_ofPred_eq]
        have h1 : 1 / ((max n₁ n₂ : ℕ) + 1 : ℝ) ≤ 1 / ((n₁ : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          have : (n₁ : ℝ) ≤ (max n₁ n₂ : ℕ) := by exact_mod_cast le_max_left n₁ n₂
          linarith
        calc 1 / ((max n₁ n₂ : ℕ) + 1 : ℝ) ≤ 1 / ((n₁ : ℝ) + 1) := h1
          _ ≤ Metric.infDist z Ωᶜ := hn₁.le
          _ ≤ dist z y := Metric.infDist_le_dist_of_mem hy
    -- Per-compact vanishing of the transported indicator integrand.
    set q : ℂ → ℂ := E'.indicator (fun _ => 1) with hqdef
    have hqmeas : Measurable q := measurable_const.indicator hE'meas
    have hker : ∀ n : ℕ, ∀ᵐ z ∂(volume : Measure ℂ),
        z ∈ Kn n → ‖q (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ) = 0 := by
      intro n
      obtain ⟨N, hCV⟩ := b_cv hΩ hφ (hKn_sub n) (hKn_compact n)
      have himg0 : (∫⁻ w in φ '' Kn n, ‖q w‖ₑ ^ (2 : ℕ) ∂volume) = 0 := by
        have hpt : ∀ w, ‖q w‖ₑ ^ (2 : ℕ) = E'.indicator (fun _ => (1 : ℝ≥0∞)) w := by
          intro w
          by_cases hw : w ∈ E' <;> simp [hqdef, hw]
        apply le_antisymm _ (zero_le)
        calc (∫⁻ w in φ '' Kn n, ‖q w‖ₑ ^ (2 : ℕ) ∂volume)
            = ∫⁻ w in φ '' Kn n, E'.indicator (fun _ => (1 : ℝ≥0∞)) w ∂volume := by
              apply lintegral_congr
              intro w
              exact hpt w
          _ ≤ ∫⁻ w, E'.indicator (fun _ => (1 : ℝ≥0∞)) w ∂volume :=
              setLIntegral_le_lintegral _ _
          _ = volume E' := by
              rw [lintegral_indicator hE'meas]
              simp
          _ = 0 := hE'null
      have hCV0 : (∫⁻ z in Kn n, ‖q (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume) = 0 := by
        apply le_antisymm _ (zero_le)
        calc (∫⁻ z in Kn n, ‖q (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume)
            ≤ N * ∫⁻ w in φ '' Kn n, ‖q w‖ₑ ^ (2 : ℕ) ∂volume := hCV q hqmeas
          _ = 0 := by rw [himg0, mul_zero]
      -- Convert the vanishing integral to an a.e. statement.
      have hφae : AEMeasurable φ (volume.restrict (Kn n)) :=
        ((hφ.continuousOn.mono (hKn_sub n)).aemeasurable (hKn_compact n).measurableSet)
      have hd'ae : AEMeasurable (deriv φ) (volume.restrict (Kn n)) :=
        ((hd'cont.mono (hKn_sub n)).aemeasurable (hKn_compact n).measurableSet)
      have hint_meas : AEMeasurable
          (fun z => ‖q (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))
          (volume.restrict (Kn n)) :=
        (((hqmeas.comp_aemeasurable hφae).enorm.pow_const 2).mul
          (hd'ae.enorm.pow_const 2))
      have hae0 := (lintegral_eq_zero_iff' hint_meas).mp hCV0
      rw [Filter.EventuallyEq, ae_restrict_iff' (hKn_compact n).measurableSet] at hae0
      filter_upwards [hae0] with z hz hzK
      exact hz hzK
    -- Combine over the exhaustion.
    have hall := (MeasureTheory.ae_all_iff).mpr hker
    filter_upwards [hall] with z hz hzΩ hzd hzE
    obtain ⟨n, hn⟩ := hKn_cover z hzΩ
    have h0 := hz n hn
    have hd_ne : ‖deriv φ z‖ₑ ^ (2 : ℕ) ≠ 0 := by
      apply pow_ne_zero
      rw [enorm_ne_zero]
      exact hzd
    have hq_ne : ‖q (φ z)‖ₑ ^ (2 : ℕ) ≠ 0 := by
      have hmem : φ z ∈ E' := hEE' hzE
      simp [hqdef, hmem]
    exact hq_ne (by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hd_ne)
  have p_conv2 : ∀ (h : ℂ → ℂ) (μ : Measure ℂ),
      eLpNorm h 2 μ = (∫⁻ z, ‖h z‖ₑ ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) := by
    intro h μ
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
    rw [h2]
    congr 1
    apply lintegral_congr
    intro z
    rw [← ENNReal.rpow_natCast]
    norm_num
  have p_collapse : ∀ (X : ℝ≥0∞), (X ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = X := by
    intro X
    rw [← ENNReal.rpow_natCast (X ^ (1 / 2 : ℝ)) 2, ← ENNReal.rpow_mul]
    norm_num
  have p_fin : ∀ {h : ℂ → ℂ} {μ : Measure ℂ} (hh : MemLp h 2 μ),
      (∫⁻ z, ‖h z‖ₑ ^ (2 : ℕ) ∂μ) < ⊤ := by
    intro h μ hh
    have h1 := hh.2
    rw [p_conv2] at h1
    by_contra hX
    have hXtop : (∫⁻ z, ‖h z‖ₑ ^ (2 : ℕ) ∂μ) = ⊤ := by
      exact eq_top_iff.mpr (not_lt.mp hX)
    rw [hXtop, ENNReal.top_rpow_of_pos (by norm_num)] at h1
    exact (lt_irrefl _ h1).elim
  have p_mollify_L2 : ∀ {g : ℂ → ℂ} (hg_meas : Measurable g)
    (hg2 : MemLpLocOn g 2 Set.univ) {S : Set ℂ} (hSc : IsCompact S)
    (bumps : ℕ → ContDiffBump (0 : ℂ))
    (hrout : Tendsto (fun n => (bumps n).rOut) atTop (𝓝 0))
    (hrout1 : ∀ n, (bumps n).rOut ≤ 1), Tendsto (fun n => ∫⁻ w in S,
        ‖MeasureTheory.convolution ((bumps n).normed volume) g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume w - g w‖ₑ ^ (2 : ℕ) ∂volume)
      atTop (𝓝 0) := by
    intro g hg_meas hg2 S hSc bumps hrout hrout1
    classical
    set D' : Set ℂ := Metric.cthickening 2 S with hD'def
    have hD'c : IsCompact D' := hSc.cthickening
    have hSD' : S ⊆ D' := Metric.self_subset_cthickening S
    set gD : ℂ → ℂ := D'.indicator g with hgDdef
    have hgD_meas : Measurable gD := hg_meas.indicator hD'c.measurableSet
    have hgD2 : MemLp gD 2 volume := by
      refine ⟨hgD_meas.aestronglyMeasurable, ?_⟩
      rw [hgDdef, eLpNorm_indicator_eq_eLpNorm_restrict hD'c.measurableSet]
      exact (hg2 D' (Set.subset_univ _) hD'c).2
    -- The two mollifications agree on `S`, and so do the functions.
    have hagree : ∀ n, ∀ w ∈ S,
        MeasureTheory.convolution ((bumps n).normed volume) g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume w
        = MeasureTheory.convolution ((bumps n).normed volume) gD
          (ContinuousLinearMap.lsmul ℝ ℝ) volume w := by
      intro n w hw
      rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      by_cases ht : t ∈ tsupport ((bumps n).normed volume)
      · have htball : ‖t‖ ≤ (bumps n).rOut := by
          have := (bumps n).tsupport_normed_eq (μ := volume) ▸ ht
          simpa [dist_eq_norm] using Metric.mem_closedBall.mp this
        have hwt : w - t ∈ D' := by
          apply Metric.mem_cthickening_of_dist_le (w - t) w 2 _ hw
          rw [dist_eq_norm]
          simpa using htball.trans ((hrout1 n).trans (by norm_num))
        rw [hgDdef]
        rw [Set.indicator_of_mem hwt]
      · have h0 : (bumps n).normed volume t = 0 := image_eq_zero_of_notMem_tsupport ht
        rw [h0]
        simp
    have hagree2 : ∀ w ∈ S, g w = gD w := fun w hw => by
      rw [hgDdef, Set.indicator_of_mem (hSD' hw)]
    -- Reduce to the global `L²` convergence for `gD`.
    have hglobal := eLpNorm_convolution_normed_sub_tendsto_zero hgD2 bumps hrout
    have hbound : ∀ n, (∫⁻ w in S,
        ‖MeasureTheory.convolution ((bumps n).normed volume) g
          (ContinuousLinearMap.lsmul ℝ ℝ) volume w - g w‖ₑ ^ (2 : ℕ) ∂volume)
        ≤ (eLpNorm (MeasureTheory.convolution ((bumps n).normed volume) gD
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - gD) 2 volume) ^ (2 : ℕ) := by
      intro n
      have hstep : (∫⁻ w in S,
          ‖MeasureTheory.convolution ((bumps n).normed volume) g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume w - g w‖ₑ ^ (2 : ℕ) ∂volume)
          = ∫⁻ w in S,
          ‖(MeasureTheory.convolution ((bumps n).normed volume) gD
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - gD) w‖ₑ ^ (2 : ℕ) ∂volume := by
        apply setLIntegral_congr_fun hSc.measurableSet
        intro w hw
        dsimp only
        rw [hagree n w hw, Pi.sub_apply, hagree2 w hw]
      rw [hstep]
      calc (∫⁻ w in S,
          ‖(MeasureTheory.convolution ((bumps n).normed volume) gD
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - gD) w‖ₑ ^ (2 : ℕ) ∂volume)
          ≤ ∫⁻ w, ‖(MeasureTheory.convolution ((bumps n).normed volume) gD
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - gD) w‖ₑ ^ (2 : ℕ) ∂volume :=
            setLIntegral_le_lintegral _ _
        _ = (eLpNorm (MeasureTheory.convolution ((bumps n).normed volume) gD
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - gD) 2 volume) ^ (2 : ℕ) := by
            rw [p_conv2, p_collapse]
    have hsq : Tendsto (fun n => (eLpNorm (MeasureTheory.convolution
        ((bumps n).normed volume) gD (ContinuousLinearMap.lsmul ℝ ℝ) volume - gD)
        2 volume) ^ (2 : ℕ)) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_pow 2).tendsto 0).comp hglobal
      simpa using! this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq
      (fun n => zero_le) hbound
  have e7_conj_enorm : ∀ (w : ℂ), ‖(starRingEnd ℂ) w‖ₑ = ‖w‖ₑ := by
    intro w
    rw [← ofReal_norm, ← ofReal_norm]
    congr 1
    simp
  have e7_habs : ∀ (a b d e : ℂ), ‖(1 / 2 : ℂ) * (a - Complex.I * b) * (d * e)
      + (1 / 2 : ℂ) * (a + Complex.I * b) * ((starRingEnd ℂ) (d * e))‖ₑ
    ≤ (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ) := by
    intro a b d e
    have hIb : ∀ x y : ℂ, ‖x - Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ := by
      intro x y
      calc ‖x - Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖Complex.I * y‖ₑ := by
            rw [sub_eq_add_neg]
            exact (enorm_add_le _ _).trans (by rw [enorm_neg])
        _ = ‖x‖ₑ + ‖y‖ₑ := by
            rw [enorm_mul]
            congr 1
            rw [← ofReal_norm, Complex.norm_I]
            simp
    have hIb' : ∀ x y : ℂ, ‖x + Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ := by
      intro x y
      calc ‖x + Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖Complex.I * y‖ₑ := enorm_add_le _ _
        _ = ‖x‖ₑ + ‖y‖ₑ := by
            rw [enorm_mul]
            congr 1
            rw [← ofReal_norm, Complex.norm_I]
            simp
    have hhalf : ‖(1 / 2 : ℂ)‖ₑ = ENNReal.ofReal (1 / 2) := by
      rw [← ofReal_norm]
      congr 1
      simp
    calc ‖(1 / 2 : ℂ) * (a - Complex.I * b) * (d * e)
        + (1 / 2 : ℂ) * (a + Complex.I * b) * ((starRingEnd ℂ) (d * e))‖ₑ
        ≤ ‖(1 / 2 : ℂ) * (a - Complex.I * b) * (d * e)‖ₑ
          + ‖(1 / 2 : ℂ) * (a + Complex.I * b) * ((starRingEnd ℂ) (d * e))‖ₑ :=
          enorm_add_le _ _
      _ = ‖(1 / 2 : ℂ)‖ₑ * ‖a - Complex.I * b‖ₑ * (‖d‖ₑ * ‖e‖ₑ)
          + ‖(1 / 2 : ℂ)‖ₑ * ‖a + Complex.I * b‖ₑ * (‖d‖ₑ * ‖e‖ₑ) := by
          simp only [enorm_mul, e7_conj_enorm]
      _ ≤ ‖(1 / 2 : ℂ)‖ₑ * (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ)
          + ‖(1 / 2 : ℂ)‖ₑ * (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ) := by
          gcongr
          · exact hIb a b
          · exact hIb' a b
      _ = (‖(1 / 2 : ℂ)‖ₑ + ‖(1 / 2 : ℂ)‖ₑ) * ((‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ)) := by ring
      _ = (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ) := by
          rw [hhalf, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  have e8_sum_sq : ∀ (a b : ℝ≥0∞), (a + b) ^ (2 : ℕ) ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
    intro a b
    rcases le_total a b with h | h
    · calc (a + b) ^ (2 : ℕ) ≤ (b + b) ^ (2 : ℕ) := by gcongr
        _ = 4 * b ^ (2 : ℕ) := by ring
        _ ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
            gcongr
            exact le_add_self
    · calc (a + b) ^ (2 : ℕ) ≤ (a + a) ^ (2 : ℕ) := by gcongr
        _ = 4 * a ^ (2 : ℕ) := by ring
        _ ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
            gcongr
            exact le_self_add
  have d_comp_weak : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {φ v : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω) (hv : Continuous v)
    {gx gy : ℂ → ℂ} (hgx_meas : Measurable gx) (hgy_meas : Measurable gy)
    (hwx : HasWeakDirDeriv 1 gx v Set.univ)
    (hwy : HasWeakDirDeriv Complex.I gy v Set.univ)
    (hgx2 : MemLpLocOn gx 2 Set.univ) (hgy2 : MemLpLocOn gy 2 Set.univ) (e : ℂ), HasWeakDirDeriv e
      (fun z => (1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
        + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
          * (starRingEnd ℂ) (deriv φ z * e))
      (fun z => v (φ z)) Ω := by
    intro Ω hΩ φ v hφ hv gx gy hgx_meas hgy_meas hwx hwy hgx2 hgy2 e
    classical
    have : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
    have : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
    have hφa : AnalyticOnNhd ℂ φ Ω := hφ.analyticOnNhd hΩ
    have hφcont : ContinuousOn φ Ω := hφ.continuousOn
    have hd'cont : ContinuousOn (deriv φ) Ω := hφa.deriv.continuousOn
    have hφAtR : ∀ z ∈ Ω, AnalyticAt ℝ φ z := fun z hz =>
      @AnalyticAt.restrictScalars ℝ _ ℂ ℂ _ _ _ _ ℂ _ _ _ IsScalarTower.right _
        IsScalarTower.right _ _ (hφa z hz)
    have hφdiffR : ∀ z ∈ Ω, DifferentiableAt ℝ φ z := fun z hz =>
      (hφAtR z hz).differentiableAt
    have hv_li : MeasureTheory.LocallyIntegrable v := hv.locallyIntegrable
    have hgx_li : MeasureTheory.LocallyIntegrable gx :=
      locallyIntegrableOn_univ.mp (d1_locInt isOpen_univ hgx2)
    have hgy_li : MeasureTheory.LocallyIntegrable gy :=
      locallyIntegrableOn_univ.mp (d1_locInt isOpen_univ hgy2)
    intro ψ hψ hcs htsupp
    change ∫ z, ((fderiv ℝ ψ z) e) • (v (φ z))
        = - ∫ z, ψ z • ((1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
          + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
            * (starRingEnd ℂ) (deriv φ z * e))
    -- The compact carrier of the test function and its image.
    have hKc : IsCompact (tsupport ψ) := hcs
    have hKΩ : tsupport ψ ⊆ Ω := htsupp
    have hKimgc : IsCompact (φ '' tsupport ψ) := hKc.image_of_continuousOn (hφcont.mono hKΩ)
    obtain ⟨N, hCV⟩ := b_cv hΩ hφ hKΩ hKc
    -- Mollifier sequence.
    set bumps : ℕ → ContDiffBump (0 : ℂ) := fun n =>
      { rIn := 1 / (n + 2), rOut := 2 / (n + 2),
        rIn_pos := by positivity,
        rIn_lt_rOut := by
          rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num } with hbumps
    have hrout : Tendsto (fun n => (bumps n).rOut) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        apply Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      simpa [hbumps] using h2
    have hrout1 : ∀ n, (bumps n).rOut ≤ 1 := by
      intro n
      change 2 / ((n : ℝ) + 2) ≤ 1
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    set ρ : ℕ → ℂ → ℝ := fun n => (bumps n).normed volume with hρdef
    have hρ_sm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
      (bumps n).contDiff_normed
    have hρ_cs : ∀ n, HasCompactSupport (ρ n) := fun n => (bumps n).hasCompactSupport_normed
    set vn : ℕ → ℂ → ℂ := fun n =>
      MeasureTheory.convolution (ρ n) v (ContinuousLinearMap.lsmul ℝ ℝ) volume with hvndef
    set cx : ℕ → ℂ → ℂ := fun n =>
      MeasureTheory.convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume with hcxdef
    set cy : ℕ → ℂ → ℂ := fun n =>
      MeasureTheory.convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume with hcydef
    have hvn_cd : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (vn n) := fun n =>
      HasCompactSupport.contDiff_convolution_left _ (hρ_cs n) (hρ_sm n) hv_li
    have hvn_fd1 : ∀ n z, (fderiv ℝ (vn n) z) 1 = cx n z := fun n z =>
      fderiv_convolution_normed_apply_eq hwx hv_li hgx_li (hρ_sm n) (hρ_cs n) z
    have hvn_fdI : ∀ n z, (fderiv ℝ (vn n) z) Complex.I = cy n z := fun n z =>
      fderiv_convolution_normed_apply_eq hwy hv_li hgy_li (hρ_sm n) (hρ_cs n) z
    -- Chain rule for the mollified composition on `Ω`.
    have hchain : ∀ n, ∀ z ∈ Ω,
        (fderiv ℝ (fun y => vn n (φ y)) z) e
          = (1 / 2 : ℂ) * (cx n (φ z) - Complex.I * cy n (φ z)) * (deriv φ z * e)
            + (1 / 2 : ℂ) * (cx n (φ z) + Complex.I * cy n (φ z))
              * (starRingEnd ℂ) (deriv φ z * e) := by
      intro n z hz
      have hvdiff : DifferentiableAt ℝ (vn n) (φ z) :=
        ((hvn_cd n).differentiable (by norm_num)).differentiableAt
      have hcomp := fderiv_comp z hvdiff (hφdiffR z hz)
      have h1 : (fderiv ℝ (fun y => vn n (φ y)) z) e
          = (fderiv ℝ (vn n) (φ z)) ((fderiv ℝ φ z) e) := by
        have : (fun y => vn n (φ y)) = (vn n) ∘ φ := rfl
        rw [this, hcomp]
        rfl
      rw [h1, e5_fderiv_apply hΩ hφ z hz e,
        e1_wirtinger_apply (fderiv ℝ (vn n) (φ z)) (deriv φ z * e),
        hvn_fd1 n (φ z), hvn_fdI n (φ z)]
    -- Smoothness of the composition and the classical weak derivative.
    have hcomp_cd : ∀ n, ContDiffOn ℝ 1 (fun y => vn n (φ y)) Ω := by
      intro n z hz
      have h1 : ContDiffAt ℝ 1 φ z := (hφAtR z hz).contDiffAt
      have h2 : ContDiffAt ℝ 1 (vn n) (φ z) :=
        ((hvn_cd n).of_le (by exact_mod_cast le_top)).contDiffAt
      exact ((h2.comp z h1).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y => rfl))).contDiffWithinAt
    have hweak_n : ∀ n, ∫ z, ((fderiv ℝ ψ z) e) • (vn n (φ z))
        = - ∫ z, ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) := by
      intro n
      exact HasWeakDirDeriv.of_contDiffOn hΩ (hcomp_cd n) ψ hψ hcs htsupp
    -- ==================== LHS convergence ====================
    have hvn_ptw : ∀ x, Tendsto (fun n => vn n x) atTop (𝓝 (v x)) := fun x =>
      ContDiffBump.convolution_tendsto_right_of_continuous hrout hv x
    -- Uniform bound of the mollifications on the image of the support.
    set D : Set ℂ := Metric.cthickening 1 (φ '' tsupport ψ) with hDdef
    have hDc : IsCompact D := hKimgc.cthickening
    obtain ⟨Cv, hCv⟩ := hDc.exists_bound_of_continuousOn hv.continuousOn
    have hvn_bd : ∀ n, ∀ x ∈ φ '' tsupport ψ, ‖vn n x‖ ≤ Cv := by
      intro n x hx
      rw [hvndef]
      simp only []
      rw [MeasureTheory.convolution_def]
      have hptbd : ∀ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ n t) (v (x - t))‖
          ≤ ρ n t * Cv := by
        intro t
        rw [ContinuousLinearMap.lsmul_apply]
        by_cases ht : t ∈ tsupport (ρ n)
        · have htball : ‖t‖ ≤ (bumps n).rOut := by
            have := (bumps n).tsupport_normed_eq (μ := volume) ▸ ht
            simpa [dist_eq_norm] using Metric.mem_closedBall.mp this
          have hxt : x - t ∈ D := by
            apply Metric.mem_cthickening_of_dist_le (x - t) x 1 _ hx
            rw [dist_eq_norm]
            simpa using htball.trans (hrout1 n)
          calc ‖ρ n t • v (x - t)‖ ≤ ‖ρ n t‖ * ‖v (x - t)‖ := norm_smul_le _ _
            _ = ρ n t * ‖v (x - t)‖ := by
                rw [Real.norm_eq_abs, abs_of_nonneg ((bumps n).nonneg_normed t)]
            _ ≤ ρ n t * Cv :=
                mul_le_mul_of_nonneg_left (hCv _ hxt) ((bumps n).nonneg_normed t)
        · have : ρ n t = 0 := image_eq_zero_of_notMem_tsupport ht
          rw [this]
          simp
      calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ n t) (v (x - t)) ∂volume‖
          ≤ ∫ t, ρ n t * Cv ∂volume := by
            apply norm_integral_le_of_norm_le
            · exact ((bumps n).integrable_normed).mul_const Cv
            · exact Filter.Eventually.of_forall hptbd
        _ = Cv := by
            rw [MeasureTheory.integral_mul_const, (bumps n).integral_normed, one_mul]
    -- Continuity of the truncated integrands.
    have hcont_dψe : Continuous (fun z => (fderiv ℝ ψ z) e) :=
      (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hts_dψe : tsupport (fun z => (fderiv ℝ ψ z) e) ⊆ tsupport ψ :=
      tsupport_fderiv_apply_subset ℝ e
    have hcover : ∀ z : ℂ, z ∈ Ω ∨ z ∉ tsupport ψ := fun z =>
      (em (z ∈ tsupport ψ)).elim (fun h => Or.inl (htsupp h)) Or.inr
    have hglue : ∀ (h : ℂ → ℂ), Continuous h →
        Continuous (fun z => ((fderiv ℝ ψ z) e) • h (φ z)) := by
      intro h hh
      rw [continuous_iff_continuousAt]
      intro z
      rcases hcover z with hz | hz
      · exact (hcont_dψe.continuousAt).smul
          ((hh.continuousAt).comp (hφcont.continuousAt (hΩ.mem_nhds hz)))
      · have hev : (fun z => ((fderiv ℝ ψ z) e) • h (φ z)) =ᶠ[𝓝 z] fun _ => 0 := by
          have hznot : z ∉ tsupport (fun z => (fderiv ℝ ψ z) e) := fun hmem => hz (hts_dψe hmem)
          filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hznot] with y hy
          rw [image_eq_zero_of_notMem_tsupport hy]
          simp
        exact ContinuousAt.congr (continuousAt_const) hev.symm
    have hLHS : Tendsto (fun n => ∫ z, ((fderiv ℝ ψ z) e) • (vn n (φ z))) atTop
        (𝓝 (∫ z, ((fderiv ℝ ψ z) e) • (v (φ z)))) := by
      apply MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun z => ‖(fderiv ℝ ψ z) e‖ * max Cv 0)
      · intro n
        exact (hglue (vn n) ((hvn_cd n).continuous)).aestronglyMeasurable
      · apply Continuous.integrable_of_hasCompactSupport
        · exact (hcont_dψe.norm).mul continuous_const
        · apply HasCompactSupport.mul_right
          exact (HasCompactSupport.fderiv_apply ℝ hcs e).norm
      · intro n
        apply Filter.Eventually.of_forall
        intro z
        by_cases hz : z ∈ tsupport ψ
        · calc ‖((fderiv ℝ ψ z) e) • vn n (φ z)‖
              ≤ ‖(fderiv ℝ ψ z) e‖ * ‖vn n (φ z)‖ := norm_smul_le _ _
            _ ≤ ‖(fderiv ℝ ψ z) e‖ * max Cv 0 :=
                mul_le_mul_of_nonneg_left
                  ((hvn_bd n (φ z) (Set.mem_image_of_mem φ hz)).trans (le_max_left _ _))
                  (norm_nonneg _)
        · have hznot : z ∉ tsupport (fun z => (fderiv ℝ ψ z) e) := fun hmem => hz (hts_dψe hmem)
          rw [image_eq_zero_of_notMem_tsupport hznot]
          simp
      · apply Filter.Eventually.of_forall
        intro z
        exact (hvn_ptw (φ z)).const_smul _
    -- ==================== RHS convergence ====================
    set Ge : ℂ → ℂ := fun z =>
      (1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
        + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
          * (starRingEnd ℂ) (deriv φ z * e) with hGedef
    have hφae : AEMeasurable φ (volume.restrict (tsupport ψ)) :=
      (hφcont.mono hKΩ).aemeasurable hKc.measurableSet
    have hd'ae : AEMeasurable (deriv φ) (volume.restrict (tsupport ψ)) :=
      (hd'cont.mono hKΩ).aemeasurable hKc.measurableSet
    obtain ⟨Cψ, hCψ⟩ := hψ.continuous.bounded_above_of_compact_support hcs
    -- Conjugation preserves the extended norm.
    have hconj_enorm : ∀ w : ℂ, ‖(starRingEnd ℂ) w‖ₑ = ‖w‖ₑ := by
      intro w
      rw [← ofReal_norm, ← ofReal_norm]
      congr 1
      simp
    have henorm_smul_le : ∀ (r : ℝ) (x : ℂ), ‖r • x‖ₑ ≤ ‖r‖ₑ * ‖x‖ₑ := by
      intro r x
      rw [← ofReal_norm, ← ofReal_norm (x := x),
        ← ofReal_norm (x := r), ← ENNReal.ofReal_mul (norm_nonneg r)]
      exact ENNReal.ofReal_le_ofReal (norm_smul_le r x)
    -- The generic algebraic bound for the Wirtinger combination.
    have habs : ∀ a b d : ℂ,
        ‖(1 / 2 : ℂ) * (a - Complex.I * b) * (d * e)
          + (1 / 2 : ℂ) * (a + Complex.I * b) * ((starRingEnd ℂ) (d * e))‖ₑ
        ≤ (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ) := by
      intro a b d
      have hIb : ∀ x y : ℂ, ‖x - Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ := by
        intro x y
        calc ‖x - Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖Complex.I * y‖ₑ := by
              rw [sub_eq_add_neg]
              exact (enorm_add_le _ _).trans (by rw [enorm_neg])
          _ = ‖x‖ₑ + ‖y‖ₑ := by
              rw [enorm_mul]
              congr 1
              rw [← ofReal_norm, Complex.norm_I]
              simp
      have hIb' : ∀ x y : ℂ, ‖x + Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ := by
        intro x y
        calc ‖x + Complex.I * y‖ₑ ≤ ‖x‖ₑ + ‖Complex.I * y‖ₑ := enorm_add_le _ _
          _ = ‖x‖ₑ + ‖y‖ₑ := by
              rw [enorm_mul]
              congr 1
              rw [← ofReal_norm, Complex.norm_I]
              simp
      have hhalf : ‖(1 / 2 : ℂ)‖ₑ = ENNReal.ofReal (1 / 2) := by
        rw [← ofReal_norm]
        congr 1
        simp
      calc ‖(1 / 2 : ℂ) * (a - Complex.I * b) * (d * e)
          + (1 / 2 : ℂ) * (a + Complex.I * b) * ((starRingEnd ℂ) (d * e))‖ₑ
          ≤ ‖(1 / 2 : ℂ) * (a - Complex.I * b) * (d * e)‖ₑ
            + ‖(1 / 2 : ℂ) * (a + Complex.I * b) * ((starRingEnd ℂ) (d * e))‖ₑ :=
            enorm_add_le _ _
        _ = ‖(1 / 2 : ℂ)‖ₑ * ‖a - Complex.I * b‖ₑ * (‖d‖ₑ * ‖e‖ₑ)
            + ‖(1 / 2 : ℂ)‖ₑ * ‖a + Complex.I * b‖ₑ * (‖d‖ₑ * ‖e‖ₑ) := by
            simp only [enorm_mul, hconj_enorm]
        _ ≤ ‖(1 / 2 : ℂ)‖ₑ * (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ)
            + ‖(1 / 2 : ℂ)‖ₑ * (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ) := by
            gcongr
            · exact hIb a b
            · exact hIb' a b
        _ = (‖(1 / 2 : ℂ)‖ₑ + ‖(1 / 2 : ℂ)‖ₑ) * ((‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ)) := by ring
        _ = (‖a‖ₑ + ‖b‖ₑ) * (‖d‖ₑ * ‖e‖ₑ) := by
            rw [hhalf, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
            norm_num
    -- The Cauchy–Schwarz + change-of-variables engine.
    have hCS : ∀ q : ℂ → ℂ, Measurable q →
        (∫⁻ z in tsupport ψ, ‖q (φ z)‖ₑ * ‖deriv φ z‖ₑ ∂volume)
          ≤ (((N : ℝ≥0∞) * ∫⁻ w in φ '' tsupport ψ, ‖q w‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ))
            * (volume (tsupport ψ)) ^ (1 / 2 : ℝ) := by
      intro q hq
      have hHolder : (2 : ℝ).HolderConjugate 2 := by
        rw [Real.holderConjugate_iff]
        norm_num
      have hfae' : AEMeasurable (fun z => ‖q (φ z)‖ₑ * ‖deriv φ z‖ₑ)
          (volume.restrict (tsupport ψ)) := by
        have h := (hq.comp_aemeasurable hφae).enorm.mul hd'ae.enorm
        simpa [Function.comp] using! h
      have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (tsupport ψ))
        hHolder hfae' (aemeasurable_const (b := (1 : ℝ≥0∞)))
      simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one,
        Measure.restrict_apply_univ] at h
      refine h.trans ?_
      gcongr
      have hsq : (∫⁻ z in tsupport ψ, (‖q (φ z)‖ₑ * ‖deriv φ z‖ₑ) ^ (2 : ℝ) ∂volume)
          = ∫⁻ z in tsupport ψ, ‖q (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume := by
        apply lintegral_congr
        intro z
        conv_lhs => rw [show ((2 : ℝ)) = (((2 : ℕ) : ℝ)) by norm_num,
          ENNReal.rpow_natCast]
        rw [mul_pow]
      calc (∫⁻ z in tsupport ψ, (‖q (φ z)‖ₑ * ‖deriv φ z‖ₑ) ^ (2 : ℝ) ∂volume)
          = ∫⁻ z in tsupport ψ, ‖q (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ) ∂volume := hsq
        _ ≤ (N : ℝ≥0∞) * ∫⁻ w in φ '' tsupport ψ, ‖q w‖ₑ ^ (2 : ℕ) ∂volume := hCV q hq
    -- Finiteness of the limit integrand.
    have hIK_gx : (∫⁻ w in φ '' tsupport ψ, ‖gx w‖ₑ ^ (2 : ℕ) ∂volume) < ⊤ :=
      p_fin (hgx2 (φ '' tsupport ψ) (Set.subset_univ _) hKimgc)
    have hIK_gy : (∫⁻ w in φ '' tsupport ψ, ‖gy w‖ₑ ^ (2 : ℕ) ∂volume) < ⊤ :=
      p_fin (hgy2 (φ '' tsupport ψ) (Set.subset_univ _) hKimgc)
    have hCS_fin : ∀ q : ℂ → ℂ, Measurable q →
        (∫⁻ w in φ '' tsupport ψ, ‖q w‖ₑ ^ (2 : ℕ) ∂volume) < ⊤ →
        (∫⁻ z in tsupport ψ, ‖q (φ z)‖ₑ * ‖deriv φ z‖ₑ ∂volume) < ⊤ := by
      intro q hq hfin
      refine lt_of_le_of_lt (hCS q hq) ?_
      apply ENNReal.mul_lt_top
      · apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        exact (ENNReal.mul_lt_top (by simp) hfin).ne
      · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKc.measure_lt_top.ne
    have hK_fin_x : (∫⁻ z in tsupport ψ, ‖gx (φ z)‖ₑ * ‖deriv φ z‖ₑ ∂volume) < ⊤ :=
      hCS_fin gx hgx_meas hIK_gx
    have hK_fin_y : (∫⁻ z in tsupport ψ, ‖gy (φ z)‖ₑ * ‖deriv φ z‖ₑ ∂volume) < ⊤ :=
      hCS_fin gy hgy_meas hIK_gy
    -- Integrability of the limit right-hand side.
    have hGe_int : Integrable (fun z => ψ z • Ge z) volume := by
      have hsupp : Function.support (fun z => ψ z • Ge z) ⊆ tsupport ψ := by
        intro z hz
        by_contra hzn
        apply hz
        change ψ z • Ge z = 0
        rw [image_eq_zero_of_notMem_tsupport hzn]
        simp
      rw [← integrableOn_iff_integrable_of_support_subset hsupp]
      constructor
      · apply AEMeasurable.aestronglyMeasurable
        have h1 : AEMeasurable (fun z => gx (φ z)) (volume.restrict (tsupport ψ)) :=
          hgx_meas.comp_aemeasurable hφae
        have h2 : AEMeasurable (fun z => gy (φ z)) (volume.restrict (tsupport ψ)) :=
          hgy_meas.comp_aemeasurable hφae
        have h3 : AEMeasurable (fun z => (starRingEnd ℂ) (deriv φ z * e))
            (volume.restrict (tsupport ψ)) :=
          (Complex.continuous_conj.measurable).comp_aemeasurable (hd'ae.mul_const e)
        have hGeae : AEMeasurable Ge (volume.restrict (tsupport ψ)) := by
          rw [hGedef]
          exact ((aemeasurable_const.mul (h1.sub (aemeasurable_const.mul h2))).mul
              (hd'ae.mul_const e)).add
            ((aemeasurable_const.mul (h1.add (aemeasurable_const.mul h2))).mul h3)
        exact (hψ.continuous.aemeasurable.restrict).smul hGeae
      · rw [hasFiniteIntegral_iff_enorm]
        have hptw : ∀ z ∈ tsupport ψ, ‖ψ z • Ge z‖ₑ
            ≤ ENNReal.ofReal Cψ * ‖e‖ₑ
              * ((‖gx (φ z)‖ₑ * ‖deriv φ z‖ₑ) + (‖gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) := by
          intro z _
          calc ‖ψ z • Ge z‖ₑ ≤ ‖ψ z‖ₑ * ‖Ge z‖ₑ := henorm_smul_le _ _
            _ ≤ ENNReal.ofReal Cψ * ((‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ)
                * (‖deriv φ z‖ₑ * ‖e‖ₑ)) := by
                apply mul_le_mul'
                · rw [← ofReal_norm]
                  exact ENNReal.ofReal_le_ofReal (hCψ z)
                · rw [hGedef]
                  exact habs _ _ _
            _ = ENNReal.ofReal Cψ * ‖e‖ₑ
                * ((‖gx (φ z)‖ₑ * ‖deriv φ z‖ₑ) + (‖gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) := by
                ring
        calc (∫⁻ z in tsupport ψ, ‖ψ z • Ge z‖ₑ ∂volume)
            ≤ ∫⁻ z in tsupport ψ, ENNReal.ofReal Cψ * ‖e‖ₑ
              * ((‖gx (φ z)‖ₑ * ‖deriv φ z‖ₑ) + (‖gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) ∂volume :=
              setLIntegral_mono' hKc.measurableSet hptw
          _ = ENNReal.ofReal Cψ * ‖e‖ₑ * ∫⁻ z in tsupport ψ,
              ((‖gx (φ z)‖ₑ * ‖deriv φ z‖ₑ) + (‖gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) ∂volume := by
              rw [lintegral_const_mul' _ _ (by
                exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top)]
          _ < ⊤ := by
              apply ENNReal.mul_lt_top
                (ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top)
              have hax : AEMeasurable (fun z => ‖gx (φ z)‖ₑ * ‖deriv φ z‖ₑ)
                  (volume.restrict (tsupport ψ)) := by
                have h := (hgx_meas.comp_aemeasurable hφae).enorm.mul hd'ae.enorm
                simpa [Function.comp] using! h
              rw [lintegral_add_left' hax]
              exact ENNReal.add_lt_top.mpr ⟨hK_fin_x, hK_fin_y⟩
    -- Integrability of the mollified right-hand sides.
    have hloc_n : ∀ n, LocallyIntegrableOn
        (fun z => (fderiv ℝ (fun y => vn n (φ y)) z) e) Ω := fun n =>
      (((hcomp_cd n).continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply
        continuousOn_const).locallyIntegrableOn hΩ.measurableSet
    have i_n : ∀ n, Integrable
        (fun z => ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e)) volume := fun n =>
      d2_integ_real ψ hψ.continuous hcs htsupp (hloc_n n)
    -- The localized mollification convergence.
    have hXn := p_mollify_L2 hgx_meas hgx2 hKimgc bumps hrout hrout1
    have hYn := p_mollify_L2 hgy_meas hgy2 hKimgc bumps hrout hrout1
    -- The per-`n` difference bound.
    set Xn : ℕ → ℝ≥0∞ := fun n => ∫⁻ w in φ '' tsupport ψ,
      ‖cx n w - gx w‖ₑ ^ (2 : ℕ) ∂volume with hXndef
    set Yn : ℕ → ℝ≥0∞ := fun n => ∫⁻ w in φ '' tsupport ψ,
      ‖cy n w - gy w‖ₑ ^ (2 : ℕ) ∂volume with hYndef
    have hcx_cont : ∀ n, Continuous (cx n) := fun n =>
      HasCompactSupport.continuous_convolution_left _ (hρ_cs n)
        (hρ_sm n).continuous hgx_li
    have hcy_cont : ∀ n, Continuous (cy n) := fun n =>
      HasCompactSupport.continuous_convolution_left _ (hρ_cs n)
        (hρ_sm n).continuous hgy_li
    have hdiff_bd : ∀ n,
        ‖(∫ z, ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e)) - ∫ z, ψ z • Ge z‖ₑ
        ≤ ENNReal.ofReal Cψ * ‖e‖ₑ
          * ((((N : ℝ≥0∞) * Xn n) ^ (1 / 2 : ℝ)) * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)
            + (((N : ℝ≥0∞) * Yn n) ^ (1 / 2 : ℝ)) * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)) := by
      intro n
      rw [← integral_sub (i_n n) hGe_int]
      refine le_trans (MeasureTheory.enorm_integral_le_lintegral_enorm _) ?_
      have hzero : ∀ z ∉ tsupport ψ,
          ‖ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) - ψ z • Ge z‖ₑ = 0 := by
        intro z hz
        rw [image_eq_zero_of_notMem_tsupport hz]
        simp
      have hred : (∫⁻ z, ‖ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) - ψ z • Ge z‖ₑ ∂volume)
          = ∫⁻ z in tsupport ψ,
            ‖ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) - ψ z • Ge z‖ₑ ∂volume := by
        rw [← lintegral_indicator hKc.measurableSet]
        apply lintegral_congr
        intro z
        by_cases hz : z ∈ tsupport ψ
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, hzero z hz]
      rw [hred]
      have hptw : ∀ z ∈ tsupport ψ,
          ‖ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) - ψ z • Ge z‖ₑ
          ≤ ENNReal.ofReal Cψ * ‖e‖ₑ
            * ((‖cx n (φ z) - gx (φ z)‖ₑ * ‖deriv φ z‖ₑ)
              + (‖cy n (φ z) - gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) := by
        intro z hz
        have hzΩ : z ∈ Ω := htsupp hz
        have hdiff_eq : ((fderiv ℝ (fun y => vn n (φ y)) z) e) - Ge z
            = (1 / 2 : ℂ) * ((cx n (φ z) - gx (φ z))
                - Complex.I * (cy n (φ z) - gy (φ z))) * (deriv φ z * e)
              + (1 / 2 : ℂ) * ((cx n (φ z) - gx (φ z))
                + Complex.I * (cy n (φ z) - gy (φ z)))
                * ((starRingEnd ℂ) (deriv φ z * e)) := by
          rw [hchain n z hzΩ, hGedef]
          ring
        calc ‖ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) - ψ z • Ge z‖ₑ
            = ‖ψ z • (((fderiv ℝ (fun y => vn n (φ y)) z) e) - Ge z)‖ₑ := by
              rw [show ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) - ψ z • Ge z
                = ψ z • (((fderiv ℝ (fun y => vn n (φ y)) z) e) - Ge z) from
                  (smul_sub _ _ _).symm]
          _ ≤ ‖ψ z‖ₑ * ‖((fderiv ℝ (fun y => vn n (φ y)) z) e) - Ge z‖ₑ :=
              henorm_smul_le _ _
          _ ≤ ENNReal.ofReal Cψ * ((‖cx n (φ z) - gx (φ z)‖ₑ + ‖cy n (φ z) - gy (φ z)‖ₑ)
              * (‖deriv φ z‖ₑ * ‖e‖ₑ)) := by
              apply mul_le_mul'
              · rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hCψ z)
              · rw [hdiff_eq]
                exact habs _ _ _
          _ = ENNReal.ofReal Cψ * ‖e‖ₑ
              * ((‖cx n (φ z) - gx (φ z)‖ₑ * ‖deriv φ z‖ₑ)
                + (‖cy n (φ z) - gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) := by
              ring
      calc (∫⁻ z in tsupport ψ,
          ‖ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) - ψ z • Ge z‖ₑ ∂volume)
          ≤ ∫⁻ z in tsupport ψ, ENNReal.ofReal Cψ * ‖e‖ₑ
            * ((‖cx n (φ z) - gx (φ z)‖ₑ * ‖deriv φ z‖ₑ)
              + (‖cy n (φ z) - gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) ∂volume :=
            setLIntegral_mono' hKc.measurableSet hptw
        _ = ENNReal.ofReal Cψ * ‖e‖ₑ * ∫⁻ z in tsupport ψ,
            ((‖cx n (φ z) - gx (φ z)‖ₑ * ‖deriv φ z‖ₑ)
              + (‖cy n (φ z) - gy (φ z)‖ₑ * ‖deriv φ z‖ₑ)) ∂volume := by
            rw [lintegral_const_mul' _ _ (by
              exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top)]
        _ ≤ ENNReal.ofReal Cψ * ‖e‖ₑ
            * ((((N : ℝ≥0∞) * Xn n) ^ (1 / 2 : ℝ)) * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)
              + (((N : ℝ≥0∞) * Yn n) ^ (1 / 2 : ℝ)) * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)) := by
            apply mul_le_mul_right
            have hax : AEMeasurable (fun z => ‖cx n (φ z) - gx (φ z)‖ₑ * ‖deriv φ z‖ₑ)
                (volume.restrict (tsupport ψ)) := by
              have h := (((hcx_cont n).measurable.sub hgx_meas).comp_aemeasurable
                hφae).enorm.mul hd'ae.enorm
              simpa [Function.comp] using! h
            rw [lintegral_add_left' hax]
            exact add_le_add
              (hCS (fun w => cx n w - gx w) ((hcx_cont n).measurable.sub hgx_meas))
              (hCS (fun w => cy n w - gy w) ((hcy_cont n).measurable.sub hgy_meas))
    -- The bound tends to zero.
    have hbound_tendsto : Tendsto (fun n => ENNReal.ofReal Cψ * ‖e‖ₑ
        * ((((N : ℝ≥0∞) * Xn n) ^ (1 / 2 : ℝ)) * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)
          + (((N : ℝ≥0∞) * Yn n) ^ (1 / 2 : ℝ)) * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)))
        atTop (𝓝 0) := by
      have hX0 : Tendsto (fun n => (N : ℝ≥0∞) * Xn n) atTop (𝓝 0) := by
        have := (ENNReal.Tendsto.const_mul hXn (Or.inr (ENNReal.natCast_ne_top N)) :
          Tendsto (fun n => (N : ℝ≥0∞) * Xn n) atTop (𝓝 ((N : ℝ≥0∞) * 0)))
        simpa using this
      have hY0 : Tendsto (fun n => (N : ℝ≥0∞) * Yn n) atTop (𝓝 0) := by
        have := (ENNReal.Tendsto.const_mul hYn (Or.inr (ENNReal.natCast_ne_top N)) :
          Tendsto (fun n => (N : ℝ≥0∞) * Yn n) atTop (𝓝 ((N : ℝ≥0∞) * 0)))
        simpa using this
      have hrp0 : ((0 : ℝ≥0∞)) ^ (1 / 2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      have hXr : Tendsto (fun n => ((N : ℝ≥0∞) * Xn n) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have hc := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞)
        have h2 := hc.comp hX0
        rw [hrp0] at h2
        simpa [Function.comp] using! h2
      have hYr : Tendsto (fun n => ((N : ℝ≥0∞) * Yn n) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have hc := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto (0 : ℝ≥0∞)
        have h2 := hc.comp hY0
        rw [hrp0] at h2
        simpa [Function.comp] using! h2
      have hvol : (volume (tsupport ψ)) ^ (1 / 2 : ℝ) ≠ ⊤ :=
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKc.measure_lt_top.ne).ne
      have hXv : Tendsto (fun n => (((N : ℝ≥0∞) * Xn n) ^ (1 / 2 : ℝ))
          * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.mul_const hXr (Or.inr hvol)
        simpa using this
      have hYv : Tendsto (fun n => (((N : ℝ≥0∞) * Yn n) ^ (1 / 2 : ℝ))
          * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.mul_const hYr (Or.inr hvol)
        simpa using this
      have hsum : Tendsto (fun n => (((N : ℝ≥0∞) * Xn n) ^ (1 / 2 : ℝ))
          * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)
          + (((N : ℝ≥0∞) * Yn n) ^ (1 / 2 : ℝ))
          * (volume (tsupport ψ)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have := hXv.add hYv
        simpa using this
      have hconst : (ENNReal.ofReal Cψ * ‖e‖ₑ) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top
      have := ENNReal.Tendsto.const_mul hsum (Or.inr hconst)
      simpa using this
    -- Difference tends to zero in extended norm, hence the integrals converge.
    have henorm0 : Tendsto (fun n =>
        ‖(∫ z, ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e)) - ∫ z, ψ z • Ge z‖ₑ)
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound_tendsto
        (fun n => zero_le) hdiff_bd
    have hRHS : Tendsto (fun n => ∫ z, ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e))
        atTop (𝓝 (∫ z, ψ z • Ge z)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h1 : Tendsto (fun n =>
          (‖(∫ z, ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e)) - ∫ z, ψ z • Ge z‖ₑ).toReal)
          atTop (𝓝 ((0 : ℝ≥0∞)).toReal)  :=
        (ENNReal.tendsto_toReal (by simp)).comp henorm0
      simpa [toReal_enorm] using h1
    -- Conclude by uniqueness of limits.
    have hAn : Tendsto (fun n => ∫ z, ((fderiv ℝ ψ z) e) • (vn n (φ z))) atTop
        (𝓝 (- ∫ z, ψ z • Ge z)) := by
      have heq : (fun n => ∫ z, ((fderiv ℝ ψ z) e) • (vn n (φ z)))
          = fun n => - ∫ z, ψ z • ((fderiv ℝ (fun y => vn n (φ y)) z) e) :=
        funext hweak_n
      rw [heq]
      exact hRHS.neg
    exact tendsto_nhds_unique hLHS hAn
  classical
  obtain ⟨gx0, gy0, hw0, hgx20, hgy20, hcombo0⟩ := hgrad
  have hφa : AnalyticOnNhd ℂ φ Ω := hφ.analyticOnNhd hΩ
  have hφcont : ContinuousOn φ Ω := hφ.continuousOn
  have hd'cont : ContinuousOn (deriv φ) Ω := hφa.deriv.continuousOn
  -- ================= measurable representatives of the witnesses =================
  have hUball : (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    obtain ⟨n, hn⟩ := exists_nat_ge (dist z 0)
    exact Set.mem_iUnion.mpr ⟨n, Metric.mem_closedBall.mpr hn⟩
  have hasm : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
      AEStronglyMeasurable g volume := by
    intro g hg
    have h1 : ∀ n : ℕ, AEStronglyMeasurable g
        (volume.restrict (Metric.closedBall (0 : ℂ) n)) := fun n =>
      (hg _ (Set.subset_univ _) (isCompact_closedBall 0 n)).1
    have h2 : AEStronglyMeasurable g
        (volume.restrict (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n)) :=
      aestronglyMeasurable_iUnion_iff.mpr h1
    rwa [hUball, Measure.restrict_univ] at h2
  have hgx_asm : AEStronglyMeasurable gx0 volume := hasm hgx20
  have hgy_asm : AEStronglyMeasurable gy0 volume := hasm hgy20
  set gx : ℂ → ℂ := hgx_asm.mk gx0 with hgxdef
  set gy : ℂ → ℂ := hgy_asm.mk gy0 with hgydef
  have hgx_meas : Measurable gx := hgx_asm.stronglyMeasurable_mk.measurable
  have hgy_meas : Measurable gy := hgy_asm.stronglyMeasurable_mk.measurable
  have haex : gx0 =ᵐ[volume] gx := hgx_asm.ae_eq_mk
  have haey : gy0 =ᵐ[volume] gy := hgy_asm.ae_eq_mk
  have hwd_congr : ∀ {g g' : ℂ → ℂ} {e : ℂ}, HasWeakDirDeriv e g v Set.univ →
      g =ᵐ[volume] g' → HasWeakDirDeriv e g' v Set.univ := by
    intro g g' e h hgg' ψ hψ hcs hts
    rw [h ψ hψ hcs hts]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hgg'] with z hz
    rw [hz]
  have hwx : HasWeakDirDeriv 1 gx v Set.univ := hwd_congr hw0.1 haex
  have hwy : HasWeakDirDeriv Complex.I gy v Set.univ := hwd_congr hw0.2 haey
  have hgx2 : MemLpLocOn gx 2 Set.univ := fun K hK hKc =>
    MemLp.ae_eq (ae_restrict_of_ae haex) (hgx20 K hK hKc)
  have hgy2 : MemLpLocOn gy 2 Set.univ := fun K hK hKc =>
    MemLp.ae_eq (ae_restrict_of_ae haey) (hgy20 K hK hKc)
  have hcombo : ∀ᵐ w ∂(volume : Measure ℂ), gx w + Complex.I * gy w = 2 * μ w := by
    filter_upwards [hcombo0, haex, haey] with w h1 h2 h3
    rw [← h2, ← h3]
    exact h1 (Set.mem_univ w)
  -- ================= L²loc membership, uniformly in the direction =================
  have hmem : ∀ e : ℂ, MemLpLocOn (fun z =>
      (1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
      + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
        * (starRingEnd ℂ) (deriv φ z * e)) 2 Ω := by
    intro e K hK hKc
    obtain ⟨N, hCV⟩ := b_cv hΩ hφ hK hKc
    have hφae : AEMeasurable φ (volume.restrict K) :=
      (hφcont.mono hK).aemeasurable hKc.measurableSet
    have hd'ae : AEMeasurable (deriv φ) (volume.restrict K) :=
      (hd'cont.mono hK).aemeasurable hKc.measurableSet
    have hKimgc : IsCompact (φ '' K) := hKc.image_of_continuousOn (hφcont.mono hK)
    have h1 : AEMeasurable (fun z => gx (φ z)) (volume.restrict K) :=
      hgx_meas.comp_aemeasurable hφae
    have h2 : AEMeasurable (fun z => gy (φ z)) (volume.restrict K) :=
      hgy_meas.comp_aemeasurable hφae
    have h3 : AEMeasurable (fun z => (starRingEnd ℂ) (deriv φ z * e))
        (volume.restrict K) :=
      (Complex.continuous_conj.measurable).comp_aemeasurable (hd'ae.mul_const e)
    constructor
    · exact (((aemeasurable_const.mul (h1.sub (aemeasurable_const.mul h2))).mul
          (hd'ae.mul_const e)).add
        ((aemeasurable_const.mul (h1.add (aemeasurable_const.mul h2))).mul
          h3)).aestronglyMeasurable
    · rw [p_conv2]
      apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      have hbd : ∀ z, ‖(1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
          + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
            * (starRingEnd ℂ) (deriv φ z * e)‖ₑ ^ (2 : ℕ)
          ≤ 4 * ‖e‖ₑ ^ (2 : ℕ)
            * ((‖gx (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))
              + (‖gy (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))) := by
        intro z
        calc ‖(1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
            + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
              * (starRingEnd ℂ) (deriv φ z * e)‖ₑ ^ (2 : ℕ)
            ≤ ((‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) * (‖deriv φ z‖ₑ * ‖e‖ₑ)) ^ (2 : ℕ) := by
              gcongr
              exact e7_habs _ _ _ _
          _ = (‖gx (φ z)‖ₑ + ‖gy (φ z)‖ₑ) ^ (2 : ℕ)
              * (‖deriv φ z‖ₑ ^ (2 : ℕ) * ‖e‖ₑ ^ (2 : ℕ)) := by
              rw [mul_pow, mul_pow]
          _ ≤ (4 * (‖gx (φ z)‖ₑ ^ (2 : ℕ) + ‖gy (φ z)‖ₑ ^ (2 : ℕ)))
              * (‖deriv φ z‖ₑ ^ (2 : ℕ) * ‖e‖ₑ ^ (2 : ℕ)) := by
              gcongr
              exact e8_sum_sq _ _
          _ = 4 * ‖e‖ₑ ^ (2 : ℕ)
              * ((‖gx (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))
                + (‖gy (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))) := by
              ring
      have haxsq : AEMeasurable
          (fun z => ‖gx (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))
          (volume.restrict K) := by
        have h := (h1.enorm.pow_const 2).mul (hd'ae.enorm.pow_const 2)
        simpa using! h
      have hfin : (∫⁻ z in K,
          ((‖gx (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))
            + (‖gy (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))) ∂volume) < ⊤ := by
        rw [lintegral_add_left' haxsq]
        apply ENNReal.add_lt_top.mpr
        constructor
        · refine lt_of_le_of_lt (hCV gx hgx_meas) ?_
          exact ENNReal.mul_lt_top (by simp)
            (p_fin (hgx2 (φ '' K) (Set.subset_univ _) hKimgc))
        · refine lt_of_le_of_lt (hCV gy hgy_meas) ?_
          exact ENNReal.mul_lt_top (by simp)
            (p_fin (hgy2 (φ '' K) (Set.subset_univ _) hKimgc))
      have htotal : (∫⁻ z in K,
          ‖(1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
          + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
            * (starRingEnd ℂ) (deriv φ z * e)‖ₑ ^ (2 : ℕ) ∂volume) < ⊤ := by
        calc (∫⁻ z in K, ‖(1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * e)
            + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
              * (starRingEnd ℂ) (deriv φ z * e)‖ₑ ^ (2 : ℕ) ∂volume)
            ≤ ∫⁻ z in K, 4 * ‖e‖ₑ ^ (2 : ℕ)
              * ((‖gx (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))
                + (‖gy (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))) ∂volume :=
              lintegral_mono (fun z => hbd z)
          _ = 4 * ‖e‖ₑ ^ (2 : ℕ) * ∫⁻ z in K,
              ((‖gx (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))
                + (‖gy (φ z)‖ₑ ^ (2 : ℕ) * ‖deriv φ z‖ₑ ^ (2 : ℕ))) ∂volume := by
              rw [lintegral_const_mul' _ _ (by
                exact ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top enorm_ne_top))]
          _ < ⊤ := by
              apply ENNReal.mul_lt_top _ hfin
              exact ENNReal.mul_lt_top (by simp) (ENNReal.pow_lt_top enorm_lt_top)
      exact htotal.ne
  -- ================= the witnesses =================
  refine ⟨fun z => (1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * 1)
      + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
        * (starRingEnd ℂ) (deriv φ z * 1),
    fun z => (1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z * Complex.I)
      + (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
        * (starRingEnd ℂ) (deriv φ z * Complex.I),
    ⟨d_comp_weak hΩ hφ hv hgx_meas hgy_meas hwx hwy hgx2 hgy2 1,
      d_comp_weak hΩ hφ hv hgx_meas hgy_meas hwx hwy hgx2 hgy2 Complex.I⟩,
    hmem 1, hmem Complex.I, ?_⟩
  -- ================= the Wirtinger combination =================
  have hEnull : volume {w : ℂ | ¬ (gx w + Complex.I * gy w = 2 * μ w)} = 0 :=
    ae_iff.mp hcombo
  filter_upwards [c_preimage_null hΩ hφ hEnull] with z hz hzΩ
  by_cases hd : deriv φ z = 0
  · simp [hd]
  · have hφzE : φ z ∉ {w : ℂ | ¬ (gx w + Complex.I * gy w = 2 * μ w)} := hz hzΩ hd
    have hP : gx (φ z) + Complex.I * gy (φ z) = 2 * μ (φ z) := by
      by_contra hne
      exact hφzE hne
    have hconjI : (starRingEnd ℂ) (deriv φ z * Complex.I)
        = (starRingEnd ℂ) (deriv φ z) * (- Complex.I) := by
      rw [map_mul, Complex.conj_I]
    have hconj1 : (starRingEnd ℂ) (deriv φ z * 1) = (starRingEnd ℂ) (deriv φ z) := by
      rw [mul_one]
    rw [hconjI, hconj1]
    linear_combination ((starRingEnd ℂ) (deriv φ z)) * hP
      + ((1 / 2 : ℂ) * (gx (φ z) - Complex.I * gy (φ z)) * (deriv φ z)
        - (1 / 2 : ℂ) * (gx (φ z) + Complex.I * gy (φ z))
          * ((starRingEnd ℂ) (deriv φ z))) * Complex.I_mul_I

end NoWanderingDomains
