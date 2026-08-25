/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.Deformation.SphereVectorField.Transport
import NoWanderingDomains.QC.Calculus.WeylLocal
import NoWanderingDomains.Sphere.OpenMapping
import NoWanderingDomains.Sphere.Iterate
import NoWanderingDomains.Dynamics.JuliaFatou.RepellingDensity

/-!
# The delta operator of a rational map and its section space

For a rational map given by `r : RationalData`, a continuous vector field `v`
determines the deformation field `δv = f′·v − v ∘ f` read in the finite chart
(`deltaField`), with `f′` the finite-chart derivative `wronskian/denReduced²`
(`fderivRational`). The concrete `(2d+1)`-dimensional target is
`SectionSpaceCarrier r = {A/denReduced² : A ∈ ℂ[X], natDegree A ≤ 2d}`, with
representatives unique off the poles. The weak-Wirtinger product rule with a
holomorphic factor closes the file.

* `fderivRational`, `IsInvariantBeltrami`, `deltaField` — the chart data.
* `SectionSpaceCarrier`, `finrank_sectionSpaceCarrier`,
  `sectionSpaceCarrier_eqOn_nonpoles_eq` — the finite-dimensional target.
* `hasL2WeakDzbar_holomorphic_mul` — the product rule.
-/

open MeasureTheory Complex Metric Filter Topology Polynomial OnePoint

namespace NoWanderingDomains

/-! ## The finite-chart derivative and the invariance law -/

/-- The finite-chart derivative of the rational map given by `r`: the
Wronskian of the reduced representation divided by the squared reduced
denominator. Away from the poles this equals the derivative of the
finite-chart reading (`RationalData.deriv_reading`); at a pole the value is
junk (`x/0 = 0` in Lean) and every downstream statement restricts to
non-poles or works almost everywhere. -/
noncomputable def fderivRational (r : RationalData) : ℂ → ℂ := fun z =>
  r.wronskian.eval z / (r.denReduced.eval z) ^ 2

/-- Away from poles, `fderivRational` is the derivative of the finite-chart
reading of the map. -/
theorem fderivRational_eq_deriv_reading (r : RationalData) {w : ℂ}
    (hden : r.denReduced.eval w ≠ 0) :
    fderivRational r w
      = deriv (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂)))) w := by
  exact (r.deriv_reading hden).symm

/-- A coefficient `μ : ℂ → ℂ` is an **invariant Beltrami coefficient** for
the rational map given by `r` when the pullback law `f*μ = μ` holds almost
everywhere in the finite chart. The pullback convention is

`(f*μ)(z) = μ(f z) · conj(f′(z)) / f′(z)`,

and the law is stated in multiplied-out form to avoid division:

`μ(z) · f′(z) = μ(f z) · conj(f′(z))` for a.e. `z`,

with `f′ = fderivRational r` and `f z` read through `chartFiniteMap` (the
junk value `0` at the finitely many poles is harmless almost everywhere).
`Spreading.lean` *proves* this law for coefficients spread from a seed on a
wandering component; this file *consumes* it to kill the weak `∂̄` of the
deformation field. -/
def IsInvariantBeltrami (r : RationalData) (μ : ℂ → ℂ) : Prop :=
  ∀ᵐ z ∂(volume : Measure ℂ),
    μ z * fderivRational r z
      = μ (chartFiniteMap (r.toSphereMap ((z : ℂ̂))))
          * starRingEnd ℂ (fderivRational r z)

/-! ## The delta operator -/

/-- The **deformation field** `δv = f′·v − v∘f` of a vector field `v` along
the rational map given by `r`, read in the finite chart. Total: at a pole of
`f` the value is junk (`fderivRational` is junk there and the composition
point is the junk reading `0` of `∞`), and every statement about `deltaField`
restricts to non-poles. -/
noncomputable def deltaField (r : RationalData) (v : ℂ → ℂ) : ℂ → ℂ := fun z =>
  fderivRational r z * v z
    - v (chartFiniteMap (r.toSphereMap ((z : ℂ̂))))

/-! ## The finite-dimensional section space -/

/-- The linear map sending a polynomial `A` to the function
`z ↦ A(z)/denReduced(z)²` — the concrete realization of "polynomial sections
over the squared denominator". -/
noncomputable def polyOverDenSq (r : RationalData) : ℂ[X] →ₗ[ℂ] (ℂ → ℂ) where
  toFun A := fun z => A.eval z / (r.denReduced.eval z) ^ 2
  map_add' A B := by
    funext z
    simp [Polynomial.eval_add, add_div]
  map_smul' c A := by
    funext z
    simp [Polynomial.eval_smul, smul_eq_mul, mul_div_assoc]

/-- The **section space** of the rational map given by `r`: the space of
functions `z ↦ A(z)/denReduced(z)²` with `A` a polynomial of degree at most
`2·degree r` — concretely, the image of `Polynomial.degreeLT ℂ (2d+1)` under
`polyOverDenSq`. This is the chart-concrete model of the space of holomorphic
sections of the pullback bundle `f*(T ℂ̂)`, of dimension `2d+1`. -/
noncomputable def SectionSpaceCarrier (r : RationalData) : Submodule ℂ (ℂ → ℂ) :=
  (Polynomial.degreeLT ℂ (2 * r.degree + 1)).map (polyOverDenSq r)

/-- Unfolding characterization of the section space: membership means being
the function `A/denReduced²` for some polynomial `A` with
`natDegree A ≤ 2·degree r`. -/
theorem mem_sectionSpaceCarrier_iff {r : RationalData} {s : ℂ → ℂ} :
    s ∈ SectionSpaceCarrier r
      ↔ ∃ A : ℂ[X], A.natDegree ≤ 2 * r.degree ∧
          s = fun z => A.eval z / (r.denReduced.eval z) ^ 2 := by
  unfold SectionSpaceCarrier
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨A, hA, hAs⟩
    rw [Polynomial.mem_degreeLT] at hA
    refine ⟨A, ?_, hAs.symm⟩
    by_cases h0 : A = 0
    · simp [h0]
    · have h1 := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hA
      omega
  · rintro ⟨A, hA, rfl⟩
    refine ⟨A, ?_, rfl⟩
    rw [Polynomial.mem_degreeLT]
    by_cases h0 : A = 0
    · rw [h0, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mp (by omega)

/-- Two elements of the section space that agree off the (finitely many)
poles are equal: `A/Q²` determines `A` by polynomial function-agreement off a
finite set, and the junk values at the poles are `0` for both. This provides
the uniqueness of the carrier representative of a deformation field, which
makes the endgame's linear map into the carrier well defined. -/
theorem sectionSpaceCarrier_eqOn_nonpoles_eq {r : RationalData} {s₁ s₂ : ℂ → ℂ}
    (h₁ : s₁ ∈ SectionSpaceCarrier r) (h₂ : s₂ ∈ SectionSpaceCarrier r)
    (h : ∀ z : ℂ, r.denReduced.eval z ≠ 0 → s₁ z = s₂ z) :
    s₁ = s₂ := by
  obtain ⟨A, -, rfl⟩ := mem_sectionSpaceCarrier_iff.mp h₁
  obtain ⟨B, -, hB⟩ := mem_sectionSpaceCarrier_iff.mp h₂
  subst hB
  have hden : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  have hAB : A = B := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := {x : ℂ | r.denReduced.IsRoot x}ᶜ)
    · intro z hz
      have hz' : r.denReduced.eval z ≠ 0 := hz
      have hq : (r.denReduced.eval z) ^ 2 ≠ 0 := pow_ne_zero _ hz'
      have hzz := h z hz'
      simp only at hzz
      exact mul_right_cancel₀ hq ((div_eq_div_iff hq hq).mp hzz)
    · exact (Polynomial.finite_setOfPred_isRoot hden).infinite_compl
  rw [hAB]

/-- The section space has dimension `2d+1`: the parametrization
`A ↦ A/denReduced²` is injective on `degreeLT ℂ (2d+1)` (a polynomial is
determined by its values off the finite root set of `denReduced`), and
`degreeLT ℂ (2d+1)` has dimension `2d+1`. -/
theorem finrank_sectionSpaceCarrier (r : RationalData) :
    Module.finrank ℂ (SectionSpaceCarrier r) = 2 * r.degree + 1 := by
  have hden : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  have hinj : Function.Injective (polyOverDenSq r) := by
    rw [injective_iff_map_eq_zero]
    intro A hA
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := {x : ℂ | r.denReduced.IsRoot x}ᶜ)
    · intro z hz
      have hz' : r.denReduced.eval z ≠ 0 := hz
      have h0 : A.eval z / (r.denReduced.eval z) ^ 2 = 0 := congrFun hA z
      have := div_eq_zero_iff.mp h0
      exact this.resolve_right (pow_ne_zero _ hz')
    · exact (Polynomial.finite_setOfPred_isRoot hden).infinite_compl
  have e := Submodule.equivMapOfInjective (polyOverDenSq r) hinj
    (Polynomial.degreeLT ℂ (2 * r.degree + 1))
  have h1 : Module.finrank ℂ (SectionSpaceCarrier r)
      = Module.finrank ℂ (Polynomial.degreeLT ℂ (2 * r.degree + 1)) :=
    e.finrank_eq.symm
  rw [h1, (Polynomial.degreeLTEquiv ℂ (2 * r.degree + 1)).finrank_eq,
    Module.finrank_fin_fun]

/-! ## Weak Wirtinger calculus: the product rule

The first of the two generic transport rules feeding the holomorphy of the
deformation field; the chain rule lives in the sibling file. -/

set_option maxHeartbeats 400000 in
-- The weak-Dzbar product rule elaborates as one large declaration: a dozen nested
-- `have` sub-lemmas (local integrability, the Leibniz identity, L²_loc closure)
-- exhaust the default heartbeat budget but finish well within twice it.
open scoped ContDiff ENNReal in
/-- **Product rule with a holomorphic factor.** If `F` is holomorphic on the
open set `Ω` and `v` has weak `∂̄`-derivative `μ` (with `L²_loc` gradient) on
`Ω`, then `F·v` has weak `∂̄`-derivative `F·μ` on `Ω` — `∂̄(Fv) = F·∂̄v` since
`∂̄F = 0`. Local integrability of `v` on `Ω` feeds the Leibniz rule for weak
derivatives. -/
theorem hasL2WeakDzbar_holomorphic_mul {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F v μ : ℂ → ℂ} (hF : DifferentiableOn ℂ F Ω)
    (hvloc : LocallyIntegrableOn v Ω)
    (hgrad : HasL2WeakDzbar v μ Ω) :
    HasL2WeakDzbar (fun z => F z * v z) (fun z => F z * μ z) Ω := by
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
  have d4_locInt_mul : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {m h : ℂ → ℂ}
    (hm : ContinuousOn m Ω) (hh : LocallyIntegrableOn h Ω),
      LocallyIntegrableOn (fun z => m z * h z) Ω := by
    intro Ω hΩ m h hm hh
    rw [MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro k hk hkc
    exact (hh.integrableOn_compact_subset hk hkc).continuousOn_mul (hm.mono hk) hkc
  have d5_weak_mul : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F v : ℂ → ℂ} (hF : DifferentiableOn ℂ F Ω)
    (hvloc : LocallyIntegrableOn v Ω)
    (e : ℂ) {gv : ℂ → ℂ} (hgv : HasWeakDirDeriv e gv v Ω)
    (hgvloc : LocallyIntegrableOn gv Ω),
      HasWeakDirDeriv e (fun z => F z * gv z + (deriv F z * e) * v z)
      (fun z => F z * v z) Ω := by
    intro Ω hΩ F v hF hvloc e gv hgv hgvloc
    -- Analyticity package for the holomorphic factor.
    have hFa : AnalyticOnNhd ℂ F Ω := hF.analyticOnNhd hΩ
    have hFcontOn : ContinuousOn F Ω := hF.continuousOn
    have hF'contOn : ContinuousOn (deriv F) Ω := hFa.deriv.continuousOn
    have hFAtR : ∀ z ∈ Ω, AnalyticAt ℝ F z := fun z hz =>
      @AnalyticAt.restrictScalars ℝ _ ℂ ℂ _ _ _ _ ℂ _ _ _ IsScalarTower.right _
        IsScalarTower.right _ _ (hFa z hz)
    have hFAt : ∀ z ∈ Ω, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F z := fun z hz =>
      (hFAtR z hz).contDiffAt
    -- Real differentiability and the applied real Fréchet derivative on `Ω`.
    have hFdiffC : ∀ z ∈ Ω, DifferentiableAt ℂ F z := fun z hz =>
      hF.differentiableAt (hΩ.mem_nhds hz)
    have hFdiffR : ∀ z ∈ Ω, DifferentiableAt ℝ F z := fun z hz =>
      (differentiableAt_complex_iff_differentiableAt_real.mp (hFdiffC z hz)).1
    have hFapp : ∀ z ∈ Ω, ∀ e : ℂ, (fderiv ℝ F z) e = deriv F z * e := by
      intro z hz e
      obtain ⟨hr, hCR⟩ := differentiableAt_complex_iff_differentiableAt_real.mp (hFdiffC z hz)
      have h1 : (fderiv ℝ F z) 1 = deriv F z := by
        have hdz := dz_eq_deriv_of_differentiableAt (hFdiffC z hz)
        rw [dz, hCR, smul_eq_mul] at hdz
        linear_combination hdz + (1 / 2 : ℂ) * ((fderiv ℝ F z) 1) * Complex.I_mul_I
      have hI : (fderiv ℝ F z) Complex.I = Complex.I * deriv F z := by
        rw [hCR, smul_eq_mul, h1]
      have hdec : e = e.re • (1 : ℂ) + e.im • Complex.I := by
        apply Complex.ext <;> simp [Complex.real_smul]
      calc (fderiv ℝ F z) e
          = e.re • ((fderiv ℝ F z) 1) + e.im • ((fderiv ℝ F z) Complex.I) := by
            conv_lhs => rw [hdec]
            rw [map_add, _root_.map_smul, _root_.map_smul]
        _ = deriv F z * e := by
            rw [h1, hI]
            simp only [Complex.real_smul]
            linear_combination (deriv F z) * (Complex.re_add_im e)
    intro φ hφ hcs htsupp
    change ∫ z, ((fderiv ℝ φ z) e) • (F z * v z)
        = - ∫ z, φ z • (F z * gv z + (deriv F z * e) * v z)
    -- Every point is either in `Ω` or outside the support of the test function.
    have hcover : ∀ z : ℂ, z ∈ Ω ∨ z ∉ tsupport φ := fun z =>
      (em (z ∈ tsupport φ)).elim (fun h => Or.inl (htsupp h)) Or.inr
    -- The two real test functions `φ·Re F` and `φ·Im F`.
    set ψ₁ : ℂ → ℝ := fun z => φ z * (F z).re with hψ₁def
    set ψ₂ : ℂ → ℝ := fun z => φ z * (F z).im with hψ₂def
    have hψsm : ∀ (P : ℂ →L[ℝ] ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ z * P (F z)) := by
      intro P
      rw [contDiff_iff_contDiffAt]
      intro z
      rcases hcover z with hz | hz
      · have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => P (F w)) z := by
          simpa [Function.comp] using! (P.contDiff.contDiffAt).comp z (hFAt z hz)
        exact (hφ.contDiffAt).mul hcomp
      · have hev : (fun w => φ w * P (F w)) =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hz] with y hy
          simp [image_eq_zero_of_notMem_tsupport hy]
        exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
    have hψ₁sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁ := by
      simpa only [Complex.reCLM_apply] using hψsm Complex.reCLM
    have hψ₂sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₂ := by
      simpa only [Complex.imCLM_apply] using hψsm Complex.imCLM
    have hψ₁cs : HasCompactSupport ψ₁ := hcs.mul_right
    have hψ₂cs : HasCompactSupport ψ₂ := hcs.mul_right
    have hψ₁ts : tsupport ψ₁ ⊆ Ω := (tsupport_mul_subset_left).trans htsupp
    have hψ₂ts : tsupport ψ₂ ⊆ Ω := (tsupport_mul_subset_left).trans htsupp
    -- The pointwise directional-derivative identity.
    have hid : ∀ z : ℂ, (((fderiv ℝ ψ₁ z) e : ℝ) : ℂ)
          + Complex.I * (((fderiv ℝ ψ₂ z) e : ℝ) : ℂ)
        = (((fderiv ℝ φ z) e : ℝ) : ℂ) * F z + (φ z : ℂ) * (deriv F z * e) := by
      intro z
      rcases hcover z with hz | hz
      · -- Product rule on `Ω`.
        have hdφ : DifferentiableAt ℝ φ z := (hφ.differentiable (by norm_num)).differentiableAt
        have hre_fdeq : fderiv ℝ (fun w => (F w).re) z
            = Complex.reCLM.comp (fderiv ℝ F z) := by
          have h := fderiv_comp z (Complex.reCLM.differentiableAt) (hFdiffR z hz)
          rw [ContinuousLinearMap.fderiv] at h
          simpa [Function.comp, Complex.reCLM_apply] using! h
        have him_fdeq : fderiv ℝ (fun w => (F w).im) z
            = Complex.imCLM.comp (fderiv ℝ F z) := by
          have h := fderiv_comp z (Complex.imCLM.differentiableAt) (hFdiffR z hz)
          rw [ContinuousLinearMap.fderiv] at h
          simpa [Function.comp, Complex.imCLM_apply] using! h
        have hre_diff : DifferentiableAt ℝ (fun w => (F w).re) z := by
          simpa [Function.comp, Complex.reCLM_apply] using!
            (Complex.reCLM.differentiableAt.comp z (hFdiffR z hz))
        have him_diff : DifferentiableAt ℝ (fun w => (F w).im) z := by
          simpa [Function.comp, Complex.imCLM_apply] using!
            (Complex.imCLM.differentiableAt.comp z (hFdiffR z hz))
        have hx1 : (fderiv ℝ ψ₁ z) e
            = φ z * (deriv F z * e).re + (F z).re * ((fderiv ℝ φ z) e) := by
          rw [hψ₁def]
          rw [fderiv_fun_mul hdφ hre_diff]
          simp only [add_apply, smul_apply,
            smul_eq_mul, hre_fdeq, ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
          rw [hFapp z hz e]
        have hx2 : (fderiv ℝ ψ₂ z) e
            = φ z * (deriv F z * e).im + (F z).im * ((fderiv ℝ φ z) e) := by
          rw [hψ₂def]
          rw [fderiv_fun_mul hdφ him_diff]
          simp only [add_apply, smul_apply,
            smul_eq_mul, him_fdeq, ContinuousLinearMap.comp_apply, Complex.imCLM_apply]
          rw [hFapp z hz e]
        rw [hx1, hx2]
        apply Complex.ext <;>
          simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] <;> ring
      · -- Outside the support everything vanishes.
        have hop : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
        have hev1 : ψ₁ =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [hop.mem_nhds hz] with y hy
          simp [hψ₁def, image_eq_zero_of_notMem_tsupport hy]
        have hev2 : ψ₂ =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [hop.mem_nhds hz] with y hy
          simp [hψ₂def, image_eq_zero_of_notMem_tsupport hy]
        have hevφ : φ =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [hop.mem_nhds hz] with y hy
          simp [image_eq_zero_of_notMem_tsupport hy]
        have h1 : fderiv ℝ ψ₁ z = 0 := by rw [hev1.fderiv_eq]; exact fderiv_const_apply 0
        have h2 : fderiv ℝ ψ₂ z = 0 := by rw [hev2.fderiv_eq]; exact fderiv_const_apply 0
        have h3 : fderiv ℝ φ z = 0 := by rw [hevφ.fderiv_eq]; exact fderiv_const_apply 0
        have h4 : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
        simp [h1, h2, h3, h4]
    -- Local integrability of the three products against `F`-data.
    have hFvloc : LocallyIntegrableOn (fun z => F z * v z) Ω := d4_locInt_mul hΩ hFcontOn hvloc
    have hFgvloc : LocallyIntegrableOn (fun z => F z * gv z) Ω := d4_locInt_mul hΩ hFcontOn hgvloc
    have hwvloc : LocallyIntegrableOn (fun z => (deriv F z * e) * v z) Ω :=
      d4_locInt_mul hΩ (hF'contOn.mul continuousOn_const) hvloc
    -- Continuity and support facts for the fderiv test weights.
    have hφcont : Continuous φ := hφ.continuous
    have hcont_dφ : Continuous (fun z => (fderiv ℝ φ z) e) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcs_dφ : HasCompactSupport (fun z => (fderiv ℝ φ z) e) :=
      HasCompactSupport.fderiv_apply ℝ hcs e
    have hts_dφ : tsupport (fun z => (fderiv ℝ φ z) e) ⊆ Ω :=
      (tsupport_fderiv_apply_subset ℝ e).trans htsupp
    have hcont_dψ₁ : Continuous (fun z => (fderiv ℝ ψ₁ z) e) :=
      (hψ₁sm.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcont_dψ₂ : Continuous (fun z => (fderiv ℝ ψ₂ z) e) :=
      (hψ₂sm.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcs_dψ₁ : HasCompactSupport (fun z => (fderiv ℝ ψ₁ z) e) :=
      HasCompactSupport.fderiv_apply ℝ hψ₁cs e
    have hcs_dψ₂ : HasCompactSupport (fun z => (fderiv ℝ ψ₂ z) e) :=
      HasCompactSupport.fderiv_apply ℝ hψ₂cs e
    have hts_dψ₁ : tsupport (fun z => (fderiv ℝ ψ₁ z) e) ⊆ Ω :=
      (tsupport_fderiv_apply_subset ℝ e).trans hψ₁ts
    have hts_dψ₂ : tsupport (fun z => (fderiv ℝ ψ₂ z) e) ⊆ Ω :=
      (tsupport_fderiv_apply_subset ℝ e).trans hψ₂ts
    -- Integrability of all pieces.
    have i_a1 : Integrable (fun z => ((fderiv ℝ ψ₁ z) e) • v z) volume :=
      d2_integ_real _ hcont_dψ₁ hcs_dψ₁ hts_dψ₁ hvloc
    have i_a2 : Integrable (fun z => ((fderiv ℝ ψ₂ z) e) • v z) volume :=
      d2_integ_real _ hcont_dψ₂ hcs_dψ₂ hts_dψ₂ hvloc
    have i_b1 : Integrable (fun z => ψ₁ z • gv z) volume :=
      d2_integ_real _ hψ₁sm.continuous hψ₁cs hψ₁ts hgvloc
    have i_b2 : Integrable (fun z => ψ₂ z • gv z) volume :=
      d2_integ_real _ hψ₂sm.continuous hψ₂cs hψ₂ts hgvloc
    have i_c : Integrable (fun z => φ z • ((deriv F z * e) * v z)) volume :=
      d2_integ_real _ hφcont hcs htsupp hwvloc
    have i_d : Integrable (fun z => φ z • (F z * gv z)) volume :=
      d2_integ_real _ hφcont hcs htsupp hFgvloc
    have i_e : Integrable (fun z => ((fderiv ℝ φ z) e) • (F z * v z)) volume :=
      d2_integ_real _ hcont_dφ hcs_dφ hts_dφ hFvloc
    -- The two tested identities from the hypothesis.
    have E₁ : ∫ z, ((fderiv ℝ ψ₁ z) e) • v z = - ∫ z, ψ₁ z • gv z :=
      hgv ψ₁ hψ₁sm hψ₁cs hψ₁ts
    have E₂ : ∫ z, ((fderiv ℝ ψ₂ z) e) • v z = - ∫ z, ψ₂ z • gv z :=
      hgv ψ₂ hψ₂sm hψ₂cs hψ₂ts
    -- Multiply the second identity by `I` and add.
    have hEI : (∫ z, Complex.I * (((fderiv ℝ ψ₂ z) e) • v z))
        = - ∫ z, Complex.I * (ψ₂ z • gv z) := by
      have h1 := integral_smul (μ := (volume : Measure ℂ)) Complex.I
        (fun z => ((fderiv ℝ ψ₂ z) e) • v z)
      have h2 := integral_smul (μ := (volume : Measure ℂ)) Complex.I
        (fun z => ψ₂ z • gv z)
      simp only [smul_eq_mul] at h1 h2
      rw [h1, h2, E₂, mul_neg]
    have hSUM : (∫ z, (((fderiv ℝ ψ₁ z) e) • v z + Complex.I * (((fderiv ℝ ψ₂ z) e) • v z)))
        = - ∫ z, (ψ₁ z • gv z + Complex.I * (ψ₂ z • gv z)) := by
      rw [integral_add i_a1 (i_a2.const_mul Complex.I),
        integral_add i_b1 (i_b2.const_mul Complex.I), E₁, hEI]
      ring
    -- Rewrite both integrands via the pointwise identities.
    have hLcong : (fun z => ((fderiv ℝ ψ₁ z) e) • v z + Complex.I * (((fderiv ℝ ψ₂ z) e) • v z))
        = fun z => ((fderiv ℝ φ z) e) • (F z * v z) + φ z • ((deriv F z * e) * v z) := by
      funext z
      simp only [Complex.real_smul]
      linear_combination (v z) * (hid z)
    have hRcong : (fun z => ψ₁ z • gv z + Complex.I * (ψ₂ z • gv z))
        = fun z => φ z • (F z * gv z) := by
      funext z
      simp only [hψ₁def, hψ₂def, Complex.real_smul]
      push_cast
      linear_combination ((φ z : ℂ) * gv z) * (Complex.re_add_im (F z))
    rw [hLcong, hRcong] at hSUM
    rw [integral_add i_e i_c] at hSUM
    -- Split the goal's right-hand side and conclude.
    have hgoalR : (∫ z, φ z • (F z * gv z + (deriv F z * e) * v z))
        = (∫ z, φ z • (F z * gv z)) + ∫ z, φ z • ((deriv F z * e) * v z) := by
      rw [← integral_add i_d i_c]
      apply integral_congr_ae
      filter_upwards with z
      exact smul_add _ _ _
    rw [hgoalR]
    linear_combination hSUM
  have d7_ext_univ : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) (e : ℂ) {f g : ℂ → ℂ}
    (hfts : tsupport f ⊆ Ω) (hgts : tsupport g ⊆ Ω)
    (hfcs : HasCompactSupport f) (hgcs : HasCompactSupport g)
    (h : HasWeakDirDeriv e g f Ω), HasWeakDirDeriv e g f Set.univ := by
    intro Ω hΩ e f g hfts hgts hfcs hgcs h φ hφ hcs _
    change ∫ z, ((fderiv ℝ φ z) e) • f z = - ∫ z, φ z • g z
    -- Compact set carrying both supports, and two nested compact collars in `Ω`.
    set Kfg : Set ℂ := tsupport f ∪ tsupport g with hKfg
    have hKfgc : IsCompact Kfg := hfcs.union hgcs
    have hKfgΩ : Kfg ⊆ Ω := Set.union_subset hfts hgts
    obtain ⟨T1, hT1c, hKT1, hT1Ω⟩ := exists_compact_between hKfgc hΩ hKfgΩ
    obtain ⟨T2, hT2c, hT1T2, hT2Ω⟩ := exists_compact_between hT1c hΩ hT1Ω
    -- Smooth Urysohn cutoff: `0` outside `interior T2`, `1` on `T1`.
    obtain ⟨χ0, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed
      (modelWithCornersSelf ℝ ℂ) (n := (⊤ : ℕ∞))
      (isOpen_interior.isClosed_compl) hT1c.isClosed
      (Set.disjoint_left.mpr fun z hzs hzt => hzs (hT1T2 hzt))
    set χ : ℂ → ℝ := fun z => χ0 z with hχdef
    have hχ_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := contMDiff_iff_contDiff.mp χ0.contMDiff
    have hχ_zero : ∀ z ∉ interior T2, χ z = 0 := fun z hz => by simpa using hχ0 hz
    have hχ_one : ∀ z ∈ T1, χ z = 1 := fun z hz => by simpa using hχ1 hz
    have hχ_supp : Function.support χ ⊆ T2 := by
      intro z hz
      by_contra hzT
      exact hz (hχ_zero z fun hzi => hzT (interior_subset hzi))
    have hχ_cs : HasCompactSupport χ := HasCompactSupport.of_support_subset_isCompact hT2c hχ_supp
    have hχ_ts : tsupport χ ⊆ Ω := (closure_minimal hχ_supp hT2c.isClosed).trans hT2Ω
    -- Test the `Ω`-hypothesis with `χ·φ`.
    have hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => χ z * φ z) := hχ_cd.mul hφ
    have hΦcs : HasCompactSupport (fun z => χ z * φ z) := hcs.mul_left
    have hΦts : tsupport (fun z => χ z * φ z) ⊆ Ω := (tsupport_mul_subset_left).trans hχ_ts
    have hfΦ := h (fun z => χ z * φ z) hΦsm hΦcs hΦts
    -- `χ ≡ 1` on the open set `interior T1 ⊇ Kfg`, so `fderiv χ = 0` there.
    have hχ1int : ∀ z ∈ interior T1, χ z = 1 := fun z hz => hχ_one z (interior_subset hz)
    have hfd0 : ∀ z ∈ interior T1, fderiv ℝ χ z = 0 := by
      intro z hz
      have hloc : χ =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
        filter_upwards [isOpen_interior.mem_nhds hz] with y hy
        exact hχ1int y hy
      rw [hloc.fderiv_eq]
      simp
    -- Pointwise product rule for the modified test function.
    have hpr : ∀ z, (fderiv ℝ (fun y => χ y * φ y) z) e
        = χ z * ((fderiv ℝ φ z) e) + φ z * ((fderiv ℝ χ z) e) := by
      intro z
      have hdχ : DifferentiableAt ℝ χ z := (hχ_cd.differentiable (by norm_num)).differentiableAt
      have hdφ : DifferentiableAt ℝ φ z := (hφ.differentiable (by norm_num)).differentiableAt
      rw [fderiv_fun_mul hdχ hdφ]
      simp only [add_apply, smul_apply, smul_eq_mul]
    -- Both sides of the tested identity coincide with the goal's sides.
    have hLHS : (∫ z, ((fderiv ℝ (fun y => χ y * φ y) z) e) • f z)
        = ∫ z, ((fderiv ℝ φ z) e) • f z := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ tsupport f
      · have hzi : z ∈ interior T1 := hKT1 (Or.inl hz)
        rw [hpr z, hfd0 z hzi]
        simp [hχ1int z hzi]
      · simp [image_eq_zero_of_notMem_tsupport hz]
    have hRHS : (∫ z, (χ z * φ z) • g z) = ∫ z, φ z • g z := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ tsupport g
      · have hzi : z ∈ interior T1 := hKT1 (Or.inr hz)
        simp [hχ1int z hzi]
      · simp [image_eq_zero_of_notMem_tsupport hz]
    rw [← hLHS, ← hRHS]
    exact hfΦ
  have d8_young : ∀ (ρ : ℂ → ℝ) (g : ℂ → ℂ) (hρmem : MemLp ρ 1 volume)
    (hgmem : MemLp g 1 volume),
      eLpNorm (MeasureTheory.convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) 1 volume
      ≤ eLpNorm ρ 1 volume * eLpNorm g 1 volume := by
    intro ρ g hρmem hgmem
    set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
    rw [eLpNorm_one_eq_lintegral_enorm]
    have hpt : ∀ z, ‖MeasureTheory.convolution ρ g L volume z‖ₑ
        ≤ ∫⁻ t, ‖ρ t‖ₑ * ‖g (z - t)‖ₑ ∂volume := by
      intro z
      rw [MeasureTheory.convolution_def]
      refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
      refine lintegral_mono (fun t => ?_)
      rw [hL, ContinuousLinearMap.lsmul_apply, enorm_smul]
    have hgsm : AEStronglyMeasurable g volume := hgmem.1
    have hρsm : AEStronglyMeasurable ρ volume := hρmem.1
    have hjoint : AEMeasurable (Function.uncurry
        (fun z t => ‖ρ t‖ₑ * ‖g (z - t)‖ₑ)) (volume.prod volume) := by
      have h1 : AEStronglyMeasurable
          (fun p : ℂ × ℂ => (L (ρ p.2)) (g (p.1 - p.2))) (volume.prod volume) :=
        AEStronglyMeasurable.convolution_integrand L hρsm hgsm
      have h2 : AEMeasurable (fun p : ℂ × ℂ => ‖(L (ρ p.2)) (g (p.1 - p.2))‖ₑ)
          (volume.prod volume) := h1.enorm
      refine h2.congr (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Function.uncurry, hL, ContinuousLinearMap.lsmul_apply, enorm_smul]
    calc ∫⁻ z, ‖MeasureTheory.convolution ρ g L volume z‖ₑ ∂volume
        ≤ ∫⁻ z, ∫⁻ t, ‖ρ t‖ₑ * ‖g (z - t)‖ₑ ∂volume ∂volume := lintegral_mono hpt
      _ = ∫⁻ t, ∫⁻ z, ‖ρ t‖ₑ * ‖g (z - t)‖ₑ ∂volume ∂volume :=
          lintegral_lintegral_swap hjoint
      _ = ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ z, ‖g (z - t)‖ₑ ∂volume ∂volume := by
          refine lintegral_congr (fun t => ?_)
          rw [lintegral_const_mul' _ _ (by simp [enorm_ne_top])]
      _ = ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ z, ‖g z‖ₑ ∂volume ∂volume := by
          refine lintegral_congr (fun t => ?_)
          congr 1
          exact lintegral_sub_right_eq_self (fun z => ‖g z‖ₑ) t
      _ = (∫⁻ t, ‖ρ t‖ₑ ∂volume) * ∫⁻ z, ‖g z‖ₑ ∂volume := by
          rw [lintegral_mul_const'' _ hρsm.enorm]
      _ = eLpNorm ρ 1 volume * eLpNorm g 1 volume := by
          rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm]
  have d9_bump_mass : ∀ (b : ContDiffBump (0 : ℂ)),
      eLpNorm (b.normed (volume : Measure ℂ)) 1 volume = 1 := by
    intro b
    rw [eLpNorm_one_eq_lintegral_enorm]
    have hnn : ∀ t, 0 ≤ b.normed (volume : Measure ℂ) t := b.nonneg_normed
    have hcongr : ∀ t : ℂ, ‖b.normed (volume : Measure ℂ) t‖ₑ
        = ENNReal.ofReal (b.normed (volume : Measure ℂ) t) := fun t =>
      Real.enorm_eq_ofReal (hnn t)
    rw [lintegral_congr hcongr]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal b.integrable_normed
      (Filter.Eventually.of_forall hnn)]
    rw [b.integral_normed]
    simp
  have d6_memL2loc : ∀ {Ω : Set ℂ} (hΩ : IsOpen Ω) {v gx gy : ℂ → ℂ}
    (hvloc : LocallyIntegrableOn v Ω)
    (hgrad : HasWeakGradient gx gy v Ω)
    (hgx2 : MemLpLocOn gx 2 Ω) (hgy2 : MemLpLocOn gy 2 Ω), MemLpLocOn v 2 Ω := by
    intro Ω hΩ v gx gy hvloc hgrad hgx2 hgy2
    classical
    have hgxloc : LocallyIntegrableOn gx Ω := d1_locInt hΩ hgx2
    have hgyloc : LocallyIntegrableOn gy Ω := d1_locInt hΩ hgy2
    intro K hKΩ hKc
    -- Cutoff `η`: smooth, compactly supported in `Ω`, `≡ 1` on `K`.
    obtain ⟨T1, hT1c, hKT1, hT1Ω⟩ := exists_compact_between hKc hΩ hKΩ
    obtain ⟨T2, hT2c, hT1T2, hT2Ω⟩ := exists_compact_between hT1c hΩ hT1Ω
    obtain ⟨η0, hη0, hη1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed
      (modelWithCornersSelf ℝ ℂ) (n := (⊤ : ℕ∞))
      (isOpen_interior.isClosed_compl) hT1c.isClosed
      (Set.disjoint_left.mpr fun z hzs hzt => hzs (hT1T2 hzt))
    set η : ℂ → ℝ := fun z => η0 z with hηdef
    have hη_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η := contMDiff_iff_contDiff.mp η0.contMDiff
    have hη_zero : ∀ z ∉ interior T2, η z = 0 := fun z hz => by simpa using hη0 hz
    have hη_one : ∀ z ∈ T1, η z = 1 := fun z hz => by simpa using hη1 hz
    have hη_supp : Function.support η ⊆ T2 := by
      intro z hz
      by_contra hzT
      exact hz (hη_zero z fun hzi => hzT (interior_subset hzi))
    have hη_cs : HasCompactSupport η := HasCompactSupport.of_support_subset_isCompact hT2c hη_supp
    have hη_ts : tsupport η ⊆ Ω := (closure_minimal hη_supp hT2c.isClosed).trans hT2Ω
    have hη_cont : Continuous η := hη_cd.continuous
    -- The localized function `u = η•v` and its weak partials on `Ω`.
    set u : ℂ → ℂ := fun z => η z • v z with hudef
    set Gx : ℂ → ℂ := fun z => η z • gx z + ((fderiv ℝ η z) 1) • v z with hGxdef
    set Gy : ℂ → ℂ := fun z => η z • gy z + ((fderiv ℝ η z) Complex.I) • v z with hGydef
    have hwx : HasWeakDirDeriv 1 Gx u Ω := hgrad.1.smul_smooth hη_cd hvloc hgxloc
    have hwy : HasWeakDirDeriv Complex.I Gy u Ω := hgrad.2.smul_smooth hη_cd hvloc hgyloc
    -- Support and integrability bookkeeping.
    have hηfd_cont : ∀ e : ℂ, Continuous fun z => (fderiv ℝ η z) e := fun e =>
      (hη_cd.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hηfd_ts : ∀ e : ℂ, tsupport (fun z => (fderiv ℝ η z) e) ⊆ Ω := fun e =>
      (tsupport_fderiv_apply_subset ℝ e).trans hη_ts
    have hηfd_cs : ∀ e : ℂ, HasCompactSupport fun z => (fderiv ℝ η z) e := fun e =>
      HasCompactSupport.fderiv_apply ℝ hη_cs e
    have hu_int : Integrable u volume := d2_integ_real η hη_cont hη_cs hη_ts hvloc
    have hGx_int : Integrable Gx volume :=
      (d2_integ_real η hη_cont hη_cs hη_ts hgxloc).add
        (d2_integ_real _ (hηfd_cont 1) (hηfd_cs 1) (hηfd_ts 1) hvloc)
    have hGy_int : Integrable Gy volume :=
      (d2_integ_real η hη_cont hη_cs hη_ts hgyloc).add
        (d2_integ_real _ (hηfd_cont Complex.I) (hηfd_cs Complex.I) (hηfd_ts Complex.I) hvloc)
    have hu_li : MeasureTheory.LocallyIntegrable u := hu_int.locallyIntegrable
    have hGx_li : MeasureTheory.LocallyIntegrable Gx := hGx_int.locallyIntegrable
    have hGy_li : MeasureTheory.LocallyIntegrable Gy := hGy_int.locallyIntegrable
    -- Supports inside `tsupport η`.
    have hu_supp : Function.support u ⊆ tsupport η := by
      intro z hz
      simp only [hudef, Function.mem_support] at hz
      by_contra hzη
      have h0 : η z = 0 := image_eq_zero_of_notMem_tsupport hzη
      apply hz; simp [h0]
    have hG_supp : ∀ (g' : ℂ → ℂ) (e : ℂ),
        Function.support (fun z => η z • g' z + ((fderiv ℝ η z) e) • v z) ⊆ tsupport η := by
      intro g' e z hz
      simp only [Function.mem_support] at hz
      by_contra hzη
      have h0 : η z = 0 := image_eq_zero_of_notMem_tsupport hzη
      have h1 : (fderiv ℝ η z) e = 0 := by
        have hnot : z ∉ tsupport (fun z => (fderiv ℝ η z) e) := fun hmem =>
          hzη ((tsupport_fderiv_apply_subset ℝ e) hmem)
        simpa using image_eq_zero_of_notMem_tsupport hnot
      apply hz; simp [h0, h1]
    have hu_ts : tsupport u ⊆ Ω :=
      (closure_minimal hu_supp (isClosed_tsupport η)).trans hη_ts
    have hu_cs : HasCompactSupport u :=
      HasCompactSupport.of_support_subset_isCompact hη_cs hu_supp
    have hGx_ts : tsupport Gx ⊆ Ω :=
      (closure_minimal (hG_supp gx 1) (isClosed_tsupport η)).trans hη_ts
    have hGx_cs : HasCompactSupport Gx :=
      HasCompactSupport.of_support_subset_isCompact hη_cs (hG_supp gx 1)
    have hGy_ts : tsupport Gy ⊆ Ω :=
      (closure_minimal (hG_supp gy Complex.I) (isClosed_tsupport η)).trans hη_ts
    have hGy_cs : HasCompactSupport Gy :=
      HasCompactSupport.of_support_subset_isCompact hη_cs (hG_supp gy Complex.I)
    -- Weak derivatives on all of `ℂ`.
    have hwx_univ : HasWeakDirDeriv 1 Gx u Set.univ :=
      d7_ext_univ hΩ 1 hu_ts hGx_ts hu_cs hGx_cs hwx
    have hwy_univ : HasWeakDirDeriv Complex.I Gy u Set.univ :=
      d7_ext_univ hΩ Complex.I hu_ts hGy_ts hu_cs hGy_cs hwy
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
    set ρ : ℕ → ℂ → ℝ := fun n => (bumps n).normed volume with hρdef
    have hρ_sm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
      (bumps n).contDiff_normed
    have hρ_cs : ∀ n, HasCompactSupport (ρ n) := fun n => (bumps n).hasCompactSupport_normed
    set w : ℕ → ℂ → ℂ := fun n =>
      MeasureTheory.convolution (ρ n) u (ContinuousLinearMap.lsmul ℝ ℝ) volume with hwdef
    have hw_cd : ∀ n, ContDiff ℝ 1 (w n) := by
      intro n
      have h1 : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) (ρ n) :=
        (hρ_sm n).of_le (by exact_mod_cast le_top)
      exact HasCompactSupport.contDiff_convolution_left _ (hρ_cs n) h1 hu_li
    have hw_cs : ∀ n, HasCompactSupport (w n) := fun n =>
      HasCompactSupport.convolution _ (hρ_cs n) hu_cs
    -- Directional derivatives of the mollification are mollified weak partials.
    have hw_fd1 : ∀ n z, (fderiv ℝ (w n) z) 1
        = MeasureTheory.convolution (ρ n) Gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z :=
      fun n z => fderiv_convolution_normed_apply_eq hwx_univ hu_li hGx_li
        (hρ_sm n) (hρ_cs n) z
    have hw_fdI : ∀ n z, (fderiv ℝ (w n) z) Complex.I
        = MeasureTheory.convolution (ρ n) Gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z :=
      fun n z => fderiv_convolution_normed_apply_eq hwy_univ hu_li hGy_li
        (hρ_sm n) (hρ_cs n) z
    -- Uniform `L²` bound from the endpoint Sobolev inequality.
    obtain ⟨C, hC0, hP1⟩ := eLpNorm_two_le_eLpNorm_fderiv_one
    set M : ℝ≥0∞ := ENNReal.ofReal C * (eLpNorm Gx 1 volume + eLpNorm Gy 1 volume) with hMdef
    have hMlt : M < ⊤ := by
      rw [hMdef]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.mpr ⟨(memLp_one_iff_integrable.mpr hGx_int).2,
          (memLp_one_iff_integrable.mpr hGy_int).2⟩)
    have hwbd : ∀ n, eLpNorm (w n) 2 volume ≤ M := by
      intro n
      have h1 := hP1 (hw_cd n) (hw_cs n)
      have h2 := eLpNorm_fderiv_one_le_partials (hw_cd n)
      have h3 : eLpNorm (fun z => (fderiv ℝ (w n) z) 1) 1 volume ≤ eLpNorm Gx 1 volume := by
        rw [show (fun z => (fderiv ℝ (w n) z) 1)
            = MeasureTheory.convolution (ρ n) Gx (ContinuousLinearMap.lsmul ℝ ℝ) volume from
          funext fun z => hw_fd1 n z]
        calc eLpNorm (MeasureTheory.convolution (ρ n) Gx
                (ContinuousLinearMap.lsmul ℝ ℝ) volume) 1 volume
            ≤ eLpNorm (ρ n) 1 volume * eLpNorm Gx 1 volume :=
              d8_young (ρ n) Gx (memLp_one_iff_integrable.mpr (bumps n).integrable_normed)
                (memLp_one_iff_integrable.mpr hGx_int)
          _ = eLpNorm Gx 1 volume := by rw [d9_bump_mass (bumps n), one_mul]
      have h4 : eLpNorm (fun z => (fderiv ℝ (w n) z) Complex.I) 1 volume
          ≤ eLpNorm Gy 1 volume := by
        rw [show (fun z => (fderiv ℝ (w n) z) Complex.I)
            = MeasureTheory.convolution (ρ n) Gy (ContinuousLinearMap.lsmul ℝ ℝ) volume from
          funext fun z => hw_fdI n z]
        calc eLpNorm (MeasureTheory.convolution (ρ n) Gy
                (ContinuousLinearMap.lsmul ℝ ℝ) volume) 1 volume
            ≤ eLpNorm (ρ n) 1 volume * eLpNorm Gy 1 volume :=
              d8_young (ρ n) Gy (memLp_one_iff_integrable.mpr (bumps n).integrable_normed)
                (memLp_one_iff_integrable.mpr hGy_int)
          _ = eLpNorm Gy 1 volume := by rw [d9_bump_mass (bumps n), one_mul]
      calc eLpNorm (w n) 2 volume
          ≤ ENNReal.ofReal C * eLpNorm (fderiv ℝ (w n)) 1 volume := h1
        _ ≤ ENNReal.ofReal C * (eLpNorm Gx 1 volume + eLpNorm Gy 1 volume) := by
            gcongr
            exact h2.trans (add_le_add h3 h4)
        _ = M := rfl
    -- Almost-everywhere convergence of the mollifications.
    have hrr : ∀ᶠ n in atTop, (bumps n).rOut ≤ 2 * (bumps n).rIn :=
      Filter.Eventually.of_forall fun n => by
        simp only [hbumps]
        rw [mul_one_div]
    have hae : ∀ᵐ x ∂(volume : Measure ℂ),
        Tendsto (fun n => w n x) atTop (𝓝 (u x)) :=
      ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hrout hrr hu_li
    -- Fatou: the limit is in `L²` with the same bound.
    have heLp2 : ∀ h : ℂ → ℂ,
        eLpNorm h 2 volume = (∫⁻ z, ‖h z‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ) := by
      intro h
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
      rw [h2]
      congr 1
      apply lintegral_congr
      intro z
      rw [← ENNReal.rpow_natCast]
      norm_num
    have hcollapse : ∀ X : ℝ≥0∞, (X ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = X := by
      intro X
      rw [← ENNReal.rpow_mul]
      norm_num
    have hbdint : ∀ n, ∫⁻ z, ‖w n z‖ₑ ^ (2 : ℕ) ∂volume ≤ M ^ (2 : ℝ) := by
      intro n
      have h1 : (∫⁻ z, ‖w n z‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ) ≤ M := by
        rw [← heLp2 (w n)]; exact hwbd n
      calc ∫⁻ z, ‖w n z‖ₑ ^ (2 : ℕ) ∂volume
          = ((∫⁻ z, ‖w n z‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
            (hcollapse _).symm
        _ ≤ M ^ (2 : ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
    have hulim : ∫⁻ z, ‖u z‖ₑ ^ (2 : ℕ) ∂volume ≤ M ^ (2 : ℝ) := by
      have hptw : ∀ᵐ z ∂(volume : Measure ℂ),
          (‖u z‖ₑ ^ (2 : ℕ)) = Filter.liminf (fun n => ‖w n z‖ₑ ^ (2 : ℕ)) atTop := by
        filter_upwards [hae] with z hz
        exact (((ENNReal.continuous_pow 2).tendsto _).comp hz.enorm).liminf_eq.symm
      calc ∫⁻ z, ‖u z‖ₑ ^ (2 : ℕ) ∂volume
          = ∫⁻ z, Filter.liminf (fun n => ‖w n z‖ₑ ^ (2 : ℕ)) atTop ∂volume :=
            lintegral_congr_ae hptw
        _ ≤ Filter.liminf (fun n => ∫⁻ z, ‖w n z‖ₑ ^ (2 : ℕ) ∂volume) atTop :=
            lintegral_liminf_le' fun n =>
              ((ENNReal.continuous_pow 2).comp (hw_cd n).continuous.enorm).aemeasurable
        _ ≤ M ^ (2 : ℝ) := by
            refine Filter.liminf_le_of_le ?_ ?_
            · isBoundedDefault
            · intro b hb
              rcases (hb.and (Filter.Eventually.of_forall hbdint)).exists with ⟨n, hn1, hn2⟩
              exact hn1.trans hn2
    have hu2 : MemLp u 2 volume := by
      refine ⟨hu_int.aestronglyMeasurable, ?_⟩
      rw [heLp2 u]
      calc (∫⁻ z, ‖u z‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / 2 : ℝ)
          ≤ (M ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hulim (by norm_num)
        _ = M := by rw [← ENNReal.rpow_mul]; norm_num
        _ < ⊤ := hMlt
    -- `v = u` on `K`, so `v ∈ L²(K)`.
    have huK : MemLp u 2 (volume.restrict K) := hu2.restrict K
    have hvu : u =ᵐ[volume.restrict K] v := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hKc.measurableSet]
      filter_upwards with z hz
      have h1 : η z = 1 := hη_one z (interior_subset (hKT1 hz))
      simp [hudef, h1]
    exact MemLp.ae_eq hvu huK
  have d10_memLp_mul : ∀ {Ω : Set ℂ} {m g : ℂ → ℂ}
    (hm : ContinuousOn m Ω) (hg : MemLpLocOn g 2 Ω), MemLpLocOn (fun z => m z * g z) 2 Ω := by
    intro Ω m g hm hg K hK hKc
    obtain ⟨Cb, hCb⟩ := hKc.exists_bound_of_continuousOn (hm.mono hK)
    refine MemLp.of_le_mul (c := Cb) (hg K hK hKc)
      (((hm.mono hK).aestronglyMeasurable hKc.measurableSet).mul (hg K hK hKc).1) ?_
    rw [ae_restrict_iff' hKc.measurableSet]
    filter_upwards with z hz
    calc ‖m z * g z‖ = ‖m z‖ * ‖g z‖ := norm_mul _ _
      _ ≤ Cb * ‖g z‖ := mul_le_mul_of_nonneg_right (hCb z hz) (norm_nonneg _)
  have d11_memLp_add : ∀ {Ω : Set ℂ} {f g : ℂ → ℂ}
    (hf : MemLpLocOn f 2 Ω) (hg : MemLpLocOn g 2 Ω), MemLpLocOn (fun z => f z + g z) 2 Ω := by
    intro Ω f g hf hg
    exact fun K hK hKc =>
        (hf K hK hKc).add (hg K hK hKc)
  obtain ⟨gx, gy, hw, hgx2, hgy2, hcombo⟩ := hgrad
  have hgxloc : LocallyIntegrableOn gx Ω := d1_locInt hΩ hgx2
  have hgyloc : LocallyIntegrableOn gy Ω := d1_locInt hΩ hgy2
  have hv2 : MemLpLocOn v 2 Ω := d6_memL2loc hΩ hvloc hw hgx2 hgy2
  have hFcontOn : ContinuousOn F Ω := hF.continuousOn
  have hF'contOn : ContinuousOn (deriv F) Ω := (hF.analyticOnNhd hΩ).deriv.continuousOn
  refine ⟨fun z => F z * gx z + (deriv F z * 1) * v z,
    fun z => F z * gy z + (deriv F z * Complex.I) * v z,
    ⟨d5_weak_mul hΩ hF hvloc 1 hw.1 hgxloc,
      d5_weak_mul hΩ hF hvloc Complex.I hw.2 hgyloc⟩, ?_, ?_, ?_⟩
  · exact d11_memLp_add (d10_memLp_mul hFcontOn hgx2)
      (d10_memLp_mul (hF'contOn.mul continuousOn_const) hv2)
  · exact d11_memLp_add (d10_memLp_mul hFcontOn hgy2)
      (d10_memLp_mul (hF'contOn.mul continuousOn_const) hv2)
  · filter_upwards [hcombo] with z hz hzΩ
    have h := hz hzΩ
    linear_combination (F z) * h + (deriv F z * v z) * Complex.I_mul_I

end NoWanderingDomains
