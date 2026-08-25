/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Defs.Analytic
import NoWanderingDomains.Hyperbolic.PathWinding.LogLiftHomotopy

/-!
# Topologically sense-preserving homeomorphisms

The geometric definition of a quasiconformal map should be purely topological and
metric: a homeomorphism plus a bound on the modulus distortion, with **no** a priori
differentiability. Orientation must still be imposed — otherwise anti-conformal maps
such as `z ↦ conj z` (which preserve every modulus) would qualify — but it must be a
*topological* condition, so that the a.e. differentiability and positivity of the
Jacobian are genuine *conclusions* of the geometric ⇒ analytic theorem rather than
hypotheses.

`SensePreserving f` is that topological orientation condition: a homeomorphism whose
small image circles wind `+1` about their image centre. The winding `+1` is expressed
without any winding-number machinery in the *definition* itself — the closed,
non-vanishing loop `θ ↦ f (z₀ + r e^{iθ}) - f z₀` admits a continuous logarithm `L`
(it always does, `exp` being a covering map of `ℂ∖{0}`), and the substantive condition
is that the total increment of `L` over `[0, 2π]` equals `2π i`. The orientation-
reversing map `z ↦ conj z` gives increment `-2π i`, so it is excluded.

The winding condition is imposed for **almost every** centre `z₀`. For a homeomorphism
the local degree is globally constant (it is a locally constant `ℤ`-valued function on
the connected plane), so this is equivalent to the everywhere condition, while matching
the a.e. form of the analytic orientation `OrientationPreservingHomeo` and keeping the
translation bridges to it free of a separate degree-constancy argument.

## Main definitions and results

* `SensePreserving f` — `f` is a homeomorphism with image winding `+1` about a.e. centre;
* `windingOne_iff_det_pos` — the local-degree core: at a point of differentiability with
  invertible derivative, image circles wind `+1` iff the Jacobian determinant is positive;
* `SensePreserving.of_orientationPreservingHomeo` — the analytic orientation
  (`IsHomeomorph` with a.e. positive Jacobian) implies the topological one (forward bridge);
* `SensePreserving.ae_det_pos` — a sense-preserving map that is a.e. differentiable with
  invertible derivative has a.e. positive Jacobian (backward bridge).

The two bridges let the analytic track keep the Jacobian condition
`OrientationPreservingHomeo` while the geometric track uses the topological
`SensePreserving`, with the equivalence theorem translating between them. Both reduce to
`windingOne_iff_det_pos`, built on the project's winding-number library
(`NoWanderingDomains/Hyperbolic/PathWinding/`).
-/

open Complex MeasureTheory
open scoped Topology Real

namespace NoWanderingDomains

/-- A planar homeomorphism `f : ℂ → ℂ` is **topologically sense-preserving** when, around
almost every point `z₀`, the small image circles wind `+1` about their image centre `f z₀`.
The winding `+1` is encoded without differentiability: the closed non-vanishing loop
`θ ↦ f (z₀ + r e^{iθ}) - f z₀` admits a continuous logarithm `L` (`exp` is a covering map
of `ℂ∖{0}`) whose total increment `L (2π) - L 0` over a turn equals `2π i`. The
orientation-reversing map `z ↦ conj z` gives increment `-2π i`, so it is excluded. -/
def SensePreserving (f : ℂ → ℂ) : Prop :=
  IsHomeomorph f ∧ ∀ᵐ z₀ : ℂ, ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
    ∃ L : ℝ → ℂ, Continuous L ∧
      (∀ θ : ℝ, Complex.exp (L θ)
        = f (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - f z₀) ∧
      L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I

/-- A sense-preserving map is in particular a homeomorphism. -/
theorem SensePreserving.isHomeomorph {f : ℂ → ℂ} (hf : SensePreserving f) :
    IsHomeomorph f := hf.1

/-- **Local degree equals the sign of the Jacobian.** At a point `z` where `f` is
differentiable with invertible derivative `A = fderiv ℝ f z`, the small image circles
about `f z` wind `+1` (admit a continuous logarithm with increment `2π i`) if and only if
`0 < det A`. This is the analytic core of both translation bridges: near `z`,
`f (z + h) - f z = A h + o(|h|)`, so for small `r` the image circle
`θ ↦ f (z + r e^{iθ}) - f z` is homotopic in `ℂ∖{0}` to the linear circle
`θ ↦ A (e^{iθ})`, whose winding about `0` is `sign (det A)` (in Wirtinger form
`A h = p·h + q·conj h` with `det A = ‖p‖² - ‖q‖²`, the term `p e^{iθ}` dominates exactly
when `‖p‖ > ‖q‖`, i.e. `det A > 0`). Built on the project's winding-number library
(`NoWanderingDomains/Hyperbolic/PathWinding/`). Continuity of `f` is needed so the image
loops `θ ↦ f (z + r e^{iθ}) - f z` are continuous (differentiability at the single point
`z` says nothing about `f` on the surrounding circles); both callers supply it from
`IsHomeomorph f`. -/
theorem windingOne_iff_det_pos {f : ℂ → ℂ} {z : ℂ} (hfc : Continuous f)
    (hz : DifferentiableAt ℝ f z) (hz' : (fderiv ℝ f z).det ≠ 0) :
    (∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), ∃ L : ℝ → ℂ, Continuous L ∧
      (∀ θ : ℝ, Complex.exp (L θ)
        = f (z + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - f z) ∧
      L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I)
    ↔ 0 < (fderiv ℝ f z).det := by
  classical
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h2pi_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  -- abbreviations
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ f z with hAdef
  set p : ℂ := dz f z with hpdef
  set q : ℂ := dzbar f z with hqdef
  ----------------------------------------------------------------------------
  -- Helper W: well-definedness of the increment of a continuous log lift.
  ----------------------------------------------------------------------------
  have helperW : ∀ (L₁ L₂ : ℝ → ℂ), Continuous L₁ → Continuous L₂ →
      (∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), Complex.exp (L₁ t) = Complex.exp (L₂ t)) →
      L₁ (2 * Real.pi) - L₁ 0 = L₂ (2 * Real.pi) - L₂ 0 := by
    intro L₁ L₂ hL₁ hL₂ hexp
    set d : ℝ → ℂ := fun t => L₁ t - L₂ t with hd
    have hdcont : Continuous d := hL₁.sub hL₂
    have hdexp : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), Complex.exp (d t) = 1 := by
      intro t ht
      simp only [hd, Complex.exp_sub, hexp t ht, div_self (Complex.exp_ne_zero _)]
    have hdK : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        ∃ K : ℤ, d t = (K : ℂ) * (2 * Real.pi * Complex.I) := fun t ht =>
      (Complex.exp_eq_one_iff).mp (hdexp t ht)
    set wfun : ℝ → ℤ :=
      fun t => if h : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) then (hdK t h).choose else 0 with hwf
    have hwf_spec : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        d t = ((wfun t : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      intro t ht; simp only [hwf, dif_pos ht]; exact (hdK t ht).choose_spec
    have hwf_cont : ContinuousOn (fun t => ((wfun t : ℤ) : ℂ)) (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
      have heq : Set.EqOn (fun t => ((wfun t : ℤ) : ℂ))
          (fun t => d t / (2 * Real.pi * Complex.I)) (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
        intro t ht
        simp only
        rw [hwf_spec t ht, mul_div_assoc, div_self h2pi_ne, mul_one]
      exact ContinuousOn.congr (hdcont.continuousOn.div_const _) heq
    have hwf_int_cont : ContinuousOn wfun (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
      rw [continuousOn_iff_continuous_domRestrict] at hwf_cont ⊢
      have hemb : Topology.IsClosedEmbedding (fun n : ℤ => (n : ℂ)) := isClosedEmbedding_intCast
      exact hemb.isEmbedding.continuous_iff.mpr hwf_cont
    have hconst : wfun 0 = wfun (2 * Real.pi) :=
      isPreconnected_Icc.constant hwf_int_cont ⟨le_refl _, hpi⟩ ⟨hpi, le_refl _⟩
    have hdd : d (2 * Real.pi) = d 0 := by
      rw [hwf_spec (2 * Real.pi) ⟨hpi, le_refl _⟩, hwf_spec 0 ⟨le_refl _, hpi⟩, hconst]
    simp only [hd] at hdd
    linear_combination hdd
  ----------------------------------------------------------------------------
  -- Wirtinger representation of A and the Jacobian identity.
  ----------------------------------------------------------------------------
  have hArep : ∀ w : ℂ, A w = p * w + q * (starRingEnd ℂ) w := by
    intro w
    rw [hpdef, hqdef, dz, dzbar]
    have hLw : A w = (↑w.re : ℂ) * A 1 + (↑w.im : ℂ) * A Complex.I := by
      conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • Complex.I by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
      rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have hcw : (starRingEnd ℂ) w = (↑w.re : ℂ) - ↑w.im * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im w]
      simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hw : w = (↑w.re : ℂ) + ↑w.im * Complex.I := (Complex.re_add_im w).symm
    rw [hLw, hcw]
    set sa : ℂ := (↑w.re : ℂ) with hsa
    set sb : ℂ := (↑w.im : ℂ) with hsb
    rw [hw]
    linear_combination (sb * A Complex.I) * Complex.I_mul_I
  have hdet_eq : A.det = ‖p‖ ^ 2 - ‖q‖ ^ 2 := by
    set a : ℝ := (A 1).re with ha
    set b : ℝ := (A 1).im with hb
    set c : ℝ := (A Complex.I).re with hc
    set d : ℝ := (A Complex.I).im with hd
    have hpval : p = (1 / 2 : ℂ) * ((A 1) - Complex.I * (A Complex.I)) := rfl
    have hqval : q = (1 / 2 : ℂ) * ((A 1) + Complex.I * (A Complex.I)) := rfl
    have hdet : A.det = a * d - b * c := by
      have key : ∀ M : ℂ →ₗ[ℝ] ℂ, LinearMap.det M
          = (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI M).det := fun M =>
        (LinearMap.det_toMatrix Complex.basisOneI M).symm
      rw [ContinuousLinearMap.det, key]
      have hb0 : (Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ) 0 = (1 : ℂ) := by
        simp [Complex.coe_basisOneI]
      have hb1 : (Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ) 1 = Complex.I := by
        simp [Complex.coe_basisOneI]
      have c00 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (↑A : ℂ →ₗ[ℝ] ℂ)) 0 0 = a := by
        rw [LinearMap.toMatrix_apply, hb0, Complex.coe_basisOneI_repr]; rfl
      have c10 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (↑A : ℂ →ₗ[ℝ] ℂ)) 1 0 = b := by
        rw [LinearMap.toMatrix_apply, hb0, Complex.coe_basisOneI_repr]; rfl
      have c01 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (↑A : ℂ →ₗ[ℝ] ℂ)) 0 1 = c := by
        rw [LinearMap.toMatrix_apply, hb1, Complex.coe_basisOneI_repr]; rfl
      have c11 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (↑A : ℂ →ₗ[ℝ] ℂ)) 1 1 = d := by
        rw [LinearMap.toMatrix_apply, hb1, Complex.coe_basisOneI_repr]; rfl
      have h0 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (↑A : ℂ →ₗ[ℝ] ℂ)) = !![a, c; b, d] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
            Matrix.cons_val_fin_one] <;>
          first | exact c00 | exact c01 | exact c10 | exact c11
      rw [h0, Matrix.det_fin_two_of]; ring
    have hp2 : ‖p‖ ^ 2 = ((a + d) ^ 2 + (b - c) ^ 2) / 4 := by
      rw [← Complex.normSq_eq_norm_sq, hpval, Complex.normSq_apply]
      have h12re : (1 / 2 : ℂ).re = 1 / 2 := by norm_num [Complex.div_re]
      have h12im : (1 / 2 : ℂ).im = 0 := by norm_num [Complex.div_im]
      have hre : ((1 / 2 : ℂ) * ((A 1) - Complex.I * (A Complex.I))).re = (a + d) / 2 := by
        rw [ha, hd]
        simp only [Complex.mul_re, Complex.sub_re, Complex.mul_im, Complex.sub_im,
          Complex.I_re, Complex.I_im, h12re, h12im]
        ring
      have him : ((1 / 2 : ℂ) * ((A 1) - Complex.I * (A Complex.I))).im = (b - c) / 2 := by
        rw [hb, hc]
        simp only [Complex.mul_im, Complex.sub_re, Complex.mul_re, Complex.sub_im,
          Complex.I_re, Complex.I_im, h12re, h12im]
        ring
      rw [hre, him]; ring
    have hq2 : ‖q‖ ^ 2 = ((a - d) ^ 2 + (b + c) ^ 2) / 4 := by
      rw [← Complex.normSq_eq_norm_sq, hqval, Complex.normSq_apply]
      have h12re : (1 / 2 : ℂ).re = 1 / 2 := by norm_num [Complex.div_re]
      have h12im : (1 / 2 : ℂ).im = 0 := by norm_num [Complex.div_im]
      have hre : ((1 / 2 : ℂ) * ((A 1) + Complex.I * (A Complex.I))).re = (a - d) / 2 := by
        rw [ha, hd]
        simp only [Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im,
          Complex.I_re, Complex.I_im, h12re, h12im]
        ring
      have him : ((1 / 2 : ℂ) * ((A 1) + Complex.I * (A Complex.I))).im = (b + c) / 2 := by
        rw [hb, hc]
        simp only [Complex.mul_im, Complex.add_re, Complex.mul_re, Complex.add_im,
          Complex.I_re, Complex.I_im, h12re, h12im]
        ring
      rw [hre, him]; ring
    rw [hdet, hp2, hq2]; ring
  ----------------------------------------------------------------------------
  -- Antilipschitz lower bound for the invertible derivative A.
  ----------------------------------------------------------------------------
  have hAlb : ∃ c > 0, ∀ w : ℂ, c * ‖w‖ ≤ ‖A w‖ := by
    have hdetne : A.det ≠ 0 := hz'
    have hunit : IsUnit (A : ℂ →ₗ[ℝ] ℂ) := by
      rw [LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      rwa [ContinuousLinearMap.det] at hdetne
    have hker : LinearMap.ker (A : ℂ →ₗ[ℝ] ℂ) = ⊥ := by
      obtain ⟨u, hu⟩ := hunit
      rw [LinearMap.ker_eq_bot]
      have hinj : Function.Injective (u.inv ∘ₗ (A : ℂ →ₗ[ℝ] ℂ)) →
          Function.Injective (A : ℂ →ₗ[ℝ] ℂ) := by
        intro hcomp
        exact Function.Injective.of_comp (f := u.inv)
          (by rw [← LinearMap.coe_comp]; exact hcomp)
      apply hinj
      have hid : u.inv ∘ₗ (A : ℂ →ₗ[ℝ] ℂ) = LinearMap.id := by rw [← hu]; exact u.inv_val
      rw [hid]; exact Function.injective_id
    obtain ⟨K, hK, hAnti⟩ := (A : ℂ →ₗ[ℝ] ℂ).exists_antilipschitzWith hker
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    refine ⟨(K : ℝ)⁻¹, by positivity, fun w => ?_⟩
    have hd := hAnti.le_mul_dist (x := w) (y := 0)
    simp only [dist_zero_right, map_zero] at hd
    rw [inv_mul_le_iff₀ hKpos]
    exact hd
  obtain ⟨c, hc, hAlb⟩ := hAlb
  ----------------------------------------------------------------------------
  -- The little-o bound for the increment of f at z.
  ----------------------------------------------------------------------------
  have hob : ∃ δ > 0, ∀ h : ℂ, ‖h‖ < δ →
      ‖f (z + h) - f z - A h‖ ≤ (c / 2) * ‖h‖ := by
    have hlo : (fun h => f (z + h) - f z - A h) =o[𝓝 0] fun h => h := by
      have := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hz.hasFDerivAt)
      simpa only [hAdef] using this
    rw [Asymptotics.isLittleO_iff] at hlo
    have hc2 := hlo (show (0 : ℝ) < c / 2 by positivity)
    rw [Metric.eventually_nhds_iff] at hc2
    obtain ⟨δ, hδ, hmem⟩ := hc2
    refine ⟨δ, hδ, fun h hh => ?_⟩
    have hball : dist h 0 < δ := by rwa [dist_zero_right]
    simpa using hmem hball
  obtain ⟨δ, hδ, hob⟩ := hob
  ----------------------------------------------------------------------------
  -- CORE: for any 0 < r < δ, an explicit lift Lℓ of the linear circle ℓ_r with
  -- increment V yields a GLOBAL continuous lift of the image loop γ_r with the
  -- same increment V (built from Lℓ and a slit-plane logarithm of γ_r / ℓ_r).
  ----------------------------------------------------------------------------
  have core : ∀ (r : ℝ), 0 < r → r < δ →
      ∀ (V : ℂ) (Lℓ : ℝ → ℂ), Continuous Lℓ →
        (∀ θ : ℝ, Complex.exp (Lℓ θ)
          = (r : ℂ) * (p * Complex.exp ((θ : ℂ) * Complex.I)
            + q * Complex.exp (-((θ : ℂ) * Complex.I)))) →
        Lℓ (2 * Real.pi) - Lℓ 0 = V →
      ∃ Lstar : ℝ → ℂ, Continuous Lstar ∧
        (∀ θ : ℝ, Complex.exp (Lstar θ)
          = f (z + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - f z) ∧
        Lstar (2 * Real.pi) - Lstar 0 = V := by
    intro r hr hrδ V Lℓ hLℓc hLℓe hLℓincr
    set γ : ℝ → ℂ := fun θ => f (z + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - f z with hγ
    set ℓ : ℝ → ℂ := fun θ => (r : ℂ) * (p * Complex.exp ((θ : ℂ) * Complex.I)
        + q * Complex.exp (-((θ : ℂ) * Complex.I))) with hℓ
    have hnorm_eiθ : ∀ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
      intro θ; rw [Complex.norm_exp]; simp [Complex.mul_re]
    have hconj : ∀ θ : ℝ, (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I))
        = Complex.exp (-((θ : ℂ) * Complex.I)) := by
      intro θ; rw [← Complex.exp_conj]; congr 1
      simp [Complex.conj_ofReal, Complex.conj_I]
    have hAℓ : ∀ θ : ℝ, A ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = ℓ θ := by
      intro θ
      rw [hArep, map_mul, hconj, Complex.conj_ofReal]
      simp only [hℓ]; ring
    have hr_eiθ_norm : ∀ θ : ℝ, ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
      intro θ
      rw [norm_mul, hnorm_eiθ, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have hdiff : ∀ θ : ℝ, ‖γ θ - ℓ θ‖ ≤ (c / 2) * r := by
      intro θ
      have heq : γ θ - ℓ θ = f (z + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - f z
          - A ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
        rw [hAℓ θ]
      rw [heq]
      have hb := hob ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
        (by rw [hr_eiθ_norm]; exact hrδ)
      rw [hr_eiθ_norm] at hb
      exact hb
    have hℓlb : ∀ θ : ℝ, r * c ≤ ‖ℓ θ‖ := by
      intro θ
      rw [← hAℓ θ]
      have hlb := hAlb ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      rw [hr_eiθ_norm] at hlb
      linarith [hlb]
    have hℓne : ∀ θ : ℝ, ℓ θ ≠ 0 := by
      intro θ
      rw [← norm_pos_iff]
      have := hℓlb θ; nlinarith [hr, hc]
    have hclose : ∀ θ : ℝ, ‖γ θ - ℓ θ‖ < ‖ℓ θ‖ := by
      intro θ
      have h1 := hdiff θ
      have h2 := hℓlb θ
      nlinarith [hr, hc, norm_nonneg (γ θ - ℓ θ)]
    have hγc : Continuous γ := by
      simp only [hγ]
      refine Continuous.sub ?_ continuous_const
      refine hfc.comp ?_
      refine continuous_const.add ?_
      exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
    have hℓc : Continuous ℓ := by
      simp only [hℓ]
      refine continuous_const.mul (Continuous.add ?_ ?_)
      · exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
      · exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
    -- both loops are 2π-periodic (their values at 0 and 2π agree)
    have hexp_loop : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [show (((2 * Real.pi : ℝ) : ℂ)) * Complex.I
            = ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I 1
    have hγper : γ 0 = γ (2 * Real.pi) := by
      simp only [hγ]
      congr 2
      rw [show ((2 * Real.pi : ℝ) : ℂ) = (2 * Real.pi : ℂ) by push_cast; ring,
          show ((0 : ℝ) : ℂ) = 0 by push_cast; ring]
      rw [show ((2 * Real.pi : ℂ)) * Complex.I
            = (0 : ℂ) * Complex.I + ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
            push_cast; ring]
      rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hℓper : ℓ 0 = ℓ (2 * Real.pi) := by
      simp only [hℓ]
      congr 2
      · rw [show ((2 * Real.pi : ℝ) : ℂ) = (2 * Real.pi : ℂ) by push_cast; ring,
            show ((0 : ℝ) : ℂ) = 0 by push_cast; ring]
        rw [show ((2 * Real.pi : ℂ)) * Complex.I
              = (0 : ℂ) * Complex.I + ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
              push_cast; ring]
        rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      · rw [show -(((2 * Real.pi : ℝ) : ℂ) * Complex.I)
              = -(((0 : ℝ) : ℂ) * Complex.I)
                + ((-1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
        rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    -- ratio ρ = γ / ℓ is in the slit plane, giving a global continuous log
    set ρ : ℝ → ℂ := fun θ => γ θ / ℓ θ with hρ
    have hρslit : ∀ θ : ℝ, ρ θ ∈ Complex.slitPlane := by
      intro θ
      refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
      have hsub : ρ θ - 1 = (γ θ - ℓ θ) / ℓ θ := by
        simp only [hρ]; rw [div_sub_one (hℓne θ)]
      have hnormlt : ‖ρ θ - 1‖ < 1 := by
        rw [hsub, norm_div, div_lt_one (by rw [norm_pos_iff]; exact hℓne θ)]
        exact hclose θ
      have hbnd := Complex.abs_re_le_norm (ρ θ - 1)
      have hlt := lt_of_le_of_lt hbnd hnormlt
      have h2 := (abs_lt.mp hlt).1
      have hre : (ρ θ - 1).re = (ρ θ).re - 1 := by simp [Complex.sub_re]
      rw [hre] at h2; linarith
    have hρne : ∀ θ : ℝ, ρ θ ≠ 0 := fun θ => Complex.slitPlane_ne_zero (hρslit θ)
    have hρc : Continuous ρ := by simp only [hρ]; exact hγc.div hℓc (fun θ => hℓne θ)
    refine ⟨fun θ => Lℓ θ + Complex.log (ρ θ), hLℓc.add (hρc.clog hρslit), ?_, ?_⟩
    · intro θ
      rw [Complex.exp_add, hLℓe θ, Complex.exp_log (hρne θ)]
      have hℓval : (r : ℂ) * (p * Complex.exp ((θ : ℂ) * Complex.I)
          + q * Complex.exp (-((θ : ℂ) * Complex.I))) = ℓ θ := rfl
      rw [hℓval]
      simp only [hρ]
      rw [mul_div_cancel₀ _ (hℓne θ)]
    · have hρper : ρ (2 * Real.pi) = ρ 0 := by simp only [hρ]; rw [← hγper, ← hℓper]
      simp only
      rw [hρper]
      have : Lℓ (2 * Real.pi) + Complex.log (ρ 0) - (Lℓ 0 + Complex.log (ρ 0))
          = Lℓ (2 * Real.pi) - Lℓ 0 := by ring
      rw [this, hLℓincr]
  ----------------------------------------------------------------------------
  -- Explicit lift of the linear circle, det > 0 case (‖q‖ < ‖p‖), increment 2πi.
  ----------------------------------------------------------------------------
  have liftPos : ∀ (r : ℝ), 0 < r → ‖q‖ < ‖p‖ →
      ∃ Lℓ : ℝ → ℂ, Continuous Lℓ ∧
        (∀ θ : ℝ, Complex.exp (Lℓ θ) = (r : ℂ) * (p * Complex.exp ((θ : ℂ) * Complex.I)
          + q * Complex.exp (-((θ : ℂ) * Complex.I)))) ∧
        Lℓ (2 * Real.pi) - Lℓ 0 = 2 * (Real.pi : ℂ) * Complex.I := by
    intro r hr hpq
    have hp_ne : p ≠ 0 := by
      intro h; rw [h] at hpq; simp only [norm_zero] at hpq
      exact absurd hpq (not_lt.mpr (norm_nonneg q))
    have hr_ne : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
    set wθ : ℝ → ℂ := fun θ => 1 + (q / p) * Complex.exp (-(2 * (θ : ℂ) * Complex.I)) with hwθ
    have hnorm : ∀ θ : ℝ, ‖(q / p) * Complex.exp (-(2 * (θ : ℂ) * Complex.I))‖ < 1 := by
      intro θ
      rw [norm_mul]
      have he : ‖Complex.exp (-(2 * (θ : ℂ) * Complex.I))‖ = 1 := by
        rw [Complex.norm_exp]; simp [Complex.neg_re, Complex.mul_re, Complex.mul_im]
      rw [he, mul_one, norm_div, div_lt_one (by positivity)]
      exact hpq
    have hw_re : ∀ θ : ℝ, 0 < (wθ θ).re := by
      intro θ
      have h1 : (wθ θ).re = 1 + ((q / p) * Complex.exp (-(2 * (θ : ℂ) * Complex.I))).re := by
        simp [hwθ, Complex.add_re]
      rw [h1]
      have hbnd := Complex.abs_re_le_norm ((q / p) * Complex.exp (-(2 * (θ : ℂ) * Complex.I)))
      have hlt := lt_of_le_of_lt hbnd (hnorm θ)
      have h2 := (abs_lt.mp hlt).1
      linarith
    have hw_slit : ∀ θ : ℝ, wθ θ ∈ Complex.slitPlane := fun θ =>
      Complex.mem_slitPlane_iff.mpr (Or.inl (hw_re θ))
    have hw_ne : ∀ θ : ℝ, wθ θ ≠ 0 := by
      intro θ h
      have hh := hw_re θ; rw [h] at hh; simp at hh
    have hwcont : Continuous wθ := by
      refine continuous_const.add (Continuous.mul continuous_const ?_)
      exact Complex.continuous_exp.comp (by fun_prop)
    refine ⟨fun θ => Complex.log ((r : ℂ) * p) + (θ : ℂ) * Complex.I + Complex.log (wθ θ),
      ?_, ?_, ?_⟩
    · refine Continuous.add (Continuous.add continuous_const ?_) (hwcont.clog hw_slit)
      exact Complex.continuous_ofReal.mul continuous_const
    · intro θ
      rw [Complex.exp_add, Complex.exp_add, Complex.exp_log (mul_ne_zero hr_ne hp_ne),
          Complex.exp_log (hw_ne θ)]
      have key : Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-(2 * (θ : ℂ) * Complex.I))
          = Complex.exp (-((θ : ℂ) * Complex.I)) := by
        rw [← Complex.exp_add]; ring_nf
      rw [hwθ]
      have expand : (r : ℂ) * p * Complex.exp ((θ : ℂ) * Complex.I) *
          (1 + q / p * Complex.exp (-(2 * (θ : ℂ) * Complex.I)))
          = (r : ℂ) * p * Complex.exp ((θ : ℂ) * Complex.I)
            + (r : ℂ) * (q / p * p)
              * (Complex.exp ((θ : ℂ) * Complex.I)
                * Complex.exp (-(2 * (θ : ℂ) * Complex.I))) := by
        ring
      rw [expand, key, div_mul_cancel₀ q hp_ne]
      ring
    · have hcancel : wθ (2 * Real.pi) = wθ 0 := by
        simp only [hwθ]
        have h1 : Complex.exp (-(2 * ((2 * Real.pi : ℝ) : ℂ) * Complex.I))
            = Complex.exp (-(2 * ((0 : ℝ) : ℂ) * Complex.I)) := by
          rw [show (-(2 * ((2 * Real.pi : ℝ) : ℂ) * Complex.I))
                = (-(2 * ((0 : ℝ) : ℂ) * Complex.I))
                  + ((-2 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
          rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
        rw [h1]
      simp only
      rw [hcancel]; push_cast; ring
  ----------------------------------------------------------------------------
  -- Explicit lift of the linear circle, det < 0 case (‖p‖ < ‖q‖), increment -2πi.
  ----------------------------------------------------------------------------
  have liftNeg : ∀ (r : ℝ), 0 < r → ‖p‖ < ‖q‖ →
      ∃ Lℓ : ℝ → ℂ, Continuous Lℓ ∧
        (∀ θ : ℝ, Complex.exp (Lℓ θ) = (r : ℂ) * (p * Complex.exp ((θ : ℂ) * Complex.I)
          + q * Complex.exp (-((θ : ℂ) * Complex.I)))) ∧
        Lℓ (2 * Real.pi) - Lℓ 0 = -(2 * (Real.pi : ℂ) * Complex.I) := by
    intro r hr hpq
    have hq_ne : q ≠ 0 := by
      intro h; rw [h] at hpq; simp only [norm_zero] at hpq
      exact absurd hpq (not_lt.mpr (norm_nonneg p))
    have hr_ne : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
    set wθ : ℝ → ℂ := fun θ => 1 + (p / q) * Complex.exp ((2 * (θ : ℂ) * Complex.I)) with hwθ
    have hnorm : ∀ θ : ℝ, ‖(p / q) * Complex.exp ((2 * (θ : ℂ) * Complex.I))‖ < 1 := by
      intro θ
      rw [norm_mul]
      have he : ‖Complex.exp ((2 * (θ : ℂ) * Complex.I))‖ = 1 := by
        rw [Complex.norm_exp]; simp [Complex.mul_re, Complex.mul_im]
      rw [he, mul_one, norm_div, div_lt_one (by positivity)]
      exact hpq
    have hw_re : ∀ θ : ℝ, 0 < (wθ θ).re := by
      intro θ
      have h1 : (wθ θ).re = 1 + ((p / q) * Complex.exp ((2 * (θ : ℂ) * Complex.I))).re := by
        simp [hwθ, Complex.add_re]
      rw [h1]
      have hbnd := Complex.abs_re_le_norm ((p / q) * Complex.exp ((2 * (θ : ℂ) * Complex.I)))
      have hlt := lt_of_le_of_lt hbnd (hnorm θ)
      have h2 := (abs_lt.mp hlt).1
      linarith
    have hw_slit : ∀ θ : ℝ, wθ θ ∈ Complex.slitPlane := fun θ =>
      Complex.mem_slitPlane_iff.mpr (Or.inl (hw_re θ))
    have hw_ne : ∀ θ : ℝ, wθ θ ≠ 0 := by
      intro θ h
      have hh := hw_re θ; rw [h] at hh; simp at hh
    have hwcont : Continuous wθ := by
      refine continuous_const.add (Continuous.mul continuous_const ?_)
      exact Complex.continuous_exp.comp (by fun_prop)
    refine ⟨fun θ => Complex.log ((r : ℂ) * q) + (-(θ : ℂ) * Complex.I) + Complex.log (wθ θ),
      ?_, ?_, ?_⟩
    · refine Continuous.add (Continuous.add continuous_const ?_) (hwcont.clog hw_slit)
      exact (Complex.continuous_ofReal.neg).mul continuous_const
    · intro θ
      rw [Complex.exp_add, Complex.exp_add, Complex.exp_log (mul_ne_zero hr_ne hq_ne),
          Complex.exp_log (hw_ne θ)]
      have key : Complex.exp (-(θ : ℂ) * Complex.I) * Complex.exp ((2 * (θ : ℂ) * Complex.I))
          = Complex.exp ((θ : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]; ring_nf
      rw [hwθ]
      have expand : (r : ℂ) * q * Complex.exp (-(θ : ℂ) * Complex.I) *
          (1 + p / q * Complex.exp ((2 * (θ : ℂ) * Complex.I)))
          = (r : ℂ) * q * Complex.exp (-(θ : ℂ) * Complex.I)
            + (r : ℂ) * (p / q * q)
              * (Complex.exp (-(θ : ℂ) * Complex.I)
                * Complex.exp ((2 * (θ : ℂ) * Complex.I))) := by
        ring
      rw [expand, key, div_mul_cancel₀ p hq_ne]
      have hneg : Complex.exp (-(θ : ℂ) * Complex.I) = Complex.exp (-((θ : ℂ) * Complex.I)) := by
        congr 1; ring
      rw [hneg]; ring
    · have hcancel : wθ (2 * Real.pi) = wθ 0 := by
        simp only [hwθ]
        have h1 : Complex.exp ((2 * ((2 * Real.pi : ℝ) : ℂ) * Complex.I))
            = Complex.exp ((2 * ((0 : ℝ) : ℂ) * Complex.I)) := by
          rw [show ((2 * ((2 * Real.pi : ℝ) : ℂ) * Complex.I))
                = ((2 * ((0 : ℝ) : ℂ) * Complex.I))
                  + ((2 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
          rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
        rw [h1]
      simp only
      rw [hcancel]; push_cast; ring
  ----------------------------------------------------------------------------
  -- Small positive radii: eventually `0 < r ∧ r < δ` in `𝓝[>] 0`.
  ----------------------------------------------------------------------------
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r ∧ r < δ := by
    have h1 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), (0 : ℝ) < r := by
      rw [eventually_nhdsWithin_iff]; filter_upwards with r hr using hr
    have h2 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < δ := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with r hr using hr
    filter_upwards [h1, h2] with r hr1 hr2 using ⟨hr1, hr2⟩
  ----------------------------------------------------------------------------
  -- Assemble the iff.
  ----------------------------------------------------------------------------
  rw [hdet_eq]
  constructor
  · -- mp : the winding-one statement forces `‖q‖² < ‖p‖²`.
    intro hwind
    by_contra hnotpos
    -- `det ≤ 0` and `det ≠ 0` ⟹ `det < 0` ⟹ `‖p‖ < ‖q‖`.
    have hdetne : ‖p‖ ^ 2 - ‖q‖ ^ 2 ≠ 0 := by rw [← hdet_eq]; exact hz'
    have hltdet : ‖p‖ ^ 2 - ‖q‖ ^ 2 < 0 := lt_of_le_of_ne (not_lt.mp hnotpos) hdetne
    have hpqlt : ‖p‖ < ‖q‖ := by nlinarith [norm_nonneg p, norm_nonneg q]
    -- pick a small `r` admitting a winding-one lift.
    obtain ⟨r, ⟨hr, hrδ⟩, L, hLc, hLe, hLincr⟩ := (hsmall.and hwind).exists
    -- the negative explicit linear lift gives increment `-2πi`.
    obtain ⟨Lℓ, hLℓc, hLℓe, hLℓincr⟩ := liftNeg r hr hpqlt
    obtain ⟨Lstar, hLstarc, hLstare, hLstarincr⟩ :=
      core r hr hrδ (-(2 * (Real.pi : ℂ) * Complex.I)) Lℓ hLℓc hLℓe hLℓincr
    -- by well-definedness, the given lift `L` has the same increment `-2πi`.
    have hLeqLstar : L (2 * Real.pi) - L 0 = Lstar (2 * Real.pi) - Lstar 0 := by
      refine helperW L Lstar hLc hLstarc ?_
      intro t _; rw [hLe t, hLstare t]
    rw [hLincr, hLstarincr] at hLeqLstar
    -- `2πi = -2πi` forces `2πi = 0`, contradiction.
    have : (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
      have h2 : (2 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
        linear_combination hLeqLstar
      have h2' : (2 : ℂ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h2).resolve_left h2'
    exact h2pi_ne this
  · -- mpr : `0 < ‖p‖² - ‖q‖²` produces winding-one lifts for all small `r`.
    intro hpos
    have hpqgt : ‖q‖ < ‖p‖ := by nlinarith [norm_nonneg p, norm_nonneg q]
    filter_upwards [hsmall] with r hr_pair
    obtain ⟨hr, hrδ⟩ := hr_pair
    obtain ⟨Lℓ, hLℓc, hLℓe, hLℓincr⟩ := liftPos r hr hpqgt
    obtain ⟨Lstar, hLstarc, hLstare, hLstarincr⟩ :=
      core r hr hrδ (2 * (Real.pi : ℂ) * Complex.I) Lℓ hLℓc hLℓe hLℓincr
    exact ⟨Lstar, hLstarc, hLstare, hLstarincr⟩

/-- **Forward bridge (analytic ⇒ topological orientation).** An orientation-preserving
homeomorphism — a homeomorphism with almost-everywhere positive Jacobian determinant — is
topologically sense-preserving. At an a.e. point of differentiability with positive
Jacobian the image circles wind `+1` by `windingOne_iff_det_pos`. -/
theorem SensePreserving.of_orientationPreservingHomeo {f : ℂ → ℂ}
    (hf : OrientationPreservingHomeo f) : SensePreserving f := by
  refine ⟨hf.1, ?_⟩
  filter_upwards [hf.2] with z₀ hz₀
  have hdiff : DifferentiableAt ℝ f z₀ := by
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at hz₀
    simp [ContinuousLinearMap.det] at hz₀
  exact (windingOne_iff_det_pos hf.1.continuous hdiff (ne_of_gt hz₀)).mpr hz₀

/-- **Backward bridge (topological orientation ⇒ analytic, almost-everywhere form).** A
sense-preserving homeomorphism that is almost everywhere differentiable with invertible
derivative has almost-everywhere positive Jacobian determinant. At an a.e. point the image
circles wind `+1` (the sense-preserving hypothesis) and `windingOne_iff_det_pos` forces the
Jacobian to be positive. -/
theorem SensePreserving.ae_det_pos {f : ℂ → ℂ} (hf : SensePreserving f)
    (hae : ∀ᵐ z : ℂ, DifferentiableAt ℝ f z ∧ (fderiv ℝ f z).det ≠ 0) :
    ∀ᵐ z : ℂ, 0 < (fderiv ℝ f z).det := by
  filter_upwards [hf.2, hae] with z hwind hz
  exact (windingOne_iff_det_pos hf.1.continuous hz.1 hz.2).mp hwind

end NoWanderingDomains
