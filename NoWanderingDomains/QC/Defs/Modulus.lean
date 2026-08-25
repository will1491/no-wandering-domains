/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Sobolev.WeakDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Conformal modulus of a curve family

The **conformal modulus** (equivalently, the reciprocal of the extremal length) of a
family of curves is the conformal invariant underlying the geometric definition of
quasiconformality. This file develops the minimum needed for the geometric
quasiconformal track: the arc-length line integral of a density, admissible
densities, and the modulus of a curve family.

A curve here is a map `γ : ℝ → ℂ` parametrized on the unit interval `[0, 1]`; a
curve family `Γ` is a `Set (ℝ → ℂ)`. A **density** `ρ : ℂ → ℝ≥0∞` is *admissible*
for `Γ` when its arc-length line integral along every curve of the family is at
least `1`, and the modulus is the infimum of the area energy `∫∫ ρ²` over all
admissible densities:

`mod Γ = inf { ∫_ℂ ρ² dA : ρ admissible for Γ }`.

The modulus is monotone in the family and conformally invariant; these are the two
properties the geometric quasiconformal theory rests on. The full extremal-length /
Grötzsch theory (the sharp modulus estimates) is not developed
here; we record only the definitions and the structural lemmas the
`IsQCGeometric` definition and the analytic/geometric equivalence consume.

## Main definitions

* `arcLengthLineIntegral ρ γ` — `∫₀¹ ρ(γ t) ‖γ'(t)‖ dt`, the line integral of the
  density `ρ` along the curve `γ` with respect to arc length;
* `IsAdmissibleDensity ρ Γ` — `ρ` is measurable and `arcLengthLineIntegral ρ γ ≥ 1`
  for every `γ ∈ Γ`;
* `curveModulus Γ` — the infimum of `∫_ℂ ρ²` over densities admissible for `Γ`.
-/

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- The **arc-length line integral** of a density `ρ : ℂ → ℝ≥0∞` along a curve
`γ : ℝ → ℂ` parametrized on `[0, 1]`: `∫₀¹ ρ(γ t) ‖γ'(t)‖ dt`. For an absolutely
continuous curve this is the integral of `ρ` with respect to arc length. -/
noncomputable def arcLengthLineIntegral (ρ : ℂ → ℝ≥0∞) (γ : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Icc (0 : ℝ) 1, ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)

/-- A density `ρ : ℂ → ℝ≥0∞` is **admissible** for a curve family `Γ` when it is
measurable and its arc-length line integral along every curve of the family is at
least `1`. -/
def IsAdmissibleDensity (ρ : ℂ → ℝ≥0∞) (Γ : Set (ℝ → ℂ)) : Prop :=
  Measurable ρ ∧ ∀ γ ∈ Γ, 1 ≤ arcLengthLineIntegral ρ γ

/-- The **conformal modulus** of a curve family `Γ`: the infimum of the area energy
`∫_ℂ ρ²` over all densities `ρ` admissible for `Γ`. This is the conformal invariant
the geometric definition of quasiconformality is built on. -/
noncomputable def curveModulus (Γ : Set (ℝ → ℂ)) : ℝ≥0∞ :=
  ⨅ ρ ∈ {ρ : ℂ → ℝ≥0∞ | IsAdmissibleDensity ρ Γ}, ∫⁻ z, (ρ z) ^ 2

/-- **Monotonicity of the modulus.** A larger curve family imposes more
admissibility constraints, so its modulus is at least as large: if `Γ₁ ⊆ Γ₂` then
`curveModulus Γ₁ ≤ curveModulus Γ₂`. -/
theorem curveModulus_mono {Γ₁ Γ₂ : Set (ℝ → ℂ)} (h : Γ₁ ⊆ Γ₂) :
    curveModulus Γ₁ ≤ curveModulus Γ₂ := by
  -- A density admissible for the larger family `Γ₂` is admissible for `Γ₁`, so the
  -- admissible set for `Γ₂` is contained in that for `Γ₁`; the infimum over the
  -- smaller set is larger.
  refine biInf_mono ?_
  intro ρ hρ
  exact ⟨hρ.1, fun γ hγ => hρ.2 γ (h hγ)⟩

/-- **Conformal invariance of the modulus.** If `φ : ℂ → ℂ` is conformal (a
holomorphic homeomorphism), the modulus of a curve family is unchanged under
post-composition by `φ`: `curveModulus ((φ ∘ ·) '' Γ) = curveModulus Γ`. This is the
defining property the geometric quasiconformal theory measures the failure of. -/
theorem curveModulus_conformal_invariant {φ : ℂ → ℂ} (hφ : IsHomeomorph φ)
    (hφ' : DifferentiableOn ℂ φ Set.univ) (Γ : Set (ℝ → ℂ)) :
    curveModulus ((fun γ : ℝ → ℂ => φ ∘ γ) '' Γ) = curveModulus Γ := by
  classical
  -- ===================================================================
  -- Conformal invariance of the curve modulus.  φ is a holomorphic
  -- homeomorphism; the modulus is transferred via the density
  --   σ(w) = ρ(φ⁻¹ w) · ‖(φ' ∘ φ⁻¹) w‖⁻¹.
  -- Admissibility transfers by the chain rule; the energy ∫σ² = ∫ρ² by
  -- the change-of-variables formula with real Jacobian ‖φ' z‖².  The
  -- two inequalities are obtained by applying the same transfer to φ and
  -- to its inverse φ⁻¹ (also a holomorphic homeomorphism, by the inverse
  -- function theorem, using that an injective entire map has nonvanishing
  -- derivative).
  -- ===================================================================
  have hφentire : Differentiable ℂ φ := fun z =>
    (hφ' z (Set.mem_univ z)).differentiableAt (by simp)
  -- An analytic n-th root of a nonvanishing analytic germ.
  have analytic_nth_root : ∀ {G : ℂ → ℂ} {z₀ : ℂ} {n : ℕ}, AnalyticAt ℂ G z₀ →
      G z₀ ≠ 0 → 1 ≤ n →
      ∃ H : ℂ → ℂ, AnalyticAt ℂ H z₀ ∧ H z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, (H z) ^ n = G z := by
    intro G z₀ n hG hGz hn
    set c : ℂ := (↑‖G z₀‖ : ℂ) / G z₀ with hc_def
    have hnorm_pos : 0 < ‖G z₀‖ := by positivity
    have hc_ne : c ≠ 0 := by
      rw [hc_def]; exact div_ne_zero (by exact_mod_cast (norm_ne_zero_iff).mpr hGz) hGz
    have hcG : c * G z₀ = (↑‖G z₀‖ : ℂ) := by rw [hc_def]; field_simp
    have hcG_an : AnalyticAt ℂ (fun z => c * G z) z₀ := analyticAt_const.mul hG
    have hval_slit : (fun z => c * G z) z₀ ∈ Complex.slitPlane := by
      simp only [hcG]; rw [Complex.mem_slitPlane_iff]; left
      simp only [Complex.ofReal_re]; positivity
    set cr : ℂ := Complex.exp (Complex.log c / n) with hcr_def
    have hcr_ne : cr ≠ 0 := Complex.exp_ne_zero _
    have hcr_pow : cr ^ n = c := by
      rw [hcr_def, ← Complex.exp_nat_mul, mul_div_cancel₀]
      · exact Complex.exp_log hc_ne
      · exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
    refine ⟨fun z => Complex.exp (Complex.log (c * G z) / n) / cr, ?_, ?_, ?_⟩
    · apply AnalyticAt.div _ analyticAt_const hcr_ne
      have hlog : AnalyticAt ℂ (fun z => Complex.log (c * G z)) z₀ := hcG_an.clog hval_slit
      have hdiv : AnalyticAt ℂ (fun z => Complex.log (c * G z) / n) z₀ :=
        hlog.div analyticAt_const (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))
      exact hdiv.cexp'
    · exact div_ne_zero (Complex.exp_ne_zero _) hcr_ne
    · have hcont : ContinuousAt (fun z => c * G z) z₀ := hcG_an.continuousAt
      have hGne_ev : ∀ᶠ z in 𝓝 z₀, c * G z ≠ 0 := hcont.eventually_ne (mul_ne_zero hc_ne hGz)
      filter_upwards [hGne_ev] with z hz
      rw [div_pow, ← Complex.exp_nat_mul,
        mul_div_cancel₀ _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn) : (n : ℂ) ≠ 0)]
      rw [Complex.exp_log hz, hcr_pow]; field_simp
  -- An injective entire map has nowhere-vanishing derivative.
  have deriv_ne_zero : ∀ (η : ℂ → ℂ), IsHomeomorph η → Differentiable ℂ η →
      ∀ z, deriv η z ≠ 0 := by
    intro η hη hη' z hderiv0
    have hinj : Function.Injective η := hη.injective
    set g : ℂ → ℂ := fun w => η w - η z with hg_def
    have hη_an : ∀ w, AnalyticAt ℂ η w := fun w =>
      (hη'.differentiableOn).analyticAt Filter.univ_mem
    have hg_an : AnalyticAt ℂ g z := (hη_an z).sub analyticAt_const
    have hge2 : 2 ≤ analyticOrderAt g z := by
      have hdη_an : AnalyticAt ℂ (deriv η) z := (hη_an z).deriv
      have key := (hη_an z).analyticOrderAt_deriv_add_one
      have hge1 : 1 ≤ analyticOrderAt (deriv η) z := by
        rw [Order.one_le_iff_ne_zero, Ne, analyticOrderAt_eq_zero, not_or, not_not, not_ne_iff]
        exact ⟨hdη_an, hderiv0⟩
      calc (2 : ℕ∞) = 1 + 1 := by rfl
        _ ≤ analyticOrderAt (deriv η) z + 1 := by gcongr
        _ = analyticOrderAt g z := key
    have hne_top : analyticOrderAt g z ≠ ⊤ := by
      rw [Ne, analyticOrderAt_eq_top]
      intro hev
      have hev2 : ∀ᶠ w in 𝓝[≠] z, η w = η z := by
        have hev' : ∀ᶠ w in 𝓝[≠] z, g w = 0 := hev.filter_mono nhdsWithin_le_nhds
        filter_upwards [hev'] with w hw
        simpa [hg_def, sub_eq_zero] using hw
      obtain ⟨w, hw, hwne⟩ := (hev2.and self_mem_nhdsWithin).exists
      exact hwne (hinj hw)
    obtain ⟨n, hn2, hordern⟩ : ∃ n : ℕ, 2 ≤ n ∧ analyticOrderAt g z = (n : ℕ∞) := by
      lift analyticOrderAt g z to ℕ using hne_top with m hm
      exact ⟨m, by exact_mod_cast hge2, rfl⟩
    obtain ⟨G, hG_an, hGz, hdecomp⟩ := (hg_an.analyticOrderAt_eq_natCast).mp hordern
    have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
    obtain ⟨H, hH_an, hHz, hHpow⟩ := analytic_nth_root hG_an hGz hn1
    set u : ℂ → ℂ := fun w => (w - z) * H w with hu_def
    have hu_an : AnalyticAt ℂ u z := (analyticAt_id.sub analyticAt_const).mul hH_an
    have huz : u z = 0 := by simp [hu_def]
    have hu_deriv : HasDerivAt u (H z) z := by
      have h1 : HasDerivAt (fun w : ℂ => w - z) 1 z := by
        simpa using (hasDerivAt_id z).sub_const z
      have h2 : HasDerivAt H (deriv H z) z := hH_an.differentiableAt.hasDerivAt
      have h3 := h1.mul h2
      simp only [sub_self, zero_mul, add_zero, one_mul] at h3
      exact h3
    have hu_strict : HasStrictDerivAt u (H z) z := by
      have hs := hu_an.hasStrictDerivAt
      rwa [hu_deriv.deriv] at hs
    have hg_eq_un : ∀ᶠ w in 𝓝 z, g w = (u w) ^ n := by
      filter_upwards [hdecomp, hHpow] with w hw hHw
      rw [hw, hu_def]; simp only; rw [mul_pow, smul_eq_mul, hHw]
    have hu_locinj := hu_strict.eventually_left_inverse hHz
    have hu_open : 𝓝 (0 : ℂ) ≤ Filter.map u (𝓝 z) := by
      rcases hu_an.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
      · exfalso
        have hconst' : u =ᶠ[𝓝 z] fun _ => u z := hconst
        have hd0 : deriv u z = 0 := by rw [hconst'.deriv_eq, deriv_const]
        rw [hu_deriv.deriv] at hd0; exact hHz hd0
      · rwa [huz] at hopen
    have hcombined : ∀ᶠ w in 𝓝 z,
        (hu_strict.localInverse u (H z) z hHz) (u w) = w ∧ g w = (u w) ^ n :=
      hu_locinj.and hg_eq_un
    obtain ⟨s, hs_mem, hs_prop⟩ := Filter.eventually_iff_exists_mem.mp hcombined
    have himg : u '' s ∈ 𝓝 (0 : ℂ) := Filter.le_map_iff.mp hu_open s hs_mem
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp himg
    set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n) with hζ_def
    have hζpow : ζ ^ n = 1 := (Complex.isPrimitiveRoot_exp n (by omega)).pow_eq_one
    have hζne1 : ζ ≠ 1 := (Complex.isPrimitiveRoot_exp n (by omega)).ne_one (by omega)
    have hζabs : ‖ζ‖ = 1 := by
      rw [hζ_def, Complex.norm_exp]
      simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    set t : ℂ := ((ρ / 2 : ℝ) : ℂ) with ht_def
    have ht_norm : ‖t‖ < ρ := by
      rw [ht_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
    have ht_ne : t ≠ 0 := by
      rw [ht_def]; simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
    have ht_ball : t ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball, dist_zero_right]; exact ht_norm
    have hζt_ball : ζ * t ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, hζabs, one_mul]; exact ht_norm
    obtain ⟨z₁, hz₁s, hz₁u⟩ := hball ht_ball
    obtain ⟨z₂, hz₂s, hz₂u⟩ := hball hζt_ball
    have hu_z₁ : u z₁ = t := hz₁u
    have hu_z₂ : u z₂ = ζ * t := hz₂u
    have hne12 : z₁ ≠ z₂ := by
      intro h; subst h
      rw [hu_z₁] at hu_z₂
      have hζeq1 : ζ = 1 := by
        have hkey : (1 - ζ) * t = 0 := by linear_combination hu_z₂
        rcases mul_eq_zero.mp hkey with h1 | h2
        · linear_combination -h1
        · exact (ht_ne h2).elim
      exact hζne1 hζeq1
    have hg1 := (hs_prop z₁ hz₁s).2
    have hg2 := (hs_prop z₂ hz₂s).2
    have heq : g z₁ = g z₂ := by
      rw [hg1, hg2, hu_z₁, hu_z₂, mul_pow, hζpow, one_mul]
    have hηeq : η z₁ = η z₂ := by
      rw [hg_def] at heq; simp only at heq; linear_combination heq
    exact hne12 (hinj hηeq)
  -- Real Jacobian of a holomorphic map: |det (fderiv ℝ η z)| = ‖deriv η z‖².
  have absdet : ∀ (z : ℂ) (c : ℂ),
      |((c • (1 : ℂ →L[ℝ] ℂ)).det)| = ‖c‖ ^ 2 := by
    intro _ c
    have hdetval : ((c • (1 : ℂ →L[ℝ] ℂ)).det) = ‖c‖ ^ 2 := by
      have key : ∀ M : ℂ →ₗ[ℝ] ℂ, LinearMap.det M
          = (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI M).det := fun M =>
        (LinearMap.det_toMatrix Complex.basisOneI M).symm
      rw [ContinuousLinearMap.det, key]
      have hb0 : (Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ) 0 = (1 : ℂ) := by
        simp [Complex.coe_basisOneI]
      have hb1 : (Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ) 1 = Complex.I := by
        simp [Complex.coe_basisOneI]
      have c00 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (↑(c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ)) 0 0 = c.re := by
        rw [LinearMap.toMatrix_apply, hb0, Complex.coe_basisOneI_repr]
        change ((↑(c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ) 1).re = c.re
        rw [ContinuousLinearMap.coe_coe, smul_apply,
          one_apply_eq_self, smul_eq_mul, mul_one]
      have c10 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (↑(c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ)) 1 0 = c.im := by
        rw [LinearMap.toMatrix_apply, hb0, Complex.coe_basisOneI_repr]
        change ((↑(c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ) 1).im = c.im
        rw [ContinuousLinearMap.coe_coe, smul_apply,
          one_apply_eq_self, smul_eq_mul, mul_one]
      have c01 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (↑(c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ)) 0 1 = -c.im := by
        rw [LinearMap.toMatrix_apply, hb1, Complex.coe_basisOneI_repr]
        change ((↑(c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ) Complex.I).re = -c.im
        rw [ContinuousLinearMap.coe_coe, smul_apply,
          one_apply_eq_self, smul_eq_mul, Complex.mul_re, Complex.I_re,
          Complex.I_im]; ring
      have c11 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (↑(c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ)) 1 1 = c.re := by
        rw [LinearMap.toMatrix_apply, hb1, Complex.coe_basisOneI_repr]
        change ((↑(c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ) Complex.I).im = c.re
        rw [ContinuousLinearMap.coe_coe, smul_apply,
          one_apply_eq_self, smul_eq_mul, Complex.mul_im, Complex.I_re,
          Complex.I_im]; ring
      have h0 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (↑(c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →ₗ[ℝ] ℂ)) = !![c.re, -c.im; c.im, c.re] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
            Matrix.cons_val_fin_one] <;>
          first | exact c00 | exact c01 | exact c10 | exact c11
      rw [h0, Matrix.det_fin_two_of]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hdetval, abs_of_nonneg (by positivity)]
  -- One-directional inequality: transfer of an admissible density under a
  -- conformal homeomorphism ψ.
  have step : ∀ ψ : ℂ → ℂ, IsHomeomorph ψ → Differentiable ℂ ψ → (∀ z, deriv ψ z ≠ 0) →
      ∀ Γ', curveModulus ((fun γ : ℝ → ℂ => ψ ∘ γ) '' Γ') ≤ curveModulus Γ' := by
    intro ψ hψ hψ' hderiv_ne Γ'
    apply le_iInf₂
    rintro ρ ⟨hρmeas, hρadm⟩
    set χ := (hψ.homeomorph ψ).symm with hχ
    set σ : ℂ → ℝ≥0∞ := fun w => ρ (χ w) * (‖deriv ψ (χ w)‖₊ : ℝ≥0∞)⁻¹ with hσ
    have hderivmeas : Measurable (deriv ψ) := by
      have h1 : AnalyticOnNhd ℂ ψ Set.univ :=
        fun z _ => (hψ'.differentiableOn).analyticAt Filter.univ_mem
      exact (continuousOn_univ.mp h1.deriv.continuousOn).measurable
    have hσmeas : Measurable σ := by
      apply Measurable.mul
      · exact hρmeas.comp χ.continuous.measurable
      · exact (((hderivmeas.comp χ.continuous.measurable).nnnorm).coe_nnreal_ennreal).inv
    have hσadm : IsAdmissibleDensity σ ((fun γ : ℝ → ℂ => ψ ∘ γ) '' Γ') := by
      refine ⟨hσmeas, ?_⟩
      rintro δ ⟨γ, hγΓ, rfl⟩
      have hpoint : ∀ t : ℝ,
          σ ((ψ ∘ γ) t) * (‖deriv (ψ ∘ γ) t‖₊ : ℝ≥0∞) = ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
        intro t
        have hsymm : χ (ψ (γ t)) = γ t := (hψ.homeomorph ψ).symm_apply_apply (γ t)
        simp only [hσ, Function.comp_apply]
        rw [hsymm]
        by_cases hd : DifferentiableAt ℝ γ t
        · have hC : HasDerivAt ψ (deriv ψ (γ t)) (γ t) := (hψ' (γ t)).hasDerivAt
          have hchain : deriv (ψ ∘ γ) t = deriv ψ (γ t) * deriv γ t := by
            have := (hC.complexToReal_fderiv.comp_hasDerivAt t hd.hasDerivAt).deriv
            simpa using this
          rw [hchain, nnnorm_mul]
          push_cast
          rw [mul_assoc]
          congr 1
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp [hderiv_ne (γ t)]) (by simp), one_mul]
        · have hgz : deriv γ t = 0 := deriv_zero_of_not_differentiableAt hd
          have hcomp_nd : ¬ DifferentiableAt ℝ (ψ ∘ γ) t := by
            intro hcd
            apply hd
            have hχd : HasDerivAt χ (deriv ψ (χ (ψ (γ t))))⁻¹ (ψ (γ t)) := by
              apply HasDerivAt.of_local_left_inverse
                χ.continuous.continuousAt ((hψ' _).hasDerivAt) (hderiv_ne _)
              filter_upwards with y using (hψ.homeomorph ψ).apply_symm_apply y
            have hd2 : DifferentiableAt ℝ (χ ∘ (ψ ∘ γ)) t :=
              (hχd.complexToReal_fderiv.comp_hasDerivAt t hcd.hasDerivAt).differentiableAt
            have heq : χ ∘ (ψ ∘ γ) = γ := by
              funext s; exact (hψ.homeomorph ψ).symm_apply_apply (γ s)
            rwa [heq] at hd2
          have hcz : deriv (ψ ∘ γ) t = 0 := deriv_zero_of_not_differentiableAt hcomp_nd
          rw [hgz, hcz]; simp
      have heqInt : arcLengthLineIntegral σ (ψ ∘ γ) = arcLengthLineIntegral ρ γ := by
        unfold arcLengthLineIntegral
        exact lintegral_congr fun t => hpoint t
      rw [heqInt]; exact hρadm γ hγΓ
    calc (⨅ ρ' ∈ {ρ' : ℂ → ℝ≥0∞ | IsAdmissibleDensity ρ' ((fun γ : ℝ → ℂ => ψ ∘ γ) '' Γ')},
            ∫⁻ z, (ρ' z) ^ 2)
        ≤ ∫⁻ z, (σ z) ^ 2 := iInf₂_le σ hσadm
      _ = ∫⁻ z, (ρ z) ^ 2 := by
          have hcov := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
              (volume : Measure ℂ) MeasurableSet.univ
              (f := ψ) (f' := fun z => deriv ψ z • (1 : ℂ →L[ℝ] ℂ))
              (fun z _ => ((hψ' z).hasDerivAt.complexToReal_fderiv).hasFDerivWithinAt)
              hψ.injective.injOn
              (fun w => (ρ (χ w)) ^ 2 * (‖deriv ψ (χ w)‖₊ : ℝ≥0∞)⁻¹ ^ 2)
          rw [Set.image_univ, hψ.surjective.range_eq] at hcov
          rw [show (fun z => (σ z) ^ 2)
                = (fun w => (ρ (χ w)) ^ 2 * (‖deriv ψ (χ w)‖₊ : ℝ≥0∞)⁻¹ ^ 2) from by
            funext w; rw [hσ, mul_pow]]
          rw [← setLIntegral_univ
            ((fun w => (ρ (χ w)) ^ 2 * (‖deriv ψ (χ w)‖₊ : ℝ≥0∞)⁻¹ ^ 2))]
          rw [hcov, setLIntegral_univ]
          apply lintegral_congr
          intro z
          have hχψ : χ (ψ z) = z := (hψ.homeomorph ψ).symm_apply_apply z
          rw [hχψ, absdet z (deriv ψ z)]
          rw [ENNReal.ofReal_pow (norm_nonneg _)]
          rw [show ENNReal.ofReal (‖deriv ψ z‖) = (‖deriv ψ z‖₊ : ℝ≥0∞) from by
            rw [ofReal_norm, enorm_eq_nnnorm]]
          rw [show (‖deriv ψ z‖₊ : ℝ≥0∞) ^ 2 * ((ρ z) ^ 2 * (‖deriv ψ z‖₊ : ℝ≥0∞)⁻¹ ^ 2)
              = ((‖deriv ψ z‖₊ : ℝ≥0∞) ^ 2 * ((‖deriv ψ z‖₊ : ℝ≥0∞)⁻¹) ^ 2) * (ρ z) ^ 2 from by
            ring]
          rw [← mul_pow, ENNReal.mul_inv_cancel (by simp [hderiv_ne z]) (by simp), one_pow, one_mul]
  -- Assemble the two inequalities, applying `step` to φ and to φ⁻¹.
  set χ := (hφ.homeomorph φ).symm with hχ
  have hd1 : ∀ z, deriv φ z ≠ 0 := deriv_ne_zero φ hφ hφentire
  have hχhomeo : IsHomeomorph χ := (hφ.homeomorph φ).symm.isHomeomorph
  have hχentire : Differentiable ℂ χ := by
    intro a
    have hψd : HasDerivAt χ (deriv φ (χ a))⁻¹ a := by
      apply HasDerivAt.of_local_left_inverse
        χ.continuous.continuousAt ((hφentire (χ a)).hasDerivAt) (hd1 _)
      filter_upwards with y using (hφ.homeomorph φ).apply_symm_apply y
    exact hψd.differentiableAt
  have hd2 : ∀ z, deriv χ z ≠ 0 := deriv_ne_zero χ hχhomeo hχentire
  have le1 : curveModulus ((fun γ : ℝ → ℂ => φ ∘ γ) '' Γ) ≤ curveModulus Γ :=
    step φ hφ hφentire hd1 Γ
  have le2 : curveModulus ((fun γ : ℝ → ℂ => χ ∘ γ) '' ((fun γ : ℝ → ℂ => φ ∘ γ) '' Γ))
      ≤ curveModulus ((fun γ : ℝ → ℂ => φ ∘ γ) '' Γ) :=
    step χ hχhomeo hχentire hd2 ((fun γ : ℝ → ℂ => φ ∘ γ) '' Γ)
  have hcancel : (fun γ : ℝ → ℂ => χ ∘ γ) '' ((fun γ : ℝ → ℂ => φ ∘ γ) '' Γ) = Γ := by
    rw [Set.image_image]
    conv_rhs => rw [← Set.image_id Γ]
    refine Set.image_congr fun γ _ => ?_
    funext s
    exact (hφ.homeomorph φ).symm_apply_apply (γ s)
  rw [hcancel] at le2
  exact le_antisymm le1 le2

end NoWanderingDomains
