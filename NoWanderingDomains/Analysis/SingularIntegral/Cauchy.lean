/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Sobolev.Wirtinger
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The Cauchy (area) transform and the Cauchy–Pompeiu formula

The **Cauchy transform** of `ω : ℂ → ℂ` is

`Pω(z) = -(1/π) ∫ ω(ζ)/(ζ - z) dA(ζ)`.

The kernel is written with denominator `ζ - z` (the standard `w - z`): with the
project's Wirtinger convention `∂̄ = ½(∂ₓ + i∂ᵧ)` and the fundamental solution
`∂̄(1/(πz)) = δ₀`, this is the sign that makes the Cauchy transform solve the
inhomogeneous `∂̄`-equation, `∂̄(Pω) = ω` (`dzbar_cauchyTransform`). The companion
holomorphic derivative `∂(Pω)` is the Beurling transform `T = ∂ ∘ P`
(`Analysis/SingularIntegral/Beurling/Kernel.lean`); together they invert the Beltrami
equation in the analytic quasiconformal theory.

The solvability `∂̄(Pω) = ω` factors through two facts about a `C¹` compactly
supported `ω`:

* `cauchyTransform_dzbar` — the **Cauchy–Pompeiu formula** `P(∂̄ω) = ω`: the area
  integral of `∂̄ω` against the Cauchy kernel recovers `ω`. This is the `∂̄`
  fundamental solution; it is proved by the complex Green's theorem
  (`Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`, whose area
  term is `2i ∂̄`) together with the `ε`-disc removal at the kernel singularity.
* `dzbar_cauchyTransform_eq` — **`∂̄ ∘ P = P ∘ ∂̄`**: differentiating `Pω` under
  the integral passes `∂̄` onto the smooth factor (the Cauchy transform is the
  convolution of `ω` with the locally integrable kernel `1/(π·)`, so
  `HasCompactSupport.hasFDerivAt_convolution_left` applies).

Composing the two gives `∂̄(Pω) = P(∂̄ω) = ω`.
-/

open MeasureTheory Complex
open scoped Real

namespace NoWanderingDomains

variable {ω : ℂ → ℂ} {z : ℂ}

/-- The **Cauchy transform** `Pω(z) = -(1/π) ∫ ω(ζ)/(ζ - z) dA(ζ)`. -/
noncomputable def cauchyTransform (ω : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(1 / (π : ℂ)) * ∫ ζ, ω ζ / (ζ - z)

/-- **Cauchy–Pompeiu formula.** For a `C¹` function of compact support the Cauchy
transform inverts `∂̄`: `P(∂̄ω) = ω`. Equivalently the area integral
`∫ (∂̄ω)(ζ)/(ζ - z) dA(ζ) = -π · ω(z)`. -/
theorem cauchyTransform_dzbar (hω : ContDiff ℝ 1 ω) (hωc : HasCompactSupport ω) (z : ℂ) :
    cauchyTransform (fun ζ => dzbar ω ζ) z = ω z := by
  -- It suffices to prove the area integral identity `∫ ζ, (∂̄ω)(ζ)/(ζ - z) = -π · ω z`.
  rw [cauchyTransform]
  -- Reduce to the case `z = 0` by translating the integral.
  set g : ℂ → ℂ := fun ξ => ω (z + ξ) with hg_def
  have hgC : ContDiff ℝ 1 g := hω.comp (contDiff_const.add contDiff_id)
  have hgc : HasCompactSupport g := by
    have h := hωc.comp_homeomorph (Homeomorph.addLeft z)
    simpa [Function.comp_def, hg_def] using h
  -- Translation identity for `∂̄`.
  have hdzbar : ∀ ξ : ℂ, dzbar ω (z + ξ) = dzbar g ξ := by
    intro ξ
    have hωd : DifferentiableAt ℝ ω (z + ξ) := hω.differentiable one_ne_zero _
    have htransd : DifferentiableAt ℝ (fun ξ : ℂ => z + ξ) ξ :=
      (differentiableAt_const z).add differentiableAt_id
    have hfd : fderiv ℝ g ξ = fderiv ℝ ω (z + ξ) := by
      have hcomp : g = ω ∘ (fun ξ : ℂ => z + ξ) := rfl
      rw [hcomp, fderiv_comp ξ hωd htransd]
      have ht : fderiv ℝ (fun ξ : ℂ => z + ξ) ξ = ContinuousLinearMap.id ℝ ℂ := by
        rw [fderiv_const_add (𝕜 := ℝ) (f := fun ξ : ℂ => ξ), fderiv_fun_id]
      rw [ht, ContinuousLinearMap.comp_id]
    rw [dzbar, dzbar, hfd]
  -- The translated integral.
  have hshift : (∫ ζ, dzbar ω ζ / (ζ - z)) = ∫ ξ, dzbar g ξ / ξ := by
    rw [← integral_add_left_eq_self (fun ζ => dzbar ω ζ / (ζ - z)) z]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [add_sub_cancel_left, hdzbar ξ]
  -- The core z = 0 identity.
  have hcore : (∫ ξ, dzbar g ξ / ξ) = -(π : ℂ) * g 0 := by
    -- Make `g` opaque so that the elaborator does not unfold the translation.
    clear_value g
    -- Continuity and compact support of the relevant derivatives of `g`.
    have hfderiv_cont : Continuous (fun ζ => fderiv ℝ g ζ) := hgC.continuous_fderiv one_ne_zero
    have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ g ζ) := hgc.fderiv (𝕜 := ℝ)
    have hgdiff : ∀ ζ : ℂ, DifferentiableAt ℝ g ζ := fun ζ => hgC.differentiable one_ne_zero ζ
    -- The map `dzbar g` is continuous with compact support.
    have hdzbar_cont : Continuous (fun ζ => dzbar g ζ) := by
      unfold dzbar
      fun_prop
    have hdzbar_cs : HasCompactSupport (fun ζ => dzbar g ζ) := by
      have : (fun ζ => dzbar g ζ)
          = (fun D : ℂ →L[ℝ] ℂ => (1/2 : ℂ) * (D 1 + I * D I)) ∘ (fun ζ => fderiv ℝ g ζ) := by
        funext ζ; rfl
      rw [this]
      refine hfderiv_cs.comp_left ?_
      simp
    -- Global bound on `‖fderiv ℝ g ζ‖`.
    obtain ⟨M, hM⟩ : ∃ M, ∀ ζ : ℂ, ‖fderiv ℝ g ζ‖ ≤ M :=
      hfderiv_cs.exists_bound_of_continuous hfderiv_cont
    -- A radius enclosing the support of `g`.
    obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport g ⊆ Metric.closedBall 0 R :=
      (hgc.isCompact.isBounded).subset_closedBall 0
    -- Outside the support radius, `g`, `fderiv ℝ g` and `dzbar g` all vanish.
    have hg_van : ∀ ζ : ℂ, R < ‖ζ‖ → g ζ = 0 := by
      intro ζ hζ
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith
    have hfderiv_van : ∀ ζ : ℂ, R < ‖ζ‖ → fderiv ℝ g ζ = 0 := by
      intro ζ hζ
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := (tsupport_fderiv_subset ℝ) hmem
      have := hR this
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith
    have hdzbar_van : ∀ ζ : ℂ, R < ‖ζ‖ → dzbar g ζ = 0 := by
      intro ζ hζ
      rw [dzbar, hfderiv_van ζ hζ]
      simp
    -- The polar coordinate map and its key abbreviations.
    set P : ℝ × ℝ → ℂ := fun p => (Complex.polarCoord).symm p with hP_def
    -- `e θ = cos θ + sin θ I`, the unit complex number.
    set e : ℝ → ℂ := fun θ => (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I with he_def
    -- Reformulation of `P`.
    have hP_eq : ∀ p : ℝ × ℝ, P p = (p.1 : ℂ) * e p.2 := by
      intro p
      simp only [hP_def, he_def, Complex.polarCoord_symm_apply]
    -- `e θ` is a unit complex number.
    have he_normSq : ∀ θ : ℝ, (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
      intro θ
      have : (Real.cos θ) ^ 2 + (Real.sin θ) ^ 2 = 1 := by
        rw [add_comm]; exact Real.sin_sq_add_cos_sq θ
      exact_mod_cast this
    have he_mul_conj : ∀ θ : ℝ, e θ * (starRingEnd ℂ) (e θ) = 1 := by
      intro θ
      simp only [he_def, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring_nf
      rw [Complex.I_sq]
      ring_nf
      have := he_normSq θ
      linear_combination this
    have he_ne : ∀ θ : ℝ, e θ ≠ 0 := by
      intro θ h
      have := he_mul_conj θ
      rw [h] at this
      simp at this
    -- The target set.
    set T : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π with hT_def
    have hT_meas : MeasurableSet T := by
      rw [hT_def]
      exact measurableSet_Ioi.prod measurableSet_Ioo
    -- Step 1: rewrite the integral in polar coordinates.
    have hpolar : (∫ ξ, dzbar g ξ / ξ)
        = ∫ p in T, dzbar g (P p) * (starRingEnd ℂ) (e p.2) := by
      rw [← Complex.integral_comp_polarCoord_symm (fun ζ => dzbar g ζ / ζ)]
      have htgt : polarCoord.target = T := polarCoord_target
      rw [htgt]
      apply setIntegral_congr_fun hT_meas
      intro p hp
      obtain ⟨hr, hθ⟩ := hp
      simp only [Set.mem_Ioi] at hr
      have hrne : (p.1 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
      change p.1 • (dzbar g (P p) / P p) = dzbar g (P p) * (starRingEnd ℂ) (e p.2)
      rw [hP_eq p, Complex.real_smul]
      have heinv : (e p.2)⁻¹ = (starRingEnd ℂ) (e p.2) :=
        inv_eq_of_mul_eq_one_right (he_mul_conj p.2)
      rw [div_eq_mul_inv, mul_inv, heinv]
      field_simp
    -- The two pieces of the integrand: a radial-derivative part `Arad` and an
    -- angular-derivative part `Bp`.
    set Arad : ℝ × ℝ → ℂ := fun p => (1/2 : ℂ) * (fderiv ℝ g (P p)) (e p.2) with hArad_def
    set Bp : ℝ × ℝ → ℂ := fun p => (1/2 : ℂ) * I * (fderiv ℝ g (P p)) (I * e p.2) with hBp_def
    -- Pointwise: the polar integrand splits as `Arad + Bp`.
    have hsplit : ∀ p : ℝ × ℝ,
        dzbar g (P p) * (starRingEnd ℂ) (e p.2) = Arad p + Bp p := by
      intro p
      set D := fderiv ℝ g (P p) with hD_def
      have hDe : D (e p.2) = (Real.cos p.2 : ℂ) * D 1 + (Real.sin p.2 : ℂ) * D I := by
        have hee : e p.2 = (Real.cos p.2 : ℝ) • (1 : ℂ) + (Real.sin p.2 : ℝ) • I := by
          rw [he_def]; simp [Complex.real_smul]
        rw [hee, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
      have hDIe : D (I * e p.2) = -(Real.sin p.2 : ℂ) * D 1 + (Real.cos p.2 : ℂ) * D I := by
        have hIe : I * e p.2 = (-(Real.sin p.2) : ℝ) • (1 : ℂ) + (Real.cos p.2 : ℝ) • I := by
          rw [he_def, Complex.real_smul, Complex.real_smul, Complex.ofReal_neg]
          linear_combination ((Real.sin p.2 : ℂ)) * Complex.I_mul_I
        rw [hIe, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul,
          Complex.ofReal_neg]
      have hconj : (starRingEnd ℂ) (e p.2) = (Real.cos p.2 : ℂ) - (Real.sin p.2 : ℂ) * I := by
        rw [he_def]
        simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
        ring
      have hdz : dzbar g (P p) = (1/2 : ℂ) * (D 1 + I * D I) := by
        rw [dzbar, ← hD_def]
      rw [hdz, hconj]
      simp only [hArad_def, hBp_def, ← hD_def, hDe, hDIe]
      have hI2 : (I : ℂ) * I = -1 := Complex.I_mul_I
      linear_combination (-(1/2 : ℂ) * (Real.sin p.2 : ℂ) * D I) * hI2
    -- `e θ` is a unit vector and `‖P p‖ = |p.1|`.
    have he_norm : ∀ θ : ℝ, ‖e θ‖ = 1 := by
      intro θ
      have h := he_mul_conj θ
      have : ‖e θ * (starRingEnd ℂ) (e θ)‖ = ‖e θ‖ ^ 2 := by
        rw [norm_mul, Complex.norm_conj]; ring
      rw [h, norm_one] at this
      nlinarith [norm_nonneg (e θ), this]
    have he_cont : Continuous e := by
      rw [he_def]; fun_prop
    have hP_norm : ∀ p : ℝ × ℝ, ‖P p‖ = |p.1| := by
      intro p
      rw [hP_eq, norm_mul, he_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    -- Continuity of `P`.
    have hP_cont : Continuous P := by
      have : P = fun p : ℝ × ℝ => (p.1 : ℂ) * e p.2 := funext hP_eq
      rw [this]
      exact (Complex.continuous_ofReal.comp continuous_fst).mul (he_cont.comp continuous_snd)
    -- A reusable integrability criterion on the polar target `T`.
    have hintT : ∀ (φ : ℝ × ℝ → ℂ) (Mφ : ℝ), Continuous φ → (∀ p, ‖φ p‖ ≤ Mφ) →
        (∀ p : ℝ × ℝ, R < |p.1| → φ p = 0) → IntegrableOn φ T := by
      intro φ Mφ hφc hφb hφsupp
      set S : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) (R + 1) ×ˢ Set.Ioo (-π) π with hS_def
      have hSmeas : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
      have hSfin : volume S ≠ ⊤ := by
        rw [hS_def, Measure.volume_eq_prod, Measure.prod_prod]
        exact (ENNReal.mul_lt_top measure_Ioo_lt_top measure_Ioo_lt_top).ne
      have hintS : IntegrableOn φ S := by
        apply Measure.integrableOn_of_bounded hSfin hφc.aestronglyMeasurable
          (M := Mφ)
        exact ae_of_all _ (fun p => hφb p)
      apply hintS.of_forall_sdiff_eq_zero hT_meas
      intro p hp
      obtain ⟨hpT, hpnS⟩ := hp
      apply hφsupp
      obtain ⟨hr, hθ⟩ := hpT
      simp only [Set.mem_Ioi] at hr
      rw [abs_of_pos hr]
      by_contra hle
      have hle' : p.1 ≤ R := not_lt.mp hle
      apply hpnS
      exact ⟨⟨hr, by linarith⟩, hθ⟩
    -- Continuity of `fun p => fderiv ℝ g (P p)`.
    have hfP_cont : Continuous (fun p : ℝ × ℝ => fderiv ℝ g (P p)) := hfderiv_cont.comp hP_cont
    -- Continuity of `Arad` and `Bp`.
    have hArad_cont : Continuous Arad := by
      rw [hArad_def]
      exact continuous_const.mul (hfP_cont.clm_apply (he_cont.comp continuous_snd))
    have hBp_cont : Continuous Bp := by
      rw [hBp_def]
      refine continuous_const.mul (hfP_cont.clm_apply ?_)
      exact continuous_const.mul (he_cont.comp continuous_snd)
    -- Bounds.
    have hArad_bound : ∀ p, ‖Arad p‖ ≤ M / 2 := by
      intro p
      rw [hArad_def]
      simp only [norm_mul]
      have h1 : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
      have h2 : ‖(fderiv ℝ g (P p)) (e p.2)‖ ≤ ‖fderiv ℝ g (P p)‖ * ‖e p.2‖ :=
        ContinuousLinearMap.le_opNorm _ _
      rw [he_norm, mul_one] at h2
      rw [h1]
      have := hM (P p)
      nlinarith [norm_nonneg (fderiv ℝ g (P p))]
    have hBp_bound : ∀ p, ‖Bp p‖ ≤ M / 2 := by
      intro p
      rw [hBp_def]
      simp only [norm_mul]
      have h1 : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
      have hI : ‖(I : ℂ)‖ = 1 := Complex.norm_I
      have h2 : ‖(fderiv ℝ g (P p)) (I * e p.2)‖ ≤ ‖fderiv ℝ g (P p)‖ * ‖I * e p.2‖ :=
        ContinuousLinearMap.le_opNorm _ _
      rw [norm_mul, hI, he_norm, mul_one, mul_one] at h2
      rw [h1, hI]
      have := hM (P p)
      nlinarith [norm_nonneg (fderiv ℝ g (P p))]
    -- Supports.
    have hArad_supp : ∀ p : ℝ × ℝ, R < |p.1| → Arad p = 0 := by
      intro p hp
      rw [hArad_def]
      have : fderiv ℝ g (P p) = 0 := hfderiv_van (P p) (by rw [hP_norm]; exact hp)
      simp [this]
    have hBp_supp : ∀ p : ℝ × ℝ, R < |p.1| → Bp p = 0 := by
      intro p hp
      rw [hBp_def]
      have : fderiv ℝ g (P p) = 0 := hfderiv_van (P p) (by rw [hP_norm]; exact hp)
      simp [this]
    -- Integrability of `Arad` and `Bp` on `T`.
    have hArad_int : IntegrableOn Arad T :=
      hintT Arad (M/2) hArad_cont hArad_bound hArad_supp
    have hBp_int : IntegrableOn Bp T :=
      hintT Bp (M/2) hBp_cont hBp_bound hBp_supp
    -- `HasDerivAt e (I * e θ) θ`.
    have he_deriv : ∀ θ : ℝ, HasDerivAt e (I * e θ) θ := by
      intro θ
      have hcos : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) (((-Real.sin θ : ℝ)) : ℂ) θ :=
        (Real.hasDerivAt_cos θ).ofReal_comp
      have hsin : HasDerivAt (fun t : ℝ => (Real.sin t : ℂ)) (((Real.cos θ : ℝ)) : ℂ) θ :=
        (Real.hasDerivAt_sin θ).ofReal_comp
      have hd : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ) + (Real.sin t : ℂ) * I)
          ((((-Real.sin θ : ℝ)) : ℂ) + (((Real.cos θ : ℝ)) : ℂ) * I) θ :=
        hcos.add (hsin.mul_const I)
      have hev : (((-Real.sin θ : ℝ)) : ℂ) + (((Real.cos θ : ℝ)) : ℂ) * I = I * e θ := by
        rw [he_def, Complex.ofReal_neg]
        linear_combination (-(Real.sin θ : ℂ)) * Complex.I_mul_I
      rw [he_def]
      rw [← hev]
      exact hd
    -- Radial derivative of `s ↦ g ((s:ℂ) * e θ)`.
    have hRad_deriv : ∀ (θ r : ℝ),
        HasDerivAt (fun s : ℝ => g ((s : ℂ) * e θ))
          ((fderiv ℝ g ((r : ℂ) * e θ)) (e θ)) r := by
      intro θ r
      have hinner : HasDerivAt (fun s : ℝ => (s : ℂ) * e θ) (e θ) r := by
        have := (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (e θ)
        simpa using this
      have hg' : HasFDerivAt g (fderiv ℝ g ((r : ℂ) * e θ)) ((r : ℂ) * e θ) :=
        (hgdiff _).hasFDerivAt
      exact hg'.comp_hasDerivAt r hinner
    -- Angular derivative of `t ↦ g ((r:ℂ) * e t)`.
    have hAng_deriv : ∀ (r θ : ℝ),
        HasDerivAt (fun t : ℝ => g ((r : ℂ) * e t))
          (r • ((fderiv ℝ g ((r : ℂ) * e θ)) (I * e θ))) θ := by
      intro r θ
      have hinner : HasDerivAt (fun t : ℝ => (r : ℂ) * e t) ((r : ℂ) * (I * e θ)) θ :=
        (he_deriv θ).const_mul (r : ℂ)
      have hg' : HasFDerivAt g (fderiv ℝ g ((r : ℂ) * e θ)) ((r : ℂ) * e θ) :=
        (hgdiff _).hasFDerivAt
      have hcomp := hg'.comp_hasDerivAt θ hinner
      have hrr : ((r : ℂ) * (I * e θ)) = r • (I * e θ) := by rw [Complex.real_smul]
      have hsm : (fderiv ℝ g ((r : ℂ) * e θ)) ((r : ℂ) * (I * e θ))
          = r • ((fderiv ℝ g ((r : ℂ) * e θ)) (I * e θ)) := by
        rw [hrr, map_smul]
      rwa [hsm] at hcomp
    -- The radial integral evaluates to `-π · g 0`.
    have hArad_eval : (∫ p in T, Arad p) = -(π : ℂ) * g 0 := by
      -- For each `θ`, the inner radial integral recovers `-½ g 0` by the FTC.
      have hinner_rad : ∀ θ : ℝ,
          (∫ r in Set.Ioi (0:ℝ), Arad (r, θ)) = -(1/2 : ℂ) * g 0 := by
        intro θ
        -- The radial function and its smoothness / compact support.
        have hRadCD : ContDiff ℝ 1 (fun s : ℝ => g ((s : ℂ) * e θ)) := by
          refine hgC.comp ?_
          have : ContDiff ℝ 1 (fun s : ℝ => (s : ℂ)) := Complex.ofRealCLM.contDiff
          exact this.mul contDiff_const
        have hRadCS : HasCompactSupport (fun s : ℝ => g ((s : ℂ) * e θ)) := by
          apply HasCompactSupport.intro (K := Set.Icc (-(|R| + 1)) (|R| + 1)) isCompact_Icc
          intro s hs
          rw [Set.mem_Icc, not_and_or] at hs
          apply hg_van
          rw [norm_mul, he_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
          rcases hs with h | h
          · rw [abs_of_neg (by nlinarith [abs_nonneg R] : s < 0)]
            nlinarith [abs_nonneg R, le_abs_self R]
          · rw [abs_of_pos (by nlinarith [abs_nonneg R] : (0:ℝ) < s)]
            nlinarith [abs_nonneg R, le_abs_self R]
        -- The inner integrand is `½ • (deriv of the radial function)`.
        have hint_eq : ∀ r : ℝ,
            Arad (r, θ) = (1/2 : ℂ) • deriv (fun s : ℝ => g ((s : ℂ) * e θ)) r := by
          intro r
          rw [hArad_def]
          simp only [hP_eq]
          rw [(hRad_deriv θ r).deriv, smul_eq_mul]
        rw [setIntegral_congr_fun measurableSet_Ioi (fun r _ => hint_eq r)]
        rw [integral_smul]
        rw [HasCompactSupport.integral_Ioi_deriv_eq hRadCD hRadCS 0]
        simp only [Complex.ofReal_zero, zero_mul]
        rw [smul_eq_mul]
        ring
      -- Fubini (`r` inner, `θ` outer) via the swap.
      have hArad_int' : IntegrableOn Arad (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π)
          (volume.prod volume) := by
        rw [← Measure.volume_eq_prod ℝ ℝ, ← hT_def]; exact hArad_int
      have hswapint : IntegrableOn (fun z : ℝ × ℝ => Arad z.swap)
          (Set.Ioo (-π) π ×ˢ Set.Ioi (0:ℝ)) (volume.prod volume) := by
        have h1 : Integrable Arad
            ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioo (-π) π))) := by
          rw [Measure.prod_restrict]; exact hArad_int'
        have h2 := h1.swap
        rw [IntegrableOn, ← Measure.prod_restrict]
        exact h2
      have hstep : (∫ p in T, Arad p)
          = ∫ θ in Set.Ioo (-π : ℝ) π, ∫ r in Set.Ioi (0:ℝ), Arad (r, θ) := by
        rw [hT_def,
          show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
        rw [← setIntegral_prod_swap (Set.Ioi (0:ℝ)) (Set.Ioo (-π) π) Arad]
        rw [setIntegral_prod _ hswapint]
        rfl
      rw [hstep]
      rw [setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hinner_rad θ)]
      rw [setIntegral_const,
        Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos] : (-π : ℝ) ≤ π)]
      have hsmul : (π - -π) • (-(1/2 : ℂ) * g 0) = ((π - -π : ℝ) : ℂ) * (-(1/2 : ℂ) * g 0) := by
        simp [Complex.real_smul]
      refine hsmul.trans ?_
      push_cast
      ring
    -- The angular integral vanishes.
    have hBp_eval : (∫ p in T, Bp p) = 0 := by
      -- For each `r > 0`, the inner angular integral is the difference of `g` at the two
      -- (identical) endpoints `±π`, hence `0`.
      have hπle : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
      have hinner_zero : ∀ r : ℝ, 0 < r → (∫ θ in Set.Ioo (-π : ℝ) π, Bp (r, θ)) = 0 := by
        intro r hr
        have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
        -- The angular curve and the continuity of its derivative.
        have hAng_cont : Continuous (fun t : ℝ => g ((r : ℂ) * e t)) :=
          hgC.continuous.comp (continuous_const.mul he_cont)
        have hAng_deriv_cont :
            Continuous (fun θ : ℝ => r • ((fderiv ℝ g ((r : ℂ) * e θ)) (I * e θ))) := by
          have h1 : Continuous (fun θ : ℝ => fderiv ℝ g ((r : ℂ) * e θ)) :=
            hfderiv_cont.comp (continuous_const.mul he_cont)
          have h2 : Continuous (fun θ : ℝ => I * e θ) := continuous_const.mul he_cont
          exact (h1.clm_apply h2).const_smul (r : ℝ)
        -- Rewrite the integrand using the angular derivative.
        have hBp_eq : ∀ θ : ℝ,
            Bp (r, θ) = ((1/2 : ℂ) * I * (r : ℂ)⁻¹)
              • (r • ((fderiv ℝ g ((r : ℂ) * e θ)) (I * e θ))) := by
          intro θ
          rw [hBp_def]
          simp only [hP_eq]
          rw [Complex.real_smul, smul_eq_mul]
          field_simp
        rw [setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hBp_eq θ)]
        rw [integral_smul]
        rw [show (0 : ℂ) = ((1/2 : ℂ) * I * (r : ℂ)⁻¹) • (0 : ℂ) by simp]
        congr 1
        -- The integral of the angular derivative over `(-π, π)` vanishes.
        rw [← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le hπle]
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun θ _ => hAng_deriv r θ)
          (hAng_deriv_cont.intervalIntegrable _ _)]
        -- endpoints coincide
        have hπ : e π = (-1 : ℂ) := by
          rw [he_def]; simp [Real.cos_pi, Real.sin_pi]
        have hmπ : e (-π) = (-1 : ℂ) := by
          rw [he_def]; simp [Real.cos_pi, Real.sin_pi]
        rw [hπ, hmπ]
        simp
      -- Fubini: integrate `θ` first, getting `0` for each `r`.
      have hBp_int' : IntegrableOn Bp (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π)
          (volume.prod volume) := by
        rw [← Measure.volume_eq_prod ℝ ℝ]
        rw [← hT_def]; exact hBp_int
      have hstep : (∫ p in T, Bp p) = ∫ r in Set.Ioi (0:ℝ), ∫ θ in Set.Ioo (-π) π, Bp (r, θ) := by
        rw [hT_def]
        rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
        exact setIntegral_prod Bp hBp_int'
      rw [hstep]
      rw [setIntegral_congr_fun measurableSet_Ioi
        (fun r hr => hinner_zero r hr)]
      simp
    -- Combine.
    rw [hpolar]
    rw [setIntegral_congr_fun hT_meas (fun p _ => hsplit p)]
    rw [integral_add hArad_int hBp_int, hArad_eval, hBp_eval, add_zero]
  rw [hshift, hcore]
  have hg0 : g 0 = ω z := by simp [hg_def]
  rw [hg0]
  have hπ : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  field_simp

/-- **`∂̄ ∘ P = P ∘ ∂̄`.** Differentiating the Cauchy transform passes `∂̄` onto the
integrand (the Cauchy transform is a convolution with a locally integrable
kernel, and `ω` is `C¹` with compact support). -/
theorem dzbar_cauchyTransform_eq (hω : ContDiff ℝ 1 ω) (hωc : HasCompactSupport ω) (z : ℂ) :
    dzbar (cauchyTransform ω) z = cauchyTransform (fun ζ => dzbar ω ζ) z := by
  set L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ with hL
  set k : ℂ → ℂ := fun u => -u⁻¹ with hk
  -- Step A: the translated Cauchy kernel `-u⁻¹` is locally integrable on `ℂ`.
  have hk_loc : LocallyIntegrable k volume := by
    rw [hk]
    apply LocallyIntegrable.neg
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    apply MeasureTheory.IntegrableOn.mono_set _ hR
    rw [IntegrableOn]
    refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
      ← Complex.lintegral_comp_polarCoord_symm]
    set lhs : ℝ × ℝ → ENNReal := fun p =>
      ENNReal.ofReal p.1 •
        (Metric.closedBall (0 : ℂ) R).indicator (fun u : ℂ => ‖u⁻¹‖ₑ) (Complex.polarCoord.symm p)
      with hlhs
    set box : ℝ × ℝ → ENNReal :=
      (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π).indicator (fun _ => (1 : ENNReal)) with hbox
    have hbound : ∀ p ∈ polarCoord.target, lhs p ≤ box p := by
      intro p hp
      simp only [hlhs, hbox]
      rw [polarCoord_target, Set.mem_prod] at hp
      obtain ⟨hp1, hp2⟩ := hp
      simp only [Set.mem_Ioi] at hp1
      by_cases hmem : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R
      · rw [Set.indicator_of_mem hmem]
        have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
        have hsymm_ne : Complex.polarCoord.symm p ≠ 0 := by
          rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hp1
        rw [enorm_inv hsymm_ne]
        have henorm : ‖Complex.polarCoord.symm p‖ₑ = ENNReal.ofReal p.1 := by
          rw [← ofReal_norm, hnorm]
        rw [henorm, smul_eq_mul,
          ENNReal.mul_inv_cancel (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp1)
            ENNReal.ofReal_lt_top.ne]
        have hpR : p.1 ≤ R := by
          rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem
          exact hmem
        have hmem2 : p ∈ Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π :=
          Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hp1, hpR⟩, hp2⟩
        rw [Set.indicator_of_mem hmem2]
      · rw [Set.indicator_of_notMem hmem]
        simp
    have hmeas : Measurable box :=
      measurable_const.indicator (measurableSet_Ioc.prod measurableSet_Ioo)
    have hbox_meas : MeasurableSet (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π) :=
      measurableSet_Ioc.prod measurableSet_Ioo
    calc
      ∫⁻ p in polarCoord.target, lhs p
          ≤ ∫⁻ p in polarCoord.target, box p := setLIntegral_mono hmeas hbound
      _ ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
      _ = volume (Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π) := by
            rw [hbox, lintegral_indicator hbox_meas]; simp
      _ < ⊤ := by
            have hvol : (volume : Measure (ℝ × ℝ)) = volume.prod volume :=
              Measure.volume_eq_prod ℝ ℝ
            rw [hvol, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  -- Step B: the Cauchy transform is the convolution of `ω` with the kernel `k`.
  have hCT : cauchyTransform ω
      = fun w => (-(1 / (π : ℂ))) • (MeasureTheory.convolution ω k L volume) w := by
    funext w
    rw [cauchyTransform, MeasureTheory.convolution_def, smul_eq_mul]
    congr 1
    apply integral_congr_ae (ae_of_all _ fun ζ => ?_)
    rw [hL, ContinuousLinearMap.mul_apply']
    change ω ζ / (ζ - w) = ω ζ * -(w - ζ)⁻¹
    have hflip : -(w - ζ)⁻¹ = (ζ - w)⁻¹ := by rw [← neg_sub ζ w, inv_neg, neg_neg]
    rw [hflip, div_eq_mul_inv]
  -- Step C: differentiate the convolution, passing the derivative onto the smooth factor `ω`.
  have hfd0 : HasFDerivAt (MeasureTheory.convolution ω k L volume)
      (MeasureTheory.convolution (fderiv ℝ ω) k (ContinuousLinearMap.precompL ℂ L) volume z) z :=
    hωc.hasFDerivAt_convolution_left L hω hk_loc z
  set D₀ := MeasureTheory.convolution (fderiv ℝ ω) k (ContinuousLinearMap.precompL ℂ L) volume z
    with hD₀
  have hfderiv : fderiv ℝ (cauchyTransform ω) z = (-(1 / (π : ℂ))) • D₀ := by
    have hfd : HasFDerivAt (cauchyTransform ω) ((-(1 / (π : ℂ))) • D₀) z := by
      rw [hCT]; exact hfd0.const_smul (-(1 / (π : ℂ)))
    exact hfd.fderiv
  -- Step D: existence of the differentiated convolution and its directional values.
  have hex : ConvolutionExistsAt (fderiv ℝ ω) k z (ContinuousLinearMap.precompL ℂ L) volume :=
    ((hωc.fderiv ℝ).convolutionExists_left (ContinuousLinearMap.precompL ℂ L)
      (hω.continuous_fderiv one_ne_zero) hk_loc) z
  have hex_int :
      Integrable (fun t => (ContinuousLinearMap.precompL ℂ L) (fderiv ℝ ω t) (k (z - t))) volume :=
    hex
  set A : ℂ → ℂ := fun t => (fderiv ℝ ω t) 1 * k (z - t) with hA
  set B : ℂ → ℂ := fun t => (fderiv ℝ ω t) Complex.I * k (z - t) with hB
  have hA_int : Integrable A volume := by
    have h := hex_int.apply_continuousLinearMap (1 : ℂ)
    apply h.congr; apply ae_of_all _ fun t => ?_
    change (ContinuousLinearMap.precompL ℂ L) (fderiv ℝ ω t) (k (z - t)) 1 = A t
    rw [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.mul_apply']
  have hB_int : Integrable B volume := by
    have h := hex_int.apply_continuousLinearMap Complex.I
    apply h.congr; apply ae_of_all _ fun t => ?_
    change (ContinuousLinearMap.precompL ℂ L) (fderiv ℝ ω t) (k (z - t)) Complex.I = B t
    rw [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.mul_apply']
  have hD₀_eval : ∀ v : ℂ, D₀ v = ∫ t, ((fderiv ℝ ω t) v) * (k (z - t)) ∂volume := by
    intro v
    rw [hD₀, MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply hex_int]
    apply integral_congr_ae (ae_of_all _ fun t => ?_)
    rw [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.mul_apply']
  have hD₀1 : D₀ 1 = ∫ t, A t := hD₀_eval 1
  have hD₀I : D₀ Complex.I = ∫ t, B t := hD₀_eval Complex.I
  -- The Cauchy transform of `∂̄ω`, expressed through the same `A`, `B` integrals.
  have hRHS : cauchyTransform (fun ζ => dzbar ω ζ) z
      = (-(1 / (π : ℂ))) * ((1 / 2) * ((∫ t, A t) + Complex.I * (∫ t, B t))) := by
    rw [cauchyTransform]
    congr 1
    have hker : ∀ t : ℂ, (dzbar ω t) / (t - z) = (1 / 2 : ℂ) * (A t + Complex.I * B t) := by
      intro t
      rw [dzbar]
      have hk_eq : (t - z)⁻¹ = k (z - t) := by
        rw [hk]; change (t - z)⁻¹ = -(z - t)⁻¹
        rw [← neg_sub t z, inv_neg, neg_neg]
      rw [div_eq_mul_inv, hk_eq, hA, hB]; ring
    rw [integral_congr_ae (ae_of_all _ hker)]
    have h1 : ∫ (a : ℂ), (1 : ℂ) / 2 * (A a + Complex.I * B a)
        = (1 : ℂ) / 2 * ∫ a, (A a + Complex.I * B a) :=
      MeasureTheory.integral_const_mul ((1 : ℂ) / 2) _
    rw [h1]; congr 1
    have h2 : ∫ a, (A a + Complex.I * B a) = (∫ a, A a) + ∫ a, Complex.I * B a :=
      integral_add hA_int (hB_int.const_mul Complex.I)
    rw [h2]; congr 1
    exact MeasureTheory.integral_const_mul Complex.I B
  -- Step E: assemble the Wirtinger derivative of `Pω` from the directional values.
  rw [hRHS, dzbar, hfderiv]
  rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  rw [hD₀1, hD₀I]
  ring

/-- **The Cauchy transform solves `∂̄`.** For a `C¹` function of compact support,
`∂̄(Pω) = ω` — the composition of `dzbar_cauchyTransform_eq` (`∂̄P = P∂̄`) and
`cauchyTransform_dzbar` (Cauchy–Pompeiu, `P∂̄ω = ω`). -/
theorem dzbar_cauchyTransform (hω : ContDiff ℝ 1 ω) (hωc : HasCompactSupport ω) (z : ℂ) :
    dzbar (cauchyTransform ω) z = ω z :=
  (dzbar_cauchyTransform_eq hω hωc z).trans (cauchyTransform_dzbar hω hωc z)

end NoWanderingDomains
