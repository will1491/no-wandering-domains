/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# `Lᵖ`–`Lᵖ'` duality (lower bound)

The `Lᵖ` norm of a complex-valued function is controlled by the supremum of the
bilinear pairing `∫ h·g` over the unit ball of the conjugate space `Lᵖ'`:

`‖h‖_p ≤ ⨆ {g : ‖g‖_{p'} ≤ 1}, ‖∫ h·g‖`.

This is the duality direction used to obtain `Lᵖ` boundedness of the Beurling
transform for `p > 2` from its boundedness for the conjugate exponent `p' < 2`
(the Beurling kernel is symmetric, so the transpose of the Beurling transform is
itself). Mathlib does not package this `Lᵖ` Riesz-duality lower bound, so we
prove it here via the explicit extremizer `g₀ = conj h · ‖h‖^{p-2} / ‖h‖_p^{p-1}`,
which lies in the unit ball of `Lᵖ'` and pairs with `h` to give exactly `‖h‖_p`.
-/

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace NoWanderingDomains

/-- **`Lᵖ` duality (lower bound).** For `1 < p < ∞` with conjugate exponent `p'`,
the `Lᵖ` norm is bounded by the supremum of the bilinear pairing `∫ h·g` over the
unit ball of `Lᵖ'`. The extremizer is `g₀ = conj h · ‖h‖^{p-2} / ‖h‖_p^{p-1}`,
which lies in the unit ball of `Lᵖ'` and pairs with `h` to give exactly `‖h‖_p`. -/
theorem eLpNorm_le_iSup_integral_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p p' : ℝ≥0∞} (hp1 : 1 < p) (hp_top : p ≠ ⊤) [hpp' : p.HolderConjugate p']
    {h : α → ℂ} (hh : MemLp h p μ) :
    eLpNorm h p μ ≤ ⨆ (g : α → ℂ) (_ : MemLp g p' μ) (_ : eLpNorm g p' μ ≤ 1),
      ‖∫ x, h x * g x ∂μ‖ₑ := by
  -- Basic facts about the exponents.
  have hp'_top : p' ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p' p).mpr hp1).ne
  have hp0 : p ≠ 0 := (ENNReal.HolderConjugate.pos p p').ne'
  have hp'0 : p' ≠ 0 := (ENNReal.HolderConjugate.pos p' p).ne'
  set q := p.toReal with hq_def
  set q' := p'.toReal with hq'_def
  have h1q : 1 < q := by
    rw [hq_def, show (1 : ℝ) = (1 : ℝ≥0∞).toReal from by simp]
    exact (ENNReal.toReal_lt_toReal (by simp) hp_top).mpr hp1
  have h1q' : 1 < q' := by
    rw [hq'_def, show (1 : ℝ) = (1 : ℝ≥0∞).toReal from by simp]
    exact (ENNReal.toReal_lt_toReal (by simp) hp'_top).mpr
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p').mp (lt_top_iff_ne_top.mpr hp_top))
  have hq0 : (0 : ℝ) < q := lt_trans one_pos h1q
  have hq'0 : (0 : ℝ) < q' := lt_trans one_pos h1q'
  have hinv : q⁻¹ + q'⁻¹ = 1 := by
    have h := ENNReal.HolderConjugate.inv_add_inv_eq_one p p'
    have heq : (p⁻¹ + p'⁻¹).toReal = (1 : ℝ≥0∞).toReal := by rw [h]
    rw [ENNReal.toReal_add (by simp [hp0]) (by simp [hp'0]), ENNReal.toReal_one,
        ENNReal.toReal_inv, ENNReal.toReal_inv] at heq
    exact heq
  -- The key exponent identity `(q-1) * q' = q`.
  have hkey : (q - 1) * q' = q := by
    have hh : q'⁻¹ = 1 - q⁻¹ := by linarith [hinv]
    field_simp at hh ⊢
    nlinarith [hh, hq0, hq'0]
  -- The `Lᵖ` norm as a real number `M`.
  set M := (eLpNorm h p μ).toReal with hM_def
  have hM_nonneg : 0 ≤ M := ENNReal.toReal_nonneg
  have heLp_M : eLpNorm h p μ = ENNReal.ofReal M :=
    (ENNReal.ofReal_toReal hh.eLpNorm_ne_top).symm
  -- The lintegral of `‖h‖ₑ ^ q` is `(eLpNorm h p μ) ^ q = ofReal (M ^ q)`.
  have hlint_eq : (∫⁻ x, ‖h x‖ₑ ^ q ∂μ) = ENNReal.ofReal (M ^ q) := by
    rw [show (∫⁻ x, ‖h x‖ₑ ^ q ∂μ) = (eLpNorm h p μ) ^ q from by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top, one_div,
            ENNReal.rpow_inv_rpow hq0.ne'],
      heLp_M, ENNReal.ofReal_rpow_of_nonneg hM_nonneg hq0.le]
  -- Measurability of `h`.
  have hh_aesm : AEStronglyMeasurable h μ := hh.1
  -- Case split on whether `M = 0`.
  rcases eq_or_lt_of_le hM_nonneg with hM0 | hMpos
  · -- `M = 0`: the `Lᵖ` norm is `0`, dominated by the nonnegative supremum.
    rw [heLp_M, ← hM0]
    simp
  · -- `0 < M`: build the extremizer.
    -- The extremizer `g₀ = conj h · ‖h‖^{q-2} / M^{q-1}`.
    set g₀ : α → ℂ := fun x =>
      conj (h x) * ((‖h x‖ ^ (q - 2) : ℝ) : ℂ) / ((M ^ (q - 1) : ℝ) : ℂ) with hg₀_def
    -- Pointwise pairing identity.
    have hpair : ∀ x, h x * g₀ x = (((‖h x‖ ^ q : ℝ) / (M ^ (q - 1) : ℝ)) : ℂ) := by
      intro x
      simp only [hg₀_def]
      rcases eq_or_ne (‖h x‖) 0 with hz | hz
      · have hz0 : h x = 0 := by rwa [norm_eq_zero] at hz
        rw [hz0]
        simp only [map_zero, zero_mul, norm_zero]
        rw [Real.zero_rpow hq0.ne']
        push_cast; ring
      · have hz0 : (0 : ℝ) < ‖h x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
        have key : h x * conj (h x) = ((‖h x‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have hpow : (‖h x‖ ^ 2 : ℝ) * (‖h x‖ ^ (q - 2) : ℝ) = (‖h x‖ ^ q : ℝ) := by
          rw [← Real.rpow_natCast (‖h x‖) 2, ← Real.rpow_add hz0]; norm_num
        have lhs_eq : h x * (conj (h x) * ((‖h x‖ ^ (q - 2) : ℝ) : ℂ) / ((M ^ (q - 1) : ℝ) : ℂ))
            = (h x * conj (h x)) * (((‖h x‖ ^ (q - 2) : ℝ)) : ℂ) / ((M ^ (q - 1) : ℝ) : ℂ) := by
          ring
        rw [lhs_eq, key, ← Complex.ofReal_mul, hpow]
    -- Norm of the extremizer.
    have hg₀_norm : ∀ x, ‖g₀ x‖ = (‖h x‖ ^ (q - 1) : ℝ) / (M ^ (q - 1) : ℝ) := by
      intro x
      simp only [hg₀_def]
      rcases eq_or_ne (‖h x‖) 0 with hz | hz
      · have hz0 : h x = 0 := by rwa [norm_eq_zero] at hz
        rw [hz0]
        simp only [map_zero, zero_mul, norm_zero, zero_div]
        rw [Real.zero_rpow (by linarith), zero_div]
      · have hz0 : (0 : ℝ) < ‖h x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
        rw [norm_div, norm_mul, RCLike.norm_conj,
            Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
            Real.norm_of_nonneg (Real.rpow_nonneg hMpos.le _),
            show (q - 1) = (q - 2) + 1 from by ring, Real.rpow_add hz0, Real.rpow_one]
        ring
    -- Measurability of the extremizer.
    have hg₀_aesm : AEStronglyMeasurable g₀ μ := by
      have h1 : AEStronglyMeasurable (fun x => conj (h x)) μ :=
        Complex.continuous_conj.comp_aestronglyMeasurable hh_aesm
      have h2 : AEStronglyMeasurable (fun x => ((‖h x‖ ^ (q - 2) : ℝ) : ℂ)) μ :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable
          ((hh_aesm.norm.aemeasurable.pow_const _).aestronglyMeasurable)
      simp only [hg₀_def]
      fun_prop
    -- The `Lᵖ'` norm of `g₀` is `1`.
    have hg₀_eLp : eLpNorm g₀ p' μ ≤ 1 := by
      have hpoint : ∀ x, ‖g₀ x‖ₑ ^ q' = ‖h x‖ₑ ^ q / ENNReal.ofReal (M ^ q) := by
        intro x
        rw [← ofReal_norm (g₀ x), hg₀_norm x,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hq'0.le,
          Real.div_rpow (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hMpos.le _),
          ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul hMpos.le, hkey,
          ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hMpos _),
          ← ofReal_norm (h x),
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le]
      have hlint_g₀ : (∫⁻ x, ‖g₀ x‖ₑ ^ q' ∂μ) = 1 := by
        simp_rw [hpoint]
        rw [show (fun x => ‖h x‖ₑ ^ q / ENNReal.ofReal (M ^ q))
              = (fun x => ‖h x‖ₑ ^ q * (ENNReal.ofReal (M ^ q))⁻¹) from by
            ext x; rw [div_eq_mul_inv],
          lintegral_mul_const'' _ ((hh_aesm.enorm.pow_const q)),
          ← div_eq_mul_inv, hlint_eq,
          ENNReal.div_self (by
            simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
            exact Real.rpow_pos_of_pos hMpos _)
            ENNReal.ofReal_ne_top]
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp'0 hp'_top, one_div, ← hq'_def, hlint_g₀,
        ENNReal.one_rpow]
    -- `g₀` is in `Lᵖ'`.
    have hg₀_memLp : MemLp g₀ p' μ := ⟨hg₀_aesm, lt_of_le_of_lt hg₀_eLp (by norm_num)⟩
    -- The pairing integral equals `M`.
    have hint_eq : ∫ x, h x * g₀ x ∂μ = (M : ℂ) := by
      have hpair' : ∀ x, h x * g₀ x = (((‖h x‖ ^ q / M ^ (q - 1)) : ℝ) : ℂ) := by
        intro x; rw [hpair x, Complex.ofReal_div]
      simp_rw [hpair']
      rw [integral_complex_ofReal, integral_div]
      -- `∫ ‖h‖^q = M^q`.
      have hint_rpow : ∫ x, (‖h x‖ ^ q) ∂μ = M ^ q := by
        have hint : Integrable (fun x => ‖h x‖ ^ q) μ := hh.integrable_norm_rpow hp0 hp_top
        have hnn : 0 ≤ᶠ[ae μ] fun x => ‖h x‖ ^ q :=
          Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) _)
        rw [integral_eq_lintegral_of_nonneg_ae hnn hint.aestronglyMeasurable]
        have hofR : (fun x => ENNReal.ofReal (‖h x‖ ^ q)) = (fun x => ‖h x‖ₑ ^ q) := by
          ext x
          rw [← ofReal_norm, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le]
        rw [hofR, hlint_eq, ENNReal.toReal_ofReal (by positivity)]
      rw [hint_rpow, ← Real.rpow_sub hMpos, show q - (q - 1) = 1 from by ring, Real.rpow_one]
    -- Conclude: `eLpNorm h p μ = ‖∫ h·g₀‖ₑ ≤ ⨆ …`.
    have hfinal : eLpNorm h p μ = ‖∫ x, h x * g₀ x ∂μ‖ₑ := by
      rw [hint_eq, heLp_M, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hM_nonneg]
    rw [hfinal]
    exact le_iSup₂_of_le g₀ hg₀_memLp (le_iSup_of_le hg₀_eLp (le_refl _))

end NoWanderingDomains
