/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
-- Provides the `MeasureSpace ℂ` instance (`instMeasureSpaceComplex`) needed for `∫⁻ u : ℂ ∂volume`.
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-!
# Annular integral of the inverse-square weight

The elementary area-integral computation underlying the `Lᵖ` mapping properties of
the **Beurling kernel** `K(z, ζ) = (z - ζ)⁻²`: over an annulus `{a ≤ ‖u‖ < b}` the
integral of the squared modulus `‖u ^ (-2)‖ = ‖u‖⁻²` against the planar Lebesgue
measure is `2π · log(b/a)`.

In polar coordinates the area element is `ρ dρ dθ`, so the integrand
`‖u‖⁻² dA = ρ⁻² · ρ dρ dθ = ρ⁻¹ dρ dθ` is constant in the angle `θ ∈ (-π, π)`
(contributing the factor `2π`) and reduces to the radial integral
`∫_a^b ρ⁻¹ dρ = log(b/a)` (`radial_lintegral_inv`). The logarithmic growth in
`b/a` is exactly the borderline (non-)integrability of the Beurling kernel: its
`L¹` mass over `{‖u‖ ≥ r}` diverges, but every higher power `‖u‖^{-2q}` with
`q > 1` is integrable.

`Analysis/SingularIntegral/Beurling/` consumes `annulus_lintegral` (and its
`Lᵖ` variants built from the same polar reduction) to show the truncated Beurling
kernel section `1_{‖·‖ ≥ r}(·) · ‖·‖⁻²` lies in `Lᵖ'`, so the singular integral is
well-defined against `Lᵖ` data, and in the Cotlar–Stein / Schur kernel bounds.
-/

open MeasureTheory Complex Set
open scoped Real ENNReal

namespace NoWanderingDomains.SingularIntegral

/-- **Radial integral of `ρ⁻¹`.** For `0 < a < b`,
`∫_{[a, b)} ρ⁻¹ dρ = log(b/a)` (as an `ℝ≥0∞`-integral of `ENNReal.ofReal ρ⁻¹`).
This is the radial part of `annulus_lintegral`, where the polar area element
`ρ dρ dθ` cancels one power of `ρ` from `‖u‖⁻²`. The proof bridges the
`ℝ≥0∞`-integral to the Bochner integral of `ρ⁻¹` (`ofReal_integral_eq_lintegral_ofReal`),
which equals `log(b/a)` by `integral_inv` since `0 ∉ [a, b]`. -/
theorem radial_lintegral_inv (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∫⁻ ρ in Set.Ico a b, ENNReal.ofReal ρ⁻¹ ∂volume = ENNReal.ofReal (Real.log (b / a)) := by
  have hb : 0 < b := ha.trans hab
  -- `ρ⁻¹` is continuous on `[[a, b]]` since `0 ∉ [[a,b]]`.
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab.le, Set.mem_Icc, not_and_or]
    exact Or.inl (not_le.mpr ha)
  have hcont : ContinuousOn (fun ρ : ℝ => ρ⁻¹) (Set.uIcc a b) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro x hx
    rintro rfl
    exact h0 hx
  have hii : IntervalIntegrable (fun ρ : ℝ => ρ⁻¹) volume a b := hcont.intervalIntegrable
  -- IntegrableOn over Ico a b
  have hIco : IntegrableOn (fun ρ : ℝ => ρ⁻¹) (Set.Ico a b) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ico_of_le hab.le]
    exact hii
  -- bridge lintegral ↔ ofReal of integral
  rw [← ofReal_integral_eq_lintegral_ofReal hIco]
  · -- now show ∫ ρ in Ico a b, ρ⁻¹ = log (b/a)
    congr 1
    rw [MeasureTheory.integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
    exact integral_inv h0
  · -- 0 ≤ᵐ ρ⁻¹
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ico] with ρ hρ
    rw [Set.mem_Ico] at hρ
    exact inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le ha hρ.1))

set_option maxHeartbeats 400000 in
-- The `annulus_lintegral` polar-coordinate reduction elaborates a long
-- `ENNReal`/`Real` rewrite chain in one theorem, exceeding the default budget.
/-- **Annular integral of the inverse-square weight.** For `0 < a < b`,
`∫_{a ≤ ‖u‖ < b} ‖u ^ (-2)‖ₑ dA = 2π · log(b/a)`; equivalently, the
`ℝ≥0∞`-integral of `‖u‖⁻²` over the annulus equals `2π log(b/a)`. Proved by changing
to polar coordinates (`Complex.lintegral_comp_polarCoord_symm`), on whose target the
integrand collapses (Tonelli) to the angle-independent radial weight `ρ⁻¹` over
`Ico a b ×ˢ Ioo (-π) π`; the angular factor gives `volume (Ioo (-π) π) = 2π` and the
radial factor is `radial_lintegral_inv`. -/
theorem annulus_lintegral (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∫⁻ u : ℂ in {u : ℂ | a ≤ ‖u‖ ∧ ‖u‖ < b}, ‖(u ^ (-2 : ℤ) : ℂ)‖ₑ ∂volume
      = ENNReal.ofReal (2 * Real.pi * Real.log (b / a)) := by
  have hb : 0 < b := ha.trans hab
  -- The annulus set is measurable.
  have hSmeas : MeasurableSet {u : ℂ | a ≤ ‖u‖ ∧ ‖u‖ < b} := by
    apply MeasurableSet.inter
    · exact measurableSet_le measurable_const measurable_norm
    · exact measurableSet_lt measurable_norm measurable_const
  -- Fold the set restriction into an indicator over all of ℂ.
  rw [← lintegral_indicator hSmeas]
  -- Change to polar coordinates.
  rw [← Complex.lintegral_comp_polarCoord_symm]
  -- Now the integral is over polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π.
  rw [show (polarCoord.target) = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π from rfl]
  -- Simplify the integrand on the target: indicator collapses to ρ⁻¹ on the annular product.
  have htarget : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π) :=
    (measurableSet_Ioi).prod measurableSet_Ioo
  rw [setLIntegral_congr_fun htarget
    (g := fun p : ℝ × ℝ =>
      (Set.Ico a b ×ˢ (Set.univ : Set ℝ)).indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.1⁻¹) p) ?_]
  · -- Fold the indicator into a restriction to the intersection of the two products.
    rw [setLIntegral_indicator ((measurableSet_Ico).prod MeasurableSet.univ)]
    -- The intersection simplifies to `Ico a b ×ˢ Ioo (-π) π` (using `a > 0`, so `Ico a b ⊆ Ioi 0`).
    have hinter : (Set.Ico a b ×ˢ (Set.univ : Set ℝ)) ∩ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π)
        = Set.Ico a b ×ˢ Set.Ioo (-π) π := by
      rw [Set.prod_inter_prod, Set.univ_inter]
      congr 1
      rw [Set.inter_eq_left]
      intro x hx
      exact lt_of_lt_of_le ha hx.1
    rw [hinter]
    -- Tonelli: factor the product integral.
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from
      (Measure.volume_eq_prod ℝ ℝ)]
    rw [setLIntegral_prod _ ?_]
    · -- inner integral over θ is constant; equals `ofReal ρ⁻¹ * volume (Ioo (-π) π)`.
      simp only [setLIntegral_const]
      -- volume (Ioo (-π) π) = ofReal (2π)
      have hvol : (volume : Measure ℝ) (Set.Ioo (-π) π) = ENNReal.ofReal (2 * π) := by
        rw [Real.volume_Ioo]; congr 1; ring
      rw [hvol]
      -- pull the constant out: ∫⁻ ρ in Ico a b, ofReal ρ⁻¹ * ofReal (2π)
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      rw [radial_lintegral_inv a b ha hab]
      -- combine: ofReal (log(b/a)) * ofReal (2π) = ofReal (2π log(b/a))
      rw [← ENNReal.ofReal_mul (Real.log_nonneg ?_)]
      · rw [mul_comm (Real.log (b / a)) (2 * π), mul_assoc]
      · rw [le_div_iff₀ ha, one_mul]
        exact hab.le
    · -- measurability of the constant indicator-free integrand on the restricted product
      apply Measurable.aemeasurable
      exact (ENNReal.measurable_ofReal.comp ((measurable_fst).inv))
  · -- pointwise equality of integrands on the target
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Set.mem_Ioi] at hp1
    -- ‖symm p‖ = |p.1| = p.1
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    simp only
    -- the set membership of `symm p` is equivalent to `p.1 ∈ Ico a b`, and `p.2 ∈ univ`.
    have hmem_iff : (Complex.polarCoord.symm p ∈ {u : ℂ | a ≤ ‖u‖ ∧ ‖u‖ < b}) ↔
        (p ∈ Set.Ico a b ×ˢ (Set.univ : Set ℝ)) := by
      simp only [Set.mem_ofPred_eq, hnorm, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true]
    by_cases hmem : p ∈ Set.Ico a b ×ˢ (Set.univ : Set ℝ)
    · -- inside the annulus: compute the integrand value
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hmem_iff.mpr hmem)]
      -- ‖(symm p)^(-2)‖ₑ = ofReal (p.1^(-2 : ℤ))
      have hnz : ‖(Complex.polarCoord.symm p ^ (-2 : ℤ) : ℂ)‖ₑ
          = ENNReal.ofReal (p.1 ^ (-2 : ℤ)) := by
        rw [← ofReal_norm (Complex.polarCoord.symm p ^ (-2 : ℤ)),
          Complex.norm_zpow, hnorm]
      rw [hnz, smul_eq_mul, ← ENNReal.ofReal_mul hp1.le]
      congr 1
      rw [zpow_neg, zpow_two]
      field_simp
    · -- outside the annulus: both indicators vanish
      rw [Set.indicator_of_notMem hmem _,
        Set.indicator_of_notMem (fun h => hmem (hmem_iff.mp h)) _, smul_zero]

end NoWanderingDomains.SingularIntegral
