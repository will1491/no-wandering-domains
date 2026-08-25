/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Regularity.GeometricToACL
import NoWanderingDomains.QC.LengthArea.CurveModulus

/-!
# Pointwise dilatation bound for geometric quasiconformality

A geometrically `K`-quasiconformal homeomorphism satisfies, almost everywhere, the pointwise
dilatation inequality `‖(Df)⁻¹‖² · det (Df) ≤ K` for the real differential `Df = fderiv ℝ f`.

This is the analytic payoff of the length–area regularity theory. From `IsQCGeometric` the map is
`W^{1,2}_loc` and almost-everywhere differentiable (`geometric_ae_differentiableAt`), and
`SensePreserving` gives a positive Jacobian almost everywhere (`SensePreserving.ae_det_pos`). The
length–area transport of the round-annulus/rectangle modulus bound pins the operator dilatation
`‖(Df)⁻¹‖² · det (Df)` — equivalently `(|∂f| + |∂̄f|) / (|∂f| − |∂̄f|)` via the Wirtinger identities
`det_fderiv_eq_wirtinger` and `opNorm_inverse_eq_wirtinger` — below `K`.

The conclusion is stated in exactly the form consumed by the length–area transport
`pushforwardGood_modulus_le`.

## Main statements

* `geometric_pointwise_dilatation` — the almost-everywhere bound `‖(Df)⁻¹‖² · det (Df) ≤ K`.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **Pointwise dilatation bound of a geometrically quasiconformal map.** For a geometrically
`K`-quasiconformal homeomorphism `f`, at almost every point the real differential `Df = fderiv ℝ f`
satisfies `‖(Df)⁻¹‖² · det (Df) ≤ K`. This is the almost-everywhere dilatation inequality in the
exact operator form the length–area transport `pushforwardGood_modulus_le` consumes; via the
Wirtinger identities it is `(|∂f| + |∂̄f|) / (|∂f| − |∂̄f|) ≤ K`, i.e. the pointwise maximal
dilatation is bounded by `K`. Where the Jacobian is non-positive the operator dilatation is
non-positive and the bound is automatic; where it is positive, the reverse length–area
infinitesimal data `IsQCGeometric.reverseLengthArea_data` supplies the pointwise operator-norm
dilatation bound `‖Df‖² ≤ K · det (Df)`, which the Wirtinger identities convert to the stated
form. -/
theorem geometric_pointwise_dilatation {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∀ᵐ z : ℂ,
      ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * (fderiv ℝ f z).det ≤ K := by
  have hK1 : (1 : ℝ) ≤ K := hf.1
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  -- The pointwise operator-norm dilatation bound `‖Df‖² ≤ K · det (Df)` a.e., from the reverse
  -- length–area infinitesimal data (the single genuine geometric ⇒ analytic residual).
  obtain ⟨_, _, hdil, _, _⟩ := IsQCGeometric.reverseLengthArea_data hf
  filter_upwards [hdil] with z hz
  by_cases hdet : 0 < (fderiv ℝ f z).det
  · -- Positive Jacobian: convert the operator-norm bound to the inverse-operator form.
    set p : ℂ := dz f z with hp
    set q : ℂ := dzbar f z with hq
    have hdetw : (fderiv ℝ f z).det = ‖p‖ ^ 2 - ‖q‖ ^ 2 := by
      rw [hp, hq]; exact det_fderiv_eq_wirtinger f z
    have hopf : ‖fderiv ℝ f z‖ = ‖p‖ + ‖q‖ := by rw [hp, hq]; exact opNorm_fderiv_eq_wirtinger f z
    have hqlt : ‖q‖ < ‖p‖ := by nlinarith [hdet, hdetw, norm_nonneg p, norm_nonneg q]
    have hσ2pos : 0 < ‖p‖ - ‖q‖ := by linarith
    have hopn : ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖
        = (‖p‖ + ‖q‖) / (fderiv ℝ f z).det := by
      rw [hp, hq]; exact opNorm_inverse_eq_wirtinger f z hdet
    -- The Wirtinger dilatation core `σ₁ ≤ K · σ₂`, extracted from `‖Df‖² ≤ K · det`.
    have hcore : ‖p‖ + ‖q‖ ≤ K * (‖p‖ - ‖q‖) := by
      rw [hopf, hdetw] at hz
      have hpqpos : 0 < ‖p‖ + ‖q‖ := by linarith [norm_nonneg p, norm_nonneg q]
      nlinarith [hz, hpqpos, hσ2pos]
    -- `‖A⁻¹‖² · det = σ₁ / σ₂` and `σ₁ ≤ K σ₂ ⇒ σ₁/σ₂ ≤ K`.
    have hval : ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * (fderiv ℝ f z).det
        = (‖p‖ + ‖q‖) / (‖p‖ - ‖q‖) := by
      rw [hopn, hdetw, div_pow,
        show (‖p‖ ^ 2 - ‖q‖ ^ 2) = (‖p‖ + ‖q‖) * (‖p‖ - ‖q‖) by ring]
      field_simp
    rw [hval, div_le_iff₀ hσ2pos]
    exact hcore
  · -- Non-positive Jacobian: the operator dilatation is non-positive.
    rw [not_lt] at hdet
    have h1 : (0 : ℝ) ≤ ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 := by positivity
    calc ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * (fderiv ℝ f z).det
        ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 hdet
      _ ≤ K := hK0

end NoWanderingDomains
