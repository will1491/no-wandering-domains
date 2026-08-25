/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Sobolev.WeakDeriv
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Beltrami coefficients

A **Beltrami coefficient** is the analytic datum of a quasiconformal map: a
measurable function `μ : ℂ → ℂ` with `‖μ‖∞ < 1`. It is the right-hand side of
the Beltrami equation `∂̄f = μ · ∂f`, and the strict bound `‖μ‖∞ < 1` is what
makes that equation elliptic — it is load-bearing for the Neumann-series
construction of the measurable Riemann mapping theorem (the series
`∑ₙ (μ · T)ⁿ μ` converges precisely because `‖μ · T‖ₚ < 1`, which needs
`‖μ‖∞ < 1`, not `≤ 1`).

We bundle the measurability and the strict essential-sup bound into a structure
so that downstream signatures carry a single `(b : BeltramiCoeff)` argument
rather than a raw `ℂ → ℂ` plus separate side hypotheses. The essential supremum
is `MeasureTheory.eLpNormEssSup μ volume`, the `L∞` seminorm with respect to
planar Lebesgue measure.

* `BeltramiCoeff.normInf b` is `‖b.μ‖∞` as a real number (`< 1` by
  `normInf_lt_one`);
* `BeltramiCoeff.K b = (1 + ‖μ‖∞) / (1 − ‖μ‖∞)` is the **maximal dilatation**,
  the bridge to the geometric `K`-quasiconformal track (`1 ≤ K` by `one_le_K`).
-/

open MeasureTheory Complex
open scoped ENNReal

namespace NoWanderingDomains

/-- A **Beltrami coefficient**: a measurable `μ : ℂ → ℂ` whose essential
supremum is strictly less than `1`. This is the analytic datum of a
quasiconformal map, the right-hand side of the Beltrami equation
`∂̄f = μ · ∂f`. The bound is strict (`< 1`, not `≤ 1`): it is what makes the
Beltrami equation elliptic and the measurable-Riemann-mapping Neumann series
converge. -/
structure BeltramiCoeff where
  /-- The coefficient function. -/
  μ : ℂ → ℂ
  /-- The coefficient is measurable. -/
  measurable : Measurable μ
  /-- The essential supremum of `μ` is strictly below `1`. -/
  bound : eLpNormEssSup μ volume < 1

namespace BeltramiCoeff

/-- The `L∞` norm `‖μ‖∞` of a Beltrami coefficient, as a real number. It lies in
`[0, 1)` by `normInf_nonneg` and `normInf_lt_one`. -/
noncomputable def normInf (b : BeltramiCoeff) : ℝ := (eLpNormEssSup b.μ volume).toReal

/-- The `L∞` norm `‖μ‖∞` of a Beltrami coefficient is nonnegative: it is the
`ENNReal.toReal` of an essential supremum, and `toReal` is always nonnegative. -/
theorem normInf_nonneg (b : BeltramiCoeff) : 0 ≤ b.normInf := ENNReal.toReal_nonneg

/-- The `L∞` norm `‖μ‖∞` of a Beltrami coefficient is strictly below `1`. This is
the real-number form of the structure's `bound` field
`eLpNormEssSup μ volume < 1`: the essential supremum is finite (it is `< 1 < ⊤`),
so passing to `ENNReal.toReal` preserves the strict inequality. The strict bound
`‖μ‖∞ < 1` (rather than `≤ 1`) is what makes the Beltrami equation elliptic and
drives the convergence of the measurable-Riemann-mapping Neumann series. -/
theorem normInf_lt_one (b : BeltramiCoeff) : b.normInf < 1 := by
  have h := b.bound
  have hlt : b.normInf < (1 : ℝ≥0∞).toReal :=
    (ENNReal.toReal_lt_toReal (ne_top_of_lt h) ENNReal.one_ne_top).mpr h
  simpa using hlt

/-- The **maximal dilatation** `K = (1 + ‖μ‖∞) / (1 − ‖μ‖∞)` of a Beltrami
coefficient. It satisfies `1 ≤ K` (`one_le_K`) and is the bridge to the
geometric `K`-quasiconformal track. -/
noncomputable def K (b : BeltramiCoeff) : ℝ := (1 + b.normInf) / (1 - b.normInf)

/-- The maximal dilatation `K = (1 + ‖μ‖∞) / (1 − ‖μ‖∞)` of a Beltrami coefficient
is at least `1` (with equality exactly in the conformal case `‖μ‖∞ = 0`).
Immediate from `0 ≤ ‖μ‖∞ < 1`: the denominator `1 − ‖μ‖∞` is positive and is
dominated by the numerator `1 + ‖μ‖∞`. -/
theorem one_le_K (b : BeltramiCoeff) : 1 ≤ b.K := by
  have h0 : 0 ≤ b.normInf := b.normInf_nonneg
  have h1 : b.normInf < 1 := b.normInf_lt_one
  rw [K, le_div_iff₀ (by linarith)]
  linarith

end BeltramiCoeff

end NoWanderingDomains
