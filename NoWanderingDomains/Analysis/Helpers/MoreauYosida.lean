/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.ENNReal.Real

/-!
# Moreau–Yosida envelopes of an `ℝ≥0∞`-valued density

The **Moreau–Yosida (infimal-convolution) envelope** of a density `φ : ℂ → ℝ≥0∞` at scale
`i ∈ ℕ`:

  `moreauEnvelope φ i x = ⨅ y, ((min (φ y) i).toReal + i · dist x y)`.

This is the standard regularization producing, from an arbitrary density, an increasing
family of `i`-Lipschitz real-valued approximants from below. The key facts recorded here:

* `moreauEnvelope_nonneg`, `ofReal_moreauEnvelope_le` — the envelope sits between `0` and
  `min (φ x) i`;
* `moreauEnvelope_mono` — the family increases in `i`;
* `moreauEnvelope_lipschitz` — the envelope is `i`-Lipschitz;
* `le_moreauEnvelope_of_forall_le` — a uniform cushion `ε ≤ φ` survives to the envelope
  (once `ε ≤ i`);
* `iSup_ofReal_moreauEnvelope` — for **lower semicontinuous** `φ` the envelopes recover `φ`
  pointwise: `⨆ i, ofReal (moreauEnvelope φ i x) = φ x`.

These are the continuous-from-below approximants used by the Beurling chain potential in the
planar Loewner reciprocity workstream (`QC/GeometricToAnalytic/Loewner/`): continuity of the
approximating density is what makes the eikonal inequality for the chain potential pointwise
(no Lebesgue-point argument), and monotonicity + the lower-semicontinuous recovery is what
drives the monotone-convergence endgame.
-/

open Metric
open scoped ENNReal NNReal

namespace NoWanderingDomains

/-- The **Moreau–Yosida envelope** of a density `φ : ℂ → ℝ≥0∞` at scale `i`: the infimal
convolution of the truncation `min (φ ·) i` (converted to `ℝ`) with `i · dist`. It is an
`i`-Lipschitz approximant of `φ` from below, increasing in `i`, recovering `φ` pointwise
when `φ` is lower semicontinuous. -/
noncomputable def moreauEnvelope (φ : ℂ → ℝ≥0∞) (i : ℕ) (x : ℂ) : ℝ :=
  ⨅ y : ℂ, ((min (φ y) (i : ℝ≥0∞)).toReal + (i : ℝ) * dist x y)

/-- The envelope is nonnegative. -/
theorem moreauEnvelope_nonneg (φ : ℂ → ℝ≥0∞) (i : ℕ) (x : ℂ) :
    0 ≤ moreauEnvelope φ i x := by
  refine Real.iInf_nonneg fun y => ?_
  exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg (Nat.cast_nonneg i) dist_nonneg)

/-- The envelope is bounded by the truncated density at the point (take `y = x`). -/
theorem moreauEnvelope_le (φ : ℂ → ℝ≥0∞) (i : ℕ) (x : ℂ) :
    moreauEnvelope φ i x ≤ (min (φ x) (i : ℝ≥0∞)).toReal := by
  have hb : BddBelow (Set.range fun y : ℂ =>
      ((min (φ y) (i : ℝ≥0∞)).toReal + (i : ℝ) * dist x y)) := by
    refine ⟨0, ?_⟩
    rintro z ⟨y, rfl⟩
    exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg (Nat.cast_nonneg i) dist_nonneg)
  simpa [moreauEnvelope, dist_self] using ciInf_le hb x

/-- The envelope sits below the truncated density in `ℝ≥0∞`:
`ofReal (moreauEnvelope φ i x) ≤ min (φ x) i`. In particular it is `≤ φ x` and `≤ i`. -/
theorem ofReal_moreauEnvelope_le (φ : ℂ → ℝ≥0∞) (i : ℕ) (x : ℂ) :
    ENNReal.ofReal (moreauEnvelope φ i x) ≤ min (φ x) (i : ℝ≥0∞) :=
  ENNReal.ofReal_le_of_le_toReal (moreauEnvelope_le φ i x)

/-- The envelopes increase in the scale parameter. -/
theorem moreauEnvelope_mono (φ : ℂ → ℝ≥0∞) {i j : ℕ} (hij : i ≤ j) (x : ℂ) :
    moreauEnvelope φ i x ≤ moreauEnvelope φ j x := by
  unfold moreauEnvelope
  refine ciInf_mono ⟨0, ?_⟩ fun y => ?_
  · rintro z ⟨y, rfl⟩
    exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg (Nat.cast_nonneg i) dist_nonneg)
  · refine add_le_add ?_ (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) dist_nonneg)
    refine ENNReal.toReal_mono
      (ne_top_of_le_ne_top (ENNReal.natCast_ne_top j) (min_le_right _ _))
      (min_le_min le_rfl ?_)
    exact_mod_cast hij

/-- The envelope at scale `i` is `i`-Lipschitz: for any `x, x'`,
each competitor `y` for `x'` is a competitor for `x` at extra cost `i · dist x x'`. -/
theorem moreauEnvelope_lipschitz (φ : ℂ → ℝ≥0∞) (i : ℕ) :
    LipschitzWith i (moreauEnvelope φ i) := by
  have hb : ∀ x : ℂ, BddBelow (Set.range fun y : ℂ =>
      ((min (φ y) (i : ℝ≥0∞)).toReal + (i : ℝ) * dist x y)) := by
    intro x
    refine ⟨0, ?_⟩
    rintro z ⟨y, rfl⟩
    exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg (Nat.cast_nonneg i) dist_nonneg)
  have key : ∀ x x' : ℂ,
      moreauEnvelope φ i x ≤ moreauEnvelope φ i x' + (i : ℝ) * dist x x' := by
    intro x x'
    rw [← sub_le_iff_le_add]
    unfold moreauEnvelope
    refine le_ciInf fun y => ?_
    rw [sub_le_iff_le_add]
    have h1 : moreauEnvelope φ i x ≤ (min (φ y) (i : ℝ≥0∞)).toReal + (i : ℝ) * dist x y :=
      ciInf_le (hb x) y
    have h4 : (i : ℝ) * dist x y ≤ (i : ℝ) * dist x x' + (i : ℝ) * dist x' y := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (dist_triangle x x' y) (Nat.cast_nonneg i)
    unfold moreauEnvelope at h1
    linarith
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  rw [Real.dist_eq, NNReal.coe_natCast, abs_sub_le_iff]
  constructor
  · have := key x x'
    linarith
  · have := key x' x
    rw [dist_comm x' x] at this
    linarith

/-- A uniform cushion below `φ` survives to the envelope: if `ofReal ε ≤ φ y` for all `y`
and `ε ≤ i`, then `ε ≤ moreauEnvelope φ i x`. Every term of the infimum is `≥ ε`, since
`(min (φ y) i).toReal ≥ min ε i = ε` and the distance term is nonnegative. -/
theorem le_moreauEnvelope_of_forall_le {φ : ℂ → ℝ≥0∞} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ y, ENNReal.ofReal ε ≤ φ y) {i : ℕ} (hi : ε ≤ i) (x : ℂ) :
    ε ≤ moreauEnvelope φ i x := by
  unfold moreauEnvelope
  refine le_ciInf fun y => ?_
  have h1 : ENNReal.ofReal ε ≤ min (φ y) (i : ℝ≥0∞) :=
    le_min (h y) (ENNReal.ofReal_le_of_le_toReal (by simpa [ENNReal.toReal_natCast] using hi))
  have h2 : ε ≤ (min (φ y) (i : ℝ≥0∞)).toReal := by
    have := ENNReal.toReal_mono
      (ne_top_of_le_ne_top (ENNReal.natCast_ne_top i) (min_le_right _ _)) h1
    rwa [ENNReal.toReal_ofReal hε] at this
  have h3 : 0 ≤ (i : ℝ) * dist x y := mul_nonneg (Nat.cast_nonneg i) dist_nonneg
  linarith

/-- **Pointwise recovery for lower semicontinuous densities.** If `φ` is lower
semicontinuous then the Moreau–Yosida envelopes increase pointwise to `φ`:
`⨆ i, ofReal (moreauEnvelope φ i x) = φ x`.

Proof sketch: `≤` is `ofReal_moreauEnvelope_le`. For `≥`, fix `c < φ x`; by lower
semicontinuity there is `r > 0` with `φ y > c` on `ball x r`; for `i` large
(`i ≥ c` and `i·r ≥ c`), every competitor `y` pays either `(min (φ y) i).toReal ≥ min c i = c`
(if `y ∈ ball x r`) or `i · dist x y ≥ i·r ≥ c` (otherwise), so
`moreauEnvelope φ i x ≥ c`. -/
theorem iSup_ofReal_moreauEnvelope {φ : ℂ → ℝ≥0∞} (hφ : LowerSemicontinuous φ) (x : ℂ) :
    ⨆ i : ℕ, ENNReal.ofReal (moreauEnvelope φ i x) = φ x := by
  refine le_antisymm
    (iSup_le fun i => (ofReal_moreauEnvelope_le φ i x).trans (min_le_left _ _)) ?_
  refine ENNReal.le_of_forall_nnreal_lt fun c hc => ?_
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hφ x _ hc)
  obtain ⟨i, hi1, hi2⟩ : ∃ i : ℕ, (c : ℝ) ≤ i ∧ (c : ℝ) ≤ i * r := by
    obtain ⟨i, hi⟩ := exists_nat_ge (max (c : ℝ) ((c : ℝ) / r))
    refine ⟨i, (le_max_left _ _).trans hi, ?_⟩
    have hdiv : (c : ℝ) / r ≤ i := (le_max_right _ _).trans hi
    rwa [div_le_iff₀ hr] at hdiv
  have henv : (c : ℝ) ≤ moreauEnvelope φ i x := by
    unfold moreauEnvelope
    refine le_ciInf fun y => ?_
    by_cases hy : y ∈ Metric.ball x r
    · have hmin : (c : ℝ≥0∞) ≤ min (φ y) (i : ℝ≥0∞) :=
        le_min (hball y hy).le (by exact_mod_cast hi1)
      have h2 : (c : ℝ) ≤ (min (φ y) (i : ℝ≥0∞)).toReal := by
        have := ENNReal.toReal_mono
          (ne_top_of_le_ne_top (ENNReal.natCast_ne_top i) (min_le_right _ _)) hmin
        simpa using this
      have h3 : 0 ≤ (i : ℝ) * dist x y := mul_nonneg (Nat.cast_nonneg i) dist_nonneg
      linarith
    · have hdist : r ≤ dist x y := by
        rw [dist_comm]
        exact le_of_not_gt fun hlt => hy (Metric.mem_ball.mpr hlt)
      have h2 : (c : ℝ) ≤ (i : ℝ) * dist x y :=
        hi2.trans (mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg i))
      have h3 : 0 ≤ (min (φ y) (i : ℝ≥0∞)).toReal := ENNReal.toReal_nonneg
      linarith
  calc (c : ℝ≥0∞) = ENNReal.ofReal (c : ℝ) := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (moreauEnvelope φ i x) := ENNReal.ofReal_le_ofReal henv
    _ ≤ ⨆ i : ℕ, ENNReal.ofReal (moreauEnvelope φ i x) :=
        le_iSup (fun i : ℕ => ENNReal.ofReal (moreauEnvelope φ i x)) i

end NoWanderingDomains
