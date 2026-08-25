/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.SingularIntegral.Beurling.Convolution

/-!
# The Beurling transform — L2Core

The dyadic almost-orthogonality / Schur assembly giving the strong `L²` bound
`czOperator_beurling_strongType_L2`, the maximal-operator `L²` bound, a.e.
convergence of the truncations, and the `L²` isometry `beurling_l2_isometry`.

Part of the `Beurling` development (overview in `Beurling/Kernel.lean`). -/

open MeasureTheory Complex Filter Topology
open scoped Real ENNReal NNReal Convolution InnerProductSpace

namespace NoWanderingDomains

variable {μ : ℂ → ℂ} {z : ℂ} {p : ℝ≥0∞}

/-- **Pointwise value-variation bound.** For `P, Q ∈ ℂ` with `Q = P + t`,
`‖P⁻² - Q⁻²‖ ≤ ‖t‖·‖P+Q‖ / (‖P‖²·‖Q‖²)`. Pure algebra: `P⁻²-Q⁻² = (Q²-P²)/(P²Q²)` and
`Q²-P² = (Q-P)(Q+P)`. -/
lemma norm_zpow_neg_two_sub_le {P Q : ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ‖P ^ (-2 : ℤ) - Q ^ (-2 : ℤ)‖ ≤ ‖Q - P‖ * ‖P + Q‖ / (‖P‖ ^ 2 * ‖Q‖ ^ 2) := by
  have hP2 : P ^ 2 ≠ 0 := pow_ne_zero _ hP
  have hQ2 : Q ^ 2 ≠ 0 := pow_ne_zero _ hQ
  have hid : P ^ (-2 : ℤ) - Q ^ (-2 : ℤ) = (Q - P) * (P + Q) / (P ^ 2 * Q ^ 2) := by
    rw [zpow_neg, zpow_neg, zpow_two, zpow_two]
    field_simp
    ring
  rw [hid, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]

/-- The annular shell `{c ≤ ‖x‖ < d}` equals `ball 0 d \ ball 0 c`. -/
lemma shell_eq_ball_diff (c d : ℝ) :
    {x : ℂ | c ≤ ‖x‖ ∧ ‖x‖ < d} = Metric.ball (0 : ℂ) d \ Metric.ball (0 : ℂ) c := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Metric.mem_ball, dist_zero_right, not_lt]
  tauto

/-- **Volume of an annular shell.** For `0 ≤ c ≤ d`, the shell `{c ≤ ‖x‖ < d}` has volume
`ofReal (d²·π) - ofReal (c²·π)`. -/
lemma volume_shell (c d : ℝ) (hc : 0 ≤ c) (hcd : c ≤ d) :
    volume {x : ℂ | c ≤ ‖x‖ ∧ ‖x‖ < d}
      = ENNReal.ofReal (d ^ 2 * Real.pi) - ENNReal.ofReal (c ^ 2 * Real.pi) := by
  have hd : 0 ≤ d := hc.trans hcd
  rw [shell_eq_ball_diff]
  rw [measure_sdiff (Metric.ball_subset_ball hcd) measurableSet_ball.nullMeasurableSet]
  · rw [Complex.volume_ball, Complex.volume_ball]
    have hpi : (↑NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    rw [hpi]
    congr 1
    · rw [← ENNReal.ofReal_pow hd, ← ENNReal.ofReal_mul (by positivity)]
    · rw [← ENNReal.ofReal_pow hc, ← ENNReal.ofReal_mul (by positivity)]
  · rw [Complex.volume_ball]
    exact ne_top_of_lt (ENNReal.mul_lt_top (by simp) (by simp))

/-- **Volume of an annular shell, packaged form.** For `0 ≤ c ≤ d`, the shell `{c ≤ ‖x‖ < d}`
has volume `ofReal ((d²-c²)·π)`. -/
lemma volume_shell' (c d : ℝ) (hc : 0 ≤ c) (hcd : c ≤ d) :
    volume {x : ℂ | c ≤ ‖x‖ ∧ ‖x‖ < d} = ENNReal.ofReal ((d ^ 2 - c ^ 2) * Real.pi) := by
  rw [volume_shell c d hc hcd, ← ENNReal.ofReal_sub _ (by positivity), sub_mul]

/-- The annular shell `{c ≤ ‖x‖ < d}` is measurable. -/
lemma measurableSet_shell (c d : ℝ) :
    MeasurableSet {x : ℂ | c ≤ ‖x‖ ∧ ‖x‖ < d} := by
  apply MeasurableSet.inter
  · exact measurableSet_le measurable_const measurable_norm
  · exact measurableSet_lt measurable_norm measurable_const

/-- **Pointwise modulus-of-continuity bound for a dyadic piece.** With `R₁ = 2ᵐr`,
`R₂ = 2ᵐ⁺¹r`, `A` the annulus, `B = A + t`, and `S` the two boundary shells thickened by `‖t‖`,
the pointwise difference `‖ψ(x-t) - ψ(x)‖ₑ` is bounded by a value-variation term supported on
`B` plus a boundary-jump term supported on `S`. -/
lemma omega_pointwise_le (r : ℝ) (hr : 0 < r) (m : ℕ) (t : ℂ)
    (ht : 2 * ‖t‖ ≤ (2 : ℝ) ^ m * r) (x : ℂ) :
    ‖dyadicBeurling r m (x - t) - dyadicBeurling r m x‖ₑ
      ≤ Set.indicator {x : ℂ | (2:ℝ)^m * r ≤ ‖x - t‖ ∧ ‖x - t‖ < (2:ℝ)^(m+1) * r}
          (fun _ => ENNReal.ofReal (24 * ‖t‖ / ((2:ℝ)^m * r) ^ 3)) x
        + Set.indicator
            ({x : ℂ | (2:ℝ)^m * r - ‖t‖ ≤ ‖x‖ ∧ ‖x‖ < (2:ℝ)^m * r + ‖t‖}
              ∪ {x : ℂ | (2:ℝ)^(m+1) * r - ‖t‖ ≤ ‖x‖ ∧ ‖x‖ < (2:ℝ)^(m+1) * r + ‖t‖})
            (fun _ => ENNReal.ofReal (4 / ((2:ℝ)^m * r) ^ 2)) x := by
  set R₁ : ℝ := (2:ℝ)^m * r with hR₁
  set R₂ : ℝ := (2:ℝ)^(m+1) * r with hR₂
  have hR₁pos : 0 < R₁ := by rw [hR₁]; positivity
  have hR₂eq : R₂ = 2 * R₁ := by rw [hR₂, hR₁, pow_succ]; ring
  have htle : ‖t‖ ≤ R₁ / 2 := by rw [hR₁] at ht ⊢; linarith
  have htnn : 0 ≤ ‖t‖ := norm_nonneg t
  set A : Set ℂ := {u : ℂ | R₁ ≤ ‖u‖ ∧ ‖u‖ < R₂}
  set B : Set ℂ := {x : ℂ | R₁ ≤ ‖x - t‖ ∧ ‖x - t‖ < R₂}
  set Inner : Set ℂ := {x : ℂ | R₁ - ‖t‖ ≤ ‖x‖ ∧ ‖x‖ < R₁ + ‖t‖}
  set Outer : Set ℂ := {x : ℂ | R₂ - ‖t‖ ≤ ‖x‖ ∧ ‖x‖ < R₂ + ‖t‖}
  -- enorm difference of indicators of `u^(-2)`.
  have hψ : ∀ u : ℂ, dyadicBeurling r m u = Set.indicator A (fun u => u ^ (-2:ℤ)) u := by
    intro u; rfl
  -- membership predicates
  have hPmem : (x - t ∈ A) ↔ (R₁ ≤ ‖x - t‖ ∧ ‖x - t‖ < R₂) := Iff.rfl
  have hQmem : (x ∈ A) ↔ (R₁ ≤ ‖x‖ ∧ ‖x‖ < R₂) := Iff.rfl
  by_cases hP : x - t ∈ A
  · by_cases hQ : x ∈ A
    · -- both in A: value-variation bound, x ∈ B.
      rw [hψ, hψ, Set.indicator_of_mem hP, Set.indicator_of_mem hQ]
      have hPne : (x - t) ≠ 0 := by
        intro h; have := hP.1; rw [h, norm_zero] at this; linarith
      have hQne : x ≠ 0 := by
        intro h; have := hQ.1; rw [h, norm_zero] at this; linarith
      have hnormP : R₁ ≤ ‖x - t‖ := hP.1
      have hnormP2 : ‖x - t‖ < R₂ := hP.2
      have hnormQ : R₁ ≤ ‖x‖ := hQ.1
      -- pointwise value bound: ‖(x-t)^(-2) - x^(-2)‖ ≤ 24‖t‖/R₁³.
      have hval : ‖(x - t) ^ (-2:ℤ) - x ^ (-2:ℤ)‖ ≤ 24 * ‖t‖ / R₁ ^ 3 := by
        refine (norm_zpow_neg_two_sub_le hPne hQne).trans ?_
        -- ‖x - (x-t)‖ = ‖t‖, ‖(x-t)+x‖ ≤ ‖x-t‖+‖x‖
        have hdiff : ‖x - (x - t)‖ = ‖t‖ := by rw [sub_sub_cancel]
        have hsum : ‖(x - t) + x‖ ≤ ‖x - t‖ + ‖x‖ := norm_add_le _ _
        have hxub : ‖x‖ ≤ R₂ + ‖t‖ := by
          calc ‖x‖ = ‖(x - t) + t‖ := by ring_nf
            _ ≤ ‖x - t‖ + ‖t‖ := norm_add_le _ _
            _ ≤ R₂ + ‖t‖ := by linarith
        have hsum2 : ‖(x - t) + x‖ ≤ R₂ + (R₂ + ‖t‖) := by
          refine hsum.trans ?_; linarith [hnormP2, hxub]
        -- numerator ≤ ‖t‖·(2R₂+‖t‖), denominator ≥ R₁²·R₁² (since ‖x‖ ≥ R₁)
        rw [hdiff]
        have hPnn : 0 ≤ ‖x - t‖ := norm_nonneg _
        have hQnn : 0 ≤ ‖x‖ := norm_nonneg _
        have hnum : ‖t‖ * ‖(x - t) + x‖ ≤ ‖t‖ * (R₂ + (R₂ + ‖t‖)) :=
          mul_le_mul_of_nonneg_left hsum2 htnn
        have hden : R₁ ^ 2 * R₁ ^ 2 ≤ ‖x - t‖ ^ 2 * ‖x‖ ^ 2 := by
          apply mul_le_mul
          · exact pow_le_pow_left₀ hR₁pos.le hnormP 2
          · exact pow_le_pow_left₀ hR₁pos.le hnormQ 2
          · positivity
          · positivity
        -- clear denominators: a/b ≤ c/d  ⇐  a*d ≤ c*b with b,d > 0.
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc ‖t‖ * ‖(x - t) + x‖ * R₁ ^ 3
            ≤ (‖t‖ * (R₂ + (R₂ + ‖t‖))) * R₁ ^ 3 :=
              mul_le_mul_of_nonneg_right hnum (by positivity)
          _ ≤ 24 * ‖t‖ * (R₁ ^ 2 * R₁ ^ 2) := by
              rw [hR₂eq]
              have hR3 : (0:ℝ) ≤ R₁ ^ 3 := by positivity
              have hkey : ‖t‖ * (2 * R₁ + (2 * R₁ + ‖t‖)) ≤ 24 * ‖t‖ * R₁ := by
                nlinarith [hR₁pos, htle, htnn]
              have : R₁ ^ 2 * R₁ ^ 2 = R₁ * R₁ ^ 3 := by ring
              rw [this]
              calc ‖t‖ * (2 * R₁ + (2 * R₁ + ‖t‖)) * R₁ ^ 3
                  ≤ (24 * ‖t‖ * R₁) * R₁ ^ 3 := mul_le_mul_of_nonneg_right hkey hR3
                _ = 24 * ‖t‖ * (R₁ * R₁ ^ 3) := by ring
          _ ≤ 24 * ‖t‖ * (‖x - t‖ ^ 2 * ‖x‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hden (by positivity)
      rw [Set.indicator_of_mem (show x ∈ B from hP)]
      calc ‖(x - t) ^ (-2:ℤ) - x ^ (-2:ℤ)‖ₑ
          = ENNReal.ofReal ‖(x - t) ^ (-2:ℤ) - x ^ (-2:ℤ)‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (24 * ‖t‖ / R₁ ^ 3) := ENNReal.ofReal_le_ofReal hval
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · -- x-t ∈ A, x ∉ A: boundary term active (x ∈ S), value `(x-t)^(-2)`.
      rw [hψ, hψ, Set.indicator_of_mem hP, Set.indicator_of_notMem hQ, sub_zero]
      have hnormP : R₁ ≤ ‖x - t‖ := hP.1
      have hnormP2 : ‖x - t‖ < R₂ := hP.2
      -- enorm value bound `‖(x-t)^(-2)‖ₑ ≤ ofReal (4 / R₁²)`.
      have hvalbd : ‖(x - t) ^ (-2:ℤ)‖ₑ ≤ ENNReal.ofReal (4 / R₁ ^ 2) := by
        rw [← ofReal_norm, norm_zpow]
        apply ENNReal.ofReal_le_ofReal
        rw [zpow_neg, zpow_two]
        have hsq : R₁ * R₁ ≤ ‖x - t‖ * ‖x - t‖ := by nlinarith [hR₁pos, hnormP, norm_nonneg (x - t)]
        calc (‖x - t‖ * ‖x - t‖)⁻¹ ≤ (R₁ * R₁)⁻¹ := inv_anti₀ (by positivity) hsq
          _ ≤ 4 / R₁ ^ 2 := by
              rw [div_eq_mul_inv, sq]
              nlinarith [inv_nonneg.mpr (mul_nonneg hR₁pos.le hR₁pos.le)]
      -- membership x ∈ S.
      have hQA : ‖x‖ < R₁ ∨ R₂ ≤ ‖x‖ := by
        rcases le_or_gt R₁ ‖x‖ with h | h
        · rcases lt_or_ge ‖x‖ R₂ with h2 | h2
          · exact absurd ⟨h, h2⟩ hQ
          · exact Or.inr h2
        · exact Or.inl h
      have hxsub : ‖x - t‖ - ‖t‖ ≤ ‖x‖ ∧ ‖x‖ ≤ ‖x - t‖ + ‖t‖ := by
        constructor
        · have := norm_sub_norm_le (x - t) x
          rw [show (x - t) - x = -t by ring, norm_neg] at this; linarith
        · calc ‖x‖ = ‖(x - t) + t‖ := by ring_nf
            _ ≤ ‖x - t‖ + ‖t‖ := norm_add_le _ _
      have hmemS : x ∈ Inner ∪ Outer := by
        rcases hQA with h | h
        · left
          refine ⟨?_, ?_⟩
          · linarith [hxsub.1, hnormP]
          · linarith [h]
        · right
          refine ⟨?_, ?_⟩
          · linarith [h]
          · linarith [hxsub.2, hnormP2]
      rw [Set.indicator_of_mem (show x ∈ Inner ∪ Outer from hmemS)]
      exact le_add_of_nonneg_of_le (by positivity) hvalbd
  · by_cases hQ : x ∈ A
    · -- x-t ∉ A, x ∈ A: boundary term active (x ∈ S), value `-x^(-2)`.
      rw [hψ, hψ, Set.indicator_of_notMem hP, Set.indicator_of_mem hQ, zero_sub, enorm_neg]
      have hnormQ : R₁ ≤ ‖x‖ := hQ.1
      have hnormQ2 : ‖x‖ < R₂ := hQ.2
      have hvalbd : ‖x ^ (-2:ℤ)‖ₑ ≤ ENNReal.ofReal (4 / R₁ ^ 2) := by
        rw [← ofReal_norm, norm_zpow]
        apply ENNReal.ofReal_le_ofReal
        rw [zpow_neg, zpow_two]
        have hsq : R₁ * R₁ ≤ ‖x‖ * ‖x‖ := by nlinarith [hR₁pos, hnormQ, norm_nonneg x]
        calc (‖x‖ * ‖x‖)⁻¹ ≤ (R₁ * R₁)⁻¹ := inv_anti₀ (by positivity) hsq
          _ ≤ 4 / R₁ ^ 2 := by
              rw [div_eq_mul_inv, sq]
              nlinarith [inv_nonneg.mpr (mul_nonneg hR₁pos.le hR₁pos.le)]
      have hPA : ‖x - t‖ < R₁ ∨ R₂ ≤ ‖x - t‖ := by
        rcases le_or_gt R₁ ‖x - t‖ with h | h
        · rcases lt_or_ge ‖x - t‖ R₂ with h2 | h2
          · exact absurd ⟨h, h2⟩ hP
          · exact Or.inr h2
        · exact Or.inl h
      have hxsub : ‖x‖ - ‖t‖ ≤ ‖x - t‖ ∧ ‖x - t‖ ≤ ‖x‖ + ‖t‖ := by
        constructor
        · have := norm_sub_norm_le x (x - t); rw [sub_sub_cancel] at this; linarith
        · have := norm_add_le x (-t); rw [show x + -t = x - t by ring, norm_neg] at this; linarith
      have hmemS : x ∈ Inner ∪ Outer := by
        rcases hPA with h | h
        · left
          refine ⟨?_, ?_⟩
          · linarith [hnormQ]
          · linarith [hxsub.2, h]
        · right
          refine ⟨?_, ?_⟩
          · linarith [hxsub.1, h]
          · linarith [hnormQ2]
      rw [Set.indicator_of_mem (show x ∈ Inner ∪ Outer from hmemS)]
      exact le_add_of_nonneg_of_le (by positivity) hvalbd
    · -- neither in A: difference is 0.
      rw [hψ, hψ, Set.indicator_of_notMem hP, Set.indicator_of_notMem hQ, sub_zero, enorm_zero]
      positivity

/-- **First-order modulus of continuity of a dyadic piece.** For a translation `t` with
`2‖t‖ ≤ 2ᵐr` (so the segment stays in the annulus and the boundary layer is thin), the `L¹`
modulus `∫ ‖ψₘ(·-t) - ψₘ‖` is `≤ 120π·‖t‖/(2ᵐr)`, linear in `‖t‖`. This is the quantitative
smoothness that, paired with mean-zero, yields the geometric almost-orthogonality decay. -/
lemma omega_dyadicBeurling_le (r : ℝ) (hr : 0 < r) (m : ℕ) (t : ℂ)
    (ht : 2 * ‖t‖ ≤ (2 : ℝ) ^ m * r) :
    (∫⁻ x, ‖dyadicBeurling r m (x - t) - dyadicBeurling r m x‖ₑ ∂volume)
      ≤ ENNReal.ofReal (120 * Real.pi * ‖t‖ / ((2:ℝ)^m * r)) := by
  set R₁ : ℝ := (2:ℝ)^m * r with hR₁
  set R₂ : ℝ := (2:ℝ)^(m+1) * r with hR₂
  have hR₁pos : 0 < R₁ := by rw [hR₁]; positivity
  have hR₂eq : R₂ = 2 * R₁ := by rw [hR₂, hR₁, pow_succ]; ring
  have htle : ‖t‖ ≤ R₁ / 2 := by rw [hR₁] at ht ⊢; linarith
  have htnn : 0 ≤ ‖t‖ := norm_nonneg t
  set B : Set ℂ := {x : ℂ | R₁ ≤ ‖x - t‖ ∧ ‖x - t‖ < R₂} with hB
  set Inner : Set ℂ := {x : ℂ | R₁ - ‖t‖ ≤ ‖x‖ ∧ ‖x‖ < R₁ + ‖t‖} with hInner
  set Outer : Set ℂ := {x : ℂ | R₂ - ‖t‖ ≤ ‖x‖ ∧ ‖x‖ < R₂ + ‖t‖} with hOuter
  -- Bound the integrand pointwise by the value+boundary terms.
  have hpt := fun x => omega_pointwise_le r hr m t ht x
  refine le_trans (lintegral_mono hpt) ?_
  -- split the integral of the sum.
  have hBmeas : MeasurableSet B := by
    apply MeasurableSet.inter
    · exact measurableSet_le measurable_const (measurable_norm.comp (measurable_id.sub_const t))
    · exact measurableSet_lt (measurable_norm.comp (measurable_id.sub_const t)) measurable_const
  have hSmeas : MeasurableSet (Inner ∪ Outer) :=
    (measurableSet_shell _ _).union (measurableSet_shell _ _)
  rw [lintegral_add_left
    ((measurable_const.indicator hBmeas))]
  rw [lintegral_indicator_const hBmeas, lintegral_indicator_const hSmeas]
  -- volume B = volume of annulus shell R₁..R₂.
  have hvolB : volume B = ENNReal.ofReal ((R₂ ^ 2 - R₁ ^ 2) * Real.pi) := by
    have hpre : B = (fun x : ℂ => x - t) ⁻¹' {y : ℂ | R₁ ≤ ‖y‖ ∧ ‖y‖ < R₂} := rfl
    rw [hpre, (measurePreserving_sub_right volume t).measure_preimage
      (measurableSet_shell _ _).nullMeasurableSet]
    exact volume_shell' R₁ R₂ hR₁pos.le (by rw [hR₂eq]; linarith)
  -- bound volume (Inner ∪ Outer) by sum of the two shells.
  have hvolS : volume (Inner ∪ Outer)
      ≤ ENNReal.ofReal (4 * R₁ * ‖t‖ * Real.pi) + ENNReal.ofReal (8 * R₁ * ‖t‖ * Real.pi) := by
    refine (measure_union_le _ _).trans ?_
    have hvolI : volume Inner = ENNReal.ofReal (4 * R₁ * ‖t‖ * Real.pi) := by
      rw [hInner, volume_shell' (R₁ - ‖t‖) (R₁ + ‖t‖) (by linarith) (by linarith)]
      congr 1; ring
    have hvolO : volume Outer = ENNReal.ofReal (8 * R₁ * ‖t‖ * Real.pi) := by
      rw [hOuter, volume_shell' (R₂ - ‖t‖) (R₂ + ‖t‖) (by rw [hR₂eq]; linarith) (by linarith)]
      rw [hR₂eq]; congr 1; ring
    rw [hvolI, hvolO]
  -- combine.
  rw [hvolB]
  have hval_bound :
      ENNReal.ofReal (24 * ‖t‖ / R₁ ^ 3) * ENNReal.ofReal ((R₂ ^ 2 - R₁ ^ 2) * Real.pi)
        ≤ ENNReal.ofReal (72 * Real.pi * ‖t‖ / R₁) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [hR₂eq, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hR₁pos]
    nlinarith [hR₁pos, htnn, Real.pi_pos]
  have hbdy_bound :
      ENNReal.ofReal (4 / R₁ ^ 2)
          * (ENNReal.ofReal (4 * R₁ * ‖t‖ * Real.pi) + ENNReal.ofReal (8 * R₁ * ‖t‖ * Real.pi))
        ≤ ENNReal.ofReal (48 * Real.pi * ‖t‖ / R₁) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hR₁pos]
    nlinarith [hR₁pos, Real.pi_pos, htnn]
  calc ENNReal.ofReal (24 * ‖t‖ / R₁ ^ 3) * ENNReal.ofReal ((R₂ ^ 2 - R₁ ^ 2) * Real.pi)
        + ENNReal.ofReal (4 / R₁ ^ 2) * volume (Inner ∪ Outer)
      ≤ ENNReal.ofReal (72 * Real.pi * ‖t‖ / R₁)
          + ENNReal.ofReal (4 / R₁ ^ 2)
            * (ENNReal.ofReal (4 * R₁ * ‖t‖ * Real.pi) + ENNReal.ofReal (8 * R₁ * ‖t‖ * Real.pi)) :=
        add_le_add hval_bound (mul_le_mul_right hvolS _)
    _ ≤ ENNReal.ofReal (72 * Real.pi * ‖t‖ / R₁) + ENNReal.ofReal (48 * Real.pi * ‖t‖ / R₁) :=
        add_le_add le_rfl hbdy_bound
    _ = ENNReal.ofReal (120 * Real.pi * ‖t‖ / R₁) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- **Support of a dyadic piece.** Outside the annulus `[2ᵃr, 2ᵃ⁺¹r)` the dyadic piece
vanishes. -/
lemma enorm_dyadicBeurling_eq_zero_of_large (r : ℝ) (a : ℕ) (t : ℂ)
    (ht : (2 : ℝ) ^ (a + 1) * r ≤ ‖t‖) : ‖dyadicBeurling r a t‖ₑ = 0 := by
  rw [enorm_dyadicBeurling]
  rw [Set.indicator_of_notMem]
  intro hmem
  exact absurd hmem.2 (not_lt.mpr ht)

/-- The dyadic piece is measurable. -/
lemma measurable_dyadicBeurling (r : ℝ) (b : ℕ) : Measurable (dyadicBeurling r b) := by
  apply Measurable.indicator _ (measurableSet_dyadicAnnulus r b)
  have : (fun u : ℂ => u ^ (-2 : ℤ)) = (fun u : ℂ => (u * u)⁻¹) := by
    funext u; rw [zpow_neg, zpow_two]
  rw [this]
  exact (measurable_id.mul measurable_id).inv

/-- **Support of the reflected kernel.** Outside the annulus the reflected kernel vanishes. -/
lemma enorm_convKernelStar_dyadicBeurling_eq_zero_of_large (r : ℝ) (a : ℕ) (t : ℂ)
    (ht : (2 : ℝ) ^ (a + 1) * r ≤ ‖t‖) : ‖convKernelStar (dyadicBeurling r a) t‖ₑ = 0 := by
  rw [convKernelStar, RCLike.enorm_conj]
  exact enorm_dyadicBeurling_eq_zero_of_large r a (-t) (by rwa [norm_neg])

/-- **First-order modulus of continuity of the reflected kernel.** Reduces to the dyadic-piece
estimate by the reflection `x ↦ -x` (measure preserving) and conjugation. -/
lemma omega_convKernelStar_le (r : ℝ) (hr : 0 < r) (b : ℕ) (s : ℂ)
    (hs : 2 * ‖s‖ ≤ (2 : ℝ) ^ b * r) :
    (∫⁻ x, ‖convKernelStar (dyadicBeurling r b) (x - s)
        - convKernelStar (dyadicBeurling r b) x‖ₑ ∂volume)
      ≤ ENNReal.ofReal (120 * Real.pi * ‖s‖ / ((2:ℝ)^b * r)) := by
  -- pointwise: ‖K(x-s) - K(x)‖ₑ = ‖ψ(s-x) - ψ(-x)‖ₑ.
  have hpt : ∀ x : ℂ, ‖convKernelStar (dyadicBeurling r b) (x - s)
      - convKernelStar (dyadicBeurling r b) x‖ₑ
      = ‖dyadicBeurling r b ((-x) - (-s)) - dyadicBeurling r b (-x)‖ₑ := by
    intro x
    rw [convKernelStar, convKernelStar]
    rw [show -(x - s) = (-x) - (-s) by ring]
    rw [← map_sub, RCLike.enorm_conj]
  simp_rw [hpt]
  -- change of variables y = -x (measure preserving negation).
  set F : ℂ → ℝ≥0∞ := fun y => ‖dyadicBeurling r b (y - (-s)) - dyadicBeurling r b y‖ₑ with hF
  have hFmeas : Measurable F := by
    apply Measurable.enorm
    apply Measurable.sub
    · exact (measurable_dyadicBeurling r b).comp (measurable_id.sub_const (-s))
    · exact measurable_dyadicBeurling r b
  have hcomp : (∫⁻ x, F (-x) ∂volume) = ∫⁻ y, F y ∂volume :=
    (Measure.measurePreserving_neg volume).lintegral_comp hFmeas
  have hrw : (∫⁻ x, ‖dyadicBeurling r b ((-x) - (-s)) - dyadicBeurling r b (-x)‖ₑ ∂volume)
      = ∫⁻ x, F (-x) ∂volume := rfl
  rw [hrw, hcomp]
  -- now ∫⁻ y, F y = ω_{ψ_b}(-s).
  have heq : (∫⁻ y, F y ∂volume)
      = ∫⁻ y, ‖dyadicBeurling r b (y - (-s)) - dyadicBeurling r b y‖ₑ ∂volume := rfl
  rw [heq]
  have := omega_dyadicBeurling_le r hr b (-s) (by rwa [norm_neg])
  rwa [norm_neg] at this

/-- **Abstract cross-convolution decay.** If `g` is a mean-zero `L¹` kernel supported in
`‖t‖ < 2ᵃ⁺¹r` with mass `≤ 2π log 2`, and `f` has first-order modulus of continuity
`≤ 120π‖s‖/2ᵇr`, then for `a + 2 ≤ b` the convolution has `L¹` mass `≤ 4096·(1/2)ᵇ⁻ᵃ`.
This packages the modulus-of-continuity estimate against the kernel support. -/
lemma cross_conv_decay_le (r : ℝ) (hr : 0 < r) {g f : ℂ → ℂ} (a b : ℕ) (hab : a + 2 ≤ b)
    (hg : MemLp g 1 volume) (hgz : ∫ t, g t ∂volume = 0)
    (hg_supp : ∀ t : ℂ, (2:ℝ)^(a+1) * r ≤ ‖t‖ → ‖g t‖ₑ = 0)
    (hg_mass : (∫⁻ t, ‖g t‖ₑ ∂volume) ≤ ENNReal.ofReal (2 * Real.pi * Real.log 2))
    (hf : MemLp f 1 volume)
    (hf_omega : ∀ s : ℂ, 2 * ‖s‖ ≤ (2:ℝ)^b * r →
        (∫⁻ x, ‖f (x - s) - f x‖ₑ ∂volume) ≤ ENNReal.ofReal (120 * Real.pi * ‖s‖ / ((2:ℝ)^b * r))) :
    eLpNorm (MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume
      ≤ ENNReal.ofReal (4096 * ((1:ℝ)/2) ^ (b - a)) := by
  refine (eLpNorm_convolution_meanZero_le hg hf hgz).trans ?_
  -- pointwise bound on the integrand `‖g t‖ₑ · ω_f(t)`.
  set c : ℝ := 120 * Real.pi * (2:ℝ)^(a+1) * r / ((2:ℝ)^b * r) with hc
  have hra : (0:ℝ) < (2:ℝ)^(a+1) * r := by positivity
  have hrb : (0:ℝ) < (2:ℝ)^b * r := by positivity
  have hptbound : ∀ t : ℂ,
      ‖g t‖ₑ * (∫⁻ x, ‖f (x - t) - f x‖ₑ ∂volume) ≤ ‖g t‖ₑ * ENNReal.ofReal c := by
    intro t
    by_cases htlarge : (2:ℝ)^(a+1) * r ≤ ‖t‖
    · rw [hg_supp t htlarge]; simp
    · push Not at htlarge
      apply mul_le_mul_right
      have hts : 2 * ‖t‖ ≤ (2:ℝ)^b * r := by
        have h1 : (2:ℝ)^(a+1) * r ≤ (2:ℝ)^(b-1) * r := by
          apply mul_le_mul_of_nonneg_right _ hr.le
          apply pow_le_pow_right₀ (by norm_num)
          omega
        have hbb : (2:ℝ)^b = 2 * (2:ℝ)^(b-1) := by
          conv_lhs => rw [show b = (b - 1) + 1 by omega]
          rw [pow_succ]; ring
        have h2 : 2 * ((2:ℝ)^(b-1) * r) = (2:ℝ)^b * r := by rw [hbb]; ring
        nlinarith [htlarge, h1, h2, norm_nonneg t]
      refine (hf_omega t hts).trans ?_
      apply ENNReal.ofReal_le_ofReal
      rw [hc, div_le_div_iff₀ hrb hrb]
      apply mul_le_mul_of_nonneg_right _ hrb.le
      nlinarith [htlarge.le, Real.pi_pos, mul_pos (pow_pos (by norm_num : (0:ℝ) < 2) (a+1)) hr]
  refine (lintegral_mono hptbound).trans ?_
  rw [lintegral_mul_const'' _ hg.1.enorm]
  refine (mul_le_mul_left hg_mass _).trans ?_
  -- (2π log2)·c ≤ 4096·(1/2)^(b-a).
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- c = 120π·2^(a+1)/2^b = 240π·(1/2)^(b-a).
  have hpow : (2:ℝ)^(a+1) / (2:ℝ)^b = 2 * ((1:ℝ)/2) ^ (b - a) := by
    have h2bne : (2:ℝ)^b ≠ 0 := by positivity
    have h2bane : (2:ℝ)^(b-a) ≠ 0 := by positivity
    rw [one_div, inv_pow, div_eq_iff h2bne, eq_comm]
    rw [show (2:ℝ) * (2 ^ (b - a))⁻¹ * 2 ^ b = (2 * 2 ^ b) * (2 ^ (b - a))⁻¹ by ring]
    rw [mul_inv_eq_iff_eq_mul₀ h2bane]
    rw [show (2:ℝ) * 2 ^ b = 2 ^ (b + 1) by rw [pow_succ]; ring, ← pow_add]
    congr 1
    omega
  have hceq : c = 240 * Real.pi * ((1:ℝ)/2) ^ (b - a) := by
    rw [hc, mul_div_mul_right _ _ (ne_of_gt hr)]
    rw [show 120 * Real.pi * (2:ℝ)^(a+1) / (2:ℝ)^b
        = 120 * Real.pi * ((2:ℝ)^(a+1) / (2:ℝ)^b) by ring]
    rw [hpow]; ring
  rw [hceq]
  -- (2π log2)·240π·(1/2)^(b-a) ≤ 4096·(1/2)^(b-a).
  have hpos : (0:ℝ) ≤ ((1:ℝ)/2) ^ (b - a) := by positivity
  have hnum : (2 * Real.pi * Real.log 2) * (240 * Real.pi) ≤ 4096 := by
    have hπ : Real.pi < 3.15 := Real.pi_lt_d2
    have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hπpos : (0:ℝ) ≤ Real.pi := Real.pi_pos.le
    have hlogpos : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hπsq : Real.pi ^ 2 ≤ 9.9225 := by nlinarith [hπ, hπpos]
    have hkey : Real.pi ^ 2 * Real.log 2 ≤ 9.9225 * 0.6931471808 := by
      apply mul_le_mul hπsq hlog2.le hlogpos (by norm_num)
    have hrw : (2 * Real.pi * Real.log 2) * (240 * Real.pi)
        = 480 * (Real.pi ^ 2 * Real.log 2) := by ring
    rw [hrw]
    nlinarith [hkey]
  calc 2 * Real.pi * Real.log 2 * (240 * Real.pi * ((1:ℝ)/2) ^ (b - a))
      = (2 * Real.pi * Real.log 2 * (240 * Real.pi)) * ((1:ℝ)/2) ^ (b - a) := by ring
    _ ≤ 4096 * ((1:ℝ)/2) ^ (b - a) := mul_le_mul_of_nonneg_right hnum hpos

/-- **Annular almost-orthogonality (the cancellation estimate).**
The `L¹` mass of the cross-convolution of two dyadic Beurling pieces (in either of the two
orders relevant to the two Schur bounds) decays geometrically in the scale separation
`d = (i - j) + (j - i) = |i - j|`, with the geometric constant `4096`. After taking square
roots (`√(4096·(1/2)^d) = 64·(1/2)^{d/2}`) and summing the geometric row, the Cotlar–Stein
constant is bounded.

The **small-separation case `d ≤ 6`** is the trivial Young `L¹⋆L¹` bound `eLpNorm_cross_le_sq`
(`‖ψ̃_i ⋆ ψ_j‖₁ ≤ (2π log 2)²`) plus the numeric comparison `sq_logmass_le`.

The **large-separation case `d ≥ 7`** is the genuine cancellation. It uses the zeroth moment
(mean-zero) of the smaller-scale factor to write the convolution value as a difference
`(g ⋆ f)(x) = ∫ g(t)·(f(x-t) - f(x)) dt` (`convolution_apply_eq_of_integral_zero`), reducing the
`L¹` norm to `∫ ‖g(t)‖·ω_f(t) dt` where `ω_f(t) = ‖f(·-t) - f‖₁` is the first-order modulus of
continuity (`eLpNorm_convolution_meanZero_le`). The dyadic pieces have `ω_f(t) ≤ 120π‖t‖/2ᵇr`
(`omega_dyadicBeurling_le`, `omega_convKernelStar_le`) — a value-variation part
(`norm_zpow_neg_two_sub_le`) plus a boundary-layer part controlled by the thin-shell measure
(`volume_shell'`). Against the kernel support `‖t‖ < 2ᵃ⁺¹r` this gives the `2^{a+1-b} = 2·2^{-d}`
decay (`cross_conv_decay_le`). Both factor orderings and both convolution orders reduce to this
single shape via commutativity of convolution. -/
lemma truncBeurling_almostOrthogonal (r : ℝ) (hr : 0 < r) (i j : ℕ) :
    eLpNorm (MeasureTheory.convolution (convKernelStar (dyadicBeurling r i)) (dyadicBeurling r j)
        (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume
        ≤ ENNReal.ofReal (4096 * ((1:ℝ)/2) ^ ((i - j) + (j - i)))
      ∧ eLpNorm (MeasureTheory.convolution (dyadicBeurling r i)
        (convKernelStar (dyadicBeurling r j))
        (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume
        ≤ ENNReal.ofReal (4096 * ((1:ℝ)/2) ^ ((i - j) + (j - i))) := by
  set d := (i - j) + (j - i) with hd_def
  by_cases hsmall : d ≤ 6
  · -- Small separation: trivial Young bound + numeric comparison (fully proved).
    have htriv := eLpNorm_cross_le_sq r hr i j
    have hnum : (2 * Real.pi * Real.log 2) ^ 2 ≤ 4096 * ((1:ℝ)/2) ^ d := sq_logmass_le d hsmall
    have hmono : ENNReal.ofReal ((2 * Real.pi * Real.log 2) ^ 2)
        ≤ ENNReal.ofReal (4096 * ((1:ℝ)/2) ^ d) := ENNReal.ofReal_le_ofReal hnum
    exact ⟨htriv.1.trans hmono, htriv.2.trans hmono⟩
  · -- Large separation `d ≥ 7`: first-order modulus-of-continuity estimate giving `2^{-d}`.
    -- The target `4096·(1/2)^d = 4096·2^{-d}` decays like `2^{-d}`, which is exactly what a
    -- first-order modulus-of-continuity bound delivers: writing the convolution value as a
    -- difference `(g⋆f)(x) = ∫ g(t)·(f(x-t)-f(x)) dt` using the mean-zero of the smaller-scale
    -- factor `g`, the `L¹` norm is `≤ ∫ ‖g(t)‖·ω_f(t) dt` with `ω_f(t) = ‖f(·-t)-f‖₁ ≤ 120π‖t‖/2ᵇr`
    -- (value-variation part + boundary-layer part, the latter controlled by the thin-shell
    -- measure).
    -- Against the kernel support `‖t‖ < 2ᵃ⁺¹r` this yields the `2^{a+1-b} = 2·2^{-d}` decay; the
    -- numeric slack `480·π²·log2 ≈ 3283 ≤ 4096` closes the constant (`cross_conv_decay_le`).
    -- All four sub-cases (two conjuncts × `i<j`/`i>j`) reduce to this single shape, using
    -- commutativity of convolution with the commutative `mul`.
    have hflip : ∀ g f : ℂ → ℂ,
        MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume
          = MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume := by
      intro g f
      have hmf : (ContinuousLinearMap.mul ℂ ℂ).flip = ContinuousLinearMap.mul ℂ ℂ := by
        ext
        simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply']
      calc MeasureTheory.convolution g f (ContinuousLinearMap.mul ℂ ℂ) volume
          = MeasureTheory.convolution g f ((ContinuousLinearMap.mul ℂ ℂ).flip) volume := by
            rw [hmf]
        _ = MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume :=
            convolution_flip (ContinuousLinearMap.mul ℂ ℂ)
    -- Mass of each kernel (zeroth moment of the absolute value): `2π log 2`.
    have hmassψ : ∀ a : ℕ, (∫⁻ t, ‖dyadicBeurling r a t‖ₑ ∂volume)
        ≤ ENNReal.ofReal (2 * Real.pi * Real.log 2) := by
      intro a
      rw [← eLpNorm_one_eq_lintegral_enorm, eLpNorm_dyadicBeurling r hr a]
    have hmassK : ∀ a : ℕ, (∫⁻ t, ‖convKernelStar (dyadicBeurling r a) t‖ₑ ∂volume)
        ≤ ENNReal.ofReal (2 * Real.pi * Real.log 2) := by
      intro a
      rw [← eLpNorm_one_eq_lintegral_enorm,
        eLpNorm_convKernelStar _ (memLp_dyadicBeurling r hr a).1, eLpNorm_dyadicBeurling r hr a]
    -- `i ≠ j` (else `d = 0 ≤ 6`).
    rcases lt_or_gt_of_ne (show i ≠ j by rintro rfl; simp only [Nat.sub_self] at hd_def; omega)
      with hij | hij
    · -- i < j: smaller scale `i`, larger scale `j`.
      have hab : i + 2 ≤ j := by omega
      have hd_eq : j - i = d := by omega
      refine ⟨?_, ?_⟩
      · -- K_i ⋆ ψ_j: kernel K_i (scale i, mean-zero), difference ψ_j (scale j).
        have := cross_conv_decay_le r hr i j hab
          (memLp_convKernelStar (memLp_dyadicBeurling r hr i))
          (integral_convKernelStar_dyadicBeurling_eq_zero r hr i)
          (fun t ht => enorm_convKernelStar_dyadicBeurling_eq_zero_of_large r i t ht)
          (hmassK i) (memLp_dyadicBeurling r hr j)
          (fun s hs => omega_dyadicBeurling_le r hr j s hs)
        rwa [hd_eq] at this
      · -- ψ_i ⋆ K_j: kernel ψ_i (scale i, mean-zero), difference K_j (scale j).
        have := cross_conv_decay_le r hr i j hab
          (memLp_dyadicBeurling r hr i) (integral_dyadicBeurling_eq_zero r hr i)
          (fun t ht => enorm_dyadicBeurling_eq_zero_of_large r i t ht)
          (hmassψ i) (memLp_convKernelStar (memLp_dyadicBeurling r hr j))
          (fun s hs => omega_convKernelStar_le r hr j s hs)
        rwa [hd_eq] at this
    · -- i > j: smaller scale `j`, larger scale `i`; flip convolutions.
      have hab : j + 2 ≤ i := by omega
      have hd_eq : i - j = d := by omega
      refine ⟨?_, ?_⟩
      · -- K_i ⋆ ψ_j = ψ_j ⋆ K_i: kernel ψ_j (scale j, mean-zero), difference K_i (scale i).
        rw [hflip (convKernelStar (dyadicBeurling r i)) (dyadicBeurling r j)]
        have := cross_conv_decay_le r hr j i hab
          (memLp_dyadicBeurling r hr j) (integral_dyadicBeurling_eq_zero r hr j)
          (fun t ht => enorm_dyadicBeurling_eq_zero_of_large r j t ht)
          (hmassψ j) (memLp_convKernelStar (memLp_dyadicBeurling r hr i))
          (fun s hs => omega_convKernelStar_le r hr i s hs)
        rwa [hd_eq] at this
      · -- ψ_i ⋆ K_j = K_j ⋆ ψ_i: kernel K_j (scale j, mean-zero), difference ψ_i (scale i).
        rw [hflip (dyadicBeurling r i) (convKernelStar (dyadicBeurling r j))]
        have := cross_conv_decay_le r hr j i hab
          (memLp_convKernelStar (memLp_dyadicBeurling r hr j))
          (integral_convKernelStar_dyadicBeurling_eq_zero r hr j)
          (fun t ht => enorm_convKernelStar_dyadicBeurling_eq_zero_of_large r j t ht)
          (hmassK j) (memLp_dyadicBeurling r hr i)
          (fun s hs => omega_dyadicBeurling_le r hr i s hs)
        rwa [hd_eq] at this

/-- `√(1/2) ≤ 3/4`, since `√2 ≥ 4/3 ⟺ 2 ≥ 16/9`. -/
lemma sqrt_half_le_three_quarters : Real.sqrt (1/2) ≤ 3/4 := by
  rw [show (3:ℝ)/4 = Real.sqrt ((3/4)^2) from (Real.sqrt_sq (by norm_num)).symm]
  apply Real.sqrt_le_sqrt; norm_num

/-- `∑_{j ∈ Fin N} (√(1/2))^|i-j| ≤ 7`, uniformly in `N`. Proof: bound the base
`√(1/2) ≤ 3/4` pointwise, so each half is a geometric `3/4`-tail; the `j ≤ i` half is
`≤ ∑_{k<N}(3/4)^k < 4` and the `j > i` half (indices `≥ 1`) is `≤ 4 - 1 = 3`. -/
lemma rowsum_half_dist_le (N : ℕ) (i : Fin N) :
    ∑ j : Fin N, (Real.sqrt (1/2)) ^ ((i.val - j.val) + (j.val - i.val)) ≤ 7 := by
  classical
  set q : ℝ := Real.sqrt (1/2) with hq_def
  have hq_pos : 0 < q := Real.sqrt_pos.mpr (by norm_num)
  have hq_le : q ≤ 3/4 := sqrt_half_le_three_quarters
  -- Pointwise: q^k ≤ (3/4)^k.
  have hqpow : ∀ k : ℕ, q ^ k ≤ ((3:ℝ)/4) ^ k := fun k =>
    pow_le_pow_left₀ hq_pos.le hq_le k
  -- Geometric bound: ∑_{k<M} (3/4)^k ≤ 4 (partial sum bounded by the tsum = (1-3/4)⁻¹ = 4).
  have hsummable : Summable (fun k : ℕ => ((3:ℝ)/4) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have htsum : (∑' k : ℕ, ((3:ℝ)/4) ^ k) = 4 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hgeom : ∀ M : ℕ, ∑ k ∈ Finset.range M, ((3:ℝ)/4) ^ k ≤ 4 := by
    intro M
    have h := hsummable.sum_le_tsum (Finset.range M) (fun k _ => by positivity)
    rw [htsum] at h; exact h
  have hsplit : ∑ j : Fin N, q ^ ((i.val - j.val) + (j.val - i.val))
      = (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val ≤ i.val),
            q ^ ((i.val - j.val) + (j.val - i.val)))
        + (∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ j.val ≤ i.val),
            q ^ ((i.val - j.val) + (j.val - i.val))) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [hsplit, show (7:ℝ) = 4 + 3 by norm_num]
  apply add_le_add
  · -- j ≤ i half: indices i-j range in {0,...}, bound by ∑_{k<N}(3/4)^k < 4.
    have hinj : Set.InjOn (fun j : Fin N => i.val - j.val)
        (Finset.univ.filter (fun j : Fin N => j.val ≤ i.val)) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      apply Fin.ext; simp only at hab; omega
    have hrw : (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val ≤ i.val),
          q ^ ((i.val - j.val) + (j.val - i.val)))
        = ∑ k ∈ (Finset.univ.filter (fun j : Fin N => j.val ≤ i.val)).image
            (fun j => i.val - j.val), q ^ k := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      congr 1; omega
    rw [hrw]
    refine le_trans (Finset.sum_le_sum (fun k _ => hqpow k)) ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity))
      (hgeom N)
    intro k hk
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    simp only [Finset.mem_range]; omega
  · -- j > i half: indices j-i ≥ 1, bound by ∑_{1≤k<N}(3/4)^k = (∑_{k<N}(3/4)^k) - 1 ≤ 3.
    have hinj : Set.InjOn (fun j : Fin N => j.val - i.val)
        (Finset.univ.filter (fun j : Fin N => ¬ j.val ≤ i.val)) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      apply Fin.ext; simp only at hab; omega
    have hrw : (∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ j.val ≤ i.val),
          q ^ ((i.val - j.val) + (j.val - i.val)))
        = ∑ k ∈ (Finset.univ.filter (fun j : Fin N => ¬ j.val ≤ i.val)).image
            (fun j => j.val - i.val), q ^ k := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      congr 1; omega
    rw [hrw]
    refine le_trans (Finset.sum_le_sum (fun k _ => hqpow k)) ?_
    -- The image is contained in `Finset.Ico 1 N` (indices ≥ 1).
    have hsub : (Finset.univ.filter (fun j : Fin N => ¬ j.val ≤ i.val)).image
        (fun j => j.val - i.val) ⊆ Finset.Ico 1 N := by
      intro k hk
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      simp only [Finset.mem_Ico]; omega
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)) ?_
    -- ∑_{k ∈ Ico 1 N} (3/4)^k = (∑_{k<N}(3/4)^k) - 1 (if N ≥ 1) ≤ 4 - 1 = 3.
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · have hrange : Finset.range N = insert 0 (Finset.Ico 1 N) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
      have hnotmem : (0:ℕ) ∉ Finset.Ico 1 N := by simp
      have hsum0 : (∑ k ∈ Finset.range N, ((3:ℝ)/4) ^ k)
          = 1 + ∑ k ∈ Finset.Ico 1 N, ((3:ℝ)/4) ^ k := by
        rw [hrange, Finset.sum_insert hnotmem]; norm_num
      have := hgeom N
      linarith [hsum0]

/-- `√(4096·(1/2)^d) = 64·(√(1/2))^d`. -/
lemma sqrt_const_geom (d : ℕ) :
    Real.sqrt (4096 * ((1:ℝ)/2)^d) = 64 * (Real.sqrt (1/2))^d := by
  have h1 : ((1:ℝ)/2)^d = ((Real.sqrt (1/2))^d)^2 := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  rw [show (4096:ℝ) = 64^2 by norm_num, h1, ← mul_pow, Real.sqrt_sq (by positivity)]

/-- The dyadic Cotlar–Stein operator `T_j = convolution by ψ_j` on `L²`. -/
noncomputable def dyadicT (r : ℝ) (hr : 0 < r) (j : ℕ) :
    (Lp ℂ 2 (volume : Measure ℂ)) →L[ℂ] (Lp ℂ 2 (volume : Measure ℂ)) :=
  convCLM (dyadicBeurling r j) (memLp_dyadicBeurling r hr j)

/-- Per-pair Schur bound (adjoint·op direction): `‖T_i* ∘ T_j‖ ≤ 4096·(1/2)^|i-j|`. -/
lemma adjMul_pair_le (r : ℝ) (hr : 0 < r) (i j : ℕ) :
    ‖(ContinuousLinearMap.adjoint (dyadicT r hr i)) ∘L (dyadicT r hr j)‖
      ≤ 4096 * ((1:ℝ)/2) ^ ((i - j) + (j - i)) := by
  unfold dyadicT
  rw [adjoint_convCLM, convCLM_comp (memLp_convKernelStar (memLp_dyadicBeurling r hr i))
    (memLp_dyadicBeurling r hr j)]
  refine (convCLM_opNorm_le _ _).trans ?_
  have hbd := (truncBeurling_almostOrthogonal r hr i j).1
  have : (eLpNorm (MeasureTheory.convolution (convKernelStar (dyadicBeurling r i))
      (dyadicBeurling r j) (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume).toReal
      ≤ (ENNReal.ofReal (4096 * ((1:ℝ)/2) ^ ((i - j) + (j - i)))).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd
  refine this.trans ?_
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- Per-pair Schur bound (op·adjoint direction): `‖T_i ∘ T_j*‖ ≤ 4096·(1/2)^|i-j|`. -/
lemma mulAdj_pair_le (r : ℝ) (hr : 0 < r) (i j : ℕ) :
    ‖(dyadicT r hr i) ∘L (ContinuousLinearMap.adjoint (dyadicT r hr j))‖
      ≤ 4096 * ((1:ℝ)/2) ^ ((i - j) + (j - i)) := by
  unfold dyadicT
  rw [adjoint_convCLM, convCLM_comp (memLp_dyadicBeurling r hr i)
    (memLp_convKernelStar (memLp_dyadicBeurling r hr j))]
  refine (convCLM_opNorm_le _ _).trans ?_
  have hbd := (truncBeurling_almostOrthogonal r hr i j).2
  have : (eLpNorm (MeasureTheory.convolution (dyadicBeurling r i)
      (convKernelStar (dyadicBeurling r j)) (ContinuousLinearMap.mul ℂ ℂ) volume) 1 volume).toReal
      ≤ (ENNReal.ofReal (4096 * ((1:ℝ)/2) ^ ((i - j) + (j - i)))).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd
  refine this.trans ?_
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- First Schur sum bound: `∑_j √‖T_i* ∘ T_j‖ ≤ 2⁹`, uniformly in `N` and `i`. -/
lemma schur_adjMul (r : ℝ) (hr : 0 < r) (N : ℕ) (i : Fin N) :
    ∑ j : Fin N,
        Real.sqrt ‖(ContinuousLinearMap.adjoint (dyadicT r hr i.val)) ∘L (dyadicT r hr j.val)‖
      ≤ (2:ℝ)^9 := by
  have hstep : ∀ j : Fin N,
      Real.sqrt ‖(ContinuousLinearMap.adjoint (dyadicT r hr i.val)) ∘L (dyadicT r hr j.val)‖
        ≤ 64 * (Real.sqrt (1/2)) ^ ((i.val - j.val) + (j.val - i.val)) := by
    intro j
    refine le_trans (Real.sqrt_le_sqrt (adjMul_pair_le r hr i.val j.val)) ?_
    rw [sqrt_const_geom]
  refine le_trans (Finset.sum_le_sum (fun j _ => hstep j)) ?_
  rw [← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left (rowsum_half_dist_le N i) (by norm_num)) ?_
  norm_num

/-- Second Schur sum bound: `∑_j √‖T_i ∘ T_j*‖ ≤ 2⁹`, uniformly in `N` and `i`. -/
lemma schur_mulAdj (r : ℝ) (hr : 0 < r) (N : ℕ) (i : Fin N) :
    ∑ j : Fin N,
        Real.sqrt ‖(dyadicT r hr i.val) ∘L (ContinuousLinearMap.adjoint (dyadicT r hr j.val))‖
      ≤ (2:ℝ)^9 := by
  have hstep : ∀ j : Fin N,
      Real.sqrt ‖(dyadicT r hr i.val) ∘L (ContinuousLinearMap.adjoint (dyadicT r hr j.val))‖
        ≤ 64 * (Real.sqrt (1/2)) ^ ((i.val - j.val) + (j.val - i.val)) := by
    intro j
    refine le_trans (Real.sqrt_le_sqrt (mulAdj_pair_le r hr i.val j.val)) ?_
    rw [sqrt_const_geom]
  refine le_trans (Finset.sum_le_sum (fun j _ => hstep j)) ?_
  rw [← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left (rowsum_half_dist_le N i) (by norm_num)) ?_
  norm_num

/-- **Cotlar–Stein operator bound.** The partial sum `∑_{j<N} T_j` of dyadic Beurling operators
has `L²` operator norm `≤ 2⁹`, uniformly in `N`. -/
lemma partialSum_opNorm_le (r : ℝ) (hr : 0 < r) (N : ℕ) :
    ‖∑ j : Fin N, dyadicT r hr j.val‖ ≤ (2:ℝ)^9 :=
  SingularIntegral.cotlarStein (fun j : Fin N => dyadicT r hr j.val) ((2:ℝ)^9) (by positivity)
    (fun i => schur_adjMul r hr N i) (fun i => schur_mulAdj r hr N i)

/-- The partial-sum kernel `∑_{j<N} ψ_j`. -/
noncomputable def partialKernel (r : ℝ) (N : ℕ) : ℂ → ℂ :=
  fun u => ∑ j : Fin N, dyadicBeurling r j.val u

/-- The partial-sum kernel lies in `L¹`. -/
lemma memLp_partialKernel (r : ℝ) (hr : 0 < r) (N : ℕ) :
    MemLp (partialKernel r N) 1 volume := by
  have heq : partialKernel r N = ∑ j : Fin N, dyadicBeurling r j.val := by
    funext u; rw [partialKernel, Finset.sum_apply]
  rw [heq]
  exact memLp_finsetSum' _ (fun j _ => memLp_dyadicBeurling r hr j.val)

/-- The coercion of a finite `Lp`-sum is a.e. the pointwise finite sum of the coercions. -/
lemma Lp_coeFn_sum {ι : Type*} (s : Finset ι) (g : ι → Lp ℂ 2 (volume : Measure ℂ)) :
    ((∑ i ∈ s, g i : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume] fun x => ∑ i ∈ s, ((g i : ℂ → ℂ) x) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact (Lp.coeFn_zero ℂ 2 (volume : Measure ℂ))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (g a) (∑ i ∈ s, g i), ih] with x hx hix
    rw [hx]
    simp only [Pi.add_apply, Finset.sum_insert ha, hix]

/-- Pointwise: convolution by the partial-sum kernel equals the sum of the dyadic
convolutions (a.e.), since each summand convolution exists a.e. -/
lemma partial_conv_eq_sum (r : ℝ) (hr : 0 < r) (N : ℕ) {F : ℂ → ℂ} (hF : MemLp F 2 volume) :
    ∀ᵐ x ∂volume,
      MeasureTheory.convolution (partialKernel r N) F (ContinuousLinearMap.mul ℂ ℂ) volume x
        = ∑ j : Fin N, MeasureTheory.convolution (dyadicBeurling r j.val) F
            (ContinuousLinearMap.mul ℂ ℂ) volume x := by
  have hex : ∀ j : Fin N, ∀ᵐ x ∂volume,
      ConvolutionExistsAt (dyadicBeurling r j.val) F x (ContinuousLinearMap.mul ℂ ℂ) volume :=
    fun j => ae_convolutionExistsAt (memLp_dyadicBeurling r hr j.val) hF
  rw [← ae_all_iff] at hex
  filter_upwards [hex] with x hx
  rw [MeasureTheory.convolution_mul]
  have heq : (fun t => partialKernel r N t * F (x - t))
      = fun t => ∑ j : Fin N, dyadicBeurling r j.val t * F (x - t) := by
    funext t; rw [partialKernel, Finset.sum_mul]
  rw [heq, integral_finsetSum]
  · exact Finset.sum_congr rfl (fun j _ => (MeasureTheory.convolution_mul ..).symm)
  · intro j _
    have hjx := hx j
    rw [ConvolutionExistsAt] at hjx
    simpa only [ContinuousLinearMap.mul_apply'] using hjx

/-- `(∑_{j<N} T_j) F =ᵐ (partialKernel r N) ⋆ F` for every `F ∈ L²`. -/
lemma sumT_apply_coeFn (r : ℝ) (hr : 0 < r) (N : ℕ) (F : Lp ℂ 2 (volume : Measure ℂ)) :
    (((∑ j : Fin N, dyadicT r hr j.val) F) : ℂ → ℂ)
      =ᵐ[volume] MeasureTheory.convolution (partialKernel r N) (F : ℂ → ℂ)
        (ContinuousLinearMap.mul ℂ ℂ) volume := by
  have hF : MemLp (F : ℂ → ℂ) 2 volume := Lp.memLp F
  have h1 : ((∑ j : Fin N, dyadicT r hr j.val) F : ℂ → ℂ)
      =ᵐ[volume] fun x => ∑ j : Fin N, ((dyadicT r hr j.val F : ℂ → ℂ) x) := by
    rw [sum_apply]
    exact Lp_coeFn_sum _ _
  have h2 : ∀ᵐ x ∂volume, ∀ j : Fin N, ((dyadicT r hr j.val F : ℂ → ℂ) x)
      = MeasureTheory.convolution (dyadicBeurling r j.val) (F : ℂ → ℂ)
        (ContinuousLinearMap.mul ℂ ℂ) volume x := by
    rw [ae_all_iff]
    exact fun j => convCLM_apply_coeFn _ _ F
  filter_upwards [h1, h2, partial_conv_eq_sum r hr N hF] with x hx1 hx2 hx3
  rw [hx1, hx3]
  exact Finset.sum_congr rfl (fun j _ => hx2 j)

/-- **Uniform `L²` bound for the partial-sum convolution.** `‖(∑_{j<N} ψ_j) ⋆ f‖₂ ≤ 2⁹ ‖f‖₂`,
uniformly in `N`; the operator translation of `partialSum_opNorm_le`. -/
lemma eLpNorm_partial_conv_le (r : ℝ) (hr : 0 < r) (N : ℕ) {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    eLpNorm (MeasureTheory.convolution (partialKernel r N) f
        (ContinuousLinearMap.mul ℂ ℂ) volume) 2 volume
      ≤ (2:ℝ≥0∞)^9 * eLpNorm f 2 volume := by
  set F : Lp ℂ 2 (volume : Measure ℂ) := hf.toLp f with hFdef
  have hFf : (F : ℂ → ℂ) =ᵐ[volume] f := hf.coeFn_toLp
  have hconv_eq : MeasureTheory.convolution (partialKernel r N) f
        (ContinuousLinearMap.mul ℂ ℂ) volume
      = MeasureTheory.convolution (partialKernel r N) (F : ℂ → ℂ)
        (ContinuousLinearMap.mul ℂ ℂ) volume :=
    MeasureTheory.convolution_congr (L := ContinuousLinearMap.mul ℂ ℂ)
      (Filter.EventuallyEq.refl _ _) hFf.symm
  have hconv_congr : MeasureTheory.convolution (partialKernel r N) f
        (ContinuousLinearMap.mul ℂ ℂ) volume
      =ᵐ[volume] (((∑ j : Fin N, dyadicT r hr j.val) F) : ℂ → ℂ) := by
    rw [hconv_eq]; exact (sumT_apply_coeFn r hr N F).symm
  rw [eLpNorm_congr_ae hconv_congr]
  have hnorm_le : ‖(∑ j : Fin N, dyadicT r hr j.val) F‖ ≤ (2:ℝ)^9 * ‖F‖ :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right (partialSum_opNorm_le r hr N) (norm_nonneg _))
  rw [Lp.norm_def] at hnorm_le
  have hFnorm : ‖F‖ = (eLpNorm f 2 volume).toReal := by rw [hFdef, Lp.norm_toLp]
  rw [hFnorm] at hnorm_le
  have h29 : (2:ℝ≥0∞)^9 = ENNReal.ofReal ((2:ℝ)^9) := by
    rw [show ((2:ℝ)^9) = (512:ℝ) by norm_num, show (2:ℝ≥0∞)^9 = (512:ℝ≥0∞) by norm_num,
      show (512:ℝ≥0∞) = ENNReal.ofReal 512 by rw [ENNReal.ofReal]; norm_num]
  have hRHSeq : (2:ℝ≥0∞)^9 * eLpNorm f 2 volume
      = ENNReal.ofReal ((2:ℝ)^9 * (eLpNorm f 2 volume).toReal) := by
    rw [ENNReal.ofReal_mul (by positivity), h29, ENNReal.ofReal_toReal hf.2.ne]
  rw [hRHSeq, ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top ((∑ j : Fin N, dyadicT r hr j.val) F))]
  apply ENNReal.ofReal_le_ofReal
  convert hnorm_le using 2

/-- Core scalar bound `‖t⁻²‖ ≤ r⁻²` whenever `r ≤ ‖t‖`. -/
lemma norminv_le (r : ℝ) (hr : 0 < r) (t : ℂ) (ht : r ≤ ‖t‖) :
    ‖(t^(-2:ℤ) : ℂ)‖ ≤ r⁻¹^2 := by
  have htpos : 0 < ‖t‖ := lt_of_lt_of_le hr ht
  rw [norm_zpow, show ((-2:ℤ)) = -(2:ℤ) by ring, zpow_neg, zpow_two, ← pow_two, inv_pow]
  apply inv_anti₀ (by positivity)
  exact pow_le_pow_left₀ hr.le ht 2

/-- The partial-sum kernel is uniformly (in `N`) bounded by `r⁻²` pointwise. -/
lemma norm_partialKernel_le (r : ℝ) (hr : 0 < r) (N : ℕ) (t : ℂ) :
    ‖partialKernel r N t‖ ≤ r⁻¹^2 := by
  classical
  unfold partialKernel
  by_cases h : ∃ j : Fin N, t ∈ {u : ℂ | (2:ℝ)^j.val * r ≤ ‖u‖ ∧ ‖u‖ < (2:ℝ)^(j.val+1) * r}
  · obtain ⟨j0, hj0⟩ := h
    rw [Finset.sum_eq_single j0]
    · rw [dyadicBeurling, Set.indicator_of_mem hj0]
      apply norminv_le r hr
      exact le_trans
        (by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j0.val), hr]) hj0.1
    · intro j _ hjne
      rw [dyadicBeurling, Set.indicator_of_notMem]
      intro hmem
      rcases lt_or_gt_of_ne (fun hc => hjne (Fin.ext hc)) with hlt | hgt
      · have h1 : (2:ℝ)^(j.val+1) * r ≤ (2:ℝ)^j0.val * r :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hr.le
        linarith [hmem.2, hj0.1, h1]
      · have h1 : (2:ℝ)^(j0.val+1) * r ≤ (2:ℝ)^j.val * r :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hr.le
        linarith [hj0.2, hmem.1, h1]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [not_exists] at h
    rw [Finset.sum_eq_zero]
    · simp only [norm_zero]; positivity
    · intro j _
      rw [dyadicBeurling, Set.indicator_of_notMem (h j)]

/-- **Pointwise convergence of the partial-sum kernel:** `∑_{j<N} ψ_j(u) → k_r(u)` for every `u`
(the dyadic annuli partition `[r,∞)`; the sum is eventually constant). -/
lemma partialKernel_tendsto (r : ℝ) (hr : 0 < r) (u : ℂ) :
    Filter.Tendsto (fun N => partialKernel r N u) Filter.atTop
      (nhds (truncBeurlingKernel r u)) := by
  apply Filter.Tendsto.congr' (f₁ := fun _ => truncBeurlingKernel r u) _ tendsto_const_nhds
  by_cases hu : r ≤ ‖u‖
  · obtain ⟨j0, hj0le, hj0lt⟩ := exists_nat_pow_near (x := ‖u‖/r) (y := 2)
      (by rw [le_div_iff₀ hr]; linarith) (by norm_num)
    have hle : (2:ℝ)^j0 * r ≤ ‖u‖ := (le_div_iff₀ hr).mp hj0le
    have hlt : ‖u‖ < (2:ℝ)^(j0+1) * r := (div_lt_iff₀ hr).mp hj0lt
    refine Filter.eventuallyEq_of_mem (s := {N | j0 + 1 ≤ N}) (Filter.mem_atTop _) ?_
    intro N hN
    simp only [Set.mem_ofPred_eq] at hN
    change truncBeurlingKernel r u = partialKernel r N u
    have hj0N : j0 < N := by omega
    rw [truncBeurlingKernel, Set.indicator_of_mem (by simpa using hu)]
    unfold partialKernel
    rw [Finset.sum_eq_single (⟨j0, hj0N⟩ : Fin N)]
    · rw [dyadicBeurling, Set.indicator_of_mem (by exact ⟨hle, hlt⟩)]
    · intro j _ hjne
      rw [dyadicBeurling, Set.indicator_of_notMem]
      simp only [Set.mem_ofPred_eq, not_and, not_lt]
      intro hjge
      have hjval : j.val ≠ j0 := fun h => hjne (Fin.ext (by simpa using h))
      rcases lt_or_gt_of_ne hjval with hlt' | hgt'
      · have hpow : (2:ℝ)^(j.val+1) * r ≤ (2:ℝ)^j0 * r :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hr.le
        linarith [le_trans hpow hle]
      · exfalso
        have hpow : (2:ℝ)^(j0+1) * r ≤ (2:ℝ)^j.val * r :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hr.le
        linarith [le_trans hpow hjge]
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Filter.eventuallyEq_of_mem (s := Set.univ) Filter.univ_mem ?_
    intro N _
    change truncBeurlingKernel r u = partialKernel r N u
    rw [truncBeurlingKernel, Set.indicator_of_notMem (by simpa using hu)]
    unfold partialKernel
    rw [Finset.sum_eq_zero]
    intro j _
    rw [dyadicBeurling, Set.indicator_of_notMem]
    simp only [Set.mem_ofPred_eq, not_and, not_lt]
    intro hge
    exfalso
    have hge' : r ≤ (2:ℝ)^j.val * r := by
      nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j.val), hr]
    linarith [le_trans hge' hge]

/-- **Convergence of the partial-sum convolutions** at every point, for `f` of bounded finite
support, via dominated convergence (uniform domination by `r⁻²‖f(x-·)‖ ∈ L¹`). -/
lemma conv_partial_tendsto (r : ℝ) (hr : 0 < r) {f : ℂ → ℂ}
    (hf : BoundedFiniteSupport f volume) (x : ℂ) :
    Filter.Tendsto (fun N => MeasureTheory.convolution (partialKernel r N) f
        (ContinuousLinearMap.mul ℂ ℂ) volume x) Filter.atTop
      (nhds (MeasureTheory.convolution (truncBeurlingKernel r) f
        (ContinuousLinearMap.mul ℂ ℂ) volume x)) := by
  have hfint : Integrable f volume := hf.integrable
  simp only [MeasureTheory.convolution_mul]
  apply tendsto_integral_of_dominated_convergence (bound := fun t => r⁻¹^2 * ‖f (x - t)‖)
  · intro n
    refine AEStronglyMeasurable.mul (memLp_partialKernel r hr n).1 ?_
    exact hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure ℂ) x)
  · exact ((hfint.comp_sub_left x).norm).const_mul _
  · intro n
    filter_upwards with t
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_partialKernel_le r hr n t) (norm_nonneg _)
  · filter_upwards with t
    exact (partialKernel_tendsto r hr t).mul_const (f (x - t))

/-- **Uniform `L²` bound for convolution against the truncated Beurling kernel.**
For every `r > 0` and every bounded, finitely-supported `f`,
`‖k_r ⋆ f‖₂ ≤ 2⁹ ‖f‖₂`, with the constant uniform in `r`.

This is the analytic heart of the Calderón–Zygmund theory of the Beurling
transform: the `L²(ℂ)→L²(ℂ)` operator norm of the singular-integral convolution
`f ↦ k_r ⋆ f`, `k_r(u) = u⁻²·1_{‖u‖≥r}`, is bounded uniformly in the truncation
scale `r`. By the dilation relation `k_r(u) = r⁻² k_1(u/r)` and the `L²`-isometric
dilation `f ↦ f(r·)` the operator `f ↦ k_r ⋆ f` is unitarily conjugate to the
single-scale operator `f ↦ k_1 ⋆ f`, so all scales share one operator norm; that
norm equals the sup of the truncated Beurling Fourier symbol `m_r(ξ) = 𝓕 k_r(ξ)`,
a function bounded uniformly in `r` (Plancherel on `Lp ℂ 2 volume`:
`‖k_r ⋆ f‖₂ = ‖m_r · 𝓕f‖₂ ≤ ‖m_r‖∞ ‖f‖₂`, with `‖m_r‖∞ = 1` the true value).
The true operator norm is `1`; the slack to `2⁹` is enormous.

PROOF: the full dyadic almost-orthogonality (Cotlar–Stein) machine is built here.
Because `k_r ∉ L¹` (its `2D` tail `∫_{|u|>r}|u|⁻²` diverges logarithmically) the
elementary Young route fails by a hair, so the bound is genuinely a *cancellation*
phenomenon. The pipeline, all proved above/in sibling files: the dyadic pieces
`ψ_j(u) = u⁻²·1_{2ʲr ≤ |u| < 2ʲ⁺¹r}` (`dyadicBeurling`) lie in `L¹`
(`memLp_dyadicBeurling`) with mass `2π log 2` uniform in `j` (`eLpNorm_dyadicBeurling`,
from the polar-coordinate annular norm `SingularIntegral.annulus_lintegral`);
`eLpNorm_convolution_le` is the Young `L¹⋆L²→L²` inequality; `convCLM` realizes
`f ↦ ψ_j ⋆ f` as a CLM on `L²` with `adjoint_convCLM` identifying its Hilbert adjoint
as convolution by `ψ̃_j(u) = conj(ψ_j(-u))`; `convCLM_comp` composes such operators;
`SingularIntegral.cotlarStein` (the abstract almost-orthogonality lemma, fully proved
in `CotlarStein.lean`) bounds `‖∑_{j<N} T_j‖ ≤ 2⁹` from the two Schur √-sum bounds
(`schur_adjMul`, `schur_mulAdj`); `eLpNorm_partial_conv_le` transports this to
`‖(∑_{j<N} ψ_j) ⋆ f‖₂ ≤ 2⁹‖f‖₂`; and `conv_partial_tendsto` + lower semicontinuity of
the `L²` norm (`Lp.eLpNorm_le_of_ae_tendsto`) pass to the `N → ∞` limit
`∑_{j<N} ψ_j ⋆ f → k_r ⋆ f`. The ONE remaining input is the deep **annular mean-zero
cancellation estimate** `truncBeurling_almostOrthogonal`
(`‖ψ̃_i ⋆ ψ_j‖₁ ≤ 16384·(1/4)^{|i-j|}`), a research-level `2D` geometric calculation
absent from Mathlib/Carleson; everything else here is proved from it. -/
lemma eLpNorm_truncBeurling_convolution_le {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : BoundedFiniteSupport f volume) :
    eLpNorm (MeasureTheory.convolution (truncBeurlingKernel r) f
        (ContinuousLinearMap.mul ℂ ℂ) volume) 2 volume
      ≤ (2 : ℝ≥0∞) ^ 9 * eLpNorm f 2 volume := by
  have hf2 : MemLp f 2 volume := hf.memLp 2
  refine MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (u := Filter.atTop)
    (f := fun N => MeasureTheory.convolution (partialKernel r N) f
      (ContinuousLinearMap.mul ℂ ℂ) volume)
    (C := (2:ℝ≥0∞)^9 * eLpNorm f 2 volume) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall (fun N => eLpNorm_partial_conv_le r hr N hf2)
  · exact fun N => (memLp_convolution_two (memLp_partialKernel r hr N) hf2).1
  · exact Filter.Eventually.of_forall (fun x => conv_partial_tendsto r hr hf x)

/-- **Single-scale `L²` bound for the truncated Beurling operator.** The truncated
Beurling operator `czOperator beurlingKernel r` (convolution against the
translation-invariant kernel `k_r(u) = u⁻² · 1_{‖u‖>r}`) is bounded `L²(ℂ) → L²(ℂ)`
with a constant `2⁹` that is *uniform in `r > 0`*.

This is the analytic core of `czOperator_beurling_strongType_L2`. By the dilation
relation `k_r(u) = r⁻² k_1(u/r)` the operator `f ↦ k_r ⋆ f` is conjugate, by the
`L²`-isometric dilation `f ↦ f(r·)`, to the single-scale operator `f ↦ k_1 ⋆ f`,
so all truncated operators share one `L²` operator norm; that single norm is the
sup of the truncated Beurling Fourier symbol `m(ξ) = 𝓕 k_1(ξ)`, a bounded function
(Plancherel: `‖k_1 ⋆ f‖₂ = ‖m · 𝓕 f‖₂ ≤ ‖m‖∞ ‖f‖₂`). The constant `2⁹` is far
from sharp; only finiteness and uniformity in `r` are used downstream.

The proof rewrites the truncated operator as the convolution `k_r ⋆ f`
(`czOperator_beurling_eq_convolution`) and applies the uniform `L²` convolution
bound `eLpNorm_truncBeurling_convolution_le`. -/
lemma eLpNorm_czOperator_beurling {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : BoundedFiniteSupport f volume) :
    eLpNorm (czOperator beurlingKernel r f) 2 volume
      ≤ (2 : ℝ≥0∞) ^ 9 * eLpNorm f 2 volume := by
  rw [czOperator_beurling_eq_convolution]
  exact eLpNorm_truncBeurling_convolution_le hr hf

/-- **Gateway `L²` bound for the truncated operator.** Each truncated Beurling
operator `czOperator beurlingKernel r` is bounded `L² → L²` with a constant
uniform in `r > 0` (`C_Ts 4`). This is the precondition `hT` threaded through the
Carleson Calderón–Zygmund machinery (`czOperator_weak_1_1`, `cotlar_estimate`,
`nontangential_from_simple`): the truncated kernel `k_r(u) = u⁻² · 1_{|u|>r}` is a
convolution kernel whose Fourier symbol is bounded uniformly in `r`. -/
lemma czOperator_beurling_strongType_L2 {r : ℝ} (hr : 0 < r) :
    HasBoundedStrongType (czOperator beurlingKernel r) 2 2 volume volume (C_Ts 4 : ℝ≥0∞) := by
  intro f hf
  refine ⟨czOperator_aestronglyMeasurable_aux hf, ?_⟩
  refine (eLpNorm_czOperator_beurling hr hf).trans ?_
  gcongr
  -- `2⁹ ≤ C_Ts 4 = 2 ^ (4 ^ 3) = 2 ^ 64`
  have hCTs : (C_Ts 4 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 64 := by
    rw [C_Ts]
    push_cast
    norm_num
  rw [hCTs]
  exact pow_le_pow_right₀ (by norm_num) (by norm_num)


/-! ## Maximal-operator `L²` bound and a.e. convergence (Theorem 1 core)

The `L²` isometry on general `μ ∈ L²` is reached from the smooth dense class by
(i) the uniform-in-`r` `L²` bound on the truncations, lifted to a maximal-operator
bound via the Carleson nontangential machinery, and (ii) the resulting a.e.
convergence of the truncations as `r → 0⁺`. The leaf lemmas build that tree. -/

/-- The truncated Beurling kernel section `1_{‖u‖≥R}·‖u‖⁻⁴` has finite mass:
`∫_{‖u‖≥R} ‖u‖⁻⁴ du < ∞` (polar coordinates, `∫_R^∞ ρ⁻³ dρ < ∞`). -/
lemma lintegral_kernelSection_lt_top (R : ℝ) (hR : 0 < R) :
    ∫⁻ u : ℂ in {u : ℂ | R ≤ ‖u‖}, ((‖u‖ₑ ^ 2)⁻¹) ^ 2 < ⊤ := by
  rw [← lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable),
    ← Complex.lintegral_comp_polarCoord_symm]
  set box : ℝ × ℝ → ENNReal := fun p =>
    (Set.Ici R ×ˢ Set.Ioo (-π) π).indicator
      (fun p => ENNReal.ofReal (p.1 * (p.1^2)⁻¹^2)) p with hbox
  have hmeas_polar : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 * (p.1^2)⁻¹^2)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_fst.mul (((measurable_fst.pow_const 2).inv).pow_const 2))
  have hbound : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • {u : ℂ | R ≤ ‖u‖}.indicator
        (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ 2) (Complex.polarCoord.symm p) ≤ box p := by
    intro p hp
    rw [polarCoord_target, Set.mem_prod] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [Set.mem_Ioi] at hp1
    simp only [hbox]
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    by_cases hmem : Complex.polarCoord.symm p ∈ {u : ℂ | R ≤ ‖u‖}
    · have hpR : R ≤ p.1 := by rw [Set.mem_ofPred_eq, hnorm] at hmem; exact hmem
      rw [Set.indicator_of_mem hmem,
        Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ici.mpr hpR, hp2⟩)]
      have henorm : ‖Complex.polarCoord.symm p‖ₑ = ENNReal.ofReal p.1 := by
        rw [← ofReal_norm, hnorm]
      rw [henorm, smul_eq_mul,
        show ((ENNReal.ofReal p.1 ^ 2)⁻¹)^2 = ENNReal.ofReal ((p.1^2)⁻¹^2) by
          rw [← ENNReal.ofReal_pow hp1.le, ← ENNReal.ofReal_inv_of_pos (by positivity),
            ← ENNReal.ofReal_pow (by positivity)],
        ← ENNReal.ofReal_mul hp1.le]
    · rw [Set.indicator_of_notMem hmem, smul_zero]; exact zero_le
  refine lt_of_le_of_lt (setLIntegral_mono
    (hmeas_polar.indicator (measurableSet_Ici.prod measurableSet_Ioo)) hbound) ?_
  calc ∫⁻ p in polarCoord.target, box p
      ≤ ∫⁻ p, box p := setLIntegral_le_lintegral _ _
    _ = ∫⁻ p in (Set.Ici R ×ˢ Set.Ioo (-π) π), ENNReal.ofReal (p.1 * (p.1^2)⁻¹^2) := by
          rw [hbox, lintegral_indicator (measurableSet_Ici.prod measurableSet_Ioo)]
    _ < ⊤ := by
          rw [Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ hmeas_polar.aemeasurable]
          simp only [setLIntegral_const]
          rw [lintegral_mul_const' _ _ (by rw [Real.volume_Ioo]; finiteness)]
          apply ENNReal.mul_lt_top _ (by rw [Real.volume_Ioo]; finiteness)
          have hint : IntegrableOn (fun r : ℝ => r * (r^2)⁻¹^2) (Set.Ici R) volume := by
            have heq : (fun r : ℝ => r * (r^2)⁻¹^2) =ᶠ[ae (volume.restrict (Set.Ici R))]
                (fun r : ℝ => r^(-3 : ℝ)) := by
              filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
              simp only [Set.mem_Ici] at hr
              have hrpos : 0 < r := lt_of_lt_of_le hR hr
              rw [Real.rpow_neg hrpos.le, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
              field_simp
            rw [integrableOn_congr_fun_ae heq, integrableOn_Ici_iff_integrableOn_Ioi,
              integrableOn_Ioi_rpow_iff hR]
            norm_num
          have hfin := hint.2
          rw [hasFiniteIntegral_iff_enorm] at hfin
          refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun x hx => ?_)) hfin
          · exact (measurable_id.mul (((measurable_id.pow_const 2).inv).pow_const 2)).enorm
          · simp only [Set.mem_Ici] at hx
            have hxpos : 0 < x := lt_of_lt_of_le hR hx
            rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]


/-- **Kernel section is `L²`.** For `R > 0` the truncated Beurling kernel
`y ↦ 1_{(ball x R)ᶜ}(y)·(x-y)⁻²` lies in `L²(ℂ)`. -/
lemma memLp_kernelSection (x : ℂ) (R : ℝ) (hR : 0 < R) :
    MemLp (fun y => (Metric.ball x R)ᶜ.indicator (fun y => beurlingKernel x y) y) 2 volume := by
  have hmeas : AEStronglyMeasurable
      (fun y => (Metric.ball x R)ᶜ.indicator (fun y => beurlingKernel x y) y) volume := by
    apply AEStronglyMeasurable.indicator _ measurableSet_ball.compl
    apply Measurable.aestronglyMeasurable
    unfold beurlingKernel; fun_prop
  refine ⟨hmeas, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  simp_rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  -- ∫⁻ ‖indicator ...‖ₑ^2 = ∫⁻_{(ball x R)ᶜ} ‖beurlingKernel x y‖ₑ^2
  have hpt : ∀ y, ‖(Metric.ball x R)ᶜ.indicator (fun y => beurlingKernel x y) y‖ₑ ^ 2
      = (Metric.ball x R)ᶜ.indicator (fun y => ‖beurlingKernel x y‖ₑ ^ 2) y := by
    intro y
    by_cases h : y ∈ (Metric.ball x R)ᶜ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, enorm_zero]; ring
  refine lt_of_eq_of_lt (lintegral_congr hpt) ?_
  rw [lintegral_indicator measurableSet_ball.compl]
  -- bound ‖beurlingKernel x y‖ₑ^2 ≤ ((‖x-y‖ₑ^2)⁻¹)^2
  have hkb : ∀ y, ‖beurlingKernel x y‖ₑ ^ 2 ≤ ((‖x - y‖ₑ ^ 2)⁻¹) ^ 2 := by
    intro y
    apply pow_le_pow_left'
    by_cases h : x = y
    · subst h; simp [beurlingKernel]
    · have hne : x - y ≠ 0 := sub_ne_zero.mpr h
      have he : beurlingKernel x y = ((x-y) * (x-y))⁻¹ := by rw [beurlingKernel, zpow_neg, zpow_two]
      rw [he, enorm_inv (mul_ne_zero hne hne), enorm_mul, sq]
  refine lt_of_le_of_lt (setLIntegral_mono ?_ (fun y _ => hkb y)) ?_
  · fun_prop
  -- now ∫⁻_{(ball x R)ᶜ} ((‖x-y‖ₑ^2)⁻¹)^2 = ∫⁻_{‖u‖≥R} ((‖u‖ₑ^2)⁻¹)^2 via u = x - y
  rw [← lintegral_indicator measurableSet_ball.compl]
  have hsub : (fun y => (Metric.ball x R)ᶜ.indicator (fun y => ((‖x - y‖ₑ ^ 2)⁻¹) ^ 2) y)
      = (fun y => {u : ℂ | R ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ 2) (x - y)) := by
    funext y
    have hiff : (y ∈ (Metric.ball x R)ᶜ) ↔ (x - y ∈ {u : ℂ | R ≤ ‖u‖}) := by
      rw [Set.mem_compl_iff, Metric.mem_ball, not_lt, Set.mem_ofPred_eq, dist_comm, Complex.dist_eq]
    by_cases h : y ∈ (Metric.ball x R)ᶜ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]
  rw [hsub, lintegral_sub_left_eq_self
    (fun u => {u : ℂ | R ≤ ‖u‖}.indicator (fun u => ((‖u‖ₑ ^ 2)⁻¹) ^ 2) u) x]
  rw [lintegral_indicator (measurableSet_le measurable_const continuous_norm.measurable)]
  exact lintegral_kernelSection_lt_top R hR

/-- **Integrability of the truncated Beurling integrand.** For `f ∈ L²` the
integrand `y ↦ (x-y)⁻² f(y)` is integrable over `(ball x r)ᶜ` (Hölder: the kernel
section is `L²` by `memLp_kernelSection`, `f ∈ L²`, product `∈ L¹`). -/
lemma integrableOn_beurlingKernel_mul {r : ℝ} (hr : 0 < r) (x : ℂ) {f : ℂ → ℂ}
    (hf : MemLp f 2 volume) :
    IntegrableOn (fun y => beurlingKernel x y * f y) (Metric.ball x r)ᶜ volume := by
  have hker : MemLp (fun y => (Metric.ball x r)ᶜ.indicator (fun y => beurlingKernel x y) y) 2
      volume := memLp_kernelSection x r hr
  rw [IntegrableOn]
  have h1 : MemLp (fun y => beurlingKernel x y) 2 (volume.restrict (Metric.ball x r)ᶜ) := by
    apply MemLp.ae_eq _ (hker.restrict (Metric.ball x r)ᶜ)
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with y hy
    rw [Set.indicator_of_mem hy]
  exact h1.integrable_mul (hf.restrict _)

/-- **`L²`-linearity of the truncated Beurling operator.** For `f, g ∈ L²`,
`czOperator beurlingKernel r (f - g) = czOperator beurlingKernel r f
  - czOperator beurlingKernel r g` pointwise (integrability from
`integrableOn_beurlingKernel_mul`). -/
lemma czOperator_beurling_sub {r : ℝ} (hr : 0 < r) (x : ℂ) {f g : ℂ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    czOperator beurlingKernel r (f - g) x
      = czOperator beurlingKernel r f x - czOperator beurlingKernel r g x := by
  have h1 := integrableOn_beurlingKernel_mul hr x hf
  have h2 := integrableOn_beurlingKernel_mul hr x hg
  unfold czOperator
  rw [← integral_sub h1 h2]
  refine setIntegral_congr_fun measurableSet_ball.compl (fun y _ => ?_)
  simp only [Pi.sub_apply]; ring

/-- **Cauchy–Schwarz bound for the truncated operator.** Pointwise,
`‖czOperator beurlingKernel R h x‖ ≤ ‖kernel section‖₂ · ‖h‖₂`, the bounded-linear
estimate that makes `czOperator beurlingKernel R · x` `L²`-continuous in `h`. -/
lemma enorm_czOperator_beurling_le_mul {R : ℝ} (_hR : 0 < R) (x : ℂ) {h : ℂ → ℂ}
    (hh : MemLp h 2 volume) :
    ‖czOperator beurlingKernel R h x‖ₑ
      ≤ eLpNorm (fun y => (Metric.ball x R)ᶜ.indicator (fun y => beurlingKernel x y) y) 2 volume
        * eLpNorm h 2 volume := by
  unfold czOperator
  have hcs : ∫⁻ y in (Metric.ball x R)ᶜ, ‖beurlingKernel x y‖ₑ * ‖h y‖ₑ
      ≤ eLpNorm (fun y => beurlingKernel x y) 2 (volume.restrict (Metric.ball x R)ᶜ)
        * eLpNorm h 2 (volume.restrict (Metric.ball x R)ᶜ) := by
    have := ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm
      (μ := volume.restrict (Metric.ball x R)ᶜ)
      (p := 2) (q := 2) ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
      (f := fun y => ‖beurlingKernel x y‖ₑ) (g := fun y => ‖h y‖ₑ)
      (by unfold beurlingKernel; fun_prop) hh.aestronglyMeasurable.enorm.restrict
    simpa [eLpNorm_enorm] using this
  calc ‖∫ y in (Metric.ball x R)ᶜ, beurlingKernel x y * h y‖ₑ
      ≤ ∫⁻ y in (Metric.ball x R)ᶜ, ‖beurlingKernel x y * h y‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y in (Metric.ball x R)ᶜ, ‖beurlingKernel x y‖ₑ * ‖h y‖ₑ := by simp_rw [enorm_mul]
    _ ≤ eLpNorm (fun y => beurlingKernel x y) 2 (volume.restrict (Metric.ball x R)ᶜ)
          * eLpNorm h 2 (volume.restrict (Metric.ball x R)ᶜ) := hcs
    _ ≤ eLpNorm (fun y => (Metric.ball x R)ᶜ.indicator (fun y => beurlingKernel x y) y) 2 volume
          * eLpNorm h 2 volume := by
        refine mul_le_mul' ?_ ?_
        · exact le_of_eq (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.compl).symm
        · exact eLpNorm_restrict_le h 2 volume _

/-- **Maximal-operator `L²` bound on the smooth dense class.** For `f` smooth with
compact support (`BoundedFiniteSupport`), the simple nontangential (maximal
truncated) Beurling operator is bounded `L² → L²` with constant `C10_1_6 4`
(`simple_nontangential_operator_le`, threading the uniform truncation bound). -/
lemma eLpNorm_simpleNontangential_beurling_le {f : ℂ → ℂ} (hf : BoundedFiniteSupport f volume) :
    eLpNorm (simpleNontangentialOperator beurlingKernel 0 f) 2 volume
      ≤ (C10_1_6 4 : ℝ≥0∞) * eLpNorm f 2 volume :=
  (simple_nontangential_operator_le (a := 4) (by norm_num)
    (fun r hr => czOperator_beurling_strongType_L2 hr) (le_refl 0) f hf).2

/-- `eLpNorm`-convergence from `eLpNorm`-difference convergence: if
`‖f - gₙ‖₂ → 0` then `‖gₙ‖₂ → ‖f‖₂` (reverse triangle, `ℝ≥0∞` squeeze). -/
lemma tendsto_eLpNorm_of_tendsto_sub {f : ℂ → ℂ} {g : ℕ → ℂ → ℂ}
    (hf : MemLp f 2 volume) (hg : ∀ n, MemLp (g n) 2 volume)
    (htend : Tendsto (fun n => eLpNorm (f - g n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (g n) 2 volume) atTop (𝓝 (eLpNorm f 2 volume)) := by
  set L := eLpNorm f 2 volume with hL
  set d := fun n => eLpNorm (f - g n) 2 volume with hd
  have hupper : ∀ n, eLpNorm (g n) 2 volume ≤ L + d n := by
    intro n
    have h : eLpNorm (g n) 2 volume ≤ eLpNorm f 2 volume + eLpNorm (g n - f) 2 volume := by
      calc eLpNorm (g n) 2 volume = eLpNorm (f + (g n - f)) 2 volume := by
            congr 1; funext x; simp
        _ ≤ eLpNorm f 2 volume + eLpNorm (g n - f) 2 volume :=
            eLpNorm_add_le hf.aestronglyMeasurable ((hg n).sub hf).aestronglyMeasurable one_le_two
    rw [hL, hd]
    rw [show eLpNorm (g n - f) 2 volume = eLpNorm (f - g n) 2 volume from by
      rw [← eLpNorm_neg]; congr 1; funext x; simp] at h
    exact h
  have hlower : ∀ n, L - d n ≤ eLpNorm (g n) 2 volume := by
    intro n
    rw [tsub_le_iff_right]
    calc L = eLpNorm ((g n) + (f - g n)) 2 volume := by rw [hL]; congr 1; funext x; simp
      _ ≤ eLpNorm (g n) 2 volume + eLpNorm (f - g n) 2 volume :=
          eLpNorm_add_le (hg n).aestronglyMeasurable (hf.sub (hg n)).aestronglyMeasurable one_le_two
  have hupper' : Tendsto (fun n => L + d n) atTop (𝓝 L) := by
    simpa using tendsto_const_nhds.add htend
  have hlower' : Tendsto (fun n => L - d n) atTop (𝓝 L) := by
    simpa using (ENNReal.Tendsto.sub (a := L) (b := 0) tendsto_const_nhds htend (Or.inr (by simp)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower' hupper' hlower hupper

/-- A smooth compactly supported `L²`-approximating sequence: for `f ∈ L²` there is
a sequence `gₙ ∈ C^∞_c` with `‖f - gₙ‖₂ → 0` (`MemLp.exist_eLpNorm_sub_le`). -/
lemma exists_contDiff_seq_tendsto_L2 {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    ∃ g : ℕ → ℂ → ℂ, (∀ n, ContDiff ℝ (⊤:ℕ∞) (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      Tendsto (fun n => eLpNorm (f - g n) 2 volume) atTop (𝓝 0) := by
  choose g hgc hgsmooth hgle using fun n : ℕ =>
    hf.exist_eLpNorm_sub_le (by norm_num) one_le_two (ε := 1/(n+1)) (by positivity)
  refine ⟨g, hgsmooth, hgc, ?_⟩
  have hto0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1/(n+1))) atTop (𝓝 0) := by
    rw [show (0:ℝ≥0∞) = ENNReal.ofReal 0 by simp]
    refine ENNReal.tendsto_ofReal (Tendsto.div_atTop tendsto_const_nhds ?_)
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto0
    (fun n => zero_le) hgle

/-- `BoundedFiniteSupport` for a smooth compactly supported function. -/
lemma boundedFiniteSupport_of_contDiff {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) : BoundedFiniteSupport g volume :=
  ⟨hg.continuous.memLp_top_of_hasCompactSupport hgc volume,
   lt_of_le_of_lt (measure_mono (subset_tsupport g)) hgc.measure_lt_top⟩

/-- **Per-point lower-semicontinuity of the truncation.** For fixed `R > 0`, `x'`,
the value `‖czOperator beurlingKernel R f x'‖` is `≤ liminf` of the corresponding
values for an `L²`-approximating sequence (Cauchy–Schwarz `L²`-continuity in `f`). -/
lemma enorm_czOperator_le_liminf {R : ℝ} (hR : 0 < R) (x' : ℂ) {f : ℂ → ℂ} {g : ℕ → ℂ → ℂ}
    (hf : MemLp f 2 volume) (hg : ∀ n, MemLp (g n) 2 volume)
    (htend : Tendsto (fun n => eLpNorm (f - g n) 2 volume) atTop (𝓝 0)) :
    ‖czOperator beurlingKernel R f x'‖ₑ
      ≤ liminf (fun n => ‖czOperator beurlingKernel R (g n) x'‖ₑ) atTop := by
  set C := eLpNorm
    (fun y => (Metric.ball x' R)ᶜ.indicator (fun y => beurlingKernel x' y) y) 2 volume
    with hC
  have hbd : ∀ n, ‖czOperator beurlingKernel R f x'‖ₑ
      ≤ ‖czOperator beurlingKernel R (g n) x'‖ₑ + C * eLpNorm (f - g n) 2 volume := by
    intro n
    have hsub : ‖czOperator beurlingKernel R f x' - czOperator beurlingKernel R (g n) x'‖ₑ
        ≤ C * eLpNorm (f - g n) 2 volume := by
      rw [← czOperator_beurling_sub hR x' hf (hg n)]
      exact enorm_czOperator_beurling_le_mul hR x' (hf.sub (hg n))
    calc ‖czOperator beurlingKernel R f x'‖ₑ
        ≤ ‖czOperator beurlingKernel R (g n) x'‖ₑ
          + ‖czOperator beurlingKernel R f x' - czOperator beurlingKernel R (g n) x'‖ₑ := by
            rw [add_comm]
            exact le_trans (by rw [sub_add_cancel]) (enorm_add_le _ _)
      _ ≤ _ := by gcongr
  have hCne : C ≠ ⊤ := by rw [hC]; exact (memLp_kernelSection x' R hR).2.ne
  have hC0 : Tendsto (fun n => C * eLpNorm (f - g n) 2 volume) atTop (𝓝 0) := by
    simpa using (ENNReal.Tendsto.const_mul htend (Or.inr hCne))
  calc ‖czOperator beurlingKernel R f x'‖ₑ
      ≤ liminf (fun n => ‖czOperator beurlingKernel R (g n) x'‖ₑ
          + C * eLpNorm (f - g n) 2 volume) atTop :=
        le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall hbd)
    _ = liminf (fun n => ‖czOperator beurlingKernel R (g n) x'‖ₑ) atTop :=
        ENNReal.liminf_add_of_right_tendsto_zero hC0 _

/-- **Maximal-operator `L²` bound on all of `L²`.** The simple nontangential
Beurling operator is bounded `L² → L²` (constant `C10_1_6 4`) for every `f ∈ L²`,
extended from the smooth dense class by per-point lower semicontinuity and Fatou. -/
lemma eLpNorm_simpleNontangential_beurling_le_L2 {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    eLpNorm (simpleNontangentialOperator beurlingKernel 0 f) 2 volume
      ≤ (C10_1_6 4 : ℝ≥0∞) * eLpNorm f 2 volume := by
  obtain ⟨g, hgsmooth, hgc, htend⟩ := exists_contDiff_seq_tendsto_L2 hf
  have hg : ∀ n, MemLp (g n) 2 volume := fun n =>
    (hgsmooth n).continuous.memLp_of_hasCompactSupport (hgc n)
  have hgBFS : ∀ n, BoundedFiniteSupport (g n) volume := fun n =>
    boundedFiniteSupport_of_contDiff (hgsmooth n) (hgc n)
  -- per-point: simpleNTO 0 f x ≤ liminf (simpleNTO 0 gₙ x)
  have hsup : ∀ x, simpleNontangentialOperator beurlingKernel 0 f x
      ≤ liminf (fun n => simpleNontangentialOperator beurlingKernel 0 (g n) x) atTop := by
    intro x
    unfold simpleNontangentialOperator
    refine iSup_le (fun R => iSup_le (fun hR => iSup_le (fun x' => iSup_le (fun hx' => ?_))))
    refine le_trans (enorm_czOperator_le_liminf hR x' hf hg htend) ?_
    refine liminf_le_liminf (Eventually.of_forall (fun n => ?_))
    exact le_iSup_of_le R (le_iSup_of_le hR (le_iSup_of_le x' (le_iSup_of_le hx' (le_refl _))))
  -- BFS bound on gₙ
  have hgbd : ∀ n, eLpNorm (simpleNontangentialOperator beurlingKernel 0 (g n)) 2 volume
      ≤ (C10_1_6 4 : ℝ≥0∞) * eLpNorm (g n) 2 volume := fun n =>
    eLpNorm_simpleNontangential_beurling_le (hgBFS n)
  -- ‖gₙ‖₂ → ‖f‖₂
  have htnorm : Tendsto (fun n => (C10_1_6 4 : ℝ≥0∞) * eLpNorm (g n) 2 volume) atTop
      (𝓝 ((C10_1_6 4 : ℝ≥0∞) * eLpNorm f 2 volume)) := by
    refine ENNReal.Tendsto.const_mul (tendsto_eLpNorm_of_tendsto_sub hf hg htend) ?_
    right; exact ENNReal.coe_ne_top
  -- Fatou
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, one_div]
  have hpowliminf : ∀ (u : ℕ → ℝ≥0∞),
      liminf (fun n => (u n) ^ (2:ℝ)) atTop = (liminf u atTop) ^ (2:ℝ) := by
    intro u
    have hmono : Monotone (fun x : ℝ≥0∞ => x ^ (2:ℝ)) :=
      fun a b h => ENNReal.rpow_le_rpow h (by norm_num)
    exact (hmono.map_liminf_of_continuousAt u (ENNReal.continuous_rpow_const).continuousAt).symm
  have hmono : ∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 f x‖ₑ ^ (2:ℝ)
      ≤ liminf (fun n => ∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 (g n) x‖ₑ ^ (2:ℝ))
        atTop := by
    have hle : ∀ x, ‖simpleNontangentialOperator beurlingKernel 0 f x‖ₑ ^ (2:ℝ)
        ≤ liminf (fun n => ‖simpleNontangentialOperator beurlingKernel 0 (g n) x‖ₑ ^ (2:ℝ))
          atTop := by
      intro x
      simp_rw [enorm_eq_self]
      rw [hpowliminf]
      gcongr
      exact hsup x
    refine le_trans (lintegral_mono hle) ?_
    refine lintegral_liminf_le (fun n => ?_)
    exact (lowerSemicontinuous_simpleNontangentialOperator.measurable).enorm.pow_const _
  calc (∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 f x‖ₑ ^ (2:ℝ)) ^ (2:ℝ)⁻¹
      ≤ (liminf (fun n => ∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 (g n) x‖ₑ ^ (2:ℝ))
          atTop) ^ (2:ℝ)⁻¹ := by gcongr
    _ = liminf (fun n => (∫⁻ x, ‖simpleNontangentialOperator beurlingKernel 0 (g n) x‖ₑ ^ (2:ℝ))
          ^ (2:ℝ)⁻¹) atTop := by
        have hmono2 : Monotone (fun x : ℝ≥0∞ => x ^ (2:ℝ)⁻¹) :=
          fun a b h => ENNReal.rpow_le_rpow h (by norm_num)
        exact hmono2.map_liminf_of_continuousAt _ (ENNReal.continuous_rpow_const).continuousAt
    _ = liminf (fun n => eLpNorm (simpleNontangentialOperator beurlingKernel 0 (g n)) 2 volume)
          atTop := by
        congr 1; funext n
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
        simp only [ENNReal.toReal_ofNat, one_div]
    _ ≤ liminf (fun n => (C10_1_6 4 : ℝ≥0∞) * eLpNorm (g n) 2 volume) atTop :=
        liminf_le_liminf (Eventually.of_forall hgbd)
    _ = (C10_1_6 4 : ℝ≥0∞) * eLpNorm f 2 volume := htnorm.liminf_eq


/-- **Pointwise domination by the maximal operator.** For `R > 0`,
`‖czOperator beurlingKernel R f x‖ ≤ simpleNontangentialOperator beurlingKernel 0 f x`
(take the supremand at scale `R`, centre `x ∈ ball x R`). -/
lemma enorm_czOperator_le_simpleNontangential {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) (x : ℂ) :
    ‖czOperator beurlingKernel R f x‖ₑ ≤ simpleNontangentialOperator beurlingKernel 0 f x := by
  unfold simpleNontangentialOperator
  exact le_iSup_of_le R (le_iSup_of_le hR (le_iSup_of_le x
    (le_iSup_of_le (Metric.mem_ball_self hR) (le_refl _))))

/-- **Uniform-in-`r` `L²` bound for the truncations on all of `L²`.** For every
`f ∈ L²` and `r > 0`, `‖czOperator beurlingKernel r f‖₂ ≤ C10_1_6 4 · ‖f‖₂`
(pointwise domination by the maximal operator, then `eLpNorm_simpleNontangential…`). -/
lemma eLpNorm_czOperator_beurling_L2 {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    eLpNorm (czOperator beurlingKernel r f) 2 volume ≤ (C10_1_6 4 : ℝ≥0∞) * eLpNorm f 2 volume := by
  refine le_trans (eLpNorm_mono_enorm (fun x => ?_)) (eLpNorm_simpleNontangential_beurling_le_L2 hf)
  exact enorm_czOperator_le_simpleNontangential hr f x

/-- The truncations are `AEStronglyMeasurable` for `f ∈ L²`. -/
lemma aestronglyMeasurable_czOperator_beurling {r : ℝ} {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    AEStronglyMeasurable (czOperator beurlingKernel r f) volume :=
  czOperator_aestronglyMeasurable hf.aestronglyMeasurable

/-- The truncations lie in `L²` for `f ∈ L²` (`r > 0`). -/
lemma memLp_czOperator_beurling {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (czOperator beurlingKernel r f) 2 volume :=
  ⟨aestronglyMeasurable_czOperator_beurling hf,
   lt_of_le_of_lt (eLpNorm_czOperator_beurling_L2 hr hf)
     (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩

/-- **Smooth pointwise convergence of the truncations to the Beurling transform.**
For `ν ∈ C¹_c`, the truncated Beurling integrals converge as `r → 0⁺` to
`-π · beurling ν`. (Own helper, proved from `czOperator_beurling_tendsto_smooth`;
distinct from the untouched `beurling_ae_tendsto_smooth`.) -/
lemma czOperator_beurling_tendsto_neg_pi {ν : ℂ → ℂ} (hν : ContDiff ℝ 1 ν)
    (hνc : HasCompactSupport ν) (w : ℂ) :
    Filter.Tendsto (fun r => czOperator beurlingKernel r ν w) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * beurling ν w)) := by
  have h := czOperator_beurling_tendsto_smooth hν hνc w
  have hval : (∫ ζ, (dz ν ζ) / (ζ - w)) = -(π : ℂ) * beurling ν w := by
    have hlim : limUnder (𝓝[>] (0:ℝ))
        (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν w)
        = (∫ ζ, (dz ν ζ) / (ζ - w)) := by
      apply Filter.Tendsto.limUnder_eq
      have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r ν w
          = czOperator beurlingKernel r ν w := fun r => rfl
      simpa only [hcz] using h
    have hb : beurling ν w = -(1 / (π : ℂ)) * (∫ ζ, (dz ν ζ) / (ζ - w)) := by
      rw [beurling, hlim]
    rw [hb]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rwa [hval] at h

/-- `simpleNontangentialOperator beurlingKernel 0 g ∈ L²` for `g ∈ L²`. -/
lemma memLp_simpleNontangential_beurling {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    MemLp (simpleNontangentialOperator beurlingKernel 0 g) 2 volume :=
  ⟨aestronglyMeasurable_simpleNontangentialOperator,
   lt_of_le_of_lt (eLpNorm_simpleNontangential_beurling_le_L2 hg)
     (ENNReal.mul_lt_top ENNReal.coe_lt_top hg.2)⟩

/-- **Chebyshev bound for the maximal Beurling operator.** The level set
`{simpleNontangentialOperator beurlingKernel 0 g ≥ a}` has measure
`≤ a⁻² (C10_1_6 4 · ‖g‖₂)²` (Markov–Chebyshev + the maximal `L²` bound). -/
lemma volume_simpleNontangential_ge_le {g : ℂ → ℂ} (hg : MemLp g 2 volume) {a : ℝ≥0∞}
    (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    volume {z | a ≤ simpleNontangentialOperator beurlingKernel 0 g z}
      ≤ a⁻¹ ^ 2 * ((C10_1_6 4 : ℝ≥0∞) * eLpNorm g 2 volume) ^ 2 := by
  have hcheb := meas_ge_le_mul_pow_eLpNorm_enorm volume (p := 2) (by norm_num) (by norm_num)
    (f := simpleNontangentialOperator beurlingKernel 0 g)
    aestronglyMeasurable_simpleNontangentialOperator (ε := a) ha (fun h => absurd h ha')
  simp only [ENNReal.toReal_ofNat, enorm_eq_self] at hcheb
  rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, ENNReal.rpow_natCast] at hcheb
  refine le_trans hcheb (mul_le_mul' (le_refl (a⁻¹ ^ 2)) ?_)
  exact pow_le_pow_left' (eLpNorm_simpleNontangential_beurling_le_L2 hg) 2

/-- **A net Cauchy criterion via `edist`.** If for every `ε > 0` the values
`F r` are eventually within `edist < ε` of each other (along `𝓝[>] 0` squared),
then `F` converges (completeness of `ℂ`). -/
lemma tendsto_of_cauchy_edist {F : ℝ → ℂ}
    (hcauchy : ∀ ε : ℝ≥0∞, 0 < ε →
      ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)), edist (F p.1) (F p.2) < ε) :
    ∃ L, Tendsto F (𝓝[>] (0:ℝ)) (𝓝 L) := by
  have hC : Cauchy (map F (𝓝[>] (0:ℝ))) := by
    rw [cauchy_map_iff]
    refine ⟨by infer_instance, ?_⟩
    rw [(uniformity_basis_edist).tendsto_right_iff]
    intro ε hε
    exact hcauchy ε hε
  obtain ⟨L, hL⟩ := CompleteSpace.complete hC
  exact ⟨L, hL⟩

/-- **Oscillation control by the maximal operator.** For `f, ν ∈ L²`,
`edist (czOp r₁ f z) (czOp r₂ f z) ≤ edist (czOp r₁ ν z) (czOp r₂ ν z)
  + 2·simpleNontangentialOperator beurlingKernel 0 (f - ν) z`. -/
lemma edist_czOperator_oscillation {f ν : ℂ → ℂ} (hf : MemLp f 2 volume) (hν : MemLp ν 2 volume)
    (z : ℂ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    edist (czOperator beurlingKernel r₁ f z) (czOperator beurlingKernel r₂ f z)
      ≤ edist (czOperator beurlingKernel r₁ ν z) (czOperator beurlingKernel r₂ ν z)
        + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
  have hd1 : czOperator beurlingKernel r₁ f z - czOperator beurlingKernel r₁ ν z
      = czOperator beurlingKernel r₁ (f - ν) z := (czOperator_beurling_sub hr₁ z hf hν).symm
  have hd2 : czOperator beurlingKernel r₂ f z - czOperator beurlingKernel r₂ ν z
      = czOperator beurlingKernel r₂ (f - ν) z := (czOperator_beurling_sub hr₂ z hf hν).symm
  set Sf1 := czOperator beurlingKernel r₁ f z
  set Sf2 := czOperator beurlingKernel r₂ f z
  set Sn1 := czOperator beurlingKernel r₁ ν z
  set Sn2 := czOperator beurlingKernel r₂ ν z
  have hb1 : edist Sf1 Sn1 ≤ simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
    rw [edist_eq_enorm_sub, hd1]; exact enorm_czOperator_le_simpleNontangential hr₁ (f - ν) z
  have hb2 : edist Sn2 Sf2 ≤ simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
    rw [edist_comm, edist_eq_enorm_sub, hd2]
    exact enorm_czOperator_le_simpleNontangential hr₂ (f - ν) z
  calc edist Sf1 Sf2 ≤ edist Sf1 Sn1 + edist Sn1 Sn2 + edist Sn2 Sf2 := by
        refine le_trans (edist_triangle Sf1 Sn2 Sf2) ?_
        gcongr
        exact edist_triangle Sf1 Sn1 Sn2
    _ = edist Sn1 Sn2 + (edist Sf1 Sn1 + edist Sn2 Sf2) := by ring
    _ ≤ edist Sn1 Sn2 + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z := by
        gcongr; rw [two_mul]; gcongr

/-- **Per-point Cauchy from smooth convergence + small maximal value.** If
`czOp · ν z` converges and `2·simpleNontangentialOperator beurlingKernel 0 (f-ν) z
< a/2`, then `edist (czOp p.1 f z) (czOp p.2 f z) < a` eventually. -/
lemma eventually_edist_lt_of_smooth_conv {f ν : ℂ → ℂ} (hf : MemLp f 2 volume)
    (hν : MemLp ν 2 volume) (z : ℂ) {a : ℝ≥0∞} (ha : 0 < a)
    (hconv : ∃ L, Tendsto (fun r => czOperator beurlingKernel r ν z) (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hsmall : 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z < a / 2) :
    ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
      edist (czOperator beurlingKernel p.1 f z) (czOperator beurlingKernel p.2 f z) < a := by
  obtain ⟨L, hL⟩ := hconv
  have hνcauchy : ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
      edist (czOperator beurlingKernel p.1 ν z) (czOperator beurlingKernel p.2 ν z) < a / 2 := by
    have hmap : Tendsto (fun p : ℝ × ℝ =>
        (czOperator beurlingKernel p.1 ν z, czOperator beurlingKernel p.2 ν z))
        ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) (𝓝 (L, L)) :=
      (hL.comp tendsto_fst).prodMk_nhds (hL.comp tendsto_snd)
    have ht : Tendsto (fun p : ℝ × ℝ =>
        edist (czOperator beurlingKernel p.1 ν z) (czOperator beurlingKernel p.2 ν z))
        ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ))) (𝓝 (edist L L)) :=
      (continuous_edist.tendsto _).comp hmap
    rw [edist_self] at ht
    exact ht (Iio_mem_nhds (ENNReal.half_pos (ne_of_gt ha)))
  have hpos : ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)), 0 < p.1 ∧ 0 < p.2 := by
    rw [eventually_prod_iff]
    refine ⟨fun r => 0 < r, ?_, fun r => 0 < r, ?_, fun {r₁} h1 {r₂} h2 => ⟨h1, h2⟩⟩
    · exact eventually_mem_of_tendsto_nhdsWithin tendsto_id |>.mono (fun x hx => hx)
    · exact eventually_mem_of_tendsto_nhdsWithin tendsto_id |>.mono (fun x hx => hx)
  filter_upwards [hνcauchy, hpos] with p hp hppos
  obtain ⟨hp1, hp2⟩ := hppos
  calc edist (czOperator beurlingKernel p.1 f z) (czOperator beurlingKernel p.2 f z)
      ≤ edist (czOperator beurlingKernel p.1 ν z) (czOperator beurlingKernel p.2 ν z)
        + 2 * simpleNontangentialOperator beurlingKernel 0 (f - ν) z :=
        edist_czOperator_oscillation hf hν z hp1 hp2
    _ < a / 2 + a / 2 := ENNReal.add_lt_add hp hsmall
    _ = a := ENNReal.add_halves a

/-- **Null oscillation set.** For `f ∈ L²` and `a > 0`, the set where the
truncations fail to be `edist`-Cauchy at level `a` is null. The smooth dense
approximants converge everywhere (`czOperator_beurling_tendsto_neg_pi`), so the
bad set sits inside `{simpleNontangentialOperator beurlingKernel 0 (f-gₙ) ≥ a/4}`,
whose measure `→ 0` as `gₙ → f` in `L²` (Chebyshev). -/
lemma volume_oscillation_set_eq_zero {f : ℂ → ℂ} (hf : MemLp f 2 volume) {a : ℝ≥0∞}
    (ha : 0 < a) (ha' : a ≠ ⊤) :
    volume {z | ¬ ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
      edist (czOperator beurlingKernel p.1 f z) (czOperator beurlingKernel p.2 f z) < a} = 0 := by
  set b := a / 4 with hb
  have hbpos : 0 < b := ENNReal.div_pos (ne_of_gt ha) (by norm_num)
  have hbne : b ≠ 0 := ne_of_gt hbpos
  have hbtop : b ≠ ⊤ := (ENNReal.div_lt_top ha' (by norm_num)).ne
  obtain ⟨g, hgsmooth, hgc, htend⟩ := exists_contDiff_seq_tendsto_L2 hf
  have hg : ∀ n, MemLp (g n) 2 volume := fun n =>
    (hgsmooth n).continuous.memLp_of_hasCompactSupport (hgc n)
  set B := {z | ¬ ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
      edist (czOperator beurlingKernel p.1 f z) (czOperator beurlingKernel p.2 f z) < a} with hBdef
  have hsubset : ∀ n, B ⊆ {z | b ≤ simpleNontangentialOperator beurlingKernel 0 (f - g n) z} := by
    intro n z hz
    by_contra hlt
    rw [Set.mem_ofPred_eq, not_le] at hlt
    apply hz
    refine eventually_edist_lt_of_smooth_conv hf (hg n) z ha
      ⟨_, czOperator_beurling_tendsto_neg_pi ((hgsmooth n).of_le (by exact_mod_cast le_top))
        (hgc n) z⟩ ?_
    rw [hb] at hlt
    calc 2 * simpleNontangentialOperator beurlingKernel 0 (f - g n) z
        < 2 * (a / 4) := by gcongr; exact (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
      _ = a / 2 := by
          rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, mul_comm (2:ℝ≥0∞) a, mul_assoc]
          congr 1
          rw [show (4:ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num),
            ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hmeas : ∀ n, volume B ≤ b⁻¹ ^ 2 * ((C10_1_6 4 : ℝ≥0∞) * eLpNorm (f - g n) 2 volume) ^ 2 :=
    fun n => le_trans (measure_mono (hsubset n))
      (volume_simpleNontangential_ge_le (hf.sub (hg n)) hbne hbtop)
  have hto0 : Tendsto (fun n => b⁻¹ ^ 2 * ((C10_1_6 4 : ℝ≥0∞) * eLpNorm (f - g n) 2 volume) ^ 2)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (C10_1_6 4 : ℝ≥0∞) * eLpNorm (f - g n) 2 volume) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul htend (Or.inr ENNReal.coe_ne_top)
    have h2 : Tendsto (fun n => ((C10_1_6 4 : ℝ≥0∞) * eLpNorm (f - g n) 2 volume) ^ 2) atTop
        (𝓝 0) := by
      have h := (ENNReal.continuous_pow 2).continuousAt.tendsto.comp h1
      rw [show ((0:ℝ≥0∞)^2) = 0 by norm_num] at h
      exact h
    have hbinv : b⁻¹ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hbne)
    have h3 := ENNReal.Tendsto.const_mul (a := b⁻¹ ^ 2) h2 (Or.inr hbinv)
    rw [mul_zero] at h3
    exact h3
  exact le_antisymm (ge_of_tendsto hto0 (Eventually.of_forall hmeas)) (zero_le)

/-- **A.e. existence of the principal-value limit.** For every `f ∈ L²` the
truncated Beurling integrals `czOperator beurlingKernel r f z` converge as
`r → 0⁺` for almost every `z` (maximal-operator + dense-class a.e. convergence). -/
lemma czOperator_beurling_ae_tendsto {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    ∀ᵐ z ∂volume, ∃ L, Tendsto (fun r => czOperator beurlingKernel r f z) (𝓝[>] (0:ℝ)) (𝓝 L) := by
  set Bk := fun k : ℕ => {z | ¬ ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ (𝓝[>] (0:ℝ)),
      edist (czOperator beurlingKernel p.1 f z) (czOperator beurlingKernel p.2 f z)
        < 1/((k:ℝ≥0∞)+1)} with hBk
  have hBknull : ∀ k, volume (Bk k) = 0 := by
    intro k
    apply volume_oscillation_set_eq_zero hf
    · apply ENNReal.div_pos one_ne_zero
      exact (ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top k, ENNReal.one_lt_top⟩).ne
    · apply ENNReal.div_ne_top ENNReal.one_ne_top
      have hkp : (0:ℝ≥0∞) < (k:ℝ≥0∞)+1 := by positivity
      exact hkp.ne'
  have hunionnull : volume (⋃ k, Bk k) = 0 := measure_iUnion_null hBknull
  rw [ae_iff]
  refine measure_mono_null ?_ hunionnull
  intro z hz
  rw [Set.mem_ofPred_eq] at hz
  rw [Set.mem_iUnion]
  by_contra hnot
  push Not at hnot
  apply hz
  apply tendsto_of_cauchy_edist
  intro ε hε
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hε)
  have hmem := hnot k
  simp only [hBk, Set.mem_ofPred_eq, not_not] at hmem
  refine hmem.mono (fun p hp => lt_of_lt_of_le hp ?_)
  rw [one_div]
  calc ((k:ℝ≥0∞)+1)⁻¹ ≤ ((k:ℝ≥0∞))⁻¹ := ENNReal.inv_le_inv.mpr le_self_add
    _ ≤ ε := le_of_lt hk

/-- **A.e. convergence to the Beurling transform.** For `f ∈ L²`, the truncated
integrals converge a.e. as `r → 0⁺` to `-π · beurling f`. Where the limit exists
(`czOperator_beurling_ae_tendsto`) it pins the defining `limUnder`, identifying
`beurling f z` with `-(1/π)·(a.e. limit)`. -/
lemma czOperator_beurling_ae_tendsto_neg_pi {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    ∀ᵐ z ∂volume, Tendsto (fun r => czOperator beurlingKernel r f z) (𝓝[>] (0:ℝ))
      (𝓝 (-(π:ℂ) * beurling f z)) := by
  filter_upwards [czOperator_beurling_ae_tendsto hf] with z hz
  obtain ⟨L, hL⟩ := hz
  have hlim : limUnder (𝓝[>] (0:ℝ))
      (fun r => czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r f z) = L := by
    apply Filter.Tendsto.limUnder_eq
    have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r f z
        = czOperator beurlingKernel r f z := fun r => rfl
    simpa only [hcz] using hL
  have hb : beurling f z = -(1 / (π : ℂ)) * L := by rw [beurling, hlim]
  have hval : -(π:ℂ) * beurling f z = L := by
    rw [hb]; have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [hval]; exact hL

/-- **`Lᵖ`-bound shape for the Beurling transform (`p = 2`).** `eLpNorm (beurling h) 2
≤ (C10_1_6 4 / π) · eLpNorm h 2` for `h ∈ L²` — Fatou applied to the uniformly
`L²`-bounded truncations along a sequence `rₙ → 0⁺`, using the a.e. limit
`-π·beurling h`. (`AEStronglyMeasurable (beurling h)` follows.) -/
lemma eLpNorm_beurling_le {h : ℂ → ℂ} (hh : MemLp h 2 volume) :
    eLpNorm (beurling h) 2 volume
      ≤ (C10_1_6 4 : ℝ≥0∞) * (ENNReal.ofReal π)⁻¹ * eLpNorm h 2 volume := by
  set r : ℕ → ℝ := fun n => 1/(n+1:ℝ) with hr
  have hrpos : ∀ n, 0 < r n := fun n => by rw [hr]; positivity
  have hrto : Tendsto r atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨Tendsto.div_atTop tendsto_const_nhds
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop), ?_⟩
    filter_upwards with n; simp only [Set.mem_Ioi, hr]; positivity
  have hbound : ∀ n, eLpNorm (czOperator beurlingKernel (r n) h) 2 volume
      ≤ (C10_1_6 4 : ℝ≥0∞) * eLpNorm h 2 volume :=
    fun n => eLpNorm_czOperator_beurling_L2 (hrpos n) hh
  have hmeas : ∀ n, AEStronglyMeasurable (czOperator beurlingKernel (r n) h) volume :=
    fun n => aestronglyMeasurable_czOperator_beurling hh
  have hae : ∀ᵐ z ∂volume, Tendsto (fun n => czOperator beurlingKernel (r n) h z) atTop
      (𝓝 (-(π:ℂ) * beurling h z)) := by
    filter_upwards [czOperator_beurling_ae_tendsto_neg_pi hh] with z hz
    exact hz.comp hrto
  have hfatou := Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hbound) hmeas hae
  have heq : eLpNorm (fun z => -(π:ℂ) * beurling h z) 2 volume
      = ENNReal.ofReal π * eLpNorm (beurling h) 2 volume := by
    have he : (fun z => -(π:ℂ) * beurling h z) = (-(π:ℂ)) • (beurling h) := by
      funext z; simp [Pi.smul_apply, smul_eq_mul]
    rw [he, eLpNorm_const_smul]
    congr 1
    rw [← ofReal_norm, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [heq] at hfatou
  -- π · ‖Th‖ ≤ C ‖h‖  ⟹  ‖Th‖ ≤ C π⁻¹ ‖h‖
  have hπpos : (0:ℝ≥0∞) < ENNReal.ofReal π := by simp [Real.pi_pos]
  have hπtop : ENNReal.ofReal π ≠ ⊤ := ENNReal.ofReal_ne_top
  have hπne : ENNReal.ofReal π ≠ 0 := ne_of_gt hπpos
  calc eLpNorm (beurling h) 2 volume
      = (ENNReal.ofReal π)⁻¹ * (ENNReal.ofReal π * eLpNorm (beurling h) 2 volume) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hπne hπtop, one_mul]
    _ ≤ (ENNReal.ofReal π)⁻¹ * ((C10_1_6 4 : ℝ≥0∞) * eLpNorm h 2 volume) := by gcongr
    _ = (C10_1_6 4 : ℝ≥0∞) * (ENNReal.ofReal π)⁻¹ * eLpNorm h 2 volume := by ring

/-- **A.e. additivity of the Beurling transform.** For `f, g ∈ L²`,
`beurling (f - g) =ᵐ beurling f - beurling g` (the truncations are linear and all
three limits exist a.e.). -/
lemma beurling_sub_ae {f g : ℂ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    beurling (f - g) =ᵐ[volume] fun z => beurling f z - beurling g z := by
  filter_upwards [czOperator_beurling_ae_tendsto_neg_pi hf,
    czOperator_beurling_ae_tendsto_neg_pi hg,
    czOperator_beurling_ae_tendsto_neg_pi (hf.sub hg)] with z hzf hzg hzfg
  have hlin : ∀ᶠ r in 𝓝[>] (0:ℝ), czOperator beurlingKernel r (f - g) z
      = czOperator beurlingKernel r f z - czOperator beurlingKernel r g z := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact czOperator_beurling_sub hr z hf hg
  have hsub : Tendsto (fun r => czOperator beurlingKernel r (f - g) z) (𝓝[>] (0:ℝ))
      (𝓝 (-(π:ℂ) * beurling f z - -(π:ℂ) * beurling g z)) := by
    refine (hzf.sub hzg).congr' ?_
    filter_upwards [hlin] with r hr; exact hr.symm
  have huniq := tendsto_nhds_unique hzfg hsub
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hmul : -(π:ℂ) * beurling (f - g) z = -(π:ℂ) * (beurling f z - beurling g z) := by
    rw [huniq]; ring
  exact mul_left_cancel₀ (by simp [hπ]) hmul

/-- `AEStronglyMeasurable (beurling f)` for `f ∈ L²` (it is `-(1/π)` times the a.e.
limit of the measurable truncations). -/
lemma aestronglyMeasurable_beurling {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    AEStronglyMeasurable (beurling f) volume := by
  set r : ℕ → ℝ := fun n => 1/(n+1:ℝ) with hr
  have hrpos : ∀ n, 0 < r n := fun n => by rw [hr]; positivity
  have hrto : Tendsto r atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨Tendsto.div_atTop tendsto_const_nhds
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop), ?_⟩
    filter_upwards with n; simp only [Set.mem_Ioi, hr]; positivity
  have hae : ∀ᵐ z ∂volume, Tendsto (fun n => czOperator beurlingKernel (r n) f z) atTop
      (𝓝 (-(π:ℂ) * beurling f z)) := by
    filter_upwards [czOperator_beurling_ae_tendsto_neg_pi hf] with z hz
    exact hz.comp hrto
  have hmeas : AEStronglyMeasurable (fun z => -(π:ℂ) * beurling f z) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => aestronglyMeasurable_czOperator_beurling hf) hae
  have heq : beurling f = fun z => (-(1/(π:ℂ))) * (-(π:ℂ) * beurling f z) := by
    funext z
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [heq]
  exact hmeas.const_mul _

/-- `beurling f ∈ L²` for `f ∈ L²`. -/
lemma memLp_beurling {f : ℂ → ℂ} (hf : MemLp f 2 volume) : MemLp (beurling f) 2 volume :=
  ⟨aestronglyMeasurable_beurling hf,
   lt_of_le_of_lt (eLpNorm_beurling_le hf)
     (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
       (by simp [ENNReal.inv_lt_top, Real.pi_pos])) hf.2)⟩

/-- **`L²` bound for the Beurling transform of a difference.** For `f, ν ∈ L²`,
`eLpNorm (beurling f - beurling ν) 2 ≤ (C10_1_6 4 / π) · ‖f - ν‖₂` (`beurling_sub_ae`
turns the difference into `beurling (f - ν)`, then `eLpNorm_beurling_le`). -/
lemma eLpNorm_beurling_sub_le {f ν : ℂ → ℂ} (hf : MemLp f 2 volume) (hν : MemLp ν 2 volume) :
    eLpNorm (fun z => beurling f z - beurling ν z) 2 volume
      ≤ (C10_1_6 4 : ℝ≥0∞) * (ENNReal.ofReal π)⁻¹ * eLpNorm (f - ν) 2 volume := by
  rw [← eLpNorm_congr_ae (beurling_sub_ae hf hν)]
  exact eLpNorm_beurling_le (hf.sub hν)

/-- **`L²` isometry.** `‖Tμ‖₂ = ‖μ‖₂`: the Beurling transform is an `L²`
isometry, its Fourier multiplier `ξ̄/ξ` having modulus one. -/
theorem beurling_l2_isometry (hμ : MemLp μ 2 volume) :
    eLpNorm (beurling μ) 2 volume = eLpNorm μ 2 volume := by
  set Cst : ℝ≥0∞ := (C10_1_6 4 : ℝ≥0∞) * (ENNReal.ofReal π)⁻¹ with hCst
  have hCsttop : Cst ≠ ⊤ := by
    rw [hCst]
    exact (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (by simp [ENNReal.inv_lt_top, Real.pi_pos])).ne
  set A := (eLpNorm (beurling μ) 2 volume).toReal with hA
  set B := (eLpNorm μ 2 volume).toReal with hB
  set Cr : ℝ := Cst.toReal with hCr
  have hCrnn : 0 ≤ Cr := ENNReal.toReal_nonneg
  have hAf : eLpNorm (beurling μ) 2 volume ≠ ⊤ := (memLp_beurling hμ).2.ne
  have hBf : eLpNorm μ 2 volume ≠ ⊤ := hμ.2.ne
  -- main estimate: |A - B| ≤ (Cr + 1) * ε for all ε > 0
  have hmain : ∀ ε : ℝ, 0 < ε → |A - B| ≤ (Cr + 1) * ε := by
    intro ε hε
    obtain ⟨ν, hνc, hνsmooth, hνle⟩ :=
      hμ.exist_eLpNorm_sub_le (by norm_num) one_le_two (ε := ε) hε
    have hνmem : MemLp ν 2 volume := hνsmooth.continuous.memLp_of_hasCompactSupport hνc
    -- smooth isometry
    have hiso : eLpNorm (beurling ν) 2 volume = eLpNorm ν 2 volume :=
      beurling_l2_isometry_smooth hνsmooth hνc
    -- ‖μ - ν‖₂ ≤ ε
    have hsubnorm : eLpNorm (μ - ν) 2 volume ≤ ENNReal.ofReal ε := hνle
    -- ‖Tμ - Tν‖₂ ≤ Cst * ‖μ - ν‖₂ ≤ Cst * ε
    have hTsub : eLpNorm (fun z => beurling μ z - beurling ν z) 2 volume
        ≤ Cst * ENNReal.ofReal ε := by
      refine le_trans (eLpNorm_beurling_sub_le hμ hνmem) ?_
      rw [hCst]; gcongr
    -- Now convert to ℝ.  Let Nν := ‖ν‖₂.toReal = ‖Tν‖₂.toReal.
    set Nν := (eLpNorm ν 2 volume).toReal with hNν
    have hνf : eLpNorm ν 2 volume ≠ ⊤ := hνmem.2.ne
    -- |A - Nν| ≤ Cr ε  (from triangle both ways)
    have hub1 : eLpNorm (beurling μ) 2 volume ≤ eLpNorm (beurling ν) 2 volume
        + eLpNorm (fun z => beurling μ z - beurling ν z) 2 volume := by
      calc eLpNorm (beurling μ) 2 volume
          = eLpNorm (beurling ν + (fun z => beurling μ z - beurling ν z)) 2 volume := by
            congr 1; funext z; simp
        _ ≤ _ := eLpNorm_add_le (memLp_beurling hνmem).1
            ((memLp_beurling hμ).sub (memLp_beurling hνmem)).1 one_le_two
    have hub2 : eLpNorm (beurling ν) 2 volume ≤ eLpNorm (beurling μ) 2 volume
        + eLpNorm (fun z => beurling μ z - beurling ν z) 2 volume := by
      calc eLpNorm (beurling ν) 2 volume
          = eLpNorm (beurling μ - (fun z => beurling μ z - beurling ν z)) 2 volume := by
            congr 1; funext z; simp
        _ ≤ eLpNorm (beurling μ) 2 volume
            + eLpNorm (fun z => beurling μ z - beurling ν z) 2 volume :=
            eLpNorm_sub_le (memLp_beurling hμ).1
              ((memLp_beurling hμ).sub (memLp_beurling hνmem)).1 one_le_two
    -- toReal: A ≤ Nν + Cr ε  and Nν ≤ A + Cr ε
    have hCstε : (Cst * ENNReal.ofReal ε).toReal = Cr * ε := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le, hCr]
    have hTsubR : (eLpNorm (fun z => beurling μ z - beurling ν z) 2 volume).toReal ≤ Cr * ε := by
      rw [← hCstε]
      exact ENNReal.toReal_mono (by finiteness) hTsub
    have hTsubfin : eLpNorm (fun z => beurling μ z - beurling ν z) 2 volume ≠ ⊤ :=
      ne_top_of_le_ne_top (by finiteness) hTsub
    have hAub : A ≤ Nν + Cr * ε := by
      rw [hA, hNν, ← hiso]
      refine le_trans (ENNReal.toReal_mono ?_ hub1) ?_
      · exact ENNReal.add_ne_top.mpr ⟨(memLp_beurling hνmem).2.ne, hTsubfin⟩
      · rw [ENNReal.toReal_add (memLp_beurling hνmem).2.ne hTsubfin]
        gcongr
    have hNνub : Nν ≤ A + Cr * ε := by
      rw [hNν, hA, ← hiso]
      refine le_trans (ENNReal.toReal_mono ?_ hub2) ?_
      · exact ENNReal.add_ne_top.mpr ⟨(memLp_beurling hμ).2.ne, hTsubfin⟩
      · rw [ENNReal.toReal_add (memLp_beurling hμ).2.ne hTsubfin]
        gcongr
    -- |Nν - B| ≤ ε
    have hμνR : (eLpNorm (μ - ν) 2 volume).toReal ≤ ε :=
      le_trans (ENNReal.toReal_mono (by finiteness) hsubnorm) (by rw [ENNReal.toReal_ofReal hε.le])
    have hμνfin : eLpNorm (μ - ν) 2 volume ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hsubnorm
    have hNνB1 : Nν ≤ B + ε := by
      rw [hNν, hB]
      have : eLpNorm ν 2 volume ≤ eLpNorm μ 2 volume + eLpNorm (μ - ν) 2 volume := by
        calc eLpNorm ν 2 volume = eLpNorm (μ - (μ - ν)) 2 volume := by congr 1; funext z; simp
          _ ≤ _ := eLpNorm_sub_le hμ.1 (hμ.sub hνmem).1 one_le_two
      refine le_trans (ENNReal.toReal_mono (by finiteness) this) ?_
      rw [ENNReal.toReal_add hBf hμνfin]; gcongr
    have hNνB2 : B ≤ Nν + ε := by
      rw [hNν, hB]
      have : eLpNorm μ 2 volume ≤ eLpNorm ν 2 volume + eLpNorm (μ - ν) 2 volume := by
        calc eLpNorm μ 2 volume = eLpNorm (ν + (μ - ν)) 2 volume := by congr 1; funext z; simp
          _ ≤ _ := eLpNorm_add_le hνmem.1 (hμ.sub hνmem).1 one_le_two
      refine le_trans (ENNReal.toReal_mono (by finiteness) this) ?_
      rw [ENNReal.toReal_add hνf hμνfin]; gcongr
    -- combine: |A - B| ≤ |A - Nν| + |Nν - B| ≤ Cr ε + ε ≤ (Cr+1) ε
    have h1 : |A - Nν| ≤ Cr * ε := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |Nν - B| ≤ ε := abs_le.mpr ⟨by linarith, by linarith⟩
    calc |A - B| ≤ |A - Nν| + |Nν - B| := by
          rw [show A - B = (A - Nν) + (Nν - B) by ring]; exact abs_add_le _ _
      _ ≤ Cr * ε + ε := add_le_add h1 h2
      _ = (Cr + 1) * ε := by ring
  -- from |A - B| ≤ (Cr+1) ε for all ε ⟹ A = B ⟹ eLpNorm equal
  have hAB : A = B := by
    have h0 : |A - B| ≤ 0 := by
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      rw [zero_add]
      calc |A - B| ≤ (Cr+1) * (ε / (Cr+1)) := hmain _ (by positivity)
        _ = ε := by field_simp
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _)))
  rw [← ENNReal.toReal_eq_toReal_iff' hAf hBf]; exact hAB

end NoWanderingDomains
