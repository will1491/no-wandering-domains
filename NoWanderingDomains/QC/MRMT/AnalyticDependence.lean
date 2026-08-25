/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.MRMT.NeumannSeries.PrincipalSolution
import NoWanderingDomains.QC.MRMT.SmoothCase.Stability

/-!
# Holomorphic dependence of the principal solution on the coefficient

Along the complex one-parameter family `t ↦ t·μ` of Beltrami coefficients, the
principal solutions depend holomorphically on `t`: for each point `z`, the map
`t ↦ f^{t·μ}(z)` is analytic on the parameter region `{t | ‖t‖·‖μ‖∞ < 1}`.

This is read off the Neumann series: the fixed point of `u ↦ t·μ·S u + t·μ` is the
power series `h_t = ∑ₙ t^{n+1}·(μ·S)^n μ` in `Lᵖ`, and pairing with the Cauchy
kernel at `z` — a bounded functional on the compactly vanishing fields — produces a
convergent power series for `f^{t·μ}(z) − z`. Around a parameter `t₀` with
`‖t₀‖·‖μ‖∞ < 1` an exponent `p(t₀)` with a contraction margin covers a neighborhood,
and the local series glue by uniqueness of principal solutions.

This is the interface for holomorphic motions of solutions along holomorphic
families of coefficients.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology

namespace NoWanderingDomains

/-- **Scaling a Beltrami coefficient** along the complex parameter `t`, on the
region `‖t‖·‖μ‖∞ < 1` where the scaled coefficient is again admissible. -/
noncomputable def BeltramiCoeff.scale (b : BeltramiCoeff) (t : ℂ)
    (ht : ‖t‖ * b.normInf < 1) : BeltramiCoeff where
  μ := fun z => t * b.μ z
  measurable := measurable_const.mul b.measurable
  bound := by
    have hne : eLpNormEssSup b.μ volume ≠ ⊤ := b.bound.trans_le le_top |>.ne
    have hself : eLpNormEssSup b.μ volume = ENNReal.ofReal b.normInf := by
      rw [BeltramiCoeff.normInf, ENNReal.ofReal_toReal hne]
    have hsmul : (fun z => t * b.μ z) = fun z => t • b.μ z := by
      funext z; simp [smul_eq_mul]
    calc eLpNormEssSup (fun z => t * b.μ z) volume
        = eLpNormEssSup (fun z => t • b.μ z) volume := by rw [hsmul]
      _ = ‖t‖ₑ * eLpNormEssSup b.μ volume := by
          rw [show (fun z => t • b.μ z) = t • b.μ from rfl,
            MeasureTheory.eLpNormEssSup_const_smul]
      _ = ENNReal.ofReal ‖t‖ * ENNReal.ofReal b.normInf := by
          rw [hself, ofReal_norm]
      _ = ENNReal.ofReal (‖t‖ * b.normInf) :=
          (ENNReal.ofReal_mul (norm_nonneg t)).symm
      _ < 1 := ENNReal.ofReal_lt_one.mpr ht

/-- The coefficient of `BeltramiCoeff.scale` is the pointwise scaling. -/
theorem BeltramiCoeff.scale_μ (b : BeltramiCoeff) (t : ℂ) (ht : ‖t‖ * b.normInf < 1) :
    (b.scale t ht).μ = fun z => t * b.μ z := rfl

/-- **Holomorphic dependence of the principal solution on the parameter.** For a
compactly vanishing coefficient `b`, there is a family `F` of principal solutions
of the scaled coefficients `t·μ`, defined on the region `‖t‖·‖μ‖∞ < 1`, such that
for every point `z` the evaluation `t ↦ F t z` is analytic on that region. -/
theorem mrmt_holomorphic_dependence_principal (b : BeltramiCoeff) {R : ℝ}
    (hsupp : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0) :
    ∃ F : ℂ → ℂ → ℂ,
      (∀ (t : ℂ) (ht : ‖t‖ * b.normInf < 1),
        IsPrincipalSolution (b.scale t ht) (F t)) ∧
      ∀ z : ℂ, AnalyticOnNhd ℂ (fun t => F t z) {t : ℂ | ‖t‖ * b.normInf < 1} := by
  -- Chunk B (transplanted): analyticity of a scalar power series with
  -- geometrically bounded coefficients.
  have depChunkB : ∀ (a : ℕ → ℂ) (M ρ : ℝ), 0 ≤ ρ →
      (∀ n : ℕ, ‖a n‖ ≤ M * ρ ^ n) →
      ∀ t₀ : ℂ, ‖t₀‖ * ρ < 1 →
        AnalyticAt ℂ (fun t : ℂ => ∑' n : ℕ, t ^ (n + 1) * a n) t₀ := by
    intro a M ρ hρ hbound t₀ ht₀
    have hM : 0 ≤ M := le_trans (norm_nonneg (a 0)) (by simpa using hbound 0)
    -- pick a radius `r` strictly above `‖t₀‖` with `r * ρ ≤ 1`
    obtain ⟨r, hr₁, hr₂⟩ : ∃ r : ℝ, ‖t₀‖ < r ∧ r * ρ ≤ 1 := by
      rcases eq_or_lt_of_le hρ with hρ0 | hρpos
      · exact ⟨‖t₀‖ + 1, by linarith, by rw [← hρ0, mul_zero]; norm_num⟩
      · have hinv : ‖t₀‖ < ρ⁻¹ := by
          have h2 : ‖t₀‖ * ρ * ρ⁻¹ < 1 * ρ⁻¹ :=
            mul_lt_mul_of_pos_right ht₀ (inv_pos.mpr hρpos)
          rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hρpos), mul_one, one_mul] at h2
        refine ⟨(‖t₀‖ + ρ⁻¹) / 2, by linarith, ?_⟩
        have hrle : (‖t₀‖ + ρ⁻¹) / 2 ≤ ρ⁻¹ := by linarith
        calc (‖t₀‖ + ρ⁻¹) / 2 * ρ ≤ ρ⁻¹ * ρ := mul_le_mul_of_nonneg_right hrle hρ
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hρpos)
    have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg t₀) hr₁
    -- the scalar power series with coefficients `a`
    have hle : ENNReal.ofReal r ≤ (FormalMultilinearSeries.ofScalars ℂ a).radius := by
      have hb : ∀ n : ℕ, ‖FormalMultilinearSeries.ofScalars ℂ a n‖ * (r.toNNReal : ℝ) ^ n ≤ M := by
        intro n
        rw [FormalMultilinearSeries.ofScalars_norm ℂ a n, Real.coe_toNNReal r hr0.le]
        calc ‖a n‖ * r ^ n ≤ M * ρ ^ n * r ^ n :=
              mul_le_mul_of_nonneg_right (hbound n) (pow_nonneg hr0.le n)
          _ = M * (ρ * r) ^ n := by rw [mul_pow]; ring
          _ ≤ M * 1 := mul_le_mul_of_nonneg_left
              (pow_le_one₀ (mul_nonneg hρ hr0.le) (by rw [mul_comm]; exact hr₂)) hM
          _ = M := mul_one M
      exact (FormalMultilinearSeries.ofScalars ℂ a).le_radius_of_bound M hb
    have hrad_pos : 0 < (FormalMultilinearSeries.ofScalars ℂ a).radius :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hr0) hle
    -- `t₀` lies in the eball of convergence
    have hmem : t₀ ∈ Metric.eball (0 : ℂ) (FormalMultilinearSeries.ofScalars ℂ a).radius := by
      apply Metric.eball_subset_eball hle
      rw [Metric.mem_eball, edist_lt_ofReal, dist_zero_right]
      exact hr₁
    -- the sum of the series is analytic at `t₀`
    have hsum_an : AnalyticAt ℂ (FormalMultilinearSeries.ofScalars ℂ a).sum t₀ :=
      ((FormalMultilinearSeries.ofScalars ℂ a).hasFPowerSeriesOnBall
        hrad_pos).analyticAt_of_mem hmem
    -- identify the target function with `t * sum` of the series
    have hfun : (fun t : ℂ => ∑' n : ℕ, t ^ (n + 1) * a n)
        = fun t : ℂ => t * (FormalMultilinearSeries.ofScalars ℂ a).sum t := by
      funext t
      have hps : (FormalMultilinearSeries.ofScalars ℂ a).sum t = ∑' n : ℕ, a n * t ^ n := by
        have h := FormalMultilinearSeries.ofScalars_sum_eq a t
        simp only [smul_eq_mul] at h
        exact h
      calc ∑' n : ℕ, t ^ (n + 1) * a n
          = ∑' n : ℕ, t * (a n * t ^ n) := tsum_congr fun n => by ring
        _ = t * ∑' n : ℕ, a n * t ^ n := tsum_mul_left
        _ = t * (FormalMultilinearSeries.ofScalars ℂ a).sum t := by rw [hps]
    rw [hfun]
    exact analyticAt_id.mul hsum_an
  -- Chunk C1 (transplanted): a principal solution for the scaled coefficient,
  -- given pointwise by the Neumann power series in the parameter.
  have depChunkC1 : ∀ (b : BeltramiCoeff) (R : ℝ),
      (∀ z : ℂ, R < ‖z‖ → b.μ z = 0) →
      ∀ (p : ℝ≥0∞) (C : ℝ), 2 < p → p ≠ ⊤ →
        IsCalderonZygmundBound beurling p C →
        ∀ (t : ℂ) (ht : ‖t‖ * b.normInf < 1), ‖t‖ * b.normInf * C < 1 →
          ∃ f : ℂ → ℂ, IsPrincipalSolution (b.scale t ht) f ∧
            ∀ z : ℂ, f z = z + ∑' n : ℕ,
              t ^ (n + 1) * cauchyTransform ((fun v w => b.μ w * beurling v w)^[n] b.μ) z := by
    intro b R hsupp p C hp hp2 hCb t ht hcontr
    classical
    have hC0 : 0 ≤ C := hCb.1
    have hCbound := hCb.2
    -- Basic constants and memberships for the unscaled coefficient.
    have hμfin : eLpNormEssSup b.μ volume ≠ ⊤ := (lt_trans b.bound ENNReal.one_lt_top).ne
    have hessSup_eq : eLpNormEssSup b.μ volume = ENNReal.ofReal b.normInf := by
      rw [BeltramiCoeff.normInf, ENNReal.ofReal_toReal hμfin]
    have hμLinf : MemLp b.μ ⊤ volume := by
      refine ⟨b.measurable.aestronglyMeasurable, ?_⟩
      rw [eLpNorm_exponent_top]
      exact lt_of_le_of_ne le_top hμfin
    have hμLp : MemLp b.μ p volume :=
      memLp_of_eLpNormEssSup_ne_top_of_support hp2 b.measurable hμfin hsupp
    -- `L²` membership of compactly vanishing `Lᵖ` fields (finite-measure embedding).
    have hL2 : ∀ u : ℂ → ℂ, MemLp u p volume → (∀ z : ℂ, R < ‖z‖ → u z = 0) →
        MemLp u 2 volume := by
      intro u hu husupp
      have hBmeas : MeasurableSet (Metric.closedBall (0 : ℂ) (max R 0)) :=
        measurableSet_closedBall
      have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) (max R 0))) :=
        ⟨by
          rw [Measure.restrict_apply_univ]
          exact (isCompact_closedBall _ _).measure_lt_top⟩
      have hind : u = (Metric.closedBall (0 : ℂ) (max R 0)).indicator u := by
        funext ζ
        by_cases hζ : ζ ∈ Metric.closedBall (0 : ℂ) (max R 0)
        · rw [Set.indicator_of_mem hζ]
        · rw [Set.indicator_of_notMem hζ]
          refine husupp ζ ?_
          have hm : max R 0 < ‖ζ‖ := by
            simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hζ
          exact lt_of_le_of_lt (le_max_left R 0) hm
      rw [hind]
      exact (memLp_indicator_iff_restrict hBmeas).2
        ((hu.restrict _).mono_exponent hp.le)
    -- The scaled multiplier.
    set tμ : ℂ → ℂ := fun z => t * b.μ z with htμ_def
    have htμmeas : Measurable tμ := measurable_const.mul b.measurable
    have htμsupp : ∀ z : ℂ, R < ‖z‖ → tμ z = 0 := by
      intro z hz
      change t * b.μ z = 0
      rw [hsupp z hz, mul_zero]
    have hesstμ : eLpNormEssSup tμ volume = ENNReal.ofReal (‖t‖ * b.normInf) := by
      have hsmul : tμ = t • b.μ := by
        funext z
        change t * b.μ z = (t • b.μ) z
        rw [Pi.smul_apply, smul_eq_mul]
      calc eLpNormEssSup tμ volume
          = eLpNormEssSup (t • b.μ) volume := by rw [hsmul]
        _ = ‖t‖ₑ * eLpNormEssSup b.μ volume :=
            MeasureTheory.eLpNormEssSup_const_smul t b.μ
        _ = ENNReal.ofReal ‖t‖ * ENNReal.ofReal b.normInf := by
            rw [hessSup_eq, ofReal_norm]
        _ = ENNReal.ofReal (‖t‖ * b.normInf) := (ENNReal.ofReal_mul (norm_nonneg t)).symm
    have htμfin : eLpNormEssSup tμ volume ≠ ⊤ := by
      rw [hesstμ]
      exact ENNReal.ofReal_ne_top
    have htμreal : (eLpNormEssSup tμ volume).toReal = ‖t‖ * b.normInf := by
      rw [hesstμ, ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg t) b.normInf_nonneg)]
    have hcontr' : (eLpNormEssSup tμ volume).toReal * C < 1 := by
      rw [htμreal]
      exact hcontr
    have htμLp : MemLp tμ p volume :=
      memLp_of_eLpNormEssSup_ne_top_of_support hp2 htμmeas htμfin htμsupp
    -- The `Lᵖ` fixed point for the scaled coefficient.
    obtain ⟨h, hLp, haeeq, _hbound⟩ :=
      exists_lp_fixedPoint_beltrami hp hp2 htμmeas htμfin hCb hcontr' htμLp
    -- The everywhere-defined representative, vanishing pointwise outside the ball.
    set h' : ℂ → ℂ := fun z => tμ z * beurling h z + tμ z with hh'_def
    have hh'ae : h' =ᵐ[volume] h := haeeq.symm
    have hh'Lp : MemLp h' p volume := hLp.ae_eq haeeq
    have hh'supp : ∀ z : ℂ, R < ‖z‖ → h' z = 0 := by
      intro z hz
      change tμ z * beurling h z + tμ z = 0
      rw [htμsupp z hz, zero_mul, zero_add]
    have hL2h' : MemLp h' 2 volume := hL2 h' hh'Lp hh'supp
    have hL2h : MemLp h 2 volume := hL2h'.ae_eq hh'ae
    have hSeq : beurling h =ᵐ[volume] beurling h' := beurling_congr_ae hL2h hL2h' haeeq
    have heq' : h' =ᵐ[volume] fun z => tμ z * beurling h' z + tμ z := by
      filter_upwards [hSeq] with z hz
      change tμ z * beurling h z + tμ z = tμ z * beurling h' z + tμ z
      rw [hz]
    -- The principal-solution bundle.
    have hprin : IsPrincipalSolution (b.scale t ht) (fun z => z + cauchyTransform h' z) :=
      ⟨p, h', R, hp, hp2, hh'Lp, hh'supp, heq', fun z => rfl⟩
    -- The iterated fields.
    set T : (ℂ → ℂ) → ℂ → ℂ := fun v w => b.μ w * beurling v w with hT_def
    set g : ℕ → ℂ → ℂ := fun n => T^[n] b.μ with hg_def
    have hg_zero : g 0 = b.μ := Function.iterate_zero_apply T b.μ
    have hg_succ : ∀ n : ℕ, g (n + 1) = fun w => b.μ w * beurling (g n) w := by
      intro n
      change T^[n + 1] b.μ = fun w => b.μ w * beurling (T^[n] b.μ) w
      rw [Function.iterate_succ_apply']
    have hgsupp : ∀ n : ℕ, ∀ z : ℂ, R < ‖z‖ → g n z = 0 := by
      intro n
      induction n with
      | zero =>
        intro z hz
        have h0 : g 0 z = b.μ z := by rw [hg_zero]
        rw [h0]
        exact hsupp z hz
      | succ n ih =>
        intro z hz
        have h1 : g (n + 1) z = b.μ z * beurling (g n) z := by rw [hg_succ n]
        rw [h1, hsupp z hz, zero_mul]
    have hgLp : ∀ n : ℕ, MemLp (g n) p volume := by
      intro n
      induction n with
      | zero =>
        rw [hg_zero]
        exact hμLp
      | succ n ih =>
        rw [hg_succ n]
        exact (memLp_beurling_of_memLp hp hp2 ih).mul' hμLinf
    have hgbound : ∀ n : ℕ, eLpNorm (g n) p volume
        ≤ (ENNReal.ofReal (b.normInf * C)) ^ n * eLpNorm b.μ p volume := by
      intro n
      induction n with
      | zero =>
        rw [hg_zero, pow_zero, one_mul]
      | succ n ih =>
        have hstep : eLpNorm (g (n + 1)) p volume
            ≤ ENNReal.ofReal (b.normInf * C) * eLpNorm (g n) p volume := by
          rw [hg_succ n]
          calc eLpNorm (fun w => b.μ w * beurling (g n) w) p volume
              ≤ eLpNormEssSup b.μ volume * eLpNorm (beurling (g n)) p volume :=
                eLpNorm_mul_le_essSup_mul b.measurable.aestronglyMeasurable
                  (memLp_beurling_of_memLp hp hp2 (hgLp n))
            _ ≤ ENNReal.ofReal b.normInf * (ENNReal.ofReal C * eLpNorm (g n) p volume) := by
                rw [hessSup_eq]
                gcongr
                exact hCbound (g n) (hgLp n)
            _ = ENNReal.ofReal (b.normInf * C) * eLpNorm (g n) p volume := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul b.normInf_nonneg]
        calc eLpNorm (g (n + 1)) p volume
            ≤ ENNReal.ofReal (b.normInf * C) * eLpNorm (g n) p volume := hstep
          _ ≤ ENNReal.ofReal (b.normInf * C)
                * ((ENNReal.ofReal (b.normInf * C)) ^ n * eLpNorm b.μ p volume) := by
              gcongr
          _ = (ENNReal.ofReal (b.normInf * C)) ^ (n + 1) * eLpNorm b.μ p volume := by
              rw [← mul_assoc, ← pow_succ']
    have hgL2 : ∀ n : ℕ, MemLp (g n) 2 volume := fun n => hL2 (g n) (hgLp n) (hgsupp n)
    -- The partial-sum fields.
    set s : ℕ → ℂ → ℂ := fun n z => ∑ m ∈ Finset.range n, t ^ (m + 1) * g m z with hs_def
    have hs_zero : ∀ z : ℂ, s 0 z = 0 := by
      intro z
      change ∑ m ∈ Finset.range 0, t ^ (m + 1) * g m z = 0
      rw [Finset.sum_range_zero]
    have hs_succ : ∀ (n : ℕ) (z : ℂ), s (n + 1) z = s n z + t ^ (n + 1) * g n z := by
      intro n z
      change ∑ m ∈ Finset.range (n + 1), t ^ (m + 1) * g m z
          = ∑ m ∈ Finset.range n, t ^ (m + 1) * g m z + t ^ (n + 1) * g n z
      rw [Finset.sum_range_succ]
    have hssupp : ∀ n : ℕ, ∀ z : ℂ, R < ‖z‖ → s n z = 0 := by
      intro n z hz
      change ∑ m ∈ Finset.range n, t ^ (m + 1) * g m z = 0
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [hgsupp m z hz, mul_zero]
    have hsLp : ∀ n : ℕ, MemLp (s n) p volume := fun n =>
      memLp_finsetSum _ fun m _ => (hgLp m).const_mul (t ^ (m + 1))
    -- Beurling of the partial sums, by finite linearity.
    have hSsum : ∀ n : ℕ, beurling (s n)
        =ᵐ[volume] fun z => ∑ m ∈ Finset.range n, t ^ (m + 1) * beurling (g m) z := by
      intro n
      induction n with
      | zero =>
        have h0 : s 0 = (0 : ℂ) • b.μ := by
          funext z
          rw [hs_zero z, Pi.smul_apply, zero_smul]
        have hb0 := beurling_smul_ae (0 : ℂ) (Or.inl (hL2 b.μ hμLp hsupp))
        rw [← h0] at hb0
        filter_upwards [hb0] with z hz
        rw [hz, Pi.smul_apply, zero_smul, Finset.sum_range_zero]
      | succ n ih =>
        have hdecomp : s (n + 1) = s n + (t ^ (n + 1)) • g n := by
          funext z
          rw [hs_succ n z]
          rfl
        have hgsm : MemLp ((t ^ (n + 1)) • g n) p volume :=
          (hgLp n).const_smul (t ^ (n + 1))
        have hadd := beurling_add_ae_lp hp hp2 (hsLp n) hgsm
        have hsm := beurling_smul_ae (t ^ (n + 1)) (Or.inl (hgL2 n))
        rw [hdecomp]
        filter_upwards [hadd, hsm, ih] with z hzadd hzsm hzih
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hzadd hzsm
        rw [hzadd, hzih, hzsm, Finset.sum_range_succ]
    -- Recursion for the partial sums under the affine operator.
    have hsrec : ∀ n : ℕ, s (n + 1) =ᵐ[volume] fun z => tμ z * beurling (s n) z + tμ z := by
      intro n
      filter_upwards [hSsum n] with z hz
      show s (n + 1) z = tμ z * beurling (s n) z + tμ z
      rw [hz]
      change ∑ m ∈ Finset.range (n + 1), t ^ (m + 1) * g m z
          = t * b.μ z * (∑ m ∈ Finset.range n, t ^ (m + 1) * beurling (g m) z) + t * b.μ z
      rw [Finset.sum_range_succ', Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun m _ => ?_
        have hgm : g (m + 1) z = b.μ z * beurling (g m) z := by rw [hg_succ m]
        rw [hgm]
        ring
      · have hg0 : g 0 z = b.μ z := by rw [hg_zero]
        rw [hg0]
        ring
    -- Beurling subtractivity on `Lᵖ`.
    have hbeurling_sub : ∀ u v : ℂ → ℂ, MemLp u p volume → MemLp v p volume →
        beurling (fun w => u w - v w)
          =ᵐ[volume] fun z => beurling u z - beurling v z := by
      intro u v hu hv
      have hadd := beurling_add_ae_lp hp hp2 hv
        (show MemLp (fun w => u w - v w) p volume from hu.sub hv)
      have hvuv : (v + fun w => u w - v w) = u := by
        funext w
        simp
      rw [hvuv] at hadd
      filter_upwards [hadd] with z hz
      simp only [Pi.add_apply] at hz
      rw [hz]
      ring
    -- The error fields and their geometric decay.
    have herrLp : ∀ n : ℕ, MemLp (fun z => h' z - s n z) p volume := fun n =>
      hh'Lp.sub (hsLp n)
    have hkey : ∀ n : ℕ, (fun z => h' z - s (n + 1) z)
        =ᵐ[volume] fun z => tμ z * beurling (fun w => h' w - s n w) z := by
      intro n
      have hsub := hbeurling_sub h' (s n) hh'Lp (hsLp n)
      filter_upwards [heq', hsrec n, hsub] with z hz1 hz2 hz3
      show h' z - s (n + 1) z = tμ z * beurling (fun w => h' w - s n w) z
      rw [hz1, hz2, hz3]
      ring
    have hρ0 : 0 ≤ ‖t‖ * b.normInf * C :=
      mul_nonneg (mul_nonneg (norm_nonneg t) b.normInf_nonneg) hC0
    have hρ1 : ‖t‖ * b.normInf * C < 1 := hcontr
    have herrbound : ∀ n : ℕ, eLpNorm (fun z => h' z - s n z) p volume
        ≤ (ENNReal.ofReal (‖t‖ * b.normInf * C)) ^ n * eLpNorm h' p volume := by
      intro n
      induction n with
      | zero =>
        have h0 : (fun z => h' z - s 0 z) = h' := by
          funext z
          rw [hs_zero z, sub_zero]
        rw [h0, pow_zero, one_mul]
      | succ n ih =>
        have hbmem : MemLp (beurling (fun w => h' w - s n w)) p volume :=
          memLp_beurling_of_memLp hp hp2 (herrLp n)
        calc eLpNorm (fun z => h' z - s (n + 1) z) p volume
            = eLpNorm (fun z => tμ z * beurling (fun w => h' w - s n w) z) p volume :=
              eLpNorm_congr_ae (hkey n)
          _ ≤ eLpNormEssSup tμ volume
                * eLpNorm (beurling (fun w => h' w - s n w)) p volume :=
              eLpNorm_mul_le_essSup_mul htμmeas.aestronglyMeasurable hbmem
          _ ≤ ENNReal.ofReal (‖t‖ * b.normInf)
                * (ENNReal.ofReal C * eLpNorm (fun z => h' z - s n z) p volume) := by
              rw [hesstμ]
              gcongr
              exact hCbound _ (herrLp n)
          _ = ENNReal.ofReal (‖t‖ * b.normInf * C)
                * eLpNorm (fun z => h' z - s n z) p volume := by
              rw [← mul_assoc,
                ← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg t) b.normInf_nonneg)]
          _ ≤ ENNReal.ofReal (‖t‖ * b.normInf * C)
                * ((ENNReal.ofReal (‖t‖ * b.normInf * C)) ^ n * eLpNorm h' p volume) := by
              gcongr
          _ = (ENNReal.ofReal (‖t‖ * b.normInf * C)) ^ (n + 1) * eLpNorm h' p volume := by
              rw [← mul_assoc, ← pow_succ']
    -- The uniform sup bound for the Cauchy transform.
    obtain ⟨C₀, hC₀0, hC₀⟩ := norm_cauchyTransform_le_of_memLp_support (R := R) hp hp2
    have hμfinLp : eLpNorm b.μ p volume ≠ ⊤ := hμLp.2.ne
    have hh'fin : eLpNorm h' p volume ≠ ⊤ := hh'Lp.2.ne
    have herrsupp : ∀ n : ℕ, ∀ z : ℂ, R < ‖z‖ → h' z - s n z = 0 := by
      intro n z hz
      rw [hh'supp z hz, hssupp n z hz, sub_zero]
    have herrreal : ∀ n : ℕ, (eLpNorm (fun z => h' z - s n z) p volume).toReal
        ≤ (‖t‖ * b.normInf * C) ^ n * (eLpNorm h' p volume).toReal := by
      intro n
      have hne : (ENNReal.ofReal (‖t‖ * b.normInf * C)) ^ n * eLpNorm h' p volume ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hh'fin
      have hmono := ENNReal.toReal_mono hne (herrbound n)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ0] at hmono
    -- Finite linearity of the Cauchy transform over the partial sums.
    have hPsum : ∀ (n : ℕ) (z : ℂ), cauchyTransform (s n) z
        = ∑ m ∈ Finset.range n, t ^ (m + 1) * cauchyTransform (g m) z := by
      intro n z
      have hint : ∀ m : ℕ, Integrable (fun ζ => g m ζ / (ζ - z)) volume := fun m =>
        integrable_div_sub_of_memLp_of_support hp hp2 (hgLp m) (hgsupp m) z
      have hsdiv : (fun ζ => s n ζ / (ζ - z))
          = fun ζ => ∑ m ∈ Finset.range n, t ^ (m + 1) * (g m ζ / (ζ - z)) := by
        funext ζ
        change (∑ m ∈ Finset.range n, t ^ (m + 1) * g m ζ) / (ζ - z) = _
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun m _ => mul_div_assoc _ _ _
      change -(1 / (Real.pi : ℂ)) * ∫ ζ, s n ζ / (ζ - z)
          = ∑ m ∈ Finset.range n, t ^ (m + 1) * cauchyTransform (g m) z
      rw [hsdiv, integral_finsetSum _ (fun m _ => (hint m).const_mul (t ^ (m + 1))),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      change -(1 / (Real.pi : ℂ)) * ∫ ζ, t ^ (m + 1) * (g m ζ / (ζ - z))
          = t ^ (m + 1) * cauchyTransform (g m) z
      have hcm : ∫ ζ, t ^ (m + 1) * (g m ζ / (ζ - z))
          = t ^ (m + 1) * ∫ ζ, g m ζ / (ζ - z) :=
        integral_const_mul _ _
      rw [hcm]
      change -(1 / (Real.pi : ℂ)) * (t ^ (m + 1) * ∫ ζ, g m ζ / (ζ - z))
          = t ^ (m + 1) * (-(1 / (Real.pi : ℂ)) * ∫ ζ, g m ζ / (ζ - z))
      ring
    -- The Cauchy transform of the error field.
    have hPdiff : ∀ (n : ℕ) (z : ℂ), cauchyTransform h' z - cauchyTransform (s n) z
        = cauchyTransform (fun w => h' w - s n w) z := by
      intro n z
      have hinth : Integrable (fun ζ => h' ζ / (ζ - z)) volume :=
        integrable_div_sub_of_memLp_of_support hp hp2 hh'Lp hh'supp z
      have hints : Integrable (fun ζ => s n ζ / (ζ - z)) volume :=
        integrable_div_sub_of_memLp_of_support hp hp2 (hsLp n) (hssupp n) z
      have hdiv : (fun ζ => (h' ζ - s n ζ) / (ζ - z))
          = fun ζ => h' ζ / (ζ - z) - s n ζ / (ζ - z) := by
        funext ζ
        rw [sub_div]
      change -(1 / (Real.pi : ℂ)) * (∫ ζ, h' ζ / (ζ - z))
            - -(1 / (Real.pi : ℂ)) * (∫ ζ, s n ζ / (ζ - z))
          = -(1 / (Real.pi : ℂ)) * ∫ ζ, (h' ζ - s n ζ) / (ζ - z)
      rw [hdiv, integral_sub hinth hints]
      ring
    -- Pointwise geometric bound on the tail of the series.
    have hEbound : ∀ (n : ℕ) (z : ℂ), ‖cauchyTransform h' z - cauchyTransform (s n) z‖
        ≤ C₀ * (eLpNorm h' p volume).toReal * (‖t‖ * b.normInf * C) ^ n := by
      intro n z
      rw [hPdiff n z]
      calc ‖cauchyTransform (fun w => h' w - s n w) z‖
          ≤ C₀ * (eLpNorm (fun w => h' w - s n w) p volume).toReal :=
            hC₀ _ (herrLp n) (herrsupp n) z
        _ ≤ C₀ * ((‖t‖ * b.normInf * C) ^ n * (eLpNorm h' p volume).toReal) :=
            mul_le_mul_of_nonneg_left (herrreal n) hC₀0
        _ = C₀ * (eLpNorm h' p volume).toReal * (‖t‖ * b.normInf * C) ^ n := by
            ring
    -- Conclusion.
    refine ⟨fun z => z + cauchyTransform h' z, hprin, fun z => ?_⟩
    have hsummand_bound : ∀ n : ℕ, ‖t ^ (n + 1) * cauchyTransform (g n) z‖
        ≤ ‖t‖ * (C₀ * (eLpNorm b.μ p volume).toReal) * (‖t‖ * b.normInf * C) ^ n := by
      intro n
      have h1 : ‖cauchyTransform (g n) z‖ ≤ C₀ * (eLpNorm (g n) p volume).toReal :=
        hC₀ (g n) (hgLp n) (hgsupp n) z
      have h2 : (eLpNorm (g n) p volume).toReal
          ≤ (b.normInf * C) ^ n * (eLpNorm b.μ p volume).toReal := by
        have hne : (ENNReal.ofReal (b.normInf * C)) ^ n * eLpNorm b.μ p volume ≠ ⊤ :=
          ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hμfinLp
        have hmono := ENNReal.toReal_mono hne (hgbound n)
        rwa [ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal (mul_nonneg b.normInf_nonneg hC0)] at hmono
      calc ‖t ^ (n + 1) * cauchyTransform (g n) z‖
          = ‖t‖ ^ (n + 1) * ‖cauchyTransform (g n) z‖ := by
            rw [norm_mul, norm_pow]
        _ ≤ ‖t‖ ^ (n + 1) * (C₀ * ((b.normInf * C) ^ n * (eLpNorm b.μ p volume).toReal)) := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg t) _)
            exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hC₀0)
        _ = ‖t‖ * (C₀ * (eLpNorm b.μ p volume).toReal) * (‖t‖ * b.normInf * C) ^ n := by
            ring
    have hsummable : Summable (fun n : ℕ => t ^ (n + 1) * cauchyTransform (g n) z) := by
      refine Summable.of_norm_bounded ?_ hsummand_bound
      exact (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
    have htend : Tendsto
        (fun n : ℕ => ∑ m ∈ Finset.range n, t ^ (m + 1) * cauchyTransform (g m) z)
        atTop (𝓝 (cauchyTransform h' z)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hb : ∀ n : ℕ, ‖(∑ m ∈ Finset.range n, t ^ (m + 1) * cauchyTransform (g m) z)
          - cauchyTransform h' z‖
          ≤ C₀ * (eLpNorm h' p volume).toReal * (‖t‖ * b.normInf * C) ^ n := by
        intro n
        rw [norm_sub_rev, ← hPsum n z]
        exact hEbound n z
      refine squeeze_zero (fun n => norm_nonneg _) hb ?_
      have hgeo := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul
        (C₀ * (eLpNorm h' p volume).toReal)
      simpa using hgeo
    have htsum : ∑' n : ℕ, t ^ (n + 1) * cauchyTransform (g n) z = cauchyTransform h' z :=
      tendsto_nhds_unique hsummable.hasSum.tendsto_sum_nat htend
    change z + cauchyTransform h' z
        = z + ∑' n : ℕ, t ^ (n + 1) * cauchyTransform (g n) z
    rw [htsum]
  -- Chunk C2 (transplanted): the uniform geometric bound on the series
  -- coefficients, independent of the parameter.
  have depChunkC2 : ∀ (b : BeltramiCoeff) (R : ℝ),
      (∀ z : ℂ, R < ‖z‖ → b.μ z = 0) →
      ∀ (p : ℝ≥0∞) (C : ℝ), 2 < p → p ≠ ⊤ →
        IsCalderonZygmundBound beurling p C →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (z : ℂ),
          ‖cauchyTransform ((fun v w => b.μ w * beurling v w)^[n] b.μ) z‖
            ≤ M * (b.normInf * max C 0) ^ n := by
    intro b R hsupp p C hp hp2 hCb
    classical
    have hC0 : 0 ≤ C := hCb.1
    have hCbound := hCb.2
    have hmaxC : max C 0 = C := max_eq_left hC0
    have hμfin : eLpNormEssSup b.μ volume ≠ ⊤ := (lt_trans b.bound ENNReal.one_lt_top).ne
    have hμLp : MemLp b.μ p volume :=
      memLp_of_eLpNormEssSup_ne_top_of_support hp2 b.measurable hμfin hsupp
    have hμLinf : MemLp b.μ ⊤ volume := by
      refine ⟨b.measurable.aestronglyMeasurable, ?_⟩
      rw [eLpNorm_exponent_top]
      exact lt_of_le_of_ne le_top hμfin
    have hessSup_eq : eLpNormEssSup b.μ volume = ENNReal.ofReal b.normInf := by
      rw [BeltramiCoeff.normInf, ENNReal.ofReal_toReal hμfin]
    -- The iterated fields.
    set T : (ℂ → ℂ) → ℂ → ℂ := fun v w => b.μ w * beurling v w with hT_def
    set g : ℕ → ℂ → ℂ := fun n => T^[n] b.μ with hg_def
    have hg_zero : g 0 = b.μ := Function.iterate_zero_apply T b.μ
    have hg_succ : ∀ n : ℕ, g (n + 1) = fun w => b.μ w * beurling (g n) w := by
      intro n
      change T^[n + 1] b.μ = fun w => b.μ w * beurling (T^[n] b.μ) w
      rw [Function.iterate_succ_apply']
    -- Support of the iterates.
    have hgsupp : ∀ n : ℕ, ∀ z : ℂ, R < ‖z‖ → g n z = 0 := by
      intro n
      induction n with
      | zero =>
        intro z hz
        have h0 : g 0 z = b.μ z := by rw [hg_zero]
        rw [h0]
        exact hsupp z hz
      | succ n ih =>
        intro z hz
        have h1 : g (n + 1) z = b.μ z * beurling (g n) z := by rw [hg_succ n]
        rw [h1, hsupp z hz, zero_mul]
    -- `Lᵖ` membership of the iterates.
    have hgLp : ∀ n : ℕ, MemLp (g n) p volume := by
      intro n
      induction n with
      | zero =>
        rw [hg_zero]
        exact hμLp
      | succ n ih =>
        rw [hg_succ n]
        exact (memLp_beurling_of_memLp hp hp2 ih).mul' hμLinf
    -- Geometric `Lᵖ` norm bound for the iterates.
    have hgbound : ∀ n : ℕ, eLpNorm (g n) p volume
        ≤ (ENNReal.ofReal (b.normInf * C)) ^ n * eLpNorm b.μ p volume := by
      intro n
      induction n with
      | zero =>
        rw [hg_zero, pow_zero, one_mul]
      | succ n ih =>
        have hstep : eLpNorm (g (n + 1)) p volume
            ≤ ENNReal.ofReal (b.normInf * C) * eLpNorm (g n) p volume := by
          rw [hg_succ n]
          calc eLpNorm (fun w => b.μ w * beurling (g n) w) p volume
              ≤ eLpNormEssSup b.μ volume * eLpNorm (beurling (g n)) p volume :=
                eLpNorm_mul_le_essSup_mul b.measurable.aestronglyMeasurable
                  (memLp_beurling_of_memLp hp hp2 (hgLp n))
            _ ≤ ENNReal.ofReal b.normInf * (ENNReal.ofReal C * eLpNorm (g n) p volume) := by
                rw [hessSup_eq]
                gcongr
                exact hCbound (g n) (hgLp n)
            _ = ENNReal.ofReal (b.normInf * C) * eLpNorm (g n) p volume := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul b.normInf_nonneg]
        calc eLpNorm (g (n + 1)) p volume
            ≤ ENNReal.ofReal (b.normInf * C) * eLpNorm (g n) p volume := hstep
          _ ≤ ENNReal.ofReal (b.normInf * C)
                * ((ENNReal.ofReal (b.normInf * C)) ^ n * eLpNorm b.μ p volume) := by
              gcongr
          _ = (ENNReal.ofReal (b.normInf * C)) ^ (n + 1) * eLpNorm b.μ p volume := by
              rw [← mul_assoc, ← pow_succ']
    -- The uniform sup bound for the Cauchy transform.
    obtain ⟨C₀, hC₀0, hC₀⟩ := norm_cauchyTransform_le_of_memLp_support (R := R) hp hp2
    have hμfinLp : eLpNorm b.μ p volume ≠ ⊤ := hμLp.2.ne
    refine ⟨C₀ * (eLpNorm b.μ p volume).toReal,
      mul_nonneg hC₀0 ENNReal.toReal_nonneg, ?_⟩
    intro n z
    have h1 : ‖cauchyTransform (g n) z‖ ≤ C₀ * (eLpNorm (g n) p volume).toReal :=
      hC₀ (g n) (hgLp n) (hgsupp n) z
    have h2 : (eLpNorm (g n) p volume).toReal
        ≤ (b.normInf * C) ^ n * (eLpNorm b.μ p volume).toReal := by
      have hne : (ENNReal.ofReal (b.normInf * C)) ^ n * eLpNorm b.μ p volume ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hμfinLp
      have hmono := ENNReal.toReal_mono hne (hgbound n)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (mul_nonneg b.normInf_nonneg hC0)] at hmono
    calc ‖cauchyTransform (g n) z‖
        ≤ C₀ * (eLpNorm (g n) p volume).toReal := h1
      _ ≤ C₀ * ((b.normInf * C) ^ n * (eLpNorm b.μ p volume).toReal) :=
          mul_le_mul_of_nonneg_left h2 hC₀0
      _ = C₀ * (eLpNorm b.μ p volume).toReal * (b.normInf * max C 0) ^ n := by
          rw [hmaxC]
          ring
  -- Exponent selection: at each admissible parameter the scaled coefficient has
  -- essential sup below one, so `exists_p_gt_two_beurling_contraction` yields an
  -- exponent `p > 2` with the contraction margin `‖t‖·‖μ‖∞·C < 1`.
  have hscale : ∀ t : ℂ, ‖t‖ * b.normInf < 1 →
      ∃ p : ℝ≥0∞, 2 < p ∧ p ≠ ⊤ ∧ ∃ C : ℝ, IsCalderonZygmundBound beurling p C ∧
        ‖t‖ * b.normInf * C < 1 := by
    intro t ht
    have hμfin : eLpNormEssSup b.μ volume ≠ ⊤ := (lt_trans b.bound ENNReal.one_lt_top).ne
    have hessSup_eq : eLpNormEssSup b.μ volume = ENNReal.ofReal b.normInf := by
      rw [BeltramiCoeff.normInf, ENNReal.ofReal_toReal hμfin]
    have hesstμ : eLpNormEssSup (fun z => t * b.μ z) volume
        = ENNReal.ofReal (‖t‖ * b.normInf) := by
      have hsmul : (fun z => t * b.μ z) = t • b.μ := by
        funext z
        show t * b.μ z = (t • b.μ) z
        rw [Pi.smul_apply, smul_eq_mul]
      calc eLpNormEssSup (fun z => t * b.μ z) volume
          = eLpNormEssSup (t • b.μ) volume := by rw [hsmul]
        _ = ‖t‖ₑ * eLpNormEssSup b.μ volume :=
            MeasureTheory.eLpNormEssSup_const_smul t b.μ
        _ = ENNReal.ofReal ‖t‖ * ENNReal.ofReal b.normInf := by
            rw [hessSup_eq, ofReal_norm]
        _ = ENNReal.ofReal (‖t‖ * b.normInf) := (ENNReal.ofReal_mul (norm_nonneg t)).symm
    have hlt : eLpNormEssSup (fun z => t * b.μ z) volume < 1 := by
      rw [hesstμ]
      exact ENNReal.ofReal_lt_one.mpr ht
    obtain ⟨p, hp, hp2, C, hCb, hcontr⟩ :=
      exists_p_gt_two_beurling_contraction (measurable_const.fun_mul b.measurable) hlt
    have htoReal : (eLpNormEssSup (fun z => t * b.μ z) volume).toReal
        = ‖t‖ * b.normInf := by
      rw [hesstμ, ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg t) b.normInf_nonneg)]
    rw [htoReal] at hcontr
    exact ⟨p, hp, hp2, C, hCb, hcontr⟩
  -- Assembly: the family is the pointwise power series; each chunk supplies
  -- one of the two conjuncts.
  refine ⟨fun t z => z + ∑' n : ℕ,
      t ^ (n + 1) * cauchyTransform ((fun v w => b.μ w * beurling v w)^[n] b.μ) z, ?_, ?_⟩
  · -- The series is a principal solution at each admissible parameter.
    intro t ht
    obtain ⟨p, hp, hp2, C, hCb, hcontr⟩ := hscale t ht
    obtain ⟨f, hfPS, hfEq⟩ := depChunkC1 b R hsupp p C hp hp2 hCb t ht hcontr
    have hfun : (fun z => z + ∑' n : ℕ,
        t ^ (n + 1) * cauchyTransform ((fun v w => b.μ w * beurling v w)^[n] b.μ) z) = f :=
      funext fun z => (hfEq z).symm
    change IsPrincipalSolution (b.scale t ht) fun z => z + ∑' n : ℕ,
      t ^ (n + 1) * cauchyTransform ((fun v w => b.μ w * beurling v w)^[n] b.μ) z
    rw [hfun]
    exact hfPS
  · -- Analyticity in the parameter at every point of the region.
    intro z t₀ ht₀
    have ht₀' : ‖t₀‖ * b.normInf < 1 := ht₀
    obtain ⟨p, hp, hp2, C, hCb, hcontr⟩ := hscale t₀ ht₀'
    obtain ⟨M, hM, hMbound⟩ := depChunkC2 b R hsupp p C hp hp2 hCb
    have hC0 : 0 ≤ C := hCb.1
    have hmax : max C 0 = C := max_eq_left hC0
    have hρ : 0 ≤ b.normInf * max C 0 :=
      mul_nonneg b.normInf_nonneg (le_max_right C 0)
    have ht₀ρ : ‖t₀‖ * (b.normInf * max C 0) < 1 := by
      rw [hmax, ← mul_assoc]
      exact hcontr
    have hB := depChunkB
      (fun n => cauchyTransform ((fun v w => b.μ w * beurling v w)^[n] b.μ) z)
      M (b.normInf * max C 0) hρ (fun n => hMbound n z) t₀ ht₀ρ
    exact (analyticAt_const (v := z)).add hB

end NoWanderingDomains
