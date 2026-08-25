/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.SingularIntegral.GehringHigherIntegrability.Sobolev

/-!
# Gehring self-improvement: the `(1,1)`-Poincaré inequality on a ball

The `(1,1)`-Poincaré inequality `poincare_one_one_ball` for the `W^{1,2}` primitive — the
analytic heart of the Sobolev–Poincaré node N1.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology Real Pointwise

namespace NoWanderingDomains

/-! ## (1,1)-Poincaré on a ball for the `W^{1,2}` primitive -/

set_option maxHeartbeats 400000 in
-- The mollification proof inlines the smooth segment-FTC Poincaré, the `conv_tendsto`
-- L²-mollification convergence and the `fderiv_conv` Leibniz identity as local `have`s,
-- so the single self-contained elaboration needs a modestly raised heartbeat budget.
open Metric in
/-- **(`poincare_one_one_ball`).** The **`(1,1)`-Poincaré inequality on a ball** for a
`W^{1,2}` primitive `F` with weak directional derivatives `Gx` (direction `1`) and `Gy`
(direction `I`). On every ball `B = ball x r` the `L¹`-mass of the oscillation of `F`
about its average is controlled by `r` times the `L¹`-mass of the **full gradient**
`‖Gx‖ + ‖Gy‖`:
`∫⁻_{B} ‖F − F_B‖ ≤ C · r · ∫⁻_{B} (‖Gx‖ + ‖Gy‖)`.

This is the lower-order companion needed in the cutoff proof of the Sobolev–Poincaré
node N1: it absorbs the cutoff-annulus commutator `(∇χ)·(F − F_B)` whose `L¹` mass is
controlled by the gradient.

**Proof (mollification route).** The witness constant is `C = 8`. We mollify `F` to a
sequence of `C¹` functions `Fₙ = ρₙ ⋆ F` (`ρₙ` a normed `ContDiffBump`), prove the
`(1,1)`-Poincaré for each smooth `Fₙ` by the all-direction segment FTC `Fₙ(z) − Fₙ(w) =
∫₀¹ ∇Fₙ(w+t(z−w))·(z−w) dt`, average over `w`, and collapse the double integral by the
affine change of variables `y = (1−t)w + tz` (Jacobian `(1−t)²` resp. `t²`) split at
`t = 1/2`, giving the scale-invariant constant `8`. We then pass `n → ∞` on the fixed ball:
the directional derivatives commute with mollification (`fderiv_conv`), `Fₙ → F` and
`ρₙ ⋆ Gᵥ → Gᵥ` in `L²(B)` (the proven `conv_tendsto`), whence both the oscillation `L¹`-mass
and the gradient `L¹`-mass converge, and the per-`n` inequality passes to the limit. -/
theorem poincare_one_one_ball :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F Gx Gy : ℂ → ℂ},
      MemLp F 2 volume → MemLp Gx 2 volume → MemLp Gy 2 volume →
      HasWeakDirDeriv 1 Gx F Set.univ → HasWeakDirDeriv Complex.I Gy F Set.univ →
        ∀ (x : ℂ) (r : ℝ), 0 < r →
          ∫⁻ z in Metric.ball x r, (‖F z - (⨍ w in Metric.ball x r, F w)‖₊ : ℝ≥0∞) ∂volume ≤
            ENNReal.ofReal (C * r) *
              ∫⁻ z in Metric.ball x r, ((‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)) ∂volume := by
  refine ⟨8, by norm_num, ?_⟩
  intro F Gx Gy hF hGx hGy hGxw hGyw x r hr
  have smooth_poincare : ∀ (u : ℂ → ℂ), ContDiff ℝ 1 u → ∀ (x : ℂ) (r : ℝ), 0 < r →
      ∫⁻ z in ball x r, (‖u z - (⨍ w in ball x r, u w ∂volume)‖ₑ) ∂volume ≤
        ENNReal.ofReal (8 * r) * ∫⁻ y in ball x r, ‖fderiv ℝ u y‖ₑ ∂volume := by
    intro u hu x r hr
    set B := ball x r with hB
    have hBmeas : MeasurableSet B := measurableSet_ball
    have hBfin : volume B ≠ ⊤ := (measure_ball_lt_top).ne
    have hBpos : volume B ≠ 0 := (measure_ball_pos volume x hr).ne'
    have hBrpos : 0 < volume.real B := by
      rw [Measure.real, ENNReal.toReal_pos_iff]; exact ⟨pos_iff_ne_zero.mpr hBpos, hBfin.lt_top⟩
    set g : ℂ → ℝ≥0∞ := fun y => ‖fderiv ℝ u y‖ₑ with hg
    have hgmeas : Measurable g := ((hu.continuous_fderiv (by norm_num)).enorm).measurable
    set G := ∫⁻ y in B, g y ∂volume with hG
    have hudiff : Differentiable ℝ u := hu.differentiable (by norm_num)
    have hucont : Continuous u := hudiff.continuous
    have hfdc : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
    have hconv : Convex ℝ B := convex_ball x r
    -- (1) Pointwise segment-FTC bound.
    have hpoint : ∀ z w : ℂ, (‖u z - u w‖ₑ) ≤
        ∫⁻ t in Set.Ioc (0:ℝ) 1, g (w + t • (z - w)) * ‖z - w‖ₑ ∂volume := by
      intro z w
      have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => w + s • (z - w)) (z - w) t := by
        intro t; have := ((hasDerivAt_id t).smul_const (z - w)).const_add w; simpa using this
      have hgderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u (w + s • (z - w)))
          ((fderiv ℝ u (w + t • (z - w))) (z - w)) t := fun t =>
        ((hudiff (w + t • (z - w))).hasFDerivAt).comp_hasDerivAt t (hline t)
      have hlinec : Continuous (fun t : ℝ => w + t • (z - w)) := by
        have h : (fun t : ℝ => w + t • (z - w)) = fun t : ℝ => w + (t : ℂ) * (z - w) := by
          funext t; rw [Complex.real_smul]
        rw [h]; fun_prop
      have hcont : Continuous (fun t : ℝ => (fderiv ℝ u (w + t • (z - w))) (z - w)) :=
        (hfdc.comp hlinec).clm_apply continuous_const
      have hftc : u z - u w = ∫ t in (0:ℝ)..1, (fderiv ℝ u (w + t • (z - w))) (z - w) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hgderiv t)
          (hcont.intervalIntegrable _ _)]; simp
      rw [hftc, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      refine le_trans (enorm_integral_le_lintegral_enorm _) (lintegral_mono (fun t => ?_))
      calc ‖(fderiv ℝ u (w + t • (z - w))) (z - w)‖ₑ
          ≤ ‖fderiv ℝ u (w + t • (z - w))‖ₑ * ‖z - w‖ₑ := by
            rw [← ofReal_norm (((fderiv ℝ u (w + t • (z - w))) (z - w))),
              ← ofReal_norm (z - w),
              show ‖fderiv ℝ u (w + t • (z - w))‖ₑ
                = ENNReal.ofReal ‖fderiv ℝ u (w + t • (z - w))‖ from
                (ofReal_norm _).symm,
              ← ENNReal.ofReal_mul (norm_nonneg _)]
            exact ENNReal.ofReal_le_ofReal ((fderiv ℝ u (w + t • (z - w))).le_opNorm (z - w))
        _ = g (w + t • (z - w)) * ‖z - w‖ₑ := rfl
    -- (2) Substitution-on-ball lemmas (both directions).
    have subW : ∀ (z : ℂ), z ∈ B → ∀ (t : ℝ), 0 < 1 - t → t ∈ Set.Icc (0:ℝ) 1 →
        ∫⁻ w in B, g ((1 - t) • w + t • z) ∂volume ≤
          ENNReal.ofReal ((1 - t) ^ 2)⁻¹ * G := by
      intro z hz t ht0 ht1
      rw [← lintegral_indicator hBmeas]
      have hmono : ∀ w : ℂ, B.indicator (fun w => g ((1 - t) • w + t • z)) w ≤
          (fun w => B.indicator g ((1 - t) • w + t • z)) w := by
        intro w
        by_cases hw : w ∈ B
        · simp only []
          have hin : (1 - t) • w + t • z ∈ B := by
            have := hconv hw hz (by linarith [ht1.1] : (0:ℝ) ≤ 1 - t) ht1.1 (by ring)
            simpa using this
          rw [Set.indicator_of_mem hw, Set.indicator_of_mem hin]
        · simp only []; rw [Set.indicator_of_notMem hw]; exact zero_le
      refine (lintegral_mono hmono).trans_eq ?_
      set h : ℂ → ℝ≥0∞ := B.indicator g with hh
      have hhmeas : Measurable h := hgmeas.indicator hBmeas
      have hfr : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
      have hmap : Measure.map (fun w : ℂ => (1 - t) • w) volume
          = ENNReal.ofReal (|((1 - t) ^ (Module.finrank ℝ ℂ))⁻¹|) • (volume : Measure ℂ) :=
        Measure.map_addHaar_smul volume ht0.ne'
      have hfmeas : Measurable (fun y : ℂ => h (y + t • z)) := hhmeas.comp (by fun_prop)
      have hgmm : Measurable (fun w : ℂ => (1 - t) • w) := by fun_prop
      calc ∫⁻ w, h ((1 - t) • w + t • z) ∂volume
          = ∫⁻ w, (fun y => h (y + t • z)) ((fun w : ℂ => (1 - t) • w) w) ∂volume := rfl
        _ = ∫⁻ w, (fun y => h (y + t • z)) w ∂(Measure.map (fun w : ℂ => (1 - t) • w) volume) :=
            (lintegral_map hfmeas hgmm).symm
        _ = ENNReal.ofReal (|((1 - t) ^ (Module.finrank ℝ ℂ))⁻¹|)
              * ∫⁻ w, h (w + t • z) ∂volume := by rw [hmap, lintegral_smul_measure, smul_eq_mul]
        _ = ENNReal.ofReal ((1 - t) ^ 2)⁻¹ * ∫⁻ y, h y ∂volume := by
            rw [lintegral_add_right_eq_self h (t • z), hfr, abs_of_nonneg (by positivity)]
        _ = ENNReal.ofReal ((1 - t) ^ 2)⁻¹ * G := by
            rw [hG, lintegral_indicator hBmeas]
    have subZ : ∀ (w : ℂ), w ∈ B → ∀ (t : ℝ), 0 < t → t ∈ Set.Icc (0:ℝ) 1 →
        ∫⁻ z in B, g ((1 - t) • w + t • z) ∂volume ≤
          ENNReal.ofReal (t ^ 2)⁻¹ * G := by
      intro w hw t ht0 ht1
      rw [← lintegral_indicator hBmeas]
      have hmono : ∀ z : ℂ, B.indicator (fun z => g ((1 - t) • w + t • z)) z ≤
          (fun z => B.indicator g ((1 - t) • w + t • z)) z := by
        intro z
        by_cases hz : z ∈ B
        · simp only []
          have hin : (1 - t) • w + t • z ∈ B := by
            have := hconv hw hz (by linarith [ht1.2] : (0:ℝ) ≤ 1 - t) ht1.1 (by ring)
            simpa using this
          rw [Set.indicator_of_mem hz, Set.indicator_of_mem hin]
        · simp only []; rw [Set.indicator_of_notMem hz]; exact zero_le
      refine (lintegral_mono hmono).trans_eq ?_
      set h : ℂ → ℝ≥0∞ := B.indicator g with hh
      have hhmeas : Measurable h := hgmeas.indicator hBmeas
      have hfr : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
      have hmap : Measure.map (fun z : ℂ => t • z) volume
          = ENNReal.ofReal (|(t ^ (Module.finrank ℝ ℂ))⁻¹|) • (volume : Measure ℂ) :=
        Measure.map_addHaar_smul volume ht0.ne'
      have hfmeas : Measurable (fun y : ℂ => h ((1 - t) • w + y)) := hhmeas.comp (by fun_prop)
      have hgmm : Measurable (fun z : ℂ => t • z) := by fun_prop
      calc ∫⁻ z, h ((1 - t) • w + t • z) ∂volume
          = ∫⁻ z, (fun y => h ((1 - t) • w + y)) ((fun z : ℂ => t • z) z) ∂volume := rfl
        _ = ∫⁻ z, (fun y => h ((1 - t) • w + y)) z ∂(Measure.map (fun z : ℂ => t • z) volume) :=
            (lintegral_map hfmeas hgmm).symm
        _ = ENNReal.ofReal (|(t ^ (Module.finrank ℝ ℂ))⁻¹|)
              * ∫⁻ z, h ((1 - t) • w + z) ∂volume := by
            rw [hmap, lintegral_smul_measure, smul_eq_mul]
        _ = ENNReal.ofReal (t ^ 2)⁻¹ * ∫⁻ y, h y ∂volume := by
            rw [lintegral_add_left_eq_self h ((1 - t) • w), hfr, abs_of_nonneg (by positivity)]
        _ = ENNReal.ofReal (t ^ 2)⁻¹ * G := by rw [hG, lintegral_indicator hBmeas]
    -- ============================================================
    -- (3) Averaging reduction: ‖u z - u_B‖ₑ ≤ ofReal((vol.real B)⁻¹) * ∫⁻_w∈B ‖u z - u w‖ₑ.
    -- ============================================================
    have hUintB : IntegrableOn u B volume :=
      (hucont.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall x r)).mono_set
        ball_subset_closedBall
    have havg : ∀ z, u z - (⨍ w in B, u w ∂volume) = ⨍ w in B, (u z - u w) ∂volume := by
      intro z
      have hconstI : IntegrableOn (fun _ => u z) B volume := integrableOn_const hBfin
      rw [setAverage_eq, setAverage_eq, integral_sub hconstI hUintB, setIntegral_const,
        smul_sub, smul_smul, mul_comm, mul_inv_cancel₀, one_smul]
      rw [Measure.real]; simp only [ne_eq, ENNReal.toReal_eq_zero_iff, not_or]
      exact ⟨hBpos, hBfin⟩
    -- ============================================================
    -- (4) The double-integral bound.  Let D := ∫⁻_z∈B ∫⁻_w∈B ‖u z - u w‖ₑ.
    -- We bound  LHS ≤ ofReal((vol.real B)⁻¹) * D  and  D ≤ ofReal(8 r) * (vol B) * G,
    -- so the (vol.real B)⁻¹ cancels (vol B).
    -- ============================================================
    set D := ∫⁻ z in B, ∫⁻ w in B, ‖u z - u w‖ₑ ∂volume ∂volume with hD
    -- LHS ≤ ofReal((vol.real B)⁻¹) * D.
    have hLHS : ∫⁻ z in B, (‖u z - (⨍ w in B, u w ∂volume)‖ₑ) ∂volume ≤
        ENNReal.ofReal (volume.real B)⁻¹ * D := by
      rw [hD, ← lintegral_const_mul' _ _ (by simp)]
      refine lintegral_mono_ae ?_
      refine Filter.Eventually.of_forall (fun z => ?_)
      rw [havg z, setAverage_eq, enorm_smul]
      refine mul_le_mul' ?_ (enorm_integral_le_lintegral_enorm _)
      rw [Real.enorm_of_nonneg (by positivity)]
    -- ============================================================
    -- (5) Triple-integral bound for D.
    -- ============================================================
    -- joint measurability used repeatedly.
    have hjm : ∀ z : ℂ, Measurable (fun p : ℂ × ℝ => g (p.1 + p.2 • (z - p.1))) := by
      intro z; apply hgmeas.comp
      have heq : (fun p : ℂ × ℝ => p.1 + p.2 • (z - p.1))
          = fun p : ℂ × ℝ => p.1 + (p.2 : ℂ) * (z - p.1) := by
        funext p; rw [Complex.real_smul]
      rw [heq]; fun_prop
    -- D ≤ ofReal(2r) * T, where T is the triple integral.
    have hzw_le : ∀ z ∈ B, ∀ w ∈ B, ‖z - w‖ₑ ≤ ENNReal.ofReal (2 * r) := by
      intro z hz w hw
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      have htri : ‖z - w‖ ≤ ‖z - x‖ + ‖x - w‖ := by
        calc ‖z - w‖ = ‖(z - x) + (x - w)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖z - x‖ + ‖x - w‖ := norm_add_le _ _
      rw [hB, mem_ball, dist_eq_norm] at hz hw
      rw [norm_sub_rev x w] at htri
      linarith [hz, hw]
    set T := ∫⁻ z in B, ∫⁻ w in B,
        (∫⁻ t in Set.Ioc (0:ℝ) 1, g (w + t • (z - w)) ∂volume) ∂volume ∂volume with hT
    have hDT : D ≤ ENNReal.ofReal (2 * r) * T := by
      rw [hD, hT, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' hBmeas]
      refine Filter.Eventually.of_forall (fun z hz => ?_)
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' hBmeas]
      refine Filter.Eventually.of_forall (fun w hw => ?_)
      refine le_trans (hpoint z w) ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun s hs => ?_)
      rw [mul_comm (ENNReal.ofReal (2 * r))]
      exact mul_le_mul' (le_refl _) (hzw_le z hz w hw)
    -- T ≤ 4 * (vol B) * G.
    -- rewrite g(w+t(z-w)) = g((1-t)•w + t•z).
    have hrw : ∀ (z w : ℂ) (t : ℝ), g (w + t • (z - w)) = g ((1 - t) • w + t • z) := by
      intro z w t; congr 1; module
    -- T₁ over Ioc 0 (1/2): bound via swap (w ↔ t) and subW.
    have hT1 : (∫⁻ z in B, ∫⁻ w in B,
          (∫⁻ t in Set.Ioc (0:ℝ) (1/2), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume)
        ≤ 2 * G * volume B := by
      have hmeasJ : Measurable (fun q : ℂ × ℝ => g ((1 - q.2) • q.1 + q.2 • (0:ℂ))) := by
        apply hgmeas.comp
        have heq : (fun q : ℂ × ℝ => (1 - q.2) • q.1 + q.2 • (0:ℂ))
            = fun q : ℂ × ℝ => ((1 - q.2 : ℝ) : ℂ) * q.1 := by
          funext q; rw [Complex.real_smul]; simp
        rw [heq]; fun_prop
      have hinner : ∀ z ∈ B, (∫⁻ w in B,
          (∫⁻ t in Set.Ioc (0:ℝ) (1/2), g ((1 - t) • w + t • z) ∂volume) ∂volume) ≤ 2 * G := by
        intro z hz
        have hJz : Measurable (fun q : ℂ × ℝ => g ((1 - q.2) • q.1 + q.2 • z)) := by
          apply hgmeas.comp
          have heq : (fun q : ℂ × ℝ => (1 - q.2) • q.1 + q.2 • z)
              = fun q : ℂ × ℝ => ((1 - q.2 : ℝ) : ℂ) * q.1 + ((q.2 : ℝ) : ℂ) * z := by
            funext q; rw [Complex.real_smul, Complex.real_smul]
          rw [heq]; fun_prop
        have hswap : (∫⁻ w in B, (∫⁻ t in Set.Ioc (0:ℝ) (1/2),
              g ((1 - t) • w + t • z) ∂volume) ∂volume)
            = ∫⁻ t in Set.Ioc (0:ℝ) (1/2),
                (∫⁻ w in B, g ((1 - t) • w + t • z) ∂volume) ∂volume := by
          rw [lintegral_lintegral_swap]
          exact (hJz.aemeasurable.comp_measurable
            (by fun_prop : Measurable (fun p : ℂ × ℝ => ((p.1, p.2) : ℂ × ℝ))))
        rw [hswap]
        calc ∫⁻ t in Set.Ioc (0:ℝ) (1/2), (∫⁻ w in B, g ((1 - t) • w + t • z) ∂volume) ∂volume
            ≤ ∫⁻ t in Set.Ioc (0:ℝ) (1/2), ENNReal.ofReal 4 * G ∂volume := by
              refine lintegral_mono_ae ?_
              rw [ae_restrict_iff' measurableSet_Ioc]
              refine Filter.Eventually.of_forall (fun t ht => ?_)
              simp only [Set.mem_Ioc] at ht
              have ht0 : 0 < 1 - t := by linarith [ht.2]
              have htIcc : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, by linarith [ht.2]⟩
              refine le_trans (subW z hz t ht0 htIcc) ?_
              refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (le_refl _)
              have hb : (1/2 : ℝ) ≤ 1 - t := by linarith [ht.2]
              rw [inv_le_iff_one_le_mul₀ (by positivity)]
              nlinarith [hb]
          _ = ENNReal.ofReal 4 * G * volume (Set.Ioc (0:ℝ) (1/2)) := by
              rw [lintegral_const, Measure.restrict_apply_univ]
          _ = 2 * G := by
              rw [Real.volume_Ioc, show ENNReal.ofReal 4 = (4:ℝ≥0∞) by norm_num,
                show ENNReal.ofReal ((1:ℝ)/2 - 0) = (1/2 : ℝ≥0∞) by
                  rw [show (1:ℝ)/2 - 0 = (2:ℝ)⁻¹ by norm_num,
                    ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num,
                mul_right_comm, show (4:ℝ≥0∞) * (1/2) = 2 from by
                  rw [one_div, show (4:ℝ≥0∞) = 2 * 2 from by norm_num, mul_assoc,
                    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]]
      calc (∫⁻ z in B, ∫⁻ w in B,
              (∫⁻ t in Set.Ioc (0:ℝ) (1/2), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume)
          ≤ ∫⁻ z in B, 2 * G ∂volume := by
            refine lintegral_mono_ae ?_
            rw [ae_restrict_iff' hBmeas]
            exact Filter.Eventually.of_forall hinner
        _ = 2 * G * volume B := by rw [lintegral_const, Measure.restrict_apply_univ]
    -- T₂ over Ioc (1/2) 1: bound via swap (z ↔ t) and subZ.
    have hT2 : (∫⁻ z in B, ∫⁻ w in B,
          (∫⁻ t in Set.Ioc (1/2) (1:ℝ), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume)
        ≤ 2 * G * volume B := by
      -- swap z and w outermost first (Tonelli), then proceed symmetrically.
      have hswapOuter : (∫⁻ z in B, ∫⁻ w in B,
            (∫⁻ t in Set.Ioc (1/2) (1:ℝ), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume)
          = (∫⁻ w in B, ∫⁻ z in B,
            (∫⁻ t in Set.Ioc (1/2) (1:ℝ), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume) := by
        have hf : Measurable (Function.uncurry (fun z w : ℂ => ∫⁻ t in Set.Ioc (1/2) (1:ℝ),
            g ((1 - t) • w + t • z) ∂volume)) := by
          have hf2 : Measurable (fun q : (ℂ × ℂ) × ℝ => g ((1 - q.2) • q.1.2 + q.2 • q.1.1)) := by
            apply hgmeas.comp
            have heq : (fun q : (ℂ × ℂ) × ℝ => (1 - q.2) • q.1.2 + q.2 • q.1.1)
                = fun q : (ℂ × ℂ) × ℝ => ((1 - q.2 : ℝ) : ℂ) * q.1.2 + ((q.2 : ℝ) : ℂ) * q.1.1 := by
              funext q; rw [Complex.real_smul, Complex.real_smul]
            rw [heq]; fun_prop
          exact hf2.lintegral_prod_right'
        exact lintegral_lintegral_swap hf.aemeasurable
      rw [hswapOuter]
      have hinner : ∀ w ∈ B, (∫⁻ z in B,
          (∫⁻ t in Set.Ioc (1/2) (1:ℝ), g ((1 - t) • w + t • z) ∂volume) ∂volume) ≤ 2 * G := by
        intro w hw
        have hJw : Measurable (fun q : ℂ × ℝ => g ((1 - q.2) • w + q.2 • q.1)) := by
          apply hgmeas.comp
          have heq : (fun q : ℂ × ℝ => (1 - q.2) • w + q.2 • q.1)
              = fun q : ℂ × ℝ => ((1 - q.2 : ℝ) : ℂ) * w + ((q.2 : ℝ) : ℂ) * q.1 := by
            funext q; rw [Complex.real_smul, Complex.real_smul]
          rw [heq]; fun_prop
        have hswap : (∫⁻ z in B, (∫⁻ t in Set.Ioc (1/2) (1:ℝ),
              g ((1 - t) • w + t • z) ∂volume) ∂volume)
            = ∫⁻ t in Set.Ioc (1/2) (1:ℝ),
                (∫⁻ z in B, g ((1 - t) • w + t • z) ∂volume) ∂volume := by
          rw [lintegral_lintegral_swap]
          exact (hJw.aemeasurable.comp_measurable
            (by fun_prop : Measurable (fun p : ℂ × ℝ => ((p.1, p.2) : ℂ × ℝ))))
        rw [hswap]
        calc ∫⁻ t in Set.Ioc (1/2) (1:ℝ), (∫⁻ z in B, g ((1 - t) • w + t • z) ∂volume) ∂volume
            ≤ ∫⁻ t in Set.Ioc (1/2) (1:ℝ), ENNReal.ofReal 4 * G ∂volume := by
              refine lintegral_mono_ae ?_
              rw [ae_restrict_iff' measurableSet_Ioc]
              refine Filter.Eventually.of_forall (fun t ht => ?_)
              simp only [Set.mem_Ioc] at ht
              have ht0 : 0 < t := by linarith [ht.1]
              have htIcc : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0.le, ht.2⟩
              refine le_trans (subZ w hw t ht0 htIcc) ?_
              refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (le_refl _)
              have hb : (1/2 : ℝ) ≤ t := by linarith [ht.1]
              rw [inv_le_iff_one_le_mul₀ (by positivity)]
              nlinarith [hb]
          _ = ENNReal.ofReal 4 * G * volume (Set.Ioc (1/2) (1:ℝ)) := by
              rw [lintegral_const, Measure.restrict_apply_univ]
          _ = 2 * G := by
              rw [Real.volume_Ioc, show ENNReal.ofReal 4 = (4:ℝ≥0∞) by norm_num,
                show ENNReal.ofReal ((1:ℝ) - 1/2) = (1/2 : ℝ≥0∞) by
                  rw [show (1:ℝ) - 1/2 = (2:ℝ)⁻¹ by norm_num,
                    ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num,
                mul_right_comm, show (4:ℝ≥0∞) * (1/2) = 2 from by
                  rw [one_div, show (4:ℝ≥0∞) = 2 * 2 from by norm_num, mul_assoc,
                    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]]
      calc (∫⁻ w in B, ∫⁻ z in B,
              (∫⁻ t in Set.Ioc (1/2) (1:ℝ), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume)
          ≤ ∫⁻ w in B, 2 * G ∂volume := by
            refine lintegral_mono_ae ?_
            rw [ae_restrict_iff' hBmeas]
            exact Filter.Eventually.of_forall hinner
        _ = 2 * G * volume B := by rw [lintegral_const, Measure.restrict_apply_univ]
    -- assemble T ≤ 4 vol B G via the t-split.
    have hT4 : T ≤ 4 * volume B * G := by
      have hTconv : T = ∫⁻ z in B, ∫⁻ w in B,
          (∫⁻ t in Set.Ioc (0:ℝ) 1, g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume := by
        rw [hT]; simp only [hrw]
      rw [hTconv]
      have hsplit : ∀ z w : ℂ,
          (∫⁻ t in Set.Ioc (0:ℝ) 1, g ((1 - t) • w + t • z) ∂volume)
            = (∫⁻ t in Set.Ioc (0:ℝ) (1/2), g ((1 - t) • w + t • z) ∂volume)
              + (∫⁻ t in Set.Ioc (1/2) (1:ℝ), g ((1 - t) • w + t • z) ∂volume) := by
        intro z w
        have hdisj : Disjoint (Set.Ioc (0:ℝ) (1/2)) (Set.Ioc (1/2) 1) := by
          simp only [Set.disjoint_left]
          intro a h1 h2
          simp only [Set.mem_Ioc] at h1 h2
          linarith [h1.2, h2.1]
        rw [← lintegral_union measurableSet_Ioc hdisj,
          Set.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)]
      have hTeq : (∫⁻ z in B, ∫⁻ w in B,
            (∫⁻ t in Set.Ioc (0:ℝ) 1, g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume)
          = (∫⁻ z in B, ∫⁻ w in B,
            (∫⁻ t in Set.Ioc (0:ℝ) (1/2), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume)
          + (∫⁻ z in B, ∫⁻ w in B,
            (∫⁻ t in Set.Ioc (1/2) (1:ℝ), g ((1 - t) • w + t • z) ∂volume) ∂volume ∂volume) := by
        have hmeasA : Measurable (fun z : ℂ => ∫⁻ w in B, ∫⁻ t in Set.Ioc (0:ℝ) (1/2),
            g ((1 - t) • w + t • z) ∂volume ∂volume) := by
          have hf2 : Measurable (fun q : (ℂ × ℂ) × ℝ => g ((1 - q.2) • q.1.2 + q.2 • q.1.1)) := by
            apply hgmeas.comp
            have heq : (fun q : (ℂ × ℂ) × ℝ => (1 - q.2) • q.1.2 + q.2 • q.1.1)
                = fun q : (ℂ × ℂ) × ℝ => ((1 - q.2 : ℝ) : ℂ) * q.1.2 + ((q.2 : ℝ) : ℂ) * q.1.1 := by
              funext q; rw [Complex.real_smul, Complex.real_smul]
            rw [heq]; fun_prop
          have hf3 : Measurable (fun p : ℂ × ℂ => ∫⁻ t in Set.Ioc (0:ℝ) (1/2),
              g ((1 - t) • p.2 + t • p.1) ∂volume) := hf2.lintegral_prod_right'
          exact hf3.lintegral_prod_right'
        rw [← lintegral_add_left' hmeasA.aemeasurable.restrict]
        refine lintegral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
        have hmeasAw : Measurable (fun w : ℂ => ∫⁻ t in Set.Ioc (0:ℝ) (1/2),
            g ((1 - t) • w + t • z) ∂volume) := by
          have hf2 : Measurable (fun q : ℂ × ℝ => g ((1 - q.2) • q.1 + q.2 • z)) := by
            apply hgmeas.comp
            have heq : (fun q : ℂ × ℝ => (1 - q.2) • q.1 + q.2 • z)
                = fun q : ℂ × ℝ => ((1 - q.2 : ℝ) : ℂ) * q.1 + ((q.2 : ℝ) : ℂ) * z := by
              funext q; rw [Complex.real_smul, Complex.real_smul]
            rw [heq]; fun_prop
          exact hf2.lintegral_prod_right'
        simp only []
        rw [← lintegral_add_left' hmeasAw.aemeasurable.restrict]
        refine lintegral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
        exact hsplit z w
      rw [hTeq]
      calc _ ≤ 2 * G * volume B + 2 * G * volume B := add_le_add hT1 hT2
        _ = 4 * volume B * G := by ring
    -- ============================================================
    -- (6) Assemble:  LHS ≤ ofReal((vol.real B)⁻¹) * D ≤ ofReal((vol.real B)⁻¹) * ofReal(2r) * T
    --             ≤ ofReal((vol.real B)⁻¹) * ofReal(2r) * 4 * vol B * G = ofReal(8r) * G.
    -- ============================================================
    have hvoleq : volume B = ENNReal.ofReal (volume.real B) := by
      rw [Measure.real, ENNReal.ofReal_toReal hBfin]
    calc ∫⁻ z in B, (‖u z - (⨍ w in B, u w ∂volume)‖ₑ) ∂volume
        ≤ ENNReal.ofReal (volume.real B)⁻¹ * D := hLHS
      _ ≤ ENNReal.ofReal (volume.real B)⁻¹ * (ENNReal.ofReal (2 * r) * T) :=
          mul_le_mul' (le_refl _) hDT
      _ ≤ ENNReal.ofReal (volume.real B)⁻¹ * (ENNReal.ofReal (2 * r) * (4 * volume B * G)) :=
          mul_le_mul' (le_refl _) (mul_le_mul' (le_refl _) hT4)
      _ = ENNReal.ofReal (8 * r) * G := by
          rw [hvoleq]
          rw [show ENNReal.ofReal (volume.real B)⁻¹ *
              (ENNReal.ofReal (2 * r) * (4 * ENNReal.ofReal (volume.real B) * G))
            = (ENNReal.ofReal (volume.real B)⁻¹ * ENNReal.ofReal (volume.real B))
              * (ENNReal.ofReal (2 * r) * 4 * G) from by ring]
          rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (ne_of_gt hBrpos),
            ENNReal.ofReal_one, one_mul]
          rw [show ENNReal.ofReal (2 * r) * 4 = ENNReal.ofReal (8 * r) from by
            rw [show (4:ℝ≥0∞) = ENNReal.ofReal 4 from by norm_num,
              ← ENNReal.ofReal_mul (by positivity)]; congr 1; ring]
  have conv_tendsto : ∀ {g : ℂ → ℂ},
      MemLp g 2 volume → ∀ (φ : ℕ → ContDiffBump (0 : ℂ)),
      Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => eLpNorm
          (MeasureTheory.convolution ((φ n).normed volume) g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - g) 2 volume)
        Filter.atTop (nhds 0) := by
    intro g hg φ hφrout
    set Cg : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed volume)
      g (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCg
    have hP3 : ∀ (h : ℂ → ℂ), HasCompactSupport h → ContDiff ℝ (⊤ : ℕ∞) h →
        Filter.Tendsto (fun n => eLpNorm
          (MeasureTheory.convolution ((φ n).normed volume) h
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - h) 2 volume)
          Filter.atTop (nhds 0) := by
      intro h hh_supp hh_smooth
      obtain ⟨M, hM⟩ := hh_smooth.continuous.bounded_above_of_compact_support hh_supp
      have hM0 : 0 ≤ M := le_trans (norm_nonneg (h 0)) (hM 0)
      set Kset : Set ℂ := Metric.cthickening 1 (tsupport h) with hKdef
      have hKcompact : IsCompact Kset := hh_supp.isCompact.cthickening
      have hKmeas : MeasurableSet Kset := hKcompact.measurableSet
      have hKfin : volume Kset < ⊤ := hKcompact.measure_lt_top
      have htsupp_sub : tsupport h ⊆ Kset := Metric.self_subset_cthickening _
      set Cn : ℕ → ℂ → ℂ := fun n => MeasureTheory.convolution ((φ n).normed volume)
        h (ContinuousLinearMap.lsmul ℝ ℝ) volume with hCn
      have hCn_cont : ∀ n, Continuous (Cn n) := fun n =>
        HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
      have hptwise : ∀ x, Filter.Tendsto (fun n => Cn n x) Filter.atTop (nhds (h x)) := fun x =>
        ContDiffBump.convolution_tendsto_right_of_continuous hφrout hh_smooth.continuous x
      have hCnbd : ∀ n x, ‖Cn n x‖ ≤ M := by
        intro n x
        set ρ := (φ n).normed volume with hρ
        have hρnn : ∀ t, 0 ≤ ρ t := (φ n).nonneg_normed
        rw [hCn]; simp only; rw [MeasureTheory.convolution_def]
        calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t)) ∂volume‖
            ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (x - t))‖ ∂volume :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ t, ρ t * M ∂volume := by
              have hint : Integrable ρ volume :=
                ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
                  ((φ n).hasCompactSupport_normed)
              apply integral_mono_of_nonneg
                (Filter.Eventually.of_forall (fun t => norm_nonneg _)) (hint.mul_const M)
              refine Filter.Eventually.of_forall (fun t => ?_)
              simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hρnn t)]
              exact mul_le_mul_of_nonneg_left (hM _) (hρnn t)
          _ = (∫ t, ρ t ∂volume) * M := by rw [integral_mul_const]
          _ = M := by rw [(φ n).integral_normed]; ring
      have hMh : ∀ y, ‖h y‖ ≤ M := hM
      have hsupp_in_K : ∀ᶠ n in Filter.atTop, Function.support (Cn n) ⊆ Kset := by
        have hev : ∀ᶠ n in Filter.atTop, (φ n).rOut ≤ 1 := by
          have := hφrout.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
          filter_upwards [this] with n hn using hn
        filter_upwards [hev] with n hrout1
        have haddsub : Metric.closedBall (0 : ℂ) (φ n).rOut + tsupport h ⊆ Kset := by
          intro z hz
          obtain ⟨a, ha, b, hb, rfl⟩ := hz
          rw [Metric.mem_closedBall, dist_zero_right] at ha
          refine Metric.mem_cthickening_of_dist_le (a + b) b 1 (tsupport h) hb ?_
          rw [dist_eq_norm]; simp only [add_sub_cancel_right]; exact le_trans ha hrout1
        have hsub := MeasureTheory.support_convolution_subset (μ := volume)
          (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ))
          (f := (φ n).normed volume) (g := h)
        refine hsub.trans (le_trans ?_ haddsub)
        apply Set.add_subset_add _ (subset_tsupport h)
        intro z hz
        have h1 : z ∈ tsupport ((φ n).normed volume) := subset_tsupport _ hz
        rwa [(φ n).tsupport_normed_eq] at h1
      have : MeasureTheory.IsFiniteMeasure (volume.restrict Kset) := by
        constructor; rw [MeasureTheory.Measure.restrict_apply_univ]; exact hKfin
      set D : ℕ → ℂ → ℂ := fun n => Cn n - h with hD
      have hrestrict : ∀ᶠ n in Filter.atTop,
          eLpNorm (D n) 2 volume = eLpNorm (D n) 2 (volume.restrict Kset) := by
        filter_upwards [hsupp_in_K] with n hn
        have hDsupp : Function.support (D n) ⊆ Kset := by
          intro x hx
          simp only [hD, Pi.sub_apply, Function.mem_support, ne_eq] at hx
          by_contra hxK
          have h1 : Cn n x = 0 := Function.notMem_support.mp (fun hc => hxK (hn hc))
          have h2 : h x = 0 := Function.notMem_support.mp
            (fun hc => hxK (htsupp_sub (subset_tsupport h hc)))
          rw [h1, h2, sub_zero] at hx; exact hx rfl
        rw [← eLpNorm_indicator_eq_eLpNorm_restrict hKmeas, Set.indicator_eq_self.mpr hDsupp]
      have hgoal : Filter.Tendsto (fun n => eLpNorm (D n) 2 (volume.restrict Kset))
          Filter.atTop (nhds 0) := by
        have hui : MeasureTheory.UnifIntegrable Cn 2 (volume.restrict Kset) := by
          refine MeasureTheory.unifIntegrable_of (by norm_num) (by norm_num)
            (fun n => (hCn_cont n).aestronglyMeasurable) (fun ε hε => ?_)
          refine ⟨(M.toNNReal + 1), fun n => ?_⟩
          have hempty : {x | (M.toNNReal + 1 : ℝ≥0) ≤ ‖Cn n x‖₊} = (∅ : Set ℂ) := by
            ext x
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
            have hb' : ‖Cn n x‖₊ ≤ M.toNNReal := by
              rw [← NNReal.coe_le_coe, Real.coe_toNNReal M hM0]; exact hCnbd n x
            exact lt_of_le_of_lt hb' (by simp)
          rw [hempty, Set.indicator_empty]; simp
        have hhmem : MemLp h 2 (volume.restrict Kset) :=
          MemLp.of_bound hh_smooth.continuous.aestronglyMeasurable M
            (Filter.Eventually.of_forall hMh)
        exact MeasureTheory.tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
          (fun n => (hCn_cont n).aestronglyMeasurable) hhmem hui
          (Filter.Eventually.of_forall hptwise)
      exact Filter.Tendsto.congr' (hrestrict.mono (fun n hn => hn.symm)) hgoal
    have hP2 : ∀ (u : ℂ → ℂ), MemLp u 2 volume → ∀ (ε : ℝ),
        eLpNorm u 2 volume ≤ ENNReal.ofReal ε → ∀ n,
          eLpNorm (MeasureTheory.convolution ((φ n).normed volume) u
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume ≤ ENNReal.ofReal ε := by
      intro u hu ε hclose n
      set ρc : ℂ → ℂ := fun z => (((φ n).normed volume z : ℝ) : ℂ) with hρc
      have hconv_eq : MeasureTheory.convolution ((φ n).normed volume) u
            (ContinuousLinearMap.lsmul ℝ ℝ) volume
          = MeasureTheory.convolution ρc u (ContinuousLinearMap.mul ℂ ℂ) volume := by
        funext x
        rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        simp only [hρc, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply]
        exact (Complex.real_smul).symm
      rw [hconv_eq]
      have hρc_memLp : MemLp ρc 1 volume := by
        have hcont : Continuous ρc :=
          Complex.continuous_ofReal.comp ((φ n).contDiff_normed (n := 0)).continuous
        have hsupp : HasCompactSupport ρc :=
          ((φ n).hasCompactSupport_normed).comp_left (g := (fun r : ℝ => (r : ℂ))) (by simp)
        exact hcont.memLp_of_hasCompactSupport hsupp
      have hρc_norm : eLpNorm ρc 1 volume = 1 := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        have hint : Integrable ((φ n).normed volume) volume :=
          ((φ n).contDiff_normed (n := 0)).continuous.integrable_of_hasCompactSupport
            ((φ n).hasCompactSupport_normed)
        have hnn : 0 ≤ᵐ[volume] (φ n).normed volume :=
          Filter.Eventually.of_forall (fun z => (φ n).nonneg_normed z)
        calc ∫⁻ z, ‖ρc z‖ₑ ∂volume
            = ∫⁻ z, ENNReal.ofReal ((φ n).normed volume z) ∂volume := by
              refine lintegral_congr (fun z => ?_)
              rw [hρc,
                show ‖(((φ n).normed volume z : ℝ) : ℂ)‖ₑ
                    = ‖(φ n).normed volume z‖ₑ from by
                  rw [← enorm_norm, Complex.norm_real, enorm_norm],
                Real.enorm_of_nonneg ((φ n).nonneg_normed z)]
          _ = ENNReal.ofReal (∫ z, (φ n).normed volume z ∂volume) :=
              (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
          _ = 1 := by rw [(φ n).integral_normed]; simp
      calc eLpNorm (MeasureTheory.convolution ρc u (ContinuousLinearMap.mul ℂ ℂ)
              volume) 2 volume
          ≤ eLpNorm ρc 1 volume * eLpNorm u 2 volume :=
            eLpNorm_convolution_le hρc_memLp hu
        _ = eLpNorm u 2 volume := by rw [hρc_norm, one_mul]
        _ ≤ ENNReal.ofReal ε := hclose
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases htop : ε = ⊤
    · refine Filter.Eventually.of_forall (fun n => ?_)
      rw [htop]; exact le_top
    set δ : ℝ := ε.toReal with hδ
    have hδpos : 0 < δ := ENNReal.toReal_pos hε.ne' htop
    have hδle : ENNReal.ofReal δ = ε := ENNReal.ofReal_toReal htop
    obtain ⟨hh, hh_supp, hh_smooth, hh_close⟩ := hg.exist_eLpNorm_sub_le
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (ε := δ / 3) (by positivity)
    have hh_memLp : MemLp hh 2 volume :=
      hh_smooth.continuous.memLp_of_hasCompactSupport hh_supp
    have hgh_memLp : MemLp (g - hh) 2 volume := hg.sub hh_memLp
    have hP2gh : ∀ n, eLpNorm (MeasureTheory.convolution ((φ n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume
          ≤ ENNReal.ofReal (δ / 3) :=
      hP2 (g - hh) hgh_memLp (δ / 3) hh_close
    have hP3ev : ∀ᶠ n in Filter.atTop,
        eLpNorm (MeasureTheory.convolution ((φ n).normed volume) hh
          (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) 2 volume
          ≤ ENNReal.ofReal (δ / 3) :=
      (ENNReal.tendsto_nhds_zero.mp (hP3 hh hh_supp hh_smooth) (ENNReal.ofReal (δ / 3))
        (ENNReal.ofReal_pos.mpr (by positivity)))
    have hdecomp : ∀ n, Cg n - g = MeasureTheory.convolution ((φ n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
        + (MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - g) := by
      intro n
      have hce1 : MeasureTheory.ConvolutionExists ((φ n).normed volume) (g - hh)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        refine HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous ?_
        exact (hg.locallyIntegrable (by norm_num)).sub hh_smooth.continuous.locallyIntegrable
      have hce2 : MeasureTheory.ConvolutionExists ((φ n).normed volume) hh
          (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
        HasCompactSupport.convolutionExists_left _ ((φ n).hasCompactSupport_normed)
          ((φ n).contDiff_normed (n := 0)).continuous hh_smooth.continuous.locallyIntegrable
      have hsplit : Cg n = MeasureTheory.convolution ((φ n).normed volume)
            (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
          + MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
        rw [hCg]; simp only
        rw [← MeasureTheory.ConvolutionExists.distrib_add hce1 hce2]
        congr 1; abel
      rw [hsplit]; abel
    filter_upwards [hP3ev] with n hn3
    rw [hdecomp n]
    have hm1 : AEStronglyMeasurable (MeasureTheory.convolution
        ((φ n).normed volume) (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ)
        volume) volume :=
      (HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous
        ((hg.locallyIntegrable (by norm_num)).sub
          hh_smooth.continuous.locallyIntegrable)).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (MeasureTheory.convolution
        ((φ n).normed volume) hh (ContinuousLinearMap.lsmul ℝ ℝ)
        volume - hh) volume :=
      ((HasCompactSupport.continuous_convolution_left _ ((φ n).hasCompactSupport_normed)
        ((φ n).contDiff_normed (n := 0)).continuous
        hh_smooth.continuous.locallyIntegrable).sub hh_smooth.continuous).aestronglyMeasurable
    have hm3 : AEStronglyMeasurable (hh - g) volume :=
      (hh_memLp.sub hg).1
    have hkey : eLpNorm (MeasureTheory.convolution ((φ n).normed volume)
          (g - hh) (ContinuousLinearMap.lsmul ℝ ℝ) volume
        + (MeasureTheory.convolution ((φ n).normed volume) hh
            (ContinuousLinearMap.lsmul ℝ ℝ) volume - hh) + (hh - g)) 2
          volume
        ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) := by
      refine le_trans (eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)) ?_
      refine add_le_add (le_trans (eLpNorm_add_le hm1 hm2 (by norm_num)) ?_) ?_
      · exact add_le_add (hP2gh n) hn3
      · rw [eLpNorm_sub_comm]; exact hh_close
    refine le_trans hkey ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← hδle]
    apply le_of_eq; congr 1; ring
  have fderiv_conv : ∀ {f gv : ℂ → ℂ} {v : ℂ},
      HasWeakDirDeriv v gv f Set.univ →
      MeasureTheory.LocallyIntegrable f → MeasureTheory.LocallyIntegrable gv →
      ∀ {ρ : ℂ → ℝ}, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ →
      HasCompactSupport ρ → ∀ (z : ℂ),
        (fderiv ℝ (MeasureTheory.convolution ρ f
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) z) v
          = MeasureTheory.convolution ρ gv (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
    intro f gv v hv hf hgv ρ hρ_smooth hρ_supp z
    have _hgv := hgv
    set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
    have hρ_one : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) ρ := hρ_smooth.of_le (by exact_mod_cast le_top)
    have hρ_diff : Differentiable ℝ ρ :=
      hρ_one.differentiable (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))
    have hdρ_supp : HasCompactSupport (fderiv ℝ ρ) := hρ_supp.fderiv ℝ
    have hderiv :
        HasFDerivAt (MeasureTheory.convolution ρ f L volume)
          (MeasureTheory.convolution (fderiv ℝ ρ) f (L.precompL ℂ) volume z) z :=
      HasCompactSupport.hasFDerivAt_convolution_left L hρ_supp hρ_one hf z
    rw [hderiv.fderiv]
    have hconvexists :
        MeasureTheory.ConvolutionExistsAt (fderiv ℝ ρ) f z (L.precompL ℂ) volume :=
      (hdρ_supp.convolutionExists_left (L.precompL ℂ)
        (hρ_one.continuous_fderiv (by exact_mod_cast (one_ne_zero : (1 : ℕ∞) ≠ 0))) hf) z
    rw [MeasureTheory.convolution_def,
        ContinuousLinearMap.integral_apply hconvexists.integrable]
    simp only [ContinuousLinearMap.precompL_apply, hL, ContinuousLinearMap.lsmul_apply]
    have hcv :
        (∫ t, ((fderiv ℝ ρ t) v) • f (z - t) ∂volume)
          = ∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂volume := by
      have hself := MeasureTheory.integral_sub_left_eq_self
        (fun t => ((fderiv ℝ ρ t) v) • f (z - t)) volume z
      simp only [sub_sub_cancel] at hself
      exact hself.symm
    refine hcv.trans ?_
    set φz : ℂ → ℝ := fun u => ρ (z - u) with hφz
    have hφz_fderiv : ∀ u, (fderiv ℝ φz u) v = -((fderiv ℝ ρ (z - u)) v) := by
      intro u
      have hsub : HasFDerivAt (fun u : ℂ => z - u) (-ContinuousLinearMap.id ℝ ℂ) u := by
        simpa using (hasFDerivAt_id u).const_sub z
      have hcomp : HasFDerivAt φz
          ((fderiv ℝ ρ (z - u)).comp (-ContinuousLinearMap.id ℝ ℂ)) u :=
        (hρ_diff (z - u)).hasFDerivAt.comp u hsub
      rw [hcomp.fderiv]
      simp only [ContinuousLinearMap.comp_apply, neg_apply,
        ContinuousLinearMap.id_apply, map_neg]
    have hint_eq :
        (∫ u, ((fderiv ℝ ρ (z - u)) v) • f u ∂volume)
          = -∫ u, ((fderiv ℝ φz u) v) • f u ∂volume := by
      rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      change ((fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ φz u) v) • f u)
      rw [hφz_fderiv u]
      rw [show (-(fderiv ℝ ρ (z - u)) v) • f u = -(((fderiv ℝ ρ (z - u)) v) • f u)
        from neg_smul _ _, neg_neg]
    rw [hint_eq]
    have hφz_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φz :=
      hρ_smooth.comp (contDiff_const.sub contDiff_id)
    have hφz_supp : HasCompactSupport φz :=
      hρ_supp.comp_homeomorph (Homeomorph.subLeft z)
    have hwd := hv φz hφz_smooth hφz_supp (Set.subset_univ _)
    rw [hwd, neg_neg]
    rw [MeasureTheory.convolution_def, ← MeasureTheory.integral_sub_left_eq_self
        (fun t => (L (ρ t)) (gv (z - t))) volume z]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only [hφz, sub_sub_cancel, hL, ContinuousLinearMap.lsmul_apply]
  -- L¹(B) integral convergence helper (from L²(B) convergence). 
  have limconv : ∀ (B : Set ℂ), MeasurableSet B → volume B ≠ ⊤ →
      ∀ (fF : ℂ → ℂ) (fnF : ℕ → ℂ → ℂ),
      (∀ n, AEStronglyMeasurable (fnF n) volume) → AEStronglyMeasurable fF volume →
      (∫⁻ z in B, ‖fF z‖ₑ ∂volume) ≠ ⊤ →
      Tendsto (fun n => eLpNorm (fun z => fnF n z - fF z) 2 (volume.restrict B)) atTop (𝓝 0) →
      Tendsto (fun n => ∫⁻ z in B, ‖fnF n z‖ₑ ∂volume) atTop
        (𝓝 (∫⁻ z in B, ‖fF z‖ₑ ∂volume)) := by
    intro B hBmeas hBfin f fn hfm hfm0 hIffin hconv
    have hdist : Tendsto (fun n => ∫⁻ z in B, ‖fn n z - f z‖ₑ ∂volume) atTop (𝓝 0) := by
      have hbound : ∀ n, (∫⁻ z in B, ‖fn n z - f z‖ₑ ∂volume)
          ≤ eLpNorm (fun z => fn n z - f z) 2 (volume.restrict B) * (volume B) ^ (1/2 : ℝ) := by
        intro n
        have h1 : (∫⁻ z in B, ‖fn n z - f z‖ₑ ∂volume)
            = eLpNorm (fun z => fn n z - f z) 1 (volume.restrict B) := by
          rw [eLpNorm_one_eq_lintegral_enorm]
        rw [h1]
        have hle := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict B)
          (p := 1) (q := 2) (f := fun z => fn n z - f z) (by norm_num)
          ((hfm n).sub hfm0).restrict
        rw [Measure.restrict_apply_univ,
          show (1 / ENNReal.toReal 1 - 1 / ENNReal.toReal 2) = (1/2 : ℝ) by norm_num] at hle
        exact hle
      have hVBfin : ((volume B) ^ (1/2 : ℝ)) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBfin
      have hrhs : Tendsto (fun n => eLpNorm (fun z => fn n z - f z) 2 (volume.restrict B)
          * (volume B) ^ (1/2 : ℝ)) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.mul_const hconv (Or.inr hVBfin); simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ≥0∞)) tendsto_const_nhds
        hrhs (fun n => zero_le) hbound
    set If := ∫⁻ z in B, ‖f z‖ₑ ∂volume with hIf
    set dn := fun n => ∫⁻ z in B, ‖fn n z - f z‖ₑ ∂volume with hdn
    have hae : ∀ n, AEMeasurable (fun z => ‖fn n z - f z‖ₑ) (volume.restrict B) :=
      fun n => (((hfm n).sub hfm0).restrict).aemeasurable.enorm
    have key1 : ∀ n, (∫⁻ z in B, ‖fn n z‖ₑ ∂volume) ≤ If + dn n := by
      intro n
      have : If + dn n = ∫⁻ z in B, (‖f z‖ₑ + ‖fn n z - f z‖ₑ) ∂volume := by
        rw [hIf, hdn]; simp only []; rw [lintegral_add_right' _ (hae n)]
      rw [this]
      refine lintegral_mono (fun z => ?_)
      calc ‖fn n z‖ₑ = ‖f z + (fn n z - f z)‖ₑ := by congr 1; ring
        _ ≤ ‖f z‖ₑ + ‖fn n z - f z‖ₑ := enorm_add_le _ _
    have key2 : ∀ n, If ≤ (∫⁻ z in B, ‖fn n z‖ₑ ∂volume) + dn n := by
      intro n
      have : (∫⁻ z in B, ‖fn n z‖ₑ ∂volume) + dn n
          = ∫⁻ z in B, (‖fn n z‖ₑ + ‖fn n z - f z‖ₑ) ∂volume := by
        rw [hdn]; simp only []; rw [lintegral_add_right' _ (hae n)]
      rw [this, hIf]
      refine lintegral_mono (fun z => ?_)
      calc ‖f z‖ₑ = ‖fn n z + (f z - fn n z)‖ₑ := by congr 1; ring
        _ ≤ ‖fn n z‖ₑ + ‖f z - fn n z‖ₑ := enorm_add_le _ _
        _ = ‖fn n z‖ₑ + ‖fn n z - f z‖ₑ := by rw [← enorm_neg (fn n z - f z), neg_sub]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun n => If - dn n) (h := fun n => If + dn n) ?_ ?_ ?_ key1
    · have : Tendsto (fun n => If - dn n) atTop (𝓝 (If - 0)) :=
        ENNReal.Tendsto.sub tendsto_const_nhds hdist (Or.inr (by simp))
      simpa using this
    · have : Tendsto (fun n => If + dn n) atTop (𝓝 (If + 0)) :=
        Tendsto.add tendsto_const_nhds hdist
      simpa using this
    · intro n; exact tsub_le_iff_right.mpr (key2 n)
  -- average convergence helper.
  have avgconv : ∀ (B : Set ℂ), volume B ≠ ⊤ → volume B ≠ 0 →
      ∀ (fF : ℂ → ℂ) (fnF : ℕ → ℂ → ℂ),
      (∀ n, IntegrableOn (fnF n) B volume) → IntegrableOn fF B volume →
      Tendsto (fun n => eLpNorm (fun z => fnF n z - fF z) 1 (volume.restrict B)) atTop (𝓝 0) →
      Tendsto (fun n => ⨍ w in B, fnF n w ∂volume) atTop (𝓝 (⨍ w in B, fF w ∂volume)) := by
    intro B hBfin hBpos F Fn hFn_int hF_int hconvF
    have : IsFiniteMeasure (volume.restrict B) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hBfin.lt_top⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ n, ‖(⨍ w in B, Fn n w ∂volume) - (⨍ w in B, F w ∂volume)‖
        ≤ (volume.real B)⁻¹ * (eLpNorm (fun z => Fn n z - F z) 1 (volume.restrict B)).toReal := by
      intro n
      set g : ℂ → ℂ := fun z => Fn n z - F z with hgdef
      have hgint : IntegrableOn g B volume := (hFn_int n).sub hF_int
      rw [setAverage_eq, setAverage_eq, ← smul_sub,
        show (∫ x in B, Fn n x ∂volume) - ∫ x in B, F x ∂volume = ∫ x in B, g x ∂volume from
          (integral_sub (hFn_int n) hF_int).symm,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
      rw [eLpNorm_one_eq_lintegral_enorm]
      calc ‖∫ z in B, g z ∂volume‖
          ≤ ∫ z in B, ‖g z‖ ∂volume := norm_integral_le_integral_norm _
        _ = (∫⁻ z in B, ‖g z‖ₑ ∂volume).toReal := by
            rw [integral_norm_eq_lintegral_enorm hgint.aestronglyMeasurable]
    have hrhs : Tendsto (fun n => (volume.real B)⁻¹ *
        (eLpNorm (fun z => Fn n z - F z) 1 (volume.restrict B)).toReal) atTop (𝓝 0) := by
      have htoreal : Tendsto
          (fun n => (eLpNorm (fun z => Fn n z - F z) 1 (volume.restrict B)).toReal)
          atTop (𝓝 0) := by
        have := (ENNReal.tendsto_toReal (by norm_num)).comp hconvF
        simpa [Function.comp_def] using this
      have := htoreal.const_mul ((volume.real B)⁻¹); simpa using this
    exact squeeze_zero (fun n => norm_nonneg _) hbound hrhs
  -- LHS oscillation L²(B) convergence helper.
  have lhsconv : ∀ (B : Set ℂ), volume B ≠ ⊤ → volume B ≠ 0 →
      ∀ (fF : ℂ → ℂ) (fnF : ℕ → ℂ → ℂ),
      (∀ n, Continuous (fnF n)) → MemLp fF 2 volume →
      Tendsto (fun n => eLpNorm (fun z => fnF n z - fF z) 2 (volume.restrict B)) atTop (𝓝 0) →
      Tendsto (fun n => (⨍ w in B, fnF n w ∂volume) - (⨍ w in B, fF w ∂volume)) atTop (𝓝 0) →
      Tendsto (fun n => eLpNorm (fun z => (fnF n z - (⨍ w in B, fnF n w ∂volume))
          - (fF z - (⨍ w in B, fF w ∂volume))) 2 (volume.restrict B)) atTop (𝓝 0) := by
    intro B hBfin hBpos F Fn hFn_cont hFmem hconvF hcn
    have : IsFiniteMeasure (volume.restrict B) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hBfin.lt_top⟩
    have hμne : (volume.restrict B) ≠ 0 := by
      rw [← Measure.measure_univ_ne_zero, Measure.restrict_apply_univ]; exact hBpos
    set cn : ℕ → ℂ := fun n => (⨍ w in B, Fn n w ∂volume) - (⨍ w in B, F w ∂volume) with hcndef
    have hbound : ∀ n, eLpNorm (fun z => (Fn n z - (⨍ w in B, Fn n w ∂volume))
          - (F z - (⨍ w in B, F w ∂volume))) 2 (volume.restrict B)
        ≤ eLpNorm (fun z => Fn n z - F z) 2 (volume.restrict B)
          + ‖cn n‖ₑ * (volume B) ^ (1 / (2:ℝ)) := by
      intro n
      have heq : (fun z => (Fn n z - (⨍ w in B, Fn n w ∂volume))
            - (F z - (⨍ w in B, F w ∂volume)))
          = (fun z => (Fn n z - F z) + (fun _ : ℂ => -cn n) z) := by
        funext z; simp only [hcndef]; ring
      rw [heq]
      refine le_trans (eLpNorm_add_le (((hFn_cont n).aestronglyMeasurable.sub hFmem.1).restrict)
        aestronglyMeasurable_const (by norm_num)) ?_
      gcongr
      rw [eLpNorm_const (-cn n) (by norm_num) hμne, Measure.restrict_apply_univ, enorm_neg,
        show (1 / ENNReal.toReal 2) = (1/2 : ℝ) by norm_num]
    have hrhs : Tendsto (fun n => eLpNorm (fun z => Fn n z - F z) 2 (volume.restrict B)
        + ‖cn n‖ₑ * (volume B) ^ (1 / (2:ℝ))) atTop (𝓝 0) := by
      have hc : Tendsto (fun n => ‖cn n‖ₑ) atTop (𝓝 0) := by
        have := (continuous_enorm.tendsto (0:ℂ)).comp hcn
        simpa [Function.comp_def] using this
      have hVBfin : ((volume B) ^ (1/2 : ℝ)) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBfin
      have hc2 : Tendsto (fun n => ‖cn n‖ₑ * (volume B) ^ (1 / (2:ℝ))) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.mul_const hc (Or.inr hVBfin); simpa using this
      have := hconvF.add hc2; simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ≥0∞))
      tendsto_const_nhds hrhs (fun n => zero_le) hbound
  -- ============================================================
  -- WIRING: mollify F, apply the smooth Poincaré, pass to the limit.
  -- ============================================================
  set B := ball x r with hB
  have hBmeas : MeasurableSet B := measurableSet_ball
  have hBfin : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hBpos : volume B ≠ 0 := (measure_ball_pos volume x hr).ne'
  have hF_li : MeasureTheory.LocallyIntegrable F := hF.locallyIntegrable (by norm_num)
  have hGx_li : MeasureTheory.LocallyIntegrable Gx := hGx.locallyIntegrable (by norm_num)
  have hGy_li : MeasureTheory.LocallyIntegrable Gy := hGy.locallyIntegrable (by norm_num)
  set φ₀ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ₀
  have hφ₀rout : Tendsto (fun n => (φ₀ n).rOut) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => (φ₀ n).rOut) = fun n : ℕ => (2 : ℝ) / (n + 2) := rfl
    rw [heq]
    exact Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  set ρ : ℕ → ℂ → ℝ := fun n => (φ₀ n).normed volume with hρ
  have hρ_smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n => (φ₀ n).contDiff_normed
  have hρ_cs : ∀ n, HasCompactSupport (ρ n) := fun n => (φ₀ n).hasCompactSupport_normed
  have hρ_cont : ∀ n, Continuous (ρ n) := fun n => (hρ_smooth n).continuous
  set Fn : ℕ → ℂ → ℂ := fun n =>
    MeasureTheory.convolution (ρ n) F (ContinuousLinearMap.lsmul ℝ ℝ) volume with hFn
  set Gxn : ℕ → ℂ → ℂ := fun n =>
    MeasureTheory.convolution (ρ n) Gx (ContinuousLinearMap.lsmul ℝ ℝ) volume with hGxn
  set Gyn : ℕ → ℂ → ℂ := fun n =>
    MeasureTheory.convolution (ρ n) Gy (ContinuousLinearMap.lsmul ℝ ℝ) volume with hGyn
  have hFn_cd : ∀ n, ContDiff ℝ 1 (Fn n) := fun n =>
    HasCompactSupport.contDiff_convolution_left _ (hρ_cs n)
      ((hρ_smooth n).of_le (by exact_mod_cast le_top)) hF_li
  have hdx : ∀ n z, (fderiv ℝ (Fn n) z) 1 = Gxn n z := fun n z =>
    fderiv_conv hGxw hF_li hGx_li (hρ_smooth n) (hρ_cs n) z
  have hdy : ∀ n z, (fderiv ℝ (Fn n) z) Complex.I = Gyn n z := fun n z =>
    fderiv_conv hGyw hF_li hGy_li (hρ_smooth n) (hρ_cs n) z
  have hGxn_cont : ∀ n, Continuous (Gxn n) := fun n =>
    HasCompactSupport.continuous_convolution_left _ (hρ_cs n) (hρ_cont n) hGx_li
  have hGyn_cont : ∀ n, Continuous (Gyn n) := fun n =>
    HasCompactSupport.continuous_convolution_left _ (hρ_cs n) (hρ_cont n) hGy_li
  have hBfinm : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hBfin.lt_top⟩
  -- L²(B) and L¹(B) convergence of Fn, Gxn, Gyn.
  have hconvF2 : Tendsto (fun n => eLpNorm (fun z => Fn n z - F z) 2 (volume.restrict B))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ≥0∞))
      tendsto_const_nhds (conv_tendsto hF φ₀ hφ₀rout) (fun n => zero_le)
      (fun n => eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hconvGx : Tendsto (fun n => eLpNorm (fun z => Gxn n z - Gx z) 2 (volume.restrict B))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ≥0∞))
      tendsto_const_nhds (conv_tendsto hGx φ₀ hφ₀rout) (fun n => zero_le)
      (fun n => eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hconvGy : Tendsto (fun n => eLpNorm (fun z => Gyn n z - Gy z) 2 (volume.restrict B))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ≥0∞))
      tendsto_const_nhds (conv_tendsto hGy φ₀ hφ₀rout) (fun n => zero_le)
      (fun n => eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hconvF1 : Tendsto (fun n => eLpNorm (fun z => Fn n z - F z) 1 (volume.restrict B))
      atTop (𝓝 0) := by
    have hb : ∀ n, eLpNorm (fun z => Fn n z - F z) 1 (volume.restrict B)
        ≤ eLpNorm (fun z => Fn n z - F z) 2 (volume.restrict B) * (volume B) ^ (1/2 : ℝ) := by
      intro n
      have hle := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict B)
        (p := 1) (q := 2) (f := fun z => Fn n z - F z) (by norm_num)
        (((hFn_cd n).continuous.aestronglyMeasurable.sub hF.1).restrict)
      rwa [Measure.restrict_apply_univ,
        show (1 / ENNReal.toReal 1 - 1 / ENNReal.toReal 2) = (1/2 : ℝ) by norm_num] at hle
    have hVBfin : ((volume B) ^ (1/2 : ℝ)) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBfin
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ≥0∞))
      tendsto_const_nhds ?_ (fun n => zero_le) hb
    have := ENNReal.Tendsto.mul_const hconvF2 (Or.inr hVBfin); simpa using this
  have hFn_intB : ∀ n, IntegrableOn (Fn n) B volume := fun n =>
    ((hFn_cd n).continuous.locallyIntegrable.integrableOn_isCompact
      (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  have hF_intB : IntegrableOn F B volume :=
    (hF_li.integrableOn_isCompact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  have havgconv : Tendsto (fun n => (⨍ w in B, Fn n w ∂volume) - (⨍ w in B, F w ∂volume))
      atTop (𝓝 0) := by
    have h0 := avgconv B hBfin hBpos F Fn hFn_intB hF_intB hconvF1
    have := h0.sub (tendsto_const_nhds (x := ⨍ w in B, F w ∂volume)); simpa using this
  have hLHSconv : Tendsto (fun n => eLpNorm (fun z => (Fn n z - (⨍ w in B, Fn n w ∂volume))
        - (F z - (⨍ w in B, F w ∂volume))) 2 (volume.restrict B)) atTop (𝓝 0) :=
    lhsconv B hBfin hBpos F Fn (fun n => (hFn_cd n).continuous) hF hconvF2 havgconv
  -- finiteness of the L¹(B) norms of F-F_B, Gx, Gy.
  have hGxfin : (∫⁻ z in B, ‖Gx z‖ₑ ∂volume) ≠ ⊤ := by
    have h1 : MemLp Gx 1 (volume.restrict B) := (hGx.restrict B).mono_exponent (by norm_num)
    have := h1.eLpNorm_lt_top; rw [eLpNorm_one_eq_lintegral_enorm] at this; exact this.ne
  have hGyfin : (∫⁻ z in B, ‖Gy z‖ₑ ∂volume) ≠ ⊤ := by
    have h1 : MemLp Gy 1 (volume.restrict B) := (hGy.restrict B).mono_exponent (by norm_num)
    have := h1.eLpNorm_lt_top; rw [eLpNorm_one_eq_lintegral_enorm] at this; exact this.ne
  have hOscfin : (∫⁻ z in B, ‖F z - (⨍ w in B, F w ∂volume)‖ₑ ∂volume) ≠ ⊤ := by
    have hmem : MemLp (fun z => F z - (⨍ w in B, F w ∂volume)) 1 (volume.restrict B) := by
      refine MemLp.sub ((hF.restrict B).mono_exponent (by norm_num)) ?_
      exact memLp_const _
    have := hmem.eLpNorm_lt_top; rw [eLpNorm_one_eq_lintegral_enorm] at this; exact this.ne
  -- Integral-convergence of LHS and RHS.
  have hRGx : Tendsto (fun n => ∫⁻ z in B, ‖Gxn n z‖ₑ ∂volume) atTop
      (𝓝 (∫⁻ z in B, ‖Gx z‖ₑ ∂volume)) :=
    limconv B hBmeas hBfin Gx Gxn (fun n => (hGxn_cont n).aestronglyMeasurable) hGx.1 hGxfin hconvGx
  have hRGy : Tendsto (fun n => ∫⁻ z in B, ‖Gyn n z‖ₑ ∂volume) atTop
      (𝓝 (∫⁻ z in B, ‖Gy z‖ₑ ∂volume)) :=
    limconv B hBmeas hBfin Gy Gyn (fun n => (hGyn_cont n).aestronglyMeasurable) hGy.1 hGyfin hconvGy
  have hLHSlim : Tendsto (fun n => ∫⁻ z in B, ‖(Fn n z - (⨍ w in B, Fn n w ∂volume))
        - (F z - (⨍ w in B, F w ∂volume)) + (F z - (⨍ w in B, F w ∂volume))‖ₑ ∂volume) atTop
      (𝓝 (∫⁻ z in B, ‖F z - (⨍ w in B, F w ∂volume)‖ₑ ∂volume)) := by
    refine limconv B hBmeas hBfin (fun z => F z - (⨍ w in B, F w ∂volume))
      (fun n z => (Fn n z - (⨍ w in B, Fn n w ∂volume)) - (F z - (⨍ w in B, F w ∂volume))
        + (F z - (⨍ w in B, F w ∂volume))) ?_ ?_ hOscfin ?_
    · intro n
      exact ((((hFn_cd n).continuous.aestronglyMeasurable.sub aestronglyMeasurable_const).sub
        (hF.1.sub aestronglyMeasurable_const)).add (hF.1.sub aestronglyMeasurable_const))
    · exact hF.1.sub aestronglyMeasurable_const
    · simpa using hLHSconv
  -- The per-n smooth Poincaré inequality.
  have hper : ∀ n, ∫⁻ z in B, ‖Fn n z - (⨍ w in B, Fn n w ∂volume)‖ₑ ∂volume
      ≤ ENNReal.ofReal (8 * r) *
        ((∫⁻ z in B, ‖Gxn n z‖ₑ ∂volume) + ∫⁻ z in B, ‖Gyn n z‖ₑ ∂volume) := by
    intro n
    refine le_trans (smooth_poincare (Fn n) (hFn_cd n) x r hr) ?_
    refine mul_le_mul' (le_refl _) ?_
    -- ∫⁻_B ‖∇Fn‖ₑ ≤ ∫⁻_B (‖Gxn‖ₑ + ‖Gyn‖ₑ).
    rw [← lintegral_add_left' ((hGxn_cont n).aestronglyMeasurable.aemeasurable.enorm.restrict)]
    refine lintegral_mono (fun z => ?_)
    -- pointwise ‖fderiv (Fn n) z‖ₑ ≤ ‖(fderiv (Fn n) z) 1‖ₑ + ‖(fderiv (Fn n) z) I‖ₑ
    have hptw : ‖fderiv ℝ (Fn n) z‖ ≤
        ‖(fderiv ℝ (Fn n) z) 1‖ + ‖(fderiv ℝ (Fn n) z) Complex.I‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro w
      have hdecomp : w = w.re • (1 : ℂ) + w.im • Complex.I := by
        apply Complex.ext <;> simp [Complex.real_smul]
      have hmap : (fderiv ℝ (Fn n) z) w
          = w.re • (fderiv ℝ (Fn n) z) 1 + w.im • (fderiv ℝ (Fn n) z) Complex.I := by
        conv_lhs => rw [hdecomp]; rw [map_add, map_smul, map_smul]
      rw [hmap]
      calc ‖w.re • (fderiv ℝ (Fn n) z) 1 + w.im • (fderiv ℝ (Fn n) z) Complex.I‖
          ≤ ‖w.re • (fderiv ℝ (Fn n) z) 1‖ + ‖w.im • (fderiv ℝ (Fn n) z) Complex.I‖ :=
            norm_add_le _ _
        _ = |w.re| * ‖(fderiv ℝ (Fn n) z) 1‖ + |w.im| * ‖(fderiv ℝ (Fn n) z) Complex.I‖ := by
            rw [Complex.real_smul, Complex.real_smul, norm_mul, norm_mul,
              Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ ‖w‖ * ‖(fderiv ℝ (Fn n) z) 1‖ + ‖w‖ * ‖(fderiv ℝ (Fn n) z) Complex.I‖ := by
            gcongr
            · exact abs_re_le_norm w
            · exact abs_im_le_norm w
        _ = (‖(fderiv ℝ (Fn n) z) 1‖ + ‖(fderiv ℝ (Fn n) z) Complex.I‖) * ‖w‖ := by ring
    calc ‖fderiv ℝ (Fn n) z‖ₑ
        ≤ ‖(fderiv ℝ (Fn n) z) 1‖ₑ + ‖(fderiv ℝ (Fn n) z) Complex.I‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
            ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal hptw
      _ = ‖Gxn n z‖ₑ + ‖Gyn n z‖ₑ := by rw [hdx n z, hdy n z]
  -- Pass to the limit.
  have hLHSeq : (fun n => ∫⁻ z in B, ‖(Fn n z - (⨍ w in B, Fn n w ∂volume))
        - (F z - (⨍ w in B, F w ∂volume)) + (F z - (⨍ w in B, F w ∂volume))‖ₑ ∂volume)
      = fun n => ∫⁻ z in B, ‖Fn n z - (⨍ w in B, Fn n w ∂volume)‖ₑ ∂volume := by
    funext n
    refine lintegral_congr (fun z => ?_)
    congr 1; ring
  rw [hLHSeq] at hLHSlim
  -- RHS limit.
  have hRHSlim : Tendsto (fun n => ENNReal.ofReal (8 * r) *
      ((∫⁻ z in B, ‖Gxn n z‖ₑ ∂volume) + ∫⁻ z in B, ‖Gyn n z‖ₑ ∂volume)) atTop
      (𝓝 (ENNReal.ofReal (8 * r) *
        ((∫⁻ z in B, ‖Gx z‖ₑ ∂volume) + ∫⁻ z in B, ‖Gy z‖ₑ ∂volume))) :=
    ENNReal.Tendsto.const_mul (hRGx.add hRGy)
      (Or.inr ENNReal.ofReal_ne_top)
  have hfinal : ∫⁻ z in B, ‖F z - (⨍ w in B, F w ∂volume)‖ₑ ∂volume
      ≤ ENNReal.ofReal (8 * r) *
        ((∫⁻ z in B, ‖Gx z‖ₑ ∂volume) + ∫⁻ z in B, ‖Gy z‖ₑ ∂volume) :=
    le_of_tendsto_of_tendsto' hLHSlim hRHSlim hper
  -- Reconcile ‖·‖₊-coercions and the averaging notation with the goal.
  have hcoeL : (fun z => (‖F z - (⨍ w in B, F w)‖₊ : ℝ≥0∞))
      = fun z => ‖F z - (⨍ w in B, F w ∂volume)‖ₑ := by funext z; rw [← enorm_eq_nnnorm]
  have hcoeR : (fun z => (‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞))
      = fun z => ‖Gx z‖ₑ + ‖Gy z‖ₑ := by funext z; rw [← enorm_eq_nnnorm, ← enorm_eq_nnnorm]
  rw [show (⨍ w in B, F w) = (⨍ w in B, F w ∂volume) from rfl]
  rw [hcoeL]
  rw [show (∫⁻ z in B, ((‖Gx z‖₊ : ℝ≥0∞) + (‖Gy z‖₊ : ℝ≥0∞)) ∂volume)
      = ∫⁻ z in B, (‖Gx z‖ₑ + ‖Gy z‖ₑ) ∂volume from by rw [hcoeR]]
  rw [lintegral_add_left' (hGx.1.aemeasurable.enorm.restrict)]
  exact hfinal


end NoWanderingDomains
