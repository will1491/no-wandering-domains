/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Regularity.RingModulus
import NoWanderingDomains.Analysis.Symmetrization.CircularRearrangement
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Grötzsch and Teichmüller extremal estimates

This file states the **extremal length estimates** that drive all of planar quasiconformal
regularity: the Grötzsch and Teichmüller modulus inequalities. All moduli here are the
**connecting-family moduli** of `QC/Regularity/RingModulus.lean` (the `curveModulus` of the curves
joining the two boundary continua of a ring; for a round annulus `2π / log (R / r)`), so the
Grötzsch and Teichmüller configurations *minimize* the connecting modulus among rings separating two
prescribed continua — the reciprocal of the classical separating-module *maximum* property. They are
the *single hardest foundational input* of the regularity layer; everything downstream
(quasisymmetry, equicontinuity, normal families) is derived from them by `K`-quasiconformal modulus
distortion.

Each estimate below is a *true classical theorem*. None of them holds for a bare
homeomorphism: they are statements about the conformal
modulus of *concrete plane rings*, used downstream only through the inequality
`curveModulus (f-image family) ≤ K · curveModulus (family)` that defines `IsQCGeometric f K`. The
estimates here carry **no derivative control** — they are pure modulus facts about plane domains.

## Main statements

* `grotzschModulus_tendsto_zero_zero` — `grotzschModulus s → 0` as `s → 0⁺`, via an explicit
  round-annulus admissible density and a squeeze. This is the vanishing half of the extremal
  Grötzsch asymptotics; the sharp extremal theory (Grötzsch's inequality, the Teichmüller
  identity and comparison) is future work and is not stated here.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Real

namespace NoWanderingDomains

set_option maxHeartbeats 400000 in
-- The explicit round-annulus density witness carries a long single-tactic-block elaboration
-- (energy via polar coordinates, admissibility via the clamped radial coordinate); the default
-- heartbeat budget is insufficient for the combined upper-bound-and-squeeze proof.
/-- **The Grötzsch connecting modulus vanishes at the inner boundary.** As the slit `[0, s]` shrinks
to the point `{0}` the Grötzsch ring approaches the punctured disk (the fat-ring degeneration
`R / r → ∞` for the *separating* family), whose connecting modulus tends to `0`:
`grotzschModulus s → 0` as `s → 0⁺`. This is the source of the logarithmic blow-up of quasiconformal
distortion near a point. -/
theorem grotzschModulus_tendsto_zero_zero :
    Tendsto grotzschModulus (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- ===================================================================
  -- Step A.  The explicit upper bound: for `0 < s < 1`,
  --   grotzschModulus s ≤ ofReal (2π / log (1/s)).
  -- The witness is the round-annulus extremal radial density on the
  -- annulus `{s < ‖z‖ < 1}` (radii `s, 1`, `L := log (1/s)`).  This is the
  -- specialization of the round-annulus computation `ringModulus_roundAnnulus`
  -- to `r := s`, `R := 1`, adapted to the Grötzsch connecting family whose
  -- curves have start norm `≤ s` (rather than `= s`) on the slit.
  -- ===================================================================
  have key_bound : ∀ {s : ℝ}, 0 < s → s < 1 →
      grotzschModulus s ≤ ENNReal.ofReal (2 * Real.pi / Real.log (1 / s)) := by
    intro s hs0 hs1
    set L := Real.log (1 / s) with hL
    have h1s : 1 < 1 / s := (one_lt_div hs0).mpr hs1
    have hLpos : 0 < L := Real.log_pos h1s
    have hRr : s < (1 : ℝ) := hs1
    -- Helper: a Lipschitz map `ℝ → ℝ` composed with an AC `ℝ → ℝ` is AC.
    have lipOnComp_ac : ∀ {F : ℝ → ℝ} {l : ℝ → ℝ} {K : NNReal} {S : Set ℝ},
        LipschitzOnWith K l S → ∀ {a b : ℝ}, AbsolutelyContinuousOnInterval F a b →
        (∀ t ∈ Set.uIcc a b, F t ∈ S) →
        AbsolutelyContinuousOnInterval (fun t => l (F t)) a b := by
      intro F l K S hl a b hF hmaps
      rw [absolutelyContinuousOnInterval_iff] at hF ⊢
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
      refine ⟨δ, hδ, fun E hE hlen => ?_⟩
      have key := hδ' E hE hlen
      have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
      have hmem : ∀ i ∈ Finset.range E.1,
          (E.2 i).1 ∈ Set.uIcc a b ∧ (E.2 i).2 ∈ Set.uIcc a b := fun i hi => hE.1 i hi
      calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
          ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hl.dist_le_mul _ (hmaps _ (hmem i hi).1) _ (hmaps _ (hmem i hi).2)
        _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
            rw [Finset.mul_sum]
        _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
        _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
    -- Helper: the round annulus is open.
    have isOpen_ann : ∀ (w : ℂ) (a b : ℝ), IsOpen (RoundAnnulus w a b) := by
      intro w a b
      have h1 : IsOpen {z : ℂ | a < dist z w} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have h2 : IsOpen {z : ℂ | dist z w < b} :=
        isOpen_lt (continuous_id.dist continuous_const) continuous_const
      exact h1.inter h2
    -- Helper: |deriv (‖γ ·‖) t| ≤ ‖deriv γ t‖.
    have norm_deriv_norm_le : ∀ {γ : ℝ → ℂ} {t : ℝ},
        HasDerivAt γ (deriv γ t) t →
        HasDerivAt (fun s => ‖γ s‖) (deriv (fun s => ‖γ s‖) t) t →
        |deriv (fun s => ‖γ s‖) t| ≤ ‖deriv γ t‖ := by
      intro γ t hγ hu
      rw [← Real.norm_eq_abs]
      have htu := hu.tendsto_slope
      have htγ := hγ.tendsto_slope
      have htu' : Filter.Tendsto (fun s => ‖slope (fun s => ‖γ s‖) t s‖) (𝓝[≠] t)
          (𝓝 ‖deriv (fun s => ‖γ s‖) t‖) := (continuous_norm.tendsto _).comp htu
      have htγ' : Filter.Tendsto (fun s => ‖slope γ t s‖) (𝓝[≠] t) (𝓝 ‖deriv γ t‖) :=
        (continuous_norm.tendsto _).comp htγ
      refine le_of_tendsto_of_tendsto htu' htγ' ?_
      filter_upwards with x
      rw [slope_def_module, slope_def_module, norm_smul, norm_smul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa using abs_norm_sub_norm_le (γ x) (γ t)
    -- The extremal radial density on the annulus `{s < ‖z‖ < 1}`.
    set rho0 : ℂ → ℝ≥0∞ := fun z =>
      Set.indicator (RoundAnnulus 0 s 1) (fun z => ENNReal.ofReal (1 / (‖z‖ * L))) z with hrho0
    have measurable_rho0 : Measurable rho0 := by
      apply Measurable.indicator _ (isOpen_ann 0 s 1).measurableSet
      exact ENNReal.measurable_ofReal.comp
        (measurable_const.div (measurable_norm.mul measurable_const))
    -- Energy: ∫⁻ rho0² = ofReal (2π/L).
    have rho0_energy : ∫⁻ z, (rho0 z) ^ 2 = ENNReal.ofReal (2 * Real.pi / L) := by
      rw [← Complex.lintegral_comp_polarCoord_symm (fun z => (rho0 z) ^ 2)]
      have hval : Set.EqOn
          (fun p : ℝ × ℝ => ENNReal.ofReal p.1 • (rho0 (Complex.polarCoord.symm p)) ^ 2)
          (fun p : ℝ × ℝ =>
            Set.indicator (Set.Ioo s 1) (fun s' => ENNReal.ofReal (1 / (s' * L ^ 2))) p.1)
          Complex.polarCoord.target := by
        intro p hp
        simp only [Complex.polarCoord_target, Set.mem_prod, Set.mem_Ioi] at hp
        have hp1 : 0 < p.1 := hp.1
        have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
        simp only [hrho0, smul_eq_mul]
        by_cases hmem : Complex.polarCoord.symm p ∈ RoundAnnulus 0 s 1
        · have hmemIoo : p.1 ∈ Set.Ioo s 1 := by
            simp only [RoundAnnulus, Set.mem_ofPred_eq, dist_zero_right, hnorm] at hmem
            exact ⟨hmem.1, hmem.2⟩
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmemIoo, hnorm]
          rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (le_of_lt hp1)]
          congr 1
          rw [div_pow, one_pow, mul_pow]
          rw [hL] at *
          field_simp
        · have hmemIoo : p.1 ∉ Set.Ioo s 1 := by
            simp only [RoundAnnulus, Set.mem_ofPred_eq, dist_zero_right, hnorm] at hmem
            simpa only [Set.mem_Ioo] using hmem
          rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmemIoo]
          simp
      refine Eq.trans (setLIntegral_congr_fun (μ := volume)
        Complex.polarCoord.open_target.measurableSet hval) ?_
      change ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
          Set.indicator (Set.Ioo s 1) (fun s' => ENNReal.ofReal (1 / (s' * L ^ 2))) p.1
            = ENNReal.ofReal (2 * π / L)
      rw [Measure.volume_eq_prod]
      rw [setLIntegral_prod]
      · have hinner : ∀ x : ℝ,
            ∫⁻ _y in Set.Ioo (-π) π,
              Set.indicator (Set.Ioo s 1) (fun s' => ENNReal.ofReal (1 / (s' * L ^ 2))) x
              = Set.indicator (Set.Ioo s 1) (fun s' => ENNReal.ofReal (1 / (s' * L ^ 2))) x
                * ENNReal.ofReal (2 * π) := by
          intro x
          rw [setLIntegral_const, Real.volume_Ioo]
          congr 2
          ring
        simp only [hinner]
        rw [lintegral_mul_const]
        · rw [setLIntegral_indicator measurableSet_Ioo]
          have hsetEq : Set.Ioo s 1 ∩ Set.Ioi (0 : ℝ) = Set.Ioo s 1 := by
            rw [Set.inter_eq_left]
            intro x hx; exact lt_trans hs0 hx.1
          rw [hsetEq]
          have hradial : ∫⁻ x in Set.Ioo s 1, ENNReal.ofReal (1 / (x * L ^ 2))
              = ENNReal.ofReal (1 / L) := by
            rw [← ofReal_integral_eq_lintegral_ofReal]
            · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hRr.le]
              have : ∀ x : ℝ, 1 / (x * L ^ 2) = (1 / L ^ 2) * x⁻¹ := by
                intro x; rw [one_div, mul_inv, one_div]; ring
              simp_rw [this]
              rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hs0 (by linarith)]
              rw [← hL]
              congr 1
              rw [sq]
              field_simp
            · rw [← IntegrableOn]
              have hcontOn : ContinuousOn (fun x : ℝ => 1 / (x * L ^ 2)) (Set.Icc s 1) := by
                apply ContinuousOn.div continuousOn_const
                · exact (continuous_id.mul continuous_const).continuousOn
                · intro x hx
                  rw [Set.mem_Icc] at hx
                  have : 0 < x := lt_of_lt_of_le hs0 hx.1
                  positivity
              exact (hcontOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
            · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => ?_)
              have : 0 < x := lt_trans hs0 hx.1
              positivity
          rw [hradial, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hL]; ring
        · apply Measurable.indicator _ measurableSet_Ioo
          apply ENNReal.measurable_ofReal.comp
          exact (measurable_const.div ((measurable_id.mul measurable_const)))
      · apply Measurable.aemeasurable
        have hh : Measurable (fun s' : ℝ => ENNReal.ofReal (1 / (s' * L ^ 2))) :=
          ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.mul measurable_const))
        exact (hh.indicator measurableSet_Ioo).comp measurable_fst
    -- Admissibility of rho0 for the Grötzsch connecting family.
    have rho0_admissible : ∀ {γ : ℝ → ℂ}, AbsolutelyContinuousOnInterval γ 0 1 →
        γ 0 ∈ grotzschInner s → γ 1 ∈ grotzschOuter →
        (∀ t ∈ Set.Ioo (0 : ℝ) 1, γ t ∈ grotzschRing s) →
        1 ≤ arcLengthLineIntegral rho0 γ := by
      intro γ hac h0 h1 hsub
      set u : ℝ → ℝ := fun t => ‖γ t‖ with hu
      -- The start radius is `≤ s` (the start lies on the slit `[0, s]`).
      have hu0 : u 0 ≤ s := by
        simp only [hu]
        obtain ⟨a, b, ha, hb, hab, hzeq⟩ := h0
        rw [← hzeq]
        have hsimp : a • (0 : ℂ) + b • (s : ℂ) = ((b * s : ℝ) : ℂ) := by
          simp only [Complex.real_smul]; push_cast; ring
        rw [hsimp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        nlinarith [ha, hb, hab, hs0]
      -- The end radius is `= 1`.
      have hu1 : u 1 = 1 := by
        simp only [hu, grotzschOuter, Metric.mem_sphere, dist_zero_right] at h1 ⊢; exact h1
      -- Interior radii are `< 1` (the interior stays in the unit ball).
      have huInt : ∀ t ∈ Set.Ioo (0 : ℝ) 1, u t < 1 := by
        intro t ht
        have := hsub t ht
        rw [grotzschRing, Set.mem_sdiff, Metric.mem_ball, dist_zero_right] at this
        exact this.1
      have huNonneg : ∀ t, 0 ≤ u t := fun t => norm_nonneg _
      have huAC : AbsolutelyContinuousOnInterval u 0 1 := by
        rw [absolutelyContinuousOnInterval_iff] at hac ⊢
        intro ε hε
        obtain ⟨δ, hδ, hδ'⟩ := hac ε hε
        refine ⟨δ, hδ, fun E hE hlen => ?_⟩
        refine lt_of_le_of_lt ?_ (hδ' E hE hlen)
        apply Finset.sum_le_sum
        intro i _
        simp only [hu, dist_eq_norm]
        exact abs_norm_sub_norm_le (γ (E.2 i).1) (γ (E.2 i).2)
      -- The clamped radial coordinate `v t = log (max (u t) s)`.
      set M : ℝ → ℝ := fun t => max (u t) s with hM
      have hMlow : ∀ t, s ≤ M t := fun t => le_max_right _ _
      have hMmaps : ∀ t ∈ Set.uIcc (0 : ℝ) 1, M t ∈ Set.Icc s 1 := by
        intro t ht
        rw [Set.uIcc_of_le zero_le_one, Set.mem_Icc] at ht
        refine ⟨hMlow t, ?_⟩
        rcases eq_or_lt_of_le ht.1 with h0t | h0t
        · simp only [hM]; rw [← h0t]; exact max_le (le_trans hu0 hRr.le) hRr.le
        rcases eq_or_lt_of_le ht.2 with h1t | h1t
        · simp only [hM]; rw [h1t, hu1]; exact max_le le_rfl hRr.le
        · exact max_le (huInt t ⟨h0t, h1t⟩).le hRr.le
      have hmaxLip : LipschitzOnWith 1 (fun x : ℝ => max x s) (Set.univ : Set ℝ) := by
        rw [lipschitzOnWith_univ]
        exact LipschitzWith.max_const LipschitzWith.id s
      have hMAC : AbsolutelyContinuousOnInterval M 0 1 :=
        lipOnComp_ac (S := Set.univ) hmaxLip huAC (fun _ _ => Set.mem_univ _)
      have hlogLip : LipschitzOnWith (⟨1/s, by positivity⟩ : ℝ≥0) Real.log (Set.Icc s 1) := by
        apply (convex_Icc s 1).lipschitzOnWith_of_nnnorm_deriv_le
        · intro x hx
          rw [Set.mem_Icc] at hx
          exact Real.differentiableAt_log (lt_of_lt_of_le hs0 hx.1).ne'
        · intro x hx
          rw [Set.mem_Icc] at hx
          have hx0 : 0 < x := lt_of_lt_of_le hs0 hx.1
          rw [Real.deriv_log]
          refine NNReal.coe_le_coe.mp ?_
          change ‖x⁻¹‖ ≤ 1 / s
          rw [Real.norm_eq_abs, abs_of_pos (by positivity), one_div]
          exact inv_anti₀ hs0 hx.1
      set v : ℝ → ℝ := fun t => Real.log (M t) with hv
      have hvAC : AbsolutelyContinuousOnInterval v 0 1 := lipOnComp_ac hlogLip hMAC hMmaps
      have hv0 : v 0 = Real.log s := by
        simp only [hv, hM]; rw [max_eq_right hu0, Real.log]
      have hv1 : v 1 = 0 := by
        simp only [hv, hM]; rw [hu1, max_eq_left hRr.le, Real.log_one]
      -- `v` has global minimum value `log s`.
      have hvmin : ∀ x, Real.log s ≤ v x := by
        intro x
        simp only [hv]
        exact Real.log_le_log hs0 (hMlow x)
      have hγdiff : ∀ᵐ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → DifferentiableAt ℝ γ t :=
        hac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
      have hudiff : ∀ᵐ t : ℝ, t ∈ Set.uIcc (0 : ℝ) 1 → DifferentiableAt ℝ u t :=
        huAC.ae_differentiableAt
      have hIccIoo : (volume.restrict (Set.Icc (0 : ℝ) 1)) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
        Measure.restrict_congr_set (Ioo_ae_eq_Icc).symm
      have hline : arcLengthLineIntegral rho0 γ
          = ∫⁻ t in Set.Ioo (0 : ℝ) 1, rho0 (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
        unfold arcLengthLineIntegral
        rw [hIccIoo]
      rw [hline]
      have hFTC : ∫ t in (0 : ℝ)..1, deriv v t = L := by
        rw [hvAC.integral_deriv_eq_sub, hv1, hv0, hL, one_div, Real.log_inv, zero_sub]
      have hvint : IntervalIntegrable (deriv v) volume 0 1 := hvAC.intervalIntegrable_deriv
      have hvintOoc : IntegrableOn (deriv v) (Set.Ioo (0 : ℝ) 1) volume :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hvint
      have hvabsintOoc : IntegrableOn (fun t => |deriv v t|) (Set.Ioo (0 : ℝ) 1) volume :=
        hvintOoc.abs
      -- The key pointwise bound.
      have hpoint : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
          ENNReal.ofReal (1 / L) * ENNReal.ofReal |deriv v t|
            ≤ rho0 (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
        rw [ae_restrict_iff' measurableSet_Ioo]
        filter_upwards [hγdiff, hudiff] with t htγ htu
        intro htmem
        have htuIcc : t ∈ Set.uIcc (0 : ℝ) 1 := by
          rw [Set.uIcc_of_le zero_le_one]; exact Set.Ioo_subset_Icc_self htmem
        have hγD : DifferentiableAt ℝ γ t := htγ htuIcc
        have huD : DifferentiableAt ℝ u t := htu htuIcc
        have hut_lt1 : u t < 1 := huInt t htmem
        by_cases hcase : s < u t
        · -- In the annulus: `s < u t < 1`.
          have hann : γ t ∈ RoundAnnulus 0 s 1 := by
            simp only [RoundAnnulus, Set.mem_ofPred_eq, dist_zero_right]
            exact ⟨hcase, hut_lt1⟩
          have hut_pos : 0 < u t := lt_trans hs0 hcase
          have hrhoval : rho0 (γ t) = ENNReal.ofReal (1 / (u t * L)) := by
            simp only [hrho0, Set.indicator_of_mem hann, hu]
          have hdu_le : |deriv u t| ≤ ‖deriv γ t‖ :=
            norm_deriv_norm_le hγD.hasDerivAt huD.hasDerivAt
          -- On a neighborhood of `t`, `M = u`, so `deriv v t = deriv u t / u t`.
          have hMeq : (fun x => M x) =ᶠ[𝓝 t] u := by
            have hev : ∀ᶠ x in 𝓝 t, s < u x :=
              continuousAt_const.eventually_lt huD.continuousAt hcase
            filter_upwards [hev] with x hx
            simp only [hM]; exact max_eq_left hx.le
          have hvderiv : deriv v t = deriv u t / u t := by
            have hveq : v =ᶠ[𝓝 t] (fun x => Real.log (u x)) := by
              filter_upwards [hMeq] with x hx
              simp only [hv]; rw [hx]
            rw [Filter.EventuallyEq.deriv_eq hveq]
            have : HasDerivAt (fun x => Real.log (u x)) (deriv u t / u t) t := by
              have := huD.hasDerivAt.log (by rw [hu] at hut_pos ⊢; exact hut_pos.ne')
              simpa [hu] using this
            exact this.deriv
          rw [hrhoval, hvderiv]
          have key1 : ENNReal.ofReal (1 / L) * ENNReal.ofReal |deriv u t / u t|
              = ENNReal.ofReal (1 / (u t * L)) * ENNReal.ofReal |deriv u t| := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [abs_div, abs_of_pos hut_pos]
            field_simp
          rw [key1]
          gcongr
          rw [show (‖deriv γ t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv γ t‖ from by
            rw [ofReal_norm, enorm_eq_nnnorm]]
          exact ENNReal.ofReal_le_ofReal hdu_le
        · -- Below the annulus: `u t ≤ s`, so `t` is a global min of `v` and `deriv v t = 0`.
          have hcase' : u t ≤ s := not_lt.mp hcase
          have hvderiv0 : deriv v t = 0 := by
            have hlocmin : IsLocalMin v t := by
              have hminon : IsMinOn v Set.univ t := by
                rw [isMinOn_iff]
                intro x _
                have : v t = Real.log s := by
                  simp only [hv, hM]; rw [max_eq_right hcase', Real.log]
                rw [this]; exact hvmin x
              exact hminon.isLocalMin (by simp)
            exact hlocmin.deriv_eq_zero
          rw [hvderiv0]
          simp
      calc (1 : ℝ≥0∞)
          = ENNReal.ofReal (1 / L) * ENNReal.ofReal L := by
            rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hLpos.ne',
              ENNReal.ofReal_one]
        _ ≤ ENNReal.ofReal (1 / L) * ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv v t| := by
            gcongr ?_ * ?_
            · exact le_rfl
            rw [← hFTC]
            calc ENNReal.ofReal (∫ t in (0 : ℝ)..1, deriv v t)
                ≤ ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, |deriv v t|) := by
                  apply ENNReal.ofReal_le_ofReal
                  rw [intervalIntegral.integral_of_le zero_le_one,
                    integral_Ioc_eq_integral_Ioo]
                  apply setIntegral_mono_on hvintOoc hvabsintOoc measurableSet_Ioo
                  intro x _; exact le_abs_self _
              _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal |deriv v t| := by
                  rw [ofReal_integral_eq_lintegral_ofReal hvabsintOoc
                    (ae_restrict_of_forall_mem measurableSet_Ioo (fun x _ => abs_nonneg _))]
        _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / L) * ENNReal.ofReal |deriv v t| := by
            rw [lintegral_const_mul]
            exact ENNReal.measurable_ofReal.comp (_root_.continuous_abs.measurable.comp
              (measurable_deriv v))
        _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, rho0 (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) :=
            lintegral_mono_ae hpoint
    -- The upper bound via the admissible witness rho0.
    unfold grotzschModulus curveModulus
    refine le_trans (iInf₂_le rho0 ?_) ?_
    · refine ⟨measurable_rho0, ?_⟩
      rintro γ ⟨_, hac, h0, h1, hsub⟩
      exact rho0_admissible hac h0 h1 hsub
    · exact le_of_eq rho0_energy
  -- ===================================================================
  -- Step B.  Squeeze: `0 ≤ grotzschModulus s ≤ ofReal (2π / log (1/s)) → 0`.
  -- ===================================================================
  have hUpperTendsto :
      Tendsto (fun s => ENNReal.ofReal (2 * Real.pi / Real.log (1 / s))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hlog : Tendsto (fun s : ℝ => Real.log (1 / s)) (𝓝[>] (0 : ℝ)) atTop := by
      have hneg : Tendsto (fun s : ℝ => -Real.log s) (𝓝[>] (0 : ℝ)) atTop :=
        tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
      refine hneg.congr (fun s => ?_)
      rw [one_div, Real.log_inv]
    have hreal : Tendsto (fun s : ℝ => 2 * Real.pi / Real.log (1 / s)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      hlog.const_div_atTop (2 * Real.pi)
    have hcont : Tendsto (fun x : ℝ => ENNReal.ofReal x) (𝓝 (0 : ℝ)) (𝓝 (ENNReal.ofReal 0)) :=
      (ENNReal.continuous_ofReal.tendsto 0)
    rw [ENNReal.ofReal_zero] at hcont
    exact hcont.comp hreal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpperTendsto
    (Filter.Eventually.of_forall (fun s => zero_le)) ?_
  have hmem : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)
  filter_upwards [self_mem_nhdsWithin, hmem] with s hs0 hs1
  exact key_bound hs0 hs1

end NoWanderingDomains
