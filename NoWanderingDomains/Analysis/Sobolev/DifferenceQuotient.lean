/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Sobolev.WeakDeriv
import NoWanderingDomains.Analysis.Sobolev.AbsolutelyContinuousLines
import NoWanderingDomains.Analysis.Sobolev.SobolevToACL
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Weak derivatives and no-singular-part from L²-bounded difference quotients

This file provides the **non-circular** bridge from pointwise almost-everywhere
differentiability *plus an `L²_loc` bound on difference quotients* to the weak
directional derivative (`HasWeakDirDeriv`), and onward to the per-line
"no singular part" bound `eVariationOn ≤ ∫⁻ ‖deriv‖`.

The point is that bounding the difference quotient `(f(z + h•v) − f z)/h` in `L²_loc`
**uniformly in `h`** does *not* require absolute continuity (it can be supplied by a
purely geometric estimate, e.g. quasiconformal roundness `diam² ≲ area`), whereas the
classical length–area route to the weak gradient assumes absolute continuity from the
start. Difference quotients converge pointwise almost everywhere to the directional
derivative `(fderiv ℝ f z) v` at differentiability points; an `L²_loc` bound provides the
uniform integrability needed to pass that convergence through the integration-by-parts
identity, producing the weak derivative. The Sobolev⇒ACL representative theorems
(`exists_aclHorizontal_of_hasWeakDirDeriv_one` / `exists_aclVertical_of_hasWeakDirDeriv_I`)
then give absolute continuity on almost every line, and a continuity transfer plus the
absolute-continuity variation bound yield the no-singular-part inequality for the
genuine slices of `f`.

## Main results

* `hasWeakDirDeriv_of_ae_differentiable_of_differenceQuotient_L2` — the core bridge.
* `ae_slice_re_im_eVariation_le_of_hasWeakDirDeriv_one` — horizontal no-singular-part.
* `ae_slice_re_im_eVariation_le_of_hasWeakDirDeriv_I` — vertical no-singular-part.
-/

open MeasureTheory Complex Set Filter Topology
open scoped ENNReal NNReal Pointwise

namespace NoWanderingDomains

/-- **Difference quotient ⟹ weak directional derivative.** Let `f : ℂ → ℂ` be
continuous and locally integrable, differentiable at almost every point, and let
`v` be a unit real direction. If the difference quotients
`z ↦ (f (z + h • v) − f z)/h` are bounded in `L²` on every compact set, uniformly for
small `h ≠ 0`, then the classical directional derivative `w ↦ (fderiv ℝ f w) v` is the
weak directional derivative of `f` in direction `v`.

The proof passes the integration-by-parts identity `∫ (∂ᵥφ)•f = − ∫ φ•(∂ᵥf)` to the
limit of difference quotients: writing `∂ᵥφ` as a limit of backward difference quotients
of the smooth test function `φ`, a translation of the Lebesgue integral turns the
expression into `−∫ φ • (forward difference quotient of f)`; the difference quotients
converge pointwise a.e. to `(fderiv ℝ f) v` and, being `L²`-bounded on the compact
support of `φ`, are uniformly integrable there, so the limit passes through the integral
(Vitali). -/
theorem hasWeakDirDeriv_of_ae_differentiable_of_differenceQuotient_L2
    {f : ℂ → ℂ} {v : ℂ} (hv : ‖v‖ = 1)
    (hfc : Continuous f) (hfloc : LocallyIntegrable f)
    (hdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ f z)
    (hbound : ∀ Kc : Set ℂ, IsCompact Kc → ∃ M : ℝ≥0∞, M < ⊤ ∧
      ∀ h : ℝ, 0 < |h| → |h| ≤ 1 →
        ∫⁻ z in Kc, ‖(f (z + h • v) - f z) / (h : ℂ)‖₊ ^ 2 ≤ M) :
    HasWeakDirDeriv v (fun w => (fderiv ℝ f w) v) f Set.univ := by
  -- The target derivative.
  set g : ℂ → ℂ := fun w => (fderiv ℝ f w) v with hg_def
  intro φ hφ hcs _
  -- Goal: `∫ z, ((fderiv ℝ φ z) v) • f z = - ∫ z, φ z • g z`.
  -- The compact support of `φ` and an enlarged compact set holding all small translates.
  set K₀ : Set ℂ := tsupport φ with hK₀_def
  have hK₀cpt : IsCompact K₀ := hcs
  set Kc : Set ℂ := K₀ + Metric.closedBall (0 : ℂ) 1 with hKc_def
  have hKccpt : IsCompact Kc :=
    hK₀cpt.add (isCompact_closedBall 0 1)
  -- `f` is integrable on the compact `Kc`.
  have hfKc : IntegrableOn f Kc volume := hfloc.integrableOn_isCompact hKccpt
  -- Backward difference quotient of `φ` times `f`, and forward difference quotient of `f`.
  set BQ : ℝ → ℂ → ℂ := fun h z => ((φ z - φ (z - h • v)) / h) • f z with hBQ_def
  set DQ : ℝ → ℂ → ℂ := fun h z => (f (z + h • v) - f z) / (h : ℂ) with hDQ_def
  -- The approximating sequence of step sizes.
  set t : ℕ → ℝ := fun n => 1 / (n + 1) with ht_def
  have ht_pos : ∀ n, 0 < t n := by
    intro n; simp only [ht_def]; positivity
  have ht_le : ∀ n, t n ≤ 1 := by
    intro n
    simp only [ht_def]
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hKcmeas : MeasurableSet Kc := hKccpt.measurableSet
  -- Translates by `h • v` with `|h| ≤ 1` of a point of `K₀` stay inside `Kc`.
  have hnorm_smul : ∀ h : ℝ, ‖h • v‖ ≤ |h| := by
    intro h
    calc ‖h • v‖ ≤ ‖h‖ * ‖v‖ := norm_smul_le h v
      _ = |h| := by rw [hv, Real.norm_eq_abs, mul_one]
  have hmem_add : ∀ (h : ℝ), |h| ≤ 1 → ∀ z ∈ K₀, z + h • v ∈ Kc := by
    intro h hh z hz
    refine Set.add_mem_add hz ?_
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact le_trans (hnorm_smul h) hh
  have hmem_sub : ∀ (h : ℝ), |h| ≤ 1 → ∀ z ∈ K₀, z - h • v ∈ Kc := by
    intro h hh z hz
    have heq : z - h • v = z + (-h) • v := by module
    rw [heq]
    exact hmem_add (-h) (by rwa [abs_neg]) z hz
  -- `φ` is continuous.
  have hφcont : Continuous φ := hφ.continuous
  -- A uniform bound on the operator norm of `fderiv ℝ φ` (continuous, compact support).
  obtain ⟨C, hC⟩ :=
    ((hφ.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
      (HasCompactSupport.fderiv (𝕜 := ℝ) hcs))
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  -- φ is globally `C`-Lipschitz from the global bound on its derivative.
  have hφlip : ∀ a b : ℂ, ‖φ a - φ b‖ ≤ C * ‖a - b‖ := by
    intro a b
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => (hφ.differentiable (by norm_num)).differentiableAt)
      (fun x _ => hC x) (convex_univ) (mem_univ a) (mem_univ b)
  -- A reusable integrability principle: a continuous, compactly supported (in `K₀`) multiplier
  -- times a function integrable on `Kc` is integrable on all of `ℂ`.
  have integ_mul : ∀ (m : ℂ → ℝ), Continuous m → (Function.support m ⊆ K₀) →
      ∀ {k : ℂ → ℂ}, IntegrableOn k Kc volume → Integrable (fun z => m z • k z) volume := by
    intro m hm hsupp k hk
    have hsubKc : K₀ ⊆ Kc := by
      intro z hz
      have : z = z + (0 : ℂ) := by ring
      rw [this]
      refine Set.add_mem_add hz ?_
      simp [Metric.mem_closedBall]
    have hon : IntegrableOn (fun z => m z • k z) Kc volume :=
      hk.continuousOn_smul hm.continuousOn hKccpt
    have hsupp' : Function.support (fun z => m z • k z) ⊆ Kc := by
      intro z hz
      apply hsubKc
      apply hsupp
      simp only [Function.mem_support] at hz ⊢
      intro hmz; apply hz; simp [hmz]
    exact (integrableOn_iff_integrable_of_support_subset hsupp').mp hon
  -- Convergence of the step sizes.
  have htn0 : Tendsto t atTop (𝓝 (0 : ℝ)) := by
    simpa only [ht_def] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have htnLT : Tendsto (fun n => -t n) atTop (𝓝[<] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using htn0.neg
    · filter_upwards with n
      simp only [Set.mem_Iio, Left.neg_neg_iff]
      exact ht_pos n
  -- Three claims (proved below).
  have claimA : Tendsto (fun n => ∫ z, BQ (t n) z)
      atTop (𝓝 (∫ z, ((fderiv ℝ φ z) v) • f z)) := by
    -- Dominator: `C * ‖f z‖` on `Kc`, zero outside.
    set bound : ℂ → ℝ := fun z => Kc.indicator (fun z => C * ‖f z‖) z with hbound_def
    have hboundOn : IntegrableOn (fun z => C * ‖f z‖) Kc volume := hfKc.norm.const_mul C
    have hbound_int : Integrable bound volume :=
      hboundOn.integrable_indicator hKcmeas
    -- Measurability of the difference quotients.
    have hmeas : ∀ n, AEStronglyMeasurable (BQ (t n)) volume := by
      intro n
      simp only [hBQ_def, Complex.real_smul]
      apply Continuous.aestronglyMeasurable
      apply Continuous.mul
      · apply Continuous.comp Complex.continuous_ofReal
        apply Continuous.div_const
        exact hφcont.sub (hφcont.comp (continuous_id.sub continuous_const))
      · exact hfc
    -- Pointwise bound by `bound`.
    have hbnd : ∀ n, ∀ᵐ z, ‖BQ (t n) z‖ ≤ bound z := by
      intro n
      have hpos := ht_pos n
      have habs : |t n| ≤ 1 := by rw [abs_of_pos hpos]; exact ht_le n
      filter_upwards with z
      by_cases hzKc : z ∈ Kc
      · -- `z ∈ Kc`: bound by `C * ‖f z‖`.
        simp only [hBQ_def, hbound_def, Set.indicator_of_mem hzKc]
        have hnum : ‖(φ z - φ (z - t n • v)) / t n‖ ≤ C := by
          rw [norm_div, Real.norm_eq_abs (t n)]
          rw [div_le_iff₀ (by rw [abs_of_pos hpos]; exact hpos)]
          calc ‖φ z - φ (z - t n • v)‖ ≤ C * ‖z - (z - t n • v)‖ := hφlip _ _
            _ = C * ‖t n • v‖ := by rw [sub_sub_cancel]
            _ ≤ C * |t n| := mul_le_mul_of_nonneg_left (hnorm_smul (t n)) hC0
        have hsmulnorm : ‖((φ z - φ (z - t n • v)) / t n) • f z‖
            = ‖(φ z - φ (z - t n • v)) / t n‖ * ‖f z‖ := by
          rw [Complex.real_smul, norm_mul, Complex.norm_real]
        rw [hsmulnorm]
        exact mul_le_mul_of_nonneg_right hnum (norm_nonneg _)
      · -- `z ∉ Kc`: the difference quotient vanishes.
        have hφz : φ z = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hz; exact hzKc (by
            have : K₀ ⊆ Kc := by
              intro w hw
              have hw0 : w = w + (0 : ℂ) := by ring
              rw [hw0]; exact Set.add_mem_add hw (by simp [Metric.mem_closedBall])
            exact this hz)
        have hφz2 : φ (z - t n • v) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hz
          exact hzKc (by
            have hmem : z = (z - t n • v) + t n • v := by abel
            rw [hmem]; exact hmem_add (t n) habs _ hz)
        simp only [hBQ_def, hφz, hφz2, sub_zero, zero_div, hbound_def,
          Set.indicator_of_notMem hzKc]
        simp
    -- Pointwise convergence: a.e. (in fact everywhere) the backward quotients converge.
    have hlim : ∀ᵐ z, Tendsto (fun n => BQ (t n) z) atTop (𝓝 (((fderiv ℝ φ z) v) • f z)) := by
      filter_upwards with z
      have hfd : HasFDerivAt φ (fderiv ℝ φ z) z :=
        (hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
      have hld : HasLineDerivAt ℝ φ ((fderiv ℝ φ z) v) z v := hfd.hasLineDerivAt v
      -- slope from the left: `s⁻¹•(φ(z+s•v)-φz) → (fderiv φ z) v` as `s → 0⁻`.
      have hslope : Tendsto (fun s : ℝ => s⁻¹ • (φ (z + s • v) - φ z))
          (𝓝[<] 0) (𝓝 ((fderiv ℝ φ z) v)) := hld.tendsto_slope_zero_left
      have hcomp : Tendsto (fun n => (-t n)⁻¹ • (φ (z + (-t n) • v) - φ z))
          atTop (𝓝 ((fderiv ℝ φ z) v)) := hslope.comp htnLT
      -- rewrite `(-t n)⁻¹ • (φ(z + (-t n)•v) - φ z) = (φ z - φ(z - t n • v))/t n`.
      have hrw : ∀ n, (-t n)⁻¹ • (φ (z + (-t n) • v) - φ z)
          = (φ z - φ (z - t n • v)) / t n := by
        intro n
        have hne : t n ≠ 0 := (ht_pos n).ne'
        have hvsub : z + (-t n) • v = z - t n • v := by module
        rw [hvsub, smul_eq_mul]
        field_simp
        ring
      have hconv : Tendsto (fun n => (φ z - φ (z - t n • v)) / t n)
          atTop (𝓝 ((fderiv ℝ φ z) v)) := by
        simp only [← hrw]; exact hcomp
      -- multiply through by `f z`: rewrite the real scalar as a complex coercion.
      have hconvC : Tendsto (fun n => ((φ z - φ (z - t n • v)) / t n : ℝ) • f z)
          atTop (𝓝 (((fderiv ℝ φ z) v) • f z)) := by
        simp only [Complex.real_smul]
        exact (Complex.continuous_ofReal.continuousAt.tendsto.comp hconv).mul_const (f z)
      simpa only [hBQ_def] using hconvC
    exact tendsto_integral_of_dominated_convergence bound hmeas hbound_int hbnd hlim
  -- Support of `fun z => φ z / h` is contained in `K₀` (for `h ≠ 0`).
  have hsupp_div : ∀ h : ℝ, Function.support (fun z => φ z / h) ⊆ K₀ := by
    intro h z hz
    apply subset_tsupport φ
    simp only [Function.mem_support] at hz ⊢
    intro hφz; apply hz; simp [hφz]
  have claimB : ∀ n, ∫ z, BQ (t n) z = - ∫ z, φ z • DQ (t n) z := by
    intro n
    set h : ℝ := t n with hh_def
    have hh0 : h ≠ 0 := (ht_pos n).ne'
    have habs : |h| ≤ 1 := by rw [abs_of_pos (ht_pos n)]; exact ht_le n
    -- `f` integrable on `Kc` and the translate `fun z => f (z + h • v)` integrable on `Kc`.
    have hmp : MeasurePreserving (fun z : ℂ => z + h • v) volume volume :=
      measurePreserving_add_right volume (h • v)
    have hemb : MeasurableEmbedding (fun z : ℂ => z + h • v) :=
      (Homeomorph.addRight (h • v)).measurableEmbedding
    have hfKc' : IntegrableOn (fun z => f (z + h • v)) Kc volume := by
      -- `Kc` is mapped into the (still compact) set `Kc + closedBall 0 1`; `f` integrable there.
      have hbig : IntegrableOn f (Kc + Metric.closedBall (0 : ℂ) 1) volume :=
        hfloc.integrableOn_isCompact (hKccpt.add (isCompact_closedBall 0 1))
      have hsub : (fun z : ℂ => z + h • v) '' Kc ⊆ Kc + Metric.closedBall (0 : ℂ) 1 := by
        rintro w ⟨z, hz, rfl⟩
        refine Set.add_mem_add hz ?_
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact le_trans (hnorm_smul h) habs
      exact (hmp.integrableOn_image hemb (f := f) (s := Kc)).mp (hbig.mono_set hsub)
    -- The two product integrands.
    have I1 : Integrable (fun z => (φ z / h) • f z) volume :=
      integ_mul _ (hφcont.div_const h) (hsupp_div h) hfKc
    have I2 : Integrable (fun z => (φ z / h) • f (z + h • v)) volume :=
      integ_mul _ (hφcont.div_const h) (hsupp_div h) hfKc'
    -- The composition `((φ(·-h•v)/h)•f ·) ∘ (·+h•v)` is `(φ·/h)•f(·+h•v)` (= `I2`).
    have heqcomp : ((fun z : ℂ => (φ (z - h • v) / h) • f z) ∘ (fun z : ℂ => z + h • v))
        = fun z => (φ z / h) • f (z + h • v) := by
      funext z; simp only [Function.comp_apply, add_sub_cancel_right]
    have I3 : Integrable (fun z => (φ (z - h • v) / h) • f z) volume :=
      (hmp.integrable_comp_emb hemb
        (g := fun z : ℂ => (φ (z - h • v) / h) • f z)).mp (heqcomp ▸ I2)
    -- Translation substitution: `∫ (φ(z-h•v)/h)•f z = ∫ (φz/h)•f(z+h•v)`.
    have hsubst : (∫ z, (φ (z - h • v) / h) • f z)
        = ∫ z, (φ z / h) • f (z + h • v) := by
      have hkey := integral_add_right_eq_self
        (μ := (volume : Measure ℂ)) (fun z : ℂ => (φ (z - h • v) / h) • f z) (h • v)
      rw [← hkey]
      apply integral_congr_ae
      filter_upwards with z
      simp only [add_sub_cancel_right]
    -- Assemble.
    have hBQint : (∫ z, BQ h z)
        = (∫ z, (φ z / h) • f z) - ∫ z, (φ z / h) • f (z + h • v) := by
      simp only [hBQ_def]
      rw [← hsubst, ← integral_sub I1 I3]
      apply integral_congr_ae
      filter_upwards with z
      rw [sub_div]; module
    rw [hBQint, ← integral_sub I1 I2, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with z
    -- `(φz/h)•f z - (φz/h)•f(z+h•v) = - (φ z • DQ h z)`.
    simp only [hDQ_def, Complex.real_smul]
    push_cast
    field_simp
    ring
  have claimC : Tendsto (fun n => ∫ z, φ z • DQ (t n) z)
      atTop (𝓝 (∫ z, φ z • g z)) := by
    -- Work on the finite measure `μ = volume.restrict K₀`.
    have hK₀fin : volume K₀ < ⊤ := hK₀cpt.measure_lt_top
    have : Fact (volume K₀ < ⊤) := ⟨hK₀fin⟩
    set μ : Measure ℂ := volume.restrict K₀ with hμ_def
    have hμfin : IsFiniteMeasure μ := by rw [hμ_def]; infer_instance
    have hK₀meas : MeasurableSet K₀ := hK₀cpt.measurableSet
    -- `φ` is bounded by `Cφ`.
    obtain ⟨Cφ, hCφ⟩ := hφcont.bounded_above_of_compact_support hcs
    have hCφ0 : 0 ≤ Cφ := le_trans (norm_nonneg _) (hCφ 0)
    -- The uniform `L²` bound on `K₀` for the difference quotients.
    obtain ⟨M, hMlt, hM⟩ := hbound K₀ hK₀cpt
    -- `Fₙ := φ • DQ (t n)`.
    set F : ℕ → ℂ → ℂ := fun n z => φ z • DQ (t n) z with hF_def
    -- `Fₙ` is supported in `K₀`; hence the integral over `ℂ` equals the integral over `K₀`.
    have hFsupp : ∀ n z, z ∉ K₀ → F n z = 0 := by
      intro n z hz
      have : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [hF_def, this]
    have hFintegral : ∀ n, (∫ z, F n z) = ∫ z, F n z ∂μ := by
      intro n
      rw [hμ_def, ← setIntegral_eq_integral_of_forall_compl_eq_zero (hFsupp n)]
    -- Continuity / measurability of the difference quotients and `Fₙ`.
    have hDQcont : ∀ n, Continuous (DQ (t n)) := by
      intro n
      simp only [hDQ_def]
      apply Continuous.div_const
      exact (hfc.comp (continuous_id.add continuous_const)).sub hfc
    have hDQmeas : ∀ n, AEStronglyMeasurable (DQ (t n)) μ :=
      fun n => (hDQcont n).aestronglyMeasurable
    have hFmeas : ∀ n, AEStronglyMeasurable (F n) μ := by
      intro n
      simp only [hF_def, Complex.real_smul]
      apply Continuous.aestronglyMeasurable
      exact ((Complex.continuous_ofReal.comp hφcont).mul (hDQcont n))
    -- `M^(1/2)` as the `L²` bound for `DQ (t n)` and `B := Cφ * M^(1/2)` for `Fₙ`.
    set Msqrt : ℝ≥0∞ := M ^ (1 / (2 : ℝ)) with hMsqrt_def
    have hMsqrt_lt : Msqrt < ⊤ := by
      rw [hMsqrt_def]; exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hMlt.ne
    have hL2DQ : ∀ n, eLpNorm (DQ (t n)) 2 μ ≤ Msqrt := by
      intro n
      have hpos := ht_pos n
      have habs0 : 0 < |t n| := by rw [abs_of_pos hpos]; exact hpos
      have habs1 : |t n| ≤ 1 := by rw [abs_of_pos hpos]; exact ht_le n
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      simp only [ENNReal.toReal_ofNat, one_div]
      rw [hMsqrt_def, one_div]
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      -- `∫⁻ ‖DQ‖ₑ² ∂μ ≤ M`.
      have hkey := hM (t n) habs0 habs1
      have heq : (∫⁻ z, ‖DQ (t n) z‖ₑ ^ (2 : ℝ) ∂μ)
          = ∫⁻ z in K₀, ‖(f (z + t n • v) - f z) / (t n : ℂ)‖₊ ^ 2 := by
        rw [hμ_def]
        apply lintegral_congr
        intro z
        rw [hDQ_def, enorm_eq_nnnorm]
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
      rw [heq]; exact hkey
    -- `Fₙ` is bounded in `L²` by `B := Cφ.toNNReal • Msqrt`.
    set B : ℝ≥0∞ := (Cφ.toNNReal : ℝ≥0∞) * Msqrt with hB_def
    have hBlt : B < ⊤ := by
      rw [hB_def]; exact ENNReal.mul_lt_top ENNReal.coe_lt_top hMsqrt_lt
    have hL2F : ∀ n, eLpNorm (F n) 2 μ ≤ B := by
      intro n
      have hpt : ∀ᵐ z ∂μ, ‖F n z‖₊ ≤ Cφ.toNNReal * ‖DQ (t n) z‖₊ := by
        filter_upwards with z
        simp only [hF_def, Complex.real_smul, nnnorm_mul]
        gcongr
        have hcoe : ‖(↑(φ z) : ℂ)‖₊ = ‖φ z‖₊ := by
          rw [Complex.nnnorm_real]
        rw [hcoe]
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hCφ0]
        exact hCφ z
      have hstep : Cφ.toNNReal • eLpNorm (DQ (t n)) 2 μ ≤ B := by
        rw [hB_def, ENNReal.smul_def, smul_eq_mul]
        gcongr
        exact hL2DQ n
      exact le_trans (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hpt 2) hstep
    -- The key truncation estimate: `eLpNorm (s.indicator Fₙ) 1 μ ≤ B * (μ s)^(1/2)`.
    have hHolder : ∀ n, ∀ s : Set ℂ, MeasurableSet s →
        eLpNorm (s.indicator (F n)) 1 μ ≤ B * (μ s) ^ (1 / (2 : ℝ)) := by
      intro n s hs
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
      have hcmp : eLpNorm (F n) 1 (μ.restrict s)
          ≤ eLpNorm (F n) 2 (μ.restrict s) * (μ.restrict s) Set.univ ^
            (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) (hFmeas n).restrict
      have hmono : eLpNorm (F n) 2 (μ.restrict s) ≤ B :=
        le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self) (hL2F n)
      have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = 1 / (2 : ℝ) := by
        norm_num
      rw [hexp, Measure.restrict_apply_univ] at hcmp
      refine le_trans hcmp ?_
      gcongr
    -- Uniform integrability of `Fₙ` at exponent 1.
    have hUI : UnifIntegrable F 1 μ := by
      intro ε hε
      set Bℝ : ℝ := B.toReal with hBℝ_def
      have hBℝ0 : 0 ≤ Bℝ := ENNReal.toReal_nonneg
      refine ⟨(ε / (Bℝ + 1)) ^ 2, by positivity, fun n s hs hμs => ?_⟩
      -- bound `eLpNorm (s.indicator Fₙ) 1 μ ≤ B * (μ s)^(1/2)`.
      have h1 := hHolder n s hs
      -- `(μ s)^(1/2) ≤ ofReal (ε/(Bℝ+1))`.
      have hμs2 : (μ s) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal (ε / (Bℝ + 1)) := by
        have hbase : μ s ≤ ENNReal.ofReal ((ε / (Bℝ + 1)) ^ 2) := hμs
        calc (μ s) ^ (1 / (2 : ℝ))
            ≤ (ENNReal.ofReal ((ε / (Bℝ + 1)) ^ 2)) ^ (1 / (2 : ℝ)) := by
              apply ENNReal.rpow_le_rpow hbase (by norm_num)
          _ = ENNReal.ofReal (ε / (Bℝ + 1)) := by
              rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
              congr 1
              rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
              norm_num
      -- assemble `B * (μ s)^(1/2) ≤ ofReal ε`.
      have hfin : B * (μ s) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal ε := by
        calc B * (μ s) ^ (1 / (2 : ℝ))
            ≤ B * ENNReal.ofReal (ε / (Bℝ + 1)) := by gcongr
          _ = ENNReal.ofReal Bℝ * ENNReal.ofReal (ε / (Bℝ + 1)) := by
              rw [hBℝ_def, ENNReal.ofReal_toReal hBlt.ne]
          _ = ENNReal.ofReal (Bℝ * (ε / (Bℝ + 1))) := by
              rw [← ENNReal.ofReal_mul hBℝ0]
          _ ≤ ENNReal.ofReal ε := by
              apply ENNReal.ofReal_le_ofReal
              rw [mul_div_assoc']
              rw [div_le_iff₀ (by positivity)]
              have : Bℝ * ε ≤ ε * (Bℝ + 1) := by nlinarith [hε.le, hBℝ0]
              linarith
      exact le_trans h1 hfin
    -- Almost-everywhere convergence `Fₙ → φ • g` (with respect to `μ`).
    have htn0R : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htn0
        (by filter_upwards with n using ht_pos n)
    have hae_conv : ∀ᵐ z ∂μ, Tendsto (fun n => F n z) atTop (𝓝 (φ z • g z)) := by
      have hdiffμ : ∀ᵐ z ∂μ, DifferentiableAt ℝ f z :=
        ae_restrict_of_ae hdiff
      filter_upwards [hdiffμ] with z hz
      -- `DQ (t n) z → (fderiv f z) v = g z`.
      have hfd : HasFDerivAt f (fderiv ℝ f z) z := hz.hasFDerivAt
      have hld : HasLineDerivAt ℝ f ((fderiv ℝ f z) v) z v := hfd.hasLineDerivAt v
      have hslope : Tendsto (fun s : ℝ => s⁻¹ • (f (z + s • v) - f z))
          (𝓝[>] 0) (𝓝 ((fderiv ℝ f z) v)) := hld.tendsto_slope_zero_right
      have hcompDQ : Tendsto (fun n => (t n)⁻¹ • (f (z + (t n) • v) - f z))
          atTop (𝓝 ((fderiv ℝ f z) v)) := hslope.comp htn0R
      have hDQeq : ∀ n, (t n)⁻¹ • (f (z + (t n) • v) - f z) = DQ (t n) z := by
        intro n
        simp only [hDQ_def, Complex.real_smul]
        rw [Complex.ofReal_inv, div_eq_inv_mul]
      have hDQlim : Tendsto (fun n => DQ (t n) z) atTop (𝓝 (g z)) := by
        simp only [← hDQeq]; exact hcompDQ
      -- multiply by `φ z`.
      simp only [hF_def, Complex.real_smul]
      exact (hDQlim.const_mul (φ z : ℂ))
    -- `g` (hence `φ • g`) is measurable, and `φ • g ∈ L¹(μ)`.
    have hgmeas : Measurable g := by
      rw [hg_def]
      exact (measurable_fderiv ℝ f).apply_continuousLinearMap v
    have hφgmeas : AEStronglyMeasurable (fun z => φ z • g z) μ := by
      simp only [Complex.real_smul]
      exact ((Complex.continuous_ofReal.comp hφcont).measurable.mul hgmeas).aestronglyMeasurable
    have hMemLp2 : MemLp (fun z => φ z • g z) 2 μ := by
      refine ⟨hφgmeas, ?_⟩
      have hle : eLpNorm (fun z => φ z • g z) 2 μ ≤ B :=
        MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
          (Filter.Eventually.of_forall hL2F) hFmeas hae_conv
      exact lt_of_le_of_lt hle hBlt
    have hMemLp : MemLp (fun z => φ z • g z) 1 μ := hMemLp2.mono_exponent (by norm_num)
    -- Each `Fₙ ∈ L²(μ) ⊆ L¹(μ)`, hence integrable.
    have hFintMemLp : ∀ n, MemLp (F n) 1 μ := by
      intro n
      have h2 : MemLp (F n) 2 μ := ⟨hFmeas n, lt_of_le_of_lt (hL2F n) hBlt⟩
      exact h2.mono_exponent (by norm_num)
    -- Vitali: `eLpNorm (Fₙ - φ•g) 1 μ → 0`.
    have hVitali : Tendsto (fun n => eLpNorm (fun z => F n z - φ z • g z) 1 μ) atTop (𝓝 0) := by
      have := tendsto_Lp_finite_of_tendsto_ae (μ := μ) (p := 1) (by norm_num) (by norm_num)
        hFmeas hMemLp hUI hae_conv
      simpa using! this
    -- `tendsto_integral_of_L1'`: pass the limit through the integral.
    have hL1tendsto : Tendsto (fun n => ∫ z, F n z ∂μ) atTop (𝓝 (∫ z, φ z • g z ∂μ)) := by
      apply tendsto_integral_of_L1' (fun z => φ z • g z) hφgmeas
      · filter_upwards with n
        exact (hFintMemLp n).integrable le_rfl
      · exact hVitali
    -- Transport back to integrals over `ℂ`: `∫ z, φ z • DQ (t n) z = ∫ z, F n z ∂μ`,
    -- and `∫ z, φ z • g z = ∫ z, φ z • g z ∂μ` (both integrands supported in `K₀`).
    have hglobal_F : ∀ n, (∫ z, φ z • DQ (t n) z) = ∫ z, F n z ∂μ := by
      intro n; rw [← hFintegral n]
    have hglobal_g : (∫ z, φ z • g z) = ∫ z, φ z • g z ∂μ := by
      rw [hμ_def, ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := K₀) (f := fun z => φ z • g z)]
      intro z hz
      have : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [this]
    rw [hglobal_g]
    simpa only [hglobal_F] using hL1tendsto
  -- Combine: the LHS is the limit of `∫ BQ (t n) = - ∫ φ • DQ (t n) → - ∫ φ • g`.
  have hAB : Tendsto (fun n => ∫ z, BQ (t n) z) atTop (𝓝 (- ∫ z, φ z • g z)) := by
    have := claimC.neg
    simpa only [claimB] using this
  exact tendsto_nhds_unique claimA hAB

/-- **Horizontal no-singular-part from the weak `x`-derivative.** If `f` is continuous
with weak `x`-directional derivative `gx` (and `gx` locally integrable), then for almost
every horizontal line the total variation of each real component of the slice is bounded
by the integral of the component's slice-derivative norm.

Proof: the Sobolev⇒ACL representative theorem produces `f' =ᵐ f` that is absolutely
continuous on almost every horizontal line with line-derivative `gx`. On almost every
line `f'` and `f` agree (Fubini); both slices are continuous (the AC representative and
the continuous `f`), hence equal on the whole line, so `f`'s own slice is absolutely
continuous with derivative `(gx⟨x,y⟩)`. Each real component is then absolutely continuous,
and for an absolutely continuous function the total variation equals the integral of the
derivative norm, giving the `≤` bound. -/
theorem ae_slice_re_im_eVariation_le_of_hasWeakDirDeriv_one
    {f gx : ℂ → ℂ} (hfc : Continuous f) (hgx : LocallyIntegrable gx)
    (h : HasWeakDirDeriv 1 gx f Set.univ) :
    ∀ᵐ y : ℝ, ∀ a b : ℝ,
      eVariationOn (fun x : ℝ => (f ⟨x, y⟩).re) (Set.Icc a b)
          ≤ ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨s, y⟩).re) x‖₊ ∧
      eVariationOn (fun x : ℝ => (f ⟨x, y⟩).im) (Set.Icc a b)
          ≤ ∫⁻ x in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨s, y⟩).im) x‖₊ := by
  -- (A) **Forward variation bound.** For a function `G : ℝ → ℝ` that is absolutely continuous
  -- on every interval, `eVariationOn G [a, b] ≤ ∫⁻ ‖deriv G‖`: each partition sum telescopes
  -- through the FTC `G v − G u = ∫ᵤᵛ deriv G`, bounded by `∫⁻_{(u, v]} ‖deriv G‖`, and the
  -- consecutive half-open subintervals are pairwise disjoint inside `[a, b]`.
  have eVarBound : ∀ (G : ℝ → ℝ), (∀ a' b' : ℝ, AbsolutelyContinuousOnInterval G a' b') →
      ∀ a b : ℝ, eVariationOn G (Set.Icc a b) ≤ ∫⁻ x in Set.Icc a b, ‖deriv G x‖₊ := by
    intro G hAC a b
    rcases le_or_gt a b with hab | hab
    · rw [eVariationOn]
      apply iSup_le
      rintro ⟨n, u, humono, husub⟩
      simp only
      have hterm : ∀ i ∈ Finset.range n,
          edist (G (u (i + 1))) (G (u i)) ≤ ∫⁻ x in Set.Ioc (u i) (u (i + 1)), ‖deriv G x‖₊ := by
        intro i _
        have hle : u i ≤ u (i + 1) := humono (Nat.le_succ i)
        have hftc : G (u (i + 1)) - G (u i) = ∫ x in (u i)..(u (i + 1)), deriv G x :=
          ((hAC (u i) (u (i + 1))).integral_deriv_eq_sub).symm
        rw [edist_eq_enorm_sub, hftc, intervalIntegral.integral_of_le hle]
        exact enorm_integral_le_lintegral_enorm _
      calc ∑ i ∈ Finset.range n, edist (G (u (i + 1))) (G (u i))
          ≤ ∑ i ∈ Finset.range n, ∫⁻ x in Set.Ioc (u i) (u (i + 1)), ‖deriv G x‖₊ :=
            Finset.sum_le_sum hterm
        _ ≤ ∫⁻ x in Set.Icc a b, ‖deriv G x‖₊ := by
            have hdisj : Set.PairwiseDisjoint (↑(Finset.range n))
                (fun i => Set.Ioc (u i) (u (i + 1))) := by
              have key : ∀ i j : ℕ, i < j →
                  Disjoint (Set.Ioc (u i) (u (i + 1))) (Set.Ioc (u j) (u (j + 1))) := by
                intro i j hlt
                have huij : u (i + 1) ≤ u j := humono hlt
                apply Set.disjoint_left.mpr
                intro x hx1 hx2
                simp only [Set.mem_Ioc] at hx1 hx2
                linarith [hx1.2, hx2.1]
              intro i _ j _ hij
              rcases lt_or_gt_of_ne hij with hlt | hgt
              · exact key i j hlt
              · exact (key j i hgt).symm
            have hmeas : ∀ i ∈ Finset.range n, MeasurableSet (Set.Ioc (u i) (u (i + 1))) :=
              fun i _ => measurableSet_Ioc
            rw [← lintegral_biUnion_finset hdisj hmeas]
            apply lintegral_mono_set
            intro x hx
            simp only [Set.mem_iUnion, Finset.mem_range] at hx
            obtain ⟨i, hi, hxi⟩ := hx
            rw [Set.mem_Ioc] at hxi
            exact ⟨le_trans (husub i).1 hxi.1.le, le_trans hxi.2 (husub (i + 1)).2⟩
    · have hEmp : Set.Icc a b = (∅ : Set ℝ) := Set.Icc_eq_empty (not_le.mpr hab)
      rw [hEmp]; simp [eVariationOn]
  -- (B) **Components of an AC slice are AC.** `re`/`im` are Lipschitz, so post-composing
  -- an absolutely continuous function with them preserves absolute continuity.
  have hReAC : ∀ (F : ℝ → ℂ) (a b : ℝ), AbsolutelyContinuousOnInterval F a b →
      AbsolutelyContinuousOnInterval (fun x => (F x).re) a b := by
    intro F a b hF
    have hl : LipschitzWith ‖Complex.reCLM‖₊ (Complex.reCLM) := Complex.reCLM.lipschitz
    set K : NNReal := ‖Complex.reCLM‖₊ with hK
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist ((F (E.2 i).1).re) ((F (E.2 i).2).re)
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) := by
          apply Finset.sum_le_sum; intro i _
          simpa [Complex.reCLM_apply] using hl.dist_le_mul (F (E.2 i).1) (F (E.2 i).2)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  have hImAC : ∀ (F : ℝ → ℂ) (a b : ℝ), AbsolutelyContinuousOnInterval F a b →
      AbsolutelyContinuousOnInterval (fun x => (F x).im) a b := by
    intro F a b hF
    have hl : LipschitzWith ‖Complex.imCLM‖₊ (Complex.imCLM) := Complex.imCLM.lipschitz
    set K : NNReal := ‖Complex.imCLM‖₊ with hK
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist ((F (E.2 i).1).im) ((F (E.2 i).2).im)
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) := by
          apply Finset.sum_le_sum; intro i _
          simpa [Complex.imCLM_apply] using hl.dist_le_mul (F (E.2 i).1) (F (E.2 i).2)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  -- (C) Continuity of the slice-embedding `x ↦ ⟨x, y⟩`.
  have hmkcont : ∀ y : ℝ, Continuous (fun x : ℝ => Complex.mk x y) := by
    intro y
    apply Continuous.comp (g := Complex.equivRealProdCLM.symm) (f := fun x : ℝ => (x, y))
    · exact Complex.equivRealProdCLM.symm.continuous
    · fun_prop
  -- ===== MAIN ARGUMENT =====
  -- The Sobolev⇒ACL representative `f'` is absolutely continuous on almost every horizontal line.
  obtain ⟨f', hf'eq, hacl⟩ :=
    exists_aclHorizontal_of_hasWeakDirDeriv_one hfc.locallyIntegrable hgx h
  have hTnull : volume {z : ℂ | f' z ≠ f z} = 0 := hf'eq
  -- **Fubini slice transfer.** Almost every horizontal slice of `f'` agrees a.e. with the
  -- corresponding slice of `f` (transport the planar null set `{f' ≠ f}` to `ℝ × ℝ`, swap so the
  -- imaginary part is the outer index, then take a.e. fibers).
  have hslice : ∀ᵐ y : ℝ, volume {x : ℝ | f' (Complex.mk x y) ≠ f (Complex.mk x y)} = 0 := by
    set T : Set ℂ := {z : ℂ | f' z ≠ f z} with hTdef
    have hmp : MeasurePreserving Complex.measurableEquivRealProd.symm
        (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
      Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
    set T' : Set (ℝ × ℝ) := Complex.measurableEquivRealProd.symm ⁻¹' T with hT'def
    have hT'null : volume T' = 0 := hmp.quasiMeasurePreserving.preimage_null hTnull
    have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
      Measure.measurePreserving_swap
    set T'' : Set (ℝ × ℝ) := Prod.swap ⁻¹' T' with hT''def
    have hT''null : volume T'' = 0 := hswap.quasiMeasurePreserving.preimage_null hT'null
    have hprodnull : ∀ᵐ q : ℝ × ℝ ∂((volume : Measure ℝ).prod volume), q ∉ T'' := by
      rw [ae_iff]; simpa [Measure.volume_eq_prod] using hT''null
    have hae : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, (y, x) ∉ T'' := Measure.ae_ae_of_ae_prod hprodnull
    refine hae.mono (fun y hy => ?_)
    have hmem : ∀ x : ℝ, ((y, x) ∈ T'') ↔ (f' (Complex.mk x y) ≠ f (Complex.mk x y)) := by
      intro x
      simp only [hT''def, hT'def, hTdef, Set.mem_preimage, Prod.swap_prod_mk,
        Complex.measurableEquivRealProd_symm_apply, Set.mem_ofPred_eq]
    rw [ae_iff] at hy
    have hset : {x : ℝ | f' (Complex.mk x y) ≠ f (Complex.mk x y)} = {x : ℝ | (y, x) ∈ T''} := by
      ext x; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hmem x]
    rw [hset]; simpa using hy
  filter_upwards [hacl, hslice] with y hy_acl hy_slice
  -- On this line `f'`'s slice is AC on every interval, hence continuous; `f`'s slice is continuous;
  -- agreeing a.e., two continuous functions on `ℝ` (full-support `volume`) are equal everywhere.
  have hf'sliceAC : ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun x : ℝ => f' (Complex.mk x y)) a b := hy_acl.1
  have hf'cont : Continuous (fun x : ℝ => f' (Complex.mk x y)) := by
    rw [continuous_iff_continuousAt]; intro x
    have hco : ContinuousOn (fun x : ℝ => f' (Complex.mk x y)) (Set.uIcc (x - 1) (x + 1)) :=
      (hf'sliceAC (x - 1) (x + 1)).continuousOn
    have hmem : Set.uIcc (x - 1) (x + 1) ∈ nhds x := by
      rw [Set.uIcc_of_le (by linarith)]; exact Icc_mem_nhds (by linarith) (by linarith)
    exact hco.continuousAt hmem
  have hfcont : Continuous (fun x : ℝ => f (Complex.mk x y)) := hfc.comp (hmkcont y)
  have hae2 : (fun x : ℝ => f' (Complex.mk x y)) =ᵐ[volume] (fun x : ℝ => f (Complex.mk x y)) := by
    rw [Filter.EventuallyEq, ae_iff]; convert hy_slice using 2
  have heq : (fun x : ℝ => f' (Complex.mk x y)) = (fun x : ℝ => f (Complex.mk x y)) :=
    MeasureTheory.Measure.eq_of_ae_eq hae2 hf'cont hfcont
  have hfsliceAC : ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun x : ℝ => f (Complex.mk x y)) a b := by
    intro a b; rw [← heq]; exact hf'sliceAC a b
  -- Each component of the (now absolutely continuous) `f`-slice satisfies the forward bound.
  intro a b
  refine ⟨?_, ?_⟩
  · exact eVarBound (fun x => (f (Complex.mk x y)).re)
      (fun a' b' => hReAC _ a' b' (hfsliceAC a' b')) a b
  · exact eVarBound (fun x => (f (Complex.mk x y)).im)
      (fun a' b' => hImAC _ a' b' (hfsliceAC a' b')) a b

/-- **Vertical no-singular-part from the weak `y`-derivative.** The vertical analogue of
`ae_slice_re_im_eVariation_le_of_hasWeakDirDeriv_one`, via the weak `y`-directional
derivative and `exists_aclVertical_of_hasWeakDirDeriv_I`. -/
theorem ae_slice_re_im_eVariation_le_of_hasWeakDirDeriv_I
    {f gy : ℂ → ℂ} (hfc : Continuous f) (hgy : LocallyIntegrable gy)
    (h : HasWeakDirDeriv Complex.I gy f Set.univ) :
    ∀ᵐ x : ℝ, ∀ a b : ℝ,
      eVariationOn (fun y : ℝ => (f ⟨x, y⟩).re) (Set.Icc a b)
          ≤ ∫⁻ y in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨x, s⟩).re) y‖₊ ∧
      eVariationOn (fun y : ℝ => (f ⟨x, y⟩).im) (Set.Icc a b)
          ≤ ∫⁻ y in Set.Icc a b, ‖deriv (fun s : ℝ => (f ⟨x, s⟩).im) y‖₊ := by
  -- (A) **Forward variation bound** (same as in the horizontal case).
  have eVarBound : ∀ (G : ℝ → ℝ), (∀ a' b' : ℝ, AbsolutelyContinuousOnInterval G a' b') →
      ∀ a b : ℝ, eVariationOn G (Set.Icc a b) ≤ ∫⁻ x in Set.Icc a b, ‖deriv G x‖₊ := by
    intro G hAC a b
    rcases le_or_gt a b with hab | hab
    · rw [eVariationOn]
      apply iSup_le
      rintro ⟨n, u, humono, husub⟩
      simp only
      have hterm : ∀ i ∈ Finset.range n,
          edist (G (u (i + 1))) (G (u i)) ≤ ∫⁻ x in Set.Ioc (u i) (u (i + 1)), ‖deriv G x‖₊ := by
        intro i _
        have hle : u i ≤ u (i + 1) := humono (Nat.le_succ i)
        have hftc : G (u (i + 1)) - G (u i) = ∫ x in (u i)..(u (i + 1)), deriv G x :=
          ((hAC (u i) (u (i + 1))).integral_deriv_eq_sub).symm
        rw [edist_eq_enorm_sub, hftc, intervalIntegral.integral_of_le hle]
        exact enorm_integral_le_lintegral_enorm _
      calc ∑ i ∈ Finset.range n, edist (G (u (i + 1))) (G (u i))
          ≤ ∑ i ∈ Finset.range n, ∫⁻ x in Set.Ioc (u i) (u (i + 1)), ‖deriv G x‖₊ :=
            Finset.sum_le_sum hterm
        _ ≤ ∫⁻ x in Set.Icc a b, ‖deriv G x‖₊ := by
            have hdisj : Set.PairwiseDisjoint (↑(Finset.range n))
                (fun i => Set.Ioc (u i) (u (i + 1))) := by
              have key : ∀ i j : ℕ, i < j →
                  Disjoint (Set.Ioc (u i) (u (i + 1))) (Set.Ioc (u j) (u (j + 1))) := by
                intro i j hlt
                have huij : u (i + 1) ≤ u j := humono hlt
                apply Set.disjoint_left.mpr
                intro x hx1 hx2
                simp only [Set.mem_Ioc] at hx1 hx2
                linarith [hx1.2, hx2.1]
              intro i _ j _ hij
              rcases lt_or_gt_of_ne hij with hlt | hgt
              · exact key i j hlt
              · exact (key j i hgt).symm
            have hmeas : ∀ i ∈ Finset.range n, MeasurableSet (Set.Ioc (u i) (u (i + 1))) :=
              fun i _ => measurableSet_Ioc
            rw [← lintegral_biUnion_finset hdisj hmeas]
            apply lintegral_mono_set
            intro x hx
            simp only [Set.mem_iUnion, Finset.mem_range] at hx
            obtain ⟨i, hi, hxi⟩ := hx
            rw [Set.mem_Ioc] at hxi
            exact ⟨le_trans (husub i).1 hxi.1.le, le_trans hxi.2 (husub (i + 1)).2⟩
    · have hEmp : Set.Icc a b = (∅ : Set ℝ) := Set.Icc_eq_empty (not_le.mpr hab)
      rw [hEmp]; simp [eVariationOn]
  -- (B) **Components of an AC slice are AC** (same as in the horizontal case).
  have hReAC : ∀ (F : ℝ → ℂ) (a b : ℝ), AbsolutelyContinuousOnInterval F a b →
      AbsolutelyContinuousOnInterval (fun x => (F x).re) a b := by
    intro F a b hF
    have hl : LipschitzWith ‖Complex.reCLM‖₊ (Complex.reCLM) := Complex.reCLM.lipschitz
    set K : NNReal := ‖Complex.reCLM‖₊ with hK
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist ((F (E.2 i).1).re) ((F (E.2 i).2).re)
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) := by
          apply Finset.sum_le_sum; intro i _
          simpa [Complex.reCLM_apply] using hl.dist_le_mul (F (E.2 i).1) (F (E.2 i).2)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  have hImAC : ∀ (F : ℝ → ℂ) (a b : ℝ), AbsolutelyContinuousOnInterval F a b →
      AbsolutelyContinuousOnInterval (fun x => (F x).im) a b := by
    intro F a b hF
    have hl : LipschitzWith ‖Complex.imCLM‖₊ (Complex.imCLM) := Complex.imCLM.lipschitz
    set K : NNReal := ‖Complex.imCLM‖₊ with hK
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist ((F (E.2 i).1).im) ((F (E.2 i).2).im)
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) := by
          apply Finset.sum_le_sum; intro i _
          simpa [Complex.imCLM_apply] using hl.dist_le_mul (F (E.2 i).1) (F (E.2 i).2)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  -- (C) Continuity of the (vertical) slice-embedding `y ↦ ⟨x, y⟩`.
  have hmkcont : ∀ x : ℝ, Continuous (fun y : ℝ => Complex.mk x y) := by
    intro x
    apply Continuous.comp (g := Complex.equivRealProdCLM.symm) (f := fun y : ℝ => (x, y))
    · exact Complex.equivRealProdCLM.symm.continuous
    · fun_prop
  -- ===== MAIN ARGUMENT =====
  -- The Sobolev⇒ACL representative `f'` is absolutely continuous on almost every vertical line.
  obtain ⟨f', hf'eq, hacl⟩ :=
    exists_aclVertical_of_hasWeakDirDeriv_I hfc.locallyIntegrable hgy h
  have hTnull : volume {z : ℂ | f' z ≠ f z} = 0 := hf'eq
  -- **Fubini slice transfer** (vertical: the real part is the outer index, so no coordinate swap).
  have hslice : ∀ᵐ x : ℝ, volume {y : ℝ | f' (Complex.mk x y) ≠ f (Complex.mk x y)} = 0 := by
    set T : Set ℂ := {z : ℂ | f' z ≠ f z} with hTdef
    have hmp : MeasurePreserving Complex.measurableEquivRealProd.symm
        (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
      Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
    set T' : Set (ℝ × ℝ) := Complex.measurableEquivRealProd.symm ⁻¹' T with hT'def
    have hT'null : volume T' = 0 := hmp.quasiMeasurePreserving.preimage_null hTnull
    have hprodnull : ∀ᵐ q : ℝ × ℝ ∂((volume : Measure ℝ).prod volume), q ∉ T' := by
      rw [ae_iff]; simpa [Measure.volume_eq_prod] using hT'null
    have hae : ∀ᵐ x : ℝ, ∀ᵐ y : ℝ, (x, y) ∉ T' := Measure.ae_ae_of_ae_prod hprodnull
    refine hae.mono (fun x hx => ?_)
    have hmem : ∀ y : ℝ, ((x, y) ∈ T') ↔ (f' (Complex.mk x y) ≠ f (Complex.mk x y)) := by
      intro y
      simp only [hT'def, hTdef, Set.mem_preimage,
        Complex.measurableEquivRealProd_symm_apply, Set.mem_ofPred_eq]
    rw [ae_iff] at hx
    have hset : {y : ℝ | f' (Complex.mk x y) ≠ f (Complex.mk x y)} = {y : ℝ | (x, y) ∈ T'} := by
      ext y; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hmem y]
    rw [hset]; simpa using hx
  filter_upwards [hacl, hslice] with x hy_acl hy_slice
  -- On this line `f'`'s slice is AC on every interval, hence continuous; `f`'s slice is continuous;
  -- agreeing a.e., two continuous functions on `ℝ` (full-support `volume`) are equal everywhere.
  have hf'sliceAC : ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun y : ℝ => f' (Complex.mk x y)) a b := hy_acl.1
  have hf'cont : Continuous (fun y : ℝ => f' (Complex.mk x y)) := by
    rw [continuous_iff_continuousAt]; intro y
    have hco : ContinuousOn (fun y : ℝ => f' (Complex.mk x y)) (Set.uIcc (y - 1) (y + 1)) :=
      (hf'sliceAC (y - 1) (y + 1)).continuousOn
    have hmem : Set.uIcc (y - 1) (y + 1) ∈ nhds y := by
      rw [Set.uIcc_of_le (by linarith)]; exact Icc_mem_nhds (by linarith) (by linarith)
    exact hco.continuousAt hmem
  have hfcont : Continuous (fun y : ℝ => f (Complex.mk x y)) := hfc.comp (hmkcont x)
  have hae2 : (fun y : ℝ => f' (Complex.mk x y)) =ᵐ[volume] (fun y : ℝ => f (Complex.mk x y)) := by
    rw [Filter.EventuallyEq, ae_iff]; convert hy_slice using 2
  have heq : (fun y : ℝ => f' (Complex.mk x y)) = (fun y : ℝ => f (Complex.mk x y)) :=
    MeasureTheory.Measure.eq_of_ae_eq hae2 hf'cont hfcont
  have hfsliceAC : ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun y : ℝ => f (Complex.mk x y)) a b := by
    intro a b; rw [← heq]; exact hf'sliceAC a b
  -- Each component of the (now absolutely continuous) `f`-slice satisfies the forward bound.
  intro a b
  refine ⟨?_, ?_⟩
  · exact eVarBound (fun y => (f (Complex.mk x y)).re)
      (fun a' b' => hReAC _ a' b' (hfsliceAC a' b')) a b
  · exact eVarBound (fun y => (f (Complex.mk x y)).im)
      (fun a' b' => hImAC _ a' b' (hfsliceAC a' b')) a b

end NoWanderingDomains
