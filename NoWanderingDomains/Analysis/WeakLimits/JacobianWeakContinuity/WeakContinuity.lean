/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.WeakLimits.JacobianWeakContinuity.NullLagrangian

/-!
# Weak continuity of the Jacobian: passing to the limit

The limit-passage half of the null-Lagrangian cluster, built on the divergence identities of
`NoWanderingDomains.Analysis.WeakLimits.JacobianWeakContinuity.NullLagrangian`. Because
`integral_jacobianWeak_smul_eq` rewrites a tested Jacobian into a first-order expression that is
*linear* in the gradient, locally uniform convergence together with weak `L²` convergence of the
gradients and a uniform local energy bound carries it to the limit. The same vocabulary gives weak
lower semicontinuity of a weighted `L²` energy and shows that a weak directional derivative
survives a locally uniform limit. Weak convergence is throughout the integral-pairing predicate
`TendstoWeaklyL2` or its compactly supported form `TendstoWeaklyL2Loc`. The exported results feed
`NoWanderingDomains.QC.Calculus.AnalyticClosedness`, and `hasWeakDirDeriv_of_tendsto` also
`NoWanderingDomains.QC.MRMT.NeumannSeries.PrincipalSolution`.

## Main results

* `NoWanderingDomains.tendsto_integral_jacobianWeak_smul` — weak continuity of the tested
  Jacobian. Assume `fₙ → g` locally uniformly, every `fₙ` and `g` continuous, a.e. differentiable
  and in `W^{1,2}_loc`; `(gxₙ, gyₙ)` and `(gxLim, gyLim)` weak gradients on `univ` of `fₙ` and `g`
  with `L²_loc` components; `gxₙ → gxLim` and `gyₙ → gyLim` weakly in `L²_loc`; and one constant
  `M` bounding `∫ z in tsupport φ, ‖gxₙ z‖²` and the same for `gyₙ`, for every `n`. Then for `φ`
  smooth with compact support, `∫ (jacobianWeak gxₙ gyₙ)·φ → ∫ (jacobianWeak gxLim gyLim)·φ`.
* `NoWanderingDomains.hasWeakDirDeriv_of_tendsto` — if `fₙ → g` locally uniformly with every `fₙ`
  and `g` continuous, each `gxₙ` is a weak directional derivative of `fₙ` in the direction `v` on
  `univ`, and `gxₙ → u` weakly in `L²_loc`, then `u` is a weak directional derivative of `g` in the
  direction `v` on `univ`. Both sides of `∫ (∂ᵥφ)•fₙ = − ∫ φ•gxₙ` pass to the limit.
* `NoWanderingDomains.le_liminf_integral_normSq_smul` — weighted weak lower semicontinuity of the
  `L²` norm: if `hₙ → h` weakly in `L²(volume)` against *global* `L²` tests, `h` and every `hₙ` are
  `MemLp _ 2 volume`, and `w` is measurable with `0 ≤ w z ≤ C` at every `z`, then
  `∫ ‖h‖²·w ≤ liminf ∫ ‖hₙ‖²·w`. It reaches consumers only through the local form below.
* `NoWanderingDomains.le_liminf_integral_normSq_smul_of_compactSupport` — the same inequality
  when `hₙ → h` only weakly in `L²_loc` and `h`, `hₙ` are only `L²_loc` on `univ`, at the price of
  asking the bounded nonnegative measurable weight `w` to vanish off a compact set `S`. Proved by
  truncating to `S`; this is the form the analytic-closedness argument consumes.
-/

open MeasureTheory Complex
open scoped ContDiff ENNReal NNReal

namespace NoWanderingDomains

variable {f : ℂ → ℂ} {φ : ℂ → ℝ}

/-- **Weighted weak lower semicontinuity of the `L²` norm.** If `hₙ` converges
weakly in `L²(volume)` to `h` and `w : ℂ → ℝ` is a measurable weight with
`0 ≤ w ≤ C`, then the weighted energy is weakly lower semicontinuous:
`∫ ‖h z‖²·w z ≤ liminf ∫ ‖hₙ z‖²·w z`.

The `√w`-multiplier preserves weak convergence, and lower semicontinuity of the norm
under weak convergence in the `√w`-weighted `L²` space gives the bound. -/
theorem le_liminf_integral_normSq_smul {hₙ : ℕ → ℂ → ℂ} {h : ℂ → ℂ}
    (hw_conv : TendstoWeaklyL2 hₙ h)
    (hmemH : MemLp h 2 volume) (hmemHn : ∀ n, MemLp (hₙ n) 2 volume)
    {w : ℂ → ℝ} (hwmeas : Measurable w) {C : ℝ} (hwnn : ∀ z, 0 ≤ w z)
    (hwle : ∀ z, w z ≤ C) :
    ∫ z, ‖h z‖ ^ 2 * w z
      ≤ (Filter.liminf (fun n => ∫ z, ‖hₙ n z‖ ^ 2 * w z) Filter.atTop) := by
  set s : ℂ → ℝ := fun z => Real.sqrt (w z) with hs
  have hsmeas : Measurable s := hwmeas.sqrt
  have hsnn : ∀ z, 0 ≤ s z := fun z => Real.sqrt_nonneg _
  -- Multiplication by the bounded multiplier `s` preserves `L²`-membership.
  have hmemLp_smul : ∀ g : ℂ → ℂ, MemLp g 2 volume →
      MemLp (fun z => (s z : ℂ) * g z) 2 volume := by
    intro g hg
    have hbound : MemLp (fun z => Real.sqrt C * ‖g z‖) 2 volume := by
      simpa using hg.norm.const_mul (Real.sqrt C)
    refine hbound.mono' ?_ ?_
    · exact (Complex.measurable_ofReal.comp hsmeas).aestronglyMeasurable.mul
        hg.aestronglyMeasurable
    · filter_upwards with z
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hsnn z)]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hwle z)) (norm_nonneg _)
  set sh : ℂ → ℂ := fun z => (s z : ℂ) * h z with hsh
  set shₙ : ℕ → ℂ → ℂ := fun n z => (s z : ℂ) * hₙ n z with hshₙ
  have hmemSH : MemLp sh 2 volume := hmemLp_smul h hmemH
  have hmemSHn : ∀ n, MemLp (shₙ n) 2 volume := fun n => hmemLp_smul (hₙ n) (hmemHn n)
  -- The `√w`-weighted energies are the norms-squared of `sh` and `shₙ` in `L²`.
  set X : Lp ℂ 2 (volume : Measure ℂ) := hmemSH.toLp sh with hX
  set Xₙ : ℕ → Lp ℂ 2 (volume : Measure ℂ) :=
    fun n => (hmemSHn n).toLp (shₙ n) with hXₙ
  -- For any `L²` function `f`, `∫ ‖f‖² = ‖toLp f‖²`.
  have intSq : ∀ (f : ℂ → ℂ) (hf : MemLp f 2 volume),
      (∫ z, ‖f z‖ ^ 2) = ‖hf.toLp f‖ ^ 2 := by
    intro f hf
    have hinner : (inner ℂ (hf.toLp f) (hf.toLp f) : ℂ) = ∫ z, (‖f z‖ ^ 2 : ℝ) := by
      rw [L2.inner_def, ← integral_complex_ofReal]
      refine integral_congr_ae ?_
      filter_upwards [hf.coeFn_toLp] with z hz
      rw [RCLike.inner_apply, hz, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hns := inner_self_eq_norm_sq (𝕜 := ℂ) (hf.toLp f)
    rw [hinner] at hns
    simpa using hns
  -- The weighted energy of `h` equals `‖X‖²`.
  have hLHS : (∫ z, ‖h z‖ ^ 2 * w z) = ‖X‖ ^ 2 := by
    rw [hX, ← intSq sh hmemSH]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [hsh]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hsnn z),
      mul_pow, Real.sq_sqrt (hwnn z)]
    ring
  -- The weighted energy of each `hₙ n` equals `‖Xₙ n‖²`.
  have hRHSn : ∀ n, (∫ z, ‖hₙ n z‖ ^ 2 * w z) = ‖Xₙ n‖ ^ 2 := by
    intro n
    rw [hXₙ, ← intSq (shₙ n) (hmemSHn n)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [hshₙ]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hsnn z),
      mul_pow, Real.sq_sqrt (hwnn z)]
    ring
  rw [hLHS]
  have hRHSeq : (fun n => ∫ z, ‖hₙ n z‖ ^ 2 * w z) = fun n => ‖Xₙ n‖ ^ 2 :=
    funext hRHSn
  rw [hRHSeq]
  -- Transport of weak convergence along the bounded multiplier `s`.
  have hconvSH : TendstoWeaklyL2 shₙ sh := by
    intro ψ hψ
    have hconv := hw_conv (fun z => (s z : ℂ) * ψ z) (hmemLp_smul ψ hψ)
    have hrhs : (∫ z, h z * ((s z : ℂ) * ψ z)) = ∫ z, sh z * ψ z :=
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by rw [hsh]; ring))
    rw [hrhs] at hconv
    exact hconv.congr (fun n => integral_congr_ae (Filter.Eventually.of_forall
      (fun z => by rw [hshₙ]; ring)))
  -- The inner products `⟪X, Xₙ⟫` converge to `⟪X, X⟫`.
  have hpair : ∀ (F : ℂ → ℂ) (hF : MemLp F 2 volume),
      (inner ℂ (hmemSH.toLp sh) (hF.toLp F) : ℂ)
        = ∫ z, F z * (starRingEnd ℂ) (sh z) := by
    intro F hF
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hmemSH.coeFn_toLp, hF.coeFn_toLp] with z h1 h2
    rw [RCLike.inner_apply, h1, h2, mul_comm]
  have hconvInner : Filter.Tendsto (fun n => (inner ℂ X (Xₙ n) : ℂ)) Filter.atTop
      (nhds (inner ℂ X X)) := by
    -- Test `hconvSH` against `ψ := star sh`.
    have hc := hconvSH (fun z => (starRingEnd ℂ) (sh z)) hmemSH.star
    have hXXn : ∀ n,
        (inner ℂ X (Xₙ n) : ℂ) = ∫ z, shₙ n z * (starRingEnd ℂ) (sh z) := by
      intro n
      rw [hX, hXₙ]; exact hpair (shₙ n) (hmemSHn n)
    have hXX : (inner ℂ X X : ℂ) = ∫ z, sh z * (starRingEnd ℂ) (sh z) := by
      rw [hX]; exact hpair sh hmemSH
    rw [hXX]
    exact (by simpa only [hXXn] using hc.congr (fun n => rfl))
  -- Uniform bound on `‖Xₙ‖` via the uniform boundedness principle.
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ n, ‖Xₙ n‖ ≤ B := by
    set v : ℕ → Lp ℂ 2 (volume : Measure ℂ) :=
      fun n => (hmemSHn n).star.toLp (star (shₙ n)) with hv
    have hptwise : ∀ y : Lp ℂ 2 (volume : Measure ℂ),
        ∃ D, ∀ n, ‖(innerSL ℂ (v n)) y‖ ≤ D := by
      intro y
      have hy : MemLp (y : ℂ → ℂ) 2 volume := Lp.memLp y
      have hpairing : ∀ n,
          ((innerSL ℂ (v n)) y : ℂ) = ∫ z, shₙ n z * (y : ℂ → ℂ) z := by
        intro n
        rw [innerSL_apply_apply, hv, L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [(hmemSHn n).star.coeFn_toLp] with z h1
        rw [RCLike.inner_apply, h1]
        simp only [Pi.star_apply, RCLike.star_def, RCLike.conj_conj]
        rw [mul_comm]
      have hconv : Filter.Tendsto (fun n => (innerSL ℂ (v n)) y) Filter.atTop
          (nhds (∫ z, sh z * (y : ℂ → ℂ) z)) := by
        have hc := hconvSH (y : ℂ → ℂ) hy
        exact hc.congr (fun n => (hpairing n).symm)
      obtain ⟨D, hD⟩ := hconv.norm.bddAbove_range
      exact ⟨D, fun n => hD ⟨n, rfl⟩⟩
    obtain ⟨M, hM⟩ := banach_steinhaus hptwise
    refine ⟨M, fun n => ?_⟩
    have hnorm : ‖innerSL ℂ (v n)‖ = ‖v n‖ := innerSL_apply_norm (𝕜 := ℂ) (v n)
    have hveq : ‖v n‖ = ‖Xₙ n‖ := by
      rw [hv, hXₙ, Lp.norm_toLp, Lp.norm_toLp, eLpNorm_star]
    rw [← hveq, ← hnorm]; exact hM n
  -- The weak lower-semicontinuity argument.
  have hre : Filter.Tendsto (fun n => (RCLike.re (inner ℂ X (Xₙ n)) : ℝ)) Filter.atTop
      (nhds (RCLike.re (inner ℂ X X))) :=
    (Complex.reCLM.continuous.tendsto _).comp hconvInner
  have hnormsq : RCLike.re (inner ℂ X X) = ‖X‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) X
  set g : ℕ → ℝ := fun n => 2 * RCLike.re (inner ℂ X (Xₙ n)) - ‖X‖ ^ 2 with hg
  have hgconv : Filter.Tendsto g Filter.atTop (nhds (‖X‖ ^ 2)) := by
    have hlim : Filter.Tendsto (fun n => 2 * RCLike.re (inner ℂ X (Xₙ n)) - ‖X‖ ^ 2)
        Filter.atTop (nhds (2 * RCLike.re (inner ℂ X X) - ‖X‖ ^ 2)) :=
      (hre.const_mul 2).sub_const (‖X‖ ^ 2)
    rwa [hnormsq, show 2 * ‖X‖ ^ 2 - ‖X‖ ^ 2 = ‖X‖ ^ 2 by ring] at hlim
  have hle : ∀ n, g n ≤ ‖Xₙ n‖ ^ 2 := by
    intro n
    have h1 : RCLike.re (inner ℂ X (Xₙ n)) ≤ ‖X‖ * ‖Xₙ n‖ :=
      re_inner_le_norm (𝕜 := ℂ) X (Xₙ n)
    have h2 : 2 * (‖X‖ * ‖Xₙ n‖) ≤ ‖X‖ ^ 2 + ‖Xₙ n‖ ^ 2 := by
      nlinarith [sq_nonneg (‖X‖ - ‖Xₙ n‖)]
    rw [hg]; nlinarith [h1, h2]
  have hcobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop (fun n => ‖Xₙ n‖ ^ 2) := by
    refine Filter.isCoboundedUnder_ge_of_le Filter.atTop (x := B ^ 2) (fun n => ?_)
    have hn : (0 : ℝ) ≤ ‖Xₙ n‖ := norm_nonneg _
    nlinarith [hB n, hn]
  calc ‖X‖ ^ 2 = Filter.liminf g Filter.atTop := (hgconv.liminf_eq).symm
    _ ≤ Filter.liminf (fun n => ‖Xₙ n‖ ^ 2) Filter.atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)
          hgconv.isBoundedUnder_ge hcobdd

/-- **Weak-derivative limit passage.** If `fₙ → g` locally uniformly (all
continuous and locally integrable), each `gxₙ` is a weak directional derivative of `fₙ`
in the real direction `v`, and `gxₙ` converges weakly in `L²` to `u`, then `u` is a
weak directional derivative of `g` in the direction `v`.

Both sides of the integration-by-parts identity `∫ (∂ᵥφ)·fₙ = − ∫ φ·gxₙ` pass to the
limit: the left through locally uniform convergence against the compactly supported
`∂ᵥφ`, the right through weak `L²` convergence tested against the `L²` function `φ`. -/
theorem hasWeakDirDeriv_of_tendsto {fₙ : ℕ → ℂ → ℂ} {g u : ℂ → ℂ} {v : ℂ}
    (hconv : TendstoLocallyUniformly fₙ g Filter.atTop)
    (hfcont : ∀ n, Continuous (fₙ n)) (hgcont : Continuous g)
    {gxₙ : ℕ → ℂ → ℂ} (hgxₙ : ∀ n, HasWeakDirDeriv v (gxₙ n) (fₙ n) Set.univ)
    (hweak : TendstoWeaklyL2Loc gxₙ u) :
    HasWeakDirDeriv v u g Set.univ := by
  intro φ hφ hcs _htsupp
  change ∫ z, ((fderiv ℝ φ z) v) • g z = - ∫ z, φ z • u z
  -- The directional-derivative weight `m := ∂ᵥφ`: continuous with compact support.
  set m : ℂ → ℝ := fun z => (fderiv ℝ φ z) v with hm
  have hmcont : Continuous m := (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hmcs : HasCompactSupport m := HasCompactSupport.fderiv_apply ℝ hcs v
  have hmint : Integrable (fun z => ‖m z‖) volume :=
    (hmcont.integrable_of_hasCompactSupport hmcs).norm
  -- Integrability of `m • h` for continuous `h`.
  have : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  have : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have integ : ∀ {h : ℂ → ℂ}, Continuous h → Integrable (fun z => m z • h z) volume := by
    intro h hh
    exact (hmcont.smul hh).integrable_of_hasCompactSupport hmcs.smul_right
  -- LHS limit: `∫ m • fₙ n → ∫ m • g` by uniform convergence on the compact `tsupport m`.
  have hL : Filter.Tendsto (fun n => ∫ z, m z • fₙ n z) Filter.atTop
      (nhds (∫ z, m z • g z)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hC0 : (0 : ℝ) ≤ ∫ z, ‖m z‖ := integral_nonneg fun z => norm_nonneg _
    set C : ℝ := (∫ z, ‖m z‖) + 1 with hC
    have hCpos : 0 < C := by linarith
    have huc : TendstoUniformlyOn fₙ g Filter.atTop (tsupport m) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hmcs).mp
        hconv.tendstoLocallyUniformlyOn
    have hev := (Metric.tendstoUniformlyOn_iff.mp huc) (ε / (2 * C)) (by positivity)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine ⟨N, fun n hn => ?_⟩
    have hsub : (∫ z, m z • fₙ n z) - ∫ z, m z • g z = ∫ z, m z • (fₙ n z - g z) := by
      rw [← integral_sub (integ (hfcont n)) (integ hgcont)]
      congr 1; funext z; exact (smul_sub (m z) (fₙ n z) (g z)).symm
    rw [dist_eq_norm, hsub]
    have hbd : ∀ z, ‖m z • (fₙ n z - g z)‖ ≤ (ε / (2 * C)) * ‖m z‖ := by
      intro z
      by_cases hz : z ∈ tsupport m
      · have hd := hN n hn z hz
        rw [dist_comm, dist_eq_norm] at hd
        rw [Complex.real_smul, norm_mul, Complex.norm_real, mul_comm]
        exact mul_le_mul_of_nonneg_right hd.le (norm_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hz]
        simp
    calc ‖∫ z, m z • (fₙ n z - g z)‖
        ≤ ∫ z, ‖m z • (fₙ n z - g z)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, (ε / (2 * C)) * ‖m z‖ := by
          refine integral_mono_of_nonneg ?_ (hmint.const_mul _) ?_
          · filter_upwards with z using norm_nonneg _
          · filter_upwards with z using hbd z
      _ = (ε / (2 * C)) * ∫ z, ‖m z‖ := integral_const_mul _ _
      _ < ε := by
          have hlt : (∫ z, ‖m z‖) < C := by rw [hC]; linarith
          calc (ε / (2 * C)) * ∫ z, ‖m z‖ ≤ (ε / (2 * C)) * C :=
                mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ = ε / 2 := by field_simp
            _ < ε := by linarith
  -- RHS limit: `∫ φ • gxₙ n → ∫ φ • u` by the weak `L²` pairing against `φ`.
  have hφC : Continuous fun z => ((φ z : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hφ.continuous
  have hφcs : HasCompactSupport fun z => ((φ z : ℝ) : ℂ) :=
    hcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hφL2 : MemLp (fun z => ((φ z : ℝ) : ℂ)) 2 volume :=
    hφC.memLp_of_hasCompactSupport hφcs
  have hpair : ∀ h : ℂ → ℂ, (∫ z, h z * ((φ z : ℝ) : ℂ)) = ∫ z, φ z • h z := by
    intro h; congr 1; funext z; rw [Complex.real_smul, mul_comm]
  have hR : Filter.Tendsto (fun n => ∫ z, φ z • gxₙ n z) Filter.atTop
      (nhds (∫ z, φ z • u z)) := by
    have hw := hweak (fun z => ((φ z : ℝ) : ℂ)) hφL2 hφcs
    rw [hpair u] at hw
    exact hw.congr fun n => hpair (gxₙ n)
  -- The per-`n` identity and uniqueness of limits.
  have hEq : ∀ n, ∫ z, m z • fₙ n z = - ∫ z, φ z • gxₙ n z := fun n =>
    hgxₙ n φ hφ hcs (Set.subset_univ _)
  have hL' : Filter.Tendsto (fun n => ∫ z, m z • fₙ n z) Filter.atTop
      (nhds (- ∫ z, φ z • u z)) :=
    hR.neg.congr fun n => (hEq n).symm
  exact tendsto_nhds_unique hL hL'

/-- **Weak continuity of the tested Jacobian.** Along a sequence `fₙ → g` locally
uniformly (continuous, `W^{1,2}_loc`, a.e. differentiable) whose weak gradients
`(gxₙ, gyₙ)` converge weakly in `L²` to the weak gradient `(gx, gy)` of `g`, with
uniform `L²`-bounds on the gradients, the tested Jacobians converge:
`∫ (jacobianWeak gxₙ gyₙ)·φ → ∫ (jacobianWeak gx gy)·φ`.

Each `∫ (jacobianWeak · ·)·φ` is rewritten by `integral_jacobianWeak_smul_eq` into the
first-order form `∫ (Re fₙ)·((Im gxₙ)·∂ᵧφ − (Im gyₙ)·∂ₓφ)`, whose two limits split into
a uniform-convergence term (`(Re fₙ − Re g)` times a uniformly-`L²`-bounded factor) and
a weak-`L²`-convergence term (the gradient tested against the fixed `L²` function
`Re g·∂φ`). -/
theorem tendsto_integral_jacobianWeak_smul {fₙ : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hconv : TendstoLocallyUniformly fₙ g Filter.atTop)
    (hfcont : ∀ n, Continuous (fₙ n)) (hgcont : Continuous g)
    (hfdiff : ∀ n, ∀ᵐ z, DifferentiableAt ℝ (fₙ n) z) (hfW12 : ∀ n, MemW12loc (fₙ n))
    (hgdiff : ∀ᵐ z, DifferentiableAt ℝ g z) (hgW12 : MemW12loc g)
    {gxₙ gyₙ : ℕ → ℂ → ℂ} {gxLim gyLim : ℂ → ℂ}
    (hgn : ∀ n, HasWeakGradient (gxₙ n) (gyₙ n) (fₙ n) Set.univ)
    (hgnx : ∀ n, MemLpLocOn (gxₙ n) 2 Set.univ) (hgny : ∀ n, MemLpLocOn (gyₙ n) 2 Set.univ)
    (hgLim : HasWeakGradient gxLim gyLim g Set.univ)
    (hgLimx : MemLpLocOn gxLim 2 Set.univ) (hgLimy : MemLpLocOn gyLim 2 Set.univ)
    (hweakx : TendstoWeaklyL2Loc gxₙ gxLim) (hweaky : TendstoWeaklyL2Loc gyₙ gyLim)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) {M : ℝ}
    (hMx : ∀ n, ∫ z in tsupport φ, ‖gxₙ n z‖ ^ 2 ≤ M)
    (hMy : ∀ n, ∫ z in tsupport φ, ‖gyₙ n z‖ ^ 2 ≤ M) :
    Filter.Tendsto (fun n => ∫ z, jacobianWeak (gxₙ n) (gyₙ n) z * φ z)
      Filter.atTop (nhds (∫ z, jacobianWeak gxLim gyLim z * φ z)) := by
  classical
  set K : Set ℂ := tsupport φ with hK_def
  have hKc : IsCompact K := hφc
  have hKm : MeasurableSet K := (isClosed_tsupport φ).measurableSet
  set q : ℂ → ℝ := fun z => (fderiv ℝ φ z) Complex.I with hq_def
  set p : ℂ → ℝ := fun z => (fderiv ℝ φ z) 1 with hp_def
  have hqc : Continuous q := (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hpc : Continuous p := (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hqcs : HasCompactSupport q := HasCompactSupport.fderiv_apply ℝ hφc Complex.I
  have hpcs : HasCompactSupport p := HasCompactSupport.fderiv_apply ℝ hφc 1
  have hqsub : tsupport q ⊆ K := tsupport_fderiv_apply_subset ℝ Complex.I
  have hpsub : tsupport p ⊆ K := tsupport_fderiv_apply_subset ℝ 1
  -- The `W^{1,2}` identity rewrites the tested Jacobian into the first-order divergence form.
  have hBn : ∀ n, (∫ z, jacobianWeak (gxₙ n) (gyₙ n) z * φ z)
      = ∫ z, (fₙ n z).re * ((gxₙ n z).im * q z - (gyₙ n z).im * p z) := fun n =>
    integral_jacobianWeak_smul_eq (f := fₙ n) (φ := φ) (hfcont n) (hfdiff n) (hfW12 n)
      (hgn n) (hgnx n) (hgny n) hφ hφc
  have hBg : (∫ z, jacobianWeak gxLim gyLim z * φ z)
      = ∫ z, (g z).re * ((gxLim z).im * q z - (gyLim z).im * p z) :=
    integral_jacobianWeak_smul_eq (f := g) (φ := φ) hgcont hgdiff hgW12 hgLim hgLimx hgLimy
      hφ hφc
  rw [show (fun n => ∫ z, jacobianWeak (gxₙ n) (gyₙ n) z * φ z)
      = fun n => ∫ z, (fₙ n z).re * ((gxₙ n z).im * q z - (gyₙ n z).im * p z)
      from funext hBn, hBg]
  -- Uniform convergence of `fₙ → g` on the compact support `K`.
  have huc : TendstoUniformlyOn fₙ g Filter.atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hKc).mp
      hconv.tendstoLocallyUniformlyOn
  -- `√M` bounds the `L²` masses of the sequence gradients on `K`.
  have hM0 : 0 ≤ M := le_trans (integral_nonneg fun z => by positivity) (hMx 0)
  -- `K` has finite volume.
  have hvolK : volume K < ⊤ := hKc.measure_lt_top
  -- Integrability of a first-order product `(Re h)·(Im w)·t` supported in `K`.
  have hint : ∀ (h w : ℂ → ℂ) (t : ℂ → ℝ), Continuous h → Continuous t →
      HasCompactSupport t → tsupport t ⊆ K → MemLpLocOn w 2 Set.univ →
      Integrable (fun z => (h z).re * (w z).im * t z) volume := by
    intro h w t hh ht htcs htsub hw
    have hwK : MemLp w 2 (volume.restrict K) := hw K (Set.subset_univ K) hKc
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hvolK⟩
    have hwim1 : Integrable (K.indicator fun z => (w z).im) volume := by
      rw [integrable_indicator_iff hKm]
      exact memLp_one_iff_integrable.mp (hwK.im.mono_exponent (p := 1) (by norm_num))
    have hst_cs : HasCompactSupport (fun z => (h z).re * t z) :=
      htcs.mul_left (f := fun z => (h z).re)
    obtain ⟨Ch, hCh⟩ := hst_cs.exists_bound_of_continuous (by fun_prop)
    have hbdd : Integrable (fun z => ((h z).re * t z)
        * (K.indicator fun z => (w z).im) z) volume :=
      hwim1.bdd_mul ((by fun_prop : Continuous fun z => (h z).re * t z)).aestronglyMeasurable
        (ae_of_all _ hCh)
    refine hbdd.congr (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ K
    · simp only [Set.indicator_of_mem hz]; ring
    · have htz : t z = 0 := image_eq_zero_of_notMem_tsupport (fun hmem => hz (htsub hmem))
      simp [Set.indicator_of_notMem hz, htz]
  -- The core per-term convergence, applied to `(gxₙ, q)` and `(gyₙ, p)`.
  have hcore : ∀ (wₙ : ℕ → ℂ → ℂ) (wLim : ℂ → ℂ) (t : ℂ → ℝ),
      Continuous t → tsupport t ⊆ K → (∀ n, MemLpLocOn (wₙ n) 2 Set.univ) →
      MemLpLocOn wLim 2 Set.univ → TendstoWeaklyL2Loc wₙ wLim →
      (∀ n, ∫ z in K, ‖wₙ n z‖ ^ 2 ≤ M) →
      Filter.Tendsto (fun n => ∫ z, (fₙ n z).re * (wₙ n z).im * t z) Filter.atTop
        (nhds (∫ z, (g z).re * (wLim z).im * t z)) := by
    intro wₙ wLim t htc htsub hwn hwL hwweak hMw
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hvolK⟩
    have htcs : HasCompactSupport t :=
      HasCompactSupport.of_support_subset_isCompact hKc (subset_trans subset_closure htsub)
    -- Integrability of each first-order product.
    have hIn : ∀ n, Integrable (fun z => (fₙ n z).re * (wₙ n z).im * t z) volume := fun n =>
      hint (fₙ n) (wₙ n) t (hfcont n) htc htcs htsub (hwn n)
    have hIg : Integrable (fun z => (g z).re * (wLim z).im * t z) volume :=
      hint g wLim t hgcont htc htcs htsub hwL
    -- WEAK TERM: `∫ g.re·(wₙ).im·t → ∫ g.re·(wLim).im·t` by weak-`L²` pairing.
    have hweakterm : Filter.Tendsto (fun n => ∫ z, (g z).re * (wₙ n z).im * t z)
        Filter.atTop (nhds (∫ z, (g z).re * (wLim z).im * t z)) := by
      -- The fixed real weight `s = g.re·t` and the complex test function `ψ = s·(-i)`.
      set s : ℂ → ℝ := fun z => (g z).re * t z with hs_def
      have hscont : Continuous s := by fun_prop
      have hscs : HasCompactSupport s := htcs.mul_left (f := fun z => (g z).re)
      set ψ : ℂ → ℂ := fun z => (s z : ℂ) * (-Complex.I) with hψ_def
      have hψcont : Continuous ψ := by fun_prop
      have hψcs : HasCompactSupport ψ :=
        (hscs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).mul_right
      have hψLp : MemLp ψ 2 volume := hψcont.memLp_of_hasCompactSupport hψcs
      -- Pairing rewrite: `(∫ w·ψ).re = ∫ g.re·w.im·t` for any `L²_loc` `w`.
      have hpairing : ∀ (w : ℂ → ℂ), MemLpLocOn w 2 Set.univ →
          (∫ z, w z * ψ z).re = ∫ z, (g z).re * (w z).im * t z := by
        intro w hw
        have hInt : Integrable (fun z => w z * ψ z) volume := by
          have hwK : MemLp w 2 (volume.restrict K) := hw K (Set.subset_univ K) hKc
          have hprodK : Integrable (fun z => w z * ψ z) (volume.restrict K) :=
            hwK.integrable_mul (hψLp.restrict K)
          rw [← integrableOn_iff_integrable_of_support_subset (s := K)]
          · exact hprodK
          · intro z hz
            by_contra hzK
            have hψz : ψ z = 0 := by
              have : s z = 0 := by
                have htz : t z = 0 :=
                  image_eq_zero_of_notMem_tsupport (fun hmem => hzK (htsub hmem))
                simp [hs_def, htz]
              simp [hψ_def, this]
            exact hz (by simp [hψz])
        have hre : (∫ z, w z * ψ z).re = ∫ z, (w z * ψ z).re :=
          (integral_re hInt).symm
        rw [hre]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [hψ_def, hs_def]
        push_cast
        simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [← hpairing wLim hwL]
      refine (Complex.reCLM.continuous.tendsto _).comp (hwweak ψ hψLp hψcs) |>.congr fun n => ?_
      rw [Function.comp_apply, Complex.reCLM_apply, hpairing (wₙ n) (hwn n)]
    -- UNIFORM TERM: `∫ (fₙ.re − g.re)·(wₙ).im·t → 0`.
    have hunifterm : Filter.Tendsto
        (fun n => ∫ z, ((fₙ n z).re - (g z).re) * (wₙ n z).im * t z)
        Filter.atTop (nhds 0) := by
      -- Cauchy–Schwarz constant: the `L²(K)`-norm of the fixed weight `t`.
      have htLp : MemLp t 2 (volume.restrict K) := (htc.memLp_of_hasCompactSupport htcs).restrict K
      set Ct : ℝ := (∫ z in K, |t z| ^ 2) ^ (1 / 2 : ℝ) with hCt_def
      have hCt0 : 0 ≤ Ct := by positivity
      have h2conj : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
      -- Uniform Cauchy–Schwarz bound: `∫_K |(wₙ).im·t| ≤ √M · Ct`.
      have hCSbd : ∀ n, (∫ z in K, |(wₙ n z).im| * |t z|) ≤ Real.sqrt M * Ct := by
        intro n
        have hwimLp : MemLp (fun z => (wₙ n z).im) 2 (volume.restrict K) :=
          ((hwn n) K (Set.subset_univ K) hKc).im
        have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict K) h2conj
          (f := fun z => |(wₙ n z).im|) (g := fun z => |t z|)
          (ae_of_all _ fun z => abs_nonneg _) (ae_of_all _ fun z => abs_nonneg _)
          (by simpa using! hwimLp.abs) (by simpa using! htLp.abs)
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num] at hcs
        simp only [Real.rpow_natCast] at hcs
        refine hcs.trans ?_
        have hwimK2 : Integrable (fun z => ‖wₙ n z‖ ^ 2) (volume.restrict K) := by
          have := ((hwn n) K (Set.subset_univ K) hKc).norm.integrable_sq
          simpa using this
        have hmono : (∫ z in K, |(wₙ n z).im| ^ 2) ≤ ∫ z in K, ‖wₙ n z‖ ^ 2 := by
          refine integral_mono_of_nonneg (ae_of_all _ fun z => by positivity) hwimK2
            (ae_of_all _ fun z => ?_)
          change |(wₙ n z).im| ^ 2 ≤ ‖wₙ n z‖ ^ 2
          exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2
        have hwbd : (∫ z in K, |(wₙ n z).im| ^ 2) ^ (1 / 2 : ℝ) ≤ Real.sqrt M := by
          rw [Real.sqrt_eq_rpow]
          refine Real.rpow_le_rpow (integral_nonneg fun z => by positivity)
            (hmono.trans (hMw n)) (by norm_num)
        exact mul_le_mul hwbd (le_of_eq hCt_def.symm) (by positivity) (Real.sqrt_nonneg _)
      -- The uniform constant `Cu = √M·Ct`.
      set Cu : ℝ := Real.sqrt M * Ct with hCu_def
      have hCu0 : 0 ≤ Cu := by positivity
      -- Integrability of `|(wₙ).im|·|t|` on the whole plane (supported in `K`).
      have hprodInt : ∀ n, Integrable (fun z => |(wₙ n z).im| * |t z|) volume := by
        intro n
        have h0 := hint (fun _ => (1 : ℂ)) (wₙ n) t continuous_const htc htcs htsub (hwn n)
        have := h0.abs
        refine this.congr (Filter.Eventually.of_forall fun z => ?_)
        simp [abs_mul]
      -- `‖∫ Iₙ‖ ≤ Cu·δ` whenever `‖fₙ n − g‖ ≤ δ` on `K`.
      have hbd : ∀ (n : ℕ) (δ : ℝ), 0 ≤ δ →
          (∀ z ∈ K, ‖fₙ n z - g z‖ ≤ δ) →
          ‖∫ z, ((fₙ n z).re - (g z).re) * (wₙ n z).im * t z‖ ≤ δ * Cu := by
        intro n δ hδ0 hδ
        calc ‖∫ z, ((fₙ n z).re - (g z).re) * (wₙ n z).im * t z‖
            ≤ ∫ z, ‖((fₙ n z).re - (g z).re) * (wₙ n z).im * t z‖ :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ z, δ * (|(wₙ n z).im| * |t z|) := by
              refine integral_mono_of_nonneg (ae_of_all _ fun z => norm_nonneg _)
                ((hprodInt n).const_mul δ) (ae_of_all _ fun z => ?_)
              simp only
              by_cases hz : z ∈ K
              · rw [Real.norm_eq_abs, abs_mul, abs_mul]
                have h1 : |(fₙ n z).re - (g z).re| ≤ δ := by
                  have hsub : (fₙ n z).re - (g z).re = (fₙ n z - g z).re := by
                    rw [Complex.sub_re]
                  rw [hsub]
                  exact le_trans (Complex.abs_re_le_norm _) (hδ z hz)
                calc |(fₙ n z).re - (g z).re| * |(wₙ n z).im| * |t z|
                    ≤ δ * |(wₙ n z).im| * |t z| := by gcongr
                  _ = δ * (|(wₙ n z).im| * |t z|) := by ring
              · have htz : t z = 0 :=
                  image_eq_zero_of_notMem_tsupport (fun hmem => hz (htsub hmem))
                simp [htz]
          _ = δ * ∫ z, |(wₙ n z).im| * |t z| := integral_const_mul _ _
          _ ≤ δ * Cu := by
              refine mul_le_mul_of_nonneg_left ?_ hδ0
              have hle : (∫ z, |(wₙ n z).im| * |t z|)
                  = ∫ z in K, |(wₙ n z).im| * |t z| := by
                rw [← integral_indicator hKm]
                refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
                by_cases hz : z ∈ K
                · rw [Set.indicator_of_mem hz]
                · have htz : t z = 0 :=
                    image_eq_zero_of_notMem_tsupport (fun hmem => hz (htsub hmem))
                  rw [Set.indicator_of_notMem hz]; simp [htz]
              rw [hle]; exact hCSbd n
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hunif := Metric.tendstoUniformlyOn_iff.mp huc (ε / (Cu + 1)) (by positivity)
      rw [Filter.eventually_atTop] at hunif
      obtain ⟨N, hN⟩ := hunif
      refine ⟨N, fun n hn => ?_⟩
      rw [dist_eq_norm, sub_zero]
      have hδ : ∀ z ∈ K, ‖fₙ n z - g z‖ ≤ ε / (Cu + 1) := by
        intro z hz
        have := hN n hn z hz
        rw [dist_comm, dist_eq_norm] at this
        exact this.le
      calc ‖∫ z, ((fₙ n z).re - (g z).re) * (wₙ n z).im * t z‖
          ≤ (ε / (Cu + 1)) * Cu := hbd n (ε / (Cu + 1)) (by positivity) hδ
        _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [hCu0, hε]
    -- Assemble: `∫ (fₙ).re·… = ∫ (fₙ.re − g.re)·… + ∫ g.re·…`.
    have hIg' : ∀ n, Integrable (fun z => (g z).re * (wₙ n z).im * t z) volume := fun n =>
      hint g (wₙ n) t hgcont htc htcs htsub (hwn n)
    have hIu : ∀ n, Integrable
        (fun z => ((fₙ n z).re - (g z).re) * (wₙ n z).im * t z) volume := fun n =>
      ((hIn n).sub (hIg' n)).congr (Filter.Eventually.of_forall fun z => by
        simp only [Pi.sub_apply]; ring)
    have hcomb : ∀ n, (∫ z, (fₙ n z).re * (wₙ n z).im * t z)
        = (∫ z, ((fₙ n z).re - (g z).re) * (wₙ n z).im * t z)
          + ∫ z, (g z).re * (wₙ n z).im * t z := by
      intro n
      rw [← integral_add (hIu n) (hIg' n)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      ring
    rw [show (fun n => ∫ z, (fₙ n z).re * (wₙ n z).im * t z)
        = fun n => (∫ z, ((fₙ n z).re - (g z).re) * (wₙ n z).im * t z)
          + ∫ z, (g z).re * (wₙ n z).im * t z from funext hcomb]
    have := hunifterm.add hweakterm
    simpa using this
  -- The two weights `q`, `p` and their `L²`-membership.
  have hxlim := hcore gxₙ gxLim q hqc hqsub hgnx hgLimx hweakx hMx
  have hylim := hcore gyₙ gyLim p hpc hpsub hgny hgLimy hweaky hMy
  -- `K` has finite volume.
  have hvolK : volume K < ⊤ := hKc.measure_lt_top
  -- Integrability of a first-order product `(Re h)·(Im w)·t` supported in `K`.
  have hint : ∀ (h w : ℂ → ℂ) (t : ℂ → ℝ), Continuous h → Continuous t →
      HasCompactSupport t → tsupport t ⊆ K → MemLpLocOn w 2 Set.univ →
      Integrable (fun z => (h z).re * (w z).im * t z) volume := by
    intro h w t hh ht htcs htsub hw
    -- The imaginary part of `w`, restricted to `K` by an indicator, is `L¹`.
    have hwK : MemLp w 2 (volume.restrict K) := hw K (Set.subset_univ K) hKc
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hvolK⟩
    have hwim1 : Integrable (K.indicator fun z => (w z).im) volume := by
      rw [integrable_indicator_iff hKm]
      exact memLp_one_iff_integrable.mp (hwK.im.mono_exponent (p := 1) (by norm_num))
    -- The continuous factor `h.re · t` is bounded (it vanishes off compact `tsupport t`).
    have hst_cs : HasCompactSupport (fun z => (h z).re * t z) :=
      htcs.mul_left (f := fun z => (h z).re)
    obtain ⟨Ch, hCh⟩ := hst_cs.exists_bound_of_continuous (by fun_prop)
    -- `(Re h · t)` is bounded and measurable, so multiplying preserves `L¹`.
    have hbdd : Integrable (fun z => ((h z).re * t z)
        * (K.indicator fun z => (w z).im) z) volume :=
      hwim1.bdd_mul ((by fun_prop : Continuous fun z => (h z).re * t z)).aestronglyMeasurable
        (ae_of_all _ hCh)
    refine hbdd.congr (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ K
    · simp only [Set.indicator_of_mem hz]; ring
    · have htz : t z = 0 := image_eq_zero_of_notMem_tsupport (fun hmem => hz (htsub hmem))
      simp [Set.indicator_of_notMem hz, htz]
  -- The difference-of-integrals split and the combined limit.
  have hsplit : ∀ (h wx wy : ℂ → ℂ),
      Integrable (fun z => (h z).re * (wx z).im * q z) volume →
      Integrable (fun z => (h z).re * (wy z).im * p z) volume →
      (∫ z, (h z).re * ((wx z).im * q z - (wy z).im * p z))
        = (∫ z, (h z).re * (wx z).im * q z) - ∫ z, (h z).re * (wy z).im * p z := by
    intro h wx wy hix hiy
    rw [← integral_sub hix hiy]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  -- Split each tested integral into the `q`- and `p`-pieces and pass to the two limits.
  have hseqeq : ∀ n, (∫ z, (fₙ n z).re * ((gxₙ n z).im * q z - (gyₙ n z).im * p z))
      = (∫ z, (fₙ n z).re * (gxₙ n z).im * q z)
        - ∫ z, (fₙ n z).re * (gyₙ n z).im * p z := fun n =>
    hsplit (fₙ n) (gxₙ n) (gyₙ n)
      (hint (fₙ n) (gxₙ n) q (hfcont n) hqc hqcs hqsub (hgnx n))
      (hint (fₙ n) (gyₙ n) p (hfcont n) hpc hpcs hpsub (hgny n))
  have hlimeq : (∫ z, (g z).re * ((gxLim z).im * q z - (gyLim z).im * p z))
      = (∫ z, (g z).re * (gxLim z).im * q z) - ∫ z, (g z).re * (gyLim z).im * p z :=
    hsplit g gxLim gyLim
      (hint g gxLim q hgcont hqc hqcs hqsub hgLimx)
      (hint g gyLim p hgcont hpc hpcs hpsub hgLimy)
  rw [show (fun n => ∫ z, (fₙ n z).re * ((gxₙ n z).im * q z - (gyₙ n z).im * p z))
      = fun n => (∫ z, (fₙ n z).re * (gxₙ n z).im * q z)
        - ∫ z, (fₙ n z).re * (gyₙ n z).im * p z from funext hseqeq, hlimeq]
  exact hxlim.sub hylim

/-- **Weighted weak lower semicontinuity of the `L²` norm, local form.** The
weighted-energy lower semicontinuity of `le_liminf_integral_normSq_smul` for sequences
that are only locally square-integrable and converge weakly against compactly supported
tests, with a bounded nonnegative weight `w` vanishing outside a compact set `S`.

Truncating the sequence to `S` reduces to the global statement: the indicator
truncations are genuinely `L²(volume)`, converge weakly in the global sense (any `L²`
test `ψ` pairs with the truncation exactly as the compactly supported test `𝟙_S·ψ`
pairs with the original), and the weighted energies are unchanged since `w` vanishes
off `S`. -/
theorem le_liminf_integral_normSq_smul_of_compactSupport {hₙ : ℕ → ℂ → ℂ} {h : ℂ → ℂ}
    (hw_conv : TendstoWeaklyL2Loc hₙ h)
    (hmemH : MemLpLocOn h 2 Set.univ) (hmemHn : ∀ n, MemLpLocOn (hₙ n) 2 Set.univ)
    {w : ℂ → ℝ} (hwmeas : Measurable w) {C : ℝ} (hwnn : ∀ z, 0 ≤ w z)
    (hwle : ∀ z, w z ≤ C) {S : Set ℂ} (hS : IsCompact S)
    (hw0 : ∀ z ∉ S, w z = 0) :
    ∫ z, ‖h z‖ ^ 2 * w z
      ≤ (Filter.liminf (fun n => ∫ z, ‖hₙ n z‖ ^ 2 * w z) Filter.atTop) := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  -- The truncations to `S` are genuinely `L²(volume)`.
  have hmemH' : MemLp (S.indicator h) 2 volume :=
    (memLp_indicator_iff_restrict hSm).mpr (hmemH S (Set.subset_univ S) hS)
  have hmemHn' : ∀ n, MemLp (S.indicator (hₙ n)) 2 volume := fun n =>
    (memLp_indicator_iff_restrict hSm).mpr (hmemHn n S (Set.subset_univ S) hS)
  -- The truncations converge weakly in the global sense: a global `L²` test `ψ`
  -- pairs with the truncation exactly as the compactly supported test `𝟙_S·ψ`
  -- pairs with the original sequence.
  have hconv' : TendstoWeaklyL2 (fun n => S.indicator (hₙ n)) (S.indicator h) := by
    intro ψ hψ
    have hψ'mem : MemLp (S.indicator ψ) 2 volume :=
      (memLp_indicator_iff_restrict hSm).mpr (hψ.restrict S)
    have hψ'cs : HasCompactSupport (S.indicator ψ) :=
      HasCompactSupport.intro hS fun _ hx => Set.indicator_of_notMem hx ψ
    have hpair : ∀ g : ℂ → ℂ, ∀ z, g z * S.indicator ψ z = S.indicator g z * ψ z := by
      intro g z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul, mul_zero]
    have hconv := hw_conv (S.indicator ψ) hψ'mem hψ'cs
    have hrhs : (∫ z, h z * S.indicator ψ z) = ∫ z, S.indicator h z * ψ z :=
      integral_congr_ae (Filter.Eventually.of_forall (hpair h))
    rw [hrhs] at hconv
    exact hconv.congr fun n =>
      integral_congr_ae (Filter.Eventually.of_forall (hpair (hₙ n)))
  -- The weighted energies are unchanged by the truncation: `w` vanishes off `S`.
  have henergy : ∀ g : ℂ → ℂ, ∀ z, ‖S.indicator g z‖ ^ 2 * w z = ‖g z‖ ^ 2 * w z := by
    intro g z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hw0 z hz, mul_zero, mul_zero]
  have hmain := le_liminf_integral_normSq_smul hconv' hmemH' hmemHn' hwmeas hwnn hwle
  have hLHS : (∫ z, ‖S.indicator h z‖ ^ 2 * w z) = ∫ z, ‖h z‖ ^ 2 * w z :=
    integral_congr_ae (Filter.Eventually.of_forall (henergy h))
  have hRHS : (fun n => ∫ z, ‖S.indicator (hₙ n) z‖ ^ 2 * w z)
      = fun n => ∫ z, ‖hₙ n z‖ ^ 2 * w z :=
    funext fun n => integral_congr_ae (Filter.Eventually.of_forall (henergy (hₙ n)))
  rw [hLHS, hRHS] at hmain
  exact hmain

end NoWanderingDomains
