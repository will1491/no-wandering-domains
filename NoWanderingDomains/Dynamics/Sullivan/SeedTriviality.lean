/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Dynamics.Deformation.SphereVectorField.Transport
import NoWanderingDomains.QC.Calculus.WeylLocal
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# The explicit seed family and its triviality criterion

The infinite-dimensional input to Sullivan's finiteness argument: an explicit
family of Beltrami *seeds* carried by a round disk, together with explicit
solutions of the corresponding `∂̄`-equations, and the **triviality
criterion**: if a sphere vector field whose `∂̄` restricts on an open set
`U'` to a linear combination of the seeds vanishes on the frontier of `U'`,
then the combination is zero.

For a disk `D = ball a ρ` the `k`-th seed (`seedBasis`, `k = 0, 1, …`) is

`σₖ(z) = (k+1)·conj(z−a)^k · 1_D`,

with the explicit solution (`seedSolution`)

`uₖ(z) = conj(z−a)^{k+1}` on `D`, `uₖ(z) = ρ^{2(k+1)}·(z−a)^{−(k+1)}` off `D`

— continuous across the circle `|z−a| = ρ` (where `conj(w)^{k+1}` equals
`(ρ²/w)^{k+1}`), with `∂̄uₖ = σₖ` weakly, holomorphic off the closed disk,
and vanishing at infinity. Off the disk the solutions assemble into the
negative-power tail `negPowerCombo`, a rational function whose only pole is
at `a`.

The triviality criterion (`seed_vanish_of_sphereField_vanish_on_frontier`)
is stated for an open `U' ⊆ ℂ` (the endgame passes the finite part of a
Fatou component and transfers frontier data through the charts): given a
sphere field `v` with `∂̄v = Σ cₖ·σₖ` a.e. on `U'` and `v = 0` on the
frontier of `U'`, the function `h := v − Σ cₖ·uₖ` is weakly holomorphic on
`U'`, hence holomorphic (open-set Weyl); damping by
`M(z) = (z−a)^K/(z−b)^{K+3}` — where `b` avoids the closure of `U'` and `K`
dominates the pole order of the tail — makes `F := (h + negPowerCombo)·M`
holomorphic on `U'` (the zero of `M` at `a` absorbs the pole), vanishing on
the frontier (there `h + negPowerCombo = v = 0`) and at infinity (`M` decays
like `|z|^{−3}` against the `O(|z|²)` growth of a sphere field). The
maximum principle for holomorphic functions with vanishing boundary and
infinity data (`eqOn_zero_of_forall_frontier_tendsto_zero`, built on
Mathlib's `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm` /
`Complex.norm_le_of_forall_mem_frontier_norm_le` via compact exhaustion of
`{‖F‖ ≥ ε}`) forces `F ≡ 0`, so the negative-power tail extends
holomorphically across `a`, which kills every coefficient
(`coeffs_eq_zero_of_negPowerCombo_extends`).
-/

open MeasureTheory Complex Metric Filter Topology

namespace NoWanderingDomains

/-! ## The seed family and its explicit solutions -/

/-- The `k`-th **seed coefficient** on the disk `ball a ρ`:
`(k+1)·conj(z−a)^k` inside the disk, `0` outside. The index `k` starts at
`0`; the normalizing factor `k+1` makes `seedSolution` a `∂̄`-primitive with
coefficient exactly `1`. -/
noncomputable def seedBasis (a : ℂ) (ρ : ℝ) (k : ℕ) : ℂ → ℂ := fun z =>
  open Classical in
  if z ∈ Metric.ball a ρ
    then ((k : ℂ) + 1) * (starRingEnd ℂ (z - a)) ^ k else 0

/-- The explicit solution of `∂̄u = seedBasis a ρ k`: the anti-holomorphic
power `conj(z−a)^{k+1}` inside the disk, matched across the circle to the
holomorphic negative power `ρ^{2(k+1)}·(z−a)^{−(k+1)}` outside. Total; the
center `z = a` lies inside the disk (for `ρ > 0`), so the negative power is
only evaluated away from its pole. -/
noncomputable def seedSolution (a : ℂ) (ρ : ℝ) (k : ℕ) : ℂ → ℂ := fun z =>
  open Classical in
  if z ∈ Metric.ball a ρ
    then (starRingEnd ℂ (z - a)) ^ (k + 1)
    else ((ρ ^ (2 * (k + 1)) : ℝ) : ℂ) * (z - a) ^ (-(k + 1 : ℤ))

/-- A linear combination of the first `K` seeds — the general element of the
`K`-dimensional seed family. -/
noncomputable def seedCombo (a : ℂ) (ρ : ℝ) (K : ℕ) (c : Fin K → ℂ) :
    ℂ → ℂ := fun z =>
  ∑ k : Fin K, c k * seedBasis a ρ k z

/-- The **negative-power tail**: the rational function
`Σ cₖ·ρ^{2(k+1)}·(z−a)^{−(k+1)}`, holomorphic on `ℂ ∖ {a}` with its only
pole at `a`. Off the disk it is the corresponding combination of the
explicit solutions. -/
noncomputable def negPowerCombo (a : ℂ) (ρ : ℝ) (K : ℕ) (c : Fin K → ℂ) :
    ℂ → ℂ := fun z =>
  ∑ k : Fin K, c k * ((ρ ^ (2 * (k.1 + 1)) : ℝ) : ℂ) * (z - a) ^ (-(k.1 + 1 : ℤ))

/-- Off the disk, the seed solutions assemble into the negative-power
tail. -/
theorem sum_seedSolution_eq_negPowerCombo (a : ℂ) (ρ : ℝ) (K : ℕ)
    (c : Fin K → ℂ) {z : ℂ} (hz : z ∉ Metric.ball a ρ) :
    ∑ k : Fin K, c k * seedSolution a ρ k z = negPowerCombo a ρ K c z := by
  simp only [negPowerCombo]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [seedSolution]
  rw [if_neg hz, mul_assoc]

/-- The explicit solution is continuous: inside and outside pieces are
continuous on their open domains, and they match on the circle
`|z−a| = ρ`, where `conj(w)^{k+1} = (ρ²/w)^{k+1} = ρ^{2(k+1)}·w^{−(k+1)}`
for `w = z−a`. -/
theorem seedSolution_continuous (a : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    Continuous (seedSolution a ρ k) := by
  -- the two branches agree on the circle `‖z - a‖ = ρ`
  have hmatch : ∀ z : ℂ, ‖z - a‖ = ρ →
      (starRingEnd ℂ (z - a)) ^ (k + 1)
        = ((ρ ^ (2 * (k + 1)) : ℝ) : ℂ) * (z - a) ^ (-(k + 1 : ℤ)) := by
    intro z hz
    have hw0 : z - a ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      exact hρ.ne hz
    have hkey : (starRingEnd ℂ (z - a)) * (z - a) = ((ρ : ℂ)) ^ 2 := by
      rw [Complex.conj_mul', hz]
    have h1 : (starRingEnd ℂ (z - a)) ^ (k + 1) * (z - a) ^ (k + 1)
        = ((ρ ^ (2 * (k + 1)) : ℝ) : ℂ) := by
      rw [← mul_pow, hkey, ← pow_mul, Complex.ofReal_pow]
    have hexp : (-(k + 1 : ℤ)) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hexp, zpow_neg, zpow_natCast]
    field_simp [pow_ne_zero (k + 1) hw0]
    linear_combination h1
  -- glue the branches with `continuous_if`
  classical
  change Continuous fun z : ℂ =>
    open Classical in
    if z ∈ Metric.ball a ρ
      then (starRingEnd ℂ (z - a)) ^ (k + 1)
      else ((ρ ^ (2 * (k + 1)) : ℝ) : ℂ) * (z - a) ^ (-(k + 1 : ℤ))
  refine continuous_if ?_ ?_ ?_
  · intro z hz
    have hz' : z ∈ Metric.sphere a ρ := by
      rw [← frontier_ball a hρ.ne']
      simpa [Set.ofPred_mem_eq] using! hz
    exact hmatch z (mem_sphere_iff_norm.mp hz')
  · exact ((Complex.continuous_conj.comp
      (continuous_id.sub continuous_const)).pow (k + 1)).continuousOn
  · have hcl : closure {x : ℂ | x ∉ Metric.ball a ρ} = (Metric.ball a ρ)ᶜ := by
      have h1 : {x : ℂ | x ∉ Metric.ball a ρ} = (Metric.ball a ρ)ᶜ := rfl
      rw [h1, IsClosed.closure_eq (isClosed_compl_iff.mpr isOpen_ball)]
    rw [hcl]
    intro z hz
    have hz_ne : z - a ≠ 0 := by
      have h1 : ¬ dist z a < ρ := fun h => hz (Metric.mem_ball.mpr h)
      have h2 : (0 : ℝ) < dist z a := lt_of_lt_of_le hρ (not_lt.mp h1)
      rw [dist_eq_norm] at h2
      intro h
      rw [h, norm_zero] at h2
      exact lt_irrefl 0 h2
    have h3 : ContinuousAt (fun w : ℂ => ((ρ ^ (2 * (k + 1)) : ℝ) : ℂ)
        * (w - a) ^ (-(k + 1 : ℤ))) z := by
      have h4 : ContinuousAt (fun w : ℂ => w ^ (-(k + 1 : ℤ))) (z - a) :=
        continuousAt_zpow₀ _ _ (Or.inl hz_ne)
      have h5 : ContinuousAt (fun w : ℂ => w - a) z :=
        (continuous_id.sub continuous_const).continuousAt
      exact continuousAt_const.mul (ContinuousAt.comp (f := fun w : ℂ => w - a) h4 h5)
    exact h3.continuousWithinAt

/-- The explicit solution solves its `∂̄`-equation weakly, with locally
square-integrable gradient: `∂̄(seedSolution) = seedBasis` on `ℂ`. Inside
and outside the disk this is the classical Wirtinger calculus of the
explicit formulas; the pieces glue across the (null) circle because the
function is continuous there — integration by parts against a test function
picks up no boundary term. -/
theorem hasL2WeakDzbar_seedSolution (a : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    HasL2WeakDzbar (seedSolution a ρ k) (seedBasis a ρ k) Set.univ := by
  -- ===== the seed coefficient: measurability, `Lᵖ` membership, support =====
  have hgcont : Continuous fun z : ℂ => ((k : ℂ) + 1) * (starRingEnd ℂ (z - a)) ^ k :=
    continuous_const.mul
      ((Complex.continuous_conj.comp (continuous_id.sub continuous_const)).pow k)
  have hind : seedBasis a ρ k
      = (Metric.ball a ρ).indicator
          (fun z : ℂ => ((k : ℂ) + 1) * (starRingEnd ℂ (z - a)) ^ k) := by
    funext z
    by_cases hz : z ∈ Metric.ball a ρ
    · rw [Set.indicator_of_mem hz]
      simp only [seedBasis]
      rw [if_pos hz]
    · rw [Set.indicator_of_notMem hz]
      simp only [seedBasis]
      rw [if_neg hz]
  have hσmem : ∀ p : ENNReal, MemLp (seedBasis a ρ k) p volume := by
    intro p
    rw [hind, memLp_indicator_iff_restrict measurableSet_ball]
    have : IsFiniteMeasure ((volume : Measure ℂ).restrict (Metric.ball a ρ)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    refine MemLp.of_bound (hgcont.aestronglyMeasurable.restrict)
      (((k : ℝ) + 1) * ρ ^ k) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hz' : ‖z - a‖ ≤ ρ := by
      rw [← dist_eq_norm]
      exact (Metric.mem_ball.mp hz).le
    have h1 : ‖((k : ℂ) + 1) * (starRingEnd ℂ (z - a)) ^ k‖
        = ((k : ℝ) + 1) * ‖z - a‖ ^ k := by
      rw [norm_mul, norm_pow, Complex.norm_conj]
      congr 1
      have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]
      push_cast
      ring
    rw [h1]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz' k) hk0
  have hσsupp : ∀ z : ℂ, ‖a‖ + ρ < ‖z‖ → seedBasis a ρ k z = 0 := by
    intro z hz
    have hz_ball : z ∉ Metric.ball a ρ := by
      intro h
      have h1 : ‖z - a‖ < ρ := by
        rw [← dist_eq_norm]
        exact Metric.mem_ball.mp h
      have h2 : ‖z‖ - ‖a‖ ≤ ‖z - a‖ := norm_sub_norm_le z a
      linarith
    simp only [seedBasis]
    rw [if_neg hz_ball]
  -- ===== the Cauchy transform of the seed and its calculus =====
  have hp4 : (2 : ENNReal) < 4 := by norm_num
  have hp4' : (4 : ENNReal) ≠ ⊤ := by norm_num
  have hP_cont : Continuous (cauchyTransform (seedBasis a ρ k)) :=
    continuous_cauchyTransform_of_memLp_of_support hp4 hp4' (hσmem 4) hσsupp
  have hP0 : Tendsto (cauchyTransform (seedBasis a ρ k)) (Filter.cocompact ℂ) (𝓝 0) :=
    cauchyTransform_tendsto_cocompact hp4 hp4' (hσmem 4) hσsupp
  obtain ⟨hPx, hPy⟩ := hasWeakGradient_cauchyTransform hp4 hp4' (hσmem 4) hσsupp
  -- the Wirtinger combination of the CT witnesses is `2·σ`, pointwise
  have hcombS : ∀ z : ℂ,
      (beurling (seedBasis a ρ k) z + seedBasis a ρ k z)
        + Complex.I * (Complex.I * (beurling (seedBasis a ρ k) z - seedBasis a ρ k z))
        = 2 * seedBasis a ρ k z := by
    intro z
    linear_combination (beurling (seedBasis a ρ k) z - seedBasis a ρ k z) * Complex.I_mul_I
  -- `L²` and local integrability of the witnesses
  have hσ2 : MemLp (seedBasis a ρ k) 2 volume := hσmem 2
  have hSx_mem : MemLp (fun z => beurling (seedBasis a ρ k) z + seedBasis a ρ k z)
      2 volume := (memLp_beurling hσ2).add hσ2
  have hSy_mem : MemLp
      (fun z => Complex.I * (beurling (seedBasis a ρ k) z - seedBasis a ρ k z))
      2 volume := ((memLp_beurling hσ2).sub hσ2).const_mul Complex.I
  have hSx_LI : LocallyIntegrable
      (fun z => beurling (seedBasis a ρ k) z + seedBasis a ρ k z) volume :=
    hSx_mem.locallyIntegrable (by norm_num)
  have hSy_LI : LocallyIntegrable
      (fun z => Complex.I * (beurling (seedBasis a ρ k) z - seedBasis a ρ k z)) volume :=
    hSy_mem.locallyIntegrable (by norm_num)
  -- ===== the smooth inside model `U(z) = conj((z-a)^(k+1))` =====
  have hU_cd : ContDiff ℝ 1 fun z : ℂ => starRingEnd ℂ ((z - a) ^ (k + 1)) := by
    have hq : ContDiff ℝ 1 fun w : ℂ => (w - a) ^ (k + 1) :=
      (contDiff_id.sub contDiff_const).pow (k + 1)
    have hc : ContDiff ℝ 1 fun z : ℂ => starRingEnd ℂ z := by
      have := ContinuousLinearMap.contDiff (n := 1)
        (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ)
      simpa using! this
    exact hc.comp hq
  have hU_cont : Continuous fun z : ℂ => starRingEnd ℂ ((z - a) ^ (k + 1)) :=
    hU_cd.continuous
  have hUx_cont : Continuous fun z : ℂ =>
      (fderiv ℝ (fun w : ℂ => starRingEnd ℂ ((w - a) ^ (k + 1))) z) 1 :=
    (hU_cd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hUy_cont : Continuous fun z : ℂ =>
      (fderiv ℝ (fun w : ℂ => starRingEnd ℂ ((w - a) ^ (k + 1))) z) Complex.I :=
    (hU_cd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hUx : HasWeakDirDeriv 1
      (fun z : ℂ => (fderiv ℝ (fun w : ℂ => starRingEnd ℂ ((w - a) ^ (k + 1))) z) 1)
      (fun z : ℂ => starRingEnd ℂ ((z - a) ^ (k + 1))) Set.univ :=
    HasWeakDirDeriv.of_contDiffOn isOpen_univ hU_cd.contDiffOn
  have hUy : HasWeakDirDeriv Complex.I
      (fun z : ℂ => (fderiv ℝ (fun w : ℂ => starRingEnd ℂ ((w - a) ^ (k + 1))) z) Complex.I)
      (fun z : ℂ => starRingEnd ℂ ((z - a) ^ (k + 1))) Set.univ :=
    HasWeakDirDeriv.of_contDiffOn isOpen_univ hU_cd.contDiffOn
  -- its Wirtinger combination is `2·(k+1)·conj(z-a)^k`, pointwise
  have hcombU : ∀ z : ℂ,
      (fderiv ℝ (fun w : ℂ => starRingEnd ℂ ((w - a) ^ (k + 1))) z) 1
        + Complex.I * (fderiv ℝ (fun w : ℂ => starRingEnd ℂ ((w - a) ^ (k + 1))) z) Complex.I
        = 2 * (((k : ℂ) + 1) * (starRingEnd ℂ (z - a)) ^ k) := by
    intro z
    have h1 : (fderiv ℝ (fun w : ℂ => starRingEnd ℂ ((w - a) ^ (k + 1))) z) 1
        + Complex.I * (fderiv ℝ (fun w : ℂ => starRingEnd ℂ ((w - a) ^ (k + 1))) z) Complex.I
        = 2 * dzbar (fun w : ℂ => starRingEnd ℂ ((w - a) ^ (k + 1))) z := by
      rw [dzbar]; ring
    have h2 : dzbar (fun w : ℂ => starRingEnd ℂ ((w - a) ^ (k + 1))) z
        = ((k : ℂ) + 1) * (starRingEnd ℂ (z - a)) ^ k := by
      rw [dzbar_conj]
      have hq : HasDerivAt (fun w : ℂ => (w - a) ^ (k + 1))
          ((k + 1 : ℕ) * (z - a) ^ k * 1) z := by
        have := ((hasDerivAt_id z).sub_const a).pow (k + 1)
        simpa using! this
      have hdz : dz (fun w : ℂ => (w - a) ^ (k + 1)) z
          = ((k + 1 : ℕ) : ℂ) * (z - a) ^ k := by
        rw [dz_eq_deriv_of_differentiableAt hq.differentiableAt, hq.deriv]
        ring
      rw [hdz, map_mul, map_pow, map_natCast]
      push_cast
      ring
    rw [h1, h2]
  -- ===== local integrability bookkeeping =====
  have hU_LI : LocallyIntegrable (fun z : ℂ => starRingEnd ℂ ((z - a) ^ (k + 1))) volume :=
    hU_cont.locallyIntegrable
  have hP_LI : LocallyIntegrable (cauchyTransform (seedBasis a ρ k)) volume :=
    hP_cont.locallyIntegrable
  -- ===== the difference is holomorphic off the circle, via the local Weyl lemma =====
  -- on the open ball
  have hD_ball : DifferentiableOn ℂ
      (fun z : ℂ => starRingEnd ℂ ((z - a) ^ (k + 1))
        - cauchyTransform (seedBasis a ρ k) z) (Metric.ball a ρ) := by
    refine weyl_lemma_on isOpen_ball ((hU_cont.sub hP_cont).continuousOn)
      (gx := fun z => (fderiv ℝ (fun w : ℂ => starRingEnd ℂ ((w - a) ^ (k + 1))) z) 1
        - (beurling (seedBasis a ρ k) z + seedBasis a ρ k z))
      (gy := fun z => (fderiv ℝ (fun w : ℂ => starRingEnd ℂ ((w - a) ^ (k + 1))) z) Complex.I
        - Complex.I * (beurling (seedBasis a ρ k) z - seedBasis a ρ k z))
      ⟨(hUx.sub hPx (hU_LI.locallyIntegrableOn _) (hP_LI.locallyIntegrableOn _)
          (hUx_cont.locallyIntegrable.locallyIntegrableOn _)
          (hSx_LI.locallyIntegrableOn _)).mono (Set.subset_univ _),
        (hUy.sub hPy (hU_LI.locallyIntegrableOn _) (hP_LI.locallyIntegrableOn _)
          (hUy_cont.locallyIntegrable.locallyIntegrableOn _)
          (hSy_LI.locallyIntegrableOn _)).mono (Set.subset_univ _)⟩
      ((hUx_cont.locallyIntegrable.locallyIntegrableOn _).sub
        (hSx_LI.locallyIntegrableOn _))
      ((hUy_cont.locallyIntegrable.locallyIntegrableOn _).sub
        (hSy_LI.locallyIntegrableOn _))
      ?_
    refine Filter.Eventually.of_forall fun z hz => ?_
    have hσz : seedBasis a ρ k z = ((k : ℂ) + 1) * (starRingEnd ℂ (z - a)) ^ k := by
      simp only [seedBasis]
      rw [if_pos hz]
    have h10 := hcombU z
    have h9 := hcombS z
    linear_combination h10 - h9 - 2 * hσz
  -- on the complement of the closed ball
  have hVout_open : IsOpen (Metric.closedBall a ρ)ᶜ := isClosed_closedBall.isOpen_compl
  have hP_Vout : DifferentiableOn ℂ (cauchyTransform (seedBasis a ρ k))
      (Metric.closedBall a ρ)ᶜ := by
    refine weyl_lemma_on hVout_open hP_cont.continuousOn
      ⟨hPx.mono (Set.subset_univ _), hPy.mono (Set.subset_univ _)⟩
      (hSx_LI.locallyIntegrableOn _) (hSy_LI.locallyIntegrableOn _) ?_
    refine Filter.Eventually.of_forall fun z hz => ?_
    have hz_ball : z ∉ Metric.ball a ρ := fun h => hz (Metric.ball_subset_closedBall h)
    have hσz : seedBasis a ρ k z = 0 := by
      simp only [seedBasis]
      rw [if_neg hz_ball]
    have h9 := hcombS z
    linear_combination h9 + 2 * hσz
  have hV_diff : DifferentiableOn ℂ
      (fun z : ℂ => ((ρ ^ (2 * (k + 1)) : ℝ) : ℂ) * (z - a) ^ (-(k + 1 : ℤ)))
      (Metric.closedBall a ρ)ᶜ := by
    intro z hz
    have hz_ne : z - a ≠ 0 := by
      have ha : a ∈ Metric.closedBall a ρ := Metric.mem_closedBall_self hρ.le
      intro h
      exact hz (by rwa [sub_eq_zero.mp h])
    exact (((differentiableAt_id.sub (differentiableAt_const a)).zpow
      (Or.inl hz_ne)).const_mul _).differentiableWithinAt
  -- assemble: `d = u - P` is holomorphic off the circle
  have hd_ball : DifferentiableOn ℂ
      (fun z => seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z)
      (Metric.ball a ρ) := by
    refine hD_ball.congr fun z hz => ?_
    have hu : seedSolution a ρ k z = starRingEnd ℂ ((z - a) ^ (k + 1)) := by
      simp only [seedSolution]
      rw [if_pos hz]
      exact (map_pow (starRingEnd ℂ) (z - a) (k + 1)).symm
    rw [hu]
  have hd_Vout : DifferentiableOn ℂ
      (fun z => seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z)
      (Metric.closedBall a ρ)ᶜ := by
    have h1 : DifferentiableOn ℂ
        (fun z : ℂ => ((ρ ^ (2 * (k + 1)) : ℝ) : ℂ) * (z - a) ^ (-(k + 1 : ℤ))
          - cauchyTransform (seedBasis a ρ k) z) (Metric.closedBall a ρ)ᶜ := by
      intro z hz
      exact ((hV_diff z hz).sub (hP_Vout z hz))
    refine h1.congr fun z hz => ?_
    have hz_ball : z ∉ Metric.ball a ρ := fun h => hz (Metric.ball_subset_closedBall h)
    have hu : seedSolution a ρ k z
        = ((ρ ^ (2 * (k + 1)) : ℝ) : ℂ) * (z - a) ^ (-(k + 1 : ℤ)) := by
      simp only [seedSolution]
      rw [if_neg hz_ball]
    rw [hu]
  have hd_cont : Continuous
      (fun z => seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z) :=
    (seedSolution_continuous a hρ k).sub hP_cont
  -- differentiability at every point off the circle
  have hd_offsphere : ∀ z : ℂ, z ∉ Metric.sphere a ρ → DifferentiableAt ℂ
      (fun z => seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z) z := by
    intro z hz
    rcases lt_trichotomy (dist z a) ρ with h | h | h
    · have hzb : z ∈ Metric.ball a ρ := Metric.mem_ball.mpr h
      exact (hd_ball z hzb).differentiableAt (isOpen_ball.mem_nhds hzb)
    · exact absurd (Metric.mem_sphere.mpr h) hz
    · have hzb : z ∈ (Metric.closedBall a ρ)ᶜ := by
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le]
        exact h
      exact (hd_Vout z hzb).differentiableAt (hVout_open.mem_nhds hzb)
  -- ===== removability across the circle =====
  -- a continuous function holomorphic off the real axis is entire (Morera on
  -- rectangles, split at the axis)
  have line_removable : ∀ G : ℂ → ℂ, Continuous G →
      (∀ w : ℂ, w.im ≠ 0 → DifferentiableAt ℂ G w) → Differentiable ℂ G := by
    intro G hGc hGd
    rw [← differentiableOn_univ,
      ← Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ]
    refine ⟨?_, hGc.continuousOn⟩
    intro z' w' _hsub
    rw [eq_neg_iff_add_eq_zero, Complex.wedgeIntegral_add_wedgeIntegral_eq]
    rcases le_or_gt 0 (min z'.im w'.im) with h_min_nn | h_min_neg
    · refine Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
        G z' w' hGc.continuousOn ?_
      intro p hp
      have hp_im_pos : 0 < p.im := lt_of_le_of_lt h_min_nn hp.2.1
      exact (hGd p hp_im_pos.ne').differentiableWithinAt
    · rcases le_or_gt (max z'.im w'.im) 0 with h_max_np | h_max_pos
      · refine Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
          G z' w' hGc.continuousOn ?_
        intro p hp
        have hp_im_neg : p.im < 0 := lt_of_lt_of_le hp.2.2 h_max_np
        exact (hGd p hp_im_neg.ne).differentiableWithinAt
      · -- the rectangle crosses the real axis: split it there
        set z_up : ℂ := ⟨z'.re, 0⟩ with hz_up_def
        set w_up : ℂ := w' with hw_up_def
        set z_low : ℂ := z' with hz_low_def
        set w_low : ℂ := ⟨w'.re, 0⟩ with hw_low_def
        have h_zero_not_in_w_Ioo : (0 : ℝ) ∉ Set.Ioo (min 0 w'.im) (max 0 w'.im) := by
          intro h
          rcases le_total (0 : ℝ) w'.im with hw | hw
          · have : min (0 : ℝ) w'.im = 0 := min_eq_left hw
            rw [this] at h; exact lt_irrefl 0 h.1
          · have : max (0 : ℝ) w'.im = 0 := max_eq_left hw
            rw [this] at h; exact lt_irrefl 0 h.2
        have h_zero_not_in_z_Ioo : (0 : ℝ) ∉ Set.Ioo (min z'.im 0) (max z'.im 0) := by
          intro h
          rcases le_total z'.im (0 : ℝ) with hz | hz
          · have : max z'.im (0 : ℝ) = 0 := max_eq_right hz
            rw [this] at h; exact lt_irrefl 0 h.2
          · have : min z'.im (0 : ℝ) = 0 := min_eq_right hz
            rw [this] at h; exact lt_irrefl 0 h.1
        have h_diff_up : DifferentiableOn ℂ G
            (Set.Ioo (min z_up.re w_up.re) (max z_up.re w_up.re) ×ℂ
              Set.Ioo (min z_up.im w_up.im) (max z_up.im w_up.im)) := by
          intro p hp
          have hp_im_in : p.im ∈ Set.Ioo (min (0 : ℝ) w'.im) (max (0 : ℝ) w'.im) := hp.2
          have hp_im_ne : p.im ≠ 0 := by
            intro h
            apply h_zero_not_in_w_Ioo
            rcases hp_im_in with ⟨h1, h2⟩
            exact ⟨by linarith, by linarith⟩
          exact (hGd p hp_im_ne).differentiableWithinAt
        have h_diff_low : DifferentiableOn ℂ G
            (Set.Ioo (min z_low.re w_low.re) (max z_low.re w_low.re) ×ℂ
              Set.Ioo (min z_low.im w_low.im) (max z_low.im w_low.im)) := by
          intro p hp
          have hp_im_in : p.im ∈ Set.Ioo (min z'.im (0 : ℝ)) (max z'.im (0 : ℝ)) := hp.2
          have hp_im_ne : p.im ≠ 0 := by
            intro h
            apply h_zero_not_in_z_Ioo
            rcases hp_im_in with ⟨h1, h2⟩
            exact ⟨by linarith, by linarith⟩
          exact (hGd p hp_im_ne).differentiableWithinAt
        have h_up_eq := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
          G z_up w_up hGc.continuousOn h_diff_up
        have h_low_eq := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
          G z_low w_low hGc.continuousOn h_diff_low
        have h_int_w : IntervalIntegrable
            (fun y => G (↑w'.re + ↑y * Complex.I)) MeasureTheory.volume
            z'.im w'.im :=
          (hGc.comp (continuous_const.add
            (Complex.continuous_ofReal.mul continuous_const))).intervalIntegrable _ _
        have h_int_z : IntervalIntegrable
            (fun y => G (↑z'.re + ↑y * Complex.I)) MeasureTheory.volume
            z'.im w'.im :=
          (hGc.comp (continuous_const.add
            (Complex.continuous_ofReal.mul continuous_const))).intervalIntegrable _ _
        have h_zero_in_im : (0 : ℝ) ∈ Set.uIcc z'.im w'.im := by
          rw [Set.uIcc, Set.mem_Icc]
          exact ⟨h_min_neg.le, h_max_pos.le⟩
        have h_int_w_z_0 := h_int_w.mono_set
          (Set.uIcc_subset_uIcc Set.left_mem_uIcc h_zero_in_im)
        have h_int_w_0_w := h_int_w.mono_set
          (Set.uIcc_subset_uIcc h_zero_in_im Set.right_mem_uIcc)
        have h_int_z_z_0 := h_int_z.mono_set
          (Set.uIcc_subset_uIcc Set.left_mem_uIcc h_zero_in_im)
        have h_int_z_0_w := h_int_z.mono_set
          (Set.uIcc_subset_uIcc h_zero_in_im Set.right_mem_uIcc)
        have h_split_w :
            (∫ y in z'.im..(0 : ℝ), G (↑w'.re + ↑y * Complex.I)) +
            (∫ y in (0 : ℝ)..w'.im, G (↑w'.re + ↑y * Complex.I)) =
            (∫ y in z'.im..w'.im, G (↑w'.re + ↑y * Complex.I)) :=
          intervalIntegral.integral_add_adjacent_intervals h_int_w_z_0 h_int_w_0_w
        have h_split_z :
            (∫ y in z'.im..(0 : ℝ), G (↑z'.re + ↑y * Complex.I)) +
            (∫ y in (0 : ℝ)..w'.im, G (↑z'.re + ↑y * Complex.I)) =
            (∫ y in z'.im..w'.im, G (↑z'.re + ↑y * Complex.I)) :=
          intervalIntegral.integral_add_adjacent_intervals h_int_z_z_0 h_int_z_0_w
        have h_up_re_eq : z_up.re = z'.re := rfl
        have h_up_im_eq : z_up.im = (0 : ℝ) := rfl
        have h_w_up_re_eq : w_up.re = w'.re := rfl
        have h_w_up_im_eq : w_up.im = w'.im := rfl
        have h_low_re_eq : z_low.re = z'.re := rfl
        have h_low_im_eq : z_low.im = z'.im := rfl
        have h_w_low_re_eq : w_low.re = w'.re := rfl
        have h_w_low_im_eq : w_low.im = (0 : ℝ) := rfl
        rw [h_up_re_eq, h_up_im_eq, h_w_up_re_eq, h_w_up_im_eq] at h_up_eq
        rw [h_low_re_eq, h_low_im_eq, h_w_low_re_eq, h_w_low_im_eq] at h_low_eq
        have h_sum_eq :
            ((∫ x in z'.re..w'.re, G (↑x + ↑(0 : ℝ) * Complex.I)) -
                (∫ x in z'.re..w'.re, G (↑x + ↑w'.im * Complex.I)) +
                Complex.I • (∫ y in (0 : ℝ)..w'.im, G (↑w'.re + ↑y * Complex.I)) -
                Complex.I • (∫ y in (0 : ℝ)..w'.im, G (↑z'.re + ↑y * Complex.I))) +
              ((∫ x in z'.re..w'.re, G (↑x + ↑z'.im * Complex.I)) -
                (∫ x in z'.re..w'.re, G (↑x + ↑(0 : ℝ) * Complex.I)) +
                Complex.I • (∫ y in z'.im..(0 : ℝ), G (↑w'.re + ↑y * Complex.I)) -
                Complex.I • (∫ y in z'.im..(0 : ℝ), G (↑z'.re + ↑y * Complex.I)))
                = 0 := by
          rw [h_up_eq, h_low_eq]; ring
        simp only [smul_eq_mul] at h_sum_eq ⊢
        linear_combination h_sum_eq - Complex.I * h_split_w + Complex.I * h_split_z
  -- transfer to the circle through the exponential chart `w ↦ a + ρ·e^{iw}`
  have hg_cont : Continuous fun w : ℂ =>
      (fun z => seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z)
        (a + ↑ρ * Complex.exp (Complex.I * w)) :=
    hd_cont.comp (continuous_const.add (continuous_const.mul
      (Complex.continuous_exp.comp (continuous_const.mul continuous_id))))
  have hg_diff : ∀ w : ℂ, w.im ≠ 0 → DifferentiableAt ℂ
      (fun w : ℂ => (fun z => seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z)
        (a + ↑ρ * Complex.exp (Complex.I * w))) w := by
    intro w hw
    have he_d : DifferentiableAt ℂ (fun w : ℂ => a + ↑ρ * Complex.exp (Complex.I * w)) w :=
      (differentiableAt_const a).add
        (((differentiableAt_id.const_mul Complex.I).cexp).const_mul (↑ρ : ℂ))
    have himg : (a + ↑ρ * Complex.exp (Complex.I * w)) ∉ Metric.sphere a ρ := by
      intro h
      have h1 : dist (a + ↑ρ * Complex.exp (Complex.I * w)) a = ρ := Metric.mem_sphere.mp h
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hρ.le, Complex.norm_exp] at h1
      have h2 : (Complex.I * w).re = -w.im := by
        simp [Complex.mul_re]
      rw [h2] at h1
      have h3 : Real.exp (-w.im) = 1 := by
        have := mul_left_cancel₀ hρ.ne' (h1.trans (mul_one ρ).symm)
        exact this
      have h4 : -w.im = 0 := (Real.exp_eq_one_iff _).mp h3
      exact hw (neg_eq_zero.mp h4)
    exact (hd_offsphere _ himg).comp w he_d
  have hg_ent := line_removable _ hg_cont hg_diff
  -- differentiability at the circle points via a local logarithmic section
  have hd_sphere : ∀ z₀ ∈ Metric.sphere a ρ, DifferentiableAt ℂ
      (fun z => seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z) z₀ := by
    intro z₀ hz₀
    have hz₀a : z₀ - a ≠ 0 := by
      have h1 : ‖z₀ - a‖ = ρ := mem_sphere_iff_norm.mp hz₀
      intro h
      rw [h, norm_zero] at h1
      exact hρ.ne h1
    have hρ0 : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
    have hh_diff : DifferentiableAt ℂ (fun z : ℂ =>
        (-Complex.I * Complex.log ((z₀ - a) / ↑ρ))
          + (-Complex.I) * Complex.log ((z - a) / (z₀ - a))) z₀ := by
      refine (differentiableAt_const _).add (DifferentiableAt.const_mul ?_ _)
      refine DifferentiableAt.clog ((differentiableAt_id.sub_const a).div_const (z₀ - a)) ?_
      rw [div_self hz₀a]
      exact Complex.one_mem_slitPlane
    have hW : {z : ℂ | (z - a) / (z₀ - a) ∈ Complex.slitPlane} ∈ 𝓝 z₀ := by
      have hopen : IsOpen {z : ℂ | (z - a) / (z₀ - a) ∈ Complex.slitPlane} :=
        Complex.isOpen_slitPlane.preimage
          ((continuous_id.sub continuous_const).div_const (z₀ - a))
      refine hopen.mem_nhds ?_
      change (z₀ - a) / (z₀ - a) ∈ Complex.slitPlane
      rw [div_self hz₀a]
      exact Complex.one_mem_slitPlane
    have heq : (fun z => seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z)
        =ᶠ[𝓝 z₀]
        ((fun w : ℂ => (fun z => seedSolution a ρ k z
            - cauchyTransform (seedBasis a ρ k) z) (a + ↑ρ * Complex.exp (Complex.I * w)))
          ∘ (fun z : ℂ => (-Complex.I * Complex.log ((z₀ - a) / ↑ρ))
              + (-Complex.I) * Complex.log ((z - a) / (z₀ - a)))) := by
      filter_upwards [hW] with z hzW
      have hne : (z - a) / (z₀ - a) ≠ 0 := Complex.slitPlane_ne_zero hzW
      have hIh : Complex.I * ((-Complex.I * Complex.log ((z₀ - a) / ↑ρ)) +
          (-Complex.I) * Complex.log ((z - a) / (z₀ - a)))
          = Complex.log ((z₀ - a) / ↑ρ) + Complex.log ((z - a) / (z₀ - a)) := by
        linear_combination (-(Complex.log ((z₀ - a) / ↑ρ))
          - Complex.log ((z - a) / (z₀ - a))) * Complex.I_mul_I
      have hchart : a + ↑ρ * Complex.exp (Complex.I *
          ((-Complex.I * Complex.log ((z₀ - a) / ↑ρ)) +
            (-Complex.I) * Complex.log ((z - a) / (z₀ - a)))) = z := by
        rw [hIh, Complex.exp_add, Complex.exp_log (div_ne_zero hz₀a hρ0),
          Complex.exp_log hne]
        field_simp
        ring
      change seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z
          = seedSolution a ρ k (a + ↑ρ * Complex.exp (Complex.I * _))
            - cauchyTransform (seedBasis a ρ k) (a + ↑ρ * Complex.exp (Complex.I * _))
      rw [hchart]
    exact ((hg_ent _).comp z₀ hh_diff).congr_of_eventuallyEq heq
  -- the difference is entire
  have hd_ent : Differentiable ℂ
      (fun z => seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z) := by
    intro z
    by_cases hz : z ∈ Metric.sphere a ρ
    · exact hd_sphere z hz
    · exact hd_offsphere z hz
  -- ===== decay of the explicit solution at infinity =====
  have hu0 : Tendsto (seedSolution a ρ k) (Filter.cocompact ℂ) (𝓝 0) := by
    have hmem : (Metric.closedBall a (max ρ 0))ᶜ ∈ Filter.cocompact ℂ :=
      Filter.mem_cocompact.mpr ⟨Metric.closedBall a (max ρ 0),
        isCompact_closedBall a (max ρ 0), subset_rfl⟩
    have hnorm_atTop : Tendsto (fun z : ℂ => ‖z - a‖) (Filter.cocompact ℂ) atTop := by
      refine tendsto_atTop_mono' _ ?_
        (tendsto_atTop_add_const_right _ (-‖a‖) tendsto_norm_cocompact_atTop)
      filter_upwards with z
      have h1 : ‖z‖ - ‖a‖ ≤ ‖z - a‖ := norm_sub_norm_le z a
      linarith
    have hpow : Tendsto (fun z : ℂ => ‖z - a‖ ^ (k + 1)) (Filter.cocompact ℂ) atTop :=
      (tendsto_pow_atTop (Nat.succ_ne_zero k)).comp hnorm_atTop
    have hmaj : Tendsto (fun z : ℂ =>
        ‖((ρ ^ (2 * (k + 1)) : ℝ) : ℂ)‖ / ‖z - a‖ ^ (k + 1))
        (Filter.cocompact ℂ) (𝓝 0) := tendsto_const_nhds.div_atTop hpow
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [hmem] with z hz
    have hz' : max ρ 0 < dist z a := by
      simpa [Metric.mem_closedBall, not_le] using hz
    have hz_ball : z ∉ Metric.ball a ρ := by
      intro h
      have h1 : dist z a < ρ := Metric.mem_ball.mp h
      have h2 : ρ ≤ max ρ 0 := le_max_left _ _
      linarith
    have hz_ne : z - a ≠ 0 := by
      have h0 : (0 : ℝ) < dist z a := lt_of_le_of_lt (le_max_right ρ 0) hz'
      rw [dist_eq_norm] at h0
      intro h
      rw [h, norm_zero] at h0
      exact lt_irrefl 0 h0
    have hval : seedSolution a ρ k z
        = ((ρ ^ (2 * (k + 1)) : ℝ) : ℂ) * (z - a) ^ (-(k + 1 : ℤ)) := by
      simp only [seedSolution]
      rw [if_neg hz_ball]
    have hexp : (-(k + 1 : ℤ)) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hval, norm_mul, hexp, zpow_neg, zpow_natCast, norm_inv, norm_pow,
      div_eq_mul_inv]
  have hd0 : Tendsto (fun z => seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z)
      (Filter.cocompact ℂ) (𝓝 0) := by
    have h1 := hu0.sub hP0
    simpa using h1
  -- ===== Liouville: the entire decaying difference vanishes =====
  have hd_zero : ∀ z : ℂ,
      seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z = 0 := by
    have hbdd : Bornology.IsBounded (Set.range
        (fun z => seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z)) := by
      have h1 : ∀ᶠ z in Filter.cocompact ℂ,
          seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z
            ∈ Metric.closedBall (0 : ℂ) 1 :=
        hd0 (Metric.closedBall_mem_nhds 0 one_pos)
      rw [Filter.eventually_iff, Filter.mem_cocompact] at h1
      obtain ⟨K, hKc, hKsub⟩ := h1
      have h2 : Set.range (fun z => seedSolution a ρ k z
          - cauchyTransform (seedBasis a ρ k) z)
          ⊆ ((fun z => seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z) '' K)
            ∪ Metric.closedBall (0 : ℂ) 1 := by
        rintro _ ⟨z, rfl⟩
        by_cases hz : z ∈ K
        · exact Or.inl ⟨z, hz, rfl⟩
        · exact Or.inr (hKsub hz)
      exact (((hKc.image hd_cont).isBounded).union Metric.isBounded_closedBall).subset h2
    intro z
    have hconst : ∀ w : ℂ, seedSolution a ρ k w - cauchyTransform (seedBasis a ρ k) w
        = seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z := fun w =>
      hd_ent.apply_eq_apply_of_bounded hbdd w z
    have hc' : Tendsto (fun w => seedSolution a ρ k w - cauchyTransform (seedBasis a ρ k) w)
        (Filter.cocompact ℂ)
        (𝓝 (seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z)) := by
      have hfe : (fun w => seedSolution a ρ k w - cauchyTransform (seedBasis a ρ k) w)
          = fun _ => seedSolution a ρ k z - cauchyTransform (seedBasis a ρ k) z :=
        funext hconst
      rw [hfe]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hc' hd0
  -- ===== conclusion: `u = P σ`, so the CT weak calculus transfers =====
  have hfin : seedSolution a ρ k = cauchyTransform (seedBasis a ρ k) :=
    funext fun z => sub_eq_zero.mp (hd_zero z)
  rw [hfin]
  exact ⟨fun z => beurling (seedBasis a ρ k) z + seedBasis a ρ k z,
    fun z => Complex.I * (beurling (seedBasis a ρ k) z - seedBasis a ρ k z),
    ⟨hPx, hPy⟩,
    fun K _ _ => hSx_mem.restrict K,
    fun K _ _ => hSy_mem.restrict K,
    Filter.Eventually.of_forall fun z _ => hcombS z⟩

-- NOTE: the hypothesis `(hρ : 0 < ρ)` is necessary — the unrestricted
-- statement is false for `ρ < 0` (then `closedBall a ρ = ∅`, the complement is
-- `univ ∋ a`, and the function is `ρ^{2(k+1)}·(z-a)^{-(k+1)}` with a
-- nonvanishing coefficient, which is not differentiable at `a`).

/-- The explicit solution is holomorphic outside the closed disk. -/
theorem differentiableOn_seedSolution (a : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    DifferentiableOn ℂ (seedSolution a ρ k) (Metric.closedBall a ρ)ᶜ := by
  have hVd : DifferentiableOn ℂ
      (fun z : ℂ => ((ρ ^ (2 * (k + 1)) : ℝ) : ℂ) * (z - a) ^ (-(k + 1 : ℤ)))
      (Metric.closedBall a ρ)ᶜ := by
    intro z hz
    have hz_ne : z - a ≠ 0 := by
      have ha : a ∈ Metric.closedBall a ρ := Metric.mem_closedBall_self hρ.le
      intro h
      exact hz (by rwa [sub_eq_zero.mp h])
    exact (((differentiableAt_id.sub (differentiableAt_const a)).zpow
      (Or.inl hz_ne)).const_mul _).differentiableWithinAt
  refine hVd.congr fun z hz => ?_
  have hz_ball : z ∉ Metric.ball a ρ := fun h => hz (Metric.ball_subset_closedBall h)
  simp only [seedSolution]
  rw [if_neg hz_ball]

/-- The explicit solution vanishes at infinity. -/
theorem seedSolution_tendsto_cocompact (a : ℂ) (ρ : ℝ) (k : ℕ) :
    Tendsto (seedSolution a ρ k) (cocompact ℂ) (nhds 0) := by
  have hmem : (Metric.closedBall a (max ρ 0))ᶜ ∈ Filter.cocompact ℂ :=
    Filter.mem_cocompact.mpr ⟨Metric.closedBall a (max ρ 0),
      isCompact_closedBall a (max ρ 0), subset_rfl⟩
  have hnorm_atTop : Tendsto (fun z : ℂ => ‖z - a‖) (Filter.cocompact ℂ) atTop := by
    refine tendsto_atTop_mono' _ ?_
      (tendsto_atTop_add_const_right _ (-‖a‖) tendsto_norm_cocompact_atTop)
    filter_upwards with z
    have h1 : ‖z‖ - ‖a‖ ≤ ‖z - a‖ := norm_sub_norm_le z a
    linarith
  have hpow : Tendsto (fun z : ℂ => ‖z - a‖ ^ (k + 1)) (Filter.cocompact ℂ) atTop :=
    (tendsto_pow_atTop (Nat.succ_ne_zero k)).comp hnorm_atTop
  have hmaj : Tendsto (fun z : ℂ =>
      ‖((ρ ^ (2 * (k + 1)) : ℝ) : ℂ)‖ / ‖z - a‖ ^ (k + 1))
      (Filter.cocompact ℂ) (𝓝 0) := tendsto_const_nhds.div_atTop hpow
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [hmem] with z hz
  have hz' : max ρ 0 < dist z a := by
    simpa [Metric.mem_closedBall, not_le] using hz
  have hz_ball : z ∉ Metric.ball a ρ := by
    intro h
    have h1 : dist z a < ρ := Metric.mem_ball.mp h
    have h2 : ρ ≤ max ρ 0 := le_max_left _ _
    linarith
  have hval : seedSolution a ρ k z
      = ((ρ ^ (2 * (k + 1)) : ℝ) : ℂ) * (z - a) ^ (-(k + 1 : ℤ)) := by
    simp only [seedSolution]
    rw [if_neg hz_ball]
  have hexp : (-(k + 1 : ℤ)) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hval, norm_mul, hexp, zpow_neg, zpow_natCast, norm_inv, norm_pow,
    div_eq_mul_inv]

/-! ## The maximum-modulus kill -/

/-- **Maximum principle with vanishing boundary and infinity data.** A
function holomorphic on an open set `V ⊆ ℂ`, tending to `0` at every
frontier point of `V` (from within `V`) and tending to `0` at infinity
within `V` (vacuous for bounded `V`), vanishes identically on `V`. Proof
route: for `ε > 0` the set `{z ∈ V | ε ≤ ‖F z‖}` is compact (closed in `V`
by the frontier data, bounded by the infinity data), so `‖F‖` attains a
maximum `≥ ε` at an interior point of `V`; Mathlib's maximum-modulus
principle (`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`, applied on a
ball around the maximum, or the frontier-norm bound
`Complex.norm_le_of_forall_mem_frontier_norm_le` on the compact piece)
propagates the maximum to the frontier, contradicting the boundary data. -/
theorem eqOn_zero_of_forall_frontier_tendsto_zero {V : Set ℂ} (hV : IsOpen V)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F V)
    (hfront : ∀ p ∈ frontier V, Tendsto F (nhdsWithin p V) (nhds 0))
    (hinfty : Tendsto F (cocompact ℂ ⊓ Filter.principal V) (nhds 0)) :
    ∀ z ∈ V, F z = 0 := by
  intro z₀ hz₀
  by_contra hne
  have hnorm₀ : 0 < ‖F z₀‖ := norm_pos_iff.mpr hne
  set ε : ℝ := ‖F z₀‖ / 2 with hε_def
  have hεpos : 0 < ε := by rw [hε_def]; linarith
  -- the "high" set
  set K : Set ℂ := {z | z ∈ V ∧ ε ≤ ‖F z‖} with hK_def
  have hKV : K ⊆ V := fun z hz => hz.1
  have hz₀K : z₀ ∈ K := ⟨hz₀, by rw [hε_def]; linarith⟩
  -- boundedness of `K` from the cocompact decay
  have hsmall : ∀ᶠ z in cocompact ℂ ⊓ Filter.principal V, ‖F z‖ < ε := by
    have h := hinfty.norm
    rw [norm_zero] at h
    exact h.eventually_lt_const hεpos
  rw [Filter.eventually_inf_principal] at hsmall
  have hsmall' : {z : ℂ | z ∈ V → ‖F z‖ < ε} ∈ cocompact ℂ := hsmall
  obtain ⟨C, hCcomp, hCsub⟩ := Filter.mem_cocompact.mp hsmall'
  have hKC : K ⊆ C := by
    intro z hz
    by_contra hzC
    exact absurd (hCsub hzC hz.1) (not_lt.mpr hz.2)
  -- `K` is closed in `ℂ` (limit points on the frontier would violate the decay)
  have hKcl : IsClosed K := by
    refine isClosed_of_closure_subset fun z hz => ?_
    have hzclV : z ∈ closure V := closure_mono hKV hz
    have hzne : (nhdsWithin z K).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz
    have hεle : ∀ᶠ w in nhdsWithin z K, ε ≤ ‖F w‖ := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact hw.2
    by_cases hzV : z ∈ V
    · have hc : ContinuousAt F z := hF.continuousOn.continuousAt (hV.mem_nhds hzV)
      have ht : Tendsto (fun w => ‖F w‖) (nhdsWithin z K) (nhds ‖F z‖) :=
        Filter.Tendsto.norm (Filter.Tendsto.mono_left hc nhdsWithin_le_nhds)
      exact ⟨hzV, ge_of_tendsto ht hεle⟩
    · exfalso
      have hzf : z ∈ frontier V := by
        rw [hV.frontier_eq]; exact ⟨hzclV, hzV⟩
      have ht : Tendsto (fun w => ‖F w‖) (nhdsWithin z K) (nhds ‖(0 : ℂ)‖) :=
        ((hfront z hzf).mono_left (nhdsWithin_mono z hKV)).norm
      have hle : ε ≤ ‖(0 : ℂ)‖ := ge_of_tendsto ht hεle
      rw [norm_zero] at hle
      linarith
  have hKcomp : IsCompact K := hCcomp.of_isClosed_subset hKcl hKC
  -- maximum of `‖F‖` over `K`
  obtain ⟨z₁, hz₁K, hz₁max⟩ :=
    hKcomp.exists_isMaxOn ⟨z₀, hz₀K⟩ ((hF.continuousOn.mono hKV).norm)
  have hz₁V : z₁ ∈ V := hz₁K.1
  have hεz₁ : ε ≤ ‖F z₁‖ := hz₁K.2
  -- `z₁` is a global maximum of `‖F‖` over `V`
  have hmaxV : IsMaxOn (norm ∘ F) V z₁ := by
    rw [isMaxOn_iff]
    intro w hw
    change ‖F w‖ ≤ ‖F z₁‖
    by_cases hwK : w ∈ K
    · exact isMaxOn_iff.mp hz₁max w hwK
    · have hlt : ‖F w‖ < ε := by
        by_contra h
        exact hwK ⟨hw, not_lt.mp h⟩
      exact hlt.le.trans hεz₁
  -- the connected component of `z₁` in `V`
  set W : Set ℂ := connectedComponentIn V z₁ with hW_def
  have hWopen : IsOpen W := hV.connectedComponentIn
  have hWconn : IsPreconnected W := isPreconnected_connectedComponentIn
  have hz₁W : z₁ ∈ W := mem_connectedComponentIn hz₁V
  have hWV : W ⊆ V := connectedComponentIn_subset V z₁
  -- maximum modulus: `F` is constant on `W`
  have hEq : Set.EqOn F (Function.const ℂ (F z₁)) W :=
    Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hWconn hWopen (hF.mono hWV) hz₁W
      (hmaxV.on_subset hWV)
  -- the frontier of the component avoids `V`
  have hdisj : ∀ q ∈ frontier W, q ∉ V := by
    intro q hq hqV
    have hqcl : q ∈ closure W := frontier_subset_closure hq
    have hqW : q ∉ W := by
      rw [hWopen.frontier_eq] at hq
      exact hq.2
    have hq'open : IsOpen (connectedComponentIn V q) := hV.connectedComponentIn
    have hq'mem : q ∈ connectedComponentIn V q := mem_connectedComponentIn hqV
    obtain ⟨y, hyq, hyW⟩ := _root_.mem_closure_iff.mp hqcl _ hq'open hq'mem
    have h1 : connectedComponentIn V q = connectedComponentIn V y :=
      connectedComponentIn_eq hyq
    have h2 : connectedComponentIn V z₁ = connectedComponentIn V y :=
      connectedComponentIn_eq hyW
    exact hqW (by rw [hW_def, h2, ← h1]; exact hq'mem)
  -- the constant value is `0`, contradicting `ε ≤ ‖F z₁‖`
  have hFz₁ : F z₁ = 0 := by
    rcases Set.eq_empty_or_nonempty (frontier W) with hfe | ⟨p, hp⟩
    · -- `W` is clopen and nonempty, hence `W = ℂ = V`; use the decay at infinity
      have hWclopen : IsClopen W := isClopen_iff_frontier_eq_empty.mpr hfe
      have hWuniv : W = Set.univ := by
        rcases isClopen_iff.mp hWclopen with h | h
        · exact absurd (h ▸ hz₁W) (Set.notMem_empty z₁)
        · exact h
      have hVuniv : V = Set.univ := Set.eq_univ_of_univ_subset (hWuniv ▸ hWV)
      have hconst : ∀ z, F z = F z₁ := fun z =>
        hEq (show z ∈ W by rw [hWuniv]; exact Set.mem_univ z)
      have h0 : Tendsto F (cocompact ℂ) (nhds 0) := by
        rw [hVuniv, Filter.principal_univ, inf_top_eq] at hinfty
        exact hinfty
      exact tendsto_nhds_unique tendsto_const_nhds (h0.congr hconst)
    · -- a frontier point of `W` is a frontier point of `V`; use the boundary decay
      have hpV : p ∉ V := hdisj p hp
      have hpfront : p ∈ frontier V := by
        rw [hV.frontier_eq]
        exact ⟨closure_mono hWV (frontier_subset_closure hp), hpV⟩
      have hpcl : p ∈ closure W := frontier_subset_closure hp
      have hpne : (nhdsWithin p W).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hpcl
      have ht0 : Tendsto F (nhdsWithin p W) (nhds 0) :=
        (hfront p hpfront).mono_left (nhdsWithin_mono p hWV)
      have ht1 : Tendsto F (nhdsWithin p W) (nhds (F z₁)) := by
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact (hEq hw).symm
      exact tendsto_nhds_unique ht1 ht0
  rw [hFz₁, norm_zero] at hεz₁
  linarith

/-! ## The triviality criterion -/

/-- **Weak holomorphy of the corrected field.** If `v` has weak
`∂̄`-derivative `μ` on `ℂ` and `μ` agrees a.e. on the open set `U'` with the
seed combination, then subtracting the explicit solutions kills the weak
`∂̄` on `U'`, and the open-set Weyl lemma makes the difference holomorphic
on `U'`. -/
theorem differentiableOn_sub_seedSolutions {U' : Set ℂ} (hU' : IsOpen U')
    {v μ : ℂ → ℂ} (hv : Continuous v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {K : ℕ} {c : Fin K → ℂ}
    (hloc : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U' → μ z = seedCombo a ρ K c z) :
    DifferentiableOn ℂ
      (fun z => v z - ∑ k : Fin K, c k * seedSolution a ρ k z) U' := by
  classical
  -- `L²_loc` on `univ` gives local integrability on all of `ℂ`.
  have hLI2 : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
      LocallyIntegrable g (volume : Measure ℂ) := by
    intro g hg
    rw [MeasureTheory.locallyIntegrable_iff]
    intro k hk
    have : IsFiniteMeasure ((volume : Measure ℂ).restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    exact (hg k (Set.subset_univ k) hk).integrable (by norm_num)
  -- closure of the weak-`∂̄` predicate under scalar multiples
  have hsmul : ∀ (γ : ℂ) (f μf : ℂ → ℂ), HasL2WeakDzbar f μf Set.univ →
      HasL2WeakDzbar (fun z => γ * f z) (fun z => γ * μf z) Set.univ := by
    rintro γ f μf ⟨gx, gy, ⟨hgx, hgy⟩, hgxL, hgyL, hcomb⟩
    refine ⟨fun z => γ * gx z, fun z => γ * gy z, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · have := hgx.const_smul γ
      simpa only [smul_eq_mul] using this
    · have := hgy.const_smul γ
      simpa only [smul_eq_mul] using this
    · intro k hk hkc
      exact (hgxL k hk hkc).const_mul γ
    · intro k hk hkc
      exact (hgyL k hk hkc).const_mul γ
    · filter_upwards [hcomb] with z hz _
      have e := hz (Set.mem_univ z)
      linear_combination γ * e
  -- closure of the weak-`∂̄` predicate under sums of continuous pieces
  have hadd : ∀ (f₁ f₂ μ₁ μ₂ : ℂ → ℂ), Continuous f₁ → Continuous f₂ →
      HasL2WeakDzbar f₁ μ₁ Set.univ → HasL2WeakDzbar f₂ μ₂ Set.univ →
      HasL2WeakDzbar (fun z => f₁ z + f₂ z) (fun z => μ₁ z + μ₂ z) Set.univ := by
    rintro f₁ f₂ μ₁ μ₂ hc₁ hc₂ ⟨gx₁, gy₁, ⟨hx₁, hy₁⟩, hLx₁, hLy₁, hcb₁⟩
      ⟨gx₂, gy₂, ⟨hx₂, hy₂⟩, hLx₂, hLy₂, hcb₂⟩
    have hf₁ : LocallyIntegrableOn f₁ Set.univ :=
      (hc₁.locallyIntegrable).locallyIntegrableOn _
    have hf₂ : LocallyIntegrableOn f₂ Set.univ :=
      (hc₂.locallyIntegrable).locallyIntegrableOn _
    refine ⟨fun z => gx₁ z + gx₂ z, fun z => gy₁ z + gy₂ z, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · exact hx₁.add hx₂ hf₁ hf₂ ((hLI2 hLx₁).locallyIntegrableOn _)
        ((hLI2 hLx₂).locallyIntegrableOn _)
    · exact hy₁.add hy₂ hf₁ hf₂ ((hLI2 hLy₁).locallyIntegrableOn _)
        ((hLI2 hLy₂).locallyIntegrableOn _)
    · intro k hk hkc
      exact (hLx₁ k hk hkc).add (hLx₂ k hk hkc)
    · intro k hk hkc
      exact (hLy₁ k hk hkc).add (hLy₂ k hk hkc)
    · filter_upwards [hcb₁, hcb₂] with z h1 h2 _
      have e1 := h1 (Set.mem_univ z)
      have e2 := h2 (Set.mem_univ z)
      linear_combination e1 + e2
  -- the zero field has weak `∂̄` zero
  have hzero : HasL2WeakDzbar (fun _ : ℂ => (0 : ℂ)) (fun _ : ℂ => (0 : ℂ))
      Set.univ := by
    refine ⟨fun _ => 0, fun _ => 0, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro φ hφ hcs hts
      simp
    · intro φ hφ hcs hts
      simp
    · intro k hk hkc
      exact MemLp.zero'
    · intro k hk hkc
      exact MemLp.zero'
    · filter_upwards with z _
      simp
  -- the seed sum solves its `∂̄`-equation, by finite induction
  have key : ∀ s : Finset (Fin K),
      HasL2WeakDzbar (fun z => ∑ k ∈ s, c k * seedSolution a ρ k z)
        (fun z => ∑ k ∈ s, c k * seedBasis a ρ k z) Set.univ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert k₀ s hk ih =>
        have h1 : HasL2WeakDzbar (fun z => c k₀ * seedSolution a ρ k₀ z)
            (fun z => c k₀ * seedBasis a ρ k₀ z) Set.univ :=
          hsmul (c k₀) _ _ (hasL2WeakDzbar_seedSolution a hρ k₀)
        have hcont1 : Continuous fun z => c k₀ * seedSolution a ρ (k₀ : ℕ) z :=
          continuous_const.mul (seedSolution_continuous a hρ k₀)
        have hconts : Continuous fun z => ∑ k ∈ s, c k * seedSolution a ρ (k : ℕ) z :=
          continuous_finsetSum _ fun k _ =>
            continuous_const.mul (seedSolution_continuous a hρ k)
        have := hadd _ _ _ _ hcont1 hconts h1 ih
        simpa only [Finset.sum_insert hk] using this
  -- unpack the two weak-`∂̄` facts and subtract
  obtain ⟨gxv, gyv, ⟨hgx1, hgy1⟩, hgxL, hgyL, hcombv⟩ := hgrad
  obtain ⟨gxS, gyS, ⟨hgxS1, hgyS1⟩, hgxSL, hgySL, hcombS⟩ := key Finset.univ
  have hSumCont : Continuous fun z => ∑ k : Fin K, c k * seedSolution a ρ k z :=
    continuous_finsetSum _ fun k _ =>
      continuous_const.mul (seedSolution_continuous a hρ k)
  have hsub_x : HasWeakDirDeriv 1 (fun z => gxv z - gxS z)
      (fun z => v z - ∑ k : Fin K, c k * seedSolution a ρ k z) Set.univ :=
    hgx1.sub hgxS1 ((hv.locallyIntegrable).locallyIntegrableOn _)
      ((hSumCont.locallyIntegrable).locallyIntegrableOn _)
      ((hLI2 hgxL).locallyIntegrableOn _) ((hLI2 hgxSL).locallyIntegrableOn _)
  have hsub_y : HasWeakDirDeriv Complex.I (fun z => gyv z - gyS z)
      (fun z => v z - ∑ k : Fin K, c k * seedSolution a ρ k z) Set.univ :=
    hgy1.sub hgyS1 ((hv.locallyIntegrable).locallyIntegrableOn _)
      ((hSumCont.locallyIntegrable).locallyIntegrableOn _)
      ((hLI2 hgyL).locallyIntegrableOn _) ((hLI2 hgySL).locallyIntegrableOn _)
  have hGxL : MemLpLocOn (fun z => gxv z - gxS z) 2 Set.univ := fun k hk hkc =>
    (hgxL k hk hkc).sub (hgxSL k hk hkc)
  have hGyL : MemLpLocOn (fun z => gyv z - gyS z) 2 Set.univ := fun k hk hkc =>
    (hgyL k hk hkc).sub (hgySL k hk hkc)
  -- the Wirtinger combination vanishes a.e. on `U'`
  have hcomb0 : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U' →
      (gxv z - gxS z) + Complex.I * (gyv z - gyS z) = 0 := by
    filter_upwards [hcombv, hcombS, hloc] with z h1 h2 h3 hz
    have e1 : gxv z + Complex.I * gyv z = 2 * μ z := h1 (Set.mem_univ z)
    have e2 : gxS z + Complex.I * gyS z
        = 2 * ∑ k : Fin K, c k * seedBasis a ρ k z := h2 (Set.mem_univ z)
    have e3 : μ z = ∑ k : Fin K, c k * seedBasis a ρ k z := h3 hz
    linear_combination e1 - e2 + 2 * e3
  exact weyl_lemma_on hU' (hv.sub hSumCont).continuousOn
    ⟨hsub_x.mono (Set.subset_univ U'), hsub_y.mono (Set.subset_univ U')⟩
    ((hLI2 hGxL).locallyIntegrableOn U') ((hLI2 hGyL).locallyIntegrableOn U') hcomb0

/-- **The pole-cancellation endgame** (elementary Laurent algebra). If the
negative-power tail agrees, away from `a`, with a function holomorphic in a
neighborhood of `a`, then every coefficient vanishes: multiplying by
`(z−a)^K` and evaluating derivatives at `a` (or comparing Laurent
coefficients through Cauchy integrals over small circles) isolates each
`cₖ·ρ^{2(k+1)} ≠ 0`-candidate in turn. -/
theorem coeffs_eq_zero_of_negPowerCombo_extends {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {K : ℕ} {c : Fin K → ℂ} {h : ℂ → ℂ} {W : Set ℂ}
    (hW : IsOpen W) (ha : a ∈ W) (hh : DifferentiableOn ℂ h W)
    (heq : ∀ z ∈ W, z ≠ a → h z = negPowerCombo a ρ K c z) :
    c = 0 := by
  -- Core step: if all coefficients above `j` vanish, so does `c j`.
  suffices core : ∀ j : Fin K, (∀ k : Fin K, j.1 < k.1 → c k = 0) → c j = 0 by
    have H : ∀ m : ℕ, ∀ i : Fin K, K - m ≤ i.1 → c i = 0 := by
      intro m
      induction m with
      | zero =>
        intro i hi
        exact absurd hi (by have := i.isLt; omega)
      | succ m ih =>
        intro i hi
        rcases Nat.lt_or_ge i.1 (K - m) with h1 | h2
        · exact core i fun k hk => ih k (by omega)
        · exact ih i h2
    funext i
    change c i = 0
    exact H K i (by omega)
  intro j hzero
  -- Value at `a` of the polynomial `ψ z = Σ cₖ ρ^{2(k+1)} (z-a)^{j-k}`.
  have hψa : (∑ k : Fin K,
      c k * ((ρ ^ (2 * (k.1 + 1)) : ℝ) : ℂ) * (a - a) ^ (j.1 - k.1))
      = c j * ((ρ ^ (2 * (j.1 + 1)) : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      rcases Nat.lt_or_ge j.1 k.1 with hlt | hle
      · simp [hzero k hlt]
      · have hne : j.1 - k.1 ≠ 0 := by
          have : k.1 ≠ j.1 := fun hc => hk (Fin.ext hc)
          omega
        simp [sub_self, zero_pow hne]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  -- `(z-a)^{j+1}·h z → 0` along the punctured neighborhood (continuity of `h` at `a`).
  have hlim0 : Tendsto (fun z : ℂ => (z - a) ^ (j.1 + 1) * h z) (𝓝[≠] a) (𝓝 0) := by
    have hca : ContinuousAt (fun z : ℂ => (z - a) ^ (j.1 + 1) * h z) a :=
      ((continuousAt_id.sub continuousAt_const).pow _).mul
        (hh.continuousOn.continuousAt (hW.mem_nhds ha))
    have h2 : Tendsto (fun z : ℂ => (z - a) ^ (j.1 + 1) * h z) (𝓝 a) (𝓝 0) := by
      simpa using hca.tendsto
    exact h2.mono_left nhdsWithin_le_nhds
  -- Off `a`, near `a`, `(z-a)^{j+1}·h z` equals the polynomial `ψ`.
  have hev : (fun z : ℂ => (z - a) ^ (j.1 + 1) * h z)
      =ᶠ[𝓝[≠] a] (fun z : ℂ => ∑ k : Fin K,
        c k * ((ρ ^ (2 * (k.1 + 1)) : ℝ) : ℂ) * (z - a) ^ (j.1 - k.1)) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hW.mem_nhds ha), self_mem_nhdsWithin]
      with z hzW hz
    have hza : z ≠ a := hz
    have hsub : z - a ≠ 0 := sub_ne_zero.mpr hza
    rw [heq z hzW hza]
    simp only [negPowerCombo, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases Nat.lt_or_ge j.1 k.1 with hlt | hle
    · simp [hzero k hlt]
    · have hpow : (z - a) ^ (j.1 + 1) * (z - a) ^ (-(k.1 + 1 : ℤ))
          = (z - a) ^ (j.1 - k.1) := by
        rw [← zpow_natCast (z - a) (j.1 + 1), ← zpow_add₀ hsub,
          ← zpow_natCast (z - a) (j.1 - k.1)]
        congr 1
        omega
      calc (z - a) ^ (j.1 + 1)
            * (c k * ((ρ ^ (2 * (k.1 + 1)) : ℝ) : ℂ) * (z - a) ^ (-(k.1 + 1 : ℤ)))
          = c k * ((ρ ^ (2 * (k.1 + 1)) : ℝ) : ℂ)
            * ((z - a) ^ (j.1 + 1) * (z - a) ^ (-(k.1 + 1 : ℤ))) := by ring
        _ = c k * ((ρ ^ (2 * (k.1 + 1)) : ℝ) : ℂ) * (z - a) ^ (j.1 - k.1) := by
            rw [hpow]
  -- The polynomial `ψ` tends to `c j · ρ^{2(j+1)}` along the punctured neighborhood.
  have hlimψ : Tendsto (fun z : ℂ => ∑ k : Fin K,
      c k * ((ρ ^ (2 * (k.1 + 1)) : ℝ) : ℂ) * (z - a) ^ (j.1 - k.1)) (𝓝[≠] a)
      (𝓝 (c j * ((ρ ^ (2 * (j.1 + 1)) : ℝ) : ℂ))) := by
    have hc : Continuous (fun z : ℂ => ∑ k : Fin K,
        c k * ((ρ ^ (2 * (k.1 + 1)) : ℝ) : ℂ) * (z - a) ^ (j.1 - k.1)) :=
      continuous_finsetSum _ fun k _ =>
        continuous_const.mul ((continuous_id.sub continuous_const).pow _)
    have h2 := (hc.tendsto a).mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] a ≤ 𝓝 a)
    rwa [hψa] at h2
  -- Uniqueness of limits along the (nontrivial) punctured filter.
  have hkey : c j * ((ρ ^ (2 * (j.1 + 1)) : ℝ) : ℂ) = 0 :=
    tendsto_nhds_unique (hlimψ.congr' hev.symm) hlim0
  have hρc : ((ρ ^ (2 * (j.1 + 1)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _ hρ.ne')
  exact (mul_eq_zero.mp hkey).resolve_right hρc

/-- **The seed-triviality criterion.** Let `U' ⊆ ℂ` be open, carrying a
closed disk `closedBall a ρ ⊆ U'`, with some point `b ∉ closure U'`
available for damping. If a sphere vector field `v` has weak `∂̄`-derivative
`μ` on `ℂ` that agrees a.e. on `U'` with the seed combination `Σ cₖ·σₖ`, and
`v` vanishes on the frontier of `U'`, then `c = 0`.

Proof route: `h := v − Σ cₖ·uₖ` is holomorphic on `U'`
(`differentiableOn_sub_seedSolutions`) and equals `v − negPowerCombo`
outside the disk; with `M(z) := (z−a)^K/(z−b)^{K+3}`, the product
`F := (h + negPowerCombo)·M` is holomorphic on `U'` (removable singularity
at `a`: the zero of `M` dominates the pole of the tail), tends to `0` at
every frontier point (there `h + negPowerCombo = v → 0`) and at infinity
within `U'` (sphere-field growth `O(|z|²)` against `M = O(|z|^{−3})`), so
`F ≡ 0` by the maximum principle; since `M ≠ 0` off `{a, b}`, the tail
`negPowerCombo = −h` extends holomorphically across `a`, and
`coeffs_eq_zero_of_negPowerCombo_extends` gives `c = 0`. -/
theorem seed_vanish_of_sphereField_vanish_on_frontier
    {U' : Set ℂ} (hU' : IsOpen U')
    {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall a ρ ⊆ U')
    (hb : ∃ b : ℂ, b ∉ closure U')
    {K : ℕ} {c : Fin K → ℂ} {v μ : ℂ → ℂ}
    (hv : IsSphereVectorField v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    (hloc : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U' → μ z = seedCombo a ρ K c z)
    (hfront : ∀ p ∈ frontier U', v p = 0) :
    c = 0 := by
  classical
  obtain ⟨b, hbc⟩ := hb
  obtain ⟨hvc, L, hL⟩ := hv
  -- ## Stage 3: quadratic growth bound for the sphere field
  have hgrow := hL.norm.eventually_lt_const (lt_add_one ‖L‖)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hgrow
  obtain ⟨ε, hε, hεb⟩ := hgrow
  have hfar : ∀ z : ℂ, ε⁻¹ < ‖z‖ → ‖v z‖ ≤ (‖L‖ + 1) * ‖z‖ ^ 2 := by
    intro z hzn
    have hz0 : z ≠ 0 := by
      intro he
      rw [he, norm_zero] at hzn
      have := inv_pos.mpr hε
      linarith
    have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
    have h1 : dist z⁻¹ 0 < ε := by
      rw [dist_zero_right, norm_inv]
      exact inv_lt_of_inv_lt₀ hε hzn
    have h2 := hεb h1 (Set.mem_compl_singleton_iff.mpr (inv_ne_zero hz0))
    rw [inv_inv] at h2
    have h3 : ‖(z⁻¹) ^ 2 * v z‖ = ‖v z‖ / ‖z‖ ^ 2 := by
      rw [norm_mul, norm_pow, norm_inv]
      ring
    rw [h3, div_lt_iff₀ (pow_pos hzpos 2)] at h2
    linarith
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : ℂ) ε⁻¹).exists_bound_of_continuousOn hvc.continuousOn
  set B : ℝ := max (‖L‖ + 1) (max C 0) with hBdef
  have hB0 : (0 : ℝ) ≤ B := le_trans (le_max_right C 0) (le_max_right _ _)
  have hBL : ‖L‖ + 1 ≤ B := le_max_left _ _
  have hB : ∀ w : ℂ, ‖v w‖ ≤ B * (1 + ‖w‖ ^ 2) := by
    intro w
    by_cases hw : ‖w‖ ≤ ε⁻¹
    · have h1 : ‖v w‖ ≤ C := hC w (by rwa [Metric.mem_closedBall, dist_zero_right])
      have h2 : C ≤ B := le_trans (le_max_left C 0) (le_max_right _ _)
      nlinarith [mul_nonneg hB0 (sq_nonneg ‖w‖)]
    · have h1 := hfar w (not_le.mp hw)
      nlinarith [mul_le_mul_of_nonneg_right hBL (sq_nonneg ‖w‖), hB0]
  -- ## Stage 1: the corrected field is holomorphic on `U'`
  set h : ℂ → ℂ := fun z => v z - ∑ k : Fin K, c k * seedSolution a ρ k z with hhdef
  have hd : DifferentiableOn ℂ h U' := by
    rw [hhdef]
    exact differentiableOn_sub_seedSolutions hU' hvc hgrad hρ hloc
  -- ## Stage 4: the pole-cleared polynomial `P` and the clearing identity
  set P : ℂ → ℂ := fun z =>
    ∑ k : Fin K, c k * ((ρ ^ (2 * (k.1 + 1)) : ℝ) : ℂ) * (z - a) ^ (K - (k.1 + 1)) with hPdef
  have hP : ∀ z : ℂ, z ≠ a → (z - a) ^ K * negPowerCombo a ρ K c z = P z := by
    intro z hz
    have hza : (z - a) ≠ 0 := sub_ne_zero_of_ne hz
    simp only [hPdef, negPowerCombo]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : k.1 + 1 ≤ K := k.isLt
    have key : (z - a) ^ K * (z - a) ^ (-(k.1 + 1 : ℤ)) = (z - a) ^ (K - (k.1 + 1)) := by
      rw [← zpow_natCast (z - a) K, ← zpow_add₀ hza, ← zpow_natCast (z - a) (K - (k.1 + 1))]
      congr 1
      omega
    linear_combination (c k * ((ρ ^ (2 * (k.1 + 1)) : ℝ) : ℂ)) * key
  have hPdiff : Differentiable ℂ P := by
    rw [hPdef]
    exact Differentiable.fun_sum fun k _ => by fun_prop
  -- membership facts
  have ha_mem : a ∈ U' := hball (mem_closedBall_self hρ.le)
  have hbne : ∀ z ∈ U', z ≠ b := fun z hz he => hbc (he ▸ subset_closure hz)
  -- ## Stage 5: the damped function `F` and its holomorphy on `U'`
  set F : ℂ → ℂ := fun z =>
    (h z * (z - a) ^ K + P z) * ((z - b) ^ (K + 3))⁻¹ with hFdef
  have hFdiff : DifferentiableOn ℂ F U' := by
    rw [hFdef]
    refine DifferentiableOn.mul
      (DifferentiableOn.add (hd.mul ?_) hPdiff.differentiableOn) ?_
    · exact (Differentiable.differentiableOn (by fun_prop))
    · intro z hz
      have h1 : DifferentiableAt ℂ (fun w : ℂ => (w - b) ^ (K + 3)) z := by fun_prop
      exact (h1.inv (pow_ne_zero _ (sub_ne_zero_of_ne (hbne z hz)))).differentiableWithinAt
  -- ## Stage 2 + 4: representation of `F` off the closed disk
  have hFoff : ∀ z : ℂ, z ∉ Metric.closedBall a ρ →
      F z = v z * (z - a) ^ K * ((z - b) ^ (K + 3))⁻¹ := by
    intro z hz
    have hzball : z ∉ Metric.ball a ρ := fun hm => hz (ball_subset_closedBall hm)
    have hza : z ≠ a := by
      intro he
      exact hz (by rw [he]; exact mem_closedBall_self hρ.le)
    have hh : h z = v z - negPowerCombo a ρ K c z := by
      simp only [hhdef]
      rw [sum_seedSolution_eq_negPowerCombo a ρ K c hzball]
    have hPz := hP z hza
    simp only [hFdef]
    rw [hh, ← hPz]
    ring
  -- ## Stage 6: `F` tends to `0` at every frontier point of `U'`
  have hfrontF : ∀ p ∈ frontier U', Tendsto F (nhdsWithin p U') (nhds 0) := by
    intro p hp
    have hp2 : p ∈ closure U' \ U' := by rwa [← hU'.frontier_eq]
    have hpball : p ∉ Metric.closedBall a ρ := fun hm => hp2.2 (hball hm)
    have hpb : p ≠ b := fun he => hbc (he ▸ hp2.1)
    have hpbne : ((p - b) ^ (K + 3) : ℂ) ≠ 0 := pow_ne_zero _ (sub_ne_zero_of_ne hpb)
    have hcont : ContinuousAt (fun z : ℂ => v z * (z - a) ^ K * ((z - b) ^ (K + 3))⁻¹) p := by
      have h1 : ContinuousAt (fun z : ℂ => v z * (z - a) ^ K) p := by fun_prop
      have h2 : ContinuousAt (fun z : ℂ => (z - b) ^ (K + 3)) p := by fun_prop
      exact h1.mul (h2.inv₀ hpbne)
    have hg0 : Tendsto (fun z : ℂ => v z * (z - a) ^ K * ((z - b) ^ (K + 3))⁻¹)
        (nhds p) (nhds 0) := by
      simpa only [hfront p hp, zero_mul] using hcont.tendsto
    refine (hg0.mono_left nhdsWithin_le_nhds).congr' ?_
    have hev : ∀ᶠ z in nhdsWithin p U', z ∉ Metric.closedBall a ρ :=
      mem_nhdsWithin_of_mem_nhds (isClosed_closedBall.isOpen_compl.mem_nhds hpball)
    filter_upwards [hev] with z hz
    exact (hFoff z hz).symm
  -- ## Stage 7: `F` tends to `0` at infinity within `U'`
  have hinfty : Tendsto F (cocompact ℂ ⊓ Filter.principal U') (nhds 0) := by
    have hbound : ∀ᶠ z in cocompact ℂ ⊓ Filter.principal U',
        ‖F z‖ ≤ B * 2 ^ (2 * K + 4) / ‖z‖ := by
      have hev : ∀ᶠ z : ℂ in cocompact ℂ ⊓ Filter.principal U',
          2 * (‖a‖ + ‖b‖ + ρ + 1) ≤ ‖z‖ :=
        (tendsto_norm_cocompact_atTop.eventually_ge_atTop _).filter_mono inf_le_left
      filter_upwards [hev] with z hz
      have hz2 : (2 : ℝ) ≤ ‖z‖ := by linarith [norm_nonneg a, norm_nonneg b, hρ.le]
      have hz0 : (0 : ℝ) < ‖z‖ := by linarith
      have hnotball : z ∉ Metric.closedBall a ρ := by
        intro hm
        rw [Metric.mem_closedBall, dist_eq_norm] at hm
        linarith [norm_sub_norm_le z a, norm_nonneg a, norm_nonneg b, hρ.le]
      have ha2 : ‖z - a‖ ≤ 2 * ‖z‖ := by
        linarith [norm_sub_le z a, norm_nonneg b, hρ.le]
      have hb2 : ‖z‖ / 2 ≤ ‖z - b‖ := by
        linarith [norm_sub_norm_le z b, norm_nonneg a, hρ.le]
      rw [hFoff z hnotball]
      simp only [norm_mul, norm_pow, norm_inv]
      have hx1 : (1 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith
      have hv2 : ‖v z‖ ≤ 2 * B * ‖z‖ ^ 2 := by
        nlinarith [hB z, mul_le_mul_of_nonneg_left hx1 hB0]
      have hnn : (0 : ℝ) ≤ 2 * B * ‖z‖ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      have hstep1 : ‖v z‖ * ‖z - a‖ ^ K ≤ (2 * B * ‖z‖ ^ 2) * (2 * ‖z‖) ^ K :=
        mul_le_mul hv2 (pow_le_pow_left₀ (norm_nonneg _) ha2 K)
          (pow_nonneg (norm_nonneg _) K) hnn
      have hdpos : (0 : ℝ) < (‖z‖ / 2) ^ (K + 3) := pow_pos (by linarith) _
      have hstep2 : (‖z - b‖ ^ (K + 3))⁻¹ ≤ ((‖z‖ / 2) ^ (K + 3))⁻¹ :=
        inv_anti₀ hdpos (pow_le_pow_left₀ (by linarith) hb2 _)
      calc ‖v z‖ * ‖z - a‖ ^ K * (‖z - b‖ ^ (K + 3))⁻¹
          ≤ ((2 * B * ‖z‖ ^ 2) * (2 * ‖z‖) ^ K) * ((‖z‖ / 2) ^ (K + 3))⁻¹ :=
            mul_le_mul hstep1 hstep2 (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _))
              (mul_nonneg hnn (pow_nonneg (by linarith) K))
        _ = B * 2 ^ (2 * K + 4) / ‖z‖ := by
            rw [div_pow, mul_pow, inv_div]
            field_simp
            ring
    exact squeeze_zero_norm' hbound
      (tendsto_const_nhds.div_atTop (tendsto_norm_cocompact_atTop.mono_left inf_le_left))
  -- ## Stage 8: maximum principle kills `F` on `U'`
  have hF0 : ∀ z ∈ U', F z = 0 :=
    eqOn_zero_of_forall_frontier_tendsto_zero hU' hFdiff hfrontF hinfty
  -- ## Stages 9–10: unwind and apply the pole-cancellation endgame
  refine coeffs_eq_zero_of_negPowerCombo_extends hρ hU' ha_mem hd.neg ?_
  intro z hzU hza
  have hzbne : ((z - b) ^ (K + 3) : ℂ) ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero_of_ne (hbne z hzU))
  have hFz := hF0 z hzU
  simp only [hFdef] at hFz
  have hnum : h z * (z - a) ^ K + P z = 0 := by
    rcases mul_eq_zero.mp hFz with h1 | h2
    · exact h1
    · exact absurd (inv_eq_zero.mp h2) hzbne
  have hPz := hP z hza
  have hzane : ((z - a) : ℂ) ^ K ≠ 0 := pow_ne_zero _ (sub_ne_zero_of_ne hza)
  have hkey : (z - a) ^ K * (h z + negPowerCombo a ρ K c z) = 0 := by
    linear_combination hnum + hPz
  have h0 : h z + negPowerCombo a ρ K c z = 0 := by
    rcases mul_eq_zero.mp hkey with h1 | h2
    · exact absurd h1 hzane
    · exact h2
  simp only [Pi.neg_apply]
  linear_combination -h0

end NoWanderingDomains
