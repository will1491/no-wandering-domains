/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Analysis.Sobolev.WeakDeriv
import NoWanderingDomains.Analysis.SingularIntegral.CalderonZygmund
import NoWanderingDomains.Analysis.SingularIntegral.Beurling.Kernel
import NoWanderingDomains.Analysis.SingularIntegral.Beurling.Convolution
import Carleson.ToMathlib.HardyLittlewood
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.UniformIntegrable
import NoWanderingDomains.Analysis.SingularIntegral.DyadicLebesgue
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# The Gehring reverse-Hölder self-improvement

This development proves the **higher-integrability residual** of Bojarski's theorem: an
`L²` Beltrami fixed point `G = h + T(μ·G)` with `‖μ‖∞ < 1` is automatically locally
`Lᵠ` for some `q > 2`, with *no* `Lᵖ` hypothesis on the inhomogeneity `h`. Classically
this is the **Gehring reverse-Hölder / Caccioppoli self-improvement lemma**.

`Sobolev` is the head module of the `GehringHigherIntegrability/` chain — every other module
imports it (transitively) — so it carries this development overview alongside its own content
(the endpoint Sobolev embedding and cutoffs; see "This file" below). There is no aggregator
module: downstream consumers import the specific node they need
(e.g. `Beurling/Beltrami` → `Residual` → `SelfImprovement`).

## The f-level reverse-Hölder

The reverse-Hölder gain cannot be derived from the bare fixed-point equation
`G = h + T(μ·G)` alone: the `L² ⟹ L¹` reverse-Hölder gain is a *Sobolev–Poincaré*
phenomenon on the **primitive** `F` of which `G` is the weak holomorphic gradient
(`G = ∂F`). The reverse-Hölder node is therefore stated at the **`f`-level**: it takes the
primitive bundle `(F, Gx, Gy)` (which L5 `dz_cutoff_eq_beurling_repr` constructs and hands
back), and reduces to two analytic nodes — a Sobolev–Poincaré inequality on balls and an
`f`-level Caccioppoli inequality obtained by weak integration by parts against the test
function `χ²(F − F_B)`.

The development is decomposed into the following dependency-ordered nodes:

* **N1** `sobolevPoincare_ball` — Sobolev–Poincaré on a ball for a `W^{1,2}` primitive
  `F` with weak gradient `(Gx, Gy)`: the `L²`-oscillation of `F` on a ball is bounded by
  `r` times the `L¹`-average of `‖∇F‖`.
* **N2** `weakIBP_against_W12` — weak integration by parts admitting a `W^{1,2}` compactly
  supported test function (not just `C^∞`), e.g. `φ = χ²(F − c)`.
* **N3** `caccioppoli_of_beltrami` — the `f`-level Caccioppoli inequality: the gradient
  energy `⨍⁻_B ‖G‖²` is bounded by `r⁻²·⨍⁻_{2B}‖F − F_B‖² + ‖h‖`-terms, by testing the
  Beltrami structure against `χ²(F − F_B)` via N2.
* **S1** `reverseHolder_of_weakGradient` — the **`f`-level reverse-Hölder** inequality on
  every ball, derived from N3 (Caccioppoli) + N1 (Sobolev–Poincaré): the `r⁻¹` from
  Caccioppoli cancels the `r` from Sobolev–Poincaré, yielding a scale-invariant constant
  `A`.
* **S2** `gehring_selfImprovement` — the **general, equation-agnostic** Gehring lemma:
  a nonnegative locally-`Lᵠ` weight satisfying a reverse-Hölder inequality on all balls
  (with a controlled lower-order term) is locally `L^{q+ε}` for some `ε > 0`.
* **S3** `beltrami_fixedPoint_memLpLocOn` — the restated residual: assemble S1 + S2
  to upgrade an `L²` Beltrami fixed point (carrying its primitive bundle) to `Lᵠ_loc`,
  `q > 2`.

## File organization

The nodes are split across the `GehringHigherIntegrability/` directory, in dependency order
(each module imports its predecessor in the list):

* `Sobolev` (this file) — the sound planar endpoint Sobolev embedding `‖u‖₂ ≤ C·‖∇u‖₁` and
  the adapted smooth cutoffs with the `1/r` gradient bound.
* `Poincare` — the `(1,1)`-Poincaré inequality `poincare_one_one_ball`.
* `SobolevPoincare` — the Sobolev–Poincaré node N1 (`sobolevPoincare_ball`).
* `Caccioppoli` — the weak IBP node N2 and the Caccioppoli inequality N3.
* `ReverseHolder` — the `f`-level reverse-Hölder inequality S1.
* `SelfImprovementCore` — the Calderón–Zygmund good-λ machinery (S2, part I): the radius
  hole-filling iteration `giaquinta_iteration` and the stopping/density/cover/engine
  lemmas, up to the honest exponent-1 good-λ integral.
* `SelfImprovement` — the collar-free good-λ companion, the `Žₙ`-truncation hole-filling
  pillars, and the assembled abstract lemma `gehring_selfImprovement` (S2, part II).
* `Residual` — the restated residual `beltrami_fixedPoint_memLpLocOn` (S3).

## Infrastructure consumed by N1 (the Sobolev–Poincaré proof)

The Sobolev–Poincaré node `sobolevPoincare_ball` is discharged by mollifying
the primitive `F` to `C¹` (Mathlib's `MeasureTheory.MemLp.exist_eLpNorm_sub_le`)
and applying Mathlib's Gagliardo–Nirenberg–Sobolev
inequality `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one`
(`Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`) at `n = finrank ℝ ℂ = 2`,
`p = 2` (the Hölder conjugate of `2`), to the mean-subtracted localized function, then
passing the weak gradient `(Gx, Gy)` to the Fréchet derivative in the `L¹` limit.

## Infrastructure consumed by S2 (the Gehring proof)

The general self-improvement node `gehring_selfImprovement` is discharged
using the **Hardy–Littlewood maximal function stack from the Carleson library**
(`Carleson.ToMathlib.HardyLittlewood`):

* `maximalFunction` — the (centered, ball-averaged)
  maximal operator over a countable family of balls.
* `hasWeakType_maximalFunction_one` — the weak-(1,1) endpoint of the maximal operator.
* `hasStrongType_maximalFunction_one` — the strong-(p,p) bound for `1 < p`.
* the Vitali covering `Vitali.exists_disjoint_subfamily_covering_enlargement_ball` and
  `measure_biUnion_le_lintegral` for the good-λ / stopping-time decomposition,

together with Mathlib's **layer-cake** representation
(`MeasureTheory.lintegral_eq_lintegral_meas_lt`, `Mathlib.MeasureTheory.Integral.Layercake`)
and the average notation `⨍⁻` (`MeasureTheory.laverage`,
`Mathlib.MeasureTheory.Integral.Average`). The Carleson maximal stack is already a dependency
(see `Beurling/Kernel.lean`).

All nodes (N1, N2, N3, S1, S2, S3) are proved across the modules listed above, so the
downstream consumer `beltrami_fixedPoint_memLpLocOn_of_memLp_two` (in `Beurling/Beltrami.lean`)
is fully discharged.

## This file (`Sobolev`)

The sound planar endpoint Sobolev embedding `‖u‖₂ ≤ C·‖∇u‖₁` (the `P`-stack:
`eLpNorm_two_le_eLpNorm_fderiv_one`, `eLpNorm_fderiv_one_le_partials`,
`exists_contDiff_approx_W11`), and the adapted smooth cutoffs with the `1/r` gradient bound
(`exists_cutoff_ball`, `exists_cutoff_ball_uniform`).
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal Topology Real Pointwise

namespace NoWanderingDomains

/-! ## P-stack — sound endpoint Sobolev (replaces the unsound `I₁` Riesz/HLS route)

The strong `I₁ : L¹ → L²` Riesz bound is the EXCLUDED Hardy–Littlewood–Sobolev endpoint and
is mathematically FALSE: the localized density `g = 1_{ball(x,ε)}` gives
`(∫_B (I₁ g)²)^{1/2} / ‖g‖₁ ≈ √(ln(1/ε)) → ∞`. The Sobolev–Poincaré target `N1` is
nevertheless TRUE and is re-derived from the genuine endpoint Sobolev embedding
`W^{1,1}(ℝ²) ↪ L²(ℝ²)` (Mathlib `eLpNorm_le_eLpNorm_fderiv_one`) via a cutoff and `W^{1,1}`
mollification. -/

/-- **P1 (`eLpNorm_two_le_eLpNorm_fderiv_one`).** The genuine planar endpoint Sobolev
inequality `‖u‖_{L²} ≤ C·‖∇u‖_{L¹}` for a `C¹` compactly-supported `u` — the true
`W^{1,1}(ℝ²) ↪ L²(ℝ²)` embedding. A thin wrapper over Mathlib's
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one` at `finrank ℝ ℂ = 2`, `p = 2` (the
Hölder-conjugate hypothesis `((2 : ℝ≥0)).HolderConjugate 2` is discharged by
`NNReal.holderConjugate_iff`). The SOUND replacement for the false strong `I₁ : L¹ → L²`
bound. -/
theorem eLpNorm_two_le_eLpNorm_fderiv_one :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : ℂ → ℂ}, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u 2 volume ≤ ENNReal.ofReal C * eLpNorm (fderiv ℝ u) 1 volume := by
  -- The witness is Mathlib's endpoint Sobolev constant at the exponent `2`.
  refine ⟨(eLpNormLESNormFDerivOneConst (volume : Measure ℂ) ((2 : NNReal) : ℝ) : ℝ),
    NNReal.coe_nonneg _, ?_⟩
  intro u hu hucs
  -- The Hölder-conjugate side condition: at `finrank ℝ ℂ = 2`, the conjugate of `2` is `2`.
  have hhc : ((2 : NNReal)).HolderConjugate (2 : NNReal) := by
    rw [NNReal.holderConjugate_iff]; exact ⟨by norm_num, by norm_num⟩
  have hfin : (((Module.finrank ℝ ℂ : ℕ) : NNReal)).HolderConjugate (2 : NNReal) := by
    rw [Complex.finrank_real_complex]; exact_mod_cast hhc
  have key := eLpNorm_le_eLpNorm_fderiv_one (volume : Measure ℂ) hu hucs hfin
  rw [ENNReal.ofReal_coe_nnreal]
  -- Reconcile `(↑(2 : NNReal) : ℝ≥0∞)` with the literal `(2 : ℝ≥0∞)` in the goal.
  have h2 : ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) := by norm_num
  rw [h2] at key
  convert key using 2

/-- **P2 (`eLpNorm_fderiv_one_le_partials`).** The operator norm of the Fréchet derivative is
controlled in `L¹` by its two directional components in the `{1, I}` basis:
`‖∇u‖_{L¹} ≤ ‖∂₁u‖_{L¹} + ‖∂_I u‖_{L¹}`. Elementary: pointwise
`‖fderiv ℝ u z‖ ≤ ‖(fderiv ℝ u z) 1‖ + ‖(fderiv ℝ u z) I‖` (any unit `w = a·1 + b·I` has
`|a|, |b| ≤ 1`), then the `L¹` triangle inequality. -/
theorem eLpNorm_fderiv_one_le_partials {u : ℂ → ℂ} (hu : ContDiff ℝ 1 u) :
    eLpNorm (fderiv ℝ u) 1 volume ≤
      eLpNorm (fun z => (fderiv ℝ u z) 1) 1 volume
        + eLpNorm (fun z => (fderiv ℝ u z) Complex.I) 1 volume := by
  -- Abbreviations for the two directional partials.
  set a : ℂ → ℂ := fun z => (fderiv ℝ u z) 1 with ha
  set b : ℂ → ℂ := fun z => (fderiv ℝ u z) Complex.I with hb
  -- Pointwise operator-norm bound `‖∇u z‖ ≤ ‖a z‖ + ‖b z‖`.
  have hptw : ∀ z : ℂ, ‖fderiv ℝ u z‖ ≤ ‖a z‖ + ‖b z‖ := by
    intro z
    apply ContinuousLinearMap.opNorm_le_bound
    · positivity
    · intro w
      -- Decompose `w = w.re • 1 + w.im • I` in `ℂ`.
      have hdecomp : w = w.re • (1 : ℂ) + w.im • Complex.I := by
        apply Complex.ext <;> simp [Complex.real_smul]
      have hmap : (fderiv ℝ u z) w = w.re • a z + w.im • b z := by
        conv_lhs => rw [hdecomp]
        rw [map_add, map_smul, map_smul]
      rw [hmap]
      calc ‖w.re • a z + w.im • b z‖
          ≤ ‖w.re • a z‖ + ‖w.im • b z‖ := norm_add_le _ _
        _ = |w.re| * ‖a z‖ + |w.im| * ‖b z‖ := by
            rw [Complex.real_smul, Complex.real_smul, norm_mul, norm_mul,
              Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ ‖w‖ * ‖a z‖ + ‖w‖ * ‖b z‖ := by
            gcongr
            · exact abs_re_le_norm w
            · exact abs_im_le_norm w
        _ = (‖a z‖ + ‖b z‖) * ‖w‖ := by ring
  -- `eLpNorm (∇u) 1 ≤ eLpNorm (z ↦ ‖a z‖ + ‖b z‖) 1` by monotonicity, then the `L¹`
  -- triangle inequality splits the majorant into the two directional `L¹` norms.
  have hcont : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hma : AEStronglyMeasurable a volume :=
    (hcont.clm_apply continuous_const).aestronglyMeasurable
  have hmb : AEStronglyMeasurable b volume :=
    (hcont.clm_apply continuous_const).aestronglyMeasurable
  calc eLpNorm (fderiv ℝ u) 1 volume
      ≤ eLpNorm (fun z => ‖a z‖ + ‖b z‖) 1 volume := eLpNorm_mono_real hptw
    _ = eLpNorm ((fun z => ‖a z‖) + (fun z => ‖b z‖)) 1 volume := by rfl
    _ ≤ eLpNorm (fun z => ‖a z‖) 1 volume + eLpNorm (fun z => ‖b z‖) 1 volume :=
        eLpNorm_add_le hma.norm hmb.norm le_rfl
    _ = eLpNorm a 1 volume + eLpNorm b 1 volume := by
        rw [eLpNorm_norm, eLpNorm_norm]

/-- **P3 (`exists_contDiff_approx_W11`).** The one genuinely new analytic node: a
compactly-supported `W^{1,2}` function `u` (given through its weak directional derivatives
`gx` (direction `1`), `gy` (direction `I`), assumed `L¹`) is approximated by a `C¹`
compactly-supported `w` simultaneously in `L²` of the function and with gradient-`L¹` norm
not exceeding `‖gx‖₁ + ‖gy‖₁` (up to `ε`). Proof by `ContDiffBump` mollification `w = η_δ ⋆ u`:
`‖w − u‖_{L²} → 0`; the directional derivatives commute with mollification
(`fderiv_convolution_normed_apply_eq`, `(fderiv w) v = η_δ ⋆ gᵥ`), so by Young
`‖η_δ ⋆ gᵥ‖₁ ≤ ‖gᵥ‖₁`, and `P2` gives `‖∇w‖₁ ≤ ‖gx‖₁ + ‖gy‖₁`. This replaces the entire
`I₁` Riesz / HLS sub-stack. -/
theorem exists_contDiff_approx_W11 {u gx gy : ℂ → ℂ}
    (hu2 : MemLp u 2 volume) (hucs : HasCompactSupport u)
    (hgx : HasWeakDirDeriv 1 gx u Set.univ) (hgy : HasWeakDirDeriv Complex.I gy u Set.univ)
    (hgx1 : MemLp gx 1 volume) (hgy1 : MemLp gy 1 volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ℂ → ℂ, ContDiff ℝ 1 w ∧ HasCompactSupport w ∧
      eLpNorm (fun z => w z - u z) 2 volume ≤ ENNReal.ofReal ε ∧
      eLpNorm (fderiv ℝ w) 1 volume ≤
        eLpNorm gx 1 volume + eLpNorm gy 1 volume + ENNReal.ofReal ε := by
  classical
  -- ====================================================================
  -- (Y) General `L¹` Young inequality `‖ρ ⋆ g‖₁ ≤ ‖ρ‖₁ · ‖g‖₁`.
  -- ====================================================================
  have young : ∀ (ρ : ℂ → ℝ) (g : ℂ → ℂ), MemLp ρ 1 volume → MemLp g 1 volume →
      eLpNorm (MeasureTheory.convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) 1 volume
        ≤ eLpNorm ρ 1 volume * eLpNorm g 1 volume := by
    intro ρ g hρmem hgmem
    set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ with hL
    rw [eLpNorm_one_eq_lintegral_enorm]
    have hpt : ∀ z, ‖MeasureTheory.convolution ρ g L volume z‖ₑ
        ≤ ∫⁻ t, ‖ρ t‖ₑ * ‖g (z - t)‖ₑ ∂volume := by
      intro z
      rw [MeasureTheory.convolution_def]
      refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
      refine lintegral_mono (fun t => ?_)
      rw [hL, ContinuousLinearMap.lsmul_apply, enorm_smul]
    have hgsm : AEStronglyMeasurable g volume := hgmem.1
    have hρsm : AEStronglyMeasurable ρ volume := hρmem.1
    have hjoint : AEMeasurable (Function.uncurry
        (fun z t => ‖ρ t‖ₑ * ‖g (z - t)‖ₑ)) (volume.prod volume) := by
      have h1 : AEStronglyMeasurable
          (fun p : ℂ × ℂ => (L (ρ p.2)) (g (p.1 - p.2))) (volume.prod volume) :=
        AEStronglyMeasurable.convolution_integrand L hρsm hgsm
      have h2 : AEMeasurable (fun p : ℂ × ℂ => ‖(L (ρ p.2)) (g (p.1 - p.2))‖ₑ)
          (volume.prod volume) := h1.enorm
      refine h2.congr (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Function.uncurry, hL, ContinuousLinearMap.lsmul_apply, enorm_smul]
    calc ∫⁻ z, ‖MeasureTheory.convolution ρ g L volume z‖ₑ ∂volume
        ≤ ∫⁻ z, ∫⁻ t, ‖ρ t‖ₑ * ‖g (z - t)‖ₑ ∂volume ∂volume := lintegral_mono hpt
      _ = ∫⁻ t, ∫⁻ z, ‖ρ t‖ₑ * ‖g (z - t)‖ₑ ∂volume ∂volume :=
          lintegral_lintegral_swap hjoint
      _ = ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ z, ‖g (z - t)‖ₑ ∂volume ∂volume := by
          refine lintegral_congr (fun t => ?_)
          rw [lintegral_const_mul' _ _ (by simp [enorm_ne_top])]
      _ = ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ z, ‖g z‖ₑ ∂volume ∂volume := by
          refine lintegral_congr (fun t => ?_)
          congr 1
          exact lintegral_sub_right_eq_self (fun z => ‖g z‖ₑ) t
      _ = (∫⁻ t, ‖ρ t‖ₑ ∂volume) * ∫⁻ z, ‖g z‖ₑ ∂volume := by
          rw [lintegral_mul_const'' _ hρsm.enorm]
      _ = eLpNorm ρ 1 volume * eLpNorm g 1 volume := by
          rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm]
  -- ====================================================================
  -- (F) Mollification commutes with the weak directional derivative.
  -- ====================================================================
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
  -- ====================================================================
  -- (C) `L²` mollification convergence `‖ρ_n ⋆ g - g‖₂ → 0` for `g ∈ L²`.
  -- ====================================================================
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
  -- ====================================================================
  -- Assembly: pick one mollifier of small enough radius.
  -- ====================================================================
  -- A canonical mollifier sequence with `rOut = 2/(n+2) → 0`.
  set φ₀ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ₀
  have hφ₀rout : Filter.Tendsto (fun n => (φ₀ n).rOut) Filter.atTop (nhds 0) := by
    have heq : (fun n : ℕ => (φ₀ n).rOut) = fun n : ℕ => (2 : ℝ) / (n + 2) := rfl
    rw [heq]
    exact Filter.Tendsto.div_atTop tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  -- The `L²` convergence of the mollification of `u`, extract one good index `N`.
  have hconvu := conv_tendsto hu2 φ₀ hφ₀rout
  have hev : ∀ᶠ n in Filter.atTop,
      eLpNorm (MeasureTheory.convolution ((φ₀ n).normed volume) u
        (ContinuousLinearMap.lsmul ℝ ℝ) volume - u) 2 volume ≤ ENNReal.ofReal ε :=
    ENNReal.tendsto_nhds_zero.mp hconvu (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨N, hN⟩ := hev.exists
  -- The chosen mollifier `ρ := (φ₀ N).normed volume` and `w := ρ ⋆ u`.
  set ρ : ℂ → ℝ := (φ₀ N).normed volume with hρdef
  set w : ℂ → ℂ := MeasureTheory.convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume with hwdef
  have hρ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ := (φ₀ N).contDiff_normed
  have hρ_cs : HasCompactSupport ρ := (φ₀ N).hasCompactSupport_normed
  have hρ_cont : Continuous ρ := hρ_smooth.continuous
  have hρ_memLp : MemLp ρ 1 volume := hρ_cont.memLp_of_hasCompactSupport hρ_cs
  -- local integrability of `u`, `gx`, `gy`.
  have hu_li : MeasureTheory.LocallyIntegrable u := hu2.locallyIntegrable (by norm_num)
  have hgx_li : MeasureTheory.LocallyIntegrable gx := hgx1.locallyIntegrable le_rfl
  have hgy_li : MeasureTheory.LocallyIntegrable gy := hgy1.locallyIntegrable le_rfl
  -- (1) `w` is `C¹` and (2) compactly supported.
  have hw_contDiff : ContDiff ℝ 1 w := by
    refine HasCompactSupport.contDiff_convolution_left _ hρ_cs ?_ hu_li
    exact hρ_smooth.of_le (by exact_mod_cast le_top)
  have hw_cs : HasCompactSupport w :=
    HasCompactSupport.convolution _ hρ_cs hucs
  refine ⟨w, hw_contDiff, hw_cs, ?_, ?_⟩
  · -- (3) `L²` distance.
    have : (fun z => w z - u z) = w - u := rfl
    rw [this]; exact hN
  · -- (4) gradient `L¹` bound.
    -- `ρ`'s `L¹` mass is `1`.
    have hρ_norm1 : eLpNorm ρ 1 volume = 1 := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      have hint : Integrable ρ volume :=
        hρ_cont.integrable_of_hasCompactSupport hρ_cs
      have hnn : 0 ≤ᵐ[volume] ρ :=
        Filter.Eventually.of_forall (fun z => (φ₀ N).nonneg_normed z)
      calc ∫⁻ z, ‖ρ z‖ₑ ∂volume
          = ∫⁻ z, ENNReal.ofReal (ρ z) ∂volume := by
            refine lintegral_congr (fun z => ?_)
            rw [Real.enorm_of_nonneg ((φ₀ N).nonneg_normed z)]
        _ = ENNReal.ofReal (∫ z, ρ z ∂volume) :=
            (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
        _ = 1 := by rw [hρdef, (φ₀ N).integral_normed]; simp
    -- Identify the two directional derivatives of `w` with mollifications.
    have hdx : (fun z => (fderiv ℝ w z) 1)
        = MeasureTheory.convolution ρ gx (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      funext z
      exact fderiv_conv hgx hu_li hgx_li hρ_smooth hρ_cs z
    have hdy : (fun z => (fderiv ℝ w z) Complex.I)
        = MeasureTheory.convolution ρ gy (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      funext z
      exact fderiv_conv hgy hu_li hgy_li hρ_smooth hρ_cs z
    -- Young `L¹` bounds: `‖ρ ⋆ gx‖₁ ≤ ‖gx‖₁`, `‖ρ ⋆ gy‖₁ ≤ ‖gy‖₁`.
    have hyx : eLpNorm (fun z => (fderiv ℝ w z) 1) 1 volume ≤ eLpNorm gx 1 volume := by
      rw [hdx]
      calc eLpNorm (MeasureTheory.convolution ρ gx (ContinuousLinearMap.lsmul ℝ ℝ) volume) 1 volume
          ≤ eLpNorm ρ 1 volume * eLpNorm gx 1 volume := young ρ gx hρ_memLp hgx1
        _ = eLpNorm gx 1 volume := by rw [hρ_norm1, one_mul]
    have hyy : eLpNorm (fun z => (fderiv ℝ w z) Complex.I) 1 volume ≤ eLpNorm gy 1 volume := by
      rw [hdy]
      calc eLpNorm (MeasureTheory.convolution ρ gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) 1 volume
          ≤ eLpNorm ρ 1 volume * eLpNorm gy 1 volume := young ρ gy hρ_memLp hgy1
        _ = eLpNorm gy 1 volume := by rw [hρ_norm1, one_mul]
    -- Combine with P2 and add the `ε` slack.
    calc eLpNorm (fderiv ℝ w) 1 volume
        ≤ eLpNorm (fun z => (fderiv ℝ w z) 1) 1 volume
            + eLpNorm (fun z => (fderiv ℝ w z) Complex.I) 1 volume :=
          eLpNorm_fderiv_one_le_partials hw_contDiff
      _ ≤ eLpNorm gx 1 volume + eLpNorm gy 1 volume := add_le_add hyx hyy
      _ ≤ eLpNorm gx 1 volume + eLpNorm gy 1 volume + ENNReal.ofReal ε := le_self_add


/-! ## P-cut — an adapted smooth cutoff with the `1/r` gradient bound -/

/-- **P-cut (`exists_cutoff_ball`).** A smooth cutoff `χ` adapted to the ball `ball x r`:
`χ ≡ 1` on `ball x r`, `0 ≤ χ ≤ 1`, support inside `closedBall x (3r/2)`, and the
**scale-correct gradient bound** `‖fderiv ℝ χ z‖ ≤ C / r` for a dimensional constant `C`
(independent of `x, r`). This is the cutoff both N1 (Sobolev–Poincaré) and N3 (Caccioppoli)
test against; Mathlib's `ContDiffBump` provides the plateau/support/smoothness but exposes no
derivative bound, so the `C/r` control is obtained here by rescaling a fixed reference bump
`ψ` (whose continuous compactly-supported `fderiv` is bounded by some `C₀`) along
`z ↦ r⁻¹ • (z − x)`, the chain rule supplying the `r⁻¹` factor. -/
theorem exists_cutoff_ball (x : ℂ) (r : ℝ) (hr : 0 < r) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ z, 0 ≤ χ z) ∧ (∀ z, χ z ≤ 1) ∧
      (∀ z ∈ Metric.ball x r, χ z = 1) ∧
      tsupport χ ⊆ Metric.closedBall x (3 * r / 2) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖fderiv ℝ χ z‖ ≤ C / r := by
  -- Reference bump centred at `0` with `rIn = 1`, `rOut = 3/2`.
  set ψ : ContDiffBump (0 : ℂ) := ⟨1, 3 / 2, by norm_num, by norm_num⟩ with hψdef
  -- The affine rescaling `g z = r⁻¹ • (z - x)` and the cutoff `χ = ψ ∘ g`.
  set g : ℂ → ℂ := fun z => r⁻¹ • (z - x) with hgdef
  set χ : ℂ → ℝ := fun z => ψ (g z) with hχdef
  -- Norm identity for the real rescaling, valid since `r > 0`.
  have hnorm : ∀ w : ℂ, ‖r⁻¹ • w‖ = r⁻¹ * ‖w‖ := by
    intro w
    rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- Membership translation: `g z ∈ ball 0 s ↔ z ∈ ball x (r*s)` (for `s ≥ 0`).
  have hball : ∀ (s : ℝ), 0 ≤ s →
      ∀ z, g z ∈ Metric.ball (0 : ℂ) s ↔ z ∈ Metric.ball x (r * s) := by
    intro s hs z
    simp only [hgdef, Metric.mem_ball, dist_eq_norm, sub_zero, hnorm]
    rw [inv_mul_lt_iff₀ hr]
  -- Membership translation for closed balls (used for the plateau).
  have hcball : ∀ (s : ℝ), 0 ≤ s →
      ∀ z, g z ∈ Metric.closedBall (0 : ℂ) s ↔ z ∈ Metric.closedBall x (r * s) := by
    intro s hs z
    simp only [hgdef, Metric.mem_closedBall, dist_eq_norm, sub_zero, hnorm]
    rw [inv_mul_le_iff₀ hr]
  -- `g` is smooth.
  have hg_cd : ContDiff ℝ (⊤ : ℕ∞) g :=
    (contDiff_id.sub contDiff_const).const_smul r⁻¹
  -- `χ` is smooth.
  have hχ_cd : ContDiff ℝ (⊤ : ℕ∞) χ := ψ.contDiff.comp hg_cd
  -- `g` is differentiable, with constant derivative `r⁻¹ • id`.
  have hg_diff : ∀ z, DifferentiableAt ℝ g z :=
    fun z => (hg_cd.differentiable (by simp)).differentiableAt
  have hfd_g : ∀ z, fderiv ℝ g z = r⁻¹ • (ContinuousLinearMap.id ℝ ℂ) := by
    intro z
    have h1 : HasFDerivAt (fun z : ℂ => z - x) (ContinuousLinearMap.id ℝ ℂ) z :=
      (hasFDerivAt_id z).sub_const x
    exact (h1.const_smul (r⁻¹)).fderiv
  refine ⟨χ, hχ_cd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Compact support: `χ` is supported where `g z ∈ support ψ = ball 0 (3/2)`,
    -- a bounded preimage under `g`.
    apply HasCompactSupport.intro (K := Metric.closedBall x (3 * r / 2))
      (isCompact_closedBall _ _)
    intro z hz
    -- If `z ∉ closedBall x (3r/2)` then `g z ∉ closedBall 0 (3/2) ⊇ ball 0 (3/2)`.
    have hznot : z ∉ Metric.closedBall x (r * (3 / 2)) := by
      intro hmem
      exact hz (by simpa [mul_div_assoc, mul_comm] using hmem)
    have hgz : g z ∉ Metric.closedBall (0 : ℂ) (3 / 2) := by
      rw [hcball (3 / 2) (by norm_num)]; exact hznot
    have hgz' : g z ∉ Function.support (⇑ψ) := by
      rw [ψ.support_eq]
      intro hmem
      exact hgz (Metric.ball_subset_closedBall hmem)
    change χ z = 0
    rw [hχdef]
    exact Function.notMem_support.mp hgz'
  · -- `0 ≤ χ`.
    intro z; exact ψ.nonneg
  · -- `χ ≤ 1`.
    intro z; exact ψ.le_one
  · -- Plateau: on `ball x r`, `g z ∈ closedBall 0 1 = closedBall 0 rIn`, so `ψ (g z) = 1`.
    intro z hz
    have hzc : z ∈ Metric.closedBall x (r * 1) := by
      rw [mul_one]; exact Metric.ball_subset_closedBall hz
    have hgz : g z ∈ Metric.closedBall (0 : ℂ) 1 := (hcball 1 (by norm_num) z).mpr hzc
    simpa [hχdef] using ψ.one_of_mem_closedBall (by simpa [hψdef] using hgz)
  · -- Support is inside `closedBall x (3r/2)`: `support χ ⊆ ball x (3r/2)`, and `tsupport`
    -- is its closure, hence inside the closed ball.
    apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    -- `z ∈ support χ` means `ψ (g z) ≠ 0`, i.e. `g z ∈ support ψ = ball 0 (3/2)`.
    have hχz : χ z ≠ 0 := Function.mem_support.mp hz
    have hgz : g z ∈ Function.support (⇑ψ) := Function.mem_support.mpr hχz
    rw [ψ.support_eq, hball (3 / 2) (by norm_num) z] at hgz
    refine Metric.ball_subset_closedBall ?_
    simpa [mul_div_assoc, mul_comm] using hgz
  · -- Gradient bound `‖fderiv χ z‖ ≤ C₀ / r`.
    -- `fderiv ψ` is continuous (smoothness ≥ 1) with compact support, hence bounded by `C₀`.
    have hψ_cd : ContDiff ℝ (⊤ : ℕ∞) (⇑ψ) := ψ.contDiff
    have hfd_cont : Continuous (fderiv ℝ (⇑ψ)) := hψ_cd.continuous_fderiv (by simp)
    have hfd_cs : HasCompactSupport (fderiv ℝ (⇑ψ)) :=
      HasCompactSupport.fderiv ℝ ψ.hasCompactSupport
    obtain ⟨C₀, hC₀⟩ := hfd_cs.exists_bound_of_continuous hfd_cont
    refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
    intro z
    -- Chain rule and operator-norm submultiplicativity supply the `r⁻¹` factor.
    have hψ_diff : DifferentiableAt ℝ (⇑ψ) (g z) :=
      (hψ_cd.differentiable (by simp)).differentiableAt
    have hcomp : fderiv ℝ χ z = (fderiv ℝ (⇑ψ) (g z)).comp (fderiv ℝ g z) := by
      have hχeq : χ = (⇑ψ) ∘ g := rfl
      rw [hχeq, fderiv_comp z hψ_diff (hg_diff z)]
    rw [hcomp, hfd_g z]
    calc ‖(fderiv ℝ (⇑ψ) (g z)).comp (r⁻¹ • ContinuousLinearMap.id ℝ ℂ)‖
        ≤ ‖fderiv ℝ (⇑ψ) (g z)‖ * ‖r⁻¹ • (ContinuousLinearMap.id ℝ ℂ)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖fderiv ℝ (⇑ψ) (g z)‖ * r⁻¹ := by
          rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hr)]
      _ ≤ max C₀ 0 * r⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt (inv_pos.mpr hr))
          exact le_trans (hC₀ (g z)) (le_max_left _ _)
      _ = max C₀ 0 / r := by rw [div_eq_mul_inv]

/-- **P-cut, uniform-constant form (`exists_cutoff_ball_uniform`).** The gradient bound
constant of `exists_cutoff_ball` is in fact **independent of the ball** `(x, r)`: it is the
bound on the Fréchet derivative of a single fixed reference bump. This uniform form hoists
that constant `Cχ` *outside* the `∀ x r` quantifier, which is what the Sobolev–Poincaré node
N1 needs in order to choose its ball-independent constant. -/
theorem exists_cutoff_ball_uniform :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ (x : ℂ) (r : ℝ), 0 < r →
      ∃ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
        (∀ z, 0 ≤ χ z) ∧ (∀ z, χ z ≤ 1) ∧
        (∀ z ∈ Metric.ball x r, χ z = 1) ∧
        tsupport χ ⊆ Metric.closedBall x (3 * r / 2) ∧
        ∀ z, ‖fderiv ℝ χ z‖ ≤ Cχ / r := by
  -- Reference bump centred at `0` with `rIn = 1`, `rOut = 3/2`, fixed once.
  set ψ : ContDiffBump (0 : ℂ) := ⟨1, 3 / 2, by norm_num, by norm_num⟩ with hψdef
  have hψ_cd : ContDiff ℝ (⊤ : ℕ∞) (⇑ψ) := ψ.contDiff
  have hfd_cont : Continuous (fderiv ℝ (⇑ψ)) := hψ_cd.continuous_fderiv (by simp)
  have hfd_cs : HasCompactSupport (fderiv ℝ (⇑ψ)) :=
    HasCompactSupport.fderiv ℝ ψ.hasCompactSupport
  obtain ⟨C₀, hC₀⟩ := hfd_cs.exists_bound_of_continuous hfd_cont
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro x r hr
  -- The affine rescaling `g z = r⁻¹ • (z - x)` and the cutoff `χ = ψ ∘ g`.
  set g : ℂ → ℂ := fun z => r⁻¹ • (z - x) with hgdef
  set χ : ℂ → ℝ := fun z => ψ (g z) with hχdef
  have hnorm : ∀ w : ℂ, ‖r⁻¹ • w‖ = r⁻¹ * ‖w‖ := by
    intro w
    rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  have hball : ∀ (s : ℝ), 0 ≤ s →
      ∀ z, g z ∈ Metric.ball (0 : ℂ) s ↔ z ∈ Metric.ball x (r * s) := by
    intro s hs z
    simp only [hgdef, Metric.mem_ball, dist_eq_norm, sub_zero, hnorm]
    rw [inv_mul_lt_iff₀ hr]
  have hcball : ∀ (s : ℝ), 0 ≤ s →
      ∀ z, g z ∈ Metric.closedBall (0 : ℂ) s ↔ z ∈ Metric.closedBall x (r * s) := by
    intro s hs z
    simp only [hgdef, Metric.mem_closedBall, dist_eq_norm, sub_zero, hnorm]
    rw [inv_mul_le_iff₀ hr]
  have hg_cd : ContDiff ℝ (⊤ : ℕ∞) g :=
    (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have hχ_cd : ContDiff ℝ (⊤ : ℕ∞) χ := ψ.contDiff.comp hg_cd
  have hg_diff : ∀ z, DifferentiableAt ℝ g z :=
    fun z => (hg_cd.differentiable (by simp)).differentiableAt
  have hfd_g : ∀ z, fderiv ℝ g z = r⁻¹ • (ContinuousLinearMap.id ℝ ℂ) := by
    intro z
    have h1 : HasFDerivAt (fun z : ℂ => z - x) (ContinuousLinearMap.id ℝ ℂ) z :=
      (hasFDerivAt_id z).sub_const x
    exact (h1.const_smul (r⁻¹)).fderiv
  refine ⟨χ, hχ_cd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.intro (K := Metric.closedBall x (3 * r / 2))
      (isCompact_closedBall _ _)
    intro z hz
    have hznot : z ∉ Metric.closedBall x (r * (3 / 2)) := by
      intro hmem
      exact hz (by simpa [mul_div_assoc, mul_comm] using hmem)
    have hgz : g z ∉ Metric.closedBall (0 : ℂ) (3 / 2) := by
      rw [hcball (3 / 2) (by norm_num)]; exact hznot
    have hgz' : g z ∉ Function.support (⇑ψ) := by
      rw [ψ.support_eq]
      intro hmem
      exact hgz (Metric.ball_subset_closedBall hmem)
    change χ z = 0
    rw [hχdef]
    exact Function.notMem_support.mp hgz'
  · intro z; exact ψ.nonneg
  · intro z; exact ψ.le_one
  · intro z hz
    have hzc : z ∈ Metric.closedBall x (r * 1) := by
      rw [mul_one]; exact Metric.ball_subset_closedBall hz
    have hgz : g z ∈ Metric.closedBall (0 : ℂ) 1 := (hcball 1 (by norm_num) z).mpr hzc
    simpa [hχdef] using ψ.one_of_mem_closedBall (by simpa [hψdef] using hgz)
  · apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    have hχz : χ z ≠ 0 := Function.mem_support.mp hz
    have hgz : g z ∈ Function.support (⇑ψ) := Function.mem_support.mpr hχz
    rw [ψ.support_eq, hball (3 / 2) (by norm_num) z] at hgz
    refine Metric.ball_subset_closedBall ?_
    simpa [mul_div_assoc, mul_comm] using hgz
  · intro z
    have hψ_diff : DifferentiableAt ℝ (⇑ψ) (g z) :=
      (hψ_cd.differentiable (by simp)).differentiableAt
    have hcomp : fderiv ℝ χ z = (fderiv ℝ (⇑ψ) (g z)).comp (fderiv ℝ g z) := by
      have hχeq : χ = (⇑ψ) ∘ g := rfl
      rw [hχeq, fderiv_comp z hψ_diff (hg_diff z)]
    rw [hcomp, hfd_g z]
    calc ‖(fderiv ℝ (⇑ψ) (g z)).comp (r⁻¹ • ContinuousLinearMap.id ℝ ℂ)‖
        ≤ ‖fderiv ℝ (⇑ψ) (g z)‖ * ‖r⁻¹ • (ContinuousLinearMap.id ℝ ℂ)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖fderiv ℝ (⇑ψ) (g z)‖ * r⁻¹ := by
          rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hr)]
      _ ≤ max C₀ 0 * r⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt (inv_pos.mpr hr))
          exact le_trans (hC₀ (g z)) (le_max_left _ _)
      _ = max C₀ 0 / r := by rw [div_eq_mul_inv]


end NoWanderingDomains
