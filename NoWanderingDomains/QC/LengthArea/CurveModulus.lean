/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.QC.Defs.Geometric
import NoWanderingDomains.QC.Defs.Analytic
import NoWanderingDomains.Analysis.Sobolev.SobolevToACL
import NoWanderingDomains.Analysis.SingularIntegral.Beurling.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Length–area infrastructure for the quasiconformal equivalence

The equivalence of the analytic and geometric definitions of quasiconformality
rests on the **length–area method**, which relates the modulus distortion of a
quasiconformal map to its differential. This subfolder collects the infrastructure
lemmas that the analytic ⇒ geometric direction consumes — the pieces
that go beyond the absolute-continuity-on-lines theory and the change-of-variables
formula already in hand.

Four ingredients:

* **Wirtinger singular values** (`det_fderiv_eq_wirtinger`, `opNorm_fderiv_eq_wirtinger`)
  — the real Jacobian determinant and operator norm of the real differential of a
  map `ℂ → ℂ`, expressed through the Wirtinger derivatives `∂f`, `∂̄f`:
  `det (Df) = ‖∂f‖² − ‖∂̄f‖²` and `‖Df‖ = ‖∂f‖ + ‖∂̄f‖`. These are the singular-value
  identities of a real-linear self-map of `ℂ`; the dilatation bound
  `‖(Df)⁻¹‖² · det (Df) ≤ K` follows algebraically from them and the Beltrami bound
  `‖∂̄f‖ ≤ ((K−1)/(K+1)) ‖∂f‖`. Self-contained linear algebra.

* **Gehring–Lehto a.e. differentiability** (`IsQCAnalytic.ae_differentiableAt`) — a
  quasiconformal map is differentiable almost everywhere. A genuine classical
  theorem (absent from Mathlib, which has a.e. differentiability only for Lipschitz
  and one-dimensional monotone maps).

* **Fuglede's theorem** (`curveModulus_sdiff_modulus_zero`,
  `IsQCAnalytic.chainRule_exceptional_modulus_zero`) — a curve subfamily of zero modulus does
  not affect the modulus, and the curves whose image under a quasiconformal map
  fails to be absolutely continuous form a family of zero modulus. This is what
  lets the length–area transfer of densities ignore the exceptional curves.

The Wirtinger singular-value identities are proved here; Gehring–Lehto and Fuglede
are the deep classical inputs the equivalence reduces to.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace NoWanderingDomains

/-- **Wirtinger Jacobian identity.** The real Jacobian determinant of `f : ℂ → ℂ`
at `z` is `‖∂f‖² − ‖∂̄f‖²`. (Singular-value identity: the determinant of the real
differential equals the product of singular values `(‖∂f‖ + ‖∂̄f‖)(‖∂f‖ − ‖∂̄f‖)`.) -/
theorem det_fderiv_eq_wirtinger (f : ℂ → ℂ) (z : ℂ) :
    (fderiv ℝ f z).det = ‖dz f z‖ ^ 2 - ‖dzbar f z‖ ^ 2 := by
  -- Work with a general real-linear self-map `A` of `ℂ`.
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ f z with hA
  -- The entries of the matrix of `A` in the basis `(1, I)`.
  set a : ℝ := (A 1).re with ha
  set b : ℝ := (A 1).im with hb
  set c : ℝ := (A Complex.I).re with hc
  set d : ℝ := (A Complex.I).im with hd
  -- `dz f z` and `dzbar f z` in terms of `a, b, c, d`.
  have hpval : dz f z = (1/2 : ℂ) * ((A 1) - Complex.I * (A Complex.I)) := rfl
  have hqval : dzbar f z = (1/2 : ℂ) * ((A 1) + Complex.I * (A Complex.I)) := rfl
  -- Determinant of `A` via the matrix in `Complex.basisOneI`.
  have hdet : A.det = a * d - b * c := by
    have key : ∀ M : ℂ →ₗ[ℝ] ℂ, LinearMap.det M
        = (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI M).det := fun M =>
      (LinearMap.det_toMatrix Complex.basisOneI M).symm
    rw [ContinuousLinearMap.det, key]
    have hb0 : (Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ) 0 = (1 : ℂ) := by
      simp [Complex.coe_basisOneI]
    have hb1 : (Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ) 1 = Complex.I := by
      simp [Complex.coe_basisOneI]
    have c00 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 0 0 = a := by
      rw [LinearMap.toMatrix_apply, hb0, Complex.coe_basisOneI_repr]
      rfl
    have c10 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 1 0 = b := by
      rw [LinearMap.toMatrix_apply, hb0, Complex.coe_basisOneI_repr]
      rfl
    have c01 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 0 1 = c := by
      rw [LinearMap.toMatrix_apply, hb1, Complex.coe_basisOneI_repr]
      rfl
    have c11 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 1 1 = d := by
      rw [LinearMap.toMatrix_apply, hb1, Complex.coe_basisOneI_repr]
      rfl
    have h0 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) = !![a, c; b, d] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
          Matrix.cons_val_fin_one] <;>
        first | exact c00 | exact c01 | exact c10 | exact c11
    rw [h0, Matrix.det_fin_two_of]; ring
  -- Compute the two norms-squared.
  have hp2 : ‖dz f z‖ ^ 2 = ((a + d) ^ 2 + (b - c) ^ 2) / 4 := by
    rw [← Complex.normSq_eq_norm_sq, hpval, Complex.normSq_apply]
    have h12re : (1/2 : ℂ).re = 1/2 := by norm_num [Complex.div_re]
    have h12im : (1/2 : ℂ).im = 0 := by norm_num [Complex.div_im]
    have hre : ((1/2 : ℂ) * ((A 1) - Complex.I * (A Complex.I))).re = (a + d) / 2 := by
      rw [ha, hd]
      simp only [Complex.mul_re, Complex.sub_re, Complex.mul_im, Complex.sub_im,
        Complex.I_re, Complex.I_im, h12re, h12im]
      ring
    have him : ((1/2 : ℂ) * ((A 1) - Complex.I * (A Complex.I))).im = (b - c) / 2 := by
      rw [hb, hc]
      simp only [Complex.mul_im, Complex.sub_re, Complex.mul_re, Complex.sub_im,
        Complex.I_re, Complex.I_im, h12re, h12im]
      ring
    rw [hre, him]; ring
  have hq2 : ‖dzbar f z‖ ^ 2 = ((a - d) ^ 2 + (b + c) ^ 2) / 4 := by
    rw [← Complex.normSq_eq_norm_sq, hqval, Complex.normSq_apply]
    have h12re : (1/2 : ℂ).re = 1/2 := by norm_num [Complex.div_re]
    have h12im : (1/2 : ℂ).im = 0 := by norm_num [Complex.div_im]
    have hre : ((1/2 : ℂ) * ((A 1) + Complex.I * (A Complex.I))).re = (a - d) / 2 := by
      rw [ha, hd]
      simp only [Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im,
        Complex.I_re, Complex.I_im, h12re, h12im]
      ring
    have him : ((1/2 : ℂ) * ((A 1) + Complex.I * (A Complex.I))).im = (b + c) / 2 := by
      rw [hb, hc]
      simp only [Complex.mul_im, Complex.add_re, Complex.mul_re, Complex.add_im,
        Complex.I_re, Complex.I_im, h12re, h12im]
      ring
    rw [hre, him]; ring
  rw [hdet, hp2, hq2]; ring

/-- **Wirtinger operator-norm identity.** The operator norm of the real differential
of `f : ℂ → ℂ` at `z` is `‖∂f‖ + ‖∂̄f‖`, the larger singular value of the real-linear
self-map of `ℂ`. -/
theorem opNorm_fderiv_eq_wirtinger (f : ℂ → ℂ) (z : ℂ) :
    ‖fderiv ℝ f z‖ = ‖dz f z‖ + ‖dzbar f z‖ := by
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ f z with hA
  set p : ℂ := dz f z with hp
  set q : ℂ := dzbar f z with hq
  -- `A` is the real-linear map `w ↦ p w + q conj w`.
  have hrepr : ∀ w : ℂ, A w = p * w + q * (starRingEnd ℂ) w := by
    intro w
    rw [hp, hq, dz, dzbar]
    have hLw : A w = (↑w.re : ℂ) * A 1 + (↑w.im : ℂ) * A Complex.I := by
      conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • Complex.I by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
      rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have hcw : (starRingEnd ℂ) w = (↑w.re : ℂ) - ↑w.im * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im w]
      simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hw : w = (↑w.re : ℂ) + ↑w.im * Complex.I := (Complex.re_add_im w).symm
    rw [hLw, hcw]
    set sa : ℂ := (↑w.re : ℂ) with hsa
    set sb : ℂ := (↑w.im : ℂ) with hsb
    rw [hw]
    linear_combination (sb * A Complex.I) * Complex.I_mul_I
  -- Upper bound: `‖A w‖ ≤ (‖p‖ + ‖q‖) ‖w‖`.
  have hub : ‖A‖ ≤ ‖p‖ + ‖q‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
    rw [hrepr w]
    calc ‖p * w + q * (starRingEnd ℂ) w‖
        ≤ ‖p * w‖ + ‖q * (starRingEnd ℂ) w‖ := norm_add_le _ _
      _ = ‖p‖ * ‖w‖ + ‖q‖ * ‖w‖ := by
            rw [norm_mul, norm_mul, Complex.norm_conj]
      _ = (‖p‖ + ‖q‖) * ‖w‖ := by ring
  -- Lower bound: exhibit a unit `w₀` with `‖A w₀‖ = ‖p‖ + ‖q‖`.
  have hlb : ‖p‖ + ‖q‖ ≤ ‖A‖ := by
    -- The target unit vector squares to `t / ‖t‖`, where `t = conj p * q`.
    obtain ⟨w₀, hw₀norm, hcross⟩ :
        ∃ w₀ : ℂ, ‖w₀‖ = 1 ∧ (p * (starRingEnd ℂ) q * (w₀ * w₀)).re = ‖p‖ * ‖q‖ := by
      by_cases ht : (starRingEnd ℂ) p * q = 0
      · -- Then `p = 0` or `q = 0`; the vector `1` works.
        refine ⟨1, by simp, ?_⟩
        rcases mul_eq_zero.mp ht with h | h
        · have hp0 : p = 0 := (map_eq_zero _).mp h
          simp [hp0]
        · have hq0 : q = 0 := h
          simp [hq0]
      · -- `t ≠ 0`: take a square root of the unit `t / ‖t‖`.
        set t : ℂ := (starRingEnd ℂ) p * q with htdef
        have htnorm : (‖t‖ : ℝ) ≠ 0 := by
          simpa [norm_eq_zero] using ht
        obtain ⟨s, hs⟩ := Complex.isSquare (t / (‖t‖ : ℂ))
        have hsnorm : ‖s‖ = 1 := by
          have h1 : ‖s * s‖ = 1 := by
            rw [← hs, norm_div]
            simp [Complex.norm_real, htnorm]
          rw [norm_mul] at h1
          nlinarith [norm_nonneg s, h1]
        refine ⟨s, hsnorm, ?_⟩
        -- `p * conj q * (s * s) = conj t * (t / ‖t‖) = ‖t‖`, a positive real.
        have hpcq : p * (starRingEnd ℂ) q = (starRingEnd ℂ) t := by
          rw [htdef, map_mul, Complex.conj_conj, mul_comm]
        have htt : (starRingEnd ℂ) t * t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
          rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have hval : p * (starRingEnd ℂ) q * (s * s) = (‖t‖ : ℂ) := by
          rw [hpcq, ← hs, ← mul_div_assoc, htt]
          rw [div_eq_iff (by exact_mod_cast htnorm)]
          push_cast; ring
        rw [hval]
        have hnormt : ‖t‖ = ‖p‖ * ‖q‖ := by
          rw [htdef, Complex.norm_mul, Complex.norm_conj]
        rw [Complex.ofReal_re, hnormt]
    -- Use the maximizer.
    have key : ‖A w₀‖ = ‖p‖ + ‖q‖ := by
      have hw₀ns : Complex.normSq w₀ = 1 := by
        rw [Complex.normSq_eq_norm_sq, hw₀norm]; norm_num
      have hcrossterm : (p * w₀ * (starRingEnd ℂ) (q * (starRingEnd ℂ) w₀)).re
          = ‖p‖ * ‖q‖ := by
        rw [map_mul, Complex.conj_conj]
        have hr : p * w₀ * ((starRingEnd ℂ) q * w₀) = p * (starRingEnd ℂ) q * (w₀ * w₀) := by
          ring
        rw [hr, hcross]
      have hpns : Complex.normSq p = ‖p‖ ^ 2 := Complex.normSq_eq_norm_sq p
      have hqns : Complex.normSq q = ‖q‖ ^ 2 := Complex.normSq_eq_norm_sq q
      have hnsq : ‖A w₀‖ ^ 2 = (‖p‖ + ‖q‖) ^ 2 := by
        rw [hrepr w₀, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
          Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_conj,
          hw₀ns, hcrossterm, hpns, hqns]
        ring
      have hnn : (0 : ℝ) ≤ ‖p‖ + ‖q‖ := by positivity
      nlinarith [norm_nonneg (A w₀), hnsq, hnn]
    calc ‖p‖ + ‖q‖ = ‖A w₀‖ := key.symm
      _ ≤ ‖A‖ * ‖w₀‖ := A.le_opNorm w₀
      _ = ‖A‖ := by rw [hw₀norm, mul_one]
  exact le_antisymm hub hlb

/-- **Wirtinger operator-norm of the inverse differential.** When the real Jacobian
determinant of `f` at `z` is positive (so the differential is invertible), the
operator norm of the inverse differential is the reciprocal of the smaller singular
value, `‖A⁻¹‖ = (‖∂f‖ + ‖∂̄f‖) / det (A)`. Combined with `det = ‖∂f‖² − ‖∂̄f‖²`, this
gives `‖A⁻¹‖ = (‖∂f‖ − ‖∂̄f‖)⁻¹`, and the dilatation bound
`‖A⁻¹‖² · det = (‖∂f‖ + ‖∂̄f‖)/(‖∂f‖ − ‖∂̄f‖)` that the length–area estimate consumes. -/
theorem opNorm_inverse_eq_wirtinger (f : ℂ → ℂ) (z : ℂ)
    (hdet : 0 < (fderiv ℝ f z).det) :
    ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖
      = (‖dz f z‖ + ‖dzbar f z‖) / (fderiv ℝ f z).det := by
  classical
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ f z with hA
  set p : ℂ := dz f z with hp
  set q : ℂ := dzbar f z with hq
  set d : ℝ := A.det with hd
  -- The differential is `w ↦ p w + q conj w` (extracted from `opNorm_fderiv_eq_wirtinger`).
  have hAval : ∀ w : ℂ, A w = p * w + q * (starRingEnd ℂ) w := by
    intro w
    rw [hp, hq, dz, dzbar]
    have hLw : A w = (↑w.re : ℂ) * A 1 + (↑w.im : ℂ) * A Complex.I := by
      conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • Complex.I by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
      rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have hcw : (starRingEnd ℂ) w = (↑w.re : ℂ) - ↑w.im * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im w]
      simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hw : w = (↑w.re : ℂ) + ↑w.im * Complex.I := (Complex.re_add_im w).symm
    rw [hLw, hcw]
    set sa : ℂ := (↑w.re : ℂ) with hsa
    set sb : ℂ := (↑w.im : ℂ) with hsb
    rw [hw]
    linear_combination (sb * A Complex.I) * Complex.I_mul_I
  -- `det A = ‖p‖² − ‖q‖²` via the already-proven identity.
  have hddef : d = ‖p‖ ^ 2 - ‖q‖ ^ 2 := by
    rw [hd, hA, hp, hq]; exact det_fderiv_eq_wirtinger f z
  -- Positivity facts: `‖p‖ > ‖q‖ ≥ 0`, hence `d > 0` and the relevant norms are nonzero.
  have hdpos : 0 < d := hdet
  have hqlt : ‖q‖ ^ 2 < ‖p‖ ^ 2 := by nlinarith [hddef, hdpos]
  have hppos : 0 < ‖p‖ := by nlinarith [norm_nonneg q, norm_nonneg p, hqlt]
  -- ***Reusable op-norm fact***: for any `p' q' : ℂ`, the real-linear map
  -- `Lpq p' q' : w ↦ p' w + q' conj w` has operator norm `‖p'‖ + ‖q'‖`.
  set Lpq : ℂ → ℂ → (ℂ →L[ℝ] ℂ) := fun p' q' =>
    (ContinuousLinearMap.mul ℝ ℂ p') +
      (ContinuousLinearMap.mul ℝ ℂ q').comp (Complex.conjCLE : ℂ →L[ℝ] ℂ) with hLpqdef
  have hLpqapp : ∀ (p' q' w : ℂ), Lpq p' q' w = p' * w + q' * (starRingEnd ℂ) w := by
    intro p' q' w
    simp [hLpqdef, ContinuousLinearMap.mul_apply']
  have opNormLpq : ∀ p' q' : ℂ, ‖Lpq p' q'‖ = ‖p'‖ + ‖q'‖ := by
    intro p' q'
    -- Upper bound.
    have hub : ‖Lpq p' q'‖ ≤ ‖p'‖ + ‖q'‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
      rw [hLpqapp p' q' w]
      calc ‖p' * w + q' * (starRingEnd ℂ) w‖
          ≤ ‖p' * w‖ + ‖q' * (starRingEnd ℂ) w‖ := norm_add_le _ _
        _ = ‖p'‖ * ‖w‖ + ‖q'‖ * ‖w‖ := by
              rw [norm_mul, norm_mul, Complex.norm_conj]
        _ = (‖p'‖ + ‖q'‖) * ‖w‖ := by ring
    -- Lower bound: exhibit a unit `w₀` with `‖Lpq p' q' w₀‖ = ‖p'‖ + ‖q'‖`.
    have hlb : ‖p'‖ + ‖q'‖ ≤ ‖Lpq p' q'‖ := by
      obtain ⟨w₀, hw₀norm, hcross⟩ :
          ∃ w₀ : ℂ, ‖w₀‖ = 1 ∧ (p' * (starRingEnd ℂ) q' * (w₀ * w₀)).re = ‖p'‖ * ‖q'‖ := by
        by_cases ht : (starRingEnd ℂ) p' * q' = 0
        · refine ⟨1, by simp, ?_⟩
          rcases mul_eq_zero.mp ht with h | h
          · have hp0 : p' = 0 := (map_eq_zero _).mp h
            simp [hp0]
          · have hq0 : q' = 0 := h
            simp [hq0]
        · set t : ℂ := (starRingEnd ℂ) p' * q' with htdef
          have htnorm : (‖t‖ : ℝ) ≠ 0 := by
            simpa [norm_eq_zero] using ht
          obtain ⟨s, hs⟩ := Complex.isSquare (t / (‖t‖ : ℂ))
          have hsnorm : ‖s‖ = 1 := by
            have h1 : ‖s * s‖ = 1 := by
              rw [← hs, norm_div]
              simp [Complex.norm_real, htnorm]
            rw [norm_mul] at h1
            nlinarith [norm_nonneg s, h1]
          refine ⟨s, hsnorm, ?_⟩
          have hpcq : p' * (starRingEnd ℂ) q' = (starRingEnd ℂ) t := by
            rw [htdef, map_mul, Complex.conj_conj, mul_comm]
          have htt : (starRingEnd ℂ) t * t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
            rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
          have hval : p' * (starRingEnd ℂ) q' * (s * s) = (‖t‖ : ℂ) := by
            rw [hpcq, ← hs, ← mul_div_assoc, htt]
            rw [div_eq_iff (by exact_mod_cast htnorm)]
            push_cast; ring
          rw [hval]
          have hnormt : ‖t‖ = ‖p'‖ * ‖q'‖ := by
            rw [htdef, Complex.norm_mul, Complex.norm_conj]
          rw [Complex.ofReal_re, hnormt]
      have key : ‖Lpq p' q' w₀‖ = ‖p'‖ + ‖q'‖ := by
        have hw₀ns : Complex.normSq w₀ = 1 := by
          rw [Complex.normSq_eq_norm_sq, hw₀norm]; norm_num
        have hcrossterm : (p' * w₀ * (starRingEnd ℂ) (q' * (starRingEnd ℂ) w₀)).re
            = ‖p'‖ * ‖q'‖ := by
          rw [map_mul, Complex.conj_conj]
          have hr : p' * w₀ * ((starRingEnd ℂ) q' * w₀)
              = p' * (starRingEnd ℂ) q' * (w₀ * w₀) := by ring
          rw [hr, hcross]
        have hpns : Complex.normSq p' = ‖p'‖ ^ 2 := Complex.normSq_eq_norm_sq p'
        have hqns : Complex.normSq q' = ‖q'‖ ^ 2 := Complex.normSq_eq_norm_sq q'
        have hnsq : ‖Lpq p' q' w₀‖ ^ 2 = (‖p'‖ + ‖q'‖) ^ 2 := by
          rw [hLpqapp p' q' w₀, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
            Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_conj,
            hw₀ns, hcrossterm, hpns, hqns]
          ring
        have hnn : (0 : ℝ) ≤ ‖p'‖ + ‖q'‖ := by positivity
        nlinarith [norm_nonneg (Lpq p' q' w₀), hnsq, hnn]
      calc ‖p'‖ + ‖q'‖ = ‖Lpq p' q' w₀‖ := key.symm
        _ ≤ ‖Lpq p' q'‖ * ‖w₀‖ := (Lpq p' q').le_opNorm w₀
        _ = ‖Lpq p' q'‖ := by rw [hw₀norm, mul_one]
    exact le_antisymm hub hlb
  -- `A = Lpq p q`.
  have hALpq : A = Lpq p q := by
    ext w; rw [hAval w, hLpqapp p q w]
  -- The inverse map: `B := Lpq (conj p / d) (-q / d)`.
  set p' : ℂ := (starRingEnd ℂ) p / (d : ℂ) with hp'def
  set q' : ℂ := -q / (d : ℂ) with hq'def
  set B : ℂ →L[ℝ] ℂ := Lpq p' q' with hBdef
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  -- `‖p‖² − ‖q‖² = d` as complex numbers via `mul_conj`.
  have hppc : p * (starRingEnd ℂ) p = ((‖p‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hqqc : q * (starRingEnd ℂ) q = ((‖q‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hdC2 : ((‖p‖ ^ 2 : ℝ) : ℂ) - ((‖q‖ ^ 2 : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_sub]; exact_mod_cast (hddef.symm)
  -- The cancellation identity, in `ℂ`: `conj p * p - q * conj q = d`.
  have hcancel : (starRingEnd ℂ) p * p - q * (starRingEnd ℂ) q = (d : ℂ) := by
    rw [mul_comm ((starRingEnd ℂ) p) p, hppc, hqqc, hdC2]
  -- Two-sided inverse: `B ∘ A = id`.
  have hBA : B.comp A = ContinuousLinearMap.id ℝ ℂ := by
    ext w
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_id', id_eq]
    rw [hBdef, hLpqapp p' q' (A w), hAval w, hp'def, hq'def]
    have hconjdist : (starRingEnd ℂ) (p * w + q * (starRingEnd ℂ) w)
        = (starRingEnd ℂ) p * (starRingEnd ℂ) w + (starRingEnd ℂ) q * w := by
      simp [map_add, map_mul]
    rw [hconjdist]
    field_simp
    linear_combination w * hcancel
  -- Two-sided inverse: `A ∘ B = id`.
  have hAB : A.comp B = ContinuousLinearMap.id ℝ ℂ := by
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_id', id_eq]
    rw [hAval (B v), hBdef, hLpqapp p' q' v, hp'def, hq'def]
    have hconjdist : (starRingEnd ℂ) ((starRingEnd ℂ) p / (d : ℂ) * v
          + -q / (d : ℂ) * (starRingEnd ℂ) v)
        = p / (d : ℂ) * (starRingEnd ℂ) v + -(starRingEnd ℂ) q / (d : ℂ) * v := by
      simp [map_add, map_mul, map_div₀, Complex.conj_ofReal]
    rw [hconjdist]
    field_simp
    linear_combination v * hcancel
  -- Identify the inverse with `B`.
  have hinv : ContinuousLinearMap.inverse A = B :=
    ContinuousLinearMap.inverse_eq hAB hBA
  -- Compute `‖B‖ = ‖p'‖ + ‖q'‖ = (‖p‖ + ‖q‖) / d`.
  have hnormp' : ‖p'‖ = ‖p‖ / d := by
    rw [hp'def, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hdpos.le]
  have hnormq' : ‖q'‖ = ‖q‖ / d := by
    rw [hq'def, norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg hdpos.le]
  rw [hA, hinv, hBdef, opNormLpq p' q', hnormp', hnormq', hp, hq, hd, hA]
  rw [← add_div]

/-- **A.e. differentiability of the analytic quasiconformal definition.** A map
satisfying `IsQCAnalytic` is differentiable almost everywhere. This is immediate
from the orientation-preserving condition `∀ᵐ z, 0 < det (fderiv ℝ f z)`: where `f`
fails to be differentiable, `fderiv ℝ f z = 0` has determinant `0`, so the
strict positivity forces differentiability. (The substantive Gehring–Lehto content
— that a *geometrically* quasiconformal map is a.e. differentiable — is discharged
inside the geometric ⇒ analytic direction of the equivalence, where this condition
must be produced rather than assumed.) -/
theorem IsQCAnalytic.ae_differentiableAt {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∀ᵐ z, DifferentiableAt ℝ f z := by
  filter_upwards [hf.1.2] with z hz
  by_contra hnd
  rw [fderiv_zero_of_not_differentiableAt hnd] at hz
  simp [ContinuousLinearMap.det] at hz

/-- **A zero-modulus subfamily is negligible.** Removing a curve subfamily of zero
modulus from a family does not change its modulus. -/
theorem curveModulus_sdiff_modulus_zero {Γ Γ' : Set (ℝ → ℂ)} (h : Γ' ⊆ Γ)
    (hΓ' : curveModulus Γ' = 0) :
    curveModulus (Γ \ Γ') = curveModulus Γ := by
  -- `Γ \ Γ' ⊆ Γ`, so one inequality is monotonicity.
  refine le_antisymm (curveModulus_mono Set.sdiff_subset) ?_
  -- For the substantive direction, bound `curveModulus Γ` by the energy of every
  -- density admissible for `Γ \ Γ'`, then take the infimum.
  refine le_iInf₂ ?_
  rintro ρ ⟨hρmeas, hρadm⟩
  -- Abbreviation: the "root energy" of a density.
  set Eρ : ℝ≥0∞ := (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2) with hEρ
  -- Algebraic facts about the square-root exponent.
  have hsqrt_sq : ∀ x : ℝ≥0∞, (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  -- It suffices to prove `(curveModulus Γ) ^ (1/2) ≤ Eρ`; then square both sides.
  have hroot : (curveModulus Γ) ^ ((1 : ℝ) / 2) ≤ Eρ := by
    -- We show `M^(1/2) ≤ Eρ + ε` for every positive real `ε`, then use the
    -- `ENNReal` Archimedean lemma.
    refine ENNReal.le_of_forall_pos_le_add (fun ε hεpos _ => ?_)
    -- From `curveModulus Γ' = 0 < ε²`, extract `σ` admissible for `Γ'` with small energy.
    have hlt : curveModulus Γ' < (ε : ℝ≥0∞) ^ 2 := by
      rw [hΓ']; positivity
    rw [curveModulus, iInf_lt_iff] at hlt
    obtain ⟨σ, hlt2⟩ := hlt
    rw [iInf_lt_iff] at hlt2
    obtain ⟨⟨hσmeas, hσadm⟩, hσenergy⟩ := hlt2
    -- `ρ + σ` is admissible for `Γ`.
    have hsum_meas : Measurable (fun z => ρ z + σ z) := hρmeas.add hσmeas
    have hsum_adm : IsAdmissibleDensity (fun z => ρ z + σ z) Γ := by
      refine ⟨hsum_meas, fun γ hγ => ?_⟩
      -- `Γ = (Γ \ Γ') ∪ Γ'`, since `Γ' ⊆ Γ`; case on which piece `γ` lies in.
      rw [← Set.sdiff_union_of_subset h] at hγ
      rcases hγ with hγΓdiff | hγΓ'
      · -- `γ ∈ Γ \ Γ'`; use `ρ`-admissibility.
        refine le_trans (hρadm γ hγΓdiff) ?_
        unfold arcLengthLineIntegral
        refine lintegral_mono fun t => ?_
        gcongr
        exact le_self_add
      · -- `γ ∈ Γ'`; use `σ`-admissibility.
        refine le_trans (hσadm γ hγΓ') ?_
        unfold arcLengthLineIntegral
        refine lintegral_mono fun t => ?_
        gcongr
        exact le_add_self
    -- Energy bound via Minkowski (`p = 2`).
    have hMink : (∫⁻ z, (ρ z + σ z) ^ 2) ^ ((1 : ℝ) / 2)
        ≤ Eρ + (∫⁻ z, (σ z) ^ 2) ^ ((1 : ℝ) / 2) := by
      have := ENNReal.lintegral_Lp_add_le (μ := volume) (p := 2)
        hρmeas.aemeasurable hσmeas.aemeasurable (by norm_num)
      simpa only [Pi.add_apply, ENNReal.rpow_two, hEρ] using this
    -- `(∫⁻ σ²)^(1/2) ≤ ε` from `∫⁻ σ² < ε²`.
    have hσroot : (∫⁻ z, (σ z) ^ 2) ^ ((1 : ℝ) / 2) ≤ (ε : ℝ≥0∞) := by
      calc (∫⁻ z, (σ z) ^ 2) ^ ((1 : ℝ) / 2)
          ≤ ((ε : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2) := by
            have : (∫⁻ z, (σ z) ^ 2) ≤ (ε : ℝ≥0∞) ^ 2 := hσenergy.le
            gcongr
        _ = (ε : ℝ≥0∞) := by
            rw [← ENNReal.rpow_natCast (ε : ℝ≥0∞) 2, ← ENNReal.rpow_mul]
            norm_num
    -- Chain: `M ≤ ∫⁻ (ρ+σ)²`, then take roots and combine.
    have hM_le : curveModulus Γ ≤ ∫⁻ z, (ρ z + σ z) ^ 2 :=
      iInf₂_le (fun z => ρ z + σ z) hsum_adm
    calc (curveModulus Γ) ^ ((1 : ℝ) / 2)
        ≤ (∫⁻ z, (ρ z + σ z) ^ 2) ^ ((1 : ℝ) / 2) := by gcongr
      _ ≤ Eρ + (∫⁻ z, (σ z) ^ 2) ^ ((1 : ℝ) / 2) := hMink
      _ ≤ Eρ + (ε : ℝ≥0∞) := by gcongr
  -- Square the root inequality to conclude.
  calc curveModulus Γ
      = ((curveModulus Γ) ^ ((1 : ℝ) / 2)) ^ 2 := (hsqrt_sq _).symm
    _ ≤ Eρ ^ 2 := by gcongr
    _ = ∫⁻ z, (ρ z) ^ 2 := hsqrt_sq _

/-- **Subadditivity for null families.** The union of two zero-modulus curve
families is again a zero-modulus family. (Special case of countable subadditivity
of the modulus; the only instance the length–area transfer consumes.) -/
theorem curveModulus_union_zero {Γ₁ Γ₂ : Set (ℝ → ℂ)}
    (h₁ : curveModulus Γ₁ = 0) (h₂ : curveModulus Γ₂ = 0) :
    curveModulus (Γ₁ ∪ Γ₂) = 0 := by
  -- The square-root exponent and its inverse on `ℝ≥0∞`.
  have hsqrt_sq : ∀ x : ℝ≥0∞, (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  -- It suffices to show the *root energy* `M^(1/2) = 0`; then square.
  suffices hroot0 : (curveModulus (Γ₁ ∪ Γ₂)) ^ ((1 : ℝ) / 2) = 0 by
    have := hsqrt_sq (curveModulus (Γ₁ ∪ Γ₂))
    rw [hroot0] at this; simpa using this.symm
  -- Show `M^(1/2) ≤ ε` for every positive real `ε`, hence `= 0`.
  refine le_antisymm ?_ (zero_le)
  refine ENNReal.le_of_forall_pos_le_add (fun ε hεpos _ => ?_)
  rw [zero_add]
  -- Extract, from `curveModulus Γᵢ = 0 < (ε/2)²`, densities `ρᵢ` admissible for `Γᵢ`
  -- with root energy `≤ ε/2`.  Work with the half `η := (ε : ℝ≥0∞)/2 > 0`.
  set η : ℝ≥0∞ := (ε : ℝ≥0∞) / 2 with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; exact ENNReal.div_pos (by exact_mod_cast hεpos.ne') (by norm_num)
  have hηsum : η + η = (ε : ℝ≥0∞) := by
    rw [hηdef, ENNReal.add_halves]
  have extract : ∀ {Γ : Set (ℝ → ℂ)}, curveModulus Γ = 0 →
      ∃ ρ : ℂ → ℝ≥0∞, IsAdmissibleDensity ρ Γ ∧
        (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2) ≤ η := by
    intro Γ hΓ
    have hlt : curveModulus Γ < η ^ 2 := by
      rw [hΓ]; positivity
    rw [curveModulus, iInf_lt_iff] at hlt
    obtain ⟨ρ, hlt2⟩ := hlt
    rw [iInf_lt_iff] at hlt2
    obtain ⟨hρadm, hρenergy⟩ := hlt2
    refine ⟨ρ, hρadm, ?_⟩
    calc (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2)
        ≤ (η ^ 2) ^ ((1 : ℝ) / 2) := by gcongr
      _ = η := by
          rw [← ENNReal.rpow_natCast η 2, ← ENNReal.rpow_mul]
          norm_num
  obtain ⟨ρ, ⟨hρmeas, hρadm⟩, hρroot⟩ := extract h₁
  obtain ⟨σ, ⟨hσmeas, hσadm⟩, hσroot⟩ := extract h₂
  -- `ρ + σ` is admissible for `Γ₁ ∪ Γ₂`.
  have hsum_meas : Measurable (fun z => ρ z + σ z) := hρmeas.add hσmeas
  have hsum_adm : IsAdmissibleDensity (fun z => ρ z + σ z) (Γ₁ ∪ Γ₂) := by
    refine ⟨hsum_meas, fun γ hγ => ?_⟩
    rcases hγ with hγ1 | hγ2
    · refine le_trans (hρadm γ hγ1) ?_
      unfold arcLengthLineIntegral
      exact lintegral_mono fun t => by gcongr; exact le_self_add
    · refine le_trans (hσadm γ hγ2) ?_
      unfold arcLengthLineIntegral
      exact lintegral_mono fun t => by gcongr; exact le_add_self
  -- Minkowski (`p = 2`) bounds the root energy of `ρ + σ`.
  have hMink : (∫⁻ z, (ρ z + σ z) ^ 2) ^ ((1 : ℝ) / 2)
      ≤ (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2) + (∫⁻ z, (σ z) ^ 2) ^ ((1 : ℝ) / 2) := by
    have := ENNReal.lintegral_Lp_add_le (μ := volume) (p := 2)
      hρmeas.aemeasurable hσmeas.aemeasurable (by norm_num)
    simpa only [Pi.add_apply, ENNReal.rpow_two] using this
  -- Chain: `curveModulus (Γ₁ ∪ Γ₂) ≤ ∫⁻ (ρ+σ)²`, take roots, combine.
  have hM_le : curveModulus (Γ₁ ∪ Γ₂) ≤ ∫⁻ z, (ρ z + σ z) ^ 2 :=
    iInf₂_le (fun z => ρ z + σ z) hsum_adm
  calc (curveModulus (Γ₁ ∪ Γ₂)) ^ ((1 : ℝ) / 2)
      ≤ (∫⁻ z, (ρ z + σ z) ^ 2) ^ ((1 : ℝ) / 2) := by gcongr
    _ ≤ (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2) + (∫⁻ z, (σ z) ^ 2) ^ ((1 : ℝ) / 2) := hMink
    _ ≤ η + η := by gcongr
    _ = (ε : ℝ≥0∞) := hηsum

/-- **Curves meeting a null set have zero modulus (weighted form).** If `N ⊆ ℂ`
is Lebesgue-null and measurable, then the family of curves whose *arc-length*
measure of the contact set `{t | γ t ∈ N}` is positive — equivalently, those `γ`
with `1 ≤ ∫₀¹ (∞ · 𝟙_N)(γ t) ‖γ' t‖ dt` — has zero modulus. The witnessing density
is `∞ · 𝟙_N`: it is admissible by hypothesis and has zero energy because
`∫⁻ (∞ · 𝟙_N)² = ∞ · volume N = 0`. -/
theorem curveModulus_meetsNullSet_zero {N : Set ℂ} (hNmeas : MeasurableSet N)
    (hNnull : volume N = 0) (Γ : Set (ℝ → ℂ)) :
    curveModulus {γ ∈ Γ | 1 ≤ arcLengthLineIntegral (N.indicator (fun _ => ∞)) γ} = 0 := by
  -- The density `ρ_N := ∞ · 𝟙_N`.
  set ρN : ℂ → ℝ≥0∞ := N.indicator (fun _ => ∞) with hρN
  -- Measurability of `ρ_N`.
  have hρNmeas : Measurable ρN := by
    rw [hρN]; exact (measurable_const).indicator hNmeas
  -- `ρ_N` is admissible for the exceptional family (admissibility is the very
  -- defining condition of the family).
  have hadm : IsAdmissibleDensity ρN
      {γ ∈ Γ | 1 ≤ arcLengthLineIntegral ρN γ} := by
    refine ⟨hρNmeas, fun γ hγ => hγ.2⟩
  -- The energy of `ρ_N` is zero: `∫⁻ (∞ · 𝟙_N)² = ∫⁻_N ∞ = ∞ · volume N = 0`.
  have henergy : ∫⁻ z, (ρN z) ^ 2 = 0 := by
    have hpt : (fun z => (ρN z) ^ 2) = N.indicator (fun _ => ∞) := by
      funext z; rw [hρN]
      by_cases hz : z ∈ N
      · simp only [Set.indicator_of_mem hz]
        exact ENNReal.top_pow (by norm_num)
      · simp only [Set.indicator_of_notMem hz]
        norm_num
    rw [hpt, lintegral_indicator hNmeas, setLIntegral_measure_zero _ _ hNnull]
  -- The modulus is bounded by this zero energy.
  refine le_antisymm ?_ (zero_le)
  calc curveModulus {γ ∈ Γ | 1 ≤ arcLengthLineIntegral ρN γ}
      ≤ ∫⁻ z, (ρN z) ^ 2 := iInf₂_le ρN hadm
    _ = 0 := henergy

/-- **Finite-energy density with infinite line integral ⇒ zero modulus.** If a
measurable density `ρ₀` has *finite* energy `∫⁻ ρ₀² < ∞` and its arc-length line
integral is infinite along every curve of a family `Δ`, then `Δ` has zero modulus.

For each `k ≥ 1` the truncated density `ρ₀/k` is admissible for `Δ`: its line
integral is `(1/k)·∞ = ∞ ≥ 1`. Its energy is `∫⁻ (ρ₀/k)² = (1/k²)·∫⁻ ρ₀²`, so
`curveModulus Δ ≤ (∫⁻ ρ₀²)·(1/k²)` for every `k`; the right-hand side tends to `0`
as `k → ∞` (finiteness of `∫⁻ ρ₀²` is what makes the limit `0`), giving the claim.
This is the elementary `ℝ≥0∞` core of Fuglede's modulus estimate. -/
theorem curveModulus_zero_of_lintegralSq_finite {ρ₀ : ℂ → ℝ≥0∞}
    (hρ₀meas : Measurable ρ₀) (hρ₀fin : ∫⁻ z, (ρ₀ z) ^ 2 ≠ ∞)
    {Δ : Set (ℝ → ℂ)} (hΔ : ∀ γ ∈ Δ, arcLengthLineIntegral ρ₀ γ = ∞) :
    curveModulus Δ = 0 := by
  -- The energy of `ρ₀`.
  set C : ℝ≥0∞ := ∫⁻ z, (ρ₀ z) ^ 2 with hC
  -- For each natural `k ≥ 1`, the truncated density `ρ₀/k` is admissible and has
  -- energy `C·(k⁻¹)²`.  Hence `curveModulus Δ ≤ C·(k⁻¹)²` eventually.
  have hbound : ∀ k : ℕ, 1 ≤ k → curveModulus Δ ≤ C * ((k : ℝ≥0∞))⁻¹ ^ 2 := by
    intro k hkpos
    -- The truncated density `ρ_k := ρ₀/k`.
    set ρk : ℂ → ℝ≥0∞ := fun z => ρ₀ z / (k : ℝ≥0∞) with hρk
    have hkne : (k : ℝ≥0∞) ≠ 0 := by
      simp only [Ne, Nat.cast_eq_zero]; omega
    have hρkmeas : Measurable ρk := by
      rw [hρk]; exact hρ₀meas.div_const _
    -- Admissibility: `ALI (ρ₀/k) γ = (1/k)·ALI ρ₀ γ = (1/k)·∞ = ∞ ≥ 1`.
    have hadm : IsAdmissibleDensity ρk Δ := by
      refine ⟨hρkmeas, fun γ hγ => ?_⟩
      have hALI : arcLengthLineIntegral ρk γ = ∞ := by
        unfold arcLengthLineIntegral
        have hpt : (fun t => ρk (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞))
            = fun t => ((k : ℝ≥0∞))⁻¹ * (ρ₀ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)) := by
          funext t; simp only [hρk, ENNReal.div_eq_inv_mul]; ring
        rw [hpt, lintegral_const_mul' _ _ (by simp [hkne])]
        have hinf : (∫⁻ t in Set.Icc (0 : ℝ) 1, ρ₀ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)) = ∞ :=
          hΔ γ hγ
        rw [hinf, ENNReal.mul_top (by simp)]
      rw [hALI]; exact le_top
    -- Energy: `∫⁻ (ρ₀/k)² = (k⁻¹)²·C`.
    have henergy : ∫⁻ z, (ρk z) ^ 2 = C * ((k : ℝ≥0∞))⁻¹ ^ 2 := by
      have hpt : (fun z => (ρk z) ^ 2)
          = fun z => ((k : ℝ≥0∞))⁻¹ ^ 2 * (ρ₀ z) ^ 2 := by
        funext z; simp only [hρk, ENNReal.div_eq_inv_mul, mul_pow]
      rw [hpt, lintegral_const_mul' _ _ (by simp [hkne]), mul_comm, hC]
    calc curveModulus Δ
        ≤ ∫⁻ z, (ρk z) ^ 2 := iInf₂_le ρk hadm
      _ = C * ((k : ℝ≥0∞))⁻¹ ^ 2 := henergy
  -- The bound `C·(k⁻¹)² → C·0 = 0` as `k → ∞`, so `curveModulus Δ ≤ 0`.
  refine le_antisymm ?_ (zero_le)
  have htend : Filter.Tendsto (fun k : ℕ => C * ((k : ℝ≥0∞))⁻¹ ^ 2) Filter.atTop
      (nhds (C * 0)) :=
    ENNReal.Tendsto.const_mul
      (by simpa using ENNReal.Tendsto.pow (n := 2) ENNReal.tendsto_inv_nat_nhds_zero)
      (Or.inr hρ₀fin)
  rw [mul_zero] at htend
  refine ge_of_tendsto htend ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk using hbound k hk

/-- **Fuglede modulus estimate with a positive uniform lower bound.** If a finite-energy density
`ρ₀` has line integral bounded below by a positive constant `c` (`c ≤ ∫_γ ρ₀` for every `γ ∈ Δ`),
then the modulus of `Δ` is at most `(∫ ρ₀²) / c²`. The density `ρ₀ / c` is admissible for `Δ` with
energy `(∫ ρ₀²) / c²`. Quantitative form of `curveModulus_zero_of_lintegralSq_finite`, used to bound
the exceptional family in the bounded-density approximation. -/
theorem curveModulus_le_of_lintegralSq_finite_of_lineIntegral_ge {ρ₀ : ℂ → ℝ≥0∞}
    (hρ₀meas : Measurable ρ₀) {c : ℝ≥0∞} (hc : 0 < c) (hctop : c ≠ ∞)
    {Δ : Set (ℝ → ℂ)} (hΔ : ∀ γ ∈ Δ, c ≤ arcLengthLineIntegral ρ₀ γ) :
    curveModulus Δ ≤ (∫⁻ z, (ρ₀ z) ^ 2) / c ^ 2 := by
  -- The energy of `ρ₀`.
  set C : ℝ≥0∞ := ∫⁻ z, (ρ₀ z) ^ 2 with hC
  have hcne : c ≠ 0 := hc.ne'
  -- The rescaled density `ρk := ρ₀ / c` is admissible for `Δ`.
  set ρk : ℂ → ℝ≥0∞ := fun z => ρ₀ z / c with hρk
  have hρkmeas : Measurable ρk := by rw [hρk]; exact hρ₀meas.div_const _
  have hcinv_ne : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hctop
  have hcinv_top : c⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hcne
  -- Admissibility: `ALI (ρ₀/c) γ = c⁻¹ · ALI ρ₀ γ ≥ c⁻¹ · c = 1`.
  have hadm : IsAdmissibleDensity ρk Δ := by
    refine ⟨hρkmeas, fun γ hγ => ?_⟩
    have hALI : arcLengthLineIntegral ρk γ = c⁻¹ * arcLengthLineIntegral ρ₀ γ := by
      unfold arcLengthLineIntegral
      have hpt : (fun t => ρk (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞))
          = fun t => c⁻¹ * (ρ₀ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)) := by
        funext t; simp only [hρk, ENNReal.div_eq_inv_mul]; ring
      rw [hpt, lintegral_const_mul' _ _ hcinv_top]
    rw [hALI]
    calc (1 : ℝ≥0∞) = c⁻¹ * c := (ENNReal.inv_mul_cancel hcne hctop).symm
      _ ≤ c⁻¹ * arcLengthLineIntegral ρ₀ γ := by gcongr; exact hΔ γ hγ
  -- Energy: `∫⁻ (ρ₀/c)² = C · (c⁻¹)² = C / c²`.
  have henergy : ∫⁻ z, (ρk z) ^ 2 = C / c ^ 2 := by
    have hpt : (fun z => (ρk z) ^ 2) = fun z => c⁻¹ ^ 2 * (ρ₀ z) ^ 2 := by
      funext z; simp only [hρk, ENNReal.div_eq_inv_mul, mul_pow]
    rw [hpt, lintegral_const_mul' _ _ (by simp [hcinv_top]), ← hC,
      ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow]
  calc curveModulus Δ
      ≤ ∫⁻ z, (ρk z) ^ 2 := iInf₂_le ρk hadm
    _ = C / c ^ 2 := henergy

/-- **Fuglede line-integral convergence (the modulus-a.e. core).** Let `G n` be a
sequence of nonnegative measurable densities whose `L²` norms have summable roots,
`∑ₙ (∫⁻ (G n)²)^{1/2} < ∞`. Then, along every family `Γ` of continuous curves, the
subfamily on which the arc-length line integrals `∫_γ (G n) ds` fail to tend to `0`
has zero modulus.

This is the elementary form of Fuglede's theorem on the plane, and it is the bridge
that turns the mollification `L²`-convergence of a Sobolev gradient into
*modulus-a.e.* convergence of its trace along curves — sidestepping the coarea
formula entirely. The proof is the classical finite-energy-density argument: set
`ρ₀ := ∑ₙ G n`. By the countable Minkowski inequality for `∫⁻ ρ₀²`
(monotone limit of the finite `eLpNorm_sum_le`) the summable-roots hypothesis makes
`∫⁻ ρ₀² < ∞`. For a continuous curve `γ`, additivity of the line integral
(`lintegral_tsum`, using continuity of `γ` for measurability of `G n ∘ γ`) gives
`arcLengthLineIntegral ρ₀ γ = ∑ₙ arcLengthLineIntegral (G n) γ`; hence whenever the
summands fail to tend to `0`, the sum is `∞`. So the bad subfamily is contained in
`{γ | arcLengthLineIntegral ρ₀ γ = ∞}`, which has zero modulus by
`curveModulus_zero_of_lintegralSq_finite`; conclude by `curveModulus_mono`. -/
theorem curveModulus_lineIntegral_not_tendsto_zero {G : ℕ → ℂ → ℝ≥0∞}
    (hGmeas : ∀ n, Measurable (G n))
    (hsum : ∑' n, (∫⁻ z, (G n z) ^ 2) ^ (1 / 2 : ℝ) ≠ ∞)
    {Γ : Set (ℝ → ℂ)} (hΓcont : ∀ γ ∈ Γ, Continuous γ) :
    curveModulus {γ ∈ Γ | ¬ Filter.Tendsto
        (fun n => arcLengthLineIntegral (G n) γ) Filter.atTop (nhds 0)} = 0 := by
  classical
  -- The square-root exponent inverts squaring (both directions on `ℝ≥0∞`).
  have hsqrt_sq : ∀ x : ℝ≥0∞, (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  have hsq_sqrt : ∀ x : ℝ≥0∞, (x ^ 2) ^ ((1 : ℝ) / 2) = x := by
    intro x
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  -- The "root energy" of a density.
  set rootE : (ℂ → ℝ≥0∞) → ℝ≥0∞ := fun ρ => (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2) with hrootE
  -- ===================================================================
  -- Step 2: countable Minkowski for `L²` of `ℝ≥0∞`-valued functions.
  -- Built from the binary `lintegral_Lp_add_le` by a `Finset` induction
  -- and monotone convergence (`tsum = ⨆ finite sums`).
  -- ===================================================================
  -- Finite Minkowski: `rootE (∑_{n∈s} ρₙ) ≤ ∑_{n∈s} rootE ρₙ`.
  have finMink : ∀ {ρ : ℕ → ℂ → ℝ≥0∞}, (∀ n, Measurable (ρ n)) →
      ∀ s : Finset ℕ, rootE (fun z => ∑ n ∈ s, ρ n z) ≤ ∑ n ∈ s, rootE (ρ n) := by
    intro ρ hρmeas s
    classical
    induction s using Finset.induction with
    | empty => simp only [Finset.sum_empty, hrootE]; simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        have hbin : rootE (fun z => ρ a z + ∑ n ∈ s, ρ n z)
            ≤ rootE (ρ a) + rootE (fun z => ∑ n ∈ s, ρ n z) := by
          have hsummeas : Measurable (fun z => ∑ n ∈ s, ρ n z) :=
            Finset.measurable_sum s (fun n _ => hρmeas n)
          have := ENNReal.lintegral_Lp_add_le (μ := volume) (p := 2)
            (hρmeas a).aemeasurable hsummeas.aemeasurable (by norm_num)
          simpa only [Pi.add_apply, ENNReal.rpow_two, hrootE] using this
        calc rootE (fun z => ∑ n ∈ insert a s, ρ n z)
            = rootE (fun z => ρ a z + ∑ n ∈ s, ρ n z) := by
              refine congrArg rootE ?_
              funext z; rw [Finset.sum_insert ha]
          _ ≤ rootE (ρ a) + rootE (fun z => ∑ n ∈ s, ρ n z) := hbin
          _ ≤ rootE (ρ a) + ∑ n ∈ s, rootE (ρ n) := by gcongr
  -- Countable Minkowski: `rootE (∑' n, ρₙ) ≤ ∑' n, rootE ρₙ`.
  have tsumMink : ∀ {ρ : ℕ → ℂ → ℝ≥0∞}, (∀ n, Measurable (ρ n)) →
      rootE (fun z => ∑' n, ρ n z) ≤ ∑' n, rootE (ρ n) := by
    intro ρ hρmeas
    have hsq_cont : Continuous (fun x : ℝ≥0∞ => x ^ 2) := by continuity
    have hsq_mono : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => by
      simpa using pow_le_pow_left' hab 2
    have hpartialsup : (∫⁻ z, (∑' n, ρ n z) ^ 2)
        = ⨆ N : ℕ, ∫⁻ z, (∑ n ∈ Finset.range N, ρ n z) ^ 2 := by
      have hsq_eq : (fun z => (∑' n, ρ n z) ^ 2)
          = fun z => ⨆ N : ℕ, (∑ n ∈ Finset.range N, ρ n z) ^ 2 := by
        funext z
        rw [ENNReal.tsum_eq_iSup_nat]
        exact hsq_mono.map_iSup_of_continuousAt hsq_cont.continuousAt (by simp)
      rw [hsq_eq]
      rw [lintegral_iSup
        (fun N => (Finset.measurable_sum (Finset.range N) (fun n _ => hρmeas n)).pow_const 2) ?_]
      intro N M hNM z
      exact hsq_mono (Finset.sum_le_sum_of_subset (Finset.range_mono hNM))
    have henergy_le : (∫⁻ z, (∑' n, ρ n z) ^ 2) ≤ (∑' n, rootE (ρ n)) ^ 2 := by
      rw [hpartialsup]
      refine iSup_le (fun N => ?_)
      calc ∫⁻ z, (∑ n ∈ Finset.range N, ρ n z) ^ 2
          = (rootE (fun z => ∑ n ∈ Finset.range N, ρ n z)) ^ 2 := by
            rw [hrootE]; rw [hsqrt_sq]
        _ ≤ (∑ n ∈ Finset.range N, rootE (ρ n)) ^ 2 := by
            gcongr; exact finMink hρmeas (Finset.range N)
        _ ≤ (∑' n, rootE (ρ n)) ^ 2 := by gcongr; exact ENNReal.sum_le_tsum (Finset.range N)
    calc rootE (fun z => ∑' n, ρ n z)
        = (∫⁻ z, (∑' n, ρ n z) ^ 2) ^ ((1 : ℝ) / 2) := rfl
      _ ≤ ((∑' n, rootE (ρ n)) ^ 2) ^ ((1 : ℝ) / 2) := by gcongr
      _ = ∑' n, rootE (ρ n) := hsq_sqrt _
  -- ===================================================================
  -- Step 1 & 2 instantiated: `ρ₀ := ∑' n, G n` has finite energy.
  -- ===================================================================
  set ρ₀ : ℂ → ℝ≥0∞ := fun z => ∑' n, G n z with hρ₀
  have hρ₀meas : Measurable ρ₀ := Measurable.tsum hGmeas
  -- `rootE (G n) = (∫⁻ (G n)²)^{1/2}`, so `hsum` says `∑' n, rootE (G n) ≠ ∞`.
  have hsum' : ∑' n, rootE (G n) ≠ ∞ := hsum
  -- Countable Minkowski: `rootE ρ₀ ≤ ∑' n, rootE (G n) < ∞`.
  have hrootE_fin : rootE ρ₀ ≠ ∞ := by
    have hle : rootE ρ₀ ≤ ∑' n, rootE (G n) := tsumMink hGmeas
    exact ne_top_of_le_ne_top hsum' hle
  -- Hence the energy `∫⁻ ρ₀² < ∞`.
  have hρ₀fin : ∫⁻ z, (ρ₀ z) ^ 2 ≠ ∞ := by
    intro hcontra
    apply hrootE_fin
    rw [hrootE]
    simp only [hcontra]
    rw [ENNReal.top_rpow_of_pos (by norm_num)]
  -- ===================================================================
  -- Step 3: line-integral additivity along a continuous curve.
  -- ===================================================================
  have hadditive : ∀ γ : ℝ → ℂ, Continuous γ →
      arcLengthLineIntegral ρ₀ γ = ∑' n, arcLengthLineIntegral (G n) γ := by
    intro γ hγcont
    unfold arcLengthLineIntegral
    -- AEMeasurability of each summand on the restricted measure.
    have hmeas_summand : ∀ n, AEMeasurable
        (fun t => G n (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞))
        (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      intro n
      have h1 : Measurable (fun t => G n (γ t)) := (hGmeas n).comp hγcont.measurable
      have h2 : Measurable (fun t : ℝ => (‖deriv γ t‖₊ : ℝ≥0∞)) :=
        (measurable_deriv γ).nnnorm.coe_nnreal_ennreal
      exact (h1.mul h2).aemeasurable
    -- Pull the tsum out of the integrand and swap with the integral.
    have hpt : (fun t => ρ₀ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞))
        = fun t => ∑' n, G n (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
      funext t
      rw [hρ₀]
      simp only
      rw [ENNReal.tsum_mul_right]
    rw [hpt, lintegral_tsum hmeas_summand]
  -- ===================================================================
  -- Step 4: the bad family lies in `{γ | arcLengthLineIntegral ρ₀ γ = ∞}`.
  -- ===================================================================
  refine curveModulus_zero_of_lintegralSq_finite hρ₀meas hρ₀fin ?_
  intro γ hγ
  obtain ⟨hγΓ, hγbad⟩ := hγ
  have hγcont : Continuous γ := hΓcont γ hγΓ
  rw [hadditive γ hγcont]
  -- If the sum were finite, its terms would tend to `0`, contradicting `hγbad`.
  by_contra hne
  apply hγbad
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hne

/-- **Countable subadditivity for null families.** A countable union of
zero-modulus curve families is again a zero-modulus family. (This is the standard
countable subadditivity of the conformal modulus, specialised to the case where
every piece is null. The binary case `curveModulus_union_zero` uses the `ρ + σ`
density and finite Minkowski; the countable case replaces the finite sum by
`∑'ₖ εₖ⁻¹-weighted` densities `ρₖ` with `∑ₖ (root energy of ρₖ) ≤ ε`, using the
countable Minkowski inequality for `∫⁻ (∑ₖ ρₖ)²`.) -/
theorem curveModulus_iUnion_zero {Γ : ℕ → Set (ℝ → ℂ)}
    (h : ∀ n, curveModulus (Γ n) = 0) :
    curveModulus (⋃ n, Γ n) = 0 := by
  classical
  -- The square-root exponent and its inverse on `ℝ≥0∞`.
  have hsqrt_sq : ∀ x : ℝ≥0∞, (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  -- ===================================================================
  -- Countable Minkowski for `L²` of `ℝ≥0∞`-valued functions.  Built from
  -- the binary case `lintegral_Lp_add_le` by a `Finset` induction and
  -- monotone convergence (`tsum = ⨆ sums`).
  -- ===================================================================
  -- Abbreviation for the "root energy" of a density.
  set rootE : (ℂ → ℝ≥0∞) → ℝ≥0∞ := fun ρ => (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2) with hrootE
  -- Finite Minkowski: `rootE (∑_{n∈s} ρₙ) ≤ ∑_{n∈s} rootE ρₙ`.
  have finMink : ∀ {ρ : ℕ → ℂ → ℝ≥0∞}, (∀ n, Measurable (ρ n)) →
      ∀ s : Finset ℕ, rootE (fun z => ∑ n ∈ s, ρ n z) ≤ ∑ n ∈ s, rootE (ρ n) := by
    intro ρ hρmeas s
    classical
    induction s using Finset.induction with
    | empty => simp only [Finset.sum_empty, hrootE]; simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        -- `rootE (ρ a + ∑_{s} ρ) ≤ rootE (ρ a) + rootE (∑_{s} ρ)` by binary Minkowski.
        have hbin : rootE (fun z => ρ a z + ∑ n ∈ s, ρ n z)
            ≤ rootE (ρ a) + rootE (fun z => ∑ n ∈ s, ρ n z) := by
          have hsummeas : Measurable (fun z => ∑ n ∈ s, ρ n z) :=
            Finset.measurable_sum s (fun n _ => hρmeas n)
          have := ENNReal.lintegral_Lp_add_le (μ := volume) (p := 2)
            (hρmeas a).aemeasurable hsummeas.aemeasurable (by norm_num)
          simpa only [Pi.add_apply, ENNReal.rpow_two, hrootE] using this
        calc rootE (fun z => ∑ n ∈ insert a s, ρ n z)
            = rootE (fun z => ρ a z + ∑ n ∈ s, ρ n z) := by
              refine congrArg rootE ?_
              funext z; rw [Finset.sum_insert ha]
          _ ≤ rootE (ρ a) + rootE (fun z => ∑ n ∈ s, ρ n z) := hbin
          _ ≤ rootE (ρ a) + ∑ n ∈ s, rootE (ρ n) := by gcongr
  -- The square-root exponent inverts squaring (the other direction).
  have hsq_sqrt : ∀ x : ℝ≥0∞, (x ^ 2) ^ ((1 : ℝ) / 2) = x := by
    intro x
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  -- Countable Minkowski: `rootE (∑' n, ρₙ) ≤ ∑' n, rootE ρₙ`.  Proved by bounding
  -- the *energy* `∫⁻ (∑' ρ)² ≤ (∑' rootE ρ)²` and then taking square roots.
  have tsumMink : ∀ {ρ : ℕ → ℂ → ℝ≥0∞}, (∀ n, Measurable (ρ n)) →
      rootE (fun z => ∑' n, ρ n z) ≤ ∑' n, rootE (ρ n) := by
    intro ρ hρmeas
    -- Squaring on `ℝ≥0∞` is continuous and monotone, hence commutes with directed sups.
    have hsq_cont : Continuous (fun x : ℝ≥0∞ => x ^ 2) := by continuity
    have hsq_mono : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => by
      simpa using pow_le_pow_left' hab 2
    -- Energy of the tsum equals the sup of energies of finite partial sums over
    -- `range N` (monotone convergence applied to `(∑_{range N} ρ)²`, monotone in `N`).
    have hpartialsup : (∫⁻ z, (∑' n, ρ n z) ^ 2)
        = ⨆ N : ℕ, ∫⁻ z, (∑ n ∈ Finset.range N, ρ n z) ^ 2 := by
      have hsq_eq : (fun z => (∑' n, ρ n z) ^ 2)
          = fun z => ⨆ N : ℕ, (∑ n ∈ Finset.range N, ρ n z) ^ 2 := by
        funext z
        rw [ENNReal.tsum_eq_iSup_nat]
        exact hsq_mono.map_iSup_of_continuousAt hsq_cont.continuousAt (by simp)
      rw [hsq_eq]
      rw [lintegral_iSup
        (fun N => (Finset.measurable_sum (Finset.range N) (fun n _ => hρmeas n)).pow_const 2) ?_]
      intro N M hNM z
      exact hsq_mono (Finset.sum_le_sum_of_subset (Finset.range_mono hNM))
    -- Bound the energy of the tsum by `(∑' rootE ρ)²`.
    have henergy_le : (∫⁻ z, (∑' n, ρ n z) ^ 2) ≤ (∑' n, rootE (ρ n)) ^ 2 := by
      rw [hpartialsup]
      refine iSup_le (fun N => ?_)
      -- `(∫⁻ (∑_range ρ)²) = (rootE (∑_range ρ))² ≤ (∑_range rootE ρ)² ≤ (∑' rootE ρ)²`.
      calc ∫⁻ z, (∑ n ∈ Finset.range N, ρ n z) ^ 2
          = (rootE (fun z => ∑ n ∈ Finset.range N, ρ n z)) ^ 2 := by
            rw [hrootE]; rw [hsqrt_sq]
        _ ≤ (∑ n ∈ Finset.range N, rootE (ρ n)) ^ 2 := by
            gcongr; exact finMink hρmeas (Finset.range N)
        _ ≤ (∑' n, rootE (ρ n)) ^ 2 := by gcongr; exact ENNReal.sum_le_tsum (Finset.range N)
    -- Take square roots.
    calc rootE (fun z => ∑' n, ρ n z)
        = (∫⁻ z, (∑' n, ρ n z) ^ 2) ^ ((1 : ℝ) / 2) := rfl
      _ ≤ ((∑' n, rootE (ρ n)) ^ 2) ^ ((1 : ℝ) / 2) := by gcongr
      _ = ∑' n, rootE (ρ n) := hsq_sqrt _
  -- ===================================================================
  -- Main argument: assemble admissible densities `ρₙ` with `rootE ρₙ ≤ ε/2^{n+1}`.
  -- ===================================================================
  -- ===================================================================
  -- Main argument: it suffices to show the *root energy*
  -- `(curveModulus (⋃ Γ n))^(1/2) = 0`; then square via `hsqrt_sq`.
  -- ===================================================================
  suffices hroot0 : (curveModulus (⋃ n, Γ n)) ^ ((1 : ℝ) / 2) = 0 by
    have := hsqrt_sq (curveModulus (⋃ n, Γ n))
    rw [hroot0] at this; simpa using this.symm
  refine le_antisymm ?_ (zero_le)
  refine ENNReal.le_of_forall_pos_le_add (fun ε hεpos _ => ?_)
  rw [zero_add]
  -- For each `n`, extract `ρₙ` admissible for `Γ n` with `rootE ρₙ ≤ ε/2^{n+1}`.
  set η : ℕ → ℝ≥0∞ := fun n => (ε : ℝ≥0∞) / 2 ^ (n + 1) with hη
  have hηpos : ∀ n, 0 < η n := by
    intro n
    rw [hη]
    exact ENNReal.div_pos (by exact_mod_cast hεpos.ne') (by simp)
  have hηsum : ∑' n, η n = (ε : ℝ≥0∞) := by
    have hgeom : ∑' n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ = 1 := by
      have hrw : (fun n : ℕ => ((2 : ℝ≥0∞) ^ (n + 1))⁻¹)
          = fun n : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) := by
        funext n; rw [ENNReal.inv_pow]
      rw [hrw, ENNReal.tsum_geometric_add_one]
      rw [ENNReal.one_sub_inv_two, inv_inv]
      rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
    calc ∑' n, η n
        = ∑' n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ * (ε : ℝ≥0∞) := by
          refine tsum_congr (fun n => ?_)
          change (ε : ℝ≥0∞) / 2 ^ (n + 1) = _
          rw [ENNReal.div_eq_inv_mul, mul_comm]
      _ = (∑' n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹) * (ε : ℝ≥0∞) := by rw [ENNReal.tsum_mul_right]
      _ = (ε : ℝ≥0∞) := by rw [hgeom, one_mul]
  have extract : ∀ n, ∃ ρ : ℂ → ℝ≥0∞, IsAdmissibleDensity ρ (Γ n) ∧ rootE ρ ≤ η n := by
    intro n
    have hlt : curveModulus (Γ n) < (η n) ^ 2 := by
      rw [h n]; exact ENNReal.pow_pos (hηpos n) 2
    rw [curveModulus, iInf_lt_iff] at hlt
    obtain ⟨ρ, hlt2⟩ := hlt
    rw [iInf_lt_iff] at hlt2
    obtain ⟨hρadm, hρenergy⟩ := hlt2
    refine ⟨ρ, hρadm, ?_⟩
    rw [hrootE]
    calc (∫⁻ z, (ρ z) ^ 2) ^ ((1 : ℝ) / 2)
        ≤ ((η n) ^ 2) ^ ((1 : ℝ) / 2) := by
            have : (∫⁻ z, (ρ z) ^ 2) ≤ (η n) ^ 2 := hρenergy.le
            gcongr
      _ = η n := by rw [← ENNReal.rpow_natCast (η n) 2, ← ENNReal.rpow_mul]; norm_num
  choose ρ hρadm hρroot using extract
  have hρmeas : ∀ n, Measurable (ρ n) := fun n => (hρadm n).1
  -- The summed density `rhoSum := ∑' n, ρₙ`.
  set rhoSum : ℂ → ℝ≥0∞ := fun z => ∑' n, ρ n z with hrhoSum
  have hrhoSum_meas : Measurable rhoSum := Measurable.tsum hρmeas
  -- `rhoSum` is admissible for `⋃ Γ n` (it dominates each `ρₙ`).
  have hrhoSum_adm : IsAdmissibleDensity rhoSum (⋃ n, Γ n) := by
    refine ⟨hrhoSum_meas, fun γ hγ => ?_⟩
    rw [Set.mem_iUnion] at hγ
    obtain ⟨n, hγn⟩ := hγ
    refine le_trans ((hρadm n).2 γ hγn) ?_
    unfold arcLengthLineIntegral
    refine lintegral_mono fun t => ?_
    gcongr
    exact ENNReal.le_tsum n
  -- Energy bound via countable Minkowski: `rootE rhoSum ≤ ∑' n, η n = ε`.
  have hrootbound : rootE rhoSum ≤ (ε : ℝ≥0∞) := by
    calc rootE rhoSum = rootE (fun z => ∑' n, ρ n z) := rfl
      _ ≤ ∑' n, rootE (ρ n) := tsumMink hρmeas
      _ ≤ ∑' n, η n := ENNReal.tsum_le_tsum hρroot
      _ = (ε : ℝ≥0∞) := hηsum
  -- Bound the root of the modulus: `(curveModulus)^(1/2) ≤ rootE rhoSum ≤ ε`.
  calc (curveModulus (⋃ n, Γ n)) ^ ((1 : ℝ) / 2)
      ≤ (∫⁻ z, (rhoSum z) ^ 2) ^ ((1 : ℝ) / 2) := by
        gcongr; exact iInf₂_le rhoSum hrhoSum_adm
    _ = rootE rhoSum := rfl
    _ ≤ (ε : ℝ≥0∞) := hrootbound

/-- **Countable subadditivity of the conformal modulus.** The modulus of a
countable union of curve families is at most the sum of their moduli:
`curveModulus (⋃ n, Γ n) ≤ ∑' n, curveModulus (Γ n)`. This is the general form of
`curveModulus_iUnion_zero` (the special case where every piece has modulus zero).

The proof uses the **ℓ²-combination** of near-optimal densities: extract for each
`n` a density `ρₙ` admissible for `Γ n` with energy `∫ρₙ² ≤ curveModulus (Γ n) +
ε/2ⁿ⁺¹`, and set `ρ = (∑' n, ρₙ²)^{1/2}`. Since `ρ ≥ ρₙ` pointwise, `ρ` is
admissible for the union; and `∫ρ² = ∑' n, ∫ρₙ²` by Tonelli, bounding the union
modulus by `∑' n, curveModulus (Γ n) + ε`. This is the standard fact that the
conformal modulus is an outer measure on curve families, and the keystone
reassembly brick for upgrading quadrilateral distortion to general curve-family
distortion. -/
theorem curveModulus_iUnion_le_tsum {Γ : ℕ → Set (ℝ → ℂ)} :
    curveModulus (⋃ n, Γ n) ≤ ∑' n, curveModulus (Γ n) := by
  classical
  -- The square-root exponent inverts squaring on `ℝ≥0∞`.
  have hsqrt_sq : ∀ x : ℝ≥0∞, (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  -- It suffices to prove the `+ ε` bound for every positive `ε`.
  refine ENNReal.le_of_forall_pos_le_add (fun ε hεpos hsum_lt => ?_)
  -- Each piece has finite modulus (the sum is finite).
  have hsum_ne : (∑' n, curveModulus (Γ n)) ≠ ⊤ := hsum_lt.ne
  have hfin : ∀ n, curveModulus (Γ n) < ⊤ := ENNReal.lt_top_of_tsum_ne_top hsum_ne
  -- The geometric weights `η n = ε / 2^{n+1}`, with `∑' η = ε`.
  set η : ℕ → ℝ≥0∞ := fun n => (ε : ℝ≥0∞) / 2 ^ (n + 1) with hη
  have hηpos : ∀ n, 0 < η n := by
    intro n
    rw [hη]
    exact ENNReal.div_pos (by exact_mod_cast hεpos.ne') (by simp)
  have hηsum : ∑' n, η n = (ε : ℝ≥0∞) := by
    have hgeom : ∑' n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ = 1 := by
      have hrw : (fun n : ℕ => ((2 : ℝ≥0∞) ^ (n + 1))⁻¹)
          = fun n : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) := by
        funext n; rw [ENNReal.inv_pow]
      rw [hrw, ENNReal.tsum_geometric_add_one]
      rw [ENNReal.one_sub_inv_two, inv_inv]
      rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
    calc ∑' n, η n
        = ∑' n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ * (ε : ℝ≥0∞) := by
          refine tsum_congr (fun n => ?_)
          change (ε : ℝ≥0∞) / 2 ^ (n + 1) = _
          rw [ENNReal.div_eq_inv_mul, mul_comm]
      _ = (∑' n : ℕ, ((2 : ℝ≥0∞) ^ (n + 1))⁻¹) * (ε : ℝ≥0∞) := by rw [ENNReal.tsum_mul_right]
      _ = (ε : ℝ≥0∞) := by rw [hgeom, one_mul]
  -- For each `n`, extract `ρₙ` admissible for `Γ n` with energy `∫ρₙ² ≤ curveModulus (Γ n) + η n`.
  have extract : ∀ n, ∃ ρ : ℂ → ℝ≥0∞, IsAdmissibleDensity ρ (Γ n) ∧
      (∫⁻ z, (ρ z) ^ 2) ≤ curveModulus (Γ n) + η n := by
    intro n
    have hlt : curveModulus (Γ n) < curveModulus (Γ n) + η n := by
      refine ENNReal.lt_add_right (hfin n).ne (hηpos n).ne'
    rw [curveModulus, iInf_lt_iff] at hlt
    obtain ⟨ρ, hlt2⟩ := hlt
    rw [iInf_lt_iff] at hlt2
    obtain ⟨hρadm, hρenergy⟩ := hlt2
    exact ⟨ρ, hρadm, hρenergy.le⟩
  choose ρ hρadm hρenergy using extract
  have hρmeas : ∀ n, Measurable (ρ n) := fun n => (hρadm n).1
  -- The ℓ²-combined density `rho = (∑' n, ρₙ²)^{1/2}`.
  set rho : ℂ → ℝ≥0∞ := fun z => (∑' n, (ρ n z) ^ 2) ^ ((1 : ℝ) / 2) with hrho
  -- Measurability of `rho`.
  have htsum_meas : Measurable (fun z => ∑' n, (ρ n z) ^ 2) :=
    Measurable.tsum (fun n => (hρmeas n).pow_const 2)
  have hrho_meas : Measurable rho := htsum_meas.pow_const ((1 : ℝ) / 2)
  -- Key pointwise fact: `(rho z)² = ∑' n, (ρₙ z)²`.
  have hrho_sq : ∀ z, (rho z) ^ 2 = ∑' n, (ρ n z) ^ 2 := by
    intro z; rw [hrho]; exact hsqrt_sq _
  -- Domination: `ρₙ z ≤ rho z` for all `n, z`.
  have hdom : ∀ n z, ρ n z ≤ rho z := by
    intro n z
    have hsq : (ρ n z) ^ 2 ≤ (rho z) ^ 2 := by
      rw [hrho_sq z]; exact ENNReal.le_tsum n
    have h1 := ENNReal.rpow_le_rpow hsq (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)
    rw [← ENNReal.rpow_natCast (ρ n z) 2, ← ENNReal.rpow_natCast (rho z) 2,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h1
    norm_num at h1
    exact h1
  -- `rho` is admissible for the union (it dominates each `ρₙ`).
  have hrho_adm : IsAdmissibleDensity rho (⋃ n, Γ n) := by
    refine ⟨hrho_meas, fun γ hγ => ?_⟩
    rw [Set.mem_iUnion] at hγ
    obtain ⟨n, hγn⟩ := hγ
    refine le_trans ((hρadm n).2 γ hγn) ?_
    unfold arcLengthLineIntegral
    refine lintegral_mono fun t => ?_
    gcongr
    exact hdom n (γ t)
  -- Energy of `rho`: `∫rho² = ∑' n, ∫ρₙ²` by Tonelli.
  have henergy_eq : (∫⁻ z, (rho z) ^ 2) = ∑' n, ∫⁻ z, (ρ n z) ^ 2 := by
    have : (∫⁻ z, (rho z) ^ 2) = ∫⁻ z, ∑' n, (ρ n z) ^ 2 := by
      refine lintegral_congr (fun z => ?_); exact hrho_sq z
    rw [this]
    exact MeasureTheory.lintegral_tsum (fun n => ((hρmeas n).pow_const 2).aemeasurable)
  -- Energy bound: `∫rho² ≤ (∑' curveModulus) + ε`.
  have henergy_bound : (∫⁻ z, (rho z) ^ 2) ≤ (∑' n, curveModulus (Γ n)) + (ε : ℝ≥0∞) := by
    rw [henergy_eq]
    calc ∑' n, ∫⁻ z, (ρ n z) ^ 2
        ≤ ∑' n, (curveModulus (Γ n) + η n) := ENNReal.tsum_le_tsum hρenergy
      _ = (∑' n, curveModulus (Γ n)) + ∑' n, η n := ENNReal.tsum_add
      _ = (∑' n, curveModulus (Γ n)) + (ε : ℝ≥0∞) := by rw [hηsum]
  -- Finish: `curveModulus (⋃ Γ) ≤ ∫rho² ≤ (∑' curveModulus) + ε`.
  refine le_trans ?_ henergy_bound
  exact iInf₂_le rho hrho_adm


end NoWanderingDomains
