/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Wirtinger derivatives `∂` and `∂̄`

For a map `f : ℂ → ℂ` the **Wirtinger derivatives** are the two complex
combinations of the real partial derivatives `∂ₓf = (fderiv ℝ f z) 1` and
`∂ᵧf = (fderiv ℝ f z) I`:

* `dz f z   = ½ (∂ₓf − i ∂ᵧf)`   (the holomorphic derivative `∂`),
* `dzbar f z = ½ (∂ₓf + i ∂ᵧf)`  (the antiholomorphic derivative `∂̄`).

They are defined directly from Mathlib's real Fréchet derivative `fderiv ℝ`,
so they are total: at a point where `f` is not real-differentiable both
return the junk value `0`.

The central fact is the **holomorphic characterization**: a real-differentiable
`f` is complex-differentiable at `z` iff `dzbar f z = 0`, which is the
Cauchy–Riemann equation `(fderiv ℝ f z) I = I • (fderiv ℝ f z) 1`
(`differentiableOn_iff_dzbar_eq_zero`). Where `f` is holomorphic the
holomorphic Wirtinger derivative agrees with the ordinary complex derivative,
`dz f z = deriv f z`.

The Wirtinger derivatives are `ℝ`-linear, satisfy the Leibniz product rule and
the chain rule `∂(g∘f) = (∂g∘f)·∂f + (∂̄g∘f)·conj(∂̄f)`, and intertwine with
complex conjugation through `dz (conj ∘ f) = conj (dzbar f)` and
`dzbar (conj ∘ f) = conj (dz f)`. These identities are the calculus the
Beltrami equation `∂̄f = μ ∂f` and the Cauchy/Beurling transforms of the
analytic engine are written in.
-/

open Complex
open scoped ComplexConjugate

namespace NoWanderingDomains

variable {f g : ℂ → ℂ} {z : ℂ} {U : Set ℂ}

/-- The Wirtinger derivative `∂f = ½(∂ₓf − i ∂ᵧf)`, built from the real
Fréchet derivative of `f` in the directions `1` and `I`. -/
noncomputable def dz (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ((fderiv ℝ f z) 1 - Complex.I * (fderiv ℝ f z) Complex.I)

/-- The Wirtinger derivative `∂̄f = ½(∂ₓf + i ∂ᵧf)`, built from the real
Fréchet derivative of `f` in the directions `1` and `I`. -/
noncomputable def dzbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ((fderiv ℝ f z) 1 + Complex.I * (fderiv ℝ f z) Complex.I)

/-- The vanishing of `∂̄f` is exactly the Cauchy–Riemann equation in the form
`(fderiv ℝ f z) I = I • (fderiv ℝ f z) 1`. -/
theorem dzbar_eq_zero_iff_fderiv :
    dzbar f z = 0 ↔ (fderiv ℝ f z) Complex.I = Complex.I • (fderiv ℝ f z) 1 := by
  rw [dzbar, smul_eq_mul]
  set D1 := (fderiv ℝ f z) 1 with hD1
  set DI := (fderiv ℝ f z) Complex.I with hDI
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (by norm_num)
    · -- D1 + I * DI = 0  ⟹  DI = I * D1
      linear_combination (-Complex.I) * h + DI * Complex.I_mul_I
  · intro h
    right
    rw [h]
    linear_combination Complex.I_mul_I * D1

/-- `∂` is additive on real-differentiable functions. -/
theorem dz_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz (fun w => f w + g w) z = dz f z + dz g z := by
  simp only [dz, fderiv_fun_add hf hg, add_apply]
  ring

/-- `∂̄` is additive on real-differentiable functions. -/
theorem dzbar_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dzbar (fun w => f w + g w) z = dzbar f z + dzbar g z := by
  simp only [dzbar, fderiv_fun_add hf hg, add_apply]
  ring

/-- **Holomorphic characterization, pointwise.** A real-differentiable function
is complex-differentiable at `z` iff its `∂̄`-derivative vanishes there. -/
theorem differentiableAt_iff_dzbar_eq_zero (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℂ f z ↔ dzbar f z = 0 := by
  rw [differentiableAt_complex_iff_differentiableAt_real, and_iff_right hf,
    ← dzbar_eq_zero_iff_fderiv]

/-- **Holomorphic characterization.** On an open set a real-differentiable
function is holomorphic iff its `∂̄`-derivative vanishes identically:
`f` holomorphic ⇔ `∂̄ f = 0`. -/
theorem differentiableOn_iff_dzbar_eq_zero (hU : IsOpen U) (hf : DifferentiableOn ℝ f U) :
    DifferentiableOn ℂ f U ↔ ∀ z ∈ U, dzbar f z = 0 := by
  constructor
  · intro hd z hz
    have hfz : DifferentiableAt ℂ f z := (hd z hz).differentiableAt (hU.mem_nhds hz)
    exact (differentiableAt_iff_dzbar_eq_zero
      (differentiableAt_complex_iff_differentiableAt_real.mp hfz).1).mp hfz
  · intro h z hz
    have hfr : DifferentiableAt ℝ f z := (hf z hz).differentiableAt (hU.mem_nhds hz)
    exact ((differentiableAt_iff_dzbar_eq_zero hfr).mpr (h z hz)).differentiableWithinAt

/-- A complex-differentiable function has vanishing `∂̄`-derivative. -/
theorem dzbar_eq_zero_of_differentiableAt (hf : DifferentiableAt ℂ f z) :
    dzbar f z = 0 := by
  exact (differentiableAt_iff_dzbar_eq_zero
    (differentiableAt_complex_iff_differentiableAt_real.mp hf).1).mp hf

/-- Where `f` is holomorphic the holomorphic Wirtinger derivative is the
ordinary complex derivative. -/
theorem dz_eq_deriv_of_differentiableAt (hf : DifferentiableAt ℂ f z) :
    dz f z = deriv f z := by
  obtain ⟨hr, hCR⟩ := differentiableAt_complex_iff_differentiableAt_real.mp hf
  rw [complexOfReal_deriv hr hCR, dz, hCR, smul_eq_mul]
  linear_combination (-1 / 2 : ℂ) * (fderiv ℝ f z) 1 * Complex.I_mul_I

/-- Conjugation intertwines `∂` and `∂̄`: `∂(conj ∘ f) = conj (∂̄ f)`. -/
theorem dz_conj (f : ℂ → ℂ) (z : ℂ) :
    dz (fun w => conj (f w)) z = conj (dzbar f z) := by
  have hd : ∀ v : ℂ, (fderiv ℝ (fun w => conj (f w)) z) v = conj ((fderiv ℝ f z) v) := by
    intro v
    have heq : (fun w => conj (f w)) = ⇑Complex.conjCLE ∘ f := by
      funext w
      simp [Function.comp]
    rw [heq, ContinuousLinearEquiv.comp_fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
  have hhalf : (starRingEnd ℂ) (1/2 : ℂ) = 1/2 := by rw [map_div₀, map_one, map_ofNat]
  simp only [dz, dzbar, hd, map_mul, map_add, Complex.conj_I, hhalf]
  ring

/-- Conjugation intertwines `∂̄` and `∂`: `∂̄(conj ∘ f) = conj (∂ f)`. -/
theorem dzbar_conj (f : ℂ → ℂ) (z : ℂ) :
    dzbar (fun w => conj (f w)) z = conj (dz f z) := by
  have hd : ∀ v : ℂ, (fderiv ℝ (fun w => conj (f w)) z) v = conj ((fderiv ℝ f z) v) := by
    intro v
    have heq : (fun w => conj (f w)) = ⇑Complex.conjCLE ∘ f := by
      funext w
      simp [Function.comp]
    rw [heq, ContinuousLinearEquiv.comp_fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
  have hhalf : (starRingEnd ℂ) (1/2 : ℂ) = 1/2 := by rw [map_div₀, map_one, map_ofNat]
  simp only [dzbar, dz, hd, map_mul, map_sub, Complex.conj_I, hhalf]
  ring

/-- Leibniz product rule for `∂`. -/
theorem dz_mul (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz (fun w => f w * g w) z = f z * dz g z + g z * dz f z := by
  have key : fderiv ℝ (fun w => f w * g w) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z :=
    fderiv_mul hf hg
  simp only [dz, key, add_apply, smul_apply, smul_eq_mul]
  ring

/-- Leibniz product rule for `∂̄`. -/
theorem dzbar_mul (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dzbar (fun w => f w * g w) z = f z * dzbar g z + g z * dzbar f z := by
  have key : fderiv ℝ (fun w => f w * g w) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z :=
    fderiv_mul hf hg
  simp only [dzbar, key, add_apply, smul_apply, smul_eq_mul]
  ring

/-- **Wirtinger chain rule for `∂`.** With `f̄ = conj ∘ f` (so `∂̄(f̄) = conj (∂̄f)`),
`∂(g∘f) = (∂g∘f)·∂f + (∂̄g∘f)·∂̄(f̄)`. -/
theorem dz_comp (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g (f z)) :
    dz (fun w => g (f w)) z = dz g (f z) * dz f z + dzbar g (f z) * conj (dzbar f z) := by
  have repr : ∀ (L : ℂ →L[ℝ] ℂ) (w : ℂ),
      L w = (1 / 2 : ℂ) * ((L 1) - I * (L I)) * w
        + (1 / 2 : ℂ) * ((L 1) + I * (L I)) * conj w := by
    intro L w
    have hLw : L w = (↑w.re : ℂ) * L 1 + (↑w.im : ℂ) * L I := by
      conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • I by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
      rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have hcw : conj w = (↑w.re : ℂ) - ↑w.im * I := by
      conv_lhs => rw [← Complex.re_add_im w]
      simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hw : w = (↑w.re : ℂ) + ↑w.im * I := (Complex.re_add_im w).symm
    rw [hLw, hcw]
    set a : ℂ := (↑w.re : ℂ) with ha
    set b : ℂ := (↑w.im : ℂ) with hb
    rw [hw]
    linear_combination (b * L I) * Complex.I_mul_I
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  have hcomp : fderiv ℝ (fun w => g (f w)) z = (fderiv ℝ g (f z)).comp (fderiv ℝ f z) :=
    fderiv_comp z hg hf
  simp only [dz, dzbar, hcomp, ContinuousLinearMap.comp_apply]
  rw [repr (fderiv ℝ g (f z)) ((fderiv ℝ f z) 1),
    repr (fderiv ℝ g (f z)) ((fderiv ℝ f z) I)]
  simp only [map_add, map_mul, Complex.conj_I, hhalf]
  ring

/-- **Wirtinger chain rule for `∂̄`.** With `f̄ = conj ∘ f` (so `∂̄(f̄) = conj (∂f)`),
`∂̄(g∘f) = (∂g∘f)·∂̄f + (∂̄g∘f)·∂̄(f̄)`. -/
theorem dzbar_comp (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g (f z)) :
    dzbar (fun w => g (f w)) z = dz g (f z) * dzbar f z + dzbar g (f z) * conj (dz f z) := by
  have repr : ∀ (L : ℂ →L[ℝ] ℂ) (w : ℂ),
      L w = (1 / 2 : ℂ) * ((L 1) - I * (L I)) * w
        + (1 / 2 : ℂ) * ((L 1) + I * (L I)) * conj w := by
    intro L w
    have hLw : L w = (↑w.re : ℂ) * L 1 + (↑w.im : ℂ) * L I := by
      conv_lhs => rw [show w = w.re • (1 : ℂ) + w.im • I by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]]
      rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have hcw : conj w = (↑w.re : ℂ) - ↑w.im * I := by
      conv_lhs => rw [← Complex.re_add_im w]
      simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hw : w = (↑w.re : ℂ) + ↑w.im * I := (Complex.re_add_im w).symm
    rw [hLw, hcw]
    set a : ℂ := (↑w.re : ℂ) with ha
    set b : ℂ := (↑w.im : ℂ) with hb
    rw [hw]
    linear_combination (b * L I) * Complex.I_mul_I
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  have hcomp : fderiv ℝ (fun w => g (f w)) z = (fderiv ℝ g (f z)).comp (fderiv ℝ f z) :=
    fderiv_comp z hg hf
  simp only [dz, dzbar, hcomp, ContinuousLinearMap.comp_apply]
  rw [repr (fderiv ℝ g (f z)) ((fderiv ℝ f z) 1),
    repr (fderiv ℝ g (f z)) ((fderiv ℝ f z) I)]
  simp only [map_sub, map_mul, Complex.conj_I, hhalf]
  ring

end NoWanderingDomains
