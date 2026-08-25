/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.DiskModel.DiskMetric
import NoWanderingDomains.Hyperbolic.ModularLambda.ModularFormsBridge
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Topology.Covering.Basic
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Ring.Int.Parity

/-! # Theta nullwerte and the modular transformations of `λ`

The theta nullwerte `θ₂`, `θ₃`, `θ₄` and the modular function `λ = (θ₂/θ₃)⁴`, with
their modular transformations under `T : τ ↦ τ + 1` and `S : τ ↦ −1/τ`, holomorphy on
`ℍ`, and the `Γ(2)`-generator identities `λ(τ + 2) = λ(τ)` and `λ(τ/(2τ+1)) = λ(τ)`.
Also the transformation laws of the Jacobi difference `θ₂⁴ + θ₄⁴ − θ₃⁴` and its square,
and the first analytic norm bounds at the cusp `i∞`, culminating in the leading-term
estimate `‖λ(τ) − 16·exp(πi τ)‖ ≤ 4096·exp(−2π·τ.im)` for `τ.im ≥ 1`.
-/

namespace NoWanderingDomains
open Complex Metric Set UpperHalfPlane CongruenceSubgroup
open scoped ModularForm Manifold MatrixGroups

/-- The half-integer theta nullwert
`θ₂(τ) = exp(πi τ / 4) · jacobiTheta₂(τ / 2, τ) = ∑ exp(πi (n + ½)² τ)`. -/
noncomputable def theta2 (τ : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ

/-- The standard theta nullwert `θ₃(τ) = jacobiTheta τ`. -/
noncomputable def theta3 (τ : ℂ) : ℂ := jacobiTheta τ

/-- The alternating-sign theta nullwert
`θ₄(τ) = ∑_{n ∈ ℤ} (-1)ⁿ exp(πi n² τ) = jacobiTheta(τ + 1)`. We take the
right-hand expression as the definition; the alternating-sign series form
is established as `jacobiTheta₂_one_half_eq_theta4` below. -/
noncomputable def theta4 (τ : ℂ) : ℂ := jacobiTheta (τ + 1)

/-- The modular function on the upper half-plane, as a map `ℂ → ℂ`. The
formula gives the correct value for `τ ∈ ℍ`; off `ℍ` the value is the
Lean junk for `0 / 0` and not mathematically meaningful. -/
noncomputable def modularLambdaH (τ : ℂ) : ℂ :=
  (theta2 τ) ^ 4 / (theta3 τ) ^ 4

/-- The modular function on the unit disk, obtained by composing
`modularLambdaH` with the Cayley transform `𝔻 → ℍ` from
`DiskMetric.lean`. -/
noncomputable def modularLambda (z : ℂ) : ℂ :=
  modularLambdaH (cayleyToHalfPlane z)

/-! ## Modular transformations under `T : τ ↦ τ + 1`

`θ₂`, `θ₃`, `θ₄` transform under `T` as follows:
- `θ₃(τ + 1) = θ₄(τ)` (immediate from the definition `θ₄(τ) := θ₃(τ + 1)`).
- `θ₄(τ + 1) = θ₃(τ)` (uses `jacobiTheta_two_add` for the period-2 invariance of `θ₃`).
- `θ₂(τ + 1) = exp(πi/4) · θ₂(τ)` (uses `jacobiTheta₂_add_half_T` below). -/

/-- Auxiliary identity for the two-variable Jacobi theta:
`jacobiTheta₂(z + ½, τ + 1) = jacobiTheta₂(z, τ)`. This follows because the
extra factor `exp(πi · n(n+1))` is `1` for every integer `n`. -/
lemma jacobiTheta₂_add_half_T (z τ : ℂ) :
    jacobiTheta₂ (z + 1 / 2) (τ + 1) = jacobiTheta₂ z τ := by
  refine tsum_congr (fun n => ?_)
  simp only [jacobiTheta₂_term]
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
  have h_int : (n : ℤ) * (n + 1) = 2 * k := by linarith
  have h_cast : (n : ℂ) * ((n : ℂ) + 1) = 2 * (k : ℂ) := by exact_mod_cast h_int
  have h_eq :
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z + 1 / 2)
        + (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ + 1)
      = (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z
          + (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ)
        + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    linear_combination (Real.pi : ℂ) * Complex.I * h_cast
  rw [h_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I k, mul_one]

/-- Identity `jacobiTheta₂(1/2, τ) = θ₄(τ)`. Both sides equal
`∑_n (−1)ⁿ exp(πi n² τ)`. -/
lemma jacobiTheta₂_one_half_eq_theta4 (τ : ℂ) :
    jacobiTheta₂ (1 / 2) τ = theta4 τ := by
  unfold theta4 jacobiTheta
  refine tsum_congr (fun n => ?_)
  simp only [jacobiTheta₂_term]
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self (n - 1)
  have h_int : (n - 1 : ℤ) * n = 2 * k := by
    have h1 : (n - 1 : ℤ) * n = (n - 1) * (n - 1 + 1) := by ring
    rw [h1]; linarith
  have h_cast : ((n : ℂ) - 1) * (n : ℂ) = 2 * (k : ℂ) := by exact_mod_cast h_int
  have h_eq :
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (1 / 2)
        + (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ
      = (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (τ + 1)
        + ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    linear_combination -((Real.pi : ℂ) * Complex.I) * h_cast
  rw [h_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I (-k), mul_one]

/-- `θ₃(τ + 1) = θ₄(τ)`. Definitional. -/
theorem theta3_add_one (τ : ℂ) : theta3 (τ + 1) = theta4 τ := rfl

/-- `θ₄(τ + 1) = θ₃(τ)`. Uses `jacobiTheta` is period-2 in its argument. -/
theorem theta4_add_one (τ : ℂ) : theta4 (τ + 1) = theta3 τ := by
  unfold theta4 theta3
  rw [show (τ + 1 + 1 : ℂ) = 2 + τ from by ring]
  exact jacobiTheta_two_add τ

/-- `θ₂(τ + 1) = exp(πi/4) · θ₂(τ)`. Uses `jacobiTheta₂_add_half_T`. -/
theorem theta2_add_one (τ : ℂ) :
    theta2 (τ + 1) = Complex.exp ((Real.pi : ℂ) * Complex.I / 4) * theta2 τ := by
  unfold theta2
  rw [show (τ + 1) / 2 = τ / 2 + 1 / 2 from by ring]
  rw [jacobiTheta₂_add_half_T (τ / 2) τ]
  rw [show (Real.pi : ℂ) * Complex.I * (τ + 1) / 4
        = (Real.pi : ℂ) * Complex.I * τ / 4 + (Real.pi : ℂ) * Complex.I / 4 from by ring]
  rw [Complex.exp_add]
  ring

/-- `θ₂(τ + 2) = i · θ₂(τ)`. Applying `theta2_add_one` twice gives the
factor `(exp(πi/4))² = exp(πi/2) = i`. -/
theorem theta2_two_add (τ : ℂ) : theta2 (τ + 2) = Complex.I * theta2 τ := by
  rw [show (τ + 2 : ℂ) = (τ + 1) + 1 from by ring]
  rw [theta2_add_one, theta2_add_one]
  rw [show Complex.exp ((Real.pi : ℂ) * Complex.I / 4)
        * (Complex.exp ((Real.pi : ℂ) * Complex.I / 4) * theta2 τ)
      = Complex.exp ((Real.pi : ℂ) * Complex.I / 4
                     + (Real.pi : ℂ) * Complex.I / 4) * theta2 τ from by
    rw [Complex.exp_add]; ring]
  rw [show ((Real.pi : ℂ) * Complex.I / 4 + (Real.pi : ℂ) * Complex.I / 4)
        = (Real.pi : ℂ) * Complex.I / 2 from by ring]
  rw [show (Real.pi : ℂ) * Complex.I / 2 = (Real.pi / 2 : ℂ) * Complex.I from by ring]
  rw [Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  simp

/-- `θ₃(τ + 2) = θ₃(τ)`. Restates `jacobiTheta_two_add` in terms of `theta3`. -/
theorem theta3_two_add (τ : ℂ) : theta3 (τ + 2) = theta3 τ := by
  unfold theta3
  rw [show (τ + 2 : ℂ) = 2 + τ from by ring]
  exact jacobiTheta_two_add τ

/-- `θ₄(τ + 2) = θ₄(τ)`. Follows from `theta4 τ = theta3(τ + 1)`
+ `theta3_two_add`. -/
theorem theta4_two_add (τ : ℂ) : theta4 (τ + 2) = theta4 τ := by
  unfold theta4
  rw [show (τ + 2 + 1 : ℂ) = (τ + 1) + 2 from by ring]
  exact theta3_two_add (τ + 1)

/-! ## Holomorphy of `θ₂`, `θ₃`, `θ₄` on `ℍ`

`jacobiTheta` is differentiable on the upper half-plane (Mathlib's
`differentiableAt_jacobiTheta`); `jacobiTheta₂` is jointly differentiable
on `ℂ × {τ : ℂ | 0 < τ.im}` (`hasFDerivAt_jacobiTheta₂`). The theta
nullwerte `θ₂`, `θ₃`, `θ₄` inherit pointwise differentiability on `ℍ`. -/

/-- `θ₃ = jacobiTheta` is differentiable at every point of `ℍ`. -/
theorem theta3_differentiableAt {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ theta3 τ := differentiableAt_jacobiTheta hτ

/-- `θ₂(τ) = exp(πi τ / 4) · jacobiTheta₂(τ / 2, τ)` is differentiable at
every point of `ℍ`. -/
theorem theta2_differentiableAt {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ theta2 τ := by
  unfold theta2
  refine DifferentiableAt.mul ?_ ?_
  · -- exp((π·I)·τ/4) is entire
    have h_inner : DifferentiableAt ℂ (fun σ : ℂ => (Real.pi : ℂ) * Complex.I * σ / 4) τ :=
      ((differentiable_id.differentiableAt).const_mul ((Real.pi : ℂ) * Complex.I)).div_const 4
    exact Complex.differentiable_exp.differentiableAt.comp τ h_inner
  · -- jacobiTheta₂(τ/2, τ) via composition
    let g : ℂ → ℂ × ℂ := fun σ => (σ / 2, σ)
    let f : ℂ × ℂ → ℂ := fun p => jacobiTheta₂ p.1 p.2
    have h_pair : DifferentiableAt ℂ g τ := by
      refine DifferentiableAt.prodMk ?_ differentiable_id.differentiableAt
      exact differentiable_id.differentiableAt.div_const 2
    have h_jt₂ : DifferentiableAt ℂ f (g τ) :=
      (hasFDerivAt_jacobiTheta₂ (τ / 2) hτ).differentiableAt
    exact h_jt₂.comp τ h_pair

/-- `θ₄(τ) = jacobiTheta(τ + 1)` is differentiable at every point of `ℍ`. -/
theorem theta4_differentiableAt {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ theta4 τ := by
  unfold theta4
  have h_shift : DifferentiableAt ℂ (fun σ : ℂ => σ + 1) τ :=
    differentiable_id.differentiableAt.add_const 1
  have h_shift_im : 0 < (τ + 1).im := by simpa [Complex.add_im] using hτ
  have h_jt : DifferentiableAt ℂ jacobiTheta (τ + 1) :=
    differentiableAt_jacobiTheta h_shift_im
  exact h_jt.comp τ h_shift

/-- **`T²`-invariance of `λ`** on the upper half-plane:
`λ(τ + 2) = λ(τ)`. The proof combines `θ₂(τ+2) = i·θ₂(τ)` with
`θ₃(τ+2) = θ₃(τ)`; raising the `θ₂/θ₃` ratio to the fourth power kills
the `i` factor since `i⁴ = 1`. -/
theorem modularLambdaH_two_add (τ : ℂ) :
    modularLambdaH (τ + 2) = modularLambdaH τ := by
  unfold modularLambdaH
  rw [theta2_two_add, theta3_two_add]
  rw [mul_pow]
  rw [show Complex.I ^ 4 = 1 from by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; ring]
  ring

/-- Subtraction-by-2 also leaves `λ` invariant (the inverse of `T²`-invariance,
needed for the `ST⁻²S` generator below). -/
theorem modularLambdaH_sub_two (τ : ℂ) :
    modularLambdaH (τ - 2) = modularLambdaH τ := by
  have h := modularLambdaH_two_add (τ - 2)
  rw [show (τ - 2 + 2 : ℂ) = τ from by ring] at h
  exact h.symm

/-- **`T`-shift formula for `λ`.** `λ(τ + 1) = −(θ₂(τ)⁴ / θ₄(τ)⁴)`.
The proof applies the T-suite: `θ₂(τ+1) = e^{iπ/4}·θ₂(τ)`, `θ₃(τ+1) = θ₄(τ)`,
then raises to the fourth power and uses `(e^{iπ/4})⁴ = e^{iπ} = -1`. -/
theorem modularLambdaH_T_smul (τ : ℂ) :
    modularLambdaH (τ + 1) = -(theta2 τ ^ 4 / theta4 τ ^ 4) := by
  unfold modularLambdaH
  rw [theta2_add_one, theta3_add_one]
  rw [mul_pow]
  rw [show (Complex.exp ((Real.pi : ℂ) * Complex.I / 4)) ^ 4 = (-1 : ℂ) from by
    have h4 : ((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I / 4) = (Real.pi : ℂ) * Complex.I := by
      ring
    calc Complex.exp ((Real.pi : ℂ) * Complex.I / 4) ^ 4
        = Complex.exp (((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I / 4)) := by
          rw [← Complex.exp_nat_mul]
      _ = Complex.exp ((Real.pi : ℂ) * Complex.I) := by rw [h4]
      _ = -1 := Complex.exp_pi_mul_I]
  ring

/-! ## Modular transformations under `S : τ ↦ −1/τ`

Mathlib provides `θ₃` under `S` as `jacobiTheta_S_smul`. The corresponding
`S`-transformations for `θ₂` and `θ₄` follow from the functional equation of
`jacobiTheta₂`, after shifting the argument `z` and tracking signs. -/

/-- `θ₂(−1/τ) = √(−iτ) · θ₄(τ)` for `τ ∈ ℍ`. Combines the
`jacobiTheta₂_functional_equation` evaluated at `z = -1/(2τ), τ = -1/τ`
with `jacobiTheta₂_one_half_eq_theta4`. -/
theorem theta2_S_smul {τ : ℂ} (hτ : 0 < τ.im) :
    theta2 (-1 / τ) = ((-Complex.I * τ) ^ (1 / 2 : ℂ)) * theta4 τ := by
  have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hτ
  have hmIτ_ne : -Complex.I * τ ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ_ne
  -- Key identity: I/τ = (-Iτ)⁻¹, since (-Iτ)·(I/τ) = -I²·(τ/τ) = 1.
  have h_inv_relation : Complex.I / τ = (-Complex.I * τ)⁻¹ := by
    have h_prod : (-Complex.I * τ) * (Complex.I / τ) = 1 := by
      rw [show (Complex.I / τ) = Complex.I * τ⁻¹ from div_eq_mul_inv _ _]
      rw [show (-Complex.I * τ) * (Complex.I * τ⁻¹)
            = -(Complex.I ^ 2) * (τ * τ⁻¹) from by ring]
      rw [mul_inv_cancel₀ hτ_ne, mul_one, Complex.I_sq]; norm_num
    exact eq_inv_of_mul_eq_one_right h_prod
  -- arg(-Iτ) ≠ π since Re(-Iτ) = τ.im > 0.
  have h_arg : (-Complex.I * τ).arg ≠ Real.pi := by
    intro h_arg_eq
    have h_eq := Complex.arg_eq_pi_iff.mp h_arg_eq
    have h_re : (-Complex.I * τ).re = τ.im := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [h_re] at h_eq
    linarith [h_eq.1]
  unfold theta2
  -- Simplify (-1/τ)/2 = -1/(2τ) in the inner jacobiTheta₂ argument.
  rw [show ((-1 / τ : ℂ)) / 2 = -1 / (2 * τ) from by ring]
  -- Apply the functional equation at z = -1/(2τ), τ_param = -1/τ.
  rw [jacobiTheta₂_functional_equation (-1 / (2 * τ)) (-1 / τ)]
  -- Simplify the substituted arguments and exponents.
  rw [show (-Complex.I * (-1 / τ) : ℂ) = Complex.I / τ from by ring]
  rw [show (-1 / (2 * τ) : ℂ) / (-1 / τ) = 1 / 2 from by field_simp]
  rw [show (-1 / (-1 / τ) : ℂ) = τ from by field_simp]
  rw [show -(Real.pi : ℂ) * Complex.I * (-1 / (2 * τ)) ^ 2 / (-1 / τ)
        = (Real.pi : ℂ) * Complex.I / (4 * τ) from by field_simp; ring]
  rw [jacobiTheta₂_one_half_eq_theta4]
  -- The outer exp argument equals the negation of the inner one.
  rw [show (Real.pi : ℂ) * Complex.I * (-1 / τ) / 4
        = -((Real.pi : ℂ) * Complex.I / (4 * τ)) from by field_simp]
  -- Combine the two exp factors: exp(-x) · exp(x) = exp(0) = 1.
  rw [show ∀ a b c d : ℂ, a * (b * c * d) = (a * c) * (b * d)
        from fun a b c d => by ring]
  rw [← Complex.exp_add]
  rw [show -((Real.pi : ℂ) * Complex.I / (4 * τ))
        + (Real.pi : ℂ) * Complex.I / (4 * τ) = 0 from by ring]
  rw [Complex.exp_zero, one_mul]
  -- Goal: 1 / (I/τ)^{1/2} · theta4 τ = (-Iτ)^{1/2} · theta4 τ.
  congr 1
  rw [h_inv_relation, Complex.inv_cpow _ _ h_arg, one_div, inv_inv]

/-- `θ₃(−1/τ) = √(−iτ) · θ₃(τ)` for `τ ∈ ℍ`. (`jacobiTheta_S_smul` ported to
the bare-`ℂ` form used in this file.) -/
theorem theta3_S_smul {τ : ℂ} (hτ : 0 < τ.im) :
    theta3 (-1 / τ) = ((-Complex.I * τ) ^ (1 / 2 : ℂ)) * theta3 τ := by
  unfold theta3
  set τH : UpperHalfPlane := ⟨τ, hτ⟩ with hτH_def
  have h_τH_coe : (τH : ℂ) = τ := rfl
  have hS_coe : ((ModularGroup.S • τH : UpperHalfPlane) : ℂ) = -1 / τ := by
    rw [UpperHalfPlane.modular_S_smul]
    change (-(τH : ℂ))⁻¹ = -1 / τ
    rw [h_τH_coe]; field_simp
  have step := jacobiTheta_S_smul τH
  rw [h_τH_coe, hS_coe] at step
  exact step

/-- `θ₄(−1/τ) = √(−iτ) · θ₂(τ)` for `τ ∈ ℍ`. Same strategy as
`theta2_S_smul` but applied at `z = 1/2` rather than `z = -1/(2τ)`. -/
theorem theta4_S_smul {τ : ℂ} (hτ : 0 < τ.im) :
    theta4 (-1 / τ) = ((-Complex.I * τ) ^ (1 / 2 : ℂ)) * theta2 τ := by
  have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hτ
  have hmIτ_ne : -Complex.I * τ ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ_ne
  have h_inv_relation : Complex.I / τ = (-Complex.I * τ)⁻¹ := by
    have h_prod : (-Complex.I * τ) * (Complex.I / τ) = 1 := by
      rw [show (Complex.I / τ) = Complex.I * τ⁻¹ from div_eq_mul_inv _ _]
      rw [show (-Complex.I * τ) * (Complex.I * τ⁻¹)
            = -(Complex.I ^ 2) * (τ * τ⁻¹) from by ring]
      rw [mul_inv_cancel₀ hτ_ne, mul_one, Complex.I_sq]; norm_num
    exact eq_inv_of_mul_eq_one_right h_prod
  have h_arg : (-Complex.I * τ).arg ≠ Real.pi := by
    intro h_arg_eq
    have h_eq := Complex.arg_eq_pi_iff.mp h_arg_eq
    have h_re : (-Complex.I * τ).re = τ.im := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [h_re] at h_eq
    linarith [h_eq.1]
  -- Rewrite θ₄(-1/τ) as jacobiTheta₂(1/2, -1/τ).
  rw [← jacobiTheta₂_one_half_eq_theta4]
  -- Apply the functional equation at z = 1/2, τ_param = -1/τ.
  rw [jacobiTheta₂_functional_equation (1 / 2) (-1 / τ)]
  rw [show (-Complex.I * (-1 / τ) : ℂ) = Complex.I / τ from by ring]
  rw [show (1 / 2 : ℂ) / (-1 / τ) = -(τ / 2) from by field_simp]
  rw [show (-1 / (-1 / τ) : ℂ) = τ from by field_simp]
  rw [show -(Real.pi : ℂ) * Complex.I * (1 / 2) ^ 2 / (-1 / τ)
        = (Real.pi : ℂ) * Complex.I * τ / 4 from by field_simp; ring]
  rw [jacobiTheta₂_neg_left]
  -- Now goal: (1/(I/τ)^{1/2}) · exp(πIτ/4) · jacobiTheta₂(τ/2, τ)
  --        = (-Iτ)^{1/2} · theta2 τ
  -- where theta2 τ = exp(πIτ/4) · jacobiTheta₂(τ/2, τ).
  unfold theta2
  rw [h_inv_relation, Complex.inv_cpow _ _ h_arg, one_div, inv_inv]
  ring

/-- **`S`-quotient form of `λ`.** For `τ ∈ ℍ`,
`λ(−1/τ) = (θ₄(τ)/θ₃(τ))⁴`. The proof cancels the common `√(−iτ)` factor
that the S-suite introduces in both numerator and denominator. -/
theorem modularLambdaH_S_smul {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH (-1 / τ) = (theta4 τ / theta3 τ) ^ 4 := by
  have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hτ
  have h_root_ne : (-Complex.I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ_ne)
  unfold modularLambdaH
  rw [theta2_S_smul hτ, theta3_S_smul hτ, mul_pow, mul_pow,
      mul_div_mul_left _ _ (pow_ne_zero 4 h_root_ne), div_pow]

/-! ## `Γ(2)`-invariance generators

`Γ(2)` is generated by `T² = [[1, 2], [0, 1]]` (which is `τ ↦ τ + 2`) and
`[[1, 0], [2, 1]] = S · T⁻² · S` (which is `τ ↦ τ / (2τ + 1)`). The first
generator is `modularLambdaH_two_add`. The second is below. -/

/-- **Second `Γ(2)` generator.** `λ(τ / (2τ + 1)) = λ(τ)` for `τ ∈ ℍ`.
The matrix `[[1, 0], [2, 1]]` acts as `τ ↦ τ / (2τ + 1) = S(T⁻²(S(τ)))`,
so we chain S-, T⁻²-, S-invariances of the `θ_i` ratios. -/
theorem modularLambdaH_div_two_tau_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH (τ / (2 * τ + 1)) = modularLambdaH τ := by
  have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hτ
  have h2τp1_im : (2 * τ + 1 : ℂ).im = 2 * τ.im := by
    simp [Complex.add_im, Complex.mul_im, Complex.one_im]
  have h2τp1_ne : (2 * τ + 1 : ℂ) ≠ 0 := by
    intro h
    have h_im : (2 * τ + 1 : ℂ).im = 0 := by rw [h]; rfl
    rw [h2τp1_im] at h_im
    linarith
  -- `Im(-1/τ) = τ.im / |τ|² > 0`.
  have h_neg_inv_im : (-1 / τ : ℂ).im = τ.im / Complex.normSq τ := by
    rw [show (-1 / τ : ℂ) = -(τ⁻¹) from by field_simp]
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  have h_neg_inv_im_pos : 0 < (-1 / τ : ℂ).im := by
    rw [h_neg_inv_im]
    exact div_pos hτ (Complex.normSq_pos.mpr hτ_ne)
  -- `Im(-1/τ - 2) = Im(-1/τ) > 0`.
  have h_σ_im_pos : 0 < (-1/τ - 2 : ℂ).im := by
    have h_eq : (-1/τ - 2 : ℂ).im = (-1/τ : ℂ).im := by
      simp [Complex.sub_im]
    rw [h_eq]; exact h_neg_inv_im_pos
  -- `-1/τ - 2 ≠ 0` (from positive imaginary part).
  have h_σ_ne : (-1/τ - 2 : ℂ) ≠ 0 := by
    intro h
    have : (-1/τ - 2 : ℂ).im = 0 := by rw [h]; rfl
    linarith
  -- `τ / (2τ + 1) = -1 / (-1/τ - 2)` via cross-multiplication.
  have h_rewrite : (τ / (2 * τ + 1) : ℂ) = -1 / (-1/τ - 2) := by
    rw [div_eq_div_iff h2τp1_ne h_σ_ne]
    field_simp
    ring
  rw [h_rewrite]
  -- Apply S-quotient form at σ = -1/τ - 2.
  rw [modularLambdaH_S_smul h_σ_im_pos]
  -- Use T²-invariance to step σ = -1/τ - 2 back to -1/τ.
  have h_t4 : theta4 (-1/τ - 2) = theta4 (-1/τ) := by
    have := theta4_two_add (-1/τ - 2)
    rwa [show (-1/τ - 2 + 2 : ℂ) = -1/τ from by ring, eq_comm] at this
  have h_t3 : theta3 (-1/τ - 2) = theta3 (-1/τ) := by
    have := theta3_two_add (-1/τ - 2)
    rwa [show (-1/τ - 2 + 2 : ℂ) = -1/τ from by ring, eq_comm] at this
  rw [h_t4, h_t3]
  -- Apply the S-suite at τ to convert θ_i(-1/τ) to factors times θ_j(τ).
  rw [theta4_S_smul hτ, theta3_S_smul hτ]
  -- Cancel the common `√(-iτ)`.
  have h_root_ne : (-Complex.I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ_ne)
  rw [mul_div_mul_left _ _ h_root_ne]
  -- Goal reduced to `(θ₂(τ)/θ₃(τ))⁴ = λ(τ)`; unfold the definition.
  unfold modularLambdaH
  rw [div_pow]

/-! ## Jacobi's identity: setup via the difference's modular transformations

Define `f(τ) := θ₂(τ)⁴ + θ₄(τ)⁴ − θ₃(τ)⁴`. Jacobi's identity asserts
`f ≡ 0` on `ℍ`. The classical proof shows that `f` transforms as a
specific modular form for `Γ_θ = ⟨S, T²⟩` of weight 2, has q-expansion
starting at `O(q²)` (the leading `q⁰` and `q¹` coefficients all cancel),
and then concludes by the uniqueness of holomorphic functions with that
transformation behaviour vanishing at the cusp.

This file proves the two transformation properties of `f` (which together
fix its weight-2 character on `Γ_θ`). The remaining work — q-expansion +
holomorphic uniqueness — requires modular-form infrastructure beyond the
current development. -/

/-- Under the T-shift `τ ↦ τ + 1`, the Jacobi difference negates:
`θ₂(τ+1)⁴ + θ₄(τ+1)⁴ − θ₃(τ+1)⁴ = −(θ₂(τ)⁴ + θ₄(τ)⁴ − θ₃(τ)⁴)`. -/
theorem jacobi_diff_T_smul (τ : ℂ) :
    theta2 (τ + 1) ^ 4 + theta4 (τ + 1) ^ 4 - theta3 (τ + 1) ^ 4
      = -(theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4) := by
  rw [theta2_add_one, theta3_add_one, theta4_add_one]
  rw [mul_pow]
  rw [show (Complex.exp ((Real.pi : ℂ) * Complex.I / 4)) ^ 4 = (-1 : ℂ) from by
    have h4 : ((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I / 4) = (Real.pi : ℂ) * Complex.I := by
      ring
    calc Complex.exp ((Real.pi : ℂ) * Complex.I / 4) ^ 4
        = Complex.exp (((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I / 4)) := by
          rw [← Complex.exp_nat_mul]
      _ = Complex.exp ((Real.pi : ℂ) * Complex.I) := by rw [h4]
      _ = -1 := Complex.exp_pi_mul_I]
  ring

/-- Under the S-action `τ ↦ −1/τ`, the Jacobi difference picks up a `−τ²`
factor: `θ₂(−1/τ)⁴ + θ₄(−1/τ)⁴ − θ₃(−1/τ)⁴ = −τ² · (θ₂(τ)⁴ + θ₄(τ)⁴ − θ₃(τ)⁴)`.
Each `θ_i(−1/τ)⁴` collects `(√(−iτ))⁴ = −τ²` from the S-suite. -/
theorem jacobi_diff_S_smul {τ : ℂ} (hτ : 0 < τ.im) :
    theta2 (-1 / τ) ^ 4 + theta4 (-1 / τ) ^ 4 - theta3 (-1 / τ) ^ 4
      = -τ ^ 2 * (theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4) := by
  have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hτ
  have hmIτ_ne : -Complex.I * τ ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ_ne
  -- `(√(-iτ))⁴ = (-iτ)² = -τ²`.
  have h_sq : ((-Complex.I * τ) ^ (1 / 2 : ℂ)) ^ 2 = -Complex.I * τ := by
    rw [sq, ← Complex.cpow_add _ _ hmIτ_ne]
    norm_num
  have h_pow4 : ((-Complex.I * τ) ^ (1 / 2 : ℂ)) ^ 4 = -τ ^ 2 := by
    have h_expand : ((-Complex.I * τ) ^ (1 / 2 : ℂ)) ^ 4
        = (((-Complex.I * τ) ^ (1 / 2 : ℂ)) ^ 2) ^ 2 := by ring
    rw [h_expand, h_sq, mul_pow, neg_sq, Complex.I_sq]
    ring
  rw [theta2_S_smul hτ, theta3_S_smul hτ, theta4_S_smul hτ]
  rw [mul_pow, mul_pow, mul_pow]
  rw [h_pow4]
  ring

/-- **`T²`-invariance of the Jacobi difference.** Applying
`jacobi_diff_T_smul` twice composes the sign factor `-1 · -1 = 1`,
showing `f(τ + 2) = f(τ)` where `f := θ₂⁴ + θ₄⁴ − θ₃⁴`. -/
theorem jacobi_diff_two_add (τ : ℂ) :
    theta2 (τ + 2) ^ 4 + theta4 (τ + 2) ^ 4 - theta3 (τ + 2) ^ 4
      = theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4 := by
  have h1 := jacobi_diff_T_smul τ
  have h2 := jacobi_diff_T_smul (τ + 1)
  rw [show (τ + 1 + 1 : ℂ) = τ + 2 from by ring] at h2
  rw [h2, h1]; ring

/-- The **squared Jacobi difference** `f² = (θ₂⁴ + θ₄⁴ − θ₃⁴)²` is
`T`-invariant: the sign from `jacobi_diff_T_smul` squares away. -/
theorem jacobi_diff_sq_T_smul (τ : ℂ) :
    (theta2 (τ + 1) ^ 4 + theta4 (τ + 1) ^ 4 - theta3 (τ + 1) ^ 4) ^ 2
      = (theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4) ^ 2 := by
  rw [jacobi_diff_T_smul]; ring

/-- The **squared Jacobi difference** `f²` transforms with weight 4
under `S : τ ↦ −1/τ`. The `(−τ²)` factor from `jacobi_diff_S_smul`
squares to `τ⁴`. -/
theorem jacobi_diff_sq_S_smul {τ : ℂ} (hτ : 0 < τ.im) :
    (theta2 (-1 / τ) ^ 4 + theta4 (-1 / τ) ^ 4 - theta3 (-1 / τ) ^ 4) ^ 2
      = τ ^ 4 * (theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4) ^ 2 := by
  rw [jacobi_diff_S_smul hτ]; ring

/-- The squared Jacobi difference is holomorphic on the upper
half-plane. Follows from holomorphy of `θ₂`, `θ₃`, `θ₄` together with
ring closure under products, sums, and powers. -/
theorem jacobi_diff_sq_differentiableOn :
    DifferentiableOn ℂ
      (fun τ : ℂ => (theta2 τ ^ 4 + theta4 τ ^ 4 - theta3 τ ^ 4) ^ 2)
      { τ : ℂ | 0 < τ.im } := by
  intro τ hτ
  refine DifferentiableAt.differentiableWithinAt ?_
  exact ((((theta2_differentiableAt hτ).pow 4).add
    ((theta4_differentiableAt hτ).pow 4)).sub
    ((theta3_differentiableAt hτ).pow 4)).pow 2

/-! ### Analytic norm bounds at the cusp

The cusp bound for `f²` is reduced to four pointwise bounds on the
individual theta nullwerte for `τ.im ≥ 1`: `θ₂` has the leading
exponential factor `exp(−π·τ.im/4)`, `θ₃` and `θ₄` are bounded
constants close to 1, and `θ₃ − θ₄` has full `exp(−π·τ.im)` decay
because the constant terms cancel. The first bound is the analytic
content of the q-expansion of `θ₂` at the cusp; the other three
follow from `norm_jacobiTheta_sub_one_le`. -/

/-- `‖θ₂(τ)‖ ≤ 10 · exp(−π·τ.im/4)` for `τ.im ≥ 1`. Encodes the
leading factor `q^{1/4}` in `θ₂(τ) = 2 q^{1/4}(1 + q² + q⁶ + …)`,
`q = exp(πiτ)`. Bounds the integer sum
`∑_{n ∈ ℤ} ‖jacobiTheta₂_term n (τ/2) τ‖` by `2·(1−R)⁻¹` where
`R = exp(−π·τ.im)`, using that each term equals
`exp(−π·τ.im·n(n+1))` and `n(n+1) ≥ |n|` (split through `Int.rec`). -/
theorem theta2_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta2 τ‖ ≤ 10 * Real.exp (-Real.pi * τ.im / 4) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- `R = exp(−π·τ.im)` and its useful bounds.
  set R : ℝ := Real.exp (-Real.pi * τ.im) with hR_def
  have hR_pos : 0 < R := Real.exp_pos _
  have hR_le_exp_neg_pi : R ≤ Real.exp (-Real.pi) := by
    rw [hR_def]; apply Real.exp_le_exp.mpr; nlinarith
  have h_exp_neg_pi_lt_half : Real.exp (-Real.pi) < 1/2 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/2),
        show (1/2 : ℝ)⁻¹ = 2 from by norm_num]
    have h1 : (1 : ℝ) + 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp 1 < Real.exp Real.pi :=
      Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_three])
    linarith
  have hR_lt_one : R < 1 := lt_of_le_of_lt hR_le_exp_neg_pi (by linarith)
  have h_one_sub_pos : 0 < 1 - R := by linarith
  have h_one_sub_ge_half : 1/2 ≤ 1 - R := by
    have hR_le_half : R ≤ 1/2 := le_trans hR_le_exp_neg_pi (le_of_lt h_exp_neg_pi_lt_half)
    linarith
  -- Geometric series HasSum and its ℤ-extension via Int.rec.
  have h_geo : HasSum (fun n : ℕ => R ^ n) ((1 - R)⁻¹) :=
    hasSum_geometric_of_lt_one hR_pos.le hR_lt_one
  have h_int_rec_hasSum :
      HasSum (fun n : ℤ => Int.rec (fun m : ℕ => R ^ m) (fun m : ℕ => R ^ m) n)
             ((1 - R)⁻¹ + (1 - R)⁻¹) :=
    HasSum.int_rec h_geo h_geo
  -- `(τ/2).im = τ.im / 2`.
  have h_zim : (τ / 2 : ℂ).im = τ.im / 2 := by
    simp
  -- Per-term bound: `‖jacobiTheta₂_term n (τ/2) τ‖ ≤ Int.rec R^· R^· n`.
  have h_term_bound : ∀ n : ℤ,
      ‖jacobiTheta₂_term n (τ / 2) τ‖
        ≤ Int.rec (fun m : ℕ => R ^ m) (fun m : ℕ => R ^ m) n := by
    intro n
    rw [norm_jacobiTheta₂_term, h_zim]
    cases n with
    | ofNat m =>
      change Real.exp _ ≤ R ^ m
      rw [hR_def, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have h_cast : ((Int.ofNat m : ℤ) : ℝ) = (m : ℝ) := by simp
      rw [h_cast]
      have h_prod_nn : 0 ≤ Real.pi * τ.im * (m : ℝ) ^ 2 := by positivity
      nlinarith
    | negSucc m =>
      change Real.exp _ ≤ R ^ m
      rw [hR_def, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have h_cast : ((Int.negSucc m : ℤ) : ℝ) = -((m : ℝ) + 1) := by
        rw [Int.cast_negSucc]; push_cast; ring
      rw [h_cast]
      have h_prod_nn : 0 ≤ Real.pi * τ.im * (m : ℝ) ^ 2 := by positivity
      nlinarith
  -- Apply `tsum_of_norm_bounded`.
  have h_hsum := hasSum_jacobiTheta₂_term (τ / 2) hτim_pos
  have h_tsum_le :
      ‖∑' n : ℤ, jacobiTheta₂_term n (τ / 2) τ‖ ≤ (1 - R)⁻¹ + (1 - R)⁻¹ :=
    tsum_of_norm_bounded h_int_rec_hasSum h_term_bound
  have h_jt₂_le : ‖jacobiTheta₂ (τ / 2) τ‖ ≤ (1 - R)⁻¹ + (1 - R)⁻¹ := by
    rw [← h_hsum.tsum_eq]; exact h_tsum_le
  -- `(1 - R)⁻¹ ≤ 2`.
  have h_quot_le : (1 - R)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ h_one_sub_pos (by norm_num : (0:ℝ) < 2)]; linarith
  have h_jt₂_le_4 : ‖jacobiTheta₂ (τ / 2) τ‖ ≤ 4 := by linarith
  -- Reassemble `‖θ₂(τ)‖ = ‖exp(πi τ/4)‖ · ‖jacobiTheta₂(τ/2, τ)‖`.
  unfold theta2
  rw [norm_mul]
  have h_exp_re : ((Real.pi : ℂ) * Complex.I * τ / 4).re = -Real.pi * τ.im / 4 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have h_exp_norm : ‖Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4)‖
                  = Real.exp (-Real.pi * τ.im / 4) := by
    rw [Complex.norm_exp, h_exp_re]
  rw [h_exp_norm]
  have h_exp_pos : 0 < Real.exp (-Real.pi * τ.im / 4) := Real.exp_pos _
  calc Real.exp (-Real.pi * τ.im / 4) * ‖jacobiTheta₂ (τ / 2) τ‖
      ≤ Real.exp (-Real.pi * τ.im / 4) * 4 :=
        mul_le_mul_of_nonneg_left h_jt₂_le_4 h_exp_pos.le
    _ ≤ 10 * Real.exp (-Real.pi * τ.im / 4) := by linarith

/-- `‖θ₃(τ)‖ ≤ 10` for `τ.im ≥ 1`. The actual value is close to 1;
the loose bound `10` is chosen for convenience. -/
theorem theta3_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta3 τ‖ ≤ 10 := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- Use the Mathlib bound on ‖jacobiTheta τ - 1‖.
  have h_mathlib : ‖jacobiTheta τ - 1‖ ≤
      2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) :=
    norm_jacobiTheta_sub_one_le hτim_pos
  -- Bound exp(-π·τ.im) ≤ exp(-π) and exp(-π) < 1/2.
  have h_exp_at_one : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have h_exp_neg_pi_lt_half : Real.exp (-Real.pi) < 1/2 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/2),
        show (1/2 : ℝ)⁻¹ = 2 from by norm_num]
    have h1 : (1 : ℝ) + 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp 1 < Real.exp Real.pi :=
      Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_three])
    linarith
  have h_exp_lt_half : Real.exp (-Real.pi * τ.im) < 1/2 :=
    lt_of_le_of_lt h_exp_at_one h_exp_neg_pi_lt_half
  have h_one_sub_ge : 1/2 ≤ 1 - Real.exp (-Real.pi * τ.im) := by linarith
  have h_one_sub_pos : 0 < 1 - Real.exp (-Real.pi * τ.im) := by linarith
  have h_exp_le_one : Real.exp (-Real.pi * τ.im) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  -- 2/(1 - e^{-π·τ.im}) ≤ 4.
  have h_quot_le : 2 / (1 - Real.exp (-Real.pi * τ.im)) ≤ 4 := by
    rw [div_le_iff₀ h_one_sub_pos]; linarith
  -- Hence ‖θ₃ - 1‖ ≤ 4 · 1 = 4.
  have h_sub_one_le : ‖jacobiTheta τ - 1‖ ≤ 4 := by
    refine h_mathlib.trans ?_
    have := mul_le_mul h_quot_le h_exp_le_one (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 4)
    linarith
  -- ‖θ₃‖ = ‖(θ₃ - 1) + 1‖ ≤ ‖θ₃ - 1‖ + 1 ≤ 5 ≤ 10.
  unfold theta3
  calc ‖jacobiTheta τ‖
      = ‖(jacobiTheta τ - 1) + 1‖ := by congr 1; ring
    _ ≤ ‖jacobiTheta τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 4 + 1 := by rw [norm_one]; linarith
    _ ≤ 10 := by norm_num

/-- `‖θ₄(τ)‖ ≤ 10` for `τ.im ≥ 1`. Same bound as `θ₃` since
`θ₄(τ) = θ₃(τ + 1)` and `(τ + 1).im = τ.im`. -/
theorem theta4_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta4 τ‖ ≤ 10 := by
  have h_eq : theta4 τ = theta3 (τ + 1) := (theta3_add_one τ).symm
  have h_im : 1 ≤ (τ + 1).im := by simpa [Complex.add_im] using hτ
  rw [h_eq]
  exact theta3_norm_le_of_im_ge_one h_im

/-- **Extracted bound `‖θ₃(τ) − 1‖ ≤ 4·exp(−π·τ.im)` for `τ.im ≥ 1`.**
This is the per-τ specialization of Mathlib's
`norm_jacobiTheta_sub_one_le`: at `τ.im ≥ 1`, the quotient
`2/(1 − exp(−π·τ.im))` is bounded by `4`. -/
theorem theta3_sub_one_norm_le_exp_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta3 τ - 1‖ ≤ 4 * Real.exp (-Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  have h_mathlib : ‖jacobiTheta τ - 1‖ ≤
      2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) :=
    norm_jacobiTheta_sub_one_le hτim_pos
  have h_exp_at_one : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have h_exp_neg_pi_lt_half : Real.exp (-Real.pi) < 1/2 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/2),
        show (1/2 : ℝ)⁻¹ = 2 from by norm_num]
    have h1 : (1 : ℝ) + 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp 1 < Real.exp Real.pi :=
      Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_three])
    linarith
  have h_exp_lt_half : Real.exp (-Real.pi * τ.im) < 1/2 :=
    lt_of_le_of_lt h_exp_at_one h_exp_neg_pi_lt_half
  have h_one_sub_pos : 0 < 1 - Real.exp (-Real.pi * τ.im) := by linarith
  have h_quot_le : 2 / (1 - Real.exp (-Real.pi * τ.im)) ≤ 4 := by
    rw [div_le_iff₀ h_one_sub_pos]; linarith
  have h_exp_pos : 0 < Real.exp (-Real.pi * τ.im) := Real.exp_pos _
  unfold theta3
  exact h_mathlib.trans (mul_le_mul_of_nonneg_right h_quot_le h_exp_pos.le)

/-- **Lower bound `1/2 ≤ ‖θ₃(τ)‖` for `τ.im ≥ 1`.** Follows from
`theta3_sub_one_norm_le_exp_of_im_ge_one` since
`4·exp(−π·τ.im) ≤ 4·exp(−π) < 1/2`. -/
theorem theta3_norm_ge_half_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    (1 : ℝ)/2 ≤ ‖theta3 τ‖ := by
  have h_sub_one := theta3_sub_one_norm_le_exp_of_im_ge_one hτ
  -- 4 exp(-π τ.im) ≤ 4 exp(-π) < 1/2. Need exp(π) > 8.
  have h_exp_at_one : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-Real.pi) := by
    apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
  -- exp(π) > 8 via exp(π) ≥ exp(3) > 2.7^3 > 8.
  have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_exp3_gt_8 : (8 : ℝ) < Real.exp 3 := by
    have h_eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
    rw [h_eq]
    nlinarith [h_e_gt, Real.exp_pos (1 : ℝ)]
  have h_pi_gt_3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h_exp_pi_gt_8 : (8 : ℝ) < Real.exp Real.pi :=
    h_exp3_gt_8.trans_le (Real.exp_le_exp.mpr h_pi_gt_3.le)
  have h_exp_neg_pi_lt : Real.exp (-Real.pi) < 1/8 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 1/8),
        show (1/8 : ℝ)⁻¹ = 8 from by norm_num]
    exact h_exp_pi_gt_8
  have h_four_exp_lt : 4 * Real.exp (-Real.pi * τ.im) < 1/2 := by
    have h1 : Real.exp (-Real.pi * τ.im) ≤ Real.exp (-Real.pi) := h_exp_at_one
    have h2 : Real.exp (-Real.pi) < 1/8 := h_exp_neg_pi_lt
    linarith
  have h_norm_sub_one_lt : ‖theta3 τ - 1‖ < 1/2 := lt_of_le_of_lt h_sub_one h_four_exp_lt
  -- ‖θ₃‖ ≥ 1 - ‖θ₃ - 1‖ > 1/2.
  have h_rev := norm_sub_norm_le (1 : ℂ) (1 - theta3 τ)
  have h_eq1 : (1 : ℂ) - (1 - theta3 τ) = theta3 τ := by ring
  have h_eq2 : ‖(1 : ℂ) - theta3 τ‖ = ‖theta3 τ - 1‖ := by
    rw [show (1 : ℂ) - theta3 τ = -(theta3 τ - 1) from by ring, norm_neg]
  rw [h_eq1, h_eq2, norm_one] at h_rev
  linarith

/-- **Uniform cusp `i∞` bound for `λ`.** For `τ.im ≥ 1`,
`‖λ(τ)‖ ≤ 160000·exp(−π·τ.im)`. Chains `‖θ₂(τ)‖⁴ ≤ 10⁴·exp(−π·τ.im)`
(from `theta2_norm_le_of_im_ge_one`) with the lower bound
`‖θ₃(τ)‖ ≥ 1/2` from `theta3_norm_ge_half_of_im_ge_one`. The bound is
not sharp; the actual leading term is `16·exp(−π·τ.im)`. -/
theorem modularLambdaH_norm_le_exp_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖modularLambdaH τ‖ ≤ 160000 * Real.exp (-Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have h2 := theta2_norm_le_of_im_ge_one hτ
  have h3_ge_half := theta3_norm_ge_half_of_im_ge_one hτ
  -- θ₃(τ) ≠ 0 because ‖θ₃(τ)‖ ≥ 1/2 > 0.
  have h3_ne : theta3 τ ≠ 0 := by
    intro h
    rw [h, norm_zero] at h3_ge_half
    linarith
  have h3_pow_ne : (theta3 τ)^4 ≠ 0 := pow_ne_zero 4 h3_ne
  have h2_nn : 0 ≤ ‖theta2 τ‖ := norm_nonneg _
  have h_exp_pos : 0 < Real.exp (-Real.pi * τ.im / 4) := Real.exp_pos _
  have h2_pow4 : ‖theta2 τ‖^4 ≤ 10000 * Real.exp (-Real.pi * τ.im) := by
    have h_pow_le : ‖theta2 τ‖^4 ≤ (10 * Real.exp (-Real.pi * τ.im / 4))^4 :=
      pow_le_pow_left₀ h2_nn h2 4
    have h_simp : (10 * Real.exp (-Real.pi * τ.im / 4))^4 =
        10000 * Real.exp (-Real.pi * τ.im) := by
      rw [mul_pow]
      ring_nf
      rw [← Real.exp_nat_mul]
      ring_nf
    linarith [h_pow_le, h_simp.symm.le]
  have h3_pow4 : (1 : ℝ)/16 ≤ ‖theta3 τ‖^4 := by
    have h_half_nn : (0 : ℝ) ≤ 1/2 := by norm_num
    have := pow_le_pow_left₀ h_half_nn h3_ge_half 4
    have h_simp : ((1 : ℝ)/2)^4 = 1/16 := by norm_num
    linarith
  unfold modularLambdaH
  rw [norm_div, norm_pow, norm_pow]
  -- ‖θ₂⁴‖ / ‖θ₃⁴‖ = ‖θ₂‖⁴ / ‖θ₃‖⁴ ≤ (10⁴ exp) / (1/16) = 16 · 10⁴ exp.
  have h_denom_pos : 0 < ‖theta3 τ‖^4 := by
    have : 0 < ‖theta3 τ‖ := norm_pos_iff.mpr h3_ne
    positivity
  rw [div_le_iff₀ h_denom_pos]
  -- Goal: ‖θ₂‖⁴ ≤ 160000 e^(-π τ.im) · ‖θ₃‖⁴.
  -- Use ‖θ₃‖⁴ ≥ 1/16 to get RHS ≥ 160000 e^(-π τ.im) · (1/16) = 10000 e^(-π τ.im) ≥ ‖θ₂‖⁴.
  have h_exp_nn : 0 ≤ Real.exp (-Real.pi * τ.im) := (Real.exp_pos _).le
  have h_factor_nn : 0 ≤ 160000 * Real.exp (-Real.pi * τ.im) := by positivity
  have h_lower : 10000 * Real.exp (-Real.pi * τ.im) ≤
      160000 * Real.exp (-Real.pi * τ.im) * ‖theta3 τ‖^4 := by
    have h_rewrite : 10000 * Real.exp (-Real.pi * τ.im) =
        160000 * Real.exp (-Real.pi * τ.im) * (1/16) := by ring
    rw [h_rewrite]
    exact mul_le_mul_of_nonneg_left h3_pow4 h_factor_nn
  linarith

/-- **Norm of a `jacobiTheta₂_term` at `z = τ/2`.** For each integer `n`,
`‖jacobiTheta₂_term n (τ/2) τ‖ = exp(-π · n·(n+1) · τ.im)`. The argument
of the exponential simplifies via `2π i n · (τ/2) + π i n² τ = π i n(n+1) τ`. -/
theorem jacobiTheta₂_term_half_norm (n : ℤ) (τ : ℂ) :
    ‖jacobiTheta₂_term n (τ / 2) τ‖ =
      Real.exp (-(Real.pi * (n : ℝ) * ((n : ℝ) + 1) * τ.im)) := by
  unfold jacobiTheta₂_term
  rw [Complex.norm_exp]
  -- Rewrite argument as πi · (n*(n+1) : ℝ) · τ.
  have h_arg :
      (2 : ℂ) * Real.pi * Complex.I * (n : ℂ) * (τ / 2) +
        Real.pi * Complex.I * (n : ℂ) ^ 2 * τ =
      ((Real.pi * (n : ℝ) * ((n : ℝ) + 1) : ℝ) : ℂ) * (Complex.I * τ) := by
    push_cast; ring
  rw [h_arg, Complex.mul_re]
  simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]

/-- **Tail bound for `jacobiTheta₂(τ/2, τ)`.** For `τ.im ≥ 1`,
`‖jacobiTheta₂(τ/2, τ) - 2‖ ≤ 8·exp(-2π·τ.im)`.

This is the leading-term estimate. The series
`jacobiTheta₂(τ/2, τ) = Σ_n jacobiTheta₂_term n (τ/2) τ` has each term
of norm `exp(-π · n·(n+1) · τ.im)` (by `jacobiTheta₂_term_half_norm`).
At `n ∈ {0, -1}`, `n(n+1) = 0` and the term is `exp(0) = 1`, so the
finite portion `∑_{n ∈ {0,-1}} term n = 2`.

**Proof outline:**

1. Set `s := {-2, -1, 0, 1} : Finset ℤ`. Then
   `∑ n ∈ s, term n = 2 + 2 · exp(2πi τ)` (since `term ±1 = term (-2) = exp(2πi τ)`).
2. By `Summable.sum_add_tsum_subtype_compl`:
   `∑'_{n ∉ s} term n = jacobiTheta₂(τ/2, τ) - (2 + 2·exp(2πi τ))`.
3. By `norm_tsum_le_tsum_norm` and `norm_jacobiTheta₂_term_le` (with
   `T = τ.im`, `S = τ.im/2`):
   `‖∑'_{n ∉ s} term n‖ ≤ ∑'_{n ∉ s} exp(-π τ.im (n² - |n|))`.
4. For `n ∉ s` (i.e., `|n| ≥ 2`): `n² - |n| ≥ |n|`. So
   `‖term n‖ ≤ exp(-π τ.im |n|)`, summing geometrically gives
   `Σ_{|n|≥2} exp(-π|n|·τ.im) ≤ 3·exp(-2π·τ.im)` for `τ.im ≥ 1`.
5. Triangle inequality:
   `‖jacobiTheta₂(τ/2, τ) - 2‖ = ‖(j₂ - 2 - 2 e^(2πi τ)) + 2 e^(2πi τ)‖`
   `≤ ‖j₂ - 2 - 2 e^(2πi τ)‖ + ‖2 e^(2πi τ)‖`
   `≤ 3·exp(-2π·τ.im) + 2·exp(-2π·τ.im) = 5·exp(-2π·τ.im) ≤ 8·exp(-2π·τ.im)`.

The key sub-step is the geometric tail bound (#4), which uses the
exponential decay of the loose Mathlib bound on `‖jacobiTheta₂_term n‖`.
-/
theorem jacobiTheta₂_half_sub_two_norm_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta₂ (τ / 2) τ - 2‖ ≤ 8 * Real.exp (-2 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  set r : ℝ := Real.exp (-2 * Real.pi * τ.im) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_nn : 0 ≤ r := hr_pos.le
  -- Need r < 1/2 for the geometric bound (1-r)⁻¹ < 2.
  have hr_lt_half : r < 1 / 2 := by
    have h_arg : -2 * Real.pi * τ.im ≤ -2 * Real.pi := by nlinarith
    have h_le : r ≤ Real.exp (-2 * Real.pi) := Real.exp_le_exp.mpr h_arg
    have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h_2pi_gt_1 : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h_exp_2pi_gt_2 : (2 : ℝ) < Real.exp (2 * Real.pi) := by
      have h_mono : Real.exp 1 ≤ Real.exp (2 * Real.pi) := Real.exp_le_exp.mpr h_2pi_gt_1.le
      linarith
    have h_exp_neg_pos : 0 < Real.exp (2 * Real.pi) := Real.exp_pos _
    have h_exp_neg_lt : Real.exp (-2 * Real.pi) < 1 / 2 := by
      rw [show (-2 * Real.pi : ℝ) = -(2 * Real.pi) from by ring, Real.exp_neg]
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by ring]
      exact inv_strictAnti₀ (by norm_num : (0:ℝ) < 2) h_exp_2pi_gt_2
    linarith
  have hr_lt_one : r < 1 := by linarith
  have h_one_sub_r_pos : 0 < 1 - r := by linarith
  have h_inv_one_sub_r_le : (1 - r)⁻¹ ≤ 2 := by
    rw [show (2 : ℝ) = (1 / 2)⁻¹ from by norm_num]
    exact inv_anti₀ (by norm_num : (0:ℝ) < 1/2) (by linarith)
  -- Setup the HasSum on ℤ.
  have h_hasSum_int := hasSum_jacobiTheta₂_term (τ / 2) hτim_pos
  -- Special term values.
  have h_term_zero : jacobiTheta₂_term 0 (τ / 2) τ = 1 := by
    unfold jacobiTheta₂_term; simp
  have h_term_one : jacobiTheta₂_term 1 (τ / 2) τ = Complex.exp (2 * Real.pi * Complex.I * τ) := by
    unfold jacobiTheta₂_term
    congr 1; push_cast; ring
  have h_term_neg_one : jacobiTheta₂_term (-1 : ℤ) (τ / 2) τ = 1 := by
    unfold jacobiTheta₂_term
    have h_arg : (2 : ℂ) * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * (τ / 2) +
        Real.pi * Complex.I * ((-1 : ℤ) : ℂ)^2 * τ = 0 := by push_cast; ring
    rw [h_arg, Complex.exp_zero]
  -- ‖exp(2πi τ)‖ = r.
  have h_norm_exp_eq : ‖Complex.exp (2 * Real.pi * Complex.I * τ)‖ = r := by
    rw [Complex.norm_exp, hr_def]
    congr 1
    have h_eq : (2 * Real.pi * Complex.I * τ : ℂ) =
        ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
  -- Apply HasSum.nat_add_neg.
  have h_pair_hasSum : HasSum (fun n : ℕ =>
      jacobiTheta₂_term (n : ℤ) (τ/2) τ + jacobiTheta₂_term (-(n : ℤ)) (τ/2) τ)
      (jacobiTheta₂ (τ/2) τ + 1) := by
    have := h_hasSum_int.nat_add_neg
    rw [h_term_zero] at this
    exact this
  -- Sum of first two terms (n = 0, 1) equals 3 + exp(2πi τ).
  have h_sum_two :
      ∑ i ∈ Finset.range 2, (jacobiTheta₂_term ((i : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-((i : ℕ) : ℤ)) (τ/2) τ) =
      3 + Complex.exp (2 * Real.pi * Complex.I * τ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    simp only [Nat.cast_zero, neg_zero, Nat.cast_one]
    rw [h_term_zero, h_term_one, h_term_neg_one]
    ring
  -- Shift by 2: HasSum of the tail starting at n = 2.
  -- We'll use the version (h_pair_hasSum.sum_nat_of_sum_int)-style by manipulating directly.
  -- Use: h_pair_hasSum has total S; subtracting the first 2 terms gives the tail.
  have h_pair_tsum : ∑' n : ℕ, (jacobiTheta₂_term ((n : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-((n : ℕ) : ℤ)) (τ/2) τ) =
      jacobiTheta₂ (τ/2) τ + 1 := h_pair_hasSum.tsum_eq
  have h_pair_summable : Summable (fun n : ℕ => jacobiTheta₂_term ((n : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-((n : ℕ) : ℤ)) (τ/2) τ) := h_pair_hasSum.summable
  have h_tail_hasSum : HasSum (fun n : ℕ =>
      jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ +
      jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ)
      (jacobiTheta₂ (τ/2) τ - 2 - Complex.exp (2 * Real.pi * Complex.I * τ)) := by
    have h_shift_summable : Summable (fun n : ℕ =>
        jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ) := by
      have := (summable_nat_add_iff (k := 2)).mpr h_pair_summable
      exact this
    rw [Summable.hasSum_iff h_shift_summable]
    have h_eq := (Summable.sum_add_tsum_nat_add 2 h_pair_summable).symm
    rw [h_pair_tsum] at h_eq
    rw [h_sum_two] at h_eq
    linear_combination -h_eq
  -- Rearrange.
  have h_eq : jacobiTheta₂ (τ/2) τ - 2 =
      Complex.exp (2 * Real.pi * Complex.I * τ) +
      ∑' n : ℕ, (jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ) := by
    rw [h_tail_hasSum.tsum_eq]; ring
  rw [h_eq]
  -- Triangle inequality.
  refine (norm_add_le _ _).trans ?_
  rw [h_norm_exp_eq]
  -- Termwise bound: ‖term(n+2) + term(-(n+2))‖ ≤ 2·r^(n+1).
  have h_termwise : ∀ n : ℕ,
      ‖jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ‖ ≤ 2 * r^(n + 1) := by
    intro n
    refine (norm_add_le _ _).trans ?_
    -- Compute r^(n+1) = exp(-2π·(n+1)·τ.im).
    have hr_pow : r^(n + 1) = Real.exp (((n : ℝ) + 1) * (-2 * Real.pi * τ.im)) := by
      rw [hr_def, ← Real.exp_nat_mul]
      congr 1; push_cast; ring
    have hN_pos : ((((n + 2) : ℕ) : ℤ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hN_neg : (((-(((n + 2) : ℕ) : ℤ)) : ℤ) : ℝ) = -((n : ℝ) + 2) := by push_cast; ring
    have h_pi_tau_nn : 0 ≤ Real.pi * τ.im := mul_nonneg Real.pi_pos.le hτim_pos.le
    have h_pos_norm : ‖jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ‖ ≤ r^(n + 1) := by
      rw [jacobiTheta₂_term_half_norm, hN_pos, hr_pow]
      apply Real.exp_le_exp.mpr
      have h_ineq : 2 * ((n : ℝ) + 1) ≤ ((n : ℝ) + 2) * ((n : ℝ) + 3) := by nlinarith
      have h_mul : Real.pi * τ.im * (2 * ((n : ℝ) + 1)) ≤
          Real.pi * τ.im * (((n : ℝ) + 2) * ((n : ℝ) + 3)) :=
        mul_le_mul_of_nonneg_left h_ineq h_pi_tau_nn
      linarith
    have h_neg_norm : ‖jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ‖ ≤ r^(n + 1) := by
      rw [jacobiTheta₂_term_half_norm]
      have hN' : ((-(((n + 2) : ℕ) : ℤ) : ℤ) : ℝ) = -((n : ℝ) + 2) := by push_cast; ring
      rw [hN', hr_pow]
      apply Real.exp_le_exp.mpr
      have h_ineq : 2 * ((n : ℝ) + 1) ≤ (-((n : ℝ) + 2)) * (-((n : ℝ) + 2) + 1) := by nlinarith
      have h_mul : Real.pi * τ.im * (2 * ((n : ℝ) + 1)) ≤
          Real.pi * τ.im * ((-((n : ℝ) + 2)) * (-((n : ℝ) + 2) + 1)) :=
        mul_le_mul_of_nonneg_left h_ineq h_pi_tau_nn
      linarith
    linarith
  -- Summability of the bound: ∑' (2·r^(n+1)) is summable (geometric).
  have h_bound_summable : Summable (fun n : ℕ => 2 * r^(n + 1)) := by
    have : Summable (fun n : ℕ => r^n) := summable_geometric_of_lt_one hr_nn hr_lt_one
    have h_shifted : Summable (fun n : ℕ => r * r^n) :=
      (summable_geometric_of_lt_one hr_nn hr_lt_one).mul_left r
    have h_eq : (fun n : ℕ => 2 * r^(n + 1)) = (fun n : ℕ => 2 * (r * r^n)) := by
      ext n; rw [pow_succ']
    rw [h_eq]
    exact h_shifted.mul_left 2
  -- Sum of bound: 2 · r · (1-r)⁻¹.
  have h_bound_tsum : ∑' n : ℕ, 2 * r^(n + 1) = 2 * r * (1 - r)⁻¹ := by
    have h_geo := tsum_geometric_of_lt_one hr_nn hr_lt_one
    -- ∑'_n r^(n+1) = r · ∑'_n r^n = r · (1-r)⁻¹.
    have h_shift : ∑' n : ℕ, r^(n + 1) = r * (1 - r)⁻¹ := by
      have h_eq : (fun n : ℕ => r^(n + 1)) = (fun n : ℕ => r * r^n) := by
        ext n; rw [pow_succ']
      rw [h_eq, tsum_mul_left, h_geo]
    rw [show (fun n : ℕ => 2 * r^(n + 1)) = fun n : ℕ => 2 * r^(n+1) from rfl]
    rw [tsum_mul_left, h_shift, ← mul_assoc]
  -- Norm-summability of the original sequence.
  have h_norm_summable : Summable (fun n : ℕ =>
      ‖jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ‖) :=
    h_bound_summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_termwise
  -- Triangle inequality on the tsum.
  have h_norm_tsum_le := norm_tsum_le_tsum_norm h_norm_summable
  -- Compare: tsum norm ≤ tsum bound.
  have h_tsum_le : (∑' n : ℕ,
      ‖jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ‖) ≤
      2 * r * (1 - r)⁻¹ := by
    rw [← h_bound_tsum]
    exact h_norm_summable.tsum_le_tsum h_termwise h_bound_summable
  -- Final calculation.
  have h_step : ‖∑' n : ℕ, (jacobiTheta₂_term (((n + 2) : ℕ) : ℤ) (τ/2) τ +
        jacobiTheta₂_term (-(((n + 2) : ℕ) : ℤ)) (τ/2) τ)‖ ≤ 2 * r * (1 - r)⁻¹ :=
    h_norm_tsum_le.trans h_tsum_le
  -- r + 2r·(1-r)⁻¹ ≤ r + 2r·2 = 5r ≤ 8r.
  have h_final : r + 2 * r * (1 - r)⁻¹ ≤ 8 * r := by
    have h1 : 2 * r * (1 - r)⁻¹ ≤ 2 * r * 2 := by
      apply mul_le_mul_of_nonneg_left h_inv_one_sub_r_le
      positivity
    linarith
  linarith

/-- **Leading-term bound for `θ₂`.** For `τ.im ≥ 1`,
`‖θ₂(τ) - 2 · exp(πi τ/4)‖ ≤ 8·exp(-9π τ.im/4)`. Follows from
`jacobiTheta₂_half_sub_two_norm_le_of_im_ge_one` and
`θ₂(τ) = exp(πi τ/4) · jacobiTheta₂(τ/2, τ)`, factoring out
`exp(πi τ/4)` with `|exp(πi τ/4)| = exp(-π τ.im/4)`. -/
theorem theta2_norm_sub_lead_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖theta2 τ - 2 * Complex.exp (Real.pi * Complex.I * τ / 4)‖ ≤
      8 * Real.exp (-(9 * Real.pi * τ.im / 4)) := by
  unfold theta2
  -- theta2 τ - 2 exp(πi τ/4) = exp(πi τ/4) · (jacobiTheta₂(τ/2, τ) - 2).
  have h_factor :
      Complex.exp (Real.pi * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ -
        2 * Complex.exp (Real.pi * Complex.I * τ / 4) =
      Complex.exp (Real.pi * Complex.I * τ / 4) * (jacobiTheta₂ (τ / 2) τ - 2) := by
    ring
  rw [h_factor, norm_mul]
  -- |exp(πi τ/4)| = exp(-π τ.im/4).
  have h_norm_exp :
      ‖Complex.exp (Real.pi * Complex.I * τ / 4)‖ = Real.exp (-(Real.pi * τ.im / 4)) := by
    rw [Complex.norm_exp]
    congr 1
    have h_eq : (Real.pi * Complex.I * τ / 4 : ℂ) =
        ((Real.pi / 4 : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
    rw [h_eq, Complex.mul_re]
    simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [h_norm_exp]
  -- Tail bound on jacobiTheta₂(τ/2, τ) - 2.
  have h_tail := jacobiTheta₂_half_sub_two_norm_le_of_im_ge_one hτ
  have h_exp_nn : 0 ≤ Real.exp (-(Real.pi * τ.im / 4)) := (Real.exp_pos _).le
  -- Combine: exp(-π τ.im/4) * 8 exp(-2π τ.im) = 8 exp(-9π τ.im/4).
  have h_combine :
      Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-2 * Real.pi * τ.im)) =
      8 * Real.exp (-(9 * Real.pi * τ.im / 4)) := by
    rw [show (8 * Real.exp (-2 * Real.pi * τ.im) : ℝ) =
        8 * Real.exp (-2 * Real.pi * τ.im) from rfl]
    rw [show Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-2 * Real.pi * τ.im)) =
        8 * (Real.exp (-(Real.pi * τ.im / 4)) * Real.exp (-2 * Real.pi * τ.im)) from by ring]
    rw [← Real.exp_add]
    exact congr_arg (fun x => 8 * Real.exp x) (by ring)
  calc Real.exp (-(Real.pi * τ.im / 4)) * ‖jacobiTheta₂ (τ / 2) τ - 2‖
      ≤ Real.exp (-(Real.pi * τ.im / 4)) * (8 * Real.exp (-2 * Real.pi * τ.im)) :=
        mul_le_mul_of_nonneg_left h_tail h_exp_nn
    _ = 8 * Real.exp (-(9 * Real.pi * τ.im / 4)) := h_combine

/-- **Leading-term bound for `λ`.** For `τ.im ≥ 1`,
`‖λ(τ) - 16 · exp(πi τ)‖ ≤ 4096 · exp(-2π τ.im)`.

Combines `theta2_norm_sub_lead_le_of_im_ge_one` (`|θ₂ - 2 e^(πi τ/4)|`
bound) with `theta3_sub_one_norm_le_exp_of_im_ge_one` and
`theta3_norm_ge_half_of_im_ge_one`, then expands `(a/b)⁴` algebraically.

**Proof outline:**
* Set `r₂ := (θ₂ - 2 e^(πi τ/4))/(2 e^(πi τ/4))` so `|r₂| ≤ 4·exp(-2π τ.im)`.
* Set `r₃ := θ₃ - 1` so `|r₃| ≤ 4·exp(-π τ.im)`.
* `λ = (θ₂)⁴/(θ₃)⁴ = (2 e^(πi τ/4))⁴ · (1+r₂)⁴/(1+r₃)⁴ = 16 e^(πi τ) · ((1+r₂)/(1+r₃))⁴`.
* Let `s := (1+r₂)/(1+r₃) - 1 = (r₂ - r₃)/(1+r₃)`. For `τ.im ≥ 1`,
  `|1+r₃| ≥ 1/2` (from `theta3_norm_ge_half`), so `|s| ≤ 2(|r₂|+|r₃|) ≤ 16·exp(-π τ.im)`.
* `((1+r₂)/(1+r₃))⁴ - 1 = (1+s)⁴ - 1 = s(4 + 6s + 4s² + s³)`, with
  `|4 + 6s + 4s² + s³| ≤ 4 + 6|s| + 4|s|² + |s|³ ≤ 16` for `|s| ≤ 1`.
* So `|((1+r₂)/(1+r₃))⁴ - 1| ≤ 16|s| ≤ 256·exp(-π τ.im)`.
* Hence `‖λ - 16 e^(πi τ)‖ = 16·|e^(πi τ)|·|((1+r₂)/(1+r₃))⁴ - 1|`
  `≤ 16·exp(-π τ.im)·256·exp(-π τ.im) = 4096·exp(-2π τ.im)`.

This bound is loose; the actual leading correction is `-128 q²`. The
constant `4096 = 2^12` is chosen as a safety margin around the actual
coefficient. The bound suffices for the witness at `τ = (1+4i)/2`
(`τ.im = 2`): `Im(16 e^(πi τ)) = 16·exp(-2π) ≈ 0.030`,
`error ≤ 4096·exp(-4π) ≈ 0.014`, so `Im(λ) ≥ 0.016 > 0`. -/
theorem modularLambdaH_norm_sub_lead_le_of_im_ge_one {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖modularLambdaH τ - 16 * Complex.exp (Real.pi * Complex.I * τ)‖ ≤
      4096 * Real.exp (-2 * Real.pi * τ.im) := by
  have hτim_pos : 0 < τ.im := lt_of_lt_of_le zero_lt_one hτ
  have hπ_pos := Real.pi_pos
  -- A := 2·exp(πi τ/4); A^4 = 16·exp(πi τ).
  set A : ℂ := 2 * Complex.exp (Real.pi * Complex.I * τ / 4) with hA_def
  have hA_pow : A^4 = 16 * Complex.exp (Real.pi * Complex.I * τ) := by
    rw [hA_def, mul_pow]
    rw [show (Complex.exp (Real.pi * Complex.I * τ / 4))^4 =
        Complex.exp (4 * (Real.pi * Complex.I * τ / 4)) from by
      rw [← Complex.exp_nat_mul]; norm_cast]
    rw [show (4 : ℂ) * (Real.pi * Complex.I * τ / 4) = Real.pi * Complex.I * τ from by ring]
    norm_num
  rw [← hA_pow]
  -- ‖A‖ = 2·exp(-π τ.im/4).
  have hA_norm : ‖A‖ = 2 * Real.exp (-(Real.pi * τ.im / 4)) := by
    rw [hA_def, norm_mul, Complex.norm_exp]
    have h_re : (Real.pi * Complex.I * τ / 4 : ℂ).re = -(Real.pi * τ.im / 4) := by
      have h_eq : (Real.pi * Complex.I * τ / 4 : ℂ) =
          ((Real.pi / 4 : ℝ) : ℂ) * (Complex.I * τ) := by push_cast; ring
      rw [h_eq, Complex.mul_re]
      simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im]
      ring
    rw [h_re]
    simp
  have hA_norm_pos : 0 < ‖A‖ := by rw [hA_norm]; positivity
  have hA_ne : A ≠ 0 := norm_ne_zero_iff.mp hA_norm_pos.ne'
  -- ‖A‖^4 = 16·exp(-π τ.im).
  have hA_pow_norm : ‖A^4‖ = 16 * Real.exp (-(Real.pi * τ.im)) := by
    rw [norm_pow, hA_norm, mul_pow]
    have h_2_pow : (2 : ℝ)^4 = 16 := by norm_num
    have h_exp_pow : Real.exp (-(Real.pi * τ.im / 4)) ^ 4 = Real.exp (-(Real.pi * τ.im)) := by
      rw [← Real.exp_nat_mul]
      congr 1; ring
    rw [h_2_pow, h_exp_pow]
  -- r₂ := (θ₂ - A)/A; |r₂| ≤ 4·exp(-2π τ.im).
  set r₂ : ℂ := (theta2 τ - A) / A with hr2_def
  have h_th2_sub_A := theta2_norm_sub_lead_le_of_im_ge_one hτ
  have hr2_bound : ‖r₂‖ ≤ 4 * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [hr2_def, norm_div, hA_norm]
    have h_denom_pos : 0 < 2 * Real.exp (-(Real.pi * τ.im / 4)) := by positivity
    rw [div_le_iff₀ h_denom_pos]
    have h_target_eq :
        4 * Real.exp (-(2 * Real.pi * τ.im)) * (2 * Real.exp (-(Real.pi * τ.im / 4))) =
        8 * Real.exp (-(9 * Real.pi * τ.im / 4)) := by
      rw [show (4 * Real.exp (-(2 * Real.pi * τ.im)) * (2 * Real.exp (-(Real.pi * τ.im / 4))) : ℝ) =
          8 * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(Real.pi * τ.im / 4))) from by ring]
      rw [← Real.exp_add]
      exact congr_arg (fun x => 8 * Real.exp x) (by ring)
    rw [h_target_eq]; exact h_th2_sub_A
  -- r₃ := θ₃ - 1; |r₃| ≤ 4·exp(-π τ.im).
  set r₃ : ℂ := theta3 τ - 1 with hr3_def
  have hr3_bound : ‖r₃‖ ≤ 4 * Real.exp (-Real.pi * τ.im) :=
    theta3_sub_one_norm_le_exp_of_im_ge_one hτ
  -- θ₂ = A·(1 + r₂); θ₃ = 1 + r₃.
  have h_th2_eq : theta2 τ = A * (1 + r₂) := by
    rw [hr2_def]; field_simp; ring
  have h_th3_eq : theta3 τ = 1 + r₃ := by rw [hr3_def]; ring
  -- ‖θ₃‖ ≥ 1/2, so 1+r₃ ≠ 0 and ‖1+r₃‖ ≥ 1/2.
  have h_th3_norm_ge := theta3_norm_ge_half_of_im_ge_one hτ
  have h_1pr3_norm_ge : (1/2 : ℝ) ≤ ‖(1 + r₃ : ℂ)‖ := by rw [← h_th3_eq]; exact h_th3_norm_ge
  have h_1pr3_pos : 0 < ‖(1 + r₃ : ℂ)‖ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) h_1pr3_norm_ge
  have h_1pr3_ne : (1 + r₃ : ℂ) ≠ 0 := norm_ne_zero_iff.mp h_1pr3_pos.ne'
  -- λ = A^4 · ((1+r₂)/(1+r₃))^4.
  have h_lambda_eq : modularLambdaH τ = A^4 * ((1 + r₂)/(1 + r₃))^4 := by
    unfold modularLambdaH
    rw [h_th2_eq, h_th3_eq, mul_pow, div_pow]
    ring
  rw [h_lambda_eq]
  -- Factor out A^4.
  rw [show (A^4 * ((1 + r₂)/(1 + r₃))^4 - A^4 : ℂ) =
      A^4 * (((1 + r₂)/(1 + r₃))^4 - 1) from by ring]
  rw [norm_mul, hA_pow_norm]
  -- Let v := (1+r₂)/(1+r₃) - 1.
  set v : ℂ := (1 + r₂)/(1 + r₃) - 1 with hv_def
  have hv_add : (1 + r₂)/(1 + r₃) = 1 + v := by rw [hv_def]; ring
  -- v = (r₂ - r₃)/(1 + r₃).
  have hv_alt : v = (r₂ - r₃)/(1 + r₃) := by
    rw [hv_def]; field_simp; ring
  -- |v| ≤ 16·exp(-π τ.im).
  have hv_bound : ‖v‖ ≤ 16 * Real.exp (-(Real.pi * τ.im)) := by
    rw [hv_alt, norm_div]
    -- ‖r₂ - r₃‖ ≤ ‖r₂‖ + ‖r₃‖ ≤ 4·exp(-2π τ.im) + 4·exp(-π τ.im) ≤ 8·exp(-π τ.im).
    have h_r3_pos : (Real.exp (-Real.pi * τ.im) : ℝ) = Real.exp (-(Real.pi * τ.im)) := by
      congr 1; ring
    have h_r3_bound' : ‖r₃‖ ≤ 4 * Real.exp (-(Real.pi * τ.im)) := by
      rw [← h_r3_pos]; exact hr3_bound
    have h_r2_relax : Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(Real.pi * τ.im)) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have h_r2_bound' : ‖r₂‖ ≤ 4 * Real.exp (-(Real.pi * τ.im)) := by
      refine hr2_bound.trans ?_
      have : (0 : ℝ) ≤ 4 := by norm_num
      nlinarith
    have h_num_le : ‖r₂ - r₃‖ ≤ 8 * Real.exp (-(Real.pi * τ.im)) := by
      calc ‖r₂ - r₃‖ ≤ ‖r₂‖ + ‖r₃‖ := norm_sub_le _ _
        _ ≤ 4 * Real.exp (-(Real.pi * τ.im)) + 4 * Real.exp (-(Real.pi * τ.im)) := by
            linarith
        _ = 8 * Real.exp (-(Real.pi * τ.im)) := by ring
    -- ‖r₂ - r₃‖/‖1+r₃‖ ≤ 8 exp(-π τ.im)/(1/2) = 16 exp(-π τ.im).
    rw [div_le_iff₀ h_1pr3_pos]
    have h_calc : 16 * Real.exp (-(Real.pi * τ.im)) * ‖(1 + r₃ : ℂ)‖ ≥
        16 * Real.exp (-(Real.pi * τ.im)) * (1/2) := by
      apply mul_le_mul_of_nonneg_left h_1pr3_norm_ge
      positivity
    linarith
  -- |v| ≤ 1 (since 16·exp(-π) < 1 because exp(π) > 16).
  have hv_le_one : ‖v‖ ≤ 1 := by
    refine hv_bound.trans ?_
    -- 16 · exp(-π τ.im) ≤ 16 · exp(-π) ≤ 1.
    have h_exp_le : Real.exp (-(Real.pi * τ.im)) ≤ Real.exp (-Real.pi) := by
      apply Real.exp_le_exp.mpr; nlinarith
    -- exp(π) > exp(3) > 16: exp(1) > 2.71828, exp(3) > 2.71828^3 > 20 > 16.
    have h_e_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h_exp3_gt_16 : (16 : ℝ) < Real.exp 3 := by
      have h_eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [show (3 : ℝ) = 1 + 1 + 1 from by norm_num, Real.exp_add, Real.exp_add]
      rw [h_eq]
      nlinarith [h_e_gt, Real.exp_pos (1 : ℝ)]
    have h_pi_gt_3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h_exp_pi_gt_16 : (16 : ℝ) < Real.exp Real.pi :=
      h_exp3_gt_16.trans_le (Real.exp_le_exp.mpr h_pi_gt_3.le)
    have h_16_exp_neg_pi : 16 * Real.exp (-Real.pi) ≤ 1 := by
      rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
      linarith
    have h_mul := mul_le_mul_of_nonneg_left h_exp_le (by norm_num : (0:ℝ) ≤ 16)
    linarith [h_exp_le, h_16_exp_neg_pi, h_mul]
  -- (1+v)^4 - 1 = v · (4 + 6v + 4v² + v³).
  rw [hv_add]
  rw [show ((1 + v)^4 - 1 : ℂ) = v * (4 + 6*v + 4*v^2 + v^3) from by ring]
  rw [norm_mul]
  -- ‖4 + 6v + 4v² + v³‖ ≤ 4 + 6 + 4 + 1 = 15.
  have h_poly_bound : ‖(4 + 6*v + 4*v^2 + v^3 : ℂ)‖ ≤ 15 := by
    have h_v_sq : ‖v‖^2 ≤ 1 := by
      have := pow_le_pow_left₀ (norm_nonneg v) hv_le_one 2
      simpa using this
    have h_v_cube : ‖v‖^3 ≤ 1 := by
      have := pow_le_pow_left₀ (norm_nonneg v) hv_le_one 3
      simpa using this
    have h_4_eq : ‖((4 : ℂ))‖ = 4 := by norm_num
    have h_6v_eq : ‖((6 * v : ℂ))‖ = 6 * ‖v‖ := by
      rw [show ((6 * v : ℂ)) = (((6 : ℝ) : ℂ)) * v from by push_cast; ring]
      rw [norm_mul, Complex.norm_real]
      simp
    have h_4v2_eq : ‖((4 * v^2 : ℂ))‖ = 4 * ‖v‖^2 := by
      rw [show ((4 * v^2 : ℂ)) = (((4 : ℝ) : ℂ)) * v^2 from by push_cast; ring]
      rw [norm_mul, Complex.norm_real, norm_pow]
      simp
    have h_v3_eq : ‖(v^3)‖ = ‖v‖^3 := norm_pow v 3
    have h_chain :
        ‖(4 + 6*v + 4*v^2 + v^3 : ℂ)‖ ≤
          ‖((4 : ℂ))‖ + ‖((6*v : ℂ))‖ + ‖((4*v^2 : ℂ))‖ + ‖(v^3 : ℂ)‖ := by
      have h1 := norm_add_le ((4 + 6*v + 4*v^2 : ℂ)) ((v^3 : ℂ))
      have h2 := norm_add_le ((4 + 6*v : ℂ)) ((4*v^2 : ℂ))
      have h3 := norm_add_le ((4 : ℂ)) ((6*v : ℂ))
      linarith
    rw [h_4_eq, h_6v_eq, h_4v2_eq, h_v3_eq] at h_chain
    linarith [hv_le_one, h_v_sq, h_v_cube]
  -- ‖v‖ · ‖4 + 6v + 4v² + v³‖ ≤ 16·exp(-π τ.im) · 15 = 240·exp(-π τ.im).
  -- And 16·exp(-π τ.im) · 240·exp(-π τ.im) = 3840·exp(-2π τ.im) ≤ 4096·exp(-2π τ.im).
  have h_step1 : ‖v‖ * ‖(4 + 6*v + 4*v^2 + v^3 : ℂ)‖ ≤
      (16 * Real.exp (-(Real.pi * τ.im))) * 15 :=
    mul_le_mul hv_bound h_poly_bound (norm_nonneg _) (by positivity)
  have h_step2 : 16 * Real.exp (-(Real.pi * τ.im)) *
      ((16 * Real.exp (-(Real.pi * τ.im))) * 15) =
      3840 * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [show (16 * Real.exp (-(Real.pi * τ.im)) *
        (16 * Real.exp (-(Real.pi * τ.im)) * 15) : ℝ) =
        3840 * (Real.exp (-(Real.pi * τ.im)) * Real.exp (-(Real.pi * τ.im))) from by ring]
    rw [← Real.exp_add]
    exact congr_arg (fun x => 3840 * Real.exp x) (by ring)
  have h_exp_eq : Real.exp (-(2 * Real.pi * τ.im)) = Real.exp (-2 * Real.pi * τ.im) :=
    congr_arg Real.exp (by ring)
  have h_target_le : 3840 * Real.exp (-(2 * Real.pi * τ.im)) ≤
      4096 * Real.exp (-2 * Real.pi * τ.im) := by
    rw [h_exp_eq]
    have h_exp_nn : 0 ≤ Real.exp (-2 * Real.pi * τ.im) := (Real.exp_pos _).le
    nlinarith
  calc 16 * Real.exp (-(Real.pi * τ.im)) * (‖v‖ * ‖(4 + 6*v + 4*v^2 + v^3 : ℂ)‖)
      ≤ 16 * Real.exp (-(Real.pi * τ.im)) *
        ((16 * Real.exp (-(Real.pi * τ.im))) * 15) :=
        mul_le_mul_of_nonneg_left h_step1 (by positivity)
    _ = 3840 * Real.exp (-(2 * Real.pi * τ.im)) := h_step2
    _ ≤ 4096 * Real.exp (-2 * Real.pi * τ.im) := h_target_le

end NoWanderingDomains
