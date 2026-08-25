/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import NoWanderingDomains.Hyperbolic.ModularFunction.GammaTwoInvariance
import NoWanderingDomains.Hyperbolic.DiskModel.SchwarzReflection
import NoWanderingDomains.Hyperbolic.ModularLambda.ArgumentPrinciple
import Mathlib.Analysis.Complex.OpenMapping

/-! # The half-fundamental domain and real boundary arcs

The half-fundamental-domain triangle `F` of `Γ(2)` and its open interior `F°`, with
their basic topological properties. The theta nullwerte `θ₂, θ₃, θ₄` are real and
strictly monotone along the imaginary axis, so `λ` maps the three boundary arcs of `F`
(the vertical edges `Re τ = 0`, `Re τ = 1` and the semicircle `|2τ − 1| = 1`) into the
real axis. The conjugation symmetry `λ(−conj τ) = conj (λ τ)` and its
Schwarz-reflection variants through the line `Re τ = 1` and through the boundary
semicircle are derived from the corresponding theta identities. The right-edge cusp
limit `Re λ(1 + iy) → −∞` as `y → 0⁺` follows from the T-shift identity and the strict
bound `λ(iy) < 1`.
-/

namespace NoWanderingDomains
open Complex Filter Topology Set

/-- The half-fundamental-domain triangle of `Γ(2)` acting on the
upper half-plane: the strip `0 ≤ Re τ ≤ 1` with the half-disk
`|2τ − 1| < 1` removed. This is an ideal triangle with vertices
`0, 1, ∞` and hyperbolic area `π`, exactly half the `Γ(2)`-covolume
`2π`. The remaining half of `Γ(2)`-orbits is reached via the
conjugation symmetry `modularLambdaH_conj_symmetry`. The name
`Gamma2FundamentalDomain` is retained for continuity with the
classical literature, which often uses "fundamental domain" loosely
when one of the two halves is implicitly identified with the other
via a real-axis reflection. -/
def Gamma2FundamentalDomain : Set ℂ :=
  { τ : ℂ | 0 < τ.im ∧ 0 ≤ τ.re ∧ τ.re ≤ 1 ∧ 1 ≤ ‖2 * τ - 1‖ }

/-- The open interior of `Gamma2FundamentalDomain`: strict
inequalities on each of the three boundary arcs. -/
def Gamma2FundamentalDomainInterior : Set ℂ :=
  { τ : ℂ | 0 < τ.im ∧ 0 < τ.re ∧ τ.re < 1 ∧ 1 < ‖2 * τ - 1‖ }

/-! ## Basic topological properties -/

/-- `F` is contained in the upper half-plane. -/
theorem Gamma2FundamentalDomain_subset_upperHalf :
    Gamma2FundamentalDomain ⊆ { τ : ℂ | 0 < τ.im } := fun _ hτ => hτ.1

/-- `F^o` is contained in `F`. -/
theorem Gamma2FundamentalDomainInterior_subset :
    Gamma2FundamentalDomainInterior ⊆ Gamma2FundamentalDomain := by
  intro τ hτ
  exact ⟨hτ.1, hτ.2.1.le, hτ.2.2.1.le, hτ.2.2.2.le⟩

/-- `F^o` is contained in the upper half-plane. -/
theorem Gamma2FundamentalDomainInterior_subset_upperHalf :
    Gamma2FundamentalDomainInterior ⊆ { τ : ℂ | 0 < τ.im } := fun _ hτ => hτ.1

/-- The open interior `F^o` is an open subset of `ℂ`. -/
theorem Gamma2FundamentalDomainInterior_isOpen :
    IsOpen Gamma2FundamentalDomainInterior := by
  have h1 : IsOpen { τ : ℂ | 0 < τ.im } :=
    isOpen_lt continuous_const Complex.continuous_im
  have h2 : IsOpen { τ : ℂ | 0 < τ.re } :=
    isOpen_lt continuous_const Complex.continuous_re
  have h3 : IsOpen { τ : ℂ | τ.re < 1 } :=
    isOpen_lt Complex.continuous_re continuous_const
  have h4 : IsOpen { τ : ℂ | 1 < ‖2 * τ - 1‖ } := by
    apply isOpen_lt continuous_const
    fun_prop
  have h_eq : Gamma2FundamentalDomainInterior =
      { τ : ℂ | 0 < τ.im } ∩ { τ : ℂ | 0 < τ.re } ∩
      { τ : ℂ | τ.re < 1 } ∩ { τ : ℂ | 1 < ‖2 * τ - 1‖ } := by
    ext τ
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩
    · exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  rw [h_eq]
  exact (((h1.inter h2).inter h3).inter h4)

/-! ## Boundary-real values of `λ`

The three boundary arcs of `F` are mapped by `λ` to real-axis arcs.
This is the boundary-correspondence half of the biholomorphism: it
makes the `schwarzReflect_differentiableOn` hypothesis (real-axis
values) directly verifiable. -/

/-- `θ₃(iy)` is real for every `y > 0`. The Jacobi theta series at
purely imaginary argument is a sum of real exponentials
`exp(−π·n²·y)`, hence real. -/
theorem theta3_pure_imag_real {y : ℝ} (hy : 0 < y) :
    (theta3 (Complex.I * y)).im = 0 := by
  -- `theta3 (Iy) = jacobiTheta (Iy)`. From `hasSum_nat_jacobiTheta`,
  -- `(jacobiTheta(Iy) - 1)/2 = ∑ exp(π·I·(n+1)²·Iy) = ∑ exp(-π·(n+1)²·y)`.
  -- Each term is a positive real, so the sum is real and
  -- `(jacobiTheta(Iy)).im = 0`.
  unfold theta3
  have hτ_im : 0 < (Complex.I * (y : ℂ)).im := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, hy]
  have h_sum := hasSum_nat_jacobiTheta hτ_im
  -- Each term has imaginary part 0.
  have h_terms_real : ∀ n : ℕ,
      (Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((↑n : ℂ) + 1) ^ 2 * (Complex.I * (y : ℂ)))).im = 0 := by
    intro n
    have h_arg : (Real.pi : ℂ) * Complex.I * ((↑n : ℂ) + 1) ^ 2 *
        (Complex.I * (y : ℂ)) =
        ((-Real.pi * ((n : ℝ) + 1) ^ 2 * y : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
      ring
    rw [h_arg]
    exact Complex.exp_ofReal_im _
  -- Apply `HasSum.map Complex.imCLM`.
  have h_map := h_sum.map Complex.imCLM Complex.continuous_im
  -- Rewrite via funext to expose `(·).im` form.
  have h_funext : (fun n : ℕ => (Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((↑n : ℂ) + 1) ^ 2 * (Complex.I * (y : ℂ)))).im) = (fun _ : ℕ => (0 : ℝ)) := by
    funext n; exact h_terms_real n
  -- HasSum of zero is zero, so the target's `.im` is zero.
  have h_im_zero : ((jacobiTheta (Complex.I * (y : ℂ)) - 1) / 2).im = 0 := by
    have h_lhs : (⇑Complex.imCLM ∘ fun n : ℕ =>
        Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((↑n : ℂ) + 1) ^ 2 * (Complex.I * (y : ℂ)))) =
        (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      change (Complex.exp _).im = 0
      exact h_terms_real n
    rw [h_lhs] at h_map
    have h_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0 := hasSum_zero
    -- `Complex.imCLM z = z.im` by definition.
    exact h_map.unique h_zero
  -- Extract jacobiTheta(Iy).im = 0.
  have h_div : ((jacobiTheta (Complex.I * (y : ℂ)) - 1) / 2).im
      = (jacobiTheta (Complex.I * (y : ℂ)) - 1).im / 2 := by
    simp
  rw [h_div] at h_im_zero
  have h_sub_zero : (jacobiTheta (Complex.I * (y : ℂ)) - 1).im = 0 := by linarith
  have h_jt_im : (jacobiTheta (Complex.I * (y : ℂ))).im = 0 := by
    have h1 : (jacobiTheta (Complex.I * (y : ℂ))).im - (1 : ℂ).im = 0 := by
      rw [← Complex.sub_im]; exact h_sub_zero
    simpa using h1
  exact h_jt_im

/-- `θ₂(iy)` is real for every `y > 0`. The defining series
`exp(πiτ/4) · jacobiTheta₂(τ/2, τ)` reduces to a sum of real
exponentials at `τ = iy`. -/
theorem theta2_pure_imag_real {y : ℝ} (hy : 0 < y) :
    (theta2 (Complex.I * y)).im = 0 := by
  unfold theta2
  have hτ_im : 0 < (Complex.I * (y : ℂ)).im := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, hy]
  -- First factor: `exp(π·I·Iy/4) = exp(-πy/4)` is real.
  have h_first_im : (Complex.exp ((Real.pi : ℂ) * Complex.I *
      (Complex.I * (y : ℂ)) / 4)).im = 0 := by
    have h_arg : (Real.pi : ℂ) * Complex.I * (Complex.I * (y : ℂ)) / 4 =
        ((-Real.pi * y / 4 : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
      ring
    rw [h_arg]
    exact Complex.exp_ofReal_im _
  -- Second factor: `jacobiTheta₂(Iy/2, Iy)` is real.
  have h_second_im : (jacobiTheta₂ (Complex.I * (y : ℂ) / 2)
      (Complex.I * (y : ℂ))).im = 0 := by
    have h_sum := hasSum_jacobiTheta₂_term (Complex.I * (y : ℂ) / 2) hτ_im
    -- Each term `cexp(2πi n (Iy/2) + πi n² (Iy)) = cexp(-π·(n²+n)·y)` is real.
    have h_terms_real : ∀ n : ℤ,
        (jacobiTheta₂_term n (Complex.I * (y : ℂ) / 2)
          (Complex.I * (y : ℂ))).im = 0 := by
      intro n
      unfold jacobiTheta₂_term
      have h_arg : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) *
          (Complex.I * (y : ℂ) / 2) +
          (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 *
          (Complex.I * (y : ℂ)) =
          ((-Real.pi * ((n : ℝ) + (n : ℝ)^2) * y : ℝ) : ℂ) := by
        push_cast
        ring_nf
        rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
        ring
      rw [h_arg]
      exact Complex.exp_ofReal_im _
    have h_map := h_sum.map Complex.imCLM Complex.continuous_im
    have h_lhs : (⇑Complex.imCLM ∘ fun n : ℤ =>
        jacobiTheta₂_term n (Complex.I * (y : ℂ) / 2)
          (Complex.I * (y : ℂ))) =
        (fun _ : ℤ => (0 : ℝ)) := by
      funext n
      change (jacobiTheta₂_term n _ _).im = 0
      exact h_terms_real n
    rw [h_lhs] at h_map
    have h_zero : HasSum (fun _ : ℤ => (0 : ℝ)) 0 := hasSum_zero
    exact h_map.unique h_zero
  -- Combine: `(real · real).im = 0`.
  rw [Complex.mul_im, h_first_im, h_second_im]
  ring

/-- `θ₄(iy)` is real for every `y > 0`. Follows from
`theta3_pure_imag_real` via `theta4 τ = jacobiTheta (τ + 1)` and the
real-valuedness of the corresponding series at imaginary argument. -/
theorem theta4_pure_imag_real {y : ℝ} (hy : 0 < y) :
    (theta4 (Complex.I * y)).im = 0 := by
  unfold theta4
  have hτ_im : 0 < (Complex.I * (y : ℂ) + 1).im := by
    simp [Complex.add_im, Complex.mul_im, Complex.one_im, Complex.I_re, Complex.I_im, hy]
  have h_sum := hasSum_nat_jacobiTheta hτ_im
  -- Each term `exp(π·I·(n+1)²·(Iy+1))` factors as `real · (±1)`, hence real.
  have h_terms_real : ∀ n : ℕ,
      (Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((↑n : ℂ) + 1) ^ 2 * (Complex.I * (y : ℂ) + 1))).im = 0 := by
    intro n
    have h_split : (Real.pi : ℂ) * Complex.I * ((↑n : ℂ) + 1) ^ 2 *
        (Complex.I * (y : ℂ) + 1) =
        ((-Real.pi * ((n : ℝ) + 1) ^ 2 * y : ℝ) : ℂ) +
        ((↑n : ℂ) + 1) ^ 2 * ((Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring_nf
      rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
      ring
    rw [h_split, Complex.exp_add]
    have h1 : (Complex.exp ((-Real.pi * ((n : ℝ) + 1) ^ 2 * y : ℝ) : ℂ)).im = 0 :=
      Complex.exp_ofReal_im _
    have h2 : (Complex.exp (((↑n : ℂ) + 1) ^ 2 * ((Real.pi : ℂ) * Complex.I))).im = 0 := by
      rw [show ((↑n : ℂ) + 1) ^ 2 = (((n + 1)^2 : ℕ) : ℂ) from by push_cast; ring]
      rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
      rcases Nat.even_or_odd ((n + 1)^2) with hev | hod
      · rw [Even.neg_one_pow hev]; simp
      · rw [Odd.neg_one_pow hod]; simp
    rw [Complex.mul_im, h1, h2]
    ring
  -- Apply HasSum.map to extract `.im` of the partial sum.
  have h_map := h_sum.map Complex.imCLM Complex.continuous_im
  have h_lhs : (⇑Complex.imCLM ∘ fun n : ℕ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((↑n : ℂ) + 1) ^ 2 * (Complex.I * (y : ℂ) + 1))) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    change (Complex.exp _).im = 0
    exact h_terms_real n
  rw [h_lhs] at h_map
  have h_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0 := hasSum_zero
  have h_im_zero : ((jacobiTheta (Complex.I * (y : ℂ) + 1) - 1) / 2).im = 0 :=
    h_map.unique h_zero
  have h_div : ((jacobiTheta (Complex.I * (y : ℂ) + 1) - 1) / 2).im
      = (jacobiTheta (Complex.I * (y : ℂ) + 1) - 1).im / 2 := by simp
  rw [h_div] at h_im_zero
  have h_sub_zero : (jacobiTheta (Complex.I * (y : ℂ) + 1) - 1).im = 0 := by linarith
  have h_jt_im : (jacobiTheta (Complex.I * (y : ℂ) + 1)).im = 0 := by
    have h1 : (jacobiTheta (Complex.I * (y : ℂ) + 1)).im - (1 : ℂ).im = 0 := by
      rw [← Complex.sub_im]; exact h_sub_zero
    simpa using h1
  exact h_jt_im

/-- **Strict monotonicity of `θ₃(iy)`.** The function `y ↦ θ₃(iy).re`
is strictly antitone on `(0, ∞)`. Proof: the series
`θ₃(iy) = 1 + 2 · ∑ exp(−π·n²·y)` consists of positive terms, each
strictly decreasing in `y`; by termwise strict comparison
(`tsum_lt_tsum`), the sum is strictly decreasing. -/
theorem theta3_iy_strictAntitone :
    StrictAntiOn (fun y : ℝ => (theta3 (Complex.I * (y : ℂ))).re) (Set.Ioi 0) := by
  intro y1 hy1 y2 hy2 h_y12
  have hy1' : (0:ℝ) < y1 := hy1
  have hy2' : (0:ℝ) < y2 := hy2
  -- Imaginary parts of the τ's are positive.
  have hτ1_im : 0 < (Complex.I * (y1 : ℂ)).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, zero_add]
    exact hy1'
  have hτ2_im : 0 < (Complex.I * (y2 : ℂ)).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, zero_add]
    exact hy2'
  -- Each complex term equals a real-coerced real exponential.
  have h_arg : ∀ y : ℝ, ∀ n : ℕ,
      (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1)^2 * (Complex.I * (y : ℂ)) =
        ((-Real.pi * ((n : ℝ) + 1)^2 * y : ℝ) : ℂ) := by
    intro y n
    push_cast
    ring_nf
    rw [show (Complex.I : ℂ)^2 = -1 from Complex.I_sq]
    ring
  have h_term : ∀ y : ℝ, ∀ n : ℕ,
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1)^2 *
        (Complex.I * (y : ℂ))) =
        ((Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y) : ℝ) : ℂ) := by
    intro y n
    rw [h_arg y n, ← Complex.ofReal_exp]
  -- Series for jacobiTheta at τ = I·y.
  have h_sum1 := hasSum_nat_jacobiTheta hτ1_im
  have h_sum2 := hasSum_nat_jacobiTheta hτ2_im
  -- Rewrite the terms in real form.
  have h_sum1' : HasSum
      (fun n : ℕ => ((Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1) : ℝ) : ℂ))
      ((jacobiTheta (Complex.I * (y1 : ℂ)) - 1) / 2) := by
    convert h_sum1 using 1
    funext n
    exact (h_term y1 n).symm
  have h_sum2' : HasSum
      (fun n : ℕ => ((Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2) : ℝ) : ℂ))
      ((jacobiTheta (Complex.I * (y2 : ℂ)) - 1) / 2) := by
    convert h_sum2 using 1
    funext n
    exact (h_term y2 n).symm
  -- Take .re of the complex HasSums to get real HasSums.
  have h_sum1_re : HasSum
      (fun n : ℕ => Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1))
      ((jacobiTheta (Complex.I * (y1 : ℂ)) - 1).re / 2) := by
    have h_map := h_sum1'.map Complex.reCLM Complex.reCLM.continuous
    simp only [Complex.reCLM_apply] at h_map
    rwa [Complex.div_ofNat_re] at h_map
  have h_sum2_re : HasSum
      (fun n : ℕ => Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2))
      ((jacobiTheta (Complex.I * (y2 : ℂ)) - 1).re / 2) := by
    have h_map := h_sum2'.map Complex.reCLM Complex.reCLM.continuous
    simp only [Complex.reCLM_apply] at h_map
    rwa [Complex.div_ofNat_re] at h_map
  -- Each term is strictly larger for y1.
  have h_term_lt : ∀ n : ℕ,
      Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2) <
        Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1) := by
    intro n
    apply Real.exp_lt_exp.mpr
    have h_coeff_pos : 0 < Real.pi * ((n : ℝ) + 1)^2 := by
      have : 0 < ((n : ℝ) + 1)^2 := by positivity
      exact mul_pos Real.pi_pos this
    nlinarith
  -- Also need non-strict for tsum_lt_tsum.
  have h_term_le : ∀ n : ℕ,
      Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2) ≤
        Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1) := fun n => (h_term_lt n).le
  -- Strict comparison of sums.
  have h_tsum_lt : ∑' n : ℕ, Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2) <
      ∑' n : ℕ, Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1) := by
    exact Summable.tsum_lt_tsum h_term_le (h_term_lt 0) h_sum2_re.summable h_sum1_re.summable
  -- Express tsum in terms of jacobiTheta.
  have h_eq1 : ∑' n : ℕ, Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1) =
      (jacobiTheta (Complex.I * (y1 : ℂ)) - 1).re / 2 := h_sum1_re.tsum_eq
  have h_eq2 : ∑' n : ℕ, Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2) =
      (jacobiTheta (Complex.I * (y2 : ℂ)) - 1).re / 2 := h_sum2_re.tsum_eq
  -- Conclude.
  change (theta3 (Complex.I * (y2 : ℂ))).re < (theta3 (Complex.I * (y1 : ℂ))).re
  unfold theta3
  rw [h_eq1, h_eq2] at h_tsum_lt
  -- (jacobiTheta(τ_k) - 1).re/2 strict comparison gives jacobiTheta(τ_k).re comparison.
  have h_re_sub_eq : ∀ y : ℝ, (jacobiTheta (Complex.I * (y : ℂ)) - 1).re =
      (jacobiTheta (Complex.I * (y : ℂ))).re - 1 := by
    intro y; rw [Complex.sub_re, Complex.one_re]
  rw [h_re_sub_eq y1, h_re_sub_eq y2] at h_tsum_lt
  linarith

/-- **Pair-difference algebraic helper.** For `0 < y₁ < y₂` and
`1/y₁ ≤ α₁ < α₂`, the strict inequality
`exp(−α₂·y₁) − exp(−α₂·y₂) < exp(−α₁·y₁) − exp(−α₁·y₂)` holds.
Proof: factor out `exp(−α_i·y₁)`; reduces to comparing
`exp(α₁·d) > (1 − exp(−s·y₂))/(1 − exp(−s·y₁))` where
`s := α₂ − α₁ > 0`, `d := y₂ − y₁ > 0`. The RHS is bounded by `y₂/y₁`
via strict monotonicity of `x ↦ (1 − exp(−x))/x`; the LHS dominates
`exp(d/y₁) > y₂/y₁` via `Real.add_one_lt_exp` applied to
`y₂/y₁ − 1 > 0`. -/
private lemma exp_neg_diff_strict_dec {y1 y2 : ℝ} (hy1 : 0 < y1) (hy12 : y1 < y2)
    {α1 α2 : ℝ} (hα1 : 1 / y1 ≤ α1) (hα12 : α1 < α2) :
    Real.exp (-α2 * y1) - Real.exp (-α2 * y2) <
      Real.exp (-α1 * y1) - Real.exp (-α1 * y2) := by
  have hy2 : 0 < y2 := lt_trans hy1 hy12
  have hd_pos : 0 < y2 - y1 := sub_pos.mpr hy12
  have hα1_pos : 0 < α1 := lt_of_lt_of_le (one_div_pos.mpr hy1) hα1
  have hα2_pos : 0 < α2 := lt_trans hα1_pos hα12
  have hs_pos : 0 < α2 - α1 := sub_pos.mpr hα12
  set s := α2 - α1 with hs_def
  set d := y2 - y1 with hd_def
  -- Auxiliary: x ↦ (1 - exp(-x))/x strict decreasing on (0, ∞).
  -- Equivalent: x₂·(1 - exp(-x₁)) > x₁·(1 - exp(-x₂)) for 0 < x₁ < x₂.
  have key_aux : ∀ {x1 x2 : ℝ}, 0 < x1 → x1 < x2 →
      x1 * (1 - Real.exp (-x2)) < x2 * (1 - Real.exp (-x1)) := by
    intro x1 x2 hx1 h12
    have hδ : 0 < x2 - x1 := sub_pos.mpr h12
    have hx1_ne : x1 ≠ 0 := ne_of_gt hx1
    have hδ_ne : -(x2 - x1) ≠ 0 := by linarith
    -- (1 - exp(-x₁)) > x₁·exp(-x₁): from exp(x₁) > x₁ + 1.
    have h_step1 : x1 * Real.exp (-x1) < 1 - Real.exp (-x1) := by
      have h_exp_x1 : x1 + 1 < Real.exp x1 := Real.add_one_lt_exp hx1_ne
      have h_exp_neg_pos : 0 < Real.exp (-x1) := Real.exp_pos _
      have h_mul : Real.exp (-x1) * (x1 + 1) < Real.exp (-x1) * Real.exp x1 :=
        mul_lt_mul_of_pos_left h_exp_x1 h_exp_neg_pos
      rw [show Real.exp (-x1) * Real.exp x1 = 1 from by rw [← Real.exp_add]; simp] at h_mul
      nlinarith
    -- 1 - exp(-(x₂-x₁)) < x₂ - x₁: from exp(-(x₂-x₁)) > 1 - (x₂-x₁).
    have h_step2 : 1 - Real.exp (-(x2 - x1)) < x2 - x1 := by
      have := Real.add_one_lt_exp hδ_ne
      linarith
    -- Combine: (x₂-x₁)·(1 - exp(-x₁)) > (x₂-x₁)·x₁·exp(-x₁) > x₁·exp(-x₁)·(1 - exp(-(x₂-x₁))).
    have h_a : (x2 - x1) * (x1 * Real.exp (-x1)) < (x2 - x1) * (1 - Real.exp (-x1)) :=
      mul_lt_mul_of_pos_left h_step1 hδ
    have h_b : (1 - Real.exp (-(x2 - x1))) * (x1 * Real.exp (-x1)) <
        (x2 - x1) * (x1 * Real.exp (-x1)) :=
      mul_lt_mul_of_pos_right h_step2 (mul_pos hx1 (Real.exp_pos _))
    have h_combine : (x2 - x1) * (1 - Real.exp (-x1)) >
        x1 * Real.exp (-x1) * (1 - Real.exp (-(x2 - x1))) := by linarith
    -- Algebraic: x₂·(1 - exp(-x₁)) - x₁·(1 - exp(-x₂)) =
    -- (x₂-x₁)·(1 - exp(-x₁)) - x₁·exp(-x₁)·(1 - exp(-(x₂-x₁))).
    have h_expand : x2 * (1 - Real.exp (-x1)) - x1 * (1 - Real.exp (-x2)) =
        (x2 - x1) * (1 - Real.exp (-x1)) -
          x1 * Real.exp (-x1) * (1 - Real.exp (-(x2 - x1))) := by
      have hx2_eq : x2 = x1 + (x2 - x1) := by ring
      rw [show (-x2) = (-x1) + (-(x2 - x1)) from by ring]
      rw [Real.exp_add]
      ring
    linarith
  -- Apply key_aux with x₁ := s·y₁, x₂ := s·y₂.
  have hsy1_pos : 0 < s * y1 := mul_pos hs_pos hy1
  have hsy12 : s * y1 < s * y2 := mul_lt_mul_of_pos_left hy12 hs_pos
  have h_ratio_s : (s * y1) * (1 - Real.exp (-(s * y2))) <
      (s * y2) * (1 - Real.exp (-(s * y1))) := key_aux hsy1_pos hsy12
  -- Divide by s > 0: y₁·(1 - exp(-s·y₂)) < y₂·(1 - exp(-s·y₁)).
  have h_ratio : y1 * (1 - Real.exp (-(s * y2))) < y2 * (1 - Real.exp (-(s * y1))) := by
    have h_lhs_eq : (s * y1) * (1 - Real.exp (-(s * y2))) =
        s * (y1 * (1 - Real.exp (-(s * y2)))) := by ring
    have h_rhs_eq : (s * y2) * (1 - Real.exp (-(s * y1))) =
        s * (y2 * (1 - Real.exp (-(s * y1)))) := by ring
    rw [h_lhs_eq, h_rhs_eq] at h_ratio_s
    exact lt_of_mul_lt_mul_left h_ratio_s hs_pos.le
  -- exp(α₁·d) > y₂/y₁ via α₁·d ≥ y₂/y₁ - 1 (from α₁ ≥ 1/y₁) and add_one_lt_exp.
  have hτ_gt_one : 1 < y2 / y1 := by rw [lt_div_iff₀ hy1, one_mul]; exact hy12
  have hτm_ne : y2 / y1 - 1 ≠ 0 := by linarith
  have h_τ_lt : y2 / y1 < Real.exp (y2 / y1 - 1) := by
    have := Real.add_one_lt_exp hτm_ne; linarith
  have hα1d_ge : y2 / y1 - 1 ≤ α1 * d := by
    have h_eq : y2 / y1 - 1 = (y2 - y1) / y1 := by field_simp
    have h_d_unfold : d = y2 - y1 := hd_def
    rw [h_eq, h_d_unfold, div_le_iff₀ hy1]
    have h_α1_y1 : 1 ≤ α1 * y1 := by
      have h_one : (1 / y1) * y1 = 1 := by field_simp
      have := mul_le_mul_of_nonneg_right hα1 hy1.le
      linarith
    nlinarith [hd_pos]
  have h_exp_α1d_gt : y2 / y1 < Real.exp (α1 * d) :=
    lt_of_lt_of_le h_τ_lt (Real.exp_le_exp.mpr hα1d_ge)
  -- Now derive the main: exp(-α₁·y₁)·(1 - exp(-s·y₁)) > exp(-α₁·y₂)·(1 - exp(-s·y₂)).
  have hp1_pos : 0 < 1 - Real.exp (-(s * y1)) := by
    have : Real.exp (-(s * y1)) < 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_strictMono (by linarith)
    linarith
  have h_step_a : y2 < Real.exp (α1 * d) * y1 := by
    have h_mul := mul_lt_mul_of_pos_right h_exp_α1d_gt hy1
    rwa [div_mul_cancel₀ y2 (ne_of_gt hy1)] at h_mul
  have h_step_b : y2 * (1 - Real.exp (-(s * y1))) <
      Real.exp (α1 * d) * y1 * (1 - Real.exp (-(s * y1))) :=
    mul_lt_mul_of_pos_right h_step_a hp1_pos
  have h_step_c : y1 * (1 - Real.exp (-(s * y2))) <
      Real.exp (α1 * d) * y1 * (1 - Real.exp (-(s * y1))) := lt_trans h_ratio h_step_b
  have h_step_d : 1 - Real.exp (-(s * y2)) <
      Real.exp (α1 * d) * (1 - Real.exp (-(s * y1))) := by
    have h_rewrite : Real.exp (α1 * d) * y1 * (1 - Real.exp (-(s * y1))) =
        y1 * (Real.exp (α1 * d) * (1 - Real.exp (-(s * y1)))) := by ring
    rw [h_rewrite] at h_step_c
    exact lt_of_mul_lt_mul_left h_step_c hy1.le
  -- Multiply by exp(-α₁·y₂) > 0 and use exp(-α₁·y₂)·exp(α₁·d) = exp(-α₁·y₁).
  have h_exp_neg_α1y2_pos : 0 < Real.exp (-α1 * y2) := Real.exp_pos _
  have h_step_e : Real.exp (-α1 * y2) * (1 - Real.exp (-(s * y2))) <
      Real.exp (-α1 * y2) * (Real.exp (α1 * d) * (1 - Real.exp (-(s * y1)))) :=
    mul_lt_mul_of_pos_left h_step_d h_exp_neg_α1y2_pos
  have h_eq_combine : Real.exp (-α1 * y2) * (Real.exp (α1 * d) * (1 - Real.exp (-(s * y1)))) =
      Real.exp (-α1 * y1) * (1 - Real.exp (-(s * y1))) := by
    rw [show Real.exp (-α1 * y2) * (Real.exp (α1 * d) * (1 - Real.exp (-(s * y1))))
          = Real.exp (-α1 * y2) * Real.exp (α1 * d) * (1 - Real.exp (-(s * y1))) from by ring,
       ← Real.exp_add]
    congr 2
    simp [d]; ring
  rw [h_eq_combine] at h_step_e
  -- Expand exp(-α₁·y) - exp(-α₂·y) = exp(-α₁·y)·(1 - exp(-s·y)).
  have h_expand_y1 : Real.exp (-α1 * y1) - Real.exp (-α2 * y1) =
      Real.exp (-α1 * y1) * (1 - Real.exp (-(s * y1))) := by
    rw [show -α2 * y1 = -α1 * y1 + -(s * y1) from by simp [s]; ring]
    rw [Real.exp_add]; ring
  have h_expand_y2 : Real.exp (-α1 * y2) - Real.exp (-α2 * y2) =
      Real.exp (-α1 * y2) * (1 - Real.exp (-(s * y2))) := by
    rw [show -α2 * y2 = -α1 * y2 + -(s * y2) from by simp [s]; ring]
    rw [Real.exp_add]; ring
  linarith [h_step_e, h_expand_y1, h_expand_y2]

/-- **Auxiliary: strict monotonicity of `θ₄(iy)` for `y ≥ 1`.**
Alternating series: `θ₄(iy) − 1 = 2·∑_{n≥0} (−1)^(n+1) exp(−π(n+1)²y)`.
Pair consecutive terms (`n=2k`, `n=2k+1`) using `HasSum.even_add_odd`
to express `(θ₄(iy) − 1)/2 = ∑_{k≥0}[exp(−π(2k+2)²y) − exp(−π(2k+1)²y)]`,
equivalently `1 − θ₄(iy) = 2·∑_{k≥0} A_k(y)` where
`A_k(y) := exp(−π(2k+1)²y) − exp(−π(2k+2)²y) > 0`. For `y ≥ 1`,
`exp_neg_diff_strict_dec` applied with `α_1 := π(2k+1)² ≥ π > 1 = 1/y`
gives `A_k(y_1) > A_k(y_2)` for `1 ≤ y_1 < y_2`. Termwise strict
comparison via `Summable.tsum_lt_tsum` finishes. -/
theorem theta4_iy_strictMono_aux_large :
    StrictMonoOn (fun y : ℝ => (theta4 (Complex.I * (y : ℂ))).re) (Set.Ici 1) := by
  intro y1 hy1 y2 hy2 h_y12
  have hy1' : (1:ℝ) ≤ y1 := hy1
  have hy2' : (1:ℝ) ≤ y2 := hy2
  have hy1_pos : (0:ℝ) < y1 := lt_of_lt_of_le zero_lt_one hy1'
  have hy2_pos : (0:ℝ) < y2 := lt_of_lt_of_le zero_lt_one hy2'
  change (theta4 (Complex.I * (y1 : ℂ))).re < (theta4 (Complex.I * (y2 : ℂ))).re
  -- Translate to jacobiTheta at τ = I·y + 1.
  have hτ1_im : 0 < (Complex.I * (y1 : ℂ) + 1).im := by
    simp only [Complex.add_im, Complex.mul_im, Complex.one_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add, add_zero]
    exact hy1_pos
  have hτ2_im : 0 < (Complex.I * (y2 : ℂ) + 1).im := by
    simp only [Complex.add_im, Complex.mul_im, Complex.one_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add, add_zero]
    exact hy2_pos
  -- Each complex term equals `(-1)^(n+1) · exp(-π(n+1)²y)` (real).
  have h_term : ∀ y : ℝ, ∀ n : ℕ,
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1)^2 *
        (Complex.I * (y : ℂ) + 1)) =
        (((-1 : ℝ)^(n+1) * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y) : ℝ) : ℂ) := by
    intro y n
    have h_split : (Real.pi : ℂ) * Complex.I * ((↑n : ℂ) + 1) ^ 2 *
        (Complex.I * (y : ℂ) + 1) =
        ((-Real.pi * ((n : ℝ) + 1) ^ 2 * y : ℝ) : ℂ) +
        ((↑n : ℂ) + 1) ^ 2 * ((Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring_nf
      rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
      ring
    rw [h_split, Complex.exp_add]
    rw [show ((↑n : ℂ) + 1) ^ 2 = (((n + 1)^2 : ℕ) : ℂ) from by push_cast; ring]
    rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    rw [← Complex.ofReal_exp]
    have h_parity : ((-1 : ℂ))^((n+1)^2) = (((-1 : ℝ)^(n+1) : ℝ) : ℂ) := by
      rcases Nat.even_or_odd (n+1) with hn | hn
      · have h2 : Even ((n+1)^2) := by
          obtain ⟨k, hk⟩ := hn
          refine ⟨k * (k + k), ?_⟩
          have heq : (n + 1)^2 = (k + k)^2 := by rw [hk]
          rw [heq]; ring
        rw [Even.neg_one_pow h2, Even.neg_one_pow hn]
        simp
      · have h2 : Odd ((n+1)^2) := by
          have hsq : (n+1)^2 = (n+1) * (n+1) := sq (n+1)
          rw [hsq]
          exact hn.mul hn
        rw [Odd.neg_one_pow h2, Odd.neg_one_pow hn]
        simp
    rw [h_parity]
    push_cast
    ring
  -- Apply HasSum.
  have h_sum1 := hasSum_nat_jacobiTheta hτ1_im
  have h_sum2 := hasSum_nat_jacobiTheta hτ2_im
  have h_sum1' : HasSum
      (fun n : ℕ => (((-1 : ℝ)^(n+1) * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1) : ℝ) : ℂ))
      ((jacobiTheta (Complex.I * (y1 : ℂ) + 1) - 1) / 2) := by
    convert h_sum1 using 1
    funext n
    exact (h_term y1 n).symm
  have h_sum2' : HasSum
      (fun n : ℕ => (((-1 : ℝ)^(n+1) * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2) : ℝ) : ℂ))
      ((jacobiTheta (Complex.I * (y2 : ℂ) + 1) - 1) / 2) := by
    convert h_sum2 using 1
    funext n
    exact (h_term y2 n).symm
  -- Map to real HasSum.
  have h_sum1_re : HasSum
      (fun n : ℕ => (-1 : ℝ)^(n+1) * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y1))
      ((jacobiTheta (Complex.I * (y1 : ℂ) + 1) - 1).re / 2) := by
    have h_map := h_sum1'.map Complex.reCLM Complex.reCLM.continuous
    simp only [Complex.reCLM_apply] at h_map
    rwa [Complex.div_ofNat_re] at h_map
  have h_sum2_re : HasSum
      (fun n : ℕ => (-1 : ℝ)^(n+1) * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y2))
      ((jacobiTheta (Complex.I * (y2 : ℂ) + 1) - 1).re / 2) := by
    have h_map := h_sum2'.map Complex.reCLM Complex.reCLM.continuous
    simp only [Complex.reCLM_apply] at h_map
    rwa [Complex.div_ofNat_re] at h_map
  -- Define f y n := (-1)^(n+1) · exp(-π·(n+1)²·y).
  set f : ℝ → ℕ → ℝ := fun y n => (-1 : ℝ)^(n+1) * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y)
    with f_def
  -- Pair sum: f y (2k) + f y (2k+1) = -A_k(y).
  have h_pair_eq : ∀ y : ℝ, ∀ k : ℕ,
      f y (2*k) + f y (2*k+1) =
        -(Real.exp (-Real.pi * ((2*k:ℝ)+1)^2 * y) -
          Real.exp (-Real.pi * ((2*k:ℝ)+2)^2 * y)) := by
    intro y k
    simp only [f_def]
    have h_2k_plus_1_odd : Odd (2*k+1) := ⟨k, rfl⟩
    have h_2k_plus_2_even : Even (2*k+2) := ⟨k+1, by ring⟩
    have h_eq1 : ((-1 : ℝ))^(2*k+1) = -1 := h_2k_plus_1_odd.neg_one_pow
    have h_eq2 : ((-1 : ℝ))^(2*k+1+1) = 1 := h_2k_plus_2_even.neg_one_pow
    rw [h_eq1, h_eq2]
    push_cast
    ring_nf
  -- Get summability of subseries.
  have h_sum_even1 : Summable (fun k => f y1 (2*k)) :=
    h_sum1_re.summable.comp_injective (fun _ _ hab => by omega)
  have h_sum_odd1 : Summable (fun k => f y1 (2*k+1)) :=
    h_sum1_re.summable.comp_injective (fun _ _ hab => by omega)
  have h_sum_even2 : Summable (fun k => f y2 (2*k)) :=
    h_sum2_re.summable.comp_injective (fun _ _ hab => by omega)
  have h_sum_odd2 : Summable (fun k => f y2 (2*k+1)) :=
    h_sum2_re.summable.comp_injective (fun _ _ hab => by omega)
  -- Combine subseries: by HasSum.even_add_odd, even + odd = full.
  have h_even_odd1 :
      HasSum (f y1)
        (∑' k, f y1 (2*k) + ∑' k, f y1 (2*k+1)) :=
    HasSum.even_add_odd h_sum_even1.hasSum h_sum_odd1.hasSum
  have h_even_odd2 :
      HasSum (f y2)
        (∑' k, f y2 (2*k) + ∑' k, f y2 (2*k+1)) :=
    HasSum.even_add_odd h_sum_even2.hasSum h_sum_odd2.hasSum
  have h_unique1 : ∑' k, f y1 (2*k) + ∑' k, f y1 (2*k+1) =
      (jacobiTheta (Complex.I * (y1 : ℂ) + 1) - 1).re / 2 :=
    h_even_odd1.unique h_sum1_re
  have h_unique2 : ∑' k, f y2 (2*k) + ∑' k, f y2 (2*k+1) =
      (jacobiTheta (Complex.I * (y2 : ℂ) + 1) - 1).re / 2 :=
    h_even_odd2.unique h_sum2_re
  -- HasSum of pair sums = full sum.
  have h_pair_sum1 :
      HasSum (fun k => f y1 (2*k) + f y1 (2*k+1))
        ((jacobiTheta (Complex.I * (y1 : ℂ) + 1) - 1).re / 2) := by
    have h := h_sum_even1.hasSum.add h_sum_odd1.hasSum
    rwa [h_unique1] at h
  have h_pair_sum2 :
      HasSum (fun k => f y2 (2*k) + f y2 (2*k+1))
        ((jacobiTheta (Complex.I * (y2 : ℂ) + 1) - 1).re / 2) := by
    have h := h_sum_even2.hasSum.add h_sum_odd2.hasSum
    rwa [h_unique2] at h
  -- Rewrite as -A_k(y).
  set A : ℝ → ℕ → ℝ := fun y k =>
    Real.exp (-Real.pi * ((2*k:ℝ)+1)^2 * y) - Real.exp (-Real.pi * ((2*k:ℝ)+2)^2 * y)
    with A_def
  have h_neg_A1 : HasSum (fun k => -A y1 k)
      ((jacobiTheta (Complex.I * (y1 : ℂ) + 1) - 1).re / 2) := by
    convert h_pair_sum1 using 1
    funext k
    rw [A_def, h_pair_eq y1 k]
  have h_neg_A2 : HasSum (fun k => -A y2 k)
      ((jacobiTheta (Complex.I * (y2 : ℂ) + 1) - 1).re / 2) := by
    convert h_pair_sum2 using 1
    funext k
    rw [A_def, h_pair_eq y2 k]
  -- HasSum of A_k(y) = - ((θ₄(iy) - 1).re / 2).
  have h_A1 : HasSum (A y1) (-(jacobiTheta (Complex.I * (y1 : ℂ) + 1) - 1).re / 2) := by
    have h := h_neg_A1.neg
    simp only [neg_neg] at h
    convert! h using 1
    ring
  have h_A2 : HasSum (A y2) (-(jacobiTheta (Complex.I * (y2 : ℂ) + 1) - 1).re / 2) := by
    have h := h_neg_A2.neg
    simp only [neg_neg] at h
    convert! h using 1
    ring
  -- Strict comparison of A's: A_k(y2) < A_k(y1).
  have h_A_lt : ∀ k : ℕ, A y2 k < A y1 k := by
    intro k
    simp only [A_def]
    -- Apply exp_neg_diff_strict_dec with α₁ = π(2k+1)², α₂ = π(2k+2)².
    set α1 := Real.pi * ((2*k:ℝ) + 1)^2 with α1_def
    set α2 := Real.pi * ((2*k:ℝ) + 2)^2 with α2_def
    have hα1_pos : 0 < α1 := by
      apply mul_pos Real.pi_pos
      positivity
    have hα12 : α1 < α2 := by
      simp only [α1_def, α2_def]
      apply mul_lt_mul_of_pos_left _ Real.pi_pos
      have h1 : (0 : ℝ) ≤ (2*k:ℝ) + 1 := by positivity
      have h2 : (2*k:ℝ) + 1 < (2*k:ℝ) + 2 := by linarith
      exact pow_lt_pow_left₀ h2 h1 (by norm_num)
    have hα1_ge : 1 / y1 ≤ α1 := by
      have h_inv_le_one : 1 / y1 ≤ 1 := by
        rw [div_le_one hy1_pos]; exact hy1'
      have h_α1_ge : (1 : ℝ) ≤ α1 := by
        simp only [α1_def]
        have h1 : (1 : ℝ) ≤ ((2*k:ℝ) + 1)^2 := by
          have h_ge_one : (1 : ℝ) ≤ (2*k:ℝ) + 1 := by
            have : (0 : ℝ) ≤ (2*k:ℝ) := by positivity
            linarith
          calc (1 : ℝ) = 1^2 := by norm_num
            _ ≤ ((2*k:ℝ) + 1)^2 := pow_le_pow_left₀ (by norm_num) h_ge_one 2
        have h2 : Real.pi * 1 ≤ Real.pi * ((2*k:ℝ) + 1)^2 :=
          mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
        have h3 : (1 : ℝ) < Real.pi := Real.pi_gt_three.trans' (by norm_num)
        linarith
      linarith
    -- Apply exp_neg_diff_strict_dec.
    have h_dec := exp_neg_diff_strict_dec hy1_pos h_y12 hα1_ge hα12
    -- h_dec : exp(-α2·y1) - exp(-α2·y2) < exp(-α1·y1) - exp(-α1·y2).
    -- We want: exp(-α1·y2) - exp(-α2·y2) < exp(-α1·y1) - exp(-α2·y1).
    -- These are equivalent after rearrangement.
    change Real.exp (-Real.pi * ((2 * (k:ℝ)) + 1)^2 * y2) -
        Real.exp (-Real.pi * ((2 * (k:ℝ)) + 2)^2 * y2) <
        Real.exp (-Real.pi * ((2 * (k:ℝ)) + 1)^2 * y1) -
        Real.exp (-Real.pi * ((2 * (k:ℝ)) + 2)^2 * y1)
    have h_α1_eq : α1 = Real.pi * ((2 * (k:ℝ)) + 1)^2 := α1_def
    have h_α2_eq : α2 = Real.pi * ((2 * (k:ℝ)) + 2)^2 := α2_def
    have h_α1_y1 : -α1 * y1 = -Real.pi * ((2 * (k:ℝ)) + 1)^2 * y1 := by
      rw [h_α1_eq]; ring
    have h_α1_y2 : -α1 * y2 = -Real.pi * ((2 * (k:ℝ)) + 1)^2 * y2 := by
      rw [h_α1_eq]; ring
    have h_α2_y1 : -α2 * y1 = -Real.pi * ((2 * (k:ℝ)) + 2)^2 * y1 := by
      rw [h_α2_eq]; ring
    have h_α2_y2 : -α2 * y2 = -Real.pi * ((2 * (k:ℝ)) + 2)^2 * y2 := by
      rw [h_α2_eq]; ring
    rw [h_α1_y1, h_α1_y2, h_α2_y1, h_α2_y2] at h_dec
    linarith
  have h_A_le : ∀ k : ℕ, A y2 k ≤ A y1 k := fun k => (h_A_lt k).le
  -- Apply Summable.tsum_lt_tsum.
  have h_tsum_lt : ∑' k, A y2 k < ∑' k, A y1 k := by
    exact Summable.tsum_lt_tsum h_A_le (h_A_lt 0) h_A2.summable h_A1.summable
  rw [h_A1.tsum_eq, h_A2.tsum_eq] at h_tsum_lt
  -- h_tsum_lt : -(θ₄(iy2) - 1)/2 < -(θ₄(iy1) - 1)/2  ⇒  (θ₄(iy1)).re < (θ₄(iy2)).re.
  change (theta4 (Complex.I * (y1 : ℂ))).re < (theta4 (Complex.I * (y2 : ℂ))).re
  unfold theta4
  have h_re_sub : ∀ y : ℝ, (jacobiTheta (Complex.I * (y : ℂ) + 1) - 1).re =
      (jacobiTheta (Complex.I * (y : ℂ) + 1)).re - 1 := by
    intro y; rw [Complex.sub_re, Complex.one_re]
  rw [h_re_sub y1, h_re_sub y2] at h_tsum_lt
  linarith

/-- **Modular transformation specialized to imaginary axis.**
For `y > 0`, `θ_4(iy)·√y = θ_2(i/y)` (both sides real). Specialization
of `theta4_S_smul` at `τ = i/y`, using `√(1/y) = 1/√y`. -/
theorem theta4_iy_mul_sqrt_eq_theta2 {y : ℝ} (hy : 0 < y) :
    (theta4 (Complex.I * (y : ℂ))).re * Real.sqrt y =
      (theta2 (Complex.I / (y : ℂ))).re := by
  have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hy)
  -- The point i/y has positive imaginary part 1/y.
  have h_inv_eq : Complex.I / (y : ℂ) = ((1 / y : ℝ) : ℂ) * Complex.I := by
    rw [show (Complex.I / (y : ℂ)) = Complex.I * ((y : ℂ))⁻¹ from div_eq_mul_inv _ _]
    push_cast
    ring
  have h_inv_im : 0 < (Complex.I / (y : ℂ)).im := by
    rw [h_inv_eq]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, add_zero]
    positivity
  -- Apply theta4_S_smul at τ = I/y.
  have h_S := theta4_S_smul h_inv_im
  -- Simplify -1 / (I/y) = I·y.
  have h_neg_inv : -1 / (Complex.I / (y : ℂ)) = Complex.I * (y : ℂ) := by
    rw [div_div_eq_mul_div, Complex.div_I]
    ring
  rw [h_neg_inv] at h_S
  -- Simplify -I·(I/y) = 1/y.
  have h_factor : (-Complex.I * (Complex.I / (y : ℂ))) = ((1 / y : ℝ) : ℂ) := by
    rw [show (-Complex.I * (Complex.I / (y : ℂ))) =
        (-(Complex.I * Complex.I)) / (y : ℂ) from by ring]
    rw [show Complex.I * Complex.I = -1 from by rw [← sq]; exact Complex.I_sq]
    push_cast
    ring
  rw [h_factor] at h_S
  -- Convert (1/y)^(1/2 : ℂ) to (Real.sqrt (1/y) : ℂ) = (1/√y : ℂ).
  have hy_inv_nn : (0 : ℝ) ≤ 1 / y := by positivity
  have h_cpow : (((1 / y : ℝ) : ℂ)) ^ (1/2 : ℂ) = (((1 / y : ℝ) ^ (1/2 : ℝ) : ℝ) : ℂ) := by
    rw [show (1/2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) from by push_cast; ring]
    exact (Complex.ofReal_cpow hy_inv_nn (1/2)).symm
  rw [h_cpow] at h_S
  -- Simplify (1/y)^(1/2) = 1/√y as real.
  have h_real_pow : ((1 / y : ℝ) ^ (1/2 : ℝ) : ℝ) = 1 / Real.sqrt y := by
    rw [← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, one_div]
  rw [h_real_pow] at h_S
  -- Now: theta4 (I*y) = (1/√y : ℂ) · theta2 (I/y).
  -- Multiply both sides by (√y : ℂ).
  have hy_sqrt_pos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hy_sqrt_ne : (Real.sqrt y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hy_sqrt_pos)
  have h_eq : theta4 (Complex.I * (y : ℂ)) * ((Real.sqrt y : ℝ) : ℂ) =
      theta2 (Complex.I / (y : ℂ)) := by
    rw [h_S]
    have : (((1 / Real.sqrt y : ℝ)) : ℂ) = ((Real.sqrt y : ℝ) : ℂ)⁻¹ := by
      push_cast
      rw [one_div]
    rw [this]
    field_simp
  -- Take real parts.
  have h_re : (theta4 (Complex.I * (y : ℂ)) * ((Real.sqrt y : ℝ) : ℂ)).re =
      (theta2 (Complex.I / (y : ℂ))).re := by
    rw [h_eq]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h_re
  exact h_re

/-- **Pair helper for the small-`y` regime.** For `α ≥ 1/2` and
`1 ≤ u₂ < u₁`, the strict bound
`√u₁ · exp(-α·u₁) < √u₂ · exp(-α·u₂)` holds. Derivation:
`u₁/u₂ = 1 + (u₁−u₂)/u₂ < exp((u₁−u₂)/u₂)` (from `Real.add_one_lt_exp`),
hence `√(u₁/u₂) < exp((u₁−u₂)/(2u₂))`. Since `1/(2u₂) ≤ 1/2 ≤ α`,
this gives `√(u₁/u₂) < exp(α(u₁−u₂))`, i.e., the claim. -/
private lemma sqrt_exp_strict_dec {α u1 u2 : ℝ} (hα : 1 / 2 ≤ α) (hu2 : 1 ≤ u2)
    (hu12 : u2 < u1) :
    Real.sqrt u1 * Real.exp (-α * u1) < Real.sqrt u2 * Real.exp (-α * u2) := by
  have hu2_pos : 0 < u2 := lt_of_lt_of_le zero_lt_one hu2
  have hu1_pos : 0 < u1 := lt_trans hu2_pos hu12
  have hd_pos : 0 < u1 - u2 := sub_pos.mpr hu12
  have hsu1_pos : 0 < Real.sqrt u1 := Real.sqrt_pos.mpr hu1_pos
  have hsu2_pos : 0 < Real.sqrt u2 := Real.sqrt_pos.mpr hu2_pos
  -- Key inequality: u₁/u₂ < exp((u₁−u₂)/u₂).
  have hu2_ne0 : u2 ≠ 0 := ne_of_gt hu2_pos
  have h_div_eq : u1 / u2 = 1 + (u1 - u2) / u2 := by
    field_simp; ring
  have hd_div_pos : 0 < (u1 - u2) / u2 := div_pos hd_pos hu2_pos
  have h_div_ne : (u1 - u2) / u2 ≠ 0 := ne_of_gt hd_div_pos
  have h_exp_lt_aux : (u1 - u2) / u2 + 1 < Real.exp ((u1 - u2) / u2) :=
    Real.add_one_lt_exp h_div_ne
  have h_u_ratio_lt : u1 / u2 < Real.exp ((u1 - u2) / u2) := by
    rw [h_div_eq]; linarith
  -- exp((u₁−u₂)/u₂) = (exp((u₁−u₂)/(2u₂)))².
  have h_exp_sq : Real.exp ((u1 - u2) / u2) = (Real.exp ((u1 - u2) / (2*u2)))^2 := by
    rw [show ((Real.exp ((u1 - u2) / (2*u2)))^2 : ℝ) =
        Real.exp ((u1 - u2) / (2*u2)) * Real.exp ((u1 - u2) / (2*u2)) from sq _]
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  -- √(u₁/u₂) < exp((u₁−u₂)/(2u₂)).
  have h_sqrt_lt : Real.sqrt (u1/u2) < Real.exp ((u1 - u2) / (2 * u2)) := by
    have h_pos_u : 0 ≤ u1/u2 := by positivity
    have h_pos_exp : 0 ≤ Real.exp ((u1 - u2) / (2 * u2)) := (Real.exp_pos _).le
    have h_eq : Real.exp ((u1 - u2) / (2 * u2)) =
        Real.sqrt ((Real.exp ((u1 - u2) / (2 * u2)))^2) := (Real.sqrt_sq h_pos_exp).symm
    rw [h_eq, ← h_exp_sq]
    exact Real.sqrt_lt_sqrt h_pos_u h_u_ratio_lt
  -- √u₁ < √u₂ · exp((u₁−u₂)/(2u₂)).
  have hu2_ne : u2 ≠ 0 := ne_of_gt hu2_pos
  have h_sqrt_div : Real.sqrt (u1/u2) = Real.sqrt u1 / Real.sqrt u2 :=
    Real.sqrt_div' u1 hu2_pos.le
  have h_su1_lt : Real.sqrt u1 < Real.sqrt u2 * Real.exp ((u1 - u2) / (2 * u2)) := by
    have h := h_sqrt_lt
    rw [h_sqrt_div, div_lt_iff₀ hsu2_pos] at h
    linarith
  -- 1/(2u₂) ≤ α, hence (u₁−u₂)/(2u₂) ≤ α·(u₁−u₂).
  have h_inv_le_α : 1 / (2 * u2) ≤ α := by
    have h_inv_le_half : 1 / (2 * u2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * u2) (by norm_num : (0:ℝ) < 2)]
      nlinarith
    linarith
  have h_d_α : (u1 - u2) / (2 * u2) ≤ α * (u1 - u2) := by
    have h1 : (u1 - u2) / (2 * u2) = (1 / (2 * u2)) * (u1 - u2) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right h_inv_le_α hd_pos.le
  -- √u₁ < √u₂ · exp(α(u₁−u₂)).
  have h_su1_lt' : Real.sqrt u1 < Real.sqrt u2 * Real.exp (α * (u1 - u2)) := by
    apply lt_of_lt_of_le h_su1_lt
    apply mul_le_mul_of_nonneg_left _ hsu2_pos.le
    exact Real.exp_le_exp.mpr h_d_α
  -- Multiply by exp(-α u₁) > 0 (positive) to get the desired form.
  have hex1_pos : 0 < Real.exp (-α * u1) := Real.exp_pos _
  have h_mul := mul_lt_mul_of_pos_right h_su1_lt' hex1_pos
  -- LHS: √u₁ · exp(-α u₁). RHS: √u₂ · exp(α(u₁−u₂)) · exp(-α u₁) = √u₂ · exp(-α u₂).
  have h_rhs_eq : Real.sqrt u2 * Real.exp (α * (u1 - u2)) * Real.exp (-α * u1) =
      Real.sqrt u2 * Real.exp (-α * u2) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [h_rhs_eq] at h_mul
  exact h_mul

/-- **Auxiliary: strict monotonicity of `θ₄(iy)` for `0 < y ≤ 1`.**
Modular transformation `θ_4(iy) · √y = θ_2(i/y)` reduces the small-`y`
regime to the large-`u` regime with `u = 1/y ≥ 1`. Expanding
`θ_2(iu) = 2·exp(-πu/4)·jacobiTheta₂(iu/2, iu)` and combining the
`exp(-πu/4)` factor with the `n`-th term `exp(-π·n(n+1)·u)` of
`jacobiTheta₂` gives `√u · θ_2(iu).re = 2·∑_{n ∈ ℤ} √u·exp(-π·(n+1/2)²·u)`.
Each term `√u·exp(-α·u)` with `α := π(n+1/2)² ≥ π/4 > 1/2` is strictly
antitone on `[1, ∞)` by `sqrt_exp_strict_dec`. Termwise strict
comparison via `Summable.tsum_lt_tsum` finishes. -/
theorem theta4_iy_strictMono_aux_small :
    StrictMonoOn (fun y : ℝ => (theta4 (Complex.I * (y : ℂ))).re) (Set.Ioc 0 1) := by
  -- Step 1: Auxiliary claim — `u ↦ √u · θ_2(iu).re` is strictly antitone on `[1, ∞)`.
  -- This is the heart of the proof; everything else is bookkeeping.
  have h_aux : ∀ u1 u2 : ℝ, 1 ≤ u2 → u2 < u1 →
      Real.sqrt u1 * (theta2 (Complex.I * (u1 : ℂ))).re <
        Real.sqrt u2 * (theta2 (Complex.I * (u2 : ℂ))).re := by
    intros u1 u2 hu2 h_u12
    have hu2_pos : 0 < u2 := lt_of_lt_of_le zero_lt_one hu2
    have hu1_pos : 0 < u1 := lt_trans hu2_pos h_u12
    -- Set up the jacobiTheta₂ HasSum at τ = i·u.
    have hτ1_im : 0 < (Complex.I * (u1 : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_add]
      exact hu1_pos
    have hτ2_im : 0 < (Complex.I * (u2 : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_add]
      exact hu2_pos
    -- jacobiTheta₂_term n (iu/2) (iu) = exp(-π·u·n(n+1)) (real positive).
    have h_jt2_term : ∀ u : ℝ, ∀ n : ℤ,
        jacobiTheta₂_term n (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ)) =
          ((Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
      intros u n
      unfold jacobiTheta₂_term
      have h_arg : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) *
          (Complex.I * (u : ℂ) / 2) +
          (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 *
          (Complex.I * (u : ℂ)) =
          ((-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1) : ℝ) : ℂ) := by
        push_cast
        ring_nf
        rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
        ring
      rw [h_arg, ← Complex.ofReal_exp]
    -- jacobiTheta₂(iu/2, iu) HasSum at τ = iu.
    have h_jt2_sum : ∀ u : ℝ, 0 < u →
        HasSum (fun n : ℤ => ((Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ))
          (jacobiTheta₂ (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ))) := by
      intros u hu
      have hτ_im : 0 < (Complex.I * (u : ℂ)).im := by
        simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
          Complex.ofReal_re, one_mul, zero_add]
        exact hu
      have h_sum := hasSum_jacobiTheta₂_term (Complex.I * (u : ℂ) / 2) hτ_im
      convert h_sum using 1
      funext n
      exact (h_jt2_term u n).symm
    -- Real version of the HasSum.
    have h_jt2_sum_re : ∀ u : ℝ, 0 < u →
        HasSum (fun n : ℤ => Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)))
          (jacobiTheta₂ (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ))).re := by
      intros u hu
      have h_map := (h_jt2_sum u hu).map Complex.reCLM Complex.reCLM.continuous
      simpa only [Complex.reCLM_apply, Complex.ofReal_re, Function.comp_def] using h_map
    -- jacobiTheta₂(iu/2, iu).re = ∑ exp(-π·u·n(n+1)).
    -- Now θ_2(iu) = exp(πi·iu/4) · jacobiTheta₂(iu/2, iu) = exp(-πu/4) · (the sum).
    have h_t2_eq : ∀ u : ℝ, 0 < u →
        (theta2 (Complex.I * (u : ℂ))).re =
          Real.exp (-Real.pi * u / 4) *
            (jacobiTheta₂ (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ))).re := by
      intros u hu
      unfold theta2
      have h_arg : (Real.pi : ℂ) * Complex.I * (Complex.I * (u : ℂ)) / 4 =
          ((-Real.pi * u / 4 : ℝ) : ℂ) := by
        push_cast
        ring_nf
        rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]
        ring
      rw [h_arg, ← Complex.ofReal_exp]
      rw [Complex.re_ofReal_mul]
    -- HasSum representation: √u · θ_2(iu).re = 2 · ∑ √u · exp(-π u/4 - π u n(n+1)).
    -- Define G u n := √u · exp(-π·u/4 - π·u·n(n+1)) = √u · exp(-π·u·(n+1/2)²) (after combining).
    -- We will show G u_2 n > G u_1 n for each n using sqrt_exp_strict_dec.
    -- HasSum for √u · θ_2(iu).re / 2 = exp(-π u/4) · jacobiTheta₂(iu/2, iu).re · √u.
    -- This is a HasSum of `(fun n : ℤ => √u · exp(-π·u/4 - π·u·n(n+1)))`.
    set G : ℝ → ℤ → ℝ := fun u n =>
      Real.sqrt u * Real.exp (-Real.pi * u / 4 - Real.pi * u * (n : ℝ) * ((n : ℝ) + 1))
      with G_def
    have h_G_eq : ∀ u : ℝ, ∀ n : ℤ,
        G u n =
          Real.sqrt u * Real.exp (-(Real.pi * ((n : ℝ) + 1/2)^2) * u) := by
      intros u n
      simp only [G_def]
      congr 1
      ring_nf
    have h_G_sum : ∀ u : ℝ, 0 < u →
        HasSum (G u)
          (Real.sqrt u * (theta2 (Complex.I * (u : ℂ))).re) := by
      intros u hu
      have hsu_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
      -- HasSum of (fun n => exp(-π·u·n(n+1))) = jacobiTheta₂(iu/2, iu).re.
      have h_inner := h_jt2_sum_re u hu
      -- Multiply by √u · exp(-π u/4): HasSum of (fun n => √u · exp(-π u/4) · exp(-π·u·n(n+1))).
      have h_const := h_inner.mul_left (Real.sqrt u * Real.exp (-Real.pi * u / 4))
      -- Combine: term = √u · exp(-π u/4 - π·u·n(n+1)) = G u n.
      have h_eq : ∀ n : ℤ,
          Real.sqrt u * Real.exp (-Real.pi * u / 4) *
            Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)) = G u n := by
        intro n
        simp only [G_def]
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
      rw [show (fun n : ℤ => Real.sqrt u * Real.exp (-Real.pi * u / 4) *
          Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1))) = G u from by
            funext n; exact h_eq n] at h_const
      -- h_const : HasSum (G u) (√u · exp(-π u/4) · jacobiTheta₂(iu/2, iu).re)
      --         = HasSum (G u) (√u · (theta2 iu).re) by h_t2_eq.
      have h_t2 := h_t2_eq u hu
      rw [show Real.sqrt u * Real.exp (-Real.pi * u / 4) *
          (jacobiTheta₂ (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ))).re =
          Real.sqrt u * ((theta2 (Complex.I * (u : ℂ))).re) from by
        rw [h_t2]; ring] at h_const
      exact h_const
    -- Now use strict comparison for each n.
    have hu1_ge_one : 1 ≤ u1 := le_of_lt (lt_of_le_of_lt hu2 h_u12)
    have h_term_lt : ∀ n : ℤ, G u1 n < G u2 n := by
      intro n
      rw [h_G_eq u1 n, h_G_eq u2 n]
      set α := Real.pi * ((n : ℝ) + 1/2)^2 with α_def
      have hα_ge : 1/2 ≤ α := by
        simp only [α_def]
        have h_sq_ge : (1/4 : ℝ) ≤ ((n : ℝ) + 1/2)^2 := by
          -- ((n : ℝ) + 1/2)^2 ≥ 1/4 since (n+1/2)² ≥ 1/4 for n ∈ ℤ.
          -- We have (n + 1/2)² = n² + n + 1/4 = n(n+1) + 1/4 ≥ 0 + 1/4 = 1/4.
          have h1 : (((n : ℝ) + 1/2)^2 : ℝ) = (n : ℝ) * ((n : ℝ) + 1) + 1/4 := by ring
          rw [h1]
          -- n(n+1) ≥ 0 for n ∈ ℤ.
          have h2 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by
            rcases le_or_gt (0 : ℝ) (n : ℝ) with hn | hn
            · have hn' : (0 : ℝ) ≤ (n : ℝ) + 1 := by linarith
              exact mul_nonneg hn hn'
            · -- n < 0 so n ≤ -1, then n + 1 ≤ 0, so n·(n+1) ≥ 0.
              have hn_int : n ≤ -1 := by
                have h_lt : (n : ℝ) < 0 := hn
                have h_lt' : (n : ℤ) < 0 := by exact_mod_cast h_lt
                omega
              have hn'' : ((n : ℝ) + 1) ≤ 0 := by
                have h_le : (n : ℝ) ≤ -1 := by exact_mod_cast hn_int
                linarith
              exact mul_nonneg_iff.mpr (Or.inr ⟨hn.le, hn''⟩)
          linarith
        have h_pi_pos : 0 < Real.pi := Real.pi_pos
        calc (1/2 : ℝ) ≤ Real.pi * (1/4) := by
                have h1 : Real.pi * (1/4) ≥ 3/4 := by
                  have h_pi_ge : Real.pi ≥ 3 := Real.pi_gt_three.le
                  linarith
                linarith
          _ ≤ Real.pi * ((n : ℝ) + 1/2)^2 := by
                exact mul_le_mul_of_nonneg_left h_sq_ge h_pi_pos.le
      exact sqrt_exp_strict_dec hα_ge hu2 h_u12
    have h_term_le : ∀ n : ℤ, G u1 n ≤ G u2 n := fun n => (h_term_lt n).le
    -- Strict comparison of tsums.
    have h_sum1 := h_G_sum u1 hu1_pos
    have h_sum2 := h_G_sum u2 hu2_pos
    have h_tsum_lt : ∑' n : ℤ, G u1 n < ∑' n : ℤ, G u2 n :=
      Summable.tsum_lt_tsum h_term_le (h_term_lt 0) h_sum1.summable h_sum2.summable
    rw [h_sum1.tsum_eq, h_sum2.tsum_eq] at h_tsum_lt
    exact h_tsum_lt
  -- Step 2: Translate back to (0, 1] via the modular transformation.
  intro y1 hy1 y2 hy2 h_y12
  obtain ⟨hy1_pos, hy1_le⟩ := hy1
  obtain ⟨hy2_pos, hy2_le⟩ := hy2
  -- Set u_i := 1/y_i; then u_1 > u_2 ≥ 1.
  have hu2_pos : 0 < 1/y2 := one_div_pos.mpr hy2_pos
  have hu1_pos : 0 < 1/y1 := one_div_pos.mpr hy1_pos
  have hu2_ge : 1 ≤ 1/y2 := by rw [le_div_iff₀ hy2_pos]; linarith
  have hu1_ge : 1 ≤ 1/y1 := by rw [le_div_iff₀ hy1_pos]; linarith
  have h_u_swap : 1/y2 < 1/y1 := one_div_lt_one_div_of_lt hy1_pos h_y12
  -- Show θ_4(iy).re = √u · θ_2(iu).re where u = 1/y, using modular transformation.
  have h_t4 : ∀ y : ℝ, 0 < y →
      (theta4 (Complex.I * (y : ℂ))).re =
        Real.sqrt (1/y) * (theta2 (Complex.I * ((1/y : ℝ) : ℂ))).re := by
    intros y hy
    -- (theta4 (I·y)).re · √y = (theta2 (I/y)).re from theta4_iy_mul_sqrt_eq_theta2.
    have h_modular_eq : Complex.I / (y : ℂ) = Complex.I * ((1/y : ℝ) : ℂ) := by
      have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hy)
      push_cast; field_simp
    have h_mod := theta4_iy_mul_sqrt_eq_theta2 hy
    rw [h_modular_eq] at h_mod
    have hsqy_pos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have hsqy_ne : Real.sqrt y ≠ 0 := ne_of_gt hsqy_pos
    -- (theta4 (I·y)).re = (theta2 (I · (1/y))).re / √y.
    have h_solve : (theta4 (Complex.I * (y : ℂ))).re =
        (theta2 (Complex.I * ((1/y : ℝ) : ℂ))).re / Real.sqrt y := by
      rw [eq_div_iff hsqy_ne]; exact h_mod
    -- 1/√y = √(1/y).
    have h_sqrt_inv : Real.sqrt (1/y) = 1 / Real.sqrt y := by
      rw [Real.sqrt_div' 1 hy.le, Real.sqrt_one]
    rw [h_solve, h_sqrt_inv]; ring
  -- Apply h_aux with u_1 := 1/y_1 and u_2 := 1/y_2.
  change (theta4 (Complex.I * (y1 : ℂ))).re < (theta4 (Complex.I * (y2 : ℂ))).re
  rw [h_t4 y1 hy1_pos, h_t4 y2 hy2_pos]
  exact h_aux (1/y1) (1/y2) hu2_ge h_u_swap

/-- **Strict monotonicity of `θ₄(iy)`.** The function `y ↦ θ₄(iy).re`
is strictly monotone increasing on `(0, ∞)`. Combine the alternating-
series argument (`theta4_iy_strictMono_aux_large`, valid for `y ≥ 1`)
with the modular-transformation argument
(`theta4_iy_strictMono_aux_small`, valid for `0 < y ≤ 1`) via a case
split at the threshold `y = 1`. -/
theorem theta4_iy_strictMono :
    StrictMonoOn (fun y : ℝ => (theta4 (Complex.I * (y : ℂ))).re) (Set.Ioi 0) := by
  intro y1 hy1 y2 hy2 h12
  have hy1' : (0:ℝ) < y1 := hy1
  have hy2' : (0:ℝ) < y2 := hy2
  by_cases hy2_le : y2 ≤ 1
  · -- Both in (0, 1].
    have hy1_le : y1 ≤ 1 := le_of_lt (lt_of_lt_of_le h12 hy2_le)
    exact theta4_iy_strictMono_aux_small ⟨hy1', hy1_le⟩ ⟨hy2', hy2_le⟩ h12
  · have hy2_gt : 1 < y2 := lt_of_not_ge hy2_le
    by_cases hy1_ge : 1 ≤ y1
    · -- Both in [1, ∞).
      exact theta4_iy_strictMono_aux_large hy1_ge (le_of_lt (lt_of_le_of_lt hy1_ge h12)) h12
    · -- y1 < 1 < y2: chain through y = 1.
      have hy1_lt : y1 < 1 := lt_of_not_ge hy1_ge
      have h_one_mem_small : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_refl _⟩
      have h_one_mem_large : (1 : ℝ) ∈ Set.Ici (1 : ℝ) := Set.self_mem_Ici
      have h_y1_one : (theta4 (Complex.I * (y1 : ℂ))).re <
          (theta4 (Complex.I * ((1 : ℝ) : ℂ))).re :=
        theta4_iy_strictMono_aux_small ⟨hy1', le_of_lt hy1_lt⟩ h_one_mem_small hy1_lt
      have h_one_y2 : (theta4 (Complex.I * ((1 : ℝ) : ℂ))).re <
          (theta4 (Complex.I * (y2 : ℂ))).re :=
        theta4_iy_strictMono_aux_large h_one_mem_large (le_of_lt hy2_gt) hy2_gt
      exact lt_trans h_y1_one h_one_y2

/-- **Strict monotonicity of `λ(iy)`.** The function `y ↦ λ(iy).re`
is strictly antitone on `(0, ∞)`. Follows from
`theta3_iy_strictAntitone` (denominator decreasing) and
`theta4_iy_strictMono` (numerator increasing) via the Jacobi
identity `θ₂⁴ + θ₄⁴ = θ₃⁴`, equivalently
`1 − λ(iy) = (θ₄(iy)/θ₃(iy))⁴`: the ratio `θ₄/θ₃` is strictly
increasing (positive numerator increases, positive denominator
decreases), so `(θ₄/θ₃)⁴` is strictly increasing, hence
`λ(iy) = 1 − (θ₄/θ₃)⁴` is strictly decreasing. -/
theorem modularLambdaH_iy_strictAntitone :
    StrictAntiOn (fun y : ℝ => (modularLambdaH (Complex.I * (y : ℂ))).re) (Set.Ioi 0) := by
  intro y1 hy1 y2 hy2 h_y12
  have hy1_pos : (0 : ℝ) < y1 := hy1
  have hy2_pos : (0 : ℝ) < y2 := hy2
  have hτ1_im : 0 < (Complex.I * (y1 : ℂ)).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
    exact hy1_pos
  have hτ2_im : 0 < (Complex.I * (y2 : ℂ)).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
    exact hy2_pos
  -- Positivity helper for `θ_3(iy).re`: it equals `1 + 2·∑_{n≥0} exp(-π(n+1)²·y) ≥ 1 > 0`.
  have h_theta3_pos : ∀ y : ℝ, 0 < y → 1 ≤ (theta3 (Complex.I * (y : ℂ))).re := by
    intros y hy
    have h_yim : 0 < (Complex.I * (y : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_add]
      exact hy
    have h_arg : ∀ n : ℕ, (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1)^2 *
        (Complex.I * (y : ℂ)) = ((-Real.pi * ((n : ℝ) + 1)^2 * y : ℝ) : ℂ) := by
      intro n; push_cast; ring_nf
      rw [show (Complex.I : ℂ)^2 = -1 from Complex.I_sq]; ring
    have h_term : ∀ n : ℕ,
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1)^2 *
          (Complex.I * (y : ℂ))) =
          ((Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y) : ℝ) : ℂ) := by
      intro n; rw [h_arg n, ← Complex.ofReal_exp]
    have h_sum_c := hasSum_nat_jacobiTheta h_yim
    have h_sum_c' : HasSum
        (fun n : ℕ => ((Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y) : ℝ) : ℂ))
        ((jacobiTheta (Complex.I * (y : ℂ)) - 1) / 2) := by
      convert h_sum_c using 1; funext n; exact (h_term n).symm
    have h_sum_re : HasSum
        (fun n : ℕ => Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y))
        ((jacobiTheta (Complex.I * (y : ℂ)) - 1).re / 2) := by
      have h_map := h_sum_c'.map Complex.reCLM Complex.reCLM.continuous
      simp only [Complex.reCLM_apply, Complex.ofReal_re, Function.comp_def] at h_map
      rwa [Complex.div_ofNat_re] at h_map
    have h_tsum_nonneg : 0 ≤ (jacobiTheta (Complex.I * (y : ℂ)) - 1).re / 2 := by
      rw [← h_sum_re.tsum_eq]
      exact tsum_nonneg (fun n => (Real.exp_pos _).le)
    have h_jt_ge : 1 ≤ (jacobiTheta (Complex.I * (y : ℂ))).re := by
      have h_eq : (jacobiTheta (Complex.I * (y : ℂ)) - 1).re =
          (jacobiTheta (Complex.I * (y : ℂ))).re - 1 := by
        rw [Complex.sub_re, Complex.one_re]
      have h_pos : 0 ≤ (jacobiTheta (Complex.I * (y : ℂ))).re - 1 := by
        rw [← h_eq]; linarith [h_tsum_nonneg]
      linarith
    change 1 ≤ (theta3 (Complex.I * (y : ℂ))).re
    unfold theta3; exact h_jt_ge
  -- Positivity helper for `θ_2(iu).re`: it equals `exp(-πu/4)·∑_{n ∈ ℤ} exp(-πu·n(n+1)) > 0`.
  have h_theta2_pos : ∀ u : ℝ, 0 < u → 0 < (theta2 (Complex.I * (u : ℂ))).re := by
    intros u hu
    have h_uim : 0 < (Complex.I * (u : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_add]
      exact hu
    -- jacobiTheta₂_term n (iu/2) (iu) = exp(-π·u·n(n+1)) (real positive).
    have h_jt2_term : ∀ n : ℤ,
        jacobiTheta₂_term n (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ)) =
          ((Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
      intro n
      unfold jacobiTheta₂_term
      have h_arg : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) *
          (Complex.I * (u : ℂ) / 2) +
          (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 *
          (Complex.I * (u : ℂ)) =
          ((-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1) : ℝ) : ℂ) := by
        push_cast; ring_nf
        rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]; ring
      rw [h_arg, ← Complex.ofReal_exp]
    have h_sum := hasSum_jacobiTheta₂_term (Complex.I * (u : ℂ) / 2) h_uim
    have h_sum' : HasSum (fun n : ℤ =>
        ((Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ))
        (jacobiTheta₂ (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ))) := by
      convert h_sum using 1; funext n; exact (h_jt2_term n).symm
    have h_sum_re : HasSum (fun n : ℤ => Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)))
        (jacobiTheta₂ (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ))).re := by
      have h_map := h_sum'.map Complex.reCLM Complex.reCLM.continuous
      simp only [Complex.reCLM_apply, Complex.ofReal_re, Function.comp_def] at h_map
      exact h_map
    -- Sum of positives > 0 (e.g., term at n=0 is exp(0) = 1).
    have h_jt2_pos : 0 < (jacobiTheta₂ (Complex.I * (u : ℂ) / 2) (Complex.I * (u : ℂ))).re := by
      rw [← h_sum_re.tsum_eq]
      have h_term_nonneg : ∀ n : ℤ,
          0 ≤ Real.exp (-Real.pi * u * (n : ℝ) * ((n : ℝ) + 1)) := fun n => (Real.exp_pos _).le
      have h_term0_pos' : 0 < Real.exp (-Real.pi * u * ((0 : ℤ) : ℝ) * (((0 : ℤ) : ℝ) + 1)) :=
        Real.exp_pos _
      exact lt_of_lt_of_le h_term0_pos' (Summable.le_tsum h_sum_re.summable 0
        (fun n _ => h_term_nonneg n))
    -- θ_2(iu).re = exp(-πu/4) · jacobiTheta₂(iu/2, iu).re > 0.
    unfold theta2
    have h_arg : (Real.pi : ℂ) * Complex.I * (Complex.I * (u : ℂ)) / 4 =
        ((-Real.pi * u / 4 : ℝ) : ℂ) := by
      push_cast; ring_nf
      rw [show (Complex.I) ^ 2 = -1 from Complex.I_sq]; ring
    rw [h_arg, ← Complex.ofReal_exp, Complex.re_ofReal_mul]
    exact mul_pos (Real.exp_pos _) h_jt2_pos
  -- Positivity helper for `θ_4(iy).re`: from `θ_4(iy)·√y = θ_2(i/y)` and θ_2 > 0.
  have h_theta4_pos : ∀ y : ℝ, 0 < y → 0 < (theta4 (Complex.I * (y : ℂ))).re := by
    intros y hy
    have h_mod := theta4_iy_mul_sqrt_eq_theta2 hy
    have hsy_pos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have h_uim_eq : Complex.I / (y : ℂ) = Complex.I * ((1/y : ℝ) : ℂ) := by
      have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hy)
      push_cast; field_simp
    rw [h_uim_eq] at h_mod
    have hu_pos : 0 < 1/y := one_div_pos.mpr hy
    have h_t2_pos := h_theta2_pos (1/y) hu_pos
    have h_t4_re_sq_pos : 0 < (theta4 (Complex.I * (y : ℂ))).re * Real.sqrt y := by
      rw [h_mod]; exact h_t2_pos
    have h_sy_ne : Real.sqrt y ≠ 0 := ne_of_gt hsy_pos
    have h_t4_eq : (theta4 (Complex.I * (y : ℂ))).re =
        ((theta4 (Complex.I * (y : ℂ))).re * Real.sqrt y) / Real.sqrt y := by
      field_simp
    rw [h_t4_eq]
    exact div_pos h_t4_re_sq_pos hsy_pos
  -- Now combine: 1 - λ(iy).re = (θ_4(iy).re / θ_3(iy).re)^4, and the ratio is strictly increasing.
  -- Key algebraic step.
  have h_lambda_eq : ∀ y : ℝ, 0 < y →
      1 - (modularLambdaH (Complex.I * (y : ℂ))).re =
        ((theta4 (Complex.I * (y : ℂ))).re / (theta3 (Complex.I * (y : ℂ))).re)^4 := by
    intros y hy
    have h_yim : 0 < (Complex.I * (y : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
        Complex.ofReal_re, one_mul, zero_add]
      exact hy
    have h_jacobi : theta2 (Complex.I * (y : ℂ)) ^ 4 +
        theta4 (Complex.I * (y : ℂ)) ^ 4 =
        theta3 (Complex.I * (y : ℂ)) ^ 4 := jacobi_identity h_yim
    have hne3 : theta3 (Complex.I * (y : ℂ)) ≠ 0 := theta3_ne_zero h_yim
    have h_one_sub : (1 : ℂ) - modularLambdaH (Complex.I * (y : ℂ)) =
        theta4 (Complex.I * (y : ℂ)) ^ 4 / theta3 (Complex.I * (y : ℂ)) ^ 4 := by
      unfold modularLambdaH
      field_simp
      linear_combination -h_jacobi
    have h4_im : (theta4 (Complex.I * (y : ℂ))).im = 0 := theta4_pure_imag_real hy
    have h3_im : (theta3 (Complex.I * (y : ℂ))).im = 0 := theta3_pure_imag_real hy
    have h_t4_eq : theta4 (Complex.I * (y : ℂ)) =
        ((theta4 (Complex.I * (y : ℂ))).re : ℂ) := by
      apply Complex.ext <;> simp [h4_im]
    have h_t3_eq : theta3 (Complex.I * (y : ℂ)) =
        ((theta3 (Complex.I * (y : ℂ))).re : ℂ) := by
      apply Complex.ext <;> simp [h3_im]
    have h_quot_eq : theta4 (Complex.I * (y : ℂ)) ^ 4 /
        theta3 (Complex.I * (y : ℂ)) ^ 4 =
        ((((theta4 (Complex.I * (y : ℂ))).re /
        (theta3 (Complex.I * (y : ℂ))).re) ^ 4 : ℝ) : ℂ) := by
      conv_lhs => rw [h_t4_eq, h_t3_eq]
      push_cast; ring
    rw [h_quot_eq] at h_one_sub
    have h_re_eq : ((1 : ℂ) - modularLambdaH (Complex.I * (y : ℂ))).re =
        (((theta4 (Complex.I * (y : ℂ))).re /
        (theta3 (Complex.I * (y : ℂ))).re) ^ 4 : ℝ) := by
      rw [h_one_sub, Complex.ofReal_re]
    have h_sub_re : ((1 : ℂ) - modularLambdaH (Complex.I * (y : ℂ))).re =
        1 - (modularLambdaH (Complex.I * (y : ℂ))).re := by simp
    rw [h_sub_re] at h_re_eq
    exact h_re_eq
  -- Apply for y1, y2.
  have h_t3_1 := h_theta3_pos y1 hy1_pos
  have h_t3_2 := h_theta3_pos y2 hy2_pos
  have h_t4_1 := h_theta4_pos y1 hy1_pos
  have h_t4_2 := h_theta4_pos y2 hy2_pos
  have h_t3_1_pos : 0 < (theta3 (Complex.I * (y1 : ℂ))).re := lt_of_lt_of_le zero_lt_one h_t3_1
  have h_t3_2_pos : 0 < (theta3 (Complex.I * (y2 : ℂ))).re := lt_of_lt_of_le zero_lt_one h_t3_2
  -- θ_4(iy_1).re < θ_4(iy_2).re from `theta4_iy_strictMono`.
  have h_t4_lt : (theta4 (Complex.I * (y1 : ℂ))).re < (theta4 (Complex.I * (y2 : ℂ))).re :=
    theta4_iy_strictMono hy1_pos hy2_pos h_y12
  -- θ_3(iy_2).re < θ_3(iy_1).re from `theta3_iy_strictAntitone`.
  have h_t3_lt : (theta3 (Complex.I * (y2 : ℂ))).re < (theta3 (Complex.I * (y1 : ℂ))).re :=
    theta3_iy_strictAntitone hy1_pos hy2_pos h_y12
  -- Ratio θ_4/θ_3 strictly increases.
  have h_ratio_lt : (theta4 (Complex.I * (y1 : ℂ))).re / (theta3 (Complex.I * (y1 : ℂ))).re <
      (theta4 (Complex.I * (y2 : ℂ))).re / (theta3 (Complex.I * (y2 : ℂ))).re := by
    rw [div_lt_div_iff₀ h_t3_1_pos h_t3_2_pos]
    -- Goal: θ_4(iy_1) · θ_3(iy_2) < θ_4(iy_2) · θ_3(iy_1).
    -- Bound θ_4(iy_1) · θ_3(iy_2) < θ_4(iy_2) · θ_3(iy_2) ≤ θ_4(iy_2) · θ_3(iy_1).
    have h_step1 : (theta4 (Complex.I * (y1 : ℂ))).re * (theta3 (Complex.I * (y2 : ℂ))).re <
        (theta4 (Complex.I * (y2 : ℂ))).re * (theta3 (Complex.I * (y2 : ℂ))).re :=
      mul_lt_mul_of_pos_right h_t4_lt h_t3_2_pos
    have h_step2 : (theta4 (Complex.I * (y2 : ℂ))).re * (theta3 (Complex.I * (y2 : ℂ))).re <
        (theta4 (Complex.I * (y2 : ℂ))).re * (theta3 (Complex.I * (y1 : ℂ))).re :=
      mul_lt_mul_of_pos_left h_t3_lt h_t4_2
    linarith
  -- The ratios are positive.
  have h_r1_pos : 0 < (theta4 (Complex.I * (y1 : ℂ))).re / (theta3 (Complex.I * (y1 : ℂ))).re :=
    div_pos h_t4_1 h_t3_1_pos
  have h_r2_pos : 0 < (theta4 (Complex.I * (y2 : ℂ))).re / (theta3 (Complex.I * (y2 : ℂ))).re :=
    div_pos h_t4_2 h_t3_2_pos
  -- Fourth powers preserve strict order on positives.
  have h_pow_lt : ((theta4 (Complex.I * (y1 : ℂ))).re / (theta3 (Complex.I * (y1 : ℂ))).re)^4 <
      ((theta4 (Complex.I * (y2 : ℂ))).re / (theta3 (Complex.I * (y2 : ℂ))).re)^4 :=
    pow_lt_pow_left₀ h_ratio_lt h_r1_pos.le (by norm_num)
  -- Conclude.
  change (modularLambdaH (Complex.I * (y2 : ℂ))).re < (modularLambdaH (Complex.I * (y1 : ℂ))).re
  have h_eq1 := h_lambda_eq y1 hy1_pos
  have h_eq2 := h_lambda_eq y2 hy2_pos
  linarith

/-- **Left boundary arc of `F`: `λ(iy) ∈ ℝ`.** For every `y > 0`,
`modularLambdaH(iy)` is real. This is the boundary correspondence for
the left vertical edge `Re τ = 0` of `F`; combined with the
biholomorphism `λ : F^o ≅ {Im w > 0}`, the image of the imaginary
axis is one of the three real-axis arcs of `ℂ ∖ {0, 1}` (specifically
`(0, 1)`). -/
theorem modularLambdaH_pure_imag_real {y : ℝ} (hy : 0 < y) :
    (modularLambdaH (Complex.I * y)).im = 0 := by
  unfold modularLambdaH
  have h2 : (theta2 (Complex.I * y)).im = 0 := theta2_pure_imag_real hy
  have h3 : (theta3 (Complex.I * y)).im = 0 := theta3_pure_imag_real hy
  -- Powers of a real-imaginary-zero complex are real-imaginary-zero.
  have hp : ∀ z : ℂ, z.im = 0 → (z^4).im = 0 := by
    intros z hz
    have : z^4 = z*z*z*z := by ring
    rw [this]
    simp [Complex.mul_im, hz]
  -- Quotient of two real-imaginary-zero complex numbers has imaginary part zero.
  have hdiv : ∀ z w : ℂ, z.im = 0 → w.im = 0 → (z / w).im = 0 := by
    intros z w hz hw
    rw [Complex.div_im, hz, hw]
    ring
  exact hdiv _ _ (hp _ h2) (hp _ h3)

/-- **Right boundary arc of `F`: `λ(1 + iy) ∈ ℝ`.** For every `y > 0`,
`modularLambdaH(1 + iy)` is real. Follows from `modularLambdaH_T_smul`
together with the reality of `θ₂(iy)` and `θ₄(iy)`. -/
theorem modularLambdaH_one_add_imag_real {y : ℝ} (hy : 0 < y) :
    (modularLambdaH (1 + Complex.I * y)).im = 0 := by
  rw [show (1 + Complex.I * y : ℂ) = Complex.I * y + 1 from by ring]
  rw [modularLambdaH_T_smul]
  have h2 : (theta2 (Complex.I * y)).im = 0 := theta2_pure_imag_real hy
  have h4 : (theta4 (Complex.I * y)).im = 0 := theta4_pure_imag_real hy
  have hp : ∀ z : ℂ, z.im = 0 → (z^4).im = 0 := by
    intros z hz
    have : z^4 = z*z*z*z := by ring
    rw [this]
    simp [Complex.mul_im, hz]
  have hdiv : ∀ z w : ℂ, z.im = 0 → w.im = 0 → (z / w).im = 0 := by
    intros z w hz hw
    rw [Complex.div_im, hz, hw]
    ring
  have hquot : (theta2 (Complex.I * y) ^ 4 / theta4 (Complex.I * y) ^ 4).im = 0 :=
    hdiv _ _ (hp _ h2) (hp _ h4)
  rw [Complex.neg_im, hquot, neg_zero]

/-- **Jacobi-derived modular identity for `λ`.** For `τ ∈ ℍ`,
`λ(τ) + λ(-1/τ) = 1`. The proof divides Jacobi's identity
`θ₂⁴ + θ₄⁴ = θ₃⁴` by `θ₃⁴` (which is non-zero on `ℍ`) and reads off
the two `λ`-quotients on the left-hand side via the definition of `λ`
and `modularLambdaH_S_smul`. -/
theorem modularLambdaH_add_S_smul_eq_one {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH τ + modularLambdaH (-1 / τ) = 1 := by
  rw [modularLambdaH_S_smul hτ]
  unfold modularLambdaH
  have h_jac : theta2 τ ^ 4 + theta4 τ ^ 4 = theta3 τ ^ 4 := jacobi_identity hτ
  have hne : theta3 τ ≠ 0 := theta3_ne_zero hτ
  field_simp
  linear_combination h_jac

/-- **Semicircle geometric lemma.** For any `τ ∈ ℂ` with `‖2τ − 1‖ = 1`,
the complex norm-squared `|τ|²` equals the real part `τ.re`. -/
theorem Gamma2FundamentalDomain_semicircle_normSq_eq_re {τ : ℂ}
    (h_circle : ‖2 * τ - 1‖ = 1) : Complex.normSq τ = τ.re := by
  have h_normSq : Complex.normSq (2 * τ - 1) = 1 := by
    rw [← Complex.sq_norm, h_circle]; ring
  have h_re : (2 * τ - 1).re = 2 * τ.re - 1 := by simp
  have h_im : (2 * τ - 1).im = 2 * τ.im := by simp
  have h_expand : Complex.normSq (2 * τ - 1) =
      (2 * τ.re - 1)^2 + (2 * τ.im)^2 := by
    rw [Complex.normSq_apply, h_re, h_im]; ring
  rw [h_expand] at h_normSq
  rw [Complex.normSq_apply]
  nlinarith

/-- **Semicircle boundary arc of `F`: `λ(τ) ∈ ℝ`.** For `τ ∈ ℂ` with
`τ.im > 0` and `‖2τ − 1‖ = 1` (the upper half of the boundary
semicircle of `F`), `modularLambdaH(τ)` is real. The proof uses the
geometric fact `|τ|² = τ.re` (so `-1/τ + 2` lies on the right edge
`Re = 1`), `T²`-invariance of `λ`, the right-edge reality
`modularLambdaH_one_add_imag_real`, and the Jacobi-derived sum identity
`modularLambdaH_add_S_smul_eq_one`. -/
theorem modularLambdaH_semicircle_real {τ : ℂ} (hτ_im : 0 < τ.im)
    (h_circle : ‖2 * τ - 1‖ = 1) :
    (modularLambdaH τ).im = 0 := by
  have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hτ_im
  -- Geometric step: |τ|² = τ.re, hence τ.re > 0.
  have h_normSq : Complex.normSq τ = τ.re :=
    Gamma2FundamentalDomain_semicircle_normSq_eq_re h_circle
  have h_re_pos : 0 < τ.re := by
    have h_pos : 0 < Complex.normSq τ := Complex.normSq_pos.mpr hτ_ne
    rw [h_normSq] at h_pos; exact h_pos
  -- Compute (-1/τ).re = -1 and (-1/τ).im = τ.im / τ.re > 0.
  have h_inv_re : (-1 / τ).re = -1 := by
    rw [show (-1 / τ : ℂ) = -(τ⁻¹) from by ring]
    rw [Complex.neg_re, Complex.inv_re, h_normSq]
    field_simp
  have h_inv_im : (-1 / τ).im = τ.im / τ.re := by
    rw [show (-1 / τ : ℂ) = -(τ⁻¹) from by ring]
    rw [Complex.neg_im, Complex.inv_im, h_normSq]
    field_simp
  -- -1/τ + 2 has Re = 1, Im = τ.im/τ.re > 0.
  have h_shift_re : (-1 / τ + 2).re = 1 := by
    rw [Complex.add_re, h_inv_re]; norm_num
  have h_shift_im : (-1 / τ + 2).im = τ.im / τ.re := by
    rw [Complex.add_im, h_inv_im]; simp
  have h_shift_im_pos : 0 < τ.im / τ.re := div_pos hτ_im h_re_pos
  -- -1/τ + 2 = 1 + Complex.I * (τ.im/τ.re).
  have h_shift_eq : (-1 / τ + 2 : ℂ) = 1 + Complex.I * (τ.im / τ.re : ℝ) := by
    rw [Complex.ext_iff]
    refine ⟨?_, ?_⟩
    · rw [h_shift_re]; simp
    · rw [h_shift_im]; simp
  -- λ(-1/τ + 2) is real by the right-edge lemma.
  have h_right_edge : (modularLambdaH (-1 / τ + 2)).im = 0 := by
    rw [h_shift_eq]
    exact modularLambdaH_one_add_imag_real h_shift_im_pos
  -- By T²-invariance, λ(-1/τ) = λ(-1/τ + 2), hence λ(-1/τ).im = 0.
  have h_lambda_inv : (modularLambdaH (-1 / τ)).im = 0 := by
    have := modularLambdaH_two_add (-1 / τ)
    rw [← this]; exact h_right_edge
  -- Sum identity: λ(τ) = 1 - λ(-1/τ).
  have h_sum := modularLambdaH_add_S_smul_eq_one hτ_im
  have h_lambda_eq : modularLambdaH τ = 1 - modularLambdaH (-1 / τ) := by
    linear_combination h_sum
  rw [h_lambda_eq, Complex.sub_im, h_lambda_inv]
  simp

/-! ## Conjugation symmetry of `λ` and theta nullwerte

The theta series and `λ` have real coefficients, so they satisfy a
reflection identity under `τ ↦ -conj τ` (the imaginary-axis reflection,
which preserves `ℍ`). Combined with `modularLambdaH_image_fundamentalDomainInterior`,
this maps `F^o` to the right half of `F'^o` and gives `λ(F''^o) = lower half`,
which together with the upper half from `F^o` and the boundary reals
covers all of `ℂ ∖ {0, 1}`. -/

/-- **Conjugation symmetry of `θ₃`.** `θ₃(-conj τ) = conj(θ₃ τ)` for
every `τ ∈ ℍ`. Reduction to `jacobiTheta₂_conj` at `z = 0`. -/
theorem theta3_conj_symmetry (τ : ℂ) :
    theta3 (-(starRingEnd ℂ τ)) = starRingEnd ℂ (theta3 τ) := by
  unfold theta3
  rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta_eq_jacobiTheta₂]
  have h := (jacobiTheta₂_conj 0 τ).symm
  -- h : jacobiTheta₂ (conj 0) (-conj τ) = conj (jacobiTheta₂ 0 τ)
  rwa [map_zero] at h

/-- **Conjugation symmetry of `θ₂`.** `θ₂(-conj τ) = conj(θ₂ τ)` for
every `τ ∈ ℍ`. The proof uses `jacobiTheta₂_conj` together with
`jacobiTheta₂_neg_left` to flip the `z = -τ/2` sign back. -/
theorem theta2_conj_symmetry (τ : ℂ) :
    theta2 (-(starRingEnd ℂ τ)) = starRingEnd ℂ (theta2 τ) := by
  unfold theta2
  -- Step 1: Rewrite the exp factor's argument as a conjugate.
  have h_exp : (Real.pi : ℂ) * Complex.I * (-(starRingEnd ℂ τ)) / 4 =
      starRingEnd ℂ ((Real.pi : ℂ) * Complex.I * τ / 4) := by
    rw [map_div₀, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [h_exp, Complex.exp_conj]
  -- Step 2: jacobiTheta₂(-conj τ / 2, -conj τ) = conj(jacobiTheta₂(τ/2, τ)).
  have h_arg : ((-(starRingEnd ℂ τ)) / 2 : ℂ) = starRingEnd ℂ (-(τ / 2)) := by
    rw [map_neg, map_div₀, map_ofNat]; ring
  have h_jt2 : jacobiTheta₂ ((-(starRingEnd ℂ τ)) / 2) (-(starRingEnd ℂ τ)) =
      starRingEnd ℂ (jacobiTheta₂ (τ / 2) τ) := by
    rw [h_arg]
    -- jacobiTheta₂(conj(-τ/2), -conj τ) = conj(jacobiTheta₂(-τ/2, τ))  -- by conj
    -- jacobiTheta₂(-τ/2, τ) = jacobiTheta₂(τ/2, τ)  -- by neg_left
    have h := (jacobiTheta₂_conj (-(τ/2)) τ).symm
    rw [← jacobiTheta₂_neg_left (τ/2) τ]
    exact h
  rw [h_jt2, ← map_mul]

/-- **Conjugation symmetry of `θ₄`.** `θ₄(-conj τ) = conj(θ₄ τ)` for
every `τ ∈ ℂ`. Uses `theta4 τ = jacobiTheta(τ + 1)` and the
2-periodicity of `jacobiTheta`. -/
theorem theta4_conj_symmetry (τ : ℂ) :
    theta4 (-(starRingEnd ℂ τ)) = starRingEnd ℂ (theta4 τ) := by
  unfold theta4
  -- jacobiTheta(-conj τ + 1) = jacobiTheta(-conj(τ - 1))
  --                          = conj(jacobiTheta(τ - 1))
  --                          = conj(jacobiTheta(τ + 1))  (by 2-periodicity).
  have h_neg_conj : -(starRingEnd ℂ τ) + 1 = -(starRingEnd ℂ (τ - 1)) := by
    rw [map_sub, map_one]; ring
  rw [h_neg_conj]
  -- Apply theta3_conj_symmetry at σ = τ - 1.
  have h_step := theta3_conj_symmetry (τ - 1)
  unfold theta3 at h_step
  rw [h_step]
  -- jacobiTheta(τ - 1) = jacobiTheta(τ + 1) by 2-periodicity.
  congr 1
  have h := jacobiTheta_two_add (τ - 1)
  rw [show (2 : ℂ) + (τ - 1) = τ + 1 from by ring] at h
  exact h.symm

/-- **Conjugation symmetry of `λ`.** For `τ ∈ ℍ`, `λ(-conj τ) = conj(λ τ)`.
The proof divides the `θ₂` and `θ₃` conjugation identities. -/
theorem modularLambdaH_conj_symmetry {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH (-(starRingEnd ℂ τ)) = starRingEnd ℂ (modularLambdaH τ) := by
  unfold modularLambdaH
  rw [theta2_conj_symmetry τ, theta3_conj_symmetry τ]
  have h3_ne : theta3 τ ≠ 0 := theta3_ne_zero hτ
  rw [map_div₀, map_pow, map_pow]

/-- **Schwarz reflection identity for `λ` through the line `Re τ = 1`.**
For `τ ∈ ℍ`, `λ(2 − conj τ) = conj(λ τ)`. Composition of
`modularLambdaH_conj_symmetry` (reflection through `Re τ = 0`) and
`modularLambdaH_sub_two` (T²-invariance). -/
theorem modularLambdaH_schwarz_reflect_re_one {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH (2 - starRingEnd ℂ τ) = starRingEnd ℂ (modularLambdaH τ) := by
  have h_eq : (2 - starRingEnd ℂ τ : ℂ) = -(starRingEnd ℂ (τ - 2)) := by
    rw [map_sub, map_ofNat]; ring
  rw [h_eq]
  have hτ_sub_2_im : 0 < (τ - 2).im := by
    rw [Complex.sub_im]; simpa using hτ
  rw [modularLambdaH_conj_symmetry hτ_sub_2_im]
  rw [modularLambdaH_sub_two]

/-- **Schwarz reflection identity for `λ` through the F^o boundary
semicircle `|τ − 1/2| = 1/2`.** For `τ ∈ ℍ`,
`λ(conj τ / (2·conj τ − 1)) = conj(λ τ)`. The Möbius `w ↦ w/(2w−1)`
fixes the semicircle pointwise; composed with conjugation it gives
the antiholomorphic inversion across the semicircle. The proof uses
`modularLambdaH_div_two_tau_add_one` (inverted to get
`λ(−τ/(2τ−1)) = λ(τ)`) and `modularLambdaH_conj_symmetry`. -/
theorem modularLambdaH_schwarz_reflect_semicircle {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambdaH (starRingEnd ℂ τ / (2 * starRingEnd ℂ τ - 1)) =
      starRingEnd ℂ (modularLambdaH τ) := by
  -- 2τ - 1 ≠ 0 since τ.im > 0 forces (2τ - 1).im > 0.
  have h_2τ_m_1_ne : (2 * τ - 1 : ℂ) ≠ 0 := by
    intro h
    have h_im : (2 * τ - 1 : ℂ).im = 0 := by rw [h]; rfl
    simp [Complex.sub_im, Complex.mul_im, Complex.one_im] at h_im
    linarith
  -- σ' := -τ/(2τ - 1). σ'.im > 0.
  set σ' : ℂ := -τ / (2 * τ - 1) with hσ'_def
  have h_denom_normSq_pos : 0 < Complex.normSq (2 * τ - 1) :=
    Complex.normSq_pos.mpr h_2τ_m_1_ne
  have hσ'_im_pos : 0 < σ'.im := by
    have h_im_eq : σ'.im = τ.im / Complex.normSq (2 * τ - 1) := by
      rw [hσ'_def]
      rw [show (-τ / (2 * τ - 1) : ℂ) = -(τ / (2 * τ - 1)) from neg_div _ _]
      rw [Complex.neg_im, Complex.div_im]
      have h_2τ_re : (2 * τ - 1 : ℂ).re = 2 * τ.re - 1 := by
        simp [Complex.sub_re, Complex.mul_re, Complex.one_re]
      have h_2τ_im : (2 * τ - 1 : ℂ).im = 2 * τ.im := by
        simp [Complex.sub_im, Complex.mul_im, Complex.one_im]
      rw [h_2τ_re, h_2τ_im]
      field_simp
      ring
    rw [h_im_eq]
    exact div_pos hτ h_denom_normSq_pos
  -- 2σ' + 1 = -1/(2τ - 1) ≠ 0.
  have h_2σ'_p_1_ne : (2 * σ' + 1 : ℂ) ≠ 0 := by
    intro h
    have h_im : (2 * σ' + 1 : ℂ).im = 0 := by rw [h]; rfl
    simp [Complex.add_im, Complex.mul_im, Complex.one_im] at h_im
    linarith
  -- σ'·(2τ - 1) = -τ (from definition of σ').
  have h_step : σ' * (2 * τ - 1) = -τ := by
    rw [hσ'_def]
    exact div_mul_cancel₀ _ h_2τ_m_1_ne
  -- σ'/(2σ' + 1) = τ.
  have h_φ_σ' : σ' / (2 * σ' + 1) = τ := by
    rw [div_eq_iff h_2σ'_p_1_ne]
    linear_combination -h_step
  -- λ(σ') = λ(τ) by Γ(2)-invariance applied to σ'.
  have h_σ'_lambda : modularLambdaH σ' = modularLambdaH τ := by
    have h := modularLambdaH_div_two_tau_add_one hσ'_im_pos
    rw [h_φ_σ'] at h
    exact h.symm
  -- conj(τ)/(2 conj(τ) - 1) = -conj(σ').
  have h_eq : (starRingEnd ℂ τ / (2 * starRingEnd ℂ τ - 1) : ℂ) =
      -(starRingEnd ℂ σ') := by
    rw [hσ'_def]
    rw [map_div₀, map_neg, map_sub, map_mul, map_ofNat, map_one]
    field_simp
  rw [h_eq, modularLambdaH_conj_symmetry hσ'_im_pos, h_σ'_lambda]

/-- **Cusp `1`:** `Re(λ(1 + iy)) → −∞` as `y → 0⁺`. Proof via the
modular identity `λ(τ + 1) = λ(τ)/(λ(τ) − 1)` (derived from
`modularLambdaH_T_smul` and `jacobi_identity` divided through by `θ₃⁴`).
With the cusp-`0` limit `λ(iy) → 1` and the strict bound `λ(iy) < 1`
(from `1 − λ(iy) = (θ₄/θ₃)⁴(iy) > 0`), we get `λ(iy) − 1 → 0⁻`. Then
`1/(λ(iy)−1) → −∞` and `λ(iy)/(λ(iy)−1) → 1·(−∞) = −∞`. -/
theorem modularLambdaH_one_add_iy_tendsto_neg_infty_atZeroPos :
    Tendsto (fun y : ℝ => (modularLambdaH (1 + Complex.I * y)).re)
      (𝓝[>] (0 : ℝ)) atBot := by
  -- Step 1: g y := (λ(I·y)).re → 1.
  have h_g_to_one : Tendsto (fun y : ℝ => (modularLambdaH (Complex.I * (y : ℂ))).re)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h_lambda := modularLambdaH_iy_tendsto_one_atZeroPos
    have h_re : Tendsto (fun y : ℝ => (modularLambdaH (Complex.I * (y : ℂ))).re)
        (𝓝[>] (0 : ℝ)) (𝓝 (Complex.re 1)) :=
      (Complex.continuous_re.tendsto _).comp h_lambda
    simpa using h_re
  -- Step 2: g y < 1 for y > 0.
  have h_g_lt_one : ∀ᶠ (y : ℝ) in 𝓝[>] (0 : ℝ),
      (modularLambdaH (Complex.I * (y : ℂ))).re < 1 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy_pos : (0 : ℝ) < y := hy
    have hτ_im : 0 < (Complex.I * (y : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero,
        Complex.I_im, Complex.ofReal_re, one_mul, zero_add]
      exact hy_pos
    have h_ne_one : modularLambdaH (Complex.I * (y : ℂ)) ≠ 1 :=
      modularLambdaH_ne_one hτ_im
    have h_jacobi : theta2 (Complex.I * (y : ℂ)) ^ 4 +
        theta4 (Complex.I * (y : ℂ)) ^ 4 =
        theta3 (Complex.I * (y : ℂ)) ^ 4 := jacobi_identity hτ_im
    have hne3 : theta3 (Complex.I * (y : ℂ)) ≠ 0 := theta3_ne_zero hτ_im
    have hne4 : theta4 (Complex.I * (y : ℂ)) ≠ 0 := theta4_ne_zero hτ_im
    have h_one_sub : (1 : ℂ) - modularLambdaH (Complex.I * (y : ℂ)) =
        theta4 (Complex.I * (y : ℂ)) ^ 4 / theta3 (Complex.I * (y : ℂ)) ^ 4 := by
      unfold modularLambdaH
      field_simp
      linear_combination -h_jacobi
    have h4_im : (theta4 (Complex.I * (y : ℂ))).im = 0 := theta4_pure_imag_real hy_pos
    have h3_im : (theta3 (Complex.I * (y : ℂ))).im = 0 := theta3_pure_imag_real hy_pos
    have h_t4_eq : theta4 (Complex.I * (y : ℂ)) =
        ((theta4 (Complex.I * (y : ℂ))).re : ℂ) := by
      apply Complex.ext <;> simp [h4_im]
    have h_t3_eq : theta3 (Complex.I * (y : ℂ)) =
        ((theta3 (Complex.I * (y : ℂ))).re : ℂ) := by
      apply Complex.ext <;> simp [h3_im]
    have ht3_re_ne : (theta3 (Complex.I * (y : ℂ))).re ≠ 0 := by
      intro h
      apply hne3
      rw [h_t3_eq, h]; simp
    have ht4_re_ne : (theta4 (Complex.I * (y : ℂ))).re ≠ 0 := by
      intro h
      apply hne4
      rw [h_t4_eq, h]; simp
    have h_quot_eq : theta4 (Complex.I * (y : ℂ)) ^ 4 /
        theta3 (Complex.I * (y : ℂ)) ^ 4 =
        ((((theta4 (Complex.I * (y : ℂ))).re /
        (theta3 (Complex.I * (y : ℂ))).re) ^ 4 : ℝ) : ℂ) := by
      conv_lhs => rw [h_t4_eq, h_t3_eq]
      push_cast; ring
    rw [h_quot_eq] at h_one_sub
    have h_nonneg : (0 : ℝ) ≤ ((theta4 (Complex.I * (y : ℂ))).re /
        (theta3 (Complex.I * (y : ℂ))).re) ^ 4 := by positivity
    have h_pos : (0 : ℝ) < ((theta4 (Complex.I * (y : ℂ))).re /
        (theta3 (Complex.I * (y : ℂ))).re) ^ 4 := by
      refine lt_of_le_of_ne h_nonneg (fun h_zero => ?_)
      have h_quot_zero : (theta4 (Complex.I * (y : ℂ))).re /
          (theta3 (Complex.I * (y : ℂ))).re = 0 :=
        pow_eq_zero_iff (n := 4) (by norm_num : (4 : ℕ) ≠ 0) |>.mp h_zero.symm
      rw [div_eq_zero_iff] at h_quot_zero
      rcases h_quot_zero with h | h
      · exact ht4_re_ne h
      · exact ht3_re_ne h
    have h_re_eq : ((1 : ℂ) - modularLambdaH (Complex.I * (y : ℂ))).re =
        (((theta4 (Complex.I * (y : ℂ))).re /
        (theta3 (Complex.I * (y : ℂ))).re) ^ 4 : ℝ) := by
      rw [h_one_sub, Complex.ofReal_re]
    have h_sub_re : ((1 : ℂ) - modularLambdaH (Complex.I * (y : ℂ))).re =
        1 - (modularLambdaH (Complex.I * (y : ℂ))).re := by simp
    rw [h_sub_re] at h_re_eq
    linarith
  -- Step 3: g y - 1 ∈ 𝓝[<] 0 (eventually).
  have h_sub_to_zero_below :
      Tendsto (fun y : ℝ => (modularLambdaH (Complex.I * (y : ℂ))).re - 1)
        (𝓝[>] (0 : ℝ)) (𝓝[<] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := h_g_to_one.sub_const 1
      simpa using this
    · filter_upwards [h_g_lt_one] with y hy
      change (modularLambdaH (Complex.I * (y : ℂ))).re - 1 < 0
      linarith
  -- Step 4: 1/(g y - 1) → atBot.
  have h_inv_atBot :
      Tendsto (fun y : ℝ => ((modularLambdaH (Complex.I * (y : ℂ))).re - 1)⁻¹)
        (𝓝[>] (0 : ℝ)) atBot :=
    tendsto_inv_nhdsLT_zero.comp h_sub_to_zero_below
  -- Step 5: g(y) * 1/(g(y) - 1) → 1 · atBot = atBot.
  have h_prod : Tendsto (fun y : ℝ => (modularLambdaH (Complex.I * (y : ℂ))).re *
      ((modularLambdaH (Complex.I * (y : ℂ))).re - 1)⁻¹)
      (𝓝[>] (0 : ℝ)) atBot :=
    h_g_to_one.pos_mul_atBot one_pos h_inv_atBot
  -- Step 6: For y > 0, (λ(1+iy)).re = g(y) * 1/(g(y) - 1).
  have h_id : (fun y : ℝ => (modularLambdaH (Complex.I * (y : ℂ))).re *
        ((modularLambdaH (Complex.I * (y : ℂ))).re - 1)⁻¹) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun y : ℝ => (modularLambdaH (1 + Complex.I * y)).re) := by
    filter_upwards [self_mem_nhdsWithin, h_g_lt_one] with y hy h_lt
    have hy_pos : (0 : ℝ) < y := hy
    have hτ_im : 0 < (Complex.I * (y : ℂ)).im := by
      simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero,
        Complex.I_im, Complex.ofReal_re, one_mul, zero_add]
      exact hy_pos
    have h_jacobi : theta2 (Complex.I * (y : ℂ)) ^ 4 +
        theta4 (Complex.I * (y : ℂ)) ^ 4 =
        theta3 (Complex.I * (y : ℂ)) ^ 4 := jacobi_identity hτ_im
    have hne3 : theta3 (Complex.I * (y : ℂ)) ≠ 0 := theta3_ne_zero hτ_im
    have hne4 : theta4 (Complex.I * (y : ℂ)) ≠ 0 := theta4_ne_zero hτ_im
    have h_im_iy : (modularLambdaH (Complex.I * (y : ℂ))).im = 0 :=
      modularLambdaH_pure_imag_real hy_pos
    have h_lam_sub_ne : modularLambdaH (Complex.I * (y : ℂ)) - 1 ≠ 0 :=
      sub_ne_zero.mpr (modularLambdaH_ne_one hτ_im)
    have h_complex_id : modularLambdaH (1 + Complex.I * (y : ℂ)) =
        modularLambdaH (Complex.I * (y : ℂ)) /
        (modularLambdaH (Complex.I * (y : ℂ)) - 1) := by
      rw [show (1 + Complex.I * (y : ℂ) : ℂ) = Complex.I * (y : ℂ) + 1 from by ring]
      rw [modularLambdaH_T_smul, eq_div_iff h_lam_sub_ne]
      unfold modularLambdaH
      field_simp
      linear_combination -(theta2 (Complex.I * (y : ℂ)) ^ 4) * h_jacobi
    have ha_eq : modularLambdaH (Complex.I * (y : ℂ)) =
        ((modularLambdaH (Complex.I * (y : ℂ))).re : ℂ) := by
      apply Complex.ext <;> simp [h_im_iy]
    have hb_im : (modularLambdaH (Complex.I * (y : ℂ)) - 1).im = 0 := by
      simp [Complex.sub_im, h_im_iy]
    have hb_eq : modularLambdaH (Complex.I * (y : ℂ)) - 1 =
        (((modularLambdaH (Complex.I * (y : ℂ))).re - 1 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hb_im]
    have hb_re_ne : ((modularLambdaH (Complex.I * (y : ℂ))).re - 1 : ℝ) ≠ 0 := by
      intro h
      have : (modularLambdaH (Complex.I * (y : ℂ))).re = 1 := by linarith
      linarith
    -- Compute the RHS using h_complex_id and reality of numerator/denominator.
    have h_rhs_eq : (modularLambdaH (1 + Complex.I * (y : ℂ))).re =
        (modularLambdaH (Complex.I * (y : ℂ))).re /
        ((modularLambdaH (Complex.I * (y : ℂ))).re - 1) := by
      rw [h_complex_id, ha_eq]
      rw [show ((modularLambdaH (Complex.I * (y : ℂ))).re : ℂ) - 1 =
          (((modularLambdaH (Complex.I * (y : ℂ))).re - 1 : ℝ) : ℂ) from by push_cast; ring]
      rw [← Complex.ofReal_div]
      exact Complex.ofReal_re _
    rw [h_rhs_eq]
    field_simp
  exact h_prod.congr' h_id

end NoWanderingDomains
